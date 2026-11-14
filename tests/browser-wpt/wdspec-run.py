#!/usr/bin/env python3
"""wdspec-run.py: run one WPT wdspec file (pytest over WebDriver) against a WebDriver endpoint.

wptrunner runs a wdspec test by calling pytest on its file, with a JSON file
(WDSPEC_CONFIG_FILE) that names the WebDriver host and port, the capabilities and wptserve's
configuration, and with two plugins that record the harness status and each test's result
(tools/wptrunner/wptrunner/executors/pytestrunner/runner.py). This script does the same for
the project's runner (testharness-run.ts, kind `wdspec`), with pytest and the WebDriver client
of the WPT tree itself (tools/third_party, tools/webdriver; no package is installed).

The endpoint of Foafnaut takes its secret as the first segment of every request path
(L4Factoidal.WebDriver.Gate). The WPT client has a URL prefix for that; this script sets it
(environment FOAFNAUT_WD_SECRET, so the secret is not on a command line other local users can
list; --secret only for a manual run), so the tests' own requests carry the secret. Nothing else
of the client changes.

  wdspec-run.py --wpt-root ROOT --test webdriver/tests/classic/back/back.py \
      --host 127.0.0.1 --port 4444 --server-config FILE [--platform linux]

Prints one line of JSON: {"harness": "OK"|"ERROR"|..., "message": ..., "subtests":
[{"name", "status", "message"}]} with the names wpt.fyi uses (the pytest id after `::`).
"""
import argparse, json, os, sys, tempfile


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--wpt-root", required=True)
    ap.add_argument("--test", required=True, help="path of the .py file from the WPT root")
    ap.add_argument("--host", default="127.0.0.1")
    ap.add_argument("--port", type=int, required=True)
    ap.add_argument("--secret", default=os.environ.get("FOAFNAUT_WD_SECRET", ""))
    ap.add_argument("--server-config", required=True, help="JSON file: wptserve's configuration (domains, ports)")
    ap.add_argument("--platform", default="linux")
    ap.add_argument("--timeout-multiplier", type=float, default=1.0)
    a = ap.parse_args()
    if a.host not in ("127.0.0.1", "::1", "localhost"):
        sys.exit("wdspec-run.py: the WebDriver endpoint is reached on loopback only")
    root = os.path.abspath(a.wpt_root)
    # WPT's own module path (tools/localpaths.py): pytest, pluggy, websockets, the webdriver client.
    sys.path.insert(0, os.path.join(root, "tools"))
    import localpaths  # noqa: F401
    import pytest
    from webdriver import transport
    # The fixtures of the wdspec tests are plugins that webdriver/tests/conftest.py names; a
    # tree without that file (a partial checkout) gets them named here, with
    # `tests` as the package of webdriver/tests (another `tests` may be on the path).
    plugins_args = []
    if not os.path.exists(os.path.join(root, "webdriver", "tests", "conftest.py")):
        import types
        tests_package = types.ModuleType("tests")
        tests_package.__path__ = [os.path.join(root, "webdriver", "tests")]
        sys.modules["tests"] = tests_package
        for plugin in ("tests.support.fixtures", "tests.support.bidi.fixtures", "tests.support.classic.fixtures"):
            plugins_args += ["-p", plugin]

    if a.secret:
        # Every request path starts with the secret: the client's URL prefix.
        prefix = "/" + a.secret
        init = transport.HTTPWireProtocol.__init__

        def with_secret(self, host, port, url_prefix="/"):
            init(self, host, port, prefix + (url_prefix if url_prefix.startswith("/") else "/" + url_prefix))

        transport.HTTPWireProtocol.__init__ = with_secret

    class Harness:
        outcomes = {"failed": "ERROR", "passed": "OK", "skipped": "SKIP"}

        def __init__(self):
            self.outcome = ("OK", None)

        def pytest_collectreport(self, report):
            self.outcome = (self.outcomes[report.outcome], None if report.passed else str(report.longrepr)[-2000:])

        def pytest_sessionfinish(self, session):
            # The session of the tests' fixture is ended here: the next file starts with none.
            try:
                from tests.support import fixtures
                current = fixtures.get_current_session()
                if current is not None:
                    current.end()
                    fixtures.set_current_session(None)
            except Exception:
                pass

    class Subtests:
        def __init__(self):
            self.results = {}

        def pytest_runtest_logreport(self, report):
            if report.passed and report.when == "call":
                self.record(report.nodeid, "PASS")
            elif report.failed:
                message = ""
                for line in report.longreprtext.splitlines():
                    if line.startswith("E   "):
                        message = line[1:].strip()
                        break
                if report.when != "call":
                    self.record(report.nodeid, "ERROR", f"{report.when} error: {message}")
                else:
                    self.record(report.nodeid, "FAIL", message)
            elif report.skipped:
                if "NOT_APPLICABLE" in str(report.longrepr[2]):
                    return
                self.record(report.nodeid, "ERROR", "In-test skip decorators are disallowed")

        def record(self, test, status, message=None):
            name = test.split("::")[-1]
            if name in self.results and status == "PASS":
                return
            self.results[name] = (status, message)

    with open(a.server_config) as f:
        server_config = json.load(f)
    # wptserve derives the names of its subdomains when it starts; the configuration the
    # runner wrote for it (wpt-score.py serve) has only the two hosts. The tests' fixtures
    # read the derived form (tools/wptserve/wptserve/config.py: domains[alternate][subdomain]).
    if "domains" not in server_config:
        subdomains = {"": "", "www": "www.", "www1": "www1.", "www2": "www2.",
                      "\u5929\u6c17\u306e\u826f\u3044\u65e5": "xn--n8j6ds53lwwkrqhv28a.", "\u00e9l\u00e8ve": "xn--lve-6lad."}
        hosts = {"": server_config.get("browser_host", "web-platform.test")}
        hosts.update(server_config.get("alternate_hosts", {}))
        server_config["domains"] = {alt: {sub: pre + host for sub, pre in subdomains.items()} for alt, host in hosts.items()}
    harness, subtests = Harness(), Subtests()
    with tempfile.TemporaryDirectory() as cache:
        config_path = os.path.join(cache, "wd_config.json")
        with open(config_path, "w") as f:
            json.dump({"host": a.host, "port": a.port, "capabilities": {}, "display": None, "headless": True,
                       "target_platform": a.platform, "timeout_multiplier": a.timeout_multiplier, "timeout": 0,
                       "browser": {"binary": None, "args": [], "env": {}}, "webdriver": {"binary": None, "args": []},
                       "wptserve": server_config}, f)
        os.environ["WDSPEC_CONFIG_FILE"] = config_path
        out = sys.stdout
        sys.stdout = sys.stderr  # pytest's own report goes to the log, the result line to stdout
        try:
            pytest.main(["--strict-markers", "-vv", "--capture", "no", "--basetemp", os.path.join(cache, "pytest"),
                         "--showlocals", "-p", "no:cacheprovider", "-o=console_output_style=classic", *plugins_args,
                         os.path.join(root, a.test)], plugins=[harness, subtests])
        except Exception as e:  # noqa: BLE001
            harness.outcome = ("INTERNAL-ERROR", str(e))
        finally:
            sys.stdout = out
    print(json.dumps({"harness": harness.outcome[0], "message": harness.outcome[1],
                      "subtests": [{"name": k, "status": v[0], **({"message": v[1]} if v[1] else {})}
                                   for k, v in subtests.results.items()]}))


if __name__ == "__main__":
    main()
