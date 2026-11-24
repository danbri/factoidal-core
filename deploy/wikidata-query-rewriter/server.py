"""Bounded HTTP adapter to a Wikimedia-compatible JSONL command."""
import json
import os
import subprocess
import threading
import uuid
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

JAR = os.environ.get('REWRITER_JAR', '/app/sparql-rewriter.jar')
REWRITER_BIN = os.environ.get('REWRITER_BIN')
COMMAND = [REWRITER_BIN] if REWRITER_BIN else ['java', '-Xmx256m', '-Xss16m', '-jar', JAR]
MAX_BODY = 1_000_000
slots = threading.BoundedSemaphore(2)

class Handler(BaseHTTPRequestHandler):
    def log_message(self, format, *args):
        pass
    def reply(self, status, obj):
        body = json.dumps(obj, ensure_ascii=False).encode('utf-8')
        self.send_response(status)
        self.send_header('Content-Type', 'application/json; charset=utf-8')
        self.send_header('Cache-Control', 'no-store')
        self.send_header('Content-Length', str(len(body)))
        self.end_headers()
        self.wfile.write(body)
    def do_GET(self):
        self.reply(200, {'ok': True}) if self.path == '/healthz' else self.reply(404, {'error': 'not_found'})
    def do_POST(self):
        if self.path != '/rewrite': return self.reply(404, {'error': 'not_found'})
        try:
            size = int(self.headers.get('Content-Length', ''))
            if size < 0 or size > MAX_BODY: return self.reply(413, {'error': 'request_too_large'})
            if self.headers.get_content_type() != 'application/json': return self.reply(415, {'error': 'expected_application_json'})
            self.connection.settimeout(10)
            payload = json.loads(self.rfile.read(size))
            if not isinstance(payload, dict) or not isinstance(payload.get('query'), str): raise ValueError()
        except (ValueError, UnicodeError, OSError, TimeoutError):
            return self.reply(400, {'error': 'invalid_request'})
        if not slots.acquire(blocking=False): return self.reply(503, {'error': 'busy'})
        try:
            ident = str(uuid.uuid4())
            request = {'protocol_version': 1, 'request_id': ident, 'query_id': ident, 'query': payload['query']}
            p = subprocess.run(COMMAND, input=json.dumps(request)+'\n', text=True, capture_output=True, timeout=75)
            result = json.loads(p.stdout)
            if p.returncode or not isinstance(result, dict) or result.get('request_id') != ident: raise ValueError()
            self.reply(200, result)
        except (OSError, ValueError, subprocess.TimeoutExpired):
            self.reply(502, {'error': 'rewriter_unavailable'})
        finally:
            slots.release()

if __name__ == '__main__':
    ThreadingHTTPServer(('0.0.0.0', int(os.environ.get('PORT', '8080'))), Handler).serve_forever()
