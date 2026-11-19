#!/bin/bash
# Run the checked Linux x86_64 Foafnaut browser in a macOS XQuartz window.
# X11 goes through an authenticated SSH tunnel, not a public X11 TCP listener.
# Requirements installed as needed: Homebrew's Podman and XQuartz.
set -euo pipefail
umask 077

if [[ ${1:-} == --help || ${1:-} == -h ]]; then
  cat <<'HELP'
Usage: bash run-foafnaut-linux-podman.sh [Foafnaut arguments]
Reclaim unused VM disk blocks: bash run-foafnaut-linux-podman.sh --reclaim-space
Example: bash run-foafnaut-linux-podman.sh --url https://example.org/
Input tracing: FOAFNAUT_TRACE_INPUT=1 bash run-foafnaut-linux-podman.sh
Stock renderer: FOAFNAUT_FULL_RENDERER=1 bash run-foafnaut-linux-podman.sh

Installs Podman/XQuartz if missing, creates a dedicated Linux VM, provisions
QEMU x86-64 execution on Apple Silicon, verifies the pinned browser archive,
and opens the Linux browser through SSH X11 forwarding and software Vulkan.
No xhost changes, XQuartz TCP settings, or Mac home-directory container mount.
Defaults to a small local page, bitmap fonts and single-frame rendering without
the animated splash. Logs are saved in ~/Library/Caches/factoidal-linux-browser.

The VM, image and verified archive are reused. The temporary container and SSH
keys are removed on exit. A VM started by this script is stopped on exit.
First-time XQuartz installation can prompt for a macOS administrator password.
Homebrew must already be installed. Do not run this script with sudo.
HELP
  exit 0
fi

say() { printf '\n%s\n' "$*"; }
die() { printf 'ERROR: %s\n' "$*" >&2; exit 1; }
[[ $(uname -s) == Darwin ]] || die 'This launcher is for macOS.'
[[ $EUID != 0 ]] || die 'Run as your normal Mac user, without sudo.'
command -v brew >/dev/null || die 'Install Homebrew from https://brew.sh, then rerun.'
if [[ ${1:-} == --reclaim-space ]]; then
  [[ $# == 1 ]] || die '--reclaim-space takes no other arguments.'
  command -v podman >/dev/null || die 'Podman is not installed; there is no VM to trim.'
  trim_machine=foafnaut-linux-x11
  podman machine inspect "$trim_machine" >/dev/null \
    || die 'The existing foafnaut-linux-x11 VM could not be found; no new VM was created.'
  trim_started=0
  finish_trim() {
    local rc=$?
    trap - EXIT INT TERM
    if (( trim_started )); then podman machine stop "$trim_machine" || true; fi
    printf '\nMac free space after trim:\n'
    df -h /
    exit "$rc"
  }
  trap finish_trim EXIT
  trap 'exit 130' INT
  trap 'exit 143' TERM
  if [[ $(podman machine inspect --format '{{.State}}' "$trim_machine") != running ]]; then
    podman machine start "$trim_machine"
    trim_started=1
  fi
  say 'Discarding unused guest filesystem blocks. No files, images or containers are deleted.'
  podman machine ssh "$trim_machine" sudo fstrim -av
  exit 0
fi
command -v podman >/dev/null || brew install podman
[[ -x /opt/X11/bin/xdpyinfo && -x /opt/X11/bin/xauth ]] || brew install --cask xquartz
[[ -x /opt/X11/bin/xdpyinfo && -x /opt/X11/bin/xauth ]] || die 'XQuartz installation did not provide its X11 tools.'

state_dir="$HOME/Library/Caches/factoidal-linux-browser"
mkdir -p "$state_dir"
check_space() {
  local available minimum=${1:-4}
  available=$(df -Pk "$state_dir" | awk 'END {print $4}')
  [[ $available =~ ^[0-9]+$ ]] || die 'Could not check available disk space.'
  (( available >= minimum * 1024 * 1024 )) || die "Need at least $minimum GiB free; no existing VM or image was deleted."
}
check_space
scratch=$(mktemp -d "$state_dir/session.XXXXXX")
machine=foafnaut-linux-x11
container="foafnaut-linux-x11-$$"
started_here=0
container_created=0
cleanup() {
  local rc=$?
  trap - EXIT INT TERM
  if (( container_created )) || [[ $(podman --connection "$machine" inspect \
    --format '{{index .Config.Labels "org.factoidal.launcher-session"}}' "$container" 2>/dev/null || true) == "$scratch" ]]; then
    podman --connection "$machine" rm -f "$container" >/dev/null 2>&1 || true
  fi
  if (( started_here )); then podman machine stop "$machine" >/dev/null 2>&1 || true; fi
  # Only this invocation's mktemp directory, never cached images or other VMs.
  [[ -n ${scratch:-} && $scratch == "$state_dir"/session.* ]] && rm -rf -- "$scratch"
  exit "$rc"
}
trap cleanup EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

say 'Starting XQuartz (X11 forwarding stays authenticated; no xhost +).'
agent=/Library/LaunchAgents/org.xquartz.startx.plist
if [[ -f $agent ]] && ! launchctl print "gui/$UID/org.xquartz.startx" >/dev/null 2>&1; then
  launchctl bootstrap "gui/$UID" "$agent" 2>/dev/null || true
fi
open -a XQuartz
x_display=
for attempt in {1..30}; do
  launch_display=$(launchctl getenv DISPLAY 2>/dev/null || true)
  for candidate in "$launch_display" "${DISPLAY:-}" ':0'; do
    if [[ -n $candidate ]] && /opt/X11/bin/xdpyinfo -display "$candidate" >/dev/null 2>&1; then
      x_display=$candidate
      break
    fi
  done
  [[ -n $x_display ]] && break
  sleep 1
done
[[ -n $x_display ]] || die 'XQuartz is not ready. After a first installation, log out/in once and rerun this same script.'

# This override belongs only to this script. It does not edit global Podman settings.
# QEMU avoids a Rosetta licence install and macOS/kernel-specific Rosetta failures.
cat > "$scratch/containers.conf" <<'CONF'
[machine]
provider="applehv"
rosetta=false
volumes=[]
CONF
export CONTAINERS_CONF_OVERRIDE="$scratch/containers.conf"
if ! podman machine inspect "$machine" >/dev/null 2>&1; then
  check_space 6
  say 'Creating reusable Podman VM: 4 CPUs, 4 GiB RAM, 16 GiB logical sparse disk.'
  podman machine init --cpus 4 --memory 4096 --disk-size 16 "$machine"
fi
if [[ $(podman machine inspect --format '{{.State}}' "$machine") != running ]]; then
  podman machine start "$machine"
  started_here=1
fi
if ! vm_mounts=$(podman machine ssh "$machine" \
  'findmnt -rn -t virtiofs; result=$?; [ "$result" -eq 1 ] && exit 0; exit "$result"'); then
  die 'Could not verify VM filesystem isolation.'
fi
[[ -z $vm_mounts ]] || die 'This dedicated VM has existing host filesystem mounts; it was left unchanged. Use a fresh foafnaut-linux-x11 VM.'
pm() { podman --connection "$machine" "$@"; }

if [[ $(uname -m) == arm64 ]]; then
  say 'Registering x86-64 QEMU execution inside the Linux VM.'
  # Privilege is confined to this Linux VM; it registers the guest kernel's binfmt handler.
  if ! podman --connection "$machine-root" image exists docker.io/tonistiigi/binfmt:latest; then check_space 6; fi
  podman --connection "$machine-root" run --rm --privileged --platform linux/arm64 \
    docker.io/tonistiigi/binfmt:latest --install amd64
fi
say 'Checking that Linux x86-64 executables really run.'
if ! pm image exists docker.io/library/ubuntu:24.04; then check_space 6; fi
[[ $(pm run --rm --platform linux/amd64 docker.io/library/ubuntu:24.04 uname -m) == x86_64 ]] \
  || die 'The x86-64 execution check failed.'
check_space

release=build-7d4794f49f5d-foafnaut-browser-linux-x86_64
archive="$state_dir/$release.tar.gz"
expected=d9c0a151ad916768a5d3607d650212f23fe1617dc38730b550ac4746489ac7e4
archive_ok() { [[ -f $archive && $(shasum -a 256 "$archive" | awk '{print $1}') == "$expected" ]]; }
if ! archive_ok; then
  check_space 6
  say 'Downloading the pinned Linux browser (about 60 MB).'
  curl --fail --location --retry 3 --output "$scratch/browser.download" \
    "https://github.com/danbri/factoidal-builds/releases/download/$release/foafnaut-browser-linux-x86_64.tar.gz"
  [[ $(shasum -a 256 "$scratch/browser.download" | awk '{print $1}') == "$expected" ]] \
    || die 'Browser archive SHA-256 mismatch.'
  mv "$scratch/browser.download" "$archive"
fi
mkdir "$scratch/build"
ln "$archive" "$scratch/build/browser.tar.gz" 2>/dev/null || cp "$archive" "$scratch/build/browser.tar.gz"
cat > "$scratch/build/Containerfile" <<'CONTAINERFILE'
FROM docker.io/library/ubuntu:24.04
ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update && apt-get install -y --no-install-recommends \
    ca-certificates openssh-server xauth x11-utils vulkan-tools \
    libsdl2-2.0-0 libvulkan1 mesa-vulkan-drivers \
 && rm -rf /var/lib/apt/lists/* /etc/ssh/ssh_host_* \
 && useradd --create-home --shell /bin/bash foafnaut \
 && passwd -d foafnaut \
 && install -d -m 0755 /run/sshd \
 && install -d -m 0700 -o foafnaut -g foafnaut /home/foafnaut/.ssh /tmp/foafnaut-runtime
RUN icd="$(find /usr/share/vulkan/icd.d -name 'lvp_icd*.json' -print -quit)" \
 && test -n "$icd" && printf '%s\n' "$icd" > /etc/foafnaut-vulkan-icd \
 && printf '%s\n' '#!/bin/sh' 'set -eu' \
    'export VK_DRIVER_FILES="$(cat /etc/foafnaut-vulkan-icd)"' \
    'export VK_ICD_FILENAMES="$VK_DRIVER_FILES"' \
    'export DENO_WEBGPU_BACKEND=vulkan SDL_VIDEODRIVER=x11 LIBGL_ALWAYS_SOFTWARE=1' \
    'export XDG_RUNTIME_DIR=/tmp/foafnaut-runtime' \
    'exec "$@"' > /usr/local/bin/foafnaut-display \
 && chmod 755 /usr/local/bin/foafnaut-display
ADD browser.tar.gz /opt/
RUN cd /opt/foafnaut-linux-x86_64 && sha256sum -c SHA256SUMS
RUN printf '%s\n' \
    'Port 22' 'AddressFamily inet' 'HostKey /etc/ssh/ssh_host_ed25519_key' \
    'PasswordAuthentication no' 'KbdInteractiveAuthentication no' \
    'PermitEmptyPasswords no' 'PermitRootLogin no' 'PubkeyAuthentication yes' \
    'UsePAM no' 'AllowUsers foafnaut' 'AllowAgentForwarding no' \
    'AllowTcpForwarding no' 'X11Forwarding yes' 'X11UseLocalhost yes' \
    'XAuthLocation /usr/bin/xauth' > /etc/ssh/sshd_config
EXPOSE 22
CMD ["/bin/sh", "-ec", "ssh-keygen -q -t ed25519 -N '' -f /etc/ssh/ssh_host_ed25519_key; exec /usr/sbin/sshd -D -e"]
CONTAINERFILE
image_hash=$(shasum -a 256 "$scratch/build/Containerfile" | cut -c1-12)
image="localhost/foafnaut-linux-x11:7d4794f49f5d-$image_hash"
if ! pm image exists "$image"; then
  check_space 6
  say 'Building the reusable Ubuntu/X11/software-Vulkan image.'
  pm build --platform linux/amd64 --tag "$image" --file "$scratch/build/Containerfile" "$scratch/build"
fi

say 'Starting a temporary browser container; SSH is published only on Mac loopback.'
ssh-keygen -q -t ed25519 -N '' -f "$scratch/client_key"
pm run -d --name "$container" --label "org.factoidal.launcher-session=$scratch" \
  --platform linux/amd64 --shm-size 256m \
  --publish 127.0.0.1::22 "$image" >/dev/null
container_created=1
pm cp "$scratch/client_key.pub" "$container:/home/foafnaut/.ssh/authorized_keys"
pm exec "$container" chown foafnaut:foafnaut /home/foafnaut/.ssh/authorized_keys
pm exec "$container" chmod 600 /home/foafnaut/.ssh/authorized_keys
host_key=
for attempt in {1..30}; do
  host_key=$(pm exec "$container" cat /etc/ssh/ssh_host_ed25519_key.pub 2>/dev/null || true)
  [[ $host_key == ssh-ed25519\ * ]] && break
  sleep 1
done
[[ $host_key == ssh-ed25519\ * ]] || { pm logs "$container" >&2; die 'The container SSH server did not start.'; }
port=$(pm port "$container" 22/tcp)
port=${port##*:}
[[ $port =~ ^[0-9]+$ ]] || die 'Could not find the loopback SSH port.'
# Obtain the host key through authenticated Podman, not an unverified ssh-keyscan.
printf '[127.0.0.1]:%s %s\n' "$port" "$host_key" > "$scratch/known_hosts"
ssh_opts=(-F /dev/null -Y -i "$scratch/client_key" -p "$port"
  -o BatchMode=yes -o IdentitiesOnly=yes -o StrictHostKeyChecking=yes
  -o "UserKnownHostsFile=$scratch/known_hosts" -o GlobalKnownHostsFile=/dev/null
  -o XAuthLocation=/opt/X11/bin/xauth -o ForwardAgent=no -o ConnectTimeout=10 -o ConnectionAttempts=10
  -o ServerAliveInterval=30)
target=foafnaut@127.0.0.1
say 'Checking X11 and presenting two software-Vulkan frames (a brief cube window).'
if ! DISPLAY="$x_display" ssh "${ssh_opts[@]}" "$target" \
  'exec /usr/local/bin/foafnaut-display sh -ec "xdpyinfo >/dev/null; vulkaninfo --summary; timeout 90s vkcube --c 2"'; then
  die 'X11/software-Vulkan presentation failed; the browser was not started. See the errors above.'
fi
if (( $# == 0 )); then
  # A small first page avoids compiling/rendering the large bundled demo index.
  pm exec --user foafnaut "$container" /bin/sh -c 'printf "%s\n" \
    "<!doctype html><html><head><title>Foafnaut Linux</title></head><body>" \
    "<h1>Foafnaut on Linux</h1><p>This page is rendered by the Linux browser.</p>" \
    "<p>Click the window, then press Control-L to enter a URL. Space or Page Down scrolls.</p>" \
    "<p><a href=\"https://example.org/\">Open Example Domain</a></p></body></html>" \
    > /tmp/foafnaut-start.html'
  set -- --html /tmp/foafnaut-start.html
fi
browser_args=(--no-state --no-splash --single-frame --bitmap-font --perf-summary)
if [[ ${FOAFNAUT_FULL_RENDERER:-0} == 1 ]]; then browser_args=(--no-state --perf-summary); fi
if [[ ${FOAFNAUT_TRACE_INPUT:-0} == 1 ]]; then browser_args+=(--trace-input); fi
remote=(exec /usr/local/bin/foafnaut-display /opt/foafnaut-linux-x86_64/foafnaut "${browser_args[@]}" "$@")
printf -v remote_command '%q ' "${remote[@]}"
say 'Launching the Linux browser. Close its window or press Control-C here to finish.'
say "Browser log: $state_dir/last-launch.log"
set +e
DISPLAY="$x_display" ssh "${ssh_opts[@]}" "$target" "$remote_command" 2>&1 | tee "$state_dir/last-launch.log"
result=${PIPESTATUS[0]}
set -e
exit "$result"
