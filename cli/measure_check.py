"""Runs csd-check on a certificate and on a copy with one false claim added.

    python3 measure_check.py [csd-check] [certificate.json]

The defaults are ./csd-check and certificate.json. Under Termux the
executable, which links glibc, runs through glibc-runner's grun when grun is
installed; elsewhere it runs directly. LD_PRELOAD is removed from its
environment. For each run the script prints the exit code, the wall time, the
user time and the maximum resident memory of the child processes, and the last
line of the output.

The false claim states that Catalog is acyclic; Catalog has a cycle. The run
passes when the checker exits 0 on the certificate and 1 on the copy. The exit
code of the script is 0 when the run passes and 1 otherwise.
"""

import json
import os
import platform
import resource
import shutil
import subprocess
import sys
import tempfile
import time


def device_info():
    lines = [f"machine: {platform.machine()}"]
    for label, cmd in (("android", ["getprop", "ro.build.version.release"]),
                       ("glibc-runner", ["dpkg-query", "-W", "-f=${Version}", "glibc-runner"])):
        try:
            out = subprocess.run(cmd, capture_output=True, text=True, timeout=10).stdout.strip()
        except (OSError, subprocess.SubprocessError):
            out = ""
        lines.append(f"{label}: {out or 'not found'}")
    return lines


def main(argv):
    exe = argv[1] if len(argv) > 1 else "./csd-check"
    cert_path = argv[2] if len(argv) > 2 else "certificate.json"
    grun = shutil.which("grun")
    runner = [grun] if grun else []
    env = {k: v for k, v in os.environ.items() if k != "LD_PRELOAD"}

    for line in device_info():
        print(line)
    print(f"runner: {grun or 'direct'}")

    with open(cert_path) as f:
        cert = json.load(f)
    cert["claims"].append({"claim": "acyclic", "schema": "Catalog"})
    tmp = tempfile.mkdtemp()
    false_path = os.path.join(tmp, "certificate-false.json")
    with open(false_path, "w") as f:
        json.dump(cert, f)

    failed = False
    for label, path, expected in (("certificate", cert_path, 0),
                                  ("certificate with a false claim", false_path, 1)):
        before = resource.getrusage(resource.RUSAGE_CHILDREN)
        start = time.monotonic()
        try:
            r = subprocess.run(runner + [exe, path], capture_output=True, text=True, env=env)
            code, out, err = r.returncode, r.stdout, r.stderr
        except OSError as e:
            code, out, err = None, "", str(e)
        wall = time.monotonic() - start
        after = resource.getrusage(resource.RUSAGE_CHILDREN)
        last = (out.strip().splitlines() or [""])[-1]
        print(f"{label}: exit {code} (expected {expected}), wall {wall:.2f} s, "
              f"user {after.ru_utime - before.ru_utime:.2f} s, "
              f"max RSS {after.ru_maxrss // 1024} MB")
        print(f"  last line: {last}")
        if err.strip():
            print(f"  stderr: {err.strip()[-800:]}")
        failed |= code != expected

    shutil.rmtree(tmp)
    print("RESULT: " + ("FAIL" if failed else "PASS"))
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
