# csd-check on Android (Termux)

A test run of the native `csd-check` on an Android phone under Termux: whether
the aarch64 executable runs there, how long it takes and how much memory it
uses. The result decides whether the checker can serve an editor hosted on the
phone. The run is on the A52 (ssh alias `a52`), driven from the Pixel; the run
of 2026-11-02 passed (`DDD/README.md`, next step 7).

The A52 rules in the brain's `fleet.md` apply. Every change to the A52 is
validated with the owner first: step 3 installs packages and needs the owner's
OK. The run touches nothing outside `~/csd-check-test` and the glibc-runner
packages.

## What runs

- `csd-check`: `cli/CsdCheck.lean` compiled for aarch64 Linux, linking glibc
  dynamically (about 175 MB, stripped). Termux runs binaries for Android's own
  C library only; a glibc binary runs through `grun`, from the Termux packages
  `glibc-repo` and `glibc-runner`.
- `certificate.json`: the certificate of 32 claims of the example map
  (`julia/out/certificate.json`).
- `measure_check.py` (`cli/measure_check.py`): runs `csd-check` on the
  certificate and on a copy with one false claim added, through `grun` when it
  is installed, and prints for each run the exit code, the wall time, the user
  time and the maximum resident memory. The last line is `RESULT: PASS` when
  the checker exits 0 on the certificate and 1 on the copy.
- `SHA256SUMS`: the checksums of the three files.

The four files are the artifact `csd-check-linux-aarch64` of the workflow
`csd-check on aarch64` (`.github/workflows/csd_check_arm.yml`), kept 30 days
after its run. A push to `claude/ddd-design` that changes `cli/` or a Lean
file of `DDD/` produces a new one.

Reference, on GitHub's two-core aarch64 runner: 0.09 s and 112 MB for the
certificate.

## Steps

1. On the Pixel, download the artifact of the latest successful run into
   `~/csd-check-test` and verify it:

   ```bash
   RUN=$(gh run list -R richard-schmidt/csd --workflow csd_check_arm.yml --branch claude/ddd-design --status success --limit 1 --json databaseId --jq '.[0].databaseId'); echo "run $RUN"
   ```

   ```bash
   gh run download "$RUN" -R richard-schmidt/csd -n csd-check-linux-aarch64 -D ~/csd-check-test
   ```

   ```bash
   cd ~/csd-check-test && sha256sum -c SHA256SUMS
   ```

   Without `gh`: in a browser signed in to GitHub, open
   <https://github.com/richard-schmidt/csd/actions/workflows/csd_check_arm.yml>,
   the latest successful run on `claude/ddd-design`, and download
   `csd-check-linux-aarch64` from its Artifacts. Then extract it and verify:

   ```bash
   python3 -m zipfile -e ~/storage/downloads/csd-check-linux-aarch64.zip ~/csd-check-test && cd ~/csd-check-test && sha256sum -c SHA256SUMS
   ```

2. Copy the directory to the A52:

   ```bash
   scp -r ~/csd-check-test a52:
   ```

3. On the A52, with the owner's OK, install glibc-runner and check that `grun`
   is there:

   ```bash
   ssh a52 'pkg install -y glibc-repo && pkg install -y glibc-runner && command -v grun'
   ```

4. On the A52, run the test:

   ```bash
   ssh a52 'cd ~/csd-check-test && sha256sum -c SHA256SUMS && chmod +x csd-check && python3 measure_check.py'
   ```

   A passing run prints `machine: aarch64`, the Android and glibc-runner
   versions, `runner:` with the path of `grun`, one line per run with
   `all 32 claims hold` and `1 of 33 claims failed` as last lines, and
   `RESULT: PASS`.

5. Clean up on both phones:

   ```bash
   ssh a52 'rm -r ~/csd-check-test'
   ```

   ```bash
   rm -r ~/csd-check-test
   ```

   glibc-runner stays installed unless the owner asks for its removal
   (`pkg uninstall glibc-runner glibc-repo`). If it stays, it is a fleet fact
   for the A52 entry of `fleet.md`.

## When the run fails

One check per hypothesis, and report what each showed.

- `runner: direct` on the A52: `grun` is not installed or not on the path, and
  Termux cannot load the binary directly (`No such file or directory`, from the
  missing glibc loader). Repeat step 3.
- Loading: `ssh a52 'cd ~/csd-check-test && grun ./csd-check'` prints
  `usage: csd-check certificate.json` and exits 2 when the binary loads. This
  proves loading only; the run on the certificate is the mode that counts.
- `Bad system call`, or exit code 159 or -31 (signal 31, SIGSYS): Android's
  system-call filter refused a call that glibc makes. The next candidate is a Debian or
  Ubuntu root file system under `proot-distro`, a larger install that needs the
  owner's OK.
- Exit 2 with a JSON error: the certificate did not arrive intact; step 4
  stops at `sha256sum -c` in that case.
- `LD_PRELOAD`: Termux sets it for its own libraries, and it can break glibc
  binaries; `measure_check.py` removes it from the checker's environment.

## Report

The full output of step 4, and of any check from the list above, goes to the
owner, who passes it on to the work on the `DDD` library. The result is
recorded under next step 7 of `DDD/README.md`.
