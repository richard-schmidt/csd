"""Checks the output of csd-check on the broken context map and the example certificate.

    python3 cli/test/check_report.py [csd-check]

The default executable is .lake/build/bin/csd-check. broken-map.json is
DDD.Examples.Problems.brokenMap, written by cli/CsdExport.lean; the expected
results below are those the #guard tests of DDD/Examples/Problems.lean state for
it. The script exits with 0 when every expectation holds and 1 otherwise.
"""

import json
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))

SCHEMA_KINDS = ["duplicateEntity", "duplicateGenerator", "referenceTarget", "referenceSource",
                "attributeSource", "equationNotParallel", "equationSource", "aggregateEntity",
                "aggregateOverlap", "missingOwner", "ownerCycle", "aggregateBoundary",
                "valueObjectFields", "valueObjectEntity", "keyEntity", "keyEmpty", "keyField",
                "subtypeEntity", "subtypeReference"]

EXPECTED_CONTEXTS = [("OrdersPL", True, []), ("Payments", True, []), ("Broken", False, SCHEMA_KINDS),
                     ("Untyped", False, ["undeclaredValueType", "nestedOptional"])]
EXPECTED_VALUE_TYPES = (False, ["emptyEnumeration", "builtinTypeName"])
EXPECTED_ARROWS = [("billing", True, []), ("billingToShipping", False, ["equationImage"]),
                   ("dangling", False, ["unknownSchema"])]


def summary(entries):
    return [(e["name"], e["ok"], [p["kind"] for p in e["problems"]]) for e in entries]


def main(argv):
    exe = argv[1] if len(argv) > 1 else os.path.join(ROOT, ".lake/build/bin/csd-check")
    broken = os.path.join(HERE, "broken-map.json")
    certificate = os.path.join(ROOT, "julia/out/certificate.json")
    errors = []

    r = subprocess.run([exe, "--json", broken], capture_output=True, text=True)
    if r.returncode != 1:
        errors.append(f"broken map: exit code {r.returncode}, expected 1")
    report = json.loads(r.stdout)
    if report.get("kind") != "mapReport":
        errors.append(f"broken map: kind {report.get('kind')}, expected mapReport")
    if report.get("failed") != 5:
        errors.append(f"broken map: {report.get('failed')} failed, expected 5")
    types = report.get("valueTypes", {})
    if (types.get("ok"), [p["kind"] for p in types.get("problems", [])]) != EXPECTED_VALUE_TYPES:
        errors.append(f"broken map: value types {types}")
    if summary(report["contexts"]) != EXPECTED_CONTEXTS:
        errors.append(f"broken map: contexts {summary(report['contexts'])}")
    if summary(report["arrows"]) != EXPECTED_ARROWS:
        errors.append(f"broken map: arrows {summary(report['arrows'])}")
    for entry in [dict(types, name="valueTypes")] + report["contexts"] + report["arrows"]:
        for p in entry["problems"]:
            if not p.get("message"):
                errors.append(f"broken map: a problem of {entry['name']} has no message")

    r = subprocess.run([exe, broken], capture_output=True, text=True)
    if r.returncode != 1 or "is declared more than once" not in r.stdout:
        errors.append(f"broken map, text output: exit code {r.returncode}, "
                      "or no problem message in the output")

    r = subprocess.run([exe, "--json", certificate], capture_output=True, text=True)
    report = json.loads(r.stdout)
    if r.returncode != 0 or report.get("failed") != 0:
        errors.append(f"certificate: exit code {r.returncode}, {report.get('failed')} failed")
    if not all(c["ok"] and c["problems"] == [] for c in report["claims"]):
        errors.append("certificate: a claim is not ok or has problems")

    for e in errors:
        print("FAILED " + e)
    print("check_report: " + ("all expectations hold" if not errors else f"{len(errors)} failed"))
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
