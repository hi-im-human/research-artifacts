"""Stage 4B: PROVENANCE-STAGE-4B.json matches the files it pins, and the ported prototype sources are unchanged."""
import hashlib
import json
from pathlib import Path

from glab.ideal_check.checker import ANALYTIC_DEPENDENCY, IDEAL_CHECKER_REVISION, IDEAL_POLICY
from glab.two_rim.ideal_actions import IDEAL_ACTION_REVISION

ENGINE = Path(__file__).resolve().parents[2]
RECORD = json.loads((ENGINE / "PROVENANCE-STAGE-4B.json").read_text(encoding="ascii"))


def _lf(path):
    return (ENGINE / path).read_bytes().replace(b"\r\n", b"\n")


def _git_blob(path):
    data = _lf(path)
    return hashlib.sha1(b"blob %d\0" % len(data) + data).hexdigest()


def test_pinned_files_match_their_recorded_hashes():
    for path, digest in RECORD["files_affecting_arithmetic_or_claims_sha256_lf"].items():
        assert hashlib.sha256(_lf(path)).hexdigest() == digest, path


def test_the_ported_prototype_sources_are_still_the_pinned_blobs():
    for path, blob in RECORD["source_blobs"].items():
        assert _git_blob(path) == blob, path


def test_recorded_revisions_and_policy_are_the_registered_ones():
    assert RECORD["revisions"] == {"two_rim.check.ideal_trimmed_development@1": IDEAL_CHECKER_REVISION,
                                   "two_rim.ideal.define@1": IDEAL_ACTION_REVISION}
    assert RECORD["policy"] == {"id": IDEAL_POLICY["policy"],
                                "contract_sha256_lf": ANALYTIC_DEPENDENCY["contract_sha256_lf"]}
