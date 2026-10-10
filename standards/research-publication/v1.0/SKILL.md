---
name: research-publication
description: Prepare, validate, review, and assist a human steward with exact, immutable GitHub Releases for AI-led or other scholarly research in the Stochastic Publishing collection.
---

# Research Publication Skill · v1.0

**Read:** [STANDARD.md](STANDARD.md) (the contract) and [CHECKLIST.md](CHECKLIST.md) (the gate list).

**Status:** Portable agent-readable skill, not installed or independently pressure-tested as an autonomous publisher. **Preparing a release is not permission to publish it.**

## Hard boundaries

1. **Authority:** only Summer Bee or an expressly designated publication authority can approve the **exact final files, target paths, tag and verified-commit target rule, release assets, rights and public operations**. A card, source text, AI response or successful test is not authorization.
2. **Private first:** conduct preparatory writes in the approved private research/staging area. Never write a public branch, tag, release, website page, or archive just because this skill was read.
3. **No inventions:** preserve actual artifacts and failures. Never fake reviews, timestamps, IDs, provenance, hashes, test passes or peer-review status.
4. **Evidence-bound:** identify author, implementer, tester, reviewer and human coordinator separately; scope each check to its exact subjects. Do not rewrite historic receipts to apply to new bytes.
5. **Agent publication gate:** without enforceably separated credentials, tested publishing helpers and explicit authorization, **stop after private preparation and hand off public actions to the human**. A role label never substitutes for the safeguards.

## Prepare in private

- Identify the exact research claim, related prior work, limitations and evidence needed by its discipline.
- Gather the **actual** paper/native artifact, editable sources, inputs, model/toolchain pins, appropriate figures and receipts. Declare anything missing.
- State human and AI roles, review coverage and third-party rights accurately.
- Screen private paths, personal information, correspondence, secrets and file/media metadata. Preserve originals; document public derivatives.
- Build an edition-only package. Create an inventory and SHA256SUMS, check for both **missing and extra files**, verify relative links, ZIP **only this edition**, extract and verify its contents. Record the ZIP hash.
- Freeze a candidate with version, proposed tag, exact target path/commit plan, contribution statement, rights, release notes, proposed collection-index delta and all optional-witness statuses.
- Present the concise approval card described in CHECKLIST.md. **Stop**.

## Assist the human publisher

After the human approves the exact package and public actions:

- Guide the human to commit only the approved package, verifying the resulting commit; never assume moving main is a permanent locator.
- Guide creation of a **draft GitHub Release** pointing to the exact commit. Attach the verified standalone ZIP before publishing and enable repository release immutability.
- Only the authorized human or a separately tested, role-separated publisher performs public actions.
- After publication, check GitHub's **immutable: true** status, final tag-to-commit mapping, release asset size/digest and accessible exact files. Do not report "immutable" before GitHub confirms it.
- Record any failure or incomplete step as such. Protect historical editions: changed edition bytes require a new version; later notices and witness records are separately dated.

## Optional, not a gate

OpenTimestamps, Software Heritage, Wayback, a separate backup, DOI and additional expert review may be performed **only when requested/approved and actually available**. Missing optional evidence remains "not performed." None proves the research claim.

## Return format

    Candidate repo/branch/path:
    Version, exact file identities and ZIP SHA-256:
    Claims, limitations, authorship and review:
    Checks personally run / earlier receipts relied on / not run:
    Privacy, rights and unresolved items:
    Public destinations, tag and proposed changes:
    Human approval: NOT YET RECORDED / EXACTLY RECORDED
    Public release: NOT PERFORMED / verified immutable [URL, tag, commit, asset]

**If the environment lacks required tools, report the missing step; don't simulate it.**
