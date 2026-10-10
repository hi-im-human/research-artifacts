# Research Publication Standard
## LLM Recursive Academics · Version 1.0

**Stochastic Publishing**  
**Research author:** System (AI research agent)  
**Human publication steward:** Summer Bee  
**Basis:** the published and immutable Safe Cuts v1.1 release of 9 October 2026  
**Scope:** AI-led and AI-written research and other scholarly artifacts accepted into the research-artifacts collection.

This is our **collection's publication policy**, not a journal accreditation, an external scientific standard, or a claim that AI-generated research has passed independent expert review. It becomes the operative published edition when specifically approved and released. The copy in private staging is a candidate, not a publication.

### The principle

**Publish the work itself, the evidence supporting its stated scope, and a permanent record of the exact edition.** Don't borrow credit, invent reviews, conceal meaningful failures, or confuse file integrity with scientific truth.

### Three levels of obligation

| Level | Meaning |
|---|---|
| **Required** | The edition is not release-ready without this, or without an explicit, justified nonapplicability decision where specified. |
| **When applicable** | Required when that kind of research or artifact depends on it. |
| **Optional witness** | Adds preservation, dating, or independent checking; must be reported accurately but is **not** a publishing gate. |

## The eight publication essentials

| Essential | Reader's question | Required release material |
|---|---|---|
| 1. **The claim** | What exactly is asserted? | Plain explanation, formal or precise statement, assumptions, limitations and relevant prior work. |
| 2. **The artifact** | Where is the actual work? | The finished native artifact plus shareable source and material needed to inspect it. |
| 3. **The people and agents** | Who actually did what? | Research authors, AI systems, human handlers, implementers, reviewers and publisher named by their real roles. |
| 4. **The evidence** | What was checked, by whom, and how? | Scoped review/check reports, actual receipts and meaningful negative results or explicit unassessed status. |
| 5. **Reproduction** | Can I inspect or rerun the work? | Methods, versions, dependencies, commands, source maps and declared missing inputs. |
| 6. **Rights and privacy** | May this be shared? | Permission and component-specific licenses, privacy screening and derivative disclosure. |
| 7. **Exact edition** | Which bytes am I looking at? | Stable versioned directory, complete inventory, SHA-256 checksums and Git commit/tag identification. |
| 8. **Immutable release** | Can the record be frozen and independently checked? | A published GitHub Release with immutability confirmed, pinned tag/commit, complete standalone ZIP attachment, and read-back verification. |

**Human specialist peer review is not a universal prerequisite.** A manuscript may be published for criticism or independent review, provided its status is unmistakable. A Lean build, AI review, or passing test is not human peer review.

## 1. Claim, originality and limitations

A release **must** describe its claim at the level supported by the actual evidence. Include hypotheses, definitions and exclusions. Attribute earlier literature and distinguish new contributions from adaptations, rediscoveries or already-established results. Do not turn a finite experiment into a universal theorem or a model-generated argument into an automatic novelty claim.

Where useful, explain the research in ordinary language without weakening the technical version or overstating the result.

## 2. Actual source, not a promise to regenerate it

The **exact artifact itself** must be in the edition or in an intentionally declared external supplement with real access information, checksum, rights and limitations. A script, citation to a temporary attachment, or a note saying the PDF *can be regenerated* is not preservation of that PDF.

Include, when applicable:

- Paper or report, complete editable manuscript and build inputs.
- Data plus schema, units, provenance, transformations and exclusions.
- Source code, pinned dependencies/toolchain, commands and outputs.
- Formal proof files, named theorem entrypoints, axiom/dependency reports and version pins.
- Figures plus underlying values/geometry, renderers, captions and accessibility descriptions.
- Supporting source map, review reports, original checks and research-history records necessary to evaluate the claims.

Include honest failed checks, abandoned methods and superseded evidence when they materially inform the published result. You may curate a public subset, but disclose important exclusions instead of rewriting history.

## 3. Attribution is role-specific

Name contributors for **what they actually produced**. Distinguish research authorship from financial support, account ownership, messaging, project administration, human handling and publication approval. A provider's model is not automatically the author, and an AI agent's named identity need not be identical to its underlying model version.

The Safe Cuts edition identifies **System** as AI author, **Summer Bee** as human coordinator and publication steward, and the distinct Forge, Codex, Opus and Claude Code contributions. Summer's coordination does **not** claim mathematical authorship or expert verification.

State AI participation directly and preserve the names and roles needed for attribution. Do not invent a human coauthor to satisfy expectations, or inflate a coordinator into a mathematician.

## 4. Evidence is bounded, never a seal of truth

For each significant check, supply: **subject/version/file identity, examiner or tool, method, relevant environment, outcome, coverage, date, artifacts/receipts, and limitations**. Distinguish author self-review, separate AI review, human expert review and machine checks.

| Evidence | Supports | Does not establish by itself |
|---|---|---|
| File checksum | Those file bytes match the recorded digest | Mathematical/scientific correctness |
| Test or numerical certificate | Specified cases and checker assumptions | Unchecked inputs or a general theorem |
| Formal proof build | Named declarations checked against the formal system's definitions | Equivalence to the intended informal mathematical claim |
| Reproduced figure/PDF | Rendering/build outcome | Truth of the depicted research |
| AI review | The reviewer's stated scope | Human expert assessment |
| Human review | The actual specialist's stated assessment | Universal acceptance or proof of every claim |
| Immutable GitHub Release | A protected release tag and assets | Validity, novelty, priority, or an independent external timestamp |

A changed input requires newly scoped checks before claiming its old tests still certify it. Never retitle, rewrite or silently replace historical verification receipts.

## 5. Privacy and reuse

Screen **all** proposed public files and names, including hidden Markdown comments, correspondence, transcripts, PDF/image metadata, private paths, account IDs and credentials. Correspondence is not public merely because it informed a scientific project.

Preserve private originals. When sanitizing copies for publication, record the changed bytes and maintain an appropriate private original-to-derivative mapping. If a check pinned the original, the included derivative must be distinguished and any necessary recheck recorded as a **new event**. A scan saying "no matches" is not a full privacy guarantee.

State rights by component, including third-party restrictions. **Do not assume the Safe Cuts licensing choice applies automatically to future packages.** Record permission to publish and reuse, attribution requests, changes and exclusions.

## 6. The core release format

Place each edition in a stable, standalone directory, such as:

    research-artifacts/
      [work-slug]/
        v1.0/
          README.md             What it is, what it claims, review status
          article/              Actual paper and sources, when applicable
          formal/               Formal source, when applicable
          data/                 Data and method records, when applicable
          code/                 Implementation, when applicable
          evidence/             Real check results, when applicable
          figures/              Actual media and supporting source, when applicable
          REPRODUCTION.md       Or another clear methods/recheck guide
          citation.txt          Version-specific citation
          RIGHTS.md             Component rights and exclusions
          INVENTORY.tsv         The real included-file inventory
          SHA256SUMS            Hashes of included files other than itself

The arrangement is adaptable to research type. Do not manufacture empty folders, data, figures, or "verified" assessments to meet an example tree.

For a complete edition, **require**:
- A whole-tree inventory that identifies all actual files; check for **extra** files as well as missing ones.
- SHA-256 entries for all files **except the checksum file itself**, in a documented relative-path format.
- A successfully checked release candidate, including relevant internal links and file/media types.
- A separately produced **standalone ZIP containing only that edition**, not merely GitHub's automatic whole-repository source ZIP.
- Verification of the ZIP after extraction against the candidate's inventory and checksums; record its SHA-256 and size.
- An exact proposed tag and target commit; no branch-name-only claim of permanent identity.

**Versioning:** once released, never overwrite or silently edit that edition. A changed manuscript, source, figure, metadata, checksum, or license becomes a new edition with renewed checks. Attach later dated reviews or notices separately when the frozen edition itself need not change. Do not rewrite an old failure or false claim away.

## 7. Immutable GitHub Releases are required

For each research edition:

1. **In private**, finish and verify the release candidate, standalone ZIP, rights, attribution, and proposed collection-index change. Finalize the exact bytes **before** asking for approval.
2. **Approval:** the named human publication authority approves the exact candidate bytes, intended public paths, rights, index change, release tag, attached ZIP and the rule that the tag will target the newly verified publication commit. The commit SHA cannot be known until the approved public commit actually exists. A generated approval card is a proposal, not permission.
3. **Commit approved bytes** to the public collection only as authorized. Verify the public commit tree against the candidate before releasing it.
4. **Create a GitHub Release draft** targeted to the newly verified publication commit, with a descriptive, edition-specific tag and clear review status. Attach the verified, edition-only ZIP **while still a draft**. A separate PDF attachment is useful but optional.
5. **Publish the release with repository release immutability enabled.** GitHub must report the release as immutable and the tag must point to the exact approved commit. A release draft, ordinary folder on main, or a plain tag alone is not the completed preservation gate.
6. **Read back the public result.** Check release status, immutable flag, tag target, asset names/sizes and asset digests; verify the archived ZIP against the approved contents. Record the actual release time and immutable GitHub URL. Report any failure or step still pending instead of claiming success.

A GitHub Release tag identifies an **entire repository commit**. This is expected in a multi-paper collection. The separate ZIP makes *that one research edition* easy to download. Later additions to main do not change the existing release tag.

GitHub's immutable feature protects the tag and its attached release assets. It does not prevent new commits on main, fix the scientific result, make mutable release notes immutable, or provide independent long-term preservation. Do **not** attach or alter files after publication; finalize attachments in the draft. Prefer commit- or tag-pinned links over moving main links in release notes.

**Practical safety rule:** A research-preparation agent must not publish merely because the files pass checks. In environments without tested credential-separated publishing controls, let the authorized human operate GitHub's final public actions. Every public commit, release, asset upload, archive submission or website deployment needs the appropriate explicit approval. Do not set up autonomous publishing as an implicit side effect of reading this standard.

## 8. Optional independent witnesses

These are useful layers, **not prerequisites**. An agent may recommend them, but may perform them only when separately authorized. Missing means missing, not failed scientific research.

| Optional measure | What it adds | Claim only after |
|---|---|---|
| **OpenTimestamps** | External timestamp evidence for an exact digest, if independently verified | Authentic client-created proof and actual verification; pending is not confirmed |
| **Software Heritage** | External source snapshot, where eligible | Actual capture and inspected source coverage |
| **Wayback Machine** | Archived web page/notice | Actual archived URL and known page scope |
| **Independent backup** | Recovery if GitHub is unavailable | Real separate stored copy plus integrity test |
| **Additional expert review** | Another scoped assessment | The actual review has been completed |
| **DOI or other identifier** | Easier scholarly citation/discovery | Identifier actually registered, not merely requested |

A witness may be added after publication as a **separate, dated record** bound to the immutable edition and its digest. Do not insert it into the already frozen ZIP, tag or edition. Later witnesses do not retroactively prove an earlier timestamp. Any request to post a witness or updated notice to public GitHub is itself a public change requiring approval.

## 9. Public example: Safe Cuts v1.1

Our first completed edition is [Safe Cuts for Two-Rim Convex Bands, publication edition 1.1](https://github.com/hi-im-human/research-artifacts/tree/7ae2208b6378d2799130e4fd1213076a35297d72/safe-cuts/v1.1). It has:

- **602 actual files** in its exact edition tree, **601** root checksum entries, and **600** inventory rows.
- A published immutable release, [safe-cuts-v1.1](https://github.com/hi-im-human/research-artifacts/releases/tag/safe-cuts-v1.1), with immutable status reported by GitHub as **true**.
- Tag and source commit: **7ae2208b6378d2799130e4fd1213076a35297d72**.
- A curated **safe-cuts-v1.1.zip**, 5,557,007 bytes, with GitHub-reported SHA-256 **2c802f665ae78519695a9e26287b034e3f6bfc33107694baa05b2e95461be031**.
- The actual 23-page PDF, Lean project, Geometry Lab, supporting arguments, AI reviews, named build/test results and source maps.
- Explicit disclosure that **no human specialist review of the completed proof is recorded**.

The original research edition was published on **9 October 2026**. Its immutable GitHub Release was published later that evening (GitHub API: 2026-10-10 01:57:02 UTC). The release date must not be backdated to pretend the immutable lock preceded the original upload.

**Postrelease ZIP verification, completed 9 October 2026 (US Eastern).** System examined the user-supplied copy of `safe-cuts-v1.1.zip` and verified that its **entire SHA-256 matched GitHub's published release-asset digest** shown above. The archive's internal CRC checks passed; its 602 files and 85 internal folders were accounted for; **601/601 checksums** and **600/600 inventory entries** matched; no extra or missing file paths were found. The included `SHA256SUMS` also matched the exact published Git blob, and the PDF matched its recorded SHA-256.

The check read ZIP members in memory, not by writing an extracted tree to disk. The exact audit script and raw PASS result are preserved in private research records. This was an **author-side packaging/integrity check**, not independent human review of the mathematics, a new Lean build, or an external timestamp. GitHub's binary asset was not downloaded directly through the connector; matching its entire public SHA-256 binds the user-supplied bytes to that release asset.

## 10. Publication decision

A candidate becomes releasable when all **required** gates have evidence and an authorized human has approved the exact final public operation. Every optional witness may remain "not done."

For step-by-step agent preparation and final verification, see [SKILL.md](SKILL.md) and [CHECKLIST.md](CHECKLIST.md).

**Do not confuse:**
- "ready for a human publication decision" with "published";
- "included and checksum-matching" with "mathematically validated";
- "immutable GitHub Release" with "independently archived forever."

### References
- [Research-artifacts collection](https://github.com/hi-im-human/research-artifacts)
- [Safe Cuts v1.1 immutable release](https://github.com/hi-im-human/research-artifacts/releases/tag/safe-cuts-v1.1)
- [GitHub release immutability documentation](https://docs.github.com/en/code-security/concepts/supply-chain-security/immutable-releases)
