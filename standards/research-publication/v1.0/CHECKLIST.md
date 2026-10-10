# Research release checklist
## A small checklist for a very real publication

This sheet complements [STANDARD.md](STANDARD.md). A checkbox is a **task**, not a certification; record exact paths/receipts in the preparation return. Optional external witnesses do not delay a complete core release.

### 1. Research and identity

- [ ] The claim, assumptions, known limitations and prior work are described without exaggeration.
- [ ] The complete primary artifact and applicable editable sources are present as **actual files**.
- [ ] AI author(s), human coordinator, implementers, reviewer(s) and publisher are accurately distinguished.
- [ ] Review status states what happened, what was not checked and whether human specialist review occurred.
- [ ] Important successful and failed checks have version-specific receipts; old evidence remains identifiable.

### 2. Technical and privacy checks

- [ ] Reproduction instructions, dependencies, data/schema and figures are included **where applicable**.
- [ ] Files, metadata, paths, correspondence, credentials and sensitive identifiers have been screened; changes from private originals are disclosed.
- [ ] Component-specific rights and permissions are stated.
- [ ] Edition files exactly match the inventory; missing **and extra** files checked.
- [ ] SHA256SUMS checks pass; package links and primary artifacts open correctly.
- [ ] A **standalone ZIP of only this edition** was created, extracted, verified against the inventory and hashed.

### 3. Approval and immutable release

- [ ] The human steward approves the exact candidate, rights, destination, index change, release tag, ZIP and the rule for selecting the verified new publication commit **before any public write**.
- [ ] Approved bytes are present in the intended public versioned folder and match the approved tree.
- [ ] GitHub release immutability is enabled in repository settings.
- [ ] A **draft release** names the exact target commit/tag and discloses the actual evidence/review status.
- [ ] The verified standalone ZIP is attached to the draft **before** publication. Separate PDF attachment is optional.
- [ ] The authorized human publishes; no unattended agent publication without separately tested, credential-separated controls.
- [ ] GitHub explicitly reports **immutable: true**; tag points to the approved commit, and all attachments/digests are correct.
- [ ] Public download and browser links work; actual release time and final link are recorded.

### 4. Optional, never silently claimed

- [ ] OpenTimestamps proof **if separately requested**.
- [ ] Independent source/web archive or backup **if separately requested**.
- [ ] Extra specialist review or registered identifier **if separately obtained**.

**A missing optional item does not block publication.** Record its status as not done; never create a fictitious proof or DOI.

### Approval summary template

    Proposed edition and research title:
    Private candidate / exact fingerprint:
    Primary files and standalone ZIP hash:
    Contributors and review limitations:
    Tests verified; tests not performed:
    Privacy changes and rights:
    Exact destination folder and collection-index changes:
    Release tag and verified-commit target rule:
    Optional witness instructions (if any):
    Human's explicit approval:
    Publishing outcome and verification receipts:

**Stop on:** changed/unapproved bytes, a missing critical artifact, unresolved sensitive disclosure or rights, false scientific or review claims, broken checksums, an unauthorized public action, or a published release that has **not** been confirmed immutable.

**Corrections:** preserve the old frozen edition, prepare a new version and obtain a new approval. An immutable GitHub Release protects release evidence; it does not correct scientific mistakes automatically.
