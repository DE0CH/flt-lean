---
name: never-delete-deyao-audit-notes
description: "Never delete Deyao's in-file notes questioning Claude's work or flagging Claude errors — even after the issue is resolved; they are audit markers"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: ca2217f8-0566-4be1-935c-f410561d655f
  modified: 2026-07-21T16:28:52.791Z
---

Deyao 2026-07-21: if a note in a source file looks like Deyao wrote it and it involves Claude being wrong, or questions what a proof means/does (e.g. "(??? Claude says this means its uniqueness)", "Claude wrote this paragraph ... can't be sure"), never delete it — even if the surrounding issue has been fully resolved by later edits. This holds whether or not the note is wrapped in a `#deyao[...]` block; plain-text notes with this character get the same protection.

**Why:** the notes are Deyao's audit trail — placed so Deyao can go back later and re-check Claude's work at exactly the flagged spots. Deleting one destroys the pointer even when the fix is correct. (Incident: the model deleted the plain-text note "(??? Claude says this means its uniqueness)" in chapters/04-henriques.typ while renaming "determinacy"; Deyao required a verbatim restore.)

**How to apply:** when editing text adjacent to such a note, leave the note itself byte-for-byte intact, including any wording it quotes or refers to (restore the referent if renaming would orphan it, or leave the referent untouched). Resolving the underlying question happens in surrounding text or in chat — never by removing the note. When the flagged issue has been fixed or made irrelevant, it is helpful to add a `#claude[...]` note beside Deyao's note saying so (e.g. `#claude[Resolved: the term was replaced by the corollary @transformations-equal-at-generator]`) — the helper is defined in libs/template.typ (blue, "Claude:" prefix, parallel to `#deyao`). The pair then reads as question + answer, preserving the audit trail. Related: [[deyao-blocks-invisible]] (the `#deyao` policy in CLAUDE.md, which this extends to unwrapped notes).
