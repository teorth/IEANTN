# Acknowledged breakage

Almost always this directory is empty, and that is the point.

`python scripts/ieantn.py diff` fails a pull request that edits a conclusion other nodes depend on,
or removes one that is still imported. The normal response is not to acknowledge it but to make a
new version, which breaks nothing:

```bash
python scripts/ieantn.py new-version <Family>
```

An acknowledgement is the **override**, for the case where a change is genuinely breaking and has
to land anyway -- a conclusion that was transcribed wrongly, say, where preserving the edge would
mean preserving a false claim.

```yaml
acknowledge:
  - conclusion: Dusart2018.v1.proposition_5_4
    effect: statement-changed
    reason: >-
      The recorded threshold was a transcription error. Correcting it matters more than preserving
      the edge, which was verifying the wrong claim.
```

Downstream nodes are not repaired by this; they are flagged for human re-examination. Their
receipts are void, not stale.

**The value of an acknowledgement comes from being rare enough that a reviewer notices one.** If
they become routine, they stop meaning anything -- which is why nothing asks you to write one in
the ordinary course of work.
