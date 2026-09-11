# Run in progress — Selection from Theorem.lean

> 2026-09-11T13:04:51.015Z · paper `unknown` · Lean project `lean`

## Done

| Milestone | Finished | Took |
| --- | --- | --- |
| Work out what the paper claims | 12:58:31 | — |
| Write the theorem into lean/, a file at a time | 12:58:31 | — |
| Design interface, instance, capstone | 13:04:50 | — |
| scaffold | 13:04:51 | — |

## Picking it up

Next would be **Pursue the proof autonomously**.

In the editor: the side bar offers it when a paused run is found, or run the command **Tex2Lean: Resume a paused run**.

From a script, by opening the editor's URI for this run:

```sh
# macOS
open 'vscode://kuldeepmeel.tex2lean4/resume?slug=selection-from-theorem-lean'
# Linux
xdg-open 'vscode://kuldeepmeel.tex2lean4/resume?slug=selection-from-theorem-lean'
```

Or read `.blueprint/run/selection-from-theorem-lean/checkpoint.json` directly — it is schema `tex2lean.checkpoint/1`, and `completed`, `next` and `briefs` are the fields that say what is left. A reader that does not recognise the schema string should stop rather than guess.
