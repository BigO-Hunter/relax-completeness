# capped-relax-sssp

Capped-relaxation SSSP engine (Lean 4): the implementation artifact for the fair-schedule
capped point-relaxation — companion to `relax-completeness`, whose `DESIGN.md` specifies this
engine (`AsyncState = (d, U, B, P)`, echo-sweep, re-settlement) together with the
beyond-dijkstra `dB[D] ≥ B′` cut-set certification.
Construction: ours — darkhipo swarm, AI-assisted, disclosed.
Status: engine not yet implemented; the spec is `relax-completeness`'s async engine plus its
beyond-dijkstra certification. **This repo is an engine spec and archive, not a race entry.**
It carries no `Race.bound` row for the directed-SSSP board, and no row can come from this
construction family: the theory has no schedule-length theorem (`converge_of_stable` takes
`N` as a hypothesis; `exists_eventuallyConstant_of_antitone` and `healing_of_*` give an
existential `N` with no formula), no cost or machine model, and no liveness theorem, so it
yields no `(D ; T)` at all. Its ceiling is the board's *classic baseline*: with the boundary
`B` existential the settlement rule collapses to Dijkstra extract-min, and the single strict
win in reach (one log below `n log² n` at `D = n log n`) is Fredman–Tarjan 1987 — a heap
theorem that owes nothing to the relaxation theory. Verdict, bar tables and the
missing-lemma inventory are in the read-only probe `CAPPED_RELAX_PROBE.md`
(2026-11-08; campaign notes, not in this repo).
Its real value is the safety layer, and it is exact: `LookaheadBoxed` is a soundness condition
for out-of-order settlement, proved **both** directions — `certified_settled_final_async`
(every legal settle with the box admits the final answer) against
`certification_fails_without_lookahead` and `cex_lookahead_violated` (drop it and a legal
settle is wrong) — with `healing_of_*` covering the no-lookahead case under edge fairness.
That is what parallel, GPU and Δ-stepping sweep engines need before they settle optimistically
and un-settle; it is robustness, not speed.
It is not redundant with `sssp-n2`, which is the CSR O(n²) construction (see topics `sssp`).
Pins: leanprover/lean4:v4.34.1, Mathlib d13f23b.

---

## Why this repo is up

Public design input: the engine spec, its exact two-direction soundness layer, and the honest verdict on what this construction family cannot yield — so nobody re-derives the dead ends.

[BigO-Hunter](https://github.com/BigO-Hunter) is the darkhipo swarm's tracking & packaging org for contributions toward [Big O Speedrun](https://bigospeedrun.com) — a companion, never the project. Org story: [profile](https://github.com/BigO-Hunter/.github) · [bigo-hunter.github.io](https://bigo-hunter.github.io).

## What work can be done here

The open build list is the design's own missing pieces: a schedule-length theorem (`converge_of_stable` takes N as a hypothesis), a cost/machine model, a liveness theorem — then the engine implementation. The exact soundness layer (`LookaheadBoxed`, both directions) is proved and reusable now.

## License

Licensed under the Copy-Free/Stays-Free (CFSF) License — see [LICENSE](LICENSE). CFSF: copy-free (use for any purpose) and stays-free (nobody may fence this work). The name is unclaimed in software licensing (checked 2026-11-09) and is deliberately not "Copyfree" — the Copyfree Initiative's certification mark — since CFSF's anti-enclosure condition is excluded by their standard. 
