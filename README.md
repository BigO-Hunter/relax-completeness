# relax-completeness

Completeness theory for capped-relaxation SSSP (Lean 4 / Mathlib, pinned `d13f23b7`, toolchain v4.34.1): any fair schedule of capped point-relaxations converges to the canonical least fixed point.
Construction: ours — fixed four-pillar architecture (fair-schedule iteration, LFP characterization, soundness, async engine). AI-assisted (darkhipo swarm), disclosed.
Status: pillars proved through (iv) — "the lookahead box is the exact soundness condition". See `DESIGN.md`.

---

## Why this repo is up

Public design input: the completeness theory (four pillars, proved through (iv)) with DESIGN.md specifying the engine — the open theoretical work is documented for anyone to pick up.

[BigO-Hunter](https://github.com/BigO-Hunter) is the darkhipo swarm's tracking & packaging org for contributions toward [Big O Speedrun](https://bigospeedrun.com) — a companion, never the project. Org story: [profile](https://github.com/BigO-Hunter/.github) · [bigo-hunter.github.io](https://bigo-hunter.github.io).

## What work can be done here

Pillars proved through (iv). Open work: the remaining pillars — schedule-length and cost theorems the companion engine in `engine-spec/` needs; see DESIGN.md.

## License

Licensed under the Copy-Free/Stays-Free (CFSF) License — see [LICENSE](LICENSE). CFSF: copy-free (use for any purpose) and stays-free (nobody may fence this work). The name is unclaimed in software licensing (checked 2026-11-09) and is deliberately not "Copyfree" — the Copyfree Initiative's certification mark — since CFSF's anti-enclosure condition is excluded by their standard. 


## Umbrella layout

- Repository root: the four-pillar completeness theory and `DESIGN.md`.
- `engine-spec/`: the complete original `capped-relax-sssp` repository at source commit `ccfb9b7da08440eb73578b0c7bc477b59a3e70da`, merged with full history. This is the capped engine specification and safety analysis, not a separate race entry and not a claim of an implemented engine.

Build or audit each package from its own directory. The companion engine's remaining schedule-length and cost work stays open here rather than in a separate notes repository.
