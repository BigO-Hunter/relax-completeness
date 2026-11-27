# relax-completeness

Completeness theory for capped-relaxation SSSP (Lean 4 / Mathlib, pinned `d13f23b7`, toolchain v4.34.1): any fair schedule of capped point-relaxations converges to the canonical least fixed point.
Construction: ours — fixed four-pillar architecture (fair-schedule iteration, LFP characterization, soundness, async engine). AI-assisted (darkhipo swarm), disclosed.
Status: pillars proved through (iv) — "the lookahead box is the exact soundness condition". See `DESIGN.md`.

---

## What work can be done here

Pillars proved through (iv). Open work: the remaining pillars — schedule-length and cost theorems the companion engine in `engine-spec/` needs; see DESIGN.md.

## License

Licensed under the Copy-Free/Stays-Free (CFSF) License — see [LICENSE](LICENSE). CFSF: copy-free (use for any purpose) and stays-free (nobody may fence this work).

## Layout

- Repository root: the four-pillar completeness theory and `DESIGN.md`.
- `engine-spec/`: the capped engine specification and safety analysis (`capped-relax-sssp` @ `ccfb9b7da08440eb73578b0c7bc477b59a3e70da`).

Build or audit each package from its own directory.

---

[BigO-Hunter](https://github.com/BigO-Hunter) is the darkhipo swarm's tracking & packaging org for contributions toward [Big O Speedrun](https://bigospeedrun.com). Org story: [profile](https://github.com/BigO-Hunter/.github) · [bigo-hunter.github.io](https://bigo-hunter.github.io).