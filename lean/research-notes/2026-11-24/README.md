# Checked auxiliary geometry and cover facts

These are **research notes on a fork**, not an accepted P-vs-NP contribution and not a proof of any complete desk assignment. No upstream pull request is associated with this directory.

## Contents

`Plane13.lean` checks three finite facts for the cyclic projective plane of order 3, with lines `t + {0,1,3,9}` in `Fin 13`:

- every line has four points;
- two distinct lines meet at exactly one point;
- the complement of every line satisfies the explicit `admissible` predicate in the file (the F01 promise used by the overnight L-meta-1580 task).

`Plane21.lean` checks seven facts about the explicit 42-vertex, 105-edge bipartite incidence graph used by L-meta-1477:

- 21 disjoint diagonal edges form a matching;
- every vertex cover has at least 21 vertices;
- the edge list has length 105;
- consequently `125 ≤ edges.length + T.card - 1` for every vertex cover `T`;
- every pair of distinct left vertices has exactly one common right neighbour;
- every left endpoint is below 21;
- the left side itself is a vertex cover of size 21.

The numerical cover-cost expression is **not** a lower bound on arbitrary circuits: no theorem here converts a circuit to a cover at that cost. Likewise, the 13-point geometry does not establish the requested multi-output mixed-AND/OR lower bound. Those structural bridges remain open in these notes.

## Verification

Checked using Lean **4.36.0** and the repository's Mathlib pin **fc4f59e577feb1a4956671bc04ac18aaaf8cd842**. All ten statements are proved without `sorry`, extra axioms or native-backed decision tactics. The actual dependency audits contain only `propext`, `Classical.choice` and `Quot.sound`, or no axioms.

After installing the pinned Lean toolchain and fetching the Mathlib cache:

```sh
cd lean
python3 research-notes/2026-11-24/verify.py
```

The script compiles both complete sources in temporary files, audits every named statement, rejects nonzero compiler exits and disallowed axiom dependencies, and records source SHA256s in `verification.json`. It terminates the exact compiler process group on timeout. The `.audit.log` files and `verification.json` are real execution output, not illustrative samples. The compiler path in the script reflects the existing local user installation and can be adapted to another installation.

These statements originated during the bounded overnight experiment of 24 November 2026 and were repackaged under descriptive namespaces and rechecked during the authorised follow-up hour. The prior native-backed Petersen diagnostic was deliberately excluded.
