# Checked auxiliary geometry and cover facts

These are **research results on a fork**, not accepted P-vs-NP contributions. They contain 24 auxiliary statements and one complete locally Lean-checked refutation of the overgeneralised desk statement L-meta-3316. That refutation is not a proof or disproof of P vs NP, nor of the fixed Heawood-graph circuit conjecture. No upstream PR for the refutation has been opened: no matching negated twin was found in the public desk snapshot, and the original live lease ended with HTTP 410.

## Contents

### Complete local refutation: L-meta-3316

`Refute3316.lean` proves the **exact negation of the original task statement**, included verbatim in the final theorem. `statement-3316.json` preserves the task text and its SHA256 without any lease token. The final theorem is audited in `Refute3316.audit.log`.

The task quantifies over *every* predicate on fourteen Boolean inputs. Choose the predicate whose only satisfying assignments have masks **127, 244 and 432**. These three assignments are pairwise incomparable in the pointwise Boolean order, so all three are minimal satisfying assignments. Every permitted pair in the task starts with one of these three. The task requires the two selected wire values to differ at that first assignment; their AND is therefore false. But its minimal-input condition requires that same AND to be true. This contradiction is formalised without any extra axioms or native-backed decision tactic.

The defect is the universal predicate quantifier in this child statement. **The original fixed-graph problem and the earlier Petersen circuit-size transfer remain open here.** A full local refutation is not the same as project acceptance. The project requires a posted negated twin for a counterexample submission; none was available in the checked desk snapshot. The positive L-meta-3316 target must not be silently replaced by its negation in an upstream PR.

### Auxiliary results

`PetersenResidual.lean` proves the exact function identity obtained by fixing input/vertex 4 to false in the nine-input Petersen-minus-one-vertex edge function and relabelling the remaining eight inputs. This was kernel-checked on all 256 residual inputs during the second follow-up hour. It links the task to the already published eight-input lower-bound certificate, but **does not prove the required circuit-size transfer or the new task's lower bound**.

`Incidence.lean` adds seven general geometry and counting lemmas, valid for arbitrary finite incidence structures satisfying their explicit hypotheses. In particular, an all-incidence rectangle must be a star (one side has at most one vertex), and any rectangle cover has total endpoint cost at least `N*k` when every line has `k` incident points. This establishes a genuine combinatorial half of a possible circuit-bound argument. **Extracting such a cover with a suitable cost bound from an arbitrary circuit remains unproved.** No circuit lower bound follows here without that bridge.

`PlaneCircuit64.lean` defines the explicit 64-gate monotone baseline for L-meta-2625. Four checked statements establish its permitted gate basis, its size, one concrete positive input and **all 52 incident-pair inputs**. These facts do not meet the task's 63-gate bound. The full negative-boundary proof was not completed within the verification time limit and is not included as a Lean theorem.

`local_search.py` independently checks this same baseline against all 676 listed tests (520 distinct inputs), including the 624 generated negative tests. It also checks 277,806 sole-use child/parent contractions without finding a 63-gate candidate. This is **only a local neighbourhood**, not an exhaustive circuit search, a nonexistence proof or a Lean-checked negative-boundary certificate. Actual output and the program SHA256 are in `local-search-result.json`.

`Matching.lean` adds two reusable results proved during the follow-up hour, rather than by finite enumeration:

- any set meeting every edge of a finite vertex-disjoint matching has at least as many elements as that matching;
- the specialisation to `n` disjoint pairs in two consecutive natural-number blocks.

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

Checked using Lean **4.36.0** and the repository's Mathlib pin **fc4f59e577feb1a4956671bc04ac18aaaf8cd842**. All twenty-five named statements (24 auxiliary results and the exact refutation) are proved without `sorry`, extra axioms or native-backed decision tactics. The actual dependency audits contain only `propext`, `Classical.choice` and `Quot.sound`, or no axioms.

After installing the pinned Lean toolchain and fetching the Mathlib cache:

```sh
cd lean
lake build PEqualNP.Defs
python3 research-notes/2026-11-24/verify.py
python3 research-notes/2026-11-24/local_search.py
```

The verifier compiles all seven complete sources in temporary files, audits every named statement, rejects nonzero compiler exits and disallowed axiom dependencies, and records source SHA256s in `verification.json`. It terminates the exact compiler process group on timeout. The `.audit.log` files and `verification.json` are real execution output, not illustrative samples. The compiler path in the script reflects the existing local user installation and can be adapted to another installation.

These statements originated during the bounded overnight experiment of 24 November 2026 and were repackaged under descriptive namespaces and rechecked during the authorised follow-up hour. The prior native-backed Petersen diagnostic was deliberately excluded.
