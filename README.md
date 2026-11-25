# Section 5 of "Explicit estimates in IUT" in Lean 4: the numerical argument, with its inputs as hypotheses

This repository contains two independently written Lean 4 / Mathlib formalizations of the numerical argument of §5 of

> S. Mochizuki, I. Fesenko, Y. Hoshi, A. Minamide, W. Porowski, *Explicit estimates in inter-universal Teichmüller theory*, Kodai Math. J. 45 (2022).

We formalize the rational numerical argument through Corollary 5.8. Page numbers refer to the [authors' 18 May 2022 PDF](https://www.kurims.kyoto-u.ac.jp/~motizuki/Explicit%20estimates%20in%20IUTeich.pdf). Everything is specialised to the base field ℚ (`d = 1`, `δ = 552960`).

## What is proved, and what is assumed

The formalizations prove the following implications:

```
explicit prime number theorem bound  +  per-curve inputs of Corollary 5.2
   ⇒  Theorem 5.3 (i) over ℚ, for every 0 < ε ≤ 1
         ⇒  Theorem 5.4 over ℚ
         ⇒  Theorem 5.3 (ii) over ℚ  ⇒ (at ε = 1)  Corollary 5.8:
               x^p + y^p ≠ z^p for positive integers x, y, z and every prime p > 1.615·10^14
```

Theorem 5.3 (i) gives two consequences, Theorem 5.4 and Theorem 5.3 (ii). At ε = 1, the latter yields Corollary 5.8.

**Everything before the first arrow is a hypothesis, not a theorem.** The hypotheses are:

1. **The explicit prime number theorem bound** of Proposition 2.2 (ii) (p. 22), which the paper takes from Rosser–Schoenfeld. The Claude formalization assumes only its lower half; the GPT formalization assumes both halves.
2. **For each curve `E_{a,b,c}` of Theorem 5.3, the inputs that the proof of Corollary 5.2 (pp. 36–43) imports.** These are:
   - local height data (Remark 1.10.1): the height as a sum of local terms over the places of a number field `F`, with the total degree bound `[F : ℚ] ≤ δ` and the fibre bound `Σ_{v|q} f_v ≤ [F : ℚ]` on residue degrees for each rational prime `q`;
   - Corollary 1.14 (iii) (the bound on the height when there is an `l`-cyclic subgroup scheme);
   - Proposition 2.1 (the four exceptional `j`-invariants). In the Claude formalization it enters only as the condition `j ∉ excJ` of the Theorem 5.1 input; the GPT formalization has a separate core predicate;
   - Theorem 5.1 (p. 34). Claude assumes the Theorem 5.1 inequality for every prime satisfying (P1)–(P5) when the curve's `j`-invariant is outside the exceptional set. GPT assumes its inequality for every natural number `l ≥ 10^15` for which the initial-Θ-data predicate holds. Both proofs apply the input at the prime they select;
   - GPT only: implications for the Galois image (P6) and for the existence of initial Θ-data (P7), represented by predicates. Claude assumes the resulting numerical inequality of Theorem 5.1 directly;
   - an assumed comparison `B ≤ log rad(a, b, c)` of a numerical divisor term `B` with the radical.

   They are stated as Lean propositions about numbers and predicates (local heights, residue degrees, primes, predicates standing for cyclic subgroup schemes, and real numbers standing for the divisor terms). They are not derived from the geometry of the curve.

**Theorem 5.1 is the result of inter-universal Teichmüller theory used in §5.** It is assumed here, not proved. This repository takes no position on the correctness of inter-universal Teichmüller theory. What it checks is narrower: given its inputs, the numerical argument of §5 is correct, and it yields the explicit constants stated in the paper.

What is proved in Lean (both formalizations, with differences listed below):

- at large height, the proofs bound the excluded set (S1)–(S3) and select a prime outside it satisfying (P1)–(P3), using the prime number theorem bound;
- the numerical forms of (P4) and (P5) for the supplied data;
- Claim 5.2A (for `d = 1`) and Claim 5.2B;
- from (P8), `h/6 ≤ (1 + ε)·B` for the numerical divisor term `B`. The assumed comparison `B ≤ log rad` then gives the rational-triple bound used in Theorem 5.3 (i). The geometric log-different and log-conductor functions in the paper's (C2) are outside this formalization;
- the case split at `h₁(ε) = 3.4·10^30·ε^(-166/81)`, giving Theorem 5.3 (i) over ℚ;
- Theorem 5.3 (i) ⇒ (ii), and (i) ⇒ Theorem 5.4 over ℚ;
- Lemmas 5.5, 5.6 and 5.7, and Corollary 5.8 from Theorem 5.3 (ii) with `ε = 1`.

What is **not** established:

- Theorem 5.1 and the other per-curve inputs are not proved. Nor is it proved that they hold for every curve `E_{a,b,c}`.
- The prime number theorem bound is a known theorem, but it is not proved in Lean here.
- The per-curve numerical inputs have individual models, including GPT models above every real height bound (see "Non-vacuity checks"). The active-prime example additionally assumes the prime number theorem bound. It is **not** shown in Lean that the universally quantified hypotheses hold, or even that they are consistent.

The conclusion of Corollary 5.8 is a special case of Fermat's Last Theorem, so it is not new. The interest here is the explicit chain from the stated inputs, and a machine check of the numerical constants of §5. In the parts we formalized, we found no numerical discrepancy with the paper.

## Two independent formalizations

| Folder | Written by | Main theorems |
|---|---|---|
| `formalization/claude/` | Anthropic Claude | `ExpEst.thm53i_of_inputs`, `ExpEst.cor58_of_inputs` (in `ExpEst/L3Main.lean`) |
| `formalization/gpt/` | OpenAI GPT (via Codex) | `ExpEstL3.theorem53i`, `ExpEstL3.corollary58` (in `ExpEstL3.lean`) |

The two teams prepared separate implementations in three stages: first Lemmas 5.5–5.7 and Corollary 5.8, then Theorem 5.3 (i) ⇒ (ii) and Theorem 5.4, then the inputs ⇒ Theorem 5.3 (i). At each stage, each side wrote its first version without seeing the other's code. They compared the first-stage versions before starting the second stage, and cross-reviewed the first two stages before starting the third (see "Checks").

They state the same chain, but they model the inputs differently.

| | Claude | GPT |
|---|---|---|
| Prime number theorem | lower half `θ(x) ≥ (1 − 0.00071)x` for `x ≥ 10^15` (`PNT_lower`). The upper bound `θ(x) ≤ 2x` used in (S1)–(S3) is proved from Mathlib's `primorial_le_four_pow`. | both halves, `abs(θ(x) − x) ≤ 0.00071x` for `x ≥ 10^15` (`PrimeEstimate`) |
| Per-curve inputs | one proposition `Cor52Input h R j` (place data, a predicate for "`l`-cyclic subgroup scheme", the bound of Corollary 1.14 (iii), and Theorem 5.1 at the primes satisfying the selection conditions, with the divisor term bounded by `R = log rad(a, b, c)`). `Sec5Inputs` asks for it for every curve `E_{a,b,c}`. | a structure `External D M` with seven fields: height identity, core criterion (Proposition 2.1), cyclic-height bound, Galois image, existence of initial Θ-data, divisor comparison, and Theorem 5.1 in the form `C_Θ ≥ −1` |
| Galois image and initial Θ-data, (P6) and (P7) | not separate hypotheses; only the resulting Theorem 5.1 inequality is assumed | separate fields |
| Theorem 5.1 constant | the rounded inequality with `4.0881` (p. 40) | the `C_Θ` form; `4.08803 → 4.0881` is proved |
| Exceptional set | lists the four exceptional `j`-values and splits at `h < h₁(ε)` and `h ≥ h₁(ε)` | also constructs the finite set of rational Legendre parameters at or below the height cutoff |
| Theorem 5.3 (i) | first displayed inequality `h/6 ≤ max((1 + ε)·log rad, h₁(ε)/6)` (the second display follows from it) | both displayed inequalities |

Where the formalizations take a shorter route than the paper:

- **Claude:**
  - The intermediate constant `1.4621` is not used; `l ≤ 1.464·δ·h^(1/2)·log(1.45·δ·h)` follows directly from `log(1.45·δ·h) ≥ 82`.
  - (P5) is proved from `log l < h^(1/2)` instead of the paper's function `f(h) > 0`.
  - Theorem 5.3 (i) ⇒ (ii) and Theorem 5.4 are proved through the divisibility relation `(abc)² ∣ 2^8·den(j)` for a primitive integer triple, instead of Claims 5.3A–C.
- **GPT:**
  - It uses the intermediate constant `1.4621`, the function `f(h)`, and rational-coordinate forms of Claims 5.3A–C. Its proof of Theorem 5.4 bounds the product of the three coordinates directly.

## Checks

- Both formalizations build from an empty `.lake/build` with no errors and no warnings.
- `#print axioms` of every main theorem reports only `propext`, `Classical.choice` and `Quot.sound`. Neither formalization uses `sorry`, `admit`, `axiom` declarations, `native_decide`, `implemented_by`, `@[extern]` or `unsafe`.
- Each formalization was reviewed by an AI reviewer of the other side. The review covered:
  - the build;
  - the faithfulness of each hypothesis to the paper (same, weaker, stronger, or not in the paper);
  - what is proved and what is assumed;
  - non-vacuity;
  - whether the comments match the code.

  The review found inputs of the Claude formalization that asked for more than the paper uses: Theorem 5.1 at primes outside the selected range, and one divisor term common to all primes. They were weakened to what the proof uses. The review also found overstatements in comments and notes on both sides, and they were corrected. The remaining findings in the re-review of the first two stages concerned Lean docstrings and the project notes. Both were corrected, and there was no further formal re-review of those edits. The final re-review of the third stage passed all three items it rechecked.
- Rational coefficient comparisons (`71.82`, `35.91`, `5.985`, `1.464`, `4.0881`, `1 − 10^−7`, `10^8`, `4·10^12`) were also checked exactly. Values involving logarithms or square roots were also spot-checked at high decimal precision.

### Non-vacuity checks

- **Claude** (`ExpEst/L3Audit.lean`):
  - `Cor52Input` holds for the actual curve `E_{1,1,−2}` (`j = 1728`, height 0).
  - Its hypotheses, together with `h ≥ h₁(1)` and `j` outside the exceptional set, are jointly satisfiable by an abstract instance (not a curve).
  - `ExpEst/Audit.lean` and `ExpEst/L2Link.lean` check that the hypotheses of the first two stages hold at small heights.
- **GPT** (`Witnesses.lean`):
  - For every real `B`, there are an actual rational triple with height `> B` and numerical data satisfying `External`. This is proved without the prime number theorem.
  - `active_example`: given `PrimeEstimate`, a selected prime and the initial-data predicate exist at the same time.

None of these checks shows that the inputs hold for every curve.

## Building

Requirements: [elan](https://github.com/leanprover/elan) and git. Lean `v4.32.0`, Mathlib `v4.32.0` (commit `81a5d257c8e410db227a6665ed08f64fea08e997`).

```
cd formalization/claude
lake exe cache get
lake build
```

and the same in `formalization/gpt`. `lake exe cache get` downloads the prebuilt Mathlib files. The `#print axioms` outputs appear in the build log. For Claude they come from `ExpEst/Audit.lean` and `ExpEst/L3Audit.lean`. For GPT they come from `ExpEst.lean`, `ExpEstL2.lean`, `ExpEstL3.lean` and `Witnesses.lean`.

`MANIFEST.sha256` covers every distributed file except itself. Its digests refer to LF bytes; `.gitattributes` keeps LF line endings on checkout.

## Roles of the AI tools

- The two formalizations were written by AI models: Anthropic Claude (`formalization/claude/`) and OpenAI GPT via Codex (`formalization/gpt/`).
- Each model reviewed the other's code, and Claude coordinated the work.
- The author chose the problem, directed the work and decided what to publish.
- The author is not a specialist in arithmetic geometry or inter-universal Teichmüller theory.
- The formalizations have not been checked by a human expert.

Hirotaka Shimizu
