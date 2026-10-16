# Roadmap: ramification along divisors, purity of the branch locus, and Abhyankar's lemma

**Summary.** This roadmap builds the codimension-one ramification theory of finite morphisms of
Noetherian schemes and its two classical local theorems: Zariski–Nagata purity of the branch locus
(Stacks, Lemma 58.21.4 (0BMB)) and Abhyankar's lemma for a regular divisor (Stacks, Lemmas 58.31.5
(0EYG) and 58.31.6 (0EYH)). We want it because ramification of a finite morphism along prime
divisors is the basic invariant of branched covers in arithmetic and algebraic geometry, and the two
theorems are what make it controllable: purity says ramification of a finite cover of a regular
scheme is detected in codimension one, and Abhyankar's lemma says tame ramification along a regular
divisor is, étale locally, the ramification of a root of an equation of the divisor. Mathlib has
schemes, quasi-finite, unramified and étale morphisms, regular local rings and ramification indices
of ideals; Tau Ceti has codimension-one points, Weil divisors, places of function fields and the
regular-local-ring basics at this repository's pin, and finite étale schemes over a base on its
current `main` (see [Scope and ownership](#scope-and-ownership)). Neither has ramification of a
finite morphism at a prime divisor, finite étale covers of punctured spectra, or either theorem.

The roadmap has five layers, built from the ground up.

| Layer | Title | What it delivers |
|---|---|---|
| [0](#layer-0-local-algebra) | Local algebra | regular local rings modulo a parameter, ramification of extensions of a discrete valuation ring (unramified, tame, totally ramified), Kummer extensions of a DVR, DVR Abhyankar, the discriminant criterion, Cohen–Macaulay miracle flatness |
| [1](#layer-1-ramification-of-finite-morphisms-along-prime-divisors) | Ramification of finite morphisms along prime divisors | the induced map on codimension-one points, ramification index and residue degree at a prime divisor, the ramification and branch loci, the branch divisor, ramification in codimension one of a finite étale cover of a dense open |
| [2](#layer-2-finite-étale-covers-of-punctured-spectra) | Finite étale covers of punctured spectra | restriction to the punctured spectrum, purity for a local ring, finite normal algebras, reflexive extension, completion, the local Lefschetz extension theorem |
| [3](#layer-3-purity-of-the-branch-locus) | Purity of the branch locus | the flat case, purity for regular local rings, pointwise purity, extension of finite étale covers across regular complements and regular divisors |
| [4](#layer-4-abhyankars-lemma-for-a-regular-divisor) | Abhyankar's lemma for a regular divisor | standard tamely ramified covers, base change to the strict henselization, Abhyankar's lemma and the structure of the normalization |

```text
Mathlib + Tau Ceti  →  Layer 0  →  Layer 1  →  Layer 2  →  Layer 3  →  Layer 4
                          └────────────────────────────────────────────↗ (0.3, 0.4 feed 4.3)
```

The end theorems are `Scheme.Hom.etaleAt_of_unramified_codimOne` (purity, Tag 0BMB, §3.3), its
affine form `Algebra.isEtaleAt_of_purity` (§3.3), `finiteEtale_extend_of_regular_divisor`
(Tag 0EYE, §3.4), `abhyankar_regularDivisor` (Tag 0EYG, §4.3) and
`abhyankar_normalization` (Tag 0EYH, §4.4).

## Scope and ownership

**This roadmap owns** ramification of a finite morphism at a codimension-one point; the ramification
locus, branch locus and branch divisor of a finite morphism; the Stacks Project notions "unramified,
resp. tamely ramified, over `X` in codimension one" for a finite étale cover of a dense open; the
ring-level notions of an unramified, tamely ramified and totally ramified finite separable extension
with respect to a discrete valuation ring; Kummer extensions of a discrete valuation ring and DVR
Abhyankar; finite étale covers of the punctured spectrum of a Noetherian local ring and the local
Lefschetz theory of Stacks, Sections 58.19–58.20; purity of the branch locus; the extension of finite
étale covers across closed subsets with regular local rings; standard tamely ramified covers; and
Abhyankar's lemma for a regular divisor.

**Owned elsewhere and consumed here.** These objects have one owner; this roadmap uses them and
states comparisons where it introduces a related notion. It never builds a second carrier.

- *Codimension-one points, Weil divisors, places of a function field attached to a point of an
  integral scheme*: Tau Ceti `TauCeti.AlgebraicGeometry.CodimensionOnePoint`, `SchemeWeilDivisor`,
  `AlgebraicGeometry.Scheme.toPlace`, `TauCeti.Place.ramificationIdx`. §1.2 compares its
  ramification index with the place ramification index.
- *Effective Cartier divisors*: Tau Ceti `AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier`.
  A regular divisor in §3.4 and Layer 4 is an ideal sheaf `I` with `I.IsEffectiveCartier` whose
  subscheme `I.subscheme` has every local ring regular.
- *Finite étale schemes over a base*: Tau Ceti `TauCeti.FiniteEtaleScheme`, in the module
  `TauCeti.AlgebraicGeometry.FiniteEtale.Basic`. It entered Tau Ceti in #15694 (2026-10-13), after
  this repository's pinned Tau Ceti `a91d3aaf`, so it is available once the pin advances; until
  then `Suggested.lean` uses Mathlib's `MorphismProperty.Over (@IsFinite ⊓ @Etale) ⊤ S`, the same
  full subcategory of `Over S`. Every finite étale category below is `FiniteEtaleScheme S` for the
  relevant `S` (Stacks' `FÉt_S`, Section 58.5 (0BL6)), and every restriction functor is its
  pullback functor. [ModularCurves](../ModularCurves/README.md) Layer 0D develops finite étale
  schemes over a field and their Galois actions; it does not name this carrier.
- *Regular local rings*: Mathlib `IsRegularLocalRing`, `IsRegularRing`; Tau Ceti
  `TauCeti.IsRegularLocalRing.isDomain` (Stacks, Lemma 10.106.2 (00NP)), `quotient_span_singleton`
  (Lemma 10.106.3 (00NQ) for one parameter) and `isDiscreteValuationRing_iff_ringKrullDim_eq_one`
  (Lemma 10.119.7 (00PD)).
- *Regular schemes and their normality, regularity under étale maps, Serre's criterion*:
  [SchemeAndStackFoundations](../SchemeAndStackFoundations/README.md) §4.13 (`IsRegular`,
  `IsRegular.isNormal`, `IsRegular.of_etale`). §0.1 here proves the local-ring statement
  `IsRegularLocalRing.isIntegrallyClosed`, and §4.13's `IsRegular.isNormal` is its stalkwise form.
- *Depth, Cohen–Macaulay rings and Serre's conditions*: SchemeAndStackFoundations §0.17
  (`IsLocalRing.depth`, `Ring.IsCohenMacaulay`, `Ring.IsCohenMacaulay.of_isRegularRing`, `satisfiesSerreS`).
- *Reflexive sheaves, reflexive extension across codimension two, coherent Hartogs*:
  SchemeAndStackFoundations §0.6 (`reflexive_extension_normal`, `coherent_hartogs`).
- *Étaleness is fpqc local on the base; unramified criteria*: SchemeAndStackFoundations §0.11
  (Stacks, Descent, Lemma 35.23.31 (02VN); Morphisms, Lemmas 29.36.10 (02V5) to 29.36.14 (02GF)).
- *Étale neighbourhoods, henselian pairs, finite étale algebras over a henselian pair*:
  SchemeAndStackFoundations §§0.12–0.14 (Stacks, More on Algebra, Lemmas 15.11.6 (09XI),
  15.13.1 (0D4A) and 15.13.2 (09ZL)), with
  `henselian_finiteEtale_equivalence` and `henselian_pair_permanence` (complete pairs are henselian).
- *Strict henselization of a local ring, completion of noetherian local rings, preservation of
  regularity under completion and étale maps, miracle flatness between regular local rings of equal
  dimension*: [ModularCurves](../ModularCurves/README.md) Layer 4D. §0.6 here is the Cohen–Macaulay
  form of miracle flatness; 4D's statement is its special case with regular target.
- *Adic thickening systems, formal completion of coherent modules, the theorem on formal
  functions*: SchemeAndStackFoundations §§4.7–4.9.
- *Tame ramification of extensions of nonarchimedean local fields*:
  [LocalFieldsRamification](../LocalFieldsRamification/README.md) Layer 3 and Tau Ceti
  `TauCeti.IsTamelyRamified`. §0.2 compares the DVR notion with it.
- *Abhyankar's lemma for composita of function fields*: Tau Ceti
  `TauCeti.Place.ramificationIdx_restrict_sup` ([AlgebraicCurves](../AlgebraicCurves/README.md)),
  in `TauCeti/FieldTheory/FunctionField/Place/Extension/Abhyankar.lean`. Like `FiniteEtaleScheme`,
  it entered Tau Ceti (#15573, 2026-10-13) after this repository's pin.
  It is a statement about ramification indices of places in a compositum; §4.3 here is the
  scheme-theoretic local structure theorem, and neither implies the other.

## Conventions

1. Rings are commutative with identity. Schemes and morphisms are Mathlib's `Scheme` and
   `Scheme.Hom` in a fixed universe `u`. "Noetherian", "normal", "regular", "finite" and "dominant"
   are hypotheses written on the statement that needs them, never folded into a definition.
2. Points of `Spec A` are `PrimeSpectrum A`; local conditions at a prime `𝔮` of an `R`-algebra `S`
   use Mathlib's pointwise predicates `Algebra.IsEtaleAt R 𝔮`, `Algebra.IsUnramifiedAt R 𝔮` and
   `Algebra.QuasiFiniteAt R 𝔮`, and at a point `x` of a scheme they use the stalk map
   `f.stalkMap x` and Mathlib's `Scheme.Hom.QuasiFiniteAt`. "Étale at `x`" for a morphism locally of
   finite presentation is `Scheme.Hom.IsEtaleAt f x`, defined in §1.4 as membership in the étale
   locus.
3. The dimension of a local ring is `ringKrullDim`; the codimension of a point is `Order.coheight`
   (as in Tau Ceti `CodimensionOnePoint`). A prime divisor of `X` is a codimension-one point.
4. Ramification indices are Mathlib's `Ideal.ramificationIdx`: for a local homomorphism of
   discrete valuation rings `A → B`, the ramification index is
   `(IsLocalRing.maximalIdeal B).ramificationIdx A`. Residue degrees are Mathlib's
   `Scheme.Hom.residueDegree` at the scheme level and `Module.finrank` of the residue field
   extension at the ring level.
5. A ring is *normal* in the sense of Stacks, Definition 10.37.11 (00GV): every localization at
   a prime is a normal domain. This is `IsStacksNormalRing`; Mathlib's `IsIntegrallyClosed` covers
   only domains. A *finite normal algebra* `B` over a domain `A` in Layer 2 is a finite `A`-algebra
   with `IsStacksNormalRing B` *and which is torsion free as an `A`-module*.
   **Divergence from Stacks.** Stacks, Lemma 58.20.3 (0BM9) has no torsion-freeness condition. As
   written, the lemma is false: for `A` normal local of dimension `≥ 2`, the algebra
   `B = A × A/𝔪` is finite and normal (Algebra, Lemma 10.37.15 (0CYA)), and `Spec B → X` is étale over `U`, but `B`
   is not `Γ(V, 𝒪_V)` for any `V` in `FÉt_U` (that would be `A`). So the functor is not essentially
   surjective. Requiring torsion freeness removes exactly the factors supported at the closed
   point, and the Stacks proof then goes through unchanged. The target `finiteNormalEquiv` (§2.2)
   is stated with the correction; this should be reported upstream to the Stacks Project.
8. **Stacks alignment.** Every target that has a Stacks Project counterpart cites its tag, and its
   statement follows the tag's hypotheses and conclusion in Mathlib's vocabulary. In Lean it carries
   Mathlib's `@[stacks XXXX]` attribute, as Mathlib does for 540 declarations at its current pin.
   Where a statement deliberately differs from its tag, the target says so under **Divergence from
   Stacks** or marks itself *adapted*, and says how. Targets without a Stacks counterpart are
   marked *API* and are kept only where a tagged target needs them. The table in
   [Stacks alignment](#stacks-alignment) lists every target.
6. A *standard tamely ramified cover* of `Spec A` along `f` is `A[x]/(x^e − f)` with `f` a
   nonzerodivisor, `A/fA` reduced, and `e ≥ 1` invertible in `A` (Stacks, Example 58.31.4 (0EYF)).
   Disjoint unions of covers are finite products of algebras, because `Spec` reverses arrows.
7. Names: ring-level statements live in the `Algebra`, `IsLocalRing`, `IsDiscreteValuationRing` and
   `IsRegularLocalRing` namespaces; scheme-level statements in `AlgebraicGeometry` and
   `AlgebraicGeometry.Scheme.Hom`. The suggested forms are in
   `TauCetiRoadmap.PurityAndAbhyankar`.

## Layer 0: local algebra

### 0.1 Regular local rings modulo a parameter

Prove `IsRegularLocalRing.of_quotient_nonZeroDivisor`: for a Noetherian local ring `R` and
`x ∈ 𝔪` a nonzerodivisor with `R/xR` regular local, `R` is regular local; and its regular-sequence
form `IsRegularLocalRing.of_quotient_isRegular` (Stacks, Lemma 10.106.7 (00NU)). Prove
`IsRegularLocalRing.isIntegrallyClosed` (Stacks, Lemma 10.157.5 (0567), local form) and
`IsRegularLocalRing.quotient_isRegularLocalRing_of_notMem_sq` in the regular-sequence form:
for a minimal generating set `x_1, …, x_d` of `𝔪`, the sequence is regular and every
`R/(x_1, …, x_c)` is regular local of dimension `d − c` (Stacks, Lemma 10.106.3 (00NQ); Tau Ceti's
`quotient_span_singleton` is the case `c = 1`). Prove `IsRegularLocalRing.localization`: the
localization of a regular local ring at a prime is regular local (Stacks, Lemma 10.110.6 (0AFS),
second sentence). Prove also the exact Stacks form
of 0567, `IsRegularRing.isStacksNormalRing`: a regular ring is normal in the sense of
Convention 5; `IsRegularLocalRing.isIntegrallyClosed` is its local case.
*Needs:* Mathlib `IsRegularLocalRing`, `RingTheory.Sequence.IsRegular`, `ringKrullDim`; Tau Ceti
`TauCeti.IsRegularLocalRing.isDomain`, `quotient_span_singleton`.

**Checks.**
- `test_of_quotient_powerSeries`: `k⟦X, Y⟧` is regular local because `k⟦X, Y⟧/(Y) ≅ k⟦X⟧` is.
- `test_not_regular_cusp`: `k⟦X, Y⟧/(Y² − X³)` is not regular local, and `x = X` is a nonzerodivisor
  whose quotient `k[Y]/(Y²)` is not regular, so §0.1 gives no information.

### 0.2 Extensions of a discrete valuation ring

Let `A` be a discrete valuation ring with fraction field `K` and `L/K` a finite separable extension.
Let `B` be the integral closure of `A` in `L` (finite over `A`, a semilocal Dedekind domain), with
maximal ideals `𝔪_1, …, 𝔪_n`, ramification indices `e_i` and residue extensions `κ(𝔪_i)/κ_A`.
This is the setup of Stacks, Remark 15.113.6 (09E8), which also gives `[L : K] = Σ e_i f_i`.
Define (Stacks, Definition 15.113.7 (09E9)):

- `Algebra.IsUnramifiedWRT A L`: every `e_i = 1` and every `κ(𝔪_i)/κ_A` is separable;
- `Algebra.IsTamelyRamifiedWRT A L`: every `κ(𝔪_i)/κ_A` is separable and every `e_i` is
  invertible in `κ_A`. Stacks writes "the characteristic of `κ_A` is `0`, or it is `p` and the
  extensions are separable and the `e_i` prime to `p`". This is the same condition, and
  "invertible in `κ_A`" is the wording of Stacks, Lemma 15.116.7 (0EXW);
- `Algebra.IsTotallyRamifiedWRT A L`: `n = 1` and `κ(𝔪_1) = κ_A`.

The definitions quantify over the maximal ideals of `integralClosure A L` with Mathlib's
`Ideal.ramificationIdx`; for a finite étale `K`-algebra `L = ∏ L_j` they are required of every
factor. API: `isUnramifiedWRT_iff_isEtale` (`L/K` is unramified with respect to `A` iff the integral
closure is étale over `A`), `IsUnramifiedWRT.isTamelyRamifiedWRT`, `isTamelyRamifiedWRT_of_charZero`
(residue characteristic zero), tower stability in both directions, and stability under base change
along an extension of discrete valuation rings with residue-separable unramified or tame
generic part (the commutative algebra of Stacks, Lemma 58.31.1 (0EYD), More on Algebra, Lemma
15.116.9 (0EXY)). Prove the characterization `isTamelyRamifiedWRT_iff_exists_kummer` (Stacks,
Lemma 15.116.7 (0EXW)): `L` is tamely ramified with respect to `A` iff it is contained in an
extension of `K[π^{1/e}]` unramified with respect to `A[π^{1/e}]`, for some `e` invertible in
`κ_A`. Prove the comparison `isTamelyRamifiedWRT_iff_isTamelyRamified`: for a finite extension
`L/K` of nonarchimedean local fields, `Algebra.IsTamelyRamifiedWRT 𝒪[K] L ↔ TauCeti.IsTamelyRamified K L`.
*Needs:* Mathlib `IsDiscreteValuationRing`, `integralClosure`, `Ideal.ramificationIdx`,
`Algebra.IsSeparable`, `Algebra.IsEtaleAt`; Tau Ceti `TauCeti.IsTamelyRamified`.

**Checks.**
- `test_gaussian`: `ℤ_(2) ⊂ ℚ(i)` is not tamely ramified (`e = 2`, residue characteristic 2).
- `test_cyclotomic3`: `ℤ_(3) ⊂ ℚ(ζ_3)` is tamely ramified and totally ramified with `e = 2`.
- `test_unramified_5`: `ℤ_(5) ⊂ ℚ(i)` is unramified.

### 0.3 Kummer extensions of a discrete valuation ring

Let `A` be a discrete valuation ring with uniformizer `π` and `n ≥ 2`. Prove `kummer_dvr`
(Stacks, Lemma 15.116.2 (09EV)), with `K_1 = K[π^{1/n}] = K[X]/(X^n − π)`: (1) `[K_1 : K] = n`;
(2) the integral closure of `A` in `K_1` is `A[X]/(X^n − π)`; (3) it is a discrete valuation ring;
(4) its ramification index over `A` is `n`; (5) `K_1/K` is totally ramified with respect to `A`;
(6) if `n` is prime to the residue characteristic, `K_1/K` is tamely ramified and every intermediate
field of `K_1/K` is `K[π^{1/d}]` for a divisor `d` of `n`. Clause (6) is stated without assuming roots
of unity in `K`.
*Needs:* §0.2; Mathlib `AdjoinRoot`, `Polynomial.irreducible_of_eisenstein_criterion`
(Eisenstein's criterion), `IntermediateField`.

**Checks.**
- `test_kummer_2_3`: for `A = ℤ_(3)`, `π = 3`, `n = 2`, the integral closure is `ℤ_(3)[√3]`, a DVR
  with `e = 2`.

### 0.4 Abhyankar's lemma for discrete valuation rings

Let `A ⊂ B` be an extension of discrete valuation rings whose residue characteristic is zero, or is
`p` with `p ∤ e(B/A)` and `κ_B/κ_A` separable; let `K_1/K` be finite, with `A_1` the integral closure
of `A` in `K_1` and `B_1` that of `B` in the compositum. Prove `abhyankar_dvr` (Stacks, Lemma
15.116.4 (0BRM)): if `e(B/A)` divides the ramification index of `A ⊂ (A_1)_{𝔪_i}`, then
`(A_1)_{𝔪_i} ⊂ (B_1)_{𝔪_{ij}}` is formally smooth in the `𝔪_{ij}`-adic topology for every `j`; and
the consequence used in Layer 4, `abhyankar_dvr_unramified`: in the same situation the extension
`(A_1)_{𝔪_i} ⊂ (B_1)_{𝔪_{ij}}` has ramification index one and separable residue extension.
*Needs:* §§0.2–0.3; Mathlib `Algebra.FormallySmooth`, `IsAdicComplete`.

### 0.5 The discriminant criterion

For a finite free `A`-algebra `B`, prove `Algebra.isEtale_iff_isUnit_discr`: `B` is étale over `A`
iff its discriminant (Mathlib `Algebra.discr` of any basis) is a unit; and the scheme form
`Scheme.Hom.etale_iff_discriminant_empty`: a finite locally free morphism is étale iff its
discriminant closed subscheme is empty, the discriminant being locally principal (Stacks, Lemma
49.3.1 (0BJF)). Prove `discriminant_support`: a point `y` lies in the discriminant iff some point of
the fibre over `y` is ramified.
*Needs:* Mathlib `Algebra.discr`, `Algebra.Etale`, `Module.Free`, `Module.Finite`,
`Algebra.FormallyUnramified`.

### 0.6 Miracle flatness

Prove `flat_of_isCohenMacaulay` (Stacks, Lemma 10.128.1 (00R4)): a local homomorphism `R → S` of
Noetherian local rings with `R` regular, `S` Cohen–Macaulay and
`dim S = dim R + dim (S/𝔪_R S)` is flat. Prove the corollary used in §3.2,
`flat_of_normal_dim_two`: a finite injective local homomorphism `A → B` with `A` regular local of
dimension two and `B` a normal local domain is flat (`B` is Cohen–Macaulay of dimension two by
Serre's criterion, SchemeAndStackFoundations §0.17).
*Needs:* SchemeAndStackFoundations §0.17; Mathlib `Module.Flat`, `IsRegularLocalRing`.

## Layer 1: ramification of finite morphisms along prime divisors

Throughout, `f : X ⟶ Y` is a finite dominant morphism of integral locally Noetherian schemes with
`Y` normal, unless a target says otherwise.

### 1.1 Codimension-one points under a finite morphism

Prove `Scheme.Hom.coheight_image`: under these hypotheses `coheight (f x) = coheight x` for every
`x : X` (going down for an integral extension of a normal domain, Stacks, Proposition 10.38.7 (00H8),
already Mathlib's `Algebra.HasGoingDown` instance with `@[stacks 00H8]`, and the dimension formula
of Stacks, Lemma 10.112.7 (00ON), already Mathlib's `@[stacks 00ON]` lemma in
`Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean` and Tau Ceti's in
`TauCeti/RingTheory/KrullDimension/Fiber.lean`). *API*: there is no single tag for
`coheight_image`.
Define `Scheme.Hom.codimensionOnePointMap f : CodimensionOnePoint X → CodimensionOnePoint Y` and prove
`codimensionOnePointMap_surjective` (lying over) and `finite_fiber_codimensionOnePointMap`
(finitely many prime divisors over each prime divisor). Prove the variant
`coheight_image_of_finiteType` for `X`, `Y` of finite type over a field, dropping normality of `Y`.
*Needs:* Mathlib `IsFinite`, `IsDominant`, `Order.coheight`, `Algebra.HasGoingDown`; Tau Ceti
`CodimensionOnePoint`.

### 1.2 Ramification index and residue degree at a prime divisor

For `x : CodimensionOnePoint X` with `𝒪_{X,x}` and `𝒪_{Y,f x}` discrete valuation rings (automatic
when `X` and `Y` are normal; Tau Ceti `isDiscreteValuationRing_stalk`), define
`Scheme.Hom.ramificationIdxAt f x := (IsLocalRing.maximalIdeal 𝒪_{X,x}).ramificationIdx 𝒪_{Y,f x}`
along `f.stalkMap x`: the ramification index of the extension of discrete valuation rings
`𝒪_{Y,f x} ⊂ 𝒪_{X,x}` (Stacks, Definition 15.113.1 (09E4)). Prove: `ramificationIdxAt_pos`;
`ramificationIdxAt_eq_ord` (`e = ord_x (f^♯ π)` for a uniformizer `π` at `f x`, with Mathlib's
`Scheme.ord`); `ramificationIdxAt_comp` (`e(g ∘ f, x) = e(f, x) · e(g, f x)`, Stacks, Lemma
15.113.3 (0BRL)); the degree formula (Stacks, Remark 15.113.6 (09E8))
`sum_ramificationIdxAt_mul_residueDegree`: `Σ_{x ↦ y} e(f, x) · f.residueDegree x = f.finrank` over the
prime divisors `x` above a prime divisor `y`, where `f.finrank` is the degree of the function field
extension; and, for `X`, `Y` integral of finite type over a field `k`, the comparison
`ramificationIdxAt_eq_place` with Tau Ceti's `TauCeti.Place.ramificationIdx` of the places
`X.toPlace x` over `Y.toPlace (f x)`.
*Needs:* §1.1; Mathlib `Ideal.ramificationIdx`, `Ideal.sum_ramification_inertia`,
`Scheme.Hom.stalkMap`, `Scheme.ord`, `Scheme.Hom.residueDegree`; Tau Ceti `Scheme.toPlace`,
`TauCeti.Place.ramificationIdx`, `isDiscreteValuationRing_stalk`.

**Checks.**
- `test_square_map`: for `f : 𝔸¹ → 𝔸¹`, `t ↦ t²` over a field of characteristic `≠ 2`, the
  ramification index at the origin is `2` and is `1` at every other closed point.
- `test_degree_formula`: for the same `f`, `Σ e · f = 2` over every prime divisor of the target.

### 1.3 Unramified and étale at a prime divisor

Prove `unramifiedAt_iff_ramificationIdxAt`: `f` is unramified at `x : CodimensionOnePoint X`
(Stacks, Definition 29.36.1 (02G4); `Algebra.IsUnramifiedAt` of the stalk map) iff
`ramificationIdxAt f x = 1` and the residue field extension at `x` is separable; and
`etaleAt_iff_unramifiedAt_codimOne` for `X` normal: at a prime divisor, unramified and étale
(Definition 29.37.1 (02GI)) coincide. Both are the case of a discrete valuation ring of Stacks,
Lemma 29.37.15 (02GU), condition (6): flat, `𝔪_s 𝒪_{X,x} = 𝔪_x`, and `κ(x)/κ(s)` finite separable.
*Needs:* §1.2, §0.2.

### 1.4 Ramification locus, branch locus, branch divisor

For `f` locally of finite type, define the open étale locus `Scheme.Hom.etaleLocus f` (its affine
form is Mathlib's `Algebra.etaleLocus`), the predicate `Scheme.Hom.IsEtaleAt f x := x ∈ f.etaleLocus`,
and the closed `Scheme.Hom.ramificationLocus f : Set X`, the complement of the unramified locus.
For `f` finite define `Scheme.Hom.branchLocus f := f '' f.ramificationLocus`, closed in `Y`, and the
reduced branch divisor `Scheme.Hom.branchDivisor f : SchemeWeilDivisor Y`, with coefficient one at
each prime divisor of `Y` contained in the branch locus. Prove `isOpen_etaleLocus`,
`isClosed_branchLocus`, `finite_support_branchDivisor` (for `Y` Noetherian and `f` generically
étale), `branchLocus_comp` (the branch locus of a composite is contained in the union of the branch
locus of the second map and the image of that of the first) and `branchLocus_iterate` for an
endomorphism.
*API*: Stacks has no "branch locus" definition; it uses the phrase in Lemma 58.21.4 (0BMB) and
Example 58.13.3 (0BTE). The étale locus is open by Definition 29.37.1 (02GI), and Weil divisors
and prime divisors are Stacks, Definition 31.27.2 (0BE2), which Tau Ceti's `SchemeWeilDivisor`
implements.
*Needs:* §1.3; Mathlib `Algebra.etaleLocus`, `Algebra.unramifiedLocus`; Tau Ceti `SchemeWeilDivisor`.

**Checks.**
- `test_branch_quotient_cone`: over a field of characteristic `≠ 2`, the quotient map
  `𝔸² → Spec k[x², xy, y²]` is finite, étale at every point of `𝔸² ∖ {0}`, and has branch locus the
  vertex, a closed point of codimension two; its branch divisor is zero. This is Stacks, Example
  58.13.3 (0BTE), with `n = 2`.

### 1.5 Ramification in codimension one of a finite étale cover of a dense open

Let `X` be locally Noetherian, `U ⊆ X` a dense open and `V ∈ FiniteEtaleScheme U`, such that for every
prime divisor `ξ` of `X` outside `U` the stalk `𝒪_{X,ξ}` is a discrete valuation ring with fraction
field `K_ξ`. Then `V ×_U Spec K_ξ = Spec L_ξ` for a finite étale `K_ξ`-algebra `L_ξ`. Define
`IsUnramifiedInCodimOne X U V` and `IsTamelyRamifiedInCodimOne X U V`: `L_ξ / K_ξ` is unramified,
resp. tamely ramified, with respect to `𝒪_{X,ξ}` (§0.2) for every such `ξ` (Stacks, Section 58.31
(0BSE), the untagged definition preceding Lemma 58.31.1). The affine form along a principal
divisor `V(a)`, `IsTamelyRamifiedAlong R S a`, quantifies over the primes of `S` minimal over `aS`
lying over primes minimal over `aR`: these are the generic points of Stacks' prime divisors
`Z ⊂ X` with `Z ∩ U = ∅`. Prove `IsUnramifiedInCodimOne.baseChange` and
`IsTamelyRamifiedInCodimOne.baseChange` (Stacks, Lemma 58.31.1 (0EYD)): under the four hypotheses of
that lemma on `X' → X`, both properties pass to `V ×_X X'`. Prove the comparison
`isUnramifiedInCodimOne_iff_etaleAt`: for `X` normal and `V → U` the restriction of a finite
morphism `Y → X` with `Y` normal, `V` is unramified over `X` in codimension one iff `Y → X` is étale
at every prime divisor of `Y`.
*Needs:* §§0.2, 1.3; Tau Ceti `FiniteEtaleScheme`, `CodimensionOnePoint`.

## Layer 2: finite étale covers of punctured spectra

Throughout, `(A, 𝔪)` is a Noetherian local ring, `X = Spec A`, and `U = X ∖ {𝔪}` is the punctured
spectrum.

### 2.1 The punctured spectrum and purity for a local ring

Define `IsLocalRing.puncturedSpectrum A : (Spec A).Opens`, the complement of the closed point, and
`IsLocalRing.restrictPunctured : FiniteEtaleScheme (Spec A) ⥤ FiniteEtaleScheme U`. Define
`IsLocalRing.PurityHolds A := (IsLocalRing.restrictPunctured A).EssSurj`, verbatim the definition
in the first paragraph of Stacks, Section 58.20 (0BM7): "purity holds for `(A, 𝔪)` if the
restriction functor `FÉt_X → FÉt_U` is essentially surjective". Prove `isQuasiCompact_puncturedSpectrum`, `puncturedSpectrum_eq_iSup_basicOpen` (it is
covered by `D(x_i)` for generators `x_i` of `𝔪`) and `restrictPunctured_faithful` for
`depth A ≥ 1`.
*Needs:* Tau Ceti `FiniteEtaleScheme`; Mathlib `PrimeSpectrum.basicOpen`, `IsLocalRing.maximalIdeal`.

### 2.2 Finite normal algebras and reflexive extension

Prove `spec_sections_of_depth` (Stacks, Lemma 58.20.1 (0BM8)): a finite `Y → X` with
`depth 𝒪_{Y,y} ≥ 2` at all closed points is `Spec Γ(Y ×_X U, 𝒪)`. Prove
`extends_iff_sections_finiteEtale` (Stacks, Lemma 58.20.2 (0BLK)): for `depth A ≥ 2`, a finite étale
`V → U` extends to a finite étale cover of `X` iff `Γ(V, 𝒪)` is finite étale over `A`. Prove
`finiteNormalEquiv` (Stacks, Lemma 58.20.3 (0BM9), **with the correction of Convention 5**;
Stacks' own statement omits torsion freeness), with finite normal algebras as in Convention 5:
for `A` normal of dimension `≥ 2`, `V ↦ Γ(V, 𝒪_V)` is an equivalence from `FiniteEtaleScheme U` to the
category of finite normal `A`-algebras `B` with `Spec B → X` étale over `U`; and `V` extends to a
finite étale cover of `X` iff `Γ(V, 𝒪_V)` is finite étale over `A`. Prove `reflexiveExtension`
(Stacks, Lemma 58.21.5 (0EY6)): for `j : U → X` an open immersion of locally Noetherian schemes with
`depth 𝒪_{X,x} ≥ 2` off `U`, and `π : V → U` finite étale, `j_* π_* 𝒪_V` is a reflexive coherent
`𝒪_X`-algebra whose relative spectrum `Y` is the unique finite `Y → X` with `Y ×_X U = V` and depth
`≥ 2` off `V`; `Y → X` is étale at `y` iff flat at `y`; the construction commutes with flat base
change.
*Needs:* §2.1; SchemeAndStackFoundations §0.6 (`reflexive_extension_normal`, `coherent_hartogs`),
§0.17 (depth); Mathlib `integralClosure`, `IsIntegralClosure`.

**Checks.**
- `test_closed_point_factor`: for `A = k⟦X, Y⟧`, the algebras `A` and `A × A/𝔪` restrict to the same
  cover of `U`; only `A` is torsion free.

### 2.3 Completion and full faithfulness of restriction to a hypersurface

Let `f ∈ 𝔪`, `X_0 = Spec A/fA` and `U_0` its punctured spectrum (Stacks, Situation 58.19.1
(0BLF)). Prove
`finite_extend_of_completion` (Stacks, Lemma 58.19.3 (0BLH)) and `extends_iff_completion_extends`
(Stacks, Lemma 58.20.4 (0BLL)): a finite étale `V → U` extends over `X` iff its base change extends
over `Spec Â`. Prove `restrictHypersurface_fullyFaithful` (Stacks, Lemma 58.19.7 (0BLJ)): if
`depth A ≥ 3` and `(A, (f))` is a henselian pair, then `FiniteEtaleScheme U ⥤ FiniteEtaleScheme U_0` is
fully faithful. The Stacks proof goes through Lemmas 58.19.4 (0BLI), 58.19.6 (0BM6) and 58.17.1
(0EL8): reduction to the complete case for a henselian pair, vanishing of `H¹_𝔪(A)` and
`H²_𝔪(A)` from depth `≥ 3` (Dualizing Complexes, Lemma 47.11.1), and full faithfulness of
restriction of finite locally free modules from `U` to the formal completion along `U_0`
(Algebraic and Formal Geometry, Lemma 52.15.5 (0EKS)). Each of these is a target of this
subsection, stated as its tag states it.
*Needs:* §2.2; Mathlib `localCohomology`, `AdicCompletion`; SchemeAndStackFoundations §§0.13–0.14
(henselian pairs), §0.17 (depth), §§4.7–4.9 (adic thickening systems, formal completion, formal
functions).

### 2.4 The local Lefschetz extension theorem

Prove `finiteEtale_extend_of_hypersurface` (Stacks, Lemma 58.20.7 (0BLM)): in Situation 58.19.1 with
`depth A ≥ 3`, if `V ∈ FiniteEtaleScheme U` restricts on `U_0` to the restriction of a finite étale
`Y_0 → X_0`, then `V` is the restriction of a finite étale `Y → X`. The Stacks proof reduces to
the complete case by §2.3, lifts `Y_0 → X_0` along the henselian pair `(Â, fÂ)`
(SchemeAndStackFoundations §0.14 `henselian_finiteEtale_equivalence`, Stacks 09ZL), and identifies
the two covers of `U` by `restrictHypersurface_fullyFaithful`.
*Needs:* §2.3; SchemeAndStackFoundations §0.14.

## Layer 3: purity of the branch locus

### 3.1 The flat case and étale localization of quasi-finite morphisms

Prove `exists_elementaryEtale_finite_of_quasiFiniteAt` (Stacks, Lemma 37.41.1 (02LK)): for `f`
locally of finite type and `x` isolated in its fibre, there are an elementary étale neighbourhood
`(U, u) → (S, f x)` and an open `V ⊆ X ×_S U` finite over `U` with a unique point `v` over `u`,
mapping to `x` with `κ(x) = κ(v)`, and the property persists under further elementary étale
neighbourhoods. Mathlib's `Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq` (Stacks,
Algebra, Lemma 10.145.2 (00UJ)) is the affine algebraic input. Prove `etaleLocal_source` (Stacks, Lemma 35.31.1 (036W)): étaleness
is étale local on the source. Prove `etaleAt_of_flat_unramified_codimOne` (Stacks, Lemma 58.21.2
(0BJH)): for `f` flat, quasi-finite at `x`, `x` not a generic point of an irreducible component, and
unramified at every specialization `x' ⤳ x` with `dim 𝒪_{X,x'} = 1`, `f` is étale at `x`.
*Needs:* §§0.5, 1.4; SchemeAndStackFoundations §0.11 (02VN); Mathlib `Scheme.Hom.QuasiFiniteAt`,
`Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq`.

### 3.2 Purity for regular local rings

Prove `purity_regularLocal` (Stacks, Lemma 58.21.3 (0BMA)): for `A` regular local of dimension
`d ≥ 2`, (1) `IsLocalRing.PurityHolds A`, and (2) any finite `A → B` with `B` normal inducing a finite
étale morphism on punctured spectra is étale. The proof is by induction on `d`: for `d = 2`,
`flat_of_normal_dim_two` (§0.6) and §3.1; for `d ≥ 3`, a parameter `f ∈ 𝔪 ∖ 𝔪²` gives `A/fA` regular
of dimension `d − 1` (§0.1), and `finiteEtale_extend_of_hypersurface` (§2.4) lifts the inductive
extension, using `finiteNormalEquiv` (§2.2) to pass between (1) and (2).
*Needs:* §§0.1, 0.6, 2.2, 2.4, 3.1.

### 3.3 Purity of the branch locus

Prove the pointwise theorem `Scheme.Hom.etaleAt_of_unramified_codimOne` (Stacks, Lemma 58.21.4
(0BMB)): let `f : X ⟶ Y` be a morphism of locally Noetherian schemes, `x : X`, `y = f x`; if
`𝒪_{X,x}` is normal, `𝒪_{Y,y}` is regular, `f` is quasi-finite at `x`,
`dim 𝒪_{X,x} = dim 𝒪_{Y,y} ≥ 1`, and `f` is unramified at every specialization `x' ⤳ x` with
`dim 𝒪_{X,x'} = 1`, then `f.IsEtaleAt x`. Prove its affine form `Algebra.isEtaleAt_of_purity`: for a
finite-type algebra `S` over a Noetherian ring `R` and a prime `𝔮` of `S` satisfying the same
hypotheses on `S_𝔮`, `R_{𝔮 ∩ R}`, `Algebra.QuasiFiniteAt R 𝔮`, heights and codimension-one
specializations, `Algebra.IsEtaleAt R 𝔮`. Mathlib's `Scheme.Hom.QuasiFiniteAt` is a condition on
the stalk map, while Stacks' "quasi-finite at `x`" (Definition 29.21.1 (01TD)) includes finite
type near `x`; the scheme form therefore also assumes `LocallyOfFiniteType f`, which loses no case
since the conclusion is local at `x`. Prove the global corollaries
`branchLocus_pure_codimOne`: for `f` finite and dominant with `X` normal integral and `Y` regular integral, every
generic point of `f.branchLocus` has codimension one; and `etale_iff_etaleAt_codimOne`: such an
`f` is étale iff it is étale at every prime divisor of `X`. The pointwise form of the latter is
Stacks, Lemma 58.28.3 (0EA4, "purity of ramification locus"), which drops quasi-finiteness and the
dimension equality in exchange for étaleness (rather than unramifiedness) in codimension one;
state it as `Scheme.Hom.etaleAt_of_etaleAt_codimOne` in the tag's form, and derive
`etale_iff_etaleAt_codimOne` from it. *API*: `branchLocus_pure_codimOne` has no tag.
*Needs:* §§1.4, 3.1, 3.2; Mathlib `Scheme.Hom.QuasiFiniteAt`, `Algebra.IsEtaleAt`,
`Algebra.QuasiFiniteAt`, `Ideal.height`.

**Checks.**
- `test_purity_needs_regular`: the quotient map of `test_branch_quotient_cone` (§1.4) has normal
  source and normal, non-regular target, is étale at every prime divisor, and is not étale at the
  origin.

### 3.4 Extending finite étale covers across regular complements and regular divisors

Prove `finiteEtale_extend_of_purity` (Stacks, Lemma 58.21.6 (0EY7)): for `j : U → X` an open
immersion of Noetherian schemes with `IsLocalRing.PurityHolds 𝒪_{X,x}` for every `x ∉ U`,
`FiniteEtaleScheme X ⥤ FiniteEtaleScheme U` is essentially surjective. Prove
`finiteEtale_extend_of_regular_complement` (Stacks, Lemma 58.31.2 (0H2W)): for `U ⊆ X` dense open with
`𝒪_{X,x}` regular for all `x ∉ U`, a cover `V ∈ FiniteEtaleScheme U` unramified over `X` in codimension
one extends to `FiniteEtaleScheme X`. Prove `finiteEtale_extend_of_regular_divisor` (Stacks, Lemma
58.31.3 (0EYE)): for `D` an effective Cartier divisor whose subscheme is regular, a finite étale
`V → X ∖ D` unramified over `X` in codimension one extends to a finite étale cover of `X`.
The spreading-out step, `spread_from_localScheme` (Stacks, Limits Lemmas 32.20.3 (0BQ5) and
32.20.4 (0EY3): a
finitely presented `V → U` and a finitely presented `Y_x → Spec 𝒪_{X,x}` agreeing over
`U ×_X Spec 𝒪_{X,x}` glue to a finitely presented morphism over an open `U' ⊇ U ∪ {x}`, which is
finite étale after shrinking `U'` when both are), is a target here; it applies SchemeAndStackFoundations
§0.9 `finite_presentation_limits` to `Spec 𝒪_{X,x}` as the limit of its affine open neighbourhoods.
*Needs:* §§0.1, 1.5, 3.2; SchemeAndStackFoundations §0.9; Tau Ceti `IsEffectiveCartier`.

## Layer 4: Abhyankar's lemma for a regular divisor

### 4.1 Standard tamely ramified covers

For `A` Noetherian, `f ∈ A` a nonzerodivisor with `A/fA` reduced and `e ≥ 1` invertible in `A`,
define `standardTameCover A f e := AdjoinRoot (X^e − C f)` (Convention 6) and
`IsFiniteProductOfStandardTameCovers A f C`: `C` is `A`-isomorphic to a finite product of
`standardTameCover A f e_i`. Prove (Stacks, Example 58.31.4 (0EYF)): `standardTameCover_free`
(finite free of rank `e`), `standardTameCover_etale_away` (étale over `A_f`),
`dvr_of_minimal_over` (`A_𝔭` is a DVR with uniformizer `f` for `𝔭` minimal over `f`) and
`standardTameCover_isTamelyRamifiedInCodimOne`, through the characterization of tame extensions in
More on Algebra, Lemma 15.116.7 (0EXW). Prove `standardTameCover_regular_divisor`: if `A/fA` is regular then
`x` is a nonzerodivisor of `standardTameCover A f e` with regular quotient `A/fA`, so the reduced
inverse image of the divisor is again a regular effective Cartier divisor (§0.1).
*Needs:* §§0.1–0.3, 1.5; Mathlib `AdjoinRoot`, `Algebra.Etale`, `Module.Free`.

### 4.2 Base change to the strict henselization

For `x ∈ D` with `𝒪_{X,x}` local and `A^{sh}` its strict henselization (ModularCurves 4D), prove
`strictHenselization_quotient` (`A^{sh}/fA^{sh} ≅ (A/fA)^{sh}`, Stacks, Algebra Lemma 10.156.4
(05WS)),
`isRegularLocalRing_strictHenselization` (the forward direction of Stacks, Lemma 15.46.10 (06LN):
if `A` is regular local then so is `A^{sh}`), `finiteEtale_split_etaleNeighbourhood` (Stacks, Lemma
41.18.3 (04HN): a finite étale cover splits as a disjoint union of copies of the base after an étale
neighbourhood of a point; over a strictly henselian local ring it is a finite disjoint union of
copies of the base), and `finitePresentation_descend_colimit` (Stacks, Lemma 10.127.8 (05N9):
finitely presented algebras and their morphisms over a filtered colimit of rings descend to a stage).
*Needs:* ModularCurves 4D (strict henselization); SchemeAndStackFoundations §0.12 (étale
neighbourhoods); Tau Ceti `FiniteEtaleScheme`; Mathlib `Algebra.FinitePresentation`, `IsFiltered`.

### 4.3 Abhyankar's lemma

Prove `abhyankar_regularDivisor` (Stacks, Lemma 58.31.5 (0EYG)): let `X` be locally Noetherian, `D`
an effective Cartier divisor whose subscheme is regular, and `V → X ∖ D` finite étale and tamely
ramified over `X` in codimension one; then for every `x : X` there are an étale neighbourhood
`(Spec A, u) → (X, x)` on which `D` is cut out by a nonzerodivisor `f` with `A/fA` regular, and an
isomorphism of `V ×_X Spec A_f` with the restriction to `Spec A_f` of a finite disjoint union of
standard tamely ramified covers `standardTameCover A f e_i`. Its affine pointwise form
`Algebra.abhyankar_standardCover` is stated for a Noetherian ring `R`, a nonzerodivisor `a` with
`R/aR` regular, and a finite `R`-algebra `S` étale over `R_a` that is the integral closure of `R` in
`S_a` and is tamely ramified in codimension one, concluding that each prime of `R` containing `a` has
an étale neighbourhood `R → R'` over which `R' ⊗_R S` is a finite product of standard tamely
ramified covers. *Adapted*: this is 0EYG with `X = Spec R`, `D = V(a)`, and `Y → X ∖ D` replaced by
its normalization `Spec S`, the object 0EYH produces. The proof follows Stacks: reduce to `A` strictly henselian by §4.2 and
`IsTamelyRamifiedInCodimOne.baseChange` (§1.5); then `A` is regular (§0.1) and normal, `f` is prime,
and with `e` the product of the ramification indices of `V` over `A_{(f)}`, `A' = A[x]/(x^e − f)` is
regular strictly henselian; DVR Abhyankar (§0.4) makes `V ×_A A'` unramified in codimension one;
§3.4 extends it to a finite étale, hence split, cover of `Spec A'`; this embeds the function field of
`V` in `K[f^{1/e}]`, and §0.3 (6) identifies it with `K[f^{1/n}]` for `n ∣ e` invertible in `A`.
*Needs:* §§0.3, 0.4, 1.5, 3.4, 4.1, 4.2.

### 4.4 The normalization

Prove `abhyankar_normalization` (Stacks, Lemma 58.31.6 (0EYH)): in the situation of §4.3 the
normalization `π : Y' → X` of `X` in `V` is finite locally free, its restriction to `X ∖ D` is `V`,
`D' = (π⁻¹ D)_red` is an effective Cartier divisor on `Y'` and `D'` is regular; and étale locally on
`X`, `Y' → X` is a finite disjoint union of `Spec A[x]/(x^e − f) → Spec A` with `f` a nonzerodivisor,
`A/fA` regular and `e` invertible in `A`. Normalization commutes with étale base change by Mathlib's
`Scheme.Hom.normalization` and its smooth base change isomorphism (Stacks, More on Morphisms,
Lemma 37.19.2 (03GV)), and the integral
closure of `A` in `A_f[x]/(x^e − f)` is `A[x]/(x^e − f)` (`standardTameCover_isIntegralClosure`,
proved here from `standardTameCover_regular_divisor` and §0.1).
*Needs:* §§4.1, 4.3; Mathlib `Scheme.Hom.normalization`, `IsIntegralClosure`.

**Checks.**
- `test_abhyankar_charZero`: over a field of characteristic zero, every finite étale cover of
  `𝔸² ∖ {x = 0}` is tamely ramified in codimension one, and §4.3 applies.
- `test_abhyankar_wild`: over `𝔽_p`, the Artin–Schreier cover `y^p − y = 1/x` of `𝔸¹ ∖ {0}` is not
  tamely ramified at `x = 0`, and is not étale locally a standard tamely ramified cover.

## Stacks alignment

Every target, its Stacks Project tag, and how its statement relates to the tag. *Exact*: same
hypotheses and conclusion, in Mathlib vocabulary. *Adapted*: same mathematics in a different but
equivalent or specialized packaging, with the difference stated at the target. *Corrected*: the
tag as written is wrong and the target fixes it (Convention 5). *API*: no Stacks counterpart, kept
because a tagged target needs it. Every tag and its number were fetched from the Stacks Project and
compared with the target on 2026-10-15.

| § | Target | Stacks | Class |
| --- | --- | --- | --- |
| 0.1 | `IsRegularLocalRing.of_quotient_nonZeroDivisor`, `.of_quotient_isRegular` | 10.106.7 (00NU) | exact |
| 0.1 | `IsRegularLocalRing.quotient_isRegularLocalRing_of_notMem_sq` | 10.106.3 (00NQ) | exact |
| 0.1 | `IsRegularRing.isStacksNormalRing` | 10.157.5 (0567) | exact |
| 0.1 | `IsRegularLocalRing.isIntegrallyClosed` | 10.157.5 (0567) | adapted (local case) |
| 0.1 | `IsRegularLocalRing.localization` | 10.110.6 (0AFS), second sentence | exact |
| 0.2 | `IsUnramifiedWRT`, `IsTamelyRamifiedWRT`, `IsTotallyRamifiedWRT` | 15.113.7 (09E9) | exact |
| 0.2 | `isTamelyRamifiedWRT_iff_exists_kummer` | 15.116.7 (0EXW) | exact |
| 0.2 | base change of unramified/tame | 15.116.9 (0EXY) | exact |
| 0.2 | `isUnramifiedWRT_iff_isEtale`, `isTamelyRamifiedWRT_iff_isTamelyRamified` | — | API (comparisons) |
| 0.3 | `kummer_dvr` | 15.116.2 (09EV) | exact |
| 0.4 | `abhyankar_dvr` | 15.116.4 (0BRM) | exact |
| 0.4 | `abhyankar_dvr_unramified` | — | API (consequence of 0BRM used in 4.3) |
| 0.5 | `Scheme.Hom.etale_iff_discriminant_empty` | 49.3.1 (0BJF) | exact |
| 0.5 | `Algebra.isEtale_iff_isUnit_discr`, `discriminant_support` | — | API (affine form of 0BJF) |
| 0.6 | `flat_of_isCohenMacaulay` | 10.128.1 (00R4) | exact |
| 0.6 | `flat_of_normal_dim_two` | — | API (case of 00R4 used in 3.2) |
| 1.1 | `Scheme.Hom.coheight_image` | 10.38.7 (00H8) + 10.112.7 (00ON) | API (combination; both tags already in Mathlib) |
| 1.2 | `ramificationIdxAt` | 15.113.1 (09E4) | adapted (at a prime divisor) |
| 1.2 | `ramificationIdxAt_comp` | 15.113.3 (0BRL) | exact (at a point) |
| 1.2 | `sum_ramificationIdxAt_mul_residueDegree` | 15.113.6 (09E8) | adapted (scheme form) |
| 1.3 | `unramifiedAt_iff_ramificationIdxAt`, `etaleAt_iff_unramifiedAt_codimOne` | 29.37.15 (02GU), (6) | adapted (DVR case) |
| 1.4 | `etaleLocus`, `ramificationLocus`, `branchLocus`, `branchDivisor` | 29.37.1 (02GI), 31.27.2 (0BE2) | API |
| 1.5 | `IsUnramifiedInCodimOne`, `IsTamelyRamifiedInCodimOne` | Section 58.31 (0BSE) | exact (untagged definition) |
| 1.5 | `.baseChange` | 58.31.1 (0EYD) | exact |
| 2.1 | `IsLocalRing.puncturedSpectrum` | Section 58.20 (0BM7) | adapted (no Noetherian hypothesis) |
| 2.1 | `FiniteEtaleScheme`, `restrictPunctured` | Section 58.5 (0BL6), 58.5.2 (0BN9) | API (carrier and base change functor; owned by Tau Ceti) |
| 2.1 | `IsLocalRing.PurityHolds` | Section 58.20 (0BM7) | exact (untagged definition) |
| 2.2 | `spec_sections_of_depth` | 58.20.1 (0BM8) | exact |
| 2.2 | `extends_iff_sections_finiteEtale` | 58.20.2 (0BLK) | exact |
| 2.2 | `finiteNormalEquiv` | 58.20.3 (0BM9) | corrected (torsion free) |
| 2.2 | `reflexiveExtension` | 58.21.5 (0EY6) | exact |
| 2.3 | `finite_extend_of_completion` | 58.19.3 (0BLH) | exact |
| 2.3 | `extends_iff_completion_extends` | 58.20.4 (0BLL) | exact |
| 2.3 | reduction to the complete case | 58.19.4 (0BLI) | exact |
| 2.3 | full faithfulness from local cohomology | 58.19.6 (0BM6) | exact |
| 2.3 | `restrictHypersurface_fullyFaithful` | 58.19.7 (0BLJ) | exact |
| 2.3 | full faithfulness from completion | 58.17.1 (0EL8), 52.15.5 (0EKS) | exact |
| 2.4 | `finiteEtale_extend_of_hypersurface` | 58.20.7 (0BLM) | exact |
| 3.1 | `exists_elementaryEtale_finite_of_quasiFiniteAt` | 37.41.1 (02LK) | exact |
| 3.1 | `etaleLocal_source` | 35.31.1 (036W) | exact |
| 3.1 | `etaleAt_of_flat_unramified_codimOne` | 58.21.2 (0BJH) | exact |
| 3.2 | `purity_regularLocal` | 58.21.3 (0BMA) | exact |
| 3.3 | `Scheme.Hom.etaleAt_of_unramified_codimOne` | 58.21.4 (0BMB) | adapted (`LocallyOfFiniteType f`, see §3.3) |
| 3.3 | `Algebra.isEtaleAt_of_purity` | 58.21.4 (0BMB) | adapted (affine) |
| 3.3 | `Scheme.Hom.etaleAt_of_etaleAt_codimOne` | 58.28.3 (0EA4) | exact |
| 3.3 | `etale_iff_etaleAt_codimOne` | 58.28.3 (0EA4) | adapted (global form) |
| 3.3 | `branchLocus_pure_codimOne` | — | API |
| 3.4 | `finiteEtale_extend_of_purity` | 58.21.6 (0EY7) | exact |
| 3.4 | `finiteEtale_extend_of_regular_complement` | 58.31.2 (0H2W) | exact |
| 3.4 | `finiteEtale_extend_of_regular_divisor` | 58.31.3 (0EYE) | exact |
| 3.4 | `spread_from_localScheme` | 32.20.3 (0BQ5), 32.20.4 (0EY3) | exact |
| 4.1 | `standardTameCover` and its properties | 58.31.4 (0EYF) | exact |
| 4.1 | `standardTameCover_regular_divisor` | 10.106.7 (00NU) | adapted (application) |
| 4.2 | `strictHenselization_quotient` | 10.156.4 (05WS) | exact |
| 4.2 | `isRegularLocalRing_strictHenselization` | 15.46.10 (06LN) | adapted (one direction) |
| 4.2 | `finiteEtale_split_etaleNeighbourhood` | 41.18.3 (04HN) | exact |
| 4.2 | `finitePresentation_descend_colimit` | 10.127.8 (05N9) | exact |
| 4.3 | `abhyankar_regularDivisor` | 58.31.5 (0EYG) | exact |
| 4.3 | `Algebra.abhyankar_standardCover` | 58.31.5 (0EYG) | adapted (affine) |
| 4.4 | `abhyankar_normalization` | 58.31.6 (0EYH) | exact |

In `Suggested.lean`, `IsUnramifiedWRT.isTamelyRamifiedWRT`, `coheight_apply`, `finiteEtale` and
`IsFiniteProductOfStandardTameCovers` carry no `@[stacks]` attribute, and each docstring says why;
`Algebra.abhyankar_standardCover` carries both 0EYG and 0EYH.

## Provenance

The `pcf` repository (github.com/tdupu/pcf, Apache-2.0, by T. Dupuy, A. Levy, T. Tucker and
Z. Wang) contains a Lean development of much of this material, written for the characteristic-zero
case of the "PCF all the way down" theorem, where purity and Abhyankar's lemma enter as hypotheses.
It is a cited source and not the specification. The closest correspondences:
`lean/Pcf/Bounding/Divisors.lean` and `CriticalLoci.lean` (§§1.1–1.4),
`lean/Pcf/Stacks/Purity/` (§§0.1, 0.5, 0.6, 2.1–2.2, 3.1, and the `0BMA` induction of §3.2, which there
is conditional on `0BLM`), `lean/Pcf/Stacks/Abhyankar/` (§§0.2–0.4, 4.1, 4.2 and the `05N9` descent of
§4.2), and the statements `Pcf.Stacks.ZariskiNagataPurity` (the affine form of §3.3) and
`Pcf.Stacks.AbhyankarLemma` (a characteristic-zero affine form of §4.3, with all positive integers
invertible). Integration of that code follows the README's porting guidance and requires its
authors' agreement.

## Toward a Stacks Project roadmap

> **Roadmap-for-a-roadmap. Do not attempt any of this section.** It records the motivation for a
> future roadmap and specifies no targets.

Purity and Abhyankar's lemma are two results of Stacks, Chapter 58 (Fundamental Groups of Schemes).
A future roadmap could organize the rest of that chapter, and more broadly a systematic
Stacks-tag-indexed import, around the carriers fixed here and in SchemeAndStackFoundations: the
Galois category of finite étale covers and `π₁` of a connected scheme, its functoriality and
specialization, Grothendieck's local Lefschetz theorems in the generality of Sections 58.17–58.19
and 58.22–58.26, the tame fundamental group and Abhyankar's lemma for normal crossings divisors, and
`π₁` of curves over algebraically closed fields of characteristic zero by comparison with topology.

## References

- The Stacks Project, Chapters 10 (Commutative Algebra), 15 (More on Algebra), 37 (More on
  Morphisms), 41 (Étale Morphisms of Schemes), 49 (Discriminants and Differents) and 58
  (Fundamental Groups of Schemes), https://stacks.math.columbia.edu. Tags cited above were checked
  against the live tag pages.
- A. Grothendieck, *Revêtements étales et groupe fondamental* (SGA 1), Exposé X: Théorème 3.1
  (Zariski–Nagata purity, recalled without proof) and Corollaire 3.2 (its local form), §3.3 here;
  Lemme 3.6 (Abhyankar's lemma for a discrete valuation ring and tame Galois extensions), §0.4 here.
  Exposé XIII, §5 (Appendice I): Proposition 5.2 (absolute Abhyankar lemma) and Proposition 5.5
  (relative form), for normal crossings divisors, §4.3 here. Checked against arXiv:math/0206203.
- A. Grothendieck, *Cohomologie locale des faisceaux cohérents et théorèmes de Lefschetz locaux et
  globaux* (SGA 2), Exposé X, Théorème 3.4 (i): a regular Noetherian local ring of dimension `≥ 2`
  is pure (§3.2 here). SGA 2's purity (Définition 3.1) asks for an equivalence of categories, which
  is stronger than Stacks' essential surjectivity. Checked against arXiv:math/0511279.
- A. Grothendieck and J. P. Murre, *The tame fundamental group of a formal neighbourhood of a divisor
  with normal crossings on a scheme*, Lecture Notes in Mathematics 208, Springer, 1971. Stacks,
  Section 58.31 (0BSE), cites it for a slightly different notion of tame ramification in
  codimension one. No pinpoint is given because none could be checked.
