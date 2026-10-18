# Roadmap: post-critically finite maps

**Summary.** This roadmap develops post-critical finiteness for finite dominant self-maps of
varieties, and proves that in characteristic zero a post-critically finite (PCF) map is PCF *all
the way down*: if `φ : X → X` is a finite dominant PCF self-map of a variety over a field of
characteristic zero and `A ⊂ X` is a prime divisor with `φ^{r+s}(A) = φ^r(A)`, `s ≥ 1`, then
`φ^s` restricted to `φ^r(A)` is again PCF, and so on through every chain of preperiodic prime
divisors. Ramification is measured at codimension-one points after normalization: the *divisorial
critical locus* of a finite dominant morphism is the set of codimension-one points under which the
lift to normalizations has ramification index `> 1`, the *divisorial branch locus* is its image,
and the *postcritical set* is the forward orbit of the divisorial branch locus. The two
unnormalized variants (not unramified, not étale) are compared with it. The geometric input is the
bounding theorem: the restriction of a finite morphism of normal varieties to a prime divisor is
étale in codimension one away from three explicit singular and intersection terms. Its proof uses
purity of the branch locus ([PurityOfBranchLocus](../PurityOfBranchLocus/README.md)) and
Abhyankar's lemma for a regular divisor ([AbhyankarLemma](../AbhyankarLemma/README.md)). Mathlib
has schemes, finite, dominant and étale morphisms, relative normalization, ramification indices of
ideals and periodic points; normal schemes, codimension-one points under finite morphisms and
ramification at a point are [SchemeAndStackFoundations](../SchemeAndStackFoundations/README.md)
§0.30. Neither library has preperiodic points of a self-map, forward orbits of sets, divisorial
branch loci or postcritical sets (Mathlib's `Flow.forwardOrbit` is the forward orbit of a point
under a flow, a different notion).

| Layer | Title | What it delivers |
|---|---|---|
| [0](#layer-0-preperiodic-points-and-forward-orbits) | Preperiodic points and forward orbits | preperiodic points of a self-map, forward orbits of sets, periodic points in finite invariant sets |
| [1](#layer-1-ramification-in-codimension-one) | Ramification in codimension one | ramification index one, étaleness and reduced fibres in characteristic zero |
| [2](#layer-2-normalization-and-the-normalization-lift) | Normalization and the normalization lift | the normalization of an integral scheme as a normal integral scheme, the lift of a dominant morphism |
| [3](#layer-3-divisorial-loci-and-postcritical-sets) | Divisorial loci and postcritical sets | the six divisorial critical and branch loci, towers, postcritical sets, iterates, normalization, ramified covers |
| [4](#layer-4-closures-of-points) | Closures of points | reduced closures, the induced maps, finiteness and dimension |
| [5](#layer-5-the-bounding-theorem) | The bounding theorem | the exceptional set, the standard piece, the bounding theorem |
| [6](#layer-6-pcf-all-the-way-down) | PCF all the way down | the invariant, preperiodic and general theorems, PCF all the way down, the non-étale refinement |
| [7](#layer-7-self-maps-of-projective-space) | Self-maps of projective space | self-maps of `ℙⁿ` given by forms, the Jacobian criterion, the projective examples |

```text
Mathlib + Tau Ceti → Layer 0 → Layer 1 → Layer 2 → Layer 3 → Layer 4 → Layer 5 → Layer 6
                                         └─────────────── Layer 7 (examples) ←───────┘
SchemeAndStackFoundations §§0.20, 0.30, 4.13 ──→ Layers 1, 2, 3, 5
PurityOfBranchLocus §§0.1, 0.4, 1.1, 2.1 ──────→ Layers 1, 3, 5
AbhyankarLemma §§1.1, 3.1, 3.3, 3.4 ───────────→ Layer 5
LocalPurity §0.1 (00R4) ───────────────────────→ Layer 7
```

The end theorems are `isPCF_restrictPointClosure` (§6.3) and `isPCFAllTheWayDown` (§6.4).

## Scope and ownership

**This roadmap owns** preperiodic points of a self-map and forward orbits of sets; the
characteristic-zero dictionary between ramification index one, étaleness and reduced fibres at
codimension-one points; the normalization of an integral scheme in its function field as a normal
integral scheme, finite over a variety, and the normalization lift of a dominant morphism (Stacks,
Lemma 29.55.5 (035Q) (4)); the divisorial critical and branch loci (normalized, non-unramified,
non-étale), the corresponding postcritical sets and PCF predicates; restriction of a self-map to
the closure of a point it fixes; the bounding theorem; PCF all the way down; and self-maps of
projective space given by forms with the Jacobian criterion.

**Owned elsewhere and consumed here.**

- *Periodic points*: Mathlib `Function.IsPeriodicPt`, `Function.minimalPeriod`,
  `Function.periodicPts`.
- *Normal schemes, codimension-one points under finite dominant morphisms, ramification at a
  point, regular quotients of a regular local ring*: SchemeAndStackFoundations §0.30
  (`NormalSchemes.IsNormalScheme`, Stacks 033I; `NormalSchemes.coheight_apply_eq_one`,
  `NormalSchemes.codimensionOneMap`; `NormalSchemes.ramificationIdxAt`,
  `NormalSchemes.ramificationIdxAt_comp`; `NormalSchemes.exists_regularSystem_of_quotient`,
  Stacks 00NR).
- *Codimension-one points*: Tau Ceti `TauCeti.AlgebraicGeometry.CodimensionOnePoint` (module
  `TauCeti.AlgebraicGeometry.Scheme.CodimensionOnePoint`) and Mathlib `Order.coheight`.
- *Relative normalization*: Mathlib `Scheme.Hom.normalization`, `Scheme.Hom.toNormalization`,
  `Scheme.Hom.fromNormalization`, `Scheme.Hom.normalizationDesc` (the universal property, Stacks,
  Lemma 29.54.4 (035I)), `normalization.hom_ext`; Tau Ceti `Scheme.Hom.normalizationMap` (035J),
  which postdates the roadmap's Tau Ceti pin `a91d3aaf` (it is in Tau Ceti `main` from `1ac117c`).
  Finiteness of the normalization of a Nagata integral scheme: SchemeAndStackFoundations §0.20
  `nagata_normalization_finite` (0AVK), with finite-type algebras over a field Nagata by §0.21.
- *Ramification indices of ideals*: Mathlib `Ideal.ramificationIdx`, `Ideal.ramificationIdx_tower`.
- *Pointwise étale and unramified, and the ramification, non-étale and branch loci as sets*:
  PurityOfBranchLocus §0.1 (`Scheme.Hom.etaleAt_iff_stalkMap`,
  `Scheme.Hom.unramifiedAt_iff_stalkMap`; Stacks 02GU, 02G4) and §0.4
  (`Scheme.Hom.ramificationLocus`, `Scheme.Hom.nonEtaleLocus`, `Scheme.Hom.branchLocus`).
- *Purity of the branch locus*: PurityOfBranchLocus §2.1
  (`Scheme.Hom.exists_etale_of_formallyUnramified_stalk_codimOne`, Stacks 0BMB) and §1.1
  (`etale_of_etale_comp_surjective`, Stacks 036W).
- *Abhyankar's lemma*: AbhyankarLemma §1.1 (`IsTamelyRamifiedInCodimOne`), §3.1
  (`standardTameCover`), §3.3 (`abhyankar_regularDivisor`, Stacks 0EYG), §3.4
  (`abhyankar_normalization`, Stacks 0EYH), with its regular-divisor convention.
- *Regular schemes, regular and smooth loci*: SchemeAndStackFoundations §4.13 (`IsRegular`,
  *IsRegular.isNormal*, `regularLocus X`, *regularLocus_eq_smoothLocus*); Mathlib `smoothLocus`.
- *Regular local rings*: Mathlib `IsRegularLocalRing`; Tau Ceti `TauCeti.IsRegularLocalRing.isDomain`
  (00NP).
- *Reduced closed subschemes*: Mathlib `Scheme.IdealSheafData.vanishingIdeal`, `.subscheme`,
  `.subschemeι`, `isIntegral_of_irreducibleSpace_of_isReduced`.
- *Projective space*: Mathlib `Proj` with `MvPolynomial.gradedAlgebra`, `Proj.basicOpen`,
  `Proj.awayι`; miracle flatness [LocalPurity](../LocalPurity/README.md) §0.1
  (`flat_of_isCohenMacaulay`, Stacks 00R4); Mathlib `KaehlerDifferential`, `MvPolynomial.pderiv`.

Heights, canonical heights of polarized endomorphisms, equidistribution and the rest of arithmetic
dynamics are not in this roadmap; an arithmetic dynamics roadmap uses the notions of Layers 0–3.
Periodic subvarieties of codimension at least two are not in this roadmap.

## Conventions

1. Rings are commutative. Schemes and morphisms are Mathlib's `Scheme` and `Scheme.Hom` in a fixed
   universe `u`. Hypotheses are written on the statement that uses them, never folded into a
   definition.
2. **Statement form.** Every target is stated in Mathlib's and Tau Ceti's vocabulary, against the
   pinned libraries, and that statement is the target. Where the Stacks Project states the same
   result differently, an accompanying statement in the form of the tag is proved equivalent or
   derived; both carry `@[stacks XXXX]`. Targets with no Stacks counterpart are marked *API*.
3. **Varieties.** A *variety over `k`* is a scheme `X` with `IsIntegral X`, `IsLocallyNoetherian X`
   and `NoetherianSpace X`, together with a structure morphism `s : X ⟶ Spec k` that is
   `LocallyOfFiniteType`. Separatedness is not assumed. Self-maps `φ : X ⟶ X` are `IsFinite` and
   `IsDominant` (hence surjective) and are not required to commute with `s`. Results on varieties
   carry exactly these hypotheses; definitions carry only what they need.
4. **Divisorial loci.** Loci are sets of points, `Set X`. The critical loci consist of points with
   `Order.coheight x = 1`; for finite dominant morphisms of varieties (or with normal target) so do
   the branch loci, by SchemeAndStackFoundations §0.30 `coheight_apply_eq_one`. Each is then the
   set of generic points of prime divisors. The *divisorial critical locus* and the
   *divisorial branch locus* are the normalized ones (Layer 3); the *non-unramified* and
   *non-étale* ones carry those words in their names. They are the codimension-one parts of the
   loci of PurityOfBranchLocus §0.4 (`Scheme.Hom.ramificationLocus`, `Scheme.Hom.nonEtaleLocus`,
   `Scheme.Hom.branchLocus`), which are sets of points of every codimension.
5. **Pointwise notions.** "Étale at `x`" means that `(f.stalkMap x).hom` is flat and formally
   unramified, and "unramified at `x`" that it is formally unramified: the stalk forms of
   PurityOfBranchLocus §0.1. The ramification index at `x` is SchemeAndStackFoundations §0.30
   `NormalSchemes.ramificationIdxAt`.
6. **PCF.** `IsPCF φ` is finiteness of the postcritical set built from the divisorial branch
   locus; `IsNonUnramifiedPCF φ` and `IsNonEtalePCF φ` are the variants for the non-unramified and
   non-étale divisorial branch loci.
7. **Iterates.** `iterateHom φ n` is the `n`-fold composite of `φ : X ⟶ X`; on points
   `iterateHom φ n x = (⇑φ)^[n] x`.
8. Names: generic statements on self-maps live in `Function`; scheme-level statements in
   `AlgebraicGeometry` and `AlgebraicGeometry.Scheme.Hom`. The suggested forms are in
   `TauCetiRoadmap.PostcriticallyFiniteMaps`.

## Layer 0: preperiodic points and forward orbits

### 0.1 Preperiodic points and forward orbits

For `f : α → α`, define `Function.IsPreperiodicPt f x`: `f^[r + s] x = f^[r] x` for some `r` and
some `s ≥ 1`. Prove `Function.isPreperiodicPt_iff_finite_range_iterate` (preperiodic iff the
forward orbit `Set.range (f^[·] x)` is finite), `Function.IsPeriodicPt.isPreperiodicPt`,
`Function.IsPreperiodicPt.apply` and `.iterate` (images and iterates of preperiodic points are
preperiodic), and `Function.IsPreperiodicPt.exists_isPeriodicPt_iterate` (some `f^[r] x` is
periodic). Define `Function.forwardOrbit f s := ⋃ n, f^[n] '' s` for `s : Set α`, with
`subset_forwardOrbit`, `mapsTo_forwardOrbit`, `forwardOrbit_union`, `forwardOrbit_image_subset`, and
`Function.finite_forwardOrbit_iff`: for finite `s`, `forwardOrbit f s` is finite iff every point of
`s` is preperiodic. Prove `Function.forwardOrbit_iterate`: for `m ≥ 1`,
`forwardOrbit f^[m] (⋃ i < m, f^[i] '' s) = forwardOrbit f s`.
*Needs:* Mathlib `Function.IsPeriodicPt`, `Set.Finite`.

### 0.2 Finite invariant sets and semiconjugacies

Prove `Function.exists_isPeriodicPt_of_mapsTo`: a self-map of a finite nonempty invariant set has a
periodic point in it. For `π : β → α`, `g : β → β`, `f : α → α` with `π ∘ g = f ∘ π` and `t ⊆ β`,
prove `Function.Semiconj.image_forwardOrbit`: `π '' forwardOrbit g t = forwardOrbit f (π '' t)`;
and `Function.Semiconj.finite_forwardOrbit_iff_of_finite_fibres`: if `π` has finite fibres,
`forwardOrbit g t` is finite iff `forwardOrbit f (π '' t)` is.
*Needs:* §0.1.

**Checks.**
- `test_double_int`: for `x ↦ 2x` on `ℤ`, `0` is periodic and `1` is not preperiodic.
- `test_square_zmod`: for `x ↦ x²` on `ZMod 10`, every point is preperiodic, and `2` is not
  periodic.

## Layer 1: ramification in codimension one

### 1.1 Ramification index one, étaleness and reduced fibres

Let `f : X ⟶ Y` be a finite dominant morphism of normal varieties over a field `k` of
characteristic zero and `x` a codimension-one point. Prove `ramificationIdxAt_eq_one_iff`:
`ramificationIdxAt f x = 1` iff `f` is étale at `x` (Stacks, Lemma 29.36.14 (02GF) (6) and Lemma
29.37.15 (02GU); the stalk of `X` is torsion free, hence flat, over the stalk of `Y`, and residue
extensions are separable in characteristic zero). For a finite dominant `g : X' ⟶ Y'` of varieties
over a field `k` of any characteristic, with `X'` normal, prove
`isReduced_fiber_iff_forall_ramificationIdxAt_eq_one`: the fibre of `g` over a codimension-one
point `η` of `Y'` is reduced iff every point of `X'` over `η` has ramification index one (the local
ring of the fibre at `x` is `𝒪_{X',x} ⧸ 𝔪_x^e`; no normality of `Y'` is needed). For `char k = 0`
and arbitrary `X'`, prove `isReduced_fiber_iff_forall_formallyUnramified`: the fibre over `η` is
reduced iff `g` is unramified at every point over `η` (02GF (6)). This needs `char k = 0`: over
`k = 𝔽_p(t)`, `x ↦ x^p` on `𝔸¹` has reduced fibre `k[x] ⧸ (x^p − t)` over `y = t`, a field, but
is not unramified there (the residue extension is inseparable).
*Needs:* SchemeAndStackFoundations §0.30; PurityOfBranchLocus §0.1; Mathlib `Module.Flat` for
torsion-free modules over a discrete valuation ring (`@[stacks 0AUW]`), `Scheme.Hom.fiber`.

## Layer 2: normalization and the normalization lift

### 2.1 The normalization of an integral scheme

For an integral scheme `X`, define `normalization X` as Mathlib's normalization of `X` in its
generic point, `(X.fromSpecStalk (genericPoint X)).normalization`, and `normalizationHom X` its
morphism to `X`. Prove `IsNormalScheme (normalization X)` (Stacks, Lemma 29.54.13 (035L)), that
`normalizationHom X` is integral, dominant and surjective and an isomorphism on generic stalks, that
it is an isomorphism when `X` is normal, and `isFinite_normalizationHom`: for a variety `X` it is
finite and `normalization X` is again a variety (SchemeAndStackFoundations §0.20
`nagata_normalization_finite`).
*Needs:* SchemeAndStackFoundations §§0.20–0.21, 0.30; Mathlib `Scheme.Hom.normalization`,
`Scheme.fromSpecStalk`, `genericPoint`; Tau Ceti
`TauCeti.AlgebraicGeometry.isIso_normalizationDesc_fromSpecStalk_genericPoint`, which postdates the
roadmap's Tau Ceti pin `a91d3aaf` (it is in Tau Ceti `main` from `05bc128`).

### 2.2 The normalization lift

For a dominant `f : X ⟶ Y` of integral schemes define `normalizationLift f :
normalization X ⟶ normalization Y` with `normalizationLift_comp_normalizationHom`:
`normalizationLift f ≫ normalizationHom Y = normalizationHom X ≫ f` (Stacks, Lemma 29.55.5 (035Q)
(4)), and prove `normalizationLift_unique` (it is the unique dominant morphism over `f`),
`normalizationLift_id`, `normalizationLift_comp`, `normalizationLift_iterateHom`, and that the lift
of a finite dominant morphism of varieties is finite and dominant.
*Needs:* §2.1; Mathlib `Scheme.Hom.normalizationDesc`, `normalization.hom_ext`; Tau Ceti
`Scheme.Hom.normalizationMap` (after the pin, see above).

**Checks.**
- `test_cusp_normalization`: the normalization of `Spec k[t², t³]` is `Spec k[t]`, and the lift of
  the identity is the identity.

## Layer 3: divisorial loci and postcritical sets

### 3.1 The six divisorial loci

For a dominant `f : X ⟶ Y` of integral schemes, define:

- the *divisorial critical locus* `divisorialCriticalLocus f`: the images under `normalizationHom X`
  of the codimension-one points `x̃` of `normalization X` with
  `1 < ramificationIdxAt (normalizationLift f) x̃`;
- the *divisorial branch locus* `divisorialBranchLocus f := f '' divisorialCriticalLocus f`;
- the *non-unramified divisorial critical locus* `nonUnramifiedDivisorialCriticalLocus f`: the
  codimension-one points of PurityOfBranchLocus §0.4 `f.ramificationLocus` (where `f` is not
  unramified), and its image, the *non-unramified divisorial branch locus*
  `nonUnramifiedDivisorialBranchLocus f`, the codimension-one points of `f.branchLocus` when `f` is
  a finite dominant morphism of varieties;
- the *non-étale divisorial critical locus* `nonEtaleDivisorialCriticalLocus f`: the
  codimension-one points of PurityOfBranchLocus §0.4 `f.nonEtaleLocus`, and its image, the
  *non-étale divisorial branch locus* `nonEtaleDivisorialBranchLocus f`.

Prove `divisorialBranchLocus_eq_image_normalization`: `divisorialBranchLocus f` is the image under
`normalizationHom Y` of `divisorialBranchLocus (normalizationLift f)`. For a finite dominant
morphism of varieties over a field of characteristic zero, prove
`mem_divisorialBranchLocus_iff_not_isReduced_fiber`: a codimension-one point `η` of `Y` is in
`divisorialBranchLocus f` iff it is the image of a codimension-one point of `normalization Y` over
which the fibre of `normalizationLift f` is not reduced, and
`mem_nonUnramifiedDivisorialBranchLocus_iff_not_isReduced_fiber`: `η` is in
`nonUnramifiedDivisorialBranchLocus f` iff the fibre of `f` over `η` is not reduced (§1.1).
*Needs:* §§1.1, 2.2; SchemeAndStackFoundations §0.30; PurityOfBranchLocus §§0.1, 0.4.

### 3.2 Finiteness and comparison

For a finite dominant morphism `f` of varieties over a field of characteristic zero, prove
`finite_nonEtaleDivisorialCriticalLocus` (the non-étale points form a closed set missing the generic
point, so it contains finitely many codimension-one points, §4.1), and the comparison
`divisorialCriticalLocus f ⊆ nonUnramifiedDivisorialCriticalLocus f ⊆
nonEtaleDivisorialCriticalLocus f`, with the same chain for the branch loci; so all six loci are
finite. Prove `divisorialCriticalLocus_eq_nonEtale_of_isNormalScheme`: if `X` and `Y` are normal the
three critical loci coincide (§1.1). In any characteristic, prove
`divisorialCriticalLocus_subset_nonUnramified_of_isNormalScheme`: for `f` finite and dominant with
`X` normal, `divisorialCriticalLocus f ⊆ nonUnramifiedDivisorialCriticalLocus f`, hence
`⊆ nonEtaleDivisorialCriticalLocus f`, with the same chain for the branch loci and the postcritical
sets. Here `normalizationHom X` is an isomorphism, and ramification index `e > 1` at `x` over the
point `ỹ` of `normalization Y` gives `𝔪_y 𝒪_x ⊆ 𝔪_ỹ 𝒪_x ≠ 𝔪_x`, so `f` is not unramified at `x`
(Stacks, Lemma 29.36.14 (02GF) (6)).
*Needs:* §§1.1, 3.1, 4.1; Mathlib `Algebra.etaleLocus` and its openness.

### 3.3 Towers

For finite dominant `f : X ⟶ Y` and `g : Y ⟶ Z` of varieties over a field of characteristic zero,
prove the tower formula `divisorialBranchLocus_comp`:
`divisorialBranchLocus (f ≫ g) = divisorialBranchLocus g ∪ g '' divisorialBranchLocus f`
(SchemeAndStackFoundations §0.30 `ramificationIdxAt_comp` on the normalization lifts, §2.2
`normalizationLift_comp`, and `codimensionOneMap_surjective` for the reverse inclusion). For the
unnormalized loci prove `nonUnramifiedDivisorialCriticalLocus_subset_comp`:
`nonUnramifiedDivisorialCriticalLocus f ⊆ nonUnramifiedDivisorialCriticalLocus (f ≫ g)`, and
`nonEtaleDivisorialCriticalLocus_subset_comp`: `nonEtaleDivisorialCriticalLocus f ⊆
nonEtaleDivisorialCriticalLocus (f ≫ g) ∪ f ⁻¹' nonEtaleDivisorialCriticalLocus g`.
*Needs:* §§1.1, 2.2, 3.1; SchemeAndStackFoundations §0.30.

### 3.4 Postcritical sets

For a dominant `φ : X ⟶ X` of an integral scheme define `postcriticalSet φ :=
Function.forwardOrbit φ (divisorialBranchLocus φ)` and `IsPCF φ := (postcriticalSet φ).Finite`;
likewise `nonUnramifiedPostcriticalSet`, `nonEtalePostcriticalSet`, `IsNonUnramifiedPCF`,
`IsNonEtalePCF`. For a finite dominant self-map of a variety over a field of characteristic zero
prove:

- `isPCF_tfae`: `φ` is PCF, iff every point of `divisorialBranchLocus φ` is preperiodic, iff
  `φ^[r + s] '' divisorialCriticalLocus φ = φ^[r] '' divisorialCriticalLocus φ` for some `r` and
  `s ≥ 1`;
- `divisorialBranchLocus_iterateHom`: `divisorialBranchLocus (iterateHom φ m) =
  ⋃ i < m, φ^[i] '' divisorialBranchLocus φ` for `m ≥ 1`; `postcriticalSet_iterateHom`:
  `postcriticalSet (iterateHom φ m) = postcriticalSet φ`; `isPCF_iterateHom_iff`; and the orbit
  propagation `iterate_mem_divisorialBranchLocus_iterateHom`: for `x ∈ divisorialBranchLocus φ`,
  `φ^[n] x ∈ divisorialBranchLocus (iterateHom φ (n + 1))`;
- `postcriticalSet_subset_nonUnramifiedPostcriticalSet`,
  `nonUnramifiedPostcriticalSet_subset_nonEtalePostcriticalSet`, so `IsNonEtalePCF φ →
  IsNonUnramifiedPCF φ → IsPCF φ`, with equality of all three when `X` is normal; and the orbit
  propagation of the non-étale locus `iterate_mem_nonEtaleDivisorialBranchLocus_iterateHom`: for
  `x ∈ nonEtaleDivisorialBranchLocus φ` and `n ≥ 1`, `φ^[n] x ∈ nonEtaleDivisorialBranchLocus
  (iterateHom φ j)` for some `j ≥ 1`.

*Needs:* §§0.1–0.2, 3.2–3.3.

### 3.5 Normalization and ramified covers

Prove `postcriticalSet_eq_image_normalization`: `postcriticalSet φ` is the image under
`normalizationHom X` of `postcriticalSet (normalizationLift φ)`, and `isPCF_normalizationLift_iff`.
Prove `IsPCF.of_semiconj`: for finite dominant self-maps `φ : X ⟶ X`, `ψ : W ⟶ W` of varieties over
a field of characteristic zero and a finite dominant `π : W ⟶ X` with `ψ ≫ π = π ≫ φ`, if `ψ` is
PCF then so is `φ` (`postcriticalSet φ` lies in `π '' postcriticalSet ψ ∪ divisorialBranchLocus π`,
a finite forward-invariant set, by §3.3 applied to both sides).
*Needs:* §§0.2, 2.2, 3.3–3.4; SchemeAndStackFoundations §0.30.

**Checks.**
- `test_tower_unnormalized_strict`: on the pinched plane of §6, the reverse inclusion of the tower
  formula fails for the non-étale branch locus.

## Layer 4: closures of points

### 4.1 Codimension-one points in a closed subset

Prove `finite_coheight_eq_one_of_isClosed`: in an integral scheme with Noetherian underlying space,
a closed subset `Z ≠ ⊤` contains finitely many codimension-one points (each is the generic point of
an irreducible component of `Z`).
*Needs:* Mathlib `NoetherianSpace`, `irreducibleComponents`, `Order.coheight`.

### 4.2 Reduced closures

For `y : X` define `pointClosure y`, the reduced closed subscheme on `closure {y}`
(`(Scheme.IdealSheafData.vanishingIdeal ⟨closure {y}, _⟩).subscheme`), and `pointClosureι y`. Prove
that it is integral with generic point over `y`, that it is a variety over `k` when `X` is (with
structure morphism `pointClosureι y ≫ s`), and `topologicalKrullDim_pointClosure_add_one`: for a
variety `X` and a codimension-one point `y`, `topologicalKrullDim (pointClosure y) + 1 =
topologicalKrullDim X`.
*Needs:* SchemeAndStackFoundations §0.7; Mathlib `Scheme.IdealSheafData.vanishingIdeal`,
`subscheme`, `isIntegral_of_irreducibleSpace_of_isReduced`, `topologicalKrullDim`; Tau Ceti
`TauCeti.AlgebraicGeometry.topologicalKrullDim_eq_toNat_trdeg_functionField`.

### 4.3 Induced maps on closures

For finite `f : X ⟶ Y` and `y : X` define `pointClosureMap f y : pointClosure y ⟶ pointClosure (f
y)`, the unique morphism with `pointClosureMap f y ≫ pointClosureι (f y) = pointClosureι y ≫ f` (a
morphism from a reduced scheme factors through a closed subscheme containing its image, Stacks,
Lemma 26.12.7 (0356)), and prove it finite and surjective, hence dominant. For `φ : X ⟶ X` with `φ y
= y` define `restrictPointClosure φ y`, prove `restrictPointClosure_iterateHom` (compatibility with
iterates) and `normalizationHom_restrictPointClosure`: for a codimension-one point `ỹ` of
`normalization X` over `y` fixed by `normalizationLift φ`, the map `pointClosure ỹ ⟶ pointClosure y`
induced by `normalizationHom X` is finite and surjective and intertwines the two restrictions.
*Needs:* §§2.2, 4.2; SchemeAndStackFoundations §0.30; Mathlib `IsClosedImmersion.lift`, `IsFinite`.

## Layer 5: the bounding theorem

### 5.1 Setup and properness of the exceptional set

Let `f : X ⟶ Y` be a finite dominant morphism of normal varieties over a field `k` of
characteristic zero, `a` a codimension-one point of `X`, and `B = pointClosure (f a)`. Let `Z ⊆ Y`
be the union of the closures of the points of `divisorialBranchLocus f` other than `f a`, and define
the *exceptional set*
`boundingLocus f a := (closure {f a} ∩ Z) ∪ (closure {f a} ∩ Sing Y) ∪ pointClosureι (f a) '' Sing B`,
where `Sing` is the complement of SchemeAndStackFoundations §4.13 `regularLocus`. Prove
`isClosed_boundingLocus` and `notMem_boundingLocus_self`: `f a ∉ boundingLocus f a` (a normal
scheme is regular at codimension-one points, SchemeAndStackFoundations §0.30; the regular locus of
a variety over a field of characteristic zero is open, §4.13 *regularLocus_eq_smoothLocus*); so
`boundingLocus f a` contains finitely many codimension-one points of `B` (§4.1).
*Needs:* §§3.2, 4.1–4.2; SchemeAndStackFoundations §§0.30, 4.13; Mathlib `smoothLocus`.

### 5.2 The standard piece

For `A` Noetherian, `a` a nonzerodivisor with `A ⧸ aA` regular, `u` a unit and `e ≥ 1` invertible,
put `C = A[z]/(z^e − ua)`. Prove `standardPiece_radical_eq` (*API*): the radical of `aC` is `zC`,
and `A ⧸ aA → C ⧸ zC` is an isomorphism; so the reduced preimage of `V(a)` maps isomorphically onto
`V(a)`.
*Needs:* AbhyankarLemma §3.1 (`standardTameCover`); Tau Ceti `TauCeti.IsRegularLocalRing.isDomain`.

### 5.3 The bounding theorem

Prove `isEtaleAt_pointClosureMap_of_notMem_boundingLocus`: in the setting of §5.1, for every
codimension-one point `x` of `pointClosure a` whose image in `Y` is not in `boundingLocus f a`, the
morphism `pointClosureMap f a` is étale at `x`. The proof: choose an affine open `U ∋ η` of `Y`
(`η` the image of `x`) missing `Z`, `Sing Y` and `Sing B`; `D = B ∩ U` is a regular divisor on the
regular scheme `U` (SchemeAndStackFoundations §0.30 `exists_regularSystem_of_quotient`); over
`U ∖ D` the morphism `f` is étale by purity (PurityOfBranchLocus §2.1), with §1.1 for the
codimension-one hypotheses; `f⁻¹ U` is the normalization of `U` in `f⁻¹(U ∖ D)`: by the
characterization of the normalization (Stacks, Lemma 29.54.4 (035I); Mathlib
`Scheme.Hom.normalizationDesc`) the normalization `U'` of `U` in `f⁻¹(U ∖ D)` comes with a map
`U' ⟶ f⁻¹ U` that is the normalization of `f⁻¹ U` in its dense open `f⁻¹(U ∖ D)`, an isomorphism
because `f⁻¹ U` is normal and integral (a function on `f⁻¹(U ∖ D)` integral over `𝒪(f⁻¹ U)` is
in `𝒪(f⁻¹ U)`); in characteristic zero every finite
étale cover is tamely ramified in codimension one, so Abhyankar's lemma (AbhyankarLemma §§3.3–3.4)
presents `f⁻¹ U → U`, étale locally, as a finite disjoint union of standard pieces; §5.2 shows that
the reduced preimage of `D` maps isomorphically onto `D` on each piece; and étaleness descends
(PurityOfBranchLocus §1.1, 036W). Prove the companion
`nonEtaleDivisorialBranchLocus_pointClosureMap_subset`: every point of
`nonEtaleDivisorialBranchLocus (pointClosureMap f a)`, hence of the other two divisorial branch
loci, lies in `boundingLocus f a`.
*Needs:* §§1.1, 3.1–3.2, 4.3, 5.1–5.2; PurityOfBranchLocus §§1.1, 2.1; AbhyankarLemma §§1.1,
3.3–3.4; SchemeAndStackFoundations §0.30.

**Checks.**
- `test_bounding_cusp`: for `f(u, v) = (u², u³ + v)` on `𝔸²` and `a` the generic point of `V(v)`,
  `pointClosureMap f a` is the normalization of the cuspidal cubic: its divisorial branch locus is
  empty while `closure {f a} ∩ Z = {(0, 0)} = boundingLocus f a`. So the inclusion of the
  divisorial branch locus in `boundingLocus f a` is strict, while the companion inclusion of §5.3
  is an equality: the normalization `𝔸¹ ⟶ {y² = x³}` is not étale at `t = 0`, so
  `nonEtaleDivisorialBranchLocus (pointClosureMap f a) = {(0, 0)}`.
- `test_bounding_singular_target`: for `𝔸² → Spec k[x, y, z]/(xz − y²)`, `(u, v) ↦ (u², uv, v²)`
  and `a` the generic point of `V(v)`, the restriction `u ↦ u²` ramifies at the origin although
  `Z = ∅`; the term `closure {f a} ∩ Sing Y` is needed.
- `test_bounding_needs_normal`: on the pinched plane of §6 the conclusion of §5.3 fails; the source
  is not normal at the pinched point.

## Layer 6: PCF all the way down

### 6.1 Invariant divisors of normal varieties

Prove `isPCF_restrictPointClosure_of_isNormalScheme`: let `φ` be a finite dominant PCF self-map of
a normal variety `X` over a field of characteristic zero and `a` a codimension-one point with
`φ a = a`. Then `restrictPointClosure φ a` is PCF. The proof applies §5.3 to every iterate
`iterateHom φ m`, with the exceptional set of `φ` built from the members of `postcriticalSet φ`
other than `a` (§3.4), which does not depend on `m`; every orbit in
`divisorialBranchLocus (restrictPointClosure φ a)` stays among its finitely many codimension-one
points.
*Needs:* §§3.4, 4.1, 4.3, 5.1, 5.3.

### 6.2 Preperiodic divisors of normal varieties

Prove `isPCF_restrictPointClosure_of_isNormalScheme_of_preperiodic`: for `a` with
`φ^[r + s] a = φ^[r] a`, `s ≥ 1`, the restriction of `iterateHom φ s` to `pointClosure (φ^[r] a)`
is PCF (§3.4 and §6.1). Prove the non-étale refinement
`isNonEtalePCF_restrictPointClosure_of_isNormalScheme`: the restriction is also non-étale and
non-unramified PCF (§5.3 companion and §3.4), and its chain form
`isNonEtalePCF_of_normal_chain` along a chain of preperiodic prime divisors whose intermediate
members are normal.
*Needs:* §§3.4, 5.3, 6.1.

### 6.3 The general case

Prove `isPCF_restrictPointClosure`: let `φ` be a finite dominant PCF self-map of a variety `X` over
a field of characteristic zero, `a` a codimension-one point with `φ^[r + s] a = φ^[r] a` and
`s ≥ 1`, and `y = φ^[r] a`. Then the restriction of `iterateHom φ s` to `pointClosure y` is PCF.
The proof passes to the normalization: `normalizationLift φ` is PCF (§3.5); the codimension-one
points of `normalization X` over `y` form a finite set mapped to itself by the lift of
`iterateHom φ s` (SchemeAndStackFoundations §0.30), which therefore has a periodic point `ỹ`
(§0.2); §6.2 applies to `ỹ`; and §3.5 transports the conclusion along the finite surjective map of
closures (§4.3), with §3.4 for the iterate.
*Needs:* §§0.2, 2.2, 3.4–3.5, 4.3, 6.2; SchemeAndStackFoundations §0.30.

### 6.4 PCF all the way down

Define `IsPCFAllTheWayDownAtDepth d φ` by recursion on `d`: at depth `0`, `φ` is PCF; at depth
`d + 1`, moreover, for every codimension-one point `x`, every `r` and every `s ≥ 1` with
`φ^[r + s] x = φ^[r] x`, the restriction of `iterateHom φ s` to `pointClosure (φ^[r] x)` is PCF all
the way down at depth `d`. Define `IsPCFAllTheWayDown φ` as holding at every depth. Prove
`isPCFAllTheWayDownAtDepth_of_dim_le` (for a variety `X`, depth `topologicalKrullDim X` implies
every depth, §4.2), `isPCFAllTheWayDown_iff_isPCF_of_dim_le_one`, and **`isPCFAllTheWayDown`**:
every finite dominant PCF self-map of a variety over a field of characteristic zero is PCF all the
way down (induction on the depth with §6.3; each restriction is a finite dominant self-map of a
variety by §§4.2–4.3).
*Needs:* §§4.2–4.3, 6.3.

**Checks.**
- `test_squaring_line`: `x ↦ x²` on `𝔸¹_k`, `char k = 0`: `divisorialBranchLocus = postcriticalSet =
  {0}`.
- `test_basilica`: `x ↦ x² − 1` on `𝔸¹_k`, `char k = 0`: `postcriticalSet = {−1, 0}` with `0` of
  period two.
- `test_squaring_plane`: `(x, y) ↦ (x², y²)` on `𝔸²_k`, `char k = 0`: the divisorial critical locus
  is the two axes, both invariant, the restrictions are the squaring map of `𝔸¹`, and the map is PCF
  all the way down; the diagonal `V(x − y)` is invariant and not in `postcriticalSet`.
- `test_pinched_plane`: let `R = {h ∈ k[z, w] : h(2, 1) = h(−2, 1)}`, `X = Spec R`, and `φ` induced by
  `(z, w) ↦ (z², w²)`. Then `φ` is PCF, non-unramified PCF and non-étale PCF; the image `B` of
  `V(w − 1)` is invariant; the restriction of `φ` to `B` is PCF but neither non-unramified PCF nor
  non-étale PCF, while its normalization lift `z ↦ z²` is all three.
- `test_frobenius_line`: over a field of characteristic `p`, `f(x, y) = (x^p + xy, y)` on `𝔸²` has
  ramification index one along the invariant line `V(y)` and is not étale there; its restriction to
  `V(y)` is the Frobenius `x ↦ x^p`, which is not étale at any point.

## Layer 7: self-maps of projective space

### 7.1 Self-maps given by forms

Let `ℙⁿ_k := Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)` (with
`MvPolynomial.gradedAlgebra`). A *system of forms of degree `d ≥ 1`* is
`F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) k` with every `F i` homogeneous of degree `d` and
every `X j` in the radical of `Ideal.span (Set.range F)` (no common zero over an algebraic
closure). Define `ProjectiveSpace.homOfForms F : ℙⁿ_k ⟶ ℙⁿ_k` (*API*): the unique morphism with
`(homOfForms F) ⁻¹ᵁ Proj.basicOpen _ (X b) = Proj.basicOpen _ (F b)` on which it is given by
`X i / X b ↦ F i / F b`. Prove `ProjectiveSpace.isFinite_homOfForms` (`k[X]` is a finite module over
`k[F_0, …, F_n]` by graded Nakayama, since the quotient by the `F i` is finite-dimensional),
`homOfForms_comp` (composition is substitution), and that `ℙⁿ_k` is a variety over `k` in the
sense of Convention 3.
*Needs:* Mathlib `Proj`, `Proj.basicOpen`, `Proj.awayι`, `HomogeneousLocalization`,
`MvPolynomial.IsHomogeneous`, `Ideal.radical`.

### 7.2 The Jacobian criterion

With `J = det (∂F i / ∂X j)`, prove `ProjectiveSpace.isEtaleAt_homOfForms_iff` (*API*): if `d` is
invertible in `k`, `homOfForms F` is étale at `ξ` iff `J` does not vanish at `ξ` (Euler's identity
reduces to the affine Jacobian on each chart; unramified iff the Kähler differentials vanish,
Stacks 02GF (3); a finite surjective morphism of smooth varieties of the same dimension is flat,
LocalPurity §0.1 `flat_of_isCohenMacaulay` (00R4)). In characteristic zero,
`ProjectiveSpace.divisorialCriticalLocus_homOfForms`: the divisorial critical locus is the set of
generic points of the codimension-one components of `V₊(J)`.
*Needs:* §§1.1, 3.2, 7.1; LocalPurity §0.1; PurityOfBranchLocus §0.1; Mathlib
`KaehlerDifferential`, `MvPolynomial.pderiv`, `Matrix.det`.

**Checks.**
- `test_squaring_projective`: `[x₀ : x₁] ↦ [x₀² : x₁²]` on `ℙ¹`, `char k = 0`:
  `postcriticalSet = {0, ∞}`.
- `test_squaring_P2`: `[x : y : z] ↦ [x² : y² : z²]` on `ℙ²`, `char k = 0`, is PCF all the way
  down; its `postcriticalSet` is the three coordinate lines.
- `test_dupont`: `φ = [(x − y + z)² : (x + y − z)² : (−x + y + z)²]` on `ℙ²`, `char k = 0`: the
  divisorial critical locus is the three lines `x − y + z = 0`, `x + y − z = 0`, `−x + y + z = 0`;
  the divisorial branch locus is the coordinate lines `H₀, H₁, H₂`; `φ(Hᵢ) = Mᵢ` with
  `M₀ = V(x − y)`, `M₁ = V(y − z)`, `M₂ = V(x − z)`, and `φ(M₀) = M₂`, `φ(M₂) = M₁`,
  `φ(M₁) = M₀`; so `postcriticalSet φ = {H₀, H₁, H₂, M₀, M₁, M₂}` and no branch line is periodic.
- `test_wild`: over `k` of characteristic `p` containing `c` transcendental over `𝔽_p`, `F = [x^p(x
  + y) : y^{p+1} − x^{p+1} − x^p z + x y^p + c z^{p+1} : z^{p+1}]` on `ℙ²` is a finite self-map with
  non-étale divisorial critical locus `V(x) ∪ V(z)`, both lines invariant, so non-étale PCF, and PCF
  by `divisorialCriticalLocus_subset_nonUnramified_of_isNormalScheme` (§3.2, valid in characteristic
  `p`; `ℙ²` is normal); its restriction to `V(x)` is `t ↦ t^{p+1} + c`, whose critical orbit `0 ↦ c
  ↦ c^{p+1} + c ↦ ⋯` is infinite (the `n`-th term has degree `(p + 1)^{n−1}` in `c`). So §6.4 fails
  in characteristic `p`.

## Stacks alignment

*Exact*: the tag's hypotheses and conclusion, in Mathlib's vocabulary. *Accompanying*: a Stacks-form
restatement of a target. *API*: no Stacks counterpart.

| Target | Tag | Alignment |
|---|---|---|
| `ramificationIdxAt_eq_one_iff` | 02GF (6), 02GU | characteristic zero, codimension one, normal |
| `isReduced_fiber_iff_forall_formallyUnramified` | 02GF (6) | characteristic zero, over a codimension-one point |
| `isNormalScheme_normalization` | 035L | the normalization in the generic point |
| `normalizationLift` | 035Q (4) | integral schemes, dominant morphisms |
| `pointClosureMap` | 0356 | reduced source, closed subscheme target |
| `isEtaleAt_pointClosureMap_of_notMem_boundingLocus` | — | the bounding theorem; inputs 0BMB, 036W, 0EYG, 0EYH, 035I, 00NR |
| `ProjectiveSpace.isEtaleAt_homOfForms_iff` | — | API; inputs 02GF (3), 02GU, 00R4 |
| every other target | — | API |

## Provenance

This roadmap is written to be implemented afresh. The source is the manuscript *PCF all the way
down* (Dupuy, Levy, Tucker, Wang; in preparation), cited by its labels, and the Lean formalization
`tdupu/pcfawd-formalization` (Dupuy, Tucker, Wang; Lean `4.35.0`, Mathlib `v4.35.0`). Its theorem
`Pcf.Palomar.pcfAllTheWayDown_charZero_unconditional` has the hypotheses of Convention 3 and is
equivalent to §6.4, not identical with it: its PCF hypothesis and recursion use `IsNormalizedPCF`
(finiteness of the postcritical set on `X̃` of the normalization lift) rather than `IsPCF`, and its
depth-`d + 1` clause ranges over the periodic points `y` of period `p` in the forward orbit of a
codimension-one point and over every `h` with `h ≫ ι = ι ≫ iterateHom φ p`, rather than over
`restrictPointClosure`. The two agree for varieties by §3.5 (`isPCF_normalizationLift_iff`) and
because closed immersions are monomorphisms. Its local inputs, Zariski–Nagata purity and
Abhyankar's lemma, are proved there in affine forms. The formalization keeps its own names; this
table maps them.

| Here | Manuscript | Formalization (`lean/Pcf/`) |
|---|---|---|
| `divisorialCriticalLocus`, `divisorialBranchLocus` | `Crit`, `Branch` (`def:crit-branch`) | `NormalizationUnnormalizedDynamics.criticalLocus`, `.branch` (`Bounding/NormalizationPcfEquiv.lean`); `DivisorDynamics.branch` (`Dynamics.lean`); `schemeNormalizedBranch` |
| `nonUnramifiedDivisorialCriticalLocus`, `nonUnramifiedDivisorialBranchLocus` | `Crit_0`, `Branch_0` (`def:crit-unnormalized`, `def:branch-loci`) | `UnnormalizedDynamics.nonUnramifiedLocus`, `.nonUnramifiedBranch` (`Unnormalized.lean`) |
| `nonEtaleDivisorialCriticalLocus`, `nonEtaleDivisorialBranchLocus` | `Crit_1`, `Branch_1` | `.nonEtaleLocus`, `.nonEtaleBranch`; `schemeNonEtaleLocus` (`Bounding/CriticalLoci.lean`) |
| `postcriticalSet`, `IsPCF` | `PC`, PCF (`def:pcf`) | `DivisorDynamics.postcriticalSet`, `.IsPCF`; `schemeNormalizedPostcriticalSet`, `IsNormalizedPCF` |
| `nonUnramifiedPostcriticalSet`, `nonEtalePostcriticalSet`, `IsNonUnramifiedPCF`, `IsNonEtalePCF` | `PC_0`, `PC_1`, `0`-PCF, `1`-PCF (`def:pcf-unnormalized`) | `nonUnramifiedPostcriticalSet`, `nonEtalePostcriticalSet`, `IsNonUnramifiedBranchPCF`, `IsNonEtaleBranchPCF` |
| `IsPCFAllTheWayDown` | `def:pcfawd` | `SchemePCFAllTheWayDown` (`Bounding/PcfAllTheWayDownCharZero.lean`) |
| §1.1 | `lem:dictionary`, `lem:branch-crit` | only the direction étale ⇒ index one: `schemeDivisorRamificationIdx_eq_one_of_formallyEtale` (`Bounding/SchemeDynamics.lean`); the ring-level fibre criterion with both rings normal: `divisorFiber_isReduced_iff_forall_ramificationIdx_eq_one` (`Bounding/ReducedFiberBranch.lean`) |
| §2 | `sec:defs` | `schemeGlobalNormalizationMorphism`, `_unique`, `schemeGlobalNormalization_isNormal`, `schemeGlobalNormalizationMap_isFinite` (`Bounding/GlobalNormalization*.lean`) |
| §3.3–3.5 | `lem:tower`, `prop:iterates`, `prop:pcf-equiv`, `lem:normalization`, `lem:covers` | `branchIterate_eq`, `postcriticalSet_iterate` (`Dynamics.lean`); `isNormalizedPCF_iff_normalization`; `scheme_isPCF_of_ramified_cover_charZero` (`Bounding/CoverDescent.lean`) |
| §4 | `lem:finitely-many`, `lem:restriction` | `finite_schemeDivisorPoint_mem_of_isClosed`; `exists_pointClosure_restriction` (`Palomar/Bridge.lean`) |
| §5.3 | `thm:bounding` | the chart route of `Bounding/` (`LocalChart.lean`, `SchemeBridge.lean`, `SchemeExtraction.lean`), for invariant divisors |
| §6.1–6.4 | `thm:normal-invariant`, `cor:normal-preperiodic`, `thm:general`, `cor:pcfawd` | `PCFSetup.restriction_isPCF` (`Restriction.lean`); `pcfAllTheWayDown_scheme`; `Pcf.Palomar.pcfAllTheWayDown_charZero_unconditional` (`Palomar/Unconditional.lean`; equivalent to §6.4, see above) |
| §6.2 refinement | `prop:normal-unnormalized`, `cor:chains-unnormalized` | abstract form only: `NonEtalePCFSetup.restriction_isNonEtaleBranchPCF` (`Unnormalized.lean`), whose key inclusion `notMem_nonEtaleBranch_iterate` is a structure field; the scheme-level forms (`InvariantDivisorSchemeNormalizationPCFSetup.restriction_isNonEtaleBranchPCF`, `Bounding/SchemeWiring.lean`) take the local covering package as data, and no unconditional scheme-level statement is proved |
| Checks | `ex:squaring`, `ex:basilica`, `ex:squaring-P2`, `ex:dupont`, `ex:cusp`, `ex:branch-singular`, `ex:pinched`, `ex:frobenius-line`, `ex:wild` | `Examples/` (abstract and ring-level models) |

## References

- A. Bridy, P. Ingram, R. Jones, J. Juul, A. Levy, M. Manes, S. Rubinstein-Salzedo, J. H. Silverman,
  *Finite ramification for preimage fields of post-critically finite morphisms*, Math. Res. Lett.
  24 (2017), 1633–1647; [arXiv:1511.00194](https://arxiv.org/abs/1511.00194). Example 9 (Dupont's
  map) and the question of PCF all the way down.
- The Stacks Project, Tags 0356, 035I, 035J, 035L, 035Q, 02GF, 02GU, 0AUW, 0AVK; and through
  the cited roadmaps 033I, 00NR, 02G4, 0BMB, 036W, 0EYG, 0EYH, 00R4.
- T. Dupuy, A. Levy, T. Tucker, Z. Wang, *PCF all the way down*, in preparation.
- T. Dupuy, T. Tucker, Z. Wang, Lean formalization `tdupu/pcfawd-formalization`.
