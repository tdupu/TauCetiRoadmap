# Roadmap: étaleness from codimension one and finite étale extension across depth two

**Summary.** This roadmap proves two results of Stacks, Section 58.21. The first is that a flat
morphism of locally Noetherian schemes, quasi-finite at a point `x` that is not the generic point
of an irreducible component, and unramified at every codimension-one point specializing to `x`, is
étale at `x` (Stacks, Lemma 58.21.2 (0BJH)). The second is the extension of a finite étale cover
across a closed subset of depth `≥ 2` (Stacks, Lemma 58.21.5 (0EY6)). For an open `j : U → X` of a
locally Noetherian scheme with `depth 𝒪_{X,x} ≥ 2` at every `x ∉ U`, and a finite étale
`π : V → U`, the algebra `𝓑 = j_*π_*𝒪_V` is coherent and reflexive, and its relative spectrum
`Y → X` is the unique finite morphism with `Y ×_X U = V` and depth `≥ 2` off `V`. It is étale
exactly where it is flat, and étale everywhere exactly when `𝓑` is finite locally free. The
construction commutes with flat base change and with enlarging `U`. The first result is the
input to the third clause of the second.

Mathlib has étale, unramified and quasi-finite morphisms with their affine pointwise forms, a
finitely presented flat algebra unramified at a prime is étale there
(`Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat`, which needs global flatness), étale localization
of a quasi-finite algebra (`@[stacks 00UJ]`), the dimension formula for going down
(`@[stacks 00ON]`) and Krull's principal ideal theorem. Tau Ceti has the relative spectrum of a
quasi-coherent algebra and finite locally free modules on a scheme.
[LocalPurity](../LocalPurity/README.md) supplies the discriminant criterion for a finite free
algebra over a local ring. [PurityOfBranchLocus](../PurityOfBranchLocus/README.md) supplies the
pointwise notions in stalk form. [SchemeAndStackFoundations](../SchemeAndStackFoundations/README.md)
supplies direct-image algebras, reflexive sheaves, Hartogs extension and depth. None of them has
0BJH or 0EY6.

| Layer | Title | What it delivers |
|---|---|---|
| [0](#layer-0-commutative-algebra) | Commutative algebra | height-one primes through an element (0BJG), heights in flat quasi-finite extensions, the finite flat local case of 0BJH, unramifiedness along base change, étaleness at a prime from flatness at it |
| [1](#layer-1-étaleness-from-codimension-one) | Étaleness from codimension one | 0BJH in affine, library and Stacks forms |
| [2](#layer-2-finite-étale-extension-across-depth-two) | Finite étale extension across depth two | the construction `depthTwoExtension` and every clause of 0EY6 |

```text
Mathlib + Tau Ceti → Layer 0 → Layer 1 → Layer 2
LocalPurity §0.2 ─────────────→ Layer 0
PurityOfBranchLocus §0.1 ─────→ Layer 1
SchemeAndStackFoundations §§0.1, 0.2, 0.4, 0.6, 0.17; AlgebraicVectorBundles L1A ──→ Layer 2
LocalPurity §2.2 ─────────────→ Layer 2
```

The end theorems are `Scheme.Hom.exists_etale_of_flat_of_formallyUnramified_codimOne` (0BJH,
§1.2) and the clauses of 0EY6 in §2.2–§2.4, among them `depthTwoExtension_unique`,
`depthTwoExtension_etaleAt_iff_flat` and `depthTwoExtension_etale_iff`.

## Scope and ownership

**This roadmap owns** Stacks, Lemmas 58.21.1 (0BJG), 58.21.2 (0BJH) and 58.21.5 (0EY6); the
heights of primes along flat quasi-finite homomorphisms of Noetherian rings; the finite flat local
case of 0BJH; ascent and descent of unramifiedness at a prime along a base change; étaleness at a
prime from flatness and unramifiedness at that prime; the scheme
`depthTwoExtension π` attached to a finite étale cover of an open whose complement has depth
`≥ 2`, with its universal property; and the criterion for such a cover to extend to a finite étale
scheme over `X`.

**Owned elsewhere and consumed here.** Each object has one owner. This roadmap uses it and builds
no second carrier.

- *Finite étale schemes over a base*: Tau Ceti `TauCeti.FiniteEtaleScheme S` (module
  `TauCeti.AlgebraicGeometry.FiniteEtale.Basic`), equivalent to Mathlib's
  `(@IsFinite ⊓ @Etale).Over ⊤ S`. The targets are stated for either carrier.
- *The discriminant criterion*: [LocalPurity](../LocalPurity/README.md) §0.2
  (`Algebra.etale_iff_isUnit_discr`, Stacks 0BJF in affine form over a local base, and
  `Algebra.isUnit_discr_localization_iff`).
- *Restriction of finite étale schemes to an open of depth `≥ 2`*: LocalPurity §2.2
  (`restrictOpen_fullyFaithful_of_depth`). The local case of 0EY6, with `U` the punctured spectrum
  of a local ring, is LocalPurity §1.2 (`spec_sections_of_depth`, Stacks 0BM8, and
  `extends_iff_sections_finiteEtale`, Stacks 0BLK).
- *Pointwise notions*: [PurityOfBranchLocus](../PurityOfBranchLocus/README.md) Convention 3 and
  §0.1 (`Scheme.Hom.unramifiedAt_iff_stalkMap`, `Scheme.Hom.etaleAt_iff_stalkMap`,
  `Scheme.Hom.etaleAt_spec_iff`).
- *Direct-image algebras and flat base change*:
  [SchemeAndStackFoundations](../SchemeAndStackFoundations/README.md) §0.1 (`pushforwardAlgebra`,
  `pushforwardAlgebra_affine`, `pushforwardAlgebra_baseChange`, Stacks 02KH for `i = 0`).
- *Morphism properties of relative spectra*: SchemeAndStackFoundations §0.2 (finiteness of the
  relative spectrum of a finite quasi-coherent algebra: over an affine open it is the spectrum of a
  finite algebra, so criterion (2) of Morphisms, Lemma 29.45.3 (01WI) applies; Tau Ceti
  `relativeSpec_finite_iff`).
- *Coherent extension*: SchemeAndStackFoundations §0.4 (`coherent_extension`, Stacks 0G41).
- *Reflexive sheaves and Hartogs extension*: SchemeAndStackFoundations §0.6
  (`Scheme.Modules.IsReflexive`, `IsReflexive.locallyFree`, `IsReflexive.two_le_depth_stalk`,
  `reflexive_extension_of_depth`, `coherent_hartogs`, Stacks 0E9I).
- *Depth*: SchemeAndStackFoundations §0.17 (`IsLocalRing.depth`, `Module.depth`,
  `depth_le_supportDim` (00LK), `depth_eq_iInf_localization_maximal` (0AUK),
  `depth_eq_add_of_flat` (0337)).
- *Relative spectrum*: Tau Ceti `CategoryTheory.CommMon.relativeSpec` and the functor
  `TauCeti.AlgebraicGeometry.relativeSpec`, with its compatibility with restriction to opens and
  with base change from [AlgebraicVectorBundles](../AlgebraicVectorBundles/README.md) L1A.
- *Finite locally free modules*: Tau Ceti `Scheme.Modules.isFiniteLocallyFree`.
- *Étale localization, heights and unramified loci*: Mathlib
  `Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq` (`@[stacks 00UJ]`),
  `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown` (`@[stacks 00ON]`),
  `Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes`,
  `Module.supportDim_le_supportDim_quotSMulTop_succ_of_mem_jacobson`,
  `Algebra.unramifiedLocus_eq_compl_support`, `Algebra.FormallyEtale.of_formallyUnramified_of_field`,
  `Algebra.FormallySmooth.of_formallySmooth_residueField_tensor`.

Purity of the branch locus (Stacks 0BMB), which has the same reduction to a finite local model with
normality and regularity in place of flatness, is PurityOfBranchLocus. Abhyankar's lemma is
[AbhyankarLemma](../AbhyankarLemma/README.md).

## Conventions

1. Rings are commutative. Schemes and morphisms are Mathlib's `Scheme` and `Scheme.Hom` in a fixed
   universe `u`. Hypotheses are written on the statement that uses them.
2. **Statement form.** Every target is stated in Mathlib's and Tau Ceti's vocabulary, against the
   pinned libraries, and that statement is the target. Where the Stacks Project states the same
   result with different notions, an accompanying statement in the form of the tag is derived from
   it. Both carry `@[stacks XXXX]`. Targets with no Stacks counterpart are marked *API*.
3. **Pointwise notions** are those of PurityOfBranchLocus, Convention 3. *Flat at `x`* is
   `(f.stalkMap x).hom.Flat`, *unramified at `x`* is `(f.stalkMap x).hom.FormallyUnramified`,
   *quasi-finite at `x`* is `f.QuasiFiniteAt x`, and *étale at `x`* is
   `∃ W : X.Opens, x ∈ W ∧ Etale (W.ι ≫ f)`. The dimension of a local ring is `ringKrullDim`, and
   for a prime ideal it is `Ideal.height`.
4. **Depth.** Depth is SchemeAndStackFoundations' `IsLocalRing.depth`. *The complement of `U` has
   depth `≥ 2`* means `∀ x : X, x ∉ U → 2 ≤ IsLocalRing.depth (X.presheaf.stalk x)`, for a
   locally Noetherian `X` and `U : X.Opens`. *Coherent* means quasi-coherent of finite type on a
   locally Noetherian scheme. *Reflexive* is SchemeAndStackFoundations' `Scheme.Modules.IsReflexive`:
   the evaluation map to the double dual is an isomorphism. That definition is made on every
   locally Noetherian scheme.
5. **Reading of Stacks 0EY6.** Two points of the tag as written are fixed here.
   (i) *Reflexive for non-integral `X`.* 0EY6 does not assume `X` integral, while Stacks defines
   reflexive modules over domains (More on Algebra, Definition 15.24.1 (0AUZ); the remark after it
   notes that the definition can be made for more general rings, and does not pursue it) and
   reflexive sheaves on integral schemes only (Divisors, Definition 31.13.1 (0AVU)). The two
   lemmas its proof cites, 31.13.12 (0EBJ) and 31.13.11 (0EBI), both assume `X` integral. Clause
   (1) is stated here with Convention 4's reflexive, and the proof cites
   `reflexive_extension_of_depth` and `IsReflexive.two_le_depth_stalk` of SchemeAndStackFoundations
   §0.6, versions of 0EBJ and 0EBI (1) that assume only that `X` is locally Noetherian.
   (ii) *Clause (b).* The tag concludes "a unique isomorphism `Y' ×_X U' = V'` over `U'`", and
   `Y'` is not defined there. Its proof applies "the uniqueness in (2) … to the restriction
   `Y ×_X U'`", so the statement meant is a unique isomorphism `Y ×_X U' ≅ V'` over `U'`
   compatible with the given identification of the restrictions over `U`. The compatibility is
   needed for uniqueness: for `U' = U` and `V' = V = U ⊔ U`, swapping the two copies is a second
   isomorphism over `U'`. §2.4 states that form.
6. Names: ring-level statements live in the `Algebra`, `Ideal` and `IsLocalRing` namespaces, and
   scheme-level statements in `AlgebraicGeometry`. The suggested forms are in
   `TauCetiRoadmap.FiniteEtaleExtensionAcrossDepthTwo`, except that names written here with a
   Mathlib prefix (`Ideal.`, `Algebra.`, `Scheme.Hom.`) are declared at that full name.

## Layer 0: commutative algebra

### 0.1 Height-one primes through an element

Prove `exists_isPrime_height_eq_one_of_mem` (Stacks, Lemma 58.21.1 (0BJG)): in a Noetherian local
ring `(A, 𝔪)` with `1 ≤ ringKrullDim A`, every `f ∈ 𝔪` lies in a prime `𝔭` with `𝔭.height = 1`.
The proof is by induction on `ringKrullDim A`; for dimension one, `𝔪` works. For dimension at
least two, choose a minimal prime `𝔮` with `ringKrullDim (A ⧸ 𝔮) = ringKrullDim A`. Then
`A ⧸ (𝔮 + (f))` has dimension `≥ 1`
(`Module.supportDim_le_supportDim_quotSMulTop_succ_of_mem_jacobson` applied to `A ⧸ 𝔮`), so the
set of non-maximal primes containing `𝔮 + (f)` is nonempty. Since `A` is Noetherian it has a
maximal element `𝔯`. Then `ringKrullDim (A ⧸ 𝔯) = 1` and `𝔮 < 𝔯`, so
`1 ≤ 𝔯.height < ringKrullDim A`, and the induction hypothesis applied to `A_𝔯` and the image of
`f` gives the prime. This replaces Stacks' appeal to closed points of the punctured spectrum
(Properties, Lemma 28.6.4) by the Noetherian maximal element.
*Needs:* Mathlib `Ideal.height`, `ringKrullDim`, `minimalPrimes`,
`Module.supportDim_le_supportDim_quotSMulTop_succ_of_mem_jacobson`, `Localization.AtPrime`.

**Checks.**
- `test_height_one_prime`: for `A = k[x, y]` localized at `(x, y)` and `f = x`, the prime `(x)`
  works; for `A` a discrete valuation ring and `f` a uniformizer, only `𝔪` works.

### 0.2 Heights along flat quasi-finite homomorphisms

Prove `Ideal.height_eq_height_under_of_flat_of_quasiFiniteAt` (*API*): for a homomorphism
`R → S` of Noetherian rings and a prime `𝔮` of `S` with `Localization.AtPrime 𝔮` flat over `R`
and `Algebra.QuasiFiniteAt R 𝔮`, `𝔮.height = (𝔮.under R).height`. This is the dimension formula
`@[stacks 00ON]` for the flat local homomorphism `R_𝔭 → S_𝔮` (flat local homomorphisms satisfy going
down), with the fibre `S_𝔮 ⧸ 𝔭 S_𝔮` of dimension zero. Prove the corollary for étale `R → S`, and
for a finite flat `R → S`, where every prime is quasi-finite.
*Needs:* Mathlib `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`, `Algebra.HasGoingDown`,
`Algebra.QuasiFiniteAt`, `Algebra.Etale`.

### 0.3 The finite flat local case

Prove `etale_of_finite_flat_of_isUnramifiedAt_height_one` (Stacks, Lemma 58.21.2 (0BJH), the
finite locally free case in its proof): for a Noetherian local ring `A` with
`1 ≤ ringKrullDim A` and a finite flat `A`-algebra `B` such that `Algebra.IsUnramifiedAt A 𝔮` for
every prime `𝔮` of `B` with `𝔮.height = 1`, `Algebra.Etale A B`. The proof follows Stacks. `B` is
free (`Module.free_of_flat_of_isLocalRing`). For a basis `b`, if `Algebra.discr A b` is not a unit,
§0.1 gives a prime `𝔭` of height one containing it. By LocalPurity §0.2
`Algebra.isUnit_discr_localization_iff`, `B_𝔭` is not étale over `A_𝔭`. Since it is finite and
flat, it is ramified at some prime of `B_𝔭` (`Algebra.Etale.of_formallyUnramified_of_flat`). That
prime may lie over a prime of `A_𝔭` smaller than `𝔭A_𝔭`, so one more step is needed. The
unramified locus of `B_𝔭` is open (`Algebra.unramifiedLocus_eq_compl_support`), so the ramified
locus is closed under specialization, and the ramified prime lies in a maximal ideal of `B_𝔭` that
is also ramified. Since `B_𝔭` is finite over the local ring `A_𝔭`, its maximal ideals lie over
`𝔭A_𝔭` (`Ideal.IsMaximal.under`). So there is a prime `𝔮` of `B` over `𝔭` at which `B` is
ramified over `A`, and `𝔮.height = 1` by §0.2. This contradicts the hypothesis, so
`Algebra.discr A b` is a unit and LocalPurity §0.2 `Algebra.etale_iff_isUnit_discr` concludes.
*Needs:* §§0.1, 0.2; LocalPurity §0.2; Mathlib `Module.free_of_flat_of_isLocalRing`,
`Algebra.discr`, `Algebra.Etale.of_formallyUnramified_of_flat`,
`Algebra.unramifiedLocus_eq_compl_support`, `Ideal.IsMaximal.under`.

**Checks.**
- `not_etale_dualNumbers`: over a field `k` (dimension zero), `k[x]/(x²)` is finite and flat, has
  no prime of height one, and is not étale. The hypothesis `1 ≤ ringKrullDim A` is needed.

### 0.4 Unramifiedness at a prime along a base change

Prove `Algebra.IsUnramifiedAt.baseChange` (*API*): for `R`-algebras `S` and `R'`, a prime `𝔮` of
`S` and a prime `𝔔` of `R' ⊗[R] S` lying over `𝔮`, `Algebra.IsUnramifiedAt R 𝔮` implies
`Algebra.IsUnramifiedAt R' 𝔔`. The module of differentials of `R' ⊗[R] S` over `R'` is the base
change of that of `S` over `R`, so its localization at `𝔔` is
`(Ω_{S/R})_𝔮 ⊗_{S_𝔮} (R' ⊗[R] S)_𝔔 = 0`.

Prove `Algebra.isUnramifiedAt_of_isUnramifiedAt_baseChange` (*API*), the converse for a flat
`R'`: with `R'` flat over `R`, `Algebra.IsUnramifiedAt R' 𝔔` implies `Algebra.IsUnramifiedAt R 𝔮`.
The same identification holds, and `S_𝔮 → (R' ⊗[R] S)_𝔔` is a flat local homomorphism, hence
faithfully flat, so `(Ω_{S/R})_𝔮 = 0`.
*Needs:* Mathlib `KaehlerDifferential`, `KaehlerDifferential.tensorKaehlerEquiv`,
`Algebra.unramifiedLocus_eq_compl_support`, `Module.FaithfullyFlat`.

### 0.5 Étale at a prime from flat and unramified at that prime

Prove `Algebra.IsEtaleAt.of_isUnramifiedAt_of_flatAt` (*API*): for a finitely presented
`R`-algebra `S` and a prime `𝔮` of `S` with `Localization.AtPrime 𝔮` flat over `R` and
`Algebra.IsUnramifiedAt R 𝔮`, `Algebra.IsEtaleAt R 𝔮`. Mathlib's
`Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat` needs `S` flat over `R`, not only `S_𝔮`. The proof
goes through the local ring. Let `𝔭 = 𝔮.under R`. Then `R_𝔭 → S_𝔮` is flat and local, and `S_𝔮`
is a localization of the finitely presented `R_𝔭`-algebra `R_𝔭 ⊗[R] S`. `S_𝔮` is formally
unramified over `R_𝔭` (`Algebra.FormallyUnramified.localization_base`), so its closed fibre
`κ(𝔭) ⊗[R_𝔭] S_𝔮` is formally unramified and essentially of finite type over `κ(𝔭)`, hence formally
étale (`Algebra.FormallyEtale.of_formallyUnramified_of_field`).
`Algebra.FormallySmooth.of_formallySmooth_residueField_tensor` gives that `S_𝔮` is formally smooth
over `R_𝔭`, hence formally étale, and composing with the formally étale `R → R_𝔭`
(`Algebra.FormallyEtale.of_isLocalization`, `Algebra.FormallyEtale.comp`) gives
`Algebra.IsEtaleAt R 𝔮`.
*Needs:* Mathlib `Algebra.IsEtaleAt`, `Algebra.FormallyUnramified.localization_base`,
`Algebra.FormallyEtale.of_formallyUnramified_of_field`,
`Algebra.FormallySmooth.of_formallySmooth_residueField_tensor`,
`Algebra.FormallyEtale.of_isLocalization`, `Algebra.FormallyEtale.comp`.

## Layer 1: étaleness from codimension one

### 1.1 Affine form

Prove `isEtaleAt_of_flat_of_isUnramifiedAt_height_one` (Stacks, Lemma 58.21.2 (0BJH), affine
form): for a Noetherian ring `R`, a finite type `R`-algebra `S` and a prime `𝔮` of `S` with
`Algebra.QuasiFiniteAt R 𝔮`, `Localization.AtPrime 𝔮` flat over `R` and `1 ≤ 𝔮.height`, if
`Algebra.IsUnramifiedAt R 𝔮'` for every prime `𝔮' ≤ 𝔮` with `𝔮'.height = 1`, then
`Algebra.IsEtaleAt R 𝔮`. The proof is as follows. Mathlib's
`Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq` (00UJ) gives an étale `R → R'`, a prime
`𝔓` of `R'` over `𝔭 = 𝔮.under R` and an idempotent `e` of `R' ⊗[R] S` such that
`(R' ⊗[R] S)_e` is finite over `R'` with a unique prime `𝔔` over `𝔓`, and `𝔔` lies over `𝔮`. Its
localization at `𝔓` is then local, finite and flat over `R'_𝔓`. Its height-one primes lie over
height-one primes `𝔮' ≤ 𝔮`, by §0.2 for the étale map `S → R' ⊗[R] S`, and unramifiedness passes
to the base change (§0.4 `Algebra.IsUnramifiedAt.baseChange`). Also `ringKrullDim R'_𝔓 = 𝔮.height ≥ 1` by §0.2. So §0.3 makes it étale over
`R'_𝔓`. Hence `R' ⊗[R] S` is unramified at `𝔔` over `R'`, and §0.4 gives
`Algebra.IsUnramifiedAt R 𝔮`. `S` is finitely presented over the Noetherian `R`, so flatness at
`𝔮` and §0.5 `Algebra.IsEtaleAt.of_isUnramifiedAt_of_flatAt` finish the proof.
*Needs:* §§0.2–0.5; Mathlib `Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq`,
`Algebra.IsUnramifiedAt`, `Algebra.QuasiFiniteAt`.

### 1.2 Scheme forms

Prove `one_le_ringKrullDim_stalk_iff` (*API*): `1 ≤ ringKrullDim (X.presheaf.stalk x)` iff `x` is
not the generic point of any irreducible component of `X`. Prove
`Scheme.Hom.exists_etale_of_flat_of_formallyUnramified_codimOne` (Stacks, Lemma 58.21.2 (0BJH),
library form): for `f : X ⟶ Y` locally of finite type between locally Noetherian schemes and
`x : X` with `f` flat and quasi-finite at `x`, `1 ≤ ringKrullDim (X.presheaf.stalk x)`, and `f`
unramified at every `x' ⤳ x` with `ringKrullDim (X.presheaf.stalk x') = 1`, `f` is étale at `x`.
On affine opens around `x` and `f x` this is §1.1, and PurityOfBranchLocus §0.1
`Scheme.Hom.etaleAt_spec_iff` translates the conclusion. Prove the accompanying statement in the
form of the tag, `Scheme.Hom.etaleAt_of_flat_of_unramifiedAt_codimOne`. Here `f` is flat, but it
is not assumed locally of finite type. It is quasi-finite at `x` and unramified at `x'` in Stacks'
forms (PurityOfBranchLocus, Convention 3), and `x` is not the generic point of an irreducible
component. It follows from the library form on an open neighbourhood of `x` on which `f` is
locally of finite type, by `Scheme.Hom.unramifiedAt_iff_stalkMap` and
`one_le_ringKrullDim_stalk_iff`.
*Needs:* §1.1; PurityOfBranchLocus §0.1; Mathlib `Scheme.Hom.stalkMap`, `Scheme.Hom.QuasiFiniteAt`,
`irreducibleComponents`, `IsGenericPoint`, `Flat`.

**Checks.**
- `test_flat_needs_codimOne`: over a field of characteristic `≠ 2`, `(x, y) ↦ (x², y)` on `𝔸²` is
  finite and flat, ramified along `x = 0`, and not étale at the origin. The codimension-one
  hypothesis fails at the generic point of `x = 0`.
- `test_flat_needed`: for `X` the union of the planes `V(x, y)` and `V(z, w)` in `𝔸⁴`, the map from
  their disjoint union to `X` is finite and a closed immersion on each plane, so it is quasi-finite
  and unramified everywhere, including at the points over the origin. It is not flat at a point
  over the origin, and not étale there.

## Layer 2: finite étale extension across depth two

Throughout, `X` is locally Noetherian, `U : X.Opens` has complement of depth `≥ 2` (Convention 4),
`j = U.ι`, and `π : V ⟶ U` is finite étale. This layer is specified in this README only: it is
stated in terms of depth, which the pinned Mathlib does not define.

### 2.1 The construction

Prove `isFiniteLocallyFree_pushforward_of_finite_flat` (*API*; Morphisms, Lemma 29.49.2 (02KB)):
for `p : V ⟶ S` finite, flat and locally of finite presentation, the underlying module of
SchemeAndStackFoundations §0.1 `pushforwardAlgebra p` satisfies Tau Ceti
`Scheme.Modules.isFiniteLocallyFree`. Affine-locally it is a finitely presented flat module, so it
is free at each local ring (`Module.free_of_flat_of_isLocalRing`) and hence locally free. Define
`depthTwoExtensionAlgebra π := pushforwardAlgebra (π ≫ j)`. Here `π ≫ j` is quasi-compact and
quasi-separated, since `π` is finite and `j` is an open immersion into a locally Noetherian scheme
(Mathlib, `@[stacks 01OX]`). Its underlying module is `j_*` of that of `pushforwardAlgebra π`
(Mathlib `Scheme.Modules.pushforwardComp`). Define
`depthTwoExtension π := relativeSpec X (depthTwoExtensionAlgebra π)` (Tau Ceti), an affine scheme
over `X` with structure morphism `p`.
*Needs:* SchemeAndStackFoundations §0.1; Tau Ceti `CommMon.relativeSpec`,
`Scheme.Modules.isFiniteLocallyFree`; Mathlib `Scheme.Modules.pushforward`, `QuasiCompact`,
`QuasiSeparated`.

### 2.2 Coherence, reflexivity, finiteness and uniqueness

Prove, each with `@[stacks 0EY6]` and its clause:

- `depthTwoExtensionAlgebra_isReflexive` (clause (1), Convention 5 (i)): the underlying module of
  `depthTwoExtensionAlgebra π` is coherent and `Scheme.Modules.IsReflexive`. The module
  `π_*𝒪_V` is finite locally free (§2.1), hence reflexive (`IsReflexive.locallyFree`), and
  SchemeAndStackFoundations §0.6 `reflexive_extension_of_depth` gives the claim for `j_*`.
- `depthTwoExtension_isFinite`: `p` is finite (Tau Ceti `relativeSpec_finite_iff`,
  SchemeAndStackFoundations §0.2).
- `depthTwoExtension_restrictIso`: an isomorphism `pullback p j ≅ V` over `U`. Mathlib
  `Scheme.Modules.restrictFunctorAdjCounitIso` gives `j^* j_* 𝓖 ≅ 𝓖`. The relative spectrum is
  compatible with restriction to opens (AlgebraicVectorBundles L1A), and for the affine `π` it
  recovers `V` (`pushforwardAlgebra_affine`, Tau Ceti `relativeSpecEquiv`).
- `depthTwoExtension_two_le_depth`: `2 ≤ IsLocalRing.depth 𝒪_{Y,y}` for every point `y` of
  `depthTwoExtension π` with `p y ∉ U`. The stalk `𝓑_x` at `x = p y` has depth `≥ 2`
  (`IsReflexive.two_le_depth_stalk`). It is finite over `𝒪_{X,x}`, and the local rings of `Y` over
  `x` are its localizations at maximal ideals, so SchemeAndStackFoundations §0.17
  `depth_eq_iInf_localization_maximal` (0AUK) applies.
- `depthTwoExtension_unique` (clause (2)): for a finite `p' : Y' ⟶ X`, an isomorphism
  `e : pullback p' j ≅ V` over `U`, and `2 ≤ IsLocalRing.depth 𝒪_{Y',y'}` for every `y'` with
  `p' y' ∉ U`, there is a unique isomorphism `Y' ≅ depthTwoExtension π` over `X` whose restriction
  over `U` is `e` followed by the inverse of `depthTwoExtension_restrictIso`. The algebra
  `p'_* 𝒪_{Y'}` has depth `≥ 2` at every `x ∉ U` (0AUK), so `coherent_hartogs` identifies it with
  `j_* j^* p'_* 𝒪_{Y'} ≅ j_* π_* 𝒪_V` as algebras. Tau Ceti `relativeSpecEquiv` turns this into
  the isomorphism. Uniqueness holds because restriction of sections to `U` is injective
  (`coherent_hartogs`).

Prove `depthTwoExtension_spec_iso` (*API*): for `X = Spec A`, `depthTwoExtension π ≅ Spec Γ(V, 𝒪_V)`
over `X`, with `Γ(V, 𝒪_V)` finite over `A`. The global sections of `j_*π_*𝒪_V` are `Γ(V, 𝒪_V)` by
the definition of the pushforward, and Tau Ceti `relativeSpecAffineIso` gives the isomorphism.
Finiteness over `A` is the coherence in `depthTwoExtensionAlgebra_isReflexive` above.

*Needs:* §2.1; SchemeAndStackFoundations §§0.2, 0.6, 0.17; AlgebraicVectorBundles L1A; Tau Ceti
`relativeSpecEquiv`, `relativeSpecAffineIso`; Mathlib `Scheme.Modules.restrictFunctorAdjCounitIso`,
`IsFinite`.

### 2.3 Étaleness and flatness

Prove `depthTwoExtension_etaleAt_iff_flat` (Stacks 0EY6, clause (3)): `p` is étale at `y` iff it
is flat at `y`. Étale implies flat. Conversely, if `p y ∈ U`, then `p` is étale near `y`. If
`p y ∉ U`, apply §1.2 `Scheme.Hom.exists_etale_of_flat_of_formallyUnramified_codimOne`. `p` is
finite, so it is locally of finite type and quasi-finite at `y`, and `Y` is locally Noetherian.
`ringKrullDim 𝒪_{Y,y} ≥ 2` because the depth is at most the dimension (SchemeAndStackFoundations
§0.17 `depth_le_supportDim`, 00LK). A specialization `y' ⤳ y` with `ringKrullDim 𝒪_{Y,y'} = 1` has
`p y' ∈ U` by the same bound and `depthTwoExtension_two_le_depth`, so `p` is unramified at `y'`.

Prove `depthTwoExtension_etale_iff` (Stacks 0EY6, clause (4)): `Etale p` iff the underlying
module of `depthTwoExtensionAlgebra π` satisfies `Scheme.Modules.isFiniteLocallyFree`. The stalk
`𝓑_x` is flat over `𝒪_{X,x}` iff its localizations at maximal ideals, the local rings of `Y` over
`x`, are flat. The "if" direction is `Module.flat_of_isLocalized_maximal`; the "only if" direction
is that a localization of a flat algebra is flat (`Localization.flat`). A finite flat module over a Noetherian local
ring is free (`Module.free_of_flat_of_isLocalRing`). Combine this with clause (3) and §2.1.

Prove `depthTwoExtension_extends_iff` (*API*): `V` is isomorphic over `U` to the restriction of a
finite étale scheme over `X` iff `Etale p`, and then `depthTwoExtension π` is that scheme. If `W`
is finite étale over `X` and restricts to `V`, then its local rings off `V` have depth `≥ 2`
(SchemeAndStackFoundations §0.17 `depth_eq_add_of_flat`, 0337, with a field as closed fibre), so
`depthTwoExtension_unique` identifies `W` with `depthTwoExtension π`. LocalPurity §2.2
`restrictOpen_fullyFaithful_of_depth` gives full faithfulness of the restriction.
*Needs:* §§1.2, 2.2; SchemeAndStackFoundations §0.17; LocalPurity §2.2; Mathlib
`Module.flat_of_isLocalized_maximal`, `Localization.flat`, `Module.free_of_flat_of_isLocalRing`.

**Checks.**
- `test_cone_cover`: over a field `k` of characteristic `≠ 2`, let `A` be `k[x², xy, y²]`
  localized at the origin (normal of dimension two, so of depth two), `X = Spec A`, `U` the
  punctured spectrum, and `V` the restriction of the spectrum of `k[x, y]` localized at the origin,
  which is finite étale over `U`. Then `depthTwoExtension π` is that spectrum. It is finite over
  `X` and not flat at the closed point, since its algebra has rank two over `A` and needs the
  three generators `1, x, y`. So it is not étale there, and clauses (3) and (4) are sharp.
- `test_two_planes`: for `X` the union of the planes `V(x, y)` and `V(z, w)` in `𝔸⁴`, `U` the
  complement of the origin and `V = U`, `depth 𝒪_{X,0} = 1`, so the standing depth hypothesis
  fails. The construction still makes sense: `j_*𝒪_U` is the direct image of the structure sheaf of
  the disjoint union `X̃` of the two planes, so `depthTwoExtension π` is `X̃`, which is not flat, hence
  not étale, at the points over the origin. Yet `V = U` is the restriction of the finite étale
  `X → X`. So the depth hypothesis on `X` is needed for `depthTwoExtension_extends_iff`.
  (Uniqueness, `depthTwoExtension_unique`, still holds here: `X` itself is not a competitor, since
  its local ring at the origin has depth `1`.)
- `test_reducible`: for `X = Spec k[x, y, z, w]/(xw)` (reducible, Cohen–Macaulay of dimension
  three), `U` the complement of the origin and `V = U`, `depthTwoExtension π ≅ X`. Every clause
  applies, though `X` is not integral (Convention 5 (i)).

### 2.4 Base change and larger opens

Prove `depthTwoExtension_baseChange` (Stacks 0EY6, clause (a)): for a flat `g : X' ⟶ X` with `X'`
locally Noetherian, `U' = g⁻¹ U` and `π'` the base change of `π`, the pullback of
`depthTwoExtensionAlgebra π` along `g` is `depthTwoExtensionAlgebra π'`, and
`depthTwoExtension π'` is `pullback p g` over `X'`. This is SchemeAndStackFoundations §0.1
`pushforwardAlgebra_baseChange` (02KH, `i = 0`) with base change of the relative spectrum
(AlgebraicVectorBundles L1A). Prove `two_le_depth_of_flat` (*API*): the complement of `U'` has
depth `≥ 2` (SchemeAndStackFoundations §0.17 `depth_eq_add_of_flat`), so §§2.2–2.3 apply to
`π'`.

Prove `depthTwoExtension_restrict_larger` (Stacks 0EY6, clause (b), Convention 5 (ii)): for opens
`U ≤ U'` of `X` and a finite étale `π' : V' ⟶ U'` with an isomorphism from its restriction to `U`
to `V` over `U`, there is a unique isomorphism `pullback p (U'.ι) ≅ V'` over `U'` compatible with
the given one over `U`. Apply `depthTwoExtension_unique` on the locally Noetherian scheme `U'`,
whose complement of `U` has depth `≥ 2`. Both schemes are finite over `U'` and restrict to `V`.
Their local rings off `V` have depth `≥ 2`: for `pullback p (U'.ι)` by
`depthTwoExtension_two_le_depth`, and for `V'` by `depth_eq_add_of_flat`, since `π'` is étale.
*Needs:* §§2.2–2.3; SchemeAndStackFoundations §§0.1, 0.17; AlgebraicVectorBundles L1A; Mathlib
`Flat`, `pullback`.

## Stacks alignment

*Exact*: the tag's hypotheses and conclusion, in Mathlib's vocabulary. *Adapted*: the same
mathematics in a different packaging, with the difference stated at the target. *API*: no Stacks
counterpart.

| § | Target | Stacks | Class |
| --- | --- | --- | --- |
| 0.1 | `exists_isPrime_height_eq_one_of_mem` | 58.21.1 (0BJG) | exact |
| 0.2 | `Ideal.height_eq_height_under_of_flat_of_quasiFiniteAt` | — | API |
| 0.3 | `etale_of_finite_flat_of_isUnramifiedAt_height_one` | step of 58.21.2 (0BJH) | adapted (finite flat, local base) |
| 0.4 | `Algebra.IsUnramifiedAt.baseChange`, `Algebra.isUnramifiedAt_of_isUnramifiedAt_baseChange` | — | API |
| 0.5 | `Algebra.IsEtaleAt.of_isUnramifiedAt_of_flatAt` | — | API |
| 1.1 | `isEtaleAt_of_flat_of_isUnramifiedAt_height_one` | 58.21.2 (0BJH) | adapted (affine) |
| 1.2 | `one_le_ringKrullDim_stalk_iff` | — | API |
| 1.2 | `Scheme.Hom.exists_etale_of_flat_of_formallyUnramified_codimOne` | 58.21.2 (0BJH) | adapted (stalk forms, flat at `x`) |
| 1.2 | `Scheme.Hom.etaleAt_of_flat_of_unramifiedAt_codimOne` | 58.21.2 (0BJH) | exact |
| 2.1 | `isFiniteLocallyFree_pushforward_of_finite_flat` | 29.49.2 (02KB) | adapted |
| 2.1 | `depthTwoExtensionAlgebra`, `depthTwoExtension` | — | API |
| 2.2 | `depthTwoExtensionAlgebra_isReflexive` | 58.21.5 (0EY6) (1) | adapted (Convention 5 (i)) |
| 2.2 | `depthTwoExtension_isFinite`, `depthTwoExtension_restrictIso`, `depthTwoExtension_two_le_depth`, `depthTwoExtension_unique` | 58.21.5 (0EY6) (2) | exact |
| 2.2 | `depthTwoExtension_spec_iso` | — | API |
| 2.3 | `depthTwoExtension_etaleAt_iff_flat` | 58.21.5 (0EY6) (3) | exact |
| 2.3 | `depthTwoExtension_etale_iff` | 58.21.5 (0EY6) (4) | exact |
| 2.3 | `depthTwoExtension_extends_iff` | — | API |
| 2.4 | `depthTwoExtension_baseChange`, `two_le_depth_of_flat` | 58.21.5 (0EY6) (a) | exact |
| 2.4 | `depthTwoExtension_restrict_larger` | 58.21.5 (0EY6) (b) | adapted (Convention 5 (ii)) |

## Provenance

This section is secondary. It maps targets to an existing formalization and prescribes nothing.
The repository https://github.com/tdupu/pcfawd-formalization (Apache-2.0; T. Dupuy, T. Tucker,
Z. Wang; Lean 4, Mathlib, no `sorry`) contains part of Layers 0 and 1. Paths are under
`lean/Pcf/Stacks/Purity/`.

| § | Existing declarations | Files |
| --- | --- | --- |
| 0.2 | `Ideal.height_under_eq_of_finite_of_flat`, `mem_minimalPrimes_of_quasiFiniteAt` | `HeightOneEtaleBridge.lean`, `Tag0BMBLocalModel.lean` |
| 0.3 | `Algebra.etale_heightOne_baseChange_of_unramifiedAt_height_one`, `Algebra.etale_of_genericFiber_and_unramifiedAt_height_one` (for `A` a domain) | `HeightOneEtaleBridge.lean` |
| 0.5 | `isEtaleAt_of_flat_of_formallyUnramified` (flat and formally unramified at `q`) | `Tag0BMBLocalModel.lean` |
| 1.1 | the étale local model and descent for 0BMB: `exists_etale_finiteComponent_of_zariskiNagataPurityHypothesesAt`, `formallyUnramified_of_faithfullyFlat_of_formallyEtale` | `Tag0BMBAssembly.lean`, `Tag0BMBLocalModel.lean` |
| 2.1 | affine depth-two extension of sections for a finite algebra: `openSections_algebraMap_bijective_of_module_regularPair` | `FiniteNormalHartogs.lean` |

## References

- The Stacks Project, Chapters 10 (Algebra), 15 (More on Algebra), 29 (Morphisms), 31 (Divisors),
  49 (Discriminants) and 58 (Fundamental Groups of Schemes), https://stacks.math.columbia.edu.
- A. Grothendieck, *Cohomologie locale des faisceaux cohérents et théorèmes de Lefschetz locaux et
  globaux* (SGA 2), Exposé X, §3.
