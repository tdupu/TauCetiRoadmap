import Mathlib
import TauCeti.AlgebraicGeometry.Scheme.CodimensionOnePoint
import TauCeti.RingTheory.RegularLocalRing.Basic

set_option autoImplicit false

/-!
# Ramification along divisors, purity of the branch locus, and Abhyankar's lemma

These are suggested forms. The README is the definitive specification.

Every declaration that has a Stacks Project counterpart carries Mathlib's `@[stacks]` attribute
with that tag, and its statement follows the shape of the tag (README, Convention 8). Where a
statement deliberately differs from the tag, its docstring says so under "Divergence from
Stacks". Declarations without a tag say why in their docstring; the README flags the
corresponding targets as API. Non-Stacks sources are cited with a pinpoint.

This file holds representative signatures for each layer: the regular-local and DVR-extension
notions of Layer 0, the ramification index at a point of Layer 1, purity for a local ring of
Layer 2, the purity theorem of Layer 3 in scheme and affine form, and the standard tamely ramified
cover and Abhyankar's lemma of Layer 4. Finite étale categories are written here with Mathlib's
morphism classes. The README's carrier for them is Tau Ceti's `TauCeti.FiniteEtaleScheme`, which is
not in this repository's pinned Tau Ceti (see `FEt`).
-/

universe u

namespace TauCetiRoadmap.PurityAndAbhyankar

noncomputable section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing

/-! ## Layer 0: local algebra -/

section Layer0

/-- If `x ∈ 𝔪` is a nonzerodivisor of a Noetherian local ring `R` and `R ⧸ (x)` is regular
local, then `R` is regular local. Stacks, Lemma 10.106.7 (00NU), first sentence. -/
@[stacks 00NU "first sentence"]
theorem isRegularLocalRing_of_quotient_nonZeroDivisor {R : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {x : R} (hx : x ∈ maximalIdeal R) (hreg : x ∈ nonZeroDivisors R)
    (hq : IsRegularLocalRing (R ⧸ Ideal.span {x})) : IsRegularLocalRing R := by
  sorry

/-- A ring is **normal** in the sense of Stacks, Definition 10.37.11 (00GV): its localization at
every prime is a normal domain. Mathlib's `IsIntegrallyClosed` is the domain case only, so a
disconnected normal ring such as `A × A ⧸ 𝔪` (README, Convention 5) needs this predicate. -/
@[stacks 00GV]
def IsStacksNormalRing (R : Type u) [CommRing R] : Prop :=
  ∀ p : PrimeSpectrum R,
    IsDomain (Localization.AtPrime p.asIdeal) ∧
      IsIntegrallyClosed (Localization.AtPrime p.asIdeal)

/-- A regular ring is normal. Stacks, Lemma 10.157.5 (0567), exactly. -/
@[stacks 0567]
theorem isStacksNormalRing_of_isRegularRing (R : Type u) [CommRing R] [IsRegularRing R] :
    IsStacksNormalRing R := by
  sorry

/-- A regular local ring is integrally closed: the local case of Stacks, Lemma 10.157.5 (0567),
via Definition 10.37.11 (00GV) at the maximal ideal. -/
@[stacks 0567 "local case"]
theorem isIntegrallyClosed_of_isRegularLocalRing (R : Type u) [CommRing R]
    [IsRegularLocalRing R] : IsIntegrallyClosed R := by
  sorry

variable (A L : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field L] [Algebra A L]

/-- A finite separable extension `L` of the fraction field of a DVR `A` is **unramified with
respect to `A`** when every maximal ideal of the integral closure of `A` in `L` has ramification
index one and separable residue field extension. Stacks, Definition 15.113.7 (09E9), clause (1),
in the notation of Remark 15.113.6 (09E8).

Divergence from Stacks: the predicate is defined for any field `L` with an `A`-algebra structure.
Stacks defines it only for a finite separable extension of the fraction field of `A`; statements
that use it carry that hypothesis. -/
@[stacks 09E9 "(1)"]
def IsUnramifiedWRT : Prop :=
  ∀ (P : Ideal (integralClosure A L)) [P.IsMaximal] [P.LiesOver (maximalIdeal A)],
    P.ramificationIdx A = 1 ∧
      Algebra.IsSeparable (A ⧸ maximalIdeal A) (integralClosure A L ⧸ P)

/-- A finite separable extension `L` of the fraction field of a DVR `A` is **tamely ramified with
respect to `A`** when every residue field extension is separable and every ramification index is
invertible in the residue field `κ_A`. Stacks, Definition 15.113.7 (09E9), clause (2). Stacks
writes "the characteristic of `κ_A` is `0`, or it is `p > 0`, the residue extensions are separable
and the `e_i` are prime to `p`"; since residue extensions of a characteristic-zero field are
separable, this is the same condition, and "`e` invertible in `κ_A`" is the phrasing of Stacks,
Lemma 15.116.7 (0EXW).

Divergence from Stacks: as for `IsUnramifiedWRT`, `L` is not required to be a finite separable
extension of the fraction field of `A`. -/
@[stacks 09E9 "(2)"]
def IsTamelyRamifiedWRT : Prop :=
  ∀ (P : Ideal (integralClosure A L)) [P.IsMaximal] [P.LiesOver (maximalIdeal A)],
    Algebra.IsSeparable (A ⧸ maximalIdeal A) (integralClosure A L ⧸ P) ∧
      IsUnit ((P.ramificationIdx A : ℕ) : A ⧸ maximalIdeal A)

/-- Unramified extensions are tamely ramified. No Stacks tag: it is immediate from clauses (1)
and (2) of Definition 15.113.7 (09E9), and Stacks states it nowhere as a result. -/
theorem IsUnramifiedWRT.isTamelyRamifiedWRT (h : IsUnramifiedWRT A L) :
    IsTamelyRamifiedWRT A L := by
  sorry

end Layer0

/-! ## Layer 1: ramification of finite morphisms along prime divisors -/

section Layer1

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A finite dominant morphism of integral schemes with normal locally Noetherian target preserves
codimension of points. Combines Stacks, Proposition 10.38.7 (00H8, going down; in Mathlib as
`Algebra.HasGoingDown`) and Lemma 10.112.7 (00ON, the dimension formula; in Tau Ceti). There is
no single tag for this statement. -/
theorem coheight_apply [IsFinite f] [IsDominant f] [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian Y] (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) (x : X) :
    Order.coheight (f x) = Order.coheight x := by
  sorry

/-- The ramification index of `f` at a point `x`: the ramification index of the maximal ideal of
`𝒪_{X,x}` over `𝒪_{Y,f x}` along the stalk map. At a prime divisor with discrete valuation rings
on both sides this is the exponent `e` with `f^♯ π_y = u · π_x ^ e`. Stacks, Definition 15.113.1
(09E4), the ramification index of an extension of discrete valuation rings.

Divergence from Stacks: the definition is made at every point, with no hypothesis on the stalks.
It is Stacks' `e` when the stalk map `𝒪_{Y,f x} → 𝒪_{X,x}` is an extension of discrete valuation
rings (injective and local); otherwise it is Mathlib's `Ideal.ramificationIdx`, whose value may be
a junk value. -/
@[stacks 09E4 "ramification index, at a point"]
def ramificationIdxAt (x : X) : ℕ :=
  letI := (f.stalkMap x).hom.toAlgebra
  (maximalIdeal (X.presheaf.stalk x)).ramificationIdx (Y.presheaf.stalk (f x))

/-- Ramification indices multiply along a composite. Stacks, Lemma 15.113.3 (0BRL), applied to
the extensions of discrete valuation rings `𝒪_{Z,g(f x)} ⊂ 𝒪_{Y,f x} ⊂ 𝒪_{X,x}`; the residue
degree half of 0BRL is not stated here.

Divergence from Stacks: the stalk maps are not assumed injective. When one of them is not, its
image of the maximal ideal is zero, so both sides are `0` under Mathlib's `Ideal.ramificationIdx`
(a discrete valuation ring has infinite length over itself). -/
@[stacks 0BRL "at a point"]
theorem ramificationIdxAt_comp {Z : Scheme.{u}} (g : Y ⟶ Z) [IsIntegral X] [IsIntegral Y]
    [IsIntegral Z] (x : X)
    (hx : IsDiscreteValuationRing (X.presheaf.stalk x))
    (hy : IsDiscreteValuationRing (Y.presheaf.stalk (f x)))
    (hz : IsDiscreteValuationRing (Z.presheaf.stalk (g (f x)))) :
    ramificationIdxAt (f ≫ g) x = ramificationIdxAt f x * ramificationIdxAt g (f x) := by
  sorry

end Layer1

/-! ## Layer 2: finite étale covers of punctured spectra -/

section Layer2

variable (A : Type u) [CommRing A] [IsLocalRing A]

/-- The punctured spectrum of a local ring: the complement of the closed point. Stacks, Section
58.20 (0BM7), first paragraph, `U = X ∖ {𝔪}`.

Divergence from Stacks: Section 58.20 assumes `A` Noetherian; the open subset makes sense for any
local ring (as in Stacks, Lemma 58.10.2 (0BLQ)), so no Noetherian hypothesis is imposed. -/
@[stacks 0BM7 "the punctured spectrum"]
def puncturedSpectrum : (Spec (.of A)).Opens where
  carrier := {closedPoint A}ᶜ
  is_open' := (isClosed_singleton_closedPoint (R := A)).isOpen_compl

end Layer2

/-- The morphism property "finite and étale". No Stacks tag of its own: Stacks, Section 58.5
(0BL6) uses it to define `FÉt_X` (see `FEt`). -/
abbrev finiteEtale : MorphismProperty Scheme.{u} := @IsFinite ⊓ @Etale

/-- The category `FÉt_X` of schemes finite étale over `X`, with all morphisms over `X`. Stacks,
Section 58.5 (0BL6), the definition of `FÉt_X` in its second paragraph.

The README's carrier is Tau Ceti's `TauCeti.FiniteEtaleScheme` (module
`TauCeti.AlgebraicGeometry.FiniteEtale.Basic`). Tau Ceti added it in #15694 (commit `8a90454a6`,
2026-10-13), after this repository's pinned Tau Ceti `a91d3aaf`, so it cannot be imported here.
Both describe the full subcategory of `Over X` on the finite étale objects. -/
@[stacks 0BL6 "the category FÉt_X"]
abbrev FEt (X : Scheme.{u}) : Type (u + 1) :=
  finiteEtale.Over ⊤ X

/-- The restriction functor `FÉt_X → FÉt_Y` along a morphism, by pullback: the base change
functor of Stacks, Lemma 58.5.2 (0BN9). The lemma's assertion, that this functor is exact, is not
stated here. -/
@[stacks 0BN9 "the base change functor only, not its exactness"]
def FEt.pullback {X Y : Scheme.{u}} (f : Y ⟶ X) : FEt X ⥤ FEt Y := by
  letI : finiteEtale.IsStableUnderBaseChange :=
    MorphismProperty.IsStableUnderBaseChange.inf
  exact MorphismProperty.Over.pullback finiteEtale ⊤ f

/-- **Purity holds** for a local ring `A`: the restriction functor `FÉt_X → FÉt_U` from
`X = Spec A` to its punctured spectrum is essentially surjective. Stacks, Section 58.20 (0BM7),
the definition in the first paragraph.

Divergence from Stacks: Stacks makes the definition for a Noetherian local ring only; here it is
made for every local ring, and agrees with Stacks' on Noetherian ones. -/
@[stacks 0BM7 "definition of purity"]
def PurityHolds (A : Type u) [CommRing A] [IsLocalRing A] : Prop :=
  (FEt.pullback (puncturedSpectrum A).ι).EssSurj

/-- Purity for a regular local ring of dimension at least two. Stacks, Lemma 58.21.3 (0BMA),
part (1), exactly (Mathlib's `IsRegularLocalRing` includes Noetherian). This is also the
Zariski–Nagata purity theorem in the form of SGA 2, Exposé X, Théorème 3.4 (i). -/
@[stacks 0BMA "(1)"]
theorem purityHolds_of_isRegularLocalRing (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (hd : 2 ≤ ringKrullDim A) : PurityHolds A := by
  sorry

/-! ## Layer 3: purity of the branch locus -/

section Layer3

/-- **Purity of the branch locus**, affine pointwise form. Stacks, Lemma 58.21.4 (0BMB).

Divergence from Stacks (adapted, not weakened): the scheme `X` is `Spec S`, finite type over a
Noetherian `R` (Stacks' "quasi-finite at `x`" already includes finite type near `x`); "normal"
for the local ring `S_𝔮` is `IsDomain ∧ IsIntegrallyClosed` (Definition 10.37.11 (00GV) for a
local ring); `dim 𝒪_{X,x}` is written as `𝔮.height`, which equals `dim S_𝔮`. -/
@[stacks 0BMB "affine form"]
theorem isEtaleAt_of_purity {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [Algebra.FiniteType R S] (q : Ideal S) [q.IsPrime]
    (hdom : IsDomain (Localization.AtPrime q))
    (hnormal : IsIntegrallyClosed (Localization.AtPrime q))
    (hreg : IsRegularLocalRing (Localization.AtPrime (q.under R)))
    (hqf : Algebra.QuasiFiniteAt R q)
    (hdim : q.height = (q.under R).height) (hpos : 1 ≤ q.height)
    (hcodim : ∀ (q' : Ideal S) [q'.IsPrime], q' ≤ q → q'.height = 1 →
      Algebra.IsUnramifiedAt R q') :
    Algebra.IsEtaleAt R q := by
  sorry

/-- **Purity of the branch locus**, scheme form. Stacks, Lemma 58.21.4 (0BMB). Unramifiedness and
étaleness at a point are stated on an open neighbourhood, which is Stacks' Definitions 29.36.1
(02G4) and 29.37.1 (02GI). Compare SGA 1, Exposé X, Théorème 3.1, which is recalled there without
proof.

Divergence from Stacks: `f` is assumed locally of finite type. Stacks' "quasi-finite at `x`"
(Definition 29.21.1 (01TD)) includes finite type on a neighbourhood of `x`, whereas Mathlib's
`Scheme.Hom.QuasiFiniteAt` is a condition on the stalk map only. Since the conclusion is local at
`x`, the global hypothesis can be met by shrinking `X`, so no case of 0BMB is lost. -/
@[stacks 0BMB "with f locally of finite type"]
theorem etaleAt_of_unramified_codimOne {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [LocallyOfFiniteType f] (x : X)
    (hdom : IsDomain (X.presheaf.stalk x))
    (hnormal : IsIntegrallyClosed (X.presheaf.stalk x))
    (hreg : IsRegularLocalRing (Y.presheaf.stalk (f x)))
    (hqf : f.QuasiFiniteAt x)
    (hdim : ringKrullDim (X.presheaf.stalk x) = ringKrullDim (Y.presheaf.stalk (f x)))
    (hpos : 1 ≤ ringKrullDim (X.presheaf.stalk x))
    (hcodim : ∀ x' : X, x' ⤳ x → ringKrullDim (X.presheaf.stalk x') = 1 →
      ∃ U : X.Opens, x' ∈ U ∧ FormallyUnramified (U.ι ≫ f)) :
    ∃ U : X.Opens, x ∈ U ∧ Etale (U.ι ≫ f) := by
  sorry

end Layer3

/-! ## Layer 4: Abhyankar's lemma for a regular divisor -/

section Layer4

/-- The standard tamely ramified cover `A[x]/(x^e − f)`. Stacks, Example 58.31.4 (0EYF).

Divergence from Stacks: Stacks assumes `A` Noetherian, `f` a nonzerodivisor with `A/fA` reduced,
and `e ≥ 1` invertible in `A`. The algebra is defined without these hypotheses; the statements about
it carry the ones they need. -/
@[stacks 0EYF "the algebra A[x]/(x^e − f)"]
abbrev standardTameCover (A : Type u) [CommRing A] (f : A) (e : ℕ) : Type u :=
  AdjoinRoot (Polynomial.X ^ e - Polynomial.C f)

/-- `C` is `A`-isomorphic to a finite product of standard tamely ramified covers along `f`, with
exponents invertible in `A`. Since `Spec` reverses arrows, this is a finite disjoint union of
standard covers. No Stacks tag: Stacks has no name for this notion; it is the shape of the
conclusions of Lemmas 58.31.5 (0EYG) and 58.31.6 (0EYH). -/
def IsFiniteProductOfStandardTameCovers (A C : Type u) [CommRing A] [CommRing C] [Algebra A C]
    (f : A) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (e : ι → ℕ), (∀ i, 1 ≤ e i) ∧ (∀ i, IsUnit (e i : A)) ∧
    Nonempty (C ≃ₐ[A] ∀ i, standardTameCover A f (e i))

/-- The standard tamely ramified cover is finite free of rank `e`: the "finite locally free"
assertion of Stacks, Example 58.31.4 (0EYF).

Divergence from Stacks (strengthened): only `A` nontrivial and `e ≥ 1` are assumed, since
`x^e − f` is monic, and the conclusion is free of rank `e` rather than finite locally free. -/
@[stacks 0EYF "finite locally free"]
theorem standardTameCover_finrank (A : Type u) [CommRing A] [Nontrivial A] (f : A) (e : ℕ)
    (he : 1 ≤ e) :
    Module.Free A (standardTameCover A f e) ∧ Module.finrank A (standardTameCover A f e) = e := by
  sorry

/-- `S` is tamely ramified along `a`: for every prime `Q` of `S` minimal over `aS` whose
contraction is minimal over `aR` (the generic points of the prime divisors of `V(a)` upstairs and
downstairs, Stacks' "prime divisor `Z` with `Z ∩ U = ∅`"), the residue field extension is
separable and the ramification index is invertible in the residue field below. For `S` the
integral closure of `R` in a finite étale `R_a`-algebra this is Stacks' "tamely ramified over
`Spec R` in codimension one" (Section 58.31 (0BSE), the definition preceding Lemma 58.31.1, with
Definition 15.113.7 (09E9)).

Divergence from Stacks: the definition is affine and along a principal divisor `V(a)`, and it does
not assume that the local rings at the primes `Q.under R` are discrete valuation rings; it is
Stacks' notion under the hypotheses just stated. -/
@[stacks 0BSE "tamely ramified in codimension one, affine form"]
def IsTamelyRamifiedAlong (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (a : R) :
    Prop :=
  ∀ (Q : Ideal S) [Q.IsPrime], Q.under R ∈ (Ideal.span {a}).minimalPrimes →
    Q ∈ ((Ideal.span {a}).map (algebraMap R S)).minimalPrimes →
    letI := (Ideal.ResidueField.map (Q.under R) Q (algebraMap R S) rfl).toAlgebra
    Algebra.IsSeparable (Q.under R).ResidueField Q.ResidueField ∧
      IsUnit ((Q.ramificationIdx R : ℕ) : (Q.under R).ResidueField)

/-- **Abhyankar's lemma for a regular divisor**, affine form. Stacks, Lemmas 58.31.5 (0EYG) and
58.31.6 (0EYH), the "Moreover" clause of the latter. Compare SGA 1, Exposé XIII, Proposition 5.2
(absolute Abhyankar lemma, for a normal crossings divisor on a regular local scheme).

Divergence from Stacks (adapted, not weakened): `X = Spec R` and `D = V(a)` with `a` a
nonzerodivisor (an effective Cartier divisor) and `R/aR` regular; `Y → X ∖ D` is replaced by its
normalization `Spec S` (which is what 0EYH produces); "étale locally on `X`" is an étale `R → R'`
whose image contains a given point of `D`. -/
@[stacks 0EYG "affine form", stacks 0EYH "étale-local structure of the normalization, affine form"]
theorem abhyankar_standardCover {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [Module.Finite R S] (a : R) (ha : a ∈ nonZeroDivisors R)
    (hreg : IsRegularRing (R ⧸ Ideal.span {a}))
    (hetale : ∀ (q : Ideal S) [q.IsPrime], algebraMap R S a ∉ q → Algebra.IsEtaleAt R q)
    (hclosure : IsIntegralClosure S R (Localization.Away (algebraMap R S a)))
    (htame : IsTamelyRamifiedAlong R S a) (y : PrimeSpectrum R) (hy : a ∈ y.asIdeal) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R'),
      Algebra.Etale R R' ∧ (∃ y' : PrimeSpectrum R', y'.asIdeal.under R = y.asIdeal) ∧
      algebraMap R R' a ∈ nonZeroDivisors R' ∧
      IsRegularRing (R' ⧸ Ideal.span {algebraMap R R' a}) ∧
      IsFiniteProductOfStandardTameCovers R' (TensorProduct R R' S) (algebraMap R R' a) := by
  sorry

end Layer4

end

end TauCetiRoadmap.PurityAndAbhyankar
