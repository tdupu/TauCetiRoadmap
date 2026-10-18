import Mathlib

/-!
# Étaleness from codimension one and finite étale extension across depth two: suggested forms

**This file is not the roadmap and is not exhaustive.** The definitive document is
`README.md`. The statements here suggest Lean forms for particular milestones, so that
contributors and reviewers converge on names and signatures; discharging all of them
finishes neither a layer nor the roadmap.

Every target is stated in Mathlib's vocabulary (README, Convention 2). The pointwise notions are
those of PurityOfBranchLocus, Convention 3: flat and unramified at a point are stalkwise, and étale
at a point is an open neighbourhood on which the morphism is étale. The form of Stacks, Lemma
58.21.2 (0BJH), with Stacks' pointwise notions written out, is an accompanying statement.
Declarations with a Stacks Project counterpart carry `@[stacks]`.

Layer 2 (Stacks, Lemma 58.21.5 (0EY6)) is stated in terms of depth, which the pinned Mathlib does
not define, so it is specified in the README only.
-/

universe u

namespace TauCetiRoadmap.FiniteEtaleExtensionAcrossDepthTwo

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

/-! ## Layer 0: commutative algebra -/

section Layer0

/-- In a Noetherian local ring of positive dimension, every element of the maximal ideal lies in
a prime of height one. Stacks, Lemma 58.21.1 (0BJG); `dim A_𝔭 = 1` is `𝔭.height = 1`. -/
@[stacks 0BJG]
theorem exists_isPrime_height_eq_one_of_mem (A : Type u) [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] (hA : 1 ≤ ringKrullDim A) {f : A} (hf : f ∈ maximalIdeal A) :
    ∃ p : Ideal A, p.IsPrime ∧ f ∈ p ∧ p.height = 1 := by
  sorry

/-- Heights are preserved at a prime where a homomorphism of Noetherian rings is flat and
quasi-finite. *API*: the dimension formula `@[stacks 00ON]` with a zero-dimensional fibre. -/
theorem _root_.Ideal.height_eq_height_under_of_flat_of_quasiFiniteAt {R S : Type u} [CommRing R]
    [CommRing S] [Algebra R S] [IsNoetherianRing R] [IsNoetherianRing S] (q : Ideal S) [q.IsPrime]
    [Algebra.QuasiFiniteAt R q] [Module.Flat R (Localization.AtPrime q)] :
    q.height = (q.under R).height := by
  sorry

/-- A finite flat algebra over a Noetherian local ring of positive dimension which is unramified
at every prime of height one is étale. The finite locally free case in the proof of Stacks, Lemma
58.21.2 (0BJH), with the discriminant criterion of LocalPurity §0.2. -/
@[stacks 0BJH "finite flat algebra over a local base"]
theorem etale_of_finite_flat_of_isUnramifiedAt_height_one (A B : Type u) [CommRing A]
    [CommRing B] [Algebra A B] [IsNoetherianRing A] [IsLocalRing A] [Module.Finite A B]
    [Module.Flat A B] (hA : 1 ≤ ringKrullDim A)
    (hunr : ∀ (q : Ideal B) [q.IsPrime], q.height = 1 → Algebra.IsUnramifiedAt A q) :
    Algebra.Etale A B := by
  sorry

/-- Check: the dimension hypothesis is needed. Over a field (dimension zero) the dual numbers are
finite and flat, have no prime of height one, and are not étale. -/
theorem not_etale_dualNumbers (k : Type u) [Field k] :
    ¬ Algebra.Etale k (Polynomial k ⧸ Ideal.span {(Polynomial.X : Polynomial k) ^ 2}) := by
  sorry

/-- Unramifiedness at a prime descends along an étale base change. *API*. -/
theorem _root_.Algebra.isUnramifiedAt_of_isUnramifiedAt_baseChange {R R' S : Type u} [CommRing R]
    [CommRing R'] [CommRing S] [Algebra R R'] [Algebra R S] [Algebra.Etale R R']
    [Algebra.FiniteType R S] (q : Ideal S) [q.IsPrime] (Q : Ideal (TensorProduct R R' S))
    [Q.IsPrime] (hQ : Q.comap Algebra.TensorProduct.includeRight.toRingHom = q)
    [Algebra.IsUnramifiedAt R' Q] :
    Algebra.IsUnramifiedAt R q := by
  sorry

end Layer0

/-! ## Layer 1: étaleness from codimension one -/

section Layer1

/-- **Affine form of Stacks, Lemma 58.21.2 (0BJH).** A finite-type algebra over a Noetherian
ring, quasi-finite and flat at a prime `q` of positive height and unramified at every prime of
height one below `q`, is étale at `q`. -/
@[stacks 0BJH "affine form"]
theorem isEtaleAt_of_flat_of_isUnramifiedAt_height_one {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [IsNoetherianRing R] [Algebra.FiniteType R S] (q : Ideal S) [q.IsPrime]
    [Algebra.QuasiFiniteAt R q] [Module.Flat R (Localization.AtPrime q)] (hq : 1 ≤ q.height)
    (hunr : ∀ (q' : Ideal S) [q'.IsPrime], q' ≤ q → q'.height = 1 →
      Algebra.IsUnramifiedAt R q') :
    Algebra.IsEtaleAt R q := by
  sorry

/-- A point has a local ring of positive dimension iff it is not the generic point of an
irreducible component. *API*; it translates condition (3) of Stacks, Lemma 58.21.2 (0BJH). -/
theorem one_le_ringKrullDim_stalk_iff {X : Scheme.{u}} (x : X) :
    1 ≤ ringKrullDim (X.presheaf.stalk x) ↔
      ∀ Z ∈ irreducibleComponents X, ¬ IsGenericPoint x Z := by
  sorry

/-- **Stacks, Lemma 58.21.2 (0BJH), library form.** A morphism of locally Noetherian schemes,
locally of finite type, flat and quasi-finite at `x`, with `dim 𝒪_{X,x} ≥ 1`, and formally
unramified at every specialization `x' ⤳ x` with `dim 𝒪_{X,x'} = 1`, is étale on an open
neighbourhood of `x`. This is the target. -/
@[stacks 0BJH]
theorem exists_etale_of_flat_of_formallyUnramified_codimOne {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y) [LocallyOfFiniteType f] (x : X)
    (hflat : (f.stalkMap x).hom.Flat) (hqf : f.QuasiFiniteAt x)
    (hdim : 1 ≤ ringKrullDim (X.presheaf.stalk x))
    (hunr : ∀ x' : X, x' ⤳ x → ringKrullDim (X.presheaf.stalk x') = 1 →
      (f.stalkMap x').hom.FormallyUnramified) :
    ∃ U : X.Opens, x ∈ U ∧ Etale (U.ι ≫ f) := by
  sorry

/-- **Stacks, Lemma 58.21.2 (0BJH)**, accompanying statement in the form of the tag: `f` is flat
but not assumed locally of finite type, "quasi-finite at `x`" and "unramified at `x'`" are Stacks'
Definitions 29.21.1 (01TD) and 29.36.1 (02G4) written with Mathlib's morphism classes, and `x` is
not the generic point of an irreducible component. It follows from
`exists_etale_of_flat_of_formallyUnramified_codimOne` by PurityOfBranchLocus §0.1
`unramifiedAt_iff_stalkMap` and `one_le_ringKrullDim_stalk_iff`. -/
@[stacks 0BJH "Stacks form"]
theorem etaleAt_of_flat_of_unramifiedAt_codimOne {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [Flat f] (x : X)
    (hqf : (∃ U : X.Opens, x ∈ U ∧ LocallyOfFiniteType (U.ι ≫ f)) ∧ f.QuasiFiniteAt x)
    (hgen : ∀ Z ∈ irreducibleComponents X, ¬ IsGenericPoint x Z)
    (hunr : ∀ x' : X, x' ⤳ x → ringKrullDim (X.presheaf.stalk x') = 1 →
      ∃ U : X.Opens, x' ∈ U ∧ LocallyOfFiniteType (U.ι ≫ f) ∧ FormallyUnramified (U.ι ≫ f)) :
    ∃ U : X.Opens, x ∈ U ∧ Etale (U.ι ≫ f) := by
  sorry

end Layer1

end

end TauCetiRoadmap.FiniteEtaleExtensionAcrossDepthTwo
