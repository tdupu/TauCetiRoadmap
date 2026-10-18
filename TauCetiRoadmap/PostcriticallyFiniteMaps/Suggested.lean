import Mathlib
import TauCeti.AlgebraicGeometry.Scheme.CodimensionOnePoint

/-!
# Post-critically finite maps: suggested forms

**This file is not the roadmap and is not exhaustive.** The definitive document is
`README.md`. The statements here suggest Lean forms for particular milestones, so that
contributors and reviewers converge on names and signatures; discharging all of them
finishes neither a layer nor the roadmap.

Loci are sets of points whose members have coheight one: the generic points of prime divisors
(Tau Ceti's `TauCeti.AlgebraicGeometry.CodimensionOnePoint`). The normal-scheme predicate and the
ramification index at a point are SchemeAndStackFoundations §0.30 (`IsNormalScheme`,
`Scheme.Hom.ramificationIdxAt`); this file writes normality as the two stalk conditions and the
ramification index as its defining formula, so that it builds against the pinned libraries.
Declarations with a Stacks Project counterpart carry `@[stacks]`.
-/

universe u

namespace TauCetiRoadmap.PostcriticallyFiniteMaps

noncomputable section

open AlgebraicGeometry CategoryTheory Order TopologicalSpace

/-! ## Layer 0: preperiodic points and forward orbits -/

section Layer0

variable {α : Type*} (f : α → α)

/-- `x` is preperiodic for `f`: `f^[r + s] x = f^[r] x` for some `r` and some `s ≥ 1`. -/
def IsPreperiodicPt (x : α) : Prop :=
  ∃ r s : ℕ, 0 < s ∧ f^[r + s] x = f^[r] x

/-- A point is preperiodic iff its forward orbit is finite. -/
theorem isPreperiodicPt_iff_finite_range_iterate (x : α) :
    IsPreperiodicPt f x ↔ (Set.range fun n : ℕ ↦ f^[n] x).Finite := by
  sorry

/-- The forward orbit `⋃ n, f^[n] '' s` of a set. -/
def forwardOrbit (s : Set α) : Set α :=
  ⋃ n : ℕ, f^[n] '' s

/-- The forward orbit of a finite set is finite iff each of its points is preperiodic. -/
theorem finite_forwardOrbit_iff {s : Set α} (hs : s.Finite) :
    (forwardOrbit f s).Finite ↔ ∀ x ∈ s, IsPreperiodicPt f x := by
  sorry

/-- A self-map of a finite nonempty invariant set has a periodic point in it. -/
theorem exists_isPeriodicPt_of_mapsTo {s : Set α} (hs : s.Finite) (hne : s.Nonempty)
    (h : Set.MapsTo f s s) : ∃ x ∈ s, ∃ n, 0 < n ∧ Function.IsPeriodicPt f n x := by
  sorry

/-- A semiconjugacy carries forward orbits to forward orbits. -/
theorem image_forwardOrbit_of_semiconj {β : Type*} (g : β → β) (π : β → α)
    (h : Function.Semiconj π g f) (t : Set β) :
    π '' forwardOrbit g t = forwardOrbit f (π '' t) := by
  sorry

end Layer0

/-! ## Layer 1: ramification in codimension one -/

section Layer1

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The ramification index of `f` at `x` (SchemeAndStackFoundations §0.30
`Scheme.Hom.ramificationIdxAt`), written out. -/
abbrev ramificationIdxAt (x : X) : ℕ :=
  letI := (f.stalkMap x).hom.toAlgebra
  (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).ramificationIdx (Y.presheaf.stalk (f x))

/-- In characteristic zero, at a codimension-one point, a finite dominant morphism of normal
varieties has ramification index one iff it is étale there. Stacks 02GF (6) and 02GU. -/
@[stacks 02GF "(6), at a codimension-one point of a normal variety"]
theorem ramificationIdxAt_eq_one_iff (k : Type u) [Field k] [CharZero k]
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (sY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType sY] [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] [NoetherianSpace X] [NoetherianSpace Y]
    [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
    [∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)]
    [IsFinite f] [IsDominant f] (x : X) (hx : coheight x = 1) :
    ramificationIdxAt f x = 1 ↔
      (f.stalkMap x).hom.Flat ∧ (f.stalkMap x).hom.FormallyUnramified := by
  sorry

end Layer1

/-! ## Layer 2: normalization and the normalization lift -/

section Layer2

/-- The inclusion of the generic point of an integral scheme is quasi-compact. -/
instance fromSpecStalk_genericPoint_quasiCompact (X : Scheme.{u}) [IsIntegral X] :
    QuasiCompact (X.fromSpecStalk (genericPoint X)) := by
  sorry

/-- The normalization `X̃` of an integral scheme: Mathlib's relative normalization of `X` in its
function field. -/
abbrev normalization (X : Scheme.{u}) [IsIntegral X] : Scheme.{u} :=
  (X.fromSpecStalk (genericPoint X)).normalization

/-- The normalization morphism `ν : X̃ ⟶ X`. -/
abbrev normalizationHom (X : Scheme.{u}) [IsIntegral X] : normalization X ⟶ X :=
  (X.fromSpecStalk (genericPoint X)).fromNormalization

/-- The normalization is normal. Stacks, Lemma 29.54.13 (035L). -/
@[stacks 035L]
theorem isIntegrallyClosed_stalk_normalization (X : Scheme.{u}) [IsIntegral X]
    (x : normalization X) : IsIntegrallyClosed ((normalization X).presheaf.stalk x) := by
  sorry

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

/-- The **normalization lift** `f̃ : X̃ ⟶ Ỹ` of a dominant morphism of integral schemes, with
`f̃ ≫ ν_Y = ν_X ≫ f`. Stacks, Lemma 29.55.5 (035Q) (4). -/
@[stacks 035Q "(4)"]
def normalizationLift (f : X ⟶ Y) [IsDominant f] : normalization X ⟶ normalization Y :=
  sorry

theorem normalizationLift_comp_normalizationHom (f : X ⟶ Y) [IsDominant f] :
    normalizationLift f ≫ normalizationHom Y = normalizationHom X ≫ f := by
  sorry

instance isDominant_normalizationLift (f : X ⟶ Y) [IsDominant f] :
    IsDominant (normalizationLift f) := by
  sorry

/-- The lift is the unique dominant morphism over `f`. -/
theorem normalizationLift_unique (f : X ⟶ Y) [IsDominant f] (g : normalization X ⟶ normalization Y)
    [IsDominant g] (hg : g ≫ normalizationHom Y = normalizationHom X ≫ f) :
    g = normalizationLift f := by
  sorry

theorem normalizationLift_comp {Z : Scheme.{u}} [IsIntegral Z] (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsDominant f] [IsDominant g] :
    normalizationLift (f ≫ g) = normalizationLift f ≫ normalizationLift g := by
  sorry

end Layer2

/-! ## Layer 3: divisorial loci and postcritical sets -/

section Layer3

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsDominant f]

/-- The **divisorial critical locus** `Crit(f)`: the images of the codimension-one points of `X̃`
at which the normalization lift is ramified. -/
def divisorialCriticalLocus : Set X :=
  ⇑(normalizationHom X) ''
    {x | coheight x = 1 ∧ 1 < ramificationIdxAt (normalizationLift f) x}

/-- The **divisorial branch locus** `Branch(f) = f(Crit(f))`. -/
def divisorialBranchLocus : Set Y :=
  ⇑f '' divisorialCriticalLocus f

/-- The **non-unramified divisorial critical locus** `Crit₀(f)`: the codimension-one points of
PurityOfBranchLocus §0.4 `Scheme.Hom.ramificationLocus`. -/
def nonUnramifiedDivisorialCriticalLocus : Set X :=
  {x | coheight x = 1 ∧ ¬ (f.stalkMap x).hom.FormallyUnramified}

/-- The **non-unramified divisorial branch locus** `Branch₀(f)`. -/
def nonUnramifiedDivisorialBranchLocus : Set Y :=
  ⇑f '' nonUnramifiedDivisorialCriticalLocus f

/-- The **non-étale divisorial critical locus** `Crit₁(f)`: the codimension-one points of
PurityOfBranchLocus §0.4 `Scheme.Hom.nonEtaleLocus` (stalk form, PurityOfBranchLocus §0.1). -/
def nonEtaleDivisorialCriticalLocus : Set X :=
  {x | coheight x = 1 ∧ ¬ ((f.stalkMap x).hom.Flat ∧ (f.stalkMap x).hom.FormallyUnramified)}

/-- The **non-étale divisorial branch locus** `Branch₁(f)`. -/
def nonEtaleDivisorialBranchLocus : Set Y :=
  ⇑f '' nonEtaleDivisorialCriticalLocus f

/-- `Branch(f) ⊆ Branch₀(f)` in characteristic zero. -/
theorem divisorialBranchLocus_subset_nonUnramified (k : Type u) [Field k] [CharZero k]
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] [IsLocallyNoetherian X] [NoetherianSpace X]
    [IsFinite f] :
    divisorialBranchLocus f ⊆ nonUnramifiedDivisorialBranchLocus f := by
  sorry

theorem nonUnramifiedDivisorialBranchLocus_subset_nonEtale :
    nonUnramifiedDivisorialBranchLocus f ⊆ nonEtaleDivisorialBranchLocus f := by
  sorry

/-- The non-étale divisorial critical locus is finite. -/
theorem finite_nonEtaleDivisorialCriticalLocus (k : Type u) [Field k] [CharZero k]
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] [IsLocallyNoetherian X] [NoetherianSpace X]
    [IsFinite f] :
    (nonEtaleDivisorialCriticalLocus f).Finite := by
  sorry

/-- **Tower formula** for the divisorial branch locus. -/
theorem divisorialBranchLocus_comp {Z : Scheme.{u}} [IsIntegral Z] (g : Y ⟶ Z) [IsDominant g]
    (k : Type u) [Field k] [CharZero k] (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX]
    [IsLocallyNoetherian X] [NoetherianSpace X] [IsFinite f] [IsFinite g] :
    divisorialBranchLocus (f ≫ g) = divisorialBranchLocus g ∪ ⇑g '' divisorialBranchLocus f := by
  sorry

/-- The `n`-th iterate `φ ≫ ⋯ ≫ φ` of an endomorphism. -/
def iterateHom {W : Scheme.{u}} (φ : W ⟶ W) : ℕ → (W ⟶ W)
  | 0 => 𝟙 W
  | n + 1 => iterateHom φ n ≫ φ

variable (φ : X ⟶ X) [IsDominant φ]

/-- The **postcritical set** `PC(φ)`: the forward orbit of the divisorial branch locus. -/
def postcriticalSet : Set X :=
  forwardOrbit (⇑φ) (divisorialBranchLocus φ)

/-- `φ` is **post-critically finite**. -/
def IsPCF : Prop :=
  (postcriticalSet φ).Finite

/-- The non-unramified postcritical set `PC₀(φ)`. -/
def nonUnramifiedPostcriticalSet : Set X :=
  forwardOrbit (⇑φ) (nonUnramifiedDivisorialBranchLocus φ)

/-- The non-étale postcritical set `PC₁(φ)`. -/
def nonEtalePostcriticalSet : Set X :=
  forwardOrbit (⇑φ) (nonEtaleDivisorialBranchLocus φ)

/-- `φ` is non-unramified PCF (`0`-PCF in the manuscript). -/
def IsNonUnramifiedPCF : Prop :=
  (nonUnramifiedPostcriticalSet φ).Finite

/-- `φ` is non-étale PCF (`1`-PCF in the manuscript). -/
def IsNonEtalePCF : Prop :=
  (nonEtalePostcriticalSet φ).Finite

/-- `φ` is PCF iff its normalization lift is. -/
theorem isPCF_normalizationLift_iff (k : Type u) [Field k] [CharZero k]
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] [IsLocallyNoetherian X] [NoetherianSpace X]
    [IsFinite φ] :
    IsPCF (normalizationLift φ) ↔ IsPCF φ := by
  sorry

/-- PCF is invariant under positive iteration. -/
theorem isPCF_iterateHom_iff (k : Type u) [Field k] [CharZero k]
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] [IsLocallyNoetherian X] [NoetherianSpace X]
    [IsFinite φ] {m : ℕ} (hm : 0 < m) [IsDominant (iterateHom φ m)] :
    IsPCF (iterateHom φ m) ↔ IsPCF φ := by
  sorry

end Layer3

/-! ## Layer 4: closures of points -/

section Layer4

variable {X Y : Scheme.{u}}

/-- The reduced closed subscheme `\overline{\{y\}}`. -/
abbrev pointClosure (y : X) : Scheme.{u} :=
  (Scheme.IdealSheafData.vanishingIdeal ⟨closure {y}, isClosed_closure⟩).subscheme

/-- Its closed immersion into `X`. -/
abbrev pointClosureι (y : X) : pointClosure y ⟶ X :=
  (Scheme.IdealSheafData.vanishingIdeal ⟨closure {y}, isClosed_closure⟩).subschemeι

instance isIntegral_pointClosure (y : X) : IsIntegral (pointClosure y) := by
  sorry

/-- A finite morphism induces `\overline{\{y\}} ⟶ \overline{\{f y\}}`. Stacks 0356. -/
@[stacks 0356 "for the reduced closure of a point"]
def pointClosureMap (f : X ⟶ Y) (y : X) : pointClosure y ⟶ pointClosure (f y) :=
  sorry

theorem pointClosureMap_comp_ι (f : X ⟶ Y) (y : X) :
    pointClosureMap f y ≫ pointClosureι (f y) = pointClosureι y ≫ f := by
  sorry

instance isFinite_pointClosureMap (f : X ⟶ Y) [IsFinite f] (y : X) :
    IsFinite (pointClosureMap f y) := by
  sorry

/-- The **restriction** of an endomorphism fixing `y` to the closure of `y`. -/
def restrictPointClosure (φ : X ⟶ X) (y : X) (hy : φ y = y) :
    pointClosure y ⟶ pointClosure y :=
  sorry

theorem restrictPointClosure_comp_ι (φ : X ⟶ X) (y : X) (hy : φ y = y) :
    restrictPointClosure φ y hy ≫ pointClosureι y = pointClosureι y ≫ φ := by
  sorry

instance isFinite_restrictPointClosure (φ : X ⟶ X) [IsFinite φ] (y : X) (hy : φ y = y) :
    IsFinite (restrictPointClosure φ y hy) := by
  sorry

instance isDominant_restrictPointClosure (φ : X ⟶ X) [IsFinite φ] [IsDominant φ] [IsIntegral X]
    (y : X) (hy : φ y = y) : IsDominant (restrictPointClosure φ y hy) := by
  sorry

end Layer4

/-! ## Layer 5: the bounding theorem -/

section Layer5

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsDominant f]

/-- The non-regular points of a scheme (the complement of SchemeAndStackFoundations §4.13
`regularLocus`). -/
def singularLocus (W : Scheme.{u}) : Set W :=
  {w | ¬ IsRegularLocalRing (W.presheaf.stalk w)}

/-- The **exceptional set** `Σ = (B ∩ Z) ∪ (B ∩ Sing Y) ∪ Sing B` of the bounding theorem, for
`B` the closure of `f a` and `Z` the union of the closures of the other points of the divisorial
branch locus. -/
def boundingLocus (a : X) : Set Y :=
  (closure {f a} ∩ ⋃ E ∈ divisorialBranchLocus f \ {f a}, closure {E}) ∪
    (closure {f a} ∩ singularLocus Y) ∪
    ⇑(pointClosureι (f a)) '' singularLocus (pointClosure (f a))

/-- **The bounding theorem.** For a finite dominant morphism of normal varieties over a field of
characteristic zero and a codimension-one point `a`, the induced map of closures is étale at every
codimension-one point whose image avoids the exceptional set. -/
theorem isEtaleAt_pointClosureMap_of_notMem_boundingLocus (k : Type u) [Field k] [CharZero k]
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (sY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType sY] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [NoetherianSpace X] [NoetherianSpace Y]
    [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
    [∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)] [IsFinite f]
    (a : X) (ha : coheight a = 1) (x : pointClosure a) (hx : coheight x = 1)
    (hSigma : pointClosureι (f a) (pointClosureMap f a x) ∉ boundingLocus f a) :
    ((pointClosureMap f a).stalkMap x).hom.Flat ∧
      ((pointClosureMap f a).stalkMap x).hom.FormallyUnramified := by
  sorry

end Layer5

/-! ## Layer 6: PCF all the way down -/

section Layer6

/-- **PCF all the way down, to depth `d`.** -/
def IsPCFAllTheWayDownAtDepth : ℕ → ∀ {X : Scheme.{u}} [IsIntegral X]
    (φ : X ⟶ X) [IsDominant φ], Prop
  | 0, _, _, φ, _ => IsPCF φ
  | d + 1, X, _, φ, _ => IsPCF φ ∧
      ∀ (x : X) (r s : ℕ) (_hs : 0 < s), coheight x = 1 → (⇑φ)^[r + s] x = (⇑φ)^[r] x →
        ∀ (hy : (iterateHom φ s) ((⇑φ)^[r] x) = (⇑φ)^[r] x),
          ∀ [IsDominant (restrictPointClosure (iterateHom φ s) ((⇑φ)^[r] x) hy)],
            IsPCFAllTheWayDownAtDepth d
              (restrictPointClosure (iterateHom φ s) ((⇑φ)^[r] x) hy)

/-- **PCF all the way down**: at every depth. -/
def IsPCFAllTheWayDown {X : Scheme.{u}} [IsIntegral X] (φ : X ⟶ X) [IsDominant φ] : Prop :=
  ∀ d, IsPCFAllTheWayDownAtDepth d φ

/-- **Restriction to a preperiodic prime divisor** in characteristic zero. -/
theorem isPCF_restrictPointClosure (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] [IsIntegral X]
    [IsLocallyNoetherian X] [NoetherianSpace X] (φ : X ⟶ X) [IsFinite φ] [IsDominant φ]
    (hφ : IsPCF φ) (x : X) (hx : coheight x = 1) (r s : ℕ) (hs : 0 < s)
    (hper : (⇑φ)^[r + s] x = (⇑φ)^[r] x)
    (hy : (iterateHom φ s) ((⇑φ)^[r] x) = (⇑φ)^[r] x)
    [IsDominant (restrictPointClosure (iterateHom φ s) ((⇑φ)^[r] x) hy)] :
    IsPCF (restrictPointClosure (iterateHom φ s) ((⇑φ)^[r] x) hy) := by
  sorry

/-- **PCF all the way down in characteristic zero.** -/
theorem isPCFAllTheWayDown (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] [IsIntegral X]
    [IsLocallyNoetherian X] [NoetherianSpace X] (φ : X ⟶ X) [IsFinite φ] [IsDominant φ]
    (hφ : IsPCF φ) :
    IsPCFAllTheWayDown φ := by
  sorry

end Layer6

/-! ## Layer 7: self-maps of projective space -/

section Layer7

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Projective space `ℙⁿ_k` as Mathlib's `Proj` of the standard grading. -/
abbrev projectiveSpace (k : Type u) [Field k] (n : ℕ) : Scheme.{u} :=
  Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)

/-- A system of forms of degree `d ≥ 1` without common zero. -/
structure FormsWithoutCommonZero (k : Type u) [Field k] (n d : ℕ) where
  /-- The forms. -/
  forms : Fin (n + 1) → MvPolynomial (Fin (n + 1)) k
  one_le_degree : 1 ≤ d
  isHomogeneous : ∀ i, (forms i).IsHomogeneous d
  mem_radical : ∀ j, MvPolynomial.X j ∈ (Ideal.span (Set.range forms)).radical

namespace FormsWithoutCommonZero

variable {k : Type u} [Field k] {n d : ℕ}

/-- The self-map of `ℙⁿ_k` given by the forms. -/
def toHom (Φ : FormsWithoutCommonZero k n d) : projectiveSpace k n ⟶ projectiveSpace k n :=
  sorry

/-- On points, the preimage of the chart `x_b ≠ 0` is the locus `F_b ≠ 0`. -/
theorem toHom_preimage_basicOpen (Φ : FormsWithoutCommonZero k n d) (b : Fin (n + 1)) :
    Φ.toHom ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X b) = Proj.basicOpen _ (Φ.forms b) := by
  sorry

instance isFinite_toHom (Φ : FormsWithoutCommonZero k n d) : IsFinite Φ.toHom := by
  sorry

instance isDominant_toHom (Φ : FormsWithoutCommonZero k n d) : IsDominant Φ.toHom := by
  sorry

end FormsWithoutCommonZero

instance isIntegral_projectiveSpace (k : Type u) [Field k] (n : ℕ) :
    IsIntegral (projectiveSpace k n) := by
  sorry

/-- Dupont's map `[(x − y + z)² : (x + y − z)² : (−x + y + z)²]` on `ℙ²`. -/
def dupont (k : Type u) [Field k] [CharZero k] : FormsWithoutCommonZero k 2 2 where
  forms := ![(MvPolynomial.X 0 - MvPolynomial.X 1 + MvPolynomial.X 2) ^ 2,
    (MvPolynomial.X 0 + MvPolynomial.X 1 - MvPolynomial.X 2) ^ 2,
    (-MvPolynomial.X 0 + MvPolynomial.X 1 + MvPolynomial.X 2) ^ 2]
  one_le_degree := by norm_num
  isHomogeneous := sorry
  mem_radical := sorry

/-- Check: Dupont's map is PCF, with postcritical set of six lines. -/
theorem test_dupont (k : Type u) [Field k] [CharZero k] :
    IsPCF (dupont k).toHom ∧ (postcriticalSet (dupont k).toHom).ncard = 6 := by
  sorry

/-- The wild map `[x^p(x + y) : y^{p+1} − x^{p+1} − x^p z + x y^p + c z^{p+1} : z^{p+1}]`. -/
def wild (k : Type u) [Field k] (p : ℕ) (c : k) : FormsWithoutCommonZero k 2 (p + 1) where
  forms := ![MvPolynomial.X 0 ^ p * (MvPolynomial.X 0 + MvPolynomial.X 1),
    MvPolynomial.X 1 ^ (p + 1) - MvPolynomial.X 0 ^ (p + 1) - MvPolynomial.X 0 ^ p * MvPolynomial.X 2
      + MvPolynomial.X 0 * MvPolynomial.X 1 ^ p + MvPolynomial.C c * MvPolynomial.X 2 ^ (p + 1),
    MvPolynomial.X 2 ^ (p + 1)]
  one_le_degree := by omega
  isHomogeneous := sorry
  mem_radical := sorry

/-- Check: in characteristic `p`, with `c` transcendental over `𝔽_p`, the wild map is PCF and not
PCF all the way down. -/
theorem test_wild (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) k] (c : k)
    (hc : Transcendental (ZMod p) c) :
    IsPCF (wild k p c).toHom ∧ ¬ IsPCFAllTheWayDown (wild k p c).toHom := by
  sorry

end Layer7

/-! ## Checks on affine space -/

section Checks

/-- The squaring map `x ↦ x²` on `𝔸¹_k`. -/
def squaringLine (k : Type u) [Field k] : Spec (.of (Polynomial k)) ⟶ Spec (.of (Polynomial k)) :=
  Spec.map (CommRingCat.ofHom (Polynomial.aeval (Polynomial.X ^ 2 : Polynomial k)).toRingHom)

instance (k : Type u) [Field k] : IsDominant (squaringLine k) := by
  sorry

/-- Check: the squaring map of `𝔸¹` has postcritical set `{0}`. -/
theorem test_squaring_line (k : Type u) [Field k] [CharZero k] :
    IsPCF (squaringLine k) ∧ (postcriticalSet (squaringLine k)).ncard = 1 := by
  sorry

end Checks

end

end TauCetiRoadmap.PostcriticallyFiniteMaps
