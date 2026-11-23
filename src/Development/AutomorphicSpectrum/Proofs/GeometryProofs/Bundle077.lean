module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle064
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsCompatibleAlongMap
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LinearIndependentEigProj
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Valuation.LocalSubring
public import Mathlib.RingTheory.RingHom.Smooth
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle052
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem germ_top_stalk_closed_point {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) {q : X}
    (hq : ξ (IsLocalRing.closedPoint Ω) ⤳ q) :
    X.presheaf.germ ⊤ q (show q ∈ (⊤ : X.Opens) from trivial) ≫ X.presheaf.stalkSpecializes hq ≫ Scheme.stalkClosedPointTo ξ
      = ξ.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom := by
  rw [TopCat.Presheaf.germ_stalkSpecializes_assoc, Scheme.germ_stalkClosedPointTo]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, Scheme.Hom.appTop]
  have e : ∀ (f : (⊤ : (Spec (CommRingCat.of Ω)).Opens) ⟶ ξ ⁻¹ᵁ ⊤),
      (Spec (CommRingCat.of Ω)).presheaf.map f.op = 𝟙 _ := fun f => (Spec (CommRingCat.of Ω)).presheaf.map_id _
  erw [e]
  simp

theorem algebraMap_mem_regAt' {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    {O : Type} [CommRing O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O))
    (h : ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω))) (p : Cpt ξ) (o : O) :
    algebraMap O Ω o ∈ regAt ξ p := by
  obtain ⟨q, hq⟩ := p
  refine ⟨X.presheaf.germ ⊤ q (show q ∈ (⊤ : X.Opens) from trivial) (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o)), ?_⟩
  have h1 := germ_top_stalk_closed_point ξ hq
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ s.appTop ≫ ξ.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom
      = CommRingCat.ofHom (algebraMap O Ω) := by
    have : s.appTop ≫ ξ.appTop = (ξ ≫ s).appTop := by simp
    rw [reassoc_of% this, h]
    simp
  have h3 := congrArg (fun f => f.hom o) h2
  have h4 := congrArg (fun f => f.hom (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o))) h1
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h3 h4
  rw [CommRingCat.hom_ofHom] at h3
  refine Eq.trans ?_ (h4.trans h3)
  rfl

theorem isIntegral_of_forall_valuationSubring' {R Ω : Type} [CommRing R] [Field Ω] [Algebra R Ω]
    (hf : Function.Injective (algebraMap R Ω)) (a : Ω)
    (H : ∀ V : ValuationSubring Ω, (∀ r : R, algebraMap R Ω r ∈ V) → a ∈ V) : IsIntegral R a := by
  have hall : a ∈ ⨅ V : {V : ValuationSubring Ω // Set.range (algebraMap R Ω) ⊆ V.toSubring}, V.1.toSubring :=
    Subring.mem_iInf.mpr fun V => H V.1 fun r => V.2 ⟨r, rfl⟩
  rw [iInf_valuationSubring_superset, Subalgebra.mem_toSubring, mem_integralClosure_iff] at hall
  let g : R →+* Subring.closure (Set.range (algebraMap R Ω)) :=
    (algebraMap R Ω).codRestrict _ fun r => Subring.subset_closure ⟨r, rfl⟩
  have hg : Function.Bijective g := by
    refine ⟨fun x y hxy => hf (congrArg Subtype.val hxy), ?_⟩
    rintro ⟨y, hy⟩
    have hle : Subring.closure (Set.range (algebraMap R Ω)) ≤ (algebraMap R Ω).range :=
      Subring.closure_le.mpr fun z hz => hz
    obtain ⟨r, rfl⟩ := hle hy
    exact ⟨r, rfl⟩
  let e := RingEquiv.ofBijective g hg
  have hcomp : (algebraMap R Ω).comp (e.symm : _ →+* R) =
      (RingHom.id Ω).comp (algebraMap (Subring.closure (Set.range (algebraMap R Ω))) Ω) := by
    ext x
    have : g (e.symm x) = x := e.apply_symm_apply x
    exact congrArg Subtype.val this
  exact IsIntegral.map_of_comp_eq (e.symm : _ →+* R) (RingHom.id Ω) hcomp hall

theorem isIntegral_and_isAlgebraic_of_regular : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s], ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → Function.Injective (algebraMap O Ω) → IsCptGen ξ → ∀ a : Ω, ((∀ p : Cpt ξ, a ∈ regAt ξ p) → IsIntegral O a) ∧ ((∀ p ∈ genFibre O ξ, a ∈ regAt ξ p) → IsAlgebraic O a) := by
  intro X Ω _ ξ O _ _ _ s _ h hinj _ a
  refine ⟨fun ha => isIntegral_of_forall_valuationSubring' hinj a fun V hV => ?_, fun ha => ?_⟩
  · obtain ⟨p, hp, -⟩ := GlobalTheory.T.valuation_centre_regular_unit X Ω ξ O s h V hV
    exact hp (ha p)
  · haveI : FaithfulSMul O Ω := (faithfulSMul_iff_algebraMap_injective O Ω).2 hinj
    letI := FractionRing.liftAlgebra O Ω
    haveI : IsScalarTower O (FractionRing O) Ω := inferInstance
    refine (IsFractionRing.isAlgebraic_iff O (FractionRing O) Ω).2 (IsIntegral.isAlgebraic
      (isIntegral_of_forall_valuationSubring' (algebraMap (FractionRing O) Ω).injective a fun V hV => ?_))
    have hO : ∀ o : O, algebraMap O Ω o ∈ V := fun o => by
      rw [IsScalarTower.algebraMap_apply O (FractionRing O) Ω]
      exact hV _
    obtain ⟨p, hp, hu⟩ := GlobalTheory.T.valuation_centre_regular_unit X Ω ξ O s h V hO
    refine hp (ha p fun o ho => ?_)
    have hne : algebraMap O Ω o ≠ 0 := fun h0 => ho (hinj (by simpa using h0))
    have hreg := algebraMap_mem_regAt' ξ s h p o
    have hinv : (algebraMap O Ω o)⁻¹ ∈ V := by
      rw [IsScalarTower.algebraMap_apply O (FractionRing O) Ω, ← map_inv₀]
      exact hV _
    obtain ⟨g, hg, hga⟩ := hu _ hreg hne hinv
    obtain ⟨u, rfl⟩ := hg
    refine ⟨hne, hreg, ⟨(u⁻¹ : (X.presheaf.stalk p.1)ˣ).1, ?_⟩⟩
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← hga, ← map_mul, Units.inv_mul, map_one]

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncSmooth

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

theorem exists_mul_pow_mem (T : Set Ω) {f : Ω} (hf0 : f ≠ 0) {x : Ω}
    (hx : x ∈ Algebra.adjoin ℚ (insert f⁻¹ T)) (hf : f ∈ Algebra.adjoin ℚ T) :
    ∃ n : ℕ, x * f ^ n ∈ Algebra.adjoin ℚ T := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · exact ⟨1, by simpa [hf0] using (Algebra.adjoin ℚ T).one_mem⟩
    · exact ⟨0, by simpa using Algebra.subset_adjoin hx⟩
  | algebraMap r => exact ⟨0, by simpa using (Algebra.adjoin ℚ T).algebraMap_mem r⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨m, hm⟩ := hy
    refine ⟨n + m, ?_⟩
    have : (x + y) * f ^ (n + m) = x * f ^ n * f ^ m + y * f ^ m * f ^ n := by ring
    rw [this]
    exact add_mem (mul_mem hn (pow_mem hf m)) (mul_mem hm (pow_mem hf n))
  | mul x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨m, hm⟩ := hy
    refine ⟨n + m, ?_⟩
    have : x * y * f ^ (n + m) = x * f ^ n * (y * f ^ m) := by ring
    rw [this]
    exact mul_mem hn hm

theorem isLocalization_away (A S : Subalgebra ℚ Ω) (hle : A ≤ S) (f : A) (hf0 : (f : Ω) ≠ 0)
    (hinv : (f : Ω)⁻¹ ∈ S) (hs : ∀ x ∈ S, ∃ n : ℕ, x * (f : Ω) ^ n ∈ A) :
    @IsLocalization.Away A _ f S _ (Subalgebra.inclusion hle).toRingHom.toAlgebra := by
  letI := (Subalgebra.inclusion hle).toRingHom.toAlgebra
  have hmap : ∀ a : A, ((algebraMap A S a : S) : Ω) = a := fun a => rfl
  have hunit : IsUnit (algebraMap A S f) := by
    refine IsUnit.of_mul_eq_one (⟨(f : Ω)⁻¹, hinv⟩ : S) ?_
    apply Subtype.ext
    rw [Subalgebra.coe_mul, hmap]
    exact mul_inv_cancel₀ hf0
  refine IsLocalization.Away.mk _ hunit ?_ ?_
  · rintro ⟨x, hx⟩
    obtain ⟨n, hn⟩ := hs x hx
    refine ⟨n, ⟨x * (f : Ω) ^ n, hn⟩, ?_⟩
    apply Subtype.ext
    rw [hmap, Subalgebra.coe_mul, Subalgebra.coe_pow, hmap]
  · intro a b hab
    refine ⟨0, ?_⟩
    have : (a : Ω) = b := by rw [← hmap a, ← hmap b, hab]
    rw [Subtype.ext this]

theorem smooth_of_cover (A : Subalgebra ℚ Ω) {m : ℕ} (f a : Fin m → Ω) (hf : ∀ l, f l ∈ A) (ha : ∀ l, a l ∈ A)
    (hsum : ∑ l, a l * f l = 1) (S : Fin m → Subalgebra ℚ Ω) (hle : ∀ l, A ≤ S l)
    (hinv : ∀ l, f l ≠ 0 → (f l)⁻¹ ∈ S l) (hs : ∀ l, f l ≠ 0 → ∀ x ∈ S l, ∃ n : ℕ, x * f l ^ n ∈ A)
    (hsm : ∀ l, f l ≠ 0 → Algebra.Smooth ℚ (S l)) : Algebra.Smooth ℚ A := by
  let s : Set A := {x | (x : Ω) ≠ 0 ∧ ∃ l, (x : Ω) = f l}
  have hspan : Ideal.span s = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have h1 : (1 : A) = ∑ l, (⟨a l, ha l⟩ : A) * (⟨f l, hf l⟩ : A) := by
      apply Subtype.ext
      rw [Subalgebra.coe_one, ← hsum, AddSubmonoidClass.coe_finsetSum]
      rfl
    rw [h1]
    refine Ideal.sum_mem _ fun l _ => ?_
    by_cases h0 : f l = 0
    · have : (⟨f l, hf l⟩ : A) = 0 := Subtype.ext h0
      rw [this, mul_zero]
      exact Ideal.zero_mem _
    · exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨h0, l, rfl⟩)
  rw [← RingHom.smooth_algebraMap]
  refine RingHom.OfLocalizationSpanTarget.ofIsLocalization RingHom.Smooth.ofLocalizationSpanTarget
    RingHom.Smooth.respectsIso _ s hspan ?_
  rintro ⟨x, hx0, l, hl⟩
  have hx0' : f l ≠ 0 := hl ▸ hx0
  letI alg := (Subalgebra.inclusion (hle l)).toRingHom.toAlgebra
  have hloc : IsLocalization.Away x (S l) :=
    isLocalization_away A (S l) (hle l) x hx0 (hl ▸ hinv l hx0') (hl ▸ hs l hx0')
  refine ⟨S l, inferInstance, alg, hloc, ?_⟩
  have hcomp : (algebraMap A (S l)).comp (algebraMap ℚ A) = algebraMap ℚ (S l) := Subsingleton.elim _ _
  rw [hcomp]
  exact RingHom.smooth_algebraMap.mpr (hsm l hx0')

theorem smoothGenericFibreM_of_isSncModel (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type)
    [Field Ω] [Algebra ℚ Ω] (y : (Σ k, J k) → Ω) (e : ℕ) (bd : Ideal (MRing J))
    (h : Cmp.IsSncModel y e bd) : SmoothGenericFibreM y := by
  intro c hc
  obtain ⟨m, f, a, hf, ha, hsum, hS⟩ := h c hc
  exact smooth_of_cover _ f a hf ha hsum (fun l => Algebra.adjoin ℚ (insert (f l)⁻¹ _))
    (fun l => Algebra.adjoin_mono (Set.subset_insert _ _))
    (fun l _ => Algebra.subset_adjoin (Set.mem_insert _ _))
    (fun l h0 x hx => exists_mul_pow_mem _ h0 hx (hf l))
    (fun l h0 => (hS l h0 _ rfl).1)

end GlobalTheory.CompanionTheory.Ar.Cmp.SncSmooth
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.CombMul

theorem pt_sum_ofFn {S : Scheme.{0}} {G : Over S} [GrpObj G] {F : Type} [Field F] {x : Sp F ⟶ S} {V : Type}
    [AddCommGroup V] [Module F V] (M : LieModel G x V) : ∀ {n : ℕ} (u : Fin n → V),
    M.pt (∑ i, u i) = (List.ofFn fun i => M.pt (u i)).prod
  | 0, u => by simp [M.pt_zero]
  | n + 1, u => by
    rw [Fin.sum_univ_succ, M.add, pt_sum_ofFn M (fun i => u i.succ), List.ofFn_succ, List.prod_cons]

theorem isComb_pt_iff {S : Scheme.{0}} {G : Over S} [GrpObj G] {F : Type} [Field F] {x : Sp F ⟶ S} {V : Type}
    [AddCommGroup V] [Module F V] (M : LieModel G x V) {n : ℕ} (c : Fin n → F) (e : Fin n → V)
    (w : epsAt x ⟶ G) : IsComb c (fun i => M.pt (e i)) w ↔ w = M.pt (∑ i, c i • e i) := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    have h : u = fun i => M.pt (c i • e i) :=
      funext fun i => Over.OverMorphism.ext ((hu i).trans (M.smul _ _).symm)
    rw [pt_sum_ofFn, h]
  · rintro rfl
    exact ⟨fun i => M.pt (c i • e i), fun i => M.smul _ _, pt_sum_ofFn M _⟩

theorem isComb_mul : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (F : Type) [Field F] (x : Sp F ⟶ S) (m n k : ℕ) (v : Fin n → (epsAt x ⟶ G)) (u : Fin m → (epsAt x ⟶ G)) (w : Fin k → (epsAt x ⟶ G)) (A : Matrix (Fin k) (Fin m) F) (C : Matrix (Fin m) (Fin n) F), (∀ i, IsTanAt G x (v i)) → (∀ i, IsComb (C i) v (u i)) → (∀ i, IsComb (A i) u (w i)) → ∀ i, IsComb ((A * C) i) v (w i) := by
  intro S G _ _ F _ x m n k v u w A C hv hu hw i
  obtain ⟨E, _, _, ⟨M⟩⟩ := lieModel_exists S G F x
  obtain ⟨e, rfl⟩ : ∃ e : Fin n → E, v = fun i => M.pt (e i) := by
    choose e he using fun i => M.onto (v i) (hv i)
    exact ⟨e, funext fun i => (he i).symm⟩
  obtain rfl : u = fun j => M.pt (∑ l, C j l • e l) :=
    funext fun j => (isComb_pt_iff M (C j) e (u j)).1 (hu j)
  have hwi := (isComb_pt_iff M (A i) _ (w i)).1 (hw i)
  rw [isComb_pt_iff, hwi]
  congr 1
  simp only [Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
  exact Finset.sum_comm

end GlobalTheory.CompanionTheory.Ar.CombMul
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.CombEig

theorem pt_sum {S : Scheme.{0}} {G : Over S} [GrpObj G] {R : Type} [CommRing R] {x : Sp R ⟶ S} {V : Type}
    [AddCommGroup V] [Module R V] (M : LieModel G x V) :
    ∀ {n : ℕ} (e : Fin n → V), M.pt (∑ i, e i) = (List.ofFn fun i => M.pt (e i)).prod
  | 0, e => by simpa using M.pt_zero
  | n + 1, e => by
    rw [Fin.sum_univ_succ, List.ofFn_succ, List.prod_cons, M.add, pt_sum M]

theorem isEigVec_comb : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (F : Type) [Field F] (x : Sp F ⟶ S) (P : Type) [CommRing P] (act : OAct P G) (σ : P →+* F) (n : ℕ) (v : Fin n → (epsAt x ⟶ G)) (cf : Fin n → F) (w : epsAt x ⟶ G), (∀ i, IsEigVec act x σ (v i)) → IsComb cf v w → IsEigVec act x σ w := by
  intro S G _ _ F _ x P _ act σ n v cf w hv hc
  have key : ∀ y : epsAt x ⟶ G, IsEigVec act x σ y ↔
      (IsTanAt G x y ∧ ∀ a, y ≫ act.act a = LieTangent.epsScale x (σ a) ≫ y) := by
    intro y
    unfold IsEigVec
    refine and_congr_right fun _ => forall_congr' fun a => ?_
    constructor
    · intro h
      apply Over.OverMorphism.ext
      rw [h]
      rfl
    · intro h
      rw [h]
      rfl
  have hcomm : ∀ c d : F, LieTangent.epsScale x c ≫ LieTangent.epsScale x d =
      LieTangent.epsScale x d ≫ LieTangent.epsScale x c := by
    intro c d
    have hr : (epsMul c).comp (epsMul d) = (epsMul d).comp (epsMul c) := by
      refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_
      · simp [LieTangent.epsMul_fst]
      · simp [LieTangent.epsMul_snd, mul_left_comm]
    apply Over.OverMorphism.ext
    show Spec.map (CommRingCat.ofHom (epsMul c)) ≫ Spec.map (CommRingCat.ofHom (epsMul d)) =
      Spec.map (CommRingCat.ofHom (epsMul d)) ≫ Spec.map (CommRingCat.ofHom (epsMul c))
    rw [LieTangent.spec_comp, LieTangent.spec_comp, hr]
  obtain ⟨u, hu, rfl⟩ := hc
  have hu' : ∀ i, u i = LieTangent.epsScale x (cf i) ≫ v i := by
    intro i
    apply Over.OverMorphism.ext
    rw [hu i]
    rfl
  rw [key]
  apply List.prod_induction
    (fun y => IsTanAt G x y ∧ ∀ a, y ≫ act.act a = LieTangent.epsScale x (σ a) ≫ y)
  · rintro y z ⟨hy, hy'⟩ ⟨hz, hz'⟩
    refine ⟨LieTangent.isTanAt_mul hy hz, fun a => ?_⟩
    haveI := act.hom a
    rw [MonObj.mul_comp, hy', hz', MonObj.comp_mul]
  · refine ⟨LieTangent.isTanAt_one, fun a => ?_⟩
    haveI := act.hom a
    rw [MonObj.one_comp, MonObj.comp_one]
  · intro y hy
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
    rw [hu']
    obtain ⟨ht, he⟩ := (key (v i)).mp (hv i)
    refine ⟨LieTangent.isTanAt_scale (cf i) ht, fun a => ?_⟩
    rw [Category.assoc, he a, ← Category.assoc, ← Category.assoc, hcomm]

end GlobalTheory.CompanionTheory.Ar.CombEig
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.CombBase

theorem comp_list_prod {S : Scheme.{0}} {G A B : Over S} [GrpObj G] (g : A ⟶ B) (l : List (B ⟶ G)) :
    g ≫ l.prod = (l.map (g ≫ ·)).prod := by
  induction l with
  | nil => simp [comp_one]
  | cons a l ih => simp only [List.prod_cons, List.map_cons, comp_mul, ih]

theorem isComb_base : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (F : Type) [Field F] (x : Sp F ⟶ S) (F' : Type) [Field F'] (f : F →+* F') (x' : Sp F' ⟶ S), spMap f ≫ x = x' → ∀ (n : ℕ) (v : Fin n → (epsAt x ⟶ G)) (cf : Fin n → F) (w : epsAt x ⟶ G) (v' : Fin n → (epsAt x' ⟶ G)) (w' : epsAt x' ⟶ G), (∀ i, (v' i).left = spMap (dualMap f) ≫ (v i).left) → w'.left = spMap (dualMap f) ≫ w.left → IsComb cf v w → IsComb (fun i => f (cf i)) v' w' := by
  rintro S G _ _ F _ x F' _ f x' hx n v cf w v' w' hv hw ⟨u, hu, e⟩
  refine ⟨fun i => LieTangent.epsBase f hx ≫ u i, fun i => ?_, ?_⟩
  · change spMap (dualMap f) ≫ (u i).left = _
    rw [hu i, ← Category.assoc, LieTangent.spec_dual_eps, Category.assoc, hv i]
  · rw [(LieTangent.left_eq_iff f hx w' w).1 hw, e, comp_list_prod, List.map_ofFn]
    rfl

end GlobalTheory.CompanionTheory.Ar.CombBase
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.smoothGenericFibre_of_dominates : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (K₁ : Type) [Fintype K₁] (J₁ : K₁ → Type) [∀ k, Fintype (J₁ k)] (y₁ : (Σ k, J₁ k) → Ω) (K₂ : Type) [Fintype K₂] (J₂ : K₂ → Type) [∀ k, Fintype (J₂ k)] (y₂ : (Σ k, J₂ k) → Ω) (X₁ X₂ : Scheme.{0}) (ξ₁ : Spec (CommRingCat.of Ω) ⟶ X₁) (ξ₂ : Spec (CommRingCat.of Ω) ⟶ X₂) (g : X₂ ⟶ X₁), (∀ q : X₁, GlobalTheory.CompanionTheory.Ar.genPt ξ₁ ⤳ q) → (∀ q : X₂, GlobalTheory.CompanionTheory.Ar.genPt ξ₂ ⤳ q) → CoordTie ℤ ξ₁ (fun c' : (k : K₁) → J₁ k => ∏ k, y₁ ⟨k, c' k⟩) → CoordTie ℤ ξ₂ (fun c' : (k : K₂) → J₂ k => ∏ k, y₂ ⟨k, c' k⟩) → GlobalTheory.CompanionTheory.Ar.Dominates ξ₂ ξ₁ g (RingHom.id Ω) → SmoothGenericFibreM y₁ → (∀ q ∈ genFib ξ₁, IsoAt ξ₂ g (RingHom.id Ω) q) → SmoothGenericFibreM y₂ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SmoothChange.smoothGenericFibreM_of_isoAt | exact GlobalTheory.CompanionTheory.Ar.SmoothChange.smoothGenericFibreM_of_isoAt | (intros; apply GlobalTheory.CompanionTheory.Ar.SmoothChange.smoothGenericFibreM_of_isoAt <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem det_eq_det_mul_det_of_block {K : Type} [Field K] {p q : ℕ} (M : Matrix (Fin (p + q)) (Fin (p + q)) K)
    (P : Matrix (Fin p) (Fin p) K) (D : Matrix (Fin q) (Fin q) K)
    (h11 : ∀ i k, M (Fin.castAdd q i) (Fin.castAdd q k) = P i k)
    (h21 : ∀ j k, M (Fin.natAdd p j) (Fin.castAdd q k) = 0)
    (h22 : ∀ j l, M (Fin.natAdd p j) (Fin.natAdd p l) = D j l) : M.det = P.det * D.det := by
  have hM : M.submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks P (Matrix.of fun i l => M (Fin.castAdd q i) (Fin.natAdd p l)) 0 D := by
    ext a b
    rcases a with i | j <;> rcases b with k | l
    · simp [h11]
    · simp
    · simp [h21]
    · simp [h22]
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv M, hM, Matrix.det_fromBlocks_zero₂₁]

theorem exists_det_mul_eq_of_isAdapted
    (E : Type) [Field E] [NumberField E] (K W : Type) [Field K] [AddCommGroup W] [Module K W]
    (ρH : 𝓞 E →+* Module.End K (W × Module.Dual K W)) (σ : E →+* K) (p q : ℕ) (v v' : Fin p → W) (w w' : Fin q → W)
    (u u' : Fin (p + q) → W × Module.Dual K W) (P : Matrix (Fin p) (Fin p) K) (Q : Matrix (Fin q) (Fin q) K) :
    IsAdapted ρH σ v w u → IsAdapted ρH σ v' w' u' → LinearIndependent K v →
    Submodule.span K (Set.range u) = HT.eigSp ρH σ →
    (∀ i, v' i = ∑ k, P i k • v k) → (∀ i, w' i = ∑ k, Q i k • w k) →
    ∃ B : Matrix (Fin (p + q)) (Fin (p + q)) K, (∀ i, u' i = ∑ k, B i k • u k) ∧ B.det * Q.det = P.det := by
  intro h h' hv hspan hP hQ
  obtain ⟨-, h1, h2⟩ := h
  obtain ⟨he', h1', h2'⟩ := h'
  have hex : ∀ i, ∃ c : Fin (p + q) → K, ∑ k, c k • u k = u' i := fun i => by
    rw [← Submodule.mem_span_range_iff_exists_fun, hspan]
    exact he' i
  choose B hB using hex
  let M : Matrix (Fin (p + q)) (Fin (p + q)) K := Matrix.of B
  have hMB : ∀ i k, M i k = B i k := fun _ _ => rfl
  refine ⟨M, fun i => (hB i).symm, ?_⟩
  have hfst : ∀ i, (u' i).1 = ∑ k : Fin p, M i (Fin.castAdd q k) • v k := fun i => by
    rw [← hB i, Prod.fst_sum, Fin.sum_univ_add]
    simp [h1, (h2 _).1, hMB]
  have h11 : ∀ i k, M (Fin.castAdd q i) (Fin.castAdd q k) = P i k := fun i k => by
    have e := (hfst (Fin.castAdd q i)).symm.trans ((h1' i).trans (hP i))
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at e
    simp only [← sub_smul] at e
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hv _ e k)
  have h21 : ∀ j k, M (Fin.natAdd p j) (Fin.castAdd q k) = 0 := fun j k => by
    have e := (hfst (Fin.natAdd p j)).symm.trans (h2' j).1
    exact Fintype.linearIndependent_iff.1 hv _ e k
  have hsnd : ∀ j, (u' (Fin.natAdd p j)).2 =
      ∑ l : Fin q, M (Fin.natAdd p j) (Fin.natAdd p l) • (u (Fin.natAdd p l)).2 := fun j => by
    rw [← hB (Fin.natAdd p j), Prod.snd_sum, Fin.sum_univ_add]
    simp only [← hMB, Prod.smul_snd, h21, zero_smul, Prod.snd_zero, Finset.sum_const_zero, _root_.zero_add]
  let D : Matrix (Fin q) (Fin q) K := fun j l => M (Fin.natAdd p j) (Fin.natAdd p l)
  have hDQ : D * Q.transpose = 1 := by
    ext j j'
    have e := (h2' j).2 j'
    rw [hsnd j, hQ j'] at e

    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, (h2 _).2, smul_eq_mul] at e
    simp only [mul_ite, _root_.mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true] at e
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.transpose_apply]
    rw [← e]
    exact Finset.sum_congr rfl fun _ _ => _root_.mul_comm _ _
  have hdet : M.det = P.det * D.det := det_eq_det_mul_det_of_block M P D h11 h21 fun _ _ => rfl
  have hDQd : D.det * Q.det = 1 := by
    rw [← Matrix.det_transpose Q, ← Matrix.det_mul, hDQ, Matrix.det_one]
  rw [hdet, _root_.mul_assoc, hDQd, _root_.mul_one]

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
end
