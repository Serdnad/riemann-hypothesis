module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

noncomputable section

namespace GlobalTheory.SectionsCommRing

variable {R : Type u} [CommRing R] {X : Scheme.{u}}

def structureHom (s : X ⟶ Spec (CommRingCat.of R)) (U : X.Opens) : R →+* Γ(X, U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ s.appTop ≫
    X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom

theorem map_structureHom (s : X ⟶ Spec (CommRingCat.of R)) {U V : X.Opens} (h : V ≤ U) (r : R) :
    (X.presheaf.map (homOfLE h).op).hom (structureHom s U r) = structureHom s V r := by
  show ((X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ X.presheaf.map (homOfLE h).op).hom
    (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))) = _
  rw [← X.presheaf.map_comp]
  rfl

def Sections (_s : X ⟶ Spec (CommRingCat.of R)) (U : X.Opens) : Type u := Γ(X, U)

namespace Sections

variable (s : X ⟶ Spec (CommRingCat.of R))

instance (U : X.Opens) : CommRing (Sections s U) := inferInstanceAs (CommRing Γ(X, U))

instance (U : X.Opens) : Algebra R (Sections s U) :=
  RingHom.toAlgebra (R := R) (S := Sections s U) (structureHom s U)

def restrict {U V : X.Opens} (h : V ≤ U) : Sections s U →ₐ[R] Sections s V where
  toRingHom := (X.presheaf.map (homOfLE h).op).hom
  commutes' r := map_structureHom s h r

end Sections

end GlobalTheory.SectionsCommRing
end
end

section

open MeasureTheory

namespace GlobalTheory.IntegralAgainstMeasure

variable {K B : Type*} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K]
  [OpensMeasurableSpace K] [NormedAddCommGroup B] [NormedSpace ℂ B]

theorem integrable_smul (μ : Measure K) [IsFiniteMeasure μ] (p : C(K, B)) (f : C(K, ℂ)) :
    Integrable (fun k => f k • p k) μ :=
  (f.continuous.smul p.continuous).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

noncomputable def integralAgainstLinear (μ : Measure K) [IsFiniteMeasure μ] (p : C(K, B)) :
    C(K, ℂ) →ₗ[ℂ] B where
  toFun f := ∫ k, f k • p k ∂μ
  map_add' f g := by
    simp only [ContinuousMap.add_apply, add_smul]
    exact integral_add (integrable_smul μ p f) (integrable_smul μ p g)
  map_smul' c f := by
    simp only [ContinuousMap.smul_apply, smul_assoc, RingHom.id_apply]
    exact integral_smul c _

theorem norm_integral_smul_le (μ : Measure K) [IsFiniteMeasure μ] (p : C(K, B)) (f : C(K, ℂ)) :
    ‖∫ k, f k • p k ∂μ‖ ≤ (μ.real Set.univ * ‖p‖) * ‖f‖ := by
  have h : ∀ᵐ k ∂μ, ‖f k • p k‖ ≤ ‖p‖ * ‖f‖ := Filter.Eventually.of_forall fun k => by
    rw [norm_smul, mul_comm]
    exact mul_le_mul (p.norm_coe_le_norm k) (f.norm_coe_le_norm k) (norm_nonneg _) (norm_nonneg _)
  calc ‖∫ k, f k • p k ∂μ‖ ≤ ‖p‖ * ‖f‖ * μ.real Set.univ := norm_integral_le_of_norm_le_const h
    _ = (μ.real Set.univ * ‖p‖) * ‖f‖ := by ring

noncomputable def integralAgainst (μ : Measure K) [IsFiniteMeasure μ] (p : C(K, B)) :
    C(K, ℂ) →L[ℂ] B :=
  (integralAgainstLinear μ p).mkContinuous (μ.real Set.univ * ‖p‖) (norm_integral_smul_le μ p)

end GlobalTheory.IntegralAgainstMeasure
end

section

namespace GlobalTheory.InnerAutomorphism

section Inner

variable {A : Type*} (R : Type*) [CommSemiring R] [Semiring A] [Algebra R A]

def innerAut (u : Aˣ) : A ≃ₐ[R] A where
  toFun x := (u : A) * x * ((u⁻¹ : Aˣ) : A)
  invFun x := ((u⁻¹ : Aˣ) : A) * x * (u : A)
  left_inv x := by simp [mul_assoc]
  right_inv x := by simp [mul_assoc]
  map_mul' x y := by simp [mul_assoc]
  map_add' x y := by simp [mul_add, add_mul]
  commutes' r := by rw [← Algebra.commutes, mul_assoc, Units.mul_inv, mul_one]

end Inner

section Bounded

variable {K n : Type*} [NormedField K]

def EntriesBounded (M : Matrix n n K) (c : ℝ) : Prop :=
  ∀ i j, ‖M i j‖ ≤ c

end Bounded

section DropLast

variable (K : Type*) [Semiring K] (d : ℕ)

def dropLast : (Fin (d + 1) → K) →ₗ[K] (Fin d → K) where
  toFun x i := x i.castSucc
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end DropLast

section Split

variable {ι : Type*} [DecidableEq ι] (F : ι → Type*)

def sigmaSplit (j : ι) : (Σ i, F i) ≃ F j ⊕ (Σ i : {i // i ≠ j}, F i.1) where
  toFun p := if h : p.1 = j then Sum.inl (h ▸ p.2) else Sum.inr ⟨⟨p.1, h⟩, p.2⟩
  invFun s := Sum.elim (fun x => ⟨j, x⟩) (fun q => ⟨q.1.1, q.2⟩) s
  left_inv := by
    rintro ⟨i, x⟩
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  right_inv := by
    rintro (x | ⟨⟨i, hi⟩, x⟩)
    · simp
    · simp [show ¬ i = j from hi]

theorem sigmaSplit_self (j : ι) (x : F j) : sigmaSplit F j ⟨j, x⟩ = Sum.inl x :=
  (Equiv.apply_eq_iff_eq_symm_apply _).2 rfl

theorem sigmaSplit_of_ne {i j : ι} (h : i ≠ j) (x : F i) :
    sigmaSplit F j ⟨i, x⟩ = Sum.inr ⟨⟨i, h⟩, x⟩ :=
  (Equiv.apply_eq_iff_eq_symm_apply _).2 rfl

end Split

end GlobalTheory.InnerAutomorphism
end

section

namespace GlobalTheory.BoundedPowerSeriesDisc

open PowerSeries

section General

variable {K : Type*} [NormedField K]

theorem summable_norm_of_bounded {a : ℕ → K} {B : ℝ} (ha : ∀ n, ‖a n‖ ≤ B) {t : K}
    (ht : ‖t‖ < 1) : Summable fun n => ‖a n * t ^ n‖ := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    ((summable_geometric_of_lt_one (norm_nonneg t) ht).mul_left B)
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_right (ha n) (pow_nonneg (norm_nonneg t) n)

theorem tsum_coeff_mul [CompleteSpace K] (f g : K⟦X⟧) (t : K)
    (hf : Summable fun n => ‖coeff n f * t ^ n‖) (hg : Summable fun n => ‖coeff n g * t ^ n‖) :
    ∑' n, coeff n (f * g) * t ^ n = (∑' n, coeff n f * t ^ n) * ∑' n, coeff n g * t ^ n := by
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg]
  refine tsum_congr fun n => ?_
  rw [coeff_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  obtain rfl : p.1 + p.2 = n := by simpa using hp
  rw [pow_add]
  ring

theorem tsum_coeff_C (c t : K) : ∑' n, coeff n (C c : K⟦X⟧) * t ^ n = c := by
  rw [tsum_eq_single 0]
  · simp
  · intro n hn
    simp [coeff_C, hn]

end General

section Integral

variable {O : Type*} [Semiring O] {K : Type*} [NormedField K] [CompleteSpace K]

noncomputable def evalDisc (i : O →+* K) (hi : ∀ a, ‖i a‖ ≤ 1) (t : K) (ht : ‖t‖ < 1) :
    O⟦X⟧ →+* K where
  toFun f := ∑' n, i (coeff n f) * t ^ n
  map_one' := by
    have := tsum_coeff_C (1 : K) t
    rw [map_one, ← map_one (PowerSeries.map i)] at this
    simpa only [coeff_map] using this
  map_mul' f g := by
    have := tsum_coeff_mul (PowerSeries.map i f) (PowerSeries.map i g) t
      (by simpa only [coeff_map] using summable_norm_of_bounded (fun n => hi (coeff n f)) ht)
      (by simpa only [coeff_map] using summable_norm_of_bounded (fun n => hi (coeff n g)) ht)
    rw [← map_mul] at this
    simpa only [coeff_map] using this
  map_zero' := by simp
  map_add' f g := by
    rw [← (summable_norm_of_bounded (fun n => hi (coeff n f)) ht).of_norm.tsum_add
      (summable_norm_of_bounded (fun n => hi (coeff n g)) ht).of_norm]
    simp only [map_add (f := _), add_mul]

variable (i : O →+* K) (hi : ∀ a, ‖i a‖ ≤ 1) (t : K) (ht : ‖t‖ < 1)

end Integral

section Bounded

def boundedSeries (F : Type*) [NormedField F] [IsUltrametricDist F] : Subring F⟦X⟧ where
  carrier := {f | ∃ B : ℝ, ∀ n, ‖coeff n f‖ ≤ B}
  mul_mem' := by
    rintro f g ⟨A, hA⟩ ⟨B, hB⟩
    have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
    refine ⟨A * B, fun n => ?_⟩
    rw [coeff_mul]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hA0 hB0)
      fun p _ => ?_
    rw [norm_mul]
    exact mul_le_mul (hA _) (hB _) (norm_nonneg _) hA0
  one_mem' := ⟨1, fun n => by rw [coeff_one]; split_ifs <;> simp⟩
  add_mem' := by
    rintro f g ⟨A, hA⟩ ⟨B, hB⟩
    refine ⟨A + B, fun n => ?_⟩
    rw [map_add (f := _)]
    exact (norm_add_le _ _).trans (add_le_add (hA n) (hB n))
  zero_mem' := ⟨0, fun n => by simp⟩
  neg_mem' := by
    rintro f ⟨A, hA⟩
    exact ⟨A, fun n => by simpa using hA n⟩

variable {F : Type*} [NormedField F] [IsUltrametricDist F]

theorem mem_boundedSeries {f : F⟦X⟧} :
    f ∈ boundedSeries F ↔ ∃ B : ℝ, ∀ n, ‖coeff n f‖ ≤ B := by exact Iff.rfl

theorem summable_norm_boundedSeries (f : boundedSeries F) {π : F} (hπ : ‖π‖ < 1) :
    Summable fun n => ‖coeff n (f : F⟦X⟧) * π ^ n‖ := by
  obtain ⟨B, hB⟩ := mem_boundedSeries.1 f.2
  exact summable_norm_of_bounded hB hπ

variable [CompleteSpace F]

noncomputable def evalBounded (π : F) (hπ : ‖π‖ < 1) : boundedSeries F →+* F where
  toFun f := ∑' n, coeff n (f : F⟦X⟧) * π ^ n
  map_one' := by simpa only [map_one, OneMemClass.coe_one] using tsum_coeff_C (1 : F) π
  map_mul' f g := tsum_coeff_mul (f : F⟦X⟧) g π (summable_norm_boundedSeries f hπ)
    (summable_norm_boundedSeries g hπ)
  map_zero' := by simp
  map_add' f g := by
    rw [← (summable_norm_boundedSeries f hπ).of_norm.tsum_add
      (summable_norm_boundedSeries g hπ).of_norm]
    simp only [Subring.coe_add, map_add (f := _), add_mul]

variable (π : F) (hπ : ‖π‖ < 1)

end Bounded

end GlobalTheory.BoundedPowerSeriesDisc
end

section

namespace GlobalTheory.ClosedBallValuationSubring

variable (K : Type*) [NormedField K] [IsUltrametricDist K]

def closedBallSubring : Subring K where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [norm_mul]
    exact mul_le_one₀ ha (norm_nonneg b) hb
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' := by
    intro a ha
    simpa using ha

def closedBallValuationSubring : ValuationSubring K where
  toSubring := closedBallSubring K
  mem_or_inv_mem' := by
    intro x
    change ‖x‖ ≤ 1 ∨ ‖x⁻¹‖ ≤ 1
    rcases le_total ‖x‖ 1 with h | h
    · exact Or.inl h
    · right
      rw [norm_inv]
      exact inv_le_one_of_one_le₀ h

def openBallIdeal : Ideal (closedBallSubring K) where
  carrier := {x | ‖(x : K)‖ < 1}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    exact (IsUltrametricDist.norm_add_le_max (a : K) (b : K)).trans_lt (max_lt ha hb)
  zero_mem' := by simp
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    have hc : ‖(c : K)‖ ≤ 1 := c.2
    change ‖(c : K) * (x : K)‖ < 1
    rw [norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right hc (norm_nonneg _) hx

variable {K}

theorem mem_closedBallSubring {x : K} : x ∈ closedBallSubring K ↔ ‖x‖ ≤ 1 := Iff.rfl

theorem mem_openBallIdeal {x : closedBallSubring K} :
    x ∈ openBallIdeal K ↔ ‖(x : K)‖ < 1 := Iff.rfl

theorem isUnit_iff_norm_eq_one {x : closedBallSubring K} : IsUnit x ↔ ‖(x : K)‖ = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    have hu : ‖((u : closedBallSubring K) : K)‖ ≤ 1 := (u : closedBallSubring K).2
    have hv : ‖((u⁻¹ : (closedBallSubring K)ˣ) : closedBallSubring K).1‖ ≤ 1 :=
      ((u⁻¹ : (closedBallSubring K)ˣ) : closedBallSubring K).2
    have hprod : ‖((u : closedBallSubring K) : K)‖ *
        ‖((u⁻¹ : (closedBallSubring K)ˣ) : closedBallSubring K).1‖ = 1 := by
      rw [← norm_mul]
      have h := congrArg Subtype.val u.mul_inv
      simp only [Subring.coe_mul, Subring.coe_one] at h
      rw [h, norm_one]
    refine le_antisymm hu ?_
    calc (1 : ℝ) = _ := hprod.symm
      _ ≤ ‖((u : closedBallSubring K) : K)‖ * 1 :=
          mul_le_mul_of_nonneg_left hv (norm_nonneg _)
      _ = _ := mul_one _
  · intro h
    have hx0 : (x : K) ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at h
      exact zero_ne_one h
    have hinv : (x : K)⁻¹ ∈ closedBallSubring K := by
      rw [mem_closedBallSubring, norm_inv, h, inv_one]
    refine isUnit_iff_exists_inv.mpr ⟨⟨(x : K)⁻¹, hinv⟩, ?_⟩
    apply Subtype.ext
    simp only [Subring.coe_mul, Subring.coe_one]
    exact mul_inv_cancel₀ hx0

theorem mem_openBallIdeal_iff_not_isUnit {x : closedBallSubring K} :
    x ∈ openBallIdeal K ↔ ¬ IsUnit x := by
  rw [mem_openBallIdeal, isUnit_iff_norm_eq_one]
  have hle : ‖(x : K)‖ ≤ 1 := mem_closedBallSubring.mp x.2
  exact ⟨fun h he => (ne_of_lt h) he, fun h => lt_of_le_of_ne hle h⟩

variable (K)

instance isLocalRing_closedBallSubring : IsLocalRing (closedBallSubring K) :=
  inferInstanceAs (IsLocalRing (closedBallValuationSubring K))

theorem openBallIdeal_eq_maximalIdeal :
    openBallIdeal K = IsLocalRing.maximalIdeal (closedBallSubring K) := by
  ext x
  rw [mem_openBallIdeal_iff_not_isUnit, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]

theorem openBallIdeal_isMaximal : (openBallIdeal K).IsMaximal := by
  rw [openBallIdeal_eq_maximalIdeal]
  exact IsLocalRing.maximalIdeal.isMaximal _

end GlobalTheory.ClosedBallValuationSubring
end

section

namespace GlobalTheory.RootCharacter

open scoped BigOperators

variable {B : Type*} [CommMonoid B] {I : Type*} [Fintype I] {n : ℕ} [NeZero n]

theorem pow_val_add {x : B} (hx : x ^ n = 1) (a b : ZMod n) :
    x ^ (a + b).val = x ^ a.val * x ^ b.val := by
  rw [ZMod.val_add, ← pow_add, ← pow_eq_pow_mod _ hx]

def rootChar (u : I → B) (hu : ∀ q, u q ^ n = 1) : Multiplicative (I → ZMod n) →* B where
  toFun a := ∏ q, u q ^ (Multiplicative.toAdd a q).val
  map_one' := by simp
  map_mul' a b := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun q _ => pow_val_add (hu q) _ _

end GlobalTheory.RootCharacter
end

section

universe u_1 u_2

namespace GlobalTheory.AdditiveValuationProduct

theorem addVal_prod : ∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsDomain R] [inst_2 : IsDiscreteValuationRing R] {ι : Type u_2} (s : Finset ι) (a : ι → R), (IsDiscreteValuationRing.addVal R : R → ℕ∞) (∏ i ∈ s, a i) = ∑ i ∈ s, (IsDiscreteValuationRing.addVal R : R → ℕ∞) (a i) := by
  intro R _ _ _ ι s a
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j t hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj, AddValuation.map_mul, ih]

end GlobalTheory.AdditiveValuationProduct
end
