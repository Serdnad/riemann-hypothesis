module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle025
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle027
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle030
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle035
public import GroundTheory.HeightsAndTheta.Heights.Intersections.LeOfHeightMapEqZero
public import GroundTheory.HeightsAndTheta.Heights.Intersections.NotIsUnitOfNumMem
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle011
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle010
import GroundTheory.HeightsAndTheta.Heights.Intersections.LogCardLocIdealUnitMul
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle032
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle042
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle014
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace RegularityRelativeClosedPoint

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] [DecidableEq K]

def killBlocks (S : Finset K) : MRing ι →ₐ[ℤ] MRing ι :=
  aeval fun p => if p.1 ∈ S then 0 else X p

theorem killBlocks_form (S : Finset K) {g : MRing ι} {a : K → ℕ} (hg : IsMultiHomog g a) :
    killBlocks S g = (∏ k, (if k ∈ S then (0 : MRing ι) else 1) ^ a k) * g := by
  have e : (fun p : (Σ k, ι k) => if p.1 ∈ S then (0 : MRing ι) else X p) =
      fun p => (if p.1 ∈ S then (0 : MRing ι) else 1) * X p := by
    funext p
    split_ifs <;> simp
  have h := regularityLocalResidue_holds.aeval_blockScale_int hg (fun k => if k ∈ S then (0 : MRing ι) else 1) X
  rw [aeval_X_left_apply] at h
  rw [killBlocks, e]
  exact h

theorem le_comap_killBlocks (S : Finset K) {W : Ideal (MRing ι)} (hW : IsMultiHomogIdeal W) :
    W ≤ W.comap (killBlocks S) := by
  obtain ⟨T, hT, rfl⟩ := hW
  rw [Ideal.span_le]
  intro g hg
  obtain ⟨a, ha⟩ := hT g hg
  rw [SetLike.mem_coe, Ideal.mem_comap, killBlocks_form S ha]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span hg)


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem killBlocks_comp {S T : Finset K} (hST : S ⊆ T) :
    (killBlocks T).comp (killBlocks S) = (killBlocks T : MRing ι →ₐ[ℤ] MRing ι) := by
  refine MvPolynomial.algHom_ext fun p => ?_
  simp only [AlgHom.comp_apply, killBlocks, aeval_X]
  by_cases h : p.1 ∈ S
  · simp [h, hST h]
  · simp [h]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem killBlocks_empty : (killBlocks ∅ : MRing ι →ₐ[ℤ] MRing ι) = AlgHom.id ℤ (MRing ι) :=
  MvPolynomial.algHom_ext fun p => by simp [killBlocks]

theorem card_le_ringKrullDim (W : Ideal (MRing ι)) [W.IsPrime] (hWh : IsMultiHomogIdeal W)
    (hWr : IsRelevant W) : ((Fintype.card K : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MRing ι ⧸ W) := by
  choose j hj using hWr
  let Q : Finset K → Ideal (MRing ι) := fun S => W.comap (killBlocks S)
  have hQp : ∀ S, (Q S).IsPrime := fun S => Ideal.comap_isPrime _ _
  have hstep : ∀ S k, k ∉ S → Q S < Q (insert k S) := by
    intro S k hk
    refine SetLike.lt_iff_le_and_exists.mpr ⟨fun g hg => ?_, X ⟨k, j k⟩, ?_, ?_⟩
    · have h1 := Ideal.mem_comap.mp (le_comap_killBlocks (insert k S) hWh (Ideal.mem_comap.mp hg))
      rw [← AlgHom.comp_apply, killBlocks_comp (Finset.subset_insert k S)] at h1
      exact Ideal.mem_comap.mpr h1
    · rw [Ideal.mem_comap]
      simp [killBlocks]
    · intro h
      rw [Ideal.mem_comap] at h
      simp only [killBlocks, aeval_X, if_neg hk] at h
      exact hj k h
  have chain : ∀ S : Finset K, (S.card : WithBot ℕ∞) + ringKrullDim (MRing ι ⧸ Q S) ≤
      ringKrullDim (MRing ι ⧸ Q ∅) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | @insert k S hk ih =>
      have : (Q S).IsPrime := hQp S
      have : (Q (insert k S)).IsPrime := hQp _
      have h1 := HorizNotMem.ringKrullDim_quotient_add_one_le (hstep S k hk)
      rw [Finset.card_insert_of_notMem hk]
      calc (((S.card + 1 : ℕ)) : WithBot ℕ∞) + ringKrullDim (MRing ι ⧸ Q (insert k S))
          = (S.card : WithBot ℕ∞) + (ringKrullDim (MRing ι ⧸ Q (insert k S)) + 1) := by
            push_cast; abel
        _ ≤ (S.card : WithBot ℕ∞) + ringKrullDim (MRing ι ⧸ Q S) := by gcongr
        _ ≤ _ := ih
  have hQ0 : Q ∅ = W := by
    ext g
    simp [Q, killBlocks_empty]
  have : (Q Finset.univ).IsPrime := hQp _
  have : IsDomain (MRing ι ⧸ Q Finset.univ) := Ideal.Quotient.isDomain _
  have h3 : (0 : WithBot ℕ∞) ≤ ringKrullDim (MRing ι ⧸ Q Finset.univ) := ringKrullDim_nonneg_of_nontrivial
  have hc := chain Finset.univ
  rw [Finset.card_univ, hQ0] at hc
  calc ((Fintype.card K : ℕ) : WithBot ℕ∞) = (Fintype.card K : WithBot ℕ∞) + 0 := (add_zero _).symm
    _ ≤ (Fintype.card K : WithBot ℕ∞) + ringKrullDim (MRing ι ⧸ Q Finset.univ) := by gcongr
    _ ≤ _ := hc

end RegularityRelativeClosedPoint

theorem RegularityRelativeClosedPoint.proof : RegularityRelativeClosedPoint.Statement := by
  intro K _ ι _ P W hP hW hPW hne
  classical
  refine ⟨hW, ?_⟩
  obtain ⟨-, ⟨hPp, -, -⟩, -, hPdim⟩ := hP
  obtain ⟨hWp, hWh, hWr⟩ := hW
  have := hPp
  have := hWp
  have e := mvPolynomialInt_dimFormula P W hPW
  rw [hPdim] at e
  have hh : (W.map (Ideal.Quotient.mk P)).height ≠ 0 := fun h0 =>
    hne (le_antisymm (RegularityDivisorSupportClosed.le_of_height_map_eq_zero h0) hPW)
  have hlow := RegularityRelativeClosedPoint.card_le_ringKrullDim W hWh hWr
  generalize ringKrullDim (MRing ι ⧸ W) = m at e hlow ⊢
  generalize (W.map (Ideal.Quotient.mk P)).height = h at e hh
  induction m using WithBot.recBotCoe with
  | bot => exact absurd hlow (by simp)
  | coe m =>
    have e' : m + h = ((1 + Fintype.card K : ℕ) : ℕ∞) := by exact_mod_cast e
    have hlow' : ((Fintype.card K : ℕ) : ℕ∞) ≤ m := by exact_mod_cast hlow
    induction m using ENat.recTopCoe with
    | top => simp at e'; exact absurd e'.symm (ENat.natCast_ne_top _)
    | coe m =>
      induction h using ENat.recTopCoe with
      | top => simp at e'; exact absurd e'.symm (ENat.natCast_ne_top _)
      | coe h =>
        have h1 : m + h = 1 + Fintype.card K := by exact_mod_cast e'
        have h2 : Fintype.card K ≤ m := by exact_mod_cast hlow'
        have h3 : h ≠ 0 := by exact_mod_cast hh
        have h4 : m = Fintype.card K := by omega
        rw [h4]
        rfl

end

end GroundTheory.Heights₂.Heights.Inter
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem regRing_intCast_coe (P : Ideal (MRing ι)) (n : ℤ) :
    (((n : regRing P) : funField P) : FractionRing (MRing ι ⧸ P)) =
      algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P (C n)) := by
  rw [eq_intCast C n, map_intCast, map_intCast]
  simp

theorem funField_exists_inv {P : Ideal (MRing ι)} [hPp : P.IsPrime] (y : funField P)
    (hy : (y : FractionRing (MRing ι ⧸ P)) ≠ 0) :
    ∃ x : funField P, (x : FractionRing (MRing ι ⧸ P)) * (y : FractionRing (MRing ι ⧸ P)) = 1 := by
  have hφ : ∀ s, s ∉ P → algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P s) ≠ 0 :=
    fun s hs => by rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]; exact hs
  have hFL : (y : FractionRing (MRing ι ⧸ P)) ∈ locRing P P := by
    have hx := y.2
    unfold funField at hx
    unfold locRing
    refine Subring.closure_mono ?_ hx
    rintro _ ⟨u, v, a, hv, hu, hva, rfl⟩
    refine ⟨u, v, a, hv, fun h => ?_, hu, hva, rfl⟩
    have h0 : Ideal.Quotient.mk P v = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr h
    exact zero_notMem_nonZeroDivisors (h0 ▸ hv)
  obtain ⟨u, v, a, hu, hv, hvP, huv⟩ := LocRingFrac.proof K ι P P hPp hPp le_rfl _ hFL
  have huP : u ∉ P := fun h => by
    have h0 : algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr h, map_zero]
    rw [← huv] at h0
    exact mul_ne_zero hy (hφ v hvP) h0
  obtain ⟨x, hx⟩ := exists_funField_mul_eq hv hu huP
  refine ⟨x, mul_right_cancel₀ (hφ v hvP) ?_⟩
  rw [mul_assoc, huv, hx, one_mul]

theorem regRing_exists_coe {P : Ideal (MRing ι)} {y : funField P} (hy : y ∈ regRing P) :
    ∃ b : regRing P, (b : funField P) = y :=
  ⟨⟨y, hy⟩, rfl⟩

theorem RegularityMaximalSurjective.proof (h₁ : RegularityOrder.Statement) (h₂ : RegularityLocalPrime.Statement) : RegularityMaximalSurjective.Statement := by
  classical
  intro K _ ι _ P hP m hm
  have hPp : P.IsPrime := hP.2.1.1
  have hL : LocRingLocal.Statement := LocRingLocal.proof LocRingFrac.proof

  have hmZ : (m.comap (algebraMap ℤ (regRing P))).IsMaximal := by
    have : Module.Finite ℤ (regRing P) := (h₁ K ι P hP).2.1
    have : Algebra.IsIntegral ℤ (regRing P) := Algebra.IsIntegral.of_finite ℤ _
    exact Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := ℤ) m
  have hp := Submodule.IsPrincipal.prime_generator_of_isPrime (is_prime := hmZ.isPrime) _
    (Ring.ne_bot_of_isMaximal_of_not_isField hmZ Int.not_isField)
  set p := Submodule.IsPrincipal.generator (m.comap (algebraMap ℤ (regRing P)))
  have hZ : ∀ n : ℤ, (n : regRing P) ∈ m ↔ p ∣ n := fun n => by
    rw [← Submodule.IsPrincipal.mem_iff_generator_dvd, Ideal.mem_comap, algebraMap_int_eq, eq_intCast]
  have hCp : C p ∉ P := fun h => by
    have h' : p ∈ P.comap (C : ℤ →+* MRing ι) := h
    rw [hP.2.2.1] at h'
    exact hp.ne_zero (Ideal.mem_bot.mp h')
  have hp0 : (p : regRing P) ≠ 0 := fun h => by
    have h' := regRing_intCast_coe P p
    rw [h, ZeroMemClass.coe_zero, ZeroMemClass.coe_zero, eq_comm, IsFractionRing.to_map_eq_zero_iff,
      Ideal.Quotient.eq_zero_iff_mem] at h'
    exact hCp h'

  have hS : {W | IsClosedPt W ∧ P ≤ W ∧ C p ∈ W}.Finite :=
    (divSupp_finite P (C p)).subset fun W hW =>
      (RegularityDivisorSupportClosed.proof K ι P (C p) 0 W hP (RegularityDenominator.isMultiHomog_C p) hCp).2 hW
  let g : Ideal (MRing ι) → Ideal (regRing P) := fun W =>
    if h : IsClosedPt W ∧ P ≤ W then regMaxAt P W h.1 h.2 (hL K ι P W hPp h.1.1.1 h.2).1 else ⊥
  have hgW : ∀ W (h : IsClosedPt W ∧ P ≤ W), g W = regMaxAt P W h.1 h.2 (hL K ι P W hPp h.1.1.1 h.2).1 :=
    fun W h => dif_pos h
  by_contra hcon
  push Not at hcon

  let T : Finset (Ideal (regRing P)) := insert ⊥ (hS.toFinset.image g)
  have hT : ¬ ((m : Set (regRing P)) ⊆ ⋃ i ∈ (↑T : Set (Ideal (regRing P))), ((fun i => i) i : Set (regRing P))) := by
    rw [Ideal.subset_union_prime (f := fun i : Ideal (regRing P) => i) ⊥ ⊥ fun i hi h1 _ => ?_]
    · rintro ⟨i, hi, hle⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact hp0 (Ideal.mem_bot.1 (hle ((hZ p).2 dvd_rfl)))
      · obtain ⟨W, hW, rfl⟩ := Finset.mem_image.1 hi
        obtain ⟨hWc, hPW, -⟩ := hS.mem_toFinset.1 hW
        obtain ⟨x, hx, z, hz, hxz⟩ := hcon W hWc hPW
        have h' := hle hx
        rw [hgW W ⟨hWc, hPW⟩] at h'
        exact (not_mem_regMaxAt_iff hWc hPW _ x).2 ⟨z, hz, hxz⟩ h'
    · rcases Finset.mem_insert.1 hi with rfl | hi
      · exact absurd rfl h1
      · obtain ⟨W, hW, rfl⟩ := Finset.mem_image.1 hi
        obtain ⟨hWc, hPW, -⟩ := hS.mem_toFinset.1 hW
        rw [hgW W ⟨hWc, hPW⟩]
        exact (regMaxAt_isMaximal h₁ hL hP hWc hPW _).isPrime
  obtain ⟨a, ham, ha⟩ := Set.not_subset.1 hT
  simp only [Set.mem_iUnion, SetLike.mem_coe, not_exists] at ha
  have ha0 : ((a : funField P) : FractionRing (MRing ι ⧸ P)) ≠ 0 := fun h =>
    ha ⊥ (Finset.mem_insert_self _ _) (Ideal.mem_bot.2 (Subtype.ext (Subtype.ext (by rw [h, ZeroMemClass.coe_zero, ZeroMemClass.coe_zero]))))

  obtain ⟨x, hxa⟩ := funField_exists_inv (a : funField P) ha0
  obtain ⟨n, hpn, hn⟩ := h₂ K ι P p x hP hp fun W hWc hPW hpW => by
    have h' := ha (g W) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem g (hS.mem_toFinset.2 ⟨hWc, hPW, hpW⟩)))
    rw [hgW W ⟨hWc, hPW⟩] at h'
    obtain ⟨z, hz, haz⟩ := (not_mem_regMaxAt_iff hWc hPW _ a).1 h'
    rwa [show (x : FractionRing (MRing ι ⧸ P)) = z by rw [← mul_one (x : FractionRing (MRing ι ⧸ P)), ← haz,
      ← mul_assoc, hxa, one_mul]]

  refine hpn ((hZ n).1 ?_)
  obtain ⟨b, hb⟩ := regRing_exists_coe hn
  have he : a * b = (n : regRing P) := by
    apply Subtype.ext
    apply Subtype.ext
    rw [Subring.coe_mul, Subring.coe_mul, hb, Subring.coe_mul, Subring.coe_intCast, Subring.coe_intCast,
      Subring.coe_intCast]
    rw [mul_left_comm, mul_comm ((a : funField P) : FractionRing (MRing ι ⧸ P)), hxa, mul_one]
  rw [← he]
  exact m.mul_mem_right b ham

end

end GroundTheory.Heights₂.Heights.Inter
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem RegularityLocalPrime.proof (h₁ : RegularityOrder.Statement) : RegularityLocalPrime.Statement := by
  intro K _ ι _ P p y hP hp hy
  have hPp : P.IsPrime := hP.2.1.1
  obtain ⟨c, hc0, hc⟩ := RegularityDenominator.proof RegularityDivisorSupportClosed.proof LocRingPow.proof K ι P y hP
  have hcR : c ∈ regRing P := fun W h1 h2 => (hc W h1 h2).1
  have : Module.Finite ℤ (regRing P) := (h₁ K ι P hP).2.1
  have hci : IsIntegral ℤ (⟨c, hcR⟩ : regRing P) := Algebra.IsIntegral.isIntegral _
  have hne := Ideal.comap_ne_bot_of_integral_mem (I := Ideal.span {(⟨c, hcR⟩ : regRing P)})
    (fun h => hc0 (congrArg Subtype.val h)) (Ideal.mem_span_singleton_self _) hci
  obtain ⟨N, hN, hN0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 (Ideal.mem_comap.1 hN)
  have hNF : ((N : funField P) : FractionRing (MRing ι ⧸ P)) =
      ((d : funField P) : FractionRing (MRing ι ⧸ P)) * (c : FractionRing (MRing ι ⧸ P)) := by
    have h := congrArg (fun z : regRing P => ((z : funField P) : FractionRing (MRing ι ⧸ P))) hd
    simp only [Subring.coe_mul, algebraMap_int_eq, eq_intCast, SubringClass.coe_intCast] at h
    simp only [SubringClass.coe_intCast]
    exact h.symm
  have hpu : p.natAbs ≠ 1 := fun h => hp.not_isUnit (Int.isUnit_iff_natAbs_eq.mpr h)
  obtain ⟨m, hNm, hpm⟩ := (Int.finiteMultiplicity_iff.mpr ⟨hpu, hN0⟩).exists_eq_pow_mul_and_not_dvd
  generalize multiplicity p N = e at hNm
  refine ⟨m, hpm, fun W h1 h2 => ?_⟩
  rw [Subring.coe_mul, SubringClass.coe_intCast]
  by_cases hpW : C p ∈ W
  · exact mul_mem (intCast_mem _ m) (hy W h1 h2 hpW)
  have hCp : algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P (C p)) = (p : _) := by
    rw [eq_intCast C p, map_intCast, map_intCast]
  have hp0 : (p : FractionRing (MRing ι ⧸ P)) ≠ 0 := by
    intro h
    apply hpW
    apply h2
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← IsFractionRing.to_map_eq_zero_iff (K := FractionRing (MRing ι ⧸ P)),
      hCp, h]
  have hq : (p : FractionRing (MRing ι ⧸ P))⁻¹ ∈ locRing P W :=
    frac_mem_locRing h2 (RegularityDenominator.isMultiHomog_C 1) (RegularityDenominator.isMultiHomog_C p) hpW
      (by rw [hCp, map_one, map_one, map_one, inv_mul_cancel₀ hp0])
  have hyc : (y : FractionRing (MRing ι ⧸ P)) * (c : FractionRing (MRing ι ⧸ P)) ∈ locRing P W := by
    have := (hc W h1 h2).2
    rwa [Subring.coe_mul] at this
  have hdW : ((d : funField P) : FractionRing (MRing ι ⧸ P)) ∈ locRing P W := d.2 W h1 h2
  have key : (m : FractionRing (MRing ι ⧸ P)) * (y : FractionRing (MRing ι ⧸ P)) =
      (p : FractionRing (MRing ι ⧸ P))⁻¹ ^ e *
        (((d : funField P) : FractionRing (MRing ι ⧸ P)) * ((y : FractionRing (MRing ι ⧸ P)) * c)) := by
    have hN' : ((d : funField P) : FractionRing (MRing ι ⧸ P)) * ((y : FractionRing (MRing ι ⧸ P)) * c) =
        (p : FractionRing (MRing ι ⧸ P)) ^ e * m * y := by
      rw [show ((d : funField P) : FractionRing (MRing ι ⧸ P)) * ((y : FractionRing (MRing ι ⧸ P)) * c) =
        ((N : funField P) : FractionRing (MRing ι ⧸ P)) * y by rw [hNF]; ring, SubringClass.coe_intCast,
        hNm, Int.cast_mul, Int.cast_pow]
    rw [hN', inv_pow, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hp0), one_mul]
  rw [key]
  exact mul_mem (pow_mem hq _) (mul_mem hdW hyc)

end

end GroundTheory.Heights₂.Heights.Inter
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

theorem SemilocIntegral.proof (h₁ : ValCentreZ.Statement) (h₂ : CentreOverW.Statement) :
    SemilocIntegral.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n s α W hv hP' hP hs hsP hW
  have := hP'.2.1.1
  letI := (locToSemiloc hv P' W).toAlgebra
  let f : locRing (imageZ v P') W →+* FractionRing (MRing ι' ⧸ P') :=
    (semiLocRing P' (fibreOver v P' W)).subtype.comp (locToSemiloc hv P' W)
  refine ⟨fun b => ?_⟩
  refine RingHom.IsIntegralElem.of_map (g := (semiLocRing P' (fibreOver v P' W)).subtype)
    Subtype.val_injective ?_
  have hmem : (b : FractionRing (MRing ι' ⧸ P')) ∈ ⨅ V : {V : ValuationSubring
      (FractionRing (MRing ι' ⧸ P')) // Set.range f ⊆ V.toSubring}, V.1.toSubring := by
    rw [Subring.mem_iInf]
    rintro ⟨V, hV⟩
    obtain ⟨y, hy⟩ := h₁ K' ι' P' hP'.2.1 V
    have hcase := h₂ K ι K' ι' κ v P' n s α W hv hP' hP hs hsP hW V
      (fun a ha => hV ⟨⟨a, ha⟩, rfl⟩) y hy
    have hle : semiLocRing P' (fibreOver v P' W) ≤ V.toSubring := by
      rw [semiLocRing, Subring.closure_le]
      rintro _ ⟨u, w, a, hw, hwW, hu, hwa, rfl⟩
      have hwy : w ∉ y := by
        rcases hcase with rfl | hy'
        · exact fun h => nonZeroDivisors.ne_zero hw (Ideal.Quotient.eq_zero_iff_mem.mpr h)
        · exact hwW y hy'
      rw [SetLike.mem_coe, IsFractionRing.mk'_eq_div]
      exact (hy.2.2 a u w hu hwa hwy).1
    exact hle b.2
  rw [iInf_valuationSubring_superset, ← RingHom.coe_range, Subring.closure_eq] at hmem
  obtain ⟨p, hp, hpx⟩ := (hmem : IsIntegral f.range (b : FractionRing (MRing ι' ⧸ P')))
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    ((Polynomial.mem_lifts p).mpr
      (Polynomial.map_surjective f.rangeRestrict (fun ⟨_, a, ha⟩ => ⟨a, Subtype.ext ha⟩) p)) hp
  refine ⟨q, hqm, ?_⟩
  change Polynomial.eval₂ (f.range.subtype.comp f.rangeRestrict) (b : FractionRing _) q = 0
  rw [← Polynomial.eval₂_map, hq]
  exact hpx

end GroundTheory.Heights₂.Heights.Inter
end
end
