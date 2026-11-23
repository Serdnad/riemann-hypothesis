module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle003
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BlockDetLowUEmb
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038

@[expose] public section

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke GlobalTheory.LowerHecke

noncomputable section

namespace GlobalTheory.LowerHecke.MaxReps

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]


variable (k D A) in
def maxLat : AddSubgroup (Matrix D A k) where
  carrier := {ν | ∀ i a, valuation k (ν i a) < 1}
  add_mem' ha hb i a := by simpa using Valuation.map_add_lt _ (ha i a) (hb i a)
  zero_mem' i a := by simp
  neg_mem' ha i a := by simpa using ha i a

def mulLat (g : Matrix D D k) : AddSubgroup (Matrix D A k) where
  carrier := {x | ∃ μ : Matrix D A k, (∀ i a, valuation k (μ i a) < 1) ∧ x = g * μ}
  add_mem' := by
    rintro _ _ ⟨μ, hμ, rfl⟩ ⟨μ', hμ', rfl⟩
    exact ⟨μ + μ', fun i a => by simpa using Valuation.map_add_lt _ (hμ i a) (hμ' i a),
      (Matrix.mul_add _ _ _).symm⟩
  zero_mem' := ⟨0, fun i a => by simp, by simp⟩
  neg_mem' := by
    rintro _ ⟨μ, hμ, rfl⟩
    exact ⟨-μ, fun i a => by simpa using hμ i a, (Matrix.mul_neg _ _).symm⟩

theorem inv_mul_mem {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) {x : k} (hx : valuation k x < 1) :
    (ϖ : k)⁻¹ * x ∈ 𝒪[k] := by
  show valuation k _ ≤ 1
  have h0 : valuation k (ϖ : k) ≠ 0 := by simp
  rw [map_mul, map_inv₀, inv_mul_le_iff₀ (zero_lt_iff.2 h0), mul_one, hϖ, le_uniformizer_iff]
  exact hx

def redMap (ϖ : kˣ) (hϖ : valuation k (ϖ : k) = uniformizer k) : maxLat k A D →+ (D → A → 𝓀[k]) where
  toFun ν i a := IsLocalRing.residue 𝒪[k] ⟨(ϖ : k)⁻¹ * (ν : Matrix D A k) i a, inv_mul_mem hϖ (ν.2 i a)⟩
  map_zero' := by
    funext i a
    simp only [AddSubgroup.coe_zero, Matrix.zero_apply, mul_zero, Pi.zero_apply]
    exact map_zero _
  map_add' ν ν' := by
    funext i a
    simp only [Pi.add_apply]
    rw [← map_add (f := _)]
    congr 1
    ext
    simp [mul_add]

theorem exists_int_right_inv {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (s : Finset D) (g : GL D k)
    (hg : ∃ κ ∈ KO k D, ∃ κ' ∈ KO k D, g = κ * torusElt k D ϖ (indic s) * κ') :
    ∃ Q : Matrix D D k, GlobalTheory.StepData.IntM Q ∧ g.1 * Q = (ϖ : k) • (1 : Matrix D D k) := by
  obtain ⟨κ, hκ, κ', hκ', rfl⟩ := hg
  have hϖ1 : (ϖ : k) ∈ 𝒪[k] := (hϖ ▸ uniformizer_lt_one).le
  let D0 : Matrix D D k := diagonal fun i => (ϖ : k) ^ (1 - indic s i)
  have hD0 : (torusElt k D ϖ (indic s)).1 * D0 = (ϖ : k) • (1 : Matrix D D k) := by
    rw [val_torusElt, diagonal_mul_diagonal, smul_one_eq_diagonal]
    congr 1
    funext i
    rw [← zpow_add₀ ϖ.ne_zero]
    simp
  refine ⟨(κ'⁻¹ : GL D k).1 * D0 * (κ⁻¹ : GL D k).1, ?_, ?_⟩
  · refine ((GlobalTheory.StepData.mem_KO.1 hκ').2.mul ?_).mul (GlobalTheory.StepData.mem_KO.1 hκ).2
    intro i j
    simp only [D0, diagonal_apply]
    split_ifs
    · by_cases hi : i ∈ s <;> simp [indic, hi, hϖ1]
    · exact zero_mem _
  · have e1 : κ'.1 * (κ'⁻¹ : GL D k).1 = 1 := Units.mul_inv κ'
    have e2 : κ.1 * (κ⁻¹ : GL D k).1 = 1 := Units.mul_inv κ
    simp only [Units.val_mul]
    calc κ.1 * (torusElt k D ϖ (indic s)).1 * κ'.1 * ((κ'⁻¹ : GL D k).1 * D0 * (κ⁻¹ : GL D k).1)
        = κ.1 * ((torusElt k D ϖ (indic s)).1 * (κ'.1 * (κ'⁻¹ : GL D k).1) * D0) * (κ⁻¹ : GL D k).1 := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [e1, Matrix.mul_one, hD0, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, e2]

end GlobalTheory.LowerHecke.MaxReps


open GlobalTheory.LowerHecke.MaxReps in
theorem GlobalTheory.LowerHecke.exists_finset_reps_maxLat_mod_mul : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (s : Finset D) (g : GL D k), (∃ κ ∈ KO k D, ∃ κ' ∈ KO k D, g = κ * torusElt k D ϖ (indic s) * κ') → ∃ N : Finset (Matrix D A k), (∀ ν ∈ N, ∀ i a, valuation k (ν i a) < 1) ∧ ∀ ν : Matrix D A k, (∀ i a, valuation k (ν i a) < 1) → ∃! ν', ν' ∈ N ∧ ∃ μ : Matrix D A k, (∀ i a, valuation k (μ i a) < 1) ∧ ν - ν' = g.1 * μ := by
  intro k _ _ _ _ A D _ _ _ _ ϖ hϖ s g hg
  classical
  obtain ⟨Q, hQ, hgQ⟩ := exists_int_right_inv hϖ s g hg
  let M := maxLat k A D
  let H := (mulLat (A := A) g.1).addSubgroupOf M
  have hK : (redMap (D := D) (A := A) ϖ hϖ).ker ≤ H := by
    intro ν hν
    rw [AddMonoidHom.mem_ker] at hν
    rw [AddSubgroup.mem_addSubgroupOf]
    have hμ : ∀ i a, valuation k ((ϖ : k)⁻¹ * (ν : Matrix D A k) i a) < 1 := fun i a => by
      have := congrFun (congrFun hν i) a
      simp only [redMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.zero_apply] at this
      exact (GlobalTheory.StepData.residue_eq_zero_iff_lt _).1 this
    refine ⟨Q * ((ϖ : k)⁻¹ • (ν : Matrix D A k)), hQ.mul_maxM (fun i a => by simpa using hμ i a), ?_⟩
    rw [← Matrix.mul_assoc, hgQ, Matrix.smul_mul, Matrix.one_mul, smul_smul, mul_inv_cancel₀ ϖ.ne_zero, one_smul]
  haveI : Finite (M ⧸ (redMap (D := D) (A := A) ϖ hϖ).ker) :=
    Finite.of_equiv _ (QuotientAddGroup.quotientKerEquivRange _).symm.toEquiv
  haveI : (redMap (D := D) (A := A) ϖ hϖ).ker.FiniteIndex := AddSubgroup.finiteIndex_of_finite_quotient
  haveI : H.FiniteIndex := AddSubgroup.finiteIndex_of_le hK
  haveI : Finite (M ⧸ H) := AddSubgroup.finite_quotient_of_finiteIndex
  letI := Fintype.ofFinite (M ⧸ H)
  refine ⟨Finset.univ.image fun q : M ⧸ H => ((Quotient.out q : M) : Matrix D A k), ?_, ?_⟩
  · intro ν hν
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hν
    exact (Quotient.out q).2
  · intro ν hν
    have key : ∀ q : M ⧸ H, q = (QuotientAddGroup.mk ⟨ν, hν⟩ : M ⧸ H) ↔
        ∃ μ : Matrix D A k, (∀ i a, valuation k (μ i a) < 1) ∧ ν - ((Quotient.out q : M) : Matrix D A k) = g.1 * μ := by
      intro q
      conv_lhs => rw [← QuotientAddGroup.out_eq' q]
      rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
      refine exists_congr fun μ => and_congr_right fun _ => ?_
      show -((Quotient.out q : M) : Matrix D A k) + ν = g.1 * μ ↔ _
      rw [neg_add_eq_sub]
    refine ⟨((Quotient.out (QuotientAddGroup.mk ⟨ν, hν⟩ : M ⧸ H) : M) : Matrix D A k),
      ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), (key _).1 rfl⟩, ?_⟩
    rintro y ⟨hy, hyμ⟩
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hy
    rw [(key q).2 hyμ]

end
end

section

namespace GlobalTheory.Honda

theorem unitFix_subMax {K : Type} [NormedField K] [IsUltrametricDist K] (x y : K) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  rw [sub_eq_add_neg, ← norm_neg y]; exact IsUltrametricDist.norm_add_le_max _ _

theorem unitFix_powSub {K : Type} [NormedField K] [IsUltrametricDist K] (a b : K) (ha : ‖a‖ ≤ 1)
    (hb : ‖b‖ ≤ 1) (hab : ‖a - b‖ < 1) : ∀ n : ℕ, ‖a ^ n - b ^ n‖ < 1 := by
  first
  | exact @_root_.GlobalTheory.UltrametricPowerDifference.norm_pow_sub_pow_lt_one
  | exact _root_.GlobalTheory.UltrametricPowerDifference.norm_pow_sub_pow_lt_one
  | (apply _root_.GlobalTheory.UltrametricPowerDifference.norm_pow_sub_pow_lt_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.UltrametricPowerDifference.norm_pow_sub_pow_lt_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UltrametricPowerDifference.norm_pow_sub_pow_lt_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UltrametricPowerDifference.norm_pow_sub_pow_lt_one ..)

theorem unitFix_sq_apply {K : Type} [NormedField K] (σ : K →+* K) (x : K) : (σ ^ 2) x = σ (σ x) := by
  rw [pow_two]; rfl

theorem unitFix_frob2 {K : Type} [NormedField K] [IsUltrametricDist K] (l : ℕ) (σ : K →+* K) (hU : Unr K l σ)
    (x : K) (hx : ‖x‖ ≤ 1) : ‖(σ ^ 2) x - x ^ (l ^ 2)‖ < 1 := by
  obtain ⟨_, _, _, _, hiso, hfr⟩ := hU
  have hsx : ‖σ x‖ ≤ 1 := by rw [hiso]; exact hx
  have h1 := hfr (σ x) hsx
  have h2 : ‖(σ x) ^ l - (x ^ l) ^ l‖ < 1 :=
    unitFix_powSub _ _ hsx (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx) (hfr x hx) l
  have hq : x ^ (l ^ 2) = (x ^ l) ^ l := by rw [← pow_mul, sq]
  have e2 : σ (σ x) - x ^ (l ^ 2) = (σ (σ x) - σ x ^ l) + ((σ x) ^ l - (x ^ l) ^ l) := by rw [hq]; ring
  rw [unitFix_sq_apply, e2]
  exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt h1 h2)

theorem unitFix_root {K : Type} [NormedField K] [IsUltrametricDist K] (hR : ResAlg K) (m : ℕ) (hm : 2 ≤ m)
    (a b : K) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ∃ y : K, ‖y‖ ≤ 1 ∧ ‖y ^ m - a * y - b‖ < 1 := by
  classical
  have hdeg : (Polynomial.C a * Polynomial.X + Polynomial.C b).natDegree
      < (Polynomial.X ^ m : Polynomial K).natDegree := by
    rw [Polynomial.natDegree_X_pow]; exact lt_of_le_of_lt Polynomial.natDegree_linear_le (by omega)
  have hmon : (Polynomial.X ^ m - (Polynomial.C a * Polynomial.X + Polynomial.C b)).Monic :=
    (Polynomial.monic_X_pow m).sub_of_left (Polynomial.degree_lt_degree hdeg)
  have hnd : 0 < (Polynomial.X ^ m - (Polynomial.C a * Polynomial.X + Polynomial.C b)).natDegree := by
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt hdeg, Polynomial.natDegree_X_pow]; omega
  have hco : ∀ n, ‖(Polynomial.X ^ m - (Polynomial.C a * Polynomial.X + Polynomial.C b)).coeff n‖ ≤ 1 := by
    intro n
    simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul,
      Polynomial.coeff_X, Polynomial.coeff_C]
    refine (unitFix_subMax _ _).trans
      (max_le ?_ ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)))
    · split_ifs <;> simp
    · split_ifs <;> simp [ha]
    · split_ifs <;> simp [hb]
  obtain ⟨y, hy, hev⟩ := hR _ hmon hnd hco
  refine ⟨y, hy, ?_⟩
  have e : (Polynomial.X ^ m - (Polynomial.C a * Polynomial.X + Polynomial.C b)).eval y = y ^ m - a * y - b := by
    simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_pow]
    ring
  rwa [e] at hev

theorem unitFix_step {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K)
    (hU : Unr K l σ) (hR : ResAlg K) (c : K) (hc : ‖c‖ = 1) (n : ℕ) (ε : K)
    (hε : ‖ε - c * (σ ^ 2) ε‖ ≤ ‖(l : K)‖ ^ n) :
    ∃ η : K, ‖η‖ ≤ ‖(l : K)‖ ^ n ∧ ‖(ε + η) - c * (σ ^ 2) (ε + η)‖ ≤ ‖(l : K)‖ ^ (n + 1) := by
  have hU' := hU
  obtain ⟨hp, h2, hl1, hdisc, hiso, hfr⟩ := hU'
  have hl0 : (l : K) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hπ0 : (l : K) ^ n ≠ 0 := pow_ne_zero _ hl0
  have hπn : ‖(l : K) ^ n‖ = ‖(l : K)‖ ^ n := norm_pow _ _
  have hπpos : 0 < ‖(l : K) ^ n‖ := norm_pos_iff.mpr hπ0
  have hbn : ‖(ε - c * (σ ^ 2) ε) / (l : K) ^ n‖ ≤ 1 := by
    rw [norm_div, div_le_one hπpos, hπn]; exact hε
  have hc0 : c ≠ 0 := by intro h; rw [h, norm_zero] at hc; exact zero_ne_one hc
  have hci : ‖c⁻¹‖ = 1 := by rw [norm_inv, hc, inv_one]
  have hq : 2 ≤ l ^ 2 := le_trans (by omega : 2 ≤ l) (Nat.le_self_pow (by norm_num) l)
  obtain ⟨y, hy, hroot⟩ := unitFix_root hR (l ^ 2) hq c⁻¹ (c⁻¹ * ((ε - c * (σ ^ 2) ε) / (l : K) ^ n)) hci.le
    (by rw [norm_mul, hci, one_mul]; exact hbn)
  have hfy := unitFix_frob2 l σ hU y hy
  have hσπ : (σ ^ 2) ((l : K) ^ n) = (l : K) ^ n := by rw [map_pow, map_natCast]
  refine ⟨(l : K) ^ n * y, ?_, ?_⟩
  · rw [norm_mul, ← hπn]; exact mul_le_of_le_one_right (norm_nonneg _) hy
  · set b : K := (ε - c * (σ ^ 2) ε) / (l : K) ^ n with hb
    have e : (ε + (l : K) ^ n * y) - c * (σ ^ 2) (ε + (l : K) ^ n * y)
        = (l : K) ^ n * (b + y - c * y ^ (l ^ 2) + c * (y ^ (l ^ 2) - (σ ^ 2) y)) := by
      rw [map_add (f := _), map_mul, hσπ, hb]; field_simp; ring
    have e2 : b + y - c * y ^ (l ^ 2) = -c * (y ^ (l ^ 2) - c⁻¹ * y - c⁻¹ * b) := by field_simp; ring
    have hlt : ‖b + y - c * y ^ (l ^ 2) + c * (y ^ (l ^ 2) - (σ ^ 2) y)‖ < 1 := by
      refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
      · rw [e2, norm_mul, norm_neg, hc, one_mul]; exact hroot
      · rw [norm_mul, hc, one_mul, ← norm_neg, neg_sub]; exact hfy
    rw [e, norm_mul, hπn, pow_succ]
    exact mul_le_mul_of_nonneg_left (hdisc _ hlt) (pow_nonneg (norm_nonneg _) _)

theorem unitFix_init {K : Type} [NormedField K] [IsUltrametricDist K] (l : ℕ) (σ : K →+* K)
    (hU : Unr K l σ) (hR : ResAlg K) (c : K) (hc : ‖c‖ = 1) :
    ∃ ε : K, ‖ε‖ = 1 ∧ ‖ε - c * (σ ^ 2) ε‖ ≤ ‖(l : K)‖ ^ 1 := by
  have hU' := hU
  obtain ⟨hp, h2, hl1, hdisc, hiso, hfr⟩ := hU'
  have hc0 : c ≠ 0 := by intro h; rw [h, norm_zero] at hc; exact zero_ne_one hc
  have hci : ‖c⁻¹‖ = 1 := by rw [norm_inv, hc, inv_one]
  have hq : 4 ≤ l ^ 2 := by nlinarith
  obtain ⟨m, hm⟩ : ∃ m, l ^ 2 = m + 1 := ⟨l ^ 2 - 1, by omega⟩
  have hm2 : 2 ≤ m := by omega
  obtain ⟨x, hx, hroot⟩ := unitFix_root hR m hm2 0 c⁻¹ (by simp) hci.le
  simp only [zero_mul, sub_zero] at hroot
  have hx1 : ‖x‖ = 1 := by
    refine le_antisymm hx (not_lt.mp fun hlt => ?_)
    have hxm : ‖x ^ m‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hlt (by omega)
    have : ‖c⁻¹‖ < 1 := by
      have e : c⁻¹ = x ^ m - (x ^ m - c⁻¹) := by ring
      rw [e]; exact lt_of_le_of_lt (unitFix_subMax _ _) (max_lt hxm hroot)
    rw [hci] at this; exact lt_irrefl _ this
  refine ⟨x, hx1, ?_⟩
  have hfx := unitFix_frob2 l σ hU x hx
  have e : x - c * (σ ^ 2) x = -(c * x) * (x ^ m - c⁻¹) + c * (x ^ (l ^ 2) - (σ ^ 2) x) := by
    rw [hm, pow_succ]; field_simp; ring
  rw [pow_one]
  apply hdisc
  rw [e]
  refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
  · rw [norm_mul, norm_neg, norm_mul, hc, hx1, one_mul, one_mul]; exact hroot
  · rw [norm_mul, hc, one_mul, ← norm_neg, neg_sub]; exact hfx

theorem unit_solution_twisted_frobenius : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K]
    [CompleteSpace K] (l : ℕ) (σ : K →+* K), Unr K l σ → ResAlg K → ∀ c : K, ‖c‖ = 1 →
    ∃ ε : K, ‖ε‖ = 1 ∧ ε = c * (σ ^ 2) ε := by
  intro K _ _ _ _ l σ hU hR c hc
  have hU' := hU
  obtain ⟨hp, h2, hl1, hdisc, hiso, hfr⟩ := hU'
  obtain ⟨ε0, hε0n, hε0⟩ := unitFix_init l σ hU hR c hc
  have hstep : ∀ (n : ℕ) (ε : K), ∃ η : K, ‖ε - c * (σ ^ 2) ε‖ ≤ ‖(l : K)‖ ^ n →
      ‖η‖ ≤ ‖(l : K)‖ ^ n ∧ ‖(ε + η) - c * (σ ^ 2) (ε + η)‖ ≤ ‖(l : K)‖ ^ (n + 1) := by
    intro n ε
    by_cases h : ‖ε - c * (σ ^ 2) ε‖ ≤ ‖(l : K)‖ ^ n
    · obtain ⟨η, h1⟩ := unitFix_step l σ hU hR c hc n ε h
      exact ⟨η, fun _ => h1⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose g hg using hstep
  let e : ℕ → K := fun k => Nat.rec ε0 (fun k x => x + g (k + 1) x) k
  have he0 : e 0 = ε0 := rfl
  have hes : ∀ k, e (k + 1) = e k + g (k + 1) (e k) := fun k => rfl
  have hpow : ∀ k : ℕ, ‖(l : K)‖ ^ (k + 1) < 1 := fun k => pow_lt_one₀ (norm_nonneg _) hl1 (by omega)
  have hinv : ∀ k, ‖e k‖ = 1 ∧ ‖e k - c * (σ ^ 2) (e k)‖ ≤ ‖(l : K)‖ ^ (k + 1) := by
    intro k
    induction k with
    | zero => exact ⟨he0 ▸ hε0n, by rw [he0]; simpa using hε0⟩
    | succ k ih =>
      obtain ⟨hη, herr⟩ := hg (k + 1) (e k) ih.2
      refine ⟨?_, by rw [hes]; exact herr⟩
      have hlt : ‖g (k + 1) (e k)‖ < ‖e k‖ := by rw [ih.1]; exact lt_of_le_of_lt hη (hpow k)
      rw [hes, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne', max_eq_left hlt.le, ih.1]
  have hcs : CauchySeq e := by
    refine cauchySeq_of_le_geometric ‖(l : K)‖ ‖(l : K)‖ hl1 (fun k => ?_)
    rw [dist_eq_norm, hes, sub_add_cancel_left, norm_neg, ← pow_succ']
    exact (hg (k + 1) (e k) (hinv k).2).1
  obtain ⟨ε, hlim⟩ := cauchySeq_tendsto_of_complete hcs
  have hτc : Continuous (fun x : K => (σ ^ 2) x) := AddMonoidHomClass.continuous_of_bound (σ ^ 2) 1 (fun x => by
    rw [one_mul, unitFix_sq_apply, hiso, hiso])
  have hcont : Continuous (fun x : K => x - c * (σ ^ 2) x) := continuous_id.sub (continuous_const.mul hτc)
  have h1 : Filter.Tendsto (fun k => e k - c * (σ ^ 2) (e k)) Filter.atTop (nhds (ε - c * (σ ^ 2) ε)) :=
    (hcont.tendsto ε).comp hlim
  have h0 : Filter.Tendsto (fun k => e k - c * (σ ^ 2) (e k)) Filter.atTop (nhds 0) :=
    squeeze_zero_norm (fun k => (hinv k).2)
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hl1).comp (Filter.tendsto_add_atTop_nat 1))
  have heq : ε - c * (σ ^ 2) ε = 0 := tendsto_nhds_unique h1 h0
  refine ⟨ε, ?_, sub_eq_zero.mp heq⟩
  have hn : Filter.Tendsto (fun k => ‖e k‖) Filter.atTop (nhds ‖ε‖) := (continuous_norm.tendsto ε).comp hlim
  have hfun : (fun k => ‖e k‖) = fun _ => (1 : ℝ) := funext fun k => (hinv k).1
  rw [hfun] at hn
  exact tendsto_nhds_unique hn tendsto_const_nhds

end GlobalTheory.Honda
end

section

open PowerSeries GlobalTheory.Honda

namespace GlobalTheory.Honda.OneTerm

variable {K : Type} [NormedField K]

theorem coeff_frobOp (τ : K →+* K) {q : ℕ} (hq : q ≠ 0) (i : ℕ) (f : K⟦X⟧) (n : ℕ) :
    coeff n (frobOp τ q i f) = if q ^ i ∣ n then (τ ^ i) (coeff (n / q ^ i) f) else 0 := by
  unfold frobOp
  rw [coeff_subst_X_pow (pow_ne_zero _ hq)]
  simp [coeff_map]

theorem pow_apply_pow (τ : K →+* K) (i k : ℕ) (x : K) : (τ ^ i) ((τ ^ k) x) = (τ ^ (i + k)) x := by
  rw [pow_add]; rfl

theorem norm_pow_apply (τ : K →+* K) (hτ : ∀ x, ‖τ x‖ = ‖x‖) (i : ℕ) (x : K) : ‖(τ ^ i) x‖ = ‖x‖ := by
  induction i generalizing x with
  | zero => rfl
  | succ i ih => rw [← pow_apply_pow, ih, pow_one, hτ]

theorem coeff_frobOp_eq_zero (τ : K →+* K) {q : ℕ} (hq : 2 ≤ q) {f : K⟦X⟧} (hf : constantCoeff f = 0)
    {k n : ℕ} (h : n ≤ k) : coeff n (frobOp τ q k f) = 0 := by
  rw [coeff_frobOp τ (by omega)]
  split_ifs with hd
  · have hlt : n < q ^ k := lt_of_le_of_lt h (Nat.lt_pow_self (by omega))
    have h0 : n = 0 := Nat.eq_zero_of_dvd_of_lt hd hlt
    subst h0
    simp [hf]
  · rfl

theorem pow_apply_coeff_frobOp (τ : K →+* K) {q : ℕ} (hq : q ≠ 0) (f : K⟦X⟧) (i k : ℕ) {n : ℕ} (hd : q ^ i ∣ n) :
    (τ ^ i) (coeff (n / q ^ i) (frobOp τ q k f)) = coeff n (frobOp τ q (i + k) f) := by
  rw [coeff_frobOp τ hq, coeff_frobOp τ hq, pow_add q i k]
  by_cases h : q ^ i * q ^ k ∣ n
  · rw [if_pos h, if_pos ((Nat.dvd_div_iff_mul_dvd hd).2 h), pow_apply_pow, Nat.div_div_eq_div_mul]
  · rw [if_neg h, if_neg (fun h' => h ((Nat.dvd_div_iff_mul_dvd hd).1 h')), map_zero]

theorem coeff_frobOp_sub_hondaSum (τ : K →+* K) (l : ℕ) {q : ℕ} (hq : 2 ≤ q) {f : K⟦X⟧} (hf : constantCoeff f = 0)
    (c : ℕ → K) (i n N : ℕ) (hN : n ≤ N) :
    coeff n (frobOp τ q i (C (l : K) * f - hondaSum τ q c f)) =
      (l : K) * coeff n (frobOp τ q i f) -
        ∑ j ∈ Finset.range N, (τ ^ i) (c j) * coeff n (frobOp τ q (i + (j + 1)) f) := by
  have hq0 : q ≠ 0 := by omega
  rw [coeff_frobOp τ hq0]

  by_cases hd : q ^ i ∣ n
  · rw [if_pos hd, coeff_frobOp τ hq0 i f, if_pos hd, map_sub, coeff_C_mul, hondaSum, coeff_mk,
     ← Finset.eventually_constant_sum (N := n / q ^ i) (n := N)
       (fun j hj => by rw [coeff_frobOp_eq_zero τ hq hf (by omega), mul_zero])
       (le_trans (Nat.div_le_self _ _) hN),
     map_sub, map_mul, map_natCast, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, pow_apply_coeff_frobOp τ hq0 f i (j + 1) hd]
  · rw [if_neg hd, coeff_frobOp τ hq0 i f, if_neg hd, mul_zero, Finset.sum_eq_zero, sub_zero]
    intro j _
    rw [coeff_frobOp τ hq0, if_neg, mul_zero]
    exact fun h => hd (dvd_trans (pow_dvd_pow q (Nat.le_add_right _ _)) h)

theorem sum_square_eq_sum_diag (N : ℕ) (F : ℕ → ℕ → K) (hF : ∀ i j, N ≤ i + j → F i j = 0) :
    ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, F i j =
      ∑ m ∈ Finset.range N, ∑ i ∈ Finset.range (m + 1), F i (m - i) := by
  rw [Finset.sum_range_diag_flip]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Finset.eventually_constant_sum (fun j hj => hF i j (by omega)) (Nat.sub_le _ _)

theorem coeff_identity (τ : K →+* K) (l : ℕ) {q : ℕ} (hq : 2 ≤ q) {f : K⟦X⟧} (hf : constantCoeff f = 0)
    (c t : ℕ → K) (ht0 : t 0 = 1)
    (ht : ∀ n, 2 ≤ n → (l : K) * t n = ∑ i ∈ Finset.range n, t i * (τ ^ i) (c (n - 1 - i))) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), t i * coeff n (frobOp τ q i (C (l : K) * f - hondaSum τ q c f)) =
      (l : K) * coeff n f - (c 0 - l * t 1) * coeff n (frobOp τ q 1 f) := by
  have hq0 : q ≠ 0 := by omega
  have h1 : ∀ i ∈ Finset.range (n + 1), t i * coeff n (frobOp τ q i (C (l : K) * f - hondaSum τ q c f)) =
      (l : K) * t i * coeff n (frobOp τ q i f) -
        ∑ j ∈ Finset.range (n + 1), t i * (τ ^ i) (c j) * coeff n (frobOp τ q (i + (j + 1)) f) := by
    intro i _
    rw [coeff_frobOp_sub_hondaSum τ l hq hf c i n (n + 1) (Nat.le_succ n), mul_sub, Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun j _ => by ring
  rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib,
    sum_square_eq_sum_diag (n + 1) (fun i j => t i * (τ ^ i) (c j) * coeff n (frobOp τ q (i + (j + 1)) f))
      (fun i j hij => by simp only [coeff_frobOp_eq_zero τ hq hf (show n ≤ i + (j + 1) by omega), mul_zero])]
  have h2 : ∀ m ∈ Finset.range (n + 1),
      ∑ i ∈ Finset.range (m + 1), t i * (τ ^ i) (c (m - i)) * coeff n (frobOp τ q (i + (m - i + 1)) f) =
      (∑ i ∈ Finset.range (m + 1), t i * (τ ^ i) (c (m - i))) * coeff n (frobOp τ q (m + 1) f) := by
    intro m _
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    have : i + (m - i + 1) = m + 1 := by have := Finset.mem_range.1 hi; omega
    rw [this]
  rw [Finset.sum_congr rfl h2, Finset.sum_range_succ', Finset.sum_range_succ _ n,
    coeff_frobOp_eq_zero τ hq hf (Nat.le_succ n), mul_zero, add_zero, add_sub_right_comm,
    ← Finset.sum_sub_distrib, Finset.sum_eq_single 0]
  · have h0 : coeff n (frobOp τ q 0 f) = coeff n f := by
      rw [coeff_frobOp τ hq0]; simp
    rw [h0, ht0]
    simp only [zero_add, Finset.sum_range_one, pow_zero, Nat.sub_zero, ht0, RingHom.one_def, RingHom.id_apply]
    ring
  · intro m _ hm
    rw [ht (m + 1) (by omega), Nat.add_sub_cancel, sub_self]
  · intro h
    have hn : n = 0 := by simpa using h
    rw [coeff_frobOp_eq_zero τ hq hf (show n ≤ 0 + 1 by omega), mul_zero, mul_zero, sub_self]

theorem exists_one_term : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] [CompleteSpace K]
    (l q : ℕ) (τ : K →+* K), 2 ≤ q → ‖(l : K)‖ < 1 → (∀ x, ‖τ x‖ = ‖x‖) → ∀ (f : K⟦X⟧), constantCoeff f = 0 →
    ∀ c : ℕ → K, (∀ j, ‖c j‖ ≤ 1) → ‖c 0‖ = 1 → CoefLe ‖(l : K)‖ (C (l : K) * f - hondaSum τ q c f) →
    ∃ c' : K, ‖c'‖ = 1 ∧ CoefLe ‖(l : K)‖ (C (l : K) * f - C c' * frobOp τ q 1 f) := by
  intro K _ _ _ _ l q τ hq hl hτ f hf c hc hc0 hg
  obtain ⟨t, ht0, ht1, ht⟩ := GlobalTheory.Honda.exists_twisted_division K τ hτ (l : K) hl c hc0 hc
  refine ⟨c 0 - l * t 1, ?_, fun n => ?_⟩
  · have hlt : ‖-((l : K) * t 1)‖ < ‖c 0‖ := by
      rw [norm_neg, norm_mul, hc0]
      exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (ht1 1)) hl
    rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne', max_eq_left hlt.le, hc0]
  · rw [map_sub, coeff_C_mul, coeff_C_mul, ← coeff_identity τ l hq hf c t ht0 ht n]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_
    rw [norm_mul]
    refine le_trans (mul_le_of_le_one_left (norm_nonneg _) (ht1 i)) ?_
    rw [coeff_frobOp τ (by omega)]
    split_ifs
    · rw [norm_pow_apply τ hτ]; exact hg _
    · simp

end GlobalTheory.Honda.OneTerm
end
