module

public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle002
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle003
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Formalism.TorsionNormIteration.InvIntegralOfClass
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
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
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle008
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle001
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQuadInt
public import Mathlib.NumberTheory.NumberField.Norm
import ReciprocityTheory.NeutralLocalFields.Bundle001

@[expose] public section

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

section Abstract

variable {K : Type} [NormedField K]

structure LawD (lam : PowerSeries K) (Φ : MvPowerSeries (Fin 2) K) : Prop where
  lam0 : constantCoeff lam = 0
  lam1 : coeff 1 lam = 1
  Φ0 : MvPowerSeries.constantCoeff Φ = 0
  Φint : IntegralMv Φ
  log : lam.subst Φ = atX lam + atY lam

structure HD (σ : K →+* K) (lam : PowerSeries K) (Φ : MvPowerSeries (Fin 2) K) (A : PowerSeries K)
    (a : K) : Prop extends LawD lam Φ where
  A0 : constantCoeff A = 0
  Aint : IntegralPS A
  Alog : lam.subst A = C a * lam
  a_ne : ‖σ a - a‖ = 1
  a_sq : σ (σ a) = a

structure QCls (l : ℕ) (Φ : MvPowerSeries (Fin 2) K) (A : PowerSeries K) (b : K)
    (D : PowerSeries K) : Prop where
  D0 : constantCoeff D = 0
  dInt : IntegralPS (PowerSeries.derivative D)
  add : DivByMv (l : K) (D.subst Φ - atX D - atY D)
  eig : DivBy (l : K) (D.subst A - C b * D)

structure HomCls (l : ℕ) (Φ₁ : MvPowerSeries (Fin 2) K) (A₁ : PowerSeries K)
    (Φ₂ : MvPowerSeries (Fin 2) K) (A₂ : PowerSeries K) (g : PowerSeries K) : Prop where
  g0 : constantCoeff g = 0
  gInt : IntegralPS g
  add : DivByMv (l : K) (g.subst Φ₁ - Φ₂.subst ![atX g, atY g])
  eig : DivBy (l : K) (g.subst A₁ - A₂.subst g)

def desc (l : ℕ) (D : PowerSeries K) : PowerSeries K := PowerSeries.mk fun m => coeff (l * m) D

def d2 (Φ : MvPowerSeries (Fin 2) K) : PowerSeries K :=
  PowerSeries.mk fun n => MvPowerSeries.coeff (Finsupp.single 0 n + Finsupp.single 1 1) Φ

end Abstract


open Classical in
def lgS {K : Type} [Field K] (g2 g3 : K) : PowerSeries K :=
  if h : ∃ t : PowerSeries K, constantCoeff t = 0 ∧ (uSer g2 g3).subst t = X then h.choose else 0

end ReciprocityTheory.ChartRestriction.L1
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM

variable (l : ℕ) [Fact l.Prime]

theorem rmu_norm_le {x : ℂ_[l]} (hx : x ∈ Rmu l) : ‖x‖ ≤ 1 := by
  induction hx using Subring.closure_induction with
  | mem x hx => exact (muP_norm l hx).le
  | zero => simp
  | one => simp
  | add x y _ _ hx hy =>
    exact (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)
  | neg x _ hx => rwa [norm_neg]
  | mul x y _ _ hx hy =>
    rw [norm_mul]
    exact mul_le_one₀ hx (norm_nonneg _) hy

theorem kmu_frac {x : ℂ_[l]} (hx : x ∈ Kmu l) :
    ∃ a ∈ Rmu l, ∃ b ∈ Rmu l, b ≠ 0 ∧ x = a / b := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Subfield.mem_closure_iff.1 hx
  by_cases hz0 : z = 0
  · refine ⟨0, (Rmu l).zero_mem, 1, (Rmu l).one_mem, one_ne_zero, ?_⟩
    rw [hz0, div_zero, zero_div]
  · exact ⟨y, hy, z, hz, hz0, rfl⟩

theorem exists_power_mul_unitNorm (k : ℕ) : ∀ a ∈ Rmu l, a ≠ 0 → 1 < (l : ℝ) ^ k * ‖a‖ →
    ∃ m : ℕ, ∃ c ∈ Rmu l, ∃ u ∈ Rmu l, ‖c‖ = 1 ∧ ‖u‖ = 1 ∧ a * u = (l : ℂ_[l]) ^ m * c := by
  induction k with
  | zero =>
    intro a ha _ h
    rw [pow_zero, one_mul] at h
    exact absurd (rmu_norm_le l ha) (not_le.2 h)
  | succ k ih =>
    intro a ha ha0 h
    rcases (rmu_norm_le l ha).eq_or_lt with h1 | h1
    · exact ⟨0, a, ha, 1, (Rmu l).one_mem, h1, norm_one, by rw [pow_zero, one_mul, mul_one]⟩
    obtain ⟨f, hf, r, hr, he⟩ := rmu_frob l a ha
    have hl1 : 1 < l := (Fact.out : l.Prime).one_lt
    have hq : 1 ≤ l ^ f - 1 := by
      have : 2 ≤ l ^ f := le_trans (Fact.out : l.Prime).two_le (Nat.le_self_pow hf.ne' l)
      omega
    set u := a ^ (l ^ f - 1) - 1 with hu
    have huR : u ∈ Rmu l := sub_mem (pow_mem ha _) (Rmu l).one_mem
    have hu1 : ‖u‖ = 1 := by
      have hsm : ‖a ^ (l ^ f - 1)‖ < 1 := by
        rw [norm_pow]
        exact pow_lt_one₀ (norm_nonneg _) h1 (by omega)
      have := ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation.norm_eq_of_norm_sub_lt' l (a := u) (b := -1)
        (by rw [hu, sub_neg_eq_add, sub_add_cancel, norm_neg, norm_one]; exact hsm)
      rwa [norm_neg, norm_one] at this
    have hau : a * u = (l : ℂ_[l]) * r := by
      rw [← he, hu, mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ l ^ f)]
    have hnr : ‖r‖ = l * ‖a‖ := by
      have := congrArg norm hau
      rw [norm_mul, norm_mul, hu1, mul_one, norm_l_Cl] at this
      have hl0 : (l : ℝ) ≠ 0 := by positivity
      rw [this, ← mul_assoc, mul_inv_cancel₀ hl0, one_mul]
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [norm_zero] at hnr
      have : (0 : ℝ) < l * ‖a‖ := mul_pos (by positivity) (norm_pos_iff.2 ha0)
      linarith
    have h' : 1 < (l : ℝ) ^ k * ‖r‖ := by
      rw [hnr, ← mul_assoc, ← pow_succ]; exact h
    obtain ⟨m, c, hc, v, hv, hc1, hv1, hrv⟩ := ih r hr hr0 h'
    refine ⟨m + 1, c, hc, u * v, mul_mem huR hv, hc1, by rw [norm_mul, hu1, hv1, one_mul], ?_⟩
    rw [← mul_assoc, hau, mul_assoc, hrv, pow_succ]
    ring

theorem rmu_shape {a : ℂ_[l]} (ha : a ∈ Rmu l) (ha0 : a ≠ 0) :
    ∃ m : ℕ, ∃ c ∈ Rmu l, ∃ u ∈ Rmu l, ‖c‖ = 1 ∧ ‖u‖ = 1 ∧ a * u = (l : ℂ_[l]) ^ m * c := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (‖a‖⁻¹) (by exact_mod_cast (Fact.out : l.Prime).one_lt :
    (1 : ℝ) < l)
  refine exists_power_mul_unitNorm l k a ha ha0 ?_
  have hpos : 0 < ‖a‖ := norm_pos_iff.2 ha0
  calc (1 : ℝ) = ‖a‖⁻¹ * ‖a‖ := (inv_mul_cancel₀ hpos.ne').symm
    _ < (l : ℝ) ^ k * ‖a‖ := mul_lt_mul_of_pos_right hk hpos

theorem kmu_shape {x : ℂ_[l]} (hx : x ∈ Kmu l) (hx0 : x ≠ 0) :
    ∃ m : ℤ, ∃ a ∈ Rmu l, ∃ b ∈ Rmu l, ‖a‖ = 1 ∧ ‖b‖ = 1 ∧ x = (l : ℂ_[l]) ^ m * (a / b) := by
  obtain ⟨a, ha, b, hb, hb0, rfl⟩ := kmu_frac l hx
  have ha0 : a ≠ 0 := by rintro rfl; exact hx0 (zero_div b)
  obtain ⟨m, c, hc, u, hu, hc1, hu1, hau⟩ := rmu_shape l ha ha0
  obtain ⟨n, d, hd, v, hv, hd1, hv1, hbv⟩ := rmu_shape l hb hb0
  have hl0 : (l : ℂ_[l]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu1
  have hv0 : v ≠ 0 := by rintro rfl; simp at hv1
  have hd0 : d ≠ 0 := by rintro rfl; simp at hd1
  refine ⟨(m : ℤ) - n, c * v, mul_mem hc hv, d * u, mul_mem hd hu,
    by rw [norm_mul, hc1, hv1, one_mul], by rw [norm_mul, hd1, hu1, one_mul], ?_⟩
  rw [zpow_sub₀ hl0, zpow_natCast, zpow_natCast]
  have ha' : a = (l : ℂ_[l]) ^ m * c / u := by rw [← hau, mul_div_cancel_right₀ _ hu0]
  have hb' : b = (l : ℂ_[l]) ^ n * d / v := by rw [← hbv, mul_div_cancel_right₀ _ hv0]
  rw [ha', hb']
  field_simp

end ReciprocityTheory.ChartRestriction.L1
end
end

section

noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F Polynomial

namespace ReciprocityTheory.ChartRestriction.L1

section Proj

variable {E : Type} [Field E]

def serMap (ψ : E →+ E) (S : PowerSeries E) : PowerSeries E :=
  PowerSeries.mk fun n => ψ (PowerSeries.coeff n S)

def polMap (ψ : E →+ E) (m : ℕ) (Q : E[X]) : E[X] :=
  ∑ i ∈ Finset.range (m + 1), monomial i (ψ (Q.coeff i))

theorem coeff_serMap (ψ : E →+ E) (S : PowerSeries E) (n : ℕ) :
    PowerSeries.coeff n (serMap ψ S) = ψ (PowerSeries.coeff n S) := by
  simp [serMap]

theorem serMap_sum (ψ : E →+ E) {ι : Type} (s : Finset ι) (f : ι → PowerSeries E) :
    serMap ψ (∑ i ∈ s, f i) = ∑ i ∈ s, serMap ψ (f i) := by
  ext n

  simp [coeff_serMap, map_sum]

theorem coeff_polMap (ψ : E →+ E) (m : ℕ) (Q : E[X]) (i : ℕ) :
    (polMap ψ m Q).coeff i = if i ≤ m then ψ (Q.coeff i) else 0 := by
  simp only [polMap, finsetSum_coeff, coeff_monomial_apply]
  rw [Finset.sum_ite_eq' (Finset.range (m + 1)) i]
  simp

theorem natDegree_polMap_le (ψ : E →+ E) (m : ℕ) (Q : E[X]) : (polMap ψ m Q).natDegree ≤ m := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro i hi
  rw [coeff_polMap, if_neg (by omega)]

variable (k : Subfield E)

theorem coeff_mem_mul {S T : PowerSeries E} (hS : ∀ n, PowerSeries.coeff n S ∈ k)
    (hT : ∀ n, PowerSeries.coeff n T ∈ k) : ∀ n, PowerSeries.coeff n (S * T) ∈ k := by
  intro n
  rw [PowerSeries.coeff_mul]
  exact sum_mem fun p _ => mul_mem (hS _) (hT _)

theorem coeff_mem_one : ∀ n, PowerSeries.coeff n (1 : PowerSeries E) ∈ k := by
  intro n
  rw [PowerSeries.coeff_one]
  split_ifs
  · exact one_mem k
  · exact zero_mem k

theorem coeff_mem_pow {S : PowerSeries E} (hS : ∀ n, PowerSeries.coeff n S ∈ k) (i : ℕ) :
    ∀ n, PowerSeries.coeff n (S ^ i) ∈ k := by
  induction i with
  | zero => simpa using coeff_mem_one k
  | succ i ih => rw [pow_succ]; exact coeff_mem_mul k ih hS

theorem coeff_mem_X : ∀ n, PowerSeries.coeff n (PowerSeries.X : PowerSeries E) ∈ k := by
  intro n
  rw [PowerSeries.coeff_X]
  split_ifs
  · exact one_mem k
  · exact zero_mem k

variable {k}

theorem serMap_mul (ψ : E →+ E) (hψ : ∀ c ∈ k, ∀ x, ψ (c * x) = c * ψ x) {W : PowerSeries E}
    (hW : ∀ n, PowerSeries.coeff n W ∈ k) (S : PowerSeries E) :
    serMap ψ (W * S) = W * serMap ψ S := by
  ext n

  rw [coeff_serMap, PowerSeries.coeff_mul, PowerSeries.coeff_mul, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [hψ _ (hW _), coeff_serMap]

theorem serMap_C (ψ : E →+ E) (q : E) : serMap ψ (PowerSeries.C q) = PowerSeries.C (ψ q) := by
  ext n
  rw [coeff_serMap, PowerSeries.coeff_C, PowerSeries.coeff_C]
  split_ifs
  · rfl
  · exact map_zero ψ

theorem serMap_homS (ψ : E →+ E) (hψ : ∀ c ∈ k, ∀ x, ψ (c * x) = c * ψ x) {U : PowerSeries E}
    (hU : ∀ n, PowerSeries.coeff n U ∈ k) (m : ℕ) (Q : E[X]) :
    serMap ψ (homS U m Q) = homS U m (polMap ψ m Q) := by
  unfold homS
  rw [serMap_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hW : ∀ n, PowerSeries.coeff n (U ^ i * PowerSeries.X ^ (2 * (m - i))) ∈ k :=
    coeff_mem_mul k (coeff_mem_pow k hU i) (coeff_mem_pow k (coeff_mem_X k) _)
  rw [coeff_polMap, if_pos hi', mul_assoc, mul_assoc, mul_comm (PowerSeries.C (Q.coeff i)),
    serMap_mul ψ hψ hW, serMap_C, mul_comm]

theorem exists_proj (k : Subfield E) : ∃ ψ : E →+ E, (∀ c ∈ k, ∀ x, ψ (c * x) = c * ψ x) ∧
    (∀ x, ψ x ∈ k) ∧ ψ 1 = 1 := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap k E)
    (LinearMap.ker_eq_bot.mpr (algebraMap k E).injective)
  refine ⟨(k.subtype : k →+ E).comp g.toAddMonoidHom, ?_, ?_, ?_⟩
  · intro c hc x
    have := g.map_smul (⟨c, hc⟩ : k) x
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe]
    have h2 : (⟨c, hc⟩ : k) • x = c * x := rfl
    rw [← h2, this]
    rfl
  · intro x
    exact (g x).2
  · have := LinearMap.congr_fun hg 1
    simp only [LinearMap.comp_apply, Algebra.linearMap_apply, map_one, LinearMap.id_apply] at this
    simp [this]

end Proj

theorem proj_trick {E : Type} [Field E] (k : Subfield E) (U V : PowerSeries E)
    (hU : ∀ n, PowerSeries.coeff n U ∈ k) (hV : ∀ n, PowerSeries.coeff n V ∈ k)
    (hU0 : PowerSeries.constantCoeff U = 1) (A B : E[X]) (N : ℕ) (hA : A.natDegree ≤ N + 1)
    (hB : B.Monic) (hBd : B.natDegree = N) (hc : IsCoprime A B)
    (h : V * homS U N B = homS U (N + 1) A) : ∀ i, B.coeff i ∈ k := by
  obtain ⟨ψ, hψ, hψk, hψ1⟩ := exists_proj k
  set A' := polMap ψ (N + 1) A with hA'
  set B' := polMap ψ N B with hB'
  have hA'd : A'.natDegree ≤ N + 1 := natDegree_polMap_le ψ _ A
  have hB'd : B'.natDegree ≤ N := natDegree_polMap_le ψ _ B
  have h' : V * homS U N B' = homS U (N + 1) A' := by
    rw [hA', hB', ← serMap_homS ψ hψ hU, ← serMap_homS ψ hψ hU, ← serMap_mul ψ hψ hV, h]
  have hBN : B'.coeff N = 1 := by
    rw [hB', coeff_polMap, if_pos le_rfl, ← hBd, hB.coeff_natDegree, hψ1]
  have hB'deg : B'.natDegree = N := by
    refine le_antisymm hB'd (le_natDegree_of_ne_zero ?_)
    rw [hBN]; exact one_ne_zero
  have hB'm : B'.Monic := by
    rw [Monic, leadingCoeff, hB'deg, hBN]
  have hcross : A * B' = A' * B := by
    have h0 : homS U (N + 1 + N) (A * B' - A' * B) = 0 := by
      rw [homS_sub, homS_mul U _ _ _ _ hA hB'd, homS_mul U _ _ _ _ hA'd hBd.le, ← h, ← h']
      ring
    have hdeg : (A * B' - A' * B).natDegree ≤ N + 1 + N := by
      refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · exact natDegree_mul_le.trans (add_le_add hA hB'd)
      · exact natDegree_mul_le.trans (add_le_add hA'd hBd.le)
    exact sub_eq_zero.mp (homS_eq_zero U hU0 _ _ hdeg h0)
  have hdvd : B ∣ B' := by
    refine hc.symm.dvd_of_dvd_mul_left ?_
    rw [hcross]
    exact dvd_mul_left _ _
  have heq : B = B' :=
    (eq_of_monic_of_dvd_of_natDegree_le hB hB'm hdvd (by rw [hB'deg, hBd])).symm
  intro i
  rw [heq, hB', coeff_polMap]
  split_ifs
  · exact hψk _
  · exact zero_mem k

end ReciprocityTheory.ChartRestriction.L1
end
end

section

noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField

namespace ReciprocityTheory.ChartRestriction.L1

theorem sqD_indep {d : ℕ} (hd : 0 < d) (u v : ℚ) (h : (u : ℂ) + v * sqD d = 0) : u = 0 ∧ v = 0 := by
  have hs : Real.sqrt d ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hd)).ne'
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [sqD] at hre him
  exact ⟨hre, him.resolve_right (by
    intro h0
    apply hs
    simpa using h0)⟩

theorem sqK_li {d : ℕ} (hd : 0 < d) : LinearIndependent ℚ ![(1 : KQ d), sqK d] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  apply sqD_indep hd
  have := congrArg (fun z : KQ d => (z : ℂ)) h
  simpa [sqK, Algebra.smul_def] using this

theorem sqK_decomp {d : ℕ} (z : KQ d) (p q : ℚ) (h : (z : ℂ) = p + q * sqD d) :
    z = p • (1 : KQ d) + q • sqK d := by
  apply Subtype.ext
  simp [sqK, Algebra.smul_def, h]

theorem sqK_span {d : ℕ} : ⊤ ≤ Submodule.span ℚ (Set.range ![(1 : KQ d), sqK d]) := by
  intro z _
  obtain ⟨u, v, h⟩ := (KQ_mem_iff d z).1 z.2
  rw [sqK_decomp z u v h]
  refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))

def bKQ {d : ℕ} (hd : 0 < d) : Module.Basis (Fin 2) ℚ (KQ d) := Module.Basis.mk (sqK_li hd) sqK_span

theorem sqK_mul_self (d : ℕ) : sqK d * sqK d = -(d : KQ d) := by
  apply Subtype.ext
  have := sqD_sq d
  simp [sqK, ← this, sq]

theorem norm_KQ {d : ℕ} (hd : 0 < d) (z : KQ d) (p q : ℚ) (h : (z : ℂ) = p + q * sqD d) :
    Algebra.norm ℚ z = p ^ 2 + d * q ^ 2 := by
  have h0 : bKQ hd 0 = 1 := by simp [bKQ]
  have h1 : bKQ hd 1 = sqK d := by simp [bKQ]
  have hz := sqK_decomp z p q h
  have e0 : z * bKQ hd 0 = p • bKQ hd 0 + q • bKQ hd 1 := by
    rw [h0, h1, mul_one]; exact hz
  have e1 : z * bKQ hd 1 = (-(d : ℚ) * q) • bKQ hd 0 + p • bKQ hd 1 := by
    rw [h0, h1, hz, add_mul, smul_mul_assoc, smul_mul_assoc, sqK_mul_self, one_mul]
    simp only [Algebra.smul_def, mul_one]
    push_cast
    ring
  rw [Algebra.norm_eq_matrix_det (bKQ hd), Matrix.det_fin_two]
  simp only [Algebra.leftMulMatrix_eq_repr_mul, e0, e1, map_add (f := _), map_smul, Module.Basis.repr_self]
  simp
  ring

theorem absNorm_span {d : ℕ} (hsf : Squarefree d) (hd : d % 4 = 3) (x : 𝓞 (KQ d)) (a b : ℤ)
    (h : (((x : KQ d) : ℂ)) = a + b * omegaK d) :
    4 * (Ideal.absNorm (Ideal.span {x}) : ℤ) = 4 * a ^ 2 + 4 * a * b + b ^ 2 * (1 + d) := by
  have hd0 : 0 < d := by omega
  have hn := norm_KQ hd0 (x : KQ d) (a + b / 2) (b / 2) (by
    rw [h]; simp only [omegaK, sqD]; push_cast; ring)
  rw [← Algebra.coe_norm_int] at hn
  have hn' : 4 * Algebra.norm ℤ x = 4 * a ^ 2 + 4 * a * b + b ^ 2 * (1 + d) := by
    have : (4 : ℚ) * (Algebra.norm ℤ x : ℚ) = 4 * a ^ 2 + 4 * a * b + b ^ 2 * (1 + d) := by
      rw [hn]; ring
    exact_mod_cast this
  have hpos : 0 ≤ Algebra.norm ℤ x := by
    have : 0 ≤ 4 * Algebra.norm ℤ x := by
      rw [hn']
      have : 4 * a ^ 2 + 4 * a * b + b ^ 2 * (1 + (d : ℤ)) = (2 * a + b) ^ 2 + d * b ^ 2 := by ring
      rw [this]; positivity
    omega
  rw [Ideal.absNorm_span_singleton, Int.natAbs_of_nonneg hpos, hn']

theorem princ_form {d : ℕ} (hsf : Squarefree d) (hd : d % 4 = 3) (v : HeightOneSpectrum (𝓞 (KQ d)))
    (hv : ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩ = 1) :
    ∃ a b : ℤ, 4 * (Nat.card (𝓞 (KQ d) ⧸ v.asIdeal) : ℤ) = 4 * a ^ 2 + 4 * a * b + b ^ 2 * (1 + d) := by
  rw [ClassGroup.mk0_eq_one_iff] at hv
  obtain ⟨x, hx⟩ := hv.principal
  obtain ⟨a, b, hab⟩ := quadInt hsf hd x
  refine ⟨a, b, ?_⟩
  rw [← absNorm_span hsf hd x a b hab, Ideal.absNorm_apply, Submodule.cardQuot_apply, hx]

end ReciprocityTheory.ChartRestriction.L1
end
end
