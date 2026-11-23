module

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NonzeroDiscriminants.DiscMain
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.NumberTheory.Padics.Complex
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Formalism.FormalGroupLog.FormalGroupLogProofs.ChainRule
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle005
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle007
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle004
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModEvalSer
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle006
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle003
import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
import Formalism.TorsionNormIteration.InvIntegralOfClass
import Mathlib.RingTheory.PowerSeries.Basic

@[expose] public section

section

noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

def latMap {L : PeriodPair} {c : ℂ} {τ : ℍ} (h : IsTauOf L c τ) (v : Fin 2 → ℤ) : L.lattice :=
  ⟨c * ((v 0 : ℂ) * (τ : ℂ) + (v 1 : ℂ)), (h.2 _).2 ⟨v 0, v 1, rfl⟩⟩

theorem latMap_bijective {L : PeriodPair} {c : ℂ} {τ : ℍ} (h : IsTauOf L c τ) :
    Function.Bijective (latMap h) := by
  constructor
  · intro v w hvw
    have h1 : c * ((v 0 : ℂ) * (τ : ℂ) + (v 1 : ℂ)) = c * ((w 0 : ℂ) * (τ : ℂ) + (w 1 : ℂ)) :=
      congrArg Subtype.val hvw
    have h2 := mul_left_cancel₀ h.1 h1
    have him := congrArg Complex.im h2
    have hre := congrArg Complex.re h2
    simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul,
      add_zero, Complex.add_re, Complex.mul_re, sub_zero] at him hre
    have hτ : (τ : ℂ).im ≠ 0 := τ.im_ne_zero
    have h0 : (v 0 : ℝ) = w 0 := mul_right_cancel₀ hτ him
    rw [h0] at hre
    have h1' : (v 1 : ℝ) = w 1 := add_left_cancel hre
    funext i
    fin_cases i
    · exact_mod_cast h0
    · exact_mod_cast h1'
  · rintro ⟨x, hx⟩
    obtain ⟨u, v, rfl⟩ := (h.2 x).1 hx
    exact ⟨![u, v], by simp [latMap]⟩

theorem G_eq {L : PeriodPair} {c : ℂ} {τ : ℍ} (h : IsTauOf L c τ) {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) :
    L.G k = (c ^ k)⁻¹ * (2 * riemannZeta k) * E hk τ := by
  have hE : E hk τ = (1 / 2 : ℂ) * eisensteinSeries (N := 1) 0 k τ := by
    rw [show E hk τ = (1 / 2 : ℂ) • eisensteinSeriesSIF (N := 1) 0 k τ from rfl,
      eisensteinSeriesSIF_apply 0 k τ, smul_eq_mul]
  have H := tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries hk τ
  have h1 : L.G k = ∑' v : Fin 2 → ℤ, (c ^ k)⁻¹ * eisSummand k v τ := by
    rw [PeriodPair.G, ← (Equiv.ofBijective _ (latMap_bijective h)).tsum_eq]
    refine tsum_congr fun v => ?_
    simp [latMap, eisSummand, mul_pow, mul_comm]
  rw [h1, tsum_mul_left, H, hE]
  ring

theorem sixVal : riemannZeta 6 = (Real.pi : ℂ) ^ 6 / 945 := by
  apply DiscrNeWork.zeta6 <;> assumption

theorem g₂_eq {L : PeriodPair} {c : ℂ} {τ : ℍ} (h : IsTauOf L c τ) :
    L.g₂ = (c ^ 4)⁻¹ * (4 * (Real.pi : ℂ) ^ 4 / 3) * E₄ τ := by
  rw [PeriodPair.g₂, G_eq h (k := 4) (by norm_num) ⟨2, rfl⟩,
    show ((4 : ℕ) : ℂ) = 4 by norm_num, riemannZeta_four]
  have hE : E (k := 4) (by norm_num) τ = E₄ τ := rfl
  rw [hE]
  ring

theorem g₃_eq {L : PeriodPair} {c : ℂ} {τ : ℍ} (h : IsTauOf L c τ) :
    L.g₃ = (c ^ 6)⁻¹ * (8 * (Real.pi : ℂ) ^ 6 / 27) * E₆ τ := by
  rw [PeriodPair.g₃, G_eq h (k := 6) (by norm_num) ⟨3, rfl⟩,
    show ((6 : ℕ) : ℂ) = 6 by norm_num, sixVal]
  have hE : E (k := 6) (by norm_num) τ = E₆ τ := rfl
  rw [hE]
  ring

end ReciprocityTheory.ChartRestriction.L1
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
open Formalism.L2.Th1

structure LatModel (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (g2 g3 : ℂ_[l]) :
    Prop where
  eq2 : g2 = ι L.g₂
  eq3 : g3 = ι L.g₃
  n2 : ‖g2‖ ≤ 1
  n3 : ‖g3‖ ≤ 1

end ReciprocityTheory.ChartRestriction.L1
end
end

section

noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem zetaRoot_mem_cyclotomicSubring_self (m : ℕ) : zetaC m ∈ Rm m := by
  exact Subring.subset_closure (Set.mem_singleton _)

theorem zetaRoot_ne_zero (e : ℕ) : zetaC e ≠ 0 := by
  exact Complex.exp_ne_zero _

private theorem dvd_and_eq_div_of_mem_Tm {m : ℕ} (hm : 0 < m) {t : ℕ × ℕ × ℕ} (ht : t ∈ Tm m) :
    t.1 ∣ m ∧ 0 < t.1 ∧ t.2.2 = m / t.1 ∧ t.1 * t.2.2 = m := by
  simp only [Tm, Finset.mem_image, Finset.mem_sigma, Nat.mem_divisors, Finset.mem_range] at ht
  obtain ⟨⟨a, b⟩, ⟨⟨hdvd, _⟩, _⟩, rfl⟩ := ht
  exact ⟨hdvd, Nat.pos_of_dvd_of_pos hdvd hm, rfl, Nat.mul_div_cancel' hdvd⟩

private theorem zetaC_div_eq_pow_of_dvd {m a : ℕ} (hm : 0 < m) (ha : a ∣ m) : zetaC (m / a) = zetaC m ^ a := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_dvd_iff] at ha
    omega
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha0
  unfold zetaC
  rw [← Complex.exp_nat_mul, Nat.cast_div ha ha']
  congr 1
  field_simp

theorem zetaRoot_pow_mem_of_mem_hermiteTriples {m : ℕ} (hm : 0 < m) {t : ℕ × ℕ × ℕ} (ht : t ∈ Tm m) :
    zetaC t.2.2 ^ t.2.1 ∈ Rm m ∧ (zetaC t.2.2 ^ t.2.1)⁻¹ ∈ Rm m := by
  obtain ⟨hdvd, _, he, _⟩ := dvd_and_eq_div_of_mem_Tm hm ht
  have hz : zetaC t.2.2 ^ t.2.1 = zetaC m ^ (t.1 * t.2.1) := by
    rw [he, zetaC_div_eq_pow_of_dvd hm hdvd, pow_mul]
  have hzm : zetaC m ^ m = 1 := by
    unfold zetaC
    rw [← Complex.exp_nat_mul]
    have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    rw [show (m : ℂ) * (2 * Real.pi * Complex.I / m) = 2 * Real.pi * Complex.I by field_simp]
    exact Complex.exp_two_pi_mul_I
  have hinv : (zetaC m)⁻¹ = zetaC m ^ (m - 1) := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_succ', Nat.sub_add_cancel hm, hzm]
  rw [hz]
  constructor
  · exact pow_mem (zetaRoot_mem_cyclotomicSubring_self m) _
  · rw [← inv_pow, hinv, ← pow_mul]
    exact pow_mem (zetaRoot_mem_cyclotomicSubring_self m) _

theorem norm_zetaRoot_pow_of_mem_hermiteTriples {m : ℕ} (hm : 0 < m) {t : ℕ × ℕ × ℕ} (ht : t ∈ Tm m) :
    ‖zetaC t.2.2 ^ t.2.1‖ = 1 := by
  rw [norm_pow, zetaC, Complex.norm_exp]
  simp

theorem convergesOnDisk_eisensteinFourCubeSeries : Conv aC := by
  rw [aC_eq]
  exact isMF_AA.conv

theorem convergesOnDisk_discriminantSeries : Conv dC := by
  rw [dC_eq]
  exact isMF_DD.conv

theorem evalSeries_eisensteinFourCubeSeries (τ : ℍ) : ev aC (qm 1 τ) = AA τ := by
  rw [aC_eq]
  exact isMF_AA.ev_eq τ

theorem evalSeries_discriminantSeries (τ : ℍ) : ev dC (qm 1 τ) = DD τ := by
  rw [dC_eq]
  exact isMF_DD.ev_eq τ

theorem eisensteinFourCubeSeries_coeff_zero : PowerSeries.coeff 0 aC = 1 := by
  rw [aC, PowerSeries.coeff_map, aZ, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, e4Z]
  simp

theorem discriminantSeries_coeff_zero : PowerSeries.coeff 0 dC = 0 := by
  rw [dC, PowerSeries.coeff_map, dZ_coeff_zero]
  simp

theorem discriminantSeries_coeff_one : PowerSeries.coeff 1 dC = 1 := by
  rw [dC, PowerSeries.coeff_map, dZ_coeff_one]
  simp

theorem facSer_coeffIn {m : ℕ} (hm : 0 < m) {t : ℕ × ℕ × ℕ} (ht : t ∈ Tm m) :
    CoeffIn (Rm m) (facSer m t) := by
  obtain ⟨hc, _⟩ := zetaRoot_pow_mem_of_mem_hermiteTriples hm ht
  have hA : CoeffIn (Rm m) aC := CoeffIn.map_int _ _
  have hD : CoeffIn (Rm m) dC := CoeffIn.map_int _ _
  unfold facSer
  exact ((hA.xp m).mul (hD.sub1 hc _)).sub ((hA.sub1 hc _).mul (hD.xp m))

theorem facSer_conv {m : ℕ} (hm : 0 < m) {t : ℕ × ℕ × ℕ} (ht : t ∈ Tm m) : Conv (facSer m t) := by
  have hc : ‖zetaC t.2.2 ^ t.2.1‖ ≤ 1 := (norm_zetaRoot_pow_of_mem_hermiteTriples hm ht).le
  have hk : t.1 ^ 2 ≠ 0 := pow_ne_zero _ (dvd_and_eq_div_of_mem_Tm hm ht).2.1.ne'
  unfold facSer
  exact ((convergesOnDisk_eisensteinFourCubeSeries.xp hm.ne').mul (convergesOnDisk_discriminantSeries.sub1 hc hk)).sub
    ((convergesOnDisk_eisensteinFourCubeSeries.sub1 hc hk).mul (convergesOnDisk_discriminantSeries.xp hm.ne'))

theorem facSer_ev {m : ℕ} (hm : 0 < m) {t : ℕ × ℕ × ℕ} (ht : t ∈ Tm m) (τ : ℍ) :
    ev (facSer m t) (qm m τ) = fac t τ := by
  obtain ⟨hdvd, ha0, he, hae⟩ := dvd_and_eq_div_of_mem_Tm hm ht
  have he0 : 0 < t.2.2 := by
    rw [he]
    exact Nat.div_pos (Nat.le_of_dvd hm hdvd) ha0
  have hq := qm_norm_lt_one hm τ
  have hc := (norm_zetaRoot_pow_of_mem_hermiteTriples hm ht).le
  have hk : t.1 ^ 2 ≠ 0 := pow_ne_zero _ ha0.ne'
  have hA := convergesOnDisk_eisensteinFourCubeSeries
  have hD := convergesOnDisk_discriminantSeries
  have hpt : zetaC t.2.2 ^ t.2.1 * qm m τ ^ (t.1 ^ 2) = qm 1 (pt t.1 t.2.1 t.2.2 τ) := by
    rw [qm_pt ha0 he0, hae]
  unfold facSer fac
  rw [ev_sub ((hA.xp hm.ne').mul (hD.sub1 hc hk)) ((hA.sub1 hc hk).mul (hD.xp hm.ne')) hq,
    ev_mul (hA.xp hm.ne') (hD.sub1 hc hk) hq, ev_mul (hA.sub1 hc hk) (hD.xp hm.ne') hq,
    ev_xp _ hm.ne', ev_xp _ hm.ne', evalSeries_rescaleExpand _ _ hk, evalSeries_rescaleExpand _ _ hk, qm_pow hm, hpt]
  simp only [evalSeries_eisensteinFourCubeSeries, evalSeries_discriminantSeries]

theorem LowUnit.facSub_left {R : Subring ℂ} {f g : PowerSeries ℂ} {n n' : ℕ} {u u' : ℂ}
    (hf : LowUnit R f n u) (hg : LowUnit R g n' u') (h : n < n') : LowUnit R (f - g) n u := by
  obtain ⟨hu, hui, hu0, hlow, hval⟩ := hf
  obtain ⟨_, _, _, hglow, _⟩ := hg
  refine ⟨hu, hui, hu0, fun k hk => ?_, ?_⟩
  · rw [map_sub, hlow k hk, hglow k (hk.trans h), sub_zero]
  · rw [map_sub, hval, hglow n h, sub_zero]

theorem LowUnit.facSub_right {R : Subring ℂ} {f g : PowerSeries ℂ} {n n' : ℕ} {u u' : ℂ}
    (hf : LowUnit R f n u) (hg : LowUnit R g n' u') (h : n' < n) : LowUnit R (f - g) n' (-u') := by
  obtain ⟨_, _, _, hflow, _⟩ := hf
  obtain ⟨hu, hui, hu0, hglow, hval⟩ := hg
  refine ⟨neg_mem hu, by rw [inv_neg]; exact neg_mem hui, neg_ne_zero.2 hu0, fun k hk => ?_, ?_⟩
  · rw [map_sub, hflow k (hk.trans h), hglow k hk, sub_zero]
  · rw [map_sub, hflow n' h, hval, zero_sub]

theorem hasUnitLeadingCoeff_rescaleExpand_eisensteinFourCubeSeries (R : Subring ℂ) (c : ℂ) {k : ℕ} (hk : k ≠ 0) :
    LowUnit R (sub1 c k aC) 0 1 := by
  refine ⟨one_mem R, by rw [inv_one]; exact one_mem R, one_ne_zero,
    fun n hn => absurd hn (Nat.not_lt_zero n), ?_⟩
  rw [sub1, coeff_xp, if_pos (dvd_zero k), Nat.zero_div, PowerSeries.coeff_rescale, pow_zero, one_mul,
    eisensteinFourCubeSeries_coeff_zero]

theorem hasUnitLeadingCoeff_rescaleExpand_discriminantSeries {R : Subring ℂ} {c : ℂ} (hc : c ∈ R) (hc' : c⁻¹ ∈ R) (hc0 : c ≠ 0) {k : ℕ}
    (hk : k ≠ 0) : LowUnit R (sub1 c k dC) k c := by
  refine ⟨hc, hc', hc0, fun n hn => ?_, ?_⟩
  · rw [sub1, coeff_xp]
    split_ifs with hd
    · have h0 : n = 0 := Nat.eq_zero_of_dvd_of_lt hd hn
      subst h0
      rw [Nat.zero_div, PowerSeries.coeff_rescale, discriminantSeries_coeff_zero, mul_zero]
    · rfl
  · rw [sub1, coeff_xp, if_pos dvd_rfl, Nat.div_self (Nat.pos_of_ne_zero hk), PowerSeries.coeff_rescale,
      pow_one, discriminantSeries_coeff_one, mul_one]

theorem rescaleExpand_one (k : ℕ) (f : PowerSeries ℂ) : sub1 1 k f = xp k f := by
  simp [sub1, PowerSeries.rescale_one]

theorem facSer_low {m : ℕ} (hm : 0 < m) {t : ℕ × ℕ × ℕ} (ht : t ∈ Tm m) (hne : t.1 ≠ t.2.2) :
    ∃ n0 u, LowUnit (Rm m) (facSer m t) n0 u := by
  obtain ⟨hdvd, ha0, he, hae⟩ := dvd_and_eq_div_of_mem_Tm hm ht
  obtain ⟨hc, hci⟩ := zetaRoot_pow_mem_of_mem_hermiteTriples hm ht
  have hc0 : zetaC t.2.2 ^ t.2.1 ≠ 0 := pow_ne_zero _ (zetaRoot_ne_zero _)
  have hk : t.1 ^ 2 ≠ 0 := pow_ne_zero _ ha0.ne'
  have hxa : LowUnit (Rm m) (xp m aC) 0 1 := by
    rw [← rescaleExpand_one]
    exact hasUnitLeadingCoeff_rescaleExpand_eisensteinFourCubeSeries _ 1 hm.ne'
  have hxd : LowUnit (Rm m) (xp m dC) m 1 := by
    rw [← rescaleExpand_one]
    exact hasUnitLeadingCoeff_rescaleExpand_discriminantSeries (one_mem _) (by rw [inv_one]; exact one_mem _) one_ne_zero hm.ne'
  have h1 := hxa.mul (hasUnitLeadingCoeff_rescaleExpand_discriminantSeries hc hci hc0 hk)
  have h2 := (hasUnitLeadingCoeff_rescaleExpand_eisensteinFourCubeSeries (Rm m) (zetaC t.2.2 ^ t.2.1) hk).mul hxd
  simp only [zero_add, one_mul] at h1 h2
  unfold facSer
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact ⟨_, _, h1.facSub_left h2 (by rw [← hae]; nlinarith)⟩
  · exact ⟨_, _, h1.facSub_right h2 (by rw [← hae]; nlinarith)⟩

end ReciprocityTheory.ChartRestriction.L1
end
end

section

noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem Gm_smul {m : ℕ} (hm : 0 < m) (γ : SL(2, ℤ)) (τ : ℍ) :
    Gm m (γ • τ) = denom γ τ ^ (24 * (Tm m).card) * Gm m τ := by
  classical
  have hex : ∀ t ∈ Tm m, ∃ (γ' : SL(2, ℤ)) (t' : ℕ × ℕ × ℕ), t' ∈ Tm m ∧
      Tmat t * (γ : Matrix (Fin 2) (Fin 2) ℤ) = (γ' : Matrix (Fin 2) (Fin 2) ℤ) * Tmat t' := by
    intro t ht
    apply hnf_exists hm
    rw [Matrix.det_mul, perm_Tmat_det hm ht, Matrix.SpecialLinearGroup.det_coe, mul_one]
  choose! g σ hσ hg using hex
  have hinvR : ∀ A : SL(2, ℤ),
      (A : Matrix (Fin 2) (Fin 2) ℤ) * ((A⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
    intro A
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hinvL : ∀ A : SL(2, ℤ),
      ((A⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (A : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
    intro A
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hinj : Set.InjOn σ (Tm m) := by
    intro t1 h1 t2 h2 he
    have e1 := hg t1 h1
    have e2 := hg t2 h2
    rw [← he] at e2
    have key : Tmat t1 * (γ : Matrix (Fin 2) (Fin 2) ℤ) =
        ((g t1 * (g t2)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
          (Tmat t2 * (γ : Matrix (Fin 2) (Fin 2) ℤ)) := by
      rw [e1, e2, Matrix.SpecialLinearGroup.coe_mul, ← mul_assoc, mul_assoc (g t1 : Matrix (Fin 2) (Fin 2) ℤ),
        hinvL, mul_one]
    apply hnf_unique hm h1 h2 (g t1 * (g t2)⁻¹)
    calc Tmat t1 = Tmat t1 * (γ : Matrix (Fin 2) (Fin 2) ℤ) * ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
          rw [mul_assoc, hinvR, mul_one]
      _ = ((g t1 * (g t2)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * Tmat t2 *
            (γ : Matrix (Fin 2) (Fin 2) ℤ) * ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
          rw [key]; simp only [mul_assoc]
      _ = ((g t1 * (g t2)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * Tmat t2 := by
          rw [mul_assoc _ (γ : Matrix (Fin 2) (Fin 2) ℤ), hinvR, mul_one]
  have himg : (Tm m).image σ = Tm m := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
      exact hσ t ht
    · rw [Finset.card_image_of_injOn hinj]
  have hprod : ∀ F : ℕ × ℕ × ℕ → ℂ, ∏ t ∈ Tm m, F (σ t) = ∏ t ∈ Tm m, F t := by
    intro F
    conv_rhs => rw [← himg]
    rw [Finset.prod_image hinj]
  have hfac : ∏ t ∈ Tm m, fac (σ t) τ = ∏ t ∈ Tm m, fac t τ := hprod (fun t => fac t τ)
  have hden : ∏ t ∈ Tm m, ((σ t).2.2 : ℂ) = ∏ t ∈ Tm m, (t.2.2 : ℂ) := hprod (fun t => (t.2.2 : ℂ))
  have hne : ∏ t ∈ Tm m, (t.2.2 : ℂ) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro t ht
    exact_mod_cast (Tm_pos hm ht).2.ne'
  have hstep : ∏ t ∈ Tm m, fac t (γ • τ) =
      ∏ t ∈ Tm m, (denom γ τ ^ 24 * ((t.2.2 : ℂ) / (σ t).2.2) ^ 12 * fac (σ t) τ) :=
    Finset.prod_congr rfl (fun t ht => fac_smul (Tm_pos hm ht) (Tm_pos hm (hσ t ht)) γ (g t) (hg t ht) τ)
  unfold Gm
  rw [hstep, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, ← pow_mul, hfac,
    Finset.prod_pow, Finset.prod_div_distrib, hden, div_self hne, one_pow, mul_one]

end ReciprocityTheory.ChartRestriction.L1
end
end
