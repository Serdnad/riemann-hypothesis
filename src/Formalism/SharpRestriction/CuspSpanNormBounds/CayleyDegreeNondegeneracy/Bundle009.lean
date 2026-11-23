module

public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsDeg
import Formalism.FlagUnipotentLattices.CardSubgroupsOfIndexLe
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.Bundle008
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsRpowPow
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticeCounting Formalism.MainNotions.BridgeLemma

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section KB

variable {D : D7} {large₂ : SizeData₂ D} {X : TermTie D} {u u' : D.what₂.Word} {C1 : ℝ} (Y : LoopTie D large₂ X u u' C1)

theorem rows_HHZ_eq (D : D7) (large₂ : SizeData₂ D) (c : ℝ) (Z : GramM D) :
    HHZ D large₂.sc.b c Z = large₂.sc.b ^ (c ^ 2 * (D.R.m : ℝ) ^ 3 * D.R.f) * sizeZ D large₂.sc.b c Z ^ 4 := by
  have hb0 : 0 < large₂.sc.b := by linarith [d_two_le_b D large₂]
  unfold HHZ
  rw [← Real.rpow_mul hb0.le]
  congr 2
  ring

theorem rows_bpow_le_HHZ (D : D7) (large₂ : SizeData₂ D) {c E : ℝ} (hE : E ≤ c ^ 2 * (D.R.m : ℝ) ^ 3 * D.R.f) (Z : GramM D) :
    large₂.sc.b ^ E ≤ HHZ D large₂.sc.b c Z := by
  have hb := d_two_le_b D large₂
  rw [rows_HHZ_eq]
  have h2 : 1 ≤ sizeZ D large₂.sc.b c Z ^ 4 := one_le_pow₀ (rows_one_le_sizeZ _ _ _)
  calc large₂.sc.b ^ E ≤ large₂.sc.b ^ (c ^ 2 * (D.R.m : ℝ) ^ 3 * D.R.f) := Real.rpow_le_rpow_of_exponent_le (by linarith) hE
    _ = large₂.sc.b ^ (c ^ 2 * (D.R.m : ℝ) ^ 3 * D.R.f) * 1 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by positivity)

theorem rows_Dr_le_HHZ (D : D7) (large₂ : SizeData₂ D) (hrd : 0 < D.host.rdE) (hr : 1 ≤ D.R.rS) {c : ℝ} (hc1 : 1 ≤ c) (Z : GramM D) :
    ∏ τ, max 1 (absDl D Z D.R.rS τ ^ 2) ≤ HHZ D large₂.sc.b c Z := by
  have hb := d_two_le_b D large₂
  have hb0 : 0 < large₂.sc.b := by linarith
  set H2 : ℝ := large₂.sc.b ^ (c * (D.R.m : ℝ) ^ 2) with hH2
  have hH21 : 1 ≤ H2 := Real.one_le_rpow (by linarith) (by positivity)
  have hm2 : (2 : ℝ) ≤ D.R.m := by
    rw [rows_m_cast]; have : (0 : ℝ) ≤ D.R.rS := by positivity
    linarith
  have each : ∀ τ, max 1 (absDl D Z D.R.rS τ ^ 2) ≤ (H2 * max 1 (absDl D Z D.R.rS τ / H2)) ^ 2 := by
    intro τ
    have hD0 := rows_absDl_nonneg hrd Z D.R.rS τ
    have a1 : 1 ≤ H2 * max 1 (absDl D Z D.R.rS τ / H2) := one_le_mul_of_one_le_of_one_le hH21 (le_max_left _ _)
    have a2 : absDl D Z D.R.rS τ ≤ H2 * max 1 (absDl D Z D.R.rS τ / H2) := by
      calc absDl D Z D.R.rS τ = H2 * (absDl D Z D.R.rS τ / H2) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_right _ _) (by linarith)
    exact max_le (one_le_pow₀ a1) (pow_le_pow_left₀ hD0 a2 2)
  have single : ∀ τ, max 1 (absDl D Z D.R.rS τ / H2) ≤
      ∏ l ∈ Finset.Icc 1 (D.R.rS + 1), max 1 (absDl D Z l τ / H2) := by
    intro τ
    have hmem : D.R.rS ∈ Finset.Icc 1 (D.R.rS + 1) := Finset.mem_Icc.2 ⟨hr, Nat.le_succ _⟩
    rw [← Finset.mul_prod_erase _ _ hmem]
    exact le_mul_of_one_le_right (le_trans zero_le_one (le_max_left _ _))
      (rows_one_le_prod _ _ fun l _ => le_max_left _ _)
  have hs1 := rows_one_le_sizeZ (D := D) large₂.sc.b c Z
  calc ∏ τ, max 1 (absDl D Z D.R.rS τ ^ 2)
      ≤ ∏ τ : D.what₂.Tau, (H2 * max 1 (absDl D Z D.R.rS τ / H2)) ^ 2 :=
        Finset.prod_le_prod₀ (fun τ _ => le_trans zero_le_one (le_max_left _ _)) fun τ _ => each τ
    _ = (H2 ^ D.R.f * ∏ τ : D.what₂.Tau, max 1 (absDl D Z D.R.rS τ / H2)) ^ 2 := by
        rw [Finset.prod_pow, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, D.what₂.card_Tau]
    _ ≤ (H2 ^ D.R.f * sizeZ D large₂.sc.b c Z) ^ 2 := by
        apply pow_le_pow_left₀ (mul_nonneg (by positivity)
          (Finset.prod_nonneg fun τ _ => le_trans zero_le_one (le_max_left _ _)))
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        unfold sizeZ
        exact Finset.prod_le_prod₀ (fun τ _ => le_trans zero_le_one (le_max_left _ _)) fun τ _ => single τ
    _ = (H2 ^ D.R.f) ^ 2 * sizeZ D large₂.sc.b c Z ^ 2 := by ring
    _ ≤ large₂.sc.b ^ (c ^ 2 * (D.R.m : ℝ) ^ 3 * D.R.f) * sizeZ D large₂.sc.b c Z ^ 4 := by
        apply mul_le_mul _ (pow_le_pow_right₀ hs1 (by norm_num)) (by positivity) (by positivity)
        rw [hH2, rows_rpow_pow hb0, rows_rpow_pow hb0]
        apply Real.rpow_le_rpow_of_exponent_le (by linarith)
        push_cast
        have h0 : 0 ≤ c * (D.R.m : ℝ) ^ 2 * D.R.f := by positivity
        have h1 : (2 : ℝ) ≤ c * D.R.m := by nlinarith
        calc c * (D.R.m : ℝ) ^ 2 * D.R.f * 2 = (c * (D.R.m : ℝ) ^ 2 * D.R.f) * 2 := by ring
          _ ≤ (c * (D.R.m : ℝ) ^ 2 * D.R.f) * (c * D.R.m) := mul_le_mul_of_nonneg_left h1 h0
          _ = _ := by ring
    _ = _ := (rows_HHZ_eq D large₂ c Z).symm

theorem rows_KBound_of {C' Cl Cg cb Cu cT CT C0 A c : ℝ} (hH : Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A)
    (hHH : UnitaryVolumeMass.stHH D large₂ u u' C' Cl Cg cb Cu cT CT C0 A c) (hc1 : 1 ≤ c) (hCT : CT ≤ c) : rows_KBound Y c := by
  intro t hG hrel
  have hrd := d_rdE_pos hH.1
  have hb := d_two_le_b D large₂
  have hb0 : 0 < large₂.sc.b := by linarith
  have hHH1 := rows_one_le_HHZ D large₂ (by linarith : 0 ≤ c) (termGramMatrix X t)
  by_cases hD : Dr (X.fl t) (X.fl' t) = 0
  · have e : rows_Kt Y t = 1 := by
      unfold rows_Kt
      refine Finset.prod_eq_one fun τ _ => ?_
      unfold chRatio
      rw [if_pos ((rows_Dr_zero_iff Y hrd t τ).2 hD)]
    rw [e, one_pow]
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ hHH1)
  · have eK : rows_Kt Y t = ∏ τ, (1 + Lat.ch (Tu D u) (Tu D u') (X.fl t) (X.fl' t) (embS D τ)) /
        Lat.sh (Tu D u) (Tu D u') (X.fl t) (X.fl' t) (embS D τ) := by
      unfold rows_Kt
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [rows_chRatio_eq Y hrd t τ]
      unfold onePlusChSh
      rw [if_neg hD]
    have hT1 : 1 ≤ Tr D u := by unfold Tr; exact_mod_cast (D.mem u).A.T_prime.pos
    have hT1' : 1 ≤ Tr D u' := by unfold Tr; exact_mod_cast (D.mem u').A.T_prime.pos
    have hDpos : ∀ τ, 0 < absDl D (termGramMatrix X t) D.R.rS τ := by
      intro τ
      rw [← d_norm_Dmin Y hrd t τ D.R.rS (Nat.le_succ _)]
      exact norm_pos_iff.2 fun h => hD ((rows_Dr_zero_iff Y hrd t τ).1 h)
    have hGeq : ∀ τ, Gz D (Tu D u) (Tu D u') (termGramMatrix X t) τ = Tr D u * Tr D u' * absDl D (termGramMatrix X t) D.R.rS τ ^ 2 *
        Lat.sh (Tu D u) (Tu D u') (X.fl t) (X.fl' t) (embS D τ) ^ 2 := by
      intro τ
      have h := rowsT_nu_eq Y hrd t hG hrel hD τ
      unfold nuV at h
      rw [d_Gf_eq Y hrd t τ, d_norm_Dmin Y hrd t τ D.R.rS (Nat.le_succ _)] at h
      have hne : Tr D u * absDl D (termGramMatrix X t) D.R.rS τ ^ 2 ≠ 0 := by
        have := hDpos τ
        positivity
      rw [div_eq_iff hne] at h
      rw [h]; ring
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h23, _, _⟩ := hH.1.1
    have hm2 : (2 : ℝ) ≤ D.R.m := by
      rw [rows_m_cast]; have : (0 : ℝ) ≤ D.R.rS := by positivity
      linarith
    have h6 : (Tr D u * Tr D u') ^ Fintype.card D.what₂.Tau ≤ HHZ D large₂.sc.b c (termGramMatrix X t) := by
      rw [D.what₂.card_Tau]
      have a1 : Tr D u * Tr D u' ≤ large₂.sc.b ^ (2 * (c * D.R.m)) := by
        have b1 : Tr D u ≤ large₂.sc.b ^ (c * (D.R.m : ℝ)) := (h23 u).2.trans
          (Real.rpow_le_rpow_of_exponent_le (by linarith) (by gcongr))
        have b2 : Tr D u' ≤ large₂.sc.b ^ (c * (D.R.m : ℝ)) := (h23 u').2.trans
          (Real.rpow_le_rpow_of_exponent_le (by linarith) (by gcongr))
        calc Tr D u * Tr D u' ≤ large₂.sc.b ^ (c * (D.R.m : ℝ)) * large₂.sc.b ^ (c * (D.R.m : ℝ)) :=
              mul_le_mul b1 b2 (by linarith) (by positivity)
          _ = _ := by rw [← Real.rpow_add hb0]; congr 1; ring
      calc (Tr D u * Tr D u') ^ D.R.f ≤ (large₂.sc.b ^ (2 * (c * D.R.m))) ^ D.R.f :=
            pow_le_pow_left₀ (by positivity) a1 _
        _ = large₂.sc.b ^ (2 * (c * D.R.m) * D.R.f) := rows_rpow_pow hb0 _ _
        _ ≤ _ := rows_bpow_le_HHZ D large₂ (by
            have h0 : 0 ≤ c * (D.R.m : ℝ) * D.R.f := by positivity
            have h1 : (2 : ℝ) ≤ c * (D.R.m : ℝ) ^ 2 := by nlinarith
            calc 2 * (c * (D.R.m : ℝ)) * D.R.f = (c * (D.R.m : ℝ) * D.R.f) * 2 := by ring
              _ ≤ (c * (D.R.m : ℝ) * D.R.f) * (c * (D.R.m : ℝ) ^ 2) := mul_le_mul_of_nonneg_left h1 h0
              _ = _ := by ring) _
    have h8 : ∏ τ, max 1 (1 / Gz D (Tu D u) (Tu D u') (termGramMatrix X t) τ) ≤ HHZ D large₂.sc.b c (termGramMatrix X t) := by
      simp only [one_div]
      exact (rowsT_HH_term Y hH hHH t hG hrel).2.2.1
    have key := Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.degFactorBound D.what₂.Tau
      (fun τ => Lat.sh (Tu D u) (Tu D u') (X.fl t) (X.fl' t) (embS D τ))
      (fun τ => Lat.ch (Tu D u) (Tu D u') (X.fl t) (X.fl' t) (embS D τ))
      (fun τ => Gz D (Tu D u) (Tu D u') (termGramMatrix X t) τ) (fun τ => absDl D (termGramMatrix X t) D.R.rS τ)
      (Tr D u) (Tr D u') (HHZ D large₂.sc.b c (termGramMatrix X t)) (one_le_mul_of_one_le_of_one_le hT1 hT1')
      (fun τ => ⟨rowsT_sh_pos Y hrd t hG hrel hD τ, by
        unfold Lat.ch; exact div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _), rowsT_ch_sq Y hrd t hG hrel hD τ⟩)
      (fun τ => rowsT_Gz_pos Y hrd t hG hrel τ) hDpos hGeq h6
      (rows_Dr_le_HHZ D large₂ hrd hH.2.1.1 hc1 _) h8
    rw [D.what₂.card_Tau] at key
    rw [eK]
    exact key

end KB

section Fam

variable {eps : ℝ} (Fm : FamP eps) (C1 : ℝ) (X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))
  (Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
    LoopTie (Fm.D x i) (Fm.L x i) (X x hx i) u u' C1)

end Fam

end Formalism.MainNotions.BridgeLemma₂

end
end

section

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticeCounting Formalism.MainNotions.BridgeLemma

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Rec

variable {D : D7} {large₂ : SizeData₂ D} {X : TermTie D} {u u' : D.what₂.Word} {C1 : ℝ} (Y : LoopTie D large₂ X u u' C1)

theorem rows_GamD_le (D : D7) (large₂ : SizeData₂ D) {Ca C2 C : ℝ} (hC2 : 2 * C2 ≤ C) (hCa : |Ca| ≤ C) :
    rows_GamD D large₂ Ca C2 ≤ GamS D large₂ * Real.exp (C * (D.R.m : ℝ) ^ 6 * D.R.f * Real.log large₂.sc.b) *
      (C / D.R.k) ^ (D.R.k * D.R.f) := by
  unfold rows_GamD
  have hb : Real.log large₂.sc.b = large₂.sc.L := by unfold Scale.b; exact Real.log_exp _
  have hL : 0 ≤ large₂.sc.L := by
    unfold Scale.L; exact Real.rpow_nonneg (by linarith [large₂.sc.one_lt_alt]) _
  have hk0 : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
  have hG : 0 ≤ GamS D large₂ := by unfold GamS; positivity
  have hQ : 0 ≤ (D.R.m : ℝ) ^ 6 * D.R.f * large₂.sc.L := mul_nonneg (by positivity) hL
  have hE : Real.exp (C2 * (D.R.m : ℝ) ^ 6 * D.R.f * Real.log large₂.sc.b) ^ 2 ≤
      Real.exp (C * (D.R.m : ℝ) ^ 6 * D.R.f * Real.log large₂.sc.b) := by
    rw [sq, ← Real.exp_add, Real.exp_le_exp, hb]
    have := mul_le_mul_of_nonneg_right hC2 hQ
    linarith
  have hX : (Ca / D.R.k) ^ (D.R.k * D.R.f) ≤ (C / D.R.k) ^ (D.R.k * D.R.f) := by
    calc (Ca / D.R.k) ^ (D.R.k * D.R.f) ≤ |Ca / D.R.k| ^ (D.R.k * D.R.f) := by
          rw [← abs_pow]; exact le_abs_self _
      _ ≤ (C / D.R.k) ^ (D.R.k * D.R.f) := by
          apply pow_le_pow_left₀ (abs_nonneg _)
          rw [abs_div, abs_of_nonneg hk0]
          exact div_le_div_of_nonneg_right hCa hk0
  have hX2 : 0 ≤ (C / D.R.k) ^ (D.R.k * D.R.f) :=
    pow_nonneg (div_nonneg (le_trans (abs_nonneg _) hCa) hk0) _
  calc GamS D large₂ * Real.exp (C2 * (D.R.m : ℝ) ^ 6 * D.R.f * Real.log large₂.sc.b) ^ 2 * (Ca / D.R.k) ^ (D.R.k * D.R.f)
      ≤ GamS D large₂ * Real.exp (C2 * (D.R.m : ℝ) ^ 6 * D.R.f * Real.log large₂.sc.b) ^ 2 * (C / D.R.k) ^ (D.R.k * D.R.f) :=
        mul_le_mul_of_nonneg_left hX (mul_nonneg hG (sq_nonneg _))
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE hG) hX2

theorem rows_degB_le {C' Cl Cg cb Cu cT CT C0 A c Ca C2 Ch C : ℝ} (hH : Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A)
    (hc : 0 ≤ c) (hcC : c ≤ C) (hC1 : 1 ≤ C)
    (hC : 4 + (c ^ 2 + 2 * max (Ch - c) 0) * (6 * c + 2) ≤ C ^ 2) (hC2 : 2 * C2 ≤ C) (hCa : |Ca| ≤ C) (s : ℕ) :
    rows_degB D large₂ u c Ca C2 Ch s ≤
      LatticeSumBounds.degRow C D.R.k D.R.m D.R.f s large₂.sc.b (gg D) D.host.v (GamS D large₂) (XiB D large₂ u C) := by
  have hg2 := two_le_gg_of_count_hypotheses hH.1
  have hv1 : 1 ≤ D.host.v := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h19, _⟩ := hH.1.1
    exact h19
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast rows_f_pos D
  have hP1 := rows_P_one_le D large₂ c Ch
  have hmx : 0 ≤ max (Ch - c) 0 := le_max_right _ _
  have hexp := rows_exp_nd (m := D.R.m) (f := D.R.f) (s := s) (r := D.R.rS) (c := c) (mx := max (Ch - c) 0)
    (cf := cF D.R.f) (C := C) (rows_m_cast D) (by positivity) hf (by positivity) hc hmx (rows_cF_le hH) hC
  have hpe2 : 2 * pairCountExponentShift D c Ch ≤ C * (D.R.m : ℝ) ^ 2 * D.R.f * (C * D.R.m) := by
    have e1 : pairCountExponentShift D c Ch = (c ^ 2 + 2 * max (Ch - c) 0) * ((D.R.m : ℝ) ^ 3 * D.R.f) := by
      unfold pairCountExponentShift
      have : (D.R.rS : ℝ) + 1 = (D.R.m : ℝ) / 2 := by rw [rows_m_cast]; ring
      rw [this]; ring
    have h0 : 0 ≤ (D.R.m : ℝ) ^ 3 * D.R.f := by positivity
    have h1 : 2 * (c ^ 2 + 2 * max (Ch - c) 0) ≤ C ^ 2 := by
      have : 0 ≤ (c ^ 2 + 2 * max (Ch - c) 0) * (6 * c) := by positivity
      nlinarith
    rw [e1]
    calc 2 * ((c ^ 2 + 2 * max (Ch - c) 0) * ((D.R.m : ℝ) ^ 3 * D.R.f))
        = (2 * (c ^ 2 + 2 * max (Ch - c) 0)) * ((D.R.m : ℝ) ^ 3 * D.R.f) := by ring
      _ ≤ C ^ 2 * ((D.R.m : ℝ) ^ 3 * D.R.f) := mul_le_mul_of_nonneg_right h1 h0
      _ = _ := by ring
  have hXs0 : 0 ≤ XiS D u (rows_P D large₂ c Ch ^ 2) c s := rows_XiS_nonneg D u (by positivity) hc s
  have hXs := rows_XiP_le D large₂ u hc hcC hpe2 s
  have core := rows_num_nd (k := D.R.k) (m := D.R.m) (f := D.R.f) (s := s) (r := D.R.rS) (b := large₂.sc.b) (g := 2)
    (v := D.host.v) (Γ := rows_GamD D large₂ Ca C2) (c := c) (C := C) (pe := pairCountExponentShift D c Ch) (E1 := pairCountExponent D c s)
    (cr := c * (D.R.rS : ℝ) ^ 2) (δ := 0) (rD := 1) (XiP := XiS D u (rows_P D large₂ c Ch ^ 2) c s)
    (Xi := XiB D large₂ u C) (d_two_le_b D large₂) (by norm_num) (by linarith) (rows_GamD_nonneg D large₂ Ca C2) hc hcC hC1 le_rfl
    zero_le_one zero_le_one hXs0 hXs (by unfold pairCountExponentShift pairCountExponent; exact hexp)
  unfold LatticeSumBounds.ndRow at core
  rw [div_self (two_ne_zero), one_pow] at core
  have hA0 : 0 ≤ (2 / gg D) ^ ((s - 2) * D.R.k * D.R.f) := by
    have : 0 ≤ gg D := by linarith
    positivity
  have hbig0 : 0 ≤ LatticeSumBounds.bigH C D.R.m D.R.f large₂.sc.b ^ (C * ((s : ℝ) + D.R.m) * (D.R.m : ℝ) ^ 2) := by
    unfold LatticeSumBounds.bigH
    have := d_two_le_b D large₂
    positivity
  have hM0 : 0 ≤ ((D.R.k : ℝ) * D.host.v) ^ (D.R.k * D.R.f) * XiB D large₂ u C s * C ^ (D.R.k * D.R.f) *
      LatticeSumBounds.bigH C D.R.m D.R.f large₂.sc.b ^ (C * ((s : ℝ) + D.R.m) * (D.R.m : ℝ) ^ 2) * (C * s * D.R.f) ^ (6 * s * D.R.f) := by
    have : 0 ≤ XiB D large₂ u C s := hXs0.trans hXs
    have : 0 ≤ D.host.v := by linarith
    positivity
  unfold rows_degB rows_RD rows_Phi LatticeSumBounds.degRow
  unfold rows_P at core ⊢
  calc (2 / gg D) ^ ((s - 2) * D.R.k * D.R.f) * ((D.R.k : ℝ) * D.host.v / (Real.exp 1 * Real.pi)) ^ (D.R.k * D.R.f) *
        (XiS D u ((large₂.sc.b ^ pairCountExponentShift D c Ch) ^ 2) c s *
          (((large₂.sc.b ^ pairCountExponentShift D c Ch) ^ pairCountExponent D c s) ^ 2 * ((large₂.sc.b ^ pairCountExponentShift D c Ch) ^ (c * (D.R.rS : ℝ) ^ 2)) ^ 2 *
            (c * s * D.R.f) ^ (6 * s * D.R.f) * rows_GamD D large₂ Ca C2)) *
        ((41 ^ D.R.f * (large₂.sc.b ^ pairCountExponentShift D c Ch) ^ 3) ^ ((D.R.rS + 1) ^ 2)) ^ 2
      = (2 / gg D) ^ ((s - 2) * D.R.k * D.R.f) *
        (1 * ((D.R.k : ℝ) * D.host.v / (Real.exp 1 * Real.pi)) ^ (D.R.k * D.R.f) *
        (XiS D u ((large₂.sc.b ^ pairCountExponentShift D c Ch) ^ 2) c s *
          (((large₂.sc.b ^ pairCountExponentShift D c Ch) ^ pairCountExponent D c s) ^ 2 * ((large₂.sc.b ^ pairCountExponentShift D c Ch) ^ (c * (D.R.rS : ℝ) ^ 2)) ^ 2 *
            (c * s * D.R.f) ^ (6 * s * D.R.f) * rows_GamD D large₂ Ca C2)) * ((1 + 0) * 1) *
        ((41 ^ D.R.f * (large₂.sc.b ^ pairCountExponentShift D c Ch) ^ 3) ^ ((D.R.rS + 1) ^ 2)) ^ 2) := by ring
    _ ≤ (2 / gg D) ^ ((s - 2) * D.R.k * D.R.f) * _ := mul_le_mul_of_nonneg_left core hA0
    _ = (2 / gg D) ^ ((s - 2) * D.R.k * D.R.f) * ((((D.R.k : ℝ) * D.host.v) ^ (D.R.k * D.R.f) * XiB D large₂ u C s *
          C ^ (D.R.k * D.R.f) * LatticeSumBounds.bigH C D.R.m D.R.f large₂.sc.b ^ (C * ((s : ℝ) + D.R.m) * (D.R.m : ℝ) ^ 2) *
          (C * s * D.R.f) ^ (6 * s * D.R.f)) * rows_GamD D large₂ Ca C2) := by ring
    _ ≤ (2 / gg D) ^ ((s - 2) * D.R.k * D.R.f) * ((((D.R.k : ℝ) * D.host.v) ^ (D.R.k * D.R.f) * XiB D large₂ u C s *
          C ^ (D.R.k * D.R.f) * LatticeSumBounds.bigH C D.R.m D.R.f large₂.sc.b ^ (C * ((s : ℝ) + D.R.m) * (D.R.m : ℝ) ^ 2) *
          (C * s * D.R.f) ^ (6 * s * D.R.f)) * (GamS D large₂ * Real.exp (C * (D.R.m : ℝ) ^ 6 * D.R.f * Real.log large₂.sc.b) *
          (C / D.R.k) ^ (D.R.k * D.R.f))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (rows_GamD_le D large₂ hC2 hCa) hM0) hA0
    _ = _ := by ring

theorem rows_RowsDeg_record {C' Cl Cg cb Cu cT CT C0 A c Cpr Ca C2 Ch δ δm C : ℝ} {q : ℕ}
    (h : rows_Hyps Y C' Cl Cg cb Cu cT CT C0 A c Cpr Ca C2 Ch δ δm q) (hK : rows_KBound Y c) (hc1 : 1 ≤ c)
    (hcC : c ≤ C) (hC1 : 1 ≤ C)
    (hC : 4 + (c ^ 2 + 2 * max (Ch - c) 0) * (6 * c + 2) ≤ C ^ 2) (hC2 : 2 * C2 ≤ C) (hCa : |Ca| ≤ C)
    (hq2 : 4 * (c * D.R.k) + 4 * pairCountExponent D c D.R.k + 4 * (c * (D.R.rS : ℝ) ^ 2) +
      (C2 * (D.R.m : ℝ) ^ 2 + C2 * (D.R.m : ℝ) ^ 4 * 2) / 2 + 12 * ((D.R.rS : ℝ) + 1) ^ 2 ≤
        (q : ℝ) / ((D.R.rS : ℝ) + 1)) : RowsDeg X Y C := by
  intro s hs hsk
  have hsk' : (s : ℝ) ≤ D.R.k := by exact_mod_cast hsk
  have hm : (0 : ℝ) ≤ D.R.m := Nat.cast_nonneg _
  have hE : pairCountExponent D c s ≤ pairCountExponent D c D.R.k := by
    unfold pairCountExponent
    have := mul_nonneg (mul_nonneg h.hc (sub_nonneg.2 hsk')) hm
    linarith
  have hq2s : 4 * (c * D.R.k) + 4 * pairCountExponent D c s + 4 * (c * (D.R.rS : ℝ) ^ 2) +
      (C2 * (D.R.m : ℝ) ^ 2 + C2 * (D.R.m : ℝ) ^ 4 * 2) / 2 + 12 * ((D.R.rS : ℝ) + 1) ^ 2 ≤
        (q : ℝ) / ((D.R.rS : ℝ) + 1) := by linarith
  exact rows_RowBound_mono Y (rows_Deg_record Y h hK hc1 s hs hsk hq2s)
    (rows_degB_le h.hH h.hc hcC hC1 hC hC2 hCa s) h.hdim.le

end Rec

section Fam

variable {eps : ℝ} (Fm : FamP eps) (C1 : ℝ) (X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))
  (Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
    LoopTie (Fm.D x i) (Fm.L x i) (X x hx i) u u' C1)

end Fam

end Formalism.MainNotions.BridgeLemma₂

end
end
