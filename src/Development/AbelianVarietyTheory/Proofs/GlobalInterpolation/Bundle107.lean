module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle002
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FundamentalDomainNeZero
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle009
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle003
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ChebyshevPsiProgressionRelativeError
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle004
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle006
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle071
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle091
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle092
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle074
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle076
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle072
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle103
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle070
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle075
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle081
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle102
public import Development.AutomorphicArithmetic.WeightCongruences.Bundle002
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle082
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle104
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle040
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle047
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle033
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle034
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle043
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle052
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle106
public import Formalism.LocalToGlobal.GlobalTheory.GL5.PClassDecomp
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle098
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanRangeEmb4EqTop
public import Formalism.LocalToGlobal.GlobalTheory.GL3.DeterminantNormOneOfUnitDisc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle011
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharacterTrivialNearOne

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct

namespace GlobalTheory.PerpFrameOfMatrix

theorem herm_eq_dot {P Q : ℕ} (u v : ActionCoordinates.Wsp P Q) :
    ActionCoordinates.herm u v = star v ⬝ᵥ Formalism.UG.Jpq P Q *ᵥ u := by
  simp [ActionCoordinates.herm, ActionCoordinates.sgn, Formalism.UG.Jpq, fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type,
    mul_comm, neg_mulVec]

theorem isPerpFrame_of_matrix : ∀ (P Q P' Q' : ℕ), P' + Q' + 1 = P + Q → ∀ x : ActionCoordinates.Wsp P Q, ActionCoordinates.qf x ≠ 0 → ∀ C : Matrix (Fin P ⊕ Fin Q) (Fin P' ⊕ Fin Q') ℂ, Cᴴ * Formalism.UG.Jpq P Q * C = Formalism.UG.Jpq P' Q' → (Cᴴ * Formalism.UG.Jpq P Q) *ᵥ x = 0 → ∀ ι : UpqT P' Q' → UpqT P Q, (∀ b, UpqT.mat (ι b) * C = C * UpqT.mat b ∧ UpqT.mat (ι b) *ᵥ x = x) → ActionCoordinates.IsPerpFrame x (Matrix.toLin' C) ι := by
  intro P Q P' Q' hc x hx C h1 h2 ι hι
  have hx' : star x ⬝ᵥ Formalism.UG.Jpq P Q *ᵥ x ≠ 0 := by
    rw [← herm_eq_dot, ActionCoordinates.herm_self]; exact_mod_cast hx
  have hperp : ∀ v, star x ⬝ᵥ Formalism.UG.Jpq P Q *ᵥ (C *ᵥ v) = 0 := fun v => by
    have h3 : star x ᵥ* (Formalism.UG.Jpq P Q * C) = 0 := by
      have := congrArg star h2
      rwa [star_mulVec, conjTranspose_mul, conjTranspose_conjTranspose,
        GlobalTheory.UnfoldingCompare.Jpq_conjTranspose, star_zero] at this
    rw [mulVec_mulVec, dotProduct_mulVec, h3, zero_dotProduct]
  refine ⟨fun v w => ?_, fun y => ⟨fun hy => ?_, ?_⟩, fun g => ⟨(hι g).2, fun v => ?_⟩⟩
  · rw [herm_eq_dot, herm_eq_dot, toLin'_apply, toLin'_apply, star_mulVec, mulVec_mulVec,
      ← dotProduct_mulVec, mulVec_mulVec, ← Matrix.mul_assoc, h1]
  · obtain ⟨N, B, -, hN, -⟩ := GlobalTheory.UnfoldingCompare.exists_frame_inv hc hx' h1 h2
    have e : y = C *ᵥ ((N *ᵥ y) ∘ Sum.inl) + (N *ᵥ y) (Sum.inr ()) • x := by
      conv_lhs => rw [← one_mulVec y, ← hN, ← mulVec_mulVec, fromCols_mulVec]
      congr 1
      funext i
      simp [mulVec, dotProduct, mul_comm]
    have ha : (N *ᵥ y) (Sum.inr ()) = 0 := by
      rw [herm_eq_dot, e, mulVec_add, mulVec_smul, dotProduct_add, hperp, zero_add,
        dotProduct_smul, smul_eq_mul] at hy
      exact (mul_eq_zero.1 hy).resolve_right hx'
    refine ⟨(N *ᵥ y) ∘ Sum.inl, ?_⟩
    rw [ha, zero_smul, add_zero] at e
    rw [toLin'_apply, ← e]
  · rintro ⟨v, rfl⟩
    rw [herm_eq_dot, toLin'_apply, hperp]
  · simp only [ActionCoordinates.act, toLin'_apply, mulVec_mulVec, (hι g).1]

end GlobalTheory.PerpFrameOfMatrix
end

section


theorem _root_.GlobalTheory.T.selfDualLattice_over_columnBaseLattice : GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.SelfDualOverBase := by
  first | exact @GlobalTheory.OverObj.selfDualOverBase | exact GlobalTheory.OverObj.selfDualOverBase | (intros; apply GlobalTheory.OverObj.selfDualOverBase <;> assumption)
end

section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

theorem _root_.GlobalTheory.T.chebyshevPsiProgression_relative_error : ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ c₀ → ∃ c₂ c₃ C : ℝ, 0 < c₂ ∧ 0 < c₃ ∧ 0 < C ∧ ∀ (M : ℕ) [NeZero M] (b : ℕ) (θ : ℤ) (β u : ℝ), 3 ≤ M → Nat.Coprime b M → ExcData c₁ M b θ β → (M : ℝ) ^ c₂ ≤ u → |(M.totient : ℝ) * psiAP M b u - (u - θ * (u ^ β / β))| ≤ C * (Real.exp (-c₃ * Real.log u / Real.log M) + Real.exp (-Real.sqrt (c₃ * Real.log u))) * (u - θ * (u ^ β / β)) := by
  first | exact @GlobalTheory.Lin.PsiRel.psiAP_relative | exact GlobalTheory.Lin.PsiRel.psiAP_relative | (intros; apply GlobalTheory.Lin.PsiRel.psiAP_relative <;> assumption)
end

section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

namespace GlobalTheory.Alc

theorem weight_rowW_apply {N : ℕ} (m : Fin N × Fin N →₀ ℕ) (a : Fin N) :
    Finsupp.weight (rowW N N) m a = rowDeg m a := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp only [Finset.sum_apply, rowW, rowDeg, Pi.smul_apply, smul_eq_mul]
  rw [Fintype.sum_prod_type]
  simp [Pi.single_apply]

theorem hw_mem_of_lt : ∀ (p : ℕ), p.Prime → ∀ (k : Type) [Field k] [CharP k p] (N : ℕ) (ν : Fin N → ℕ), Antitone ν → (∀ h : 0 < N, ν ⟨N - 1, by omega⟩ = 0 ∧ ν ⟨0, h⟩ + (N - 1) ≤ p) → ∀ M M' : Submodule k (MvPolynomial (Fin N × Fin N) k), Good M → Good M' → M < M' → M' ≤ dualWeyl k N N ν → hw k le_rfl ν ∈ M' ∧ hw k le_rfl ν ∉ M := by
  intro p hp k _ _ N ν hν hal M M' hM hM' hlt hle
  have dom := GlobalTheory.T.rowDeg_dominated_of_mem_dualWeylModule k N ν
  obtain ⟨μ, v, hμ, hvM', hvM, hvw, hraise⟩ := GlobalTheory.T.exists_dominant_highest_vector_of_lt_stable k N M M' hM hM' hlt
    ⟨∑ a, ν a, fun f hf m hm => ((dom f (hle hf) m hm).2).le⟩
  have hv0 : v ≠ 0 := fun h => hvM (h ▸ zero_mem M)
  have hwt := GlobalTheory.T.rowPolarizationOperators_action_on_rowWeight k N N μ v hvw
  have hrel := (GlobalTheory.T.rowPolarizationOperators_relations_divPow_baseChange k N N).1
  have hhw := GlobalTheory.T.trace_glMatrixUnit_pow_highestWeight_mod k _ N (rowE k N N) hrel M (fun a b f hf => hM.1 a b f hf)
    (fun a => (μ a : k)) v hraise (fun a => by rw [hwt.1 a, sub_self]; exact zero_mem M)
  have hval : ∀ j, hcVal k (fun i => (μ i : k)) j = hcVal k (fun i => (ν i : k)) j := by
    intro j
    by_contra hne
    have h1 := hhw j
    have h2 : gel k N N j v = hcVal k (fun i => (ν i : k)) j • v := GlobalTheory.T.traceRowOperatorPower_dualWeyl_field_smul k N ν hν j v (hle hvM')
    change gel k N N j v - _ ∈ M at h1
    rw [h2, ← sub_smul] at h1
    exact hvM ((Submodule.smul_mem_iff M (sub_ne_zero.mpr (Ne.symm hne))).mp h1)
  obtain ⟨m, hm⟩ : v.support.Nonempty := Finset.nonempty_iff_ne_empty.mpr (by rwa [Ne, MvPolynomial.support_eq_empty])
  have hmμ : ∀ a, μ a = rowDeg m a := fun a => by rw [← hvw (mem_support_iff.mp hm)]; exact (weight_rowW_apply m a)
  have hcond : ∀ h : 0 < N, ν ⟨N - 1, by omega⟩ = 0 ∧ μ ⟨0, h⟩ ≤ ν ⟨0, h⟩ ∧ ν ⟨0, h⟩ + (N - 1) ≤ p := by
    intro h
    refine ⟨(hal h).1, ?_, (hal h).2⟩
    have hd := (dom v (hle hvM') m hm).1 1
    have hs : (Finset.univ.filter fun a : Fin N => a.val < 1) = {⟨0, h⟩} := by
      ext a; simp [Fin.ext_iff]
    rw [hs, Finset.sum_singleton, Finset.sum_singleton] at hd
    rw [hmμ]; exact hd
  have hμν : μ = ν := GlobalTheory.T.eq_weights_of_traceEPowerHighestWeightValue_eq p hp k N ν μ hν hμ hcond hval
  subst hμν
  obtain ⟨c, hc⟩ := GlobalTheory.T.dualWeyl_highestWeight_space_line_field k N μ hν v (hle hvM') hvw
  have hc0 : c ≠ 0 := by rintro rfl; exact hv0 (by rw [hc, zero_smul])
  refine ⟨?_, fun h => hvM (hc ▸ M.smul_mem c h)⟩
  have : hw k le_rfl μ = c⁻¹ • v := by rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  rw [this]; exact M'.smul_mem _ hvM'

end GlobalTheory.Alc
end

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem Std.parConsts_pos {C : FC} (hC : Std C) : ∀ c ∈ C.P.list, 0 < c := by
  obtain ⟨hF, -, h1, h2, h3, h4, h5, -, -, -, -, h6, h7, -, hM, hL⟩ := hC
  obtain ⟨-, -, -, -, -, -, -, h8, -, -⟩ := hF
  simp only [FC.cLast, FC.cMid, List.forall_mem_cons] at hM hL
  obtain ⟨hCF, -⟩ := hM
  obtain ⟨a1, a2, a3, a4, a5, -, a6, a7, a8, a9, a10, a11, a12, a13, a14, -⟩ := hL
  have a4' : 0 < C.P.cLL := inv_pos.mp (lt_of_lt_of_le one_pos a4)
  simp only [PC.list, List.forall_mem_cons]
  refine ⟨?_, ?_, ?_, a4', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by simp⟩ <;>
    linarith

theorem explicitConstants_parameterConditions_large :
    SzRow (fun C D L => HostArith D.host → ∃ P : ParameterChoice' D L, parConsts P = C.PK ∧ P.CnW = C.P.CnW) := by
  refine SzRow.imp (
    SzRow.and GlobalTheory.T.sizes_host_degree_and_log_q_and_conductor_bounds <|
    SzRow.and GlobalTheory.EX.explicitChoice_rankK_lower_upper_bounds <|
    SzRow.and GlobalTheory.EX.szRow_rank_lower_bounds <|
    SzRow.and GlobalTheory.EX.szRow_logf <|
    SzRow.and GlobalTheory.T.sizes_etaSz_le_b_div_and_log_etaSz_le_and_t_le <|
    SzRow.and GlobalTheory.T.sizes_m_mul_Sc_add_etaSz_le_w_mul_L_and_bounds <|
    SzRow.and GlobalTheory.T.sizes_card_TT_le_Nstar_and_rhoP_le_and_bT_le <|
    SzRow.and GlobalTheory.EX.szRow_cloud_le <|
    SzRow.and GlobalTheory.EX.szRow_windowLength <|
    SzRow.and GlobalTheory.EX.szRow_exact <|
    SzRow.and GlobalTheory.EX.szRow_lowsFar <|
    SzRow.and GlobalTheory.T.explicitChoice_rowWeight_ratio_and_lastCloud_le_twice_first <|
    SzRow.and GlobalTheory.EX.szRow_thinSize_ge <|
    SzRow.and GlobalTheory.T.sizes_del_ge_cloudUnit_and_count_bounds <|
    SzRow.and GlobalTheory.T.sizes_node_bounds_le_h0 <|
    SzRow.and GlobalTheory.T.sizes_t_add_cube_le_h0_and_f_mul_N_pow_le_h0 <|
    SzRow.and GlobalTheory.EX.szRow_sig_gaps <|
    SzRow.and GlobalTheory.EX.szRow_rbS <|
    SzRow.and GlobalTheory.T.sizes_b_add_Sc_add_etaSz_add_div_lt_lStar <|
    SzRow.and GlobalTheory.EX.szRow_card_words_le <|
    GlobalTheory.T.sizes_exists_Y_bounds_host_g_mem_Icc_Y_two_mul_Y) ?_
  intro C cD ch D L hC _ h hA
  obtain ⟨⟨h_qd_pow, h_logq_ge, h_dlogL1_le, h_condE_le, h_pde_log⟩,
    ⟨h_k_low, h_k_up, h_R0_ge⟩,
    ⟨h_k_ge_m2L, h_k_ge_mx, h_klogk, h_flogk⟩,
    ⟨h_logf_le, h_log2f_le, h_loglogb, h_nW_ge⟩,
    ⟨h_eta_le, h_logeta, h_t_le_eta, h_teta, h_mteta⟩,
    ⟨h_mSeta, h_Neta, h_eta2, h_kS_le⟩,
    ⟨h_TT_card_le, h_rho_le, h_bT_le⟩,
    ⟨h_S_le, h_Del_le, h_logDel⟩,
    ⟨h_Lw_j, h_Lw_le, h_j0_le⟩,
    ⟨h_top_b1, h_cloud_le2, h_uk_extreme, h_em_win, h_nodes_gap, h_e_centred, h_e_parity, h_etaF_eq, h_pde_mod, h_pde_ne, h_ccK_log, h_ccK_le⟩,
    h_lows_far,
    ⟨h_X''_ratio, h_bm_le⟩,
    h_w''_ge,
    ⟨h_Del_ge, h_Del_count⟩,
    h_h0_ge,
    ⟨h_h0_fun, h_h0_fN⟩,
    h_sig_gaps,
    h_rbS,
    ⟨h_lstar1, h_lstar2⟩,
    h_words_le,
    h_g_Y⟩ := h
  have hp := hC.parConsts_pos
  simp only [PC.list, List.forall_mem_cons] at hp
  obtain ⟨p_CkLow, p_Ck6, p_CfL, p_cLL, p_CnW, p_Crho, p_CDelG, p_CLw, p_Cj0, p_Cw, p_cw, p_CDel, p_CCount, p_Ch0r, p_Ch0k, p_Ch0N, p_Cgap, p_CetaF, p_CY, p_CYL, p_Cpde, p_CccK, p_CF, -⟩ := hp
  exact ⟨
    { CkLow := C.P.CkLow, CkLow_pos := p_CkLow
      Ck6 := C.P.Ck6, Ck6_pos := p_Ck6
      CfL := C.P.CfL, CfL_pos := p_CfL
      cLL := C.P.cLL, cLL_pos := p_cLL
      CnW := C.P.CnW, CnW_pos := p_CnW
      Crho := C.P.Crho, Crho_pos := p_Crho
      CDelG := C.P.CDelG, CDelG_pos := p_CDelG
      CLw := C.P.CLw, CLw_pos := p_CLw
      Cj0 := C.P.Cj0, Cj0_pos := p_Cj0
      Cw := C.P.Cw, Cw_pos := p_Cw
      cw := C.P.cw, cw_pos := p_cw
      CDel := C.P.CDel, CDel_pos := p_CDel
      CCount := C.P.CCount, CCount_pos := p_CCount
      Ch0r := C.P.Ch0r, Ch0r_pos := p_Ch0r
      Ch0k := C.P.Ch0k, Ch0k_pos := p_Ch0k
      Ch0N := C.P.Ch0N, Ch0N_pos := p_Ch0N
      Cgap := C.P.Cgap, Cgap_pos := p_Cgap
      CetaF := C.P.CetaF, CetaF_pos := p_CetaF
      CY := C.P.CY, CY_pos := p_CY
      CYL := C.P.CYL, CYL_pos := p_CYL
      Cpde := C.P.Cpde, Cpde_pos := p_Cpde
      CccK := C.P.CccK, CccK_pos := p_CccK
      CF := C.P.CF, CF_pos := p_CF
      qd_pow := h_qd_pow
      logq_ge := h_logq_ge
      logDerivative_le_power := h_dlogL1_le
      condE_le := h_condE_le
      pde_log := h_pde_log
      k_low := h_k_low
      k_up := h_k_up
      radius_ge_sqrt_ratio := h_R0_ge
      k_ge_m2L := h_k_ge_m2L
      k_ge_mx := h_k_ge_mx
      klogk := h_klogk
      flogk := h_flogk
      logf_le := h_logf_le
      log_sq_conductor_le := h_log2f_le
      loglogb := h_loglogb
      nW_ge := h_nW_ge
      eta_le := h_eta_le
      logeta := h_logeta
      t_le_eta := h_t_le_eta
      teta := h_teta
      mteta := h_mteta
      mSeta := h_mSeta
      Neta := h_Neta
      eta2 := h_eta2
      kS_le := h_kS_le
      TT_card_le := h_TT_card_le
      rho_le := h_rho_le
      bT_le := h_bT_le
      S_le := h_S_le
      Del_le := h_Del_le
      logDel := h_logDel
      Lw_j := h_Lw_j
      Lw_le := h_Lw_le
      jetIndex_le_log := h_j0_le
      topPlace_first_bound := h_top_b1
      cloud_place_bound := h_cloud_le2
      uk_extreme := h_uk_extreme
      em_win := h_em_win
      nodes_gap := h_nodes_gap
      e_centred := h_e_centred
      e_mu := fun j => (h_e_parity j).num
      etaF_eq := h_etaF_eq
      pde_mod := h_pde_mod
      pde_ne := h_pde_ne
      ccK_log := h_ccK_log
      ccK_le := h_ccK_le
      lows_far := h_lows_far
      X''_ratio := h_X''_ratio
      bm_le := h_bm_le
      w''_ge := h_w''_ge
      Del_ge := h_Del_ge
      Del_count := h_Del_count
      h0_ge := h_h0_ge
      heightBound_ge_rank_cubic := h_h0_fun
      heightBound_ge_degree_power := h_h0_fN
      sig_gaps := h_sig_gaps
      rbS := h_rbS
      lstar1 := h_lstar1
      lstar2 := h_lstar2
      words_le := h_words_le
      g_Y := h_g_Y
      g_norm := hA.1
      g_mod := hA.2.1
      pde_split := hA.2.2.1
      level_split := hA.2.2.2 }, rfl, rfl⟩

end GlobalTheory.EX
end

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

theorem _root_.GlobalTheory.T.explicitChoice_sizeEta : SzRow (fun _ _ L => SizeEta L) := by
  first | exact @GlobalTheory.EX.szRow_sizeEta | exact GlobalTheory.EX.szRow_sizeEta | (intros; apply GlobalTheory.EX.szRow_sizeEta <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

theorem _root_.GlobalTheory.T.explicitChoice_sizeNodes : SzRow (fun _ _ L => SizeNodes L) := by
  first | exact @GlobalTheory.EX.szRow_sizeNodes | exact GlobalTheory.EX.szRow_sizeNodes | (intros; apply GlobalTheory.EX.szRow_sizeNodes <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

theorem _root_.GlobalTheory.T.explicitChoice_sizeLstar : SzRow (fun _ _ L => SizeLstar L) := by
  first | exact @GlobalTheory.EX.szRow_sizeLstar | exact GlobalTheory.EX.szRow_sizeLstar | (intros; apply GlobalTheory.EX.szRow_sizeLstar <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

theorem _root_.GlobalTheory.T.per_relIndex_ne_zero_and_mem_locP_iff : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), A.AA.FG → A.AA ≠ ⊥ → IsSdLat N → IsSdLat N' → (per A N N').FG ∧ (∀ x : HomE X.E a b, ∃ n : ℕ, 0 < n ∧ (n : X.E) • x ∈ per A N N') ∧ (∀ r : 𝓞 X.E, r ≠ 0 → (smulLat (r : X.E) (per A N N')).toAddSubgroup.relIndex (per A N N').toAddSubgroup ≠ 0) ∧ ∀ P : HeightOneSpectrum (𝓞 X.E), localization₂ P.asIdeal A.AA = localization₂ P.asIdeal (1 : Submodule (𝓞 X.E) X.E) → ∀ y : HomE X.E a b, y ∈ localization₂ P.asIdeal (per A N N') ↔ ∀ v ∈ localization₂ P.asIdeal N, y v ∈ localization₂ P.asIdeal N' := by
  first | exact @GlobalTheory.MomT.LatFin.per_lattice_facts | exact GlobalTheory.MomT.LatFin.per_lattice_facts | (intros; apply GlobalTheory.MomT.LatFin.per_lattice_facts <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

theorem _root_.GlobalTheory.T.fieldIso_selfDual_and_periodLattices_agree : ∀ (X : Fields) (D : D7) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ), s.Ok → (∀ (n : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E n)), IsSdLat N → StandardLatticesGL3.SD D (s.lat N)) ∧ ∀ (a b : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (z : VCx X.Tau a b), z ∈ lam (ambOf s B χ cD) N N' ↔ (fun τ => z (s.iT.symm τ)) ∈ TaylorLogMetric.La D B.tor (s.lat N) (s.lat N') := by
  first | exact @GlobalTheory.PeriodTransport.seam_lattices | exact GlobalTheory.PeriodTransport.seam_lattices | (intros; apply GlobalTheory.PeriodTransport.seam_lattices <;> assumption)
end

section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem uj_neg_eq {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (s : A →+* A)
    (J : Matrix n n A) : Formalism.UG.UJ s (-J) = Formalism.UG.UJ s J := by
  ext g
  show Formalism.UG.cT s (g : Matrix n n A) * (-J) * (g : Matrix n n A) = -J ↔
    Formalism.UG.cT s (g : Matrix n n A) * J * (g : Matrix n n A) = J
  rw [Matrix.mul_neg, Matrix.neg_mul, neg_inj]

theorem hR_neg_eq {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : HR R σ (-J) = HR R σ J := by
  unfold HR JR
  rw [Matrix.map_neg _ (map_neg _), uj_neg_eq]

theorem hFin_neg_eq {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : HFin R σ (-J) = HFin R σ J := by
  unfold HFin
  rw [uj_neg_eq]

theorem unitary_neg_same : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J J' : Matrix (Fin M) (Fin M) E), J' = -J → ∃ φ : HA (AF F) σ J ≃ₜ* HA (AF F) σ J', (∀ h, HA.mat (AF F) σ J' (φ h) = HA.mat (AF F) σ J h) ∧ (∀ h, h ∈ HFinIn (AF F) σ J ↔ φ h ∈ HFinIn (AF F) σ J') ∧ ∀ (L : Set (Fin M → E)) h, h ∈ StabFin.SFin σ J L ↔ φ h ∈ StabFin.SFin σ J' L := by
  intro F E _ _ _ _ _ σ M J J' hJ
  subst hJ
  have e := (hR_neg_eq (AF F) σ J).symm
  let ψ : HA (AF F) σ J ≃* HA (AF F) σ (-J) := MulEquiv.subgroupCongr e
  have hψ : ∀ h : HA (AF F) σ J, HA.mat (AF F) σ (-J) (ψ h) = HA.mat (AF F) σ J h := fun h => rfl
  let φ : HA (AF F) σ J ≃ₜ* HA (AF F) σ (-J) :=
    { ψ with
      continuous_toFun := Continuous.subtype_mk continuous_subtype_val _
      continuous_invFun := Continuous.subtype_mk continuous_subtype_val _ }
  have hφ : ∀ h : HA (AF F) σ J, HA.mat (AF F) σ (-J) (φ h) = HA.mat (AF F) σ J h := fun h => rfl
  refine ⟨φ, hφ, ?_, ?_⟩
  · intro h
    show (HA.mat (AF F) σ J h) ∈ HFin (AF F) σ J ↔ (HA.mat (AF F) σ (-J) (φ h)) ∈ HFin (AF F) σ (-J)
    rw [hFin_neg_eq]
    exact Iff.rfl
  · intro L h
    exact Iff.rfl

end GlobalTheory
end

section

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.PlaceComponents GlobalTheory.QuadSubfield
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

namespace GlobalTheory.MomT.FromComb

variable {D : D7} {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])

variable {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
  {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}

theorem chi_mem {χ : IdE D → ℂ} (hχ : IsChi D χ) {𝔞 : IdE D} (ha : N1 D 𝔞) : χ 𝔞 ∈ Qbar := by
  let _ := D.host.cmStar
  obtain ⟨k, hk, z, hz, hspan⟩ := CU.pow_unitary D ha
  have hzu : z ∈ unitary D.host.E := by
    rw [Unitary.mem_iff, CU.star_conj]
    exact ⟨by rw [mul_comm]; exact hz, hz⟩
  have h := hχ.2 ⟨z, hzu⟩
  simp only at h
  rw [← hspan, CU.chi_pow D χ hχ ha k hk] at h
  refine mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow (by omega : 0 < k) (mem_algebraicClosure_iff.1 ?_))
  rw [h]
  exact prod_mem fun τ _ => inv_mem (emb_mem D _ _)

theorem chiFac_mem {χ : IdE D → ℂ} (hχ : IsChi D χ) (hA : admitted D N N' L L') : Base.chiFac χ N N' L L' ∈ Qbar :=
  mul_mem (zpow_mem (chi_mem hχ (relative_determinant_norm_one D N _ L hA.1 (GlobalTheory.FourthRootStd.stdL_isSD D N) hA.2.2.1)) _)
    (zpow_mem (chi_mem hχ (relative_determinant_norm_one D N' _ L' hA.2.1 (GlobalTheory.FourthRootStd.stdL_isSD D N') hA.2.2.2)) _)

end GlobalTheory.MomT.FromComb
end
end
