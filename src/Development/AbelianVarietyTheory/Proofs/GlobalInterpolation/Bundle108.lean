module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle004
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.Bundle001
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle006
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle081
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle080
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle071
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle008
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle051
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle104
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle102
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle033
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle034
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle103
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle089
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FieldIsoLatticesFormTaylorCorrespond
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.JetSumTable
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle082

@[expose] public section

section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

noncomputable section

namespace GlobalTheory.Alc

theorem rename_rowPerm_eq_rowAct (R : Type) [CommRing R] (r n : ℕ) (σ : Equiv.Perm (Fin r)) :
    (rename (fun v : Fin r × Fin n => (σ v.1, v.2)) : MvPolynomial (Fin r × Fin n) R →ₐ[R] _) =
      rowAct R (n := n) (Matrix.of fun a b : Fin r => if b = σ a then (1 : R) else 0) := by
  apply MvPolynomial.algHom_ext
  intro v
  simp [rowAct]

theorem good_nablaSq (k : Type) [Field k] (N : ℕ) (lam : DomWeight N) : Good (nablaSq k N lam) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b f hf
    rw [(GlobalTheory.T.rowPolarizationOperators_relations_divPow_baseChange k N N).2.1 a b f]
    exact rowDivStable k N N _ a b 1 f hf
  · intro μ f hf
    exact dualWeylRowGraded k N N _ μ f hf
  · intro σ f hf
    rw [rename_rowPerm_eq_rowAct]
    exact dualWeylRowStable k N N _ _ f hf

theorem good_of_isGLSubmodule (k : Type) [Field k] (N : ℕ) (lam : DomWeight N)
    (M : Submodule k (MvPolynomial (Fin N × Fin N) k)) (hM : GlobalTheory.Published.IsGLSubmodule k N lam M) : Good M := by
  have hw : ∀ μ : Fin N → ℕ, ∀ f ∈ M, weightedHomogeneousComponent (rowW N N) μ f ∈ M :=
    GlobalTheory.T.weightedHomogeneousComponent_mem_of_GLSchemeSubmodule k N lam M hM
  refine ⟨?_, hw, GlobalTheory.T.GLSchemeSubmodule_stable_under_row_perm k N lam M hM⟩
  intro a b f hf
  by_cases hab : a = b
  · subst hab
    classical
    have hsum := sum_weightedHomogeneousComponent (rowW N N) f
    rw [finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)] at hsum

    rw [← hsum, map_sum]
    refine Submodule.sum_mem _ fun μ _ => ?_
    rw [((GlobalTheory.T.rowPolarizationOperators_action_on_rowWeight k N N μ _ (weightedHomogeneousComponent_isWeightedHomogeneous μ f)).1 a)]
    exact Submodule.smul_mem _ _ (hw μ f hf)
  · exact GlobalTheory.T.rowPolarization_mem_of_isGLSchemeSubmodule k N lam M hM a b hab f hf

theorem good_nablaSq_and_submodules : ∀ (k : Type) [Field k] (N : ℕ) (lam : DomWeight N), Good (nablaSq k N lam) ∧
    ∀ M : Submodule k (MvPolynomial (Fin N × Fin N) k), GlobalTheory.Published.IsGLSubmodule k N lam M → Good M :=
  fun k _ N lam => ⟨good_nablaSq k N lam, good_of_isGLSubmodule k N lam⟩

end GlobalTheory.Alc
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem nodeGap_blockLength_poly (x T t P Dy f m N k c h : ℝ) (hx : 6 ≤ x)
    (hT0 : 0 ≤ T) (hT : T ≤ x ^ 378) (ht : t ≤ x ^ 401) (hP0 : 0 ≤ P) (hP : P ≤ x ^ 85)
    (hD0 : 0 ≤ Dy) (hD : Dy ≤ x ^ 12) (hf0 : 0 ≤ f) (hf : f ≤ x ^ 3) (hm1 : 1 ≤ m) (hm : m ≤ x)
    (hN0 : 0 ≤ N) (hN : N ≤ x ^ 402) (hk0 : 0 ≤ k) (hk : k ≤ x ^ 5) (hc : c ≤ x)
    (hh : x ^ 1000 ≤ h) :
    (4 * T ^ 2 + 2 * t ≤ h) ∧ (P * Dy * f * m ^ 2 * N * T ≤ h) ∧ (P * (f * m * k) ^ 3 * k / m ≤ h) ∧
      (c * T * N * f ^ 2 * m ^ 2 * k * Dy * P ≤ h) := by
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 ≤ x := by linarith
  have hm0 : 0 ≤ m := by linarith
  have hp : ∀ n : ℕ, n ≤ 1000 → x ^ n ≤ h := fun n hn => (pow_le_pow_right₀ hx1 hn).trans hh
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h1 : T ^ 2 ≤ x ^ 756 := by
      calc T ^ 2 ≤ (x ^ 378) ^ 2 := by gcongr
        _ = x ^ 756 := by ring
    have h2 : t ≤ x ^ 756 := ht.trans (pow_le_pow_right₀ hx1 (by norm_num))
    have h3 : 6 * x ^ 756 ≤ x ^ 757 := by
      calc 6 * x ^ 756 ≤ x * x ^ 756 := by gcongr
        _ = x ^ 757 := by ring
    have h4 := hp 757 (by norm_num)
    linarith
  · calc P * Dy * f * m ^ 2 * N * T ≤ x ^ 85 * x ^ 12 * x ^ 3 * x ^ 2 * x ^ 402 * x ^ 378 := by gcongr
      _ = x ^ 882 := by ring
      _ ≤ h := hp _ (by norm_num)
  · calc P * (f * m * k) ^ 3 * k / m ≤ P * (f * m * k) ^ 3 * k := div_le_self (by positivity) hm1
      _ ≤ x ^ 85 * (x ^ 3 * x * x ^ 5) ^ 3 * x ^ 5 := by gcongr
      _ = x ^ 117 := by ring
      _ ≤ h := hp _ (by norm_num)
  · calc c * T * N * f ^ 2 * m ^ 2 * k * Dy * P
        ≤ x * x ^ 378 * x ^ 402 * (x ^ 3) ^ 2 * x ^ 2 * x ^ 5 * x ^ 12 * x ^ 85 := by
          calc c * T * N * f ^ 2 * m ^ 2 * k * Dy * P = c * (T * N * f ^ 2 * m ^ 2 * k * Dy * P) := by ring
            _ ≤ x * (T * N * f ^ 2 * m ^ 2 * k * Dy * P) := by gcongr
            _ = x * T * N * f ^ 2 * m ^ 2 * k * Dy * P := by ring
            _ ≤ _ := by gcongr
      _ = x ^ 891 := by ring
      _ ≤ h := hp _ (by norm_num)

theorem szRow_nodeGap_blockLength : SzRow (fun C D L => (4 * ((TOv L.sc : ℕ) : ℝ) ^ 2 + 2 * D.R.t ≤ h0 L) ∧ ((C.T.CP * zBase L ^ C.T.eP) * (D.R.f * D.R.r.choose 2 : ℕ) * D.R.f * (D.R.m : ℝ) ^ 2 * (D.R.N D.R.m : ℝ) * (TOv L.sc : ℕ) ≤ h0 L) ∧ ((C.T.CP * zBase L ^ C.T.eP) * ((D.R.f : ℝ) * D.R.m * D.R.k) ^ 3 * D.R.k / D.R.m ≤ h0 L) ∧ (C.T.ChT * (TOv L.sc : ℕ) * (D.R.N D.R.m : ℝ) * (D.R.f : ℝ) ^ 2 * (D.R.m : ℝ) ^ 2 * D.R.k * (D.R.f * D.R.r.choose 2 : ℕ) * (C.T.CP * zBase L ^ C.T.eP) ≤ h0 L)) := by
  intro eps he he' C hC
  obtain ⟨x1, hx1⟩ := GlobalTheory.T.explicitRanks_basic_bounds_large_scale eps he he'
  have heP : C.T.eP = 12 := hC.2.2.2.2.2.2.2.2.1
  have hCP : 1000 ≤ C.T.CP := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨0, fun cD _ => ⟨1000, fun ch hch => ⟨max (max x1 6) (max C.T.CP C.T.ChT), ?_⟩⟩⟩
  intro D L hLe hx V
  simp only [max_le_iff] at hx
  obtain ⟨⟨hxa, hx6⟩, hxP, hxC⟩ := hx
  obtain ⟨hf, hm, hr, hkr, -, -, hL1, -, hZ, hD, -, -, -, ht, hN, hm1, -⟩ := hx1 L.sc D.R hLe hxa V.ranks
  set x := L.sc.x with hxdef
  have hx1' : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hm1' : (1 : ℝ) ≤ D.R.m :=
    (Real.one_le_rpow hx1' (by rw [hLe]; linarith)).trans hm1
  have cast : ∀ n : ℕ, x ^ ((n : ℕ) : ℝ) = x ^ n := fun n => Real.rpow_natCast x n
  have hZ0 : 0 ≤ zBase L := by unfold zBase; have : (0:ℝ) ≤ L.sc.L := by linarith
                               positivity
  have hZ7 : zBase L ≤ x ^ 7 := by
    rw [← cast]
    exact hZ.trans (Real.rpow_le_rpow_of_exponent_le hx1' (by norm_num))
  have hPe : zBase L ^ C.T.eP = zBase L ^ (12 : ℕ) := by
    rw [heP]; first | rfl | exact_mod_cast Real.rpow_natCast _ 12
  refine nodeGap_blockLength_poly x _ _ _ _ _ _ _ _ _ _ hx6 (Nat.cast_nonneg _) ?_ ?_ ?_ ?_ (Nat.cast_nonneg _) ?_
    (Nat.cast_nonneg _) ?_ hm1' hm (Nat.cast_nonneg _) ?_ (Nat.cast_nonneg _) ?_ hxC ?_
  · have h1 : x ^ (377 : ℝ) = x ^ 377 := by exact_mod_cast cast 377
    have h2 : ((TOv L.sc : ℕ) : ℝ) ≤ x ^ 377 + 1 := by
      unfold TOv
      rw [← hxdef, h1]
      exact (Nat.ceil_lt_add_one (by positivity)).le
    have h3 : (1 : ℝ) ≤ x ^ 377 := one_le_pow₀ hx1'
    have h4 : 2 * x ^ 377 ≤ x ^ 378 := by
      calc 2 * x ^ 377 ≤ x * x ^ 377 := by gcongr; linarith
        _ = x ^ 378 := by ring
    linarith
  · exact_mod_cast ht
  · rw [hPe]; have : 0 ≤ C.T.CP := by linarith
    positivity
  · rw [hPe]
    calc C.T.CP * zBase L ^ 12 ≤ x * (x ^ 7) ^ 12 := by gcongr
      _ = x ^ 85 := by ring
  · exact_mod_cast hD
  · exact_mod_cast hf
  · exact_mod_cast hN
  · have : (D.R.k : ℝ) ≤ D.R.r := by exact_mod_cast hkr
    exact this.trans (by exact_mod_cast hr)
  · have h1 : h0 L = (h0v L.sc ch : ℝ) := by
      unfold h0
      rw [V.eta_eq]
      field_simp
    rw [h1, ← cast]
    unfold h0v
    rw [← hxdef]
    have h2 : x ^ ((1000 : ℕ) : ℝ) ≤ x ^ ch := Real.rpow_le_rpow_of_exponent_le hx1' (by exact_mod_cast hch)
    have h3 := Nat.le_ceil (x ^ ch)
    have h4 : (0 : ℝ) ≤ (⌈x ^ ch⌉₊ : ℝ) := Nat.cast_nonneg _
    push_cast at *
    linarith

theorem szRow_blockLengthParams : SzRow (fun C D L => ∀ P : ParameterChoice' D L, P.CnW = C.P.CnW → ∃ T : ParamsT D L P,
    [T.CP, T.eP, T.Cp, T.Cb, T.cTO, T.ChT, T.CbN] = C.PT ∧ T.eP = C.T.eP) := by
  have hand := szRow_and_imp.1
  have hall := hand _ _ GlobalTheory.T.sizes_PP_and_dim_and_TOv_le_x_rpow_Ct <| hand _ _ GlobalTheory.T.explicitChoice_windowRank_conditions <| hand _ _ GlobalTheory.T.explicitChoice_windowRank_le_polyBound <|
    hand _ _ GlobalTheory.T.sizes_PP_pow_mul_dim_pow_div_le_TOv <| hand _ _ GlobalTheory.T.sizes_rank_and_poly_counts_le_TOv <| hand _ _ GlobalTheory.T.sizes_TOv_mul_PP_le_b_and_sqrt_b <|
    hand _ _ GlobalTheory.T.sizes_TOv_sq_le_del_and_gap_mul_le_del <| hand _ _ szRow_nodeGap_blockLength GlobalTheory.T.explicitChoice_polynomial_le_baseSize
  refine szRow_and_imp.2 _ _ hall ?_
  rintro C cD ch D L hS - ⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩, ⟨c1, c2⟩, ⟨d1, d2⟩,
    ⟨e1, e2, e3, e4⟩, ⟨f1, f2, f3, f4⟩, ⟨g1, g2⟩, ⟨h1, h2, h3, h4⟩, ⟨i1, i2, i3⟩⟩ P hP
  obtain ⟨-, -, -, -, -, -, -, hCp, heP, -, -, -, -, hCP, -, hlast⟩ := hS
  have hCb : 1 ≤ C.T.Cb := hlast _ (by simp [FC.cLast])
  have hChT : 1 ≤ C.T.ChT := hlast _ (by simp [FC.cLast])
  have hCbN : 1 ≤ C.T.CbN := hlast _ (by simp [FC.cLast])
  refine ⟨{
    TO := TOv L.sc
    nWn := nWv D.R L.sc
    nP := 8 * D.R.f * D.R.r + 4
    PP := C.T.CP * zBase L ^ C.T.eP
    Dp := D.R.f * D.R.r.choose 2
    s := D.R.r + 6
    CP := C.T.CP
    one_le_CP := by linarith
    eP := C.T.eP
    eP_ge := heP.ge
    Cp := C.T.Cp
    Cp_ge := hCp.ge
    Cb := C.T.Cb
    Cb_nonneg := by linarith
    cTO := C.T.cTO
    ChT := C.T.ChT
    ChT_ge := hChT
    CbN := C.T.CbN
    CbN_ge := hCbN
    PP_eq := rfl
    Dp_eq := rfl
    PP_poly := a1
    Dp_poly := a2
    TO_poly := a3
    nW_win := hP ▸ b1
    nW_dvd := b2
    PP_nW := c1
    nW_le := c2
    nW_lo := b8
    split := b3
    nP_eq := rfl
    TO_eq := b4
    TO_ge := d1
    TO_PP := f1
    TO_nW := e1
    TO_40 := e2
    TO_11D2 := e3
    order_ge_rank_bound := e4
    TO_PP' := f2
    precision_cube_order_sq_le := f3
    precision_cube_order_sq_le_sqrt := f4
    TO_Dk := d2
    Del_TO := g1
    Del_gap := g2
    heightBound_ge_order_sq := h1
    heightBound_ge_precision_degree := h2
    heightBound_ge_precision_cubic := h3
    heightBound_ge_order_product := h4
    log_bound_le_sqrt := i1
    TD2' := i2
    b_ge := i3
    s_odd := b5
    s_lo := b6
    s_hi := b7 }, rfl, rfl⟩

end GlobalTheory.EX
end

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem bottom_window_le (eps : ℝ) (K : G.Consts) (h0 : 0 < eps) (h1 : eps < 1 / 52) (hK : 1 ≤ K.La) :
    ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks), s.eps = eps → x0 ≤ s.x → RankVal s R →
      2 * (R.n : ℝ) * s.delta1 * s.x ^ s.eps * G.La K s * s.b' / (R.k : ℝ) ≤ s.b' := by
  obtain ⟨CN, x1, hx1⟩ := GlobalTheory.topCount_and_lambda_bounds eps h0 h1
  refine ⟨max x1 (32 * K.La * CN ^ 2), fun s R he hx hR => ?_⟩
  obtain ⟨-, -, hLa⟩ := hx1 s he (le_trans (le_max_left _ _) hx)
  obtain ⟨hLa1, hLa2⟩ := hLa K hK
  have hx2 : 32 * K.La * CN ^ 2 ≤ s.x := le_trans (le_max_right _ _) hx
  obtain ⟨⟨-, hn⟩, -, ⟨hk, -⟩, -⟩ := hR
  have hx1' : 1 < s.x := s.one_lt_alt
  have hxp : 0 < s.x := by linarith
  have hb : 0 < s.b' := by
    unfold Scale.b' Scale.a Scale.b Scale.X'
    positivity
  have hkp : (0 : ℝ) < R.k := lt_of_lt_of_le (Real.rpow_pos_of_pos hxp _) hk
  have hd0 : 0 < s.delta1 := Real.rpow_pos_of_pos hxp _
  have hd1 : s.delta1 ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1'.le (by have := s.eps_pos; linarith)
  have hy : 0 < s.x ^ s.eps := Real.rpow_pos_of_pos hxp _
  have hlog0 : 0 ≤ Real.log s.x := Real.log_nonneg hx1'.le
  have hlog : Real.log s.x ^ 2 ≤ 4 * s.x := by
    have h := Real.log_le_rpow_div hxp.le (show (0 : ℝ) < 1 / 2 by norm_num)
    have h2 : (s.x ^ (1 / 2 : ℝ)) ^ 2 = s.x := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hxp.le]; norm_num
    calc Real.log s.x ^ 2 ≤ (s.x ^ (1 / 2 : ℝ) / (1 / 2)) ^ 2 := pow_le_pow_left₀ hlog0 h 2
      _ = 4 * (s.x ^ (1 / 2 : ℝ)) ^ 2 := by ring
      _ = 4 * s.x := by rw [h2]
  have hKC : 0 ≤ K.La * CN ^ 2 := by positivity
  have hLa3 : G.La K s ≤ s.x ^ (2 : ℝ) / 4 * s.x ^ s.eps := by
    refine hLa2.trans ?_
    rw [Real.rpow_two]
    have : K.La * CN ^ 2 * Real.log s.x ^ 2 ≤ s.x / 32 * (4 * s.x) :=
      mul_le_mul (by linarith) hlog (by positivity) (by positivity)
    nlinarith
  have hLa0 : 0 ≤ G.La K s := hy.le.trans hLa1
  have hmain : 2 * (R.n : ℝ) * s.delta1 * s.x ^ s.eps * G.La K s ≤ R.k := by
    calc 2 * (R.n : ℝ) * s.delta1 * s.x ^ s.eps * G.La K s
        ≤ 2 * (2 * s.x ^ (2 + 8 * s.eps)) * 1 * s.x ^ s.eps * (s.x ^ (2 : ℝ) / 4 * s.x ^ s.eps) := by
          gcongr
      _ = s.x ^ (2 + 8 * s.eps) * s.x ^ s.eps * s.x ^ (2 : ℝ) * s.x ^ s.eps := by ring
      _ = s.x ^ (2 + 8 * s.eps + s.eps + 2 + s.eps) := by
          rw [← Real.rpow_add hxp, ← Real.rpow_add hxp, ← Real.rpow_add hxp]
      _ ≤ s.x ^ (9 / 2 + 10 * s.eps) := Real.rpow_le_rpow_of_exponent_le hx1'.le (by linarith)
      _ ≤ R.k := hk
  rw [div_le_iff₀ hkp]
  nlinarith

theorem middle_between {R : Ranks} (p : HCParam R) {S : ℝ}
    (hv : ∀ i : Fin (R.k - 1), 0 ≤ ((p.v i : ℚ) : ℝ) ∧ ((p.v i : ℚ) : ℝ) ≤ S) (i : Fin R.k) (h1 : 1 ≤ i.1)
    (h2 : i.1 + 1 < R.k) : 0 ≤ ((p.u i : ℚ) : ℝ) ∧ ((p.u i : ℚ) : ℝ) ≤ S := by
  obtain ⟨i, hi⟩ := i
  simp only at h1 h2
  have ha := p.u_gt_v ⟨i, by omega⟩
  have hb := p.v_gt_u ⟨i - 1, by omega⟩
  have he : (⟨i - 1 + 1, by omega⟩ : Fin R.k) = ⟨i, hi⟩ := Fin.ext (by simp only; omega)
  simp only [he] at hb
  have ha' : ((p.v ⟨i, by omega⟩ : ℚ) : ℝ) < ((p.u ⟨i, hi⟩ : ℚ) : ℝ) := by exact_mod_cast ha
  have hb' : ((p.u ⟨i, hi⟩ : ℚ) : ℝ) < ((p.v ⟨i - 1, by omega⟩ : ℚ) : ℝ) := by exact_mod_cast hb
  exact ⟨(hv _).1.trans ha'.le, hb'.le.trans (hv _).2⟩

theorem exists_sizeData_explicit : ∀ (eps : ℝ) (C : FC) (cD ch : ℝ), 0 < eps → eps < 1 / 52 → Std C → 0 ≤ cD → 402 ≤ ch → ∃ x0 : ℝ, ∀ (s : Scale) (D : D7) (aT bT : D.host.TT → ℤ), s.eps = eps → x0 ≤ s.x → RankVal s D.R → HostVal s C.P.Cpde D.host → HCVal s cD ch D.host (fun τ => (D.eTau τ : D.R.GG)) D.hc bT → |dlogH D.host| ≤ s.x ^ s.eps → D.s.Del = (Delv s cD : ℚ) → D.host.CT2 = C.CT2 → Fintype.card D.what₂.Word = ⌈3 * Real.exp (C.CGam * (D.R.m : ℝ) ^ 5 * D.R.f * s.L) ^ 2 * s.x ^ C.P.CF⌉₊ → D.div.etaF = 6 * s.x ^ (-C.P.CF) → (∀ u, Real.log (D.mem u).A.GamP = C.CGam * (D.R.m : ℝ) ^ 5 * D.R.f * s.L) → (∀ t, (s.a ≤ (aT t : ℝ) ∧ (aT t : ℝ) ≤ s.a + s.a / ((D.R.k : ℝ) * s.x ^ (Scale.A / 2))) ∧ s.b' ≤ (bT t : ℝ) ∧ (bT t : ℝ) ≤ s.b' + 2 * (D.R.n : ℝ) * s.delta1 * s.x ^ s.eps * G.La C.GK s * s.b' / (D.R.k : ℝ)) → (∀ τ (t : D.host.TT) (h : 0 < D.R.k), (D.eTau τ : D.R.GG) = D.R.tau1 t → (D.hc τ).u ⟨0, h⟩ = (aT t : ℚ) + ((D.R.k : ℚ) - 1) / 2 ∧ (D.hc τ).u ⟨D.R.k - 1, by omega⟩ = -(bT t : ℚ) - ((D.R.k : ℚ) - 1) / 2) → (∀ w, D.what₂.muAt w = D.what₂.mu0 → ∀ j, 1 ≤ j → j ≤ D.R.m → D.what₂.Aj j w = 0) → ∃ L : SizeData₂ D, L.sc = s ∧ L.aT = aT ∧ L.bT = bT ∧ Val C cD ch L := by
  intro eps C cD ch h0 h1 hC hcD hch
  obtain ⟨hfix, hCc, -, -, -, -, -, -, -, -, -, -, -, -, hmid, -⟩ := hC
  have hLa : 1 ≤ C.GK.La := hmid _ (by simp [FC.cMid])
  have hGam : 1 ≤ C.CGam := hmid _ (by simp [FC.cMid])
  have hCt : C.Ct = 401 := hfix.2.2.2.2.2.2.2.2.2
  obtain ⟨x1, hx1⟩ := bottom_window_le eps C.GK h0 h1 hLa
  obtain ⟨x2, hx2⟩ := GlobalTheory.T.windows_of_explicitParameters eps cD ch C.P.Cpde h0 h1 hcD hch
  refine ⟨max (max x1 x2) ((max C.P.Cpde 1) ^ (100 / eps)), ?_⟩
  intro s D aT bT he hx0 hR hH hHC hdl hDel hCT2 hW heta hG hwin htop hA
  have hx : max x1 x2 ≤ s.x := le_trans (le_max_left _ _) hx0
  have hCo : C.P.Cpde ≤ s.x ^ (s.eps / 100) := by
    have hM : (0 : ℝ) ≤ max C.P.Cpde 1 := le_trans zero_le_one (le_max_right _ _)
    have h3 : (max C.P.Cpde 1) ^ (100 / eps) ≤ s.x := le_trans (le_max_right _ _) hx0
    have h4 := Real.rpow_le_rpow (Real.rpow_nonneg hM _) h3 (show 0 ≤ eps / 100 by positivity)
    rw [← Real.rpow_mul hM, show 100 / eps * (eps / 100) = 1 by field_simp, Real.rpow_one] at h4
    rw [he]
    exact (le_max_left _ _).trans h4
  have hb := hx1 s D.R he (le_trans (le_max_left _ _) hx) hR
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13⟩ :=
    hx2 s D bT he (le_trans (le_max_right _ _) hx) hR hH
      (fun t => ⟨(hwin t).2.1, by linarith [(hwin t).2.2]⟩) hHC
  have hDelR : ((D.s.Del : ℚ) : ℝ) = (Delv s cD : ℝ) := by rw [hDel]; norm_cast
  have hkp : (0 : ℝ) < D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : 0 < D.R.k)
  have hmp : (0 : ℝ) < D.R.m := by
    have := D.R.two_le_m
    exact_mod_cast (by omega : 0 < D.R.m)
  have hnp : (0 : ℝ) < D.R.n := by
    unfold Ranks.n
    exact_mod_cast D.R.ord_pos
  have hxp : 0 < s.x := lt_trans one_pos s.one_lt_alt
  have hh0 : (0 : ℝ) < (h0v s ch : ℝ) := by
    have : 0 < ⌈s.x ^ ch⌉₊ := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hxp _)
    unfold h0v
    exact_mod_cast (by omega : 0 < 2 * ⌈s.x ^ ch⌉₊)
  have hDp : (0 : ℝ) < (Delv s cD : ℝ) := by
    rw [← hDelR]; exact_mod_cast D.s.Del_pos
  let L : SizeData₂ D :=
    { sc := s
      aT := aT
      aT_win := fun t => (hwin t).1
      bT := bT
      bT_ge := fun t => (hwin t).2.1
      top_u := fun τ t h hτ => by
        obtain ⟨e1, e2⟩ := htop τ t h hτ
        rw [e1, e2]
        push_cast
        exact ⟨rfl, rfl⟩
      top_b := w1
      supp := ∅
      gain := fun _ _ => 0
      F := fun _ _ => 0
      E := fun _ _ _ => 0
      tau := fun _ => 0
      io := fun _ => 0
      gain_supp := fun _ _ _ => rfl
      F_supp := fun _ _ _ => rfl
      E_supp := fun _ _ _ _ => rfl
      tau_supp := fun _ _ => rfl
      io_supp := fun _ _ => rfl
      gain_g := fun _ _ _ => rfl
      b_le := w2
      untwisted := fun w h j j1 j2 => ⟨hA w h j j1 j2, rfl⟩
      not_inert := fun _ _ _ => ⟨fun _ => rfl, rfl, rfl⟩
      drop := ∅
      drop_alt := fun _ => Set.notMem_empty _
      F_conj := fun _ _ => rfl
      F_above := fun _ _ _ _ _ => rfl
      j0 := ⌈Real.logb 5 ((D.R.n : ℝ) * D.R.N D.R.m / D.R.m)⌉₊
      logFiveDepth_le := Nat.le_ceil _
      weightLength_ge_depth := w11
      logDerivativeAtOne := dlogL D 1
      logDerivative_at_one_eq := rfl
      split_tie := hH.split_tie
      o_tie := hH.o_le.trans hCo
      QS_tie := by
        have h3 := hH.QS_le
        have h4 := mul_le_mul_of_nonneg_right hCo hnp.le
        have h5 : 0 ≤ s.x ^ (s.eps / 100) * D.R.n := by positivity
        show (D.host.QS : ℝ) ≤ 4 * D.R.n * s.x ^ (s.eps / 100)
        nlinarith
      NuLat := fun _ => ⊥
      de2 := (D.host.T2.card : ℝ) / D.R.n
      thickDensity_pos := div_pos (by exact_mod_cast w12) hnp
      thickDensity_le_one := (div_le_one hnp).mpr (by exact_mod_cast w13)
      typeDensity_eq_card_div := rfl
      LaG := G.La C.GK s
      Sc := (D.R.k : ℝ) * (4 * (Delv s cD : ℝ))
      etaSz := (D.R.m : ℝ) * (h0v s ch : ℝ)
      Sc_pos := by positivity
      Sc_eq := by rw [hDelR]
      Cc := C.Cc
      win_thick := w3
      win_top := w4
      win_thin := w5
      cloud_gap := by rw [hCc]; exact w6
      cloud_v := w7
      cloud_u := fun u τ i i1 i2 =>
        middle_between (D.hcW u τ) (by rw [D.hcW_v]; exact w7 τ) i i1 i2
      be_close := w8
      etaSz_pos := by positivity
      TTw := fun _ => Finset.univ
      TTw_full := fun _ _ => rfl
      Ct := C.Ct
      t_win := ⟨w9, by rw [hCt]; exact w10⟩
      CGam := C.CGam
      CGam_pos := by linarith
      Gam_eq := hG
      wPart := fun _ _ _ _ => 1
      wPart_ge := fun _ _ _ _ => le_rfl
      lenMN := fun _ _ => 0 }
  exact ⟨L, rfl, rfl, rfl,
    { ranks := hR
      host := hH
      hc := hHC
      dlog := hdl
      Del_eq := hDel
      eta_eq := rfl
      La_eq := rfl
      bT_le := fun t => (hwin t).2.2
      logFiveDepth_eq := rfl
      Ct_eq := rfl
      Cc_eq := rfl
      CGam_eq := rfl
      secondConstant_eq := hCT2
      words := hW
      etaF_eq := heta }⟩

end GlobalTheory.EX
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

theorem _root_.GlobalTheory.T.fieldIso_lattices_form_taylor_correspond : ∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (a b : ℕ), s.Ok → (∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (z : TaylorLogMetric.VC D a b), z ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (s.lat N) (s.lat N') ↔ (fun τ => z (s.iT τ)) ∈ LamC (X.embC s.σ₀) δ (ambOf s B χ cD).AA N N') ∧ (∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), Even a → Even b → IsSdLat N → IsSdLat N' → TaylorLogMetric.admitted D a b (s.lat N) (s.lat N')) ∧ (∀ z w : TaylorLogMetric.VC D a b, TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) z w = HV (ambOf s B χ cD).sc (fun τ => z (s.iT τ)) (fun τ => w (s.iT τ))) ∧ ∀ G : TaylorLogMetric.VC D a b → ℂ, (∀ k : ℕ, ContDiff ℂ k G) → ∀ m : DVar X.Tau a b →₀ ℕ, derivAt0 (fun z : VCx X.Tau a b => G fun τ => z (s.iT.symm τ)) m = (m.prod fun _ n => (n.factorial : ℂ)) * TaylorLogMetric.taylor D G (m.mapDomain fun v => (s.iT v.1, v.2)) := by
  first | exact @GlobalTheory.SeamTransport.transport | exact GlobalTheory.SeamTransport.transport | (intros; apply GlobalTheory.SeamTransport.transport <;> assumption)
end
