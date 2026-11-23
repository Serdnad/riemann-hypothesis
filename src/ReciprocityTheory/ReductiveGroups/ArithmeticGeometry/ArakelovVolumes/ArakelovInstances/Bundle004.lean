module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.DiagonalCurvatureCoefficient
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthonormalFlagTranslateHolds
public import ReciprocityTheory.AnalyticForms.LeviForms.HomDens
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
public import Mathlib.Analysis.Complex.CauchyIntegral

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.AR.Inst

open NumberField ReciprocityTheory.ChartRestriction.G.FD

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem normFactor_rightBorel_holds : NfacRmulStatement (E := E) := by
  unfold NfacRmulStatement
  intro r X la x hx b hb
  have key : ∀ (τ : X.Ψ) (i : Fin r),
      ‖dmin X.Gm (rmul x b) τ i.succ / dmin X.Gm (rmul x b) τ i.castSucc‖ ^ (-(la τ i : ℝ) / 2)
        = (‖b τ i i‖ ^ la τ i)⁻¹ *
          ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ ^ (-(la τ i : ℝ) / 2) := by
    intro τ i
    have ht : 0 < ‖b τ i i‖ := norm_pos_iff.mpr (FrameDegreeData.bdiag_ne (X := X) hb τ i)
    rw [FrameDegreeData.ratio_rmul (X := X) x hx hb τ i, eq_inv_mul_iff_mul_eq₀ (zpow_ne_zero _ ht.ne')]
    exact FrameDegreeData.factor_eq _ _ ht (norm_nonneg _) (la τ i)
  have hbc : ‖bchar la b‖ = ∏ τ, ∏ i, ‖b τ i i‖ ^ la τ i := by
    simp only [bchar, norm_prod, norm_zpow]
  simp only [Data.nfac, key, Finset.prod_mul_distrib, Finset.prod_inv_distrib, hbc]

private theorem ringHom_cc_eq_conj (τ : E →+* ℂ) (y : E) : τ (cc y) = starRingEnd ℂ (τ y) :=
  NumberField.IsCMField.complexEmbedding_complexConj E τ y

private theorem sum_mul_gram_mul_cc_of_isUStab {r : ℕ} (G : Matrix (Fin r) (Fin r) E)
    (Λ : Submodule (𝓞 E) (Fin r → E)) (γ : GL (Fin r) E) (hγ : IsUStab G Λ γ) (j l : Fin r) :
    ∑ a, ∑ b, (γ : Matrix (Fin r) (Fin r) E) a j * G a b * cc ((γ : Matrix (Fin r) (Fin r) E) b l)
      = G j l := by
  have hs : ∀ k : Fin r, Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) (Pi.single k 1)
      = fun a => (γ : Matrix (Fin r) (Fin r) E) a k := by
    intro k
    funext a
    change ∑ c, (γ : Matrix (Fin r) (Fin r) E) a c * (Pi.single k (1 : E) : Fin r → E) c = _
    simp [Pi.single_apply]
  have h := hγ.1 (Pi.single j 1) (Pi.single l 1)
  rw [hs j, hs l] at h
  have hc : ∀ c : Fin r, cc ((Pi.single l (1 : E) : Fin r → E) c) = (Pi.single l (1 : E) : Fin r → E) c := by
    intro c
    by_cases hcl : c = l
    · subst hcl
      simp [cc]
    · simp [cc, hcl]
  change herm G (fun a => (γ : Matrix (Fin r) (Fin r) E) a j)
    (fun a => (γ : Matrix (Fin r) (Fin r) E) a l) = G j l
  rw [h]
  simp only [herm, hc]
  simp [Pi.single_apply]

private theorem sum_four_comm_arakelov_instances {ι : Type*} [Fintype ι] (F : ι → ι → ι → ι → ℂ) :
    ∑ a, ∑ b, ∑ j, ∑ l, F a b j l = ∑ j, ∑ l, ∑ a, ∑ b, F a b j l := by
  calc ∑ a, ∑ b, ∑ j, ∑ l, F a b j l = ∑ a, ∑ j, ∑ b, ∑ l, F a b j l :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a, ∑ j, ∑ l, ∑ b, F a b j l :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ j, ∑ a, ∑ l, ∑ b, F a b j l := Finset.sum_comm
    _ = ∑ j, ∑ l, ∑ a, ∑ b, F a b j l := Finset.sum_congr rfl fun j _ => Finset.sum_comm

private theorem hermC_mulVec_map_of_isUStab {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (Λ : Submodule (𝓞 E) (Fin r → E)) (γ : GL (Fin r) E) (hγ : IsUStab G Λ γ)
    (u v : Fin r → ℂ) :
    hermC τ G (Matrix.mulVec ((γ : Matrix (Fin r) (Fin r) E).map τ) u)
        (Matrix.mulVec ((γ : Matrix (Fin r) (Fin r) E).map τ) v) = hermC τ G u v := by
  have key : ∀ j l : Fin r, ∑ a, ∑ b, τ ((γ : Matrix (Fin r) (Fin r) E) a j) * τ (G a b) *
      starRingEnd ℂ (τ ((γ : Matrix (Fin r) (Fin r) E) b l)) = τ (G j l) := by
    intro j l
    rw [← sum_mul_gram_mul_cc_of_isUStab G Λ γ hγ j l]

    simp only [map_sum, map_mul, ringHom_cc_eq_conj]
  have hmv : ∀ (M : Matrix (Fin r) (Fin r) ℂ) (w : Fin r → ℂ) (i : Fin r),
      Matrix.mulVec M w i = ∑ j, M i j * w j := fun _ _ _ => rfl
  have lhs : hermC τ G (Matrix.mulVec ((γ : Matrix (Fin r) (Fin r) E).map τ) u)
        (Matrix.mulVec ((γ : Matrix (Fin r) (Fin r) E).map τ) v)
      = ∑ a, ∑ b, ∑ j, ∑ l, u j * (τ ((γ : Matrix (Fin r) (Fin r) E) a j) * τ (G a b) *
          starRingEnd ℂ (τ ((γ : Matrix (Fin r) (Fin r) E) b l))) * starRingEnd ℂ (v l) := by

    simp only [hermC, hmv, Matrix.map_apply, map_sum, map_mul]
    simp only [Finset.sum_mul]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  have rhs : hermC τ G u v = ∑ j, ∑ l, ∑ a, ∑ b, u j * (τ ((γ : Matrix (Fin r) (Fin r) E) a j) *
      τ (G a b) * starRingEnd ℂ (τ ((γ : Matrix (Fin r) (Fin r) E) b l))) * starRingEnd ℂ (v l) := by
    simp only [hermC]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    rw [← key j l]
    simp only [Finset.mul_sum, Finset.sum_mul]
  rw [lhs, rhs]
  exact sum_four_comm_arakelov_instances (fun a b j l => u j * (τ ((γ : Matrix (Fin r) (Fin r) E) a j) * τ (G a b) *
      starRingEnd ℂ (τ ((γ : Matrix (Fin r) (Fin r) E) b l))) * starRingEnd ℂ (v l))

private theorem gram_map_mul_of_isUStab' {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (Λ : Submodule (𝓞 E) (Fin r → E)) (γ : GL (Fin r) E) (hγ : IsUStab G Λ γ)
    (M : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G ((γ : Matrix (Fin r) (Fin r) E).map τ * M) = gram τ G M := by
  have hcol : ∀ a, col ((γ : Matrix (Fin r) (Fin r) E).map τ * M) a
      = Matrix.mulVec ((γ : Matrix (Fin r) (Fin r) E).map τ) (col M a) := fun _ => rfl
  ext a b
  simp only [gram, Matrix.of_apply, hcol, hermC_mulVec_map_of_isUStab τ G Λ γ hγ]

private theorem dmin_lact_of_mem_Γ {r : ℕ} (X : Data E r) (γ : GL (Fin r) E) (hγ : γ ∈ X.Γ)
    (x : Frame X.Ψ r) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm (lact γ x) τ i = dmin X.Gm x τ i := by
  have hm : mat (lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := rfl
  simp only [dmin, hm, gram_map_mul_of_isUStab' τ.1 X.Gm X.Λ γ (X.Γ_stab γ hγ)]

theorem normFactor_leftAction_holds : NfacLactStatement (E := E) := by
  unfold NfacLactStatement
  intro r X la γ hγ x hx
  simp only [Data.nfac, dmin_lact_of_mem_Γ X γ hγ]

theorem pointwiseNorm_invariance_holds : PnormInvStatement (E := E) := by
  unfold PnormInvStatement
  intro r X la P hP γ hγ x hx b hb
  obtain ⟨-, hPr, hPl⟩ := hP
  have hlx : lact γ x ∈ X.dom := by
    refine fun τ => ⟨?_, fun i => ?_⟩
    · have hm : mat (lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := rfl
      have hd : ((γ : Matrix (Fin r) (Fin r) E).map τ.1).det = τ.1 (γ : Matrix (Fin r) (Fin r) E).det :=
        (RingHom.map_det τ.1 _).symm
      rw [hm, Matrix.det_mul, hd]
      exact mul_ne_zero ((map_ne_zero τ.1).mpr
        ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit γ)).ne_zero) (hx τ).1
    · rw [dmin_lact_of_mem_Γ X γ hγ]
      exact (hx τ).2 i
  have hcomm : lact γ (rmul x b) = rmul (lact γ x) b := by
    funext τ
    show ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * (mat x τ * mat b τ) : Matrix (Fin r) (Fin r) ℂ)
      = ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) * mat b τ
    exact (Matrix.mul_assoc _ _ _).symm
  have hN : ∀ y : Frame X.Ψ r, X.pnorm la P y = ‖P y‖ * X.nfac la y := fun _ => rfl
  obtain ⟨n, hn, hpow⟩ := X.χ_fin la
  have h1 : ‖X.χ la γ‖ ^ n = 1 := by rw [← norm_pow, hpow γ hγ, norm_one]
  have hχ : ‖X.χ la γ‖ = 1 := (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').mp h1
  rw [hcomm, FrameDegreeData.pnorm_rmul (X := X) la P hPr (lact γ x) hlx b hb, hN, hN, hPl γ hγ x hx,
    normFactor_leftAction_holds r X la γ hγ x hx, norm_mul, hχ, one_mul]

end

end ReciprocityTheory.ChartRestriction.G.AR.Inst
end

section

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf

open Polynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.P Filter Topology

variable {r m : ℕ} (hm : m ≤ r) (D : Fin r → ℝ) (Y : Matrix (Fin r) (Fin r) ℂ)

theorem fn_zero_ne (hD : ∀ k, D k ≠ 0) : fn hm D Y 0 ≠ 0 := by
  unfold fn
  simp only [Pi.zero_apply]
  have h : Gnz hm D Y 0 = Matrix.diagonal fun a : Fin m => ((D (Fin.castLE hm a) : ℝ) : ℂ) := by
    simp only [Gnz, Gz, zero_smul, sub_zero, add_zero, Matrix.conjTranspose_one, Matrix.one_mul,
      Matrix.mul_one]
    first
    | exact Matrix.submatrix_diagonal _ _ (Fin.castLE_injective hm)
    | simp [Matrix.submatrix_diagonal _ _ (Fin.castLE_injective hm)]
    | (ext i j
       simp [Matrix.diagonal_apply, (Fin.castLE_injective hm).eq_iff])
  rw [h, Matrix.det_diagonal, ← Complex.ofReal_prod, Complex.ofReal_re]
  exact Finset.prod_ne_zero_iff.2 fun a _ => hD _

theorem levi_logfn (hD : ∀ k, D k ≠ 0) :
    levi (fun v => Real.log |fn hm D Y v|) 0 (fun _ => 1) =
      levi (fn hm D Y) 0 (fun _ => 1) / fn hm D Y 0 := by
  have hc : ContDiffAt ℝ 2 (fn hm D Y) 0 := (contDiff_fn hm D Y).contDiffAt
  have h0 := fn_zero_ne hm D Y hD
  have h := leviHalfLogAbs (ι := Fin 1) (fn hm D Y) 0 hc h0 (fderiv_fn_zero hm D Y) (fun _ => 1)
  have hL : ContDiffAt ℝ 2 (fun x => (1 / 2 : ℝ) * Real.log |fn hm D Y x|) 0 := by
    have e : (fun x => (1 / 2 : ℝ) * Real.log |fn hm D Y x|) = fun x => (1 / 2 : ℝ) * Real.log (fn hm D Y x) := by
      funext x; rw [Real.log_abs]
    rw [e]
    exact contDiffAt_const.mul (hc.log h0)
  have e : (fun v => Real.log |fn hm D Y v|) =
      fun v => (1 / 2 * Real.log |fn hm D Y v|) + 1 * (1 / 2 * Real.log |fn hm D Y v|) := by
    funext v; ring
  rw [e, levi_add_smul 1 hL hL, h]
  field_simp
  ring

theorem Gz_herm (ζ : ℂ) : (Gz hm D Y ζ)ᴴ = Gz hm D Y ζ := by
  have hD : (Matrix.diagonal fun k => (D k : ℂ))ᴴ = Matrix.diagonal fun k => (D k : ℂ) := by
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext k
    simp
  first
  | simp only [Gz, Matrix.conjTranspose_submatrix, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hD, Matrix.mul_assoc]
  | (unfold Gz
     rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
       Matrix.conjTranspose_conjTranspose]
     erw [hD]
     simp only [Matrix.mul_assoc])

theorem fn_eq (v : Fin 1 → ℂ) : fn hm D Y v = ‖pd hm Y v‖ ^ 2 * fY hm D Y v := by
  have key : ∀ (p G : ℂ), (star p * (G * p)).re = ‖p‖ ^ 2 * G.re := by
    intro p G
    have h1 : star p * (G * p) = ((Complex.normSq p : ℝ) : ℂ) * G := by
      rw [Complex.star_def, ← Complex.mul_conj]
      ring
    rw [h1, Complex.re_ofReal_mul]
    first
    | rw [Complex.normSq_eq_norm_sq]
    | rw [← Complex.sq_norm]
    | simp [Complex.normSq_eq_norm_sq]
  simp only [fn, fY, Gnz, pd, Matrix.det_mul, Matrix.det_conjTranspose]
  exact key _ _

theorem pd_eval (v : Fin 1 → ℂ) : pd hm Y v = (lin (-(Ym hm Y))).det.eval (v 0) := by
  unfold pd lin
  rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  by_cases h : i = j
  · subst h
    simp [Matrix.one_apply, sub_eq_add_neg] <;> ring
  · simp [Matrix.one_apply, h, sub_eq_add_neg] <;> ring

theorem pd_analytic : AnalyticAt ℂ (pd hm Y) 0 := by
  have e : pd hm Y = (fun z => (lin (-(Ym hm Y))).det.eval z) ∘ (fun v : Fin 1 → ℂ => v 0) :=
    funext fun v => pd_eval hm Y v
  rw [e]
  exact ((lin (-(Ym hm Y))).det.differentiable.analyticAt _).comp
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).analyticAt _)

theorem pd_zero : pd hm Y 0 = 1 := by
  simp [pd]

theorem logpd_analytic : AnalyticAt ℂ (fun v => 2 * Complex.log (pd hm Y v)) 0 := by
  have h0 : pd hm Y 0 ∈ Complex.slitPlane := by
    rw [pd_zero]
    exact Complex.one_mem_slitPlane
  exact analyticAt_const.mul ((pd_analytic hm Y).clog h0)

theorem logpd_eq (v : Fin 1 → ℂ) : Real.log (‖pd hm Y v‖ ^ 2) = (2 * Complex.log (pd hm Y v)).re := by
  have h : (2 * Complex.log (pd hm Y v)).re = 2 * (Complex.log (pd hm Y v)).re := by
    simp [Complex.mul_re]
  rw [h, Complex.log_re, Real.log_pow]
  push_cast
  ring

theorem levi_logpd (w : Fin 1 → ℂ) : levi (fun v => Real.log (‖pd hm Y v‖ ^ 2)) 0 w = 0 := by
  have e : (fun v => Real.log (‖pd hm Y v‖ ^ 2)) = fun v => (2 * Complex.log (pd hm Y v)).re :=
    funext fun v => logpd_eq hm Y v
  rw [e]
  exact levi_re_analytic (logpd_analytic hm Y) w

theorem core_levi (hD : ∀ k, D k ≠ 0) :
    levi (fun v => Real.log |fY hm D Y v|) 0 (fun _ => 1) =
      ∑ a : Fin m, (D (Fin.castLE hm a))⁻¹ * Sa hm D Y a := by
  have hP : (∏ a : Fin m, D (Fin.castLE hm a)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => hD _
  have hfY0 : fY hm D Y 0 ≠ 0 := by rw [fY_zero]; exact hP
  have h0 := fn_zero_ne hm D Y hD
  have hcont : ContinuousAt (fY hm D Y) 0 := (contDiff_fY hm D Y).continuous.continuousAt
  have hpdc : ContinuousAt (pd hm Y) 0 := (pd_analytic hm Y).continuousAt
  have hev : (fun v => Real.log |fY hm D Y v|) =ᶠ[𝓝 0]
      fun v => Real.log |fn hm D Y v| + (-1) * Real.log (‖pd hm Y v‖ ^ 2) := by
    filter_upwards [hcont.eventually_ne hfY0, hpdc.eventually_ne (by rw [pd_zero]; exact one_ne_zero)]
      with v h1 h2
    have hp : ‖pd hm Y v‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 h2)
    rw [Real.log_abs, Real.log_abs, fn_eq, Real.log_mul hp h1]
    ring
  have hL1 : ContDiffAt ℝ 2 (fun v => Real.log |fn hm D Y v|) 0 := by
    have e : (fun v => Real.log |fn hm D Y v|) = fun v => Real.log (fn hm D Y v) := by
      funext v; rw [Real.log_abs]
    rw [e]
    exact (contDiff_fn hm D Y).contDiffAt.log h0
  have hL2 : ContDiffAt ℝ 2 (fun v => Real.log (‖pd hm Y v‖ ^ 2)) 0 := by
    rw [funext (logpd_eq hm Y)]
    exact Complex.reCLM.contDiff.contDiffAt.comp _
      ((logpd_analytic hm Y).contDiffAt.restrict_scalars ℝ)
  rw [levi_congr hev, levi_add_smul (-1) hL1 hL2, levi_logpd, levi_logfn hm D Y hD, levi_fn hm D Y hD,
    fn_zero, mul_zero, add_zero, mul_div_cancel_left₀ _ hP]

end ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
end
end
