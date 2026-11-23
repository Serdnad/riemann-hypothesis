module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SupportProposition
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalModelPeriodLattices
public import Formalism.SharpRestriction.CuspSpanNormBounds.OscillatoryIntegralBounds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle034
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle036
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDict
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle035
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DataCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IntegralApproximation
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
import Mathlib.RingTheory.WittVector.IsPoly
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

@[expose] public section

section

noncomputable section

namespace Formalism.L2.SG.WConst

open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.RealObj Formalism.MainNotions.S.LocalSplitGroups

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section LinAlg

variable {r : ℕ}

theorem Dl_scale (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (c : Fin (r + 1) → ℂ) (l : ℕ) (hl : l ≤ r + 1) :
    Formalism.L2.SG.RealObj.Dl (r := r) (fun a b => c a * Z a b * c b) l = (∏ a : Fin l, c (Fin.castLE hl a)) ^ 2 * Formalism.L2.SG.RealObj.Dl Z l := by
  simp only [Formalism.L2.SG.RealObj.Dl, dif_pos hl]

  have h : Matrix.submatrix (fun a b => c a * Z a b * c b : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (Fin.castLE hl) (Fin.castLE hl) =
      Matrix.of (fun i j => c (Fin.castLE hl i) *
        Matrix.of (fun i j => c (Fin.castLE hl j) * (Z.submatrix (Fin.castLE hl) (Fin.castLE hl)) i j) i j) := by
    ext i j
    show c (Fin.castLE hl i) * Z (Fin.castLE hl i) (Fin.castLE hl j) * c (Fin.castLE hl j) =
      c (Fin.castLE hl i) * (c (Fin.castLE hl j) * Z (Fin.castLE hl i) (Fin.castLE hl j))
    ring
  rw [h, Matrix.det_mul_column, Matrix.det_mul_row]
  ring

theorem Gv_scale (T T' : ℝ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (c : Fin (r + 1) → ℂ)
    (hc : c (Fin.last r) = 1) :
    Formalism.L2.SG.RealObj.Gv T T' (fun a b => c a * Z a b * c b) = ‖∏ a : Fin r, c a.castSucc‖ ^ 4 * Formalism.L2.SG.RealObj.Gv T T' Z := by
  have h1 := Dl_scale Z c (r + 1) (le_refl (r + 1))
  have h0 := Dl_scale Z c r (Nat.le_succ r)
  have hp1 : (∏ a : Fin (r + 1), c (Fin.castLE (le_refl (r + 1)) a)) = ∏ a : Fin r, c a.castSucc := by
    rw [Fin.prod_univ_castSucc]
    show (∏ a : Fin r, c a.castSucc) * c (Fin.last r) = _
    rw [hc, mul_one]
  have hp0 : (∏ a : Fin r, c (Fin.castLE (Nat.le_succ r) a)) = ∏ a : Fin r, c a.castSucc := rfl
  simp only [Formalism.L2.SG.RealObj.Gv]
  rw [h1, h0, hp1, hp0, norm_mul, norm_mul, norm_pow]
  ring

private theorem norm_Dl_ZhatO_eq_norm_Dl (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (l : ℕ) :
    ‖Formalism.L2.SG.RealObj.Dl (Formalism.L2.SG.RealObj.ZhatO Z) l‖ = ‖Formalism.L2.SG.RealObj.Dl Z l‖ := by
  simp only [Formalism.L2.SG.RealObj.Dl]
  split_ifs with hl
  · have h : ((Formalism.L2.SG.RealObj.ZhatO Z).submatrix (Fin.castLE hl) (Fin.castLE hl)) =
        Matrix.of (fun i j => (-1 : ℂ) ^ (r - (Fin.castLE hl j).1) *
          (Z.submatrix (Fin.castLE hl) (Fin.castLE hl)) i j) := by
      ext i j
      rfl
    rw [h, Matrix.det_mul_row, norm_mul]
    simp
  · rfl

theorem Gv_zhatO (T T' : ℝ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) : Formalism.L2.SG.RealObj.Gv T T' (Formalism.L2.SG.RealObj.ZhatO Z) = Formalism.L2.SG.RealObj.Gv T T' Z := by
  simp only [Formalism.L2.SG.RealObj.Gv, norm_Dl_ZhatO_eq_norm_Dl]

end LinAlg

section Scale

theorem sum_range_sub_two (r : ℕ) : (∑ i ∈ Finset.range r, (r - i)) * 2 = r * (r + 1) := by
  induction r with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ']
    simp only [Nat.add_sub_add_right, Nat.sub_zero]
    rw [add_mul, ih]
    ring

theorem sum_sub_two (r : ℕ) : (∑ a : Fin r, (r - a.1)) * 2 = r * (r + 1) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => r - i) r]
  exact sum_range_sub_two r

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem ZX_scale (u u' : D.what₂.Word) (sc : ℝ) (γ : X.B.I.Ginf) (v : InfinitePlace X.B.I.F) :
    ZX X u u' sc γ v = fun a b => ((sc : ℂ) ^ (D.R.rS - a.1))⁻¹ * ZX X u u' 1 γ v a b * ((sc : ℂ) ^ (D.R.rS - b.1))⁻¹ := by
  funext a b
  simp [ZX, Formalism.L2.SG.RealObj.Zhat, frm, famSc, Formalism.L2.SG.HidaSetting.hJ, Matrix.mulVec_smul, star_smul]
  ring

theorem GX_scale (u u' : D.what₂.Word) {sc : ℝ} (hsc : 0 < sc) (γ : X.B.I.Ginf) (v : InfinitePlace X.B.I.F) :
    GX X u u' sc γ v = (sc ^ (2 * D.R.rS * (D.R.rS + 1)))⁻¹ * GX X u u' 1 γ v := by
  have hc : ((sc : ℂ) ^ (D.R.rS - (Fin.last D.R.rS).1))⁻¹ = 1 := by simp
  have hG := Gv_scale (Tw u) (Tw u') (ZX X u u' 1 γ v) (fun a => ((sc : ℂ) ^ (D.R.rS - a.1))⁻¹) hc
  beta_reduce at hG
  simp only [GX]
  rw [ZX_scale X u u' sc γ v, hG]
  congr 1
  have hn : ‖∏ a : Fin D.R.rS, ((sc : ℂ) ^ (D.R.rS - (Fin.castSucc a).1))⁻¹‖ =
      (sc ^ (∑ a : Fin D.R.rS, (D.R.rS - a.1)))⁻¹ := by
    rw [norm_prod]
    simp only [norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsc, Fin.coe_castSucc]
    rw [Finset.prod_inv_distrib, Finset.prod_pow_eq_pow_sum]
  have hS : (∑ a : Fin D.R.rS, (D.R.rS - a.1)) * 4 = 2 * D.R.rS * (D.R.rS + 1) := by
    have h2 := sum_sub_two D.R.rS
    calc (∑ a : Fin D.R.rS, (D.R.rS - a.1)) * 4 = ((∑ a : Fin D.R.rS, (D.R.rS - a.1)) * 2) * 2 := by ring
      _ = 2 * D.R.rS * (D.R.rS + 1) := by rw [h2]; ring
  rw [hn, inv_pow, ← pow_mul, hS]

end Scale

section Pt

theorem prod_normSq_embS (D : D7) (x : D.host.E) :
    ∏ τ : D.what₂.Tau, ‖Formalism.MainNotions.S.embS D τ x‖ ^ 2 = ((|Algebra.norm ℚ x| : ℚ) : ℝ) := by
  have := Formalism.MainNotions.InterlacingSignCuts.host_totallyComplex D
  have h := InfinitePlace.prod_eq_abs_norm x
  rw [Formalism.MainNotions.InterlacingSignCuts.prod_places D] at h
  rw [← h]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [InfinitePlace.mult_isComplex ⟨_, IsTotallyComplex.isComplex _⟩, Formalism.MainNotions.InterlacingSignCuts.plOf_apply]
  rfl

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem ptC_eq (v : InfinitePlace X.B.I.F) (w : Point D.host.E (D.R.rS + 1)) :
    ptC X v w = (ptMat w).map (Formalism.MainNotions.S.embS D (X.pl v)) := by
  simp only [ptC, X.φ_eq, RingEquiv.apply_symm_apply]

theorem Dl_ptC (v : InfinitePlace X.B.I.F) (w : Point D.host.E (D.R.rS + 1)) (l : ℕ) (hl : l ≤ D.R.rS + 1) :
    Formalism.L2.SG.RealObj.Dl (ptC X v w) l = Formalism.MainNotions.S.embS D (X.pl v) (Dmin w l) := by
  rw [ptC_eq]
  simp only [Formalism.L2.SG.RealObj.Dl, dif_pos hl, Dmin]
  rw [RingHom.map_det]
  rfl

private theorem embS_conjF_eq_conj_embS (τ : D.what₂.Tau) (x : D.host.E) :
    Formalism.MainNotions.S.embS D τ (D.conjF x) = starRingEnd ℂ (Formalism.MainNotions.S.embS D τ x) :=
  Formalism.L2.SG.Pf.emb_conjF τ x

theorem Gv_ptC (u u' : D.what₂.Word) (v : InfinitePlace X.B.I.F) (w : Point D.host.E (D.R.rS + 1)) :
    Gv (Tw u) (Tw u') (ptC X v w) =
      (Formalism.MainNotions.S.embS D (X.pl v) (Gpt (D.mem u).A.T (D.mem u').A.T w)).re := by
  simp only [Gv]
  rw [Dl_ptC X v w (D.R.rS + 1) le_rfl, Dl_ptC X v w D.R.rS (Nat.le_succ _)]
  simp only [Gpt, map_sub, map_mul, map_natCast, embS_conjF_eq_conj_embS, Complex.mul_conj]
  simp [Complex.normSq_eq_norm_sq, Tw]
  rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_re]

theorem embS_GPoint_im (τ : D.what₂.Tau) (T T' : ℕ) (w : Point D.host.E (D.R.rS + 1)) :
    (Formalism.MainNotions.S.embS D τ (Gpt T T' w)).im = 0 := by
  simp only [Gpt, map_sub, map_mul, map_natCast, embS_conjF_eq_conj_embS, Complex.mul_conj]
  simp

end Pt

section Prod

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem card_places : Fintype.card (InfinitePlace X.B.I.F) = D.R.f := by
  rw [Fintype.card_congr X.pl, D.what₂.card_Tau]

theorem isPtRep_gamW {u u' : D.what₂.Word} {w : Point D.host.E (D.R.rS + 1)} (h : ∃ γ, IsPtRep X u u' w γ) :
    IsPtRep X u u' w (gamW X u u' w) := by
  simp only [gamW, dif_pos h]
  exact h.choose_spec

theorem GX_gamW (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (h : ∃ γ, IsPtRep X u u' w γ)
    (v : InfinitePlace X.B.I.F) :
    GX X u u' D.host.rdE (gamW X u u' w) v = (D.host.rdE ^ (2 * D.R.rS * (D.R.rS + 1)))⁻¹ *
      (Formalism.MainNotions.S.embS D (X.pl v) (Gpt (D.mem u).A.T (D.mem u').A.T w)).re := by
  rw [GX_scale X u u' (Formalism.MainNotions.LocalModelPeriodLattices.rdE_pos D) (gamW X u u' w) v]
  congr 1
  simp only [GX]
  rw [← Gv_zhatO, isPtRep_gamW X h v, Gv_ptC]

theorem prod_re_embS_GPoint (T T' : ℕ) (w : Point D.host.E (D.R.rS + 1)) (hT : TotPos (Gpt T T' w)) :
    ∏ τ : D.what₂.Tau, (Formalism.MainNotions.S.embS D τ (Gpt T T' w)).re =
      Real.sqrt ((|Algebra.norm ℚ (Gpt T T' w)| : ℚ) : ℝ) := by
  have hpos : ∀ τ : D.what₂.Tau, 0 < (Formalism.MainNotions.S.embS D τ (Gpt T T' w)).re := fun τ => hT τ
  have hnorm : ∀ τ : D.what₂.Tau, ‖Formalism.MainNotions.S.embS D τ (Gpt T T' w)‖ = (Formalism.MainNotions.S.embS D τ (Gpt T T' w)).re := by
    intro τ
    have e : Formalism.MainNotions.S.embS D τ (Gpt T T' w) = ((Formalism.MainNotions.S.embS D τ (Gpt T T' w)).re : ℂ) := by
      apply Complex.ext <;> simp [embS_GPoint_im τ T T' w]
    rw [congrArg norm e, Complex.norm_real, Real.norm_of_nonneg (hpos τ).le]
  calc ∏ τ : D.what₂.Tau, (Formalism.MainNotions.S.embS D τ (Gpt T T' w)).re
      = Real.sqrt ((∏ τ : D.what₂.Tau, (Formalism.MainNotions.S.embS D τ (Gpt T T' w)).re) ^ 2) :=
        (Real.sqrt_sq (Finset.prod_nonneg fun τ _ => (hpos τ).le)).symm
    _ = Real.sqrt (∏ τ : D.what₂.Tau, ‖Formalism.MainNotions.S.embS D τ (Gpt T T' w)‖ ^ 2) := by
        rw [← Finset.prod_pow]
        simp only [hnorm]
    _ = _ := by rw [prod_normSq_embS]

theorem prod_GX_gamW (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (h : ∃ γ, IsPtRep X u u' w γ)
    (hT : TotPos (Gpt (D.mem u).A.T (D.mem u').A.T w)) :
    ∏ v, GX X u u' D.host.rdE (gamW X u u' w) v =
      ((D.host.rdE ^ (2 * D.R.rS * (D.R.rS + 1)))⁻¹) ^ D.R.f *
        Real.sqrt ((|Algebra.norm ℚ (Gpt (D.mem u).A.T (D.mem u').A.T w)| : ℚ) : ℝ) := by
  simp only [GX_gamW X u u' w h]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, card_places]
  congr 1
  rw [← prod_re_embS_GPoint _ _ w hT]
  exact Fintype.prod_equiv X.pl _ _ (fun v => rfl)

end Prod

end Formalism.L2.SG.WConst
end
end

section

noncomputable section

open scoped Classical TensorProduct
open Matrix NumberField

namespace Formalism.L2.SG.RhoPf

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section W3

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem fuX : (X.Fu u).X = Xs X := by
  rw [FlagG.X, X.Fu_e]
  rfl

theorem AH_stab {Λ : Submodule (𝓞 D.host.E) (VS D).V} {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hγ : γ ∈ AH X u Λ) : γ ∈ stabF D (X.Fu u) := by
  obtain ⟨hi, he, -, hz, -⟩ := hγ
  refine ⟨hi, fun j => ?_, ?_⟩
  · unfold Formalism.MainNotions.S.FlagG.Xa
    rw [Submodule.map_span, Set.image_image]
    congr 1
    apply Set.image_congr
    intro a _
    rw [X.Fu_e u]
    exact he a
  · show γ (X.Fu u).z = (X.Fu u).z
    rw [X.flagZVector u]
    exact hz

def indA (Λ : Submodule (𝓞 D.host.E) (VS D).V) (γ : ↥(AH X u Λ)) : WbQ D (X.Fu u) → WbQ D (X.Fu u) :=
  ind (X.Fu u) (AH_stab X u γ.2)

theorem prV_perp (v : (VS D).V) : prV X v ∈ perpS (VS D) (X.Fu u).X := by
  intro x hx
  rw [fuX] at hx
  exact hT_Xs_prV X hx v

theorem prV_fix (w : (VS D).V) (he : ∀ a, (VS D).hT (X.eX a) w = 0) (hf : ∀ a, (VS D).hT (X.fY a) w = 0) :
    prV X w = w := by
  rw [prV_apply]
  simp [he, hf]

theorem prV_of_fix (g : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hgi : g ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (hge : ∀ a, g (X.eX a) = X.eX a) (hgf : ∀ a, g (X.fY a) = X.fY a) (v : (VS D).V) :
    prV X (g (prV X v)) = g (prV X v) := by
  have h1 : ∀ a, (VS D).hT (X.eX a) (g (prV X v)) = 0 := fun a => by
    rw [← hge a, hgi, hT_e_prV]
  have h2 : ∀ a, (VS D).hT (X.fY a) (g (prV X v)) = 0 := fun a => by
    rw [← hgf a, hgi, hT_f_prV]
  exact prV_fix X _ h1 h2

theorem fix_sub_prV (g : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hge : ∀ a, g (X.eX a) = X.eX a) (hgf : ∀ a, g (X.fY a) = X.fY a) (v : (VS D).V) :
    g (v - prV X v) = v - prV X v := by
  rw [sub_prV_eq]

  simp [map_sum, map_smul, hge, hgf]

theorem indA_inj (Λ : Submodule (𝓞 D.host.E) (VS D).V) : Function.Injective (indA X u Λ) := by
  intro γ γ' hγγ
  obtain ⟨hi, he, hf, -, -⟩ := γ.2
  obtain ⟨hi', he', hf', -, -⟩ := γ'.2
  apply Subtype.ext
  apply LinearEquiv.ext
  intro y
  have hq := congrFun hγγ (Submodule.Quotient.mk ⟨prV X y, prV_perp X u y⟩)
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk _ at hq
  rw [Submodule.Quotient.eq] at hq
  have hd : γ.1 (prV X y) - γ'.1 (prV X y) ∈ Xs X := by
    rw [← fuX X u]
    exact hq
  have h0 := prV_Xs X hd
  rw [map_sub, prV_of_fix X γ.1 hi he hf, prV_of_fix X γ'.1 hi' he' hf', sub_eq_zero] at h0
  calc γ.1 y = γ.1 (y - prV X y) + γ.1 (prV X y) := by rw [← map_add (f := _), sub_add_cancel]
    _ = γ'.1 (y - prV X y) + γ'.1 (prV X y) := by
        rw [fix_sub_prV X γ.1 he hf, fix_sub_prV X γ'.1 he' hf', h0]
    _ = γ'.1 y := by rw [← map_add (f := _), sub_add_cancel]

theorem mem_lat_gmap (h : Hfin X u) {γ0 : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hΛ : Formalism.HermitianLatticesTheory.gmap γ0 (lat X u h) = lat X u h) :
    (∀ y ∈ latOf X u h, γ0 y ∈ latOf X u h) ∧ (∀ y ∈ latOf X u h, γ0.symm y ∈ latOf X u h) := by
  constructor
  · intro y hy
    rw [← lat_coe] at hy ⊢
    rw [SetLike.mem_coe, ← hΛ, mem_gmap, LinearEquiv.symm_apply_apply]
    exact hy
  · intro y hy
    rw [← lat_coe] at hy ⊢
    rw [SetLike.mem_coe, ← hΛ, mem_gmap] at hy
    exact hy

theorem autLz_range (h : Hfin X u) : autLz D (X.Fu u) (lat X u h) = Set.range (indA X u (lat X u h)) := by
  ext φ
  rw [autLz_iff]
  constructor
  · rintro ⟨γ0, hγ0, hΛ, rfl⟩
    have hinv : γ0⁻¹ ∈ stabF D (X.Fu u) := st_inv (X.Fu u) hγ0
    let γ : (VS D).V ≃ₗ[D.host.E] (VS D).V := LinearEquiv.ofLinear (gW X γ0) (gW X γ0⁻¹)
      (LinearMap.ext fun y => gW_gW X u hγ0 hinv (fun w => LinearEquiv.apply_symm_apply γ0 w) y)
      (LinearMap.ext fun y => gW_gW X u hinv hγ0 (fun w => LinearEquiv.symm_apply_apply γ0 w) y)
    have hm := mem_lat_gmap X u h hΛ
    have hAH : γ ∈ AH X u (lat X u h) := by
      refine ⟨fun x y => gW_isom X u hγ0 x y, fun a => gW_e X a, fun a => gW_f X a, stabilizer_fix_anisotropic X u hγ0, ?_⟩
      ext y
      rw [mem_gmap]
      constructor
      · intro hy
        rw [← SetLike.mem_coe, lat_coe] at hy ⊢
        have := gW_mem X u h h hm.1 hy
        have e : gW X γ0 (γ.symm y) = y := gW_gW X u hγ0 hinv (fun w => LinearEquiv.apply_symm_apply γ0 w) y
        rwa [e] at this
      · intro hy
        rw [← SetLike.mem_coe, lat_coe] at hy ⊢
        exact gW_mem X u h h (fun w hw => hm.2 w hw) hy
    refine ⟨⟨γ, hAH⟩, ?_⟩
    funext q
    refine Submodule.Quotient.induction_on _ q (fun x => ?_)
    show ind (X.Fu u) (AH_stab X u hAH) (Submodule.Quotient.mk x) = ind (X.Fu u) hγ0 (Submodule.Quotient.mk x)
    rw [ind_mk, ind_mk, Submodule.Quotient.eq]
    show gW X γ0 x.1 - γ0 x.1 ∈ (X.Fu u).X
    apply (show Xs X ≤ (X.Fu u).X from (fuX X u).ge)
    have hx : ∀ a, (VS D).hT (X.eX a) x.1 = 0 := fun a => x.2 _ (by rw [fuX X u]; exact eX_mem_Xs X a)
    have h1 := sub_prV_mem_Xs X hx
    have h2 := stab_Xs X u hγ0 h1
    have h3 := stab_perp X u hγ0 x.1
    have e : gW X γ0 x.1 - γ0 x.1 =
        (x.1 - prV X x.1) - γ0 (x.1 - prV X x.1) - (γ0 (prV X x.1) - prV X (γ0 (prV X x.1))) := by
      rw [gW_apply, map_sub]
      abel
    rw [e]
    exact Submodule.sub_mem _ (Submodule.sub_mem _ h1 h2) h3
  · rintro ⟨γ, rfl⟩
    exact ⟨γ.1, AH_stab X u γ.2, γ.2.2.2.2.2, rfl⟩

theorem card_AH (h : Hfin X u) :
    Nat.card ↥(AH X u (lat X u h)) = Nat.card ↥(autLz D (X.Fu u) (lat X u h)) := by
  rw [autLz_range]
  exact (Nat.card_range_of_injective (indA_inj X u _)).symm

end W3

end Formalism.L2.SG.RhoPf
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.ProdEP2Core

open Formalism.L2.SG.Pf.IndexCocycleOrbits

variable {G : Type} [Group G]

structure Retr (S N : Subgroup G) (π : G → G) : Prop where
  le : S ≤ N
  mul : ∀ x ∈ N, ∀ y ∈ N, π (x * y) = π x * π y
  mem : ∀ x ∈ N, π x ∈ S
  id : ∀ s ∈ S, π s = s

theorem Retr.one {S N : Subgroup G} {π : G → G} (h : Retr S N π) : π 1 = 1 := by
  have h1 := h.mul 1 N.one_mem 1 N.one_mem
  rw [mul_one] at h1
  simpa using h1

theorem Retr.inv {S N : Subgroup G} {π : G → G} (h : Retr S N π) {x : G} (hx : x ∈ N) : π x⁻¹ = (π x)⁻¹ := by
  have h1 := h.mul x⁻¹ (N.inv_mem hx) x hx
  rw [inv_mul_cancel, h.one] at h1
  exact eq_inv_of_mul_eq_one_left h1.symm

def img {S N : Subgroup G} {π : G → G} (h : Retr S N π) (H : Subgroup G) (hH : H ≤ N) : Subgroup G where
  carrier := π '' H
  mul_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x * y, H.mul_mem hx hy, h.mul x (hH hx) y (hH hy)⟩
  one_mem' := ⟨1, H.one_mem, h.one⟩
  inv_mem' := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x⁻¹, H.inv_mem hx, h.inv (hH hx)⟩

theorem cj_eq_cj_img {S N : Subgroup G} {π : G → G} (h : Retr S N π) {H : Subgroup G} (hH : H ≤ N) {g₀ : G}
    (hg : g₀ ∈ N) (hC : cj g₀ H ≤ S) : cj g₀ H = cj (π g₀) (img h H hH) := by
  ext y
  rw [mem_cj, mem_cj]
  constructor
  · intro hy
    have hyS : y ∈ S := hC ((mem_cj).2 hy)
    have hyN : y ∈ N := h.le hyS
    refine (Set.mem_image π _ _).2 ⟨g₀ * y * g₀⁻¹, hy, ?_⟩
    rw [h.mul _ (N.mul_mem hg hyN) _ (N.inv_mem hg), h.mul _ hg _ hyN, h.inv hg, h.id y hyS]
  · intro hy
    obtain ⟨x, hx, hxe⟩ := (Set.mem_image π _ _).1 hy
    have hz : g₀⁻¹ * x * g₀ ∈ cj g₀ H := by
      rw [mem_cj]
      simpa [mul_assoc] using hx
    have hzS := hC hz
    have e1 : π (g₀⁻¹ * x * g₀) = g₀⁻¹ * x * g₀ := h.id _ hzS
    rw [h.mul _ (N.mul_mem (N.inv_mem hg) (hH hx)) _ hg, h.mul _ (N.inv_mem hg) _ (hH hx), h.inv hg,
      hxe] at e1
    have hyz : y = g₀⁻¹ * x * g₀ := by
      rw [← e1]
      group
    rw [hyz]
    simpa [mul_assoc] using hx

end Formalism.L2.SG.Pf.ProdEP2Core
end
end

section

namespace Formalism.L2.SG.IntegralApproximation

theorem AlpBound_holds (D : Formalism.BasicNotions.D7) : Formalism.L2.SG.DataCut.AlpBound D := alpBoundU D

end Formalism.L2.SG.IntegralApproximation
end
