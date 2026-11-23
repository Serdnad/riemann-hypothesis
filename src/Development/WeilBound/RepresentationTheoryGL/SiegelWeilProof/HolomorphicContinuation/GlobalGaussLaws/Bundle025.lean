module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle002
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle024
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle019
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle016
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle020
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.CompAtAdd
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle022
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle023
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

open Matrix Complex

namespace PositivityTheory.Rg.Sw.Glob.VacC

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.Glob PositivityTheory.Rg.Sw.Glob.VacS

variable {m n : ℕ}

def sigR (ε : Fin m → Bool) (a : Fin m) : ℝ := if ε a then 1 else -1

theorem sgn_eq (ε : Fin m → Bool) (a : Fin m) : sgn ε a = ((sigR ε a : ℝ) : ℂ) := by
  unfold sgn sigR
  by_cases h : ε a <;> simp [h]

theorem ftLoc_eq (ε : Fin m → Bool) (s : ℝ) (f : (Fin m → Fin n → ℂ) → ℂ) (u : Fin m → Fin n → ℂ) :
    ftLoc ε s f u = ftG (sigR ε) s f u := by
  simp only [ftLoc, ftG]
  congr 1
  funext y
  have key : ((of u)ᴴ * diagonal (sgn ε) * of y).trace.re =
      ∑ a, ∑ j, sigR ε a * ((starRingEnd ℂ) (u a j) * y a j).re := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.of_apply, Complex.re_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    rw [sgn_eq, mul_comm (star (u a j)) _, mul_assoc, Complex.re_ofReal_mul]
    rfl
  rw [key]

theorem gramX_diag (ε : Fin m → Bool) (u : Fin m → Fin n → ℂ) (j : Fin n) :
    gramX ε u j j = ∑ a, ((sigR ε a : ℝ) : ℂ) * ((‖u a j‖ ^ 2 : ℝ) : ℂ) := by

  simp only [gramX, Qp, Qb, evX, map_sub, map_sum, map_mul, MvPolynomial.eval_X, if_true,
  Bool.false_eq_true, if_false, Finset.sum_filter]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : ε a <;> simp [h, sigR, Complex.conj_mul']

theorem chN_DG (ε : Fin m → Bool) (t : ℝ) (β : Fin n → ℝ) (K : ℂ) (γ : Fin m → Fin n → ℂ) (u : Fin m → Fin n → ℂ) :
    chN ε t (diagonal fun j => (β j : ℂ)) u * DG K γ u =
      DG K (fun a j => γ a j - I * t * (sigR ε a : ℂ) * (β j : ℂ)) u := by
  simp only [chN, DG]
  simp only [← Complex.exp_sum]
  rw [mul_left_comm, ← Complex.exp_add]
  congr 2
  have htr : (diagonal (fun j => (β j : ℂ)) * gramX ε u).trace = ∑ j, (β j : ℂ) * gramX ε u j j := by
    simp [Matrix.trace, Matrix.diagonal_mul]
  rw [htr]
  simp_rw [gramX_diag, Finset.mul_sum]
  conv_lhs => arg 1; rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem dg_const (K γ0 : ℂ) (v : Fin m → Fin n → ℂ) :
    DG K (fun _ _ => γ0) v = K * cexp (-γ0 * ∑ a, ∑ j, ((‖v a j‖ ^ 2 : ℝ) : ℂ)) := by
  simp only [DG]
  congr 1
  rw [Finset.mul_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, Complex.exp_sum]

theorem vac_eq (ε : Fin m → Bool) (t c : ℝ) : vac (n := n) ε t c = DG 1 (fun _ _ => (c : ℂ)) := by
  funext y
  rw [dg_const, one_mul]
  simp only [vac, gZf]
  congr 1
  have hsum : (gramB (epsT t ε) true y).trace + (gramB (epsT t ε) false y).trace =
      ∑ a, ∑ j, ((‖y a j‖ ^ 2 : ℝ) : ℂ) := by

    simp only [Matrix.trace, Matrix.diag, gramB, Qb, evX, map_sum, Finset.sum_filter]
    rw [← Finset.sum_add_distrib, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases h : epsT t ε a <;> simp [h, Complex.conj_mul']
  rw [smul_mul_assoc, one_mul, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
    smul_mul_assoc, one_mul, Matrix.trace_smul, Matrix.trace_smul]
  simp only [smul_eq_mul, Complex.star_def, Complex.conj_I]
  linear_combination ((c : ℂ) * ((gramB (epsT t ε) true y).trace + (gramB (epsT t ε) false y).trace)) *
    Complex.I_sq + (-(c : ℂ)) * hsum

theorem levF_diag (e : ℤ) (δ : Fin n → ℝ) (hδ : ∀ j, 0 < δ j) (K : ℂ) (γ : Fin m → Fin n → ℂ) :
    levF e (diagonal fun j => (δ j : ℂ)) (DG K γ) =
      DG (K * (∏ j, (δ j : ℂ)) ^ m) (fun a j => γ a j * ((δ j : ℂ) ^ 2)) := by
  funext u
  simp only [levF, DG, Matrix.det_diagonal]
  have hD : (∏ j, (δ j : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => by exact_mod_cast (hδ j).ne'
  have hs : star (∏ j, (δ j : ℂ)) = ∏ j, (δ j : ℂ) := by
    rw [← Complex.ofReal_prod]
    exact Complex.conj_ofReal _
  rw [hs, ← zpow_add₀ hD, add_sub_cancel, zpow_natCast]
  rw [← mul_assoc, mul_comm (_ ^ m) K]
  congr 1
  refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun j _ => ?_
  congr 1
  simp only [Matrix.mul_diagonal, Matrix.of_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    mul_pow, sq_abs]
  push_cast
  ring

end PositivityTheory.Rg.Sw.Glob.VacC
end
end

section

noncomputable section

open scoped Matrix ComplexOrder
open Matrix

namespace PositivityTheory.Rg.Sw.Glob.GaussH

variable {n : ℕ}

theorem actZ_conj (y : GR n) {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : IsSiegel Z) :
    (actZ y Z)ᴴ = ((mR y).toBlocks₁₁ * Zᴴ + (mR y).toBlocks₁₂) * ((mR y).toBlocks₂₁ * Zᴴ + (mR y).toBlocks₂₂)⁻¹ := by
  have hg := inG_mR y
  have hM := det_CZD hg hZ
  have hM' := det_CZhD hg hZ
  have hid := identG hg Z Zᴴ
  rw [sub_self] at hid
  have hE := sub_eq_zero.mp hid
  unfold actZ
  set N := (mR y).toBlocks₁₁ * Z + (mR y).toBlocks₁₂
  set M := (mR y).toBlocks₂₁ * Z + (mR y).toBlocks₂₂
  set N' := (mR y).toBlocks₁₁ * Zᴴ + (mR y).toBlocks₁₂
  set M' := (mR y).toBlocks₂₁ * Zᴴ + (mR y).toBlocks₂₂
  have hMh : IsUnit (Mᴴ).det := by
    rw [det_conjTranspose]
    exact hM.star
  rw [conjTranspose_mul, conjTranspose_nonsing_inv]
  calc (Mᴴ)⁻¹ * Nᴴ = (Mᴴ)⁻¹ * (Nᴴ * M') * M'⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hM', Matrix.mul_one]
    _ = (Mᴴ)⁻¹ * (Mᴴ * N') * M'⁻¹ := by rw [hE]
    _ = N' * M'⁻¹ := by rw [← Matrix.mul_assoc, nonsing_inv_mul _ hMh, Matrix.one_mul]

theorem isSiegel_actZ (y : GR n) {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : IsSiegel Z) : IsSiegel (actZ y Z) := by
  have hg := inG_mR y
  have hM := det_CZD hg hZ
  have hid := identG hg Z Z
  unfold IsSiegel actZ
  unfold IsSiegel at hZ
  set N := (mR y).toBlocks₁₁ * Z + (mR y).toBlocks₁₂
  set M := (mR y).toBlocks₂₁ * Z + (mR y).toBlocks₂₂
  have hMM : M * M⁻¹ = 1 := mul_nonsing_inv _ hM
  have hMM' : ∀ X : Matrix (Fin n) (Fin n) ℂ, (M⁻¹)ᴴ * (Mᴴ * X) = X := by
    intro X
    rw [← Matrix.mul_assoc, ← conjTranspose_mul, hMM, conjTranspose_one, Matrix.one_mul]
  have hZZ : Mᴴ * N - Nᴴ * M = Z - Zᴴ := by
    rw [← neg_sub, hid, neg_sub]
  have key : -(Complex.I / 2) • (N * M⁻¹ - (N * M⁻¹)ᴴ) =
      (M⁻¹)ᴴ * (-(Complex.I / 2) • (Z - Zᴴ)) * M⁻¹ := by
    rw [← hZZ, conjTranspose_mul, Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    rw [Matrix.mul_sub, Matrix.sub_mul]
    simp only [Matrix.mul_assoc, hMM, Matrix.mul_one, hMM']
  rw [key]
  refine Matrix.PosDef.conjTranspose_mul_mul_same hZ ?_
  exact mulVec_injective_iff_isUnit.mpr ((isUnit_iff_isUnit_det _).mpr (isUnit_nonsing_inv_det _ hM))

end PositivityTheory.Rg.Sw.Glob.GaussH
end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.DilCH

variable {D : D7} {n : ℕ} {θ : InfFam D} {V : HSp D} {τ : D.what₂.Tau} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ}

theorem tens_cancel (hθ : IsInfFam θ) (hfr : IsUnit fr.det) {Ψ : Mx D V.rank n → ℂ} (hΨ : AwayCls θ τ fr Ψ)
    {x₀ : Mx D V.rank n} (hx₀ : Ψ x₀ ≠ 0) {F G : (Fin V.rank → Fin n → ℂ) → ℂ}
    (h : tens θ τ fr F Ψ = tens θ τ fr G Ψ) : F = G := by
  funext u
  obtain ⟨x, hxu, hxo, hxf⟩ := DilBH.pointAt θ hθ τ fr hfr x₀ u
  have hΨx : Ψ x = Ψ x₀ := hΨ.1 x x₀ hxo hxf
  have := congrFun h x
  simp only [tens, hxu, hΨx] at this
  exact mul_right_cancel₀ hx₀ this

variable {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} {ι : GR n →* G D n}
  {L : GR n → ((Fin V.rank → Fin n → ℂ) → ℂ) → ((Fin V.rank → Fin n → ℂ) → ℂ)}

theorem L_sub (hL : IsLocFact ω τ fr ι L) (hθ : IsInfFam θ) (hfr : IsUnit fr.det) {Ψ : Mx D V.rank n → ℂ}
    (hΨ : AwayCls θ τ fr Ψ) {x₀ : Mx D V.rank n} (hx₀ : Ψ x₀ ≠ 0) (y : GR n) {f g : (Fin V.rank → Fin n → ℂ) → ℂ}
    (hf : IsSch f) (hg : IsSch g) : L y (f - g) = L y f - L y g := by
  have h := hL.2 y Ψ hΨ (f - g) (SchwartzDifferenceQuotient.isSch_sub hf hg)
  have e : (⟨tens θ τ fr (f - g) Ψ, hΨ.2 _ (SchwartzDifferenceQuotient.isSch_sub hf hg)⟩ : schwartzA θ V.rank n) =
      ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩ - ⟨tens θ τ fr g Ψ, hΨ.2 g hg⟩ :=
    Subtype.ext (by funext x; simp only [tens, Submodule.coe_sub]; show (f _ - g _) * _ = f _ * _ - g _ * _; ring)
  rw [e, map_sub, Submodule.coe_sub, hL.2 y Ψ hΨ f hf, hL.2 y Ψ hΨ g hg] at h
  refine tens_cancel hθ hfr hΨ hx₀ ?_
  rw [← h]; funext x
  show tens θ τ fr (L y f) Ψ x - tens θ τ fr (L y g) Ψ x = _
  simp only [tens]
  show _ = (L y f _ - L y g _) * _
  ring

theorem L_smul (hL : IsLocFact ω τ fr ι L) (hθ : IsInfFam θ) (hfr : IsUnit fr.det) {Ψ : Mx D V.rank n → ℂ}
    (hΨ : AwayCls θ τ fr Ψ) {x₀ : Mx D V.rank n} (hx₀ : Ψ x₀ ≠ 0) (y : GR n) (a : ℂ) {f : (Fin V.rank → Fin n → ℂ) → ℂ}
    (hf : IsSch f) : L y (fun u => a * f u) = fun u => a * L y f u := by
  have h := hL.2 y Ψ hΨ _ (SchwartzDifferenceQuotient.isSch_smul a hf)
  have e : (⟨tens θ τ fr (fun u => a * f u) Ψ, hΨ.2 _ (SchwartzDifferenceQuotient.isSch_smul a hf)⟩ : schwartzA θ V.rank n) =
      a • ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩ :=
    Subtype.ext (by funext x; simp [tens, mul_assoc])
  rw [e, map_smul, Submodule.coe_smul, hL.2 y Ψ hΨ f hf] at h
  refine tens_cancel hθ hfr hΨ hx₀ ?_
  rw [← h]; funext x; simp [tens, mul_assoc]

theorem L_mul (hL : IsLocFact ω τ fr ι L) (hθ : IsInfFam θ) (hfr : IsUnit fr.det) {Ψ : Mx D V.rank n → ℂ}
    (hΨ : AwayCls θ τ fr Ψ) {x₀ : Mx D V.rank n} (hx₀ : Ψ x₀ ≠ 0) (y y' : GR n) {f : (Fin V.rank → Fin n → ℂ) → ℂ}
    (hf : IsSch f) : L (y * y') f = L y (L y' f) := by
  have h := hL.2 (y * y') Ψ hΨ f hf
  have h' : ω (ι y') ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩ = ⟨tens θ τ fr (L y' f) Ψ, hΨ.2 _ (hL.1 y' f hf)⟩ :=
    Subtype.ext (hL.2 y' Ψ hΨ f hf)
  rw [map_mul, map_mul, Module.End.mul_apply, h', hL.2 y Ψ hΨ _ (hL.1 y' f hf)] at h
  exact tens_cancel hθ hfr hΨ hx₀ h.symm

theorem diffOn_iteratedDeriv {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (r : ℕ) :
    DifferentiableOn ℂ (iteratedDeriv r f) U := by
  induction r with
  | zero => simpa using hf
  | succ r ih => rw [iteratedDeriv_succ]; exact ih.deriv hU

theorem iteratedDeriv_ofReal {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hR : ∀ s : ℝ, (s : ℂ) ∈ U) (r : ℕ) : iteratedDeriv r (fun t : ℝ => f t) = fun t : ℝ => iteratedDeriv r f t := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    have hd : DifferentiableAt ℂ (iteratedDeriv r f) t :=
      (diffOn_iteratedDeriv hU hf r).differentiableAt (hU.mem_nhds (hR t))
    rw [iteratedDeriv_succ]
    exact (hd.hasDerivAt.comp_ofReal).deriv

end PositivityTheory.Rg.Sw.Glob.DilCH
end
end

section

noncomputable section

open Matrix Complex

namespace PositivityTheory.Rg.Sw.Glob.VacI

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.Glob PositivityTheory.Rg.Sw.Glob.VacB PositivityTheory.Rg.Sw.Glob.VacD PositivityTheory.Rg.Sw.Glob.VacG

variable {n : ℕ}

theorem blocks_kak (u u' : Matrix (Fin n) (Fin n) ℂ) (hu : uᴴ * u = 1) (hu' : u'ᴴ * u' = 1) (θ : Fin n → ℝ) :
    mM u * kth θ * mM u' = fromBlocks (u * (dR fun j => Real.cos (θ j)) * u') (u * (dR fun j => Real.sin (θ j)) * u')
      (-(u * (dR fun j => Real.sin (θ j)) * u')) (u * (dR fun j => Real.cos (θ j)) * u') := by
  have h1 : uᴴ⁻¹ = u := Matrix.inv_eq_right_inv hu
  have h2 : u'ᴴ⁻¹ = u' := Matrix.inv_eq_right_inv hu'
  simp only [mM, kth, dR, h1, h2, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, neg_zero, add_zero,
    zero_add, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]

theorem det_mM_unitary (u : Matrix (Fin n) (Fin n) ℂ) (hu : uᴴ * u = 1) : (mM u).det = u.det * u.det := by
  rw [mM_unitary u hu, det_fromBlocks_zero₂₁]

private theorem det_kth_eq_one (θ : Fin n → ℝ) : (kth θ).det = 1 := by
  have hL : (fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) (I • (1 : Matrix (Fin n) (Fin n) ℂ))
      (0 : Matrix (Fin n) (Fin n) ℂ) (1 : Matrix (Fin n) (Fin n) ℂ)).det = 1 := by
    rw [det_fromBlocks_zero₂₁]
    simp
  have hR : (fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) (-(I • (1 : Matrix (Fin n) (Fin n) ℂ)))
      (0 : Matrix (Fin n) (Fin n) ℂ) (1 : Matrix (Fin n) (Fin n) ℂ)).det = 1 := by
    rw [det_fromBlocks_zero₂₁]
    simp
  have key : fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) (I • (1 : Matrix (Fin n) (Fin n) ℂ))
        (0 : Matrix (Fin n) (Fin n) ℂ) (1 : Matrix (Fin n) (Fin n) ℂ) * kth θ *
        fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) (-(I • (1 : Matrix (Fin n) (Fin n) ℂ)))
        (0 : Matrix (Fin n) (Fin n) ℂ) (1 : Matrix (Fin n) (Fin n) ℂ)
      = fromBlocks (diagonal fun j => (Real.cos (θ j) : ℂ) - I * Real.sin (θ j)) (0 : Matrix (Fin n) (Fin n) ℂ)
          (-diagonal fun j => (Real.sin (θ j) : ℂ))
          (diagonal fun j => (Real.cos (θ j) : ℂ) + I * Real.sin (θ j)) := by
    simp only [kth, fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero,
      add_zero, zero_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_neg, Matrix.neg_mul]
    congr 1 <;> ext i j <;> by_cases h : i = j <;> simp [h, diagonal_apply] <;>
      first
      | ring1
      | linear_combination Complex.sin ((θ j : ℝ) : ℂ) * I_sq
  have hprod : ∏ j, (((Real.cos (θ j) : ℂ) - I * Real.sin (θ j)) * ((Real.cos (θ j) : ℂ) + I * Real.sin (θ j))) = 1 := by
    apply Finset.prod_eq_one
    intro j _
    have hp := Real.sin_sq_add_cos_sq (θ j)
    generalize Real.cos (θ j) = c at *
    generalize Real.sin (θ j) = s at *
    have hp' : (s : ℂ) ^ 2 + (c : ℂ) ^ 2 = 1 := by exact_mod_cast hp
    linear_combination hp' - (s : ℂ) ^ 2 * I_sq
  have h := congrArg Matrix.det key
  rw [det_mul, det_mul, hL, hR, det_fromBlocks_zero₁₂, det_diagonal, det_diagonal, ← Finset.prod_mul_distrib,
    hprod, one_mul, mul_one] at h
  exact h

theorem det_kth (θ : Fin n → ℝ) (hθ : ∀ j, -(Real.pi / 2) < θ j ∧ θ j ≤ Real.pi / 2) : (kth θ).det = 1 := by
  exact det_kth_eq_one θ

theorem jF_kak (e : ℤ) (p q : ℕ) (k : GR n) (u u' : Matrix (Fin n) (Fin n) ℂ) (θ : Fin n → ℝ) (hu : uᴴ * u = 1)
    (hu' : u'ᴴ * u' = 1) (hθ : ∀ j, -(Real.pi / 2) < θ j ∧ θ j ≤ Real.pi / 2) (hkm : mR k = mM u * kth θ * mM u') :
    jF e p q k (I • (1 : Matrix (Fin n) (Fin n) ℂ)) =
      (u.det * u.det * (u'.det * u'.det)) ^ e * (u.det * (∏ j, cexp (-(I * (θ j : ℂ)))) * u'.det) ^ (-(p : ℤ)) *
        (u.det * (∏ j, cexp (I * (θ j : ℂ))) * u'.det) ^ (-(q : ℤ)) := by
  have hdet : (mR k).det = u.det * u.det * (u'.det * u'.det) := by
    rw [hkm, det_mul, det_mul, det_mM_unitary u hu, det_mM_unitary u' hu', det_kth θ hθ, mul_one]
  have hk2 := hkm.trans (blocks_kak u u' hu hu' θ)
  have hdm : diagonal (fun j => cexp (-(I * (θ j : ℂ)))) =
      (dR fun j => Real.cos (θ j)) - I • (dR fun j => Real.sin (θ j)) := by
    ext a b
    by_cases h : a = b
    · subst h
      simp only [dR, diagonal_apply_eq, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      rw [show -(I * (θ a : ℂ)) = (-(θ a : ℂ)) * I by ring, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg,
        ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      ring
    · simp [dR, diagonal_apply, h]
  have hdp : diagonal (fun j => cexp (I * (θ j : ℂ))) =
      (dR fun j => Real.cos (θ j)) + I • (dR fun j => Real.sin (θ j)) := by
    ext a b
    by_cases h : a = b
    · subst h
      simp only [dR, diagonal_apply_eq, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      rw [show I * (θ a : ℂ) = (θ a : ℂ) * I by ring, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      ring
    · simp [dR, diagonal_apply, h]
  have hA : toBlocks₂₁ (mR k) * (I • (1 : Matrix (Fin n) (Fin n) ℂ)) + toBlocks₂₂ (mR k) =
      u * diagonal (fun j => cexp (-(I * (θ j : ℂ)))) * u' := by
    rw [hk2, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, hdm]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, smul_neg]
    abel
  have hZ : (I • (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ = -(I • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
    rw [conjTranspose_smul, conjTranspose_one, Complex.star_def, conj_I, neg_smul]
  have hB : toBlocks₂₁ (mR k) * (I • (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ + toBlocks₂₂ (mR k) =
      u * diagonal (fun j => cexp (I * (θ j : ℂ))) * u' := by
    rw [hZ, hk2, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, hdp, Matrix.mul_neg, Matrix.mul_smul, Matrix.mul_one]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, smul_neg, neg_neg]
    abel
  simp only [jF, hdet, hA, hB, det_mul, det_diagonal]

end PositivityTheory.Rg.Sw.Glob.VacI
end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.GaussH

variable {D : D7} {n : ℕ}

theorem isSch_smul {m : ℕ} {f : (Fin m → Fin n → ℂ) → ℂ} (hf : IsSch f) (c : ℂ) : IsSch (fun u => c * f u) := by
  obtain ⟨S, hS⟩ := hf
  exact ⟨c • S, by funext u; simp [hS]⟩

theorem locLin (hTI : TensInj) {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D}
    {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} {H : G D n → ℝ≥0}
    {l : D.what₂.Tau → ℝ} {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ν : Measure (GA D V)}
    {τ : D.what₂.Tau} {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} {ι : GR n →* G D n}
    (hcx : Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι) {L : GR n → ((Fin V.rank → Fin n → ℂ) → ℂ) → ((Fin V.rank → Fin n → ℂ) → ℂ)}
    (hL : IsLocFact ω τ fr ι L) (y : GR n) (c : ℂ) {f : (Fin V.rank → Fin n → ℂ) → ℂ} (hf : IsSch f) :
    L y (fun u => c * f u) = fun u => c * L y f u := by
  have hcf := isSch_smul hf c
  refine hTI D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx _ _ fun Ψ hΨ => ?_
  rw [← hL.2 y Ψ hΨ _ hcf]
  have e : (⟨tens θ τ fr (fun u => c * f u) Ψ, hΨ.2 _ hcf⟩ : schwartzA θ V.rank n) = c • ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩ := by
    apply Subtype.ext
    funext x
    simp [tens, mul_assoc]
  rw [e, map_smul, Submodule.coe_smul, hL.2 y Ψ hΨ f hf]
  funext x
  simp [tens, mul_assoc]

theorem abs_tLoc (l : D.what₂.Tau → ℝ) (τ : D.what₂.Tau) : |tLoc l τ| = cLoc l τ := by
  simp only [tLoc, cLoc, abs_mul, abs_of_pos Real.pi_pos, abs_two]

theorem GR_ext {y y' : GR n} (h : mR y = mR y') : y = y' := Subtype.ext (Units.ext h)

end PositivityTheory.Rg.Sw.Glob.GaussH
end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

theorem locMul_of : TensInj → LocMul := by
  intro hTI D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx L hL y y' f hf
  refine hTI D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx _ _ fun Ψ hΨ => ?_
  have hf' := hL.1 y' f hf
  rw [← hL.2 (y * y') Ψ hΨ f hf, ← hL.2 y Ψ hΨ _ hf', map_mul, map_mul, Module.End.mul_apply]
  congr 2
  apply Subtype.ext
  exact hL.2 y' Ψ hΨ f hf

end PositivityTheory.Rg.Sw.Glob
end
end
