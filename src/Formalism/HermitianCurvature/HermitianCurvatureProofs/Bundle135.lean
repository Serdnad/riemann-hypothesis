module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle126
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormalFormOrderZeroOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedS
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedLocSec
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle128
public import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
public import Formalism.HermitianCurvature.HeisenbergConjugationMeasurePreserving
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle098
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle070
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
public import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle121

@[expose] public section

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

open Formalism.FourierDecayAlt.P.NFx4.NO

section Curv

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] (d : Q.NFData P A)

def curvTh0 : A := d.L.ζ * d.L.nab + d.L.ζb * d.L.nabs

def curvK : A := d.κ (fun ρ => ((absTy P ρ : ℝ) : ℂ)) +
    algebraMap ℂ A (P.TT : ℂ) * d.L.GGi * d.κ (fun ρ => ((-2 * M.aC P ρ : ℝ) : ℂ))

theorem curv_theta_split : ThetaC d = curvTh0 d + curvK d := by
  unfold ThetaC curvTh0 curvK; abel

theorem curv_fc {x y : A} (hx : x ∈ ({d.L.ζ, d.L.ζi, d.L.ζb, d.L.ζbi, d.L.GG, d.L.GGi} : Set A))
    (hy : y ∈ ({d.L.ζ, d.L.ζi, d.L.ζb, d.L.ζbi, d.L.GG, d.L.GGi} : Set A)) : Commute x y :=
  d.L.fns_comm x (Or.inr hx) y (Or.inr hy)

theorem curvature_theta_commutator_zeta : curvTh0 d * d.L.ζb = d.L.ζb * curvTh0 d - d.L.ζb := by
  have h1 : Commute d.L.ζ d.L.ζb := curv_fc d (by simp) (by simp)
  unfold curvTh0
  simp only [add_mul, mul_add, mul_assoc, d.L.nab_ζb, d.L.nabs_ζb, mul_sub, mul_one]
  rw [h1.left_comm]
  abel

theorem curvature_theta_commutes_G : curvTh0 d * d.L.GG = d.L.GG * curvTh0 d := by
  have h1 : Commute d.L.ζ d.L.ζb := curv_fc d (by simp) (by simp)
  have h2 : Commute d.L.ζ d.L.GG := curv_fc d (by simp) (by simp)
  have h3 : Commute d.L.ζb d.L.GG := curv_fc d (by simp) (by simp)
  unfold curvTh0
  simp only [add_mul, mul_add, mul_assoc, d.L.nab_GG, d.L.nabs_GG, mul_sub]
  rw [h2.left_comm, h3.left_comm, h1.eq]
  abel

theorem curvature_theta_commutator_nabla : curvTh0 d * d.L.nab =
    d.L.nab * curvTh0 d - d.L.nab + d.L.ζb * (d.L.nabs * d.L.nab - d.L.nab * d.L.nabs) := by
  have e1 : ∀ X : A, d.L.nab * (d.L.ζ * X) = d.L.ζ * (d.L.nab * X) + X := fun X => by
    rw [← mul_assoc, d.L.nab_ζ, add_mul, one_mul, mul_assoc]
  have e2 : ∀ X : A, d.L.nab * (d.L.ζb * X) = d.L.ζb * (d.L.nab * X) := fun X => by
    rw [← mul_assoc, d.L.nab_ζb, mul_assoc]
  unfold curvTh0
  simp only [add_mul, mul_add, mul_assoc, e1, e2, mul_sub]
  abel

theorem curv_K_comm (hRel : d.Rel) {g : A} (hg : g ∈ ({d.L.ζb, d.L.GG} : Set A)) : curvK d * g = g * curvK d := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  have hg' : g ∈ ({d.L.ζ, d.L.ζi, d.L.ζb, d.L.ζbi, d.L.GG, d.L.GGi} : Set A) := by rcases hg with rfl | rfl <;> simp
  have hk : ∀ f : M.Ty P → ℂ, Commute (d.κ f) g := fun f => kap_comm_fn hRel f (Or.inl (Or.inr hg'))
  have hGi : Commute d.L.GGi g := curv_fc d (by simp) hg'
  have ha : Commute (algebraMap ℂ A (P.TT : ℂ)) g := Algebra.commute_algebraMap_left _ _
  exact ((hk _).add_left ((ha.mul_left hGi).mul_left (hk _))).eq

theorem curv_K_nab (hRel : d.Rel) : curvK d * d.L.nab = d.L.nab * curvK d +
    algebraMap ℂ A (P.TT : ℂ) * d.L.ζb * d.L.GGi * d.L.GGi * d.κ (fun ρ => ((-2 * M.aC P ρ : ℝ) : ℂ)) := by
  have hk : ∀ f : M.Ty P → ℂ, Commute (d.κ f) d.L.nab := fun f => kap_comm_fn hRel f (Or.inr (by simp))
  have ha : Commute (algebraMap ℂ A (P.TT : ℂ)) d.L.nab := Algebra.commute_algebraMap_left _ _
  have hζ : Commute (algebraMap ℂ A (P.TT : ℂ)) d.L.ζb := Algebra.commute_algebraMap_left _ _
  unfold curvK
  rw [add_mul, mul_add, (hk _).eq]
  have : algebraMap ℂ A (P.TT : ℂ) * d.L.GGi * d.κ (fun ρ => ((-2 * M.aC P ρ : ℝ) : ℂ)) * d.L.nab =
      d.L.nab * (algebraMap ℂ A (P.TT : ℂ) * d.L.GGi * d.κ (fun ρ => ((-2 * M.aC P ρ : ℝ) : ℂ))) +
      algebraMap ℂ A (P.TT : ℂ) * d.L.ζb * d.L.GGi * d.L.GGi * d.κ (fun ρ => ((-2 * M.aC P ρ : ℝ) : ℂ)) := by
    rw [mul_assoc _ _ d.L.nab, (hk _).eq, ← mul_assoc, mul_assoc _ d.L.GGi d.L.nab]
    rw [show d.L.nab * (algebraMap ℂ A (P.TT : ℂ) * d.L.GGi * d.κ (fun ρ => ((-2 * M.aC P ρ : ℝ) : ℂ))) =
      algebraMap ℂ A (P.TT : ℂ) * (d.L.nab * d.L.GGi) * d.κ (fun ρ => ((-2 * M.aC P ρ : ℝ) : ℂ)) by
        rw [← mul_assoc, ← mul_assoc, ← ha.eq]; simp only [mul_assoc]]
    rw [d.L.nab_GGi]
    rw [show d.L.GGi * d.L.nab = (d.L.GGi * d.L.nab - d.L.ζb * d.L.GGi * d.L.GGi) + d.L.ζb * d.L.GGi * d.L.GGi by abel]
    simp only [mul_add, add_mul, mul_assoc]
    rw [← mul_assoc (algebraMap ℂ A (P.TT : ℂ)) d.L.ζb, hζ.eq]
    simp only [mul_assoc]
    abel
  rw [this]
  abel

theorem curv_kap_theta (hRel : d.Rel) (f : M.Ty P → ℂ) : Commute (d.κ f) (ThetaC d) := by
  have hf : ∀ g ∈ d.L.fns ∪ {d.L.nab, d.L.nabs}, Commute (d.κ f) g := fun g hg => kap_comm_fn hRel f hg
  have hz : Commute (d.κ f) d.L.ζ := hf _ (Or.inl (by simp [R.LevelData.fns]))
  have hzb : Commute (d.κ f) d.L.ζb := hf _ (Or.inl (by simp [R.LevelData.fns]))
  have hGi : Commute (d.κ f) d.L.GGi := hf _ (Or.inl (by simp [R.LevelData.fns]))
  have hn : Commute (d.κ f) d.L.nab := hf _ (Or.inr (by simp))
  have hns : Commute (d.κ f) d.L.nabs := hf _ (Or.inr (by simp))
  have hkk : ∀ h : M.Ty P → ℂ, Commute (d.κ f) (d.κ h) := fun h => by
    show d.κ f * d.κ h = d.κ h * d.κ f
    rw [← map_mul, ← map_mul, mul_comm]
  unfold ThetaC
  exact (((hz.mul_right hn).add_right (hzb.mul_right hns)).add_right (hkk _)).add_right
    (((Algebra.commute_algebraMap_right _ _).mul_right hGi).mul_right (hkk _))

theorem curv_theta_zb (hRel : d.Rel) : ThetaC d * d.L.ζb = d.L.ζb * ThetaC d - d.L.ζb := by
  rw [curv_theta_split, add_mul, curvature_theta_commutator_zeta, curv_K_comm d hRel (by simp), mul_add]; abel

theorem curv_theta_GG (hRel : d.Rel) : ThetaC d * d.L.GG = d.L.GG * ThetaC d := by
  rw [curv_theta_split, add_mul, curvature_theta_commutes_G, curv_K_comm d hRel (by simp), mul_add]

theorem curv_theta_nab (hRel : d.Rel) : ThetaC d * d.L.nab = d.L.nab * ThetaC d - d.L.nab +
    d.L.ζb * (d.L.nabs * d.L.nab - d.L.nab * d.L.nabs) +
    algebraMap ℂ A (P.TT : ℂ) * d.L.ζb * d.L.GGi * d.L.GGi * d.κ (fun ρ => ((-2 * M.aC P ρ : ℝ) : ℂ)) := by
  rw [curv_theta_split, add_mul, curvature_theta_commutator_nabla, curv_K_nab d hRel, mul_add]; abel

theorem GG_mul_l0_eq (Y : ℂ) : d.L.GG * d.L.l0 Y = -(d.L.GG * d.L.nab) - algebraMap ℂ A (Y + 1 / 2) * d.L.ζb := by
  have h3 : Commute d.L.GG d.L.ζb := curv_fc d (by simp) (by simp)
  have ha : Commute d.L.GG (algebraMap ℂ A (Y + 1 / 2)) := Algebra.commute_algebraMap_right _ _
  unfold R.LevelData.l0
  rw [mul_sub, mul_neg, ← mul_assoc, ha.eq, mul_assoc, ← mul_assoc d.L.GG, h3.eq, mul_assoc, d.L.GG_GGi, mul_one]

theorem curv_key (hRel : d.Rel) (Y : ℂ) :
    ThetaC d * (d.L.GG * d.L.l0 Y) - d.L.GG * d.L.l0 Y * ThetaC d + d.L.GG * d.L.l0 Y =
      -(d.L.GG * (d.L.ζb * ((d.L.nabs * d.L.nab - d.L.nab * d.L.nabs) +
        algebraMap ℂ A (P.TT : ℂ) * d.L.GGi * d.L.GGi * d.κ (fun ρ => ((-2 * M.aC P ρ : ℝ) : ℂ))))) := by
  have hzbT : Commute d.L.ζb (algebraMap ℂ A (P.TT : ℂ)) := Algebra.commute_algebraMap_right _ _
  have r1 : ThetaC d * (d.L.GG * d.L.nab) = d.L.GG * (ThetaC d * d.L.nab) := by
    rw [← mul_assoc, curv_theta_GG d hRel, mul_assoc]
  have r2 : ThetaC d * (algebraMap ℂ A (Y + 1 / 2) * d.L.ζb) =
      algebraMap ℂ A (Y + 1 / 2) * (ThetaC d * d.L.ζb) := by
    rw [← mul_assoc, (Algebra.commute_algebraMap_right (Y + 1 / 2) (ThetaC d)).eq, mul_assoc]
  rw [GG_mul_l0_eq]
  simp only [mul_neg, neg_mul, mul_sub, sub_mul, r1, r2, curv_theta_nab d hRel, curv_theta_zb d hRel]
  simp only [mul_add, mul_sub, mul_assoc]
  rw [← mul_assoc d.L.ζb (algebraMap ℂ A (P.TT : ℂ)), hzbT.eq]
  simp only [mul_assoc]
  abel

theorem curvature_block_form_holds : GTCCurvBlock := by
  intro P A _ _ _ d hRel hc ρ
  have hκ : d.κ (dTy P ρ) = Pj d ρ := rfl
  rw [hκ]
  set Pp := Pj d ρ with hPp
  have hΘ : Pp * ThetaC d = ThetaC d * Pp := comm_Pj_of d (curv_kap_theta d hRel) ρ
  have hGGP : Pp * d.L.GG = d.L.GG * Pp := comm_Pj_of d (fun f => kap_GG hRel f) ρ
  have hl0P : Pp * d.L.l0 Complex.I = d.L.l0 Complex.I * Pp := comm_Pj_of d (fun f => kappa_commute_l0 hRel f _) ρ
  have hPP : Pp * Pp = Pp := Pj_idem d ρ
  have hx : M.xC P ρ Complex.I ≠ 0 := by
    unfold M.xC
    rw [Finset.prod_ne_zero_iff]
    intro i _ h
    have := congrArg Complex.im h
    simp at this
  have hPt : Pp * d.QQ Complex.I 1 0 * Pp = M.xC P ρ Complex.I • (d.L.GG * d.L.l0 Complex.I * Pp) := by
    rw [normal_form_lower_left, mul_add, add_mul, lower_sum_diagonal_zero hRel, add_zero]
    rw [← mul_assoc Pp, ← mul_assoc Pp, hGGP, mul_assoc d.L.GG Pp, Q.NFData.x, hPp, Pj_kap, ← hPp]
    rw [mul_smul_comm, smul_mul_assoc, smul_mul_assoc]
    congr 1
    simp only [mul_assoc]
    rw [← mul_assoc Pp, hl0P, mul_assoc, hPP]
  set W := d.L.GG * d.L.l0 Complex.I with hW
  have hv : Pp * (ThetaC d * d.QQ Complex.I 1 0 - d.QQ Complex.I 1 0 * ThetaC d) * Pp =
      Pp * (-d.QQ Complex.I 1 0) * Pp := by rw [hc]
  have e1 : Pp * (ThetaC d * d.QQ Complex.I 1 0 - d.QQ Complex.I 1 0 * ThetaC d) * Pp =
      ThetaC d * (Pp * d.QQ Complex.I 1 0 * Pp) - (Pp * d.QQ Complex.I 1 0 * Pp) * ThetaC d := by
    rw [mul_sub, sub_mul]
    congr 1
    · rw [← mul_assoc, hΘ]; simp only [mul_assoc]
    · simp only [mul_assoc]; rw [← hΘ]
  rw [e1, mul_neg, neg_mul, hPt] at hv
  have hv2 : M.xC P ρ Complex.I • ((ThetaC d * W - W * ThetaC d + W) * Pp) = 0 := by
    have : (ThetaC d * W - W * ThetaC d + W) * Pp = ThetaC d * (W * Pp) - W * Pp * ThetaC d + W * Pp := by
      rw [add_mul, sub_mul, mul_assoc, mul_assoc W, mul_assoc W, ← hΘ]
    rw [mul_smul_comm, smul_mul_assoc] at hv
    rw [this, smul_add, smul_sub, hv]
    abel
  have hv3 : (ThetaC d * W - W * ThetaC d + W) * Pp = 0 := by
    have := congrArg (fun z => (M.xC P ρ Complex.I)⁻¹ • z) hv2
    simpa only [smul_smul, inv_mul_cancel₀ hx, one_smul, smul_zero] using this
  rw [hW, curv_key d hRel, neg_mul, neg_eq_zero] at hv3
  set C := d.L.nabs * d.L.nab - d.L.nab * d.L.nabs
  have hκP : d.κ (fun ρ => ((-2 * M.aC P ρ : ℝ) : ℂ)) * Pp = ((-2 * M.aC P ρ : ℝ) : ℂ) • Pp := by
    rw [hPp, kap_Pj]
  have hv4 : C * Pp + algebraMap ℂ A (P.TT : ℂ) * d.L.GGi * d.L.GGi * (((-2 * M.aC P ρ : ℝ) : ℂ) • Pp) = 0 := by
    have e : d.L.ζbi * (d.L.GGi * (d.L.GG * (d.L.ζb * (C + algebraMap ℂ A (P.TT : ℂ) * d.L.GGi * d.L.GGi *
        d.κ (fun ρ => ((-2 * M.aC P ρ : ℝ) : ℂ)))) * Pp)) = 0 := by
      rw [hv3, mul_zero, mul_zero]
    rw [← e]
    simp only [mul_assoc]
    rw [← mul_assoc d.L.GGi d.L.GG, d.L.GGi_GG, one_mul, ← mul_assoc d.L.ζbi d.L.ζb, d.L.ζbi_ζb, one_mul]
    rw [add_mul]
    simp only [mul_assoc]
    rw [hκP]
  have hfin : C * Pp = -(algebraMap ℂ A (P.TT : ℂ) * d.L.GGi * d.L.GGi * (((-2 * M.aC P ρ : ℝ) : ℂ) • Pp)) :=
    eq_neg_of_add_eq_zero_left hv4
  rw [hfin, mul_smul_comm]
  simp only [mul_assoc]
  rw [← Algebra.smul_def, ← Algebra.smul_def, smul_smul, ← neg_smul]
  congr 1
  push_cast
  ring

end Curv

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Polynomial

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.LNab

noncomputable section

section poly

theorem lag_weights (k : ℕ) : ∃ lam : Fin (k + 1) → ℂ, ∀ p : ℂ[X], p.natDegree ≤ k →
    ∑ j : Fin (k + 1), lam j * p.eval ((j : ℕ) : ℂ) = p.coeff (k - 1) := by
  classical
  let v : Fin (k + 1) → ℂ := fun j => ((j : ℕ) : ℂ)
  have hinj : Set.InjOn v (Finset.univ : Finset (Fin (k + 1))) := by
    intro a _ b _ hab
    have h' : ((a : ℕ) : ℂ) = ((b : ℕ) : ℂ) := hab
    exact Fin.ext (by exact_mod_cast h')
  refine ⟨fun j => (Lagrange.basis Finset.univ v j).coeff (k - 1), ?_⟩
  intro p hp
  have hdeg : p.degree < (Finset.univ : Finset (Fin (k + 1))).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt (Polynomial.degree_le_of_natDegree_le hp) (by exact_mod_cast Nat.lt_succ_self k)
  conv_rhs => rw [Lagrange.eq_interpolate hinj hdeg]
  rw [Lagrange.interpolate_apply, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [Polynomial.coeff_C_mul, mul_comm]

def xpol (P : M.Par) (ρ : M.Ty P) : ℂ[X] := ∏ i ∈ Finset.Icc 1 (P.k - 1), (X + C ((M.rho P ρ i : ℝ) : ℂ))

def xepol (P : M.Par) (l : ℕ) (ρ : M.Ty P) : ℂ[X] :=
  ∏ i ∈ Finset.Icc 1 (P.k - 1) \ {l}, (X + C ((M.rho P ρ i : ℝ) : ℂ))

theorem xpol_eval (P : M.Par) (ρ : M.Ty P) (Y : ℂ) : (xpol P ρ).eval Y = M.xC P ρ Y := by
  simp [xpol, M.xC, Polynomial.eval_prod]

theorem xepol_eval (P : M.Par) (l : ℕ) (ρ : M.Ty P) (Y : ℂ) : (xepol P l ρ).eval Y = M.xEx P {l} ρ Y := by
  simp [xepol, M.xEx, Polynomial.eval_prod]

theorem xpol_monic (P : M.Par) (ρ : M.Ty P) : (xpol P ρ).Monic :=
  Polynomial.monic_prod_of_monic _ _ (fun _ _ => Polynomial.monic_X_add_C _)

theorem xpol_natDegree (P : M.Par) (ρ : M.Ty P) : (xpol P ρ).natDegree = P.k - 1 := by
  unfold xpol
  rw [Polynomial.natDegree_prod_of_monic _ _ (fun _ _ => Polynomial.monic_X_add_C _)]
  simp [Polynomial.natDegree_X_add_C]

theorem xpol_coeff (P : M.Par) (ρ : M.Ty P) : (xpol P ρ).coeff (P.k - 1) = 1 := by
  rw [← xpol_natDegree P ρ]
  exact (xpol_monic P ρ).coeff_natDegree

theorem xepol_natDegree (P : M.Par) {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) (ρ : M.Ty P) :
    (xepol P l ρ).natDegree = P.k - 2 := by
  unfold xepol
  rw [Polynomial.natDegree_prod_of_monic _ _ (fun _ _ => Polynomial.monic_X_add_C _)]
  simp only [Polynomial.natDegree_X_add_C, Finset.sum_const, smul_eq_mul, mul_one]
  rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hl, Nat.card_Icc]
  omega

end poly

section ring

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]

def fl (P : M.Par) (l : ℕ) (ρ : M.Ty P) : M.Ty P → ℂ := fun ρ0 => if M.Up P l ρ0 ρ then 1 else 0

theorem up_func {l : ℕ} {ρ0 ρ ρ' : M.Ty P} (h1 : M.Up P l ρ0 ρ) (h2 : M.Up P l ρ0 ρ') : ρ = ρ' := by
  funext i
  apply Fin.ext
  rw [h1 i, h2 i]

theorem kap_decomp (d : Q.NFData P A) (g : M.Ty P → ℂ) : d.κ g = ∑ ρ0, g ρ0 • d.κ (dl ρ0) := by
  have h : g = ∑ ρ0, g ρ0 • dl ρ0 := by
    funext ρ
    simp [dl, Finset.sum_apply]
  conv_lhs => rw [h]

  rw [map_sum]
  simp only [map_smul]

theorem sum_dl (d : Q.NFData P A) : ∑ ρ, d.κ (dl ρ) = 1 := by
  have h : ∑ ρ, (dl ρ : M.Ty P → ℂ) = 1 := by
    funext x
    simp [dl, Finset.sum_apply]

  rw [← map_sum, h, map_one]

theorem dl_mul_kap (d : Q.NFData P A) (ρ : M.Ty P) (g : M.Ty P → ℂ) :
    d.κ (dl ρ) * d.κ g = g ρ • d.κ (dl ρ) := by
  have h : dl ρ * g = g ρ • dl ρ := by
    funext x
    by_cases hx : x = ρ
    · subst hx
      simp [dl]
    · simp [dl, hx]
  rw [← map_mul, h, map_smul]

theorem kap_comm (d : Q.NFData P A) (hR : d.Rel) (f : M.Ty P → ℂ) {g : A}
    (hg : g ∈ ({d.L.ζ, d.L.ζi, d.L.ζb, d.L.ζbi, d.L.GG, d.L.GGi} : Set A)) : d.κ f * g = g * d.κ f := by
  have hm : g ∈ d.L.fns ∪ {d.L.nab, d.L.nabs} := Or.inl (Or.inr hg)
  exact (hR.2.1 f g hm).eq

theorem fns_comm' (d : Q.NFData P A) {x y : A}
    (hx : x ∈ ({d.L.ζ, d.L.ζi, d.L.ζb, d.L.ζbi, d.L.GG, d.L.GGi} : Set A))
    (hy : y ∈ ({d.L.ζ, d.L.ζi, d.L.ζb, d.L.ζbi, d.L.GG, d.L.GGi} : Set A)) : x * y = y * x :=
  d.L.fns_comm x (Or.inr hx) y (Or.inr hy)

theorem comb {k : ℕ} {lam : Fin (k + 1) → ℂ}
    (hlam : ∀ p : ℂ[X], p.natDegree ≤ k → ∑ j : Fin (k + 1), lam j * p.eval ((j : ℕ) : ℂ) = p.coeff (k - 1))
    (p : ℂ[X]) (hp : p.natDegree ≤ k) (O : A) :
    ∑ j : Fin (k + 1), lam j • (p.eval ((j : ℕ) : ℂ) • O) = p.coeff (k - 1) • O := by
  simp_rw [smul_smul]
  rw [← Finset.sum_smul, hlam p hp]

theorem e10 (d : Q.NFData P A) (hR : d.Rel) (ρ : M.Ty P) (Y : ℂ) :
    d.κ (dl ρ) * d.QQ Y 1 0 =
      (xpol P ρ).eval Y • (-(d.L.GG * d.κ (dl ρ) * d.L.nab)) +
      ((xpol P ρ) * (X + C (1 / 2 : ℂ))).eval Y • (-(d.κ (dl ρ) * d.L.ζb)) +
      ∑ l ∈ Finset.Icc 1 (P.k - 1), ∑ ρ0, (C (fl P l ρ ρ0) * xepol P l ρ0).eval Y • (d.SS l * d.κ (dl ρ0)) := by
  have hG : d.κ (dl ρ) * d.L.GG = d.L.GG * d.κ (dl ρ) := kap_comm d hR _ (by simp)
  have hGGi : d.L.GG * d.L.GGi = 1 := d.L.GG_GGi
  have hζbG : d.L.GG * d.L.ζb = d.L.ζb * d.L.GG := fns_comm' d (by simp) (by simp)
  have hx : d.κ (dl ρ) * d.x Y = (xpol P ρ).eval Y • d.κ (dl ρ) := by
    rw [Q.NFData.x, dl_mul_kap]
    simp only [xpol_eval]
  have key : d.L.GG * d.κ (dl ρ) * (d.L.ζb * d.L.GGi) = d.κ (dl ρ) * d.L.ζb := by
    calc d.L.GG * d.κ (dl ρ) * (d.L.ζb * d.L.GGi) = d.κ (dl ρ) * (d.L.GG * d.L.ζb * d.L.GGi) := by
          rw [← hG]; simp only [mul_assoc]
      _ = d.κ (dl ρ) * (d.L.ζb * (d.L.GG * d.L.GGi)) := by rw [hζbG]; simp only [mul_assoc]
      _ = d.κ (dl ρ) * d.L.ζb := by rw [hGGi, mul_one]
  show d.κ (dl ρ) * (d.L.GG * d.x Y * d.L.l0 Y + d.weightedSumBis Y) = _
  rw [mul_add]
  congr 1
  · calc d.κ (dl ρ) * (d.L.GG * d.x Y * d.L.l0 Y)
          = d.L.GG * (d.κ (dl ρ) * d.x Y) * d.L.l0 Y := by
            rw [← mul_assoc, ← mul_assoc, hG]; simp only [mul_assoc]
      _ = (xpol P ρ).eval Y • (d.L.GG * d.κ (dl ρ) * d.L.l0 Y) := by
            rw [hx, mul_smul_comm, smul_mul_assoc]
      _ = _ := by
            rw [R.LevelData.l0, mul_sub, mul_neg, ← Algebra.smul_def, mul_smul_comm, key]
            rw [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
            module
  · rw [Q.NFData.weightedSumBis, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    have hc : d.κ (dl ρ) * d.SS l = d.SS l * d.κ (fl P l ρ) := by
      apply hR.2.2.2.1 l
      intro ρ0 ρ' hup
      by_cases h : ρ' = ρ
      · subst h
        simp [dl, fl, hup]
      · have hn : ¬ M.Up P l ρ0 ρ := fun h2 => h (up_func hup h2)
        simp [dl, fl, h, hn]
    rw [← mul_assoc, hc, mul_assoc, ← map_mul, kap_decomp, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun ρ0 _ => ?_)
    rw [mul_smul_comm]
    congr 1
    simp [Polynomial.eval_mul, Polynomial.eval_C, xepol_eval]

theorem e01 (d : Q.NFData P A) (hR : d.Rel) (ρ : M.Ty P) (Y : ℂ) :
    d.κ (dl ρ) * d.QQ Y 0 1 =
      (xpol P ρ).eval Y • (-(d.L.GG * d.κ (dl ρ) * d.L.nabs)) +
      ((xpol P ρ) * (X - C (1 / 2 : ℂ))).eval Y • (-(d.κ (dl ρ) * d.L.ζ)) +
      ∑ l ∈ Finset.Icc 1 (P.k - 1), (xepol P l ρ).eval Y • (d.κ (dl ρ) * star (d.SS l)) := by
  have hG : d.κ (dl ρ) * d.L.GG = d.L.GG * d.κ (dl ρ) := kap_comm d hR _ (by simp)
  have hGGi : d.L.GG * d.L.GGi = 1 := d.L.GG_GGi
  have hζG : d.L.GG * d.L.ζ = d.L.ζ * d.L.GG := fns_comm' d (by simp) (by simp)
  have hx : d.κ (dl ρ) * d.x Y = (xpol P ρ).eval Y • d.κ (dl ρ) := by
    rw [Q.NFData.x, dl_mul_kap]
    simp only [xpol_eval]
  have key : d.L.GG * d.κ (dl ρ) * (d.L.ζ * d.L.GGi) = d.κ (dl ρ) * d.L.ζ := by
    calc d.L.GG * d.κ (dl ρ) * (d.L.ζ * d.L.GGi) = d.κ (dl ρ) * (d.L.GG * d.L.ζ * d.L.GGi) := by
          rw [← hG]; simp only [mul_assoc]
      _ = d.κ (dl ρ) * (d.L.ζ * (d.L.GG * d.L.GGi)) := by rw [hζG]; simp only [mul_assoc]
      _ = d.κ (dl ρ) * d.L.ζ := by rw [hGGi, mul_one]
  show d.κ (dl ρ) * (d.L.GG * d.x Y * d.L.m0 Y + d.S12 Y) = _
  rw [mul_add]
  congr 1
  · calc d.κ (dl ρ) * (d.L.GG * d.x Y * d.L.m0 Y)
          = d.L.GG * (d.κ (dl ρ) * d.x Y) * d.L.m0 Y := by
            rw [← mul_assoc, ← mul_assoc, hG]; simp only [mul_assoc]
      _ = (xpol P ρ).eval Y • (d.L.GG * d.κ (dl ρ) * d.L.m0 Y) := by
            rw [hx, mul_smul_comm, smul_mul_assoc]
      _ = _ := by
            rw [R.LevelData.m0, mul_sub, mul_neg, ← Algebra.smul_def, mul_smul_comm, key]
            rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
            module
  · rw [Q.NFData.S12, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [← mul_assoc, dl_mul_kap]
    simp only [xepol_eval, smul_mul_assoc]

end ring

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.LNab
end

section

namespace Formalism.FourierDecayAlt.P

theorem representation_smooth : NFRadRedS.RepSmooth := representation_smooth_of_log local_logarithm_unitary

theorem radical_reduction_surjective : Formalism.FourierDecayAlt.NF.RadRedSurj :=
  radical_surjective_of_parts local_smooth_section representation_smooth

end Formalism.FourierDecayAlt.P
end

section

namespace Formalism.FourierDecayAlt.P.BXiAsm
open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem closed_of (hX : XiExists) : LemmaBClosed := Formalism.FourierDecayAlt.P.b_lemmaBClosed_of hX

theorem norm_of (hX : XiExists) : LemmaBNorm :=
  Formalism.FourierDecayAlt.Final.lemma_b_norm_of_parts (closed_of hX) Formalism.FourierDecayAlt.Final.conjugation_invariance_all Formalism.FourierDecayAlt.Final.dilation_jacobian_all
    Formalism.FourierDecayAlt.Final.integral_bound_all

theorem any_of (hX : XiExists) : LemmaBAny :=
  Formalism.FourierDecayAlt.Final.lemma_b_from_norm_bound (norm_of hX) Formalism.FourierDecayAlt.Final.integral_norm_bound_variant_b

end Formalism.FourierDecayAlt.P.BXiAsm

namespace Formalism.FourierDecayAlt.P

theorem b_any_of_xi : Formalism.FourierDecayAlt.B2.LemmaBAny := Formalism.FourierDecayAlt.P.BXiAsm.any_of exists_auxiliary_xi

end Formalism.FourierDecayAlt.P
end
