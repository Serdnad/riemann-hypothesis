module

public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HasSumPolyDerivMulProdAddMatrix
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EqZeroOfSemicharacterMultiplier
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaHolomorphic
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle002
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle003
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle060
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HaarPushforwardEqBallDensity
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle061
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle062
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
import ReciprocityTheory.ThetaQuasiPeriods.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle013
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle001
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle021
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
import GroundTheory.AutomorphicForms.LocallyProfinite
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentModulusMatrix
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section

namespace GlobalTheory.CompanionTheory.CanThLine

section Law

open Complex Matrix ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CanTh
open scoped Real

variable {g : ℕ}

theorem gaussian_mul_factor {τ : Matrix (Fin g) (Fin g) ℂ} (hs : τ.IsSymm)
    (hp : (τ.map Complex.im).PosDef) (a c : Fin g → ℝ) (m n : Fin g → ℤ) {l : Fin g → ℂ}
    (hl : l = (fun i => (m i : ℂ)) + τ *ᵥ fun i => (n i : ℂ)) (ζ : Fin g → ℂ) :
    cexp (-(π / 2 * ((ζ + l) ⬝ᵥ imInv τ *ᵥ (ζ + l)))) *
        (canMult a c m n *
          cexp (π * hermForm (imInv τ) ζ l + π / 2 * hermForm (imInv τ) l l)) =
      eC (((1 : ℕ) : ℂ) * (ofRealVec a ⬝ᵥ ofIntVec m - ofRealVec c ⬝ᵥ ofIntVec n)) *
        eC (-((1 : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ ζ)) *
        cexp (-(π / 2 * (ζ ⬝ᵥ imInv τ *ᵥ ζ))) := by
  have hl' : l = (fun i => (((m i : ℝ)) : ℂ)) + τ *ᵥ fun i => (((n i : ℝ)) : ℂ) := by
    simpa using hl
  have h1 := dot_imInv_eq_hermForm_add hp (fun i => (n i : ℝ)) (fun i => (m i : ℝ)) ζ
  have h2 := dot_imInv_eq_hermForm_add hp (fun i => (n i : ℝ)) (fun i => (m i : ℝ)) l
  rw [← hl'] at h1 h2
  have h3 := dot_mulVec_symm (isSymm_imInv hs) ζ l
  have e0 : (fun i => (((n i : ℝ)) : ℂ)) = ofIntVec n := by
    funext i; simp [ofIntVec]
  have h5 : (l ⬝ᵥ ofIntVec n) = ((m ⬝ᵥ n : ℤ) : ℂ) + ofIntVec n ⬝ᵥ τ *ᵥ ofIntVec n := by
    rw [hl, add_dotProduct, dotProduct_comm (τ *ᵥ _)]
    congr 1
    simp [dotProduct, ofIntVec]
  have e1 : ((a ⬝ᵥ (fun i => (m i : ℝ)) : ℝ) : ℂ) = ofRealVec a ⬝ᵥ ofIntVec m := by
    simp [dotProduct, ofRealVec, ofIntVec]
  have e2 : ((c ⬝ᵥ (fun i => (n i : ℝ)) : ℝ) : ℂ) = ofRealVec c ⬝ᵥ ofIntVec n := by
    simp [dotProduct, ofRealVec, ofIntVec]
  rw [e0] at h1 h2
  rw [canMult, e1, e2]
  simp only [eC, ← Complex.exp_add]
  congr 1
  rw [mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add, h3, h1, h2, h5,
    dotProduct_comm (ofIntVec n) ζ]
  push_cast
  ring

end Law

section Main

open Complex Matrix ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CanTh
open scoped Real

variable {g : ℕ}

theorem gaussian_mul_mem_thetaLevelChar {τ h Hm : Matrix (Fin g) (Fin g) ℂ} {a c : Fin g → ℝ}
    {θ : (Fin g → ℂ) → ℂ} (hs : τ.IsSymm) (hp : (τ.map Complex.im).PosDef) (hh : IsUnit h.det)
    (hH : ∀ z w, hermForm Hm z w = hermForm (imInv τ) (h *ᵥ z) (h *ᵥ w))
    (hθ : Differentiable ℂ θ)
    (hlaw : ∀ (m n : Fin g → ℤ) (lam : Fin g → ℂ),
      h *ᵥ lam = (fun i => (m i : ℂ)) + τ *ᵥ (fun i => (n i : ℂ)) →
      ∀ z, θ (z + lam) = canMult a c m n *
        cexp (π * hermForm Hm z lam + π / 2 * hermForm Hm lam lam) * θ z) :
    (fun ζ => cexp (-(π / 2 * (ζ ⬝ᵥ imInv τ *ᵥ ζ))) * θ (h⁻¹ *ᵥ ζ)) ∈
      GlobalTheory.thetaLevelChar a c 1 τ := by
  have hhi : h * h⁻¹ = 1 := mul_nonsing_inv _ hh
  have hback : ∀ v : Fin g → ℂ, h *ᵥ (h⁻¹ *ᵥ v) = v := fun v => by
    rw [mulVec_mulVec, hhi, one_mulVec]
  have hd : Differentiable ℂ (fun ζ : Fin g → ℂ => h⁻¹ *ᵥ ζ) :=
    differentiable_pi.2 fun i => by
      simp only [mulVec, dotProduct]
      fun_prop
  refine GlobalTheory.mem_thetaLevelChar.2 ⟨?_, fun n n' z => ?_⟩
  · refine Differentiable.mul ?_ (hθ.comp hd)
    simp only [dotProduct, mulVec]
    fun_prop
  · set l : Fin g → ℂ := (fun i => (n' i : ℂ)) + τ *ᵥ fun i => (n i : ℂ) with hl
    have e : z + τ *ᵥ ofIntVec n + ofIntVec n' = z + l := by
      rw [hl, add_assoc, add_comm (τ *ᵥ _)]
      rfl
    have hL := hlaw n' n (h⁻¹ *ᵥ l) (hback l) (h⁻¹ *ᵥ z)
    rw [hH, hH, hback, hback] at hL
    have hG := gaussian_mul_factor hs hp a c n' n hl z
    simp only [e]
    rw [show h⁻¹ *ᵥ (z + l) = h⁻¹ *ᵥ z + h⁻¹ *ᵥ l from mulVec_add _ _ _, hL]
    linear_combination θ (h⁻¹ *ᵥ z) * hG

theorem eq_const_mul_canTh {τ h Hm : Matrix (Fin g) (Fin g) ℂ} {a c : Fin g → ℝ}
    {θ : (Fin g → ℂ) → ℂ} (hs : τ.IsSymm) (hp : (τ.map Complex.im).PosDef) (hh : IsUnit h.det)
    (hH : ∀ z w, hermForm Hm z w = hermForm (imInv τ) (h *ᵥ z) (h *ᵥ w))
    (hθ : Differentiable ℂ θ)
    (hlaw : ∀ (m n : Fin g → ℤ) (lam : Fin g → ℂ),
      h *ᵥ lam = (fun i => (m i : ℂ)) + τ *ᵥ (fun i => (n i : ℂ)) →
      ∀ z, θ (z + lam) = canMult a c m n *
        cexp (π * hermForm Hm z lam + π / 2 * hermForm Hm lam lam) * θ z) :
    ∃ κ : ℂ, ∀ z, θ z = κ * canTh τ a c (h *ᵥ z) := by
  have hmem := gaussian_mul_mem_thetaLevelChar hs hp hh hH hθ hlaw
  rw [GlobalTheory.thetaLevelChar_one (a := a) (b := c) (τ := τ) ⟨hs, hp⟩, Submodule.mem_span_singleton] at hmem
  obtain ⟨κ, hκ⟩ := hmem
  refine ⟨κ, fun z => ?_⟩
  have hback : h⁻¹ *ᵥ (h *ᵥ z) = z := by
    rw [mulVec_mulVec, nonsing_inv_mul _ hh, one_mulVec]
  have hz := congrFun hκ (h *ᵥ z)
  simp only [Pi.smul_apply, smul_eq_mul] at hz
  rw [hback] at hz
  rw [canTh, thetaChar_eq_theta, mul_left_comm, hz, ← _root_.mul_assoc, ← Complex.exp_add]
  simp

end Main

theorem level_one_line : ∀ (g : ℕ) (τ h Hm : Matrix (Fin g) (Fin g) ℂ) (a c : Fin g → ℝ) (θ : (Fin g → ℂ) → ℂ),
    τ.IsSymm → (τ.map Complex.im).PosDef → IsUnit h.det →
    (∀ z w, hermForm Hm z w = hermForm (GlobalTheory.CanTh.imInv τ) (h.mulVec z) (h.mulVec w)) →
    Differentiable ℂ θ →
    (∀ (m n : Fin g → ℤ) (lam : Fin g → ℂ), h.mulVec lam = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ)) →
      ∀ z, θ (z + lam) = GlobalTheory.CanTh.canMult a c m n *
        Complex.exp (Real.pi * hermForm Hm z lam + Real.pi / 2 * hermForm Hm lam lam) * θ z) →
    ∃ κ : ℂ, ∀ z, θ z = κ * GlobalTheory.CanTh.canTh τ a c (h.mulVec z) := by
  intro g τ h Hm a c θ hs hp hh hH hθ hlaw
  exact eq_const_mul_canTh hs hp hh hH hθ hlaw

end GlobalTheory.CompanionTheory.CanThLine
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

namespace GlobalTheory.CompanionTheory.Ar.Nform

theorem exists_half_canMult : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (bs : Module.Basis (Fin g ⊕ Fin g) ℤ Λ) (χ : Λ → ℂ),
    (∀ l l' : Λ, χ (l + l') = χ l * χ l' * Complex.exp (Real.pi * Complex.I *
      (((∑ i, (bs.repr l (Sum.inr i) * bs.repr l' (Sum.inl i) - bs.repr l (Sum.inl i) * bs.repr l' (Sum.inr i)) : ℤ) : ℝ) : ℂ))) →
    (∀ l, χ l ^ 2 = 1) →
    ∃ a c : Fin g → ℝ, (∀ i, a i = 0 ∨ a i = 1 / 2) ∧ (∀ i, c i = 0 ∨ c i = 1 / 2) ∧
      ∀ x, χ x = GlobalTheory.CanTh.canMult a c (fun i => bs.repr x (Sum.inl i)) (fun i => bs.repr x (Sum.inr i)) := by
  intro g Λ bs χ hχ hsq
  classical
  have hpm : ∀ l, χ l = 1 ∨ χ l = -1 := fun l =>
    mul_self_eq_one_iff.mp (by rw [← sq]; exact hsq l)
  have hexp : ∀ k : ℤ, Complex.exp (↑Real.pi * Complex.I * ((k : ℝ) : ℂ)) = (-1) ^ k := by
    intro k
    rw [Complex.ofReal_intCast, mul_comm, Complex.exp_int_mul, Complex.exp_pi_mul_I]
  have hhalf : Complex.exp (2 * ↑Real.pi * Complex.I * ((1 / 2 : ℝ) : ℂ)) = -1 := by
    rw [show (2 : ℂ) * ↑Real.pi * Complex.I * ((1 / 2 : ℝ) : ℂ) = ↑Real.pi * Complex.I by
      push_cast; ring, Complex.exp_pi_mul_I]
  have hhalf' : Complex.exp (-(2 * ↑Real.pi * Complex.I * ((1 / 2 : ℝ) : ℂ))) = -1 := by
    rw [Complex.exp_neg, hhalf]
    norm_num
  have hsame : ∀ j k : Fin g ⊕ Fin g, bs.repr (bs j) k = if j = k then 1 else 0 := by
    intro j k
    rw [Module.Basis.repr_self, Finsupp.single_apply]
  have hsingle : ∀ i : Fin g, (fun k => bs.repr (bs (Sum.inl i)) (Sum.inl k)) = Pi.single i 1 ∧
      (fun k => bs.repr (bs (Sum.inl i)) (Sum.inr k)) = 0 ∧
      (fun k => bs.repr (bs (Sum.inr i)) (Sum.inl k)) = 0 ∧
      (fun k => bs.repr (bs (Sum.inr i)) (Sum.inr k)) = Pi.single i 1 := by
    intro i
    refine ⟨funext fun k => ?_, funext fun k => ?_, funext fun k => ?_, funext fun k => ?_⟩ <;>
      by_cases hk : k = i
    · subst hk; simp [hsame]
    · simp [hsame, Pi.single_apply, hk, Ne.symm hk]
    · simp [hsame]
    · simp [hsame]
    · simp [hsame]
    · simp [hsame]
    · subst hk; simp [hsame]
    · simp [hsame, Pi.single_apply, hk, Ne.symm hk]
  have hdot : ∀ (a : Fin g → ℝ) (i : Fin g),
      (a ⬝ᵥ fun k => (((Pi.single i 1 : Fin g → ℤ) k : ℤ) : ℝ)) = a i := by
    intro a i
    simp [dotProduct, Pi.single_apply]
  have hdot0 : ∀ a : Fin g → ℝ, (a ⬝ᵥ fun k => (((0 : Fin g → ℤ) k : ℤ) : ℝ)) = 0 := by
    intro a
    simp [dotProduct]
  have hC_inl : ∀ (a c : Fin g → ℝ) (i : Fin g),
      GlobalTheory.CanTh.canMult a c (fun k => bs.repr (bs (Sum.inl i)) (Sum.inl k))
        (fun k => bs.repr (bs (Sum.inl i)) (Sum.inr k)) =
        Complex.exp (2 * ↑Real.pi * Complex.I * ((a i : ℝ) : ℂ)) := by
    intro a c i
    obtain ⟨h1, h2, -, -⟩ := hsingle i
    rw [h1, h2]
    simp only [GlobalTheory.CanTh.canMult, dotProduct_zero, hdot, hdot0]
    congr 1
    push_cast
    ring
  have hC_inr : ∀ (a c : Fin g → ℝ) (i : Fin g),
      GlobalTheory.CanTh.canMult a c (fun k => bs.repr (bs (Sum.inr i)) (Sum.inl k))
        (fun k => bs.repr (bs (Sum.inr i)) (Sum.inr k)) =
        Complex.exp (-(2 * ↑Real.pi * Complex.I * ((c i : ℝ) : ℂ))) := by
    intro a c i
    obtain ⟨-, -, h3, h4⟩ := hsingle i
    rw [h3, h4]
    simp only [GlobalTheory.CanTh.canMult, zero_dotProduct, hdot, hdot0]
    congr 1
    push_cast
    ring
  obtain ⟨a, ha⟩ : ∃ a : Fin g → ℝ, a = fun i => if χ (bs (Sum.inl i)) = 1 then 0 else 1 / 2 :=
    ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : Fin g → ℝ, c = fun i => if χ (bs (Sum.inr i)) = 1 then 0 else 1 / 2 :=
    ⟨_, rfl⟩
  refine ⟨a, c, fun i => ?_, fun i => ?_, ?_⟩
  · simp only [ha]
    split_ifs <;> norm_num
  · simp only [hc]
    split_ifs <;> norm_num
  have hχ0 : ∀ l, χ l ≠ 0 := by
    intro l h
    have h' := hsq l
    rw [h] at h'
    norm_num at h'
  have hψ0 : ∀ l : Λ, GlobalTheory.CanTh.canMult a c (fun i => bs.repr l (Sum.inl i))
      (fun i => bs.repr l (Sum.inr i)) ≠ 0 := by
    intro l
    simp only [GlobalTheory.CanTh.canMult]
    exact Complex.exp_ne_zero _
  have hψ : ∀ l l' : Λ,
      GlobalTheory.CanTh.canMult a c (fun i => bs.repr (l + l') (Sum.inl i))
                   (fun i => bs.repr (l + l') (Sum.inr i)) =
        GlobalTheory.CanTh.canMult a c (fun i => bs.repr l (Sum.inl i))
                     (fun i => bs.repr l (Sum.inr i)) *
          GlobalTheory.CanTh.canMult a c (fun i => bs.repr l' (Sum.inl i))
            (fun i => bs.repr l' (Sum.inr i)) *
          Complex.exp (Real.pi * Complex.I *
            (((∑ i, (bs.repr l (Sum.inr i) * bs.repr l' (Sum.inl i) -
              bs.repr l (Sum.inl i) * bs.repr l' (Sum.inr i)) : ℤ) : ℝ) : ℂ)) := by
    intro l l'
    have hm : (fun i => bs.repr (l + l') (Sum.inl i)) =
        (fun i => bs.repr l (Sum.inl i)) + (fun i => bs.repr l' (Sum.inl i)) := by
      funext i
      simp [map_add (f := _)]
    have hn : (fun i => bs.repr (l + l') (Sum.inr i)) =
        (fun i => bs.repr l (Sum.inr i)) + (fun i => bs.repr l' (Sum.inr i)) := by
      funext i
      simp [map_add (f := _)]
    rw [hm, hn, GlobalTheory.HolTheta.canMult_add, hexp, Finset.sum_sub_distrib]
    rfl
  have hbasis : ∀ j : Fin g ⊕ Fin g, χ (bs j) =
      GlobalTheory.CanTh.canMult a c (fun i => bs.repr (bs j) (Sum.inl i))
        (fun i => bs.repr (bs j) (Sum.inr i)) := by
    rintro (i | i)
    · rw [hC_inl]
      rcases hpm (bs (Sum.inl i)) with h | h
      · simp [ha, h]
      · have h' : χ (bs (Sum.inl i)) ≠ 1 := by rw [h]; norm_num
        simp only [ha, h', if_false]
        rw [h, hhalf]
    · rw [hC_inr]
      rcases hpm (bs (Sum.inr i)) with h | h
      · simp [hc, h]
      · have h' : χ (bs (Sum.inr i)) ≠ 1 := by rw [h]; norm_num
        simp only [hc, h', if_false]
        rw [h, hhalf']
  exact GlobalTheory.HolTheta.eq_of_cocycle bs
    (fun l l' => Complex.exp (Real.pi * Complex.I *
      (((∑ i, (bs.repr l (Sum.inr i) * bs.repr l' (Sum.inl i) -
        bs.repr l (Sum.inl i) * bs.repr l' (Sum.inr i)) : ℤ) : ℝ) : ℂ)))
    (ψ := fun l => GlobalTheory.CanTh.canMult a c (fun i => bs.repr l (Sum.inl i))
      (fun i => bs.repr l (Sum.inr i)))
    (fun _ _ => Complex.exp_ne_zero _) hχ0 hψ0 hχ hψ hbasis

end GlobalTheory.CompanionTheory.Ar.Nform
end

section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Small.Fund


theorem _root_.GlobalTheory.T.root_origin_weight_comparison_shift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (RM : RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (Or : RootOrigin Y S RM Fx) (lam nu : Wt (CMType H) (D.p + D.q)) (n' n₀ : Option (RootIx D) → ℤ) (q₀ : ℕ) (s t : ℝ) (cc : RM.K → ℂ) (z : (Σ k, RM.ι k) → ℂ) (v : ℂ), 0 < q₀ → (∀ j, (n' j : ℝ) = RM.coef lam 0 j) → (∀ j, (n₀ j : ℝ) = q₀ * RM.coef nu (-1) j) → (∀ k, cc k ≠ 0) → (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → v ≠ 0 → s / q₀ * Real.log ‖v * ∏ k, cc k ^ (combLine (RM.line 1) n₀).a k‖ + RM.weight t (lam - s • nu) s (fun p => cc p.1 * z p) - Real.log (∏ r, (Or.sing r).h (fun p => cc p.1 * z p) ^ n' (some r)) = s / q₀ * Real.log ‖v‖ + RM.weight t (lam - s • nu) s z - Real.log (∏ r, (Or.sing r).h z ^ n' (some r)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Small.Fund.Orbit.torus_invariant | exact GlobalTheory.CompanionTheory.Ar.Small.Fund.Orbit.torus_invariant | (intros; apply GlobalTheory.CompanionTheory.Ar.Small.Fund.Orbit.torus_invariant <;> assumption)
end

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder


theorem _root_.GlobalTheory.T.ball_domain_open_convex_zero : ∀ (Ψ : Type) [Fintype Ψ] (j j' n : ℕ) (q : Ψ × Fin j × Fin j' ≃ Fin n), IsOpen (ballDom q) ∧ Convex ℝ (ballDom q) ∧ (0 : Fin n → ℂ) ∈ ballDom q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.BallConvex.ballDom_open_convex_zero | exact GlobalTheory.CompanionTheory.Ar.Cusp.BallConvex.ballDom_open_convex_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.BallConvex.ballDom_open_convex_zero <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.T.polar_identity_from_symmetric_forms : ∀ (σ : Type) [Fintype σ] (D : ℕ) (a : (Fin (D + 1) → σ) → ℝ) (b : (Fin D → σ) → ℝ) (κ : ℕ → ℝ) (ε : σ → ℤ) (a₀ : σ), (∀ (π : Equiv.Perm (Fin (D + 1))) w, a (w ∘ π) = a w) → (∀ (π : Equiv.Perm (Fin D)) w, b (w ∘ π) = b w) → (∀ n : σ → ℤ, n a₀ = 0 → polar (D + 1) a (fun _ x => (n x : ℝ)) = 0 ∧ ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D + 1 → polar (D + 1) a (mix (2 * k) (fun x => (ε x : ℝ)) fun x => (n x : ℝ)) = -(2 * κ k) * polar D b (mix (2 * k - 1) (fun x => (ε x : ℝ)) fun x => (n x : ℝ))) → ∀ (c : σ → ℝ), c a₀ = 0 → ∀ u : ℝ, eval (fun x => c x - u / 2 * ε x) (formPoly (D + 1) a) + eval (fun x => c x + u / 2 * ε x) (formPoly (D + 1) a) = (tsgPoly D κ (linePoly c ε (formPoly D b))).eval u := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.coefficient_identities_give_operator_identity | exact GlobalTheory.CompanionTheory.Ar.PB.coefficient_identities_give_operator_identity | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.coefficient_identities_give_operator_identity <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.T.square_parametrized_density_formula : ∀ (d : ℕ) (σ : Type) [Fintype σ] (SY : AnSys (d + 1) σ) (a₀ : σ) (ε : σ → ℤ) (Q : AnSq SY a₀ ε) (c : σ → ℝ), c a₀ = 0 → ∀ (n k : ℕ), 1 ≤ k → 2 * k ≤ d + 2 → (∀ z : Fin (d + 1) → ℂ, Fin.tail z ∈ Q.U n → paramDens (fun r => sumPot (mix (2 * k - 1) (fun a => (ε a : ℝ)) c r) SY.potH) (Q.ΦY n) z = maDens (fun (r : Fin (d + 1)) (z' : Fin (d + 1) → ℂ) => if (r : ℕ) < 2 * k - 1 then xiPot (Q.G n (Fin.tail z')) (z' 0) else ∑ a, c a * Q.α n a (Fin.tail z')) z) ∧ ∀ i < k, ∀ z : Fin (d + 2) → ℂ, Fin.tail (Fin.tail z) ∈ Q.U n → paramDens (fun r => sumPot (Q.wcoef c k i r) Q.SW.potH) (Q.ΦW n) z = maDens (let u : ℕ → Fin 2 → ℝ := (fun (i : ℕ) (r : ℕ) (c : Fin 2) => if r = 0 then (![1, -1] : Fin 2 → ℝ) c else if r = 1 then (![0, 1] : Fin 2 → ℝ) c else if r < 2 + 2 * i then (![1, 0] : Fin 2 → ℝ) c else (![0, 1] : Fin 2 → ℝ) c) i; fun (r : Fin (d + 2)) (z' : Fin (d + 2) → ℂ) => if (r : ℕ) < 2 * k then u r 0 * xiPot (Q.G n (Fin.tail (Fin.tail z'))) (z' 0) + u r 1 * xiPot (Q.G n (Fin.tail (Fin.tail z'))) (z' 1) else ∑ a, c a * Q.α n a (Fin.tail (Fin.tail z'))) z := by
  first | exact @GlobalTheory.CompanionTheory.Relay.square_parametrized_density_formula | exact GlobalTheory.CompanionTheory.Relay.square_parametrized_density_formula | (intros; apply GlobalTheory.CompanionTheory.Relay.square_parametrized_density_formula <;> assumption)
end

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace

theorem _root_.GlobalTheory.T.haar_pushforward_eq_ball_density : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (Δ : GroupDict F) (μ : Measure (archUnitary Δ.h (Pi.basisFun E (Fin (j + j'))))) [μ.IsHaarMeasure], ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ μ.map Δ.π = c • (volume.restrict (ballDom F.q)).withDensity fun t => ENNReal.ofReal (ballDens F.q t) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.DictMeas.haar_projects | exact GlobalTheory.CompanionTheory.Ar.Cusp.DictMeas.haar_projects | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.DictMeas.haar_projects <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.T.arithmetic_intersection_multilinear_polar : MetricLocalStatement → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ : Type) [Fintype σ] (P : Ideal (MRing ι)) (n : ℕ) (A : σ → HermLine ι) (c : Fin n → σ → ℤ), IsArithVar P n → (∀ a, IsSmoothHerm (A a)) → (∀ r, IsSmoothHerm (combLine A (c r))) ∧ II K ι P n (fun r => combLine A (c r)) = polar n (fun w => II K ι P n fun r => A (w r)) (fun r a => (c r a : ℝ)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.combLine_intersection | exact GlobalTheory.CompanionTheory.Ar.PB.combLine_intersection | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.combLine_intersection <;> assumption)
end

section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

theorem _root_.GlobalTheory.T.cusp_weight_invariant_under_isometry : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (R : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (g' : ℕ) (Λ' : Type) [AddCommGroup Λ'] [Module (𝓞 E) Λ'] (R' : RiemLat E g' Λ') (φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g' → ℂ)), IsCMFam σ → φ '' Set.range R.P = Set.range R'.P → (∀ x y, R'.ip (φ x) (φ y) = R.ip x y) → (∀ a x, φ (R.B a x) = R'.B a (φ x)) → R'.cuspW σ = R.cuspW σ ∧ R'.lam1 = R.lam1 ∧ (∀ m, R'.HasRank σ m ↔ R.HasRank σ m) ∧ ∃ α : Λ ≃ₗ[𝓞 E] Λ', (∀ v, R'.P (α v) = φ (R.P v)) ∧ ∀ I, IsIsoSub R.form I → R'.nz σ (I.map α.toLinearMap) = R.nz σ I := by
  first | exact @GlobalTheory.CompanionTheory.Relay.cusp_weight_invariant_under_isometry | exact GlobalTheory.CompanionTheory.Relay.cusp_weight_invariant_under_isometry | (intros; apply GlobalTheory.CompanionTheory.Relay.cusp_weight_invariant_under_isometry <;> assumption)
end

section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

theorem _root_.GlobalTheory.T.isotropic_sublattice_covolume_positive : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (R : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (I : Submodule (𝓞 E) Λ), IsCMFam σ → IsIsoSub R.form I → I ≠ ⊥ → (∃ r v, IsNzFamily I r v) ∧ ∀ r v, IsNzFamily I r v → R.nz σ I = R.nzOf σ I v ∧ 0 < R.nz σ I ∧ r = Module.finrank (𝓞 E) I := by
  first | exact @GlobalTheory.CompanionTheory.Relay.isotropic_sublattice_covolume_positive | exact GlobalTheory.CompanionTheory.Relay.isotropic_sublattice_covolume_positive | (intros; apply GlobalTheory.CompanionTheory.Relay.isotropic_sublattice_covolume_positive <;> assumption)
end

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder


theorem _root_.GlobalTheory.T.genus_eq_card_mul_signature : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (g j j' : ℕ) (B : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (σ : Ψ → (𝓞 E →+* ℂ)), IsCMFam σ → (∀ τ, Module.finrank ℂ (eigSp B (σ τ)) = j' ∧ Module.finrank ℂ (eigSp B ((starRingEnd ℂ).comp (σ τ))) = j) → g = Fintype.card Ψ * (j + j') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.TangentDim.dim_eq_card_mul | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.TangentDim.dim_eq_card_mul | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.TangentDim.dim_eq_card_mul <;> assumption)
end

section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

namespace GlobalTheory.CompanionTheory.Ar.Cusp

theorem riemLat_basis_periods_linearIndependent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ) (n : ℕ) (b : Module.Basis (Fin n) ℤ Λ), LinearIndependent ℝ (fun j => R.P (b j)) := by
  intro E _ _ _ g Λ _ _ R n b
  have hspan : Submodule.span ℝ (Set.range R.P) = ⊤ := (GlobalTheory.T.riemann_lattice_eigen_projection E g Λ Unit R).2.1
  have hmem : ∀ x : Λ, R.P x ∈ Submodule.span ℝ (Set.range fun j => R.P (b j)) := by
    intro x
    have hx : x ∈ Submodule.span ℤ (Set.range b) := by
      rw [b.span_eq]; trivial
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      exact Submodule.subset_span ⟨j, rfl⟩
    | zero => simp
    | add y z _ _ hy hz =>
      rw [map_add (f := _)]
      exact Submodule.add_mem _ hy hz
    | smul c y _ hy =>
      rw [map_zsmul]
      exact Submodule.smul_of_tower_mem _ c hy
  have htop : ⊤ ≤ Submodule.span ℝ (Set.range fun j => R.P (b j)) := by
    rw [← hspan]
    apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    exact hmem x
  have hcard : Fintype.card (Fin n) = Module.finrank ℝ (Fin g → ℂ) := by
    have h1 : Module.finrank ℤ Λ = Fintype.card (Fin n) := by
      haveI := R.free
      haveI := R.fin
      exact Module.finrank_eq_card_basis b
    have h2 : Module.finrank ℝ (Fin g → ℂ) = 2 * g := by
      simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, mul_comm]
    rw [← h1, R.rank, h2]
  exact linearIndependent_of_top_le_span_of_card_eq_finrank htop hcard

end GlobalTheory.CompanionTheory.Ar.Cusp
end
