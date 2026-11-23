module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle040
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule

@[expose] public section

section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA

theorem differentiableAt_entries_exp_smul {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) :
    DifferentiableAt ℝ
      (fun t : ℝ => (Matrix.of.symm (NormedSpace.exp (t • X)) : Fin n → Fin n → ℂ)) s := by
  let _ : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  have hc : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X)) _ s :=
    hasDerivAt_exp_smul_const (𝕂 := ℝ) X s
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] (Fin n → Fin n → ℂ) :=
    LinearMap.toContinuousLinearMap (Matrix.ofLinearEquiv ℝ).symm.toLinearMap
  exact (L.hasFDerivAt.comp_hasDerivAt s hc).differentiableAt

theorem dRep_equivariant : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {v : H} (hv : IsSmoothVec G π v) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ G), π g (dRep π X v) = dRep π (g * X * g⁻¹) (π g v) := by
  intro n G H _ _ π hG hrep v hv X hX g hg
  obtain ⟨F, hF, hFv⟩ := hv
  have hu : IsUnit g := hG.isUnit g hg
  have hgi : g⁻¹ ∈ G := hG.inv_mem g hg
  have hinv : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul g ((Matrix.isUnit_iff_isUnit_det g).1 hu)
  have hd : DifferentiableAt ℝ (fun t : ℝ => π (NormedSpace.exp (t • X)) v) 0 := by
    have he : (fun t : ℝ => π (NormedSpace.exp (t • X)) v) =
        F ∘ fun t : ℝ => (Matrix.of.symm (NormedSpace.exp (t • X)) : Fin n → Fin n → ℂ) := by
      funext t
      exact hFv _ (hX t)
    rw [he]
    exact (hF.differentiable (by simp)).differentiableAt.comp 0
      (differentiableAt_entries_exp_smul X 0)
  have key : ∀ t : ℝ, π (NormedSpace.exp (t • (g * X * g⁻¹))) (π g v) =
      π g (π (NormedSpace.exp (t • X)) v) := by
    intro t
    have hconj : NormedSpace.exp (t • (g * X * g⁻¹)) = g * NormedSpace.exp (t • X) * g⁻¹ := by
      have : t • (g * X * g⁻¹) = g * (t • X) * g⁻¹ := by
        simp [Matrix.mul_assoc, Matrix.mul_smul, Matrix.smul_mul]
      rw [this, Matrix.exp_conj _ _ hu]
    have hge : g * NormedSpace.exp (t • X) ∈ G := hG.mul_mem _ hg _ (hX t)
    have h1 : π (g * NormedSpace.exp (t • X) * g⁻¹ * g) =
        (π (g * NormedSpace.exp (t • X) * g⁻¹)).comp (π g) :=
      hrep.2 _ (hG.mul_mem _ hge _ hgi) _ hg
    have h2 : g * NormedSpace.exp (t • X) * g⁻¹ * g = g * NormedSpace.exp (t • X) := by
      rw [Matrix.mul_assoc _ g⁻¹ g, hinv, Matrix.mul_one]
    have h3 := hrep.2 _ hg _ (hX t)
    rw [hconj]
    rw [h2, h3] at h1
    exact (DFunLike.congr_fun h1 v).symm
  have h2 := ((π g).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd.hasDerivAt
  have h3 : deriv (fun t : ℝ => π (NormedSpace.exp (t • (g * X * g⁻¹))) (π g v)) 0 =
      π g (deriv (fun t : ℝ => π (NormedSpace.exp (t • X)) v) 0) := by
    rw [funext key]
    exact h2.deriv
  exact h3.symm

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA
end

section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA.SmoothDeriv

open scoped Matrix.Norms.Operator

variable {n : ℕ}

def coord : Matrix (Fin n) (Fin n) ℂ →L[ℝ] (Fin n → Fin n → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => Matrix.of.symm A
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

theorem coord_apply (A : Matrix (Fin n) (Fin n) ℂ) : coord A = Matrix.of.symm A := rfl

theorem hasDerivAt_coord_mul_exp (g X : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => coord (g * NormedSpace.exp (t • X))) (coord (g * X)) 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h
  exact coord.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (h.const_mul g)

theorem contDiff_mul_right (X : Matrix (Fin n) (Fin n) ℂ) :
    ContDiff ℝ ∞ (fun z : Fin n → Fin n → ℂ => Matrix.of.symm (Matrix.of z * X)) := by
  refine contDiff_pi.2 fun a => contDiff_pi.2 fun b => ?_
  have e : (fun z : Fin n → Fin n → ℂ => Matrix.of.symm (Matrix.of z * X) a b) =
      fun z => ∑ c, z a c * X c b := by
    funext z
    simp [Matrix.mul_apply]
  rw [e]
  refine ContDiff.sum fun c _ => ContDiff.mul ?_ contDiff_const
  exact (contDiff_apply ℝ (fun _ => ℂ) c).comp (contDiff_apply ℝ (fun _ => (Fin n → ℂ)) a)

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA.SmoothDeriv

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA

open SmoothDeriv

theorem hasDerivAt_dRep_and_isSmoothVec : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G)
    (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {v : H} (hv : IsSmoothVec G π v) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X ∈ HCSS.lieOf G),
    HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) v) (dRep π X v) 0 ∧
      IsSmoothVec G π (dRep π X v) := by
  intro n G H _ _ π hG hrep v hv X hX
  obtain ⟨F, hF, hFG⟩ := hv
  have hFd : Differentiable ℝ F := hF.differentiable (by simp)

  have key : ∀ g ∈ G, HasDerivAt (fun t : ℝ => π g (π (NormedSpace.exp (t • X)) v))
      (fderiv ℝ F (Matrix.of.symm g) (coord (g * X))) 0 := by
    intro g hg
    have h1 := ((hFd (Matrix.of.symm g)).hasFDerivAt)
    have h2 : HasFDerivAt F (fderiv ℝ F (Matrix.of.symm g)) (coord (g * NormedSpace.exp ((0 : ℝ) • X))) := by
      simpa [coord_apply] using h1
    have h3 := h2.comp_hasDerivAt (0 : ℝ) (hasDerivAt_coord_mul_exp g X)
    refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    have hm : g * NormedSpace.exp (t • X) ∈ G := hG.mul_mem g hg _ (hX t)
    have := hFG (Matrix.of.symm (g * NormedSpace.exp (t • X))) (by
      rw [Equiv.apply_symm_apply]
      exact hm)
    simp only [Equiv.apply_symm_apply] at this
    simp only [Function.comp, coord_apply]
    rw [← this, hrep.2 g hg _ (hX t)]
    rfl
  have h1 : HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) v)
      (fderiv ℝ F (Matrix.of.symm 1) (coord (1 * X))) 0 := by
    have := key 1 hG.one_mem
    simpa [hrep.1] using this
  have hd : dRep π X v = fderiv ℝ F (Matrix.of.symm 1) (coord (1 * X)) := h1.deriv
  have h1' : HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) v) (dRep π X v) 0 := by
    rw [hd]; exact h1
  refine ⟨h1', fun z => fderiv ℝ F z (Matrix.of.symm (Matrix.of z * X)), ?_, ?_⟩
  · exact (hF.fderiv_right (m := ∞) (by simp)).clm_apply (contDiff_mul_right X)
  · intro z hz
    have h2 := ((π (Matrix.of z)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1'
    exact h2.unique (key _ hz)

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA

end
end

section

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA

theorem contDiff_mulRight {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    ContDiff ℝ ∞ (fun z : Fin n → Fin n → ℂ => (fun i j => (Matrix.of z * g) i j : Fin n → Fin n → ℂ)) := by
  have e : (fun z : Fin n → Fin n → ℂ => (fun i j => (Matrix.of z * g) i j : Fin n → Fin n → ℂ)) =
      fun z i j => ∑ k, z i k * g k j := by
    ext z i j
    simp [Matrix.mul_apply]
  rw [e]
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  refine ContDiff.sum fun k _ => ?_
  exact ((contDiff_apply ℝ (fun _ => ℂ) k).comp (contDiff_apply ℝ (fun _ => (Fin n → ℂ)) i)).mul contDiff_const

theorem smooth_closed : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G)
    (hrep : Formalism.QuantumDeterminants.IsCRepOn G π),
    (∀ u v : H, IsSmoothVec G π u → IsSmoothVec G π v → IsSmoothVec G π (u + v)) ∧
    (∀ (c : ℂ) (v : H), IsSmoothVec G π v → IsSmoothVec G π (c • v)) ∧
    (∀ g ∈ G, ∀ v : H, IsSmoothVec G π v → IsSmoothVec G π (π g v)) := by
  intro n G H _ _ π hG hrep
  refine ⟨?_, ?_, ?_⟩
  · rintro u v ⟨Fu, hFu, hu⟩ ⟨Fv, hFv, hv⟩
    refine ⟨fun z => Fu z + Fv z, hFu.add hFv, fun z hz => ?_⟩
    rw [map_add (f := _), hu z hz, hv z hz]
  · rintro c v ⟨Fv, hFv, hv⟩
    refine ⟨fun z => c • Fv z, hFv.const_smul c, fun z hz => ?_⟩
    rw [map_smul, hv z hz]
  · rintro g hg v ⟨Fv, hFv, hv⟩
    refine ⟨fun z => Fv (fun i j => (Matrix.of z * g) i j), hFv.comp (contDiff_mulRight g),
      fun z hz => ?_⟩
    calc π (Matrix.of z) (π g v) = π (Matrix.of z * g) v := by
          rw [hrep.2 _ hz _ hg, ContinuousLinearMap.comp_apply]
      _ = Fv (fun i j => (Matrix.of z * g) i j) := hv _ (hG.mul_mem _ hz _ hg)

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA

end
end
