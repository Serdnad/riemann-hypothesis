import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.HasDerivAtInvExpCurveEntry
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.CoefOfEmb
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.IsSmoothL2OfCasimirEigen
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Smooth
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IntegrableComplexContinuousBoundedSupport
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.AnyDec
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.DataGenSubIrred
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.HasGelfandCharSigLam

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.G2

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

section Mat

variable {ε : Fin n → Bool}

theorem J_mul_J_eq_one (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  exact ReciprocityTheory.ChartRestriction.DS.J_mul_J_eq_one ε

theorem unitary_group_inv_eq_conj {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) : g⁻¹ = Jm ε * gᴴ * Jm ε := by
  exact ReciprocityTheory.ChartRestriction.DS.unitary_group_inv_eq_conj hg

theorem J_conj_entry (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ) (d c : Fin n) :
    (Jm ε * A * Jm ε) d c = (if ε d then 1 else -1) * A d c * (if ε c then 1 else -1) := by
  simp [Jm, Matrix.diagonal_mul, Matrix.mul_diagonal]

theorem J_conj_neg_mul_inv {g X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) :
    Jm ε * (g * X)ᴴ * Jm ε = -(X * (Jm ε * gᴴ * Jm ε)) := by
  exact ReciprocityTheory.ChartRestriction.DS.J_conj_neg_mul_inv hX

theorem hasDerivAt_exp_curve_entry (g X : Matrix (Fin n) (Fin n) ℂ) (c d : Fin n) :
    HasDerivAt (fun t : ℝ => (g * NormedSpace.exp ((t : ℂ) • X)) c d) ((g * X) c d) 0 := by
  have h := Formalism.REAL.hasDerivAt_mul_exp_smul_zero g X
  exact hasDerivAt_pi.1 (hasDerivAt_pi.1 h c) d

theorem hasDerivAt_inv_exp_curve_entry {g X : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (hX : inG ε X) (d c : Fin n) :
    HasDerivAt (fun t : ℝ => (g * NormedSpace.exp ((t : ℂ) • X))⁻¹ d c) (-(X * g⁻¹) d c) 0 := by
  exact ReciprocityTheory.ChartRestriction.DS.hasDerivAt_inv_exp_curve_entry hg hX d c

end Mat

section Coef

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem hasDerivAt_inner_rep_exp (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {g X : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (hX : inG ε X) (w : H) (v : D) :
    HasDerivAt (fun t : ℝ => inner ℂ w (σ (g * NormedSpace.exp ((t : ℂ) • X)) (v : H)))
      (inner ℂ w (σ g ((actM E X v : D) : H))) 0 := by
  exact ReciprocityTheory.ChartRestriction.DS.hasDerivAt_inner_rep_exp hσ hD hg hX w v

def oa1Phi (dual : Bool) (g : Matrix (Fin n) (Fin n) ℂ) (c d : Fin n) : ℂ := cond dual ((g⁻¹) d c) (g c d)

def oa1DPhi (dual : Bool) (g X : Matrix (Fin n) (Fin n) ℂ) (c d : Fin n) : ℂ :=
  cond dual ((-(X * g⁻¹)) d c) ((g * X) c d)

theorem hasDerivAt_tensor_phi {g X : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (hX : inG ε X) (dual : Bool)
    (c d : Fin n) :
    HasDerivAt (fun t : ℝ => oa1Phi dual (g * NormedSpace.exp ((t : ℂ) • X)) c d) (oa1DPhi dual g X c d) 0 := by
  exact ReciprocityTheory.ChartRestriction.DS.hasDerivAt_tensor_phi hg hX dual c d

theorem tensor_coef_expand (dual : Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (η f : Fin n → H)
    (g : Matrix (Fin n) (Fin n) ℂ) :
    ∑ c, inner ℂ (η c) (tensGrp dual σ g f c) = ∑ c, ∑ d, oa1Phi dual g c d * inner ℂ (η c) (σ g (f d)) := by
  simp [tensGrp, oa1Phi, inner_sum]

theorem hasDerivAt_tensor_coef (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {g X : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (hX : inG ε X) (dual : Bool) (η : Fin n → H)
    (f : Fin n → D) :
    HasDerivAt (fun t : ℝ => ∑ c, inner ℂ (η c)
        (tensGrp dual σ (g * NormedSpace.exp ((t : ℂ) • X)) (fun d => (f d : H)) c))
      (∑ c, ∑ d, (oa1DPhi dual g X c d * inner ℂ (η c) (σ g (f d : H)) +
        oa1Phi dual g c d * inner ℂ (η c) (σ g ((actM E X (f d) : D) : H)))) 0 := by
  exact ReciprocityTheory.ChartRestriction.DS.hasDerivAt_tensor_coef hσ hD hg hX dual η f

end Coef

section Eab

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem tensor_dphi_complex_comb (dual : Bool) (g : Matrix (Fin n) (Fin n) ℂ) (a b c d : Fin n) :
    oa1DPhi dual g (Formalism.REAL.cpart1 ε (Matrix.single a b 1)) c d +
        Complex.I * oa1DPhi dual g (Formalism.REAL.cpart2 ε (Matrix.single a b 1)) c d =
      cond dual (-(if d = a then (g⁻¹) b c else 0)) (if d = b then g c a else 0) := by
  exact ReciprocityTheory.ChartRestriction.DS.tensor_dphi_complex_comb dual g a b c d

theorem tensor_coef_Eab_action (dual : Bool) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (η : Fin n → H)
    (f : Fin n → D) (a b : Fin n) {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) :
    Formalism.REAL.Eab ε a b (fun x => ∑ c, inner ℂ (η c) (tensGrp dual σ x (fun d => (f d : H)) c)) g =
      ∑ c, inner ℂ (η c) (tensGrp dual σ g (fun d => (tensF dual E a b f d : H)) c) := by
  exact ReciprocityTheory.ChartRestriction.DS.tensor_coef_Eab_action dual hσ hD η f a b hg

end Eab

end ReciprocityTheory.ChartRestriction.DS.G2
