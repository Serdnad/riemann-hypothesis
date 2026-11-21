import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.ComplexHessianIsHermitianOfContDiffAt

namespace ReciprocityTheory.AnForm

open Complex
open A.TraceConjugationCover (hess_comp lv lv_add_left lv_smul_left lv_sum_left lv_comp)
open scoped Matrix

noncomputable section

def leviC {e : ℕ} (H : (Fin e → ℂ) →L[ℝ] (Fin e → ℂ) →L[ℝ] ℝ) (a b : Fin e → ℂ) : ℂ :=
  ((H a b + H (I • a) (I • b) : ℝ) + I * ((H a (I • b) - H (I • a) b : ℝ))) / 4

theorem hessC_eq_leviC {e : ℕ} (f : (Fin e → ℂ) → ℝ) (z : Fin e → ℂ) (i j : Fin e) :
    hessC f z i j = leviC (fderiv ℝ (fderiv ℝ f) z) (Pi.single i 1) (Pi.single j 1) := rfl

theorem leviC_add {e : ℕ} (H : (Fin e → ℂ) →L[ℝ] (Fin e → ℂ) →L[ℝ] ℝ) (a a' b : Fin e → ℂ) :
    leviC H (a + a') b = leviC H a b + leviC H a' b := lv_add_left H a a' b

theorem leviC_smul {e : ℕ} (H : (Fin e → ℂ) →L[ℝ] (Fin e → ℂ) →L[ℝ] ℝ) (c : ℂ) (a b : Fin e → ℂ) :
    leviC H (c • a) b = c * leviC H a b := lv_smul_left H c a b

theorem sum_mul_leviC {e : ℕ} (H : (Fin e → ℂ) →L[ℝ] (Fin e → ℂ) →L[ℝ] ℝ) (v b : Fin e → ℂ) :
    ∑ i, v i * leviC H (Pi.single i 1) b = leviC H v b := (lv_sum_left H v b).symm

theorem hess_comp_of_ker {N e : ℕ} (φ : (Fin N → ℂ) → ℝ) (τ : (Fin e → ℂ) → (Fin N → ℂ))
    (z : Fin e → ℂ) (hτ : AnalyticAt ℂ τ z) (hφ : ContDiffAt ℝ 2 φ (τ z))
    (w b : Fin e → ℂ) (hw : fderiv ℂ τ z w = 0) :
    fderiv ℝ (fderiv ℝ (φ ∘ τ)) z w b =
      fderiv ℝ φ (τ z) (fderiv ℂ (fun x => fderiv ℂ τ x b) z w) := by
  simpa [hw] using hess_comp φ τ z hτ hφ w b

theorem vecMul_hessC_comp_eq_zero {N e : ℕ} (φ : (Fin N → ℂ) → ℝ) (τ : (Fin e → ℂ) → (Fin N → ℂ))
    (z : Fin e → ℂ) (hτ : AnalyticAt ℂ τ z) (hφ : ContDiffAt ℝ 2 φ (τ z))
    (v : Fin e → ℂ) (hv : fderiv ℂ τ z v = 0) :
    v ᵥ* hessC (φ ∘ τ) z = 0 := by
  funext j
  show ∑ i, v i * hessC (φ ∘ τ) z i j = 0
  simp_rw [hessC_eq_leviC]
  rw [sum_mul_leviC]
  change lv _ v (Pi.single j 1) = 0
  rw [lv_comp φ τ z hτ hφ, hv]
  simp [lv]

theorem maDens_comp_eq_zero_of_rank_lt {N e : ℕ} (φ : Fin e → (Fin N → ℂ) → ℝ)
    (τ : (Fin e → ℂ) → (Fin N → ℂ)) (z : Fin e → ℂ) (hτ : AnalyticAt ℂ τ z)
    (hφ : ∀ k, ContDiffAt ℝ 2 (φ k) (τ z))
    (hrk : Module.finrank ℂ (LinearMap.range (fderiv ℂ τ z).toLinearMap) < e) :
    maDens (fun k => φ k ∘ τ) z = 0 := by
  obtain ⟨v, hv0, hv⟩ : ∃ v : Fin e → ℂ, v ≠ 0 ∧ fderiv ℂ τ z v = 0 := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (fderiv ℂ τ z).toLinearMap
    rw [Module.finrank_fin_fun] at h1
    have h2 : 0 < Module.finrank ℂ (LinearMap.ker (fderiv ℂ τ z).toLinearMap) := by omega
    obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.mp h2
    exact ⟨x, fun h => hx (Subtype.ext h), x.2⟩
  have hvm : ∀ S : Finset (Fin e), v ᵥ* (∑ k ∈ S, hessC (φ k ∘ τ) z) = 0 := by
    intro S
    simp [Matrix.vecMul_sum, fun k => vecMul_hessC_comp_eq_zero (φ k) τ z hτ (hφ k) v hv]
  have hdet : ∀ S : Finset (Fin e), (∑ k ∈ S, hessC (φ k ∘ τ) z).det = 0 := fun S =>
    Matrix.exists_vecMul_eq_zero_iff.mp ⟨v, hv0, hvm S⟩
  unfold maDens mdisc
  simp [hdet]

end

end ReciprocityTheory.AnForm
