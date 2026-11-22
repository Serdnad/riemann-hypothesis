import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.DecompB
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.Unitarize
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CasimirGapAtNoncompactWeight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.CasimirGapAtNoncompactWeight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.DecompA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.AnyDec
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.DataGenSubIrred
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.HasGelfandCharSigLam

noncomputable section

open Polynomial Finset

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

theorem dc_tensF_single_false {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (a b c : Fin n) (v : M) :
    tensF false E a b (Pi.single c v) = Pi.single c (E a b v) + (if b = c then Pi.single a v else 0) := by
  exact ReciprocityTheory.ChartRestriction.DS.dc_tensF_single_false E a b c v

theorem dc_tensF_single_true {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (a b c : Fin n) (v : M) :
    tensF true E a b (Pi.single c v) = Pi.single c (E a b v) - (if a = c then Pi.single b v else 0) := by
  exact ReciprocityTheory.ChartRestriction.DS.dc_tensF_single_true E a b c v

theorem dc_mem_tensSub {M : Type*} [AddCommGroup M] [Module ℂ M] {S : Submodule ℂ M} {f : Fin n → M} :
    f ∈ tensSub S ↔ ∀ c, f c ∈ S := by
  simp [tensSub, Submodule.mem_pi]

theorem dc_tens_gen_le {M : Type*} [AddCommGroup M] [Module ℂ M] {E : Fin n → Fin n → Module.End ℂ M}
    {V : Submodule ℂ M} (dual : Bool) {T : Submodule ℂ (Fin n → M)} (hVT : tensSub V ≤ T)
    (hT : ∀ a b, ∀ f ∈ T, tensF dual E a b f ∈ T) : tensSub (genSub E V) ≤ T := by
  exact ReciprocityTheory.ChartRestriction.DS.dc_tens_gen_le dual hVT hT

section Ambient
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {D : Submodule ℂ H}
  {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {E : Fin n → Fin n → Module.End ℂ D}
  {S : Submodule ℂ D} {dual : Bool}

theorem dc_kDiag_add (k : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → H) :
    kDiag dual σ k (fun c => x c + y c) = fun c => kDiag dual σ k x c + kDiag dual σ k y c := by
  funext c
  simp only [kDiag, map_add, smul_add, Finset.sum_add_distrib]

theorem dc_kDiag_smul (k : Matrix (Fin n) (Fin n) ℂ) (a : ℂ) (x : Fin n → H) :
    kDiag dual σ k (fun c => a • x c) = fun c => a • kDiag dual σ k x c := by
  exact ReciprocityTheory.ChartRestriction.DS.dc_kDiag_smul k a x

theorem dc_isGKEndo_add' {A B : Module.End ℂ (Fin n → D)} (hA : IsGKEndo dual ε σ E S A)
    (hB : IsGKEndo dual ε σ E S B) : IsGKEndo dual ε σ E S (A + B) := by
  exact ReciprocityTheory.ChartRestriction.DS.dc_isGKEndo_add' hA hB

theorem dc_isGKEndo_smul' {A : Module.End ℂ (Fin n → D)} (hA : IsGKEndo dual ε σ E S A) (a : ℂ) :
    IsGKEndo dual ε σ E S (a • A) := by
  exact ReciprocityTheory.ChartRestriction.DS.dc_isGKEndo_smul' hA a

theorem dc_isGKEndo_mul' {A B : Module.End ℂ (Fin n → D)} (hA : IsGKEndo dual ε σ E S A)
    (hB : IsGKEndo dual ε σ E S B) : IsGKEndo dual ε σ E S (A * B) := by
  exact ReciprocityTheory.ChartRestriction.DS.dc_isGKEndo_mul' hA hB

theorem dc_isGKEndo_one' : IsGKEndo dual ε σ E S 1 :=
  ⟨fun f hf => hf, fun _ _ _ _ => rfl, fun _ _ _ _ _ _ h => h⟩

theorem dc_isGKEndo_zero' : IsGKEndo dual ε σ E S 0 := by
  exact ReciprocityTheory.ChartRestriction.DS.dc_isGKEndo_zero'

theorem dc_isGKEndo_aeval {A : Module.End ℂ (Fin n → D)} (hA : IsGKEndo dual ε σ E S A) (p : ℂ[X]) :
    IsGKEndo dual ε σ E S (aeval A p) := by
  exact ReciprocityTheory.ChartRestriction.DS.dc_isGKEndo_aeval hA p

end Ambient

end ReciprocityTheory.ChartRestriction.DS.G2

end

noncomputable section

open Polynomial Finset

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ} {ε : Fin n → Bool}

def dc_wsh (dual : Bool) (μ : Fin n → ℝ) (c : Fin n) : Fin n → ℝ :=
  if dual then μ + Pi.single c 1 else μ - Pi.single c 1

section
variable {M : Type*} [AddCommGroup M] [Module ℂ M] {E : Fin n → Fin n → Module.End ℂ M}

theorem dc_top_coord_false {μ : Fin n → ℝ} {f : Fin n → M} (hf : IsKHWVec ε (tensF false E) μ f)
    (h0 : f ≠ 0) : ∃ c, f c ≠ 0 ∧ IsKHWVec ε E (dc_wsh false μ c) (f c) := by
  exact ReciprocityTheory.ChartRestriction.DS.dc_top_coord_false hf h0

theorem dc_top_coord_true {μ : Fin n → ℝ} {f : Fin n → M} (hf : IsKHWVec ε (tensF true E) μ f)
    (h0 : f ≠ 0) : ∃ c, f c ≠ 0 ∧ IsKHWVec ε E (dc_wsh true μ c) (f c) := by
  exact ReciprocityTheory.ChartRestriction.DS.dc_top_coord_true hf h0

theorem dc_top_coord {dual : Bool} {μ : Fin n → ℝ} {f : Fin n → M} (hf : IsKHWVec ε (tensF dual E) μ f)
    (h0 : f ≠ 0) : ∃ c, f c ≠ 0 ∧ IsKHWVec ε E (dc_wsh dual μ c) (f c) := by
  exact ReciprocityTheory.ChartRestriction.DS.dc_top_coord hf h0

end

section Pi
variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℂ D]

abbrev dc_TX (n : ℕ) (D : Type*) [NormedAddCommGroup D] [InnerProductSpace ℂ D] := PiLp 2 (fun _ : Fin n => D)

def dc_eqv : dc_TX n D ≃ₗ[ℂ] (Fin n → D) := WithLp.linearEquiv 2 ℂ (Fin n → D)

theorem dc_eqv_apply (x : dc_TX n D) : dc_eqv x = x.ofLp := rfl

theorem dc_eqv_symm_apply (f : Fin n → D) : (dc_eqv (n := n)).symm f = WithLp.toLp 2 f := rfl

def dc_tensX (dual : Bool) (E : Fin n → Fin n → Module.End ℂ D) (a b : Fin n) : Module.End ℂ (dc_TX n D) :=
  dc_eqv.symm.conj (tensF dual E a b)

theorem dc_tensX_apply (dual : Bool) (E : Fin n → Fin n → Module.End ℂ D) (a b : Fin n) (x : dc_TX n D) :
    dc_tensX dual E a b x = dc_eqv.symm (tensF dual E a b (dc_eqv x)) := by
  simp [dc_tensX, LinearEquiv.conj_apply]

theorem dc_eqv_tensX (dual : Bool) (E : Fin n → Fin n → Module.End ℂ D) (a b : Fin n) (x : dc_TX n D) :
    dc_eqv (dc_tensX dual E a b x) = tensF dual E a b (dc_eqv x) := by
  rw [dc_tensX_apply, LinearEquiv.apply_symm_apply]

theorem dc_tensX_isGlRep {dual : Bool} {E : Fin n → Fin n → Module.End ℂ D} (hE : IsGlRep E) :
    IsGlRep (dc_tensX dual E) := by
  exact ReciprocityTheory.ChartRestriction.DS.dc_tensX_isGlRep hE

theorem dc_sum_inner_ite_left (a : Fin n) (u : D) (g : Fin n → D) :
    ∑ i, inner ℂ (if i = a then u else 0) (g i) = inner ℂ u (g a) := by
  rw [Finset.sum_eq_single a (fun i _ hi => by simp [hi]) (by simp)]
  simp

theorem dc_sum_inner_ite_right (b : Fin n) (u : D) (g : Fin n → D) :
    ∑ i, inner ℂ (g i) (if i = b then u else 0) = inner ℂ (g b) u := by
  rw [Finset.sum_eq_single b (fun i _ hi => by simp [hi]) (by simp)]
  simp

theorem dc_tensX_isKUnitary {dual : Bool} {E : Fin n → Fin n → Module.End ℂ D} (hU : IsKUnitary ε E) :
    IsKUnitary ε (dc_tensX dual E) := by
  exact ReciprocityTheory.ChartRestriction.DS.dc_tensX_isKUnitary hU

end Pi

end ReciprocityTheory.ChartRestriction.DS.G2

end
