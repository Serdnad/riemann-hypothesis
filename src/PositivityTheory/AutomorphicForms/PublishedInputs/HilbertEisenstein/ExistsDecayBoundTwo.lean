module

public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.SSmooth
public import GroundTheory.GlobalFields.TateThesis.AdelePoissonUniform
import GroundTheory.GlobalFields.TateThesis.AdeleScaling
public import GroundTheory.GlobalFields.TateThesis.TateThetaDecay
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published
open NumberField.mixedEmbedding
open scoped nonZeroDivisors Classical

namespace UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem norm_hms_le_norm_pInf (x : Ad F) :
    ‖homeomorphMixedSpace F x.1‖ ≤ ‖UpperTheory.V.TR.pInf F x‖ := by
  rw [norm_eq_sup'_normAtPlace]
  refine Finset.sup'_le _ _ fun v _ ↦ ?_
  rw [normAtPlace_homeomorphMixedSpace]
  have hv := IsTotallyReal.isReal v
  have h : ‖x.1 v‖ = ‖UpperTheory.V.TR.pInf F x v‖ := by
    change ‖x.1 v‖ = ‖InfinitePlace.Completion.ringEquivRealOfIsReal hv (x.1 v)‖
    exact ((InfinitePlace.Completion.isometryEquivRealOfIsReal hv).isometry.norm_map_of_map_zero
      (map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal hv)) (x.1 v)).symm
  rw [h]
  exact norm_le_pi_norm (UpperTheory.V.TR.pInf F x) v

theorem decay_one {C : Set (Ideles F)} (hC : IsCompact C) (d : 𝓞 F) (hd : d ≠ 0) (r : ℕ) :
    ∃ (k : ℕ) (u : F → ℝ), Summable u ∧ (∀ ξ, 0 ≤ u ξ) ∧ ∀ a ∈ C, ∀ T : {x : ℝ // 0 < x},
      1 ≤ (T : ℝ) → ∀ ξ : F, ξ ≠ 0 → (∃ s : 𝓞 F, (d : F) * ξ = s) →
      ((1 + ‖homeomorphMixedSpace F ((((moduleSection (w0 F) T * a : Ideles F) : Ad F) *
          algebraMap F (Ad F) ξ).1)‖) ^ k)⁻¹ ≤ ((T : ℝ) ^ r)⁻¹ * u ξ :=
  exists_summable_majorant_moduleSection (w0 F) hC d hd r

theorem exists_decay_bound_two (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
    {C : Set (Ideles F)} (hC : IsCompact C) (d : 𝓞 F) (hd : d ≠ 0) (r : ℕ) :
    ∃ (k : ℕ) (U : (Fin 2 → F) → ℝ), Summable U ∧ ∀ a ∈ C, ∀ T : {x : ℝ // 0 < x}, 1 ≤ (T : ℝ) →
      ∀ ξ : Fin 2 → F, ξ ≠ 0 → (∀ i, ∃ s : 𝓞 F, (d : F) * ξ i = s) →
      ((1 + ‖fun i => UpperTheory.V.TR.pInf F (((moduleSection (w0 F) T * a : Ideles F) : Ad F) *
          algebraMap F (Ad F) (ξ i))‖) ^ k)⁻¹ ≤ ((T : ℝ) ^ r)⁻¹ * U ξ := by
  obtain ⟨k, u, hu, hu0, hb⟩ := decay_one hC d hd r
  set W : F → ℝ := fun η => if η = 0 then 1 else u η with hWdef
  have hW0 : ∀ η, 0 ≤ W η := fun η => by
    simp only [hWdef]
    split_ifs
    · exact zero_le_one
    · exact hu0 η
  have hWs : Summable W := by
    refine Summable.of_nonneg_of_le hW0 (fun η => ?_)
      (hu.add (hasSum_ite_eq (0 : F) (1 : ℝ)).summable)
    simp only [hWdef]
    split_ifs with h
    · linarith [hu0 η]
    · linarith
  refine ⟨2 * k, fun ξ => W (ξ 0) * W (ξ 1), ?_, ?_⟩
  · have hprod : Summable fun p : F × F => W p.1 * W p.2 :=
      hWs.mul_of_nonneg hWs (fun η => hW0 η) (fun η => hW0 η)
    exact (finTwoArrowEquiv F).summable_iff.2 hprod
  intro a ha T hT ξ hξ hds
  set y : Ideles F := moduleSection (w0 F) T * a with hy
  have hTr : ((T : ℝ) ^ r)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hT)
  set f : Fin 2 → ℝ := fun i =>
    ((1 + ‖homeomorphMixedSpace F (((y : Ad F)) * algebraMap F (Ad F) (ξ i)).1‖) ^ k)⁻¹ with hfdef
  have hf0 : ∀ i, 0 ≤ f i := fun i => by simp only [hfdef]; positivity
  have hfT : ∀ i, ξ i ≠ 0 → f i ≤ ((T : ℝ) ^ r)⁻¹ * W (ξ i) := by
    intro i h
    simp only [hfdef, hWdef, if_neg h]
    exact hb a ha T hT (ξ i) h (hds i)
  have hfW : ∀ i, f i ≤ W (ξ i) := by
    intro i
    by_cases h : ξ i = 0
    · have h0 : homeomorphMixedSpace F (((y : Ad F)) * algebraMap F (Ad F) (ξ i)).1 = 0 := by
        rw [h, map_zero, mul_zero, homeomorphMixedSpace_apply]
        exact map_zero _
      simp only [hfdef, hWdef, if_pos h, h0, norm_zero, add_zero, one_pow, inv_one, le_refl]
    · exact (hfT i h).trans (mul_le_of_le_one_left (hW0 _) hTr)
  have hvec : ∀ i, ‖homeomorphMixedSpace F (((y : Ad F)) * algebraMap F (Ad F) (ξ i)).1‖ ≤
      ‖fun i => UpperTheory.V.TR.pInf F ((y : Ad F) * algebraMap F (Ad F) (ξ i))‖ := fun i =>
    (norm_hms_le_norm_pInf _).trans
      (norm_le_pi_norm (fun i => UpperTheory.V.TR.pInf F ((y : Ad F) * algebraMap F (Ad F) (ξ i))) i)
  have hmain : ((1 + ‖fun i => UpperTheory.V.TR.pInf F ((y : Ad F) * algebraMap F (Ad F) (ξ i))‖) ^
      (2 * k))⁻¹ ≤ f 0 * f 1 := by
    rw [two_mul, pow_add, mul_inv]
    exact mul_le_mul
      (inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) (by linarith [hvec 0]) k))
      (inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) (by linarith [hvec 1]) k))
      (by positivity) (hf0 0)
  refine hmain.trans ?_
  have hTr0 : 0 ≤ ((T : ℝ) ^ r)⁻¹ := by positivity
  by_cases h0 : ξ 0 = 0
  · have h1 : ξ 1 ≠ 0 := by
      intro h1
      apply hξ
      funext i
      fin_cases i
      · exact h0
      · exact h1
    calc f 0 * f 1 ≤ W (ξ 0) * (((T : ℝ) ^ r)⁻¹ * W (ξ 1)) :=
          mul_le_mul (hfW 0) (hfT 1 h1) (hf0 1) (hW0 _)
      _ = ((T : ℝ) ^ r)⁻¹ * (W (ξ 0) * W (ξ 1)) := by ring
  · calc f 0 * f 1 ≤ (((T : ℝ) ^ r)⁻¹ * W (ξ 0)) * W (ξ 1) :=
          mul_le_mul (hfT 0 h0) (hfW 1) (hf0 1) (mul_nonneg hTr0 (hW0 _))
      _ = ((T : ℝ) ^ r)⁻¹ * (W (ξ 0) * W (ξ 1)) := by ring

end UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness
