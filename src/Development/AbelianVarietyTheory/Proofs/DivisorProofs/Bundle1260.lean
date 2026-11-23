module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle917
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle002
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1183
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1117
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisKaehlerOfAlgebraicIndependent
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1179
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1180
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ComplexMultiplicationJPremises
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective

@[expose] public section

section

open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

noncomputable section

namespace GlobalTheory.JSW.MirCinf

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

namespace SmoothGrowth

theorem isOpenEmbedding_valGLInf :
    Topology.IsOpenEmbedding (fun g : GL (Fin n) (Cinf E) => fun i j => (g : Matrix (Fin n) (Fin n) (Cinf E)) i j) := by
  open scoped Matrix.Norms.Operator in exact Units.isOpenEmbedding_val (R := Matrix (Fin n) (Fin n) (Cinf E))

theorem isOpen_isUnit_ofInf : IsOpen {x : Fin n → Fin n → Cinf E | IsUnit (Matrix.of x)} := by
  have := (isOpenEmbedding_valGLInf (E := E) (n := n)).isOpen_range
  convert this using 1
  ext x
  exact ⟨fun ⟨u, hu⟩ => ⟨u, hu⟩, fun ⟨u, hu⟩ => ⟨u, hu⟩⟩

theorem continuousOn_toGLInf :
    ContinuousOn (fun x : Fin n → Fin n → Cinf E => toGLInf (Matrix.of x)) {x | IsUnit (Matrix.of x)} := by
  rw [isOpenEmbedding_valGLInf.isInducing.continuousOn_iff]
  exact continuousOn_id.congr fun x hx => val_toGLInf hx

theorem continuous_compGL (w : InfinitePlace E) : Continuous (compGL (n := n) w) := by
  rw [Units.continuous_iff]
  refine ⟨?_, ?_⟩
  · have h : Continuous fun g : GL (Fin n) (Cinf E) => (g : Matrix (Fin n) (Fin n) (Cinf E)) := Units.continuous_val
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact (continuous_apply w).comp ((continuous_apply j).comp ((continuous_apply i).comp h))
  · have h : Continuous fun g : GL (Fin n) (Cinf E) => ((g⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) :=
      Units.continuous_coe_inv
    refine continuous_pi fun i => continuous_pi fun j => ?_
    have e : (fun g : GL (Fin n) (Cinf E) => ((compGL w g)⁻¹ : GL (Fin n) ℂ).val i j) =
        fun g => ((g⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) i j w := by
      funext g
      rw [← map_inv]; rfl
    change Continuous (fun g : GL (Fin n) (Cinf E) => ((compGL w g)⁻¹ : GL (Fin n) ℂ).val i j)
    rw [e]
    exact (continuous_apply w).comp ((continuous_apply j).comp ((continuous_apply i).comp h))

theorem continuous_htInf : Continuous (htInf : GL (Fin n) (Cinf E) → ℝ) := by
  unfold htInf
  exact continuous_finsetProd _ fun w _ => continuous_htGL.comp (continuous_compGL w)

theorem htInf_pos' (g : GL (Fin n) (Cinf E)) : 0 < htInf g := by
  unfold htInf
  exact Finset.prod_pos fun w _ => htGL_pos _

theorem htInf_mul_le (g h : GL (Fin n) (Cinf E)) : htInf (g * h) ≤ htInf g * htInf h := by
  unfold htInf
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun w _ => (htGL_pos _).le) fun w _ => ?_
  rw [map_mul]
  exact htGL_mul_le _ _

theorem measurable_comp_GLInf {X β : Type} [MeasurableSpace X] [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β]
    {F : GL (Fin n) (Cinf E) → β} (hF : Continuous F) {γ : X → GL (Fin n) (Cinf E)}
    (hγ : ∀ i j, Measurable fun x => (γ x : Matrix (Fin n) (Fin n) (Cinf E)) i j) : Measurable fun x => F (γ x) := by
  letI : MeasurableSpace (GL (Fin n) (Cinf E)) := borel _
  haveI : BorelSpace (GL (Fin n) (Cinf E)) := ⟨rfl⟩
  have h : Measurable γ := (isOpenEmbedding_valGLInf.measurableEmbedding.measurable_comp_iff).1
    (Measurable.of_eval fun i => Measurable.of_eval fun j => hγ i j)
  exact hF.measurable.comp h

theorem measurable_toGLInf_entry (i j : Fin n) :
    Measurable fun x : Fin n → Fin n → Cinf E => (toGLInf (Matrix.of x) : Matrix (Fin n) (Fin n) (Cinf E)) i j := by
  classical
  have : (fun x : Fin n → Fin n → Cinf E => (toGLInf (Matrix.of x) : Matrix (Fin n) (Fin n) (Cinf E)) i j) =
      fun x => if x ∈ {x : Fin n → Fin n → Cinf E | IsUnit (Matrix.of x)} then x i j
        else (1 : Matrix (Fin n) (Fin n) (Cinf E)) i j := by
    funext x
    by_cases h : IsUnit (Matrix.of x) <;> simp [toGLInf, h]
  rw [this]
  exact Measurable.ite isOpen_isUnit_ofInf.measurableSet (by fun_prop) measurable_const

theorem smoothMatInf_integrand_eq (α : (Fin n → Fin n → Cinf E) → ℂ)
    (hsub : tsupport α ⊆ {x | IsUnit (Matrix.of x)}) (W : GL (Fin n) (Cinf E) → ℂ) (g : GL (Fin n) (Cinf E))
    (a : Fin n → Fin n → Cinf E) :
    α a * onMatInf W ((g : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of a) = α a * W (g * toGLInf (Matrix.of a)) := by
  by_cases ha : a ∈ tsupport α
  · have hu : IsUnit (Matrix.of a) := hsub ha
    have : (g : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of a =
        ((g * toGLInf (Matrix.of a) : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) := by
      rw [Units.val_mul, val_toGLInf hu]
    rw [this, onMatInf_val]
  · rw [image_eq_zero_of_notMem_tsupport ha, zero_mul, zero_mul]

end SmoothGrowth

open SmoothGrowth

theorem isModGrowthInf_smoothMatInf : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (α : (Fin n → Fin n → Cinf E) → ℂ),
    Continuous α → HasCompactSupport α → tsupport α ⊆ {x | IsUnit (Matrix.of x)} →
    ∀ W : GL (Fin n) (Cinf E) → ℂ, IsModGrowthInf W → IsModGrowthInf (smoothMatInf α W) := by
  intro E _ _ n α hα hcs hsub W hW
  haveI : FirstCountableTopology (GL (Fin n) (Cinf E)) :=
    (isOpenEmbedding_valGLInf (E := E) (n := n)).isInducing.firstCountableTopology
  obtain ⟨hWc, C, N, hC⟩ := hW
  have hC0 : 0 ≤ C := by
    have := (norm_nonneg _).trans (hC 1)
    exact nonneg_of_mul_nonneg_left this (pow_pos (htInf_pos' _) _)
  have hK : IsCompact (tsupport α) := hcs
  have hcont : ContinuousOn (fun a : Fin n → Fin n → Cinf E => htInf (toGLInf (Matrix.of a))) (tsupport α) :=
    continuous_htInf.comp_continuousOn (continuousOn_toGLInf.mono hsub)
  obtain ⟨R₀, hR₀⟩ := hK.exists_bound_of_continuousOn hcont
  set R : ℝ := max R₀ 1
  have hRb : ∀ a ∈ tsupport α, htInf (toGLInf (Matrix.of a)) ≤ R := fun a ha => by
    have := hR₀ a ha
    rw [Real.norm_eq_abs] at this
    exact (le_abs_self _).trans (this.trans (le_max_left _ _))
  have hαi : Integrable (fun a => ‖α a‖) (volume : Measure (Fin n → Fin n → Cinf E)) :=
    (hα.integrable_of_hasCompactSupport hcs).norm
  set F : GL (Fin n) (Cinf E) → (Fin n → Fin n → Cinf E) → ℂ := fun g a => α a * W (g * toGLInf (Matrix.of a)) with hF
  have hsm : smoothMatInf α W = fun g => ∫ a, F g a := by
    funext g
    unfold smoothMatInf
    exact integral_congr_ae (Filter.Eventually.of_forall fun a => smoothMatInf_integrand_eq α hsub W g a)
  have hbound : ∀ g a, ‖F g a‖ ≤ ‖α a‖ * (C * R ^ N * htInf g ^ N) := by
    intro g a
    by_cases ha : a ∈ tsupport α
    · simp only [hF, norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have h1 : htInf (g * toGLInf (Matrix.of a)) ≤ htInf g * R :=
        (htInf_mul_le _ _).trans (mul_le_mul_of_nonneg_left (hRb a ha) (htInf_pos' _).le)
      have h2 := pow_le_pow_left₀ (htInf_pos' _).le h1 N
      calc ‖W (g * toGLInf (Matrix.of a))‖ ≤ C * htInf (g * toGLInf (Matrix.of a)) ^ N := hC _
        _ ≤ C * (htInf g * R) ^ N := mul_le_mul_of_nonneg_left h2 hC0
        _ = C * R ^ N * htInf g ^ N := by ring
    · simp [hF, image_eq_zero_of_notMem_tsupport ha]
  have hmeas : ∀ g, AEStronglyMeasurable (F g) volume := fun g =>
    (hα.measurable.mul (measurable_comp_GLInf (F := fun q => W (g * q)) (by fun_prop)
      (fun i j => measurable_toGLInf_entry i j))).aestronglyMeasurable
  rw [hsm]
  refine ⟨?_, C * R ^ N * ∫ a, ‖α a‖, N, fun g => ?_⟩
  · rw [continuous_iff_continuousAt]
    intro g₀
    have hev : ∀ᶠ g in nhds g₀, htInf g ≤ htInf g₀ + 1 :=
      (continuous_htInf.continuousAt).eventually (gt_mem_nhds (lt_add_one (htInf g₀))) |>.mono fun _ h => h.le
    refine continuousAt_of_dominated (bound := fun a => ‖α a‖ * (C * R ^ N * (htInf g₀ + 1) ^ N))
      (Filter.Eventually.of_forall hmeas) ?_ (hαi.mul_const _) ?_
    · filter_upwards [hev] with g hg
      refine Filter.Eventually.of_forall fun a => (hbound g a).trans ?_
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity)) (norm_nonneg _)
      exact pow_le_pow_left₀ (htInf_pos' _).le hg N
    · refine Filter.Eventually.of_forall fun a => ?_
      exact (continuous_const.mul (hWc.comp (continuous_id.mul continuous_const))).continuousAt
  · calc ‖∫ a, F g a‖ ≤ ∫ a, ‖α a‖ * (C * R ^ N * htInf g ^ N) :=
          norm_integral_le_of_norm_le (hαi.mul_const _) (Filter.Eventually.of_forall (hbound g))
      _ = C * R ^ N * (∫ a, ‖α a‖) * htInf g ^ N := by rw [integral_mul_const]; ring

end GlobalTheory.JSW.MirCinf
end
end

section

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW.MirCinf

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem isOpenEmbedding_entriesGLInf :
    Topology.IsOpenEmbedding (fun g : GL (Fin n) (Cinf E) => fun i j => (g : Matrix (Fin n) (Fin n) (Cinf E)) i j) := by
  open scoped Matrix.Norms.Operator in exact Units.isOpenEmbedding_val (R := Matrix (Fin n) (Fin n) (Cinf E))

theorem measurable_comp_GLInf {X β : Type} [MeasurableSpace X] [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β]
    {F : GL (Fin n) (Cinf E) → β} (hF : Continuous F) {γ : X → GL (Fin n) (Cinf E)}
    (hγ : ∀ i j, Measurable fun x => (γ x : Matrix (Fin n) (Fin n) (Cinf E)) i j) : Measurable fun x => F (γ x) := by
  letI : MeasurableSpace (GL (Fin n) (Cinf E)) := borel _
  haveI : BorelSpace (GL (Fin n) (Cinf E)) := ⟨rfl⟩
  have h : Measurable γ := (isOpenEmbedding_entriesGLInf.measurableEmbedding.measurable_comp_iff).1
    (Measurable.of_eval fun i => Measurable.of_eval fun j => hγ i j)
  exact hF.measurable.comp h

theorem htInf_pos' (g : GL (Fin n) (Cinf E)) : 0 < htInf g := by
  unfold htInf
  exact Finset.prod_pos fun w _ => htGL_pos _

theorem htInf_mul_le (g h : GL (Fin n) (Cinf E)) : htInf (g * h) ≤ htInf g * htInf h := by
  unfold htInf
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun w _ => (htGL_pos _).le) fun w _ => ?_
  rw [map_mul]
  exact htGL_mul_le _ _

theorem IsRapidFInf.integrable {X Z : Type} [MeasurableSpace X] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {ν : Measure X} {k : X → ℂ} {γ : X → GL (Fin n) (Cinf E)} {η : X → Z →L[ℝ] ℝ} (h : IsRapidFInf ν k γ η)
    {W : GL (Fin n) (Cinf E) → ℂ} (hW : IsModGrowthInf W) (z : Z) (g : GL (Fin n) (Cinf E)) :
    Integrable (fun x => k x * (𝐞 (η x z) : ℂ) * W (g * γ x)) ν := by
  obtain ⟨hc, C, N, hC⟩ := hW
  have hC0 : 0 ≤ C := by
    have := (norm_nonneg _).trans (hC 1)
    exact nonneg_of_mul_nonneg_left this (pow_pos (htInf_pos' _) _)
  refine ((h.2.2.2 N).const_mul (C * htInf g ^ N)).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · refine Measurable.aestronglyMeasurable ((h.1.mul ?_).mul ?_)
    · exact (continuous_subtype_val.comp Real.continuous_fourierChar).measurable.comp (h.2.2.1 z)
    · exact measurable_comp_GLInf (F := fun q => W (g * q)) (by fun_prop) h.2.1
  · rw [norm_mul, norm_mul, Circle.norm_coe, mul_one]
    have h1 : htInf (g * γ x) ≤ htInf g * (htInf (γ x) * (1 + ‖η x‖)) :=
      (htInf_mul_le _ _).trans (mul_le_mul_of_nonneg_left
        (le_mul_of_one_le_right (htInf_pos' _).le (by linarith [norm_nonneg (η x)])) (htInf_pos' _).le)
    have h2 := pow_le_pow_left₀ (htInf_pos' _).le h1 N
    rw [mul_pow] at h2
    calc ‖k x‖ * ‖W (g * γ x)‖ ≤ ‖k x‖ * (C * (htInf g ^ N * (htInf (γ x) * (1 + ‖η x‖)) ^ N)) :=
          mul_le_mul_of_nonneg_left ((hC _).trans (mul_le_mul_of_nonneg_left h2 hC0)) (norm_nonneg _)
      _ = _ := by ring

theorem isKerOpInf_zero_sum {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] :
    IsKerOpInf (E := E) (n := n)
      (fun (_ : GL (Fin n) (Cinf E) → ℂ) (_ : Z) (_ : GL (Fin n) (Cinf E)) => (0 : ℂ)) := by
  refine ⟨Unit, inferInstance, 0, inferInstance, fun _ => 0, fun _ => 1, fun _ => 0, ?_, ?_⟩
  · exact ⟨measurable_const, fun _ _ => measurable_const, fun _ => measurable_const, fun _ => integrable_zero_measure⟩
  · intro W _ z g
    simp

theorem isKerOpInf_add_sum {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {T T' : (GL (Fin n) (Cinf E) → ℂ) → Z → GL (Fin n) (Cinf E) → ℂ} (hT : IsKerOpInf T) (hT' : IsKerOpInf T') :
    IsKerOpInf (fun W z g => T W z g + T' W z g) := by
  obtain ⟨X, mX, ν, hν, k, γ, η, hr, hT⟩ := hT
  obtain ⟨X', mX', ν', hν', k', γ', η', hr', hT'⟩ := hT'
  have e1 : MeasurableEmbedding (Sum.inl : X → X ⊕ X') :=
    ⟨Sum.inl_injective, measurable_inl, fun _ hs => measurableSet_inl_image.2 hs⟩
  have e2 : MeasurableEmbedding (Sum.inr : X' → X ⊕ X') :=
    ⟨Sum.inr_injective, measurable_inr, fun _ hs => measurableSet_inr_image.2 hs⟩
  refine ⟨X ⊕ X', inferInstance, ν.map Sum.inl + ν'.map Sum.inr, inferInstance, Sum.elim k k', Sum.elim γ γ',
    Sum.elim η η', ?_, ?_⟩
  · refine ⟨hr.1.sumElim hr'.1, fun i j => ?_, fun z => ?_, fun N => ?_⟩
    · have : (fun x : X ⊕ X' => ((Sum.elim γ γ' x : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) i j) =
          Sum.elim (fun x => (γ x : Matrix (Fin n) (Fin n) (Cinf E)) i j)
            (fun x => (γ' x : Matrix (Fin n) (Fin n) (Cinf E)) i j) := by
        funext x; cases x <;> rfl
      rw [this]; exact (hr.2.1 i j).sumElim (hr'.2.1 i j)
    · have : (fun x : X ⊕ X' => Sum.elim η η' x z) = Sum.elim (fun x => η x z) (fun x => η' x z) := by
        funext x; cases x <;> rfl
      rw [this]; exact (hr.2.2.1 z).sumElim (hr'.2.2.1 z)
    · rw [integrable_add_measure, e1.integrable_map_iff, e2.integrable_map_iff]
      exact ⟨hr.2.2.2 N, hr'.2.2.2 N⟩
  · intro W hW z g
    have i1 := hr.integrable hW z g
    have i2 := hr'.integrable hW z g
    show T W z g + T' W z g = _
    rw [integral_add_measure, e1.integral_map, e2.integral_map, hT W hW z g, hT' W hW z g]
    · rfl
    · rw [e1.integrable_map_iff]; exact i1
    · rw [e2.integrable_map_iff]; exact i2

theorem isKerOpInf_fintype_sum (E : Type) [Field E] [NumberField E] (n : ℕ) (Z : Type) [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] (ι : Type) [Fintype ι]
    (T : ι → (GL (Fin n) (Cinf E) → ℂ) → Z → GL (Fin n) (Cinf E) → ℂ) (hT : ∀ i, IsKerOpInf (T i)) :
    IsKerOpInf (fun W z g => ∑ i, T i W z g) := by
  classical
  suffices h : ∀ s : Finset ι, IsKerOpInf (fun W z g => ∑ i ∈ s, T i W z g) from h Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty => simpa using (isKerOpInf_zero_sum (E := E) (n := n) (Z := Z))
  | insert a s ha ih =>
    have : (fun W z g => ∑ i ∈ insert a s, T i W z g) = fun W z g => T a W z g + ∑ i ∈ s, T i W z g := by
      funext W z g; rw [Finset.sum_insert ha]
    rw [this]
    exact isKerOpInf_add_sum (hT a) ih

end GlobalTheory.JSW.MirCinf
end
end

section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem prod_derivWeierstrassP_kerReps_pow_four_mul :
    ∀ (L : PeriodPair) (α : ℂ) (S : Finset ℂ), α ≠ 0 → MulStable L α → IsKerReps L α S →
      Even S.card →
      (∏ t ∈ S, L.derivWeierstrassP t) ^ 4 * α ^ 12 = (latticeCurve L).Δ ^ S.card := by
  intro L α S hα hst hS hev
  obtain ⟨a, ha⟩ : ∃ a : ℂ, a = L.ω₁ / 2 := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℂ, b = L.ω₂ / 2 := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : ℂ, z = L.ω₁ / (4 * α) := ⟨_, rfl⟩
  have haL : a ∉ L.lattice := ha ▸ L.ω₁_div_two_notMem_lattice
  have hbL : b ∉ L.lattice := hb ▸ L.ω₂_div_two_notMem_lattice
  have habL : a + b ∉ L.lattice := by
    intro h
    have := (PeriodPair.mul_ω₁_add_mul_ω₂_mem_lattice (L := L) (α := 1 / 2) (β := 1 / 2)).mp
      (by convert h using 1; rw [ha, hb]; push_cast; ring)
    norm_num at this
  have ha2 : 2 * a ∈ L.lattice := by
    have : 2 * a = L.ω₁ := by rw [ha]; ring
    rw [this]; exact L.ω₁_mem_lattice
  have hb2 : 2 * b ∈ L.lattice := by
    have : 2 * b = L.ω₂ := by rw [hb]; ring
    rw [this]; exact L.ω₂_mem_lattice
  have hab2 : 2 * (a + b) ∈ L.lattice := by
    rw [mul_add]; exact add_mem ha2 hb2
  have hz2 : 2 * (α * z) ∉ L.lattice := by
    have : 2 * (α * z) = L.ω₁ / 2 := by rw [hz]; field_simp; ring
    rw [this]; exact L.ω₁_div_two_notMem_lattice
  have two : ∀ x, x ∈ L.lattice → 2 * x ∈ L.lattice := fun x hx => by
    rw [two_mul]; exact add_mem hx hx
  have hshift : ∀ c, 2 * c ∈ L.lattice → α * (z + c) ∉ L.lattice := by
    intro c hc h
    apply hz2
    have := sub_mem (two _ h) (hst _ hc)
    convert this using 1; ring
  have hz1 : α * z ∉ L.lattice := fun h => hz2 (two _ h)
  have hαc : ∀ c, 2 * c ∈ L.lattice → 2 * (α * c) ∈ L.lattice := fun c hc => by
    have := hst _ hc
    convert this using 1; ring
  have h0 := GlobalTheory.T.derivWeierstrassP_mul_prod_translate_of_kernel_reps L α S hα hst hS hev z hz1
  have h1 := GlobalTheory.T.derivWeierstrassP_mul_prod_translate_of_kernel_reps L α S hα hst hS hev (z + a) (hshift a ha2)
  have h2 := GlobalTheory.T.derivWeierstrassP_mul_prod_translate_of_kernel_reps L α S hα hst hS hev (z + b) (hshift b hb2)
  have h3 := GlobalTheory.T.derivWeierstrassP_mul_prod_translate_of_kernel_reps L α S hα hst hS hev (z + (a + b)) (hshift _ hab2)
  have hzz : 2 * z ∉ L.lattice := fun h => hz2 (hαc z h)
  have hL0 := GlobalTheory.T.product_derivWeierstrassP_half_periods_discriminant L a b z haL hbL habL ha2 hb2 hzz
  have hLt : ∀ t ∈ S, L.derivWeierstrassP (z + t) * L.derivWeierstrassP (z + a + t)
      * L.derivWeierstrassP (z + b + t) * L.derivWeierstrassP (z + (a + b) + t)
        = (latticeCurve L).Δ := by
    intro t ht
    have h2t : 2 * (z + t) ∉ L.lattice := by
      intro h
      apply hz2
      have := sub_mem (hαc _ h) (two _ (hS.1 t ht).1)
      convert this using 1; ring
    have := GlobalTheory.T.product_derivWeierstrassP_half_periods_discriminant L a b (z + t) haL hbL habL ha2 hb2 h2t
    rw [← this, add_right_comm z a t, add_right_comm z b t, add_right_comm z (a + b) t]
  have hR := GlobalTheory.T.product_derivWeierstrassP_half_periods_discriminant L (α * a) (α * b) (α * z)
    (fun h => haL (GlobalTheory.T.not_mem_half_lattice_of_odd_multiplier L α a S hα hst hS hev h ha2))
    (fun h => hbL (GlobalTheory.T.not_mem_half_lattice_of_odd_multiplier L α b S hα hst hS hev h hb2))
    (fun h => habL (GlobalTheory.T.not_mem_half_lattice_of_odd_multiplier L α (a + b) S hα hst hS hev (by rwa [mul_add]) hab2))
    (hαc a ha2) (hαc b hb2) hz2
  rw [← mul_add α a b, ← mul_add, ← mul_add, ← mul_add] at hR
  have hP : (∏ t ∈ S, L.derivWeierstrassP (z + t)) * (∏ t ∈ S, L.derivWeierstrassP (z + a + t))
      * (∏ t ∈ S, L.derivWeierstrassP (z + b + t))
      * (∏ t ∈ S, L.derivWeierstrassP (z + (a + b) + t)) = (latticeCurve L).Δ ^ S.card := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
      Finset.prod_congr rfl hLt, Finset.prod_const]
  apply mul_left_cancel₀ (latticeCurve_Δ_ne_zero L)
  have hall := congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) h0 h1) h2) h3
  rw [← hP]
  nth_rewrite 1 [← hR]
  rw [← hL0]
  linear_combination -hall

end GlobalTheory.CMModel
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open IsLocalRing

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.EtaleKlt

theorem ord_functionFieldMap_of_formallyEtale : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (p : W ⟶ Sp ℂ) (f : M ⟶ W) [IsDominant f] (E : DivOver p) (E' : DivOver (f ≫ p)) (h : ∀ x ∈ E.ring, functionFieldMap f x ∈ E'.ring), (∀ x, functionFieldMap f x ∈ E'.ring → x ∈ E.ring) → ((functionFieldMap f).restrict E.ring E'.ring h).FormallyEtale → ((functionFieldMap f).restrict E.ring E'.ring h).EssFiniteType → ∀ g : W.functionFieldˣ, E'.ord (Units.map (functionFieldMap f).toMonoidHom g) = E.ord g := by
  intro M W _ _ p f _ E E' h htr het hft g
  set φ := functionFieldMap f
  set ρ := φ.restrict E.ring E'.ring h
  letI := ρ.toAlgebra
  haveI : Algebra.FormallyEtale E.ring E'.ring := het
  haveI : Algebra.EssFiniteType E.ring E'.ring := hft
  haveI : IsLocalHom (algebraMap E.ring E'.ring) := by
    refine ⟨fun x hx => ?_⟩
    obtain ⟨y, hy⟩ := hx.exists_right_inv
    have e : φ (x : W.functionField) * (y : M.functionField) = 1 := congrArg Subtype.val hy
    have hx0 : (x : W.functionField) ≠ 0 := by
      rintro h0
      rw [h0, map_zero, zero_mul] at e
      exact zero_ne_one e
    have hinv : φ ((x : W.functionField)⁻¹) = y := by
      rw [map_inv₀]
      exact inv_eq_of_mul_eq_one_right e
    have hmem : (x : W.functionField)⁻¹ ∈ E.ring := htr _ (hinv ▸ y.2)
    exact IsUnit.of_mul_eq_one (b := (⟨_, hmem⟩ : E.ring)) (Subtype.ext (mul_inv_cancel₀ hx0))
  have hm := Algebra.FormallyUnramified.map_maximalIdeal (R := E.ring) (S := E'.ring)
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible E.ring
  have ht' : Irreducible (ρ t) := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer, ← hm, (IsDiscreteValuationRing.irreducible_iff_uniformizer t).1 ht, Ideal.map_span,
      Set.image_singleton]
    rfl
  obtain ⟨m, u, e⟩ := exists_eq_unit_mul_zpow (F := W.functionField) ht g.ne_zero
  have h1 := ordTop_vw_unit_mul_zpow (F := W.functionField) ht u m
  have h2 := ordTop_vw_unit_mul_zpow (F := M.functionField) ht' (Units.map ρ.toMonoidHom u) m
  rw [← e, ordTop_vw_of_ne_zero _ g.ne_zero, WithTop.coe_inj] at h1
  have e2 : ((Units.map φ.toMonoidHom g : M.functionFieldˣ) : M.functionField) =
      algebraMap E'.ring M.functionField (Units.map ρ.toMonoidHom u) *
        algebraMap E'.ring M.functionField (ρ t) ^ m := by
    rw [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, e, map_mul, map_zpow₀]
    rfl
  rw [← e2, ordTop_vw_of_ne_zero _ (Units.ne_zero _), WithTop.coe_inj] at h2
  exact h2.trans h1.symm

end GlobalTheory.EtaleKlt
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.rigidified_picard_class_zero_of_locally_zero : ∀ (S : Scheme.{0}) (A T : Over S) [GrpObj A], IsAbelianScheme A → ∀ c : Pic (A ⊗ T).left, GlobalTheory.CechPic.pull (lift (1 : T ⟶ A) (𝟙 T)).left c = 0 → (∀ p : T.left, ∃ (Z : Over S) (z : Z ⟶ T), IsOpenImmersion z.left ∧ p ∈ Set.range z.left ∧ GlobalTheory.CechPic.pull (A ◁ z).left c = 0) → c = 0 := by
  first | exact @GlobalTheory.PicGlue.eq_zero_of_rigid_of_locally_zero | exact GlobalTheory.PicGlue.eq_zero_of_rigid_of_locally_zero | (intros; apply GlobalTheory.PicGlue.eq_zero_of_rigid_of_locally_zero <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.poincareCrystalPairing_swap_eq_neg_flip : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left), P.IsLB → ∀ φ : HdR A →ₗ[R] HdR B →ₗ[R] R, AbDual.IsCorrForm (dp0 R) (𝟙 _) A B P φ → AbDual.IsCorrForm (dp0 R) (𝟙 _) B A (AbDual.swap P) (-φ.flip) := by
  first | exact @GlobalTheory.pairing_swap_eq_neg_flip | exact GlobalTheory.pairing_swap_eq_neg_flip | (intros; apply GlobalTheory.pairing_swap_eq_neg_flip <;> assumption)
end
