module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle002
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsBorelSectionUnitaryOrbitQuadric
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle015
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle035
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle003
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle004
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle005
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle004
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle044
public import Formalism.LocalRingCardinality.DataParams₂
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
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
public import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Uniformizable
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle021
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct

namespace GlobalTheory.SelfDualProduct

theorem exists_test (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] :
    ∃ Φ : SchwartzMap V ℂ, HasCompactSupport Φ ∧ Φ 0 = 1 := by
  let b : ContDiffBump (0 : V) := ⟨1, 2, one_pos, one_lt_two⟩
  have h1 : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) :=
    b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  refine ⟨h1.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff), h1, ?_⟩
  change ((b 0 : ℝ) : ℂ) = 1
  rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)]
  simp

theorem integral_prod_exp {T V : Type} [Fintype T] [MeasurableSpace V] (ε : ℝ) (β : V → V → ℝ)
    (μ₀ : Measure V) [SigmaFinite μ₀] (f : V → ℂ) (y : T → V) :
    ∫ x : T → V, (∏ ρ, f (x ρ)) *
        Complex.exp (2 * Real.pi * Complex.I * ((ε * ∑ ρ, β (x ρ) (y ρ) : ℝ) : ℂ))
        ∂(Measure.pi fun _ : T => μ₀) = ∏ ρ, ActionCoordinates.fourierT ε β μ₀ f (y ρ) := by
  unfold ActionCoordinates.fourierT
  rw [← integral_fintype_prod_eq_prod (fun ρ (x : V) => f x *
    Complex.exp (2 * Real.pi * Complex.I * ((ε * β x (y ρ) : ℝ) : ℂ)))]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [Finset.prod_mul_distrib, ← Complex.exp_sum]
  congr 2
  rw [Finset.mul_sum, Complex.ofReal_sum, Finset.mul_sum]

theorem map_eq_pi : ∀ (T V W : Type) [Fintype T] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [AddCommGroup W] [TopologicalSpace W] [MeasurableSpace W] [BorelSpace W] (e : W ≃ₜ+ (T → V)) (ε : ℝ) (β : V → V → ℝ) (μ₀ : Measure V), μ₀.IsAddHaarMeasure → ActionCoordinates.IsSelfDualFor ε β μ₀ → ∀ (μ : Measure W) (χ : W → W → ℂ), (∀ x y, χ x y = Complex.exp (2 * Real.pi * Complex.I * ((ε * ∑ ρ, β (e x ρ) (e y ρ) : ℝ) : ℂ))) → SelfDual μ χ → μ.map e = Measure.pi fun _ : T => μ₀ := by
  intro T V W _ _ _ _ _ _ _ _ _ _ e ε β μ₀ hμ₀ hsd μ χ hχ hμ
  haveI : IsTopologicalAddGroup W :=
    Topology.IsInducing.topologicalAddGroup (e : W →+ (T → V)) e.toHomeomorph.isInducing
  haveI := hμ.1
  haveI : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  set ν : Measure (T → V) := Measure.pi fun _ : T => μ₀ with hν
  haveI : ν.IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have h0 : μ.map e = Measure.addHaarScalarFactor (μ.map e) ν • ν :=
    Measure.isAddLeftInvariant_eq_smul _ _
  set c : NNReal := Measure.addHaarScalarFactor (μ.map e) ν
  have hemb : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  have hint : ∀ F : (T → V) → ℂ, ∫ x, F (e x) ∂μ = (c : ℂ) * ∫ x, F x ∂ν := fun F => by
    rw [← hemb.integral_map, h0, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  have hF : ∀ (f : V → ℂ) (y : W), ∫ x, (∏ ρ, f (e x ρ)) * χ x y ∂μ =
      (c : ℂ) * ∏ ρ, ActionCoordinates.fourierT ε β μ₀ f (e y ρ) := fun f y => by
    rw [← integral_prod_exp, ← hint]
    simp only [hχ]
  obtain ⟨φ, hφs, hφ0⟩ := exists_test V
  obtain ⟨-, hI, hinv⟩ := hsd φ
  have hc1 : Continuous fun x : T → V => ∏ ρ, φ (x ρ) :=
    by fun_prop
  have hs1 : HasCompactSupport fun x : T → V => ∏ ρ, φ (x ρ) := by
    refine HasCompactSupport.intro (isCompact_univ_pi fun _ : T => hφs.isCompact) fun x hx => ?_
    rw [Set.mem_univ_pi, not_forall] at hx
    obtain ⟨ρ, hρ⟩ := hx
    exact Finset.prod_eq_zero (Finset.mem_univ ρ) (image_eq_zero_of_notMem_tsupport hρ)
  have hI1 : Integrable (fun y : T → V => (c : ℂ) * ∏ ρ, ActionCoordinates.fourierT ε β μ₀ φ (y ρ))
      (μ.map e) := by
    rw [h0]
    exact ((Integrable.fintype_prod (f := fun _ : T => ActionCoordinates.fourierT ε β μ₀ φ)
      fun _ => hI).const_mul _).smul_measure_nnreal
  have key := hμ.2 (fun x => ∏ ρ, φ (e x ρ)) (hc1.comp e.continuous)
    (hs1.comp_homeomorph e.toHomeomorph) (by
      simp only [hF]
      exact (hemb.integrable_map_iff).1 hI1) 0
  simp only [hF, mul_assoc] at key
  rw [integral_const_mul, hF] at key
  simp only [hinv, map_zero, neg_zero, Pi.zero_apply, hφ0, Finset.prod_const_one, mul_one] at key
  have h5 : c * c = 1 := by exact_mod_cast key
  have h6 : c = 1 := by
    have : (c : ℝ) * c = 1 := by exact_mod_cast h5
    have h7 : (c : ℝ) = 1 := by nlinarith [c.coe_nonneg]
    exact_mod_cast h7
  rw [h0, h6, one_smul]

end GlobalTheory.SelfDualProduct
end

section

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot
open scoped ENNReal NNReal

theorem _root_.GlobalTheory.T.positiveDefiniteUnitSphereMass_proof : GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.SphereMass := by
  first | exact @GlobalTheory.SphereMassProof.sphereMass | exact GlobalTheory.SphereMassProof.sphereMass | (intros; apply GlobalTheory.SphereMassProof.sphereMass <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct

namespace GlobalTheory.StabiliserCutoff

variable {P Q : ℕ}

theorem qf_eq (x : ActionCoordinates.Wsp P Q) : ActionCoordinates.qf x = PerpendicularEmbedding.qf x := by
  have h : ActionCoordinates.herm x x = PerpendicularEmbedding.herm x x := by
    simp [ActionCoordinates.herm, PerpendicularEmbedding.herm, ActionCoordinates.sgn, Fintype.sum_sum_type, sub_eq_add_neg]
  rw [ActionCoordinates.qf, h, PerpendicularEmbedding.herm_self, Complex.ofReal_re]

theorem qf_act (g : UpqT P Q) (x : PerpendicularEmbedding.Sp P Q) : PerpendicularEmbedding.qf (ActionCoordinates.act g x) = PerpendicularEmbedding.qf x := by
  have h : (PerpendicularEmbedding.qf (ActionCoordinates.act g x) : ℂ) = PerpendicularEmbedding.qf x := by
    rw [← GlobalTheory.QuadricSection.form_self, ← GlobalTheory.QuadricSection.form_self, ActionCoordinates.act, star_mulVec,
      mulVec_mulVec, ← dotProduct_mulVec, mulVec_mulVec, ← Matrix.mul_assoc,
      GlobalTheory.UpqTopology.mat_unitary]
  exact_mod_cast h

theorem act_mul (g h : UpqT P Q) (x : ActionCoordinates.Wsp P Q) :
    ActionCoordinates.act (g * h) x = ActionCoordinates.act g (ActionCoordinates.act h x) := by
  unfold ActionCoordinates.act
  rw [Matrix.mulVec_mulVec]; rfl

theorem act_one (x : ActionCoordinates.Wsp P Q) : ActionCoordinates.act (1 : UpqT P Q) x = x := Matrix.one_mulVec x

theorem continuous_act (x : ActionCoordinates.Wsp P Q) : Continuous fun g : UpqT P Q => ActionCoordinates.act g x :=
  GlobalTheory.UpqTopology.continuous_mat.matrix_mulVec continuous_const

theorem eq_zero_of_herm {v : ActionCoordinates.Wsp P Q} (h : ∀ w, ActionCoordinates.herm v w = 0) : v = 0 := by
  funext i
  have := h (Pi.single i 1)
  rcases i with i | i <;>
    simpa [ActionCoordinates.herm, ActionCoordinates.sgn, Pi.single_apply, apply_ite] using this

theorem exists_cutoff : ∀ (c : CDHaar) (P Q P' Q' : ℕ) (x₀ : ActionCoordinates.Wsp P Q), ActionCoordinates.qf x₀ ≠ 0 →
    ∀ (j : ActionCoordinates.Wsp P' Q' →ₗ[ℂ] ActionCoordinates.Wsp P Q) (ι : UpqT P' Q' → UpqT P Q),
    ActionCoordinates.IsPerpFrame x₀ j ι → Set.range ι = {g | ActionCoordinates.act g x₀ = x₀} →
    ∃ u : UpqT P Q → ℝ≥0∞, Measurable u ∧
      ∀ g, Measurable (fun h => u (ι h * g)) ∧ ∫⁻ h, u (ι h * g) ∂(c.cd P' Q') = 1 := by
  intro c P Q P' Q' x₀ h0 j ι hι hr
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.UpqTopology.upq_lcsc P Q
  obtain ⟨k1, k2, k3, k4, k5, -⟩ := GlobalTheory.UpqTopology.upq_lcsc P' Q'
  haveI := c.haar P' Q'
  haveI := GlobalTheory.UpqUnimodular.isMulRightInvariant_of_isHaarMeasure P' Q' _ (c.haar P' Q')
  obtain ⟨s, hsm, hs⟩ := GlobalTheory.QuadricSection.exists_isSection P Q _ x₀ (qf_eq x₀ ▸ h0) rfl
  obtain ⟨L, hL⟩ := j.exists_leftInverse_of_injective (LinearMap.ker_eq_bot'.2 fun v hv =>
    eq_zero_of_herm fun w => by rw [← hι.1, hv]; simp [ActionCoordinates.herm])
  have hL' : ∀ v, L (j v) = v := fun v => LinearMap.congr_fun hL v
  let Φ : UpqT P' Q' → (Fin P' ⊕ Fin Q') → ActionCoordinates.Wsp P' Q' :=
    fun h b => ActionCoordinates.act h (Pi.single b 1)
  let π : UpqT P Q → (Fin P' ⊕ Fin Q') → ActionCoordinates.Wsp P' Q' :=
    fun g b => L (ActionCoordinates.act g (j (Pi.single b 1)))
  have hΦ : Continuous Φ := continuous_pi fun b => continuous_act _
  have hπ : Continuous π := continuous_pi fun b =>
    L.continuous_of_finiteDimensional.comp (continuous_act _)
  have hΦi : Function.Injective Φ := fun a b hab =>
    GlobalTheory.UpqTopology.isClosedEmbedding_mat.injective (by
      ext x y
      simpa [Φ, ActionCoordinates.act] using congrFun (congrFun hab y) x)
  have hπι : ∀ a b, π (ι a * ι b) = Φ (a * b) := fun a b => by
    funext x
    simp only [π, Φ, act_mul, (hι.2.2 _).2, hL']
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : UpqT P' Q')
  have hpos : c.cd P' Q' K ≠ 0 := (Measure.measure_pos_of_mem_nhds _ hK1).ne'
  have hfin : c.cd P' Q' K ≠ ⊤ := hK.measure_lt_top.ne
  have hO : MeasurableSet (Φ '' K) := (hK.image hΦ).isClosed.measurableSet
  let F : ((Fin P' ⊕ Fin Q') → ActionCoordinates.Wsp P' Q') → ℝ≥0∞ :=
    (Φ '' K).indicator fun _ => (c.cd P' Q' K)⁻¹
  have hF : Measurable F := measurable_const.indicator hO
  have hFΦ : ∀ h, F (Φ h) = K.indicator (fun _ => (c.cd P' Q' K)⁻¹) h := fun h => by
    by_cases hh : h ∈ K
    · simp only [F, Set.indicator_of_mem hh, Set.indicator_of_mem (Set.mem_image_of_mem Φ hh)]
    · simp only [F, Set.indicator_of_notMem hh,
        Set.indicator_of_notMem (mt hΦi.mem_set_image.1 hh)]
  refine ⟨fun g => F (π (g * s (ActionCoordinates.act g⁻¹ x₀))), ?_, fun g => ?_⟩
  · exact hF.comp (hπ.measurable.comp (measurable_id.mul
      (hsm.comp ((continuous_act x₀).comp continuous_inv).measurable)))
  · obtain ⟨h₀, hh₀⟩ : g * s (ActionCoordinates.act g⁻¹ x₀) ∈ Set.range ι := by
      rw [hr]
      change ActionCoordinates.act (g * s (ActionCoordinates.act g⁻¹ x₀)) x₀ = x₀
      have e : ActionCoordinates.act (s (ActionCoordinates.act g⁻¹ x₀)) x₀ = ActionCoordinates.act g⁻¹ x₀ := hs _ (qf_act _ _)
      rw [act_mul, e, ← act_mul, mul_inv_cancel, act_one]
    have e : ∀ h, F (π (ι h * g * s (ActionCoordinates.act (ι h * g)⁻¹ x₀))) = F (Φ (h * h₀)) := fun h => by
      have e1 : ActionCoordinates.act (ι h)⁻¹ x₀ = x₀ := by
        conv_lhs => rw [← (hι.2.2 h).1, ← act_mul, inv_mul_cancel, act_one]
      rw [_root_.mul_inv_rev, act_mul, e1, mul_assoc, ← hh₀, hπι]
    simp only [e]
    refine ⟨hF.comp (hΦ.measurable.comp (measurable_mul_const h₀)), ?_⟩
    rw [lintegral_mul_right_eq_self (fun h => F (Φ h)) h₀]
    simp only [hFΦ]
    rw [lintegral_indicator_const hK.isClosed.measurableSet, ENNReal.inv_mul_cancel hpos hfin]

end GlobalTheory.StabiliserCutoff
end
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct
open scoped RestrictedProduct

noncomputable section

namespace GlobalTheory.LocalComponentChar


open Classical in
theorem continuous_singleV (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (singleV F v) := by
  have hS : Filter.cofinite ≤ Filter.principal ({v}ᶜ : Set (HeightOneSpectrum (𝓞 F))) :=
    Filter.le_principal_iff.2 (Set.finite_singleton v).compl_mem_cofinite
  let f : v.adicCompletion F → Πʳ w : HeightOneSpectrum (𝓞 F),
      [w.adicCompletion F, w.adicCompletionIntegers F]_[Filter.principal ({v}ᶜ : Set _)] :=
    fun x => ⟨Pi.single (M := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) v x, by
      intro w hw
      have hw' : w ≠ v := hw
      simp only [Set.mem_ofPred_eq, Pi.single_eq_of_ne hw', SetLike.mem_coe]
      exact zero_mem _⟩
  have hf : Continuous f := RestrictedProduct.continuous_rng_of_principal.2 (continuous_single v)
  exact (RestrictedProduct.continuous_inclusion hS).comp hf

theorem index_intV (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    (LocalAdditiveCharacterDual.intV F v).index = 0 := by
  by_contra hn
  haveI : CharZero (Fv F v) := charZero_of_injective_algebraMap (algebraMap F (Fv F v)).injective
  obtain ⟨t, ht⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp (1 : ℤ))
  have hn' : (((LocalAdditiveCharacterDual.intV F v).index : ℕ) : Fv F v) ≠ 0 := Nat.cast_ne_zero.2 hn
  have h := (LocalAdditiveCharacterDual.intV F v).nsmul_index_mem (t / (((LocalAdditiveCharacterDual.intV F v).index : ℕ) : Fv F v))
  rw [nsmul_eq_mul, mul_div_cancel₀ _ hn'] at h
  have h1 : Valued.v t ≤ 1 := h
  rw [ht, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
  omega

theorem exists_localChar : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ v : HeightOneSpectrum (𝓞 F), LocalAdditiveCharacterDual.IndexFinite F ψ v → ∃ χ : AddChar (Fv F v) ℂ, PlaceSplittingTypes.IsLocalChar F v χ ∧ ∀ t, χ t = psiV F ψ v t := by
  intro F _ _ ψ hψ v hfin
  refine ⟨⟨psiV F ψ v, LocalAdditiveCharacterDual.psiV_zero F ψ v, LocalAdditiveCharacterDual.psiV_add F ψ v⟩, ⟨?_, fun t => hψ.2.1 _, ?_⟩,
    fun _ => rfl⟩
  · have h2 : Continuous fun x : Fv F v => pairA F 0 (singleV F v x) :=
      Continuous.prodMk continuous_const (continuous_singleV F v)
    exact hψ.1.comp h2
  · by_contra h
    push Not at h
    have htop : LocalAdditiveCharacterDual.psiDual F ψ v = ⊤ := by
      rw [eq_top_iff]
      intro t _ s _
      exact h _
    apply hfin.1
    rw [htop, AddSubgroup.relIndex_top_right]
    exact index_intV F v

end GlobalTheory.LocalComponentChar
end
end

section

noncomputable section

namespace GlobalTheory.UnitVectorPerpCompare

open NumberField Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke

section General

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem selfDual_iff (W : HSpace E) (L : Submodule (𝓞 E) W.V) :
    UnitVectorOrthogonal.IsSelfDualLat W L ↔ SelfDualLatticeComplements.IsSelfDualLattice W L := Iff.rfl

theorem ofKind_iff (W : HSpace E) (M P Q : ℕ) :
    UnitVectorOrthogonal.OfKind W M P Q ↔ SelfDualLatticeComplements.OfKind W M P Q :=
  ⟨fun ⟨a, b, c⟩ => ⟨b, a, c⟩, fun ⟨a, b, c⟩ => ⟨b, a, c⟩⟩

theorem hasComplement_iff (W : HSpace E) (x : W.V) (M' P' Q' : ℕ) :
    UnitVectorOrthogonal.HasComplement W x M' P' Q' ↔ SelfDualLatticeComplements.HasComplement W x M' P' Q' := by
  constructor
  · rintro ⟨L, hL, hx, hs, W', ι, hk, hi, hr, hm⟩
    exact ⟨L, W', ι, (selfDual_iff W L).1 hL, hx, (ofKind_iff _ _ _ _).1 hk, hi, hr, hm, hs⟩
  · rintro ⟨L, W', ι, hL, hx, hk, hi, hr, hm, hs⟩
    exact ⟨L, (selfDual_iff W L).2 hL, hx, hs, W', ι, (ofKind_iff _ _ _ _).2 hk, hi, hr, hm⟩


omit [NumberField E] [StarRing E] in
theorem forall_step_iff (P Q : ℕ) (C : E → ℕ → ℕ → Prop) :
    (∀ (β : E) (P' Q' : ℕ), SelfDualLatticeComplements.Step β P Q P' Q' → C β P' Q') ↔
      (1 ≤ P → C 1 (P - 1) Q) ∧ (1 ≤ Q → C (-1) P (Q - 1)) := by
  constructor
  · intro h
    exact ⟨fun hP => h _ _ _ (Or.inl ⟨rfl, hP, rfl, rfl⟩),
      fun hQ => h _ _ _ (Or.inr ⟨rfl, hQ, rfl, rfl⟩)⟩
  · rintro ⟨h1, h2⟩ β P' Q' (⟨rfl, hP, rfl, rfl⟩ | ⟨rfl, hQ, rfl, rfl⟩)
    · exact h1 hP
    · exact h2 hQ

theorem conclusion_iff (W : HSpace E) (M P Q : ℕ) :
    ((1 ≤ P → ∃ x : W.V, W.hD x x = 1 ∧ UnitVectorOrthogonal.HasComplement W x (M - 1) (P - 1) Q) ∧
      (1 ≤ Q → ∃ x : W.V, W.hD x x = -1 ∧ UnitVectorOrthogonal.HasComplement W x (M - 1) P (Q - 1))) ↔
    ∀ (β : E) (P' Q' : ℕ), SelfDualLatticeComplements.Step β P Q P' Q' →
      ∃ x : W.V, W.hD x x = β ∧ SelfDualLatticeComplements.HasComplement W x (M - 1) P' Q' := by
  rw [forall_step_iff P Q
    (fun β P' Q' => ∃ x : W.V, W.hD x x = β ∧ SelfDualLatticeComplements.HasComplement W x (M - 1) P' Q')]
  simp only [hasComplement_iff]

theorem over_iff : UnitVectorOrthogonal.UnitVectorPerpOver E ↔ SelfDualLatticeComplements.ExistsPerpOver E := by
  refine forall_congr' fun W => forall_congr' fun M => forall_congr' fun P =>
    forall_congr' fun Q => imp_congr (ofKind_iff W M P Q) (imp_congr Iff.rfl ?_)
  exact conclusion_iff W M P Q

end General

theorem unitVectorPerp_iff (D : D7) : UnitVectorOrthogonal.UnitVectorPerp D ↔ SelfDualLatticeComplements.UnitVectorPerp D :=
  @over_iff D.host.E _ _ D.host.cmStar

end GlobalTheory.UnitVectorPerpCompare

end
end

section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

theorem _root_.GlobalTheory.T.traceRowOperatorPower_dualWeyl_highestWeight : ∀ (N : ℕ) (ν : Fin N → ℕ), Antitone ν → ∀ k : ℕ, ∀ f ∈ dualWeyl ℚ N N ν, gel ℚ N N k f = hcVal ℚ (fun i => (ν i : ℚ)) k • f := by
  first | exact @GlobalTheory.Alc.gel_dualWeyl_rat | exact GlobalTheory.Alc.gel_dualWeyl_rat | (intros; apply GlobalTheory.Alc.gel_dualWeyl_rat <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.exists_measure_isCov1 : ∀ (F : Type) [Field F] [NumberField F], ∃ ν : Measure (AF F), IsCov1 ν := by
  first | exact @GlobalTheory.SWQ.exists_adeles_haarMeasure_covolume_one | exact GlobalTheory.SWQ.exists_adeles_haarMeasure_covolume_one | (intros; apply GlobalTheory.SWQ.exists_adeles_haarMeasure_covolume_one <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.integral_adelicVectors_character_orthogonality : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)) (a : Fin N → F), Ctx ψ lam ν a → ∀ D : Set (Fin N → AF F), IsAddFundamentalDomain (AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F)))) D (muV N ν) → muV N ν D = 1 → ∀ ξ : Fin N → F, ξ ≠ 0 → ∫ u in D, ψ (Bd (AF F) a u (rat ξ)) ∂(muV N ν) = 0 := by
  first | exact @GlobalTheory.SWQ.charOrth | exact GlobalTheory.SWQ.charOrth | (intros; apply GlobalTheory.SWQ.charOrth <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory

theorem _root_.GlobalTheory.scale_poly_comparison : ∀ eps c κ : ℝ, 0 < eps → 0 < κ → ∃ x0 : ℝ, ∀ s : _root_.Formalism.BasicNotions.Scale, s.eps = eps → x0 ≤ s.x → s.x ^ c ≤ Real.exp (s.x ^ (s.eps / 8)) ∧ s.x ^ c ≤ s.X' ^ κ ∧ s.x ^ c * s.X' ≤ s.b ^ κ ∧ s.b' * s.x ^ c ≤ s.b ∧ s.b ^ (1 - κ) * s.x ^ c ≤ s.b' ∧ (∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ s.x ^ (3 : ℝ) → s.b ^ (1 - κ) * s.x ^ c ≤ s.w'' n ∧ s.w'' n ≤ s.b' ∧ s.X'' n = s.x * n * s.X') ∧ Real.exp (c * s.x ^ (s.eps / 5) * Real.log s.x ^ 2) * s.x ^ c ≤ s.X' ^ κ := by
  intro eps c κ heps hκ
  obtain ⟨x1, h1⟩ := _root_.GlobalTheory.log_add_rpow_mul_log_pow_le_rpow 0 (eps / 8) c 0 1 0 le_rfl
    (by positivity) one_pos
  obtain ⟨x2, h2⟩ := _root_.GlobalTheory.log_add_rpow_mul_log_pow_le_rpow 0 (eps / 3) c 0 κ 0 le_rfl
    (by positivity) hκ
  obtain ⟨x3, h3⟩ := _root_.GlobalTheory.log_add_rpow_mul_log_pow_le_rpow (eps / 3) eps (c + 3) 1 κ 0
    (by positivity) (by linarith) hκ
  obtain ⟨x4, h4⟩ := _root_.GlobalTheory.log_add_rpow_mul_log_pow_le_rpow 0 (eps / 3) (c + 1) 0 1 0 le_rfl
    (by positivity) one_pos
  obtain ⟨x5, h5⟩ := _root_.GlobalTheory.log_add_rpow_mul_log_pow_le_rpow (eps / 5) (eps / 3) |c| |c| κ 2
    (by positivity) (by linarith) hκ
  refine ⟨max (max (max x1 x2) (max x3 x4)) x5, ?_⟩
  intro s hs hx
  subst hs
  have ht : 1 < s.x := s.one_lt_alt
  have ht0 : 0 < s.x := by linarith
  have hlog : 0 ≤ Real.log s.x := Real.log_nonneg ht.le
  have g1 := h1 s.x (le_trans (by simp) hx)
  have g2 := h2 s.x (le_trans (by simp) hx)
  have g3 := h3 s.x (le_trans (by simp) hx)
  have g4 := h4 s.x (le_trans (by simp) hx)
  have g5 := h5 s.x (le_trans (by simp) hx)
  simp only [Real.rpow_zero, pow_zero, mul_one, zero_mul, add_zero, one_mul] at g1 g2 g3 g4
  have hxc : s.x ^ c = Real.exp (Real.log s.x * c) := Real.rpow_def_of_pos ht0 c
  have hX' : s.X' = Real.exp (s.x ^ (s.eps / 3)) := by unfold _root_.Formalism.BasicNotions.Scale.X'; rfl
  have hb : s.b = Real.exp (s.x ^ s.eps) := by unfold _root_.Formalism.BasicNotions.Scale.b _root_.Formalism.BasicNotions.Scale.L; rfl
  have hb'def : s.b' = s.x * s.b / s.X' := by unfold _root_.Formalism.BasicNotions.Scale.b' _root_.Formalism.BasicNotions.Scale.a; rfl
  have hb' : s.b' = Real.exp (Real.log s.x + s.x ^ s.eps - s.x ^ (s.eps / 3)) := by
    rw [hb'def, hb, hX', Real.exp_sub, Real.exp_add, Real.exp_log ht0]
  have hw : ∀ n : ℕ, s.w'' n = s.b' / (s.x * n) := fun n => by unfold _root_.Formalism.BasicNotions.Scale.w''; rfl
  have hX'' : ∀ n : ℕ, s.X'' n = s.x * s.b / s.w'' n := fun n => by
    unfold _root_.Formalism.BasicNotions.Scale.X'' _root_.Formalism.BasicNotions.Scale.a; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hxc]
    exact Real.exp_le_exp.2 (by linarith)
  · rw [hxc, hX', ← Real.exp_mul]
    exact Real.exp_le_exp.2 (by linarith)
  · rw [hxc, hX', hb, ← Real.exp_mul, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith)
  · rw [hb', hxc, hb, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith)
  · rw [hb, ← Real.exp_mul, hxc, ← Real.exp_add, hb']
    exact Real.exp_le_exp.2 (by nlinarith)
  · intro n hn hnx
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    refine ⟨?_, ?_, ?_⟩
    · rw [hw, le_div_iff₀ (by positivity), hb, ← Real.exp_mul, hxc]
      calc Real.exp (s.x ^ s.eps * (1 - κ)) * Real.exp (Real.log s.x * c) * (s.x * n)
          ≤ Real.exp (s.x ^ s.eps * (1 - κ)) * Real.exp (Real.log s.x * c) *
              (s.x * s.x ^ (3 : ℝ)) := by gcongr
        _ = Real.exp (s.x ^ s.eps * (1 - κ) + Real.log s.x * c +
              (Real.log s.x + Real.log s.x * 3)) := by
            rw [Real.rpow_def_of_pos ht0 3, Real.exp_add, Real.exp_add, Real.exp_add,
              Real.exp_log ht0]
        _ ≤ s.b' := by
            rw [hb']
            exact Real.exp_le_exp.2 (by nlinarith)
    · rw [hw]
      have hpos : 0 ≤ s.b' := by rw [hb']; positivity
      exact div_le_self hpos (one_le_mul_of_one_le_of_one_le ht.le hn')
    · have hn0 : (n : ℝ) ≠ 0 := by positivity
      have hbne : s.b ≠ 0 := by rw [hb]; positivity
      have hX'ne : s.X' ≠ 0 := by rw [hX']; positivity
      rw [hX'', hw, hb'def]
      field_simp
  · have hY : 0 ≤ s.x ^ (s.eps / 5) * Real.log s.x ^ 2 := by positivity
    have hA : c * (s.x ^ (s.eps / 5) * Real.log s.x ^ 2) ≤
        |c| * (s.x ^ (s.eps / 5) * Real.log s.x ^ 2) :=
      mul_le_mul_of_nonneg_right (le_abs_self c) hY
    have hB : c * Real.log s.x ≤ |c| * Real.log s.x :=
      mul_le_mul_of_nonneg_right (le_abs_self c) hlog
    have habs : 0 ≤ |c| := abs_nonneg c
    rw [hxc, hX', ← Real.exp_mul, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith)

end GlobalTheory
end
