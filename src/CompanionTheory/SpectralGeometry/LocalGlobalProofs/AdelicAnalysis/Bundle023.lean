module

public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ArchimedeanPrimitiveVectorCompactRescale
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle003
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle071
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CapelliComplements.Bundle003
public import GroundTheory.GlobalFields.TateThesis.AdelicChar
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd

@[expose] public section

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.HermTop

theorem sigma_sigma {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

section

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem sigR_sigR {σ : E →ₐ[F] E} (h : ∀ x, σ (σ x) = x) (y : R ⊗[F] E) :
    sigR R σ (sigR R σ y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sigR, h]
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]

theorem sigR_inclR (σ : E →ₐ[F] E) (x : E) : sigR R σ (inclR R x) = inclR R (σ x) := by
  simp [sigR, inclR]

theorem gramR_mem {σ : E →ₐ[F] E} (h : ∀ x, σ (σ x) = x) {n M : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (hJ : ∀ i j, σ (J j i) = J i j) (X : Fin n → Fin M → R ⊗[F] E) :
    gramR R σ J X ∈ HermR R σ n := by
  intro a b

  simp only [gramR, hR, hform, JR, Matrix.map_apply, map_sum, map_mul, sigR_sigR R h, sigR_inclR, hJ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

variable [TopologicalSpace R] [IsTopologicalRing R]

theorem isModTop : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩

theorem isTopRing [Module.Finite F E] : IsTopologicalRing (R ⊗[F] E) :=
  haveI := isModTop (F := F) (E := E) R
  IsModuleTopology.isTopologicalRing R (R ⊗[F] E)

theorem exists_homeo [Module.Finite F E] :
    Nonempty ((R ⊗[F] E) ≃ₜ (Fin (Module.finrank F E) → R)) := by
  haveI := isModTop (F := F) (E := E) R
  haveI := isTopRing (F := F) (E := E) R
  let e := (Algebra.TensorProduct.basis R (Module.finBasis F E)).equivFun
  exact ⟨{ e.toEquiv with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }⟩

theorem continuous_sigR [Module.Finite F E] (σ : E →ₐ[F] E) : Continuous (sigR R σ) := by
  haveI := isModTop (F := F) (E := E) R
  haveI := isTopRing (F := F) (E := E) R
  exact IsModuleTopology.continuous_of_linearMap
    (Algebra.TensorProduct.map (AlgHom.id R R) σ).toLinearMap

end

theorem herm_top : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R], ∀ n : ℕ, LocallyCompactSpace (HermR R σ n) ∧ SecondCountableTopology (HermR R σ n) ∧ T2Space (HermR R σ n) ∧ BorelSpace (HermR R σ n) ∧ ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∃ g : (Fin n → Fin M → R ⊗[F] E) → HermR R σ n, Continuous g ∧ ∀ X, gramR R σ J X = (g X : Matrix (Fin n) (Fin n) (R ⊗[F] E)) := by
  intro F E _ _ _ _ _ σ hσ R _ _ _ _ _ _ _ _ _ n
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  haveI := isTopRing (F := F) (E := E) R
  obtain ⟨e⟩ := exists_homeo (F := F) (E := E) R
  haveI : LocallyCompactSpace (R ⊗[F] E) := e.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (R ⊗[F] E) := e.secondCountableTopology
  haveI : T2Space (R ⊗[F] E) := e.isEmbedding.t2Space
  have hs := continuous_sigR R σ
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (R ⊗[F] E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → R ⊗[F] E))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (R ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → R ⊗[F] E))
  have hc : IsClosed (HermR R σ n : Set (Matrix (Fin n) (Fin n) (R ⊗[F] E))) := by
    have : (HermR R σ n : Set (Matrix (Fin n) (Fin n) (R ⊗[F] E))) =
        ⋂ a, ⋂ b, {S | sigR R σ (S b a) = S a b} := by
      ext S
      simp only [Set.mem_iInter]
      rfl
    rw [this]
    refine isClosed_iInter fun a => isClosed_iInter fun b => isClosed_eq ?_ ?_
    · exact hs.comp (continuous_id.matrix_elem b a)
    · exact continuous_id.matrix_elem a b
  refine ⟨hc.locallyCompactSpace, ?_, inferInstance, ⟨rfl⟩, ?_⟩
  · exact TopologicalSpace.Subtype.secondCountableTopology _
  · intro M J hJ
    refine ⟨fun X => ⟨gramR R σ J X, gramR_mem R (sigma_sigma hσ) hJ.1 X⟩, ?_, fun _ => rfl⟩
    refine Continuous.subtype_mk ?_ _
    refine continuous_matrix fun a b => ?_
    simp only [gramR, hR, hform]
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    refine ((hs.comp ?_).mul continuous_const).mul ?_
    · exact (continuous_apply i).comp (continuous_apply a)
    · exact (continuous_apply j).comp (continuous_apply b)

end GlobalTheory.CompanionTheory.SW.HermTop
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.SdChange

theorem selfDual_twist : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) (χ : V → V → ℂ), SelfDual μ χ → ∀ (B : V ≃ₜ+ V),
    (∀ x y, χ x (B y) = χ (B x) y) → ∀ c : ℝ≥0, μ.map B = c • μ →
    SelfDual ((NNReal.sqrt c)⁻¹ • μ) (fun x y => χ x (B y)) := by
  intro V _ _ _ _ _ _ _ _ μ χ hsd B hsym c hc
  obtain ⟨hHaar, hinv⟩ := hsd
  have hemb : MeasurableEmbedding B := (B.toHomeomorph).measurableEmbedding
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h0 : μ.map B = 0 := by simpa using hc
    rw [Measure.map_eq_zero_iff hemb.measurable.aemeasurable] at h0
    exact (NeZero.ne μ) h0
  have hs0 : NNReal.sqrt c ≠ 0 := by simpa using hc0
  have hss : NNReal.sqrt c * NNReal.sqrt c = c := NNReal.mul_self_sqrt c
  generalize NNReal.sqrt c = s at hs0 hss ⊢
  refine ⟨Measure.IsAddHaarMeasure.nnreal_smul μ (inv_ne_zero hs0), ?_⟩
  intro Φ _ _ hint z
  let H : V → ℂ := fun y => ∫ x, Φ x * χ x y ∂μ
  have h1 : ∀ y, ∫ x, Φ x * χ x (B y) ∂(s⁻¹ • μ) = s⁻¹ • H (B y) :=
    fun y => integral_smul_nnreal_measure _ _
  simp only [h1] at hint ⊢
  have hsE : ((s⁻¹ : ℝ≥0) : ℝ≥0∞) ≠ 0 := by simpa using hs0
  have hint2 : Integrable (fun y => H (B y)) μ := by
    have h2 : Integrable (fun y => s⁻¹ • H (B y)) μ := by
      have h3 : s⁻¹ • μ = ((s⁻¹ : ℝ≥0) : ℝ≥0∞) • μ := rfl
      rw [h3] at hint
      exact (integrable_smul_measure hsE ENNReal.coe_ne_top).1 hint
    have h4 := h2.smul (s : ℝ)
    refine h4.congr (Filter.Eventually.of_forall fun y => ?_)
    have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast hs0
    have hsC : ((s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsR
    simp [NNReal.smul_def, smul_smul]
    rw [← mul_assoc, mul_inv_cancel₀ hsC, one_mul]
  have hintH : Integrable H μ := by
    have h5 : Integrable H (μ.map B) := (hemb.integrable_map_iff).2 hint2
    rw [hc] at h5
    have h6 : c • μ = (c : ℝ≥0∞) • μ := rfl
    rw [h6] at h5
    exact (integrable_smul_measure (by simpa using hc0) ENNReal.coe_ne_top).1 h5
  have hI := hinv Φ ‹_› ‹_› hintH z
  have h7 : ∫ w, H w * χ w z ∂(μ.map B) = c • ∫ w, H w * χ w z ∂μ := by
    rw [hc]; exact integral_smul_nnreal_measure _ _
  have h8 : ∫ w, H w * χ w z ∂(μ.map B) = ∫ y, H (B y) * χ (B y) z ∂μ :=
    hemb.integral_map _
  rw [integral_smul_nnreal_measure]
  have h9 : ∀ y, (s⁻¹ • H (B y)) * χ y (B z) = s⁻¹ • (H (B y) * χ (B y) z) := by
    intro y; rw [hsym, smul_mul_assoc]
  simp only [h9]
  have h10 : ∫ y, H (B y) * χ (B y) z ∂μ = c • Φ (-z) := by
    rw [← h8, h7]
    exact congrArg (c • ·) hI
  have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast hs0
  have hcR : (c : ℝ) = (s : ℝ) * s := by exact_mod_cast hss.symm
  simp only [NNReal.smul_def] at h10 ⊢
  rw [integral_smul, h10, smul_smul, smul_smul, hcR]
  have h11 : (((s⁻¹ : ℝ≥0) : ℝ)) = (s : ℝ)⁻¹ := by simp
  rw [h11]
  field_simp
  simp

end GlobalTheory.CompanionTheory.SW.SdChange
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW

theorem selfDual_map_of_comp {V V' : Type} [AddCommGroup V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V] [AddCommGroup V']
    [TopologicalSpace V'] [IsTopologicalAddGroup V'] [MeasurableSpace V'] [BorelSpace V']
    (e : V ≃ₜ+ V') (μ : Measure V) (χ : V' → V' → ℂ)
    (h : SelfDual μ (fun x y => χ (e x) (e y))) : SelfDual (μ.map e) χ := by
  obtain ⟨hH, hF⟩ := h
  let eM : V ≃ᵐ V' := e.toHomeomorph.toMeasurableEquiv
  have hcoe : (eM : V → V') = e := rfl
  have hint : ∀ g : V' → ℂ, ∫ y, g y ∂(μ.map e) = ∫ x, g (e x) ∂μ := fun g => by
    rw [← hcoe]; exact integral_map_equiv eM g
  refine ⟨e.isAddHaarMeasure_map μ, fun Φ hc hs hi z => ?_⟩
  have hinner : ∀ y : V, ∫ x, Φ x * χ x (e y) ∂(μ.map e)
      = ∫ x, (Φ ∘ e) x * χ (e x) (e y) ∂μ := fun y => hint _
  have hi' : Integrable (fun y => ∫ x, (Φ ∘ e) x * χ (e x) (e y) ∂μ) μ := by
    have h1 : Integrable ((fun y => ∫ x, Φ x * χ x y ∂(μ.map e)) ∘ eM) μ :=
      (eM.measurableEmbedding.integrable_map_iff).1 (by rw [hcoe]; exact hi)
    refine h1.congr (Filter.Eventually.of_forall fun y => ?_)
    exact hinner y
  have hcs : HasCompactSupport (Φ ∘ e) :=
    hs.comp_homeomorph e.toHomeomorph
  have key := hF (Φ ∘ e) (hc.comp e.continuous) hcs hi' (e.symm z)
  rw [hint]
  simp only [hinner]
  simpa using key

theorem selfDual_transport (V V' : Type) [AddCommGroup V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V] [AddCommGroup V']
    [TopologicalSpace V'] [IsTopologicalAddGroup V'] [MeasurableSpace V'] [BorelSpace V']
    (e : V ≃ₜ+ V') (μ : Measure V) (χ : V' → V' → ℂ) :
    SelfDual μ (fun x y => χ (e x) (e y)) ↔ SelfDual (μ.map e) χ := by
  refine ⟨selfDual_map_of_comp e μ χ, fun h => ?_⟩
  have h2 := selfDual_map_of_comp e.symm (μ.map e) (fun x y => χ (e x) (e y)) (by simpa using h)
  have hm : (μ.map e).map e.symm = μ := by
    have m1 : Measurable (e.symm : V' → V) := e.symm.continuous.measurable
    have m2 : Measurable (e : V → V') := e.continuous.measurable
    rw [Measure.map_map m1 m2]
    have : (e.symm : V' → V) ∘ e = id := by ext x; simp
    rw [this, Measure.map_id]
  rwa [hm] at h2

end GlobalTheory.CompanionTheory.SW
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.archimedean_primitive_vector_compact_rescale : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ), ∃ Ω : Set (Fin 1 → Fin M → Ainf F ⊗[F] E), IsCompact Ω ∧ ∀ y : Fin 1 → Fin M → Ainf F ⊗[F] E, (∃ z : Fin M → Ainf F ⊗[F] E, z ⬝ᵥ y 0 = 1) → ∃ (a : (Ainf F ⊗[F] E)ˣ) (z : Fin 1 → Fin M → Ainf F ⊗[F] E), (a : Ainf F ⊗[F] E) • y ∈ Ω ∧ z ∈ Ω ∧ z 0 ⬝ᵥ ((a : Ainf F ⊗[F] E) • y) 0 = 1 := by
  first | exact @GlobalTheory.CompanionTheory.SW.PrimInf.unimodular_mod_units_inf | exact GlobalTheory.CompanionTheory.SW.PrimInf.unimodular_mod_units_inf | (intros; apply GlobalTheory.CompanionTheory.SW.PrimInf.unimodular_mod_units_inf <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW

theorem rational_countable_discrete : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → Countable (HFinIn (AF F) σ J) ∧ ∃ U ∈ 𝓝 (1 : HA (AF F) σ J), ∀ h ∈ U, HA.mat (AF F) σ J h ∈ HFin (AF F) σ J → h = 1 := by
  intro F E _ _ _ _ _ σ hσ M J _
  have hfr : Module.finrank F E = 2 := hσ.2.2.1
  have : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  constructor
  · have : Countable E := (Module.finBasis ℚ E).equivFun.toEquiv.injective.countable
    have : Countable (Matrix (Fin M) (Fin M) E) :=
      inferInstanceAs (Countable (Fin M → Fin M → E))
    have : Countable (GL (Fin M) E) :=
      (Units.val_injective : Function.Injective
        (Units.val : GL (Fin M) E → Matrix (Fin M) (Fin M) E)).countable
    have hS : ((HFin (AF F) σ J : Subgroup (GL (Fin M) (AF F ⊗[F] E))) :
        Set (GL (Fin M) (AF F ⊗[F] E))).Countable := by
      unfold HFin
      rw [Subgroup.coe_map]
      exact (Set.to_countable _).image _
    have := hS.to_subtype
    let f : HFinIn (AF F) σ J → (HFin (AF F) σ J : Subgroup (GL (Fin M) (AF F ⊗[F] E))) :=
      fun g => ⟨g.1.1, Subgroup.mem_subgroupOf.1 g.2⟩
    have hf : Function.Injective f := by
      intro x y h
      have h' : (f x).1 = (f y).1 := by rw [h]
      exact Subtype.ext (Subtype.ext h')
    exact hf.countable
  · obtain ⟨W, hW, hWp⟩ := GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero F
    have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
    let b := Module.finBasis F E
    let B := Algebra.TensorProduct.basis (AF F) b
    have hc : ∀ k, Continuous (B.coord k) := fun k => IsModuleTopology.continuous_of_linearMap _
    let m : HA (AF F) σ J → Matrix (Fin M) (Fin M) (AF F ⊗[F] E) :=
      fun h => ((HA.mat (AF F) σ J h : GL (Fin M) (AF F ⊗[F] E)) :
        Matrix (Fin M) (Fin M) (AF F ⊗[F] E))
    have hm : Continuous m := Units.continuous_val.comp continuous_subtype_val
    have hm1 : m 1 = 1 := rfl
    let e : HA (AF F) σ J → Fin M → Fin M → _ → AF F := fun h i j k =>
      B.coord k (m h i j) - B.coord k ((1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j)
    refine ⟨⋂ i, ⋂ j, ⋂ k, (fun h => e h i j k) ⁻¹' W,
      Filter.iInter_mem.2 fun i => Filter.iInter_mem.2 fun j => Filter.iInter_mem.2 fun k => ?_, ?_⟩
    · have hce : Continuous fun h => e h i j k :=
        ((hc k).comp (hm.matrix_elem i j)).sub continuous_const
      refine hce.continuousAt.preimage_mem_nhds ?_
      have : e 1 i j k = 0 := by
        show B.coord k (m 1 i j) - _ = 0
        rw [hm1, sub_self]
      rw [this]; exact hW
    · intro h hU hh
      obtain ⟨γ, -, hγ⟩ := Subgroup.mem_map.1 hh
      have hent : ∀ i j, m h i j = inclR (F := F) (AF F) ((γ : Matrix (Fin M) (Fin M) E) i j) := by
        intro i j
        show ((HA.mat (AF F) σ J h : GL (Fin M) (AF F ⊗[F] E)) :
          Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j = _
        rw [← hγ]
        rfl
      have hco : ∀ (x : E) k, B.coord k (inclR (F := F) (AF F) x) =
          algebraMap F (AF F) (b.repr x k) := by
        intro x k
        show B.repr ((1 : AF F) ⊗ₜ[F] x) k = _
        rw [Algebra.TensorProduct.basis_repr_tmul]
        simp
      have hone : ∀ i j, (1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j =
          inclR (F := F) (AF F) ((1 : Matrix (Fin M) (Fin M) E) i j) := by
        intro i j
        by_cases hij : i = j
        · subst hij; simp
        · simp [Matrix.one_apply_ne hij]
      have hγ1 : (γ : Matrix (Fin M) (Fin M) E) = 1 := by
        ext i j
        refine b.repr.injective (Finsupp.ext fun k => ?_)
        have hk : e h i j k ∈ W := by
          have := Set.mem_iInter.1 (Set.mem_iInter.1 (Set.mem_iInter.1 hU i) j) k
          exact this
        have hk' : algebraMap F (AF F)
            (b.repr ((γ : Matrix (Fin M) (Fin M) E) i j) k -
              b.repr ((1 : Matrix (Fin M) (Fin M) E) i j) k) ∈ W := by
          rw [map_sub, ← hco, ← hco, ← hent, ← hone]
          exact hk
        exact sub_eq_zero.1 (hWp _ hk')
      have hγ2 : γ = 1 := Units.ext hγ1
      have hfin : HA.mat (AF F) σ J h = 1 := by
        rw [← hγ, hγ2, map_one]
      exact Subtype.ext hfin

end GlobalTheory.CompanionTheory.SW
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.AlgDiag

theorem diag_hermitian : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E), IsHermND σ T → ∃ (g : GL (Fin n) E) (D : Fin n → Fˣ), cT (σ : E →+* E) (g : Matrix (Fin n) (Fin n) E) * T * g = Matrix.diagonal fun i => algebraMap F E (D i : F) :=
  _root_.UpperTheory.Reformulated.B.Gka4.diag_hermitian

end GlobalTheory.CompanionTheory.SW.AlgDiag
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.HermRep

section Fixed

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}

theorem sig_sig (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem exists_of_sig_fixed (h : IsCMExt F E σ) {x : E} (hx : σ x = x) :
    ∃ t : F, algebraMap F E t = x :=
  _root_.Bl.EqIdOfFixed.goal1 h hx

end Fixed

section Form

variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (T : Matrix (Fin M) (Fin M) E)

theorem hE_add_left (x x' y : Fin M → E) :
    hE σ T (x + x') y = hE σ T x y + hE σ T x' y := by
  simp only [hE, HeckeCharacterZeroLocus.SiegelWeilU.hform, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem hE_add_right (x y y' : Fin M → E) :
    hE σ T x (y + y') = hE σ T x y + hE σ T x y' := by
  simp only [hE, HeckeCharacterZeroLocus.SiegelWeilU.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hE_single (i j : Fin M) (a b : E) :
    hE σ T (Pi.single i a) (Pi.single j b) = σ a * T i j * b := by
  simp only [hE, HeckeCharacterZeroLocus.SiegelWeilU.hform]
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
  · simp
  · intro k _ hk; simp [Pi.single_eq_of_ne hk]
  · simp
  · intro k _ hk; simp [Pi.single_eq_of_ne hk]
  · simp

end Form

theorem exists_repr : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (T : Matrix (Fin (n + 1)) (Fin (n + 1)) E), IsHermND σ T → ∃ (t : F) (x : Fin (n + 1) → E), t ≠ 0 ∧ hE σ T x x = algebraMap F E t := by
  intro F E _ _ _ _ _ σ hσ n T hT
  obtain ⟨hH, hdet⟩ := hT
  by_cases hd : ∃ i, T i i ≠ 0
  · obtain ⟨i, hi⟩ := hd
    obtain ⟨t, ht⟩ := exists_of_sig_fixed hσ (hH i i)
    refine ⟨t, Pi.single i 1, ?_, ?_⟩
    · rintro rfl
      exact hi (by rw [← ht, map_zero])
    · rw [hE_single, ht]; simp
  · push_neg at hd
    obtain ⟨i, j, hij⟩ : ∃ i j, T i j ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hdet (by rw [show T = 0 from Matrix.ext hc, Matrix.det_zero])
    refine ⟨2, Pi.single i (σ (T i j)⁻¹) + Pi.single j 1, two_ne_zero, ?_⟩
    have hji : T j i = σ (T i j) := (hH j i).symm
    have hs : σ (σ (T i j)⁻¹) = (T i j)⁻¹ := sig_sig hσ _
    rw [hE_add_left, hE_add_right, hE_add_right, hE_single, hE_single, hE_single, hE_single,
      hd i, hd j, hs, hji, map_one, map_ofNat, map_inv₀]
    have h1 : σ (T i j) ≠ 0 := (map_ne_zero _).2 hij
    field_simp
    ring

end GlobalTheory.CompanionTheory.SW.HermRep
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.CharEx

theorem exists_isCharAF : ∀ (F : Type) [Field F] [NumberField F], ∃ ψ, IsCharAF F ψ := by
  intro F _ _
  refine ⟨Circle.coeHom.compAddChar (GroundTheory.Global.adelicChar F), ?_, ?_, ?_, ?_⟩
  · exact continuous_subtype_val.comp (GroundTheory.Global.continuous_adelicChar (K := F))
  · intro x
    exact Circle.norm_coe _
  · intro a
    show ((GroundTheory.Global.adelicChar F _ : Circle) : ℂ) = 1
    rw [GroundTheory.Global.adelicChar_algebraMap]
    rfl
  · by_contra h
    push Not at h
    apply GroundTheory.Global.adelicChar_ne_one (K := F)
    ext x
    exact h x

end GlobalTheory.CompanionTheory.SW.CharEx
end
