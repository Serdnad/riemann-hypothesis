module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle018
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle022
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle034
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle007
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import GroundTheory.GlobalFields.Bundle001
import Mathlib.Algebra.Order.Archimedean.Real.Hom
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
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd

@[expose] public section

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂.Coord

theorem schurM_mem {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) (hinv : ∀ y : R ⊗[F] E, sigR R σ (sigR R σ y) = y) {n : ℕ} (t : F) (a : R → Rˣ)
    (S : HermR R σ (n + 1)) :
    schurM R σ t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ HermR R σ n := by
  intro i j
  have hS := S.2 i.succ j.succ
  have ht : sigR R σ (inclR R (algebraMap F E t)) = inclR R (algebraMap F E t) := by
    simp [sigR, inclR]
  simp only [schurM, map_sub, map_mul, hinv, ht]
  rw [hS]
  ring

theorem coords : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → Continuous (fun S : HermR R σ (n + 1) => s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) ∧ ContinuousOn (fun S : HermR R σ (n + 1) => (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))))) {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} ∧ ContinuousOn (fun S : HermR R σ (n + 1) => cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} ∧ ContinuousOn (fun S : HermR R σ (n + 1) => schur R σ t a S) {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} ∧ IsOpen (Bset R σ t a B₀ : Set (HermR R σ (n + 1))) := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D
  obtain ⟨hTR, hLC, hSC, hT2, hAr, hRed, hUR, -⟩ := D.hR
  have hK := GlobalTheory.T.tensor_locally_compact_ring F E σ D.hCM R
  obtain ⟨hKR, -, -, -, hsig, htr, -⟩ := hK
  have hinv := (GlobalTheory.CompanionTheory.SW.KAlg.algebra_tensor_invol F E σ D.hCM R).2.2.2.1
  have hopenU := GlobalTheory.T.units_open_embedding_local_tensor F E σ D.hCM R D.hR

  have hs0 : Continuous (fun S : HermR R σ (n + 1) =>
      s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) := by
    unfold s0
    have h1 : Continuous (fun S : HermR R σ (n + 1) =>
        (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) 0 0) :=
      (continuous_apply_apply 0 0).comp continuous_subtype_val
    exact continuous_const.mul (htr.comp h1)
  have hA : IsOpen {S : HermR R σ (n + 1) |
      s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} := D.hB₀.preimage hs0
  have ha : ContinuousOn (fun S : HermR R σ (n + 1) =>
      a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))))
      {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} :=
    D.hac.comp hs0.continuousOn (fun S hS => hS)

  have hleft : Continuous (fun r : R => r ⊗ₜ[F] (1 : E)) := by
    have : (fun r : R => r ⊗ₜ[F] (1 : E)) = fun r : R => r • (1 : R ⊗[F] E) := by
      funext r
      simp [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul']
    rw [this]
    exact (continuous_id (X := R)).smul (continuous_const (y := (1 : R ⊗[F] E)))
  have hc : ContinuousOn (fun S : HermR R σ (n + 1) =>
      cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))
      {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} := by
    refine continuousOn_pi.2 fun j => ?_
    have hent : Continuous (fun S : HermR R σ (n + 1) =>
        (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) 0 j.succ) :=
      (continuous_apply_apply 0 j.succ).comp continuous_subtype_val
    have hu : ContinuousOn (fun S : HermR R σ (n + 1) =>
        ((((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))))⁻¹ : Rˣ) : R)))
        {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} :=
      (Units.continuous_val (M := R)).comp_continuousOn ha.inv
    have hfac : (fun S : HermR R σ (n + 1) =>
        cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) j) =
        fun S : HermR R σ (n + 1) =>
        (((((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))))⁻¹ : Rˣ) : R) ⊗ₜ[F] (1 : E)) *
          ((1 : R) ⊗ₜ[F] (algebraMap F E t⁻¹))) *
          (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) 0 j.succ := by
      funext S
      simp [cvec, Algebra.TensorProduct.tmul_mul_tmul]
    rw [hfac]
    exact ((hleft.comp_continuousOn hu).mul continuousOn_const).mul hent.continuousOn

  have hM : ContinuousOn (fun S : HermR R σ (n + 1) =>
      schurM R σ t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))
      {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} := by
    refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => ?_
    have hent : Continuous (fun S : HermR R σ (n + 1) =>
        (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) i.succ j.succ) :=
      (continuous_apply_apply i.succ j.succ).comp continuous_subtype_val
    have hci := (continuous_apply i).comp_continuousOn hc
    have hcj := (continuous_apply j).comp_continuousOn hc
    exact hent.continuousOn.sub (((hsig.comp_continuousOn hci).mul continuousOn_const).mul hcj)
  have hsc : ∀ S : HermR R σ (n + 1),
      (schur R σ t a S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) =
        schurM R σ t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) :=
    fun S => schur_coe R σ t a S (schurM_mem R σ hinv t a S)
  have hcoe : ContinuousOn (fun S : HermR R σ (n + 1) =>
      (schur R σ t a S : Matrix (Fin n) (Fin n) (R ⊗[F] E)))
      {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} := by
    simpa only [hsc] using hM
  have hschur : ContinuousOn (fun S : HermR R σ (n + 1) => schur R σ t a S)
      {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} :=
    (Topology.IsInducing.subtypeVal.continuousOn_iff).2 hcoe
  refine ⟨hs0, ha, hc, hschur, ?_⟩

  have hdet : ContinuousOn (fun S : HermR R σ (n + 1) =>
      (schur R σ t a S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det)
      {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} :=
    (continuous_id.matrix_det).comp_continuousOn hcoe
  have hU : IsOpen {y : R ⊗[F] E | IsUnit y} := by
    have : {y : R ⊗[F] E | IsUnit y} = Set.range (Units.val : (R ⊗[F] E)ˣ → R ⊗[F] E) := by
      ext y; simp [IsUnit]
    rw [this]
    exact hopenU.isOpen_range
  have := hdet.isOpen_inter_preimage hA hU
  exact this

end GlobalTheory.CompanionTheory.SW.PiLocalization₂.Coord
end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.LatCpt

theorem latV_compact_open : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (v : HeightOneSpectrum (𝓞 F)), IsCompact (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) ∧ IsOpen (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) := by
  intro F E _ _ _ _ _ σ hCM d b n M v
  haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  haveI : LocallyCompactSpace (Fv F v) := inferInstance
  haveI : SecondCountableTopology (Fv F v) := inferInstance
  haveI : T2Space (Fv F v) := inferInstance
  haveI : IsTopologicalRing (Fv F v) := inferInstance
  obtain ⟨-, -, -, -, -, -, hH, -, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Fv F v)
  have hcoord := hH d b
  let H : (Fin n → Fin M → Fv F v ⊗[F] E) ≃ₜ (Fin n → Fin M → Fin d → Fv F v) :=
    Homeomorph.piCongrRight fun _ => Homeomorph.piCongrRight fun _ => hcoord.homeomorph
  let O : Set (Fv F v) := (v.adicCompletionIntegers F : Set (Fv F v))
  have hOc : IsCompact O := GroundTheory.Global.isCompact_adicCompletionIntegers v
  have hOo : IsOpen O := Valued.isOpen_valuationSubring _
  let P : Set (Fin n → Fin M → Fin d → Fv F v) :=
    Set.univ.pi fun _ => Set.univ.pi fun _ => Set.univ.pi fun _ => O
  have hE : (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) = H ⁻¹' P := by
    ext Y
    simp only [latV, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_univ_pi, P, O, SetLike.mem_coe]
    rfl
  have hPc : IsCompact P :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hOc
  have hPo : IsOpen P :=
    isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ =>
      isOpen_set_pi Set.finite_univ fun _ _ => hOo
  rw [hE]
  exact ⟨H.isCompact_preimage.2 hPc, hPo.preimage H.continuous⟩

end GlobalTheory.CompanionTheory.SW.LatCpt
end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.AdeleTop

theorem t2Space_finiteAdeleRing_of_numberField (F : Type) [Field F] [NumberField F] : T2Space (Af F) :=
  inferInstanceAs (T2Space (RestrictedProduct
    (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite))

theorem t2Space_infiniteAdeleRing_of_numberField_field (F : Type) [Field F] [NumberField F] : T2Space (InfiniteAdeleRing F) :=
  inferInstanceAs (T2Space ((v : InfinitePlace F) → v.Completion))

theorem adele_top : ∀ (F : Type) [Field F] [NumberField F],
    (LocallyCompactSpace (AF F) ∧ SecondCountableTopology (AF F) ∧ T2Space (AF F)) ∧
    (LocallyCompactSpace (Af F) ∧ SecondCountableTopology (Af F) ∧ T2Space (Af F)) := by
  intro F _ _
  refine ⟨⟨GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F,
    GlobalTheory.AdelicUnitaryTop.secondCountable_adele F, ?_⟩,
    GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F,
    GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F, t2Space_finiteAdeleRing_of_numberField F⟩
  haveI : T2Space (FiniteAdeleRing (𝓞 F) F) := t2Space_finiteAdeleRing_of_numberField F
  haveI := t2Space_infiniteAdeleRing_of_numberField_field F
  exact inferInstanceAs (T2Space (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

end GlobalTheory.CompanionTheory.AdeleTop
end

section

open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.AdelicFlow

theorem map_eq_smul_of_scale {V W G : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    [AddCommGroup W] [TopologicalSpace W] [IsTopologicalAddGroup W] [LocallyCompactSpace W]
    [SecondCountableTopology W] [MeasurableSpace W] [BorelSpace W]
    [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [MeasurableSpace G]
    [BorelSpace G]
    (Φ : G ≃ₜ+ V × W) (φ : G → G) (t : ℝ) (ht : t ≠ 0)
    (h : ∀ x, Φ (φ x) = (t • (Φ x).1, (Φ x).2))
    (μ : Measure G) [μ.IsAddHaarMeasure] :
    μ.map φ = ENNReal.ofReal |(t ^ Module.finrank ℝ V)⁻¹| • μ := by
  set k := ENNReal.ofReal |(t ^ Module.finrank ℝ V)⁻¹| with hk
  have hΦ : Measurable Φ := Φ.continuous.measurable
  have hΦs : Measurable Φ.symm := Φ.symm.continuous.measurable
  let ν : Measure V := Measure.addHaar
  let ρ : Measure W := Measure.addHaar
  let ψ : V × W → V × W := Prod.map (fun v => t • v) id
  have hψ : Measurable ψ := (measurable_const_smul t).prodMap measurable_id
  haveI : (μ.map Φ).IsAddHaarMeasure := Φ.isAddHaarMeasure_map μ
  have hc := Measure.isAddLeftInvariant_eq_smul (μ.map Φ) (ν.prod ρ)
  set c := Measure.addHaarScalarFactor (μ.map Φ) (ν.prod ρ) with hcdef
  have hπ : (μ.map Φ).map ψ = k • μ.map Φ := by
    have h1 : (ν.prod ρ).map ψ = k • ν.prod ρ := by
      have := Measure.map_prod_map ν ρ (f := fun v : V => t • v) (g := (id : W → W))
        (measurable_const_smul t) measurable_id
      rw [show (ν.prod ρ).map ψ = (ν.map fun v => t • v).prod (ρ.map id) from this.symm,
        Measure.map_addHaar_smul ν ht, Measure.map_id, Measure.prod_smul_left]
    rw [hc, Measure.map_smul c hψ.aemeasurable, h1, smul_comm]
  have hφ : φ = Φ.symm ∘ ψ ∘ Φ := by
    funext x
    apply Φ.injective
    simp [h]
    rfl
  have hμ : (μ.map Φ).map Φ.symm = μ := by
    rw [Measure.map_map hΦs hΦ]
    simp
  calc μ.map φ = ((μ.map Φ).map ψ).map Φ.symm := by
        rw [Measure.map_map hΦs hψ, Measure.map_map (hΦs.comp hψ) hΦ, hφ]; rfl
    _ = k • μ := by rw [hπ, Measure.map_smul k hΦs.aemeasurable, hμ]

section Adelic

variable (F : Type) [Field F] [NumberField F]

noncomputable def coords [IsTotallyReal F] (ι : Type) :
    (ι → AdeleRing (𝓞 F) F) ≃ₜ+
      (ι → InfinitePlace F → ℝ) × (ι → FiniteAdeleRing (𝓞 F) F) where
  toFun x := (fun i w => InfinitePlace.Completion.ringEquivRealOfIsReal
      (IsTotallyReal.isReal w) ((x i).1 w), fun i => (x i).2)
  invFun p := fun i => (show AdeleRing (𝓞 F) F from
    (fun w => (InfinitePlace.Completion.ringEquivRealOfIsReal
      (IsTotallyReal.isReal w)).symm (p.1 i w), p.2 i))
  left_inv x := by
    funext i
    refine Prod.ext ?_ rfl
    funext w
    exact RingEquiv.symm_apply_apply _ _
  right_inv p := by
    refine Prod.ext ?_ rfl
    funext i w
    exact RingEquiv.apply_symm_apply _ _
  map_add' x y := by
    refine Prod.ext ?_ rfl
    funext i w
    exact map_add (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)) _ _
  continuous_toFun := by
    refine Continuous.prodMk (continuous_pi fun i => continuous_pi fun w => ?_)
      (continuous_pi fun i => ?_)
    · exact (InfinitePlace.Completion.isometryEquivRealOfIsReal
        (IsTotallyReal.isReal w)).continuous.comp
        ((continuous_apply w).comp (continuous_fst.comp (continuous_apply i)))
    · exact continuous_snd.comp (continuous_apply i)
  continuous_invFun := by
    refine continuous_pi fun i => Continuous.prodMk (continuous_pi fun w => ?_) ?_
    · exact (InfinitePlace.Completion.isometryEquivRealOfIsReal
        (IsTotallyReal.isReal w)).symm.continuous.comp
        ((continuous_apply w).comp ((continuous_apply i).comp continuous_fst))
    · exact (continuous_apply i).comp continuous_snd

theorem coord_theta [IsTotallyReal F] (θ : ℝ →+* InfiniteAdeleRing F) (t : ℝ)
    (w : InfinitePlace F) :
    InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w) (θ t w) = t := by
  have h : ((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w) :
      w.Completion →+* ℝ).comp ((Pi.evalRingHom (fun v : InfinitePlace F => v.Completion) w).comp θ))
      = RingHom.id ℝ := Subsingleton.elim _ _
  exact DFunLike.congr_fun h t

theorem card_places [IsTotallyReal F] :
    Fintype.card (InfinitePlace F) = Module.finrank ℚ F := by
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyReal.nrComplexPlaces_eq_zero, add_zero, IsTotallyReal.finrank]

end Adelic

theorem map_scalar : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F →
    ∀ θ : ℝ →+* InfiniteAdeleRing F, Continuous θ →
    ∀ [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)] (ι : Type)
      [Fintype ι] (μ : Measure (ι → AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure] (t : ℝ), 0 < t →
      μ.map (fun x i => (show AdeleRing (𝓞 F) F from (θ t, 1)) * x i) =
        ENNReal.ofReal ((t ^ (Module.finrank ℚ F * Fintype.card ι))⁻¹) • μ := by
  intro F _ _ hF θ _ _ _ ι _ μ _ t ht
  haveI := hF
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  letI : MeasurableSpace (FiniteAdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  have key := map_eq_smul_of_scale (coords F ι)
    (fun x i => (show AdeleRing (𝓞 F) F from (θ t, 1)) * x i) t ht.ne' ?_ μ
  · have hd : Module.finrank ℝ (ι → InfinitePlace F → ℝ) =
        Module.finrank ℚ F * Fintype.card ι := by
      rw [Module.finrank_pi_fintype]
      simp [Module.finrank_fintype_fun_eq_card, card_places F, mul_comm]
    rw [key, hd, abs_of_pos (inv_pos.2 (pow_pos ht _))]
  · intro x
    refine Prod.ext ?_ ?_
    · funext i w
      show InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)
        (θ t w * (x i).1 w) = t * _
      rw [map_mul, coord_theta]
      rfl
    · funext i
      exact one_mul _

end GlobalTheory.CompanionTheory.AdelicFlow
end
