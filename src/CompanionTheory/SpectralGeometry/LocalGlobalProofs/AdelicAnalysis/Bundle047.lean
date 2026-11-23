module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle038
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle040
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle007
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle008
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle042
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle043
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle044
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle018
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle045
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

theorem _root_.GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties : ∀ (F : Type) [Field F] [NumberField F], LocallyCompactSpace (A F) ∧ SecondCountableTopology (A F) ∧ T2Space (A F) ∧ IsCompact (Oh F) ∧ IsOpen (Oh F) ∧ DenseRange (algebraMap F (A F)) ∧ (∀ b : F, algebraMap F (A F) b ∈ Oh F ↔ ∃ r : 𝓞 F, (r : F) = b) ∧ (∀ U ∈ 𝓝 (0 : A F), ∃ N : ℕ, 0 < N ∧ ∀ x ∈ Oh F, (N : A F) * x ∈ U) ∧ (∀ K : Set (A F), IsCompact K → ∃ N : ℕ, 0 < N ∧ ∀ x ∈ K, (N : A F) * x ∈ Oh F) ∧ ∀ N : ℕ, 0 < N → IsOpen {x : A F | ∃ y ∈ Oh F, x = (N : A F) * y} := by
  first | exact @GlobalTheory.CompanionTheory.SW.Core.AfTop.finiteAdele_topology | exact GlobalTheory.CompanionTheory.SW.Core.AfTop.finiteAdele_topology | (intros; apply GlobalTheory.CompanionTheory.SW.Core.AfTop.finiteAdele_topology <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.FChi

theorem continuous_norm_tensor {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsTopologicalRing (R ⊗[F] E)] :
    Continuous (Algebra.norm R : R ⊗[F] E → R) := by
  classical
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  let B := Algebra.TensorProduct.basis R (Module.finBasis F E)
  have h : (fun y : R ⊗[F] E => Algebra.norm R y) = fun y => (Algebra.leftMulMatrix B y).det := by
    funext y; exact Algebra.norm_eq_matrix_det B y
  change Continuous (fun y : R ⊗[F] E => Algebra.norm R y)
  rw [h]
  refine Continuous.matrix_det ?_
  refine continuous_matrix fun i j => ?_
  let L : (R ⊗[F] E) →ₗ[R] R :=
    (Matrix.entryLinearMap R R i j) ∘ₗ (Algebra.leftMulMatrix B).toLinearMap
  exact IsModuleTopology.continuous_of_linearMap L

theorem norm_tmul_one {F E : Type} [Field F] [Field E] [Algebra F E]
    (h2 : Module.finrank F E = 2) (R : Type) [CommRing R] [Nontrivial R] [Algebra F R] (r : R) :
    Algebra.norm R (r ⊗ₜ[F] (1 : E)) = r ^ 2 := by
  classical
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  have e : r ⊗ₜ[F] (1 : E) = algebraMap R (R ⊗[F] E) r := by
    simp [Algebra.TensorProduct.algebraMap_apply]
  rw [e, Algebra.norm_algebraMap, Module.finrank_baseChange, h2]

theorem map_scale_adele {F : Type} [Field F] [NumberField F] (hF : IsTotallyReal F)
    (θ : ℝ →+* Ainf F) (hθ : Continuous θ) (μA : Measure (AF F)) (hA : μA.IsAddHaarMeasure)
    (t : ℝ) (ht : 0 < t) :
    μA.map (fun y => pairA F (θ t) 1 * y) =
      ENNReal.ofReal ((t ^ Module.finrank ℚ F)⁻¹) • μA := by
  obtain ⟨⟨lcA, scA, t2A⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  let μ' : Measure (Unit → AF F) := Measure.pi fun _ => μA
  haveI : μ'.IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have h := GlobalTheory.T.adelic_haar_scaling_by_real_idele F hF θ hθ Unit μ' t ht
  have he : μ'.map (MeasurableEquiv.funUnique Unit (AF F)) = μA :=
    (measurePreserving_funUnique μA Unit).map_eq
  have hf : Measurable (fun y : AF F => pairA F (θ t) 1 * y) :=
    (continuous_const.mul continuous_id).measurable
  have hg : Measurable (fun (x : Unit → AF F) (i : Unit) =>
      (show AdeleRing (𝓞 F) F from (θ t, 1)) * x i) :=
    Measurable.of_eval fun i =>
      (continuous_const.mul (continuous_apply i)).measurable
  have hc : (fun y : AF F => pairA F (θ t) 1 * y) ∘ (MeasurableEquiv.funUnique Unit (AF F)) =
      (MeasurableEquiv.funUnique Unit (AF F)) ∘ (fun (x : Unit → AF F) (i : Unit) =>
        (show AdeleRing (𝓞 F) F from (θ t, 1)) * x i) := rfl
  have hEquiv : AEMeasurable (MeasurableEquiv.funUnique Unit (AF F)) μ' :=
    (MeasurableEquiv.measurable _).aemeasurable
  calc μA.map (fun y => pairA F (θ t) 1 * y)
      = (μ'.map (MeasurableEquiv.funUnique Unit (AF F))).map (fun y => pairA F (θ t) 1 * y) := by
        rw [he]
    _ = (μ'.map (fun (x : Unit → AF F) (i : Unit) =>
          (show AdeleRing (𝓞 F) F from (θ t, 1)) * x i)).map
          (MeasurableEquiv.funUnique Unit (AF F)) := by
        rw [Measure.map_map hf (MeasurableEquiv.measurable _),
          Measure.map_map (MeasurableEquiv.measurable _) hg, hc]
    _ = ENNReal.ofReal ((t ^ Module.finrank ℚ F)⁻¹) • μA := by
        rw [h, Measure.map_smul _ hEquiv, he]
        simp

theorem exists_modulus_chi : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ τ : Multiplicative ℝ →* (AF F ⊗[F] E)ˣ, IsFlow τ →
    ∀ (M : ℕ) (μW : Measure (Fin 1 → Fin M → AF F ⊗[F] E)) (μA : Measure (AF F)),
    μW.IsAddHaarMeasure → μA.IsAddHaarMeasure →
    ∃ χ : (AF F ⊗[F] E)ˣ →* ℝ≥0, Continuous χ ∧
      (∀ a : (AF F ⊗[F] E)ˣ, (μW.prod μA).map (fun p =>
        (sigR (AF F) σ (a : AF F ⊗[F] E) • p.1, Algebra.norm (AF F) (a : AF F ⊗[F] E) * p.2)) =
          χ a • μW.prod μA) ∧
      ∀ x : ℝ, (χ (τ (Multiplicative.ofAdd x)) : ℝ) =
        Real.exp (-(2 * Module.finrank ℚ F * (M + 1) * x)) := by
  intro F E _ _ _ _ _ σ hCM τ hτ M μW μA hW hA
  obtain ⟨⟨lcA, scA, t2A⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  obtain ⟨trK, lcK, scK, t2K, cSig, -, -, bor, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (AF F)
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  haveI : BorelSpace (Fin 1 → Fin M → AF F ⊗[F] E) := bor 1 M
  have h2 : Module.finrank F E = 2 := hCM.2.2.1
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  have cN : Continuous (Algebra.norm (AF F) : AF F ⊗[F] E → AF F) := continuous_norm_tensor (AF F)
  let a : (AF F ⊗[F] E)ˣ →
      ((Fin 1 → Fin M → AF F ⊗[F] E) × AF F) →+ ((Fin 1 → Fin M → AF F ⊗[F] E) × AF F) := fun t =>
    { toFun := fun p => (sigR (AF F) σ (t : AF F ⊗[F] E) • p.1,
        Algebra.norm (AF F) (t : AF F ⊗[F] E) * p.2)
      map_zero' := by simp
      map_add' := by intro p q; simp [smul_add, mul_add] }
  have ha : ∀ t p, a t p = (sigR (AF F) σ (t : AF F ⊗[F] E) • p.1,
      Algebra.norm (AF F) (t : AF F ⊗[F] E) * p.2) := fun _ _ => rfl
  haveI : LocallyCompactSpace (AF F ⊗[F] E)ˣ :=
    (Units.isClosedEmbedding_embedProduct (α := AF F ⊗[F] E)).locallyCompactSpace
  haveI : SecondCountableTopology (AF F ⊗[F] E)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := AF F ⊗[F] E)).symm.secondCountableTopology
  haveI : SecondCountableTopology (AF F ⊗[F] E)ˣ :=
    (Units.isEmbedding_embedProduct (M := AF F ⊗[F] E)).secondCountableTopology
  have hcont : Continuous fun p : (AF F ⊗[F] E)ˣ × ((Fin 1 → Fin M → AF F ⊗[F] E) × AF F) =>
      a p.1 p.2 := by
    have hv : Continuous fun p : (AF F ⊗[F] E)ˣ × ((Fin 1 → Fin M → AF F ⊗[F] E) × AF F) =>
        ((p.1 : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) := Units.continuous_val.comp continuous_fst
    refine Continuous.prodMk ?_ ?_
    · exact (cSig.comp hv).smul (continuous_fst.comp continuous_snd)
    · exact (cN.comp hv).mul (continuous_snd.comp continuous_snd)
  haveI : μW.IsAddHaarMeasure := hW
  haveI : μA.IsAddHaarMeasure := hA
  haveI : IsTopologicalAddGroup (Fin 1 → Fin M → AF F ⊗[F] E) := inferInstance
  haveI : LocallyCompactSpace (Fin 1 → Fin M → AF F ⊗[F] E) := inferInstance
  haveI : SecondCountableTopology (Fin 1 → Fin M → AF F ⊗[F] E) := inferInstance
  haveI : SigmaFinite μW := inferInstance
  haveI : SigmaFinite μA := inferInstance
  haveI : (μW.prod μA).IsAddHaarMeasure := inferInstance
  obtain ⟨χ, hχc, hχ⟩ := GlobalTheory.T.group_action_haar_scaling_continuous ((Fin 1 → Fin M → AF F ⊗[F] E) × AF F) (μW.prod μA)
    (AF F ⊗[F] E)ˣ a hcont continuous_inv
    (by intro y; rw [ha]; simp)
    (by intro s t y; simp only [ha, Units.val_mul, map_mul, smul_smul, mul_assoc])
  refine ⟨χ, hχc, hχ, ?_⟩
  intro x
  have hτ' := hτ
  obtain ⟨-, θ, hθ, hval⟩ := hτ
  have hu := hval x
  have hsig : sigR (AF F) σ ((τ (Multiplicative.ofAdd x) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) =
      ((τ (Multiplicative.ofAdd x) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) := by
    rw [hu]; simp [sigR]
  haveI : Nontrivial (Ainf F) := by
    obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
    unfold Ainf InfiniteAdeleRing
    exact Pi.nontrivial_at v
  haveI : Nontrivial (AF F) := inferInstanceAs (Nontrivial (Ainf F × Af F))
  have hnorm : Algebra.norm (AF F) ((τ (Multiplicative.ofAdd x) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) =
      pairA F (θ (Real.exp (2 * x))) 1 := by
    rw [hu, norm_tmul_one h2, sq]
    have e2 : Real.exp (2 * x) = Real.exp x * Real.exp x := by
      rw [← Real.exp_add]; congr 1; ring
    rw [e2, map_mul]
    change ((θ (Real.exp x) * θ (Real.exp x), (1 : Af F) * 1) : Ainf F × Af F) = (_, 1)
    rw [one_mul]
  have hWm := GlobalTheory.T.haar_scaling_under_flow F E σ hCM τ hτ' 1 M μW hW x
  have hAm := map_scale_adele hCM.1 θ hθ μA hA (Real.exp (2 * x)) (Real.exp_pos _)
  have mW : Measurable (fun X : Fin 1 → Fin M → AF F ⊗[F] E =>
      ((τ (Multiplicative.ofAdd x) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • X) :=
    (continuous_const_smul _).measurable
  have mA : Measurable (fun y : AF F => pairA F (θ (Real.exp (2 * x))) 1 * y) :=
    (continuous_const.mul continuous_id).measurable
  have hmap := Measure.map_prod_map μW μA mW mA
  rw [hWm, hAm, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul] at hmap
  have hfun : (a (τ (Multiplicative.ofAdd x)) : _ → _) = Prod.map
      (fun X : Fin 1 → Fin M → AF F ⊗[F] E =>
        ((τ (Multiplicative.ofAdd x) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • X)
      (fun y : AF F => pairA F (θ (Real.exp (2 * x))) 1 * y) := by
    funext p
    rw [ha, hsig, hnorm]
    rfl
  have hfin := hχ (τ (Multiplicative.ofAdd x))
  rw [hfun, ← hmap] at hfin
  obtain ⟨S, hS, hS0⟩ := exists_compact_mem_nhds (0 : (Fin 1 → Fin M → AF F ⊗[F] E) × AF F)
  have pos : (μW.prod μA) S ≠ 0 := (Measure.measure_pos_of_mem_nhds _ hS0).ne'
  have fin : (μW.prod μA) S ≠ ⊤ := hS.measure_lt_top.ne
  have hS1 := congrArg (fun m : Measure _ => m S) hfin
  simp only [Measure.smul_apply, smul_eq_mul, ENNReal.smul_def] at hS1
  have hS2 := (ENNReal.mul_left_inj pos fin).1 hS1
  have hS3 := congrArg ENNReal.toReal hS2
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le,
    ENNReal.toReal_ofReal (by positivity), ENNReal.coe_toReal] at hS3
  rw [← hS3, ← Real.exp_nat_mul, ← Real.exp_neg, ← Real.exp_add]
  congr 1
  push_cast
  ring

end GlobalTheory.CompanionTheory.SW.FChi
end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.AfBox

theorem eq_of_invariant_of_open {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ ν : Measure G) [ν.IsAddHaarMeasure] [μ.IsAddLeftInvariant] {C : Set G} (hC : IsOpen C)
    (h0 : (0 : G) ∈ C) (hμ : μ C = 1) (hν : ν C = 1) : μ = ν := by
  haveI : IsFiniteMeasureOnCompacts μ := by
    refine ⟨fun K hK => ?_⟩
    have hU : ∀ k : G, IsOpen ((fun x => -k + x) ⁻¹' C) := fun k =>
      hC.preimage (continuous_const.add continuous_id)
    obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover (fun k => (fun x => -k + x) ⁻¹' C)
      (fun k _ => (hU k).mem_nhds (by simpa using h0))
    have hm : ∀ k : G, μ ((fun x => -k + x) ⁻¹' C) = 1 := fun k => by
      rw [measure_preimage_add, hμ]
    calc μ K ≤ μ (⋃ k ∈ t, (fun x => -k + x) ⁻¹' C) := measure_mono ht
      _ ≤ ∑ k ∈ t, μ ((fun x => -k + x) ⁻¹' C) := measure_biUnion_finset_le _ _
      _ = t.card := by simp [hm]
      _ < ⊤ := by simp
  have h := Measure.isAddLeftInvariant_eq_smul μ ν
  have hc : Measure.addHaarScalarFactor μ ν = 1 := by
    have h2 : μ C = (Measure.addHaarScalarFactor μ ν • ν) C := by rw [← h]
    rw [Measure.smul_apply, hμ, hν] at h2
    simpa [ENNReal.smul_def, eq_comm] using h2
  rw [hc, one_smul] at h
  exact h

theorem map_restrict_invariant {G T : Type} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd G]
    [AddCommGroup T] [MeasurableSpace T] [MeasurableAdd T]
    (m : Measure G) [m.IsAddLeftInvariant] (H : AddSubgroup G) (hH : MeasurableSet (H : Set G))
    (ρ : G →+ T) (hρ : Measurable ρ) (hs : ∀ t, ∃ h ∈ H, ρ h = t) :
    ((m.restrict H).map ρ).IsAddLeftInvariant := by
  constructor
  intro g
  obtain ⟨h, hh, rfl⟩ := hs g
  have e : (m.restrict H).map (fun x => h + x) = m.restrict H := by
    have hp : (fun x => h + x) ⁻¹' (H : Set G) = H := by
      ext x
      simp [H.add_mem_cancel_left hh]
    have := Measure.restrict_map (μ := m) (measurable_const_add h) hH
    rw [map_add_left_eq_self, hp] at this
    exact this.symm
  rw [Measure.map_map (measurable_const_add _) hρ]
  have hc : (fun x => ρ h + x) ∘ ρ = ρ ∘ (fun x => h + x) := by
    ext x
    simp
  rw [hc, ← Measure.map_map hρ (measurable_const_add _), e]

theorem measure_inter_preimage {G T : Type} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd G]
    [AddCommGroup T] [TopologicalSpace T] [IsTopologicalAddGroup T] [LocallyCompactSpace T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T]
    (m : Measure G) [m.IsAddLeftInvariant] (H : AddSubgroup G) (hH : MeasurableSet (H : Set G))
    (ρ : G →+ T) (hρ : Measurable ρ) (hs : ∀ t, ∃ h ∈ H, ρ h = t)
    (ν : Measure T) [ν.IsAddHaarMeasure] {C : Set T} (hC : IsOpen C) (h0 : (0 : T) ∈ C)
    (hm : m ((H : Set G) ∩ ρ ⁻¹' C) = 1) (hν : ν C = 1) {B : Set T} (hB : MeasurableSet B) :
    m ((H : Set G) ∩ ρ ⁻¹' B) = ν B := by
  haveI := map_restrict_invariant m H hH ρ hρ hs
  have hmap : ∀ D : Set T, MeasurableSet D → ((m.restrict H).map ρ) D = m ((H : Set G) ∩ ρ ⁻¹' D) := by
    intro D hD
    rw [Measure.map_apply hρ hD, Measure.restrict_apply (hρ hD), Set.inter_comm]
  have he := eq_of_invariant_of_open ((m.restrict H).map ρ) ν hC h0
    (by rw [hmap C hC.measurableSet, hm]) hν
  rw [← he, hmap B hB]

variable {F : Type} [Field F] [NumberField F]

def offS (ι : Type) (S : Finset (HeightOneSpectrum (𝓞 F))) : AddSubgroup (ι → Af F) where
  carrier := {x | ∀ v, v ∉ S → ∀ i, evalV F v (x i) ∈ v.adicCompletionIntegers F}
  add_mem' := fun {a b} ha hb v hv i => by
    simpa using add_mem (ha v hv i) (hb v hv i)
  zero_mem' := fun v _ i => by simp
  neg_mem' := fun {a} ha v hv i => by
    simpa using neg_mem (ha v hv i)

def compS (ι : Type) (S : Finset (HeightOneSpectrum (𝓞 F))) :
    (ι → Af F) →+ ∀ v : S, ι → Fv F v.1 where
  toFun x := fun v i => evalV F v.1 (x i)
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

theorem continuous_compS (ι : Type) (S : Finset (HeightOneSpectrum (𝓞 F))) :
    Continuous (compS (F := F) ι S) :=
  continuous_pi fun v => continuous_pi fun i =>
    (RestrictedProduct.continuous_eval v.1).comp (continuous_apply i)


open Classical in
def liftS {S : Finset (HeightOneSpectrum (𝓞 F))} (t : ∀ v : S, Fv F v.1) : Af F :=
  ⟨fun w => if hw : w ∈ S then t ⟨w, hw⟩ else (0 : Fv F w), by
    filter_upwards [S.finite_toSet.compl_mem_cofinite] with w hw
    have : w ∉ S := by simpa using hw
    simp [this]⟩

open Classical in
theorem evalV_liftS_of_mem {S : Finset (HeightOneSpectrum (𝓞 F))} (t : ∀ v : S, Fv F v.1) (v : S) :
    evalV F v.1 (liftS t) = t v := by
  have : evalV F v.1 (liftS t) = dite (v.1 ∈ S) (fun hw => t ⟨v.1, hw⟩) (fun _ => (0 : Fv F v.1)) := rfl
  rw [this, dite_eq_left v.2]

open Classical in
theorem evalV_liftS_of_notMem {S : Finset (HeightOneSpectrum (𝓞 F))} (t : ∀ v : S, Fv F v.1)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) : evalV F v (liftS t) = 0 := by
  have : evalV F v (liftS t) = dite (v ∈ S) (fun hw => t ⟨v, hw⟩) (fun _ => (0 : Fv F v)) := rfl
  rw [this, dite_eq_right hv]

theorem exists_offS_compS (ι : Type) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (t : ∀ v : S, ι → Fv F v.1) : ∃ h ∈ offS (F := F) ι S, compS ι S h = t := by
  refine ⟨fun i => liftS fun v => t v i, fun v hv i => ?_, ?_⟩
  · rw [evalV_liftS_of_notMem _ hv]
    exact zero_mem (v.adicCompletionIntegers F)
  · funext v i
    exact evalV_liftS_of_mem (fun v => t v i) v

theorem isOpen_integral : IsOpen {x : Af F | ∀ v, x v ∈ v.adicCompletionIntegers F} :=
  RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring _)

theorem isOpen_offS (ι : Type) [Finite ι] (S : Finset (HeightOneSpectrum (𝓞 F))) :
    IsOpen (offS (F := F) ι S : Set (ι → Af F)) := by
  refine AddSubgroup.isOpen_of_mem_nhds _ (g := 0) ?_
  have ho : IsOpen (Set.pi Set.univ fun _ : ι => {x : Af F | ∀ v, x v ∈ v.adicCompletionIntegers F}) :=
    isOpen_set_pi Set.finite_univ fun _ _ => isOpen_integral
  refine Filter.mem_of_superset (ho.mem_nhds ?_) ?_
  · intro i _ v
    exact zero_mem (v.adicCompletionIntegers F)
  · intro x hx v _ i
    exact hx i (Set.mem_univ i) v

theorem pi_box : ∀ (F : Type) [Field F] [NumberField F] (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), (∀ v, IsStdV v (lam v)) → ∀ (lf : Measure (Af F)), lf.IsAddHaarMeasure → lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1 → ∀ (ι : Type) [Fintype ι] (S : Finset (HeightOneSpectrum (𝓞 F))) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (ι → Fv F v)), (∀ v, MeasurableSet (A v)) → (Measure.pi fun _ : ι => lf) {x | (∀ v ∈ S, (fun i => evalV F v (x i)) ∈ A v) ∧ ∀ v, v ∉ S → ∀ i, evalV F v (x i) ∈ v.adicCompletionIntegers F} = ∏ v ∈ S, (Measure.pi fun _ : ι => lam v) (A v) := by
  intro F _ _ lam hlam lf hlf h1 ι _ S A hA
  obtain ⟨-, hAfLC, hAfSC, hAfT2⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  have hloc := fun v => GlobalTheory.T.completion_is_local_ring F v
  haveI : ∀ v, IsTopologicalRing (Fv F v) := fun v => (hloc v).1
  haveI : ∀ v, LocallyCompactSpace (Fv F v) := fun v => (hloc v).2.1
  haveI : ∀ v, SecondCountableTopology (Fv F v) := fun v => (hloc v).2.2.1
  haveI : ∀ v, BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  haveI : ∀ v, (lam v).IsAddHaarMeasure := fun v => (hlam v).1
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  let ν : Measure (∀ v : S, ι → Fv F v.1) := Measure.pi fun v : S => Measure.pi fun _ : ι => lam v.1
  let O : Set (∀ v : S, ι → Fv F v.1) :=
    Set.pi Set.univ fun v : S => Set.pi Set.univ fun _ : ι => (v.1.adicCompletionIntegers F : Set (Fv F v.1))
  have hOo : IsOpen O := isOpen_set_pi Set.finite_univ fun v _ =>
    isOpen_set_pi Set.finite_univ fun _ _ => Valued.isOpen_valuationSubring _
  have hO0 : (0 : ∀ v : S, ι → Fv F v.1) ∈ O := fun v _ i _ => zero_mem (v.1.adicCompletionIntegers F)
  have hνO : ν O = 1 := by
    simp only [ν, O]
    rw [Measure.pi_pi]
    refine Finset.prod_eq_one fun v _ => ?_
    rw [Measure.pi_pi]
    exact Finset.prod_eq_one fun _ _ => (hlam v.1).2
  have hmO : (Measure.pi fun _ : ι => lf) ((offS (F := F) ι S : Set (ι → Af F)) ∩ compS ι S ⁻¹' O) = 1 := by
    have : ((offS (F := F) ι S : Set (ι → Af F)) ∩ compS ι S ⁻¹' O) =
        Set.pi Set.univ fun _ : ι => {x : Af F | ∀ v, x v ∈ v.adicCompletionIntegers F} := by
      ext x
      constructor
      · rintro ⟨hx1, hx2⟩ i _ v
        by_cases hv : v ∈ S
        · exact hx2 ⟨v, hv⟩ (Set.mem_univ _) i (Set.mem_univ _)
        · exact hx1 v hv i
      · intro hx
        exact ⟨fun v _ i => hx i (Set.mem_univ i) v, fun v _ i _ => hx i (Set.mem_univ i) v.1⟩
    rw [this, Measure.pi_pi]
    exact Finset.prod_eq_one fun _ _ => h1
  have hset : {x : ι → Af F | (∀ v ∈ S, (fun i => evalV F v (x i)) ∈ A v) ∧ ∀ v, v ∉ S → ∀ i, evalV F v (x i) ∈ v.adicCompletionIntegers F} =
      (offS (F := F) ι S : Set (ι → Af F)) ∩ compS ι S ⁻¹' (Set.pi Set.univ fun v : S => A v.1) := by
    ext x
    constructor
    · rintro ⟨hx1, hx2⟩
      exact ⟨hx2, fun v _ => hx1 v.1 v.2⟩
    · rintro ⟨hx1, hx2⟩
      exact ⟨fun v hv => hx2 ⟨v, hv⟩ (Set.mem_univ _), hx1⟩
  rw [hset, measure_inter_preimage (Measure.pi fun _ : ι => lf) (offS (F := F) ι S)
    (isOpen_offS ι S).measurableSet (compS ι S) (continuous_compS ι S).measurable
    (exists_offS_compS ι S) ν hOo hO0 hmO hνO (MeasurableSet.univ_pi fun v => hA v.1)]
  simp only [ν]
  rw [Measure.pi_pi]
  exact Finset.prod_coe_sort S fun v => (Measure.pi fun _ : ι => lam v) (A v)

end GlobalTheory.CompanionTheory.SW.AfBox
end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.gram_fiber_measure_disintegration_formula : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ) (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∀ S : HermR R σ n, IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det → ∃ B : Set (HermR R σ n), IsOpen B ∧ S ∈ B ∧ (∀ S' ∈ B, IsUnit (S' : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det) ∧ ∃ fib, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ (gramR R σ J) Subtype.val (gramR R σ J ⁻¹' (Subtype.val '' B)) ν B fib := by
  first | exact @GlobalTheory.CompanionTheory.SW.GramNear.exists_fibre_near | exact GlobalTheory.CompanionTheory.SW.GramNear.exists_fibre_near | (intros; apply GlobalTheory.CompanionTheory.SW.GramNear.exists_fibre_near <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.hermitian_local_continuous_congruence_section : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ) (S : HermR R σ n), IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det → ∃ (B : Set (HermR R σ n)) (g : HermR R σ n → GL (Fin n) (R ⊗[F] E)), IsOpen B ∧ S ∈ B ∧ ContinuousOn g B ∧ g S = 1 ∧ ∀ S' ∈ B, (S' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = cT (sigR R σ) (g S' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * (g S' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.exists_local_section | exact GlobalTheory.CompanionTheory.SW.exists_local_section | (intros; apply GlobalTheory.CompanionTheory.SW.exists_local_section <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.euler_product_measure_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (I : Measure (Fin n → Fin M → AF F ⊗[F] E)) (c : ℝ≥0) (minf : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (m : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)), (IsEulerProd b I c minf m → I = 0 → c = 0 ∨ minf = 0 ∨ ∃ v, m v = 0) ∧ (IsEulerProd b I c minf m → (minf = 0 ∨ ∃ v, m v = 0) → I = 0) ∧ ((∀ v, m v (latV b v) < ⊤) → Summable (fun v => |(m v (latV b v)).toReal - 1|) → (minf = 0 ∨ ∃ v, m v = 0) → IsEulerProd b 0 c minf m) := by
  first | exact @GlobalTheory.CompanionTheory.SW.EulerZero.euler_zero | exact GlobalTheory.CompanionTheory.SW.EulerZero.euler_zero | (intros; apply GlobalTheory.CompanionTheory.SW.EulerZero.euler_zero <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.finite_adelic_trace_form_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (B : Matrix (Fin M × Fin d) (Fin M × Fin d) F), (∀ x y : Fin M → Af F ⊗[F] E, Algebra.trace (Af F) (Af F ⊗[F] E) (hR (Af F) σ J x y) = cv (Af F) b x ⬝ᵥ (B.map (algebraMap F (Af F)) *ᵥ cv (Af F) b y)) → ∀ (lf : Measure (Af F)), lf.IsAddHaarMeasure → ∀ (a : ℕ) (U : Set (Af F)), coordW (Af F) b lf 1 M {X | (∀ v, projV v X ∈ {X : (Fin 1 → Fin M → Fv F v ⊗[F] E) | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v}) ∧ algebraMap F (Af F) (1 / 2) * Algebra.trace (Af F) (Af F ⊗[F] E) (gramR (Af F) σ J X 0 0) ∈ U} = (Measure.pi fun _ : Fin M × Fin d => lf) {x | (∀ i v, ((a : Af F) * x i) v ∈ v.adicCompletionIntegers F) ∧ algebraMap F (Af F) (1 / 2) * (x ⬝ᵥ (B.map (algebraMap F (Af F)) *ᵥ x)) ∈ U} := by
  first | exact @GlobalTheory.CompanionTheory.SW.BB.finDensity_coord | exact GlobalTheory.CompanionTheory.SW.BB.finDensity_coord | (intros; apply GlobalTheory.CompanionTheory.SW.BB.finDensity_coord <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.gram_fiber_cons_product_fold : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∀ x ∈ B₀, ∀ y₀ : Fin 1 → Fin (M + 1) → R ⊗[F] E, gramR R σ (blockOne (algebraMap F E t) J) y₀ = (hermScal R σ (algebraMap F R t) : HermR R σ 1) → chi σ J t s a b lam ((Uset σ J t B₀ a : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)).indicator φ) (scl (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E)) y₀) = ∫⁻ c : Fin n → R ⊗[F] E, ∫⁻ S' in Unt σ R n, ∫⁻ X, φ (actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E)) c X)) ∂(m' S') ∂(coordHerm R σ b lam n) ∂(Measure.pi fun _ => coordK R b lam) := by
  first | exact @GlobalTheory.CompanionTheory.SW.PiLocalization₂.chi_at_fibre | exact GlobalTheory.CompanionTheory.SW.PiLocalization₂.chi_at_fibre | (intros; apply GlobalTheory.CompanionTheory.SW.PiLocalization₂.chi_at_fibre <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.gram_fiber_cons_concentrated_on_fiber : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ S : HermR R σ (n + 1), fibS σ J t m₁ m' s B₀ a κ₁ cm S (gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' {(S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))} ∩ gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' (Subtype.val '' (Bset R σ t a B₀ : Set (HermR R σ (n + 1)))))ᶜ = 0 := by
  first | exact @GlobalTheory.CompanionTheory.SW.PiLocalization₂.fibS_support | exact GlobalTheory.CompanionTheory.SW.PiLocalization₂.fibS_support | (intros; apply GlobalTheory.CompanionTheory.SW.PiLocalization₂.fibS_support <;> assumption)
end
