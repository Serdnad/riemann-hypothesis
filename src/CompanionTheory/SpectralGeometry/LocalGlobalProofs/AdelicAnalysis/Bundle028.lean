module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.Bundle001
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.StLamOf
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle015
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicTupleLocalGlobalProperties
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle022
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle023
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsTraceFormGramMatrixInBasis
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.WittExtensionGlobal
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
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd

@[expose] public section

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.LamUnit

theorem conj_ne_id {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : σ ≠ AlgHom.id F E := by
  intro hσ
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have := h.2.1
  apply IsTotallyComplex.complexEmbedding_not_isReal τ
  rw [ComplexEmbedding.isReal_iff]
  ext x
  have := h.2.2.2 τ x
  rw [hσ] at this
  simpa [ComplexEmbedding.conjugate_coe_eq] using this.symm

theorem fixed_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (a : E) : σ a = a ↔ a ∈ (algebraMap F E).range := by
  constructor
  · intro ha
    by_contra hnot
    have hli : LinearIndependent F ![(1 : E), a] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      have ht : t = 0 := by
        by_contra ht
        apply hnot
        refine ⟨-(s / t), ?_⟩
        have ht' : algebraMap F E t ≠ 0 := (map_ne_zero _).2 ht
        have h1 : algebraMap F E s + algebraMap F E t * a = 0 := by
          simpa [Algebra.smul_def] using hst
        rw [map_neg, map_div₀]
        field_simp
        linear_combination -h1
      subst ht
      refine ⟨?_, rfl⟩
      simpa using hst
    have hspan := hli.span_eq_top_of_card_eq_finrank (by simp [h.2.2.1])
    apply conj_ne_id h
    have hlin : σ.toLinearMap = (AlgHom.id F E).toLinearMap := by
      refine LinearMap.ext_on hspan ?_
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · simp
      · simpa using ha
    ext x
    exact LinearMap.congr_fun hlin x
  · rintro ⟨c, rfl⟩
    exact σ.commutes c

theorem exists_norm_one_sub_isUnit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R],
    PIW.AdelicOrbitU.UnitChoice R → ∀ (t : R ⊗[F] E) (β : Rˣ), ∃ lam : R ⊗[F] E,
      lam * sigR R σ lam = 1 ∧ IsUnit (algebraMap R (R ⊗[F] E) (β : R) - sigR R σ lam * t) := by
  intro F E _ _ _ _ _ σ hcm R _ _ hU t β
  obtain ⟨lam, h1, h2⟩ := PIW.AdelicOrbitU.stLam F E σ hcm.2.2.1 (fixed_iff hcm) R hU
    (algebraMap R (R ⊗[F] E) ((β⁻¹ : Rˣ) : R) * t) 1 one_ne_zero
  refine ⟨lam, h1, ?_⟩
  have hb : IsUnit (algebraMap R (R ⊗[F] E) (β : R)) := β.isUnit.map _
  have hinv : algebraMap R (R ⊗[F] E) (β : R) * algebraMap R (R ⊗[F] E) ((β⁻¹ : Rˣ) : R) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have key : algebraMap R (R ⊗[F] E) (β : R) - sigR R σ lam * t =
      algebraMap R (R ⊗[F] E) (β : R) * (algebraMap F (R ⊗[F] E) 1 -
        Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ lam * (algebraMap R (R ⊗[F] E) ((β⁻¹ : Rˣ) : R) * t)) := by
    have hs : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ lam = sigR R σ lam := rfl
    rw [map_one, hs]
    linear_combination (sigR R σ lam * t) * hinv
  rw [key]
  exact hb.mul h2

end GlobalTheory.CompanionTheory.SW.LamUnit
end

section

open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SW.FibreGlue

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

section Local

variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure V} {ν : Measure X} {f : V → Y} {g : V → X} {ι : X → Y}

lemma ae_g_eq (hι : Function.Injective ι) (hf : ∀ v, f v = ι (g v)) {U : Set V} {m : Measure V}
    {b : X} (h : m (f ⁻¹' {ι b} ∩ U)ᶜ = 0) : ∀ᵐ v ∂m, g v = b := by
  have h' : ∀ᵐ v ∂m, v ∈ f ⁻¹' {ι b} ∩ U := by
    rw [ae_iff]; exact h
  refine h'.mono fun v hv => ?_
  apply hι
  rw [← hf v]
  exact hv.1

lemma piece (hι : Function.Injective ι) (hg : Continuous g) (hf : ∀ v, f v = ι (g v))
    {s D : Set X} (hD : MeasurableSet D) (hDs : D ⊆ s) {F : X → Measure V}
    (h : IsFibreFamily μ f ι (g ⁻¹' s) ν s F) {φ : V → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ v in g ⁻¹' D, φ v ∂μ = ∫⁻ b in D, ∫⁻ v, φ v ∂(F b) ∂ν := by
  have hm : MeasurableSet (g ⁻¹' D) := hg.measurable hD
  have e1 : ∫⁻ v in g ⁻¹' D, φ v ∂μ = ∫⁻ v in g ⁻¹' s, (g ⁻¹' D).indicator φ v ∂μ := by
    rw [setLIntegral_indicator hm, Set.inter_eq_left.2 (Set.preimage_mono hDs)]
  rw [e1, h.2.1 _ (hφ.indicator hm), ← lintegral_indicator hD]
  refine lintegral_congr fun b => ?_
  have hae := ae_g_eq hι hf (h.1 b)
  by_cases hb : b ∈ D
  · rw [Set.indicator_of_mem hb]
    refine lintegral_congr_ae (hae.mono fun v hv => ?_)
    have : v ∈ g ⁻¹' D := by
      show g v ∈ D
      rw [hv]; exact hb
    simp only [Set.indicator_of_mem this]
  · rw [Set.indicator_of_notMem hb]
    have e : ∫⁻ v, (g ⁻¹' D).indicator φ v ∂(F b) = ∫⁻ _, 0 ∂(F b) := by
      refine lintegral_congr_ae (hae.mono fun v hv => ?_)
      have : v ∉ g ⁻¹' D := by
        show g v ∉ D
        rw [hv]; exact hb
      simp only [Set.indicator_of_notMem this]
    simpa using e


open Classical in
noncomputable def restr (B : Set X) (fam : X → Measure V) : X → Measure V := by
  classical
  exact fun b => if b ∈ B then fam b else 0

lemma restr_family (hι : Function.Injective ι) (hg : Continuous g) (hf : ∀ v, f v = ι (g v))
    {B B₂ : Set X} (hB₂ : IsOpen B₂) (hsub : B₂ ⊆ B) {fam : X → Measure V}
    (h : IsFibreFamily μ f ι (g ⁻¹' B) ν B fam) :
    IsFibreFamily μ f ι (g ⁻¹' B₂) ν B₂ (restr B₂ fam) := by
  refine ⟨?_, ?_, ?_⟩
  · intro b
    by_cases hb : b ∈ B₂
    · simp only [restr, if_pos hb]
      refine measure_mono_null ?_ (h.1 b)
      intro v hv hv2
      apply hv
      refine ⟨hv2.1, ?_⟩
      show g v ∈ B₂
      have : g v = b := by
        apply hι
        rw [← hf v]
        exact hv2.1
      rw [this]; exact hb
    · simp [restr, hb]
  · intro φ hφ
    rw [piece hι hg hf hB₂.measurableSet hsub h hφ, ← lintegral_indicator hB₂.measurableSet]
    refine lintegral_congr fun b => ?_
    by_cases hb : b ∈ B₂
    · simp [restr, hb]
    · simp [restr, hb]
  · intro φ hφ hφc hφs
    have H := h.2.2 φ hφ hφc (hφs.trans (Set.preimage_mono hsub))
    refine ⟨fun b hb => ?_, ?_⟩
    · simp only [restr, if_pos hb]
      exact H.1 b (hsub hb)
    · refine (H.2.mono hsub).congr fun b hb => ?_
      simp only [restr, if_pos hb]

end Local

theorem glue : ∀ (V X Y : Type) [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X) [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure] (f : V → Y) (g : V → X) (ι : X → Y), Function.Injective ι → Continuous g → (∀ v, f v = ι (g v)) → ∀ (B : Set X), IsOpen B → (∀ b ∈ B, ∃ B' : Set X, IsOpen B' ∧ b ∈ B' ∧ B' ⊆ B ∧ ∃ fib' : X → Measure V, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B') ν B' fib') → ∃ fib : X → Measure V, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B) ν B fib := by
  intro V X Y _ _ _ _ _ _ _ _ _ _ _ _ μ ν _ _ _ f g ι hι hg hf B hB hloc
  classical
  choose! C hCo hbC hCB F hF using hloc
  let fib : X → Measure V := fun b => if b ∈ B then F b b else 0
  have hfibB : ∀ c ∈ B, fib c = F c c := fun c hc => by simp only [fib, if_pos hc]
  have hagree : ∀ a ∈ B, ∀ c ∈ C a, fib c = F a c := by
    intro a ha c hc
    have hcB : c ∈ B := hCB a ha hc
    have hI : IsOpen (C c ∩ C a) := (hCo c hcB).inter (hCo a ha)
    have r1 := restr_family hι hg hf hI Set.inter_subset_right (hF a ha)
    have u := GlobalTheory.T.fibre_family_eq_on_open_subset V X Y μ ν f g ι hι hg hf (C c) (C c ∩ C a) (hCo c hcB) hI
      Set.inter_subset_left (F c) (restr (C c ∩ C a) (F a)) (hF c hcB) r1 c ⟨hbC c hcB, hc⟩
    have hm : c ∈ C c ∩ C a := ⟨hbC c hcB, hc⟩
    simp only [restr, if_pos hm] at u
    rw [hfibB c hcB, u]
  refine ⟨fib, ?_, ?_, ?_⟩
  · intro b
    by_cases hb : b ∈ B
    · rw [hfibB b hb]
      refine measure_mono_null (Set.compl_subset_compl.2 ?_) ((hF b hb).1 b)
      intro v hv
      exact ⟨hv.1, hCB b hb hv.2⟩
    · simp [fib, hb]
  · intro φ hφ
    rcases B.eq_empty_or_nonempty with rfl | hne
    · simp [fib]
    obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable (fun b : B => C b)
      (fun b => hCo b b.2)
    have hall : ⋃ b : B, C b = B := by
      apply Set.Subset.antisymm
      · exact Set.iUnion_subset fun b => hCB b b.2
      · intro b hb
        exact Set.mem_iUnion.2 ⟨⟨b, hb⟩, hbC b hb⟩
    have hTne : T.Nonempty := by
      by_contra hT
      rw [Set.not_nonempty_iff_eq_empty] at hT
      subst hT
      rw [hall] at hTU
      simp only [Set.mem_empty_iff_false, Set.iUnion_of_empty, Set.iUnion_empty] at hTU
      exact hne.ne_empty hTU.symm
    obtain ⟨e, he⟩ := hTc.exists_eq_range hTne
    let s : ℕ → Set X := fun n => C (e n)
    have hsU : ⋃ n, s n = B := by
      rw [← hall, ← hTU, he]
      simp [s]
    have hDm : ∀ n, MeasurableSet (disjointed s n) :=
      MeasurableSet.disjointed fun n => (hCo (e n) (e n).2).measurableSet
    have hDd : Pairwise (Function.onFun Disjoint (disjointed s)) := disjoint_disjointed s
    have hDU : ⋃ n, disjointed s n = B := by rw [iUnion_disjointed, hsU]
    calc ∫⁻ v in g ⁻¹' B, φ v ∂μ
        = ∫⁻ v in ⋃ n, g ⁻¹' (disjointed s n), φ v ∂μ := by
          rw [← Set.preimage_iUnion, hDU]
      _ = ∑' n, ∫⁻ v in g ⁻¹' (disjointed s n), φ v ∂μ :=
          lintegral_iUnion (fun n => hg.measurable (hDm n))
            (fun i j hij => (hDd hij).preimage g) _
      _ = ∑' n, ∫⁻ b in disjointed s n, ∫⁻ v, φ v ∂(fib b) ∂ν := by
          refine tsum_congr fun n => ?_
          rw [piece hι hg hf (hDm n) (disjointed_subset s n) (hF (e n) (e n).2) hφ]
          refine setLIntegral_congr_fun (hDm n) fun b hb => ?_
          rw [hagree (e n) (e n).2 b (disjointed_subset s n hb)]
      _ = ∫⁻ b in ⋃ n, disjointed s n, ∫⁻ v, φ v ∂(fib b) ∂ν :=
          (lintegral_iUnion hDm hDd _).symm
      _ = ∫⁻ b in B, ∫⁻ v, φ v ∂(fib b) ∂ν := by rw [hDU]
      _ = ∫⁻ b, ∫⁻ v, φ v ∂(fib b) ∂ν := by
          rw [← lintegral_indicator hB.measurableSet]
          refine lintegral_congr fun b => ?_
          by_cases hb : b ∈ B
          · simp [hb]
          · simp [hb, fib]
  · intro φ hφ hφc hφs
    have key : ∀ b ∈ B, Integrable φ (fib b) ∧
        ContinuousAt (fun c => ∫ v, φ v ∂(fib c)) b := by
      intro b hb
      obtain ⟨L₁, hL₁c, hbL₁, hL₁C⟩ := exists_compact_between (isCompact_singleton (x := b))
        (hCo b hb) (Set.singleton_subset_iff.2 (hbC b hb))
      obtain ⟨L₂, hL₂c, hbL₂, hL₂C⟩ := exists_compact_between (isCompact_singleton (x := b))
        isOpen_interior hbL₁
      have hclos : IsCompact (closure (interior L₁)) :=
        hL₁c.closure_of_subset interior_subset
      obtain ⟨χ, hχs, hχ1, -⟩ := exists_tsupport_one_of_isOpen_isClosed isOpen_interior hclos
        hL₂c.isClosed hL₂C
      have hK : L₂ ∈ 𝓝 b := mem_interior_iff_mem_nhds.1 (hbL₂ rfl)
      let ψ : V → ℝ := φ * (χ ∘ g)
      have hψ : Continuous ψ := hφ.mul (χ.continuous.comp hg)
      have hψc : HasCompactSupport ψ := hφc.mul_right
      have hψs : tsupport ψ ⊆ g ⁻¹' (C b) := by
        refine (tsupport_mul_subset_right).trans ?_
        refine (tsupport_comp_subset_preimage _ hg).trans ?_
        exact Set.preimage_mono (hχs.trans (interior_subset.trans hL₁C))
      have H := (hF b hb).2.2 ψ hψ hψc hψs
      have hCsub : L₂ ⊆ C b := hL₂C.trans (interior_subset.trans hL₁C)
      have hae : ∀ c ∈ L₂, ∀ᵐ v ∂(F b c), ψ v = φ v := by
        intro c hc
        refine (ae_g_eq hι hf ((hF b hb).1 c)).mono fun v hv => ?_
        simp [ψ, hv, hχ1 hc]
      have hbK : b ∈ L₂ := mem_of_mem_nhds hK
      refine ⟨?_, ?_⟩
      · rw [hagree b hb b (hbC b hb)]
        exact (H.1 b (hbC b hb)).congr (hae b hbK)
      · refine (H.2.continuousAt ((hCo b hb).mem_nhds (hbC b hb))).congr ?_
        filter_upwards [hK] with c hc
        rw [hagree b hb c (hCsub hc)]
        exact integral_congr_ae (hae c hc)
    exact ⟨fun b hb => (key b hb).1, fun b hb => (key b hb).2.continuousWithinAt⟩

end GlobalTheory.CompanionTheory.SW.FibreGlue
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.adelic_tuple_local_global_properties : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ), (∀ X Y : Fin n → Fin M → AF F ⊗[F] E, projInf X = projInf Y → (∀ v, projV v (projFin X) = projV v (projFin Y)) → X = Y) ∧ (∀ X : Fin n → Fin M → AF F ⊗[F] E, ∀ᶠ v in Filter.cofinite, projV v (projFin X) ∈ latV b v) ∧ (∀ (Xinf : Fin n → Fin M → Ainf F ⊗[F] E) (Xv : ∀ v : HeightOneSpectrum (𝓞 F), Fin n → Fin M → Fv F v ⊗[F] E), (∀ᶠ v in Filter.cofinite, Xv v ∈ latV b v) → ∃ X : Fin n → Fin M → AF F ⊗[F] E, projInf X = Xinf ∧ ∀ v, projV v (projFin X) = Xv v) ∧ ∀ (Cinf : Set (Fin n → Fin M → Ainf F ⊗[F] E)) (Cv : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E)), IsCompact Cinf → (∀ v, IsCompact (Cv v)) → (∀ᶠ v in Filter.cofinite, Cv v ⊆ latV b v) → IsCompact {X : Fin n → Fin M → AF F ⊗[F] E | projInf X ∈ Cinf ∧ ∀ v, projV v (projFin X) ∈ Cv v} := by
  first | exact @GlobalTheory.CompanionTheory.SW.Glue.glue_main | exact GlobalTheory.CompanionTheory.SW.Glue.glue_main | (intros; apply GlobalTheory.CompanionTheory.SW.Glue.glue_main <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.gram_matrix_local_global : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ) (X : (Fin n → Fin M → AF F ⊗[F] E)) (T : Matrix (Fin n) (Fin n) E), (gramR (AF F) σ J X = T.map (inclR (AF F)) ↔ gramR (Ainf F) σ J (projInf X) = T.map (inclR (Ainf F)) ∧ ∀ v, gramR (Fv F v) σ J (projV v (projFin X)) = T.map (inclR (Fv F v))) ∧ ∀ Y : Fin n → Fin M → E, gramR (AF F) σ J (ratTup (AF F) Y) = (gramE σ J Y).map (inclR (AF F)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.GramLocal.gram_local | exact GlobalTheory.CompanionTheory.SW.GramLocal.gram_local | (intros; apply GlobalTheory.CompanionTheory.SW.GramLocal.gram_local <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.integral_almost_all_places : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), (∀ x : E, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr (inclR (Fv F v) x) k ∈ v.adicCompletionIntegers F) ∧ ∀ x : F, x ≠ 0 → ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, Valued.v (algebraMap F (Fv F v) x) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.SW.GoodInt.rational_integral_units | exact GlobalTheory.CompanionTheory.SW.GoodInt.rational_integral_units | (intros; apply GlobalTheory.CompanionTheory.SW.GoodInt.rational_integral_units <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.tensor_involution_algebra_properties : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [IsArtinianRing R] [IsReduced R], IsArtinianRing (R ⊗[F] E) ∧ IsReduced (R ⊗[F] E) ∧ IsUnit (2 : R ⊗[F] E) ∧ (∀ y, sigR R σ (sigR R σ y) = y) ∧ (∃ δ : R ⊗[F] E, IsUnit δ ∧ sigR R σ δ = -δ) ∧ (∀ y : R ⊗[F] E, sigR R σ y = y → ∃ r : R, y = r ⊗ₜ[F] (1 : E)) ∧ ∀ r : R, IsUnit (r ⊗ₜ[F] (1 : E) : R ⊗[F] E) ↔ IsUnit r := by
  first | exact @GlobalTheory.CompanionTheory.SW.KAlg.algebra_tensor_invol | exact GlobalTheory.CompanionTheory.SW.KAlg.algebra_tensor_invol | (intros; apply GlobalTheory.CompanionTheory.SW.KAlg.algebra_tensor_invol <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.arithmetic_unitary_group_discrete : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → Countable (HFinIn (AF F) σ J) ∧ ∃ U ∈ 𝓝 (1 : HA (AF F) σ J), ∀ h ∈ U, HA.mat (AF F) σ J h ∈ HFin (AF F) σ J → h = 1 := by
  first | exact @GlobalTheory.CompanionTheory.SW.rational_countable_discrete | exact GlobalTheory.CompanionTheory.SW.rational_countable_discrete | (intros; apply GlobalTheory.CompanionTheory.SW.rational_countable_discrete <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.hermitian_matrices_locally_compact_borel : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R], ∀ n : ℕ, LocallyCompactSpace (HermR R σ n) ∧ SecondCountableTopology (HermR R σ n) ∧ T2Space (HermR R σ n) ∧ BorelSpace (HermR R σ n) ∧ ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∃ g : (Fin n → Fin M → R ⊗[F] E) → HermR R σ n, Continuous g ∧ ∀ X, gramR R σ J X = (g X : Matrix (Fin n) (Fin n) (R ⊗[F] E)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.HermTop.herm_top | exact GlobalTheory.CompanionTheory.SW.HermTop.herm_top | (intros; apply GlobalTheory.CompanionTheory.SW.HermTop.herm_top <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.selfdual_measure_transport_equiv : ∀ (V V' : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V] [AddCommGroup V'] [TopologicalSpace V'] [IsTopologicalAddGroup V'] [MeasurableSpace V'] [BorelSpace V'] (e : V ≃ₜ+ V') (μ : Measure V) (χ : V' → V' → ℂ), SelfDual μ (fun x y => χ (e x) (e y)) ↔ SelfDual (μ.map e) χ := by
  first | exact @GlobalTheory.CompanionTheory.SW.selfDual_transport | exact GlobalTheory.CompanionTheory.SW.selfDual_transport | (intros; apply GlobalTheory.CompanionTheory.SW.selfDual_transport <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.selfdual_measure_twist_by_symmetric_auto : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) (χ : V → V → ℂ), SelfDual μ χ → ∀ (B : V ≃ₜ+ V), (∀ x y, χ x (B y) = χ (B x) y) → ∀ c : ℝ≥0, μ.map B = c • μ → SelfDual ((NNReal.sqrt c)⁻¹ • μ) (fun x y => χ x (B y)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.SdChange.selfDual_twist | exact GlobalTheory.CompanionTheory.SW.SdChange.selfDual_twist | (intros; apply GlobalTheory.CompanionTheory.SW.SdChange.selfDual_twist <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.exists_trace_form_gram_matrix_in_basis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∃ B : Matrix (Fin M × Fin d) (Fin M × Fin d) F, B.IsSymm ∧ B.det ≠ 0 ∧ (∀ x : Fin M → E, Algebra.trace F E (hE σ J x x) = (fun p : Fin M × Fin d => b.repr (x p.1) p.2) ⬝ᵥ (B *ᵥ fun p : Fin M × Fin d => b.repr (x p.1) p.2)) ∧ ∀ (R : Type) [CommRing R] [Algebra F R], (∀ x y : Fin M → R ⊗[F] E, Algebra.trace R (R ⊗[F] E) (hR R σ J x y) = (fun p : Fin M × Fin d => (Algebra.TensorProduct.basis R b).repr (x p.1) p.2) ⬝ᵥ (B.map (algebraMap F R) *ᵥ fun p : Fin M × Fin d => (Algebra.TensorProduct.basis R b).repr (y p.1) p.2)) ∧ ∀ h : HA R σ J, ∀ g : Matrix (Fin M × Fin d) (Fin M × Fin d) R, (∀ p q, g p q = (Algebra.TensorProduct.basis R b).repr ((HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) p.1 q.1 * inclR R (b q.2)) p.2) → gᵀ * B.map (algebraMap F R) * g = B.map (algebraMap F R) ∧ ∀ x : Fin M → R ⊗[F] E, (fun p : Fin M × Fin d => (Algebra.TensorProduct.basis R b).repr (((HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ x) p.1) p.2) = g *ᵥ fun p : Fin M × Fin d => (Algebra.TensorProduct.basis R b).repr (x p.1) p.2 := by
  first | exact @GlobalTheory.CompanionTheory.SW.TraceCoord.exists_trace_coord | exact GlobalTheory.CompanionTheory.SW.TraceCoord.exists_trace_coord | (intros; apply GlobalTheory.CompanionTheory.SW.TraceCoord.exists_trace_coord <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.witt_extension_global : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ) (X Y : Fin n → Fin M → E), gramE σ J X = gramE σ J Y → (gramE σ J X).det ≠ 0 → ∃ g ∈ UJ (σ : E →+* E) J, ∀ a, (g : Matrix (Fin M) (Fin M) E) *ᵥ X a = Y a := by
  first | exact @GlobalTheory.CompanionTheory.SW.WittE.witt_tuple | exact GlobalTheory.CompanionTheory.SW.WittE.witt_tuple | (intros; apply GlobalTheory.CompanionTheory.SW.WittE.witt_tuple <;> assumption)
end
