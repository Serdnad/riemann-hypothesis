module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.NumFieldHosCountable
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle019
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle037
import GroundTheory.AutomorphicForms.Bundle012
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.Bundle002
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle053

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal NNReal Topology

namespace GlobalTheory.CompanionTheory.HaarScale

theorem unit_mul_map_haar : ∀ (F : Type) [Field F] [NumberField F] (e : Ainf F ≃+* (InfinitePlace F → ℝ)), IsHomeomorph e → ∀ (lam : Measure (Ainf F)), lam.IsAddHaarMeasure → ∀ t : Ainf F, IsUnit t → lam.map (fun y => t * y) = (∏ w, ‖e t w‖₊)⁻¹ • lam := by
  intro F _ _ e he lam hlam t ht
  classical
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  have hc : Continuous e := he.continuous
  let h : Ainf F ≃ₜ (InfinitePlace F → ℝ) := he.homeomorph e
  have hcs : Continuous e.symm := by
    have : (e.symm : (InfinitePlace F → ℝ) → Ainf F) = h.symm := by
      funext y
      have h1 : e (h.symm y) = y := h.apply_symm_apply y
      exact e.symm_apply_eq.2 h1.symm
    rw [this]; exact h.symm.continuous
  have hm : Measurable e := hc.measurable
  have hms : Measurable e.symm := hcs.measurable
  have hmul : Measurable (fun y : Ainf F => t * y) := by
    have : (fun y : Ainf F => t * y) = fun y => e.symm (e t * e y) := by
      funext y; simp
    rw [this]
    exact hcs.measurable.comp (hm.const_mul _)
  obtain ⟨D, hD⟩ : ∃ D : InfinitePlace F → ℝ, D = e t := ⟨_, rfl⟩
  have hDu : IsUnit D := hD ▸ ht.map e
  have hD0 : ∀ w, D w ≠ 0 := fun w => by
    obtain ⟨u, hu⟩ := hDu
    have h1 : D w * (u⁻¹ : (InfinitePlace F → ℝ)ˣ).1 w = 1 := by
      have := congrFun (u.mul_inv) w
      rw [hu] at this
      simpa using this
    exact left_ne_zero_of_mul_eq_one h1
  haveI hμ : (lam.map e).IsAddHaarMeasure :=
    AddEquiv.isAddHaarMeasure_map lam e.toAddEquiv hc hcs
  let L : (InfinitePlace F → ℝ) →ₗ[ℝ] (InfinitePlace F → ℝ) := Matrix.toLin' (Matrix.diagonal D)
  have hL : ∀ x, L x = D * x := fun x => by
    funext w
    simp [L, Matrix.toLin'_apply, Matrix.mulVec_diagonal]
  have hdet : LinearMap.det L = ∏ w, D w := by
    simp [L, LinearMap.det_toLin', Matrix.det_diagonal]
  have hdet0 : LinearMap.det L ≠ 0 := by
    rw [hdet]; exact Finset.prod_ne_zero_iff.2 fun w _ => hD0 w
  have hscale := Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := lam.map e) hdet0
  have hconst : ENNReal.ofReal |(LinearMap.det L)⁻¹| = (((∏ w, ‖e t w‖₊)⁻¹ : ℝ≥0) : ℝ≥0∞) := by
    have : |(LinearMap.det L)⁻¹| = (((∏ w, ‖e t w‖₊)⁻¹ : ℝ≥0) : ℝ) := by
      rw [hdet, abs_inv, Finset.abs_prod]
      push_cast
      simp [hD]
    rw [this, ENNReal.ofReal_coe_nnreal]
  have key : (lam.map (fun y => t * y)).map e = (∏ w, ‖e t w‖₊)⁻¹ • lam.map e := by
    rw [Measure.map_map hm hmul, ENNReal.smul_def, ← hconst, ← hscale,
      Measure.map_map L.continuous_of_finiteDimensional.measurable hm]
    congr 1
    funext y
    simp [hL, hD]
  have back : ∀ ν : Measure (Ainf F), (ν.map e).map e.symm = ν := fun ν => by
    rw [Measure.map_map hms hm]
    have : (e.symm ∘ e : Ainf F → Ainf F) = id := by funext y; simp
    rw [this, Measure.map_id]
  rw [← back (lam.map fun y => t * y), key, Measure.map_smul, back]
  exact hms.aemeasurable

end GlobalTheory.CompanionTheory.HaarScale
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.AvgV

theorem fibre_mass_eq {V R : Type} [TopologicalSpace V] [MeasurableSpace V] [TopologicalSpace R] [MeasurableSpace R]
    (μ : Measure V) (ν : Measure R) (q : V → R) (hq : Measurable q) (B : Set R) (fib : R → Measure V)
    (h : IsFibreFamily μ q id Set.univ ν B fib) {A : Set V} {S : Set R} (hA : MeasurableSet A)
    (hS : MeasurableSet S) : μ (A ∩ q ⁻¹' S) = ∫⁻ s in S, fib s A ∂ν := by
  obtain ⟨h1, h2, -⟩ := h
  have hT : MeasurableSet (A ∩ q ⁻¹' S) := hA.inter (hq hS)
  have e := h2 ((A ∩ q ⁻¹' S).indicator 1) (measurable_one.indicator hT)
  simp only [Measure.restrict_univ, lintegral_indicator_one hT] at e
  rw [e, ← lintegral_indicator hS]
  refine lintegral_congr fun b => ?_
  have hae : ∀ᵐ x ∂(fib b), q x = b := by
    refine measure_mono_null ?_ (h1 b)
    intro x hx hx'
    exact hx hx'.1
  by_cases hb : b ∈ S
  · rw [Set.indicator_of_mem hb]
    refine measure_congr ?_
    filter_upwards [hae] with x hx
    refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
    show q x ∈ S
    rwa [hx]
  · rw [Set.indicator_of_notMem hb]
    refine measure_mono_null (t := {x | ¬ q x = b}) ?_ hae
    intro x hx hxb
    apply hb
    rw [← hxb]
    exact hx.2

theorem tendsto_mean {R : Type} [TopologicalSpace R] [MeasurableSpace R] (ν : Measure R) (G : R → ℝ≥0∞) (c : R)
    (hG : ContinuousAt (fun s => (G s).toReal) c) (hfin : ∀ᶠ s in nhds c, G s ≠ ⊤) (S : ℕ → Set R)
    (hS : ∀ k, MeasurableSet (S k)) (hl : Filter.Tendsto S Filter.atTop (nhds c).smallSets)
    (hpos : ∀ k, ν (S k) ≠ 0) (htop : ∀ k, ν (S k) ≠ ⊤) :
    Filter.Tendsto (fun k => (∫⁻ s in S k, G s ∂ν).toReal / (ν (S k)).toReal) Filter.atTop
      (nhds (G c).toReal) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hN : {s | G s ≠ ⊤ ∧ dist (G s).toReal (G c).toReal < ε / 2} ∈ nhds c :=
    Filter.inter_mem hfin (hG.eventually (Metric.ball_mem_nhds _ (half_pos hε)))
  have hev := hl.eventually (Filter.eventually_smallSets_subset.2 hN)
  filter_upwards [hev] with k hk
  set g := (G c).toReal with hg
  have hg0 : 0 ≤ g := ENNReal.toReal_nonneg
  set n := ν (S k) with hn
  have hnr : 0 < n.toReal := ENNReal.toReal_pos (hpos k) (htop k)
  have hup : ∫⁻ s in S k, G s ∂ν ≤ ENNReal.ofReal (g + ε / 2) * n := by
    rw [hn, ← setLIntegral_const]
    refine setLIntegral_mono' (hS k) fun s hs => ?_
    obtain ⟨h1, h2⟩ := hk hs
    rw [← ENNReal.ofReal_toReal h1]
    refine ENNReal.ofReal_le_ofReal ?_
    have := (abs_lt.1 (Real.dist_eq _ _ ▸ h2)).2
    linarith
  have hlo : ENNReal.ofReal (g - ε / 2) * n ≤ ∫⁻ s in S k, G s ∂ν := by
    rw [hn, ← setLIntegral_const]
    refine setLIntegral_mono' (hS k) fun s hs => ?_
    obtain ⟨h1, h2⟩ := hk hs
    rw [← ENNReal.ofReal_toReal h1]
    refine ENNReal.ofReal_le_ofReal ?_
    have := (abs_lt.1 (Real.dist_eq _ _ ▸ h2)).1
    linarith
  have hfinU : ENNReal.ofReal (g + ε / 2) * n ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (htop k)
  have hup' : (∫⁻ s in S k, G s ∂ν).toReal ≤ (g + ε / 2) * n.toReal := by
    have := ENNReal.toReal_mono hfinU hup
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this
  have hlo' : (g - ε / 2) * n.toReal ≤ (∫⁻ s in S k, G s ∂ν).toReal := by
    have := ENNReal.toReal_mono (ne_top_of_le_ne_top hfinU hup) hlo
    rw [ENNReal.toReal_mul] at this
    refine le_trans ?_ this
    refine mul_le_mul_of_nonneg_right ?_ hnr.le
    rw [ENNReal.toReal_ofReal']
    exact le_max_left _ _
  rw [Real.dist_eq, abs_lt]
  constructor
  · have : g - ε / 2 ≤ (∫⁻ s in S k, G s ∂ν).toReal / n.toReal := (le_div_iff₀ hnr).2 hlo'
    linarith
  · have : (∫⁻ s in S k, G s ∂ν).toReal / n.toReal ≤ g + ε / 2 := (div_le_iff₀ hnr).2 hup'
    linarith

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.AvgV

end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.PureSB

section Coord

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def coordH (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] {d : ℕ}
    (b : Module.Basis (Fin d) F E) : R ⊗[F] E ≃ₜ (Fin d → R) :=
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : Module.Finite R (R ⊗[F] E) := Module.Finite.of_basis (Algebra.TensorProduct.basis R b)
  haveI : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R _
  { toEquiv := (Algebra.TensorProduct.basis R b).equivFun.toEquiv
    continuous_toFun := IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.basis R b).equivFun.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.basis R b).equivFun.symm.toLinearMap }

theorem repr_map {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] {d : ℕ}
    (b : Module.Basis (Fin d) F E) (f : R →ₐ[F] R') (z : R ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis R' b).repr (Algebra.TensorProduct.map f (AlgHom.id F E) z) k =
      f ((Algebra.TensorProduct.basis R b).repr z k) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e =>
    simp [Algebra.TensorProduct.basis_repr_tmul, Algebra.smul_def]
  | add x y hx hy => simp [map_add (f := _), hx, hy]

end Coord

section Box

variable {F : Type} [Field F] [NumberField F]

theorem isCompact_box (S : Finset (HeightOneSpectrum (𝓞 F))) (C : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v))
    (hC : ∀ v, IsCompact (C v))
    (hS : ∀ v, v ∉ S → C v ⊆ (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :
    IsCompact {y : Af F | ∀ v, y v ∈ C v} := by
  classical
  let R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F
  let A := fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F))
  have hAo : ∀ v, IsOpen (A v) := fun v => Valued.isOpen_valuationSubring _
  have hF : Filter.cofinite ≤ Filter.principal ((S : Set (HeightOneSpectrum (𝓞 F)))ᶜ) := by
    rw [Filter.le_principal_iff, Filter.mem_cofinite, compl_compl]
    exact S.finite_toSet
  have hemb := RestrictedProduct.isOpenEmbedding_inclusion_principal (R := R) hAo hF
  have hcoe := RestrictedProduct.isEmbedding_coe_of_principal (R := R) (A := A)
    (S := (S : Set (HeightOneSpectrum (𝓞 F)))ᶜ)
  let K : Set (RestrictedProduct R A (Filter.principal ((S : Set (HeightOneSpectrum (𝓞 F)))ᶜ))) :=
    {x | ∀ v, x v ∈ C v}
  have hK : IsCompact K := by
    rw [hcoe.isCompact_iff]
    have : (DFunLike.coe '' K : Set (∀ v, R v)) = Set.pi Set.univ C := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩ v _
        exact hy v
      · intro hx
        refine ⟨⟨x, Filter.eventually_principal.2 fun v hv => hS v hv (hx v (Set.mem_univ v))⟩,
          fun v => hx v (Set.mem_univ v), rfl⟩
    rw [this]
    exact isCompact_univ_pi hC
  have himg := hK.image hemb.continuous
  have hset : {y : Af F | ∀ v, y v ∈ C v} = RestrictedProduct.inclusion R A hF '' K := by
    ext y
    constructor
    · intro hy
      have hy' : ∀ᶠ v in Filter.principal ((S : Set (HeightOneSpectrum (𝓞 F)))ᶜ), y v ∈ A v :=
        Filter.eventually_principal.2 fun v hv => hS v hv (hy v)
      exact ⟨⟨y, hy'⟩, hy, rfl⟩
    · rintro ⟨x, hx, rfl⟩ v
      exact hx v
  rw [hset]
  exact himg

end Box

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

variable {d M : ℕ} (b : Module.Basis (Fin d) F E) (S : Finset (HeightOneSpectrum (𝓞 F)))
  (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin M → Fv F v ⊗[F] E))


end Main

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.PureSB

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef
end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.ProdM

def splitVec (F : Type) [Field F] [NumberField F] (ι : Type) :
    (ι → AF F) ≃ₜ+ (ι → Ainf F) × (ι → Af F) where
  toFun y := (fun i => (y i).1, fun i => (y i).2)
  invFun p := fun i => (p.1 i, p.2 i)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  continuous_toFun := by
    refine Continuous.prodMk ?_ ?_
    · exact continuous_pi fun i => continuous_fst.comp (continuous_apply i)
    · exact continuous_pi fun i => continuous_snd.comp (continuous_apply i)
  continuous_invFun := by
    refine continuous_pi fun i => Continuous.prodMk ?_ ?_
    · exact (continuous_apply i).comp continuous_fst
    · exact (continuous_apply i).comp continuous_snd

theorem map_split_eq_smul_prod : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι]
    (m : Measure (ι → AF F)) (μ₁ : Measure (ι → Ainf F)) (μ₂ : Measure (ι → Af F)),
    m.IsAddHaarMeasure → μ₁.IsAddHaarMeasure → μ₂.IsAddHaarMeasure →
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
      m.map (fun y : ι → AF F => ((fun i => (y i).1, fun i => (y i).2) : (ι → Ainf F) × (ι → Af F))) =
        c • μ₁.prod μ₂ := by
  intro F _ _ ι _ m μ₁ μ₂ hm h₁ h₂
  haveI : SecondCountableTopology (Af F) := Formalism.IndefR.Eqv.G5.af_secondCountable
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  haveI : SecondCountableTopology (AF F) :=
    inferInstanceAs (SecondCountableTopology (Ainf F × Af F))
  have hH : (m.map (splitVec F ι)).IsAddHaarMeasure :=
    ContinuousAddEquiv.isAddHaarMeasure_map m (splitVec F ι)
  have hc := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure (m.map (splitVec F ι)) (μ₁.prod μ₂)
  refine ⟨(Measure.addHaarScalarFactor (m.map (splitVec F ι)) (μ₁.prod μ₂) : ENNReal), ?_, ENNReal.coe_ne_top, ?_⟩
  · exact_mod_cast hc.ne'
  · have h := Measure.isAddLeftInvariant_eq_smul (m.map (splitVec F ι)) (μ₁.prod μ₂)
    exact h

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.ProdM
end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Euler

open GlobalTheory.CompanionTheory.SW

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem measurable_projInf [Module.Finite F E] {d : ℕ} (b : Module.Basis (Fin d) F E) (n M : ℕ) :
    Measurable (HeckeCharacterZeroLocus.SiegelWeilU.projInf : (Fin n → Fin M → AF F ⊗[F] E) → _) := by
  have e := TopK.coordHomeo (E := E) (AF F) b
  have : SecondCountableTopology (AF F ⊗[F] E) := e.secondCountableTopology
  have : BorelSpace (AF F ⊗[F] E) := ⟨rfl⟩
  have : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
  have hc : Continuous (HeckeCharacterZeroLocus.SiegelWeilU.projInf : (Fin n → Fin M → AF F ⊗[F] E) → _) :=
    MeasProj.continuous_mapTup b (HeckeCharacterZeroLocus.SiegelWeilU.fstA F) MeasProj.continuous_fstA
  refine measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun i => ?_
  exact (((continuous_apply i).comp (continuous_apply a)).comp hc).measurable

theorem measurable_projV [Module.Finite F E] {d : ℕ} (b : Module.Basis (Fin d) F E) (n M : ℕ)
    (v : HeightOneSpectrum (𝓞 F)) :
    Measurable (fun X : Fin n → Fin M → AF F ⊗[F] E =>
      HeckeCharacterZeroLocus.SiegelWeilU.projV v (HeckeCharacterZeroLocus.SiegelWeilU.projFin X)) := by
  have e := TopK.coordHomeo (E := E) (AF F) b
  have : SecondCountableTopology (AF F ⊗[F] E) := e.secondCountableTopology
  have : BorelSpace (AF F ⊗[F] E) := ⟨rfl⟩
  have : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  have h1 : Continuous (HeckeCharacterZeroLocus.SiegelWeilU.projFin : (Fin n → Fin M → AF F ⊗[F] E) → _) :=
    MeasProj.continuous_mapTup b (HeckeCharacterZeroLocus.SiegelWeilU.sndA F) MeasProj.continuous_sndA
  have h2 : Continuous (HeckeCharacterZeroLocus.SiegelWeilU.projV v : (Fin n → Fin M → Af F ⊗[F] E) → _) :=
    MeasProj.continuous_mapTup b (HeckeCharacterZeroLocus.SiegelWeilU.evalV F v) (MeasProj.continuous_evalV v)
  refine measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun i => ?_
  exact (((continuous_apply i).comp (continuous_apply a)).comp (h2.comp h1)).measurable

theorem measurableSet_box [Module.Finite F E] {d : ℕ} (b : Module.Basis (Fin d) F E) (n M : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))
    (hA : ∀ v, MeasurableSet (A v)) (hS : ∀ v, v ∉ S → A v = HeckeCharacterZeroLocus.SiegelWeilU.latV b v) :
    MeasurableSet {X : Fin n → Fin M → AF F ⊗[F] E |
      ∀ v, HeckeCharacterZeroLocus.SiegelWeilU.projV v (HeckeCharacterZeroLocus.SiegelWeilU.projFin X) ∈ A v} := by
  have e := TopK.coordHomeo (E := E) (AF F) b
  have : SecondCountableTopology (AF F ⊗[F] E) := e.secondCountableTopology
  have : BorelSpace (AF F ⊗[F] E) := ⟨rfl⟩
  rw [EulerBox.box_eq b S A hS]
  exact (MeasProj.isOpen_intOff b S).measurableSet.inter
    (Finset.measurableSet_biInter S fun v _ => measurable_projV b n M v (hA v))

end SlopeTestRemainingChoices

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Euler
end
end
