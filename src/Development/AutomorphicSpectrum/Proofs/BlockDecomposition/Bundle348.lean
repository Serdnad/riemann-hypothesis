module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import GroundTheory.PAdicHodge.Bundle004
public import GroundTheory.PAdicHodge.NormalizedTraceTower
public import GroundTheory.PAdicHodge.SenTateCharTower
import GroundTheory.LocalFields.PadicLogSeries
public import GroundTheory.PAdicHodge.Bundle013
import GroundTheory.PAdicHodge.BCrisEigenFrob
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RepresentationTheory.Subrepresentation
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle324
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilOrbitalMeasure
public import Mathlib.Order.Fin.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle022
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle223
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle214
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import GroundTheory.PAdicHodge.Bundle009
import ReciprocityTheory.GaloisValuations.GlobalA
import ReciprocityTheory.NeutralLocalFields.Bundle001
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle313
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.EPGFalseEqLastIff
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipApplyCastSuccLast
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet

@[expose] public section

section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer

open GroundTheory.LocalField GroundTheory.PAdicHodge GroundTheory.PAdicHodge.EigenWitt GroundTheory.PAdicHodge.EigenChar

theorem exists_pow_eigenvector_of_unramified_units {l : ℕ} [Fact l.Prime]
    (E : IntermediateField ℚ_[l] (Om l)) [FiniteDimensional ℚ_[l] ↥E]
    (ψ : Gal(Om l/↥E) →* ℤ_[l]ˣ) (hψ : Continuous ψ)
    (hI : ∀ σ, GroundTheory.LocalField.unramifiedDegree ↥E (Om l) σ = 1 → ψ σ = 1) :
    ∃ f : ℕ, 0 < f ∧ ∃ x : ℂ_[l], x ≠ 0 ∧ ∀ σ : Gal(Om l/↥E),
      σ • x = algebraMap ℚ_[l] ℂ_[l] ((((ψ σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) ^ f) * x := by
  have := isSepClosure_padicAlgCl (p := l) (L := E)
  obtain ⟨σ₀, hσ₀⟩ := unramifiedDegree_surjective (K := E) (Ω := PadicAlgCl l)
    (Multiplicative.ofAdd 1)
  set w : ℤ_[l]ˣ := ψ σ₀ with hwdef
  obtain ⟨f, hf, hq⟩ := exists_card_residueField_eq_pow (p := l) (L := E)
  obtain ⟨b, hb, hbσ⟩ := exists_unit_aInf_eigen (K := E) w
  set cA := wittToAInf (b : WittVector l (Fpbar l)) with hcA
  have hcu : IsUnit cA := b.isUnit.map _
  set θ := WittVector.fontaineTheta (normInteger ℂ_[l]) l
  set xc : ℂ_[l] := ((θ cA : normInteger ℂ_[l]) : ℂ_[l]) with hxcdef
  have hxc : xc ≠ 0 := by
    have h1 : θ cA ≠ 0 := (hcu.map θ).ne_zero
    exact fun h => h1 (Subtype.ext h)
  choose z hz using hbσ
  have hxcσ : ∀ σ, σ • xc = algebraMap ℚ_[l] ℂ_[l] (z σ) * xc := fun σ => by
    rw [hxcdef, ← AInf.fontaineTheta_gal_smul, hz σ, map_mul, Subring.coe_mul,
      fontaineTheta_padicIntToWitt]
  have hz₀ : (z σ₀ : ℚ_[l]) = ((w : ℤ_[l]) : ℚ_[l]) ^ f := by
    have h1 := gal_smul_twist_of_degree_one hb hq hσ₀
    rw [← hcA, hz σ₀] at h1
    have h2 := hcu.mul_left_inj.1 h1
    have h3 := congrArg (fun y => ((θ y : normInteger ℂ_[l]) : ℂ_[l])) h2
    simp only [θ, fontaineTheta_padicIntToWitt] at h3
    rw [← PadicInt.coe_pow]
    exact algebraMap_padic_cp_injective h3
  have hzI : ∀ σ, unramifiedDegree E (PadicAlgCl l) σ = 1 → (z σ : ℚ_[l]) = 1 := fun σ hσ => by
    have h1 := gal_smul_twist_of_inertia (b : WittVector l (Fpbar l)) hσ
    rw [← hcA, hz σ] at h1
    have h2 : IsPerfectoidField.padicIntToWitt l (z σ) * cA =
        IsPerfectoidField.padicIntToWitt l 1 * cA := by
      rw [h1, map_one, one_mul]
    have h3 := congrArg (fun y => ((θ y : normInteger ℂ_[l]) : ℂ_[l])) (hcu.mul_left_inj.1 h2)
    simp only [θ, fontaineTheta_padicIntToWitt] at h3
    have := algebraMap_padic_cp_injective h3
    rw [this, PadicInt.coe_one]
  obtain ⟨χ, hχc, hχ⟩ := exists_eigenChar hxc (fun σ => ⟨_, hxcσ σ⟩)
  have hχeq : ∀ σ, ((χ σ : ℚ_[l]ˣ) : ℚ_[l]) = (z σ : ℚ_[l]) := fun σ =>
    eq_of_mul_eq hxc ((hχ σ).symm.trans (hxcσ σ))
  have hψne : ∀ σ, ((((ψ σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l])) ≠ 0 := fun σ => by
    intro h
    exact (ψ σ).ne_zero (Subtype.ext (h.trans PadicInt.coe_zero.symm))
  let ρC : Gal(PadicAlgCl l/E) →* ℂ_[l] :=
    { toFun := fun σ => algebraMap ℚ_[l] ℂ_[l]
        ((((ψ σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) ^ f * ((χ σ⁻¹ : ℚ_[l]ˣ) : ℚ_[l]))
      map_one' := by simp
      map_mul' := fun a c => by
        simp only [mul_inv_rev, map_mul, Units.val_mul, PadicInt.coe_mul, mul_pow]
        ring }
  have hρC : Continuous ρC := by
    have hc1 : Continuous fun σ : Gal(PadicAlgCl l/E) => (((ψ σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) := by
      have hu : Continuous fun σ : Gal(PadicAlgCl l/E) => ((ψ σ : ℤ_[l]ˣ) : ℤ_[l]) :=
        (Units.continuous_val (M := ℤ_[l])).comp hψ
      exact (continuous_subtype_val : Continuous (fun y : ℤ_[l] => (y : ℚ_[l]))).comp hu
    have hc2 : Continuous fun σ : Gal(PadicAlgCl l/E) => ((χ σ⁻¹ : ℚ_[l]ˣ) : ℚ_[l]) :=
      Units.continuous_val.comp (hχc.comp continuous_inv)
    exact isometry_algebraMap_padic_cp.continuous.comp ((hc1.pow f).mul hc2)
  have hρval : ∀ σ, ρC σ = algebraMap ℚ_[l] ℂ_[l]
      ((((ψ σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) ^ f * (z σ : ℚ_[l])⁻¹) := fun σ => by
    change algebraMap ℚ_[l] ℂ_[l] _ = _
    rw [map_inv, Units.val_inv_eq_inv_val, hχeq]
  have hall := eq_one_of_degree_one ρC hρC hσ₀
    (by rw [hρval, hz₀, ← hwdef, mul_inv_cancel₀ (pow_ne_zero _ (hψne σ₀)), map_one])
    (fun σ hσ => by rw [hρval, hzI σ hσ, hI σ hσ, Units.val_one, PadicInt.coe_one, one_pow, inv_one,
      mul_one, map_one])
  refine ⟨f, hf, xc, hxc, fun σ => ?_⟩
  have h1 : (((ψ σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) ^ f * (z σ : ℚ_[l])⁻¹ = 1 :=
    algebraMap_padic_cp_injective (by rw [map_one, ← hρval]; exact hall σ)
  have hz0 : (z σ : ℚ_[l]) ≠ 0 := by
    intro h
    rw [h, inv_zero, mul_zero] at h1
    exact zero_ne_one h1
  rw [hxcσ σ, (mul_inv_eq_one₀ hz0).1 h1]

end GlobalTheory.CompanionTheory.LTPer
end
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZRes.TwoOrbit

theorem exists_equivariant_extension :
    ∀ {G : Type} [Group G] {W₁ : Type} [AddCommGroup W₁] [Module ℂ W₁] {Q P : Subgroup G} {x : G} (σ : Representation ℂ Q W₁) (φ : P → W₁) (C : Set P) (K : Subgroup G), (∀ c ∈ C, ∀ κ ∈ K, ∀ (q : Q) (p' : P), (q : G) * x * (c : G) * κ = x * (p' : G) → φ p' = σ q (φ c)) → (∀ p : P, φ p ≠ 0 → ∃ c ∈ C, ∃ q : Q, x * (p : G) = (q : G) * x * (c : G)) → ∃ f : G → W₁, (∀ (q : Q) (g : G), f ((q : G) * g) = σ q (f g)) ∧ (∀ (g : G), ∀ κ ∈ K, f (g * κ) = f g) ∧ (∀ p : P, f (x * (p : G)) = φ p) ∧ ∀ g : G, f g ≠ 0 → ∃ q : Q, ∃ c ∈ C, ∃ κ ∈ K, g = (q : G) * x * (c : G) * κ := by
  intro G _ W₁ _ _ Q P x σ φ C K h1 h2
  classical
  let Ω : G → Prop := fun g =>
    ∃ (q : Q) (c : P), c ∈ C ∧ ∃ κ ∈ K, g = (q : G) * x * (c : G) * κ
  have wd : ∀ (q q' : Q) (c c' : P), c ∈ C → c' ∈ C → ∀ κ ∈ K, ∀ κ' ∈ K,
      (q : G) * x * (c : G) * κ = (q' : G) * x * (c' : G) * κ' →
        σ q (φ c) = σ q' (φ c') := by
    intro q q' c c' hc hc' κ hκ κ' hκ' e
    have e' : ((q'⁻¹ * q : Q) : G) * x * (c : G) * (κ * κ'⁻¹) = x * (c' : G) := by
      have e2 : (q : G) * x * (c : G) * κ * κ'⁻¹ = (q' : G) * x * (c' : G) := by
        rw [e]; group
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      calc ((q' : G)⁻¹ * q) * x * c * (κ * κ'⁻¹)
          = (q' : G)⁻¹ * ((q : G) * x * (c : G) * κ * κ'⁻¹) := by group
        _ = x * (c' : G) := by rw [e2]; group
    have e3 := h1 c hc (κ * κ'⁻¹) (K.mul_mem hκ (K.inv_mem hκ')) (q'⁻¹ * q) c' e'
    rw [e3, ← Module.End.mul_apply, ← map_mul]
    simp
  let f : G → W₁ := fun g =>
    if h : Ω g then σ h.choose (φ h.choose_spec.choose) else 0
  have hf : ∀ (q : Q) (c : P), c ∈ C → ∀ κ ∈ K,
      f ((q : G) * x * (c : G) * κ) = σ q (φ c) := by
    intro q c hc κ hκ
    have h : Ω ((q : G) * x * (c : G) * κ) := ⟨q, c, hc, κ, hκ, rfl⟩
    simp only [f]
    rw [dite_eq_left h]
    obtain ⟨hc', κ', hκ', e⟩ := h.choose_spec.choose_spec
    exact wd _ _ _ _ hc' hc κ' hκ' κ hκ e.symm
  have h0 : ∀ g, ¬ Ω g → f g = 0 := fun g h => dif_neg h
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · intro q g
    by_cases h : Ω g
    · obtain ⟨q₁, c, hc, κ, hκ, rfl⟩ := h
      have e : (q : G) * ((q₁ : G) * x * (c : G) * κ)
          = ((q * q₁ : Q) : G) * x * (c : G) * κ := by
        simp only [Subgroup.coe_mul]; group
      rw [e, hf _ _ hc _ hκ, hf _ _ hc _ hκ, map_mul, Module.End.mul_apply]
    · have h' : ¬ Ω ((q : G) * g) := by
        rintro ⟨q₁, c, hc, κ, hκ, e⟩
        refine h ⟨q⁻¹ * q₁, c, hc, κ, hκ, ?_⟩
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        calc g = (q : G)⁻¹ * ((q : G) * g) := by group
          _ = _ := by rw [e]; group
      rw [h0 _ h, h0 _ h', map_zero]
  · intro g κ hκ
    by_cases h : Ω g
    · obtain ⟨q₁, c, hc, κ₁, hκ₁, rfl⟩ := h
      have e : (q₁ : G) * x * (c : G) * κ₁ * κ = (q₁ : G) * x * (c : G) * (κ₁ * κ) := by group
      rw [e, hf _ _ hc _ (K.mul_mem hκ₁ hκ), hf _ _ hc _ hκ₁]
    · have h' : ¬ Ω (g * κ) := by
        rintro ⟨q₁, c, hc, κ₁, hκ₁, e⟩
        refine h ⟨q₁, c, hc, κ₁ * κ⁻¹, K.mul_mem hκ₁ (K.inv_mem hκ), ?_⟩
        calc g = (g * κ) * κ⁻¹ := by group
          _ = _ := by rw [e]; group
      rw [h0 _ h, h0 _ h']
  · intro p
    by_cases h : Ω (x * (p : G))
    · obtain ⟨q, c, hc, κ, hκ, e⟩ := h
      rw [e, hf _ _ hc _ hκ]
      exact (h1 c hc κ hκ q p e.symm).symm
    · rw [h0 _ h]
      by_contra hne
      obtain ⟨c, hc, q, e⟩ := h2 p (fun hz => hne hz.symm)
      exact h ⟨q, c, hc, 1, K.one_mem, by rw [e, mul_one]⟩
  · intro g hg
    by_contra hcon
    refine hg (h0 g ?_)
    rintro ⟨q, c, hc, κ, hκ, e⟩
    exact hcon ⟨q, c, hc, κ, hκ, e⟩

end GlobalTheory.CompanionTheory.BZRes.TwoOrbit
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

theorem _root_.GlobalTheory.T.inf_not_in_codim_one_submodule : ∀ {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (T : Submodule ℂ V), Module.rank ℂ (V ⧸ T) ≤ 1 → ∀ A C : Subrepresentation ρ, (A ⊔ C).toSubmodule ⊓ T ≤ A.toSubmodule ⊓ T ⊔ C.toSubmodule ⊓ T → ¬ A.toSubmodule ≤ T → ¬ C.toSubmodule ≤ T → ¬ (A ⊓ C).toSubmodule ≤ T := by
  first | exact @GlobalTheory.CompanionTheory.RgGuCore.gen_core_meet | exact GlobalTheory.CompanionTheory.RgGuCore.gen_core_meet | (intros; apply GlobalTheory.CompanionTheory.RgGuCore.gen_core_meet <;> assumption)
end

section

open MeasureTheory Topology
open scoped ENNReal NNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.FactS.OpenFactor

section Generic

variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]

theorem map_comap_of_carried {e : Y → X} (he : MeasurableEmbedding e) {μ : Measure X}
    (hμ : μ (Set.range e)ᶜ = 0) : (μ.comap e).map e = μ := by
  rw [he.map_comap]
  exact Measure.restrict_eq_self_of_ae_mem (mem_ae_iff.mpr hμ)

theorem comap_invariant {e : Y → X} (he : MeasurableEmbedding e) {a : X → X} {a' : Y → Y}
    (ha : Measurable a) (ha' : Measurable a') (hcomm : ∀ y, e (a' y) = a (e y)) {μ : Measure X}
    (hμ : μ (Set.range e)ᶜ = 0) (hinv : μ.map a = μ) : (μ.comap e).map a' = μ.comap e := by
  have hν := map_comap_of_carried he hμ
  have h2 : ((μ.comap e).map a').map e = μ := by
    rw [Measure.map_map he.measurable ha']
    have h3 : e ∘ a' = a ∘ e := funext hcomm
    rw [h3, ← Measure.map_map ha he.measurable, hν, hinv]
  have h4 := he.comap_map ((μ.comap e).map a')
  rw [h2] at h4
  exact h4.symm

theorem lintegral_comap_of_carried {e : Y → X} (he : MeasurableEmbedding e) {μ : Measure X}
    (hμ : μ (Set.range e)ᶜ = 0) (G : X → ℝ≥0∞) :
    ∫⁻ y, G (e y) ∂(μ.comap e) = ∫⁻ x, G x ∂μ := by
  rw [← he.lintegral_map, map_comap_of_carried he hμ]

theorem comap_ne_zero_of_carried {e : Y → X} (he : MeasurableEmbedding e) {μ : Measure X}
    (hμ : μ (Set.range e)ᶜ = 0) (h0 : μ ≠ 0) : μ.comap e ≠ 0 := by
  intro h
  have h1 := map_comap_of_carried he hμ
  rw [h, Measure.map_zero] at h1
  exact h0 h1.symm

theorem comap_finite_compacts [TopologicalSpace X] [TopologicalSpace Y] {e : Y → X}
    (he : MeasurableEmbedding e) (hc : Continuous e) {S : Set X} (hS : ∀ y, e y ∈ S)
    {μ : Measure X} (hfin : ∀ K, IsCompact K → K ⊆ S → μ K < ⊤) :
    IsFiniteMeasureOnCompacts (μ.comap e) :=
  ⟨fun K hK => by
    rw [he.comap_apply]
    exact hfin _ (hK.image hc) (by rintro _ ⟨y, -, rfl⟩; exact hS y)⟩

end Generic

theorem prod_factor_open : ∀ {ι : Type} [Fintype ι]
  {G₀ : Type} [Group G₀] [TopologicalSpace G₀] [IsTopologicalGroup G₀] [T2Space G₀]
  [LocallyCompactSpace G₀] [SecondCountableTopology G₀]
  {G : ι → Type} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)]
  [∀ i, T2Space (G i)] [∀ i, LocallyCompactSpace (G i)] [∀ i, SecondCountableTopology (G i)]
  {W₀ : Type} [TopologicalSpace W₀] [T2Space W₀] [LocallyCompactSpace W₀]
  [SecondCountableTopology W₀] [MeasurableSpace W₀] [BorelSpace W₀]
  {W : ι → Type} [∀ i, TopologicalSpace (W i)] [∀ i, T2Space (W i)] [∀ i, LocallyCompactSpace (W i)]
  [∀ i, SecondCountableTopology (W i)] [∀ i, MeasurableSpace (W i)] [∀ i, BorelSpace (W i)]
  (a₀ : G₀ → W₀ → W₀) (a : ∀ i, G i → W i → W i),
  (Continuous fun p : G₀ × W₀ => a₀ p.1 p.2) → (∀ x, a₀ 1 x = x) →
  (∀ g h x, a₀ (g * h) x = a₀ g (a₀ h x)) →
  (∀ i, Continuous fun p : G i × W i => a i p.1 p.2) → (∀ i x, a i 1 x = x) →
  (∀ i g h x, a i (g * h) x = a i g (a i h x)) →
  ∀ (U₀ : Set W₀) (U : ∀ i, Set (W i)), IsOpen U₀ → (∀ i, IsOpen (U i)) →
  (∀ g, ∀ x ∈ U₀, a₀ g x ∈ U₀) → (∀ i g, ∀ x ∈ U i, a i g x ∈ U i) →
  ∀ (Z₀ : Set W₀) (Z : ∀ i, Set (W i)), IsClosed Z₀ → (∀ i, IsClosed (Z i)) →
  (∀ g, ∀ x ∈ Z₀, a₀ g x ∈ Z₀) → (∀ i g, ∀ x ∈ Z i, a i g x ∈ Z i) →
  (∀ x ∈ Z₀ ∩ U₀, ∀ y ∈ Z₀ ∩ U₀, ∃ g, a₀ g x = y) →
  (∀ i, ∀ x ∈ Z i ∩ U i, ∀ y ∈ Z i ∩ U i, ∃ g, a i g x = y) →
  ∀ (m₀ : Measure W₀) (m : ∀ i, Measure (W i)),
  (∀ K, IsCompact K → K ⊆ U₀ → m₀ K < ⊤) → (∀ i K, IsCompact K → K ⊆ U i → m i K < ⊤) →
  (∀ g, m₀.map (a₀ g) = m₀) → (∀ i g, (m i).map (a i g) = m i) →
  m₀ (Z₀ ∩ U₀)ᶜ = 0 → (∀ i, m i (Z i ∩ U i)ᶜ = 0) →
  ((Z₀ ∩ U₀).Nonempty → m₀ ≠ 0) → (∀ i, (Z i ∩ U i).Nonempty → m i ≠ 0) →
  ∀ (P : Measure (W₀ × ∀ i, W i)), IsFiniteMeasureOnCompacts P →
  (∀ (g₀ : G₀) (g : ∀ i, G i),
      P.map (fun x => (a₀ g₀ x.1, fun i => a i (g i) (x.2 i))) = P) →
  P ((Z₀ ∩ U₀) ×ˢ Set.univ.pi fun i => Z i ∩ U i)ᶜ = 0 →
  ∃ c : ℝ≥0, ∀ (f₀ : W₀ → ℝ≥0∞) (f : ∀ i, W i → ℝ≥0∞), Measurable f₀ →
      (∀ i, Measurable (f i)) →
      ∫⁻ x, f₀ x.1 * ∏ i, f i (x.2 i) ∂P =
        (c : ℝ≥0∞) * ((∫⁻ x, f₀ x ∂m₀) * ∏ i, ∫⁻ x, f i x ∂(m i)) := by
  intro ι _ G₀ _ _ _ _ _ _ G _ _ _ _ _ _ W₀ _ _ _ _ _ _ W _ _ _ _ _ _
    a₀ a hc₀ h1₀ hm₀ hc h1 hm U₀ U hU₀ hU hsU₀ hsU Z₀ Z hZ₀ hZ hs₀ hs ht₀ ht m₀ m hfin₀ hfin
    hi₀ hi hz₀ hz hn₀ hn P hPc hP hPZ
  classical
  haveI : LocallyCompactSpace ↥U₀ := hU₀.locallyCompactSpace
  haveI : ∀ i, LocallyCompactSpace ↥(U i) := fun i => (hU i).locallyCompactSpace
  have hmeas₀ : ∀ g, Measurable (a₀ g) := fun g =>
    (hc₀.comp (Continuous.prodMk_right g)).measurable
  have hmeas : ∀ i g, Measurable (a i g) := fun i g =>
    ((hc i).comp (Continuous.prodMk_right g)).measurable
  let b₀ : G₀ → ↥U₀ → ↥U₀ := fun g x => ⟨a₀ g x.1, hsU₀ g x.1 x.2⟩
  let b : ∀ i, G i → ↥(U i) → ↥(U i) := fun i g x => ⟨a i g x.1, hsU i g x.1 x.2⟩
  let E : (↥U₀ × ∀ i, ↥(U i)) → W₀ × ∀ i, W i := Prod.map Subtype.val fun z i => (z i).1
  have he₀ : MeasurableEmbedding (Subtype.val : ↥U₀ → W₀) :=
    MeasurableEmbedding.subtype_coe hU₀.measurableSet
  have he : ∀ i, MeasurableEmbedding (Subtype.val : ↥(U i) → W i) := fun i =>
    MeasurableEmbedding.subtype_coe (hU i).measurableSet
  have hEo : IsOpenEmbedding E :=
    hU₀.isOpenEmbedding_subtypeVal.prodMap
      (IsOpenEmbedding.piMap fun i => (hU i).isOpenEmbedding_subtypeVal)
  have hE : MeasurableEmbedding E := hEo.measurableEmbedding
  have hcar₀ : m₀ (Set.range (Subtype.val : ↥U₀ → W₀))ᶜ = 0 := by
    refine measure_mono_null (Set.compl_subset_compl.mpr ?_) hz₀
    rw [Subtype.range_coe]
    exact Set.inter_subset_right
  have hcar : ∀ i, m i (Set.range (Subtype.val : ↥(U i) → W i))ᶜ = 0 := fun i => by
    refine measure_mono_null (Set.compl_subset_compl.mpr ?_) (hz i)
    rw [Subtype.range_coe]
    exact Set.inter_subset_right
  have hcarP : P (Set.range E)ᶜ = 0 := by
    refine measure_mono_null (Set.compl_subset_compl.mpr ?_) hPZ
    rintro ⟨x, z⟩ ⟨h₀, hz'⟩
    exact ⟨(⟨x, h₀.2⟩, fun i => ⟨z i, (hz' i (Set.mem_univ i)).2⟩), rfl⟩
  haveI : IsFiniteMeasureOnCompacts (m₀.comap (Subtype.val : ↥U₀ → W₀)) :=
    comap_finite_compacts he₀ continuous_subtype_val (fun y => y.2) (hfin₀)
  haveI : ∀ i, IsFiniteMeasureOnCompacts ((m i).comap (Subtype.val : ↥(U i) → W i)) := fun i =>
    comap_finite_compacts (he i) continuous_subtype_val (fun y => y.2) (hfin i)
  haveI : IsFiniteMeasureOnCompacts (P.comap E) :=
    comap_finite_compacts hE hEo.continuous (S := Set.univ) (fun _ => Set.mem_univ _)
      (fun K hK _ => hK.measure_lt_top)
  have hcb₀ : Continuous fun p : G₀ × ↥U₀ => b₀ p.1 p.2 :=
    Continuous.subtype_mk (hc₀.comp (continuous_fst.prodMk
      (continuous_subtype_val.comp continuous_snd))) _
  have hcb : ∀ i, Continuous fun p : G i × ↥(U i) => b i p.1 p.2 := fun i =>
    Continuous.subtype_mk ((hc i).comp (continuous_fst.prodMk
      (continuous_subtype_val.comp continuous_snd))) _
  have hmb₀ : ∀ g, Measurable (b₀ g) := fun g =>
    (hcb₀.comp (Continuous.prodMk_right g)).measurable
  have hmb : ∀ i g, Measurable (b i g) := fun i g =>
    ((hcb i).comp (Continuous.prodMk_right g)).measurable
  obtain ⟨c, hcf⟩ := prod_factor (G₀ := G₀) (G := G) (W₀ := ↥U₀) (W := fun i => ↥(U i)) b₀ b
    hcb₀ (fun x => Subtype.ext (h1₀ x.1)) (fun g h x => Subtype.ext (hm₀ g h x.1))
    hcb (fun i x => Subtype.ext (h1 i x.1)) (fun i g h x => Subtype.ext (hm i g h x.1))
    (Subtype.val ⁻¹' Z₀) (fun i => Subtype.val ⁻¹' Z i)
    (hZ₀.preimage continuous_subtype_val) (fun i => (hZ i).preimage continuous_subtype_val)
    (fun g x hx => hs₀ g x.1 hx) (fun i g x hx => hs i g x.1 hx)
    (fun x hx y hy => by
      obtain ⟨g, hg⟩ := ht₀ x.1 ⟨hx, x.2⟩ y.1 ⟨hy, y.2⟩
      exact ⟨g, Subtype.ext hg⟩)
    (fun i x hx y hy => by
      obtain ⟨g, hg⟩ := ht i x.1 ⟨hx, x.2⟩ y.1 ⟨hy, y.2⟩
      exact ⟨g, Subtype.ext hg⟩)
    (m₀.comap Subtype.val) (fun i => (m i).comap Subtype.val)
    (fun g => comap_invariant he₀ (hmeas₀ g) (hmb₀ g) (fun _ => rfl) hcar₀ (hi₀ g))
    (fun i g => comap_invariant (he i) (hmeas i g) (hmb i g) (fun _ => rfl) (hcar i) (hi i g))
    (by
      rw [he₀.comap_apply]
      refine measure_mono_null ?_ hz₀
      rintro _ ⟨y, hy, rfl⟩ hmem
      exact hy hmem.1)
    (fun i => by
      rw [(he i).comap_apply]
      refine measure_mono_null ?_ (hz i)
      rintro _ ⟨y, hy, rfl⟩ hmem
      exact hy hmem.1)
    (fun ⟨x, hx⟩ => comap_ne_zero_of_carried he₀ hcar₀ (hn₀ ⟨x.1, hx, x.2⟩))
    (fun i ⟨x, hx⟩ => comap_ne_zero_of_carried (he i) (hcar i) (hn i ⟨x.1, hx, x.2⟩))
    (P.comap E)
    (fun g₀ g => comap_invariant hE
      (a := fun x => (a₀ g₀ x.1, fun i => a i (g i) (x.2 i)))
      ((hmeas₀ g₀).comp measurable_fst |>.prodMk (Measurable.of_eval fun i =>
        (hmeas i (g i)).comp ((measurable_pi_apply i).comp measurable_snd)))
      ((hmb₀ g₀).comp measurable_fst |>.prodMk (Measurable.of_eval fun i =>
        (hmb i (g i)).comp ((measurable_pi_apply i).comp measurable_snd)))
      (fun _ => rfl) hcarP (hP g₀ g))
    (by
      rw [hE.comap_apply]
      refine measure_mono_null ?_ hPZ
      rintro _ ⟨y, hy, rfl⟩ hmem
      exact hy ⟨hmem.1.1, fun i _ => (hmem.2 i (Set.mem_univ i)).1⟩)
  refine ⟨c, fun f₀ f hf₀ hf => ?_⟩
  have h := hcf (fun x => f₀ x.1) (fun i x => f i x.1) (hf₀.comp measurable_subtype_coe)
    (fun i => (hf i).comp measurable_subtype_coe)
  have hL := lintegral_comap_of_carried hE hcarP fun x => f₀ x.1 * ∏ i, f i (x.2 i)
  have hL₀ := lintegral_comap_of_carried he₀ hcar₀ f₀
  have hLi := fun i => lintegral_comap_of_carried (he i) (hcar i) (f i)
  rw [← hL, ← hL₀]
  simp only [← hLi]
  exact h

end GlobalTheory.CompanionTheory.SW.FactS.OpenFactor
end
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

theorem _root_.GlobalTheory.T.strict_anti_of_two_exceptions : ∀ (l : ℕ) (hl : 3 ≤ l) (w : Fin l → ℕ) (hw : ∀ a, w a < l) (i j : Fin l) (hi : w i = 0) (hj : w j = l - 1) (h1 : ∀ a b, a < b → a ≠ i → b ≠ i → w b < w a) (h2 : ∀ a b, a < b → a ≠ j → b ≠ j → w b < w a), StrictAnti w := by
  first | exact @GlobalTheory.CompanionTheory.Segments.shufcomb | exact GlobalTheory.CompanionTheory.Segments.shufcomb | (intros; apply GlobalTheory.CompanionTheory.Segments.shufcomb <;> assumption)
end
