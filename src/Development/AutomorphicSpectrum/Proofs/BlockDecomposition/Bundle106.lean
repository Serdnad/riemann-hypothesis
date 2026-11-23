module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle016
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle088
public import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerPolynomialFiltration
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle001
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Separation.CompletelyRegular
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsDPMorphismBot
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.InstAddCommGroup
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle001
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.XSmulSucc
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle101
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle089
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.SpecialFunctions.Exponential

@[expose] public section

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical
noncomputable section

namespace GlobalTheory.CompanionTheory.Mass.MeanV

theorem isStdV_measure_singleton_zero : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (lam : Measure (Fv F v)), IsStdV v lam → lam {0} = 0 := by
  intro F _ _ v lam hstd
  obtain ⟨hH, h1⟩ := hstd
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI : CharZero (Fv F v) :=
    charZero_of_injective_algebraMap (algebraMap F (Fv F v)).injective
  have hs : ∀ x : Fv F v, lam {x} = lam {0} := by
    intro x
    rw [← measure_preimage_add lam x ({x} : Set (Fv F v))]
    congr 1
    ext y
    simp
  by_contra h0
  obtain ⟨N, hN⟩ := ENNReal.exists_nat_mul_gt h0 ENNReal.one_ne_top
  have hcard : ((Finset.range N).image (fun n : ℕ => (n : Fv F v))).card = N := by
    rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
  have hsum : lam (((Finset.range N).image (fun n : ℕ => (n : Fv F v)) : Finset (Fv F v)) : Set (Fv F v))
      = N * lam {0} := by
    rw [← sum_measure_singleton, Finset.sum_congr rfl (fun x _ => hs x), Finset.sum_const, hcard,
      nsmul_eq_mul]
  have hsub : (((Finset.range N).image (fun n : ℕ => (n : Fv F v)) : Finset (Fv F v)) : Set (Fv F v))
      ⊆ (v.adicCompletionIntegers F : Set (Fv F v)) := by
    intro x hx
    simp only [Finset.coe_image, Set.mem_image] at hx
    obtain ⟨n, -, rfl⟩ := hx
    exact natCast_mem (v.adicCompletionIntegers F) n
  have hle := measure_mono (μ := lam) hsub
  rw [hsum, h1] at hle
  exact absurd hN (not_lt.2 hle)

end GlobalTheory.CompanionTheory.Mass.MeanV

end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypMass

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep

def scalT {K : Type} [Mul K] {n M : ℕ} (c : K) (y : Fin n → Fin M → K) : Fin n → Fin M → K :=
  fun p i => c * y p i

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def intK {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) : Set (Fv F v ⊗[F] E) :=
  {x | ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr x k ∈ v.adicCompletionIntegers F}

def qv (v : HeightOneSpectrum (𝓞 F)) : ℝ≥0 := (Ideal.absNorm v.asIdeal : ℝ≥0)


variable (E) in
def zetaV (v : HeightOneSpectrum (𝓞 F)) (s : ℕ) : ℝ :=
  open Classical in
  if IsField (Fv F v ⊗[F] E) then (1 - ((qv v : ℝ) ^ (2 * s))⁻¹)⁻¹ else ((1 - ((qv v : ℝ) ^ s)⁻¹)⁻¹) ^ 2

def IsContent (σ : E →ₐ[F] E) {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) {ι : Type}
    (c : ι → Fv F v ⊗[F] E) (w : ι → ℕ) : Prop :=
  (∀ i, IsUnit (c i) ∧ c i ∈ intK b v) ∧
  (∀ i (lam : Measure (Fv F v)), IsStdV v lam →
    (coordK (Fv F v) b lam).map (fun x => c i * x) = (qv v ^ w i) • coordK (Fv F v) b lam) ∧
  (∀ i, ∃ t : Fv F v, algebraMap (Fv F v) (Fv F v ⊗[F] E) t = sigR (Fv F v) σ (c i) * c i ∧
    ‖t‖ = ((qv v : ℝ) ^ w i)⁻¹) ∧
  (∀ x ∈ intK b v, IsUnit x → ∃ i, ∃ u ∈ intK b v, ∃ u' ∈ intK b v, u * u' = 1 ∧ x = c i * u) ∧
  (∀ i j, ∀ u ∈ intK b v, ∀ u' ∈ intK b v, u * u' = 1 → c i = c j * u → i = j)

end Adelic

end GlobalTheory.CompanionTheory.WeilSiegel.HypMass
end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Equi.InfScale

open GlobalTheory.CompanionTheory.SW.LocInf

theorem eInf_theta {F : Type} [Field F] [NumberField F] (h : IsTotallyReal F) (θ : ℝ →+* Ainf F) (t : ℝ)
    (w : InfinitePlace F) : eInf F h (θ t) w = t := by
  have key : ((Pi.evalRingHom (fun _ : InfinitePlace F => ℝ) w).comp
      ((eInf F h).toRingHom.comp θ)) = RingHom.id ℝ := Subsingleton.elim _ _
  exact congrArg (fun f : ℝ →+* ℝ => f t) key

theorem finrank_fun_places (F : Type) [Field F] [NumberField F] (h : IsTotallyReal F) :
    Module.finrank ℝ (InfinitePlace F → ℝ) = Module.finrank ℚ F := by
  haveI := h
  rw [Module.finrank_fintype_fun_eq_card, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyReal.nrComplexPlaces_eq_zero, add_zero, IsTotallyReal.finrank]

theorem map_theta_mul {F : Type} [Field F] [NumberField F] (h : IsTotallyReal F) (θ : ℝ →+* Ainf F)
    (li : Measure (Ainf F)) [li.IsAddHaarMeasure] {ε : ℝ} (hε : 0 < ε) :
    Measure.map (fun y : Ainf F => θ ε * y) li =
      ENNReal.ofReal ((ε ^ Module.finrank ℚ F)⁻¹) • li := by
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  have hc : Continuous (eInf F h) := continuous_eInf F h
  have hcs : Continuous (eInf F h).symm := continuous_eInf_symm F h
  have hm : Measurable (eInf F h) := hc.measurable
  have hms : Measurable (eInf F h).symm := hcs.measurable
  have hL : Measurable (fun x : InfinitePlace F → ℝ => ε • x) := (continuous_const_smul ε).measurable
  have hθ : (fun y : Ainf F => θ ε * y) = (eInf F h).symm ∘ (fun x => ε • x) ∘ (eInf F h) := by
    funext y
    apply (eInf F h).injective
    simp only [Function.comp_apply, RingEquiv.apply_symm_apply, map_mul]
    funext w
    rw [Pi.mul_apply, Pi.smul_apply, eInf_theta h θ ε w, smul_eq_mul]
  haveI : (Measure.map (eInf F h) li).IsAddHaarMeasure :=
    AddEquiv.isAddHaarMeasure_map li (eInf F h).toAddEquiv hc hcs
  have hdet : LinearMap.det (ε • (LinearMap.id : (InfinitePlace F → ℝ) →ₗ[ℝ] (InfinitePlace F → ℝ))) ≠ 0 := by
    rw [LinearMap.det_smul, LinearMap.det_id, mul_one]
    exact pow_ne_zero _ hε.ne'
  have hmapL := Measure.map_linearMap_addHaar_eq_smul_addHaar (Measure.map (eInf F h) li) hdet
  rw [LinearMap.det_smul, LinearMap.det_id, mul_one, finrank_fun_places F h] at hmapL
  have hcoe : (⇑(ε • (LinearMap.id : (InfinitePlace F → ℝ) →ₗ[ℝ] (InfinitePlace F → ℝ)))) =
      fun x => ε • x := by
    funext x
    simp
  rw [hcoe] at hmapL
  have hid : (eInf F h).symm ∘ (eInf F h) = id := by
    funext x
    simp
  rw [hθ, ← Measure.map_map hms (hL.comp hm), ← Measure.map_map hL hm, hmapL, Measure.map_smul,
    Measure.map_map hms hm, hid, Measure.map_id, abs_of_pos (inv_pos.mpr (pow_pos hε _))]
  exact hms.aemeasurable

theorem pi_const_smul {X : Type} [MeasurableSpace X] (ι : Type) [Fintype ι] (μ : Measure X) [SigmaFinite μ]
    (c : ENNReal) [SigmaFinite (c • μ)] :
    (Measure.pi fun _ : ι => c • μ) = c ^ Fintype.card ι • Measure.pi fun _ : ι => μ := by
  refine Measure.pi_eq fun s _ => ?_
  simp only [Measure.smul_apply, smul_eq_mul, Measure.pi_pi, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ]

theorem map_theta_mul_pi : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ θ : ℝ →+* Ainf F, Continuous θ →
    ∀ li : Measure (Ainf F), li.IsAddHaarMeasure → ∀ (ι : Type) [Fintype ι] (ε : ℝ), 0 < ε →
    Measure.map (fun (y : ι → Ainf F) (i : ι) => θ ε * y i) (Measure.pi fun _ => li) =
      ENNReal.ofReal ((ε ^ (Module.finrank ℚ F * Fintype.card ι))⁻¹) • Measure.pi fun _ => li := by
  intro F _ _ h θ _ li _ ι _ ε hε
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  have h1 := map_theta_mul h θ li hε
  have hc : Continuous (eInf F h) := continuous_eInf F h
  have hcs : Continuous (eInf F h).symm := continuous_eInf_symm F h
  have hm : Measurable (eInf F h) := hc.measurable
  have hms : Measurable (eInf F h).symm := hcs.measurable
  haveI : (Measure.map (eInf F h) li).IsAddHaarMeasure :=
    AddEquiv.isAddHaarMeasure_map li (eInf F h).toAddEquiv hc hcs
  haveI : SigmaFinite (Measure.map (eInf F h) li) := Measure.IsAddHaarMeasure.sigmaFinite _
  let me : (InfinitePlace F → ℝ) ≃ᵐ Ainf F :=
    { toEquiv := (eInf F h).symm.toEquiv
      measurable_toFun := hms
      measurable_invFun := hm }
  have hme : (⇑me : (InfinitePlace F → ℝ) → Ainf F) = (eInf F h).symm := rfl
  have hli : Measure.map me (Measure.map (eInf F h) li) = li := by
    rw [Measure.map_map me.measurable hm, hme]
    have hid : ((eInf F h).symm ∘ (eInf F h)) = id := by
      funext x
      simp
    rw [hid, Measure.map_id]
  haveI : SigmaFinite li := by
    rw [← hli]
    exact MeasurableEquiv.sigmaFinite_map me
  haveI hsf : SigmaFinite (ENNReal.ofReal ((ε ^ Module.finrank ℚ F)⁻¹) • li) := by
    have hle : ENNReal.ofReal ((ε ^ Module.finrank ℚ F)⁻¹) • li =
        ((ε ^ Module.finrank ℚ F)⁻¹).toNNReal • li := rfl
    rw [hle]
    infer_instance
  have hmeas : Measurable (fun y : Ainf F => θ ε * y) := by
    have hθ' : (fun y : Ainf F => θ ε * y) = (eInf F h).symm ∘ (fun x => ε • x) ∘ (eInf F h) := by
      funext y
      apply (eInf F h).injective
      simp only [Function.comp_apply, RingEquiv.apply_symm_apply, map_mul]
      funext w
      rw [Pi.mul_apply, Pi.smul_apply, eInf_theta h θ ε w, smul_eq_mul]
    rw [hθ']
    exact hms.comp ((continuous_const_smul ε).measurable.comp hm)
  have h2 := Measure.pi_map_pi (μ := fun _ : ι => li) (f := fun _ y => θ ε * y)
    (hμ := fun _ => by
      show SigmaFinite (Measure.map (fun y : Ainf F => θ ε * y) li)
      rw [h1]
      exact hsf)
    (fun _ => hmeas.aemeasurable)
  rw [h2]
  simp only [h1]
  rw [pi_const_smul ι li _, ← ENNReal.ofReal_pow (inv_nonneg.mpr (pow_nonneg hε.le _)), inv_pow, ← pow_mul]

end GlobalTheory.CompanionTheory.Equi.InfScale

end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Equi

open GlobalTheory.CompanionTheory.SW.RealCoord

section Domain

variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]

def infToMixed (y : Ainf F) : mixedEmbedding.mixedSpace F := toMixed F (coord F y)

theorem infToMixed_add (x y : Ainf F) : infToMixed F (x + y) = infToMixed F x + infToMixed F y := by
  show toMixed F (coord F (x + y)) = toMixed F (coord F x) + toMixed F (coord F y)
  rw [map_add (f := _), toMixed_add]

theorem infToMixed_algebraMap (x : F) :
    infToMixed F (algebraMap F (Ainf F) x) = mixedEmbedding F x := toMixed_coord_algebraMap F x

theorem infToMixed_sub (x y : Ainf F) : infToMixed F (x - y) = infToMixed F x - infToMixed F y := by
  rw [eq_sub_iff_add_eq, ← infToMixed_add, sub_add_cancel]

theorem measurable_infToMixed : Measurable (infToMixed F) := (measurePreserving_toMixed F).measurable.comp (coord_measurable F)

def infDomain : Set (Ainf F) :=
  infToMixed F ⁻¹' ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F)

theorem measurableSet_infDomain : MeasurableSet (infDomain F) := measurable_infToMixed F (ZSpan.fundamentalDomain_measurableSet (mixedEmbedding.latticeBasis F))

theorem exists_mem_lattice {x : mixedEmbedding.mixedSpace F}
    (hx : x ∈ Submodule.span ℤ (Set.range (mixedEmbedding.latticeBasis F))) :
    ∃ a : 𝓞 F, mixedEmbedding F (a : F) = x := by
  rw [mixedEmbedding.mem_span_latticeBasis F] at hx
  obtain ⟨a, rfl⟩ := hx
  exact ⟨a, rfl⟩

theorem mem_lattice (a : 𝓞 F) :
    mixedEmbedding F (a : F) ∈ Submodule.span ℤ (Set.range (mixedEmbedding.latticeBasis F)) := (mixedEmbedding.mem_span_latticeBasis F).2 ⟨a, rfl⟩

theorem existsUnique_sub_mem_infDomain (y : Ainf F) :
    ∃! a : 𝓞 F, y - algebraMap F (Ainf F) (a : F) ∈ infDomain F := by
  obtain ⟨v, hv, huniq⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain (mixedEmbedding.latticeBasis F)
    (infToMixed F y)
  obtain ⟨a, ha⟩ := exists_mem_lattice F (Submodule.neg_mem _ v.2)
  have key : ∀ b : 𝓞 F, infToMixed F (y - algebraMap F (Ainf F) (b : F)) =
      -mixedEmbedding F (b : F) + infToMixed F y := fun b => by
    rw [infToMixed_sub, infToMixed_algebraMap]
    abel
  refine ⟨a, ?_, fun b hb => ?_⟩
  · show infToMixed F (y - algebraMap F (Ainf F) (a : F)) ∈ ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F)
    rw [key, ha, neg_neg]
    exact hv
  · have hw := huniq ⟨-mixedEmbedding F (b : F), neg_mem (mem_lattice F b)⟩ (by
      show -mixedEmbedding F (b : F) + infToMixed F y ∈ ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F)
      rw [← key]
      exact hb)
    have hb' : mixedEmbedding F (b : F) = mixedEmbedding F (a : F) := by
      rw [ha]
      have := congrArg Subtype.val hw
      simp only at this
      rw [← this, neg_neg]
    exact RingOfIntegers.ext (mixedEmbedding_injective F hb')

theorem exists_isCompact_superset_infDomain :
    ∃ K₀ : Set (Ainf F), IsCompact K₀ ∧ infDomain F ⊆ K₀ := by
  let g : mixedEmbedding.mixedSpace F → (InfinitePlace F → ℝ) := fun x w => x.1 ⟨w, IsTotallyReal.isReal w⟩
  have hg : Continuous g := continuous_pi fun w => (continuous_apply _).comp continuous_fst
  have hC : IsCompact (closure (ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F))) :=
    (ZSpan.fundamentalDomain_isBounded _).isCompact_closure
  refine ⟨coord F ⁻¹' (g '' closure (ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F))), ?_, ?_⟩
  · rw [← coordHomeo_coe]
    exact (coordHomeo F).isCompact_preimage.2 (hC.image hg)
  · intro y hy
    exact ⟨infToMixed F y, subset_closure hy, rfl⟩

theorem measure_infDomain (li : Measure (Ainf F)) (hl : IsStdInf li) : li (infDomain F) = 1 := by
  have hfd := ZSpan.fundamentalDomain_measurableSet (mixedEmbedding.latticeBasis F)
  have hmeas := (measurePreserving_toMixed F).measurable hfd
  have hpos : 0 < Real.sqrt |(discr F : ℝ)| :=
    Real.sqrt_pos.2 (abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero F)))
  have hv : volume (ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F)) =
      ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|) := by
    rw [mixedEmbedding.volume_fundamentalDomain_latticeBasis, IsTotallyReal.nrComplexPlaces_eq_zero, pow_zero,
      one_mul, ← ENNReal.ofReal_coe_nnreal, Real.coe_sqrt, coe_nnnorm, Int.norm_eq_abs]
  calc li (infDomain F)
      = (li.map (coord F)) (toMixed F ⁻¹' ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F)) :=
        (Measure.map_apply (coord_measurable F) hmeas).symm
    _ = ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|)⁻¹ *
          volume (toMixed F ⁻¹' ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F)) := by
        rw [map_coord_eq F li hl, Measure.smul_apply, smul_eq_mul]
    _ = ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|)⁻¹ *
          volume (ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F)) := by
        rw [(measurePreserving_toMixed F).measure_preimage hfd.nullMeasurableSet]
    _ = 1 := by
        rw [hv, ← ENNReal.ofReal_mul (inv_nonneg.2 (Real.sqrt_nonneg _)), inv_mul_cancel₀ hpos.ne',
          ENNReal.ofReal_one]

end Domain

theorem exists_bounded_infDomain : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F →
    ∀ li : Measure (Ainf F), IsStdInf li → ∃ D K₀ : Set (Ainf F), MeasurableSet D ∧ IsCompact K₀ ∧ D ⊆ K₀ ∧
      li D = 1 ∧ ∀ y : Ainf F, ∃! a : 𝓞 F, y - algebraMap F (Ainf F) (a : F) ∈ D := by
  intro F _ _ hTR li hl
  have := hTR
  obtain ⟨K₀, hK₀, hsub⟩ := exists_isCompact_superset_infDomain F
  exact ⟨infDomain F, K₀, measurableSet_infDomain F, hK₀, hsub, measure_infDomain F li hl,
    existsUnique_sub_mem_infDomain F⟩

end GlobalTheory.CompanionTheory.Equi

end
end

section

open NumberField GlobalTheory.CuspRep

theorem _root_.GlobalTheory.T.compact_adelic_integral_denominator : ∀ (E : Type) [Field E] [NumberField E] (Q : Set (Af E)), IsCompact Q →
    ∃ D : ℕ, D ≠ 0 ∧ ∀ x : E, algebraMap E (Af E) x ∈ Q → ∃ r : 𝓞 E, (r : E) = D * x := by
  first | exact @GlobalTheory.CompanionTheory.AdeleDen.exists_common_denominator | exact GlobalTheory.CompanionTheory.AdeleDen.exists_common_denominator | (intros; apply GlobalTheory.CompanionTheory.AdeleDen.exists_common_denominator <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

theorem _root_.GlobalTheory.T.divided_power_polynomial_filtration : ∀ {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (Q : PDPoly B) (η : DividedPowers (Q.ext J)), Q.IsStd δ η → (∀ a c, fil δ a * fil δ c ≤ fil δ (a + c)) ∧ (∀ a c, a ≤ c → fil δ c ≤ fil δ a) ∧ fil δ 0 = ⊤ ∧ ∀ (r : ℕ) (z : Q.P), z ∈ fil η r ↔ ∀ k, Q.e.repr z k ∈ fil δ (r - k) := by
  first | exact @GlobalTheory.CompanionTheory.PDFil.fil_pdPoly | exact GlobalTheory.CompanionTheory.PDFil.fil_pdPoly | (intros; apply GlobalTheory.CompanionTheory.PDFil.fil_pdPoly <;> assumption)
end

section

open Matrix Topology Filter

noncomputable section

namespace GlobalTheory.CompanionTheory.LieStable

open scoped Matrix.Norms.Operator

variable {n : ℕ}

theorem hasDerivAt_conj_curve (X Y : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (s • X) * Y * NormedSpace.exp (s • (-X)))
      (X * Y - Y * X) 0 := by
  have h₁ := hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0
  have h₂ := hasDerivAt_exp_smul_const (𝕂 := ℝ) (-X) 0
  have h : HasDerivAt (fun s : ℝ => NormedSpace.exp (s • X) * Y * NormedSpace.exp (s • (-X)))
      (NormedSpace.exp ((0 : ℝ) • X) * X * Y * NormedSpace.exp ((0 : ℝ) • (-X)) +
        NormedSpace.exp ((0 : ℝ) • X) * Y * (NormedSpace.exp ((0 : ℝ) • (-X)) * -X)) 0 :=
    (h₁.mul_const Y).fun_mul h₂
  refine h.congr_deriv ?_
  simp only [zero_smul, NormedSpace.exp_zero, one_mul, mul_one, mul_neg, sub_eq_add_neg]

theorem conj_mem {G : Set (Matrix (Fin n) (Fin n) ℂ)} (hG : GlobalTheory.LinRed.IsLinRed G)
    {𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)}
    (h𝔤 : ∀ X, X ∈ 𝔤 ↔ ∀ t : ℝ, NormedSpace.exp (t • X) ∈ G)
    {g Y : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ G) (hY : Y ∈ 𝔤) : g * Y * g⁻¹ ∈ 𝔤 := by
  obtain ⟨-, hmul, hunit, hinv, -, -, -⟩ := hG
  rw [h𝔤] at hY ⊢
  intro t
  have hconj : t • (g * Y * g⁻¹) = g * (t • Y) * g⁻¹ := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [hconj, Matrix.exp_conj g (t • Y) (hunit g hg)]
  exact hmul _ (hmul _ hg _ (hY t)) _ (hinv g hg)

theorem lieAlg_stable : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)}, GlobalTheory.LinRed.IsLinRed G →
    ∀ 𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ),
      (∀ X, X ∈ 𝔤 ↔ ∀ t : ℝ, NormedSpace.exp (t • X) ∈ G) →
      (∀ X ∈ 𝔤, Xᴴ ∈ 𝔤) ∧ ∀ X ∈ 𝔤, ∀ Y ∈ 𝔤, X * Y - Y * X ∈ 𝔤 := by
  intro n G hG 𝔤 h𝔤
  have hexp : ∀ X ∈ 𝔤, ∀ t : ℝ, NormedSpace.exp (t • X) ∈ G := fun X hX => (h𝔤 X).1 hX
  refine ⟨fun X hX => ?_, fun X hX Y hY => ?_⟩
  · obtain ⟨-, -, -, -, -, -, hstar⟩ := hG
    refine (h𝔤 _).2 fun t => ?_
    have ht : t • Xᴴ = (t • X)ᴴ := by
      rw [Matrix.conjTranspose_smul, star_trivial]
    rw [ht, Matrix.exp_conjTranspose]
    exact hstar _ (hexp X hX t)
  · have hmem : ∀ s : ℝ,
        NormedSpace.exp (s • X) * Y * NormedSpace.exp (s • (-X)) ∈ 𝔤 := by
      intro s
      rw [smul_neg, Matrix.exp_neg]
      exact GlobalTheory.CompanionTheory.LieStable.conj_mem hG h𝔤 (hexp X hX s) hY
    have hd := hasDerivAt_iff_tendsto_slope.1 (GlobalTheory.CompanionTheory.LieStable.hasDerivAt_conj_curve X Y)
    refine (Submodule.closed_of_finiteDimensional 𝔤).mem_of_tendsto hd
      (Filter.Eventually.of_forall fun s => ?_)
    rw [slope_def_module]
    exact 𝔤.smul_mem _ (𝔤.sub_mem (hmem s) (hmem 0))

end GlobalTheory.CompanionTheory.LieStable

end
end
