module

public import Aesop.BuiltinRules
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle145
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle072
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle134
import Aesop.Main
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdicIntegersCompact.IsCompactAdicCompletionIntegers
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Mathlib.Topology.UniformSpace.Uniformizable
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ModuNorm

open scoped Pointwise

def mulUnitCE {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (a : Rˣ) : R ≃ₜ+ R where
  toFun x := (a : R) * x
  invFun x := ((a⁻¹ : Rˣ) : R) * x
  left_inv x := by simp [← mul_assoc]
  right_inv x := by simp [← mul_assoc]
  map_add' x y := mul_add _ x y
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_const.mul continuous_id

theorem distribHaarChar_eq_addEquivAddHaarChar {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [MeasurableSpace R] [BorelSpace R] (a : Rˣ) :
    distribHaarChar R a = addEquivAddHaarChar (mulUnitCE a) := by
  let μ : Measure R := Measure.addHaar
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds (0 : R)
  have h0 : μ K ≠ 0 := (Measure.measure_pos_of_mem_nhds μ hKn).ne'
  have hT : μ K ≠ ⊤ := hK.measure_lt_top.ne
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) h0 hT ?_
  have e := addEquivAddHaarChar_smul_preimage μ (X := a • K) (mulUnitCE a)
  have hpre : (mulUnitCE a : R → R) ⁻¹' (a • K) = K := by
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      have : y = x := (Units.mul_right_inj a).1 hxy
      exact this ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  rw [hpre] at e
  rw [← e]
  rfl

def evalUnitCE (R : Type) [AddCommGroup R] [TopologicalSpace R] : (Unit → R) ≃ₜ+ R where
  toFun f := f ()
  invFun x := fun _ => x
  left_inv f := rfl
  right_inv x := rfl
  map_add' f g := rfl
  continuous_toFun := continuous_apply ()
  continuous_invFun := continuous_pi fun _ => continuous_id

theorem modu_norm_eq_absE : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], NumberField.IsTotallyReal F →
    ∀ t : (AE F E)ˣ, (((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F) t) : ℝ≥0) : ℝ) = (absE F E t : ℝ) := by
  intro F E _ _ _ _ _ hF t
  haveI := hF
  letI : MeasurableSpace (AF F) := borel _
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  set a : (AF F)ˣ := Units.map (Algebra.norm (AF F) : AE F E →* AF F) t with ha
  let M : Matrix Unit Unit (AF F) := fun _ _ => (a : AF F)
  have hdet : M.det = (a : AF F) := Matrix.det_unique M
  have hM : IsUnit M.det := hdet ▸ a.isUnit
  have hχ := GlobalTheory.ModuLR.chi_AF F M hM
  have htr := GlobalTheory.ModuLR.addEquivAddHaarChar_transport (evalUnitCE (AF F)) (GlobalTheory.ModuLR.mulVecCE M hM)
  have hext : ((evalUnitCE (AF F)).symm.trans (GlobalTheory.ModuLR.mulVecCE M hM)).trans (evalUnitCE (AF F)) = mulUnitCE a := by
    ext x
    show (M *ᵥ fun _ => x) () = (a : AF F) * x
    simp [Matrix.mulVec, dotProduct, M]
  rw [hext] at htr
  show ((distribHaarChar (AdeleRing (𝓞 F) F) a : ℝ≥0) : ℝ) = _
  rw [show distribHaarChar (AdeleRing (𝓞 F) F) a = distribHaarChar (AF F) a from rfl,
    distribHaarChar_eq_addEquivAddHaarChar, htr, hχ, hdet]
  exact GlobalTheory.absE_eq_prod_norm_fstA_sndA F E t

end GlobalTheory.ModuNorm
end
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LatVac
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open MeasureTheory

noncomputable section
namespace GlobalTheory.HaarSB

section General

variable (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G]
  [LocallyCompactSpace G]

def measG : MeasurableSpace G := borel G

attribute [local instance] measG

instance borelG : BorelSpace G := ⟨rfl⟩

def intSub : Submodule ℂ (G → ℂ) where
  carrier := {h | Integrable h (Measure.addHaar : Measure G)}
  zero_mem' := integrable_zero _ _ _
  add_mem' := Integrable.add
  smul_mem' c _ h := h.smul c

def I0 : intSub G →ₗ[ℂ] ℂ where
  toFun h := ∫ x, (h : G → ℂ) x ∂(Measure.addHaar : Measure G)
  map_add' h h' := integral_add h.2 h'.2
  map_smul' c h := integral_smul c (h : G → ℂ)

def Lext : (G → ℂ) →ₗ[ℂ] ℂ := (LinearMap.exists_extend (I0 G)).choose

variable {G}

theorem Lext_apply (h : G → ℂ) (hh : Integrable h (Measure.addHaar : Measure G)) :
    Lext G h = ∫ x, h x ∂(Measure.addHaar : Measure G) :=
  LinearMap.congr_fun (LinearMap.exists_extend (I0 G)).choose_spec ⟨h, hh⟩

theorem integrable_of_SB {f : G → ℂ} (hf : f ∈ SB G) : Integrable f (Measure.addHaar : Measure G) :=
  hf.1.continuous.integrable_of_hasCompactSupport hf.2

theorem Lext_translate {f : G → ℂ} (hf : f ∈ SB G) (a : G) :
    Lext G (fun x => f (x + a)) = Lext G f := by
  have hi := integrable_of_SB hf
  rw [Lext_apply _ (hi.comp_add_right a), Lext_apply _ hi]
  exact integral_add_right_eq_self _ _

end General

theorem exists_invariant_form (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [T2Space G] (K : Set G) (hKc : IsCompact K) (hKo : IsOpen K) (h0 : (0 : G) ∈ K) :
    ∃ Λ : (G → ℂ) →ₗ[ℂ] ℂ, (∀ f ∈ SB G, ∀ a, Λ (fun Y => f (Y + a)) = Λ f) ∧ ∃ f ∈ SB G, Λ f ≠ 0 := by
  haveI : LocallyCompactSpace G := hKc.locallyCompactSpace_of_mem_nhds_of_addGroup (hKo.mem_nhds h0)
  letI := measG G
  refine ⟨Lext G, fun f hf a => Lext_translate hf a, K.indicator fun _ => 1, ?_, ?_⟩
  · exact ⟨(LocallyConstant.indicator (1 : LocallyConstant G ℂ) ⟨hKc.isClosed, hKo⟩).isLocallyConstant,
      HasCompactSupport.intro hKc fun z hz => Set.indicator_of_notMem hz _⟩
  · have hi : Integrable (K.indicator fun _ => (1 : ℂ)) (Measure.addHaar : Measure G) :=
      (integrable_indicator_iff hKo.measurableSet).2 (integrableOn_const hKc.measure_lt_top.ne)
    rw [Lext_apply _ hi, integral_indicator_const _ hKo.measurableSet]
    have hpos : 0 < (Measure.addHaar : Measure G) K := hKo.measure_pos _ ⟨0, h0⟩
    have : 0 < (Measure.addHaar : Measure G).real K := ENNReal.toReal_pos hpos.ne' hKc.measure_lt_top.ne
    simpa using this.ne'

theorem exists_invariant_form_matrix : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (n d : ℕ), ∃ Λ : (Matrix (Fin n) (Fin d) (Fv F v) → ℂ) →ₗ[ℂ] ℂ,
    (∀ f ∈ SB (Matrix (Fin n) (Fin d) (Fv F v)), ∀ a, Λ (fun Y => f (Y + a)) = Λ f) ∧
      ∃ f ∈ SB (Matrix (Fin n) (Fin d) (Fv F v)), Λ f ≠ 0 := by
  intro F _ _ v n d
  set O : Set (Fv F v) := (v.adicCompletionIntegers F : Set (Fv F v))
  have hO : IsOpen O := Valued.isOpen_valuationSubring _
  have hOc : IsCompact O := PI.IntAdCpctOpenWork.isCompact_adicCompletionIntegers v
  have h0 : (0 : Fv F v) ∈ O := (v.adicCompletionIntegers F).zero_mem
  set K : Set (Matrix (Fin n) (Fin d) (Fv F v)) := Set.univ.pi fun _ => Set.univ.pi fun _ => O
  exact exists_invariant_form _ K
    (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hOc)
    (isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => hO)
    (fun _ _ _ _ => h0)

end GlobalTheory.HaarSB
end
end

section

noncomputable section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open IsDedekindDomain

namespace GlobalTheory.ArchimedeanL2

theorem lintegral_eq_of_fibres {Z X Y : Type} [AddGroup Z] [TopologicalSpace Z] [IsTopologicalAddGroup Z] [MeasurableSpace Z]
    [BorelSpace Z] [AddGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [MeasurableSpace X] [BorelSpace X]
    [LocallyCompactSpace X] [SecondCountableTopology X]
    [AddGroup Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y] [MeasurableSpace Y] [BorelSpace Y]
    [LocallyCompactSpace Y] [SecondCountableTopology Y] (e : Z ≃ₜ+ X × Y) (μ : Measure Z) [μ.IsAddHaarMeasure]
    (ν : Measure X) [ν.IsAddHaarMeasure] {G G' : X × Y → ENNReal} (hG : Measurable G) (hG' : Measurable G')
    (h : ∀ y, ∫⁻ x, G (x, y) ∂ν = ∫⁻ x, G' (x, y) ∂ν) : ∫⁻ z, G (e z) ∂μ = ∫⁻ z, G' (e z) ∂μ := by
  have he : Measurable e := e.continuous.measurable
  let ρ : Measure Y := Measure.addHaar
  haveI : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  haveI : (ν.prod ρ).IsAddHaarMeasure := inferInstance
  rw [← lintegral_map hG he, ← lintegral_map hG' he, Measure.isAddLeftInvariant_eq_smul (μ.map e) (ν.prod ρ),
    lintegral_smul_measure, lintegral_smul_measure, lintegral_prod_symm _ hG.aemeasurable,
    lintegral_prod_symm _ hG'.aemeasurable]
  simp only [h]

theorem lintegral_sq_eq {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
    [BorelSpace V] (ν : Measure V) [ν.IsAddHaarMeasure] (g : SchwartzMap V ℂ) :
    ∫⁻ x, ‖g x‖ₑ ^ 2 ∂ν = ENNReal.ofReal (∫ x, star (g x) * g x ∂ν).re := by
  have hi : Integrable (fun x => ‖g x‖ ^ 2) ν := (g.memLp 2 ν).integrable_norm_pow (by norm_num)
  have h1 : ∀ x, star (g x) * g x = ((‖g x‖ ^ 2 : ℝ) : ℂ) := fun x => by
    rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [h1]
  rw [integral_complex_ofReal, Complex.ofReal_re,
    ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun x => by positivity)]
  refine lintegral_congr fun x => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

variable {F : Type} [Field F] [NumberField F]

theorem cont_toMixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  change Continuous fun x : InfiniteAdeleRing F =>
    ((fun (v : {w : InfinitePlace F // w.IsReal}) => InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
     (fun (v : {w : InfinitePlace F // w.IsComplex}) => InfinitePlace.Completion.extensionEmbedding v.1 (x v)))
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

theorem cont_ofMixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
  refine continuous_pi fun v => ?_
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_fst).congr fun y =>
      (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_snd).congr fun y =>
      (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm


variable (F) in
def splitEquiv (κ : Type) : (κ → AF F) ≃ₜ+ (κ → mixedEmbedding.mixedSpace F) × (κ → Af F) where
  toFun x := (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1, fun i => (x i).2)
  invFun p := fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i), p.2 i)
  left_inv x := funext fun i => Prod.ext ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm_apply_apply _) rfl
  right_inv p := Prod.ext (funext fun i => (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply _) rfl
  map_add' x y := Prod.ext (funext fun i => map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) (x i).1 (y i).1) rfl
  continuous_toFun := (continuous_pi fun i => cont_toMixed.comp (continuous_fst.comp (continuous_apply i))).prodMk
    (continuous_pi fun i => continuous_snd.comp (continuous_apply i))
  continuous_invFun := continuous_pi fun i =>
    (cont_ofMixed.comp ((continuous_apply i).comp continuous_fst)).prodMk ((continuous_apply i).comp continuous_snd)

theorem lintegral_arch_eq : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (L : SInf F κ →ₗ[ℂ] SInf F κ) (Ω : Module.End ℂ ((κ → AF F) → ℂ)),
    (∀ (f : SInf F κ) (h : (κ → Af F) → ℂ), Ω (pureA F f h) = pureA F (L f) h) →
    (∀ ν : Measure (κ → mixedEmbedding.mixedSpace F), ν.IsAddHaarMeasure → ∀ f₁ f₂ : SInf F κ,
      ∫ x, star (L f₁ x) * L f₂ x ∂ν = ∫ x, star (f₁ x) * f₂ x ∂ν) →
    ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ φ ∈ schA F κ, ∫⁻ x, ‖Ω φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ := by
  intro F _ _ κ _ L Ω hΩ hL μ hμ φ hφ
  classical
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  letI : MeasurableSpace (κ → Af F) := borel _
  haveI : BorelSpace (κ → Af F) := ⟨rfl⟩
  haveI : LocallyCompactSpace (Af F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI : SecondCountableTopology (Af F) := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  obtain ⟨n, c, g, rfl⟩ := Submodule.mem_span_set'.1 hφ
  choose f h hh hg using fun i => (g i).2
  let ν : Measure (κ → mixedEmbedding.mixedSpace F) := Measure.addHaar
  have hB : BorelSpace (κ → mixedEmbedding.mixedSpace F) := inferInstance
  have hν : ν.IsAddHaarMeasure := inferInstance
  have hsq : ∀ u : SInf F κ, ∫⁻ x, ‖u x‖ₑ ^ 2 ∂ν = ENNReal.ofReal (∫ x, star (u x) * u x ∂ν).re := fun u =>
    @lintegral_sq_eq (κ → mixedEmbedding.mixedSpace F) _ _ _ _ hB ν hν u
  haveI : OpensMeasurableSpace ((κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) :=
    (Prod.borelSpace (α := κ → mixedEmbedding.mixedSpace F) (β := κ → Af F)).opensMeasurable
  have hm : ∀ u : Fin n → SInf F κ, Measurable fun p : (κ → mixedEmbedding.mixedSpace F) × (κ → Af F) =>
      ‖∑ i, c i * (u i p.1 * h i p.2)‖ₑ ^ 2 := fun u =>
    (continuous_finsetSum _ fun i _ => continuous_const.mul
      (((u i).continuous.comp continuous_fst).mul ((hh i).1.continuous.comp continuous_snd))).measurable.enorm.pow_const 2
  have hs : ∀ (u : Fin n → SInf F κ) (y : κ → Af F) (x : κ → mixedEmbedding.mixedSpace F),
      ∑ i, c i * (u i x * h i y) = (∑ i, (c i * h i y) • u i) x := fun u y x => by
    rw [sum_apply]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_apply, smul_eq_mul]; ring
  have key := lintegral_eq_of_fibres (splitEquiv F κ) μ ν (hm fun i => L (f i)) (hm f) fun y => by
    simp only [hs]
    have e : ∑ i, (c i * h i y) • L (f i) = L (∑ i, (c i * h i y) • f i) := by simp only [map_sum, map_smul]
    rw [e, hsq, hsq, hL ν hν]
  have e1 : Ω (∑ i, c i • (g i : (κ → AF F) → ℂ)) = ∑ i, c i • pureA F (L (f i)) (h i) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, hg, hΩ]
  rw [e1]
  simp only [hg, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact key

end GlobalTheory.ArchimedeanL2
end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
noncomputable section

namespace GlobalTheory.SchwartzBruhatRestrict

theorem map_funLeft_extendZero : ∀ (F : Type) [Field F] [NumberField F] {κ₁ κ : Type} [Fintype κ₁] [Fintype κ] (j : κ₁ → κ), Function.Injective j →
    ∀ v : Pl (F := F), (SB (κ → Fv F v)).map (LinearMap.funLeft ℂ ℂ (fun y : κ₁ → Fv F v => Function.extend j y 0)) = SB (κ₁ → Fv F v) := by
  intro F _ _ κ₁ κ _ _ j hj v
  classical
  set ext : (κ₁ → Fv F v) → (κ → Fv F v) := fun y => Function.extend j y 0 with hext
  have hr : Function.LeftInverse (fun x : κ → Fv F v => x ∘ j) ext :=
    fun y => funext fun i => hj.extend_apply y 0 i
  have hcr : Continuous (fun x : κ → Fv F v => x ∘ j) :=
    continuous_pi fun i => continuous_apply (j i)
  have hce : Continuous ext := by
    refine continuous_pi fun k => ?_
    by_cases hk : ∃ i, j i = k
    · obtain ⟨i, rfl⟩ := hk
      simp only [ext, hj.extend_apply]
      exact continuous_apply i
    · simp only [ext, Function.extend_apply' _ _ _ hk]
      exact continuous_const
  have hemb : Topology.IsClosedEmbedding ext := hr.isClosedEmbedding hcr hce
  apply le_antisymm
  · rintro _ ⟨φ, ⟨hlc, hcs⟩, rfl⟩
    exact ⟨hlc.comp_continuous hce, hcs.comp_isClosedEmbedding hemb⟩
  · rintro φ₁ ⟨hlc, hcs⟩
    let O : Set (Fv F v) := (v.adicCompletionIntegers F : Set (v.adicCompletion F))
    have hOeq : O = ((Valued.v : Valuation (v.adicCompletion F) _).integer : Set (v.adicCompletion F)) := by
      ext x
      simp only [O, SetLike.mem_coe, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
        Valuation.mem_integer_iff]
    have hOo : IsOpen O := by rw [hOeq]; exact Valued.isOpen_integer _
    have hOc : IsClosed O := by rw [hOeq]; exact Valued.isClosed_integer _
    have hOk : IsCompact O :=
      isCompact_iff_compactSpace.2 (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v)
    have hO0 : (0 : Fv F v) ∈ O := (v.adicCompletionIntegers F).zero_mem
    let S : Set (κ → Fv F v) := {x | ∀ k, k ∉ Set.range j → x k ∈ O}
    have hSeq : S = ⋂ k ∈ (Set.range j)ᶜ, (fun x : κ → Fv F v => x k) ⁻¹' O := by
      ext x; simp [S]
    have hSo : IsOpen S := by
      rw [hSeq]
      exact Set.Finite.isOpen_biInter (Set.toFinite _) fun k _ => hOo.preimage (continuous_apply k)
    have hSc : IsClosed S := by
      rw [hSeq]
      exact isClosed_biInter fun k _ => hOc.preimage (continuous_apply k)
    set g : (κ → Fv F v) → ℂ := fun x => φ₁ (x ∘ j) with hg
    have hglc : IsLocallyConstant g := hlc.comp_continuous hcr
    refine ⟨S.indicator g, ⟨?_, ?_⟩, ?_⟩
    · refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
      by_cases hx : x ∈ S
      · filter_upwards [hSo.mem_nhds hx, (IsLocallyConstant.iff_eventually_eq _).1 hglc x] with y hy hgy
        rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx, hgy]
      · filter_upwards [hSc.isOpen_compl.mem_nhds hx] with y hy
        rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]
    · let C : κ → Set (Fv F v) := fun k =>
        if h : k ∈ Set.range j then (fun y : κ₁ → Fv F v => y (Classical.choose h)) '' tsupport φ₁ else O
      have hC : IsCompact (Set.univ.pi C) := by
        refine isCompact_univ_pi fun k => ?_
        by_cases h : k ∈ Set.range j
        · simp only [C, dif_pos h]
          exact hcs.isCompact.image (continuous_apply _)
        · simp only [C, dif_neg h]
          exact hOk
      refine HasCompactSupport.intro hC fun x hx => ?_
      by_contra hne
      have hxS : x ∈ S := by
        by_contra hxS; exact hne (Set.indicator_of_notMem hxS _)
      have hgx : g x ≠ 0 := by rwa [Set.indicator_of_mem hxS] at hne
      apply hx
      intro k _
      by_cases h : k ∈ Set.range j
      · simp only [C, dif_pos h]
        refine ⟨x ∘ j, subset_tsupport _ hgx, ?_⟩
        simp only [Function.comp_apply]
        rw [Classical.choose_spec h]
      · simp only [C, dif_neg h]
        exact hxS k h
    · funext y
      rw [LinearMap.funLeft_apply]
      have hyS : ext y ∈ S := by
        intro k hk
        have hk' : ¬ ∃ i, j i = k := hk
        simp only [ext, Function.extend_apply' _ _ _ hk']
        exact hO0
      rw [Set.indicator_of_mem hyS]
      exact congrArg φ₁ (hr y)

end GlobalTheory.SchwartzBruhatRestrict
end
end

section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

noncomputable section
namespace GlobalTheory.RealScalar

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem ext_realAd (r : ℝ) (w : InfinitePlace F) :
    InfinitePlace.Completion.extensionEmbedding w (evInf F w (realAd F r)) = (r : ℂ) := by
  set y : mixedEmbedding.mixedSpace F := algebraMap ℝ _ r with hy
  set a := (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm y with ha
  have hev : evInf F w (realAd F r) = a w := rfl
  have hay : InfiniteAdeleRing.ringEquiv_mixedSpace F a = y := by rw [ha]; exact RingEquiv.apply_symm_apply _ _
  rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply] at hay
  rw [hev]
  rcases w.isReal_or_isComplex with hw | hw
  · have h1 := congrFun (congrArg Prod.fst hay) ⟨w, hw⟩
    simp only [hy] at h1
    rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw]
    rw [show (InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (a w)) = r from by simpa using h1]
  · have h1 := congrFun (congrArg Prod.snd hay) ⟨w, hw⟩
    simpa [hy] using h1

theorem piInf_algebraMap {w : InfinitePlace F} (τ : EmbOver E w) (x : AF F) :
    piInf τ (algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) x) = InfinitePlace.Completion.extensionEmbedding w (evInf F w x) := by
  change infEmb τ (compInf F E w (x ⊗ₜ[F] (1 : E))) = _
  rw [compInf]
  change infEmb τ ((evInf F w x) ⊗ₜ[F] ((AlgHom.id F E) 1)) = _
  rw [infEmb_tmul]
  simp

theorem piInf_realAd_smul {w : InfinitePlace F} (τ : EmbOver E w) (r : ℝ) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    piInf τ (realAd F r • z) = (r : ℂ) * piInf τ z := by
  rw [Algebra.smul_def, map_mul, piInf_algebraMap, ext_realAd]

theorem realAd_smul_map : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {α β : Type}
    (τ : ∀ w : InfinitePlace F, EmbOver E w), IsCMExt F E σ →
    ∀ (u : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (r : ℝ) (w : InfinitePlace F),
      (realAd F r • u).map (piInf (τ w)) = (r : ℂ) • u.map (piInf (τ w)) := by
  intro F E _ _ _ _ _ σ α β τ _ u r w
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  exact piInf_realAd_smul (τ w) r (u i j)

end GlobalTheory.RealScalar
end
end
