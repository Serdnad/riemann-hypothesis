module

public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle078
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle074
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle084
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LintegralMulRight
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsWeightedHomogeneousOfMemOrbitSpan
import Development.AbelianVarietyTheory.Definitions.ThetaValues.PolyDerivSmulLetter
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory NumberField
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StabOpen

noncomputable def stab {D : D7} (V : HSp D) (L : AddSubgroup (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E)) :
    Subgroup (GA D V) where
  carrier := {h | ∀ y, y ∈ L ↔ (finHom V h).1.mulVec y ∈ L}
  one_mem' := fun y => by rw [map_one, Units.val_one, Matrix.one_mulVec]
  mul_mem' := by
    intro a b ha hb y
    rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec]
    exact (hb y).trans (ha _)
  inv_mem' := by
    intro a ha y
    rw [ha ((finHom V a⁻¹).1.mulVec y), Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel,
      map_one, Units.val_one, Matrix.one_mulVec]

theorem isOpen_stab_latHat : ∀ (D : D7) (V : HSp D), IsOpen {h : GA D V | ∀ y, y ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V) ↔ (finMat D.sp.cm.sig V.gram h).mulVec y ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V)} := by
  intro D V
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  obtain ⟨-, -, hfg, hsp, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  have e : Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V) =
      GlobalTheory.AdLat.hat D.host.F (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) := by
    rw [GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq]
    rfl
  rw [e]
  have hn := GlobalTheory.LevelOpen.congr_mem_nhds D.host.F D.host.E V.rank _ hfg hsp 1 one_pos
  have hc := GlobalTheory.Member.continuous_finHom_val D V
  have h1 := hc.continuousAt (x := 1) |>.preimage_mem_nhds (by rw [map_one, Units.val_one]; exact hn)
  have h2 := (hc.comp continuous_inv).continuousAt (x := 1) |>.preimage_mem_nhds
    (by rw [Function.comp_apply, inv_one, map_one, Units.val_one]; exact hn)
  refine Subgroup.isOpen_of_mem_nhds (stab V (GlobalTheory.AdLat.hat D.host.F
    (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)))) (g := 1) ?_
  refine Filter.mem_of_superset (Filter.inter_mem h1 h2) ?_
  rintro k ⟨hk1, hk2⟩ y
  constructor
  · intro hy
    obtain ⟨w, hw, h⟩ := hk1 y hy
    rw [eq_add_of_sub_eq h]
    exact add_mem (nsmul_mem hw 1) hy
  · intro hy
    obtain ⟨w, hw, h⟩ := hk2 _ hy
    rw [Function.comp_apply, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one,
      Units.val_one, Matrix.one_mulVec] at h
    rw [eq_add_of_sub_eq h]
    exact add_mem (nsmul_mem hw 1) hy

end GlobalTheory.StabOpen
end

section

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW

theorem summable_setIntegral_of_summable_norm {I Y : Type} [MeasurableSpace Y] (ν : Measure Y)
    (D : I → Set Y) (f : I → Y → ℂ) (h : Summable fun i => ∫ y in D i, ‖f i y‖ ∂ν) :
    Summable fun i => ∫ y in D i, f i y ∂ν := by

  exact Summable.of_norm_bounded h fun i => norm_integral_le_integral_norm _

def finiteRankDomain {I Y : Type} [MeasurableSpace Y] (ν : Measure Y) (D : I → Set Y) {m : ℕ}
    (t : Fin m → I → Y → ℂ) : Submodule ℂ (Fin m → ℂ) where
  carrier := {v | (∀ i, IntegrableOn (fun y => ∑ j, v j * t j i y) (D i) ν) ∧
    Summable fun i => ∫ y in D i, ‖∑ j, v j * t j i y‖ ∂ν}
  zero_mem' := by
    refine ⟨fun i => ?_, ?_⟩
    · simp
    · simp
  add_mem' := by
    rintro v w ⟨hv, hv'⟩ ⟨hw, hw'⟩
    have key : ∀ i y, ∑ j, (v + w) j * t j i y = ∑ j, v j * t j i y + ∑ j, w j * t j i y := by
      intro i y
      simp [add_mul, Finset.sum_add_distrib]
    refine ⟨fun i => ?_, ?_⟩
    · simp only [key]
      exact (hv i).add (hw i)
    · simp only [key]
      refine Summable.of_nonneg_of_le (fun i => integral_nonneg fun y => norm_nonneg _)
        (fun i => ?_) (hv'.add hw')
      rw [← integral_add (hv i).norm (hw i).norm]
      exact integral_mono ((hv i).add (hw i)).norm ((hv i).norm.add (hw i).norm)
        (fun y => norm_add_le _ _)
  smul_mem' := by
    rintro c v ⟨hv, hv'⟩
    have key : ∀ i y, ∑ j, (c • v) j * t j i y = c * ∑ j, v j * t j i y := by
      intro i y
      simp [Finset.mul_sum, mul_assoc]
    refine ⟨fun i => ?_, ?_⟩
    · simp only [key]
      exact (hv i).const_mul c
    · simp only [key, norm_mul, integral_const_mul]
      exact hv'.mul_left _

noncomputable def finiteRankFunctional {I Y : Type} [MeasurableSpace Y] (ν : Measure Y)
    (D : I → Set Y) {m : ℕ} (t : Fin m → I → Y → ℂ) : finiteRankDomain ν D t →ₗ[ℂ] ℂ where
  toFun v := ∑' i, ∫ y in D i, ∑ j, v.1 j * t j i y ∂ν
  map_add' := by
    rintro ⟨v, hv, hv'⟩ ⟨w, hw, hw'⟩
    have key : ∀ i y, ∑ j, (v + w) j * t j i y = ∑ j, v j * t j i y + ∑ j, w j * t j i y := by
      intro i y
      simp [add_mul, Finset.sum_add_distrib]
    show ∑' i, ∫ y in D i, ∑ j, (v + w) j * t j i y ∂ν
      = ∑' i, ∫ y in D i, ∑ j, v j * t j i y ∂ν + ∑' i, ∫ y in D i, ∑ j, w j * t j i y ∂ν
    rw [← Summable.tsum_add (summable_setIntegral_of_summable_norm ν D _ hv')
      (summable_setIntegral_of_summable_norm ν D _ hw')]
    refine tsum_congr fun i => ?_
    simp only [key]
    exact integral_add (hv i) (hw i)
  map_smul' := by
    rintro c ⟨v, hv⟩
    have key : ∀ i y, ∑ j, (c • v) j * t j i y = c * ∑ j, v j * t j i y := by
      intro i y
      simp [Finset.mul_sum, mul_assoc]
    show ∑' i, ∫ y in D i, ∑ j, (c • v) j * t j i y ∂ν
      = c * ∑' i, ∫ y in D i, ∑ j, v j * t j i y ∂ν
    simp only [key, integral_const_mul]
    exact tsum_mul_left

theorem finiteRank_integral_mem_span : ∀ (A I Y : Type) [Countable I] [MeasurableSpace Y] (ν : Measure Y) (D : I → Set Y) (S : Set A) (m : ℕ) (e : Fin m → A → ℂ) (t : Fin m → I → Y → ℂ), (∀ a ∈ S, (∀ i, IntegrableOn (fun y => ∑ j, e j a * t j i y) (D i) ν) ∧ Summable fun i => ∫ y in D i, ‖∑ j, e j a * t j i y‖ ∂ν) → ∃ b : Fin m → ℂ, ∀ a ∈ S, ∑' i, ∫ y in D i, ∑ j, e j a * t j i y ∂ν = ∑ j, b j * e j a := by
  intro A I Y _ _ ν D S m e t hS

  obtain ⟨g, hg⟩ := LinearMap.exists_extend (finiteRankFunctional ν D t)
  refine ⟨fun j => g (Pi.single j 1), fun a ha => ?_⟩
  have hmem : (fun j => e j a) ∈ finiteRankDomain ν D t := hS a ha
  have h1 : g (fun j => e j a) = ∑' i, ∫ y in D i, ∑ j, e j a * t j i y ∂ν :=
    LinearMap.congr_fun hg ⟨fun j => e j a, hmem⟩
  rw [← h1]
  have hx : (fun j => e j a) = ∑ j, e j a • (Pi.single j (1 : ℂ) : Fin m → ℂ) := by
    ext k
    simp [Pi.single_apply]

  rw [hx, map_sum]
  simp [mul_comm]

end GlobalTheory.SW
end

section

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW

private theorem integrable_tsum_of_summable_integral_norm' {ι Y E : Type} [Countable ι] [MeasurableSpace Y]
    [NormedAddCommGroup E] [CompleteSpace E]
    (μ : Measure Y) (F : ι → Y → E) (hF : ∀ i, Integrable (F i) μ)
    (hs : Summable fun i => ∫ y, ‖F i y‖ ∂μ) :
    Integrable (fun y => ∑' i, F i y) μ ∧ ∀ᵐ y ∂μ, Summable fun i => ‖F i y‖ := by
  have hmeas : ∀ i, AEMeasurable (fun y => ‖F i y‖ₑ) μ := fun i => (hF i).1.enorm

  have htot : ∫⁻ y, ∑' i, ‖F i y‖ₑ ∂μ ≠ ⊤ := by
    rw [lintegral_tsum hmeas]
    have h : ∀ i, ∫⁻ y, ‖F i y‖ₑ ∂μ = ENNReal.ofReal (∫ y, ‖F i y‖ ∂μ) := fun i =>
      (ofReal_integral_norm_eq_lintegral_enorm (hF i)).symm
    simp_rw [h]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => integral_nonneg fun y => norm_nonneg _) hs]
    exact ENNReal.ofReal_ne_top

  have hsum : ∀ᵐ y ∂μ, Summable fun i => ‖F i y‖ := by
    filter_upwards [ae_lt_top' (AEMeasurable.tsum hmeas) htot] with y hy
    exact tsum_enorm_ne_top_iff_summable_norm.1 hy.ne
  refine ⟨⟨?_, ?_⟩, hsum⟩
  · refine aestronglyMeasurable_of_tendsto_ae (Filter.atTop : Filter (Finset ι))
      (f := fun s y => ∑ i ∈ s, F i y) (fun s => ?_) ?_
    · exact Finset.aestronglyMeasurable_fun_sum s fun i _ => (hF i).1
    · filter_upwards [hsum] with y hy
      exact hy.of_norm.hasSum
  · exact lt_of_le_of_lt (lintegral_mono fun y => enorm_tsum_le_tsum_enorm) htot.lt_top

theorem integrable_tsum_of_summable_integral_norm {ι Y : Type} [Countable ι] [MeasurableSpace Y]
    (μ : Measure Y) (F : ι → Y → ℂ) (hF : ∀ i, Integrable (F i) μ)
    (hs : Summable fun i => ∫ y, ‖F i y‖ ∂μ) :
    Integrable (fun y => ∑' i, F i y) μ ∧ ∫ y, ‖∑' i, F i y‖ ∂μ ≤ ∑' i, ∫ y, ‖F i y‖ ∂μ := by
  obtain ⟨hint, hsum⟩ := integrable_tsum_of_summable_integral_norm' μ F hF hs
  refine ⟨hint, ?_⟩
  have hnorm : ∀ i, Integrable (fun y => ‖F i y‖) μ := fun i => (hF i).norm
  have hs' : Summable fun i => ∫ y, ‖‖F i y‖‖ ∂μ := by simpa only [norm_norm] using hs
  calc ∫ y, ‖∑' i, F i y‖ ∂μ ≤ ∫ y, ∑' i, ‖F i y‖ ∂μ := by
        refine integral_mono_ae hint.norm (integrable_tsum_of_summable_integral_norm' μ _ hnorm hs').1 ?_
        filter_upwards [hsum] with y hy
        exact norm_tsum_le_tsum_norm hy
    _ = ∑' i, ∫ y, ‖F i y‖ ∂μ := (integral_tsum_of_summable_integral_norm hnorm hs').symm

theorem hasSum_setIntegral_of_ae_existsUnique {ι Y E : Type} [Countable ι] [MeasurableSpace Y]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Y) (S : ι → Set Y) (hS : ∀ i, MeasurableSet (S i))
    (hu : ∀ᵐ y ∂μ, ∃! i, y ∈ S i) (f : Y → E) (hf : Integrable f μ) :
    HasSum (fun i => ∫ y in S i, f y ∂μ) (∫ y, f y ∂μ) := by

  have hdisj : Pairwise fun i j => AEDisjoint μ (S i) (S j) := by
    intro i j hij
    refine measure_mono_null (t := {y | ¬ ∃! k, y ∈ S k}) ?_ (ae_iff.1 hu)
    intro y hy h
    exact hij (ExistsUnique.unique h hy.1 hy.2)

  have hcover : (⋃ i, S i : Set Y) =ᵐ[μ] (Set.univ : Set Y) := by
    filter_upwards [hu] with y ⟨i, hi, _⟩
    exact ⟨fun _ => trivial, fun _ => Set.mem_iUnion.2 ⟨i, hi⟩⟩
  have h := hasSum_integral_iUnion_ae (fun i => (hS i).nullMeasurableSet) hdisj hf.integrableOn
  rwa [setIntegral_congr_set hcover, setIntegral_univ] at h

theorem setIntegral_smul_of_measurePreserving {Γ Y E : Type} [Group Γ] [MeasurableSpace Y]
    [MulAction Γ Y] [NormedAddCommGroup E] [NormedSpace ℝ E] (ν : Measure Y)
    (hν : ∀ γ : Γ, MeasurePreserving (fun y : Y => γ • y) ν ν) (γ : Γ) (D : Set Y) (g : Y → E) :
    ∫ y in D, g (γ • y) ∂ν = ∫ y in (fun y : Y => γ⁻¹ • y) ⁻¹' D, g y ∂ν := by
  let φ : Y ≃ᵐ Y :=
    { toEquiv := MulAction.toPerm γ
      measurable_toFun := (hν γ).measurable
      measurable_invFun := (hν γ⁻¹).measurable }
  have hemb : MeasurableEmbedding (fun y : Y => γ • y) := φ.measurableEmbedding
  have hD : D = (fun y : Y => γ • y) ⁻¹' ((fun y : Y => γ⁻¹ • y) ⁻¹' D) := by
    ext y
    simp
  have key := (hν γ).setIntegral_preimage_emb hemb g ((fun y : Y => γ⁻¹ • y) ⁻¹' D)
  rw [← hD] at key
  exact key

theorem unfolding_abstract : ∀ (Γ I Y : Type) [Group Γ] [Countable Γ] [Countable I] [MeasurableSpace Y] [MulAction Γ I] [MulAction Γ Y] (ν : Measure Y) [SFinite ν], (∀ γ : Γ, MeasurePreserving (fun y : Y => γ • y) ν ν) → ∀ D : I → Set Y, (∀ i, MeasurableSet (D i)) → (∀ i, ∀ᵐ y ∂ν, ∃! γ : Γ, γ • y ∈ D (γ • i)) → ∀ f : I → Y → ℂ, (∀ i, Integrable (f i) ν) → Summable (fun i => ∫ y, ‖f i y‖ ∂ν) → (∀ i, IntegrableOn (fun y => ∑' γ : Γ, f (γ • i) (γ • y)) (D i) ν) ∧ Summable (fun i => ∫ y in D i, ‖∑' γ : Γ, f (γ • i) (γ • y)‖ ∂ν) ∧ ∑' i, ∫ y in D i, ∑' γ : Γ, f (γ • i) (γ • y) ∂ν = ∑' i, ∫ y, f i y ∂ν := by
  intro Γ I Y _ _ _ _ _ _ ν _ hν D hD hcov f hf hs

  have hSm : ∀ (j : I) (δ : Γ), MeasurableSet ((fun y : Y => δ • y) ⁻¹' D (δ • j)) :=
    fun j δ => (hν δ).measurable (hD _)
  have hP : ∀ (j : I) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : Y → E),
      Integrable g ν →
      HasSum (fun δ : Γ => ∫ y in (fun y : Y => δ • y) ⁻¹' D (δ • j), g y ∂ν) (∫ y, g y ∂ν) :=
    fun j E _ _ g hg => hasSum_setIntegral_of_ae_existsUnique ν
      (fun δ : Γ => (fun y : Y => δ • y) ⁻¹' D (δ • j)) (hSm j) (hcov j) g hg

  have hmove : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (j : I) (δ : Γ) (g : Y → E),
      ∫ y in D (δ • j), g (δ⁻¹ • y) ∂ν = ∫ y in (fun y : Y => δ • y) ⁻¹' D (δ • j), g y ∂ν := by
    intro E _ _ j δ g
    rw [setIntegral_smul_of_measurePreserving ν hν δ⁻¹ (D (δ • j)) g]
    simp only [inv_inv]

  let e : I × Γ ≃ I × Γ :=
    { toFun := fun p => (p.2 • p.1, p.2⁻¹)
      invFun := fun p => (p.2 • p.1, p.2⁻¹)
      left_inv := fun p => by simp
      right_inv := fun p => by simp }
  have he : ∀ p : I × Γ, e p = (p.2 • p.1, p.2⁻¹) := fun p => rfl
  obtain ⟨c, hc⟩ : ∃ c : I × Γ → ℂ,
      ∀ p, c p = ∫ y in D p.1, f (p.2 • p.1) (p.2 • y) ∂ν := ⟨_, fun _ => rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : I × Γ → ℝ,
      ∀ p, a p = ∫ y in D p.1, ‖f (p.2 • p.1) (p.2 • y)‖ ∂ν := ⟨_, fun _ => rfl⟩
  have hce : ∀ p : I × Γ,
      c (e p) = ∫ y in (fun y : Y => p.2 • y) ⁻¹' D (p.2 • p.1), f p.1 y ∂ν := by
    rintro ⟨j, δ⟩
    rw [he, hc]
    dsimp only
    simp only [inv_smul_smul]
    exact hmove j δ (f j)
  have hae : ∀ p : I × Γ,
      a (e p) = ∫ y in (fun y : Y => p.2 • y) ⁻¹' D (p.2 • p.1), ‖f p.1 y‖ ∂ν := by
    rintro ⟨j, δ⟩
    rw [he, ha]
    dsimp only
    simp only [inv_smul_smul]
    exact hmove j δ (fun y => ‖f j y‖)
  have hnorm_int : ∀ j, Integrable (fun y => ‖f j y‖) ν := fun j => (hf j).norm

  have ha0 : 0 ≤ a := fun p => by
    rw [Pi.zero_apply, ha]
    exact integral_nonneg fun _ => norm_nonneg _
  have hb_sum : Summable (a ∘ e) := by
    have h0 : 0 ≤ a ∘ e := fun p => ha0 (e p)
    refine (summable_prod_of_nonneg h0).2 ⟨fun j => ?_, ?_⟩
    · simp only [Function.comp_apply, hae]
      exact (hP j _ (hnorm_int j)).summable
    · simp only [Function.comp_apply, hae]
      have h1 : ∀ j : I, ∑' δ : Γ, ∫ y in (fun y : Y => δ • y) ⁻¹' D (δ • j), ‖f j y‖ ∂ν =
          ∫ y, ‖f j y‖ ∂ν := fun j => (hP j _ (hnorm_int j)).tsum_eq
      simpa only [h1] using hs
  have ha_sum : Summable a := e.summable_iff.1 hb_sum
  have hc_sum : Summable c := ha_sum.of_norm_bounded fun p => by
    rw [hc, ha]
    exact norm_integral_le_integral_norm _

  have hFint : ∀ (i : I) (γ : Γ), Integrable (fun y => f (γ • i) (γ • y)) (ν.restrict (D i)) :=
    fun i γ => ((hν γ).integrable_comp_of_integrable (hf (γ • i))).restrict
  have hFsum : ∀ i, Summable fun γ : Γ => ∫ y in D i, ‖f (γ • i) (γ • y)‖ ∂ν := fun i => by
    simpa only [ha] using ha_sum.prod_factor i
  have hmain := fun i => integrable_tsum_of_summable_integral_norm (ν.restrict (D i))
    (fun (γ : Γ) (y : Y) => f (γ • i) (γ • y)) (hFint i) (hFsum i)
  refine ⟨fun i => (hmain i).1, ?_, ?_⟩
  · refine Summable.of_nonneg_of_le (fun i => integral_nonneg fun y => norm_nonneg _)
      (fun i => (hmain i).2) ?_
    simpa only [ha] using ((summable_prod_of_nonneg ha0).1 ha_sum).2
  · have hrow : ∀ i, ∫ y in D i, ∑' γ : Γ, f (γ • i) (γ • y) ∂ν = ∑' γ : Γ, c (i, γ) :=
      fun i => (integral_tsum_of_summable_integral_norm (hFint i) (hFsum i)).symm.trans
        (tsum_congr fun γ => (hc (i, γ)).symm)
    have hd : Summable fun p : I × Γ =>
        ∫ y in (fun y : Y => p.2 • y) ⁻¹' D (p.2 • p.1), f p.1 y ∂ν := by
      have h1 := e.summable_iff.2 hc_sum
      simpa only [Function.comp_def, hce] using h1
    calc ∑' i, ∫ y in D i, ∑' γ : Γ, f (γ • i) (γ • y) ∂ν = ∑' i, ∑' γ : Γ, c (i, γ) :=
          tsum_congr hrow
      _ = ∑' p, c p := (hc_sum.tsum_prod' hc_sum.prod_factor).symm
      _ = ∑' p, c (e p) := (e.tsum_eq c).symm
      _ = ∑' p : I × Γ, ∫ y in (fun y : Y => p.2 • y) ⁻¹' D (p.2 • p.1), f p.1 y ∂ν :=
          tsum_congr hce
      _ = ∑' j, ∑' δ : Γ, ∫ y in (fun y : Y => δ • y) ⁻¹' D (δ • j), f j y ∂ν :=
          hd.tsum_prod' hd.prod_factor
      _ = ∑' j, ∫ y, f j y ∂ν := tsum_congr fun j => (hP j (f j) (hf j)).tsum_eq

end GlobalTheory.SW
end

section

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.MinorInt

theorem integrableOn_minor_fin : ∀ (p q n : ℕ), 2 * (p + q) ≤ n → ∃ δ₀ : ℝ, 0 < δ₀ ∧ IntegrableOn (fun y : (Fin p ⊕ Fin q) → (Fin p ⊕ Fin q) → ℂ => (‖(Matrix.of y).toBlocks₁₁.det‖ ^ n)⁻¹) {y | ∀ a b, ‖((Matrix.of y)ᵀ * Matrix.fromBlocks (1 : Matrix (Fin p) (Fin p) ℂ) 0 0 (-1 : Matrix (Fin q) (Fin q) ℂ) * (Matrix.of y).map conj - Matrix.fromBlocks (1 : Matrix (Fin p) (Fin p) ℂ) 0 0 (-1 : Matrix (Fin q) (Fin q) ℂ)) a b‖ < δ₀} volume := by
  intro p q n hn
  convert integrableOn_minor (Fin p) (Fin q) n (by simpa using hn)

end GlobalTheory.MinorInt
end
