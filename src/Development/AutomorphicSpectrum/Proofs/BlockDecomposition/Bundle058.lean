module

public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle002
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EncardSmulMemLeEncardSmulInterNonempty
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle020
public import Mathlib.MeasureTheory.Measure.Haar.DistribChar
public import Mathlib.NumberTheory.LocalField.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle021
public import Mathlib.Topology.Instances.Matrix
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle022
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle059
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
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.PsiApply

@[expose] public section

section

open TensorProduct CrystallineSemistableComparison.Pb.Psi

namespace GlobalTheory.CompanionTheory.FrobFix

theorem extension_fixed : ∀ {W C₀ : Type} [CommRing W] [CommRing C₀] {K₀ : Type} [Field K₀] [Algebra W K₀] {L : Type 1} [AddCommGroup L] [Module W L] (k : K₀ →+* C₀) {B : Type} [Field B] [IsFractionRing W K₀] (ι : C₀ →+* B) (σB : B →+* B) (h : L →+ B) (E : K₀ ⊗[W] L →+ B), (∀ x y, E (x ⊗ₜ y) = ι (k x) * h y) → (∀ w, σB (ι (k (algebraMap W K₀ w))) = ι (k (algebraMap W K₀ w))) → (∀ y, σB (h y) = h y) → ∀ v : K₀ ⊗[W] L, σB (E v) = E v := by
  intro W C₀ _ _ K₀ _ _ L _ _ k B _ _ ι σB h E hE hW hy v
  have hinj : Function.Injective (ι.comp k) := (ι.comp k).injective
  have hg : ∀ x : K₀, σB (ι (k x)) = ι (k x) := by
    intro x
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := W) x
    have hb0 : algebraMap W K₀ b ≠ 0 :=
      (IsLocalization.map_units K₀ (⟨b, hb⟩ : nonZeroDivisors W)).ne_zero
    have hgb : ι (k (algebraMap W K₀ b)) ≠ 0 := by
      intro h0
      apply hb0
      apply hinj
      simpa using h0
    have hmul : ι (k (algebraMap W K₀ a / algebraMap W K₀ b)) * ι (k (algebraMap W K₀ b))
        = ι (k (algebraMap W K₀ a)) := by
      rw [← map_mul, ← map_mul, div_mul_cancel₀ _ hb0]
    apply mul_right_cancel₀ hgb
    calc σB (ι (k (algebraMap W K₀ a / algebraMap W K₀ b))) * ι (k (algebraMap W K₀ b))
        = σB (ι (k (algebraMap W K₀ a / algebraMap W K₀ b))) * σB (ι (k (algebraMap W K₀ b))) := by
          rw [hW b]
      _ = σB (ι (k (algebraMap W K₀ a))) := by rw [← map_mul, hmul]
      _ = ι (k (algebraMap W K₀ a)) := hW a
      _ = ι (k (algebraMap W K₀ a / algebraMap W K₀ b)) * ι (k (algebraMap W K₀ b)) := hmul.symm
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => rw [hE, map_mul, hg, hy]
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]

end GlobalTheory.CompanionTheory.FrobFix
end

section

open MeasureTheory Topology
open scoped ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.PeriodisedMean

theorem setLIntegral_tsum_comp_inv_eq : ∀ (N : Type) [Group N] [TopologicalSpace N] [IsTopologicalGroup N] [LocallyCompactSpace N] [SecondCountableTopology N] [T2Space N] [MeasurableSpace N] [BorelSpace N] (ν : Measure N) [ν.IsHaarMeasure] (Γ : Subgroup N) [Countable Γ] (𝓕N : Set N), IsFundamentalDomain Γ 𝓕N ν → ν 𝓕N < ⊤ → ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (dA : Measure V) [dA.IsAddHaarMeasure] (Λ : AddSubgroup V) [Countable Λ] (D : Set V), IsAddFundamentalDomain Λ D dA → dA D = 1 → ∀ l : N → V, Continuous l → (∀ x y, l (x * y) = l x + l y) → Function.Surjective l → (∀ γ ∈ Γ, l γ ∈ Λ) → ∀ f : V → ℝ≥0∞, Measurable f → ∫⁻ m in 𝓕N, ∑' a : Λ, f ((a : V) + l m⁻¹) ∂ν = ν 𝓕N * ∫⁻ x, f x ∂dA := by
  intro N _ _ _ _ _ _ _ _ ν _ Γ _ 𝓕N h𝓕 hfin V _ _ _ _ _ _ _ _ dA _ Λ _ D hD hD1 l hlc hlmul hlsurj hlΓ f hf
  obtain ⟨-, hR, -⟩ :=
    GlobalTheory.CompanionTheory.SW.LatticeUnimod.unimodular_of_isFundamentalDomain N Γ ν 𝓕N h𝓕 hfin
  have hlm : Measurable l := hlc.measurable

  set Ft : V → ℝ≥0∞ := fun x => ∑' a : Λ, f ((a : V) + x) with hFt
  have hFtm : Measurable Ft :=
    Measurable.tsum fun a => hf.comp (measurable_const.add measurable_id)
  have hper : ∀ b ∈ Λ, ∀ x, Ft (x + b) = Ft x := by
    intro b hb x
    simp only [hFt]
    rw [← (Equiv.addRight (⟨b, hb⟩ : Λ)).tsum_eq (fun a : Λ => f ((a : V) + x))]
    refine tsum_congr fun a => ?_
    simp only [Equiv.coe_addRight, AddSubgroup.coe_add]
    congr 1
    abel
  set h : N → ℝ≥0∞ := fun m => Ft (l m⁻¹) with hh
  have hinv : ∀ γ ∈ Γ, ∀ m, h (γ * m) = h m := by
    intro γ hγ m
    simp only [hh]
    rw [mul_inv_rev, hlmul]
    exact hper _ (hlΓ _ (Γ.inv_mem hγ)) _

  have hshift : ∀ n₀ : N, ∫⁻ m in 𝓕N, h (m * n₀) ∂ν = ∫⁻ m in 𝓕N, h m ∂ν := by
    intro n₀
    have hF : IsFundamentalDomain Γ ((· * n₀⁻¹) ⁻¹' 𝓕N) ν :=
      h𝓕.preimage_of_equiv (quasiMeasurePreserving_mul_right ν n₀⁻¹) (e := id)
        Function.bijective_id (fun γ x => by simp [Subgroup.smul_def, smul_eq_mul, mul_assoc])
    have hmp : MeasurePreserving (· * n₀) ν ν := measurePreserving_mul_right ν n₀
    have hemb : MeasurableEmbedding (· * n₀ : N → N) :=
      (MeasurableEquiv.mulRight n₀).measurableEmbedding
    have e1 := hmp.setLIntegral_comp_preimage_emb hemb h ((· * n₀⁻¹) ⁻¹' 𝓕N)
    have e2 : (· * n₀ : N → N) ⁻¹' ((· * n₀⁻¹) ⁻¹' 𝓕N) = 𝓕N := by
      ext x; simp
    rw [e2] at e1
    rw [e1]
    exact hF.setLIntegral_eq h𝓕 h (fun γ x => hinv γ γ.2 x)

  have hT : ∀ x, ∫⁻ m in 𝓕N, Ft (x + l m⁻¹) ∂ν = ∫⁻ m in 𝓕N, h m ∂ν := by
    intro x
    obtain ⟨y, rfl⟩ := hlsurj x
    rw [← hshift y⁻¹]
    refine lintegral_congr fun m => ?_
    simp only [hh]
    rw [mul_inv_rev, inv_inv, hlmul]

  have hfold : ∀ c : V, ∫⁻ x in D, Ft (x + c) ∂dA = ∫⁻ x, f x ∂dA := by
    intro c
    have e0 : ∫⁻ x, f (x + c) ∂dA = ∫⁻ x, f x ∂dA := lintegral_add_right_eq_self f c
    have e3 : ∫⁻ x in D, ∑' a : Λ, f ((a +ᵥ x) + c) ∂dA
        = ∑' a : Λ, ∫⁻ x in D, f ((a +ᵥ x) + c) ∂dA :=
      lintegral_tsum fun a => (hf.comp ((measurable_const_vadd a).add_const c)).aemeasurable
    rw [← e0, hD.lintegral_eq_tsum'' (fun x => f (x + c)), ← e3]
    refine lintegral_congr fun x => ?_
    simp only [hFt]
    refine tsum_congr fun a => ?_
    simp [AddSubgroup.vadd_def, vadd_eq_add, add_assoc]
  have hswapm : Measurable (Function.uncurry fun (x : V) (m : N) => Ft (x + l m⁻¹)) :=
    hFtm.comp (measurable_fst.add (hlm.comp measurable_snd.inv))
  calc ∫⁻ m in 𝓕N, ∑' a : Λ, f ((a : V) + l m⁻¹) ∂ν
      = ∫⁻ m in 𝓕N, h m ∂ν := rfl
    _ = ∫⁻ _x in D, (∫⁻ m in 𝓕N, h m ∂ν) ∂dA := by
        rw [setLIntegral_const, hD1, mul_one]
    _ = ∫⁻ x in D, ∫⁻ m in 𝓕N, Ft (x + l m⁻¹) ∂ν ∂dA :=
        lintegral_congr fun x => (hT x).symm
    _ = ∫⁻ m in 𝓕N, ∫⁻ x in D, Ft (x + l m⁻¹) ∂dA ∂ν :=
        lintegral_lintegral_swap hswapm.aemeasurable
    _ = ∫⁻ _m in 𝓕N, (∫⁻ x, f x ∂dA) ∂ν := lintegral_congr fun m => hfold _
    _ = ν 𝓕N * ∫⁻ x, f x ∂dA := by
        rw [setLIntegral_const, mul_comm]

end GlobalTheory.CompanionTheory.SW.PeriodisedMean
end

section

open MeasureTheory Topology
open scoped ENNReal NNReal Matrix Pointwise

namespace GlobalTheory.CompanionTheory.SplitExtLat

theorem exists_borel_section_ker :
    ∀ (P G₁ : Type) [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [LocallyCompactSpace P] [SecondCountableTopology P] [T2Space P] [MeasurableSpace P] [BorelSpace P] [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁] (ι : G₁ →* P) (π : P →* G₁) (hι : Continuous ι) (hπ : Continuous π) (hπι : ∀ u, π (ι u) = u) (Γ : Subgroup P) [Countable Γ], (∃ U ∈ 𝓝 (1 : P), ∀ γ ∈ Γ, γ ∈ U → γ = 1) → (∃ K : Set P, IsCompact K ∧ ∀ m ∈ π.ker, ∃ γ ∈ Γ, π γ = 1 ∧ γ * m ∈ K) → ∃ D : Set π.ker, MeasurableSet D ∧ (∀ x : π.ker, ∃! g : Γ.subgroupOf π.ker, g • x ∈ D) ∧ ∀ (ν : Measure π.ker) [ν.IsHaarMeasure], IsFundamentalDomain (Γ.subgroupOf π.ker) D ν ∧ ν D ≠ 0 ∧ ν D < ⊤ := by
  intro P G₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ι π hι hπ hπι Γ _ hU hK
  obtain ⟨U, hU, hU1⟩ := hU
  obtain ⟨K, hKc, hK⟩ := hK
  have hcl : IsClosed (π.ker : Set P) := by
    have : (π.ker : Set P) = π ⁻¹' {1} := by
      ext x
      simp [MonoidHom.mem_ker]
    rw [this]
    exact isClosed_singleton.preimage hπ
  have hemb : IsClosedEmbedding (Subtype.val : π.ker → P) := hcl.isClosedEmbedding_subtypeVal
  haveI : LocallyCompactSpace π.ker := hemb.locallyCompactSpace
  haveI : SecondCountableTopology π.ker := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : BorelSpace π.ker := Subtype.borelSpace _
  haveI : Countable (Γ.subgroupOf π.ker) :=
    Function.Injective.countable (f := fun h : Γ.subgroupOf π.ker =>
      (⟨((h : π.ker) : P), h.2⟩ : Γ)) (fun a b hab => by
        have h1 : ((a : π.ker) : P) = ((b : π.ker) : P) := congrArg (fun x : Γ => (x : P)) hab
        exact Subtype.ext (Subtype.ext h1))
  haveI : DiscreteTopology (Γ.subgroupOf π.ker) := by
    refine discreteTopology_of_isOpen_singleton_one ?_
    have hc : Continuous fun h : Γ.subgroupOf π.ker => ((h : π.ker) : P) :=
      continuous_subtype_val.comp continuous_subtype_val
    have : ({1} : Set (Γ.subgroupOf π.ker)) =
        (fun h : Γ.subgroupOf π.ker => ((h : π.ker) : P)) ⁻¹' interior U := by
      ext h
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      constructor
      · rintro rfl
        exact mem_interior_iff_mem_nhds.2 hU
      · intro hh
        have h1 : ((h : π.ker) : P) = 1 :=
          hU1 _ (Subgroup.mem_subgroupOf.1 h.2) (interior_subset hh)
        exact Subtype.ext (Subtype.ext h1)
    rw [this]
    exact isOpen_interior.preimage hc
  obtain ⟨D, hDm, hDu, hDf⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup (Γ.subgroupOf π.ker)
  refine ⟨D, hDm, hDu, fun ν _ => ⟨hDf ν, (hDf ν).measure_ne_zero (NeZero.ne ν), ?_⟩⟩
  have hKc' : IsCompact ((Subtype.val : π.ker → P) ⁻¹' K) := hemb.isCompact_preimage hKc
  refine lt_of_le_of_lt
    (GlobalTheory.measure_le_of_isFundamentalDomain_of_ae_covers (hDf ν)
      (D' := (Subtype.val : π.ker → P) ⁻¹' K) (.of_forall fun m => ?_)) hKc'.measure_lt_top
  obtain ⟨γ, hγ, hπγ, hmem⟩ := hK m m.2
  have hγk : γ ∈ π.ker := hπγ
  refine ⟨⟨⟨γ, hγk⟩, Subgroup.mem_subgroupOf.2 hγ⟩, ?_⟩
  exact hmem

end GlobalTheory.CompanionTheory.SplitExtLat
end

section

open MeasureTheory Topology
open scoped ENNReal

theorem _root_.GlobalTheory.T.fundamental_domain_integral_count_bound : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant]
    (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → ∀ (M : Set G), MeasurableSet M → ∀ (f : G → ℝ≥0∞), Measurable f →
    (∀ γ ∈ Γ, ∀ x, f (γ * x) = f x) → ∀ n : ℕ, (∀ x, Set.encard {γ : Γ | (γ : G) * x ∈ M} ≤ n) →
    ∫⁻ x in M, f x ∂μ ≤ n * ∫⁻ x in 𝓕, f x ∂μ := by
  first | exact @GlobalTheory.CompanionTheory.Growth.lintegral_le_mul_of_encard_le | exact GlobalTheory.CompanionTheory.Growth.lintegral_le_mul_of_encard_le | (intros; apply GlobalTheory.CompanionTheory.Growth.lintegral_le_mul_of_encard_le <;> assumption)
end

section

open MeasureTheory Topology
open scoped ENNReal NNReal Matrix Pointwise

theorem _root_.GlobalTheory.T.parabolic_haar_decomposition : ∀ (P G₁ : Type) [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [LocallyCompactSpace P] [SecondCountableTopology P] [T2Space P] [MeasurableSpace P] [BorelSpace P] [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁] (ι : G₁ →* P) (π : P →* G₁) (hι : Continuous ι) (hπ : Continuous π) (hπι : ∀ u, π (ι u) = u) (Γ : Subgroup P) (Γ₁ : Subgroup G₁) [Countable Γ] [Countable Γ₁], (∀ u ∈ Γ₁, ι u ∈ Γ) → ∀ (ν : Measure π.ker) [ν.IsHaarMeasure] (D : Set π.ker), MeasurableSet D → IsFundamentalDomain (Γ.subgroupOf π.ker) D ν → ν D ≠ 0 → ν D < ⊤ → ∃ δ : G₁ →* ℝ≥0, Measurable δ ∧ (∀ γ ∈ Γ₁, δ γ = 1) ∧ ∀ u, Measure.map (fun m : π.ker => MulAut.conjNormal (ι u) m) ν = δ u • ν := by
  first | exact @GlobalTheory.CompanionTheory.SplitExtLat.conj_haar_character | exact GlobalTheory.CompanionTheory.SplitExtLat.conj_haar_character | (intros; apply GlobalTheory.CompanionTheory.SplitExtLat.conj_haar_character <;> assumption)
end

section

open Matrix ValuativeRel MeasureTheory
open scoped Topology

namespace GlobalTheory.CompanionTheory.LocalModule

theorem distribHaarChar_det_eventually_eq_one :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (n : ℕ), ∀ᶠ g in nhds (1 : GL (Fin n) k),
        MeasureTheory.distribHaarChar k (Matrix.GeneralLinearGroup.det g) = 1 := by
  intro k _ _ _ _ n
  have hc : Continuous fun g : GL (Fin n) k => ((Matrix.GeneralLinearGroup.det g : kˣ) : k) := by
    have : (fun g : GL (Fin n) k => ((Matrix.GeneralLinearGroup.det g : kˣ) : k)) =
        fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k).det := rfl
    rw [this]
    exact Continuous.matrix_det Units.continuous_val
  have hO : IsOpen {x : k | valuation k (x - 1) < 1} := by
    have h : IsOpen {z : k | valuation k z < 1} := by simpa using (valuation k).isOpen_ball 1
    exact h.preimage (continuous_id.sub continuous_const)
  have hm : ∀ᶠ g in nhds (1 : GL (Fin n) k),
      ((Matrix.GeneralLinearGroup.det g : kˣ) : k) ∈ {x : k | valuation k (x - 1) < 1} := by
    refine hc.continuousAt.eventually (hO.mem_nhds ?_)
    simp
  filter_upwards [hm] with g hg
  refine distribHaarChar_eq_one_of_valuation_eq_one k _ ?_
  have hv : valuation k (((Matrix.GeneralLinearGroup.det g : kˣ) : k) - 1) < 1 := hg
  have h1 := Valuation.map_one_add_of_lt (valuation k) hv
  rwa [add_sub_cancel] at h1

end GlobalTheory.CompanionTheory.LocalModule
end

section

open Matrix

theorem _root_.GlobalTheory.T.isCompact_isOpen_comap_mulVecLin : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (g : Matrix (Fin n) (Fin n) k), IsUnit g → ∀ A : AddSubgroup (Fin n → k), IsCompact (A : Set (Fin n → k)) → IsOpen (A : Set (Fin n → k)) → IsCompact ((A.comap (Matrix.mulVecLin g).toAddMonoidHom : AddSubgroup (Fin n → k)) : Set (Fin n → k)) ∧ IsOpen ((A.comap (Matrix.mulVecLin g).toAddMonoidHom : AddSubgroup (Fin n → k)) : Set (Fin n → k)) := by
  first | exact @GlobalTheory.CompanionTheory.Dblock.ComapLat.comap_mulVec_compact_open | exact GlobalTheory.CompanionTheory.Dblock.ComapLat.comap_mulVec_compact_open | (intros; apply GlobalTheory.CompanionTheory.Dblock.ComapLat.comap_mulVec_compact_open <;> assumption)
end

section

open ValuativeRel MeasureTheory Matrix

theorem _root_.GlobalTheory.T.compact_scaled_into_nhds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (K : Set (Fin n → k)), IsCompact K → ∀ U ∈ nhds (0 : Fin n → k), ∀ ϖ : k, valuation k ϖ < 1 → ∃ l : ℕ, ∀ x ∈ K, ϖ ^ l • x ∈ U := by
  first | exact @GlobalTheory.CompanionTheory.CompactScaling.exists_pow_smul_mem | exact GlobalTheory.CompanionTheory.CompactScaling.exists_pow_smul_mem | (intros; apply GlobalTheory.CompanionTheory.CompactScaling.exists_pow_smul_mem <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.exists_compact_open_subgroup_mem : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (x : Fin n → k), ∃ A : AddSubgroup (Fin n → k), IsCompact (A : Set (Fin n → k)) ∧ IsOpen (A : Set (Fin n → k)) ∧ x ∈ A := by
  first | exact @GlobalTheory.CompanionTheory.LatticePoint.exists_compact_open_addSubgroup_mem | exact GlobalTheory.CompanionTheory.LatticePoint.exists_compact_open_addSubgroup_mem | (intros; apply GlobalTheory.CompanionTheory.LatticePoint.exists_compact_open_addSubgroup_mem <;> assumption)
end

section

open Matrix
open scoped Topology

theorem _root_.GlobalTheory.T.exists_open_compact_lattice_containing : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (K : Set (Fin n → k)), IsCompact K → ∃ A : AddSubgroup (Fin n → k), IsCompact (A : Set (Fin n → k)) ∧ IsOpen (A : Set (Fin n → k)) ∧ K ⊆ A := by
  first | exact @GlobalTheory.CompanionTheory.LocalLattice.exists_compact_open_addSubgroup | exact GlobalTheory.CompanionTheory.LocalLattice.exists_compact_open_addSubgroup | (intros; apply GlobalTheory.CompanionTheory.LocalLattice.exists_compact_open_addSubgroup <;> assumption)
end

section

open Matrix
open scoped Topology

theorem _root_.GlobalTheory.T.local_continuous_section_vecMul_orbit : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ζ : Fin n → k), ζ ≠ 0 → ∃ N : Set (Fin n → k), IsOpen N ∧ ζ ∈ N ∧ ∃ f : (Fin n → k) → GL (Fin n) k, ContinuousOn f N ∧ f ζ = 1 ∧ ∀ ξ ∈ N, ζ ᵥ* (f ξ : Matrix (Fin n) (Fin n) k) = ξ := by
  first | exact @GlobalTheory.CompanionTheory.OrbitSection.exists_local_section | exact GlobalTheory.CompanionTheory.OrbitSection.exists_local_section | (intros; apply GlobalTheory.CompanionTheory.OrbitSection.exists_local_section <;> assumption)
end

section

open NumberField NumberField.mixedEmbedding Module

namespace GlobalTheory.CompanionTheory.IntCount

theorem finite_and_ncard_le :
    ∀ (E : Type) [Field E] [NumberField E], ∃ (C : ℝ) (N : ℕ), ∀ R : ℝ, 1 ≤ R →
      {r : 𝓞 E | ∀ w : InfinitePlace E, w (r : E) ≤ R}.Finite ∧
      ({r : 𝓞 E | ∀ w : InfinitePlace E, w (r : E) ≤ R}.ncard : ℝ) ≤ C * R ^ N :=
  _root_.UpperTheory.Reformulated.B.FiniteAndNcardBound.finite_and_ncard_le

end GlobalTheory.CompanionTheory.IntCount
end
