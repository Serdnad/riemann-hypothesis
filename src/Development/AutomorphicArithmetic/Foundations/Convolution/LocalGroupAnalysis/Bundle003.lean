module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.Bundle001
public import CompanionTheory.AutomorphicTheory.UnitriangularMeasure.AdeleCoordinateMeasure.EllipticTorusNorm
public import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Action
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init
public import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles

@[expose] public section

section

open PositivityTheory.Rg.Tf.Geo

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.RightCosetSpace
open scoped ENNReal

private theorem UpperTheory.ConvolutionTheory.G.stage_key
    {X T : Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [LocallyCompactSpace X] [T2Space X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] [Group T] [TopologicalSpace T]
    [IsTopologicalGroup T] [LocallyCompactSpace T] [T2Space T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] (μ : Measure X) [μ.IsHaarMeasure]
    (ν : Measure T) [ν.IsHaarMeasure] [ν.IsInvInvariant] (i : T →* X) (hi : Continuous i)
    (hinj : Function.Injective i) (Λ : Subgroup T) [DiscreteTopology Λ] (Γ₀ : Subgroup X)
    [DiscreteTopology Γ₀] (hΛ : Λ.map i = Γ₀)
    (ρ : X → ℝ≥0∞) (hρ : Measurable ρ) (hρ1 : ∀ x, ∫⁻ t, ρ (i t * x) ∂ν = 1)
    (F : X → ℝ≥0∞) (hF : Measurable F) (hFi : ∀ t x, F (i t * x) = F x) :
    ∫⁻ x in fundamentalDomain Γ₀, F x ∂μ = ν (fundamentalDomain Λ) * ∫⁻ x, F x * ρ x ∂μ := by
  subst hΛ
  set D := fundamentalDomain Λ with hDdef
  set E := fundamentalDomain (Λ.map i) with hEdef
  have hD : IsFundamentalDomain Λ D ν := isFundamentalDomain_fundamentalDomain Λ ν
  have hE : IsFundamentalDomain (Λ.map i) E μ := isFundamentalDomain_fundamentalDomain _ μ
  have hc : Continuous fun p : X × T => i p.2⁻¹ * p.1 :=
    (hi.comp continuous_snd.inv).mul continuous_fst
  have hm : Measurable fun p : X × T => ρ (i p.2⁻¹ * p.1) := hρ.comp hc.measurable
  set ρ' : X → ℝ≥0∞ := fun x => ∫⁻ d in D, ρ (i d⁻¹ * x) ∂ν with hρ'
  have hρ'm : Measurable ρ' := hm.lintegral_prod_right'
  have hinv : ∀ x, ∫⁻ d, ρ (i d⁻¹ * x) ∂ν = 1 := fun x => by
    rw [← hρ1 x]
    exact lintegral_inv_eq_self (fun t => ρ (i t * x))
  have hsum : ∀ x, ∑' l : Λ, ρ' (i l * x) = 1 := fun x => by
    rw [← hinv x, hD.lintegral_eq_tsum']
    refine tsum_congr fun l => ?_
    simp only [hρ']
    refine lintegral_congr fun d => ?_
    simp [Subgroup.smul_def, mul_assoc]
  have hunf : ∫⁻ x, F x * ρ' x ∂μ = ∫⁻ x in E, F x ∂μ := by
    rw [hE.lintegral_eq_tsum'', ← lintegral_tsum]
    · refine lintegral_congr fun x => ?_
      rw [← (Subgroup.equivMapOfInjective Λ i hinj).toEquiv.tsum_eq]
      have : ∀ l : Λ, F ((Subgroup.equivMapOfInjective Λ i hinj).toEquiv l • x) *
          ρ' ((Subgroup.equivMapOfInjective Λ i hinj).toEquiv l • x) = F x * ρ' (i l * x) := fun l => by
        have h : (Subgroup.equivMapOfInjective Λ i hinj).toEquiv l • x = i l * x := rfl
        rw [h, hFi]
      simp only [this]
      rw [ENNReal.tsum_mul_left, hsum, mul_one]
    · intro g
      exact ((hF.mul hρ'm).comp (measurable_const_smul g)).aemeasurable
  have hfub : ∫⁻ x, F x * ρ' x ∂μ = ν D * ∫⁻ x, F x * ρ x ∂μ := by
    have h1 : ∀ x, F x * ρ' x = ∫⁻ d in D, F x * ρ (i d⁻¹ * x) ∂ν := fun x => by
      have hd : Measurable fun d : T => ρ (i d⁻¹ * x) :=
        hρ.comp ((hi.comp continuous_inv).mul continuous_const).measurable
      rw [lintegral_const_mul _ hd]
    simp only [h1]
    rw [lintegral_lintegral_swap]
    · have h2 : ∀ d : T, ∫⁻ x, F x * ρ (i d⁻¹ * x) ∂μ = ∫⁻ x, F x * ρ x ∂μ := fun d => by
        rw [← lintegral_mul_left_eq_self (fun y => F y * ρ y) (i d⁻¹)]
        refine lintegral_congr fun x => ?_
        rw [hFi]
      simp only [h2]
      rw [lintegral_const, Measure.restrict_apply_univ, mul_comm]
    · exact ((hF.comp measurable_fst).mul hm).aemeasurable
  rw [← hunf, hfub]

theorem UpperTheory.ConvolutionTheory.G.unitaryGroupGeometricSide_of_quotient_identities :
    Q1 → Q2 → U2 := by
  intro hQ1 hQ2 X T _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ _ ν _ _ _ i hi Λ _ Γ₀ _ hΛ hvol Φ hΦc hΦi hint
  have hD : IsFundamentalDomain Λ (fundamentalDomain Λ) ν := isFundamentalDomain_fundamentalDomain Λ ν
  have hvolD : quotientMeasure Λ ν Set.univ = ν (fundamentalDomain Λ) := quotientMeasure_univ ν hD
  have hD0 : ν (fundamentalDomain Λ) ≠ 0 := hD.measure_ne_zero (NeZero.ne ν)
  have hΦm : Measurable Φ := hΦc.measurable
  have hic : Continuous i := hi.continuous
  have hout : ∀ g, Φ (Quotient.out (RightCosetSpace.mk Γ₀ g)) = Φ g := fun g => by
    obtain ⟨γ, hγ⟩ := mk_eq_mk_iff.1 (Quotient.out_eq (RightCosetSpace.mk Γ₀ g))
    have hγm : (γ : X) ∈ Λ.map i := hΛ ▸ γ.2
    obtain ⟨t, -, ht⟩ := Subgroup.mem_map.1 hγm
    rw [← hγ, Subgroup.smul_def, smul_eq_mul, ← ht, hΦi]
  have key := fun ρ hρ hρ1 F hF hFi =>
    UpperTheory.ConvolutionTheory.G.stage_key μ ν i hic hi.injective Λ Γ₀ hΛ ρ hρ hρ1 F hF hFi
  have hEfin : ∫⁻ x in fundamentalDomain Γ₀, ‖Φ x‖ₑ ∂μ < ⊤ := by
    have h := hint.2
    rw [HasFiniteIntegral, lintegral_quotientMeasure] at h
    simpa only [hout] using h
  have hfin : ∀ ρ, IsNormAlong id i ν ρ → ∫⁻ x, ‖Φ x‖ₑ * ρ x ∂μ < ⊤ := fun ρ hρ => by
    have h := key ρ hρ.1 hρ.2 (fun x => ‖Φ x‖ₑ) hΦm.enorm (fun t x => by simp only [hΦi])
    rw [h] at hEfin
    by_contra hc
    rw [not_lt, top_le_iff] at hc
    rw [hc, ENNReal.mul_top hD0] at hEfin
    exact lt_irrefl _ hEfin
  refine ⟨?_, hfin⟩
  obtain ⟨ρ₀, hρc, hρn, -⟩ := hQ2 X T ν i hi
  have e1 := hQ1 X X T μ ν (MonoidHom.id X) i measurable_id hic Φ (fun x => (ρ₀ x : ℝ≥0∞)) hΦm hΦi hρn (hfin _ hρn)
  have hmeas : (μ.restrict (fundamentalDomain Γ₀)).map Φ =
      (ν (fundamentalDomain Λ) • μ.withDensity (fun x => (ρ₀ x : ℝ≥0∞))).map Φ := by
    rw [Measure.ext_iff_lintegral]
    intro f hf
    have hw : ∫⁻ a, f (Φ a) ∂μ.withDensity (fun x => (ρ₀ x : ℝ≥0∞)) =
        ∫⁻ a, f (Φ a) * (ρ₀ a : ℝ≥0∞) ∂μ := by
      rw [show (fun a => f (Φ a)) = f ∘ Φ from rfl,
        lintegral_withDensity_eq_lintegral_mul μ hρn.1 (hf.comp hΦm)]
      exact lintegral_congr fun a => mul_comm _ _
    rw [lintegral_map hf hΦm, lintegral_map hf hΦm, lintegral_smul_measure, hw, smul_eq_mul]
    exact key _ hρn.1 hρn.2 (fun x => f (Φ x)) (hf.comp hΦm) (fun t x => by simp only [hΦi])
  have hq : ∫ y, Φ (Quotient.out y) ∂quotientMeasure Γ₀ μ = ∫ g in fundamentalDomain Γ₀, Φ g ∂μ := by
    rw [integral_quotientMeasure]
    simp only [hout]
  have hz : ∫ g in fundamentalDomain Γ₀, Φ g ∂μ =
      ∫ x, Φ x ∂(ν (fundamentalDomain Λ) • μ.withDensity (fun x => (ρ₀ x : ℝ≥0∞))) := by
    have h1 : ∀ m : Measure X, ∫ z, z ∂(m.map Φ) = ∫ x, Φ x ∂m := fun m =>
      integral_map hΦm.aemeasurable aestronglyMeasurable_id
    rw [← h1, ← h1, hmeas]
  rw [hq, hz, integral_smul_measure, integral_withDensity_eq_integral_toReal_smul hρn.1
    (Filter.Eventually.of_forall fun x => ENNReal.coe_lt_top), hvolD, Complex.real_smul]
  congr 1
  have e2 : quotInt μ id i ν Φ = ∫ x, Φ x * (((ρ₀ x : ℝ≥0∞)).toReal : ℂ) ∂μ := e1
  rw [e2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [Complex.real_smul, mul_comm]
end

section

open PositivityTheory.Rg.Tf.Geo
open MeasureTheory Topology
open scoped ENNReal Pointwise

namespace UpperTheory.ConvolutionTheory.G

private theorem exists_bump {X : Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X]
    [LocallyCompactSpace X] [T2Space X] [SecondCountableTopology X]
    (H : Subgroup X) (hH : IsClosed (H : Set X)) :
    ∃ β : X → ℝ, Continuous β ∧ (∀ x, 0 ≤ β x) ∧ (∀ x, ∃ h ∈ H, β (h * x) ≠ 0) ∧
      ∀ C : Set X, IsCompact C → ∃ C' : Set X, IsCompact C' ∧
        ∀ h ∈ H, ∀ x ∈ C, β (h * x) ≠ 0 → h * x ∈ C' := by
  classical
  let K : CompactExhaustion X := (CompactExhaustion.choice X).shiftr.shiftr
  have hK0 : K 0 = ∅ := rfl
  have hK1 : K 1 = ∅ := rfl
  let S : ℕ → Set X := fun m => (H : Set X) * K m
  let O : ℕ → Set X := fun m => (H : Set X) * interior (K m)
  have hSc : ∀ m, IsClosed (S m) := fun m => hH.mul_right_of_isCompact (K.isCompact m)
  have hOo : ∀ m, IsOpen (O m) := fun m => isOpen_interior.mul_left
  have hQ : ∀ m, IsCompact (K (m + 2) \ O (m + 1)) := fun m => (K.isCompact _).diff (hOo _)
  have hSO : ∀ m, S m ⊆ O (m + 1) := fun m => Set.mul_subset_mul_left (K.subset_interior_succ m)
  have hd : ∀ m, Disjoint (K (m + 2) \ O (m + 1)) (S m) := fun m =>
    Set.disjoint_left.2 fun x hx hxS => hx.2 (hSO m hxS)
  choose f hf1 hf0 hfc hfI using fun m =>
    exists_continuous_one_zero_of_isCompact (hQ m) (hSc m) (hd m)
  have hself : ∀ m, K m ⊆ S m := fun m x hx => ⟨1, H.one_mem, x, hx, one_mul x⟩
  have hSmono : ∀ {a b : ℕ}, a ≤ b → S a ⊆ S b := fun hab =>
    Set.mul_subset_mul_left (K.subset hab)
  have hvan : ∀ {N m : ℕ}, N ≤ m → ∀ x ∈ S N, f m x = 0 := fun hNm x hx => hf0 _ (hSmono hNm hx)
  have hnn : ∀ m x, 0 ≤ f m x := fun m x => (hfI m x).1
  have hlf : LocallyFinite fun m => Function.support (f m) := by
    intro x
    obtain ⟨n, hn⟩ := K.exists_mem x
    refine ⟨interior (K (n + 1)), isOpen_interior.mem_nhds (K.subset_interior_succ n hn),
      (Set.finite_lt_nat (n + 1)).subset ?_⟩
    rintro m ⟨y, hy, hyU⟩
    by_contra hm
    exact hy (hvan (not_lt.1 hm) y (hself _ (interior_subset hyU)))
  have hfin : ∀ x, (Function.support fun m => f m x).Finite := by
    intro x
    obtain ⟨n, hn⟩ := K.exists_mem x
    refine (Set.finite_lt_nat n).subset ?_
    intro m hm
    by_contra hmn
    exact hm (hvan (not_lt.1 hmn) x (hself _ hn))
  refine ⟨fun x => ∑ᶠ m, f m x, continuous_finsum (fun m => (f m).continuous) hlf,
    fun x => finsum_nonneg fun m => hnn m x, ?_, ?_⟩
  · intro x
    have hex : ∃ n, x ∈ O n := by
      obtain ⟨n, hn⟩ := K.exists_mem x
      exact ⟨n + 1, 1, H.one_mem, x, K.subset_interior_succ n hn, one_mul x⟩
    have hspec := Nat.find_spec hex
    have hmin : ∀ n, n < Nat.find hex → x ∉ O n := fun n hn => Nat.find_min hex hn
    obtain ⟨m, hm⟩ : ∃ m, Nat.find hex = m + 2 := by
      rcases hN : Nat.find hex with _ | _ | m
      · rw [hN] at hspec
        obtain ⟨h, -, y, hy, -⟩ := hspec
        simp [hK0] at hy
      · rw [hN] at hspec
        obtain ⟨h, -, y, hy, -⟩ := hspec
        simp [hK1] at hy
      · exact ⟨m, rfl⟩
    rw [hm] at hspec
    obtain ⟨h, hh, y, hy, rfl⟩ := hspec
    have hyQ : y ∈ K (m + 2) \ O (m + 1) := by
      refine ⟨interior_subset hy, ?_⟩
      rintro ⟨h', hh', z, hz, rfl⟩
      refine hmin (m + 1) (by omega) ⟨h * h', H.mul_mem hh hh', z, hz, (mul_assoc _ _ _)⟩
    refine ⟨h⁻¹, H.inv_mem hh, ?_⟩
    rw [inv_mul_cancel_left]
    have h1 : f m y ≤ ∑ᶠ m, f m y := single_le_finsum m (hfin y) (fun j => hnn j y)
    have h2 : f m y = 1 := hf1 m hyQ
    intro h0
    simp only [h0, h2] at h1
    linarith
  · intro C hC
    obtain ⟨N, hN⟩ := K.exists_superset_of_isCompact hC
    refine ⟨⋃ m ∈ Finset.range N, tsupport (f m),
      (Finset.range N).isCompact_biUnion fun m _ => hfc m, ?_⟩
    intro h hh x hx hne
    obtain ⟨m, hm⟩ : ∃ m, f m (h * x) ≠ 0 := by
      by_contra hall
      push_neg at hall
      exact hne (finsum_eq_zero_of_forall_eq_zero hall)
    have hmN : m < N := by
      by_contra hmN
      exact hm (hvan (not_lt.1 hmN) _ ⟨h, hh, x, hN hx, rfl⟩)
    exact Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_range.2 hmN)) (subset_tsupport _ hm)

end UpperTheory.ConvolutionTheory.G

theorem UpperTheory.ConvolutionTheory.G.closedSubgroup_cutoff_exists :
    Q2 := by
  intro X T _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ν _ _ i hi
  have hH : IsClosed ((i.range : Subgroup X) : Set X) := by
    rw [MonoidHom.coe_range]; exact hi.isClosed_range
  obtain ⟨β, hβ, hβ0, hcov, hsupp⟩ := UpperTheory.ConvolutionTheory.G.exists_bump i.range hH
  have hB : ∀ C : Set X, IsCompact C → ∃ B : Set T, IsCompact B ∧
      ∀ t, ∀ x ∈ C, β (i t * x) ≠ 0 → t ∈ B := by
    intro C hC
    obtain ⟨C', hC', h⟩ := hsupp C hC
    refine ⟨i ⁻¹' (C' * C⁻¹), hi.isCompact_preimage (hC'.mul hC.inv), fun t x hx hne => ?_⟩
    exact ⟨i t * x, h _ ⟨t, rfl⟩ x hx hne, x⁻¹, Set.inv_mem_inv.2 hx, by simp⟩
  have hc : Continuous (Function.uncurry fun (x : X) (t : T) => β (i t * x)) :=
    hβ.comp ((hi.continuous.comp continuous_snd).mul continuous_fst)
  have hcx : ∀ x, Continuous fun t => β (i t * x) := fun x =>
    hβ.comp (hi.continuous.mul continuous_const)
  have hcs : ∀ x, HasCompactSupport fun t => β (i t * x) := by
    intro x
    obtain ⟨B, hBc, hB'⟩ := hB {x} isCompact_singleton
    refine HasCompactSupport.intro hBc fun t ht => ?_
    by_contra hne
    exact ht (hB' t x rfl hne)
  let D : X → ℝ := fun x => ∫ t, β (i t * x) ∂ν
  have hDc : Continuous D := by
    rw [continuous_iff_continuousAt]
    intro x₀
    obtain ⟨N, hNc, hN⟩ := exists_compact_mem_nhds x₀
    obtain ⟨B, hBc, hB'⟩ := hB N hNc
    have h1 : Continuous fun x => ∫ t in B, β (i t * x) ∂ν :=
      continuous_parametric_integral_of_continuous hc hBc
    refine h1.continuousAt.congr ?_
    filter_upwards [hN] with x hx
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => ?_
    by_contra hne
    exact ht (hB' t x hx hne)
  have hDpos : ∀ x, 0 < D x := by
    intro x
    obtain ⟨h, ⟨t₀, rfl⟩, hne⟩ := hcov x
    exact (hcx x).integral_pos_of_hasCompactSupport_nonneg_nonzero (hcs x)
      (fun t => hβ0 _) hne
  have hDinv : ∀ s x, D (i s * x) = D x := by
    intro s x
    have := integral_mul_right_eq_self (μ := ν) (fun t => β (i t * x)) s
    simpa [D, mul_assoc] using this
  refine ⟨fun x => Real.toNNReal (β x / D x),
    continuous_real_toNNReal.comp (hβ.div hDc fun x => (hDpos x).ne'), ⟨?_, ?_⟩, ?_⟩
  · exact (ENNReal.continuous_coe.comp
      (continuous_real_toNNReal.comp (hβ.div hDc fun x => (hDpos x).ne'))).measurable
  · intro x
    have hint : Integrable (fun t => β (i t * x) / D x) ν :=
      ((hcx x).integrable_of_hasCompactSupport (hcs x)).div_const _
    have h1 : ∫⁻ t, ((Real.toNNReal (β (i t * id x) / D (i t * id x)) : NNReal) : ℝ≥0∞) ∂ν =
        ∫⁻ t, ENNReal.ofReal (β (i t * x) / D x) ∂ν := by
      refine lintegral_congr fun t => ?_
      simp only [id, hDinv]
      rfl
    rw [h1, ← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun t => div_nonneg (hβ0 _) (hDpos x).le), integral_div]
    change ENNReal.ofReal (D x / D x) = 1
    rw [div_self (hDpos x).ne', ENNReal.ofReal_one]
  · intro C hC
    obtain ⟨C', hC', h⟩ := hsupp C hC
    refine ⟨C', hC', fun t x hx hne => h _ ⟨t, rfl⟩ x hx fun h0 => hne ?_⟩
    simp [h0]
end

section

open PositivityTheory.Rg.Tf.Geo
open MeasureTheory
open scoped ENNReal

private theorem finite_fiber_integral {X T : Type} [Group X] [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] [Group T]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (i : T →* X) (Φ : X → ℂ) (ρ : X → NNReal) (hΦ : Continuous Φ)
    (hρ : Continuous ρ) (hC : ∃ C, IsCompact C ∧ ∀ x, Φ x ≠ 0 → ∃ t, ∃ y ∈ C, x = i t * y)
    (h : ∀ C : Set X, IsCompact C → ∃ C' : Set X, IsCompact C' ∧ ∀ t, ∀ x ∈ C, ρ (i t * x) ≠ 0 → i t * x ∈ C') :
    ∫⁻ x, ‖Φ x‖ₑ * (ρ x : ℝ≥0∞) ∂μ < ⊤ := by
  obtain ⟨C, hC, hs⟩ := hC
  obtain ⟨C', hC', hs'⟩ := h C hC
  have hc : Continuous fun x => Φ x * ((ρ x : ℝ) : ℂ) :=
    hΦ.mul (Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp hρ))
  have hk : HasCompactSupport fun x => Φ x * ((ρ x : ℝ) : ℂ) := by
    refine HasCompactSupport.intro hC' fun x hx => ?_
    by_contra hne
    have h1 : Φ x ≠ 0 := left_ne_zero_of_mul hne
    have h2 : ρ x ≠ 0 := by
      intro h0
      exact hne (by simp [h0])
    obtain ⟨t, y, hy, rfl⟩ := hs x h1
    exact hx (hs' t y hy h2)
  have hi := (hc.integrable_of_hasCompactSupport (μ := μ) hk).2
  unfold HasFiniteIntegral at hi
  convert hi using 3 with x
  rw [enorm_mul]
  congr 1
  simp [eNorm_eq_nnNorm]

private theorem prod_isInvInvariant {T T' : Type} [Group T] [MeasurableSpace T] [MeasurableInv T] [Group T'] [MeasurableSpace T']
    [MeasurableInv T'] (ν : Measure T) (ν' : Measure T') [SFinite ν] [SFinite ν'] [ν.IsInvInvariant] [ν'.IsInvInvariant] :
    (ν.prod ν').IsInvInvariant := by
  constructor
  exact ((Measure.measurePreserving_inv ν).prod (Measure.measurePreserving_inv ν')).map_eq

theorem UpperTheory.ConvolutionTheory.G.orbitalIntegral_absolute_convergence :
    Q1 → Q2 → Q3 := by
  intro h1 h2 X T X' T' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ _ ν _ μ' _ ν' _ _ _ _ _
    i i' hi hi' Φ Φ' hΦ hΦ' hinv hinv' hC hC'
  obtain ⟨ρ, hρ, hn, hs⟩ := h2 X T ν i hi
  obtain ⟨ρ', hρ', hn', hs'⟩ := h2 X' T' ν' i' hi'
  have f1 := finite_fiber_integral μ i Φ ρ hΦ hρ hC hs
  have f2 := finite_fiber_integral μ' i' Φ' ρ' hΦ' hρ' hC' hs'
  have e1 := h1 X X T μ ν (MonoidHom.id X) i measurable_id hi.continuous Φ _ hΦ.measurable hinv hn f1
  have e2 := h1 X' X' T' μ' ν' (MonoidHom.id X') i' measurable_id hi'.continuous Φ' _ hΦ'.measurable hinv' hn' f2
  haveI := prod_isInvInvariant ν ν'
  have hn3 : IsNormAlong id (fun t : T × T' => (i t.1, i' t.2)) (ν.prod ν')
      (fun x : X × X' => (ρ x.1 : ℝ≥0∞) * (ρ' x.2 : ℝ≥0∞)) := by
    refine ⟨(hn.1.comp measurable_fst).mul (hn'.1.comp measurable_snd), fun x => ?_⟩
    have a1 : Measurable fun t => (ρ (i t * x.1) : ℝ≥0∞) :=
      hn.1.comp (hi.continuous.mul continuous_const).measurable
    have a2 : Measurable fun t => (ρ' (i' t * x.2) : ℝ≥0∞) :=
      hn'.1.comp (hi'.continuous.mul continuous_const).measurable
    have := lintegral_prod_mul (μ := ν) (ν := ν') a1.aemeasurable a2.aemeasurable
    have b1 := hn.2 x.1
    have b2 := hn'.2 x.2
    simp only [id] at b1 b2
    rw [b1, b2, mul_one] at this
    exact this
  have f3 : ∫⁻ x : X × X', ‖Φ x.1 * Φ' x.2‖ₑ * ((ρ x.1 : ℝ≥0∞) * (ρ' x.2 : ℝ≥0∞)) ∂(μ.prod μ') < ⊤ := by
    have a1 : Measurable fun x => ‖Φ x‖ₑ * (ρ x : ℝ≥0∞) := hΦ.measurable.enorm.mul hn.1
    have a2 : Measurable fun x => ‖Φ' x‖ₑ * (ρ' x : ℝ≥0∞) := hΦ'.measurable.enorm.mul hn'.1
    have := lintegral_prod_mul (μ := μ) (ν := μ') a1.aemeasurable a2.aemeasurable
    refine lt_of_eq_of_lt ?_ (this ▸ ENNReal.mul_lt_top f1 f2)
    refine lintegral_congr fun x => ?_
    rw [enorm_mul]
    ring
  have e3 := h1 (X × X') (X × X') (T × T') (μ.prod μ') (ν.prod ν') (MonoidHom.id _) (i.prodMap i') measurable_id
    (hi.continuous.prodMap hi'.continuous) (fun x => Φ x.1 * Φ' x.2) _
    ((hΦ.measurable.comp measurable_fst).mul (hΦ'.measurable.comp measurable_snd))
    (fun t x => by
      show Φ (i t.1 * x.1) * Φ' (i' t.2 * x.2) = _
      rw [hinv, hinv']) hn3 f3
  refine e3.trans (Eq.trans ?_ (congrArg₂ (· * ·) e1 e2).symm)
  rw [← integral_prod_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [MonoidHom.id_apply, ENNReal.toReal_mul, Complex.ofReal_mul]
  ring
end

section

open PositivityTheory.Rg.Tf.Geo
open NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.AdeleBaseChange
open scoped NumberField.AdeleRing TensorProduct

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem galAd_apply (σ : E ≃ₐ[F] E) (y : 𝔸[E]) : galAd σ y = σ • y := by
  have h : galAd σ = MulSemiringAction.toRingHom (E ≃ₐ[F] E) 𝔸[E] σ := by
    refine adeleRingHom_ext (K := F) (fun l => ?_) (fun a => ?_)
    · change adeleTensorEquiv F E (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F 𝔸[F])
        ((adeleTensorEquiv F E).symm (algebraMap E 𝔸[E] l))) = σ • algebraMap E 𝔸[E] l
      rw [adeleTensorEquiv_symm_algebraMap, Algebra.TensorProduct.map_tmul, adeleTensorEquiv_tmul,
        AdeleBaseChange.smul_algebraMap, map_one, map_one, mul_one]
      rfl
    · change adeleTensorEquiv F E (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F 𝔸[F])
        ((adeleTensorEquiv F E).symm (adeleMap F E a))) = σ • adeleMap F E a
      rw [adeleTensorEquiv_symm_adeleMap, Algebra.TensorProduct.map_tmul, adeleTensorEquiv_tmul,
        smul_adeleMap, map_one, map_one, one_mul]
      rfl
  rw [h]
  rfl

private theorem closedEmb (n : ℕ) : Topology.IsClosedEmbedding
    (mapGL n (adeleMap F E) : AdelicGLn.AdelicGL F n → AdelicGLn.AdelicGL E n) := by
  have hM : Topology.IsClosedEmbedding
      ((adeleMap F E).mapMatrix.toMonoidHom : Matrix (Fin n) (Fin n) 𝔸[F] → Matrix (Fin n) (Fin n) 𝔸[E]) :=
    Function.LeftInverse.isClosedEmbedding (f := fun M : Matrix (Fin n) (Fin n) 𝔸[E] => M.map (adeleRetraction F E))
      (fun M => Matrix.ext fun i j => adeleRetraction_adeleMap (M i j))
      (continuous_id.matrix_map continuous_adeleRetraction)
      (continuous_id.matrix_map continuous_adeleMap)
  exact @Topology.IsClosedEmbedding.units_map (AdelicGLn.AdelicMatrix F n) (AdelicGLn.AdelicMatrix E n)
    _ _ _ _ _ _ (adeleMap F E).mapMatrix.toMonoidHom hM

private theorem det_inc (n : ℕ) (g : AdelicGLn.AdelicGL F n) :
    AdelicGLn.det E n (mapGL n (adeleMap F E) g) = ideleEmbedding F E (AdelicGLn.det F n g) :=
  Units.ext ((adeleMap F E).map_det (g : Matrix (Fin n) (Fin n) 𝔸[F])).symm

private theorem det_gal (σ : E ≃ₐ[F] E) (n : ℕ) (g : AdelicGLn.AdelicGL E n) :
    AdelicGLn.det E n (mapGL n (galAd σ) g) = σ • (AdelicGLn.det E n g : IdeleGroup E) :=
  Units.ext ((((galAd σ).map_det (g : Matrix (Fin n) (Fin n) 𝔸[E])).symm).trans (galAd_apply σ _))

end

theorem UpperTheory.ConvolutionTheory.G.character_column_kernels_of_block_chi_c_of_block_chi_one :
    N5 := by
  intro F E _ _ _ _ _ _ σ _ n _
  refine ⟨closedEmb n, fun g => ?_, fun g => ?_⟩
  · change (IdeleGroup.ideleModule E (AdelicGLn.det E n (mapGL n (adeleMap F E) g)) : ℝ) =
      (IdeleGroup.ideleModule F (AdelicGLn.det F n g) : ℝ) ^ Module.finrank F E
    rw [det_inc, ← EllipticTorus.ideleModule_ideleNorm (K := F), ideleNorm_ideleEmbedding, map_pow,
      Positive.val_pow]
  · change IdeleGroup.ideleModule E (AdelicGLn.det E n (mapGL n (galAd σ) g)) =
      IdeleGroup.ideleModule E (AdelicGLn.det E n g)
    rw [det_gal, ← EllipticTorus.ideleModule_ideleNorm (K := F), ideleNorm_smul,
      EllipticTorus.ideleModule_ideleNorm]
end
