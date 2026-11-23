module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HasConductorMulShift
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle037
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle026
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle032
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle031
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.Topology.Instances.Matrix
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle033
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
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
public import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected
import Mathlib.Topology.InductiveDimension.Functions
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower

@[expose] public section

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

namespace GlobalTheory.LocConstTensor

theorem exists_sum (Z : Type) [TopologicalSpace Z] [T2Space Z] (V : Type) [AddCommGroup V]
    [Module ℂ V] (T : Z → V) (hT : IsLocallyConstant T) (K : Set Z) (hK : IsCompact K)
    (h0 : ∀ y, y ∉ K → T y = 0) :
    ∃ (m : ℕ) (v : Fin m → V) (Φ : Fin m → SB Z), ∀ y, T y = ∑ i, (Φ i).1 y • v i := by
  classical
  have hfin : (T '' K).Finite := by
    letI : TopologicalSpace V := ⊥
    haveI : DiscreteTopology V := ⟨rfl⟩
    exact (hK.image hT.continuous).finite_of_discrete
  let S : Finset V := hfin.toFinset.erase 0
  let e : Fin S.card ≃ S := S.equivFin.symm
  have hmem : ∀ w : V, w ≠ 0 → (fun y => if T y = w then (1 : ℂ) else 0) ∈ SB Z := by
    intro w hw
    refine ⟨hT.comp (fun u => if u = w then (1 : ℂ) else 0), ?_⟩
    refine HasCompactSupport.intro hK ?_
    intro y hy
    rw [h0 y hy, if_neg (Ne.symm hw)]
  refine ⟨S.card, fun i => (e i : V),
    fun i => ⟨_, hmem (e i) (Finset.ne_of_mem_erase (e i).2)⟩, fun y => ?_⟩
  have h1 : ∑ i, (if T y = (e i : V) then (1 : ℂ) else 0) • (e i : V)
      = ∑ w ∈ S, (if T y = w then (1 : ℂ) else 0) • w := by
    rw [← Finset.sum_coe_sort S]
    exact Equiv.sum_comp e (fun w : S => (if T y = (w : V) then (1 : ℂ) else 0) • (w : V))
  change T y = ∑ i, (if T y = (e i : V) then (1 : ℂ) else 0) • (e i : V)
  rw [h1]
  simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · by_contra hne
    apply h
    refine Finset.mem_erase.2 ⟨hne, hfin.mem_toFinset.2 ⟨y, ?_, rfl⟩⟩
    by_contra hy
    exact hne (h0 y hy)

end GlobalTheory.LocConstTensor
end

section

open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Topology
open scoped ENNReal

namespace GlobalTheory.SmGL

theorem exists_open_normalised_subgroup_subset (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] :
    ∀ U ∈ 𝓝 (1 : GL n k), ∃ J : Subgroup (GL n k), IsOpen (J : Set (GL n k)) ∧
      (J : Set (GL n k)) ⊆ U ∧ J ≤ KO k n ∧ ∀ x ∈ KO k n, ∀ j ∈ J, x * j * x⁻¹ ∈ J := by
  intro U hU
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have : NonarchimedeanAddGroup k := ⟨fun V hV => by
    obtain ⟨s, hs⟩ := SplitWeil.exists_cball_subset hV
    exact ⟨⟨⟨⟨⟨SplitWeil.cball s, SplitWeil.add_mem_cball⟩, by simp [SplitWeil.cball]⟩,
      SplitWeil.neg_mem_cball⟩, SplitWeil.isOpen_cball s⟩, hs⟩⟩
  have : TotallyDisconnectedSpace k := inferInstance
  have : TotallyDisconnectedSpace (Matrix n n k) :=
    inferInstanceAs (TotallyDisconnectedSpace (n → n → k))
  have : TotallyDisconnectedSpace (GL n k) :=
    ⟨(SplitFlip.isEmbedding_val_GL (k := k) (n := n)).isTotallyDisconnected
      (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩
  have : CompactSpace (KO k n) :=
    isCompact_iff_compactSpace.1 (SplitFlip.isCompact_KO (k := k) (n := n))
  have hV : IsOpen ((fun x : KO k n => (x : GL n k)) ⁻¹' interior U) :=
    isOpen_interior.preimage continuous_subtype_val
  have h1 : (1 : KO k n) ∈ (fun x : KO k n => (x : GL n k)) ⁻¹' interior U :=
    mem_interior_iff_mem_nhds.2 hU
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hV h1
  refine ⟨H.toSubgroup.map (KO k n).subtype, ?_, ?_, ?_, ?_⟩
  · exact (SplitFlip.isOpen_KO (k := k) (n := n)).isOpenMap_subtype_val _ H.isOpen
  · rintro _ ⟨y, hy, rfl⟩
    exact interior_subset (hH hy)
  · rintro _ ⟨y, -, rfl⟩
    exact y.2
  · rintro x hx _ ⟨y, hy, rfl⟩
    have hc : (⟨x, hx⟩ : KO k n) * y * (⟨x, hx⟩ : KO k n)⁻¹ ∈ H.toSubgroup :=
      H.isNormal'.conj_mem y hy (⟨x, hx⟩ : KO k n)
    exact Subgroup.mem_map_of_mem (KO k n).subtype hc

end GlobalTheory.SmGL
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology

theorem _root_.GlobalTheory.T.schwartzBruhat_sweep_smoothly_induced : ∀ (G X Y W : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [AddCommGroup W] [Module ℂ W] (r : X → G → X), (∀ x, r x 1 = x) → (∀ x g h, r x (g * h) = r (r x g) h) → Continuous (fun p : X × G => r p.1 p.2) → ∀ (j : Y → X), IsClosedEmbedding j → ∀ (P : Subgroup G) (K : Set G), IsCompact K → (∀ x, ∃ y, ∃ c ∈ K, x = r (j y) c) → ∀ (s : Y → P → Y), (∀ y (p : P), r (j y) p = j (s y p)) → (∀ y y' g, r (j y) g = j y' → g ∈ P) → ∀ (χ : G →* ℂˣ), IsSmoothChar χ → ∀ (σ : Representation ℂ P W) (ev : W ≃ₗ[ℂ] SB Y), (∀ (p : P) w y, (ev (σ p w)).1 y = (χ p : ℂ) * (ev w).1 (s y p)) → ∃ E : SB X ≃ₗ[ℂ] smoothPart (ind P σ), ∀ Φ g y, (ev ((E Φ).1.1 g)).1 y = (χ g : ℂ) * Φ.1 (r (j y) g) := by
  first | exact @GlobalTheory.SBInduced.sb_induced | exact GlobalTheory.SBInduced.sb_induced | (intros; apply GlobalTheory.SBInduced.sb_induced <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Topology

namespace GlobalTheory.SplitWeil

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable (k) in
theorem one_lt_resCard : 1 < resCard k := Finite.one_lt_card

theorem nabs_le_of_valuation_le {x y : kˣ} (h : valuation k (x : k) ≤ valuation k (y : k)) :
    nabs k x ≤ nabs k y := by
  borelize k
  obtain ⟨ν, hν, h1⟩ := exists_isUnitVol k
  have hx := measureReal_cball ν x
  have hy := measureReal_cball ν y
  have h2 : ν.real (𝒪[k] : Set k) = 1 := by rw [Measure.real, h1]; simp
  rw [h2, mul_one] at hx hy
  rw [← hx, ← hy]
  have h3 : cball x ⊆ cball y := fun z hz => le_trans (show valuation k z ≤ _ from hz) h
  exact measureReal_mono h3 (isCompact_cball y).measure_lt_top.ne

theorem nabs_lt_of_valuation_lt {x y : kˣ} (h : valuation k (x : k) < valuation k (y : k)) :
    nabs k x < nabs k y := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  have h0 : (ϖ : k) ≠ 0 := by simpa using hϖ.ne_zero
  have hy0 : 0 < valuation k (y : k) := by simp [zero_lt_iff]
  have hlt : valuation k ((x : k) * (y : k)⁻¹) < 1 := by
    rw [map_mul, map_inv₀, mul_inv_lt_iff₀ hy0, one_mul]; exact h
  let z : 𝒪[k] := ⟨(x : k) * (y : k)⁻¹, (Valuation.mem_integer_iff _ _).mpr hlt.le⟩
  have hz : z ∈ 𝓂[k] := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.mpr hlt
  have h1 : valuation k ((x : k) * (y : k)⁻¹) ≤ valuation k (ϖ : k) :=
    (mem_cball_uniformiser hϖ (x := Units.mk0 _ h0) rfl z).mpr hz
  have h2 : valuation k (x : k) ≤ valuation k ((Units.mk0 _ h0 * y : kˣ) : k) := by
    rw [map_mul, map_inv₀, mul_inv_le_iff₀ hy0] at h1
    rw [Units.val_mul, map_mul]
    exact h1
  have h3 := nabs_le_of_valuation_le h2
  rw [nabs_mul, nabs_uniformiser hϖ (x := Units.mk0 _ h0) rfl] at h3
  refine h3.trans_lt (mul_lt_of_lt_one_left (nabs_pos k y) (inv_lt_one_of_one_lt₀ ?_))
  exact_mod_cast one_lt_resCard k

theorem nabs_le_iff (x y : kˣ) : nabs k x ≤ nabs k y ↔ valuation k (x : k) ≤ valuation k (y : k) :=
  ⟨fun h => not_lt.mp fun h' => absurd h (not_le.mpr (nabs_lt_of_valuation_lt h')),
    nabs_le_of_valuation_le⟩

theorem nabs_eq_iff (x y : kˣ) : nabs k x = nabs k y ↔ valuation k (x : k) = valuation k (y : k) := by
  rw [le_antisymm_iff, le_antisymm_iff, nabs_le_iff, nabs_le_iff]

theorem nabs_eq_one_iff (x : kˣ) : nabs k x = 1 ↔ valuation k (x : k) = 1 := by
  rw [← nabs_one k, nabs_eq_iff, Units.val_one, map_one]

variable (k) in
theorem isLocallyConstant_nabs : IsLocallyConstant (nabs k) := by
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_
  obtain ⟨r, hr, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  have hr0 : r ≠ 0 := by simpa using hr
  have h1 : (fun z : kˣ => (z : k) - x) ⁻¹' cball (Units.mk0 r hr0 * x) ∈ 𝓝 x :=
    ((isOpen_cball _).preimage (Units.continuous_val.sub continuous_const)).mem_nhds (by simp [cball])
  filter_upwards [h1] with z hz
  rw [nabs_eq_iff]
  have h2 : valuation k ((z : k) - x) ≤ valuation k (r * x) := hz
  refine Valuation.map_eq_of_sub_lt _ (h2.trans_lt ?_)
  rw [map_mul]
  exact mul_lt_of_lt_one_left (by simp [zero_lt_iff]) hr1

theorem nabs_properties : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], (∀ x y : kˣ, nabs k (x * y) = nabs k x * nabs k y) ∧ (∀ x : kˣ, 0 < nabs k x) ∧ (∀ x y : kˣ, nabs k x ≤ nabs k y ↔ valuation k (x : k) ≤ valuation k (y : k)) ∧ (∀ x : kˣ, nabs k x = 1 ↔ valuation k (x : k) = 1) ∧ (∀ (ϖ : 𝒪[k]) (x : kˣ), Irreducible ϖ → (x : k) = (ϖ : k) → nabs k x = (resCard k : ℝ)⁻¹) ∧ IsLocallyConstant (nabs k) ∧ 1 < resCard k :=
  fun k _ _ _ _ => ⟨nabs_mul k, nabs_pos k, nabs_le_iff, nabs_eq_one_iff,
    fun _ _ h h' => nabs_uniformiser h h', isLocallyConstant_nabs k, one_lt_resCard k⟩

end GlobalTheory.SplitWeil
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

noncomputable section
namespace GlobalTheory.SBConv

section Abstract
variable {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]

theorem eventually_translate {F : G → ℂ} (hF : F ∈ SB G) :
    ∀ᶠ x in nhds (0 : G), ∀ g, F (g - x) = F g := by
  have hlc : IsLocallyConstant F := hF.1
  have hK : IsCompact (tsupport F) := hF.2
  have hz : ∀ z, z ∉ tsupport F → F z = 0 := fun z hz => by
    by_contra h
    exact hz (subset_tsupport F h)
  have step : ∀ᶠ x in nhds (0 : G), ∀ y ∈ tsupport F, F (y - x) = F y := by
    refine hK.eventually_forall_of_forall_eventually fun y _ => ?_
    have hy := hlc.eventually_eq y
    have h1 : Filter.Tendsto (fun p : G × G => p.2 - p.1) (nhds ((0 : G), y)) (nhds y) := by
      simpa using (continuous_snd.tendsto ((0 : G), y)).sub (continuous_fst.tendsto ((0 : G), y))
    have h2 : Filter.Tendsto (fun p : G × G => p.2) (nhds ((0 : G), y)) (nhds y) :=
      continuous_snd.tendsto _
    filter_upwards [h1.eventually hy, h2.eventually hy] with p hp1 hp2
    exact hp1.trans hp2.symm
  have step' : ∀ᶠ x in nhds (0 : G), ∀ y ∈ tsupport F, F (y - -x) = F y :=
    (continuous_neg.tendsto' (0 : G) 0 neg_zero).eventually step
  filter_upwards [step, step'] with x hx hx' g
  by_cases hg : g ∈ tsupport F
  · exact hx g hg
  · rw [hz g hg]
    by_cases hg' : g - x ∈ tsupport F
    · have h := hx' (g - x) hg'
      rw [sub_neg_eq_add, sub_add_cancel, hz g hg] at h
      exact h.symm
    · exact hz _ hg'

def translate (Ψ : SB G) (y : G) : SB G :=
  ⟨fun x => Ψ.1 (x - y), Ψ.2.1.comp_continuous (continuous_sub_right y),
    Ψ.2.2.comp_homeomorph (Homeomorph.subRight y)⟩

theorem isLocallyConstant_translate (Ψ : SB G) : IsLocallyConstant (translate Ψ) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro y
  have hmap : Filter.Tendsto (fun y' : G => y' - y) (nhds y) (nhds 0) := by
    simpa using (continuous_id.tendsto y).sub_const y
  filter_upwards [hmap.eventually (eventually_translate Ψ.2)] with y' hy'
  apply Subtype.ext
  funext x
  show Ψ.1 (x - y') = Ψ.1 (x - y)
  have h := hy' (x - y)
  rwa [sub_sub_sub_cancel_right] at h

theorem exists_conv [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [IsFiniteMeasureOnCompacts μ] (Φ Ψ : SB G) :
    ∃ w : SB G, (∀ x, w.1 x = ∫ y, Φ.1 y * Ψ.1 (x - y) ∂μ) ∧
      ∀ l : SB G →ₗ[ℂ] ℂ, l w = ∫ y, Φ.1 y * l (translate Ψ y) ∂μ := by
  have hT : IsLocallyConstant (fun y => Φ.1 y • translate Ψ y) :=
    IsLocallyConstant.comp₂ Φ.2.1 (isLocallyConstant_translate Ψ) (fun c f => c • f)
  have hz : ∀ y, y ∉ tsupport Φ.1 → Φ.1 y • translate Ψ y = 0 := by
    intro y hy
    have h0 : Φ.1 y = 0 := by
      by_contra h
      exact hy (subset_tsupport _ h)
    rw [h0, zero_smul]
  obtain ⟨w, hw⟩ := GlobalTheory.exists_weakIntegral_of_isLocallyConstant_of_isCompact G μ (SB G)
    (fun y => Φ.1 y • translate Ψ y) hT (tsupport Φ.1) Φ.2.2.isCompact hz
  refine ⟨w, fun x => ?_, fun l => ?_⟩
  · exact hw ((LinearMap.proj x).comp (SB G).subtype)
  · rw [hw l]
    simp only [map_smul, smul_eq_mul]

end Abstract

theorem exists_convolution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (ν : Measure k) [ν.IsAddHaarMeasure] (Φ Ψ : SB (n → k)), ∃ (T : (n → k) → SB (n → k)) (w : SB (n → k)), (∀ y x, (T y).1 x = Ψ.1 (x - y)) ∧ (∀ x, w.1 x = ∫ y, Φ.1 y * Ψ.1 (x - y) ∂(Measure.pi fun _ => ν)) ∧ (∀ x, w.1 x = ∫ y, Ψ.1 y * Φ.1 (x - y) ∂(Measure.pi fun _ => ν)) ∧ ∀ l : SB (n → k) →ₗ[ℂ] ℂ, l w = ∫ y, Φ.1 y * l (T y) ∂(Measure.pi fun _ => ν) := by
  intro k _ _ _ _ _ _ n _ _ ν _ Φ Ψ
  have : SecondCountableTopology k := GlobalTheory.SplitWeil.secondCountable k
  have : T2Space k := GlobalTheory.SplitWeil.t2Space k
  have : ν.Regular := inferInstance
  have : ν.IsNegInvariant := inferInstance
  obtain ⟨w, hw1, hw2⟩ := exists_conv (Measure.pi fun _ : n => ν) Φ Ψ
  refine ⟨translate Ψ, w, fun y x => rfl, hw1, fun x => ?_, hw2⟩
  rw [hw1 x]
  have h := integral_sub_left_eq_self (fun y => Φ.1 (x - y) * Ψ.1 y) (Measure.pi fun _ : n => ν) x
  simp only [sub_sub_cancel] at h
  refine h.trans ?_
  congr 1
  funext y
  exact mul_comm _ _

end GlobalTheory.SBConv
end
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

theorem _root_.GlobalTheory.T.schwartzBruhat_matrix_exists_open_addSubgroup_invariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : Type) [Fintype a] [Fintype b], ∀ Φ ∈ SB (Matrix a b k), ∃ Λ : AddSubgroup (Matrix a b k), IsOpen (Λ : Set (Matrix a b k)) ∧ ∀ x, ∀ y ∈ Λ, Φ (x + y) = Φ x := by
  first | exact @GlobalTheory.RootEx.sb_matrix_exists_isOpen_addSubgroup | exact GlobalTheory.RootEx.sb_matrix_exists_isOpen_addSubgroup | (intros; apply GlobalTheory.RootEx.sb_matrix_exists_isOpen_addSubgroup <;> assumption)
end

section

open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL

theorem _root_.GlobalTheory.T.schwartzBruhat_distribution_eq_zero_baire : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] (ι : Type) [Countable ι] (K : ι → ℕ → Subgroup G), (∀ i m, IsOpen (K i m : Set G) ∧ IsCompact (K i m : Set G)) → (∀ i, ∀ U ∈ nhds (1 : G), ∃ m, (K i m : Set G) ⊆ U) → ∀ D : SB G →ₗ[ℂ] ℂ, (∀ x : G, ∃ i, ∀ (m : ℕ) (φ : SB G), φ.1 = Set.indicator {g : G | ∃ a ∈ K i m, ∃ b ∈ K i m, g = a * x * b} (fun _ => (1 : ℂ)) → D φ = 0) → D = 0 := by
  first | exact @GlobalTheory.BaireDistribution.eq_zero | exact GlobalTheory.BaireDistribution.eq_zero | (intros; apply GlobalTheory.BaireDistribution.eq_zero <;> assumption)
end

section

open ValuativeRel Matrix IsLocalRing
open scoped Pointwise

noncomputable section
namespace GlobalTheory.LatPair
open SplitWeil

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type*}

theorem ite_mem_SB {X : Type*} [TopologicalSpace X] {p : X → Prop} [DecidablePred p] (h : IsClopen {x | p x})
    (hc : IsCompact {x | p x}) : (fun x => if p x then (1 : ℂ) else 0) ∈ SB X := by
  refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun x => ?_, HasCompactSupport.intro' hc h.1 fun x hx => if_neg hx⟩
  by_cases hx : p x
  · exact ⟨_, h.2, hx, fun y hy => (if_pos hy).trans (if_pos hx).symm⟩
  · exact ⟨_, h.compl.2, hx, fun y hy => (if_neg hy).trans (if_neg hx).symm⟩

variable [Fintype n] [Fintype n']

theorem isClopen_lattice (L : Submodule 𝒪[k] (n → k)) [L.IsFullLattice k] : IsClopen (L : Set (n → k)) := by
  classical
  haveI := t2Space k
  obtain ⟨g, rfl⟩ := exists_smul_lat (stdLat k n) L
  have h : ((g • stdLat k n : Submodule 𝒪[k] (n → k)) : Set (n → k)) =
      ⋂ i, (fun x => ((g⁻¹ : GL n k).val *ᵥ x) i) ⁻¹' (𝒪[k] : Set k) := by
    ext x
    simp only [SetLike.mem_coe, mem_smul_iff, mem_stdLat, Set.mem_iInter, Set.mem_preimage]
    rfl
  rw [h]
  refine isClopen_iInter_of_finite fun i => IsClopen.preimage ⟨(isCompact_int k).isClosed, isOpen_int k⟩ ?_
  exact (continuous_apply i).comp (continuous_const.matrix_mulVec continuous_id)


omit [Fintype n] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem maps_stdLat_iff {x : Matrix n n' k} :
    (∀ y ∈ stdLat k n', x *ᵥ y ∈ stdLat k n) ↔ ∀ i j, x i j ∈ 𝒪[k] := by
  classical
  simp only [mem_stdLat]
  refine ⟨fun h i j => ?_, fun h y hy i => sum_mem fun j _ => mul_mem (h i j) (hy j)⟩
  have := h (Pi.single j 1) (fun l => ?_) i
  · simpa using this
  · rw [Pi.single_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]

theorem isClopen_isCompact_maps (S : Submodule 𝒪[k] (n' → k)) (L : Submodule 𝒪[k] (n → k)) [S.IsFullLattice k]
    [L.IsFullLattice k] : IsClopen {x : Matrix n n' k | ∀ y ∈ S, x *ᵥ y ∈ L} ∧
      IsCompact {x : Matrix n n' k | ∀ y ∈ S, x *ᵥ y ∈ L} := by
  classical
  haveI := t2Space k
  obtain ⟨g, rfl⟩ := exists_smul_lat (stdLat k n') S
  obtain ⟨h, rfl⟩ := exists_smul_lat (stdLat k n) L
  let K : Set (Matrix n n' k) := Set.univ.pi fun _ => Set.univ.pi fun _ => (𝒪[k] : Set k)
  have hKc : IsCompact K := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_int k
  have hKo : IsOpen K :=
    isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => isOpen_int k
  have e : {x : Matrix n n' k | ∀ y ∈ g • stdLat k n', x *ᵥ y ∈ h • stdLat k n} = sideMul g h ⁻¹' K := by
    ext x
    have h1 : sideMul g h x ∈ K ↔ ∀ i j, ((h⁻¹ : GL n k).val * x * g.val) i j ∈ 𝒪[k] :=
      ⟨fun H i j => H i trivial j trivial, fun H i _ j _ => H i j⟩
    rw [Set.mem_preimage, h1, ← maps_stdLat_iff, Set.mem_setOf_eq]
    simp only [mem_smul_iff, ← mulVec_mulVec]
    refine ⟨fun H y hy => H (g • y) (by simpa using hy), fun H y hy => ?_⟩
    have := H _ hy
    rwa [show g.val *ᵥ (g⁻¹ • y) = y from smul_inv_smul g y] at this
  rw [e]
  exact ⟨IsClopen.preimage ⟨hKc.isClosed, hKo⟩ (sideMul g h).continuous, (sideMul g h).isCompact_preimage.2 hKc⟩

theorem latInd_mem_SB (S : Submodule 𝒪[k] (n' → k)) (L : Submodule 𝒪[k] (n → k)) [S.IsFullLattice k] [L.IsFullLattice k] :
    latInd S L ∈ SB (Matrix n n' k) := by
  classical
  exact ite_mem_SB (isClopen_isCompact_maps S L).1 (isClopen_isCompact_maps S L).2

theorem isClopen_isCompact_mapsPair (P : Pair k n') (Q : Pair k n) :
    IsClopen {x : Matrix n n' k | Maps P Q x} ∧ IsCompact {x : Matrix n n' k | Maps P Q x} := by
  have e : {x : Matrix n n' k | Maps P Q x} = {x : Matrix n n' k | ∀ y ∈ P.ker, x *ᵥ y ∈ Q.ker} ∩
      (fun x : Matrix n n' k => x *ᵥ P.vec - Q.vec) ⁻¹' (Q.ker : Set (n → k)) := by
    ext x
    exact maps_iff_glue P.hasVal_vec Q.hasVal_vec
  have h2 := (isClopen_lattice Q.ker).preimage (f := fun x : Matrix n n' k => x *ᵥ P.vec - Q.vec)
    ((continuous_id.matrix_mulVec continuous_const).sub continuous_const)
  obtain ⟨h1, hc⟩ := isClopen_isCompact_maps P.ker Q.ker
  rw [e]
  exact ⟨h1.inter h2, hc.inter_right h2.1⟩

theorem phiOne_mem_SB (P : Pair k n') (Q : Pair k n) : phiOne P Q ∈ SB (Matrix n n' k) := by
  classical
  exact ite_mem_SB (isClopen_isCompact_mapsPair P Q).1 (isClopen_isCompact_mapsPair P Q).2

end GlobalTheory.LatPair
end
end

section


theorem _root_.GlobalTheory.T.matrixFamilyBilateralSubstitution_scalar_monomial : ∀ {ι : Type} [DecidableEq ι] {N n : ℕ} (τ₀ : ι) (ζ : ℂ) (k : ι × Fin N × Fin n →₀ ℕ), GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) (fun τ => if τ = τ₀ then ζ • (1 : Matrix (Fin n) (Fin n) ℂ) else 1) (MvPolynomial.monomial k 1) = ζ ^ (Finsupp.mapDomain Prod.fst k τ₀) • MvPolynomial.monomial k 1 := by
  first | exact @GlobalTheory.CompactHowe.substF_scalar_monomial | exact GlobalTheory.CompactHowe.substF_scalar_monomial | (intros; apply GlobalTheory.CompactHowe.substF_scalar_monomial <;> assumption)
end

section


theorem _root_.GlobalTheory.T.matrixFamilyBilateralSubstitution_comp_eq_mul : ∀ {ι : Type} {N n : ℕ} (h h' : ι → Matrix (Fin N) (Fin N) ℂ) (g g' : ι → Matrix (Fin n) (Fin n) ℂ) (P : MvPolynomial (ι × Fin N × Fin n) ℂ), GlobalTheory.CompactHowe.substF h g (GlobalTheory.CompactHowe.substF h' g' P) = GlobalTheory.CompactHowe.substF (h * h') (g * g') P := by
  first | exact @GlobalTheory.CompactHowe.substF_mul | exact GlobalTheory.CompactHowe.substF_mul | (intros; apply GlobalTheory.CompactHowe.substF_mul <;> assumption)
end

section


theorem _root_.GlobalTheory.T.mapDomain_fst_eq_of_coeff_matrixFamilyBilateralSubstitution_ne_zero : ∀ {ι : Type} {N n : ℕ} (h : ι → Matrix (Fin N) (Fin N) ℂ) (g : ι → Matrix (Fin n) (Fin n) ℂ) (k k' : ι × Fin N × Fin n →₀ ℕ), AddMonoidAlgebra.coeff (GlobalTheory.CompactHowe.substF h g (MvPolynomial.monomial k 1)) k' ≠ 0 → Finsupp.mapDomain Prod.fst k' = Finsupp.mapDomain Prod.fst k := by
  first | exact @GlobalTheory.CompactHowe.mapDomain_fst_eq_of_coeff_substF_ne_zero | exact GlobalTheory.CompactHowe.mapDomain_fst_eq_of_coeff_substF_ne_zero | (intros; apply GlobalTheory.CompactHowe.mapDomain_fst_eq_of_coeff_substF_ne_zero <;> assumption)
end

section


theorem _root_.GlobalTheory.T.coeff_matrixFamilyBilateralSubstitution_monomial_continuous_algebraic : ∀ {ι : Type} {N n : ℕ} (k k' : ι × Fin N × Fin n →₀ ℕ), Continuous (fun p : (ι → Matrix (Fin N) (Fin N) ℂ) × (ι → Matrix (Fin n) (Fin n) ℂ) => AddMonoidAlgebra.coeff (GlobalTheory.CompactHowe.substF p.1 p.2 (MvPolynomial.monomial k 1)) k') ∧ ∀ (h : ι → Matrix (Fin N) (Fin N) ℂ) (g : ι → Matrix (Fin n) (Fin n) ℂ), (∀ i a b, IsAlgebraic ℚ (h i a b)) → (∀ i a b, IsAlgebraic ℚ (g i a b)) → IsAlgebraic ℚ (AddMonoidAlgebra.coeff (GlobalTheory.CompactHowe.substF h g (MvPolynomial.monomial k 1)) k') := by
  first | exact @GlobalTheory.SubstCoeff.coeff_substF_monomial_continuous_algebraic | exact GlobalTheory.SubstCoeff.coeff_substF_monomial_continuous_algebraic | (intros; apply GlobalTheory.SubstCoeff.coeff_substF_monomial_continuous_algebraic <;> assumption)
end
