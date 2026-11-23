module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001
public import Mathlib.Basic.Real.Basic
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle016
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsGlOfEquiv
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle026
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle009
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle020
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle008
public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.RingTheory.SimpleRing.Basic
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open scoped Matrix

namespace GlobalTheory.UTrans

open GlobalTheory.UTrans.Calc

private theorem sigma_hf_eq_hf_swap {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R)
    (G : Matrix (Fin n) (Fin n) R) (hσ : ∀ a, σ (σ a) = a) (hG : ∀ a b, σ (G a b) = G b a)
    (x y : Fin n → R) : σ (GlobalTheory.UTrans.hf σ G x y) = GlobalTheory.UTrans.hf σ G y x := by
  unfold GlobalTheory.UTrans.hf

  simp only [map_sum, map_mul, hσ, hG]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

private theorem hf_add_smul_self {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R)
    (G : Matrix (Fin n) (Fin n) R) (x y : Fin n → R) (c : R) (hc : σ c = c) :
    GlobalTheory.UTrans.hf σ G (x + c • y) (x + c • y) = GlobalTheory.UTrans.hf σ G x x
      + c * (GlobalTheory.UTrans.hf σ G y x + GlobalTheory.UTrans.hf σ G x y) + c * c * GlobalTheory.UTrans.hf σ G y y := by
  unfold GlobalTheory.UTrans.hf
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add (f := _), map_mul, hc, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

private theorem exists_eq_algebraMap_of_fixed' {K L : Type} [Field K] [Field L] [CharZero L] [Algebra K L]
    (σ : L →+* L) (δ : L) (hK : ∀ a : K, σ (algebraMap K L a) = algebraMap K L a)
    (hσδ : σ δ = -δ) (hspan : ∀ x : L, ∃ a b : K, x = algebraMap K L a + algebraMap K L b * δ)
    (z : L) (hz : σ z = z) : ∃ k : K, z = algebraMap K L k := by
  obtain ⟨a, b, rfl⟩ := hspan z
  refine ⟨a, ?_⟩
  rw [map_add (f := _), map_mul, hK, hK, hσδ] at hz
  have h2 : (2 : L) * (algebraMap K L b * δ) = 0 := by linear_combination -hz
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd h two_ne_zero
  · rw [h, add_zero]

private theorem involutive_of_anti_fixed_generator {K L : Type} [Field K] [Field L] [Algebra K L]
    (σ : L →+* L) (δ : L) (hK : ∀ a : K, σ (algebraMap K L a) = algebraMap K L a)
    (hσδ : σ δ = -δ) (hspan : ∀ x : L, ∃ a b : K, x = algebraMap K L a + algebraMap K L b * δ)
    (x : L) : σ (σ x) = x := by
  obtain ⟨a, b, rfl⟩ := hspan x
  simp only [map_add (f := _), map_mul, hK, hσδ, map_neg, neg_neg]

private theorem hf_smul_smul' {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R)
    (G : Matrix (Fin n) (Fin n) R) (y : Fin n → R) (c : R) (hc : σ c = c) :
    GlobalTheory.UTrans.hf σ G (c • y) (c • y) = c * c * GlobalTheory.UTrans.hf σ G y y := by
  unfold GlobalTheory.UTrans.hf
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, hc, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem real_isotropic_or_one_class : ∀ (K L : Type) [Field K] [Field L] [CharZero L] [Algebra K L] (σ : L →+* L) (δ : L), (∀ a : K, σ (algebraMap K L a) = algebraMap K L a) → δ ≠ 0 → σ δ = -δ → (∀ x : L, ∃ a b : K, x = algebraMap K L a + algebraMap K L b * δ) → Nonempty (K ≃+* ℝ) → ∀ (n : ℕ) (G : Matrix (Fin n) (Fin n) L), (∀ a b, σ (G a b) = G b a) → (∃ z : Fin n → L, z ≠ 0 ∧ GlobalTheory.UTrans.hf σ G z z = 0) ∨ ∀ x y : Fin n → L, GlobalTheory.UTrans.hf σ G x x ≠ 0 → GlobalTheory.UTrans.hf σ G y y ≠ 0 → ∃ a : L, GlobalTheory.UTrans.hf σ G y y = σ a * a * GlobalTheory.UTrans.hf σ G x x := by
  intro K L _ _ _ _ σ δ hK hδ hσδ hspan ⟨e⟩ n G hG
  have hσ : ∀ a : L, σ (σ a) = a := involutive_of_anti_fixed_generator σ δ hK hσδ hspan
  have hfix : ∀ z : L, σ z = z → ∃ k : K, z = algebraMap K L k :=
    exists_eq_algebraMap_of_fixed' σ δ hK hσδ hspan
  by_cases hiso : ∃ z : Fin n → L, z ≠ 0 ∧ GlobalTheory.UTrans.hf σ G z z = 0
  · exact Or.inl hiso
  right
  push_neg at hiso
  intro x y hx hy
  obtain ⟨p, hp⟩ := hfix _ (sigma_hf_eq_hf_swap σ G hσ hG x x)
  obtain ⟨q, hq⟩ := hfix _ (sigma_hf_eq_hf_swap σ G hσ hG y y)
  obtain ⟨m, hm⟩ := hfix (GlobalTheory.UTrans.hf σ G y x + GlobalTheory.UTrans.hf σ G x y)
    (by rw [map_add (f := _), sigma_hf_eq_hf_swap σ G hσ hG, sigma_hf_eq_hf_swap σ G hσ hG, add_comm])
  have hp0 : e p ≠ 0 := by
    intro h
    apply hx
    rw [hp, (map_eq_zero_iff e e.injective).mp h, map_zero]
  have hq0 : e q ≠ 0 := by
    intro h
    apply hy
    rw [hq, (map_eq_zero_iff e e.injective).mp h, map_zero]

  have hpos : 0 < e q / e p := by
    by_contra hneg
    push_neg at hneg
    have hlt : e q * e p < 0 := by
      have h1 : e q / e p < 0 := lt_of_le_of_ne hneg (div_ne_zero hq0 hp0)
      have h2 : e q * e p = e q / e p * (e p * e p) := by field_simp
      rw [h2]
      exact mul_neg_of_neg_of_pos h1 (mul_self_pos.mpr hp0)
    have hd : 0 ≤ discrim (e q) (e m) (e p) := by
      unfold discrim
      nlinarith [sq_nonneg (e m)]
    have hs : discrim (e q) (e m) (e p) = Real.sqrt (discrim (e q) (e m) (e p))
        * Real.sqrt (discrim (e q) (e m) (e p)) := (Real.mul_self_sqrt hd).symm
    have ht := (quadratic_eq_zero_iff hq0 hs ((-(e m) + Real.sqrt (discrim (e q) (e m) (e p)))
      / (2 * e q))).mpr (Or.inl rfl)
    set t : ℝ := (-(e m) + Real.sqrt (discrim (e q) (e m) (e p))) / (2 * e q) with ht_def
    have hT : q * (e.symm t * e.symm t) + m * e.symm t + p = 0 := by
      apply e.injective
      simp only [map_add (f := _), map_mul, RingEquiv.apply_symm_apply, map_zero]
      linear_combination ht
    have hTK : σ (algebraMap K L (e.symm t)) = algebraMap K L (e.symm t) := hK _
    apply hiso (x + algebraMap K L (e.symm t) • y)
    · intro h0
      have hx' : x = (-(algebraMap K L (e.symm t))) • y := by
        rw [neg_smul]
        exact eq_neg_of_add_eq_zero_left h0
      have hxx := hf_smul_smul' σ G y (-(algebraMap K L (e.symm t))) (by rw [map_neg, hTK])
      rw [← hx', hp, hq, neg_mul_neg, ← map_mul, ← map_mul] at hxx
      have hpk := congrArg e ((algebraMap K L).injective hxx)
      simp only [map_mul, RingEquiv.apply_symm_apply] at hpk
      rw [hpk] at hlt
      nlinarith [mul_self_nonneg (t * e q)]
    · rw [hf_add_smul_self σ G x y _ hTK, hm, hp, hq, ← map_mul, ← map_mul, ← map_mul, ← map_add (f := _),
        ← map_add, ← map_zero (algebraMap K L)]
      congr 1
      linear_combination hT

  refine ⟨algebraMap K L (e.symm (Real.sqrt (e q / e p))), ?_⟩
  rw [hK, hp, hq, ← map_mul, ← map_mul]
  congr 1
  apply e.injective
  simp only [map_mul, RingEquiv.apply_symm_apply]
  rw [Real.mul_self_sqrt hpos.le]
  field_simp

end GlobalTheory.UTrans
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Topology

namespace GlobalTheory.RootEx


open MeasureTheory ValuativeRel Matrix in
open scoped Topology Pointwise in
theorem _root_.GlobalTheory.RootEx.exists_isOpen_addSubgroup_add_eq {X : Type*}
    [AddCommGroup X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] {Φ : X → ℂ} (hlc : IsLocallyConstant Φ) (hcs : IsCompact (tsupport Φ)) :
    ∃ Λ : AddSubgroup X, IsOpen (Λ : Set X) ∧ ∀ x, ∀ y ∈ Λ, Φ (x + y) = Φ x := by
  classical
  obtain ⟨t, ht⟩ := hcs.elim_finite_subcover (fun c : ℂ => {x | Φ x = c})
    (fun c => hlc.isOpen_fiber c) (fun x _ => Set.mem_iUnion.2 ⟨Φ x, rfl⟩)
  have hV : ∀ c : ℂ, ∃ V ∈ 𝓝 (0 : X), c ≠ 0 → {x | Φ x = c} + V ⊆ {x | Φ x = c} := by
    intro c
    by_cases hc : c = 0
    · exact ⟨Set.univ, Filter.univ_mem, fun h => (h hc).elim⟩
    · have hsub : {x | Φ x = c} ⊆ tsupport Φ := fun x hx =>
        subset_tsupport Φ (by
          rw [Function.mem_support]
          rw [Set.mem_setOf_eq] at hx
          rw [hx]
          exact hc)
      obtain ⟨V, hV0, hVs⟩ := compact_open_separated_add_right
        (hcs.of_isClosed_subset (hlc.isClosed_fiber c) hsub) (hlc.isOpen_fiber c) le_rfl
      exact ⟨V, hV0, fun _ => hVs⟩
  choose V hV0 hVsub using hV
  have hW : (⋂ c ∈ t, (V c ∩ -V c)) ∈ 𝓝 (0 : X) :=
    (Filter.biInter_finset_mem t).2 fun c _ =>
      Filter.inter_mem (hV0 c) (neg_mem_nhds_zero X (hV0 c))
  have hstep : ∀ x, ∀ v ∈ (⋂ c ∈ t, (V c ∩ -V c)), Φ (x + v) = Φ x := by
    intro x v hv
    have hv' : ∀ c ∈ t, v ∈ V c ∧ -v ∈ V c := by
      intro c hc
      have h := Set.mem_iInter₂.1 hv c hc
      exact ⟨h.1, Set.mem_neg.1 h.2⟩
    by_cases h0 : Φ x = 0
    · by_contra hne
      have hne' : Φ (x + v) ≠ 0 := by rwa [h0] at hne
      have hxK : x + v ∈ tsupport Φ := subset_tsupport Φ hne'
      obtain ⟨c, hct, hc⟩ := Set.mem_iUnion₂.1 (ht hxK)
      have hc' : Φ (x + v) = c := hc
      have hc0 : c ≠ 0 := hc' ▸ hne'
      have h := hVsub c hc0 (Set.add_mem_add hc (hv' c hct).2)
      have h' : Φ (x + v + -v) = c := h
      rw [add_neg_cancel_right] at h'
      exact hc0 (h'.symm.trans h0)
    · have hxK : x ∈ tsupport Φ := subset_tsupport Φ h0
      obtain ⟨c, hct, hc⟩ := Set.mem_iUnion₂.1 (ht hxK)
      have hc' : Φ x = c := hc
      have hc0 : c ≠ 0 := hc' ▸ h0
      have h := hVsub c hc0 (Set.add_mem_add hc (hv' c hct).1)
      have h' : Φ (x + v) = c := h
      exact h'.trans hc'.symm
  refine ⟨AddSubgroup.closure (⋂ c ∈ t, (V c ∩ -V c)),
    AddSubgroup.isOpen_of_mem_nhds _ (g := 0)
      (Filter.mem_of_superset hW AddSubgroup.subset_closure), ?_⟩
  intro x y hy
  induction hy using AddSubgroup.closure_induction generalizing x with
  | mem y hy => exact hstep x y hy
  | zero => simp
  | add y z _ _ hy hz => rw [← add_assoc, hz, hy]
  | neg y _ hy =>
    have h := hy (x + -y)
    rw [neg_add_cancel_right] at h
    exact h.symm


open MeasureTheory ValuativeRel Matrix in
open scoped Topology Pointwise in
theorem _root_.GlobalTheory.RootEx.sb_matrix_exists_isOpen_addSubgroup :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (a b : Type) [Fintype a] [Fintype b], ∀ Φ ∈ _root_.GlobalTheory.SplitWeil.SB (Matrix a b k),
      ∃ Λ : AddSubgroup (Matrix a b k), IsOpen (Λ : Set (Matrix a b k)) ∧
        ∀ x, ∀ y ∈ Λ, Φ (x + y) = Φ x := by
  intro k _ _ _ _ a b _ _ Φ hΦ
  obtain ⟨hlc, hcs⟩ := hΦ
  exact _root_.GlobalTheory.RootEx.exists_isOpen_addSubgroup_add_eq hlc hcs

end GlobalTheory.RootEx
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

namespace GlobalTheory.RootEx

theorem exists_mem_SB_eq_one_on_compact (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] (C : Set (n → k)) (hC : IsCompact C) :
    ∃ χ ∈ SB (n → k), ∀ u ∈ C, χ u = 1 := by
  classical
  haveI : T2Space k := by
    letI := IsTopologicalAddGroup.rightUniformSpace k
    haveI := isUniformAddGroup_of_addCommGroup (G := k)
    infer_instance
  have ho : IsOpen (𝒪[k] : Set k) := Valuation.isOpen_integer
  have hc : IsCompact (𝒪[k] : Set k) := IsNonarchimedeanLocalField.isCompact_closedBall k 1
  let B : Set (n → k) := Set.univ.pi fun _ => (𝒪[k] : Set k)
  have hBo : IsOpen B := isOpen_set_pi Set.finite_univ fun _ _ => ho
  have hBc : IsCompact B := isCompact_univ_pi fun _ => hc
  let U : (n → k) → Set (n → k) := fun x => (Homeomorph.addLeft x) '' B
  have hUo : ∀ x, IsOpen (U x) := fun x => (Homeomorph.addLeft x).isOpenMap _ hBo
  have hUc : ∀ x, IsCompact (U x) := fun x => hBc.image (Homeomorph.addLeft x).continuous
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover U hUo fun x _ =>
    Set.mem_iUnion.mpr ⟨x, 0, fun _ _ => zero_mem _, by simp⟩
  set K : Set (n → k) := ⋃ x ∈ t, U x with hK
  have hKo : IsOpen K := isOpen_biUnion fun x _ => hUo x
  have hKc : IsCompact K := t.isCompact_biUnion fun x _ => hUc x
  have hcl : IsClopen K := ⟨hKc.isClosed, hKo⟩
  refine ⟨K.indicator fun _ => (1 : ℂ), ⟨?_, ?_⟩, fun u hu => Set.indicator_of_mem (ht hu) _⟩
  · refine (IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_
    by_cases hx : x ∈ K
    · filter_upwards [hKo.mem_nhds hx] with y hy
      simp [hx, hy]
    · filter_upwards [hcl.compl.isOpen.mem_nhds hx] with y hy
      simp [hx, Set.notMem_of_mem_compl hy]
  · exact HasCompactSupport.intro hKc fun x hx => Set.indicator_of_notMem hx _

end GlobalTheory.RootEx
end

section

open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.OpTrace

noncomputable section

namespace GlobalTheory.InvBilinTest

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]

local instance (p : Prop) : Decidable p := Classical.propDecidable p


open Classical in
def cosetInd (K : Subgroup G) (ho : IsOpen (K : Set G)) (hK : IsCompact (K : Set G)) (g : G) :
    SB G := by
  classical
  exact ⟨fun x => if x * g⁻¹ ∈ K then 1 else 0, by
    constructor
    · have h1 : IsOpen {x : G | x * g⁻¹ ∈ K} := ho.preimage (continuous_id.mul continuous_const)
      have h2 : IsClosed {x : G | x * g⁻¹ ∈ K} :=
        (K.isClosed_of_isOpen ho).preimage (continuous_id.mul continuous_const)
      rw [IsLocallyConstant.iff_exists_open]
      intro y
      by_cases hy : y * g⁻¹ ∈ K
      · exact ⟨_, h1, hy, fun x hx => by rw [if_pos hy]; exact if_pos hx⟩
      · exact ⟨_, h2.isOpen_compl, hy, fun x hx => by rw [if_neg hy]; exact if_neg hx⟩
    · refine HasCompactSupport.intro (hK.image (continuous_id.mul (continuous_const (y := g))))
        fun x hx => if_neg fun h => hx ⟨x * g⁻¹, h, by change (x * g⁻¹) * g = x; group⟩⟩


open Classical in
theorem cosetInd_apply (K : Subgroup G) (ho : IsOpen (K : Set G)) (hK : IsCompact (K : Set G))
    (g x : G) : (cosetInd K ho hK g).1 x = if x * g⁻¹ ∈ K then 1 else 0 := rfl

variable [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]
  {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ G V}
  {Y : Type} [AddCommGroup Y] [Module ℂ Y]


open Classical in
theorem _root_.GlobalTheory.InvBilinTest.integral_ite (K : Subgroup G) (ho : IsOpen (K : Set G)) (c : ℂ) :
    ∫ g, (if g ∈ K then c else 0) ∂μ = (μ.real K : ℂ) * c := by
  classical
  have hm : MeasurableSet (K : Set G) := ho.measurableSet
  have h : (fun g : G => if g ∈ K then c else 0) = (K : Set G).indicator (fun _ => c) := by
    ext g
    simp [Set.indicator_apply]
  rw [h, integral_indicator_const c hm, Complex.real_smul]

end GlobalTheory.InvBilinTest
end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology

namespace GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences

theorem comp_mem_SB_of_isInducing {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {i : Y → X}
    (hi : IsInducing i) (Φ : SB X) {C : Set X} (hC : IsClosed C) (hiC : ∀ y, i y ∈ C)
    (hs : ∀ x ∈ C, Φ.1 x ≠ 0 → x ∈ Set.range i) : (fun y => Φ.1 (i y)) ∈ SB Y := by
  refine ⟨Φ.2.1.comp_continuous hi.continuous, ?_⟩
  have h0 : IsClosed (Function.support Φ.1) := (Φ.2.1.isOpen_fiber 0).isClosed_compl
  have h1 : IsCompact (Function.support Φ.1) := Φ.2.2.of_isClosed_subset h0 subset_closure
  have h2 : IsCompact (i ⁻¹' (Function.support Φ.1 ∩ C)) :=
    hi.isCompact_preimage' (h1.inter_right hC) fun x hx => hs x hx.2 hx.1
  refine HasCompactSupport.intro' h2 ((h0.inter hC).preimage hi.continuous) fun y hy => ?_
  by_contra h
  exact hy ⟨h, hiC y⟩

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]


omit [DecidableEq a] [DecidableEq b] in
theorem isOpen_le_rank (κ : ℕ) : IsOpen {x : Matrix b a k | κ ≤ x.rank} := by
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  exact GlobalTheory.isOpen_setOf_le_rank k b a κ



end

end GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences
end
end

section

open MeasureTheory ValuativeRel Matrix IsLocalRing GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LatPair
open scoped Pointwise

namespace GlobalTheory.LatPair

theorem card_withLat_eq_card_withKer {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : Type} (L : Submodule (↥𝒪[k]) (n → k))
    [Submodule.IsFullLattice k L] : (withLat L).card = (withKer L).card := by
  classical
  obtain ⟨q⟩ : Nonempty (Unif k) := inferInstance
  have e : Red L ≃ₗ[𝓀[k]] Module.Dual 𝓀[k] (Red L) := (Module.Free.chooseBasis 𝓀[k] (Red L)).toDualEquiv
  have e' : {x : Red L // x ≠ 0} ≃ {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0} :=
    e.toEquiv.subtypeEquiv (fun x => by simp)
  refine Finset.card_eq_of_equiv ?_
  exact (Equiv.subtypeEquivRight (fun P => mem_withLat)).trans
    ((latEquiv L).symm.trans (e'.symm.trans ((kerEquiv L q).trans
      (Equiv.subtypeEquivRight (fun P => mem_withKer.symm)))))

end GlobalTheory.LatPair
end

section

noncomputable section
open MvPolynomial

namespace GlobalTheory.CompactHowe

theorem substF_scalar_X {ι : Type} [DecidableEq ι] {N n : ℕ} (τ₀ : ι) (ζ : ℂ) (p : ι × Fin N × Fin n) :
    substF (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) (fun τ => if τ = τ₀ then ζ • (1 : Matrix (Fin n) (Fin n) ℂ) else 1) (X p)
      = C (if p.1 = τ₀ then ζ else 1) * X p := by
  rw [substF_X, Finset.sum_eq_single p.2.1, Finset.sum_eq_single p.2.2]
  · obtain ⟨a, b⟩ := p
    by_cases h : a = τ₀
    · subst h; simp
    · simp [h]
  · intro l _ hl
    by_cases h : p.1 = τ₀ <;> simp [h, Matrix.one_apply_ne hl]
  · simp
  · intro k _ hk
    simp [Matrix.one_apply_ne hk]
  · simp

theorem mapDomain_fst_apply {ι : Type} [DecidableEq ι] {N n : ℕ} (k : ι × Fin N × Fin n →₀ ℕ) (τ₀ : ι) :
    Finsupp.mapDomain Prod.fst k τ₀ = ∑ p ∈ k.support, if p.1 = τ₀ then k p else 0 := by
  unfold Finsupp.mapDomain
  rw [Finsupp.sum_apply]
  unfold Finsupp.sum
  refine Finset.sum_congr rfl fun p _ => ?_
  dsimp only
  rw [Finsupp.single_apply]

theorem substF_scalar_monomial {ι : Type} [DecidableEq ι] {N n : ℕ} (τ₀ : ι) (ζ : ℂ) (k : ι × Fin N × Fin n →₀ ℕ) :
    GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) (fun τ => if τ = τ₀ then ζ • (1 : Matrix (Fin n) (Fin n) ℂ) else 1) (MvPolynomial.monomial k 1) = ζ ^ (Finsupp.mapDomain Prod.fst k τ₀) • MvPolynomial.monomial k 1 := by
  rw [monomial_eq, C_1, one_mul, Finsupp.prod, map_prod]
  simp only [map_pow, substF_scalar_X, mul_pow, Finset.prod_mul_distrib]
  rw [mapDomain_fst_apply, smul_eq_C_mul, ← Finset.prod_pow_eq_pow_sum, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [← map_pow]
  split_ifs <;> simp

end GlobalTheory.CompactHowe
end
end

section

open MeasureTheory

theorem _root_.GlobalTheory.T.exists_schwartz_heisenbergOperatorDerivative : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (w : V × V) (f : SchwartzMap V ℂ),
    ∃ g : SchwartzMap V ℂ, ∀ x, g x = GlobalTheory.GaussLine.dHeis β w ⇑f x := by
  first | exact @GlobalTheory.dHeis_schwartz | exact GlobalTheory.dHeis_schwartz | (intros; apply GlobalTheory.dHeis_schwartz <;> assumption)
end
