module

public import Mathlib.Topology.Covering.Basic
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Compactness.CompactlyGeneratedSpace
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Topology.Maps.Proper.CompactlyGenerated
public import Mathlib.MeasureTheory.Integral.IntegrableOn

@[expose] public section

section

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas Asymptotics
open scoped ContDiff ENNReal Pointwise Matrix

noncomputable section

universe u

theorem isCoveringMapOn_of_proper {n : ℕ} {E : Type*} [TopologicalSpace E] [T2Space E] (z : E → V n)
    (U : Set (V n)) (hU : IsOpen U) (hz : ∀ x, z x ∈ U) (hl : IsLocalHomeomorph z)
    (hp : ∀ K : Set (V n), IsCompact K → K ⊆ U → IsCompact (z ⁻¹' K)) :
    IsCoveringMapOn z U ∧ ∀ y, (z ⁻¹' {y}).Finite := by
  let g : E → U := fun x => ⟨z x, hz x⟩
  have hgc : Continuous g := hl.continuous.subtype_mk _
  have hgl : IsLocalHomeomorph g :=
    IsLocalHomeomorph.of_comp (g := Subtype.val) (by simpa [Function.comp_def, g] using hl)
      hU.isOpenEmbedding_subtypeVal.isLocalHomeomorph hgc
  have hgp : IsProperMap g := by
    refine isProperMap_iff_isCompact_preimage.2 ⟨hgc, fun K hK => ?_⟩
    have h1 := hp (Subtype.val '' K) (hK.image continuous_subtype_val)
      (by rintro _ ⟨y, -, rfl⟩; exact y.2)
    have h2 : g ⁻¹' K = z ⁻¹' (Subtype.val '' K) := by
      ext x; simp only [Set.mem_preimage, Set.mem_image]
      constructor
      · intro hx; exact ⟨g x, hx, rfl⟩
      · rintro ⟨y, hy, hyx⟩
        have : y = g x := Subtype.ext hyx
        rw [← this]; exact hy
    rw [h2]; exact h1
  have hfib : ∀ y (hy : y ∈ U), (z ⁻¹' {y}).Finite := by
    intro y hy
    have h2 : z ⁻¹' {y} = g ⁻¹' {⟨y, hy⟩} := by
      ext x; simp [g, Subtype.ext_iff]
    rw [h2]
    refine (hgp.isCompact_preimage isCompact_singleton).finite ?_
    refine (hgl.isLocalHomeomorphOn.mono (Set.subset_univ _)).isDiscrete_of_image ?_
    refine (Set.subsingleton_singleton.anti (Set.image_preimage_subset _ _)).isDiscrete
  refine ⟨?_, fun y => ?_⟩
  · refine IsCoveringMapOn.of_isCoveringMap_subtype hU hz ?_
    refine isCoveringMap_iff_isCoveringMapOn_univ.2 ?_
    refine hgp.isClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn (fun x _ => ?_)
      hgl.isLocalHomeomorphOn
    have h2 : g ⁻¹' {x} = z ⁻¹' {(x : V n)} := by
      ext x'; simp [g, Subtype.ext_iff]
    rw [h2]; exact hfib x x.2
  · by_cases hy : y ∈ U
    · exact hfib y hy
    · convert Set.finite_empty
      ext x; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      intro h; exact hy (h ▸ hz x)

section atlas

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]

theorem transition_zero_eq_one (A : WeightedAtlas n Y ι La) (i j : ι) (y : Y)
    (hi : y ∈ (A.chart i).source) (hj : y ∈ (A.chart j).source) : A.g 0 i j y = 1 := by
  have h := A.g_add 0 0 i j y hi hj
  rw [add_zero] at h
  have hne := A.g_ne 0 i j y hi hj
  exact mul_left_cancel₀ hne ((h.symm).trans (mul_one _).symm)

theorem transition_nsmul_eq_pow (A : WeightedAtlas n Y ι La) (la : La) (m : ℕ) (i j : ι) (y : Y)
    (hi : y ∈ (A.chart i).source) (hj : y ∈ (A.chart j).source) :
    A.g (m • la) i j y = A.g la i j y ^ m := by
  induction m with
  | zero => rw [zero_nsmul, pow_zero, transition_zero_eq_one A i j y hi hj]
  | succ k ih => rw [succ_nsmul, A.g_add _ _ i j y hi hj, ih, pow_succ]

theorem weight_zero_eq_zero (A : WeightedAtlas n Y ι La) (i : ι) (y : Y)
    (hi : y ∈ (A.chart i).source) : A.ph 0 i y = 0 := by
  have h := A.ph_add 0 0 i y hi
  rw [add_zero] at h
  linarith

theorem weight_nsmul_eq_mul (A : WeightedAtlas n Y ι La) (la : La) (m : ℕ) (i : ι) (y : Y)
    (hi : y ∈ (A.chart i).source) : A.ph (m • la) i y = m * A.ph la i y := by
  induction m with
  | zero => rw [zero_nsmul, weight_zero_eq_zero A i y hi]; simp
  | succ k ih => rw [succ_nsmul, A.ph_add _ _ i y hi, ih]; push_cast; ring

theorem ratio_pow_chart_independent (A : WeightedAtlas n Y ι La) (la : La) (m : ℕ) (F w0 : ι → Y → ℂ)
    (hF : A.IsSec (m • la) F) (hw : A.IsSec la w0) (i j : ι) (y : Y)
    (hi : y ∈ (A.chart i).source) (hj : y ∈ (A.chart j).source) :
    F i y / w0 i y ^ m = F j y / w0 j y ^ m := by
  rw [hF.2 i j y (Set.mem_univ y) hi hj, hw.2 i j y (Set.mem_univ y) hi hj,
    transition_nsmul_eq_pow A la m i j y hi hj, mul_pow]
  exact mul_div_mul_left _ _ (pow_ne_zero _ (A.g_ne la i j y hi hj))

theorem ne_zero_of_overlap_ne_zero (A : WeightedAtlas n Y ι La) (la : La) (w0 : ι → Y → ℂ)
    (hw : A.IsSec la w0) (i j : ι) (y : Y)
    (hi : y ∈ (A.chart i).source) (hj : y ∈ (A.chart j).source) (h : w0 j y ≠ 0) :
    w0 i y ≠ 0 := by
  rw [hw.2 i j y (Set.mem_univ y) hi hj]
  exact mul_ne_zero (A.g_ne la i j y hi hj) h

theorem localCoordinates_eq_zmap (A : WeightedAtlas n Y ι La) (la : La) (w0 : ι → Y → ℂ)
    (s : Fin n → ι → Y → ℂ) (hw : A.IsSec la w0) (hs : ∀ k, A.IsSec la (s k)) (i : ι) (y : Y)
    (hi : y ∈ (A.chart i).source) :
    A.zLoc w0 s i (A.chart i y) = A.zmap w0 s y := by
  simp only [zLoc, zmap, (A.chart i).left_inv hi]
  congr 1
  funext k
  have := ratio_pow_chart_independent A la 1 (s k) w0 (by rw [one_nsmul]; exact hs k) hw i (A.pick y) y hi
    (A.mem_pick y)
  simpa using this

end atlas

theorem holo_restrict_open {n : ℕ} {M : Type*} [TopologicalSpace M] (z : M → V n) (u : M → ℂ)
    (hu : Holo n z u) (S : Set M) (hS : IsOpen S) [Nonempty S] :
    Holo n (fun x : S => z x) (fun x : S => u x) := by
  intro e he
  let f := hS.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph (Subtype.val : S → M)
  have hc : IsChart n z (f.symm.trans e) := by
    intro x hx
    simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      Set.mem_inter_iff, Set.mem_preimage, f, Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target] at hx
    obtain ⟨⟨x', rfl⟩, hx2⟩ := hx
    simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply, f,
      hS.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph_left_inv] at hx2 ⊢
    exact he hx2
  have h2 := hu _ hc
  have ht : (f.symm.trans e).target = e.target := by
    simp [f]
  rw [ht] at h2
  refine h2.congr (fun v hv => ?_)
  simp [f, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]

theorem sub_isBigO_of_det_ne_zero {n : ℕ} {q : V n → V n} {D : V n →L[ℂ] V n} {a : V n}
    (hq : HasFDerivAt q D a) (hD : LinearMap.det (D : V n →ₗ[ℂ] V n) ≠ 0) :
    (fun x => x - a) =O[𝓝 a] (fun x => q x - q a) := by
  let E : V n ≃L[ℂ] V n :=
    (LinearMap.equivOfDetNeZero (D : V n →ₗ[ℂ] V n) hD).toContinuousLinearEquiv
  have hE : ∀ x, E x = D x := by
    intro x
    rfl
  have h1 : (fun x => x - a) =O[𝓝 a] (fun x => D (x - a)) := by
    simpa [hE] using E.isBigO_sub_rev (𝓝 a) a
  have h3 : (fun x => D (x - a) - (q x - q a)) =o[𝓝 a] (fun x => D (x - a)) := by
    have := (hq.isLittleO.trans_isBigO h1).neg_left
    refine this.congr_left (fun x => ?_)
    abel
  have h4 := h3.right_isBigO_sub
  refine h1.trans (h4.congr_right (fun x => ?_))
  abel

section atlas

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]

theorem differentiableAt_localCoordinates (A : WeightedAtlas n Y ι La) (la : La) (w0 : ι → Y → ℂ)
    (s : Fin n → ι → Y → ℂ) (hw : A.IsSec la w0) (hs : ∀ k, A.IsSec la (s k)) (i : ι) (y : Y)
    (hi : y ∈ (A.chart i).source) (h0 : w0 i y ≠ 0) :
    DifferentiableAt ℂ (A.zLoc w0 s i) (A.chart i y) := by
  have hT : (A.chart i).target ∈ 𝓝 (A.chart i y) :=
    (A.chart i).open_target.mem_nhds ((A.chart i).map_source hi)
  have hd : ∀ F : ι → Y → ℂ, A.IsSec la F →
      DifferentiableAt ℂ (fun v => F i ((A.chart i).symm v)) (A.chart i y) := by
    intro F hF
    have := hF.1 i
    simp only [Set.preimage_univ, Set.inter_univ] at this
    exact (this.differentiableAt hT)
  rw [differentiableAt_euclidean]
  intro k
  simp only [zLoc, PiLp.toLp_apply, div_eq_mul_inv]
  refine (hd (s k) (hs k)).mul ((hd w0 hw).inv ?_)
  simpa [(A.chart i).left_inv hi] using h0

end atlas

end

end ReciprocityTheory.L2DbarEstimates.Y
end

section

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal

noncomputable section

universe u

variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La)

def bsTr (la : La) (U : Set Y) (a : ι → Y → ℂ) : Prop :=
  ∀ i j y, y ∈ U → y ∈ (A.chart i).source → y ∈ (A.chart j).source → a i y = A.g la i j y * a j y

theorem bsA_g_zero {i j : ι} {y : Y} (hi : y ∈ (A.chart i).source) (hj : y ∈ (A.chart j).source) :
    A.g 0 i j y = 1 := by
  have h := A.g_add 0 0 i j y hi hj
  rw [add_zero] at h
  have hne := A.g_ne 0 i j y hi hj
  have h2 : A.g 0 i j y * (A.g 0 i j y - 1) = 0 := by linear_combination -h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 hne
  · exact sub_eq_zero.mp h3

theorem bsA_g_nsmul (la : La) (k : ℕ) {i j : ι} {y : Y} (hi : y ∈ (A.chart i).source)
    (hj : y ∈ (A.chart j).source) : A.g (k • la) i j y = A.g la i j y ^ k := by
  induction k with
  | zero => rw [zero_nsmul, pow_zero]; exact bsA_g_zero A hi hj
  | succ k ih => rw [succ_nsmul, A.g_add _ _ i j y hi hj, ih, pow_succ]

theorem bsA_ph_zero {i : ι} {y : Y} (hi : y ∈ (A.chart i).source) : A.ph 0 i y = 0 := by
  have h := A.ph_add 0 0 i y hi
  rw [add_zero] at h
  linarith

theorem bsA_ph_nsmul (la : La) (k : ℕ) {i : ι} {y : Y} (hi : y ∈ (A.chart i).source) :
    A.ph (k • la) i y = k * A.ph la i y := by
  induction k with
  | zero => rw [zero_nsmul, bsA_ph_zero A hi]; simp
  | succ k ih => rw [succ_nsmul, A.ph_add _ _ i y hi, ih]; push_cast; ring

theorem bsA_ph_sub (la mu : La) {i : ι} {y : Y} (hi : y ∈ (A.chart i).source) :
    A.ph (la - mu) i y = A.ph la i y - A.ph mu i y := by
  have h := A.ph_add (la - mu) mu i y hi
  rw [sub_add_cancel] at h
  linarith

theorem bsA_tr_of_isSecOn {la : La} {U : Set Y} {a : ι → Y → ℂ} (h : A.IsSecOn la U a) :
    bsTr A la U a := by
  unfold WeightedAtlas.IsSecOn at h
  exact h.2

theorem bsA_isSecOn_mono {la : La} {U V : Set Y} {a : ι → Y → ℂ} (h : A.IsSecOn la U a)
    (hVU : V ⊆ U) : A.IsSecOn la V a := by
  unfold WeightedAtlas.IsSecOn at h ⊢
  exact And.intro (fun i => (h.1 i).mono (fun v hv => ⟨hv.1, hVU hv.2⟩))
    (fun i j y hy => h.2 i j y (hVU hy))

theorem bsA_tr_mul {la mu : La} {U : Set Y} {a b : ι → Y → ℂ} (ha : bsTr A la U a)
    (hb : bsTr A mu U b) : bsTr A (la + mu) U (fun i y => a i y * b i y) := by
  unfold bsTr at ha hb ⊢
  intro i j y hy hi hj
  show a i y * b i y = A.g (la + mu) i j y * (a j y * b j y)
  rw [ha i j y hy hi hj, hb i j y hy hi hj, A.g_add la mu i j y hi hj]
  ring

theorem bsA_tr_pow {la : La} {U : Set Y} {a : ι → Y → ℂ} (ha : bsTr A la U a) (k : ℕ) :
    bsTr A (k • la) U (fun i y => a i y ^ k) := by
  unfold bsTr at ha ⊢
  intro i j y hy hi hj
  show a i y ^ k = A.g (k • la) i j y * a j y ^ k
  rw [ha i j y hy hi hj, bsA_g_nsmul A la k hi hj, mul_pow]

theorem bsA_tr_ratio {la : La} {U : Set Y} {a b : ι → Y → ℂ} (ha : bsTr A la U a)
    (hb : bsTr A la U b) {i j : ι} {y : Y} (hy : y ∈ U) (hi : y ∈ (A.chart i).source)
    (hj : y ∈ (A.chart j).source) : a i y / b i y = a j y / b j y := by
  unfold bsTr at ha hb
  rw [ha i j y hy hi hj, hb i j y hy hi hj, mul_div_mul_left _ _ (A.g_ne la i j y hi hj)]

theorem bsA_ne_of_tr {la : La} {U : Set Y} {a : ι → Y → ℂ} (ha : bsTr A la U a) {i j : ι}
    {y : Y} (hy : y ∈ U) (hi : y ∈ (A.chart i).source) (hj : y ∈ (A.chart j).source)
    (h : a j y ≠ 0) : a i y ≠ 0 := by
  unfold bsTr at ha
  rw [ha i j y hy hi hj]
  exact mul_ne_zero (A.g_ne la i j y hi hj) h

theorem bsA_nsq_chart {la : La} {U : Set Y} {a : ι → Y → ℂ} (ha : bsTr A la U a) {i : ι} {y : Y}
    (hy : y ∈ U) (hi : y ∈ (A.chart i).source) :
    A.nsq la a y = ‖a i y‖ ^ 2 * Real.exp (-A.ph la i y) := by
  have hp := A.mem_pick y
  unfold bsTr at ha
  unfold WeightedAtlas.nsq
  have hg : 0 < ‖A.g la (A.pick y) i y‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr (A.g_ne la (A.pick y) i y hp hi)) 2
  rw [ha (A.pick y) i y hy hp hi, A.ph_trans la (A.pick y) i y hp hi, norm_mul, mul_pow, neg_sub,
    sub_eq_add_neg, Real.exp_add, Real.exp_log hg]
  ring

theorem continuousOn_section_chart {la : La} {a : ι → Y → ℂ} (ha : A.IsSec la a) (i : ι) :
    ContinuousOn (a i) (A.chart i).source := by
  unfold WeightedAtlas.IsSec WeightedAtlas.IsSecOn at ha
  have h1 := (ha.1 i).continuousOn
  have h2 : ContinuousOn ((a i ∘ (A.chart i).symm) ∘ (A.chart i)) (A.chart i).source :=
    h1.comp (A.chart i).continuousOn (fun z hz => ⟨(A.chart i).map_source hz, Set.mem_univ _⟩)
  refine h2.congr ?_
  intro z hz
  simp only [Function.comp_apply, (A.chart i).left_inv hz]

theorem bsA_ph_cont (la : La) (i : ι) : ContinuousOn (A.ph la i) (A.chart i).source := by
  have h1 := (A.smooth_ph la i).continuousOn
  have h2 : ContinuousOn ((A.ph la i ∘ (A.chart i).symm) ∘ (A.chart i)) (A.chart i).source :=
    h1.comp (A.chart i).continuousOn (fun z hz => (A.chart i).map_source hz)
  refine h2.congr ?_
  intro z hz
  simp only [Function.comp_apply, (A.chart i).left_inv hz]

theorem bsA_nsq_cont {la : La} {a : ι → Y → ℂ} (ha : A.IsSec la a) : Continuous (A.nsq la a) := by
  have htr : bsTr A la Set.univ a := bsA_tr_of_isSecOn A (U := Set.univ) ha
  rw [continuous_iff_continuousAt]
  intro y
  have hs : (A.chart (A.pick y)).source ∈ 𝓝 y :=
    (A.chart (A.pick y)).open_source.mem_nhds (A.mem_pick y)
  have hc : ContinuousOn (fun z => ‖a (A.pick y) z‖ ^ 2 * Real.exp (-A.ph la (A.pick y) z))
      (A.chart (A.pick y)).source :=
    ((continuousOn_section_chart A ha (A.pick y)).norm.pow 2).mul ((bsA_ph_cont A la (A.pick y)).neg.rexp)
  refine (hc.continuousAt hs).congr ?_
  filter_upwards [hs] with z hz
  exact (bsA_nsq_chart A htr (Set.mem_univ z) hz).symm

theorem bsA_sqn_cont {la : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} (hw : ∀ k, A.IsSec la (w k)) :
    Continuous (A.sqn la w) := by
  show Continuous (fun y => ∑ k, A.nsq la (w k) y)
  exact continuous_finsetSum _ (fun k _ => bsA_nsq_cont A (hw k))

theorem bsA_nsq_nonneg (la : La) (a : ι → Y → ℂ) (y : Y) : 0 ≤ A.nsq la a y := by
  unfold WeightedAtlas.nsq
  positivity

theorem bsA_nsq_pos {la : La} {a : ι → Y → ℂ} {y : Y} (h : a (A.pick y) y ≠ 0) :
    0 < A.nsq la a y := by
  unfold WeightedAtlas.nsq
  exact mul_pos (pow_pos (norm_pos_iff.mpr h) 2) (Real.exp_pos _)

theorem bsA_sqn_pos {la : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {y : Y}
    (h : ∃ k, w k (A.pick y) y ≠ 0) : 0 < A.sqn la w y := by
  obtain ⟨k, hk⟩ := h
  show 0 < ∑ k, A.nsq la (w k) y
  exact Finset.sum_pos' (fun m _ => bsA_nsq_nonneg A la (w m) y) ⟨k, Finset.mem_univ _, bsA_nsq_pos A hk⟩

end

end ReciprocityTheory.L2DbarEstimates.Y
end

section

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology
open scoped ContDiff ENNReal

noncomputable section

namespace WeightedAtlas

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La)

theorem g_self (la : La) (i : ι) {y : Y} (hy : y ∈ (A.chart i).source) : A.g la i i y = 1 := by
  have h := A.g_cocycle la i i i y hy hy hy
  have h0 := A.g_ne la i i y hy hy
  have h2 : A.g la i i y * (A.g la i i y - 1) = 0 := by rw [mul_sub, ← h]; ring
  rcases mul_eq_zero.1 h2 with h1 | h1
  · exact absurd h1 h0
  · exact sub_eq_zero.1 h1

theorem g_mul_g (la : La) (i j : ι) {y : Y} (hi : y ∈ (A.chart i).source)
    (hj : y ∈ (A.chart j).source) : A.g la i j y * A.g la j i y = 1 := by
  rw [← A.g_cocycle la i j i y hi hj hi, A.g_self la i hi]

theorem nsq_chart (la : La) (s : ι → Y → ℂ) (i : ι) {y : Y} (hy : y ∈ (A.chart i).source)
    (hs : s (A.pick y) y = A.g la (A.pick y) i y * s i y) :
    A.nsq la s y = ‖s i y‖ ^ 2 * Real.exp (-A.ph la i y) := by
  have hp := A.mem_pick y
  unfold nsq
  rw [hs, A.ph_trans la i (A.pick y) y hy hp]
  have h1 := A.g_mul_g la (A.pick y) i hp hy
  have hgn : ‖A.g la i (A.pick y) y‖ ≠ 0 := norm_ne_zero_iff.2 (A.g_ne la i _ y hy hp)
  have hn : ‖A.g la (A.pick y) i y‖ ^ 2 * ‖A.g la i (A.pick y) y‖ ^ 2 = 1 := by
    rw [← mul_pow, ← norm_mul, h1, norm_one, one_pow]
  rw [neg_sub, Real.exp_sub, Real.exp_log (by positivity), Real.exp_neg, norm_mul, mul_pow,
    div_eq_mul_inv]
  linear_combination (‖s i y‖ ^ 2 * (Real.exp (A.ph la i y))⁻¹) * hn

theorem aap_ph_zero (i : ι) {y : Y} (hy : y ∈ (A.chart i).source) : A.ph 0 i y = 0 := by
  have h := A.ph_add 0 0 i y hy
  rw [add_zero] at h
  linarith

theorem aap_ph_nsmul (L : La) (k : ℕ) (i : ι) {y : Y} (hy : y ∈ (A.chart i).source) :
    A.ph (k • L) i y = k * A.ph L i y := by
  induction k with
  | zero => simp [A.aap_ph_zero i hy]
  | succ k ih => rw [succ_nsmul, A.ph_add _ _ i y hy, ih]; push_cast; ring

theorem aap_lintegral_chart_le (i : ι) (f : Y → ℝ≥0∞) (hf : Measurable f) (s : Set (V n))
    (hs : s ⊆ (A.chart i).target) :
    ∫⁻ v in s, f ((A.chart i).symm v) *
        ENNReal.ofReal (Real.exp (A.ph A.kap i ((A.chart i).symm v))) ≤ ∫⁻ y, f y ∂A.mu := by
  set φ := A.chart i
  set dens : V n → ℝ≥0∞ := fun v => ENNReal.ofReal (Real.exp (A.ph A.kap i (φ.symm v)))
  set ν := (volume.restrict φ.target).withDensity dens
  have hsymm0 : AEMeasurable φ.symm (volume.restrict φ.target) :=
    φ.continuousOn_symm.aemeasurable φ.open_target.measurableSet
  have hsymm : AEMeasurable φ.symm ν := hsymm0.mono_ac (withDensity_absolutelyContinuous _ _)
  have hdens : AEMeasurable dens (volume.restrict φ.target) := by
    have hc : ContinuousOn dens φ.target :=
      ENNReal.continuous_ofReal.comp_continuousOn
        (Real.continuous_exp.comp_continuousOn (A.smooth_ph A.kap i).continuousOn)
    exact hc.aemeasurable φ.open_target.measurableSet
  have hmeas : A.mu.restrict φ.source = ν.map φ.symm := by
    ext B hB
    rw [Measure.restrict_apply hB, Measure.map_apply_of_aemeasurable hsymm hB, withDensity_apply',
      Measure.restrict_restrict' φ.open_target.measurableSet,
      A.mu_chart i _ (hB.inter φ.open_source.measurableSet) Set.inter_subset_right]
    have hset : φ '' (B ∩ φ.source) = φ.symm ⁻¹' B ∩ φ.target := by
      rw [Set.inter_comm, φ.image_source_inter_eq', Set.inter_comm]
    rw [hset]
  calc ∫⁻ v in s, f (φ.symm v) * dens v
      ≤ ∫⁻ v in φ.target, f (φ.symm v) * dens v := lintegral_mono_set hs
    _ = ∫⁻ v in φ.target, dens v * f (φ.symm v) := by simp_rw [mul_comm]
    _ = ∫⁻ v, f (φ.symm v) ∂ν := (lintegral_withDensity_eq_lintegral_mul₀ hdens
          (hf.comp_aemeasurable hsymm0)).symm
    _ = ∫⁻ y, f y ∂(ν.map φ.symm) := (lintegral_map' hf.aemeasurable hsymm).symm
    _ = ∫⁻ y in φ.source, f y ∂A.mu := by rw [hmeas]
    _ ≤ ∫⁻ y, f y ∂A.mu := setLIntegral_le_lintegral _ _

end WeightedAtlas

end

end ReciprocityTheory.L2DbarEstimates.Y
end
