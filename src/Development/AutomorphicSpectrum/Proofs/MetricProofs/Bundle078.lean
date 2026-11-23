module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GenericBlockMatrixIsBlockDiag
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.MemMCoordIdealOfAevalEqZero
public import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.SheetDensityEqSetSheetDensity
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle076
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle002
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle037

@[expose] public section

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.ValRing

section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem isPrime_mCoordIdeal (z : (Σ k, ι k) → ℂ) : (mCoordIdeal z).IsPrime :=
  RingHom.ker_isPrime _

theorem eval_ne_zero_of_notMem {z : (Σ k, ι k) → ℂ} {h : MRing ι} {d : K → ℕ}
    (hh : IsMultiHomog h d) (hn : h ∉ mCoordIdeal z) :
    eval z (map (Int.castRingHom ℂ) h) ≠ 0 := by
  intro h0
  refine hn (mem_mCoordIdeal_of_aeval_eq_zero z hh ?_)
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq_eval_map]
  simpa using h0

theorem aeval_ne_zero_of_notMem {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal x)) {h : MRing ι} {d : K → ℕ}
    (hh : IsMultiHomog h d) (hn : h ∉ mCoordIdeal z) : aeval x h ≠ 0 := fun h0 =>
  eval_ne_zero_of_notMem hh hn
    (eval_eq_zero_of_mem_mcPts hz (mem_mCoordIdeal_of_aeval_eq_zero x hh h0))

theorem exists_isValueAt {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal x)) {s : Ω} (hs : RegAt x (mCoordIdeal z) s) :
    ∃ v, IsValueAt x s z v := by
  obtain ⟨d, g, h, hg, hh, hn, heq⟩ := hs
  exact ⟨_, d, g, h, hg, hh, aeval_ne_zero_of_notMem hz hh hn, heq,
    eval_ne_zero_of_notMem hh hn, rfl⟩

theorem isValueAt_add {x : (Σ k, ι k) → Ω} {s t : Ω} {z : (Σ k, ι k) → ℂ} {v w : ℂ}
    (hv : IsValueAt x s z v) (hw : IsValueAt x t z w) : IsValueAt x (s + t) z (v + w) := by
  obtain ⟨d, g, h, hg, hh, hy, heq, hz0, rfl⟩ := hv
  obtain ⟨d', g', h', hg', hh', hy', heq', hz0', rfl⟩ := hw
  refine ⟨d + d', g * h' + g' * h, h * h', GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_add (GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_mul hg hh') ?_,
    GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_mul hh hh', ?_, ?_, ?_, ?_⟩
  · rw [add_comm d d']
    exact GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_mul hg' hh
  · rw [map_mul]; exact mul_ne_zero hy hy'
  · simp only [map_add (f := _), map_mul, heq, heq']; ring
  · simp only [map_mul]; exact mul_ne_zero hz0 hz0'
  · simp only [map_add (f := _), map_mul]
    field_simp

theorem regAt_mul {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} {s t : Ω}
    (hs : RegAt x (mCoordIdeal z) s) (ht : RegAt x (mCoordIdeal z) t) :
    RegAt x (mCoordIdeal z) (s * t) := by
  obtain ⟨d, g, h, hg, hh, hn, heq⟩ := hs
  obtain ⟨d', g', h', hg', hh', hn', heq'⟩ := ht
  refine ⟨d + d', g * g', h * h', GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_mul hg hg', GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_mul hh hh',
    fun hm => ((isPrime_mCoordIdeal z).mem_or_mem hm).elim hn hn', ?_⟩
  rw [map_mul, map_mul, heq, heq']; ring

theorem regAt_add {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} {s t : Ω}
    (hs : RegAt x (mCoordIdeal z) s) (ht : RegAt x (mCoordIdeal z) t) :
    RegAt x (mCoordIdeal z) (s + t) := by
  obtain ⟨d, g, h, hg, hh, hn, heq⟩ := hs
  obtain ⟨d', g', h', hg', hh', hn', heq'⟩ := ht
  refine ⟨d + d', g * h' + g' * h, h * h', GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_add (GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_mul hg hh') ?_,
    GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_mul hh hh',
    fun hm => ((isPrime_mCoordIdeal z).mem_or_mem hm).elim hn hn', ?_⟩
  · rw [add_comm d d']
    exact GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_mul hg' hh
  · simp only [map_add (f := _), map_mul, heq, heq']; ring

theorem one_notMem_mCoordIdeal (z : (Σ k, ι k) → ℂ) : (1 : MRing ι) ∉ mCoordIdeal z :=
  (Ideal.ne_top_iff_one _).1 (isPrime_mCoordIdeal z).ne_top

theorem regAt_zero (x : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ) : RegAt x (mCoordIdeal z) 0 :=
  ⟨0, 0, 1, GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_zero 0, GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_one, one_notMem_mCoordIdeal z, by simp⟩

theorem regAt_one (x : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ) : RegAt x (mCoordIdeal z) 1 :=
  ⟨0, 1, 1, GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_one, GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_one, one_notMem_mCoordIdeal z, by simp⟩

theorem isValueAt_zero_self (x : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ) : IsValueAt x 0 z 0 :=
  ⟨0, 0, 1, GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_zero 0, GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_one, by simp, by simp, by simp, by simp⟩

end

theorem regAt_valAt_ring : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (x : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ), z ∈ mcPts (mCoordIdeal x) → RegAt x (mCoordIdeal z) 0 ∧ RegAt x (mCoordIdeal z) 1 ∧ valAt x 0 z = 0 ∧ valAt x 1 z = 1 ∧ ∀ s t : Ω, RegAt x (mCoordIdeal z) s → RegAt x (mCoordIdeal z) t → RegAt x (mCoordIdeal z) (s * t) ∧ RegAt x (mCoordIdeal z) (s + t) ∧ valAt x (s * t) z = valAt x s z * valAt x t z ∧ valAt x (s + t) z = valAt x s z + valAt x t z := by
  intro K _ ι _ Ω _ x z hz
  refine ⟨regAt_zero x z, regAt_one x z, valAt_eq hz (isValueAt_zero_self x z),
    valAt_eq hz (isValueAt_one_self x z), fun s t hs ht => ⟨regAt_mul hs ht, regAt_add hs ht, ?_, ?_⟩⟩
  · obtain ⟨v, hv⟩ := exists_isValueAt hz hs
    obtain ⟨w, hw⟩ := exists_isValueAt hz ht
    rw [valAt_eq hz hv, valAt_eq hz hw, valAt_eq hz (isValueAt_mul hv hw)]
  · obtain ⟨v, hv⟩ := exists_isValueAt hz hs
    obtain ⟨w, hw⟩ := exists_isValueAt hz ht
    rw [valAt_eq hz hv, valAt_eq hz hw, valAt_eq hz (isValueAt_add hv hw)]

end GlobalTheory.CompanionTheory.Ar.PB.ValRing
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW.ValHolo

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem holoOn_eval {σ : Type} (A : FinHolAtlas e X) {W : Set X} {b : X → σ → ℂ}
    (hb : ∀ q, A.HoloOn W fun y => b y q) (p : MvPolynomial σ ℤ) :
    A.HoloOn W fun y => eval (b y) (map (Int.castRingHom ℂ) p) := by
  intro j
  induction p using MvPolynomial.induction_on with
  | C a =>
    simpa [Function.comp_def] using
      (analyticOnNhd_const (v := ((a : ℤ) : ℂ)) (s := (A.chart j).target ∩ (A.chart j).symm ⁻¹' W))
  | add p q hp hq =>
    convert hp.add hq using 1
    funext u
    simp [Function.comp_def]
  | mul_X p q hp =>
    simpa [Function.comp_def] using hp.mul (hb q j)

theorem continuousAt_of_holoOn (A : FinHolAtlas e X) {W : Set X} {f : X → ℂ} (hf : A.HoloOn W f) {y : X}
    (hy : y ∈ W) : ContinuousAt f y := by
  obtain ⟨j, hj⟩ := A.cover y
  have h1 : (A.chart j) y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' W :=
    ⟨(A.chart j).map_source hj, by
      rw [Set.mem_preimage, (A.chart j).left_inv hj]; exact hy⟩
  have h2 : ContinuousAt (f ∘ (A.chart j).symm) ((A.chart j) y) := (hf j _ h1).continuousAt
  have h3 : ContinuousAt (fun u => (f ∘ (A.chart j).symm) ((A.chart j) u)) y :=
    ContinuousAt.comp (f := A.chart j) h2 ((A.chart j).continuousAt hj)
  refine h3.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with u hu
  simp only [Function.comp_apply, (A.chart j).left_inv hu]

theorem isOpen_inter_ne (A : FinHolAtlas e X) {W : Set X} {f : X → ℂ} (hW : IsOpen W)
    (hf : A.HoloOn W f) : IsOpen (W ∩ {y | f y ≠ 0}) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨hy, h0⟩
  filter_upwards [hW.mem_nhds hy, (continuousAt_of_holoOn A hf hy).eventually_ne h0] with u h1 h2
  exact ⟨h1, h2⟩

theorem holoOn_div_congr (A : FinHolAtlas e X) {W : Set X} {f g v : X → ℂ} (hW : IsOpen W)
    (hf : A.HoloOn W f) (hg : A.HoloOn W g) (h0 : ∀ y ∈ W, g y ≠ 0) (hv : ∀ y ∈ W, v y = f y / g y) :
    A.HoloOn W v := by
  intro j
  have hO : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' W) :=
    (A.chart j).isOpen_inter_preimage_symm hW
  have h1 : AnalyticOnNhd ℂ (fun u => (f ∘ (A.chart j).symm) u / (g ∘ (A.chart j).symm) u)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' W) := fun u hu =>
    (hf j u hu).div (hg j u hu) (h0 _ hu.2)
  exact h1.congr hO fun u hu => (hv _ hu.2).symm

theorem holoOn_valAt (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (x : (Σ k, ι k) → Ω) (s : Ω) (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (W : Set X)
    (b : X → (Σ k, ι k) → ℂ) (y₀ : X) (hW : IsOpen W) (hy₀ : y₀ ∈ W) (hb : ∀ q, A.HoloOn W fun y => b y q)
    (hpt : ∀ y ∈ W, b y ∈ mcPts (mCoordIdeal x)) (hs : RegAt x (mCoordIdeal (b y₀)) s) :
    ∃ W' : Set X, IsOpen W' ∧ y₀ ∈ W' ∧ W' ⊆ W ∧ A.HoloOn W' fun y => valAt x s (b y) := by
  obtain ⟨d, g, h, hg, hh, hQ, heq⟩ := hs
  have hz : eval (b y₀) (map (Int.castRingHom ℂ) h) ≠ 0 := by
    intro h0
    refine hQ (mem_mCoordIdeal_of_aeval_eq_zero (b y₀) hh ?_)
    rw [← h0]
    rw [aeval_def, eval_map, Subsingleton.elim (algebraMap ℤ ℂ) (Int.castRingHom ℂ)]
  have hx : aeval x h ≠ 0 := fun h0 =>
    hz (eval_eq_zero_of_mem_mcPts (hpt y₀ hy₀) (mem_mCoordIdeal_of_aeval_eq_zero x hh h0))
  have Hg := holoOn_eval A hb g
  have Hh := holoOn_eval A hb h
  refine ⟨W ∩ {y | eval (b y) (map (Int.castRingHom ℂ) h) ≠ 0}, isOpen_inter_ne A hW Hh, ⟨hy₀, hz⟩,
    Set.inter_subset_left, ?_⟩
  refine holoOn_div_congr A (isOpen_inter_ne A hW Hh) (fun j => (Hg j).mono ?_) (fun j => (Hh j).mono ?_)
    (fun y hy => hy.2) fun y hy => ?_
  · exact Set.inter_subset_inter_right _ (Set.preimage_mono Set.inter_subset_left)
  · exact Set.inter_subset_inter_right _ (Set.preimage_mono Set.inter_subset_left)
  · exact valAt_eq (hpt y hy.1) ⟨d, g, h, hg, hh, hx, heq, hy.2, rfl⟩

end GlobalTheory.CompanionTheory.Ar.PB.StepW.ValHolo
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.Factor

theorem exists_upper_transvection_upper : ∀ (N j : ℕ) (ca cb : Fin N) (C : Matrix (Fin N) (Fin N) ℂ), (cb : ℕ) = ca + 1 → ((ca : ℕ) < N - j ↔ (cb : ℕ) < N - j) → IsBlockDiag j C → C.det ≠ 0 → (∀ r c, c < r → ¬ (r = cb ∧ c = ca) → C r c = 0) → ∃ (B U : Matrix (Fin N) (Fin N) ℂ) (t : ℂ), IsBlockDiag j B ∧ B.BlockTriangular id ∧ B.det ≠ 0 ∧ IsBlockDiag j U ∧ U.BlockTriangular id ∧ (∀ c, U c c ≠ 0) ∧ C = B * (1 + Matrix.single cb ca t) * U := by
  intro N j ca cb C hcb hblk hC hdet hlow
  have hlt : ca < cb := by rw [Fin.lt_def]; omega
  have hne : ca ≠ cb := ne_of_lt hlt
  have hne' : cb ≠ ca := hne.symm
  have hx : C ca ca = 0 → C cb ca ≠ 0 := by
    intro ha hx
    apply hdet
    have hT : C.BlockTriangular id := by
      intro r c hrc
      by_cases h : r = cb ∧ c = ca
      · obtain ⟨rfl, rfl⟩ := h
        exact hx
      · exact hlow r c hrc h
    rw [Matrix.det_of_upperTriangular hT]
    exact Finset.prod_eq_zero (Finset.mem_univ ca) ha
  set s : ℂ := if C ca ca = 0 then -(C cb ca)⁻¹ else 0 with hs
  set C' : Matrix (Fin N) (Fin N) ℂ := Matrix.transvection ca cb (-s) * C with hC'
  have hC'o : ∀ r c, r ≠ ca → C' r c = C r c := fun r c hr =>
    Matrix.transvection_mul_apply_of_ne ca cb r c hr (-s) C
  have hC'a : ∀ c, C' ca c = C ca c + -s * C cb c := fun c =>
    Matrix.transvection_mul_apply_same ca cb c (-s) C
  have hC'blk : IsBlockDiag j C' := by
    intro a b hab
    by_cases ha : a = ca
    · subst ha
      rw [hC'a, hC a b hab, hC cb b (by rw [← hblk]; exact hab)]
      ring
    · rw [hC'o a b ha, hC a b hab]
  have hC'low : ∀ r c, c < r → ¬ (r = cb ∧ c = ca) → C' r c = 0 := by
    intro r c hrc h
    by_cases hr : r = ca
    · subst hr
      have hcb' : c < cb := lt_trans hrc hlt
      rw [hC'a, hlow _ c hrc (fun h' => hne h'.1),
        hlow cb c hcb' (fun h' => (ne_of_lt hrc) h'.2)]
      ring
    · rw [hC'o r c hr]
      exact hlow r c hrc h
  have hdiag : C' ca ca ≠ 0 := by
    rw [hC'a]
    by_cases ha : C ca ca = 0
    · have hx' := hx ha
      rw [hs, if_pos ha, ha, neg_neg, inv_mul_cancel₀ hx']
      simp
    · rw [hs, if_neg ha]
      simpa using ha
  set t : ℂ := C' cb ca / C' ca ca with ht
  set U : Matrix (Fin N) (Fin N) ℂ := Matrix.transvection cb ca (-t) * C' with hU
  have hUo : ∀ r c, r ≠ cb → U r c = C' r c := fun r c hr =>
    Matrix.transvection_mul_apply_of_ne cb ca r c hr (-t) C'
  have hUb : ∀ c, U cb c = C' cb c + -t * C' ca c := fun c =>
    Matrix.transvection_mul_apply_same cb ca c (-t) C'
  have hUtri : U.BlockTriangular id := by
    intro r c hrc
    change c < r at hrc
    by_cases hr : r = cb
    · subst hr
      rw [hUb]
      by_cases hc : c = ca
      · subst hc
        rw [ht, neg_mul, div_mul_cancel₀ _ hdiag]
        ring
      · have hca : c < ca := by
          rw [Fin.lt_def] at hrc ⊢
          have : (c : ℕ) ≠ ca := fun h => hc (Fin.ext h)
          omega
        rw [hC'low _ c hrc (fun h => hc h.2), hC'low ca c hca (fun h => hne h.1)]
        ring
    · rw [hUo r c hr]
      exact hC'low r c hrc (fun h => hr h.1)
  have hdetU : U.det = C.det := by
    rw [hU, hC', Matrix.det_mul, Matrix.det_mul, Matrix.det_transvection_of_ne _ _ hne',
      Matrix.det_transvection_of_ne _ _ hne, one_mul, one_mul]
  refine ⟨Matrix.transvection ca cb s, U, t, ?_, ?_, ?_, ?_, hUtri, ?_, ?_⟩
  · intro a b hab
    rw [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    have hab' : a ≠ b := fun h => hab (by rw [h])
    rw [if_neg hab']
    by_cases h : ca = a ∧ cb = b
    · obtain ⟨rfl, rfl⟩ := h
      exact absurd hblk hab
    · rw [if_neg h]
      simp
  · intro r c hrc
    change c < r at hrc
    rw [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply,
      if_neg (ne_of_gt hrc)]
    have h : ¬ (ca = r ∧ cb = c) := by
      rintro ⟨rfl, rfl⟩
      exact absurd (lt_trans hrc hlt) (lt_irrefl _)
    rw [if_neg h]
    simp
  · rw [Matrix.det_transvection_of_ne _ _ hne]
    exact one_ne_zero
  · intro a b hab
    by_cases ha : a = cb
    · subst ha
      rw [hUb, hC'blk _ b hab, hC'blk ca b (by rw [hblk]; exact hab)]
      ring
    · rw [hUo a b ha, hC'blk a b hab]
  · intro c
    have hp : ∏ i, U i i ≠ 0 := by
      rw [← Matrix.det_of_upperTriangular hUtri, hdetU]
      exact hdet
    exact Finset.prod_ne_zero_iff.mp hp c (Finset.mem_univ c)
  · change C = Matrix.transvection ca cb s * Matrix.transvection cb ca t * U
    rw [hU, hC', Matrix.mul_assoc (Matrix.transvection ca cb s), ← Matrix.mul_assoc (Matrix.transvection cb ca t),
      Matrix.transvection_mul_transvection_same cb ca hne' t (-t), add_neg_cancel, Matrix.transvection_zero, Matrix.one_mul,
      ← Matrix.mul_assoc, Matrix.transvection_mul_transvection_same ca cb hne s (-s), add_neg_cancel,
      Matrix.transvection_zero, Matrix.one_mul]

end GlobalTheory.CompanionTheory.Ar.PB.Factor
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.MoveTransvection

theorem exists_conj : ∀ (L : Type) [Field L] (N j : ℕ) (ca cb : Fin N) (U : Matrix (Fin N) (Fin N) L) (X' s : L), (cb : ℕ) = ca + 1 → ((ca : ℕ) < N - j ↔ (cb : ℕ) < N - j) → IsBlockDiag j U → U.BlockTriangular id → (∀ c, U c c ≠ 0) → U ca ca + s * U ca cb ≠ 0 → X' * (U ca ca + s * U ca cb) = s * U cb cb → ∃ V : Matrix (Fin N) (Fin N) L, IsBlockDiag j V ∧ V.BlockTriangular id ∧ (∀ c, c ≠ cb → V c c ≠ 0) ∧ (1 + Matrix.single cb ca X') * V = U * (1 + Matrix.single cb ca s) := by
  intro L _ N j ca cb U X' s hcb hblk hU hT hd hne hX
  have hlt : ca < cb := by rw [Fin.lt_def]; omega
  have hne' : cb ≠ ca := hlt.ne'
  have hR : ∀ (M : Matrix (Fin N) (Fin N) L) (t : L) (r c : Fin N),
      (M * Matrix.single cb ca t) r c = if c = ca then M r cb * t else 0 := by
    intro M t r c
    by_cases h : c = ca
    · subst h; simp [Matrix.mul_apply, Matrix.single_apply]
    · simp [Matrix.mul_apply, h, Ne.symm h]
  have hL : ∀ (M : Matrix (Fin N) (Fin N) L) (t : L) (r c : Fin N),
      (Matrix.single cb ca t * M) r c = if r = cb then t * M ca c else 0 := by
    intro M t r c
    by_cases h : r = cb
    · subst h; simp [Matrix.mul_apply, Matrix.single_apply]
    · simp [Matrix.mul_apply, h, Ne.symm h]
  have hW : ∀ r c : Fin N, ((1 + Matrix.single cb ca (-X')) * U) r c
      = U r c + if r = cb then -X' * U ca c else 0 := by
    intro r c
    rw [add_mul, one_mul, Matrix.add_apply, hL]
  have hV : ∀ r c : Fin N,
      ((1 + Matrix.single cb ca (-X')) * U * (1 + Matrix.single cb ca s)) r c
      = U r c + (if r = cb then -X' * U ca c else 0)
        + if c = ca then (U r cb + if r = cb then -X' * U ca cb else 0) * s else 0 := by
    intro r c
    rw [mul_add, mul_one, Matrix.add_apply, hR, hW, hW]
  have hTv : ∀ t : L, IsBlockDiag j (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) L) := by
    intro t a b h
    have hab : a ≠ b := by
      rintro rfl
      exact h Iff.rfl
    rw [Matrix.add_apply, Matrix.one_apply_ne hab, Matrix.single_apply, zero_add]
    rw [if_neg]
    rintro ⟨rfl, rfl⟩
    exact h hblk.symm
  refine ⟨(1 + Matrix.single cb ca (-X')) * U * (1 + Matrix.single cb ca s),
    ((hTv _).mul hU).mul (hTv _), ?_, ?_, ?_⟩
  · intro r c hrc
    have hrc' : c < r := hrc
    rw [hV]
    by_cases hc : c = ca
    · subst hc
      by_cases hr : r = cb
      · subst hr
        have h0 : U r c = 0 := hT hrc
        simp only [if_true, h0]
        linear_combination -hX
      · have hcr : cb < r := by
          rw [Fin.lt_def] at hrc' ⊢
          have : (r : ℕ) ≠ cb := fun h => hr (Fin.ext h)
          omega
        have h0 : U r c = 0 := hT hrc
        have h1 : U r cb = 0 := hT hcr
        simp [hr, h0, h1]
    · by_cases hr : r = cb
      · subst hr
        have hcca : c < ca := by
          rw [Fin.lt_def] at hrc' ⊢
          have : (c : ℕ) ≠ ca := fun h => hc (Fin.ext h)
          omega
        have h0 : U r c = 0 := hT hrc
        have h1 : U ca c = 0 := hT hcca
        simp [hc, h0, h1]
      · have h0 : U r c = 0 := hT hrc
        simp [hc, hr, h0]
  · intro c hc
    rw [hV]
    by_cases hca : c = ca
    · subst hca
      simp only [if_true, if_neg hc, add_zero]
      intro h
      apply hne
      linear_combination h
    · simpa [hc, hca] using hd c
  · have hinv : (1 + Matrix.single cb ca X') * (1 + Matrix.single cb ca (-X'))
        = (1 : Matrix (Fin N) (Fin N) L) := by
      have h0 : Matrix.single cb ca X' * Matrix.single cb ca (-X')
          = (0 : Matrix (Fin N) (Fin N) L) := by
        ext r c
        rw [hL, Matrix.single_apply]
        simp [hne']
      rw [add_mul, mul_add, mul_add, one_mul, one_mul, mul_one, h0, add_zero, add_assoc,
        ← Matrix.single_add]
      simp
    rw [← mul_assoc, ← mul_assoc, hinv, one_mul]

end GlobalTheory.CompanionTheory.Ar.PB.MoveTransvection
end

section

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)


theorem _root_.GlobalTheory.T.exists_smooth_metrics_nonneg_density : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (e : ℕ) (L : Fin e → HermLine ι),
    (∀ j, IsSmoothHerm (L j)) →
    ∃ N : Fin e → HermLine ι, (∀ j, IsSmoothHerm (N j)) ∧
      ∀ (S : Set ((Σ k, ι k) → ℂ)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
        (∀ z ∈ S, ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0) →
        (∀ (g : ((Σ k, ι k) → ℂ) → ℝ) y w, (∀ z, 0 ≤ g z) → 0 ≤ setSheetDensity S Ψ (pot N) g y w) ∧
        ∀ (g g' : ((Σ k, ι k) → ℂ) → ℝ) y w, (∀ z ∈ S, |g z| ≤ g' z) →
          |setSheetDensity S Ψ (pot L) g y w| ≤ 3 ^ e * setSheetDensity S Ψ (pot N) g' y w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Pub.CxTwist.exists_dominating_twist | exact GlobalTheory.CompanionTheory.Ar.Pub.CxTwist.exists_dominating_twist | (intros; apply GlobalTheory.CompanionTheory.Ar.Pub.CxTwist.exists_dominating_twist <;> assumption)
end
