module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle097
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle166
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticFifth
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.MemMCoordIdealOfAevalEqZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Analytic.Polynomial
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle090

@[expose] public section

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC

private theorem sameOrbit_symm_metric {K : Type} {ι : K → Type} {z z' : (Σ k, ι k) → ℂ}
    (h : SameOrbit z z') : SameOrbit z' z := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), ?_⟩
  funext p
  show z' p = (c p.1)⁻¹ * (c p.1 * z' p)
  rw [← mul_assoc, inv_mul_cancel₀ (hc p.1), one_mul]

private theorem sameOrbit_trans_metric {K : Type} {ι : K → Type} {z z' z'' : (Σ k, ι k) → ℂ}
    (h1 : SameOrbit z z') (h2 : SameOrbit z' z'') : SameOrbit z z'' := by
  obtain ⟨c, hc, rfl⟩ := h1
  obtain ⟨d, hd, rfl⟩ := h2
  refine ⟨fun k => c k * d k, fun k => mul_ne_zero (hc k) (hd k), ?_⟩
  funext p
  show c p.1 * (d p.1 * z'' p) = c p.1 * d p.1 * z'' p
  rw [mul_assoc]

theorem exists_flagPt_of_orbit : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (l : Fin BM.q), ∀ b ∈ BM.O l, ∀ z ∈ mcPts (mCoordIdeal y), SameOrbit (basePart M.blk z) (BM.Rb.lift b b) → ∃ h : Ψ → Matrix (Fin N) (Fin N) ℂ, (∀ τ', IsBlockDiag j (h τ') ∧ (h τ').det ≠ 0) ∧ SameOrbit z (FC.flagPt M (BM.F l) (FC.bvec BM l b) h) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM l b hb z hz hzb
  obtain ⟨hβmem, hβgood, hβc, hβorb⟩ := bvec_good K ι Φ y Ψ N j M n BM l b hb
  have h1 : SameOrbit (basePart M.blk z) (bvec BM l b) :=
    sameOrbit_trans_metric hzb (sameOrbit_symm_metric hβorb)
  obtain ⟨d, hd, hdz⟩ := id h1
  have hne : ∀ k, basePart M.blk z ⟨k, (BM.F l).c k⟩ ≠ 0 := by
    intro k
    rw [hdz]
    show d k * bvec BM l b ⟨k, (BM.F l).c k⟩ ≠ 0
    rw [hβc k, mul_one]
    exact hd k
  obtain ⟨z₁, hz₁z, hz₁c⟩ := GlobalTheory.CompanionTheory.Ar.PB.FibreCount.exists_normal_base M.blk (BM.F l).c z hne
  have hb1 : SameOrbit (basePart M.blk z₁) (bvec BM l b) :=
    sameOrbit_trans_metric (GlobalTheory.CompanionTheory.Ar.PB.FibreCount.basePart_orbit M.blk hz₁z) h1
  have hbeq : basePart M.blk z₁ = bvec BM l b := by
    obtain ⟨e, he, hez⟩ := hb1
    have he1 : ∀ k, e k = 1 := by
      intro k
      have hk := congrFun hez ⟨k, (BM.F l).c k⟩
      have hk' : basePart M.blk z₁ ⟨k, (BM.F l).c k⟩ = e k * bvec BM l b ⟨k, (BM.F l).c k⟩ := hk
      rw [hz₁c k, hβc k, mul_one] at hk'
      exact hk'.symm
    rw [hez]
    funext p
    show e p.1 * bvec BM l b p = bvec BM l b p
    rw [he1, one_mul]
  have hz₁ : z₁ ∈ mcPts (mCoordIdeal y) := by
    obtain ⟨c, hc, hcz⟩ := id hz₁z
    refine ⟨?_, ?_⟩
    · intro k
      obtain ⟨i, hi⟩ := hz.1 k
      refine ⟨i, ?_⟩
      rw [hcz]
      exact mul_ne_zero (hc k) hi
    · intro f hf
      have hf' : f ∈ mCoordIdeal z₁ := by
        rw [GlobalTheory.CompanionTheory.Ar.PB.FibreCount.mCoordIdeal_eq_of_orbit hz₁z]
        exact GlobalTheory.CompanionTheory.Ar.PB.CPts.mCoordIdeal_le hz hf
      exact eval_eq_zero_of_mem_mCoordIdeal hf'
  have hgood : M.GoodAt (BM.F l) (mCoordIdeal (basePart M.blk z₁)) := by
    rw [hbeq]
    exact hβgood
  obtain ⟨h, hflag⟩ := GlobalTheory.CompanionTheory.Ar.PB.CPts.flag_fwd M (BM.isFrame l) hz₁ hgood hz₁c
  obtain ⟨_, hhb, hblocks⟩ := hflag
  refine ⟨h, hhb, ?_⟩
  have h2 : SameOrbit z₁ (flagPt M (BM.F l) (bvec BM l b) h) := by
    apply GlobalTheory.CompanionTheory.Ar.PB.FibreCount.sameOrbit_of_blocks M.blk
    · rw [basePart_flagPt, hbeq]
    · intro p k hpk
      obtain ⟨a, ha, hza⟩ := hblocks p k hpk
      refine ⟨a, ha, fun m => ?_⟩
      rw [hza m, flagPt_step M (BM.F l) (bvec BM l b) h hpk m, hbeq]
  exact sameOrbit_trans_metric (sameOrbit_symm_metric hz₁z) h2

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC

theorem lift_analyticAt {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)} {n e : ℕ}
    (R : AnLogRes P J n) {V : Set (Fin e → ℂ)} {bp : (Fin e → ℂ) → R.X} (hV : IsOpen V) (hc : ContinuousOn bp V)
    (ha : ∀ k, AnalyticOnNhd ℂ (R.A.chart k ∘ bp) (V ∩ bp ⁻¹' (R.A.chart k).source)) {u₀ : Fin e → ℂ} (hu : u₀ ∈ V)
    (p : Σ k, ι k) : AnalyticAt ℂ (fun u => R.lift (bp u₀) (bp u) p) u₀ := by
  obtain ⟨k, hk⟩ := R.A.cover (bp u₀)
  have h1 : AnalyticAt ℂ (R.A.chart k ∘ bp) u₀ := ha k u₀ ⟨hu, hk⟩
  have h2 : AnalyticAt ℂ ((fun y => R.lift (bp u₀) y p) ∘ (R.A.chart k).symm) ((R.A.chart k ∘ bp) u₀) :=
    R.holo (bp u₀) p k _ ⟨(R.A.chart k).map_source hk, by
      show (R.A.chart k).symm (R.A.chart k (bp u₀)) ∈ R.U (bp u₀)
      rw [(R.A.chart k).left_inv hk]
      exact R.mem_U _⟩
  refine (h2.comp h1).congr ?_
  have hW : V ∩ bp ⁻¹' (R.A.chart k).source ∈ 𝓝 u₀ :=
    (hc.isOpen_inter_preimage hV (R.A.chart k).open_source).mem_nhds ⟨hu, hk⟩
  filter_upwards [hW] with u hu'
  simp only [Function.comp, (R.A.chart k).left_inv hu'.2]

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

theorem bvec_analyticAt {M : FlagModel y Ψ N j} {n : ℕ} (BM : BaseMetric M n) (l : Fin BM.q) {e : ℕ}
    {V : Set (Fin e → ℂ)} {bp : (Fin e → ℂ) → BM.Rb.X} (hV : IsOpen V) (hc : ContinuousOn bp V)
    (ha : ∀ k, AnalyticOnNhd ℂ (BM.Rb.A.chart k ∘ bp) (V ∩ bp ⁻¹' (BM.Rb.A.chart k).source))
    (hO : ∀ u ∈ V, bp u ∈ BM.O l) {u₀ : Fin e → ℂ} (hu : u₀ ∈ V) (q : Σ k, baseIdx ι M.blk k) :
    AnalyticAt ℂ (fun u => FC.bvec BM l (bp u) q) u₀ := by
  have hne : BM.Rb.lift (bp u₀) (bp u₀) ⟨q.1, (BM.F l).c q.1⟩ ≠ 0 :=
    FibreCount.chart_ne ((BM.good l _ (hO u₀ hu)).1 q.1)
  have hq := (lift_analyticAt BM.Rb hV hc ha hu q).div
    (lift_analyticAt BM.Rb hV hc ha hu ⟨q.1, (BM.F l).c q.1⟩) hne
  refine hq.congr ?_
  have hW : V ∩ bp ⁻¹' (BM.Rb.U (bp u₀)) ∈ 𝓝 u₀ :=
    (hc.isOpen_inter_preimage hV (BM.Rb.isOpen_U _)).mem_nhds ⟨hu, BM.Rb.mem_U _⟩
  filter_upwards [hW] with u hu'
  obtain ⟨c, hc0, ec⟩ := BM.Rb.compat (bp u₀) (bp u) (bp u) ⟨hu'.2, BM.Rb.mem_U _⟩
  show BM.Rb.lift (bp u₀) (bp u) q / BM.Rb.lift (bp u₀) (bp u) ⟨q.1, (BM.F l).c q.1⟩ =
    BM.Rb.lift (bp u) (bp u) q / BM.Rb.lift (bp u) (bp u) ⟨q.1, (BM.F l).c q.1⟩
  rw [ec]
  exact mul_div_mul_left _ _ (hc0 q.1)

theorem valAt_analyticAt {M : FlagModel y Ψ N j} {n : ℕ} (BM : BaseMetric M n) (l : Fin BM.q) {e : ℕ}
    {V : Set (Fin e → ℂ)} {bp : (Fin e → ℂ) → BM.Rb.X} (hV : IsOpen V) (hO : ∀ u ∈ V, bp u ∈ BM.O l)
    {u₀ : Fin e → ℂ} (hu : u₀ ∈ V) (hw : ∀ q, AnalyticAt ℂ (fun u => FC.bvec BM l (bp u) q) u₀) {s : M.Ω}
    (hs : RegAt M.x (mCoordIdeal (FC.bvec BM l (bp u₀))) s) :
    AnalyticAt ℂ (fun u => valAt M.x s (FC.bvec BM l (bp u))) u₀ := by
  obtain ⟨d, g, h, hg, hh, hQ, eq⟩ := hs
  have hE : ∀ (z : (Σ k, baseIdx ι M.blk k) → ℂ) (f : MRing (baseIdx ι M.blk)),
      eval z (map (Int.castRingHom ℂ) f) = aeval z f := fun z f => by
    rw [aeval_def, algebraMap_int_eq, ← eval_map]
  have aG : AnalyticAt ℂ (fun u => aeval (FC.bvec BM l (bp u)) g) u₀ := AnalyticAt.aeval_mvPolynomial hw g
  have aH : AnalyticAt ℂ (fun u => aeval (FC.bvec BM l (bp u)) h) u₀ := AnalyticAt.aeval_mvPolynomial hw h
  have h0 : aeval (FC.bvec BM l (bp u₀)) h ≠ 0 := fun e0 => hQ (mem_mCoordIdeal_of_aeval_eq_zero _ hh e0)
  refine (aG.div aH h0).congr ?_
  filter_upwards [hV.mem_nhds hu, aH.continuousAt.eventually_ne h0] with u hu' hne
  have hz := (bvec_good K ι Φ y Ψ N j M n BM l _ (hO u hu')).1
  have h1 : eval (FC.bvec BM l (bp u)) (map (Int.castRingHom ℂ) h) ≠ 0 := by rwa [hE]
  have h2 : aeval M.x h ≠ 0 := fun e0 => h1 (hz.2 h (mem_mCoordIdeal_of_aeval_eq_zero M.x hh e0))
  have hv : IsValueAt M.x s (FC.bvec BM l (bp u))
      (eval (FC.bvec BM l (bp u)) (map (Int.castRingHom ℂ) g) / eval (FC.bvec BM l (bp u)) (map (Int.castRingHom ℂ) h)) :=
    ⟨d, g, h, hg, hh, h2, eq, h1, rfl⟩
  rw [valAt_eq hz hv, hE, hE]
  rfl

theorem bvec_val_analytic : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (l : Fin BM.q) (e : ℕ) (V : Set (Fin e → ℂ)) (bp : (Fin e → ℂ) → BM.Rb.X), IsOpen V → ContinuousOn bp V → (∀ k, AnalyticOnNhd ℂ (BM.Rb.A.chart k ∘ bp) (V ∩ bp ⁻¹' (BM.Rb.A.chart k).source)) → (∀ u ∈ V, bp u ∈ BM.O l) → (∀ q, AnalyticOnNhd ℂ (fun u => FC.bvec BM l (bp u) q) V) ∧ ∀ s : M.Ω, (∀ b ∈ BM.O l, RegAt M.x (mCoordIdeal (FC.bvec BM l b)) s) → AnalyticOnNhd ℂ (fun u => valAt M.x s (FC.bvec BM l (bp u))) V := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM l e V bp hV hc ha hO
  have hb : ∀ q, AnalyticOnNhd ℂ (fun u => FC.bvec BM l (bp u) q) V := fun q u hu =>
    bvec_analyticAt BM l hV hc ha hO hu q
  exact ⟨hb, fun s hs u hu => valAt_analyticAt BM l hV hO hu (fun q => hb q u hu) (hs _ (hO u hu))⟩

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC

section Minors

variable {N : ℕ}

theorem minor_self_of_lowerUni {L : Matrix (Fin N) (Fin N) ℂ} (hL : IsLowerUni L) (C : Finset (Fin N)) :
    minorIJ L C C = 1 := by
  unfold minorIJ
  rw [dite_eq_left rfl, Matrix.det_of_lowerTriangular]
  · exact Finset.prod_eq_one fun i _ => hL.1 _
  · intro a b hab
    exact hL.2 _ _ ((C.orderEmbOfFin rfl).strictMono hab)

theorem minor_insert_of_lowerUni {L : Matrix (Fin N) (Fin N) ℂ} (hL : IsLowerUni L) {C : Finset (Fin N)} {s r : Fin N}
    (hs : s ∈ C) (hmax : ∀ a ∈ C, a ≤ s) (hr : s < r) : minorIJ L (insert r (C.erase s)) C = L r s := by
  have hrn : r ∉ C.erase s := fun h => absurd (hmax r (Finset.mem_of_mem_erase h)) (not_le.2 hr)
  have hcard : (insert r (C.erase s)).card = C.card := by
    rw [Finset.card_insert_of_notMem hrn, Finset.card_erase_of_mem hs]
    have := Finset.card_pos.2 ⟨s, hs⟩
    omega
  unfold minorIJ
  rw [dite_eq_left hcard]
  set e := C.orderEmbOfFin rfl with he
  have hmem : ∀ i, e i ∈ C := fun i => Finset.orderEmbOfFin_mem C rfl i
  obtain ⟨m, hm⟩ : ∃ m, e m = s := by
    have : s ∈ Set.range e := by
      rw [he, Finset.range_orderEmbOfFin]
      exact hs
    exact this
  have hle : ∀ i, i ≤ m := fun i => e.le_iff_le.1 (by rw [hm]; exact hmax _ (hmem i))
  let f : Fin C.card → Fin N := fun i => if i = m then r else e i
  have hf_ne : ∀ i, i ≠ m → f i = e i := fun i h => if_neg h
  have hf_m : f m = r := if_pos rfl
  have hmono : StrictMono f := by
    intro a b hab
    have ham : a ≠ m := fun h => absurd (hle b) (by rw [← h]; exact not_le.2 hab)
    rw [hf_ne a ham]
    by_cases hb : b = m
    · rw [hb, hf_m]
      exact lt_of_le_of_lt (hmax _ (hmem a)) hr
    · rw [hf_ne b hb]
      exact e.strictMono hab
  have hin : ∀ i, f i ∈ insert r (C.erase s) := by
    intro i
    by_cases hi : i = m
    · rw [hi, hf_m]
      exact Finset.mem_insert_self _ _
    · rw [hf_ne i hi]
      refine Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨fun h => hi ?_, hmem i⟩)
      exact e.injective (h.trans hm.symm)
  have hfe : f = (insert r (C.erase s)).orderEmbOfFin hcard := Finset.orderEmbOfFin_unique hcard hin hmono
  rw [← hfe, Matrix.det_of_lowerTriangular]
  · rw [Finset.prod_eq_single m]
    · rw [Matrix.submatrix_apply, hf_m, hm]
    · intro i _ hi
      rw [Matrix.submatrix_apply, hf_ne i hi]
      exact hL.1 _
    · intro h
      exact absurd (Finset.mem_univ m) h
  · intro a b hab
    have hab' : a < b := hab
    have ham : a ≠ m := fun h => absurd (hle b) (by rw [← h]; exact not_le.2 hab')
    rw [Matrix.submatrix_apply, hf_ne a ham]
    exact hL.2 _ _ (e.strictMono hab')

end Minors

theorem flag_uniq : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (l : Fin BM.q), ∀ b ∈ BM.O l, ∀ L L' : Ψ → Matrix (Fin N) (Fin N) ℂ, (∀ τ', IsBlockDiag j (L τ') ∧ IsLowerUni (L τ')) → (∀ τ', IsBlockDiag j (L' τ') ∧ IsLowerUni (L' τ')) → SameOrbit (FC.flagPt M (BM.F l) (FC.bvec BM l b) L) (FC.flagPt M (BM.F l) (FC.bvec BM l b) L') → L = L' := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM l b hb L L' hL hL' ho
  obtain ⟨hβ, hg, -, -⟩ := bvec_good K ι Φ y Ψ N j M n BM l b hb
  obtain ⟨c, -, ez⟩ := ho
  have hjN := M.j_le
  have key : ∀ (τ' : Ψ) (i : Fin N), IsProperStep N j i → ∃ a : ℂ, ∀ I,
      minorIJ (L τ') I (stepCols N j i) = a * minorIJ (L' τ') I (stepCols N j i) := by
    intro τ' i hi
    obtain ⟨k, hk⟩ : ∃ k, M.blk (τ', i) = some k :=
      Option.ne_none_iff_exists'.1 fun e => (M.blk_none _).1 e hi
    refine ⟨c k, fun I => ?_⟩
    have h0 := FibreCount.plucker_inj M (BM.isFrame l) hβ hg hk
      (fun I => minorIJ (L τ') I (stepCols N j i) - c k * minorIJ (L' τ') I (stepCols N j i))
      (fun I hI => by
        show minorIJ (L τ') I (stepCols N j i) - c k * minorIJ (L' τ') I (stepCols N j i) = 0
        rw [FibreCount.minor_off_step hjN hi (hL τ').1 hI, FibreCount.minor_off_step hjN hi (hL' τ').1 hI]
        ring)
      (fun m => by
        have x := congrFun ez ⟨k, m⟩
        simp only at x
        rw [flagPt_step M (BM.F l) _ L hk m, flagPt_step M (BM.F l) _ L' hk m] at x
        simp only [mul_sub, Finset.sum_sub_distrib]
        rw [x, Finset.mul_sum, sub_eq_zero]
        exact Finset.sum_congr rfl fun _ _ => by ring) I
    exact sub_eq_zero.1 h0
  have ent : ∀ (τ' : Ψ) (i : Fin N) (s r : Fin N), IsProperStep N j i → s ∈ stepCols N j i →
      (∀ a ∈ stepCols N j i, a ≤ s) → s < r → L τ' r s = L' τ' r s := by
    intro τ' i s r hi hs hmax hr
    obtain ⟨a, ha⟩ := key τ' i hi
    have h1 := ha (stepCols N j i)
    rw [minor_self_of_lowerUni (hL τ').2, minor_self_of_lowerUni (hL' τ').2, mul_one] at h1
    have h2 := ha (insert r ((stepCols N j i).erase s))
    rw [minor_insert_of_lowerUni (hL τ').2 hs hmax hr, minor_insert_of_lowerUni (hL' τ').2 hs hmax hr, ← h1,
      one_mul] at h2
    exact h2
  funext τ'
  ext r s
  rcases lt_trichotomy s r with hsr | hsr | hsr
  · have hsr' : (s : ℕ) < r := hsr
    by_cases hblk : ((r : ℕ) < N - j ↔ (s : ℕ) < N - j)
    · by_cases hs : (s : ℕ) < N - j
      · have hr : (r : ℕ) < N - j := hblk.2 hs
        refine ent τ' ⟨s + j, by omega⟩ s r ⟨by simp only; omega, by simp only; omega⟩ ?_ ?_ hsr
        · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [if_neg (by omega)]
          omega
        · intro a ha
          simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at ha
          rw [if_neg (by omega)] at ha
          exact Fin.le_def.2 (by omega)
      · have hr : ¬ (r : ℕ) < N - j := fun h => hs (hblk.1 h)
        have hrN := r.2
        refine ent τ' ⟨s - (N - j), by omega⟩ s r ⟨by simp only; omega, by simp only; omega⟩ ?_ ?_ hsr
        · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [if_pos (by omega)]
          omega
        · intro a ha
          simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at ha
          rw [if_pos (by omega)] at ha
          exact Fin.le_def.2 (by omega)
    · rw [(hL τ').1 r s hblk, (hL' τ').1 r s hblk]
  · rw [hsr, (hL τ').2.1, (hL' τ').2.1]
  · rw [(hL τ').2.2 r s hsr, (hL' τ').2.2 r s hsr]

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
end
end
