module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle051
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ZeroNotMemPreimagePow
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle055
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle045
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJfSSymExp
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle054
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle062
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegralNormCvecSq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Monotonicity.Lemmas
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
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

namespace Formalism.FourierDecayAlt.P.PBK

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace ENNReal

noncomputable section

open Classical

section ss2

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem memLp_bz_of_sup {s : ℕ} (hs : s ≠ 0) {β : ℂ} (hβ : β ≠ 0) {ε : ℂ} (hε : ‖ε‖ = 1)
    (ut : ℂ → ℂ → H) (bt : ℂ → H) (SS : ℝ) (memU : ∀ x : ℂ, x ≠ 0 → MemLp (ut x) 2 volume)
    (sup : ∀ x : ℂ, x ≠ 0 → ∫ D, ‖ut x D‖ ^ 2 ≤ SS) (hbt : StronglyMeasurable bt)
    (hloc : ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K → IntegrableOn (fun z => ‖bz s bt z‖ ^ 2) K)
    (germ : ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K → ∃ C : ℝ, ∀ x : ℂ, x ≠ 0 →
      ∀ᵐ D, D ∈ K → ‖ut x D - mainD s β ε bt x D‖ ≤ C * ‖x‖⁻¹) :
    MemLp (bz s bt) 2 volume ∧ ∫ z, ‖bz s bt z‖ ^ 2 ≤ SS := by
  have hSS : 0 ≤ SS := (integral_nonneg fun D => sq_nonneg ‖ut 1 D‖).trans (sup 1 one_ne_zero)
  have hε0 : ε ≠ 0 := by
    intro h; rw [h, norm_zero] at hε; exact zero_ne_one hε
  let K : ℕ → Set ℂ := fun n => {z : ℂ | ε⁻¹ * z ^ s ∈ ann n}
  have hKc : ∀ n, IsCompact (K n) := fun n => isCompact_preimage_pow hs hε (isCompact_ann n)
  have hK0 : ∀ n, (0 : ℂ) ∉ K n := fun n => zero_notMem_preimage_pow hs ε (zero_notMem_ann n)
  have hKm : ∀ n, MeasurableSet (K n) := fun n => (hKc n).isClosed.measurableSet
  have hbm : StronglyMeasurable (bz s bt) := stronglyMeasurable_bz s hbt
  have hmem : ∀ n, MemLp ((K n).indicator (bz s bt)) 2 volume := fun n =>
    memLp_indicator_bz hbt (hKm n) (hloc _ (hKc n) (hK0 n))
  have hbound : ∀ n, ∫ z, ‖(K n).indicator (bz s bt) z‖ ^ 2 ≤ SS := fun n => by
    obtain ⟨C, hC⟩ := germ (ann n) (isCompact_ann n) (zero_notMem_ann n)
    exact integral_bz_Q_le hs hβ hε ut bt SS memU sup hbt (ann n) (isCompact_ann n)
      (hloc _ (hKc n) (hK0 n)) C hC
  let g : ℕ → ℂ → ℝ≥0∞ := fun n z => ENNReal.ofReal (‖(K n).indicator (bz s bt) z‖ ^ 2)
  have hgm : ∀ n, Measurable (g n) := fun n =>
    ENNReal.measurable_ofReal.comp (((hbm.indicator (hKm n)).norm.measurable).pow_const 2)
  have hKmono : Monotone K := fun m n hmn z hz => ann_mono hmn hz
  have hgmono : Monotone g := by
    intro m n hmn z
    apply ENNReal.ofReal_le_ofReal
    by_cases hz : z ∈ K m
    · simp only [Set.indicator_of_mem hz, Set.indicator_of_mem (hKmono hmn hz), le_refl]
    · rw [Set.indicator_of_notMem hz, norm_zero, zero_pow two_ne_zero]
      positivity
  have hgn : ∀ n, ∫⁻ z, g n z ≤ ENNReal.ofReal SS := fun n => by
    have hi : Integrable (fun z => ‖(K n).indicator (bz s bt) z‖ ^ 2) :=
      (memLp_two_iff_integrable_sq_norm (hmem n).aestronglyMeasurable).1 (hmem n)
    show ∫⁻ z, ENNReal.ofReal (‖(K n).indicator (bz s bt) z‖ ^ 2) ≤ _
    rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun z => sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  have hsup : (fun z => ENNReal.ofReal (‖bz s bt z‖ ^ 2)) =ᵐ[volume] fun z => ⨆ n, g n z := by
    have h0 : ∀ᵐ z : ℂ ∂volume, z ≠ 0 := by
      rw [ae_iff]; simp
    filter_upwards [h0] with z hz
    have hw : ε⁻¹ * z ^ s ≠ 0 := mul_ne_zero (inv_ne_zero hε0) (pow_ne_zero _ hz)
    obtain ⟨n, hn⟩ := exists_mem_ann hw
    apply le_antisymm
    · refine le_iSup_of_le n (le_of_eq ?_)
      show ENNReal.ofReal (‖bz s bt z‖ ^ 2) = ENNReal.ofReal (‖(K n).indicator (bz s bt) z‖ ^ 2)
      rw [Set.indicator_of_mem (show z ∈ K n from hn)]
    · refine iSup_le fun m => ENNReal.ofReal_le_ofReal ?_
      by_cases hzm : z ∈ K m
      · simp only [Set.indicator_of_mem hzm, le_refl]
      · rw [Set.indicator_of_notMem hzm, norm_zero, zero_pow two_ne_zero]
        positivity
  have hlin : ∫⁻ z, ENNReal.ofReal (‖bz s bt z‖ ^ 2) ≤ ENNReal.ofReal SS := by
    rw [lintegral_congr_ae hsup, lintegral_iSup hgm hgmono]
    exact iSup_le hgn
  have hint : Integrable (fun z => ‖bz s bt z‖ ^ 2) := by
    refine ⟨(hbm.norm.measurable.pow_const 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun z => sq_nonneg _)]
    exact lt_of_le_of_lt hlin ENNReal.ofReal_lt_top
  refine ⟨(memLp_two_iff_integrable_sq_norm hbm.aestronglyMeasurable).2 hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun z => sq_nonneg _)
    (hbm.norm.measurable.pow_const 2).aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal hSS hlin

end ss2

end

end Formalism.FourierDecayAlt.P.PBK
end

section

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JfS.Sym

noncomputable section

variable {k r : ℕ}

theorem colN {ζ : B.Mat k r} (hζ : B.inLie k r ζ) (z : Fin (2 * r + k + 1) → ℂ)
    (hN : ∀ X ∈ lieOf (Sset k r z), (Matrix.trace (ζ * X)).re = 0) (a : Fin r) :
    ∀ i : Fin (2 * r + k + 1), a.val < i.val → (ζ *ᵥ bvec (eI k r a)) i = 0 := by
  have orth : ∀ v : Fin (2 * r + k + 1) → ℂ, (∀ b : Fin r, b.val ≤ a.val → v (esI k r b) = 0) →
      herm (Hpk k r) (ζ *ᵥ bvec (eI k r a)) v = 0 := by
    intro v hv
    refine herm_zero_of_trace hζ _ v (hN _ (xuv_lieN z a v hv)) (hN _ (xuv_lieN z a _ ?_))
    intro b hb; simp [hv b hb]
  intro i hi
  by_cases h1 : i.val < r
  · have e := herm_es (ζ *ᵥ bvec (eI k r a)) ⟨i.val, h1⟩
    rw [show eI k r ⟨i.val, h1⟩ = i from Fin.ext rfl] at e
    rw [← e]
    refine orth _ (fun b hb => ?_)
    have : esI k r b ≠ esI k r ⟨i.val, h1⟩ := by
      intro h; have := congrArg Fin.val h; simp [esI] at this; omega
    simp [bvec, this]
  · by_cases h2 : i.val ≤ r + k
    · have hw := herm_w (ζ *ᵥ bvec (eI k r a)) i (by omega) h2
      have h0 : herm (Hpk k r) (ζ *ᵥ bvec (eI k r a)) (bvec i) = 0 := by
        refine orth _ (fun b hb => ?_)
        have : esI k r b ≠ i := by
          intro h; have := congrArg Fin.val h; simp [esI] at this; omega
        simp [bvec, this]
      rw [hw] at h0
      split_ifs at h0 with h3
      · exact neg_eq_zero.1 h0
      · exact h0
    · have e : i = esI k r ⟨2 * r + k - i.val, by omega⟩ := by
        apply Fin.ext; simp [esI]; omega
      have e2 := herm_e (ζ *ᵥ bvec (eI k r a)) ⟨2 * r + k - i.val, by omega⟩
      rw [← e] at e2
      rw [← e2]
      refine orth _ (fun b hb => ?_)
      have : esI k r b ≠ eI k r ⟨2 * r + k - i.val, by omega⟩ := by
        intro h; have := congrArg Fin.val h; simp [esI, eI] at this; omega
      simp [bvec, this]

theorem flt_bvec (a : ℕ) (c : Fin r) (hc : c.val < a) : Flt (k := k) a (bvec (eI k r c)) := by
  intro i hi
  have : i ≠ eI k r c := by intro h; rw [h] at hi; simp [eI] at hi; omega
  simp [bvec, this]

theorem flt_zero_eq (y : Fin (2 * r + k + 1) → ℂ) (hy : Flt 0 y) : y = 0 := by
  funext i; exact hy i (Nat.zero_le _)

theorem stepNil (ζ : B.Mat k r) (N : ℕ) (hζN : ζ ^ N = 0) (a : Fin r)
    (hcol : ∀ i : Fin (2 * r + k + 1), a.val < i.val → (ζ *ᵥ bvec (eI k r a)) i = 0)
    (hkill : ∀ y, Flt a.val y → ζ *ᵥ y = 0) : Flt a.val (ζ *ᵥ bvec (eI k r a)) := by
  set ea := bvec (eI k r a) with hea
  set x := ζ *ᵥ ea with hx
  set xa := x (eI k r a)
  have hea1 : ea (eI k r a) = 1 := by simp [hea, bvec]
  have hy : Flt a.val (x - xa • ea) := by
    intro i hi
    by_cases he : i = eI k r a
    · rw [he]; simp only [Pi.sub_apply, Pi.smul_apply, hea1, smul_eq_mul, mul_one]; exact sub_self _
    · have hi' : a.val < i.val := by
        have : i.val ≠ a.val := fun h => he (Fin.ext h)
        omega
      simp [hcol i hi', hea, bvec, he]
  have hζx : ζ *ᵥ x = xa • x := by
    have e : x = xa • ea + (x - xa • ea) := by abel
    conv_lhs => rw [e]
    rw [mulVec_add, mulVec_smul, hkill _ hy, add_zero]
  have hp : ∀ m, (ζ ^ (m + 1)) *ᵥ ea = xa ^ m • x := by
    intro m
    induction m with
    | zero => simp [hx]
    | succ m ih => rw [pow_succ', ← mulVec_mulVec, ih, mulVec_smul, hζx, smul_smul, pow_succ]
  have hxa : xa = 0 := by
    cases N with
    | zero =>
      exfalso
      have := congrFun (congrArg (fun M => M *ᵥ ea) hζN) (eI k r a)
      simp [hea1] at this
    | succ m =>
      have := congrFun (hp m) (eI k r a)
      rw [hζN, zero_mulVec] at this
      simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul] at this
      have h2 : xa ^ (m + 1) = 0 := by rw [pow_succ]; exact this.symm
      exact (pow_eq_zero_iff'.1 h2).1
  have : x = x - xa • ea := by rw [hxa, zero_smul, sub_zero]
  rw [this]; exact hy

theorem killX (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r)
    (hD : ∀ a (ha : a ≤ r), Dmin k r z z' g ⟨a, by omega⟩ ≠ 0)
    (ξ η : B.Mat k r) (hξ : B.inLie k r ξ) (N : ℕ) (hξN : ξ ^ N = 0) (hηN : η ^ N = 0)
    (hgη : g * η = ξ * g)
    (colξ : ∀ a : Fin r, ∀ i : Fin (2 * r + k + 1), a.val < i.val → (ξ *ᵥ bvec (eI k r a)) i = 0)
    (colη : ∀ a : Fin r, ∀ i : Fin (2 * r + k + 1), a.val < i.val → (η *ᵥ bvec (eI k r a)) i = 0) :
    ∀ a, a ≤ r → ∀ y, Flt a y → ξ *ᵥ y = 0 ∧ η *ᵥ y = 0 := by
  have hξg : ∀ y, ξ *ᵥ (g *ᵥ y) = g *ᵥ (η *ᵥ y) := by
    intro y; rw [mulVec_mulVec, mulVec_mulVec, hgη]
  intro a
  induction a with
  | zero =>
    intro _ y hy
    rw [flt_zero_eq y hy, mulVec_zero, mulVec_zero]
    exact ⟨rfl, rfl⟩
  | succ a ih =>
    intro ha y hy
    have IH := ih (by omega)
    set a' : Fin r := ⟨a, by omega⟩
    have hxξ : Flt a (ξ *ᵥ bvec (eI k r a')) := stepNil ξ N hξN a' (colξ a') (fun y hy => (IH y hy).1)
    have hxη : Flt a (η *ᵥ bvec (eI k r a')) := stepNil η N hηN a' (colη a') (fun y hy => (IH y hy).2)
    have hξa : ξ *ᵥ bvec (eI k r a') = 0 := by
      refine dlem_ii z z' g a (by omega) (hD a (by omega)) _ hxξ (fun c hc => ?_)
      rw [herm_skew hξ, hξg, (IH _ (flt_bvec a c hc)).2, mulVec_zero, herm_zero_right, neg_zero]
    have hηa : η *ᵥ bvec (eI k r a') = 0 := by
      refine dlem_i z z' g a (by omega) (hD a (by omega)) _ hxη (fun c hc => ?_)
      rw [← hξg, herm_skew hξ, (IH _ (flt_bvec a c hc)).1, herm_zero_right, neg_zero]
    set ya := y (eI k r a')
    have hrest : Flt a (y - ya • bvec (eI k r a')) := by
      intro i hi
      by_cases he : i = eI k r a'
      · rw [he]; simp [bvec, ya]
      · have hi' : a + 1 ≤ i.val := by
          have : i.val ≠ a := fun h => he (Fin.ext h)
          omega
        simp [hy i hi', bvec, he]
    have e : y = ya • bvec (eI k r a') + (y - ya • bvec (eI k r a')) := by abel
    rw [e, mulVec_add, mulVec_smul, mulVec_add, mulVec_smul, hξa, hηa, (IH _ hrest).1, (IH _ hrest).2]
    simp

end

end Formalism.FourierDecayAlt.P.CutMP.JfS.Sym
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem second_shift_slice_derivative : GTSSLSliceDZ := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl T hT Φ Φ' c c' hc hc' hEq ζ hζ
  obtain ⟨n, A, -, hTA⟩ := hT
  have hTT : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' = P.TT := by
    rw [hpl.2.2.2.1, hpl.2.2.2.2.1]; rfl
  have hU : IsOpen (Ann P) := isOpen_lt continuous_const Complex.continuous_normSq
  have hq : ((c, ζ) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨hc, by rw [hTT]; exact hζ⟩
  have hq' : ((c', ζ) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨hc', by rw [hTT]; exact hζ⟩
  have hev : (fun ζ' => NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c, ζ')) =ᶠ[nhds ζ]
      (fun ζ' => NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (Φ' : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c', ζ')) := by
    filter_upwards [hU.mem_nhds hζ] with ζ' hζ'
    have m : ((c, ζ') : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨hc, by rw [hTT]; exact hζ'⟩
    have m' : ((c', ζ') : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨hc', by rw [hTT]; exact hζ'⟩
    unfold NF.radR
    rw [Set.indicator_of_mem m, Set.indicator_of_mem m']
    exact hEq ζ' hζ'
  have e1 : NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (T Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c, ζ) =
      (T Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ) := by
    unfold NF.radR; rw [Set.indicator_of_mem hq]
  have e2 : NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (T Φ' : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c', ζ) =
      (T Φ' : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c' (NF.muZ P.k P.r Bs.μsec ζ) := by
    unfold NF.radR; rw [Set.indicator_of_mem hq']
  have h1 := hTA Φ (c, ζ) hq
  have h2 := hTA Φ' (c', ζ) hq'
  dsimp only at h1 h2
  rw [← e1, ← e2, h1, h2]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [(hev.iteratedFDeriv ℝ j).eq_of_nhds]

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section

namespace Formalism.FourierDecayAlt.P.CutBP.GT

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {I : Type} [Fintype I]
  {p : KB.Pl P Wp Wq} {nn : ℝ → ℝ} {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} {w : List C.Letter} {c : I → ℝ}
  {Fi : I → B.Mat P.k P.r → (Wq →L[ℂ] Wp)} {L : I → (Wq →L[ℂ] Wp) →L[ℂ] HS Wp Wq}

theorem vecT_cont (hV : VecHyp p nn F w c Fi L) {h : C.LPt} (hh : ∀ q ∈ h, 1 ≤ q.1 ∧ q.2 ≠ 0) {m : ℕ}
    (hm : 1 ≤ m) (hsz : D.ptSize h + m = P.r + 1) :
    ContinuousOn (fun z : ℂ => vecT p w.length c Fi L (h ++ [(m, z)])) {0}ᶜ := by
  have hcomp : ∀ i, ContinuousOn (fun z : ℂ =>
      ((√(c i) * omT p w.length (h ++ [(m, z)]) : ℝ) : ℂ) • L i (p.V (Fi i) (h ++ [(m, z)]))) {0}ᶜ := by
    intro i
    have := ((L i).continuous.comp_continuousOn (hV.cont i m h hh hm hsz)).const_smul ((√(c i) : ℝ) : ℂ)
    refine this.congr fun z _ => ?_
    show _ = (((√(c i) : ℝ) : ℂ)) • L i ((omT p w.length (h ++ [(m, z)]) : ℂ) • p.V (Fi i) (h ++ [(m, z)]))
    rw [map_smul, smul_smul, Complex.ofReal_mul]
  exact (PiLp.continuous_toLp 2 _).comp_continuousOn (continuousOn_pi.2 hcomp)

theorem norm_vecT_sq (hV : VecHyp p nn F w c Fi L) (Q : C.LPt) :
    ‖vecT p w.length c Fi L Q‖ ^ 2 = (TBB.NP p nn F (P.r + 1) w Q Q).re := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), inner_vecT p w.length c hV.hc Fi L Q Q, hV.gram Q Q]
  rfl

def gT (p : KB.Pl P Wp Wq) (N : ℕ) (c : I → ℝ) (Fi : I → B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (L : I → (Wq →L[ℂ] Wp) →L[ℂ] HS Wp Wq) (s : ℕ) (h : C.LPt) (u : ℂ) : HT I Wp Wq :=
  ((Real.pi ^ (s - 1) * ((s : ℝ) * ‖u‖ ^ (s - 1))⁻¹ : ℝ) : ℂ) • vecT p N c Fi L (h ++ [(s, u)])

theorem gT_cont (hV : VecHyp p nn F w c Fi L) {b s : ℕ} (hb : 1 ≤ b) (hs : 2 ≤ s) (hbs : b + s = P.r + 2) {h : C.LPt}
    (hh : D.IsLocPt h (b - 1)) : ContinuousOn (gT p w.length c Fi L s h) {0}ᶜ := by
  have hv := vecT_cont hV hh.1 (m := s) (by omega) (by rw [hh.2]; omega)
  have hsc : ContinuousOn
      (fun u : ℂ => (((Real.pi ^ (s - 1) * ((s : ℝ) * ‖u‖ ^ (s - 1))⁻¹ : ℝ)) : ℂ)) {0}ᶜ := by
    refine Complex.continuous_ofReal.comp_continuousOn (continuousOn_const.mul ?_)
    refine ContinuousOn.inv₀ (continuousOn_const.mul (continuous_norm.continuousOn.pow _)) fun u hu => ?_
    exact mul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) (pow_ne_zero _ (norm_ne_zero_iff.mpr hu))
  exact hsc.smul hv

theorem btT_eq_piecewise (s : ℕ) (h : C.LPt) :
    btT p w.length c Fi L s h = ({0}ᶜ : Set ℂ).piecewise (gT p w.length c Fi L s h) (fun _ => 0) := by
  funext u
  by_cases hu : u = 0
  · simp [btT, Set.piecewise, hu]
  · simp [btT, gT, Set.piecewise, hu]

end place


theorem field_measurability : FieldMeas := by
  intro P Wp Wq _ _ _ _ _ _ I _ p nn F w c Fi L hV b s hb hs hbs h hh
  rw [btT_eq_piecewise]
  letI : MeasurableSpace (HT I Wp Wq) := borel _
  haveI : BorelSpace (HT I Wp Wq) := ⟨rfl⟩
  exact ((gT_cont hV hb hs hbs hh).measurable_piecewise continuousOn_const
    (measurableSet_singleton 0).compl).stronglyMeasurable

theorem field_locality : FieldLoc := by
  intro P Wp Wq _ _ _ _ _ _ I _ p nn F w c Fi L hV b s hb hs hbs h hh K hK h0
  have hsub : K ⊆ {0}ᶜ := fun z hz hz0 => h0 (by rwa [Set.mem_singleton_iff.mp hz0] at hz)
  have hg := (gT_cont hV hb hs hbs hh).mono hsub
  refine ContinuousOn.integrableOn_compact hK ?_
  have hc : ContinuousOn
      (fun z => ‖(((s : ℝ) * ‖z‖ ^ (s - 1) : ℝ) : ℂ) • gT p w.length c Fi L s h z‖ ^ 2) K := by
    have h1 : ContinuousOn (fun z : ℂ => ((((s : ℝ) * ‖z‖ ^ (s - 1) : ℝ)) : ℂ)) K :=
      Complex.continuous_ofReal.comp_continuousOn
        (continuousOn_const.mul (continuous_norm.continuousOn.pow _))
    exact (h1.smul hg).norm.pow 2
  refine hc.congr fun z hz => ?_
  have hz0 : z ≠ 0 := fun e => h0 (e ▸ hz)
  simp only [PBK.bz, btT, gT, hz0, if_false]

theorem field_supremum : FieldSup := by
  intro P Wp Wq _ _ _ _ _ _ I _ p nn F w c Fi L hV b s hb hs hbs h hh x hx
  set a : C.LPt := h ++ [(s - 1, x⁻¹)] with ha
  have hloc : D.IsLocPt a P.r := by
    refine ⟨fun q hq => ?_, ?_⟩
    · rcases List.mem_append.mp hq with hq | hq
      · exact hh.1 q hq
      · rw [List.mem_singleton.mp hq]
        exact ⟨show 1 ≤ s - 1 by omega, show x⁻¹ ≠ 0 from inv_ne_zero hx⟩
    · have := hh.2
      simp [ha, D.ptSize] at this ⊢
      omega
  have hx' : x ^ (s - 1) ≠ 0 := pow_ne_zero _ hx
  have hn : ‖x‖ ^ (s - 1) ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hx)
  have hcv : ∀ cc, PBK.cvec s (utT p w.length c Fi L s h) x cc = vecT p w.length c Fi L (a ++ [(1, cc)]) := by
    intro cc
    rw [PBK.cvec, utT, smul_smul, mul_div_cancel₀ cc hx', ← Complex.ofReal_mul, inv_mul_cancel₀ hn,
      Complex.ofReal_one, one_smul]
    simp [ha]
  rw [← PBK.integral_norm_cvec_sq s (utT p w.length c Fi L s h) x hx]
  simp_rw [hcv, norm_vecT_sq hV]
  rw [TBB.Ew, hV.fibre a a hloc hloc]
  exact integral_re (hV.int a hloc)

theorem field_mem_unitary : FieldMemU := by
  intro P Wp Wq _ _ _ _ _ _ I _ p nn F w c Fi L hV b s hb hs hbs h hh x hx
  set a : C.LPt := h ++ [(s - 1, x⁻¹)] with ha
  have hloc : D.IsLocPt a P.r := by
    refine ⟨fun q hq => ?_, ?_⟩
    · rcases List.mem_append.mp hq with hq | hq
      · exact hh.1 q hq
      · rw [List.mem_singleton.mp hq]
        exact ⟨show 1 ≤ s - 1 by omega, show x⁻¹ ≠ 0 from inv_ne_zero hx⟩
    · have := hh.2
      simp [ha, D.ptSize] at this ⊢
      omega
  have hx' : x ^ (s - 1) ≠ 0 := pow_ne_zero _ hx
  have hn : ‖x‖ ^ (s - 1) ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hx)
  have hcv : ∀ cc, PBK.cvec s (utT p w.length c Fi L s h) x cc = vecT p w.length c Fi L (a ++ [(1, cc)]) := by
    intro cc
    rw [PBK.cvec, utT, smul_smul, mul_div_cancel₀ cc hx', ← Complex.ofReal_mul, inv_mul_cancel₀ hn,
      Complex.ofReal_one, one_smul]
    simp [ha]
  refine (PBK.memLp_cvec s (utT p w.length c Fi L s h) x hx).2 ?_
  have hfun : PBK.cvec s (utT p w.length c Fi L s h) x = fun cc => vecT p w.length c Fi L (a ++ [(1, cc)]) :=
    funext hcv
  rw [hfun]
  have hcont := vecT_cont hV hloc.1 (m := 1) le_rfl (by rw [hloc.2])
  have hmeas : AEStronglyMeasurable (fun cc => vecT p w.length c Fi L (a ++ [(1, cc)])) volume := by
    have := hcont.aestronglyMeasurable (μ := volume) (measurableSet_singleton (0 : ℂ)).compl
    first
      | rwa [restrict_compl_singleton] at this
      | rwa [Measure.restrict_eq_self_of_ae_mem (compl_mem_ae_iff.mpr (measure_singleton 0))] at this
  refine (memLp_two_iff_integrable_sq_norm hmeas).2 ?_
  refine ((hV.int a hloc).re).congr (Filter.Eventually.of_forall fun cc => ?_)
  exact (norm_vecT_sq hV _).symm

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {I : Type} [Fintype I]
  {p : KB.Pl P Wp Wq} {nn : ℝ → ℝ} {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} {w : List C.Letter} {c : I → ℝ}
  {Fi : I → B.Mat P.k P.r → (Wq →L[ℂ] Wp)} {L : I → (Wq →L[ℂ] Wp) →L[ℂ] HS Wp Wq}

end place

end

end Formalism.FourierDecayAlt.P.CutBP.GT
end
