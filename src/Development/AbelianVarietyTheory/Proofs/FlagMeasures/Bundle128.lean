module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ShearMeasurability
public import Formalism.CyclotomicNorms.StatementT
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.FieldTheory.Finite.Extension
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle006

@[expose] public section

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.CutQuot

section Abstract

variable {X : Type*} [MeasurableSpace X] {T : X → X → X} {G R : Set X} {μG μR ν : Measure X}

theorem null_of_stable (hR : ∀ᵐ s ∂μR, s ∈ R) (h0 : μR ≠ 0)
    (hW : ∀ f : X → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, f (T s x) ∂μR) ∂ν)
    {B : Set X} (hB : MeasurableSet B) (hst : ∀ s ∈ R, ∀ x ∈ B, T s x ∈ B) (hn : μG B = 0) : ν B = 0 := by
  have h1 := hW (B.indicator 1) (measurable_one.indicator hB)
  rw [lintegral_indicator_one hB, hn] at h1
  have h2 : ∫⁻ x, B.indicator (fun _ => μR Set.univ) x ∂ν ≤
      ∫⁻ x, (∫⁻ s, B.indicator (1 : X → ℝ≥0∞) (T s x) ∂μR) ∂ν := by
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx, ← lintegral_one]
      refine le_of_eq (lintegral_congr_ae ?_)
      filter_upwards [hR] with s hs
      rw [Set.indicator_of_mem (hst s hs x hx)]; rfl
    · rw [Set.indicator_of_notMem hx]; exact zero_le
  rw [← h1, lintegral_indicator_const hB, nonpos_iff_eq_zero, mul_eq_zero] at h2
  exact h2.resolve_left (by simpa using h0)

theorem exists_cut [SigmaFinite μG] [SFinite μR] (hT : Measurable (Function.uncurry T))
    (hR : ∀ᵐ s ∂μR, s ∈ R) (h0 : μR ≠ 0)
    (hW : ∀ f : X → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, f (T s x) ∂μR) ∂ν)
    (hG : ∀ᵐ x ∂ν, x ∈ G)
    (hinv : ∀ ρ ∈ R, ∀ x, ∀ f : X → ℝ≥0∞, Measurable f →
      ∫⁻ s, f (T s (T ρ x)) ∂μR = ∫⁻ s, f (T s x) ∂μR) :
    ∃ φ : X → ℝ≥0∞, Measurable φ ∧ (∀ x, ∫⁻ ρ, φ (T ρ x) ∂μR ≤ 1) ∧
      ∀ F : X → ℝ≥0∞, Measurable F → (∀ ρ ∈ R, ∀ x ∈ G, F (T ρ x) = F x) →
        ∫⁻ x, F x ∂ν = ∫⁻ x, φ x * F x ∂μG := by
  obtain ⟨g, hg0, hgm, hgi⟩ := exists_pos_lintegral_lt_of_sigmaFinite μG (ε := 1) one_ne_zero
  set ψ : X → ℝ≥0∞ := fun x => (g x : ℝ≥0∞) with hψ
  have hψm : Measurable ψ := hgm.coe_nnreal_ennreal
  have hTx : ∀ x, Measurable fun s => T s x := fun x => hT.comp (measurable_id.prodMk measurable_const)
  set I : X → ℝ≥0∞ := fun x => ∫⁻ s, ψ (T s x) ∂μR with hI
  have hIm : Measurable I := Measurable.lintegral_prod_left (f := fun s x => ψ (T s x)) (hψm.comp hT)
  have hI0 : ∀ x, I x ≠ 0 := by
    intro x hx
    have h := (lintegral_eq_zero_iff (hψm.comp (hTx x))).1 hx
    apply h0
    rw [← ae_eq_bot, ← Filter.eventually_false_iff_eq_bot]
    filter_upwards [h] with s hs
    have := hg0 (T s x)
    simp [hψ] at hs
    exact this.ne' hs
  have hIfin : ∀ᵐ x ∂ν, I x < ∞ := by
    refine ae_lt_top hIm ?_
    rw [← hW ψ hψm]
    exact (hgi.trans ENNReal.one_lt_top).ne
  have key : ∀ x, ∫⁻ ρ, ψ (T ρ x) * (I (T ρ x))⁻¹ ∂μR = I x * (I x)⁻¹ := by
    intro x
    rw [show I x * (I x)⁻¹ = ∫⁻ ρ, ψ (T ρ x) * (I x)⁻¹ ∂μR from
      (lintegral_mul_const (I x)⁻¹ (f := fun s => ψ (T s x)) (hψm.comp (hTx x))).symm]
    refine lintegral_congr_ae ?_
    filter_upwards [hR] with s hs
    have : I (T s x) = I x := hinv s hs x ψ hψm
    rw [this]
  have hφm : Measurable fun x => ψ x * (I x)⁻¹ := hψm.mul hIm.inv
  refine ⟨fun x => ψ x * (I x)⁻¹, hφm, fun x => ?_, fun F hF hFi => ?_⟩
  · rw [key]; exact ENNReal.mul_inv_le_one _
  · show _ = ∫⁻ x, ψ x * (I x)⁻¹ * F x ∂μG
    rw [hW (fun x => ψ x * (I x)⁻¹ * F x) (hφm.mul hF)]
    refine lintegral_congr_ae ?_
    filter_upwards [hG, hIfin] with x hx hx'
    have h1 : ∫⁻ s, ψ (T s x) * (I (T s x))⁻¹ * F (T s x) ∂μR =
        ∫⁻ s, ψ (T s x) * (I (T s x))⁻¹ * F x ∂μR := by
      refine lintegral_congr_ae ?_
      filter_upwards [hR] with s hs
      rw [hFi s hs x hx]
    rw [h1, lintegral_mul_const (F x) (f := fun s => ψ (T s x) * (I (T s x))⁻¹) (hφm.comp (hTx x)), key,
      ENNReal.mul_inv_cancel (hI0 x) hx'.ne, one_mul]

end Abstract

theorem mul_mem_iff {k r : ℕ} {s : Mat k r} (hs : s ∈ GG k r) (x : Mat k r) :
    s * x ∈ GG k r ↔ x ∈ GG k r := by
  have hs' : sᴴ * Hpk k r * s = Hpk k r := hs
  have : (s * x)ᴴ * Hpk k r * (s * x) = xᴴ * Hpk k r * x := by
    rw [conjTranspose_mul]
    conv_rhs => rw [← hs']
    simp only [Matrix.mul_assoc]
  show (s * x)ᴴ * Hpk k r * (s * x) = Hpk k r ↔ xᴴ * Hpk k r * x = Hpk k r
  rw [this]

theorem measurable_G (k r : ℕ) : MeasurableSet {x : Mt k r | Matrix.of x ∈ GG k r} := by
  refine IsClosed.measurableSet ?_
  have h : Continuous fun x : Mt k r => (Matrix.of x : Mat k r) := continuous_id
  exact isClosed_eq (f := fun x : Mt k r => (Matrix.of x : Mat k r)ᴴ * Hpk k r * Matrix.of x)
    ((h.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul h) continuous_const

theorem continuous_act (k r : ℕ) :
    Continuous (Function.uncurry fun s x : Mt k r => lmulM (Matrix.of s) x) := by
  have h : Continuous fun x : Mt k r => (Matrix.of x : Mat k r) := continuous_id
  exact (h.comp continuous_fst).matrix_mul (h.comp continuous_snd)

theorem cut_quotient : ∀ (k r : ℕ) (R : Set (Mat k r)) (μG μR ν : Measure (Mt k r)), IsClosedSub k r R → IsHaarOn (GG k r) μG → IsHaarOn R μR → IsUnimod R μR → IsQuotMeas μG μR ν → ν {x | Matrix.of x ∉ GG k r} = 0 ∧ (∀ A : Set (Mt k r), MeasurableSet A → (∀ ρ ∈ R, ∀ x, Matrix.of x ∈ GG k r → (lmulM ρ x ∈ A ↔ x ∈ A)) → μG A = 0 → ν A = 0) ∧ ∃ φ, SubCut (GG k r) μR φ ∧ ∀ F : Mt k r → ℝ≥0∞, Measurable F → (∀ ρ ∈ R, ∀ x, Matrix.of x ∈ GG k r → F (lmulM ρ x) = F x) → ∫⁻ x, F x ∂ν = ∫⁻ x, φ x * F x ∂μG := by
  intro k r R μG μR ν hR hG hμ hU hW
  haveI := hG.1
  haveI := hμ.1
  set T : Mt k r → Mt k r → Mt k r := fun s x => lmulM (Matrix.of s) x with hT
  have hTm : Measurable (Function.uncurry T) := (continuous_act k r).measurable
  have hae : ∀ᵐ s ∂μR, s ∈ {x : Mt k r | Matrix.of x ∈ R} := hμ.2.2.1
  have hW' : ∀ f : Mt k r → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, f (T s x) ∂μR) ∂ν := hW
  have hmem : ∀ s : Mt k r, Matrix.of s ∈ R → ∀ x : Mt k r,
      (Matrix.of (T s x) ∈ GG k r ↔ Matrix.of x ∈ GG k r) := fun s hs x =>
    mul_mem_iff (hR.1 hs) (Matrix.of x)
  have h1 : ν {x | Matrix.of x ∉ GG k r} = 0 :=
    null_of_stable hae hμ.2.1 hW' (measurable_G k r).compl
      (fun s hs x hx h => hx ((hmem s hs x).1 h)) hG.2.2.1
  have h1' : ∀ᵐ x ∂ν, x ∈ {x : Mt k r | Matrix.of x ∈ GG k r} := h1
  refine ⟨h1, fun A hA hst hn => ?_, ?_⟩
  · have h2 : ν (A ∩ {x : Mt k r | Matrix.of x ∈ GG k r}) = 0 :=
      null_of_stable hae hμ.2.1 hW' (hA.inter (measurable_G k r))
        (fun s hs x hx => ⟨(hst _ hs x hx.2).2 hx.1, (hmem s hs x).2 hx.2⟩)
        (measure_mono_null Set.inter_subset_left hn)
    refine measure_mono_null (fun x hx => ?_) (measure_union_null h2 h1)
    by_cases h : Matrix.of x ∈ GG k r
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr h
  · obtain ⟨φ, hφ, hle, hF⟩ := exists_cut hTm hae hμ.2.1 hW' h1' (by
      intro ρ hρ x f hf
      have hTx : Measurable fun s => T s x := hTm.comp (measurable_id.prodMk measurable_const)
      have hc : Continuous fun x : Mt k r => (Matrix.of x : Mat k r) := continuous_id
      have hr : Measurable (rmulM (k := k) (r := r) (Matrix.of ρ)) :=
        by
        have hc' : Continuous (rmulM (k := k) (r := r) (Matrix.of ρ)) := hc.matrix_mul continuous_const
        exact hc'.measurable
      conv_rhs => rw [← hU.1 (Matrix.of ρ) hρ]
      rw [lintegral_map (f := fun s => f (T s x)) (hf.comp hTx) hr]
      refine lintegral_congr fun s => congrArg f ?_
      exact (Matrix.mul_assoc (Matrix.of s) (Matrix.of ρ) (Matrix.of x)).symm)
    exact ⟨φ, ⟨hφ, fun x _ => hle x⟩, fun F hFm hFi => hF F hFm fun ρ hρ x hx => hFi _ hρ x hx⟩

end GlobalTheory.Amp.CutQuot
end

section

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.USplit

def coords {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) : UT r → ℂ := fun p => A p.1.1 p.1.2

theorem upper_of_lt {r : ℕ} (x : UT r → ℂ) {a b : Fin r} (h : a < b) : upper x a b = x ⟨(a, b), h⟩ := by
  unfold upper
  rw [dif_pos h]

theorem upper_diag {r : ℕ} (x : UT r → ℂ) (a : Fin r) : upper x a a = 1 := by
  unfold upper
  rw [dif_neg (lt_irrefl a), if_pos rfl]

theorem upper_of_gt {r : ℕ} (x : UT r → ℂ) {a b : Fin r} (h : b < a) : upper x a b = 0 := by
  unfold upper
  rw [dif_neg (lt_asymm h), if_neg (ne_of_gt h)]

theorem mul_apply_lt {r : ℕ} (x y : UT r → ℂ) {a b : Fin r} (h : a < b) :
    (upper x * upper y) a b = x ⟨(a, b), h⟩ + y ⟨(a, b), h⟩ +
      ∑ c, if a < c ∧ c < b then upper x a c * upper y c b else 0 := by
  rw [Matrix.mul_apply]
  have key : ∀ c, upper x a c * upper y c b =
      ((if c = a then y ⟨(a, b), h⟩ else 0) + (if c = b then x ⟨(a, b), h⟩ else 0)) +
        (if a < c ∧ c < b then upper x a c * upper y c b else 0) := by
    intro c
    rcases lt_trichotomy c a with hca | hca | hac
    · have hcb : c ≠ b := ne_of_lt (hca.trans h)
      rw [upper_of_gt x hca, zero_mul, if_neg (ne_of_lt hca), if_neg hcb,
        if_neg (fun k => lt_asymm hca k.1)]
      simp
    · subst hca
      rw [upper_diag, one_mul, upper_of_lt y h, if_pos rfl, if_neg (ne_of_lt h),
        if_neg (fun k => lt_irrefl _ k.1)]
      simp
    · rcases lt_trichotomy c b with hcb | hcb | hbc
      · rw [if_neg (ne_of_gt hac), if_neg (ne_of_lt hcb), if_pos ⟨hac, hcb⟩]
        simp
      · subst hcb
        rw [upper_diag, mul_one, upper_of_lt x h, if_neg (ne_of_gt h), if_pos rfl,
          if_neg (fun k => lt_irrefl _ k.2)]
        simp
      · rw [upper_of_gt y hbc, mul_zero, if_neg (ne_of_gt hac), if_neg (ne_of_gt hbc),
          if_neg (fun k => lt_asymm hbc k.2)]
        simp
  rw [Finset.sum_congr rfl (fun c _ => key c), Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ a, Finset.sum_ite_eq' Finset.univ b]
  simp only [Finset.mem_univ, if_true]
  ring

theorem upper_coords_mul {r : ℕ} (x y : UT r → ℂ) : upper (coords (upper x * upper y)) = upper x * upper y := by
  ext a b
  rcases lt_trichotomy a b with hab | hab | hba
  · rw [upper_of_lt _ hab]
    rfl
  · subst hab
    rw [upper_diag, Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [upper_diag, upper_diag, mul_one]
    · intro c _ hc
      rcases lt_or_gt_of_ne hc with hlt | hgt
      · rw [upper_of_gt x hlt, zero_mul]
      · rw [upper_of_gt y hgt, mul_zero]
    · intro ha
      exact absurd (Finset.mem_univ a) ha
  · rw [upper_of_gt _ hba, Matrix.mul_apply]
    refine (Finset.sum_eq_zero fun c _ => ?_).symm
    rcases lt_or_ge c a with hca | hac
    · rw [upper_of_gt x hca, zero_mul]
    · rw [upper_of_gt y (lt_of_lt_of_le hba hac), mul_zero]

theorem continuous_upper (r : ℕ) : Continuous (upper : (UT r → ℂ) → Matrix (Fin r) (Fin r) ℂ) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  by_cases h : a < b
  · simp only [upper, dif_pos h]
    exact continuous_apply _
  · simp only [upper, dif_neg h]
    exact continuous_const

theorem continuous_upperIn {r : ℕ} (β : Fin r → ℕ) : Continuous (upperIn β) := by
  have hg : Continuous fun (x : UTin β → ℂ) (p : UT r) =>
      if h : β p.1.1 = β p.1.2 then x ⟨p, h⟩ else 0 := by
    refine continuous_pi fun p => ?_
    by_cases h : β p.1.1 = β p.1.2
    · simp only [dif_pos h]
      exact continuous_apply _
    · simp only [dif_neg h]
      exact continuous_const
  exact (continuous_upper r).comp hg

theorem continuous_upperOff {r : ℕ} (β : Fin r → ℕ) : Continuous (upperOff β) := by
  have hg : Continuous fun (x : UToff β → ℂ) (p : UT r) =>
      if h : β p.1.1 ≠ β p.1.2 then x ⟨p, h⟩ else 0 := by
    refine continuous_pi fun p => ?_
    by_cases h : β p.1.1 ≠ β p.1.2
    · simp only [dif_pos h]
      exact continuous_apply _
    · simp only [dif_neg h]
      exact continuous_const
  exact (continuous_upper r).comp hg

def prodMap {r : ℕ} (β : Fin r → ℕ) (u : UT r → ℂ) : UT r → ℂ :=
  coords (upperIn β (fun p => u p.1) * upperOff β (fun p => u p.1))

theorem continuous_prodMap {r : ℕ} (β : Fin r → ℕ) : Continuous (prodMap β) := by
  have h1 : Continuous fun u : UT r → ℂ => upperIn β (fun p => u p.1) :=
    (continuous_upperIn β).comp (continuous_pi fun p => continuous_apply _)
  have h2 : Continuous fun u : UT r → ℂ => upperOff β (fun p => u p.1) :=
    (continuous_upperOff β).comp (continuous_pi fun p => continuous_apply _)
  exact continuous_pi fun p => (h1.matrix_mul h2).matrix_elem p.1.1 p.1.2

private theorem shearCond_prodMap {r : ℕ} (β : Fin r → ℕ) :
    Formalism.FourierDecayAlt.P.ShearMeasurability.ShearCond (fun p : UT r => p.1.2.val - p.1.1.val) (prodMap β) := by
  intro q x y hxy
  obtain ⟨⟨a, b⟩, h⟩ := q
  have e : ∀ u : UT r → ℂ, prodMap β u ⟨(a, b), h⟩ - u ⟨(a, b), h⟩ = ∑ c, if a < c ∧ c < b then
      upper (fun p => if β p.1.1 = β p.1.2 then u p else 0) a c *
      upper (fun p => if β p.1.1 ≠ β p.1.2 then u p else 0) c b else 0 := by
    intro u
    have hin : upperIn β (fun p => u p.1) = upper (fun p => if β p.1.1 = β p.1.2 then u p else 0) := by
      unfold upperIn
      congr 1
    have hoff : upperOff β (fun p => u p.1) =
        upper (fun p => if β p.1.1 ≠ β p.1.2 then u p else 0) := by
      unfold upperOff
      congr 1
    show (upperIn β (fun p => u p.1) * upperOff β (fun p => u p.1)) a b - _ = _
    rw [hin, hoff, mul_apply_lt _ _ h]
    by_cases hb : β a = β b
    · have hb' : ¬ β a ≠ β b := not_not.mpr hb
      simp only [if_pos hb, if_neg hb', add_zero, add_sub_cancel_left]
    · simp only [if_neg hb, if_pos hb, zero_add, add_sub_cancel_left]
  rw [e x, e y]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs with hc
  · have h1 : c.val - a.val < b.val - a.val := by
      have := hc.1; have := hc.2; omega
    have h2 : b.val - c.val < b.val - a.val := by
      have := hc.1; have := hc.2; omega
    rw [upper_of_lt _ hc.1, upper_of_lt _ hc.2, upper_of_lt _ hc.1, upper_of_lt _ hc.2,
      hxy ⟨(a, c), hc.1⟩ h1, hxy ⟨(c, b), hc.2⟩ h2]
  · rfl

theorem prodMap_mp {r : ℕ} (β : Fin r → ℕ) : MeasurePreserving (prodMap β) volume volume := Formalism.FourierDecayAlt.P.ShearMeasurability.shear_mp _ (prodMap β) (continuous_prodMap β).measurable (shearCond_prodMap β)

theorem lebesgue_split : ∀ (r : ℕ) (β : Fin r → ℕ), Monotone β → (∀ (x : UTin β → ℂ) (y : UToff β → ℂ), ∃ u : UT r → ℂ, upper u = upperIn β x * upperOff β y) ∧ ∀ f : (Fin r → Fin r → ℂ) → ℝ≥0∞, Measurable f → ∫⁻ u : UT r → ℂ, f (Matrix.of.symm (upper u)) = ∫⁻ y : UToff β → ℂ, ∫⁻ x : UTin β → ℂ, f (Matrix.of.symm (upperIn β x * upperOff β y)) := by
  intro r β _
  refine ⟨fun x y => ⟨coords (upperIn β x * upperOff β y), ?_⟩, fun f hf => ?_⟩
  · unfold upperIn upperOff
    exact upper_coords_mul _ _
  · have hc : Continuous fun u : UT r → ℂ => (Matrix.of.symm (upper u) : Fin r → Fin r → ℂ) :=
      continuous_upper r
    have hu : Measurable fun u : UT r → ℂ => f (Matrix.of.symm (upper u)) := hf.comp hc.measurable
    have hM : Continuous fun z : (UTin β → ℂ) × (UToff β → ℂ) =>
        (Matrix.of.symm (upperIn β z.1 * upperOff β z.2) : Fin r → Fin r → ℂ) :=
      ((continuous_upperIn β).comp continuous_fst).matrix_mul ((continuous_upperOff β).comp continuous_snd)
    have hG : Measurable fun z : (UTin β → ℂ) × (UToff β → ℂ) =>
        f (Matrix.of.symm (upperIn β z.1 * upperOff β z.2)) := hf.comp hM.measurable
    have hsplit := MeasureTheory.volume_preserving_piEquivPiSubtypeProd (fun _ : UT r => ℂ)
      (fun p : UT r => β p.1.1 = β p.1.2)
    have key : ∀ v : UT r → ℂ, f (Matrix.of.symm (upper (prodMap β v))) =
        f (Matrix.of.symm (upperIn β (fun p => v p.1) * upperOff β (fun p => v p.1))) := by
      intro v
      have hp : upper (prodMap β v) = upperIn β (fun p => v p.1) * upperOff β (fun p => v p.1) := by
        unfold prodMap upperIn upperOff
        exact upper_coords_mul _ _
      rw [hp]
    calc ∫⁻ u : UT r → ℂ, f (Matrix.of.symm (upper u))
        = ∫⁻ v : UT r → ℂ, f (Matrix.of.symm (upper (prodMap β v))) :=
          ((prodMap_mp β).lintegral_comp hu).symm
      _ = ∫⁻ v : UT r → ℂ, (fun z : (UTin β → ℂ) × (UToff β → ℂ) =>
            f (Matrix.of.symm (upperIn β z.1 * upperOff β z.2)))
            (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : UT r => ℂ)
              (fun p : UT r => β p.1.1 = β p.1.2) v) := lintegral_congr fun v => key v
      _ = ∫⁻ z : (UTin β → ℂ) × (UToff β → ℂ), f (Matrix.of.symm (upperIn β z.1 * upperOff β z.2)) :=
          hsplit.lintegral_comp hG
      _ = _ := lintegral_prod_symm _ hG.aemeasurable

end GlobalTheory.Amp.USplit
end
end

section

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm.SubfieldCount

theorem sum_bound {g : ℕ} (hg : 5 ≤ g) (m : ℕ) :
    4 * (∑ e ∈ Finset.range m, (g ^ (e + 1) - 1)) + 4 * m + 5 ≤ 5 * g ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have h1 : 0 < g ^ (m + 1) := pow_pos (by omega) _
    have h2 : 5 * g ^ m ≤ g ^ (m + 1) := by
      rw [pow_succ, mul_comm]; exact Nat.mul_le_mul_left _ hg
    omega

theorem five_mul_le {g : ℕ} (hg : 5 ≤ g) (m : ℕ) : 5 * (m + 1) ≤ g ^ (m + 1) := by
  induction m with
  | zero => simpa using hg
  | succ m ih =>
    have h2 : g ^ (m + 1) * 5 ≤ g ^ (m + 1 + 1) := by
      rw [pow_succ g (m + 1)]; exact Nat.mul_le_mul_left _ hg
    omega

theorem num_bound {g : ℕ} (hg : 5 ≤ g) {d : ℕ} (hd : 0 < d) :
    2 * d * (∑ e ∈ Finset.range (d / 2), (g ^ (e + 1) - 1)) < g ^ d - 1 := by
  have key : ∀ m : ℕ, 4 * (m + 1) * (∑ e ∈ Finset.range (m + 1), (g ^ (e + 1) - 1)) + 1
      < g ^ (2 * (m + 1)) := by
    intro m
    have h1 := sum_bound hg (m + 1)
    have h2 := five_mul_le hg m
    rw [two_mul (m + 1), pow_add]
    generalize (∑ e ∈ Finset.range (m + 1), (g ^ (e + 1) - 1)) = T at *
    generalize g ^ (m + 1) = x at *
    have h3 := Nat.mul_le_mul_left (m + 1) h1
    have h4 := Nat.mul_le_mul_right x h2
    nlinarith
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' d
  · obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have h := key m
    rw [show 2 * (m + 1) / 2 = m + 1 by omega, show 2 * (2 * (m + 1)) = 4 * (m + 1) by ring]
    omega
  · rcases m with _ | m
    · simp; omega
    · have h := key m
      rw [show (2 * (m + 1) + 1) / 2 = m + 1 by omega, pow_succ g (2 * (m + 1))]
      generalize (∑ e ∈ Finset.range (m + 1), (g ^ (e + 1) - 1)) = T at *
      generalize g ^ (2 * (m + 1)) = x at *
      have h4 := Nat.mul_le_mul_left x hg
      apply Nat.lt_sub_of_add_lt
      nlinarith [Nat.zero_le (m * T), Nat.zero_le T]

theorem natDegree_dvd_iff {g : ℕ} [Fact g.Prime] (z : Formalism.CyclotomicNorms.Fbar g) (n : ℕ) :
    (minpoly (ZMod g) z).natDegree ∣ n ↔ z ^ (g ^ n) = z := by
  have hx : IsIntegral (ZMod g) z := Algebra.IsIntegral.isIntegral z
  rw [(minpoly.irreducible hx).natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X, minpoly.dvd_iff,
    Nat.card_zmod]
  simp [sub_eq_zero]

end GlobalTheory.GLm.SubfieldCount

namespace GlobalTheory.GLm
open SubfieldCount

theorem card_proper_subfield_elements_lt : ∀ (g : ℕ) [Fact g.Prime] (d : ℕ), 5 ≤ g → 0 < d →
    2 * d * Nat.card {z : Formalism.CyclotomicNorms.Fbar g // z ≠ 0 ∧ z ^ (g ^ d) = z ∧
      (minpoly (ZMod g) z).natDegree ≠ d} < g ^ d - 1 := by
  intro g _ d hg hd
  refine lt_of_le_of_lt (Nat.mul_le_mul_left _ ?_) (num_bound hg hd)
  let F : Finset (Formalism.CyclotomicNorms.Fbar g) := (Finset.range (d / 2)).biUnion fun e =>
    (nthRoots (g ^ (e + 1) - 1) (1 : Formalism.CyclotomicNorms.Fbar g)).toFinset
  have hsub : {z : Formalism.CyclotomicNorms.Fbar g | z ≠ 0 ∧ z ^ (g ^ d) = z ∧
      (minpoly (ZMod g) z).natDegree ≠ d} ⊆ (F : Set _) := by
    rintro z ⟨h0, hz, hne⟩
    have hx : IsIntegral (ZMod g) z := Algebra.IsIntegral.isIntegral z
    have hpos := minpoly.natDegree_pos hx
    have h1 := (natDegree_dvd_iff z _).1 dvd_rfl
    obtain ⟨k, hk⟩ := (natDegree_dvd_iff z d).2 hz
    obtain ⟨e, he⟩ : ∃ e, (minpoly (ZMod g) z).natDegree = e + 1 :=
      ⟨(minpoly (ZMod g) z).natDegree - 1, by omega⟩
    rw [he] at hk h1 hne
    have hk2 : 2 ≤ k := by
      rcases k with _ | _ | k
      · omega
      · omega
      · omega
    have hle : (e + 1) * 2 ≤ d := hk ▸ Nat.mul_le_mul_left _ hk2
    have hp : 1 < g ^ (e + 1) := Nat.one_lt_pow (by omega) (by omega)
    simp only [F, Finset.coe_biUnion, Finset.coe_range, Set.mem_iUnion, Finset.mem_coe,
      Multiset.mem_toFinset]
    refine ⟨e, by simp only [Set.mem_Iio]; omega, ?_⟩
    rw [mem_nthRoots (by omega)]
    apply mul_right_cancel₀ h0
    rw [← pow_succ, one_mul, Nat.sub_add_cancel hp.le, h1]
  calc _ = Set.ncard {z : Formalism.CyclotomicNorms.Fbar g | z ≠ 0 ∧ z ^ (g ^ d) = z ∧
      (minpoly (ZMod g) z).natDegree ≠ d} := rfl
    _ ≤ (F : Set _).ncard := Set.ncard_le_ncard hsub F.finite_toSet
    _ = F.card := Set.ncard_coe_finset F
    _ ≤ _ := Finset.card_biUnion_le.trans (Finset.sum_le_sum fun e _ =>
        (Multiset.toFinset_card_le _).trans (card_nthRoots _ _))

end GlobalTheory.GLm
end
