module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle049
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle048
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle050
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

def topR {P : M.Par} (l0 : ℕ) (w : List C.Letter) (e : Wd.Ix (Fin w.length)) (ρ : M.Ty P) (y : ℝ) : ℂ :=
  Wd.qw (M.qC P) (D.positionted w) (y : ℂ) / Fr.xs (fun Y => M.sgn P l0 * M.xC P ρ Y) (D.positionted w) e ((y : ℂ) + 1)

def TopRatio : Prop :=
  ∀ (Cb Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) (A₀ : ℝ),
    KB.IsLeadingFormSetting Cb Cc S p f χ A₀ → 28 * Real.exp 1 ≤ Cc → ∀ (v : Fin S.f) (w : List C.Letter) (y : ℝ),
    KB.CutWord (D.parOf S v) (S.l + 1) ((true, y) :: w) → (∃ m, y ∈ S.grid v m) → w.length < S.Ntop →
    (∀ x ∈ w, (S.Ntop : ℝ) ^ 2 + 1 ≤ |y - x.2| ∧ (x.1 = false → (S.Ntop : ℝ) ^ 2 + 1 ≤ |y - (x.2 - 1)|)) →
    ∀ (e : Wd.Ix (Fin w.length)) (ρ : M.Ty (D.parOf S v)),
      0 < (topR (S.l + 1) w e ρ y).re ∧ (topR (S.l + 1) w e ρ y).im = 0 ∧
      |S.P v y| ≤ Real.exp 1 * J.supA S.G S.de S.de' S.T S.T' S.l false (S.pl v) *
        (Real.sqrt (S.T * S.T'))⁻¹ * (topR (S.l + 1) w e ρ y).re

def lamTop {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
    [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq) (b : ℕ) (v : Fin S.f) : ℝ :=
  √((2 * Real.pi / S.G.g) ^ (-(2 * S6.nuBlock S.G.r b ((S.G.r : ℤ) + 2 - b))) * Real.exp 1 *
    (28 * S.G.N / S.G.lenI) ^ (2 * (b - 1)) * J.supA S.G S.de S.de' S.T S.T' S.l false (S.pl v) *
    (√(S.T * S.T'))⁻¹)

def TopLocB : Prop :=
  KB.DegTop → Top.VecVTypes → TopRatio →
  ∀ (Cb Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) (A₀ : ℝ),
    28 * Real.exp 1 ≤ Cc → KB.IsLeadingFormSetting Cb Cc S p f χ A₀ →
    (∀ s, 2 ≤ s → s ≤ S.G.r + 1 → ∀ v, 0 ≤ lamTop S (S.G.r + 2 - s) v ∧
      2 * lamTop S (S.G.r + 2 - s) v ≤ S.base.szL (S.G.r + 2 - s) s v) ∧
    ∀ F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)),
      (∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) → ∀ v, KB.TopLoc (setC S p F) v fun b _ => lamTop S b v

end

end Formalism.FourierDecayAlt.P.PBL
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt MeasureTheory

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField

noncomputable section

section gen

variable (P : M.Par)

theorem jd_actA_add (a b : MA.A P (MA.DQ P)) (x : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (a + b) x = MA.actA P a x + MA.actA P b x := by
  funext π
  show ∑ π', ((a + b) π π').1 (x π') = ∑ π', (a π π').1 (x π') + ∑ π', (b π π').1 (x π')
  rw [← Finset.sum_add_distrib]
  rfl

theorem jd_actA_zero (x : M.Ty P → MA.SmQ P.r P.TT) : MA.actA P 0 x = 0 := by
  funext π
  show ∑ π', ((0 : MA.A P (MA.DQ P)) π π').1 (x π') = 0
  exact Finset.sum_eq_zero fun _ _ => rfl

theorem jd_actA_addR (a : MA.A P (MA.DQ P)) (x y : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P a (x + y) = MA.actA P a x + MA.actA P a y := by
  funext π
  show ∑ π', (a π π').1 (x π' + y π') = ∑ π', (a π π').1 (x π') + ∑ π', (a π π').1 (y π')
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => map_add _ _ _

theorem jd_actA_smulR (a : MA.A P (MA.DQ P)) (c : ℂ) (x : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P a (c • x) = c • MA.actA P a x := by
  funext π
  show ∑ π', (a π π').1 (c • x π') = c • ∑ π', (a π π').1 (x π')
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun _ _ => map_smul _ _ _

theorem jd_actA_zeroR (a : MA.A P (MA.DQ P)) : MA.actA P a 0 = 0 := by
  have h := jd_actA_smulR P a 0 0
  rw [zero_smul, zero_smul] at h
  exact h

theorem jd_actA_listsum {ι : Type} (a : MA.A P (MA.DQ P)) (l : List ι) (g : ι → M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P a (l.map g).sum = (l.map fun i => MA.actA P a (g i)).sum := by
  induction l with
  | nil => simp only [List.map_nil, List.sum_nil]; exact jd_actA_zeroR P a
  | cons i l ih => rw [List.map_cons, List.sum_cons, jd_actA_addR, ih, List.map_cons, List.sum_cons]

variable {P}

theorem jd_word_span {Fn : Type} (L : R.LevelData (MA.A P (MA.DQ P)) P.r) (Good : ℕ → Fn → Prop)
    (tr : Fn → M.Ty P → MA.SmQ P.r P.TT) (m : ℕ)
    (hBdd : ∀ X ∈ MA.hatSet P L, ∀ b ∈ Submonoid.closure (MA.bddSet P L), X * b ∈ Submodule.span ℂ (bddHat P L))
    (hStep : ∀ i, i < m → ∀ F, Good i F → ∀ X ∈ MA.hatSet P L,
      ∃ ts : List (MA.A P (MA.DQ P) × Fn), (∀ t ∈ ts, t.1 ∈ Submonoid.closure (MA.bddSet P L) ∧ Good (i + 1) t.2) ∧
        MA.actA P X (tr F) = (ts.map fun t => MA.actA P t.1 (tr t.2)).sum) :
    ∀ w : List (MA.A P (MA.DQ P)), w.length ≤ m → (∀ a ∈ w, a ∈ MA.hatSet P L) → ∀ F, Good 0 F →
      MA.actA P w.prod (tr F) ∈ Submodule.span ℂ
        {u | ∃ b ∈ Submonoid.closure (MA.bddSet P L), ∃ F', Good w.length F' ∧ u = MA.actA P b (tr F')} := by
  intro w
  induction w with
  | nil =>
    intro _ _ F hF
    refine Submodule.subset_span ⟨1, Submonoid.one_mem _, F, hF, ?_⟩
    rw [List.prod_nil, actA_one]
  | cons a w ih =>
    intro hlen hw F hF
    have ha : a ∈ MA.hatSet P L := hw a (List.mem_cons_self ..)
    have hlt : w.length < m := by simp only [List.length_cons] at hlen; omega
    have hIH := ih hlt.le (fun x hx => hw x (List.mem_cons_of_mem _ hx)) F hF
    rw [List.prod_cons, actA_mul]
    have hgen : ∀ c ∈ Submodule.span ℂ (bddHat P L), ∀ F', Good w.length F' →
        MA.actA P c (tr F') ∈ Submodule.span ℂ
          {u | ∃ b ∈ Submonoid.closure (MA.bddSet P L), ∃ F', Good (a :: w).length F' ∧ u = MA.actA P b (tr F')} := by
      intro c hc F' hF'
      induction hc using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨b', hb', X', hX', rfl⟩ := hx
        obtain ⟨ts, hts, he⟩ := hStep w.length hlt F' hF' X' hX'
        rw [actA_mul, he, jd_actA_listsum]
        refine list_sum_mem fun u hu => ?_
        obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hu
        rw [← actA_mul]
        exact Submodule.subset_span ⟨b' * t.1, Submonoid.mul_mem _ hb' (hts t ht).1, t.2, (hts t ht).2, rfl⟩
      | zero => rw [jd_actA_zero]; exact Submodule.zero_mem _
      | add x y _ _ h1 h2 => rw [jd_actA_add]; exact Submodule.add_mem _ h1 h2
      | smul c x _ h1 => rw [actA_smul]; exact Submodule.smul_mem _ c h1
    have key : ∀ x ∈ Submodule.span ℂ
        {u | ∃ b ∈ Submonoid.closure (MA.bddSet P L), ∃ F', Good w.length F' ∧ u = MA.actA P b (tr F')},
        MA.actA P a x ∈ Submodule.span ℂ
          {u | ∃ b ∈ Submonoid.closure (MA.bddSet P L), ∃ F', Good (a :: w).length F' ∧ u = MA.actA P b (tr F')} := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨b, hb, F', hF', rfl⟩ := hx
        rw [← actA_mul]
        exact hgen _ (hBdd a ha b hb) F' hF'
      | zero => rw [jd_actA_zeroR]; exact Submodule.zero_mem _
      | add x y _ _ h1 h2 => rw [jd_actA_addR]; exact Submodule.add_mem _ h1 h2
      | smul c x _ h1 => rw [jd_actA_smulR]; exact Submodule.smul_mem _ c h1
    exact key _ hIH

variable (P)

theorem jd_evQ_meas (g : MA.SmQ P.r P.TT) : AEStronglyMeasurable (MA.evQ P g) (MA.mu0 P.r P.TT) := by
  have hs : ContDiffOn ℝ MA.sm (MA.ext (g : MA.Qp P.r P.TT → ℂ)) (MA.Qset P.r P.TT) := g.2
  have h2 := hs.continuousOn.comp_continuous continuous_subtype_val (fun q => q.2)
  have hc : Continuous (MA.evQ P g) := h2.congr fun q => by
    simp only [Function.comp, MA.ext, dif_pos q.2]
    rfl
  exact hc.aestronglyMeasurable

def componentwiseL2 (u : M.Ty P → MA.SmQ P.r P.TT) : Prop := ∀ π, MemLp (MA.evQ P (u π)) 2 (MA.mu0 P.r P.TT)

theorem componentwiseL2_iff_integrable (u : M.Ty P → MA.SmQ P.r P.TT) :
    componentwiseL2 P u ↔ ∀ π, Integrable (fun q => ‖MA.evQ P (u π) q‖ ^ 2) (MA.mu0 P.r P.TT) :=
  forall_congr' fun π => memLp_two_iff_integrable_sq_norm (jd_evQ_meas P (u π))

theorem componentwiseL2_of_span (G : Set (M.Ty P → MA.SmQ P.r P.TT)) (h : ∀ u ∈ G, componentwiseL2 P u) :
    ∀ u ∈ Submodule.span ℂ G, componentwiseL2 P u := by
  intro u hu
  induction hu using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => intro π; exact MemLp.zero
  | add x y _ _ h1 h2 => intro π; exact (h1 π).add (h2 π)
  | smul c x _ h1 => intro π; exact (h1 π).const_smul c

end gen

theorem jd_arith (C2 C3 C5 R n N A₀ : ℝ) (hC2 : 0 ≤ C2) (hR : 0 ≤ R) (hn : 1 ≤ n) (hN : 0 ≤ N)
    (hA : (8 * C2 + |C3| + |C5|) * (R + 1) ^ 4 * (N * n ^ 2 + n ^ 3) ≤ A₀) :
    (∀ i o : ℝ, i + 1 ≤ 2 * N + 2 → o ≤ C2 * n →
      C3 * (R + 1) * n ^ 2 + 6 * R * o + C2 * (R + 1) * n ≤ A₀ - i * (C2 * (R + 1) * n)) ∧
      (∀ i : ℝ, i ≤ 2 * N + 2 → C5 * (R + 1) ^ 2 * n ≤ A₀ - i * (C2 * (R + 1) * n)) := by
  have hρ : 1 ≤ R + 1 := by linarith
  have hρ0 : 0 ≤ R + 1 := by linarith
  have hn0 : 0 ≤ n := by linarith
  have hρ4 : R + 1 ≤ (R + 1) ^ 4 := le_self_pow₀ hρ (by norm_num)
  have hR4 : R ≤ (R + 1) ^ 4 := by linarith
  have hρ24 : (R + 1) ^ 2 ≤ (R + 1) ^ 4 := pow_le_pow_right₀ hρ (by norm_num)
  have hn2 : n ≤ n ^ 2 := le_self_pow₀ hn (by norm_num)
  have hn3 : n ≤ n ^ 3 := le_self_pow₀ hn (by norm_num)
  have hn23 : n ^ 2 ≤ n ^ 3 := pow_le_pow_right₀ hn (by norm_num)
  have hNn : 0 ≤ N * n ^ 2 := by positivity
  set X : ℝ := (R + 1) ^ 4 * (N * n ^ 2 + n ^ 3) with hX
  have hX0 : 0 ≤ X := by positivity
  have hY : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a ≤ (R + 1) ^ 4 → b ≤ n ^ 3 → a * b ≤ X := by
    intro a b ha hb h1 h2
    calc a * b ≤ (R + 1) ^ 4 * n ^ 3 := mul_le_mul h1 h2 hb (by positivity)
      _ ≤ X := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hXa : (R + 1) * n ^ 2 ≤ X := hY _ _ hρ0 (by positivity) hρ4 hn23
  have hXa' : (R + 1) ^ 2 * n ≤ X := hY _ _ (by positivity) hn0 hρ24 hn3
  have hXc : R * n ≤ X := hY _ _ hR hn0 hR4 hn3
  have hXb : (2 * N + 2) * ((R + 1) * n) ≤ 2 * X := by
    have h1' : N * n ≤ N * n ^ 2 := mul_le_mul_of_nonneg_left hn2 hN
    have h2' : (R + 1) * (N * n + n) ≤ (R + 1) ^ 4 * (N * n ^ 2 + n ^ 3) :=
      mul_le_mul hρ4 (by linarith) (by positivity) (by positivity)
    have e : (2 * N + 2) * ((R + 1) * n) = 2 * ((R + 1) * (N * n + n)) := by ring
    rw [e, hX]; linarith
  have hdm0 : 0 ≤ C2 * (R + 1) * n := by positivity
  have e2 : (2 * N + 2) * (C2 * (R + 1) * n) ≤ 2 * C2 * X := by
    have := mul_le_mul_of_nonneg_left hXb hC2
    have e : (2 * N + 2) * (C2 * (R + 1) * n) = C2 * ((2 * N + 2) * ((R + 1) * n)) := by ring
    rw [e]; linarith
  have e3 : C3 * (R + 1) * n ^ 2 ≤ |C3| * X :=
    calc C3 * (R + 1) * n ^ 2 = C3 * ((R + 1) * n ^ 2) := by ring
      _ ≤ |C3| * ((R + 1) * n ^ 2) := mul_le_mul_of_nonneg_right (le_abs_self C3) (by positivity)
      _ ≤ |C3| * X := mul_le_mul_of_nonneg_left hXa (abs_nonneg C3)
  have e3' : C5 * (R + 1) ^ 2 * n ≤ |C5| * X :=
    calc C5 * (R + 1) ^ 2 * n = C5 * ((R + 1) ^ 2 * n) := by ring
      _ ≤ |C5| * ((R + 1) ^ 2 * n) := mul_le_mul_of_nonneg_right (le_abs_self C5) (by positivity)
      _ ≤ |C5| * X := mul_le_mul_of_nonneg_left hXa' (abs_nonneg C5)
  have e4 : 0 ≤ |C5| * X := mul_nonneg (abs_nonneg _) hX0
  have e4' : 0 ≤ |C3| * X := mul_nonneg (abs_nonneg _) hX0
  have e6 : 0 ≤ 6 * C2 * X := by positivity
  constructor
  · intro i o hi ho
    have e1 : (i + 1) * (C2 * (R + 1) * n) ≤ (2 * N + 2) * (C2 * (R + 1) * n) := mul_le_mul_of_nonneg_right hi hdm0
    have e5 : 6 * R * o ≤ 6 * C2 * X := by
      have h1 : R * o ≤ R * (C2 * n) := mul_le_mul_of_nonneg_left ho hR
      have h3 : C2 * (R * n) ≤ C2 * X := mul_le_mul_of_nonneg_left hXc hC2
      linarith
    have e : C3 * (R + 1) * n ^ 2 + 6 * R * o + C2 * (R + 1) * n + i * (C2 * (R + 1) * n) =
        C3 * (R + 1) * n ^ 2 + 6 * R * o + (i + 1) * (C2 * (R + 1) * n) := by ring
    linarith
  · intro i hi
    have e1 : i * (C2 * (R + 1) * n) ≤ (2 * N + 2) * (C2 * (R + 1) * n) := mul_le_mul_of_nonneg_right hi hdm0
    linarith

end

end Formalism.FourierDecayAlt.P.CutMP
end

section

open MeasureTheory Filter Topology Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.ParameterFamilyAlgebra

section Fam

variable {k ρ : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {Par : Type} [NormedAddCommGroup Par]
  [NormedSpace ℝ Par] {U₀ : Set (Par × Mt k ρ)}

theorem parFam_add {f g : Par × Mt k ρ → E} (hf : PBI.ParFam k ρ U₀ f) (hg : PBI.ParFam k ρ U₀ g) :
    PBI.ParFam k ρ U₀ (fun q => f q + g q) := by
  intro q₀ hq hG
  obtain ⟨U, F, hU, hqU, hF, hfF⟩ := hf q₀ hq hG
  obtain ⟨U', F', hU', hqU', hF', hgF⟩ := hg q₀ hq hG
  exact ⟨U ∩ U', fun q => F q + F' q, hU.inter hU', ⟨hqU, hqU'⟩,
    (hF.mono Set.inter_subset_left).add (hF'.mono Set.inter_subset_right),
    fun q hq hG => by show f q + g q = F q + F' q; rw [hfF q hq.1 hG, hgF q hq.2 hG]⟩

theorem parFam_smul (a : ℂ) {f : Par × Mt k ρ → E} (hf : PBI.ParFam k ρ U₀ f) :
    PBI.ParFam k ρ U₀ (fun q => a • f q) := by
  intro q₀ hq hG
  obtain ⟨U, F, hU, hqU, hF, hfF⟩ := hf q₀ hq hG
  exact ⟨U, fun q => a • F q, hU, hqU, hF.const_smul a, fun q hq hG => by show a • f q = a • F q; rw [hfF q hq hG]⟩

theorem parFam_zero : PBI.ParFam k ρ U₀ (fun _ => (0 : E)) := fun q₀ _ _ =>
  ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun _ _ _ => rfl⟩

theorem parFam_sum {ι : Type} (s : Finset ι) {f : ι → Par × Mt k ρ → E}
    (hf : ∀ i ∈ s, PBI.ParFam k ρ U₀ (f i)) : PBI.ParFam k ρ U₀ (fun q => ∑ i ∈ s, f i q) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (parFam_zero (E := E) (U₀ := U₀))
  | insert a s ha ih =>
    have h1 := hf a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have := parFam_add h1 h2
    simpa [Finset.sum_insert ha] using this

theorem parFam_contAt {f : Par × Mt k ρ → E} (hf : PBI.ParFam k ρ U₀ f) {Z : Par} {y : Mt k ρ} (hq : (Z, y) ∈ U₀)
    (hy : Matrix.of y ∈ Q.Glev k ρ (Fin.last ρ)) : ContinuousAt (fun Z' => f (Z', y)) Z := by
  obtain ⟨U, F, hU, hqU, hF, hfF⟩ := hf (Z, y) hq hy
  have hci : Continuous fun Z' : Par => ((Z', y) : Par × Mt k ρ) := continuous_id.prodMk continuous_const
  have hm : {Z' | (Z', y) ∈ U} ∈ 𝓝 Z := hci.continuousAt.preimage_mem_nhds (hU.mem_nhds hqU)
  have hcF : ContinuousAt (fun Z' => F (Z', y)) Z :=
    ContinuousAt.comp (g := F) (f := fun Z' : Par => ((Z', y) : Par × Mt k ρ)) (x := Z)
      (hF.continuousOn.continuousAt (hU.mem_nhds hqU)) hci.continuousAt
  refine hcF.congr ?_
  filter_upwards [hm] with Z' hZ'
  exact (hfF (Z', y) hZ' hy).symm

theorem parFam_integrable [MeasurableSpace Par] [BorelSpace Par] {f : Par × Mt k ρ → E}
    (hf : PBI.ParFam k ρ U₀ f) {ν : Measure Par} [IsFiniteMeasure ν] {Kp : Set Par} (hK : IsCompact Kp)
    (hν : ν Kpᶜ = 0) {y : Mt k ρ} (hy : Matrix.of y ∈ Q.Glev k ρ (Fin.last ρ)) (hKU : ∀ Z ∈ Kp, (Z, y) ∈ U₀) :
    Integrable (fun Z => f (Z, y)) ν := by
  have hc : ContinuousOn (fun Z => f (Z, y)) Kp := fun Z hZ =>
    (parFam_contAt hf (hKU Z hZ) hy).continuousWithinAt
  have hI : IntegrableOn (fun Z => f (Z, y)) Kp ν := hc.integrableOn_compact hK
  have hae : ∀ᵐ Z ∂ν, Z ∈ Kp := by
    rw [ae_iff]
    simpa [Set.compl_def] using hν
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hae] at hI

end Fam

section Cls

variable {k ρ : ℕ} {z z' : Fin (2 * ρ + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] {π : Q.Mx k ρ → (Wp →L[ℂ] Wp)}
  {π' : Q.Mx k ρ → (Wq →L[ℂ] Wq)}

def Rep {Par : Type} (Ψ : Par → Q.RadSp k ρ z z' π π') (Ψf : Par → Mt k ρ → (Wq →L[ℂ] Wp)) : Prop :=
  ∀ Z c y, Matrix.of y ∈ Q.Glev k ρ (Fin.last ρ) → (Ψ Z : Q.Fn k ρ (Wq →L[ℂ] Wp)) c (Matrix.of y) = Ψf Z y

def GGpos (k ρ : ℕ) (z z' : Fin (2 * ρ + k + 1) → ℂ) : Set (Mt k ρ) := {y | 0 < Q.GGl k ρ z z' (Matrix.of y)}


variable (z z' π π') in
def Good (A : Module.End ℂ (Q.RadSp k ρ z z' π π')) : Prop :=
  ∀ (Par : Type) [NormedAddCommGroup Par] [NormedSpace ℝ Par] [FiniteDimensional ℝ Par] [MeasurableSpace Par]
    [BorelSpace Par] (U₀ : Set (Par × Mt k ρ)), IsOpen U₀ → U₀ ⊆ Set.univ ×ˢ GGpos k ρ z z' →
  ∀ (Ψ : Par → Q.RadSp k ρ z z' π π') (Ψf : Par → Mt k ρ → (Wq →L[ℂ] Wp)), Rep Ψ Ψf →
    PBI.ParFam k ρ U₀ (fun q => Ψf q.1 q.2) →
  ∃ Φf : Par → Mt k ρ → (Wq →L[ℂ] Wp), Rep (fun Z => A (Ψ Z)) Φf ∧ PBI.ParFam k ρ U₀ (fun q => Φf q.1 q.2) ∧
    (∀ K : Set (Par × Mt k ρ), (∀ q, Matrix.of q.2 ∈ Q.Glev k ρ (Fin.last ρ) → q ∉ K → Ψf q.1 q.2 = 0) →
      ∀ q ∈ U₀, Matrix.of q.2 ∈ Q.Glev k ρ (Fin.last ρ) → q ∉ closure K → Φf q.1 q.2 = 0) ∧
    ∀ (ν : Measure Par) [IsFiniteMeasure ν] (Kp : Set Par), IsCompact Kp → ν Kpᶜ = 0 →
    ∀ (Ψi : Q.RadSp k ρ z z' π π') (y : Mt k ρ) (V : Set (Mt k ρ)), IsOpen V → y ∈ V →
      Matrix.of y ∈ Q.Glev k ρ (Fin.last ρ) → Kp ×ˢ V ⊆ U₀ →
      (∀ c y', y' ∈ V → Matrix.of y' ∈ Q.Glev k ρ (Fin.last ρ) →
        (Ψi : Q.Fn k ρ (Wq →L[ℂ] Wp)) c (Matrix.of y') = ∫ Z, Ψf Z y' ∂ν) →
      ∀ c, (A Ψi : Q.Fn k ρ (Wq →L[ℂ] Wp)) c (Matrix.of y) = ∫ Z, Φf Z y ∂ν

theorem good_id : Good z z' π π' (LinearMap.id : Module.End ℂ (Q.RadSp k ρ z z' π π')) := by
  intro Par _ _ _ _ _ U₀ _ _ Ψ Ψf hR hF
  refine ⟨Ψf, fun Z c y hy => hR Z c y hy, hF, fun K hK q _ hG hq => hK q hG (fun h => hq (subset_closure h)),
    fun ν _ Kp _ _ Ψi y V _ hyV hyG _ hi c => hi c y hyV hyG⟩

theorem good_comp {A B : Module.End ℂ (Q.RadSp k ρ z z' π π')} (hA : Good z z' π π' A) (hB : Good z z' π π' B) :
    Good z z' π π' (A * B) := by
  intro Par _ _ _ _ _ U₀ hU₀ hUpos Ψ Ψf hR hF
  obtain ⟨Φ₁, hR₁, hF₁, hS₁, hW₁⟩ := hB Par U₀ hU₀ hUpos Ψ Ψf hR hF
  obtain ⟨Φ₂, hR₂, hF₂, hS₂, hW₂⟩ := hA Par U₀ hU₀ hUpos (fun Z => B (Ψ Z)) Φ₁ hR₁ hF₁
  refine ⟨Φ₂, fun Z c y hy => hR₂ Z c y hy, hF₂, fun K hK q hq hG hqK => ?_, ?_⟩
  · have hK' : ∀ q', Matrix.of q'.2 ∈ Q.Glev k ρ (Fin.last ρ) → q' ∉ closure K ∪ U₀ᶜ → Φ₁ q'.1 q'.2 = 0 := by
      intro q' hG' hq'
      simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not] at hq'
      exact hS₁ K hK q' hq'.2 hG' hq'.1
    refine hS₂ _ hK' q hq hG ?_
    rw [closure_union, hU₀.isClosed_compl.closure_eq, closure_closure]
    simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not]
    exact ⟨hqK, hq⟩
  · intro ν _ Kp hKp hν Ψi y V hV hyV hyG hKV hi c
    have hi' : ∀ c y', y' ∈ V → Matrix.of y' ∈ Q.Glev k ρ (Fin.last ρ) →
        (B Ψi : Q.Fn k ρ (Wq →L[ℂ] Wp)) c (Matrix.of y') = ∫ Z, Φ₁ Z y' ∂ν :=
      fun c y' hy' hG' => hW₁ ν Kp hKp hν Ψi y' V hV hy' hG' hKV hi c
    exact hW₂ ν Kp hKp hν (B Ψi) y V hV hyV hyG hKV hi' c

theorem good_add {A B : Module.End ℂ (Q.RadSp k ρ z z' π π')} (hA : Good z z' π π' A) (hB : Good z z' π π' B) :
    Good z z' π π' (A + B) := by
  intro Par _ _ _ _ _ U₀ hU₀ hUpos Ψ Ψf hR hF
  obtain ⟨Φ₁, hR₁, hF₁, hS₁, hW₁⟩ := hA Par U₀ hU₀ hUpos Ψ Ψf hR hF
  obtain ⟨Φ₂, hR₂, hF₂, hS₂, hW₂⟩ := hB Par U₀ hU₀ hUpos Ψ Ψf hR hF
  refine ⟨fun Z y => Φ₁ Z y + Φ₂ Z y, fun Z c y hy => ?_, parFam_add hF₁ hF₂, fun K hK q hq hG hqK => ?_, ?_⟩
  · simp only [LinearMap.add_apply, Submodule.coe_add, Pi.add_apply]
    rw [hR₁ Z c y hy, hR₂ Z c y hy]
  · simp only [hS₁ K hK q hq hG hqK, hS₂ K hK q hq hG hqK, add_zero]
  · intro ν _ Kp hKp hν Ψi y V hV hyV hyG hKV hi c
    have hKU : ∀ Z ∈ Kp, (Z, y) ∈ U₀ := fun Z hZ => hKV ⟨hZ, hyV⟩
    simp only [LinearMap.add_apply, Submodule.coe_add, Pi.add_apply]
    rw [hW₁ ν Kp hKp hν Ψi y V hV hyV hyG hKV hi c, hW₂ ν Kp hKp hν Ψi y V hV hyV hyG hKV hi c,
      ← integral_add (parFam_integrable hF₁ hKp hν hyG hKU) (parFam_integrable hF₂ hKp hν hyG hKU)]

theorem good_smul (a : ℂ) {A : Module.End ℂ (Q.RadSp k ρ z z' π π')} (hA : Good z z' π π' A) :
    Good z z' π π' (a • A) := by
  intro Par _ _ _ _ _ U₀ hU₀ hUpos Ψ Ψf hR hF
  obtain ⟨Φ₁, hR₁, hF₁, hS₁, hW₁⟩ := hA Par U₀ hU₀ hUpos Ψ Ψf hR hF
  refine ⟨fun Z y => a • Φ₁ Z y, fun Z c y hy => ?_, parFam_smul a hF₁, fun K hK q hq hG hqK => ?_, ?_⟩
  · simp only [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply]
    rw [hR₁ Z c y hy]
  · simp only [hS₁ K hK q hq hG hqK, smul_zero]
  · intro ν _ Kp hKp hν Ψi y V hV hyV hyG hKV hi c
    simp only [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply]
    rw [hW₁ ν Kp hKp hν Ψi y V hV hyV hyG hKV hi c, integral_smul]


variable (z z' π π') in
def PGood (x : Q.Pr (Q.RadSp k ρ z z' π π')) : Prop := Good z z' π π' x.1 ∧ Good z z' π π' x.2.unop


variable (z z' π π') in
def goodAlg : StarSubalgebra ℂ (Q.Pr (Q.RadSp k ρ z z' π π')) where
  carrier := {x | PGood z z' π π' x}
  mul_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    exact ⟨good_comp hx1 hy1, good_comp hy2 hx2⟩
  add_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    exact ⟨good_add hx1 hy1, good_add hx2 hy2⟩
  algebraMap_mem' := by
    intro a
    have e1 : (algebraMap ℂ (Q.Pr (Q.RadSp k ρ z z' π π')) a).1 = a • LinearMap.id := by
      show algebraMap ℂ (Module.End ℂ (Q.RadSp k ρ z z' π π')) a = _
      exact Module.algebraMap_end_eq_smul_id _ _ _ a
    have e2 : (algebraMap ℂ (Q.Pr (Q.RadSp k ρ z z' π π')) a).2.unop = (starRingEnd ℂ a) • LinearMap.id := by
      show algebraMap ℂ (Module.End ℂ (Q.RadSp k ρ z z' π π')) (starRingEnd ℂ a) = _
      exact Module.algebraMap_end_eq_smul_id _ _ _ _
    refine ⟨?_, ?_⟩
    · show Good z z' π π' (algebraMap ℂ (Q.Pr (Q.RadSp k ρ z z' π π')) a).1
      rw [e1]; exact good_smul a good_id
    · show Good z z' π π' (algebraMap ℂ (Q.Pr (Q.RadSp k ρ z z' π π')) a).2.unop
      rw [e2]; exact good_smul _ good_id
  star_mem' := by
    rintro x ⟨hx1, hx2⟩
    exact ⟨hx2, hx1⟩

theorem good_mkP {X Xs : Module.End ℂ (Q.RadSp k ρ z z' π π')} (h1 : Good z z' π π' X) (h2 : Good z z' π π' Xs) :
    Q.mkP X Xs ∈ goodAlg z z' π π' := ⟨h1, h2⟩

end Cls

end Formalism.FourierDecayAlt.P.ParameterFamilyAlgebra
end
end
