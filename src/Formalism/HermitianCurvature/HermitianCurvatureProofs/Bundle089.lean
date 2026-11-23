module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle084
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SeminormCompletion
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ListSumSplittings
public import Formalism.HermitianCurvature.StatementD
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RightTypeAction
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH Formalism.FourierDecayAlt.P.AdmissibleLieWords
open scoped ContDiff Matrix

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section tools

variable {k r : ℕ}

theorem ckOn_of_cd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : Mat k r → E} (hf : ContDiff ℝ ∞ f)
    (m : ℕ∞) (UU : Set (Mat k r)) : CkOn m UU f := by
  intro g₀ _
  exact ⟨Set.univ, f, isOpen_univ, Set.mem_univ _,
    (hf.of_le (WithTop.coe_le_coe.2 le_top)).contDiffOn, fun _ _ _ => rfl⟩

theorem lss_add {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {S : Set (Mat k r)}
    {f₁ f₂ : Mat k r → E} (hl₁ : LSS f₁ S) (hl₂ : LSS f₂ S) : LSS (fun g => f₁ g + f₂ g) S := by
  intro g hg
  obtain ⟨a, ha, V, hV, hgV, hae⟩ := hl₁ g hg
  obtain ⟨b, hb, W, hW, hgW, hbe⟩ := hl₂ g hg
  refine ⟨fun g => a g + b g, ha.add hb, V ∩ W, hV.inter hW, ⟨hgV, hgW⟩, fun g' hg' hm => ?_⟩
  show f₁ g' + f₂ g' = a g' + b g'
  rw [hae g' hg' hm.1, hbe g' hg' hm.2]

theorem ubl_add {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {S : Set (Mat k r)} (hSG : S ⊆ GV k r)
    {f₁ f₂ : Mat k r → E} {n e γ : ℕ} (h₁ : UBL f₁ S n e γ) (h₂ : UBL f₂ S n e γ) :
    UBL (fun g => f₁ g + f₂ g) S n e γ := by
  obtain ⟨⟨C₁, hC₁, hb₁⟩, hl₁⟩ := h₁
  obtain ⟨⟨C₂, hC₂, hb₂⟩, hl₂⟩ := h₂
  refine ⟨⟨C₁ + C₂, add_nonneg hC₁ hC₂, fun w hw g hg => ?_⟩, lss_add hl₁ hl₂⟩
  obtain ⟨a, ha, V, hV, hgV, haa⟩ := hl₁ g hg
  obtain ⟨b, hb, W, hW, hgW, hbb⟩ := hl₂ g hg
  have hlie := admissible_word_mem_lie hw
  have hG := hSG hg
  have e0 : Dw w (fun g => f₁ g + f₂ g) g = Dw w (fun g => a g + b g) g :=
    Dw_congr_loc hlie (hV.inter hW) (fun g' hG' hg' => by simp [haa g' hG' hg'.1, hbb g' hG' hg'.2]) g hG
      ⟨hgV, hgW⟩
  rw [e0, Dw_add hlie (ckOn_of_cd ha _ _) (ckOn_of_cd hb _ _) g hG,
    ← Dw_congr_loc hlie hV haa g hG hgV, ← Dw_congr_loc hlie hW hbb g hG hgW]
  refine (norm_add_le _ _).trans ?_
  rw [add_mul]
  exact add_le_add (hb₁ w hw g hg) (hb₂ w hw g hg)

theorem ubl_sum {ι E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {S : Set (Mat k r)} (hSG : S ⊆ GV k r)
    (s : Finset ι) {f : ι → Mat k r → E} {n e γ : ℕ} (h : ∀ i ∈ s, UBL (f i) S n e γ) :
    UBL (fun g => ∑ i ∈ s, f i g) S n e γ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ubl_mono hSG (ubl_const (0 : E) hSG n γ) (Nat.zero_le e) le_rfl
  | @insert a s has ih =>
    simp only [Finset.sum_insert has]
    exact ubl_add hSG (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem lss_pi {ι E : Type} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℂ E] {S : Set (Mat k r)}
    {f : Mat k r → ι → E} (h : ∀ i, LSS (fun g => f g i) S) : LSS f S := by
  intro g hg
  choose F hF V hV hgV hFe using fun i => h i g hg
  refine ⟨fun g i => F i g, contDiff_pi.2 hF, ⋂ i, V i, isOpen_iInter_of_finite hV,
    Set.mem_iInter.2 hgV, fun g' hg' hm => funext fun i => hFe i g' hg' (Set.mem_iInter.1 hm i)⟩

theorem ubl_pi {ι E : Type} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℂ E] {S : Set (Mat k r)}
    (hSG : S ⊆ GV k r) {f : Mat k r → ι → E} {n e γ : ℕ} (h : ∀ i, UBL (fun g => f g i) S n e γ) :
    UBL f S n e γ := by
  have h1 := fun i => (h i).1
  have hL := fun i => (h i).2
  choose C hC hB using h1
  have hCs : 0 ≤ ∑ i, C i := Finset.sum_nonneg fun i _ => hC i
  refine ⟨⟨∑ i, C i, hCs, fun w hw g hg => ?_⟩, lss_pi hL⟩
  have hlie := admissible_word_mem_lie hw
  have hgG := hSG hg
  have hgN : 0 ≤ gN g := Real.sqrt_nonneg _
  obtain ⟨F, hF, V, hV, hgV, hFe⟩ := lss_pi hL g hg
  rw [Dw_congr_loc hlie hV hFe g hgG hgV]
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hCs (pow_nonneg hgN _))).2 fun i => ?_
  rw [Formalism.FourierDecayAlt.P.Ux8.Dw_pi hlie (ckOn_of_cd hF _ _) g hgG i]
  have e1 := Dw_congr_loc hlie hV (f := fun g => f g i) (f₂ := fun g => F g i)
    (fun g' hg' hm => congrFun (hFe g' hg' hm) i) g hgG hgV
  rw [← e1]
  calc ‖Dw w (fun g => f g i) g‖ ≤ C i * gN g ^ (e + γ * w.length) := hB i w hw g hg
    _ ≤ (∑ j, C j) * gN g ^ (e + γ * w.length) :=
        mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i))
          (pow_nonneg hgN _)

theorem ubl_star {S : Set (Mat k r)} (hSG : S ⊆ GV k r) {f : Mat k r → ℂ} {n e γ : ℕ} (h : UBL f S n e γ) :
    UBL (fun g => star (f g)) S n e γ := by
  have hfun : (fun g => star (f g)) =
      fun g => (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap (f g) := by
    funext g; rfl
  rw [hfun]
  exact ubl_clm _ hSG h

theorem ubl_mmul {m : ℕ} {S : Set (Mat k r)} (hSG : S ⊆ GV k r)
    {A B : Mat k r → Matrix (Fin m) (Fin m) ℂ} {n ea eb γ : ℕ}
    (hA : ∀ i j, UBL (fun g => A g i j) S n ea γ) (hB : ∀ i j, UBL (fun g => B g i j) S n eb γ) (i j : Fin m) :
    UBL (fun g => (A g * B g) i j) S n (ea + eb) γ := by
  have hfun : (fun g => (A g * B g) i j) = fun g => ∑ l ∈ Finset.univ, A g i l * B g l j := by
    funext g; simp [Matrix.mul_apply]
  rw [hfun]
  exact ubl_sum hSG _ fun l _ => ubl_mul hSG (hA i l) (hB l j)

end tools

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom
end

section

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

def ThChain (Ψ : ℕ → ℝ → ℝ) : Prop := ∀ (n : ℕ) (x : ℝ), 0 < x → HasDerivAt (Ψ n) (Ψ (n + 1) x / x) x

section leibterm

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def LeibTerm (Bs : B.RealPlaceData k r Wp Wq) (Dop : B.DiffOp k r Wp Wq) (T' : B.DTerm k r Wp Wq) : Prop :=
  ∃ T ∈ Dop, ∃ (P : B.Mat k r → ℂ) (j : ℕ), ListSumSplittings.PolyClass ((2 * r + 2) * T.word.length) P ∧
    T'.word.Sublist T.word ∧
    ∀ g ∈ C6.domL Bs ∅, T'.coef g = (P g * ((Gf k r Bs.z Bs.z' g : ℝ) : ℂ)⁻¹ ^ j) • T.coef g

end leibterm

def NFLeibExp : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (w : List (B.Mat k r)), (∀ X ∈ w, B.inLie k r X) →
    ∃ terms : List (ℕ × (B.Mat k r → ℂ) × ℕ × List (B.Mat k r)),
      (∀ t ∈ terms, t.1 ≤ w.length ∧ ListSumSplittings.PolyClass ((2 * r + 2) * w.length) t.2.1 ∧ t.2.2.2.Sublist w) ∧
      ∀ Ψ : ℕ → ℝ → ℝ, ThChain Ψ → ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) F →
        ∀ x ∈ C6.domL Bs ∅,
          B.Rw w (fun y => ((Ψ 0 (Gf k r Bs.z Bs.z' y) : ℝ) : ℂ) • F y) x =
            (terms.map fun t => ((((Ψ t.1 (Gf k r Bs.z Bs.z' x) : ℝ) : ℂ) * t.2.1 x *
              ((Gf k r Bs.z Bs.z' x : ℝ) : ℂ)⁻¹ ^ t.2.2.1) • B.Rw t.2.2.2 F x)).sum

def NFLeibOps : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (Dop : B.DiffOp k r Wp Wq),
    B.SmoothCoef (C6.domL Bs ∅) Dop →
    ∃ (Q : ℕ) (L : Fin (Q + 1) → B.DiffOp k r Wp Wq),
      (∀ q, B.SmoothCoef (C6.domL Bs ∅) (L q)) ∧ (∀ q, ∀ T' ∈ L q, LeibTerm Bs Dop T') ∧
      ∀ Ψ : ℕ → ℝ → ℝ, ThChain Ψ → ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) F →
        ∀ x ∈ C6.domL Bs ∅,
          B.opApply Dop (fun y => ((Ψ 0 (Gf k r Bs.z Bs.z' y) : ℝ) : ℂ) • F y) x =
            ∑ q : Fin (Q + 1), ((Ψ q (Gf k r Bs.z Bs.z' x) : ℝ) : ℂ) • B.opApply (L q) F x

def NFLeibBd : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (nf : ℕ)
    (fib : Fin nf → B.Mat k r → C6.EndH Wp Wq) (o κ : ℕ) (Dop : B.DiffOp k r Wp Wq),
    (∀ j, C6.FibBound Bs (fib j)) → C6.InDDPlus Bs fib ∅ o κ Dop →
    ∀ L : B.DiffOp k r Wp Wq, (∀ T' ∈ L, LeibTerm Bs Dop T') →
    ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : B.Mat k r → (Wq →L[ℂ] Wp)) (A b : ℝ), B.CCle A o F b →
      ∀ g ∈ B.GV k r, ε ≤ Gf k r Bs.z Bs.z' g →
        ‖B.opApply L F g‖ ≤ K * b * B.gN g ^ ((κ : ℝ) + 3 * ((r : ℝ) + 1) * o + (2 * (r : ℝ) + 2) * o - A)

def NFVLin : Prop :=
  ∃ c₃ : ℝ, ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r) (Q : ℕ) (c : Fin (Q + 1) → ℝ → ℂ)
    (H : B.Mat k r → (Wq →L[ℂ] Wp)) (Hq : Fin (Q + 1) → B.Mat k r → (Wq →L[ℂ] Wp)) (A : ℝ),
    c₃ * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1) ≤ A →
    (∀ q, ContinuousOn (Hq q) (B.GPos Bs)) →
    (∀ q, ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ g ∈ B.GV k r, ε ≤ Gf k r Bs.z Bs.z' g → ‖Hq q g‖ ≤ C * B.gN g ^ (-A)) →
    (∀ g ∈ B.GPos Bs, H g = ∑ q, c q (Gf k r Bs.z Bs.z' g) • Hq q g) →
    ∀ γ : C.LPt, D.IsLocPt γ (r + 1) → 0 < D.ptG (Tz k r Bs.z * Tz k r Bs.z') r γ →
      D.vecV Bs ν' m₀ H γ = ∑ q, c q (D.ptG (Tz k r Bs.z * Tz k r Bs.z') r γ) • D.vecV Bs ν' m₀ (Hq q) γ

end

end Formalism.FourierDecayAlt.P.CutBP
end

section

open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.NFRadRedL

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.QrD

variable {k r : ℕ}

def cinv (g : Q.Mx k r) : Q.Mx k r := (g + 1)⁻¹ * (g - 1)

theorem cinv_one : cinv (1 : Q.Mx k r) = 0 := by
  simp [cinv]

theorem add_one_mul_cinv {g : Q.Mx k r} (hg : IsUnit (g + 1).det) : (g + 1) * cinv g = g - 1 := by
  rw [cinv, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hg, Matrix.one_mul]

theorem cinv_mul_add_one {g : Q.Mx k r} (hg : IsUnit (g + 1).det) : cinv g * (g + 1) = g - 1 := by
  rw [cinv, Matrix.mul_assoc, show (g - 1) * (g + 1) = (g + 1) * (g - 1) by noncomm_ring,
    ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hg, Matrix.one_mul]

theorem cinv_inj {g₁ g₂ : Q.Mx k r} (h₁ : IsUnit (g₁ + 1).det) (h₂ : IsUnit (g₂ + 1).det)
    (he : cinv g₁ = cinv g₂) : g₁ = g₂ := by
  have k1 : g₁ * (1 - cinv g₁) = 1 + cinv g₁ := by
    have h := add_one_mul_cinv h₁
    rw [add_mul, Matrix.one_mul] at h
    rw [mul_sub, mul_one, eq_sub_of_add_eq h]; abel
  have k2 : g₂ * (1 - cinv g₁) = 1 + cinv g₁ := by
    have h := add_one_mul_cinv h₂
    rw [add_mul, Matrix.one_mul] at h
    rw [he, mul_sub, mul_one, eq_sub_of_add_eq h]; abel
  have hL : ((1 / 2 : ℂ) • (g₁ + 1)) * (1 - cinv g₁) = 1 := by
    rw [Matrix.smul_mul, mul_sub, mul_one, add_one_mul_cinv h₁,
      show g₁ + 1 - (g₁ - 1) = (2 : ℂ) • (1 : Q.Mx k r) by rw [two_smul]; abel, smul_smul]
    norm_num
  have hR : (1 - cinv g₁) * ((1 / 2 : ℂ) • (g₁ + 1)) = 1 := mul_eq_one_comm.mp hL
  calc g₁ = g₁ * ((1 - cinv g₁) * ((1 / 2 : ℂ) • (g₁ + 1))) := by rw [hR, mul_one]
    _ = g₂ * ((1 - cinv g₁) * ((1 / 2 : ℂ) • (g₁ + 1))) := by rw [← mul_assoc, k1, ← k2, mul_assoc]
    _ = g₂ := by rw [hR, mul_one]

theorem cinv_lie {z : Fin (2 * r + k + 1) → ℂ} {g : Q.Mx k r} (hg : g ∈ UWset k r z) (hu : IsUnit (g + 1).det) :
    InLieW k r z (cinv g) := by
  obtain ⟨hU, hfix, hz⟩ := hg
  have fixv : ∀ v, g *ᵥ v = v → cinv g *ᵥ v = 0 := by
    intro v hv
    simp only [cinv]
    rw [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, hv, sub_self, Matrix.mulVec_zero]
  refine ⟨⟨?_, fun a _ => ⟨fixv _ (hfix a).1, fixv _ (hfix a).2⟩⟩, fixv _ hz⟩
  have hU' : gᴴ * Hpk k r * g = Hpk k r := hU
  have hAH : IsUnit (g + 1)ᴴ.det := by rw [Matrix.det_conjTranspose]; exact hu.star
  have e1 : (g + 1) * (g + 1)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have e2 : ((g + 1)ᴴ)⁻¹ * (g + 1)ᴴ = 1 := Matrix.nonsing_inv_mul _ hAH
  have hc : cinv g = (g - 1) * (g + 1)⁻¹ := by
    calc cinv g = cinv g * ((g + 1) * (g + 1)⁻¹) := by rw [e1, mul_one]
      _ = (g - 1) * (g + 1)⁻¹ := by rw [← mul_assoc, cinv_mul_add_one hu]
  have mid : (g - 1)ᴴ * Hpk k r * (g + 1) + (g + 1)ᴴ * Hpk k r * (g - 1) = 0 := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_add, Matrix.conjTranspose_one]
    have : (gᴴ - 1) * Hpk k r * (g + 1) + (gᴴ + 1) * Hpk k r * (g - 1) =
        (gᴴ * Hpk k r * g - Hpk k r) + (gᴴ * Hpk k r * g - Hpk k r) := by noncomm_ring
    rw [this, hU', sub_self, add_zero]
  have t1 : ((g + 1)ᴴ)⁻¹ * ((g - 1)ᴴ * Hpk k r * (g + 1)) * (g + 1)⁻¹ = ((g + 1)ᴴ)⁻¹ * (g - 1)ᴴ * Hpk k r := by
    simp only [Matrix.mul_assoc]; rw [e1, Matrix.mul_one]
  have t2 : ((g + 1)ᴴ)⁻¹ * ((g + 1)ᴴ * Hpk k r * (g - 1)) * (g + 1)⁻¹ = Hpk k r * ((g - 1) * (g + 1)⁻¹) := by
    simp only [← Matrix.mul_assoc]; rw [e2, Matrix.one_mul]
  rw [hc, Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, ← t1, ← t2, ← add_mul, ← mul_add, mid,
    Matrix.mul_zero, Matrix.zero_mul]

end Formalism.FourierDecayAlt.P.NFRadRedL
end
end

section

open Matrix Finset Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace QrD

section Left

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq]
  [NormedSpace ℂ Wq] [FiniteDimensional ℂ Wp] {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
  {π' : Mx k r → (Wq →L[ℂ] Wq)} {D : Set (Mx k r)} {J : Mx k r → (Wq →L[ℂ] Wp)}

theorem mem_left (hD : IsDom k r z z' (Fin.last r) D) {g h : Mx k r} (hg : g ∈ Glev k r (Fin.last r) ∩ D)
    (hh : h ∈ UWset k r z) : h * g ∈ Glev k r (Fin.last r) ∩ D := by
  obtain ⟨hgG, hgD⟩ := hg
  refine ⟨?_, ?_⟩
  · simp only [Glev, UH, UWset, Set.mem_setOf_eq] at hgG hh ⊢
    refine ⟨?_, fun a ha => ?_⟩
    · rw [conjTranspose_mul]
      calc gᴴ * hᴴ * Hpk k r * (h * g) = gᴴ * (hᴴ * Hpk k r * h) * g := by simp only [Matrix.mul_assoc]
        _ = Hpk k r := by rw [hh.1, hgG.1]
    · rw [← mulVec_mulVec, ← mulVec_mulVec, (hgG.2 a ha).1, (hgG.2 a ha).2]
      exact hh.2.1 a
  · have h1z' : (1 : Mx k r) ∈ UWset k r z' := by simp [UWset, UH]
    have h1N : (1 : Mx k r) ∈ Nlev k r (Fin.last r) := by simp [Nlev, QuantumDeterminants.Nset, Glev, UH, Matrix.one_apply]
    have hS := hD.2 g ⟨hgG, hgD⟩ h ⟨h, hh, 1, h1N, by simp⟩ 1 ⟨1, h1z', 1, h1N, by simp⟩
    simpa using hS

theorem J_left (hπ : IsCRepOn (UWset k r z) π) (hJ : J ∈ FFl k r z z' π π' (Fin.last r) D) {g h : Mx k r}
    (hg : g ∈ Glev k r (Fin.last r) ∩ D) (hh : h ∈ UWset k r z) : J (h * g) = (π h).comp (J g) := by
  have h1z : (1 : Mx k r) ∈ UWset k r z := by simp [UWset, UH]
  have h1z' : (1 : Mx k r) ∈ UWset k r z' := by simp [UWset, UH]
  simp only [FFl, Set.mem_setOf_eq] at hJ
  have e1 := hJ.2.2.2 g hg 1 h1z 1 h1z'
  have e2 := hJ.2.2.2 g hg h hh 1 h1z'
  rw [one_mul, mul_one, hπ.1] at e1
  have e1' : J g ∘SL π' 1 = J g := by
    ext x
    exact (congrArg (fun T => T x) e1).symm
  rw [mul_one] at e2
  rw [e2, e1']

theorem ld_left (hD : IsDom k r z z' (Fin.last r) D) (hπ : IsCRepOn (UWset k r z) π)
    (hc : ContinuousOn π (UWset k r z)) (hJ : J ∈ FFl k r z z' π π' (Fin.last r) D)
    {F : Mx k r → (Wq →L[ℂ] Wp)} {B : Wp →L[ℂ] Wp}
    (hF : ∀ g ∈ Glev k r (Fin.last r) ∩ D, F g = B.comp (J g)) {X : Mx k r} (hX : InLieW k r z X)
    {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r) ∩ D) : LdV X F g = (B.comp (dOp π X)).comp (J g) := by
  have hfun : (fun t : ℝ => F (NormedSpace.exp ((t : ℂ) • X) * g)) =
      fun t : ℝ => (B.comp (π (NormedSpace.exp ((t : ℂ) • X)))).comp (J g) := by
    funext t
    have hu := exp_uw hX t
    rw [hF _ (mem_left hD hg hu), J_left hπ hJ hg hu, ContinuousLinearMap.comp_assoc]
  unfold LdV
  rw [hfun]
  have hd := dOp_hasDeriv hπ hc hX
  let L : (Wp →L[ℂ] Wp) →L[ℝ] (Wq →L[ℂ] Wp) :=
    (((ContinuousLinearMap.compL ℂ Wq Wp Wp).flip (J g)).comp
      ((ContinuousLinearMap.compL ℂ Wp Wp Wp) B)).restrictScalars ℝ
  have key : HasDerivAt (fun t : ℝ => (B.comp (π (NormedSpace.exp ((t : ℂ) • X)))).comp (J g))
      ((B.comp (dOp π X)).comp (J g)) 0 := by
    have h2 := L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
    convert h2 using 1
    all_goals first | rfl | (ext; rfl)
  exact key.deriv

theorem lz_left (hD : IsDom k r z z' (Fin.last r) D) (hπ : IsCRepOn (UWset k r z) π)
    (hc : ContinuousOn π (UWset k r z)) (hJ : J ∈ FFl k r z z' π π' (Fin.last r) D)
    {F : Mx k r → (Wq →L[ℂ] Wp)} {B : Wp →L[ℂ] Wp}
    (hF : ∀ g ∈ Glev k r (Fin.last r) ∩ D, F g = B.comp (J g)) {Z : Mx k r}
    (h1 : InLieW k r z (hpart1 (Hpk k r) Z)) (h2 : InLieW k r z (hpart2 (Hpk k r) Z))
    {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r) ∩ D) :
    LZ (Hpk k r) Z F g = (B.comp (ecOp π Z)).comp (J g) := by
  unfold LZ
  rw [ld_left hD hπ hc hJ hF h1 hg, ld_left hD hπ hc hJ hF h2 hg]
  ext v
  simp [ecOp]

theorem fold_left (hD : IsDom k r z z' (Fin.last r) D) (hπ : IsCRepOn (UWset k r z) π)
    (hc : ContinuousOn π (UWset k r z)) (hJ : J ∈ FFl k r z z' π π' (Fin.last r) D)
    (L : List (ℂ × Mx k r))
    (hL : ∀ p ∈ L, InLieW k r z (hpart1 (Hpk k r) p.2) ∧ InLieW k r z (hpart2 (Hpk k r) p.2)) :
    ∀ (F : Mx k r → (Wq →L[ℂ] Wp)) (B : Wp →L[ℂ] Wp), (∀ g ∈ Glev k r (Fin.last r) ∩ D, F g = B.comp (J g)) →
      ∀ g ∈ Glev k r (Fin.last r) ∩ D, ∀ v,
        (L.map fun p => fun y : Mx k r → (Wq →L[ℂ] Wp) => p.1 • y + LZ (Hpk k r) p.2 y).foldl (fun h T => T h) F g v =
          B ((L.map fun p => fun y : Wp => p.1 • y + EcRep (Hpk k r) π p.2 y).foldr (fun T h => T h) (J g v)) := by
  induction L with
  | nil => intro F B hF g hg v; simp [hF g hg]
  | cons p L ih =>
    intro F B hF g hg v
    obtain ⟨h1, h2⟩ := hL p (by simp)
    have hF' : ∀ g ∈ Glev k r (Fin.last r) ∩ D,
        (p.1 • F + LZ (Hpk k r) p.2 F) g = (p.1 • B + B.comp (ecOp π p.2)).comp (J g) := by
      intro g hg
      rw [Pi.add_apply, Pi.smul_apply, lz_left hD hπ hc hJ hF h1 h2 hg, hF g hg]
      ext x
      simp
    have := ih (fun q hq => hL q (by simp [hq])) _ _ hF' g hg v
    simp only [List.map_cons, List.foldl_cons, List.foldr_cons]
    rw [this]
    simp [ecRep_eq hπ hc h1 h2]

end Left

end QrD

theorem left_type_action : Formalism.FourierDecayAlt.Q.LeftTypeAction := by
  intro Wp Wq _ _ _ _ _ k r m z z' π π' D hz hz' hD hπ hc J hJ g hg Bs hB w v
  unfold capLft capRep qmFrev qmF
  have key : ∀ σ : Equiv.Perm (Fin m), ∀ g ∈ Glev k r (Fin.last r) ∩ D, ∀ v,
      ((List.ofFn fun j => ((if σ j = j then w - ((j : ℕ) : ℂ) else 0), unitB (Hpk k r) Bs (σ j) j)).map
          fun p => fun y : Mx k r → (Wq →L[ℂ] Wp) => p.1 • y + LZ (Hpk k r) p.2 y).foldl (fun h T => T h) J g v =
        (ContinuousLinearMap.id ℂ Wp)
          (((List.ofFn fun j => ((if σ j = j then w - ((j : ℕ) : ℂ) else 0), unitB (Hpk k r) Bs (σ j) j)).map
            fun p => fun y : Wp => p.1 • y + EcRep (Hpk k r) π p.2 y).foldr (fun T h => T h) (J g v)) :=
    fun σ => QrD.fold_left hD hπ hc hJ _ (by
      intro p hp
      simp only [List.mem_ofFn] at hp
      obtain ⟨j, rfl⟩ := hp
      exact QrD.frame_lie hB (σ j) j) J (ContinuousLinearMap.id ℂ Wp) (fun g _ => by simp)
  simp only [List.map_ofFn, Function.comp_def, ite_smul, zero_smul, ContinuousLinearMap.id_apply] at key
  simp only [id, Finset.sum_apply, Pi.smul_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [key σ g hg v]

end Formalism.FourierDecayAlt.P
end
end
