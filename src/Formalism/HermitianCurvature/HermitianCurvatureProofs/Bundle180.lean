module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BlockOfCauchySchwarz
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BlockOfChoices
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle047
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle049
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle083
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle070
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle115
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyContinuousOn
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle080
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle050
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceCompactSupportCoefficient
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle036
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle063
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle173
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle151
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LocalNablaHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle068
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAStarOpModelAdj
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Finset
open scoped ComplexConjugate ComplexOrder InnerProductSpace

noncomputable section

section gram

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {α : Type}

def gramH (h : α → H) : α → α → ℂ := fun P Q => ⟪h Q, h P⟫_ℂ

theorem qf_gramH (Y : Finset α) (h : α → H) (c : α → ℂ) :
    PBA.qf Y (gramH h) c = ⟪∑ P ∈ Y, conj (c P) • h P, ∑ P ∈ Y, conj (c P) • h P⟫_ℂ := by
  unfold PBA.qf gramH
  rw [sum_inner]
  simp only [inner_sum, inner_smul_left, inner_smul_right, Complex.conj_conj]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun P _ => Finset.sum_congr rfl fun Q _ => by ring

theorem psd_gramH (Y : Finset α) (h : α → H) : TB.PSDOn Y (gramH h) := by
  rw [PBA.psd_iff_qf]
  refine ⟨fun P _ Q _ => (inner_conj_symm (𝕜 := ℂ) (h P) (h Q)).symm, fun c => ?_⟩
  rw [qf_gramH]
  exact inner_self_nonneg (𝕜 := ℂ)

def Loe (Y : Finset α) (A B : α → α → ℂ) : Prop := TB.PSDOn Y fun P Q => B P Q - A P Q

theorem loe_iff (Y : Finset α) (A B : α → α → ℂ) :
    Loe Y A B ↔ (∀ x ∈ Y, ∀ y ∈ Y, B y x - A y x = conj (B x y - A x y)) ∧
      ∀ c, (PBA.qf Y A c).re ≤ (PBA.qf Y B c).re := by
  unfold Loe
  rw [PBA.psd_iff_qf]
  have e : ∀ c, PBA.qf Y (fun P Q => B P Q - A P Q) c = PBA.qf Y B c - PBA.qf Y A c := by
    intro c; unfold PBA.qf; simp only [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun P _ => Finset.sum_congr rfl fun Q _ => by ring
  simp only [e, Complex.sub_re, sub_nonneg]

theorem loe_trans {Y : Finset α} {A B C : α → α → ℂ} (h1 : Loe Y A B) (h2 : Loe Y B C) : Loe Y A C := by
  rw [loe_iff] at h1 h2 ⊢
  refine ⟨fun x hx y hy => ?_, fun c => (h1.2 c).trans (h2.2 c)⟩
  have a := h1.1 x hx y hy
  have b := h2.1 x hx y hy
  have : C y x - A y x = (C y x - B y x) + (B y x - A y x) := by ring
  rw [this, a, b, ← map_add (f := _)]; ring_nf

theorem loe_zero_of_psd {Y : Finset α} {B : α → α → ℂ} (h : TB.PSDOn Y B) : Loe Y (fun _ _ => 0) B := by
  unfold Loe; simpa using h

theorem psd_of_loe_zero {Y : Finset α} {B : α → α → ℂ} (h : Loe Y (fun _ _ => 0) B) : TB.PSDOn Y B := by
  unfold Loe at h; simpa using h

theorem qf_mix {N : Type} [Fintype N] (Y : Finset α) (A : N → α → α → ℂ) (θ : N → ℝ) (M : ℝ) (c : α → ℂ) :
    PBA.qf Y (fun p q => (M : ℂ) * ∑ n, (θ n : ℂ) * A n p q) c = (M : ℂ) * ∑ n, (θ n : ℂ) * PBA.qf Y (A n) c := by
  unfold PBA.qf
  have e' : ∀ x y, conj (c x) * ((M : ℂ) * ∑ n, (θ n : ℂ) * A n x y) * c y =
      ∑ n, (M : ℂ) * ((θ n : ℂ) * (conj (c x) * A n x y * c y)) := by
    intro x y
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun n _ => by ring
  simp_rw [e']
  rw [swap3, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]

theorem norm_mix_sq {N : Type} [Fintype N] (lam : N → ℂ) (W : N → H) :
    ‖∑ n, lam n • W n‖ ^ 2 ≤ (∑ n, ‖lam n‖) * ∑ n, ‖lam n‖ * ‖W n‖ ^ 2 := by
  have h1 : ‖∑ n, lam n • W n‖ ≤ ∑ n, ‖lam n‖ * ‖W n‖ :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => (norm_smul _ _).le)
  have h2 : (∑ n, ‖lam n‖ * ‖W n‖) ^ 2 ≤ (∑ n, ‖lam n‖) * ∑ n, ‖lam n‖ * ‖W n‖ ^ 2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun n => Real.sqrt ‖lam n‖)
      (fun n => Real.sqrt ‖lam n‖ * ‖W n‖)
    have e1 : ∀ n, Real.sqrt ‖lam n‖ * (Real.sqrt ‖lam n‖ * ‖W n‖) = ‖lam n‖ * ‖W n‖ := fun n => by
      rw [← mul_assoc, Real.mul_self_sqrt (norm_nonneg _)]
    have e2 : ∀ n, Real.sqrt ‖lam n‖ ^ 2 = ‖lam n‖ := fun n => Real.sq_sqrt (norm_nonneg _)
    have e3 : ∀ n, (Real.sqrt ‖lam n‖ * ‖W n‖) ^ 2 = ‖lam n‖ * ‖W n‖ ^ 2 := fun n => by
      rw [mul_pow, e2]
    simp only [e1, e2, e3] at this
    exact this
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2

theorem loe_convex {N : Type} [Fintype N] (Y : Finset α) (lam : N → ℂ) (h : N → α → H) :
    Loe Y (gramH fun P => ∑ n, lam n • h n P)
      (fun P Q => ((∑ n, ‖lam n‖ : ℝ) : ℂ) * ∑ n, ((‖lam n‖ : ℝ) : ℂ) * gramH (h n) P Q) := by
  rw [loe_iff]
  constructor
  · intro x _ y _

    simp only [gramH, map_sub, map_mul, map_sum, Complex.conj_ofReal, inner_conj_symm]
  · intro c
    have eW : ∑ P ∈ Y, conj (c P) • ∑ n, lam n • h n P = ∑ n, lam n • ∑ P ∈ Y, conj (c P) • h n P := by
      simp only [Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun P _ => by rw [mul_comm]
    rw [qf_gramH, eW, qf_mix]
    simp only [qf_gramH]
    have hre : ∀ x : H, (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := fun x => by
      have := inner_self_eq_norm_sq (𝕜 := ℂ) x; simpa using this
    rw [Complex.re_ofReal_mul, Complex.re_sum, hre]
    simp only [Complex.re_ofReal_mul, hre]
    exact norm_mix_sq lam _

theorem loe_congr {Y : Finset α} {A A' B B' : α → α → ℂ} (hA : ∀ x ∈ Y, ∀ y ∈ Y, A x y = A' x y)
    (hB : ∀ x ∈ Y, ∀ y ∈ Y, B x y = B' x y) (h : Loe Y A B) : Loe Y A' B' :=
  psd_congr (fun x hx y hy => by rw [hA x hx y hy, hB x hx y hy]) h

theorem loe_refl (Y : Finset α) (A : α → α → ℂ) : Loe Y A A := by
  unfold Loe
  refine psd_congr (k := fun _ _ => (0 : ℂ)) (fun x _ y _ => by ring) ?_
  rw [PBA.psd_iff_qf]; exact ⟨fun _ _ _ _ => by simp, fun c => by simp [PBA.qf]⟩

theorem loe_add {Y : Finset α} {A B A' B' : α → α → ℂ} (h : Loe Y A B) (h' : Loe Y A' B') :
    Loe Y (fun x y => A x y + A' x y) (fun x y => B x y + B' x y) := by
  rw [loe_iff] at h h' ⊢
  refine ⟨fun x hx y hy => ?_, fun c => ?_⟩
  · have a := h.1 x hx y hy; have b := h'.1 x hx y hy
    have : B y x + B' y x - (A y x + A' y x) = (B y x - A y x) + (B' y x - A' y x) := by ring
    rw [this, a, b, ← map_add (f := _)]; ring_nf
  · have e : ∀ K K' : α → α → ℂ, PBA.qf Y (fun x y => K x y + K' x y) c = PBA.qf Y K c + PBA.qf Y K' c := by
      intro K K'; unfold PBA.qf; simp only [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
    rw [e, e, Complex.add_re, Complex.add_re]
    linarith [h.2 c, h'.2 c]

theorem loe_smul {Y : Finset α} {A B : α → α → ℂ} (r : ℝ) (hr : 0 ≤ r) (h : Loe Y A B) :
    Loe Y (fun x y => (r : ℂ) * A x y) (fun x y => (r : ℂ) * B x y) := by
  rw [loe_iff] at h ⊢
  refine ⟨fun x hx y hy => ?_, fun c => ?_⟩
  · have a := h.1 x hx y hy
    rw [← mul_sub, ← mul_sub, a, map_mul, Complex.conj_ofReal]
  · have e : ∀ K : α → α → ℂ, PBA.qf Y (fun x y => (r : ℂ) * K x y) c = (r : ℂ) * PBA.qf Y K c := by
      intro K; unfold PBA.qf; simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
    rw [e, e, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
    exact mul_le_mul_of_nonneg_left (h.2 c) hr

theorem loe_sum {ι : Type} (s : Finset ι) {Y : Finset α} {A B : ι → α → α → ℂ} (h : ∀ i ∈ s, Loe Y (A i) (B i)) :
    Loe Y (fun x y => ∑ i ∈ s, A i x y) (fun x y => ∑ i ∈ s, B i x y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using loe_refl Y (fun _ _ => (0 : ℂ))
  | insert b t hb ih =>
    have h1 := loe_add (h b (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    refine loe_congr (fun x _ y _ => ?_) (fun x _ y _ => ?_) h1
    · rw [Finset.sum_insert hb]
    · rw [Finset.sum_insert hb]

theorem loe_diag {Y : Finset α} {A B : α → α → ℂ} (ω : α → ℝ) (h : Loe Y A B) :
    Loe Y (fun x y => (ω x : ℂ) * (ω y : ℂ) * A x y) (fun x y => (ω x : ℂ) * (ω y : ℂ) * B x y) := by
  rw [loe_iff] at h ⊢
  refine ⟨fun x hx y hy => ?_, fun c => ?_⟩
  · have a := h.1 x hx y hy
    have : (ω y : ℂ) * (ω x : ℂ) * B y x - (ω y : ℂ) * (ω x : ℂ) * A y x = (ω y : ℂ) * (ω x : ℂ) * (B y x - A y x) := by
      ring
    rw [this, a]; simp only [map_mul, map_sub, Complex.conj_ofReal]; ring
  · have e : ∀ K : α → α → ℂ, PBA.qf Y (fun x y => (ω x : ℂ) * (ω y : ℂ) * K x y) c =
        PBA.qf Y K (fun x => (ω x : ℂ) * c x) := by
      intro K; unfold PBA.qf
      exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
        simp only [map_mul, Complex.conj_ofReal]; ring
    rw [e, e]
    exact h.2 _

theorem loe_scale {Y : Finset α} {K : α → α → ℂ} (hK : TB.PSDOn Y K) {r r' : ℝ} (hr : 0 ≤ r' - r) :
    Loe Y (fun x y => (r : ℂ) * K x y) (fun x y => (r' : ℂ) * K x y) := by
  have h := loe_smul (r' - r) hr (loe_zero_of_psd hK)
  unfold Loe at h ⊢
  refine psd_congr (fun x _ y _ => ?_) h
  push_cast; ring

theorem gramH_smul (c : ℂ) (h : α → H) :
    gramH (fun P => c • h P) = fun P Q => ((‖c‖ ^ 2 : ℝ) : ℂ) * gramH h P Q := by
  funext P Q
  unfold gramH
  rw [inner_smul_left, inner_smul_right, ← mul_assoc, mul_comm (conj c) c, Complex.mul_conj']
  push_cast; ring

end gram

end

end Formalism.FourierDecayAlt.P.PBL
end

section

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem gauge_locality_holds : GTCLocal := gTCLocal_of_cut radial_torus_local_holds local_nabla_holds local_frame_holds

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section

open Formalism.FourierDecayAlt MeasureTheory
open Formalism.REAL Formalism.QuantumDeterminants
open NumberField

namespace Formalism.FourierDecayAlt.P.CutMP.En

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem foldCV_memB {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] {z z' : Fin (2 * r + k + 1) → ℂ} {π : Q.Mx k r → (Wp →L[ℂ] Wp)}
    {π' : Q.Mx k r → (Wq →L[ℂ] Wq)} {Dm : Set (Q.Mx k r)}
    (hcl : ∀ J ∈ Q.FFl k r z z' π π' 0 Dm, ∀ (Y : ℝ) (s : ℂ), s • Q.CV k r (Y : ℂ) J ∈ Q.FFl k r z z' π π' 0 Dm)
    {J : Q.Mx k r → (Wq →L[ℂ] Wp)} (hJ : J ∈ Q.FFl k r z z' π π' 0 Dm) (s : ℂ) :
    ∀ a : List C.Letter, foldCV k r s a J ∈ Q.FFl k r z z' π π' 0 Dm
  | [] => hJ
  | x :: a => hcl _ (foldCV_memB hcl hJ s a) x.2 s

theorem mem_level_zero_of_mem_group {k r : ℕ} {g : B.Mat k r} (hg : g ∈ B.GV k r) : g ∈ Q.Glev k r 0 :=
  ⟨hg, fun a ha => absurd ha (Nat.not_lt_zero _)⟩

theorem JF_smul' {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (c : ℂ)
    (G : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r) : B.JF D (c • G) g = c • B.JF D G g := by
  show ∫ p, JF.xiP D p • B.rho D p (c • G) g ∂D.μSS = c • ∫ p, JF.xiP D p • B.rho D p G g ∂D.μSS
  rw [← integral_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only [B.rho, Pi.smul_apply, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  rw [smul_comm]

theorem thr_budget (k r N : ℕ) (A₀ : ℝ) (hk : 2 ≤ k)
    (hA : 100 * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) ≤ A₀)
    (m : ℕ) (hm : m ≤ (2 * r + k + 1) * (N + 1)) :
    JF.TransportedAlt k r (A₀ - 2 * ((r : ℝ) + 1) * (((2 * r + k + 1) * (N + 1) : ℕ) : ℝ)) m := by
  unfold JF.TransportedAlt
  have hR : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hK : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  set n : ℝ := 2 * (r : ℝ) + k + 1 with hn
  set R : ℝ := (r : ℝ) + 1 with hRdef
  have hcast : ((2 * r + k + 1 : ℕ) : ℝ) = n := by rw [hn]; push_cast; ring
  have hMc : (((2 * r + k + 1) * (N + 1) : ℕ) : ℝ) = n * ((N : ℝ) + 1) := by rw [hn]; push_cast; ring
  have hmr : (m : ℝ) ≤ n * ((N : ℝ) + 1) := by rw [← hMc]; exact_mod_cast hm
  have hn3 : (3 : ℝ) ≤ n := by rw [hn]; linarith
  have hn0 : (0 : ℝ) ≤ n := by linarith
  have hR1 : (1 : ℝ) ≤ R := by rw [hRdef]; linarith
  have hR0 : (0 : ℝ) < R := by linarith
  have h4 : R ≤ R ^ 4 := by
    have : (1 : ℝ) ≤ R ^ 3 := one_le_pow₀ hR1
    calc R = R * 1 := by ring
      _ ≤ R * R ^ 3 := by gcongr
      _ = R ^ 4 := by ring
  set P : ℝ := (N : ℝ) * n ^ 2 + n ^ 3 with hP
  have hP0 : 0 ≤ P := by positivity
  have hA' : 100 * R * P ≤ A₀ := le_trans (by gcongr) hA
  have hnn : n ≤ n ^ 2 := by
    have := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ n by linarith) hn0
    calc n = n * 1 := by ring
      _ ≤ n * n := this
      _ = n ^ 2 := by ring
  have hn23 : 3 * n ^ 2 ≤ n ^ 3 := by
    have := mul_le_mul_of_nonneg_right hn3 (sq_nonneg n)
    calc 3 * n ^ 2 ≤ n * n ^ 2 := this
      _ = n ^ 3 := by ring
  have hn1 : 3 * n ≤ n ^ 2 := by
    have := mul_le_mul_of_nonneg_right hn3 hn0
    calc 3 * n ≤ n * n := this
      _ = n ^ 2 := by ring
  have i1 : 8 * (n * (N : ℝ)) ≤ 100 * ((N : ℝ) * n ^ 2) := by
    have := mul_le_mul_of_nonneg_right hnn hN0
    nlinarith
  have i2 : 8 * n + 9 * n ^ 2 < 100 * n ^ 3 := by nlinarith
  have inner : 8 * (n * ((N : ℝ) + 1)) + 9 * n ^ 2 < 100 * P := by rw [hP]; nlinarith
  have key : R * (8 * (n * ((N : ℝ) + 1)) + 9 * n ^ 2) < R * (100 * P) := mul_lt_mul_of_pos_left inner hR0
  have hrm : 6 * (r : ℝ) * (m : ℝ) ≤ 6 * R * (n * ((N : ℝ) + 1)) := by
    have h6 : 6 * (r : ℝ) ≤ 6 * R := by rw [hRdef]; linarith
    calc 6 * (r : ℝ) * (m : ℝ) ≤ 6 * R * (m : ℝ) := by gcongr
      _ ≤ 6 * R * (n * ((N : ℝ) + 1)) := by gcongr
  rw [hcast, hMc, lt_div_iff₀ (by positivity)]
  have e1 : R * (100 * P) = 100 * R * P := by ring
  have e2 : R * (8 * (n * ((N : ℝ) + 1)) + 9 * n ^ 2) =
      2 * R * (n * ((N : ℝ) + 1)) + 6 * R * (n * ((N : ℝ) + 1)) + n ^ 2 * (9 * R) := by ring
  rw [e1, e2] at key
  linarith

theorem besselFoldBuilt_of (hC : CVInCC) : BesselFoldBuilt := by
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v hcl ε hε hJF
  obtain ⟨⟨_, _, _, hbuilt, _, _, _, _, _, _, hk2, hA, _⟩, _, _, _⟩ := hB
  obtain ⟨hcut, hv⟩ := hbuilt
  obtain ⟨_, _, _, _, hCC, _⟩ := hv v
  set Db := (T v).base with hDb
  set s : ℂ := M.sgn (D.parOf S v) (S.l + 1) with hs
  set F := D.cutF Db χ (f v) ε with hF
  set n : ℕ := 2 * S.G.r + S.G.k + 1 with hn
  set N : ℕ := S.Ntop with hN
  set A : ℝ := A₀ - 2 * ((S.G.r : ℝ) + 1) * ((n * (N + 1) : ℕ) : ℝ) with hAdef
  have hThr : ∀ m, m ≤ n * (N + 1) → JF.TransportedAlt S.G.k S.G.r A m := fun m hm =>
    thr_budget S.G.k S.G.r N A₀ hk2 hA m hm
  have hFcc : B.InCC A (n * (N + 1)) F :=
    Formalism.FourierDecayAlt.P.PBE.cutF_inCC Db hcut hCC hε A (n * (N + 1)) (by rw [hAdef]; linarith)

  have hreg : ∀ a : List C.Letter, a.length ≤ N →
      B.InCC A (n * (N + 1 - a.length)) (foldCV S.G.k S.G.r s a F) := by
    intro a
    induction a with
    | nil => intro _; simp only [List.length_nil, Nat.sub_zero]; exact hFcc
    | cons x a ih =>
      intro hl
      simp only [List.length_cons] at hl
      have h1 := ih (by omega)
      have e : n * (N + 1 - a.length) = n * (N + 1 - (a.length + 1)) + (2 * S.G.r + S.G.k + 1) := by
        rw [← hn, ← Nat.mul_succ]; congr 1; omega
      rw [e] at h1
      have h2 := hC S.G.k S.G.r _ A _ _ (x.2 : ℂ) s h1
      simp only [List.length_cons]
      exact h2
  have hOp : IsOpen (Q.OmPlus S.G.k S.G.r Db.z Db.z') := Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet.isOpen_OmPlus _ _
  intro a
  induction a with
  | nil => intro _ g _; rfl
  | cons x a ih =>
    intro hl g hg
    simp only [List.length_cons] at hl
    have ih' := ih (by omega)
    set H := foldCV S.G.k S.G.r s a F with hH
    set m : ℕ := n * (N + 1 - a.length) with hm
    have hHcc : B.InCC A m H := hreg a (by omega)
    have hnm : 2 * S.G.r + S.G.k + 1 ≤ m := by
      rw [hm, ← hn]; exact Nat.le_mul_of_pos_right n (by omega)
    have hmM : m ≤ n * (N + 1) := by rw [hm]; exact Nat.mul_le_mul_left n (by omega)
    have hThm := hThr m hmM
    have hCkn : B.CkOn ((2 * S.G.r + S.G.k + 1 : ℕ) : ℕ∞) (B.GV S.G.k S.G.r) H :=
      Formalism.FourierDecayAlt.P.B5.ckOn_mono (by exact_mod_cast hnm) hHcc.choose_spec.1

    have hswap : B.JF Db (Q.CV S.G.k S.G.r (x.2 : ℂ) H) g = Q.CV S.G.k S.G.r (x.2 : ℂ) (B.JF Db H) g := by
      rw [Formalism.FourierDecayAlt.P.casimir_under_jacquet_integral S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) Db A m H (x.2 : ℂ) hnm hThm hHcc g hg]
      show ∫ p, JF.xiP Db p • B.rho Db p (Q.CV S.G.k S.G.r (x.2 : ℂ) H) g ∂Db.μSS = _
      refine integral_congr_ae ?_
      filter_upwards [Formalism.FourierDecayAlt.P.B7.ae_inSS Db] with p hp
      rw [Formalism.FourierDecayAlt.P.capelli_rho_commute S.G.k S.G.r _ _ Db (x.2 : ℂ) H p hp hCkn g hg.1]

    have hJHk : B.CkOn ((2 * S.G.r + S.G.k + 1 : ℕ) : ℕ∞) (Q.OmPlus S.G.k S.G.r Db.z Db.z' ∩ B.GV S.G.k S.G.r)
        (B.JF Db H) := by
      intro g₀ hg₀
      obtain ⟨U, F', hU, hgU, hc, he⟩ :=
        (Formalism.FourierDecayAlt.P.jacquet_derivative_formula S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) Db A m H hThm hHcc).1 g₀
          ⟨mem_level_zero_of_mem_group hg₀.2, hg₀.1⟩
      exact ⟨U, F', hU, hgU, hc.of_le (by exact_mod_cast hnm), fun g hgU hgG => he g hgU (mem_level_zero_of_mem_group hgG)⟩
    have hfold : foldCV S.G.k S.G.r s a (B.JF Db F) ∈
        Q.FFl S.G.k S.G.r Db.z Db.z' Db.π Db.π' 0 (OmP S T v) := foldCV_memB hcl hJF s a
    have hfk : B.CkOn ((2 * S.G.r + S.G.k + 1 : ℕ) : ℕ∞) (Q.OmPlus S.G.k S.G.r Db.z Db.z' ∩ B.GV S.G.k S.G.r)
        (foldCV S.G.k S.G.r s a (B.JF Db F)) := by
      intro g₀ hg₀
      obtain ⟨U, F', hU, hgU, hc, he⟩ := hfold.1 g₀
        ⟨mem_level_zero_of_mem_group hg₀.2, hg₀.1.2, fun b => hg₀.1.1 _ (by simp <;> omega)⟩
      exact ⟨U, F', hU, hgU, hc.of_le (by exact_mod_cast le_top), fun g hgU hgG => he g hgU (mem_level_zero_of_mem_group hgG)⟩
    have hloc := coefficient_vector_locality S.G.k S.G.r _ (Q.OmPlus S.G.k S.G.r Db.z Db.z') (B.JF Db H)
      (foldCV S.G.k S.G.r s a (B.JF Db F)) (x.2 : ℂ) hOp hJHk hfk
      (fun g' hg' => ih' g' ⟨hg'.2, hg'.1⟩) g ⟨hg.2, hg.1⟩
    show B.JF Db (s • Q.CV S.G.k S.G.r (x.2 : ℂ) H) g = (s • Q.CV S.G.k S.G.r (x.2 : ℂ) (foldCV S.G.k S.G.r s a (B.JF Db F))) g
    rw [JF_smul', hswap, hloc, Pi.smul_apply]

end Formalism.FourierDecayAlt.P.CutMP.En
end

section

open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

def PointStepT : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (j : ℕ) (hj : j + 1 ≤ P.r) (h : C.LPt) (c : ℂ) (hh : D.IsLocPt h j) (hc : D.IsLocPt (h ++ [(1, c)]) (j + 1)),
    KB.CptCoef p.T.base F → ∀ γ ∈ B.GV P.k (P.r - (j + 1)),
    KB.slv p.T F (j + 1) hj [] _ hc.2 (fun a => a.elim0) γ =
      ∫ xx : U.RC P.k 1 (P.r - (j + 1)) × U.RC P.k 1 (P.r - (j + 1)),
        (psi P.k (P.r - j) (p.T.bs j).z cStd (rn1 (by omega : P.r - (j + 1) + 1 = P.r - j) xx.1) *
            star (psi P.k (P.r - j) (p.T.bs j).z' cStd (rn1 (by omega : P.r - (j + 1) + 1 = P.r - j) xx.2))) •
          KB.slv p.T F j (by omega) [] h hh.2 (fun a => a.elim0)
            ((rn1 (by omega : P.r - (j + 1) + 1 = P.r - j) xx.1)⁻¹ *
              mc (by omega : P.r - (j + 1) + 1 = P.r - j) c γ * rn1 (by omega : P.r - (j + 1) + 1 = P.r - j) xx.2)
        ∂((U.muRC P.k 1 (P.r - (j + 1))).prod (U.muRC P.k 1 (P.r - (j + 1))))

theorem asm_castV_castV {k a b d : ℕ} (h1 : a = b) (h2 : b = d) (v : Fin (2 * a + k + 1) → ℂ) :
    D.castV h2 (D.castV h1 v) = D.castV (h1.trans h2) v := by
  subst h1; subst h2; rfl

theorem castM_castM' {k a b d : ℕ} (h1 : a = b) (h2 : b = d) (g : B.Mat k a) :
    D.castM h2 (D.castM h1 g) = D.castM (h1.trans h2) g := by
  subst h1; subst h2; rfl

theorem sliceStep_of (hJ : JFStep) (hP : PointStepT) : KB.SliceStep := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj h c hh hc hF γ hγ hΩ
  have e : P.r - (j + 1) + 1 = P.r - j := by omega
  have hc0 : c ≠ 0 := (hc.1 (1, c) (List.mem_append_right _ (List.mem_singleton_self _))).2
  have hT := p.hT
  have key := hJ P.k (P.r - (j + 1)) (P.r - j) e Wp Wq (p.T.bs j) (p.T.bs (j + 1))
    (by rw [levTower_bs_z_eq_castV_liftVec p.T j hj, asm_castV_castV])
    (by rw [levTower_bs_z'_eq_castV_liftVec p.T j hj, asm_castV_castV])
    (fun y => by rw [tower_π p.T j hj, lev1, castM_castM'])
    (fun y => by rw [tower_π' p.T j hj, lev1, castM_castM'])
    (hT j (by omega)).1 (hT j (by omega)).2.1 (hT (j + 1) hj).1 (hT (j + 1) hj).2.1
    (hT j (by omega)).2.2 (hT (j + 1) hj).2.2
    (KB.slv p.T F j (by omega) [] h hh.2 fun a => a.elim0)
    (KB.slv p.T F (j + 1) hj [] _ hc.2 fun a => a.elim0) c hc0
    (Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F j (by omega) [] h hh hF _)
    (fun γ' hγ' => hP Wp Wq P p F j hj h c hh hc hF γ' hγ') γ hγ hΩ
  rw [key, mc, castM_castM']

end Formalism.FourierDecayAlt.P.PBH
end
end

section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

theorem jAStarOp_of_pairL (h : SA.SAPairL) : JAStarOp :=
  SA.jAStarOp_of_parts SA.model_adjoint_identity_holds self_adjoint_section_holds h SA.fundamental_quadratic_identity

end Formalism.FourierDecayAlt.P.CutMP.JA
end
