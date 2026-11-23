module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.NumberTheory.ModularForms.BoundedAtCusp
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.HeckeFamilyMatrices

def wOld (N l : ℕ) (a b : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![(l : ℤ), a; (N : ℤ) * l, (l : ℤ) * b]

def gaOld (N l : ℕ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1) (j : ℕ) : SL(2, ℤ) :=
  ⟨!![1, (j : ℤ) + a; (N : ℤ), (N : ℤ) * j + l * b], by
    rw [Matrix.det_fin_two_of]; linear_combination h⟩

def trOld (k : ℤ) (N l : ℕ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1) (G : ℍ → ℂ) : ℍ → ℂ :=
  G + ∑ j ∈ Finset.range l, G ∣[k] gaOld N l a b h j

def ChiInv (k : ℤ) (N M : ℕ) (χ : DirichletCharacter ℂ N) (G : ℍ → ℂ) : Prop :=
  ∀ γ : SL(2, ℤ), γ ∈ Gamma0 M → G ∣[k] γ = χ ((mat γ 1 1 : ℤ) : ZMod N) • G

def CuspAll (k : ℤ) (G : ℍ → ℂ) : Prop :=
  MDiff G ∧ ∀ c : OnePoint ℝ, IsCusp c 𝒮ℒ → c.IsZeroAt G k

end GlobalTheory.HeckeFamilyMatrices

namespace GlobalTheory.HeckeFamilyMatrices

lemma toGL_val (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : g.det ≠ 0) :
    ((toGL g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = (Int.castRingHom ℝ).mapMatrix g := by
  unfold toGL
  rw [dite_eq_right hg]
  rfl

lemma toGL_det (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : g.det ≠ 0) :
    ((toGL g).det : ℝ) = (g.det : ℝ) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, toGL_val g hg, ← RingHom.map_det]
  simp

lemma toGL_mul (g h : Matrix (Fin 2) (Fin 2) ℤ) (hg : g.det ≠ 0) (hh : h.det ≠ 0) :
    toGL (g * h) = toGL g * toGL h := by
  have hgh : (g * h).det ≠ 0 := by
    rw [Matrix.det_mul]
    exact mul_ne_zero hg hh
  apply Units.ext
  rw [Units.val_mul, toGL_val _ hgh, toGL_val _ hg, toGL_val _ hh]
  exact map_mul (Int.castRingHom ℝ).mapMatrix g h

lemma slash_SL_eq (k : ℤ) (γ : SL(2, ℤ)) (G : ℍ → ℂ) : G ∣[k] γ = G ∣[k] toGL (mat γ) := by
  rw [ModularForm.SL_slash]
  congr 1
  apply Units.ext
  rw [toGL_val _ (by simp [mat])]
  ext i j
  simp [mat]

end GlobalTheory.HeckeFamilyMatrices

namespace GlobalTheory.HeckeFamilyMatrices

lemma sigma_pos {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val) (z : ℂ) : σ g z = z := by
  rw [σ, if_pos hg]
  rfl

lemma slash_scalar (k : ℤ) (c : ℝ) (hc : 0 < c) (G : ℍ → ℂ) :
    G ∣[k] (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 c hc.ne')) = ((c : ℂ) ^ (k - 2)) • G := by
  ext τ
  have hdet : (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 c hc.ne')).det.val = c ^ 2 := by
    simp [Matrix.GeneralLinearGroup.det_scalar]
  have hpos : 0 < (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 c hc.ne')).det.val := by
    rw [hdet]; positivity
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  rw [ModularForm.slash_apply, sigma_pos hpos, hdet, abs_of_pos (by positivity),
    UpperHalfPlane.glScalar_smul, UpperHalfPlane.denom_scalar]
  simp only [Units.val_mk0, Pi.smul_apply, smul_eq_mul]
  push_cast
  rw [← zpow_natCast, ← zpow_mul]
  have he : (c : ℂ) ^ (k - 2) = (c : ℂ) ^ (((2 : ℕ) : ℤ) * (k - 1)) * (c : ℂ) ^ (-k) := by
    rw [← zpow_add₀ hc']
    congr 1
    push_cast
    ring
  rw [he]
  ring

end GlobalTheory.HeckeFamilyMatrices

namespace GlobalTheory.HeckeFamilyMatrices

lemma toGL_det_pos (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : 0 < g.det) : 0 < (toGL g).det.val := by
  rw [toGL_det g hg.ne']
  exact_mod_cast hg

lemma smul_slash_toGL (k : ℤ) (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0 < M.det) (c : ℂ) (G : ℍ → ℂ) :
    (c • G) ∣[k] toGL M = c • (G ∣[k] toGL M) := by
  rw [ModularForm.smul_slash, sigma_pos (toGL_det_pos M hM)]

lemma toGL_smul (c : ℕ) (hc : 0 < c) (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : g.det ≠ 0) :
    toGL ((c : ℤ) • g) = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (c : ℝ) (by positivity)) * toGL g := by
  have h1 : ((c : ℤ) • g).det ≠ 0 := by
    rw [Matrix.det_smul]
    simp [hg, hc.ne']
  apply Units.ext
  rw [Units.val_mul, toGL_val _ h1, toGL_val _ hg, Matrix.GeneralLinearGroup.coe_scalar]
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.scalar_apply, Matrix.diagonal_mul,
    Units.val_mk0, Matrix.smul_apply, smul_eq_mul]
  simp

lemma slash_toGL_smul (k : ℤ) (c : ℕ) (hc : 0 < c) (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : 0 < g.det)
    (G : ℍ → ℂ) : G ∣[k] toGL ((c : ℤ) • g) = ((c : ℂ) ^ (k - 2)) • (G ∣[k] toGL g) := by
  rw [toGL_smul c hc g hg.ne', SlashAction.slash_mul, slash_scalar k (c : ℝ) (by positivity),
    smul_slash_toGL k g hg, Complex.ofReal_natCast]

lemma ulFam_det (l : ℕ) (hl : 0 < l) (j : Fin l) : 0 < (ulFam l j).det := by
  simp [ulFam, Matrix.det_fin_two_of]
  exact_mod_cast hl

lemma ulF_add (k : ℤ) (l : ℕ) (F G : ℍ → ℂ) : UlF k l (F + G) = UlF k l F + UlF k l G := by
  simp only [UlF, hkF, SlashAction.add_slash, Finset.sum_add_distrib]

lemma ulF_smul (k : ℤ) (l : ℕ) (hl : 0 < l) (c : ℂ) (F : ℍ → ℂ) : UlF k l (c • F) = c • UlF k l F := by
  simp only [UlF, hkF, Finset.smul_sum]
  exact Finset.sum_congr rfl fun j _ => smul_slash_toGL k _ (ulFam_det l hl j) c F

lemma ulF_sub (k : ℤ) (l : ℕ) (hl : 0 < l) (F G : ℍ → ℂ) : UlF k l (F - G) = UlF k l F - UlF k l G := by
  have h := ulF_smul k l hl (-1) G
  rw [sub_eq_add_neg, ulF_add, sub_eq_add_neg]
  congr 1
  simpa using h

end GlobalTheory.HeckeFamilyMatrices

namespace GlobalTheory.HeckeFamilyMatrices
open CongruenceSubgroup

lemma chiInv_add {k : ℤ} {N M : ℕ} {χ : DirichletCharacter ℂ N} {F G : ℍ → ℂ} (hF : ChiInv k N M χ F)
    (hG : ChiInv k N M χ G) : ChiInv k N M χ (F + G) := by
  intro γ hγ
  rw [SlashAction.add_slash, hF γ hγ, hG γ hγ, smul_add]

lemma chiInv_smul {k : ℤ} {N M : ℕ} {χ : DirichletCharacter ℂ N} {F : ℍ → ℂ} (c : ℂ) (hF : ChiInv k N M χ F) :
    ChiInv k N M χ (c • F) := by
  intro γ hγ
  rw [ModularForm.SL_smul_slash, hF γ hγ, smul_comm]

lemma cuspAll_add {k : ℤ} {F G : ℍ → ℂ} (hF : CuspAll k F) (hG : CuspAll k G) : CuspAll k (F + G) := ⟨hF.1.add hG.1, fun c hc => (hF.2 c hc).add (hG.2 c hc)⟩

lemma cuspAll_smul {k : ℤ} {F : ℍ → ℂ} (c : ℂ) (hF : CuspAll k F) : CuspAll k (c • F) := by
  refine ⟨hF.1.const_smul c, fun p hp g hg => ?_⟩
  rw [ModularForm.smul_slash]
  exact Filter.ZeroAtFilter.smul _ (hF.2 p hp g hg)

end GlobalTheory.HeckeFamilyMatrices
end
end

section

noncomputable section

open Finset
open scoped Classical

namespace GlobalTheory.KummerEisensteinGalois.Smoothing

variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
theorem zpow_congr_of_pow_eq_one {ζ : K} {M : ℕ} (hM : 0 < M) (hζ : ζ ^ M = 1) {a b : ℤ}
    (h : a ≡ b [ZMOD M]) : ζ ^ a = ζ ^ b := by
  have hz : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hM.ne'] at hζ
    exact zero_ne_one hζ
  obtain ⟨s, hs⟩ := h.dvd
  have hb : b = a + M * s := by linarith
  rw [hb, zpow_add₀ hz, zpow_mul, zpow_natCast, hζ, one_zpow, mul_one]

theorem eisF_congr_mod {j M : ℕ} (hM : 0 < M) {ζ : K} (hζ : ζ ^ M = 1) {a₁ a₂ b₁ b₂ : ℤ}
    (h₁ : a₁ ≡ b₁ [ZMOD M]) (h₂ : a₂ ≡ b₂ [ZMOD M]) :
    eisF j M ζ a₁ a₂ = eisF j M ζ b₁ b₂ := by
  funext n
  have h₁' : a₁ % (M : ℤ) = b₁ % (M : ℤ) := h₁
  have hc : const0 j M ζ a₁ a₂ = const0 j M ζ b₁ b₂ := by
    have hd : ((M : ℤ) ∣ a₁) ↔ ((M : ℤ) ∣ b₁) := by
      rw [Int.dvd_iff_emod_eq_zero, Int.dvd_iff_emod_eq_zero, h₁']
    have hf : frc M a₁ = frc M b₁ := by unfold frc; rw [h₁']
    unfold const0
    rw [zpow_congr_of_pow_eq_one hM hζ h₂, hf]
    simp only [hd]
  have hp : coefPos j M ζ a₁ a₂ n = coefPos j M ζ b₁ b₂ n := by
    unfold coefPos
    refine Finset.sum_congr rfl (fun d _ => ?_)
    have e1 : ∀ z : ℤ, z ≡ a₁ [ZMOD M] ↔ z ≡ b₁ [ZMOD M] :=
      fun z => ⟨fun h => h.trans h₁, fun h => h.trans h₁.symm⟩
    rw [zpow_congr_of_pow_eq_one hM hζ (h₂.mul_right (d : ℤ)),
      zpow_congr_of_pow_eq_one hM hζ (h₂.mul_right (d : ℤ)).neg]
    simp only [e1]
  unfold eisF
  rw [hc, hp]

omit [CharZero K] in
theorem cmul_expand (a b a' b' : K) (f g h l : ℕ → K) (r : ℕ) :
    cmul (fun i => a * f i - b * g i) (fun i => a' * h i - b' * l i) r =
      a * a' * cmul f h r - a * b' * cmul f l r - b * a' * cmul g h r + b * b' * cmul g l r := by
  unfold cmul
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

theorem not_dvd_val_iff_isUnit {p n : ℕ} [hp : Fact p.Prime] (hn : 0 < n) (y : ZMod (p ^ n)) :
    ¬ p ∣ y.val ↔ IsUnit y := by
  have h := ZMod.isUnit_iff_coprime y.val (p ^ n)
  rw [ZMod.natCast_zmod_val] at h
  rw [h, Nat.coprime_pow_right_iff hn, Nat.coprime_comm, hp.out.coprime_iff_not_dvd]

theorem isUnit_intCast_of_not_dvd {p n : ℕ} [hp : Fact p.Prime] {c : ℤ}
    (hc : ¬ (p : ℤ) ∣ c) : IsUnit (c : ZMod (p ^ n)) := by
  have h1 : IsCoprime (p : ℤ) c :=
    (Nat.prime_iff_prime_int.mp hp.out).irreducible.coprime_iff_not_dvd.mpr hc
  obtain ⟨a, b, hab⟩ := (h1.pow_left (m := n))
  have h2 : ((a * (p : ℤ) ^ n + b * c : ℤ) : ZMod (p ^ n)) = 1 := by rw [hab]; simp
  have h3 : ((p : ZMod (p ^ n))) ^ n = 0 := by
    rw [← Nat.cast_pow]; exact ZMod.natCast_self _
  push_cast at h2
  rw [h3, mul_zero, zero_add, mul_comm] at h2
  exact IsUnit.of_mul_eq_one _ h2

def diagGL {R : Type*} [CommRing R] (u v : Rˣ) : GL (Fin 2) R :=
  ⟨Matrix.diagonal ![(u : R), v], Matrix.diagonal ![((u⁻¹ : Rˣ) : R), ((v⁻¹ : Rˣ) : R)],
   by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; ext i; fin_cases i <;> simp,
   by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; ext i; fin_cases i <;> simp⟩

theorem diagGL_mul_zero {R : Type*} [CommRing R] (u v : Rˣ) (γ : GL (Fin 2) R) (j : Fin 2) :
    ((diagGL u v * γ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 j =
      (u : R) * (γ : Matrix (Fin 2) (Fin 2) R) 0 j := by
  rw [Units.val_mul]
  exact Matrix.diagonal_mul _ _ _ _

theorem diagGL_mul_one {R : Type*} [CommRing R] (u v : Rˣ) (γ : GL (Fin 2) R) (j : Fin 2) :
    ((diagGL u v * γ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 j =
      (v : R) * (γ : Matrix (Fin 2) (Fin 2) R) 1 j := by
  rw [Units.val_mul]
  exact Matrix.diagonal_mul _ _ _ _

theorem diagGL_mul_det {R : Type*} [CommRing R] (u v : Rˣ) (γ : GL (Fin 2) R) :
    ((diagGL u v * γ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R).det =
      (u : R) * v * (γ : Matrix (Fin 2) (Fin 2) R).det := by
  rw [Matrix.det_fin_two, Matrix.det_fin_two]
  simp only [diagGL_mul_zero, diagGL_mul_one]
  ring

theorem diagGL_mul_mem {p n : ℕ} [Fact p.Prime] (hn : 0 < n) (u v : (ZMod (p ^ n))ˣ)
    (γ : GL (Fin 2) (ZMod (p ^ n))) : diagGL u v * γ ∈ unitSet p n ↔ γ ∈ unitSet p n := by
  simp only [unitSet, Finset.mem_filter, Finset.mem_univ, true_and, not_dvd_val_iff_isUnit hn,
    diagGL_mul_zero, diagGL_mul_one, Units.isUnit_units_mul]

end GlobalTheory.KummerEisensteinGalois.Smoothing
end
end

section

open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

variable {L : Type} [Field L]

theorem approxRoot_exists_val_pow {p : ℕ} {v : Valuation L ℝ≥0} {F : Subfield L}
    (hA : ApproxRoot p v F) {u : L} (hu : u ∈ F) (hu0 : u ≠ 0) :
    ∃ w ∈ F, v w ^ p = v u := by
  obtain ⟨θ, hθ, h⟩ := hA
  obtain ⟨w, hw, hle⟩ := h u hu
  have hvu : 0 < v u := pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff v).mpr hu0)
  have hlt : v (w ^ p - u) < v u := by
    rw [Valuation.map_sub_swap]
    exact lt_of_le_of_lt hle (mul_lt_of_lt_one_left hvu hθ)
  refine ⟨w, hw, ?_⟩
  rw [← map_pow]
  exact Valuation.map_eq_of_sub_lt v hlt

theorem approxRoot_exists_root_of_p {p : ℕ} (hp : p.Prime) {v : Valuation L ℝ≥0} {F : Subfield L}
    (hA : ApproxRoot p v F) (hp0 : 0 < v (p : L)) :
    ∀ k : ℕ, ∃ π ∈ F, v π ^ (p ^ k) = v (p : L) := by
  intro k
  induction k with
  | zero => exact ⟨(p : L), natCast_mem F p, by simp⟩
  | succ k ih =>
    obtain ⟨π, hπ, hv⟩ := ih
    have hπ0 : π ≠ 0 := by
      rintro rfl
      rw [map_zero, zero_pow (pow_ne_zero _ hp.ne_zero)] at hv
      exact hp0.ne hv
    obtain ⟨w, hw, hw'⟩ := approxRoot_exists_val_pow hA hπ hπ0
    refine ⟨w, hw, ?_⟩
    rw [pow_succ', pow_mul, hw', hv]

theorem exists_scale_shell (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ) (hp : p.Prime)
    (F : Subfield L) (hA : ApproxRoot p v F) (hp0 : 0 < v (p : L)) (hp1 : v (p : L) < 1)
    (r : ℝ≥0) (hr : r < 1) (x : L) (hx : x ≠ 0) :
    ∃ d ∈ F, d ≠ 0 ∧ r < v (x * d ^ p) ∧ v (x * d ^ p) ≤ 1 := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (pow_pos hp0 p) hr
  obtain ⟨π, hπ, hv⟩ := approxRoot_exists_root_of_p hp hA hp0 n
  set s := v π with hs
  set t := s ^ p with ht
  have hrt : r < t := by
    by_contra h
    push_neg at h
    have h1 : t ^ (p ^ n) ≤ r ^ (p ^ n) := pow_le_pow_left₀ (by positivity) h _
    have h2 : r ^ (p ^ n) ≤ r ^ n :=
      pow_le_pow_of_le_one (by positivity) hr.le (Nat.lt_pow_self hp.one_lt).le
    have h3 : t ^ (p ^ n) = v (p : L) ^ p := by rw [ht, ← pow_mul, mul_comm, pow_mul, hv]
    exact absurd (lt_of_le_of_lt (h3 ▸ h1.trans h2) hn) (lt_irrefl _)
  have hs1 : s < 1 := by
    by_contra h
    push_neg at h
    have := one_le_pow₀ (n := p ^ n) h
    rw [hv] at this
    exact absurd hp1 (not_lt.mpr this)
  have ht1 : t < 1 := pow_lt_one₀ (by positivity) hs1 hp.ne_zero
  have ht0 : 0 < t := lt_of_le_of_lt (by positivity) hrt
  have hπ0 : π ≠ 0 := by
    rintro rfl
    have h0 : s = 0 := by rw [hs, map_zero]
    rw [ht, h0, zero_pow hp.ne_zero] at ht0
    exact lt_irrefl _ ht0
  have hvx : 0 < v x := pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff v).mpr hx)
  obtain ⟨m, hm1, hm2⟩ := exists_mem_Ioc_zpow hvx ((one_lt_inv₀ ht0).mpr ht1)
  refine ⟨π ^ (m + 1), zpow_mem hπ _, zpow_ne_zero _ hπ0, ?_⟩
  have hval : v (x * (π ^ (m + 1)) ^ p) = v x * t ^ (m + 1) := by
    rw [map_mul, map_pow, map_zpow₀, ← hs, ht, ← zpow_natCast, ← zpow_natCast, ← zpow_mul,
      ← zpow_mul, mul_comm (m + 1)]
  rw [hval]
  have htne : t ≠ 0 := ht0.ne'
  constructor
  · have e : t⁻¹ ^ m * t ^ (m + 1) = t := by
      rw [inv_zpow, zpow_add_one₀ htne, ← mul_assoc, inv_mul_cancel₀ (zpow_ne_zero _ htne), one_mul]
    calc r < t := hrt
      _ = t⁻¹ ^ m * t ^ (m + 1) := e.symm
      _ < v x * t ^ (m + 1) := mul_lt_mul_of_pos_right hm1 (zpow_pos ht0 _)
  · have e : t⁻¹ ^ (m + 1) * t ^ (m + 1) = 1 := by
      rw [inv_zpow, inv_mul_cancel₀ (zpow_ne_zero _ htne)]
    calc v x * t ^ (m + 1) ≤ t⁻¹ ^ (m + 1) * t ^ (m + 1) := mul_le_mul_of_nonneg_right hm2 (by positivity)
      _ = 1 := e

theorem klc_scale : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime → ∀ F : Subfield L,
    ApproxRoot p v F → 0 < v (p : L) → v (p : L) < 1 → ∀ r : ℝ≥0, r < 1 → ∀ x : L, x ≠ 0 →
    ∃ d ∈ F, d ≠ 0 ∧ r < v (x * d ^ p) ∧ v (x * d ^ p) ≤ 1 :=
  fun L _ v p hp F hA hp0 hp1 r hr x hx => exists_scale_shell L v p hp F hA hp0 hp1 r hr x hx

end GlobalTheory.AlmostEt
end

section

open GlobalTheory.NeedB Polynomial

namespace GlobalTheory

open MvPolynomial

theorem is_c1_of_finite_of_tsen_lang_systems : ∀ (F K : Type) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K],
  (∀ (n r d : ℕ) (f : Fin r → MvPolynomial (Fin n) F), (∀ i, (f i).IsHomogeneous d) → 0 < d → r * d < n →
    ∃ x : Fin n → F, x ≠ 0 ∧ ∀ i, MvPolynomial.eval x (f i) = 0) → IsFirstChernClassOfLineBundle K := by
  intro F K _ _ _ _ hF n d f hf hd hdn
  set m := Module.finrank F K with hm
  have hm0 : 0 < m := Module.finrank_pos
  let b : Module.Basis (Fin m) F K := Module.finBasis F K
  let e : Fin n × Fin m ≃ Fin (n * m) := finProdFinEquiv
  let g : Fin n → MvPolynomial (Fin (n * m)) K := fun i => ∑ j, MvPolynomial.C (b j) * MvPolynomial.X (e (i, j))
  have hg : ∀ i, (g i).IsHomogeneous 1 := fun i =>
    IsHomogeneous.sum _ _ _ (fun j _ => isHomogeneous_C_mul_X _ _)
  let G : MvPolynomial (Fin (n * m)) K := aeval g f
  have hG : G.IsHomogeneous d := by
    have h1 := hf.aeval g hg
    rwa [one_mul] at h1
  let P : Fin m → MvPolynomial (Fin (n * m)) F := fun l =>
    ∑ s ∈ G.support, monomial s (b.repr (G.coeff s) l)
  have hP : ∀ l, (P l).IsHomogeneous d := fun l =>
    IsHomogeneous.sum _ _ _ (fun s hs => isHomogeneous_monomial _ (by
      rw [Finsupp.degree_eq_weight_one]; exact hG (mem_support_iff.mp hs)))
  have hlt : m * d < n * m := by
    rw [mul_comm n m]; exact Nat.mul_lt_mul_of_pos_left hdn hm0
  obtain ⟨y, hy0, hy⟩ := hF (n * m) m d P hP hd hlt
  let x : Fin n → K := fun i => ∑ j, algebraMap F K (y (e (i, j))) * b j
  refine ⟨x, ?_, ?_⟩
  · intro hx
    apply hy0
    funext k
    obtain ⟨⟨i, j⟩, rfl⟩ := e.surjective k
    have hxi : ∑ j, y (e (i, j)) • b j = 0 := by
      have := congrFun hx i
      simpa [x, Algebra.smul_def] using this
    exact Fintype.linearIndependent_iff.mp b.linearIndependent (fun j => y (e (i, j))) hxi j
  · have key : MvPolynomial.eval x f = MvPolynomial.eval (fun k => algebraMap F K (y k)) G := by
      rw [← MvPolynomial.coe_aeval_eq_eval, ← MvPolynomial.coe_aeval_eq_eval]
      show _ = MvPolynomial.aeval _ (MvPolynomial.bind₁ g f)
      rw [MvPolynomial.aeval_bind₁]
      have hxe : x = fun i => MvPolynomial.aeval (fun k => algebraMap F K (y k)) (g i) := by
        funext i
        simp [g, x, mul_comm]
      rw [hxe]
      rfl
    have key2 : MvPolynomial.eval (fun k => algebraMap F K (y k)) G
        = ∑ l, algebraMap F K (MvPolynomial.eval y (P l)) * b l := by

      simp only [P, map_sum, MvPolynomial.eval_monomial, Finset.sum_mul]
      rw [Finset.sum_comm, MvPolynomial.eval_eq]
      refine Finset.sum_congr rfl (fun s hs => ?_)
      conv_lhs => rw [← b.sum_repr (G.coeff s)]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      simp [Finsupp.prod, map_prod, map_pow, Algebra.smul_def]
      ring
    rw [key, key2]
    exact Finset.sum_eq_zero (fun l _ => by rw [hy l, map_zero, zero_mul])

end GlobalTheory
end
