module

public import Formalism.PeriodIntegrals.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

section Transport
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

lemma mem_dualLat_iff (H : Sesq V) (Λ : AddSubgroup V) (x : V) :
    x ∈ dualLat H Λ ↔ ∀ y ∈ Λ, ∃ k : ℤ, altE H x y = k := by
  exact Iff.rfl

lemma mem_imgLat_iff (g : V ≃ₗ[ℂ] V) (Λ : AddSubgroup V) (x : V) :
    x ∈ imgLat (g : V →ₗ[ℂ] V) Λ ↔ ∃ y ∈ Λ, g y = x := by
  simp [imgLat, AddSubgroup.mem_map]

lemma selfDual_img (H : Sesq V) (g : V ≃ₗ[ℂ] V) (hg : IsIsom H H (g : V →ₗ[ℂ] V)) {Λ : AddSubgroup V}
    (hΛ : IsSelfDual H Λ) : IsSelfDual H (imgLat (g : V →ₗ[ℂ] V) Λ) := by
  have hg' : ∀ a b, H (g a) (g b) = H a b := fun a b => by simpa using hg a b
  unfold IsSelfDual at hΛ ⊢
  ext x
  rw [mem_dualLat_iff, mem_imgLat_iff]
  obtain ⟨x₀, rfl⟩ := g.surjective x
  have key : (∀ y ∈ imgLat (g : V →ₗ[ℂ] V) Λ, ∃ k : ℤ, altE H (g x₀) y = k) ↔ x₀ ∈ dualLat H Λ := by
    rw [mem_dualLat_iff]
    constructor
    · intro h y hy
      obtain ⟨k, hk⟩ := h (g y) ((mem_imgLat_iff g Λ _).mpr ⟨y, hy, rfl⟩)
      exact ⟨k, by rw [← hk]; simp only [altE]; rw [hg']⟩
    · intro h y' hy'
      obtain ⟨y, hy, rfl⟩ := (mem_imgLat_iff g Λ y').mp hy'
      obtain ⟨k, hk⟩ := h y hy
      exact ⟨k, by simp only [altE]; rw [hg']; exact hk⟩
  rw [key, hΛ]
  constructor
  · intro h
    exact ⟨x₀, h, rfl⟩
  · rintro ⟨y, hy, hxy⟩
    rwa [g.injective hxy] at hy

lemma comm_img (g : V ≃ₗ[ℂ] V) {S Λ : AddSubgroup V}
    (hg1 : relIdx S (imgLat (g : V →ₗ[ℂ] V) S) ≠ 0) (hg2 : relIdx (imgLat (g : V →ₗ[ℂ] V) S) S ≠ 0)
    (h1 : relIdx S Λ ≠ 0) (h2 : relIdx Λ S ≠ 0) :
    relIdx S (imgLat (g : V →ₗ[ℂ] V) Λ) ≠ 0 ∧ relIdx (imgLat (g : V →ₗ[ℂ] V) Λ) S ≠ 0 := by
  have hinj : Function.Injective (g : V →ₗ[ℂ] V).toAddMonoidHom := g.injective
  have hm : ∀ A B : AddSubgroup V, relIdx (imgLat (g : V →ₗ[ℂ] V) A) (imgLat (g : V →ₗ[ℂ] V) B) = relIdx A B :=
    fun A B => AddSubgroup.relIndex_map_map_of_injective A B hinj
  refine ⟨?_, ?_⟩
  · exact AddSubgroup.relIndex_ne_zero_trans hg1 (by rw [← hm S Λ] at h1; exact h1)
  · exact AddSubgroup.relIndex_ne_zero_trans (by rw [← hm Λ S] at h2; exact h2) hg2

lemma imgLat_trans (g σ : V ≃ₗ[ℂ] V) (Λ : AddSubgroup V) :
    imgLat ((g.trans σ : V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V) Λ = imgLat (σ : V →ₗ[ℂ] V) (imgLat (g : V →ₗ[ℂ] V) Λ) := by
  ext x
  simp only [mem_imgLat_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨g y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, rfl⟩

lemma isom_trans (H : Sesq V) (g σ : V ≃ₗ[ℂ] V) (hg : IsIsom H H (g : V →ₗ[ℂ] V)) (hσ : IsIsom H H (σ : V →ₗ[ℂ] V)) :
    IsIsom H H ((g.trans σ : V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V) := by
  intro x y
  have h1 := hσ (g x) (g y)
  have h2 := hg x y
  simp only [LinearEquiv.coe_coe] at h1 h2 ⊢
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, h1, h2]

end Transport

lemma exists_good_form {a : ℕ} {b c : ℤ} {d : ℕ} (hok : CmOK a b c d) {l : ℕ} (hl : l.Prime) :
    ∃ x y : ℤ, ¬ (l : ℤ) ∣ a * x ^ 2 + b * x * y + c * y ^ 2 := by
  obtain ⟨hE, _, _, hd⟩ := hok
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  have h1 := hcon 1 0
  have h2 := hcon 0 1
  have h3 := hcon 1 1
  norm_num at h1 h2 h3
  have hb : (l : ℤ) ∣ b := by
    have h4 := dvd_sub (dvd_sub h3 h1) h2
    have e : (a : ℤ) + b + c - a - c = b := by ring
    rwa [e] at h4
  have hl2 : (l : ℤ) ^ 2 ∣ (d : ℤ) := by
    have e : (d : ℤ) = 4 * a * c - b ^ 2 := by linarith
    rw [e]
    refine dvd_sub ?_ (pow_dvd_pow_of_dvd hb 2)
    rw [pow_two]
    exact mul_dvd_mul (dvd_mul_of_dvd_right h1 4) h2
  have hl2' : l ^ 2 ∣ d := by exact_mod_cast hl2
  have hld : l ∣ d := (dvd_pow_self l two_ne_zero).trans hl2'
  have hleq : l = d := (Nat.prime_dvd_prime_iff_eq hl hd).mp hld
  subst hleq
  have h5 := Nat.le_of_dvd hd.pos hl2'
  have h6 := hd.two_le
  nlinarith

end PI.UnitaryGroupMassFormula.UnimodLocStd
end
end

section

noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

section IsKsec
variable (b : ℤ) (d : ℕ)

def IsK (t : ℂ) : Prop := ∃ p q r : ℤ, r ≠ 0 ∧ (r : ℂ) * t = p + q * cmTheta b d

variable {b d}

lemma isK_int (n : ℤ) : IsK b d n := by
  unfold PI.UnitaryGroupMassFormula.UnimodLocStd.IsK
  exact ⟨n, 0, 1, one_ne_zero, by simp⟩

lemma isK_theta : IsK b d (cmTheta b d) := by
  unfold PI.UnitaryGroupMassFormula.UnimodLocStd.IsK
  exact ⟨0, 1, 1, one_ne_zero, by simp⟩

lemma isK_add {t t' : ℂ} (h : IsK b d t) (h' : IsK b d t') : IsK b d (t + t') := by
  obtain ⟨p, q, r, hr, h⟩ := h
  obtain ⟨p', q', r', hr', h'⟩ := h'
  unfold PI.UnitaryGroupMassFormula.UnimodLocStd.IsK
  refine ⟨r' * p + r * p', r' * q + r * q', r * r', mul_ne_zero hr hr', ?_⟩
  push_cast
  linear_combination (r' : ℂ) * h + (r : ℂ) * h'

lemma isK_neg {t : ℂ} (h : IsK b d t) : IsK b d (-t) := by
  obtain ⟨p, q, r, hr, h⟩ := h
  unfold PI.UnitaryGroupMassFormula.UnimodLocStd.IsK
  refine ⟨-p, -q, r, hr, ?_⟩
  push_cast
  linear_combination -h

lemma isK_sub {t t' : ℂ} (h : IsK b d t) (h' : IsK b d t') : IsK b d (t - t') := by
  rw [sub_eq_add_neg]
  exact PI.UnitaryGroupMassFormula.UnimodLocStd.isK_add h (PI.UnitaryGroupMassFormula.UnimodLocStd.isK_neg h')

private lemma conj_cmTheta : conj (cmTheta b d) = (b : ℂ) - cmTheta b d := by
  unfold cmTheta
  simp only [map_div₀, map_add (f := _), map_mul, Complex.conj_I, Complex.conj_ofReal, map_intCast, map_ofNat]
  ring

lemma isK_conj {t : ℂ} (h : IsK b d t) : IsK b d (conj t) := by
  obtain ⟨p, q, r, hr, h⟩ := h
  have h2 : (r : ℂ) * conj t = p + q * conj (cmTheta b d) := by
    have h3 := congrArg conj h
    simpa using h3
  unfold PI.UnitaryGroupMassFormula.UnimodLocStd.IsK
  refine ⟨p + q * b, -q, r, hr, ?_⟩
  rw [h2, PI.UnitaryGroupMassFormula.UnimodLocStd.conj_cmTheta]
  push_cast
  ring

variable {e : ℤ} (hn : cmTheta b d * (b - cmTheta b d) = (e : ℂ))
include hn

lemma isK_mul {t t' : ℂ} (h : IsK b d t) (h' : IsK b d t') : IsK b d (t * t') := by
  obtain ⟨p, q, r, hr, h⟩ := h
  obtain ⟨p', q', r', hr', h'⟩ := h'
  unfold PI.UnitaryGroupMassFormula.UnimodLocStd.IsK
  refine ⟨p * p' - q * q' * e, p * q' + q * p' + q * q' * b, r * r', mul_ne_zero hr hr', ?_⟩
  push_cast
  linear_combination ((r' : ℂ) * t') * h + ((p : ℂ) + q * cmTheta b d) * h' - ((q : ℂ) * q') * hn

lemma isK_inv {t : ℂ} (h : IsK b d t) : IsK b d t⁻¹ := by
  by_cases ht : t = 0
  · rw [ht, inv_zero]
    simpa using PI.UnitaryGroupMassFormula.UnimodLocStd.isK_int (b := b) (d := d) 0
  obtain ⟨p, q, r, hr, h⟩ := h
  have hrt : (r : ℂ) * t ≠ 0 := mul_ne_zero (Int.cast_ne_zero.mpr hr) ht

  have hz : ((p ^ 2 + p * q * b + q ^ 2 * e : ℤ) : ℂ) =
      (r : ℂ) * t * (p + q * b - q * cmTheta b d) := by
    rw [h]
    push_cast
    linear_combination (-(q : ℂ) ^ 2) * hn
  unfold PI.UnitaryGroupMassFormula.UnimodLocStd.IsK
  by_cases hN : p ^ 2 + p * q * b + q ^ 2 * e = 0
  ·
    have hw : (p : ℂ) + q * b - q * cmTheta b d = 0 := by
      have h0 : (r : ℂ) * t * (p + q * b - q * cmTheta b d) = 0 := by
        rw [← hz, hN, Int.cast_zero]
      exact (mul_eq_zero.mp h0).resolve_left hrt
    have hk : (r : ℂ) * t = ((2 * p + q * b : ℤ) : ℂ) := by
      rw [h]
      push_cast
      linear_combination -hw
    have hk0 : (2 * p + q * b : ℤ) ≠ 0 := by
      intro h0
      rw [h0, Int.cast_zero] at hk
      exact hrt hk
    refine ⟨r, 0, 2 * p + q * b, hk0, ?_⟩
    rw [← hk, mul_inv_cancel_right₀ ht]
    simp
  · refine ⟨r * (p + q * b), -(r * q), p ^ 2 + p * q * b + q ^ 2 * e, hN, ?_⟩
    rw [hz]
    field_simp
    push_cast
    ring

lemma isK_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ) (hf : ∀ i ∈ s, IsK b d (f i)) : IsK b d (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PI.UnitaryGroupMassFormula.UnimodLocStd.isK_int (b := b) (d := d) 0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact PI.UnitaryGroupMassFormula.UnimodLocStd.isK_add (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

end IsKsec

end PI.UnitaryGroupMassFormula.UnimodLocStd
end
end

section

noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

section QR
variable {V : Type*} [AddCommGroup V] [Module ℂ V] (H : Sesq V)

def qmap (z : V) (ν : ℂ) : V →ₗ[ℂ] V := LinearMap.id - (ν • H.flip z).smulRight z

lemma qmap_apply (z : V) (ν : ℂ) (w : V) : qmap H z ν w = w - (ν * H w z) • z := by
  simp [qmap]

lemma qmap_coef {c h k : ℂ} (hc0 : c ≠ 0) (hc : c + conj c = k) :
    c⁻¹ * h + (conj c)⁻¹ * (h - c⁻¹ * h * k) = 0 := by
  subst hc
  have hc1 : conj c ≠ 0 := by simpa using hc0
  field_simp
  ring

lemma qmap_qmap {z : V} {c : ℂ} (hc0 : c ≠ 0) (hc : c + conj c = H z z) (w : V) :
    qmap H z (conj c)⁻¹ (qmap H z c⁻¹ w) = w := by
  rw [qmap_apply, qmap_apply]
  have e : H (w - (c⁻¹ * H w z) • z) z = H w z - c⁻¹ * H w z * H z z := by
    simp [map_sub, map_smul, mul_assoc]
  rw [e, sub_sub, ← add_smul, qmap_coef hc0 hc, zero_smul, sub_zero]

lemma qmap_qmap' {z : V} {c : ℂ} (hc0 : c ≠ 0) (hc : c + conj c = H z z) (w : V) :
    qmap H z c⁻¹ (qmap H z (conj c)⁻¹ w) = w := by
  have h1 := qmap_qmap H (c := conj c) (by simpa using hc0) (by rw [Complex.conj_conj, add_comm]; exact hc) w
  rwa [Complex.conj_conj] at h1

def qequiv (z : V) {c : ℂ} (hc0 : c ≠ 0) (hc : c + conj c = H z z) : V ≃ₗ[ℂ] V :=
  LinearEquiv.ofLinear (qmap H z c⁻¹) (qmap H z (conj c)⁻¹)
    (LinearMap.ext fun w => qmap_qmap' H hc0 hc w) (LinearMap.ext fun w => qmap_qmap H hc0 hc w)

lemma qequiv_apply (z : V) {c : ℂ} (hc0 : c ≠ 0) (hc : c + conj c = H z z) (w : V) :
    qequiv H z hc0 hc w = w - (c⁻¹ * H w z) • z := by
  show qmap H z c⁻¹ w = _
  exact qmap_apply H z c⁻¹ w

lemma qequiv_isom (hsym : ∀ x y, H y x = conj (H x y)) (z : V) {c : ℂ} (hc0 : c ≠ 0)
    (hc : c + conj c = H z z) : IsIsom H H (qequiv H z hc0 hc : V →ₗ[ℂ] V) := by
  intro x y
  have hc1 : conj c ≠ 0 := by simpa using hc0
  simp only [LinearEquiv.coe_coe]
  rw [qequiv_apply, qequiv_apply]
  simp only [map_sub, map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, map_mul, map_inv₀,
    RingHom.id_apply, hsym y z, ← hc]
  field_simp
  ring

end QR

end PI.UnitaryGroupMassFormula.UnimodLocStd
end
end

section

noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

def SatMem {m : Type*} (l : ℕ) (Λ : AddSubgroup (m → ℂ)) (x : m → ℂ) : Prop := ∃ n : ℕ, ¬ l ∣ n ∧ n • x ∈ Λ

def KeyRep : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0), CmOK a b c d →
    ∀ (m : Type) [Fintype m] [DecidableEq m] (Λ : AddSubgroup (m → ℂ)),
      IsSelfDual (stdH (cmL a b d ha hd lam hlam) m) Λ →
      (∀ x ∈ Λ, cmTheta b d • x ∈ Λ) →
      relIdx (stdLat (cmL a b d ha hd lam hlam) m) Λ ≠ 0 →
      relIdx Λ (stdLat (cmL a b d ha hd lam hlam) m) ≠ 0 →
      ∀ l : ℕ, l.Prime → ∀ x y : ℤ, ¬ (l : ℤ) ∣ a * x ^ 2 + b * x * y + c * y ^ 2 →
      ∀ (T : Finset m) (i₀ : m), i₀ ∉ T →
        (∀ j ∈ T, SatMem l Λ (Pi.single j (lam * ((x * a : ℂ) + y * cmTheta b d)))) →
        ∃ v : m → ℂ, SatMem l Λ v ∧ (∀ j ∈ T, v j = 0) ∧
          stdH (cmL a b d ha hd lam hlam) m v v =
            stdH (cmL a b d ha hd lam hlam) m (Pi.single i₀ (lam * ((x * a : ℂ) + y * cmTheta b d)))
              (Pi.single i₀ (lam * ((x * a : ℂ) + y * cmTheta b d)))

end PI.UnitaryGroupMassFormula.UnimodLocStd
end
end

section

noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

def StepB : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0), CmOK a b c d →
    ∀ (m : Type) [Fintype m] [DecidableEq m] (Λa : AddSubgroup (m → ℂ)),
      IsSelfDual (stdH (cmL a b d ha hd lam hlam) m) Λa →
      (∀ x ∈ Λa, cmTheta b d • x ∈ Λa) →
      relIdx (stdLat (cmL a b d ha hd lam hlam) m) Λa ≠ 0 →
      relIdx Λa (stdLat (cmL a b d ha hd lam hlam) m) ≠ 0 →
      ∀ l : ℕ, l.Prime → ∃ g : (m → ℂ) ≃ₗ[ℂ] (m → ℂ),
        IsIsom (stdH (cmL a b d ha hd lam hlam) m) (stdH (cmL a b d ha hd lam hlam) m)
          (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) ∧
        relIdx (stdLat (cmL a b d ha hd lam hlam) m) (imgLat (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa) ≠ 0 ∧
        ¬ l ∣ relIdx (stdLat (cmL a b d ha hd lam hlam) m) (imgLat (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa) ∧
        relIdx (imgLat (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa) (stdLat (cmL a b d ha hd lam hlam) m) ≠ 0

def StepC : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0), CmOK a b c d →
    ∀ (m : Type) [Fintype m] [DecidableEq m] (Λa : AddSubgroup (m → ℂ)) (g : (m → ℂ) ≃ₗ[ℂ] (m → ℂ)),
      (∀ x ∈ Λa, cmTheta b d • x ∈ Λa) →
      ∀ l : ℕ, l.Prime →
      IsIsom (stdH (cmL a b d ha hd lam hlam) m) (stdH (cmL a b d ha hd lam hlam) m)
          (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) →
        relIdx (stdLat (cmL a b d ha hd lam hlam) m) (imgLat (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa) ≠ 0 →
        ¬ l ∣ relIdx (stdLat (cmL a b d ha hd lam hlam) m) (imgLat (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa) →
        relIdx (imgLat (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa) (stdLat (cmL a b d ha hd lam hlam) m) ≠ 0 →
      ∃ δ : (m → ℂ) ≃ₗ[ℂ] (m → ℂ),
        IsIsom (stdH (cmL a b d ha hd lam hlam) m) (stdH (cmL a b d ha hd lam hlam) m)
          (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) ∧ (∀ x, δ x = x → x = 0) ∧
        relIdx (stdLat (cmL a b d ha hd lam hlam) m) (imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa) ≠ 0 ∧
        ¬ l ∣ relIdx (stdLat (cmL a b d ha hd lam hlam) m) (imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa) ∧
        relIdx (imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa) (stdLat (cmL a b d ha hd lam hlam) m) ≠ 0

theorem target_of (hB : StepB) (hC : StepC) : PI.UnimodLocStd := by
  intro a b c d ha hd lam hlam hok m _ _ Λa hsd hθ h1 h2 l hl
  obtain ⟨g, hg, g1, g2, g3⟩ := hB a b c d ha hd lam hlam hok m Λa hsd hθ h1 h2 l hl
  exact hC a b c d ha hd lam hlam hok m Λa g hθ l hl hg g1 g2 g3

end PI.UnitaryGroupMassFormula.UnimodLocStd
end
end

section

noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

section Helpers

theorem rep_H_nsmul (L : PeriodPair) (m : Type) [Fintype m] [DecidableEq m] (M : ℕ) (z : m → ℂ) :
    stdH L m (M • z) (M • z) = (M : ℂ) ^ 2 * stdH L m z z := by
  simp only [map_nsmul, LinearMap.smul_apply]
  simp only [nsmul_eq_mul]
  ring

end Helpers

end PI.UnitaryGroupMassFormula.UnimodLocStd
end
end
