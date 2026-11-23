module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.Bundle003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.Bundle004
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
public import Mathlib.RingTheory.DedekindDomain.PID
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

namespace PI.ScRefExists.Id

theorem idemLift : PI.ScRefExists.Sk.IdemLift :=
  idemLift_of_steps locIdem adOfLoc fixInt tenStep

end PI.ScRefExists.Id
end

section

noncomputable section

open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct nonZeroDivisors

namespace PI.ScRefExists.ApP

open PI.ScRefExists.Sk

abbrev Pz (p : ℕ) : Ideal ℤ := Ideal.span {(p : ℤ)}

theorem pz_prime {p : ℕ} (hp : p.Prime) : (Pz p).IsPrime := (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hp)

instance pz_isPrime (p : ℕ) [hp : Fact p.Prime] : (Pz p).IsPrime := pz_prime hp.out

theorem pz_ne_bot {p : ℕ} (hp : p.Prime) : Pz p ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]
  exact_mod_cast hp.ne_zero

theorem natCast_not_mem {p : ℕ} (hp : p.Prime) {s : ℕ} (hs : Nat.Coprime s p) : (s : ℤ) ∉ Pz p := by
  rw [Ideal.mem_span_singleton]
  intro h
  have h1 : p ∣ s := Int.natCast_dvd_natCast.mp h
  have h2 : p ∣ Nat.gcd s p := Nat.dvd_gcd h1 dvd_rfl
  rw [Nat.Coprime.gcd_eq_one hs] at h2
  exact hp.one_lt.ne' (Nat.dvd_one.mp h2)

variable (I : Formalism.MainNotions.S.AutInst)

private theorem mem_Ap_lemma (p : ℕ) (x : I.E) :
    x ∈ Ap I p ↔ ∃ s : ℕ, Nat.Coprime s p ∧ ∃ a : 𝓞 I.E, (s : I.E) * x = (a : I.E) :=
  Iff.rfl

private theorem coe_algebraMap_int_ringOfIntegers (n : ℤ) :
    ((algebraMap ℤ (𝓞 I.E) n : 𝓞 I.E) : I.E) = (n : I.E) := by
  rw [algebraMap_int_eq, eq_intCast]
  exact map_intCast (algebraMap (𝓞 I.E) I.E) n

theorem inv_mem {p : ℕ} (hp : p.Prime) {n : ℤ} (hn : ¬ (p : ℤ) ∣ n) : ((n : I.E))⁻¹ ∈ Ap I p := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn (dvd_zero _)
  have hE : (n : I.E) ≠ 0 := Int.cast_ne_zero.mpr hn0
  have hcop : Nat.Coprime n.natAbs p := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
    intro h
    exact hn (Int.natCast_dvd.mpr h)
  refine (mem_Ap_lemma I p _).mpr ⟨n.natAbs, hcop, ?_⟩
  rcases Int.natAbs_eq n with h | h
  · have h' : (n.natAbs : ℤ) = n := by linarith
    have e : (n.natAbs : I.E) = (n : I.E) := by rw [← Int.cast_natCast, h']
    exact ⟨1, by rw [e, mul_inv_cancel₀ hE]; simp⟩
  · have h' : (n.natAbs : ℤ) = -n := by linarith
    have e : (n.natAbs : I.E) = -(n : I.E) := by rw [← Int.cast_natCast, h', Int.cast_neg]
    exact ⟨-1, by rw [e, neg_mul, mul_inv_cancel₀ hE]; simp⟩

theorem isLoc {p : ℕ} [hpf : Fact p.Prime] :
    IsLocalization (Algebra.algebraMapSubmonoid (𝓞 I.E) (Pz p).primeCompl) (Ap I p) := by
  constructor
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨n, hn, rfl⟩ := hy
    have hnd : ¬ (p : ℤ) ∣ n := fun h => hn (Ideal.mem_span_singleton.mpr h)
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hnd (dvd_zero _)
    refine isUnit_iff_exists_inv.mpr ⟨⟨((n : I.E))⁻¹, inv_mem I hpf.out hnd⟩, ?_⟩
    apply Subtype.ext
    show ((algebraMap ℤ (𝓞 I.E) n : 𝓞 I.E) : I.E) * (n : I.E)⁻¹ = 1
    rw [coe_algebraMap_int_ringOfIntegers]
    exact mul_inv_cancel₀ (Int.cast_ne_zero.mpr hn0)
  · intro z
    obtain ⟨s, hs, a, ha⟩ := (mem_Ap_lemma I p z).mp z.2
    refine ⟨(a, ⟨_, Algebra.mem_algebraMapSubmonoid_of_mem
      (⟨(s : ℤ), natCast_not_mem hpf.out hs⟩ : (Pz p).primeCompl)⟩), ?_⟩
    apply Subtype.ext
    show (z : I.E) * ((algebraMap ℤ (𝓞 I.E) (s : ℤ) : 𝓞 I.E) : I.E) = (a : I.E)
    rw [coe_algebraMap_int_ringOfIntegers]
    push_cast
    linear_combination ha
  · intro x y h
    refine ⟨1, ?_⟩
    have h2 : (x : I.E) = y := by
      have h3 := congrArg (fun z : Ap I p => (z : I.E)) h
      exact h3
    have hxy : x = y := NumberField.RingOfIntegers.ext h2
    subst hxy
    rfl

private theorem algebraMapSubmonoid_primeCompl_le_nonZeroDivisors (p : ℕ) [Fact p.Prime] :
    Algebra.algebraMapSubmonoid (𝓞 I.E) (Pz p).primeCompl ≤ nonZeroDivisors (𝓞 I.E) := by
  rintro _ ⟨n, hn, rfl⟩
  apply mem_nonZeroDivisors_of_ne_zero
  intro h
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn (Pz p).zero_mem
  apply hn0
  have h2 := congrArg ((↑) : 𝓞 I.E → I.E) h
  rw [coe_algebraMap_int_ringOfIntegers] at h2
  simpa using h2

theorem isDedekind {p : ℕ} [Fact p.Prime] : IsDedekindDomain (Ap I p) := by
  haveI := isLoc I (p := p)
  exact IsLocalization.isDedekindDomain (𝓞 I.E) (algebraMapSubmonoid_primeCompl_le_nonZeroDivisors I p) (Ap I p)

theorem principal_ideal_ring_at_prime : ApPID := by
  intro I p hp
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := isLoc I (p := p)
  haveI := isDedekind I (p := p)
  exact IsDedekindDomain.isPrincipalIdealRing_localization_over_prime (𝓞 I.E) (Pz p) (pz_ne_bot hp)

end PI.ScRefExists.ApP

end
end

section

noncomputable section

open NumberField Formalism.MainNotions.S
open PI.ScRefExists.Sk
open Matrix

namespace PI.ScRefExists.WF

variable (I : Formalism.MainNotions.S.AutInst)

theorem hG_def (x y : Fin I.n → I.E) : hG I x y = ∑ i, ∑ j, star (x i) * I.J i j * y j := rfl

theorem hG_add_left (x y z : Fin I.n → I.E) : hG I (x + y) z = hG I x z + hG I y z := by
  simp only [hG_def, Pi.add_apply, star_add, add_mul, Finset.sum_add_distrib]

theorem hG_add_right (x y z : Fin I.n → I.E) : hG I x (y + z) = hG I x y + hG I x z := by
  simp only [hG_def, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hG_smul_left (c : I.E) (x y : Fin I.n → I.E) : hG I (c • x) y = star c * hG I x y := by
  simp only [hG_def, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hG_smul_right (c : I.E) (x y : Fin I.n → I.E) : hG I x (c • y) = c * hG I x y := by
  simp only [hG_def, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hG_zero_left (y : Fin I.n → I.E) : hG I 0 y = 0 := by
  simp [hG_def]

theorem hG_zero_right (x : Fin I.n → I.E) : hG I x 0 = 0 := by
  simp [hG_def]

theorem hG_neg_right (x y : Fin I.n → I.E) : hG I x (-y) = - hG I x y := by
  simp only [hG_def, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

theorem hG_sub_right (x y z : Fin I.n → I.E) : hG I x (y - z) = hG I x y - hG I x z := by
  rw [sub_eq_add_neg, hG_add_right, hG_neg_right, ← sub_eq_add_neg]

theorem hG_sum_right {ι : Type*} (s : Finset ι) (x : Fin I.n → I.E) (y : ι → Fin I.n → I.E) :
    hG I x (∑ t ∈ s, y t) = ∑ t ∈ s, hG I x (y t) := by
  exact map_sum (AddMonoidHom.mk' (hG I x) (hG_add_right I x)) y s

theorem J_entry (i j : Fin I.n) : star (I.J j i) = I.J i j := by
  have h : Formalism.UG.cT (starRingEnd I.E) I.J = I.J := I.J_herm
  have h2 := congrFun (congrFun h i) j
  simpa [Formalism.UG.cT, starRingEnd_apply] using h2

theorem hG_symm (x y : Fin I.n → I.E) : hG I y x = star (hG I x y) := by
  simp only [hG_def, star_sum, star_mul', star_star]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [J_entry I a b]
  ring

theorem hG_single (i : Fin I.n) (v : Fin I.n → I.E) :
    hG I (Pi.single i 1) v = (I.J *ᵥ v) i := by
  rw [hG_def, Finset.sum_eq_single i]
  · simp [Matrix.mulVec, dotProduct]
  · intro b _ hb
    simp [Pi.single_apply, hb]
  · simp

theorem hG_nondeg (v : Fin I.n → I.E) (h : ∀ x, hG I x v = 0) : v = 0 := by
  have h1 : I.J *ᵥ v = 0 := funext fun i => by
    rw [← hG_single I i v]
    exact h _
  exact Matrix.eq_zero_of_mulVec_eq_zero I.J_det h1

variable {I}

theorem mem_Ap {p : ℕ} {x : I.E} :
    x ∈ Ap I p ↔ ∃ s : ℕ, Nat.Coprime s p ∧ ∃ a : 𝓞 I.E, (s : I.E) * x = (a : I.E) := Iff.rfl

theorem inv_mem_Ap {p s : ℕ} (hp : p.Prime) (hs : Nat.Coprime s p) : ((s : I.E))⁻¹ ∈ Ap I p := by
  have hs0 : (s : I.E) ≠ 0 := by
    refine Nat.cast_ne_zero.mpr ?_
    rintro rfl
    rw [Nat.coprime_zero_left] at hs
    exact hp.one_lt.ne' hs
  exact mem_Ap.mpr ⟨s, hs, 1, by rw [mul_inv_cancel₀ hs0]; simp⟩

theorem star_mem_Ap {p : ℕ} {x : I.E} (hx : x ∈ Ap I p) : star x ∈ Ap I p := by
  obtain ⟨s, hs, a, ha⟩ := mem_Ap.mp hx
  have hint : IsIntegral ℤ (star (a : I.E)) := by
    have := map_isIntegral_int (starRingEnd I.E) (RingOfIntegers.isIntegral_coe a)
    simpa [starRingEnd_apply] using this
  refine mem_Ap.mpr ⟨s, hs, ⟨star (a : I.E), hint⟩, ?_⟩
  show (s : I.E) * star x = star (a : I.E)
  rw [← ha, star_mul', star_natCast]

end PI.ScRefExists.WF
end
end

section

noncomputable section

open NumberField Formalism.MainNotions.S IsDedekindDomain

namespace PI.ScRefExists.PPA

open PI.ScRefExists.Sk

variable (I : Formalism.MainNotions.S.AutInst)

theorem hG_add_left (x x' y : Fin I.n → I.E) : hG I (x + x') y = hG I x y + hG I x' y := by
  simp only [hG, Formalism.UG.hform, starRingEnd_apply, Pi.add_apply, star_add, add_mul, Finset.sum_add_distrib]

theorem hG_add_right (x y y' : Fin I.n → I.E) : hG I x (y + y') = hG I x y + hG I x y' := by
  simp only [hG, Formalism.UG.hform, starRingEnd_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hG_smul_left (c : I.E) (x y : Fin I.n → I.E) : hG I (c • x) y = star c * hG I x y := by
  simp only [hG, Formalism.UG.hform, starRingEnd_apply, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hG_smul_right (c : I.E) (x y : Fin I.n → I.E) : hG I x (c • y) = c * hG I x y := by
  simp only [hG, Formalism.UG.hform, starRingEnd_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hG_neg_left (x y : Fin I.n → I.E) : hG I (-x) y = -hG I x y := by
  simp only [hG, Formalism.UG.hform, starRingEnd_apply, Pi.neg_apply, star_neg, neg_mul, Finset.sum_neg_distrib]

theorem hG_neg_right (x y : Fin I.n → I.E) : hG I x (-y) = -hG I x y := by
  simp only [hG, Formalism.UG.hform, starRingEnd_apply, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

theorem hG_sub_left (x x' y : Fin I.n → I.E) : hG I (x - x') y = hG I x y - hG I x' y := by
  rw [sub_eq_add_neg, hG_add_left, hG_neg_left, ← sub_eq_add_neg]

theorem hG_sub_right (x y y' : Fin I.n → I.E) : hG I x (y - y') = hG I x y - hG I x y' := by
  rw [sub_eq_add_neg, hG_add_right, hG_neg_right, ← sub_eq_add_neg]

theorem hG_symm (x y : Fin I.n → I.E) : hG I y x = star (hG I x y) := by
  have hJ : ∀ a b, star (I.J b a) = I.J a b := by
    intro a b
    have h : Formalism.UG.cT (starRingEnd I.E) I.J = I.J := I.J_herm
    have h2 := congrFun (congrFun h a) b
    simpa [Formalism.UG.cT, starRingEnd_apply] using h2
  simp only [hG, Formalism.UG.hform, starRingEnd_apply, star_sum, star_mul', star_star]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hJ a b]
  ring

private theorem mem_Ap_lemma (p : ℕ) (x : I.E) :
    x ∈ Ap I p ↔ ∃ s : ℕ, Nat.Coprime s p ∧ ∃ a : 𝓞 I.E, (s : I.E) * x = (a : I.E) :=
  Iff.rfl

theorem int_mem_Ap (p : ℕ) (a : 𝓞 I.E) : (a : I.E) ∈ Ap I p := (mem_Ap_lemma I p _).mpr ⟨1, Nat.coprime_one_left p, a, by simp⟩

theorem natCast_smul_mem_L (s : ℕ) {x : Fin I.n → I.E} (hx : x ∈ I.L) : (s : I.E) • x ∈ I.L := by
  rw [Nat.cast_smul_eq_nsmul]
  exact nsmul_mem hx s

theorem oE_smul (a : 𝓞 I.E) (x : Fin I.n → I.E) : a • x = (a : I.E) • x := by
  ext i; simp [Algebra.smul_def]

theorem natE_smul (t : ℕ) (x : Fin I.n → I.E) : (t : I.E) • x = (t : 𝓞 I.E) • x := by
  rw [oE_smul]
  simp

theorem intE_smul_mem_L (a : 𝓞 I.E) {x : Fin I.n → I.E} (hx : x ∈ I.L) : (a : I.E) • x ∈ I.L := by
  rw [← oE_smul]
  exact I.L.smul_mem a hx

theorem LA_clear (p : ℕ) {v : Fin I.n → I.E} (hv : v ∈ LA I p) :
    ∃ s : ℕ, Nat.Coprime s p ∧ (s : I.E) • v ∈ I.L := by
  have hv' : v ∈ Submodule.span (Ap I p) (I.L : Set (Fin I.n → I.E)) := hv
  clear hv
  induction hv' using Submodule.span_induction with
  | mem x hx => exact ⟨1, Nat.coprime_one_left p, by simpa using hx⟩
  | zero => exact ⟨1, Nat.coprime_one_left p, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨t, ht, hty⟩ := hy
    refine ⟨s * t, Nat.Coprime.mul_left hs ht, ?_⟩
    have e : ((s * t : ℕ) : I.E) • (x + y) = (t : I.E) • ((s : I.E) • x) + (s : I.E) • ((t : I.E) • y) := by
      simp only [Nat.cast_mul, smul_add, smul_smul, mul_comm (t : I.E) (s : I.E)]
    rw [e]
    exact add_mem (natCast_smul_mem_L I t hsx) (natCast_smul_mem_L I s hty)
  | smul c x _ hx =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨s0, hs0, a, ha⟩ := (mem_Ap_lemma I p (c : I.E)).mp c.2
    refine ⟨s0 * s, Nat.Coprime.mul_left hs0 hs, ?_⟩
    have hc : c • x = (c : I.E) • x := rfl
    have e : ((s0 * s : ℕ) : I.E) • (c • x) = (a : I.E) • ((s : I.E) • x) := by
      rw [hc, smul_smul, smul_smul, ← ha]
      push_cast
      congr 1
      ring
    rw [e]
    exact intE_smul_mem_L I a hsx

theorem hG_mem_Ap (p : ℕ) {v v' : Fin I.n → I.E} (hv : v ∈ LA I p) (hv' : v' ∈ LA I p) :
    hG I v v' ∈ Ap I p := by
  obtain ⟨s, hs, hsv⟩ := LA_clear I p hv
  obtain ⟨t, ht, htv⟩ := LA_clear I p hv'
  obtain ⟨a, ha⟩ := RingHom.mem_range.mp ((I.L_dual _).mp htv _ hsv)
  have e : hG I ((s : I.E) • v) ((t : I.E) • v') = (s : I.E) * t * hG I v v' := by
    rw [hG_smul_left, hG_smul_right, star_natCast]
    ring
  refine (mem_Ap_lemma I p _).mpr ⟨s * t, Nat.Coprime.mul_left hs ht, a, ?_⟩
  rw [Nat.cast_mul, ← e]
  exact ha.symm

theorem span_clear (p : ℕ) (S : Set (Fin I.n → I.E)) {y : Fin I.n → I.E}
    (hy : y ∈ Submodule.span (Ap I p) S) :
    ∃ s : ℕ, Nat.Coprime s p ∧ (s : I.E) • y ∈ Submodule.span (𝓞 I.E) S := by
  have key : ∀ (a : 𝓞 I.E) {z : Fin I.n → I.E}, z ∈ Submodule.span (𝓞 I.E) S →
      (a : I.E) • z ∈ Submodule.span (𝓞 I.E) S := fun a z hz => by
    rw [← oE_smul]
    exact Submodule.smul_mem _ a hz
  have keyN : ∀ (t : ℕ) {z : Fin I.n → I.E}, z ∈ Submodule.span (𝓞 I.E) S →
      (t : I.E) • z ∈ Submodule.span (𝓞 I.E) S := fun t z hz => by
    rw [natE_smul]
    exact Submodule.smul_mem _ _ hz
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, Nat.coprime_one_left p, by simpa using Submodule.subset_span hx⟩
  | zero => exact ⟨1, Nat.coprime_one_left p, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨t, ht, hty⟩ := hy
    refine ⟨s * t, Nat.Coprime.mul_left hs ht, ?_⟩
    have e : ((s * t : ℕ) : I.E) • (x + y) = (t : I.E) • ((s : I.E) • x) + (s : I.E) • ((t : I.E) • y) := by
      simp only [Nat.cast_mul, smul_add, smul_smul, mul_comm (t : I.E) (s : I.E)]
    rw [e]
    exact add_mem (keyN t hsx) (keyN s hty)
  | smul c x _ hx =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨s0, hs0, a, ha⟩ := (mem_Ap_lemma I p (c : I.E)).mp c.2
    refine ⟨s0 * s, Nat.Coprime.mul_left hs0 hs, ?_⟩
    have hc : c • x = (c : I.E) • x := rfl
    have e : ((s0 * s : ℕ) : I.E) • (c • x) = (a : I.E) • ((s : I.E) • x) := by
      rw [hc, smul_smul, smul_smul, ← ha]
      push_cast
      congr 1
      ring
    rw [e]
    exact key a hsx

def QA (p q : ℕ) (x : I.E) : Prop := ∃ s : ℕ, Nat.Coprime s p ∧ ∃ a : 𝓞 I.E, (s : I.E) * x = (q : I.E) * a

theorem QA_of_GE (p q : ℕ) {x : I.E} (h : GE I q x) : QA I p q x := by
  obtain ⟨t, rfl⟩ := h
  exact ⟨1, Nat.coprime_one_left p, t, by simp⟩

theorem QA_add (p q : ℕ) {x y : I.E} (hx : QA I p q x) (hy : QA I p q y) : QA I p q (x + y) := by
  obtain ⟨s, hs, a, ha⟩ := hx
  obtain ⟨t, ht, b, hb⟩ := hy
  refine ⟨s * t, Nat.Coprime.mul_left hs ht, (t : 𝓞 I.E) * a + (s : 𝓞 I.E) * b, ?_⟩
  push_cast at ha hb ⊢
  linear_combination (t : I.E) * ha + (s : I.E) * hb

theorem QA_neg (p q : ℕ) {x : I.E} (hx : QA I p q x) : QA I p q (-x) := by
  obtain ⟨s, hs, a, ha⟩ := hx
  refine ⟨s, hs, -a, ?_⟩
  push_cast
  linear_combination -ha

theorem QA_sub (p q : ℕ) {x y : I.E} (hx : QA I p q x) (hy : QA I p q y) : QA I p q (x - y) := by
  rw [sub_eq_add_neg]
  exact QA_add I p q hx (QA_neg I p q hy)

theorem QA_mul (p q : ℕ) {c x : I.E} (hc : c ∈ Ap I p) (hx : QA I p q x) : QA I p q (c * x) := by
  obtain ⟨s, hs, a, ha⟩ := hx
  obtain ⟨s0, hs0, a0, ha0⟩ := (mem_Ap_lemma I p c).mp hc
  refine ⟨s0 * s, Nat.Coprime.mul_left hs0 hs, a0 * a, ?_⟩
  push_cast
  linear_combination ((s : I.E) * x) * ha0 + (a0 : I.E) * ha

theorem GE_of_QA (p m : ℕ) {x : I.E} (hint : ∃ a : 𝓞 I.E, (a : I.E) = x) (h : QA I p (p ^ m) x) :
    GE I (p ^ m) x := by
  obtain ⟨b, rfl⟩ := hint
  obtain ⟨s, hs, a, ha⟩ := h
  have hcop : Nat.Coprime s (p ^ m) := Nat.Coprime.pow_right m hs
  have hz : (s : ℤ) * Nat.gcdA s (p ^ m) + ((p ^ m : ℕ) : ℤ) * Nat.gcdB s (p ^ m) = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, Nat.Coprime.gcd_eq_one hcop]
    norm_num
  have hzE := congrArg (Int.cast : ℤ → I.E) hz
  push_cast at hzE ha
  refine ⟨(Nat.gcdA s (p ^ m) : 𝓞 I.E) * a + (Nat.gcdB s (p ^ m) : 𝓞 I.E) * b, ?_⟩
  have hA : (((Nat.gcdA s (p ^ m) : ℤ) : 𝓞 I.E) : I.E) = ((Nat.gcdA s (p ^ m) : ℤ) : I.E) :=
    map_intCast (algebraMap (𝓞 I.E) I.E) _
  have hB : (((Nat.gcdB s (p ^ m) : ℤ) : 𝓞 I.E) : I.E) = ((Nat.gcdB s (p ^ m) : ℤ) : I.E) :=
    map_intCast (algebraMap (𝓞 I.E) I.E) _
  push_cast
  linear_combination ((Nat.gcdA s (p ^ m) : ℤ) : I.E) * ha - (b : I.E) * hzE -
    (p : I.E) ^ m * (a : I.E) * hA - (b : I.E) * (p : I.E) ^ m * hB

end PI.ScRefExists.PPA
end
end
