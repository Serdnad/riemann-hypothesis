module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsIsoTermComparisonRestrictScalars
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle158
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle233
public import Mathlib.RingTheory.RingHom.Etale
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle239
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
public import Mathlib.LinearAlgebra.ExteriorAlgebra.OfAlternating
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
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

open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI

theorem exists_isPhi : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι] (p : ℕ) [Fact p.Prime] [CharP K p] (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) (f : ι → V →+ V) (h : ι → ι → V →+ K), IsDatum p d f h → ∃ Φ, IsPhi p f h Φ := by
  intro K _ V _ _ ι _ p _ _ d f h hD
  have lopAddV : ∀ (x x' : V) (y : Finset ι → ExteriorAlgebra K V),
      Lop f h (x + x') y = Lop f h x y + Lop f h x' y := by
    intro x x' y
    funext t
    simp only [Lop, Pi.add_apply]
    split_ifs <;> simp only [map_add (f := _), add_mul, smul_add, add_smul, add_zero] <;> abel
  have lopAddY : ∀ (x : V) (y y' : Finset ι → ExteriorAlgebra K V),
      Lop f h x (y + y') = Lop f h x y + Lop f h x y' := by
    intro x y y'
    funext t
    simp only [Lop, Pi.add_apply]
    split_ifs <;> simp only [mul_add, smul_add, add_zero] <;> abel
  have lopSmulV : ∀ (c : K) (x : V) (y : Finset ι → ExteriorAlgebra K V),
      Lop f h (c • x) y = c ^ p • Lop f h x y := by
    intro c x y
    funext t
    simp only [Lop, Pi.smul_apply]
    split_ifs <;>
      simp only [hD.f_smul, hD.h_smul, map_smul, smul_mul_assoc, mul_smul, smul_add, smul_zero,
        smul_comm ((-1 : ℤ) ^ t.card) (c ^ p)]
  have lopSmulY : ∀ (k : K) (x : V) (y : Finset ι → ExteriorAlgebra K V),
      Lop f h x (k • y) = k • Lop f h x y := by
    intro k x y
    funext t
    simp only [Lop, Pi.smul_apply]
    split_ifs <;>
      simp only [mul_smul_comm, smul_add, smul_zero, smul_comm ((-1 : ℤ) ^ t.card) k, smul_comm _ k]
  have hcons : ∀ (x : V) (l : List V), prodL f h (x :: l) = Lop f h x (prodL f h l) := fun _ _ => rfl
  have hupd0 : ∀ {a : ℕ} (v : Fin (a + 1) → V) (z : V),
      (fun k : Fin a => Function.update v 0 z k.succ) = fun k => v k.succ := by
    intro a v z
    funext k
    exact Function.update_of_ne (Fin.succ_ne_zero k) _ _
  have hupds : ∀ {a : ℕ} (v : Fin (a + 1) → V) (j : Fin a) (z : V),
      (fun k : Fin a => Function.update v j.succ z k.succ) = Function.update (fun k => v k.succ) j z := by
    intro a v j z
    funext k
    by_cases hk : k = j
    · subst hk
      simp
    · rw [Function.update_of_ne hk, Function.update_of_ne (fun e => hk (Fin.succ_injective _ e))]
  have hPadd : ∀ (a : ℕ) (v : Fin a → V) (i : Fin a) (x x' : V),
      prodL f h (List.ofFn (Function.update v i (x + x'))) =
        prodL f h (List.ofFn (Function.update v i x)) + prodL f h (List.ofFn (Function.update v i x')) := by
    intro a
    induction a with
    | zero => intro v i; exact i.elim0
    | succ a ih =>
      intro v i x x'
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
      · simp only [List.ofFn_succ, hcons, Function.update_self, hupd0]
        exact lopAddV _ _ _
      · simp only [List.ofFn_succ, hcons, hupds,
          Function.update_of_ne (Fin.succ_ne_zero j).symm]
        rw [ih, lopAddY]
  have hPsmul : ∀ (a : ℕ) (v : Fin a → V) (i : Fin a) (c : K) (x : V),
      prodL f h (List.ofFn (Function.update v i (c • x))) =
        c ^ p • prodL f h (List.ofFn (Function.update v i x)) := by
    intro a
    induction a with
    | zero => intro v i; exact i.elim0
    | succ a ih =>
      intro v i c x
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
      · simp only [List.ofFn_succ, hcons, Function.update_self, hupd0]
        exact lopSmulV _ _ _
      · simp only [List.ofFn_succ, hcons, hupds,
          Function.update_of_ne (Fin.succ_ne_zero j).symm]
        rw [ih, lopSmulY]
  have key : ∃ Φ : ExteriorAlgebra K V →+ (Finset ι → ExteriorAlgebra K V),
      (∀ (c : K) (x : ExteriorAlgebra K V), Φ (c • x) = c ^ p • Φ x) ∧
        ∀ (a : ℕ) (v : Fin a → V), Φ (ExteriorAlgebra.ιMulti K a v) = alt f h a v := by
    letI tw : Module K (Finset ι → ExteriorAlgebra K V) := Module.compHom _ (frobenius K p)
    let P : ∀ a : ℕ, (Fin a → V) →ₘₗ[K] (Finset ι → ExteriorAlgebra K V) := fun a =>
      { toFun := fun v => prodL f h (List.ofFn v)
        map_update_add' := fun v i x x' => by
          obtain rfl : ‹DecidableEq (Fin a)› = instDecidableEqFin a := Subsingleton.elim _ _
          exact hPadd a v i x x'
        map_update_smul' := fun v i c x => by
          obtain rfl : ‹DecidableEq (Fin a)› = instDecidableEqFin a := Subsingleton.elim _ _
          exact hPsmul a v i c x }
    let A : ∀ a : ℕ, V [⋀^Fin a]→ₗ[K] (Finset ι → ExteriorAlgebra K V) := fun a =>
      MultilinearMap.alternatization (P a)
    let Φ0 := ExteriorAlgebra.liftAlternating (R := K) A
    refine ⟨Φ0.toAddMonoidHom, fun c x => ?_, fun a v => ?_⟩
    · exact Φ0.map_smul c x
    · show Φ0 (ExteriorAlgebra.ιMulti K a v) = _
      rw [ExteriorAlgebra.liftAlternating_apply_ιMulti]
      show (MultilinearMap.alternatization (P a)) v = alt f h a v
      rw [MultilinearMap.alternatization_apply]
      unfold alt
      apply Finset.sum_congr rfl
      intro σ _
      rw [Units.smul_def]
      rfl
  obtain ⟨Φ, h1, h2⟩ := key
  exact ⟨Φ, fun c a v => by rw [h1, h2]⟩

end GlobalTheory.DI
end

section

set_option autoImplicit false

noncomputable section

open MvPolynomial

namespace GlobalTheory.DI

section FrobDiff

variable {K : Type} [CommRing K]

theorem kaehlerD_aeval_fin_two (x : Fin 2 → K) (P : MvPolynomial (Fin 2) ℤ) :
    KaehlerDifferential.D ℤ K (aeval x P) =
      ∑ i, aeval x (pderiv i P) • KaehlerDifferential.D ℤ K (x i) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ => simp [hP, hQ, add_smul, Finset.sum_add_distrib]
  | mul_X P i hP =>
    simp only [map_mul, aeval_X, Derivation.leibniz, hP, Finset.smul_sum, smul_smul,
      Derivation.leibniz, pderiv_X, Fin.sum_univ_two]
    fin_cases i <;> simp [add_smul, mul_comm, smul_smul, Pi.single_apply] <;> abel

theorem ringHom_aeval_fin_two {Kt : Type} [CommRing Kt] (π : Kt →+* K) (x : Fin 2 → Kt)
    (P : MvPolynomial (Fin 2) ℤ) : π (aeval x P) = aeval (fun i => π (x i)) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P j hP => simp [hP]

variable {Kt : Type} [CommRing Kt] (p : ℕ) [hp : Fact p.Prime] [CharP K p] (π : Kt →+* K) (F : Kt →+* Kt)

theorem frobLift_exists_w (hL : IsFlatLift p π) (hF : IsFrob p π F) (z : Kt) :
    ∃ w, F z = z ^ p + p * w := by
  obtain ⟨w, hw⟩ := (hL.ker (F z - z ^ p)).1 (by rw [map_sub, hF, map_pow, sub_self])
  exact ⟨w, by rw [← hw]; ring⟩

theorem frobLift_w_unique (hL : IsFlatLift p π) {z w w' : Kt} (h : F z = z ^ p + p * w)
    (h' : F z = z ^ p + p * w') : π w = π w' := by
  have e : (p : Kt) * (w - w') = 0 := by
    have := h.symm.trans h'
    rw [mul_sub, sub_eq_zero]
    exact add_left_cancel this
  have e2 := (hL.ann _).mp e
  rwa [map_sub, sub_eq_zero] at e2

theorem kaehlerD_pow_char (x : K) : KaehlerDifferential.D ℤ K (x ^ p) = 0 := by
  rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero, zero_smul]

def frobLiftPsi (hL : IsFlatLift p π) (hF : IsFrob p π F) (z : Kt) : Ω[K⁄ℤ] :=
  π z ^ (p - 1) • KaehlerDifferential.D ℤ K (π z) +
    KaehlerDifferential.D ℤ K (π (frobLift_exists_w p π F hL hF z).choose)

variable {p π F}

theorem frobLiftPsi_spec (hL : IsFlatLift p π) (hF : IsFrob p π F) {z w : Kt}
    (h : F z = z ^ p + p * w) :
    frobLiftPsi p π F hL hF z = π z ^ (p - 1) • KaehlerDifferential.D ℤ K (π z) +
      KaehlerDifferential.D ℤ K (π w) := by
  unfold frobLiftPsi
  rw [frobLift_w_unique p π F hL (frobLift_exists_w p π F hL hF z).choose_spec h]

theorem frobLiftPsi_add (hL : IsFlatLift p π) (hF : IsFrob p π F) (z z' : Kt) :
    frobLiftPsi p π F hL hF (z + z') = frobLiftPsi p π F hL hF z + frobLiftPsi p π F hL hF z' := by
  obtain ⟨w, hw⟩ := frobLift_exists_w p π F hL hF z
  obtain ⟨w', hw'⟩ := frobLift_exists_w p π F hL hF z'
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp.out (X 0 : MvPolynomial (Fin 2) ℤ) (X 1)
  have hp0 : (p : MvPolynomial (Fin 2) ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  obtain ⟨C, hC0⟩ : ∃ C : MvPolynomial (Fin 2) ℤ,
      (p : MvPolynomial (Fin 2) ℤ) * C = (X 0 + X 1) ^ p - X 0 ^ p - X 1 ^ p :=
    ⟨X 0 * X 1 * r, by rw [hr]; ring⟩
  have hpd0 : pderiv 0 C = (X 0 + X 1) ^ (p - 1) - X 0 ^ (p - 1) := by
    have := congrArg (pderiv 0) hC0
    simp [Derivation.leibniz_pow] at this
    exact mul_left_cancel₀ hp0 (by rw [this]; ring)
  have hpd1 : pderiv 1 C = (X 0 + X 1) ^ (p - 1) - X 1 ^ (p - 1) := by
    have := congrArg (pderiv 1) hC0
    simp [Derivation.leibniz_pow] at this
    exact mul_left_cancel₀ hp0 (by rw [this]; ring)
  have hc : (z + z') ^ p = z ^ p + z' ^ p + p * aeval ![z, z'] C := by
    have := congrArg (aeval ![z, z']) hC0
    simp at this
    rw [this]
    ring
  rw [frobLiftPsi_spec hL hF hw, frobLiftPsi_spec hL hF hw',
    frobLiftPsi_spec hL hF (w := w + w' - aeval ![z, z'] C) (by rw [map_add (f := _), hw, hw', hc]; ring)]
  have hD : KaehlerDifferential.D ℤ K (π (aeval ![z, z'] C)) =
      ((π z + π z') ^ (p - 1) - π z ^ (p - 1)) • KaehlerDifferential.D ℤ K (π z) +
      ((π z + π z') ^ (p - 1) - π z' ^ (p - 1)) • KaehlerDifferential.D ℤ K (π z') := by
    rw [ringHom_aeval_fin_two, kaehlerD_aeval_fin_two, Fin.sum_univ_two, hpd0, hpd1]
    simp
  simp only [map_add (f := _), map_sub, hD, smul_add, sub_smul]
  abel

theorem frobLiftPsi_mul (hL : IsFlatLift p π) (hF : IsFrob p π F) (z z' : Kt) :
    frobLiftPsi p π F hL hF (z * z') =
      π z ^ p • frobLiftPsi p π F hL hF z' + π z' ^ p • frobLiftPsi p π F hL hF z := by
  obtain ⟨w, hw⟩ := frobLift_exists_w p π F hL hF z
  obtain ⟨w', hw'⟩ := frobLift_exists_w p π F hL hF z'
  have hp1 : 1 ≤ p := hp.out.one_lt.le
  have hpK : (p : K) = 0 := CharP.cast_eq_zero K p
  rw [frobLiftPsi_spec hL hF hw, frobLiftPsi_spec hL hF hw',
    frobLiftPsi_spec hL hF (w := w * z' ^ p + z ^ p * w' + p * w * w')
      (by rw [map_mul, hw, hw']; ring)]
  simp only [map_add (f := _), map_mul, map_pow, map_natCast, hpK, zero_mul, add_zero, Derivation.leibniz,
    kaehlerD_pow_char p, smul_zero, zero_add]
  have e1 : (π z * π z') ^ (p - 1) * π z = π z ^ p * π z' ^ (p - 1) := by
    rw [mul_pow, mul_right_comm, ← pow_succ, Nat.sub_add_cancel hp1]
  have e2 : (π z * π z') ^ (p - 1) * π z' = π z' ^ p * π z ^ (p - 1) := by
    rw [mul_pow, mul_assoc, ← pow_succ, Nat.sub_add_cancel hp1, mul_comm]
  simp only [smul_add, smul_smul, e1, e2]
  abel

theorem frobLiftPsi_natCast_mul (hL : IsFlatLift p π) (hF : IsFrob p π F) (y : Kt) :
    frobLiftPsi p π F hL hF ((p : Kt) * y) = 0 := by
  have hp1 : 1 ≤ p := hp.out.one_lt.le
  have hp2 : p - 1 ≠ 0 := by have := hp.out.two_le; omega
  have hpK : (p : K) = 0 := CharP.cast_eq_zero K p
  have e : (p : Kt) * (p : Kt) ^ (p - 1) = (p : Kt) ^ p := by
    rw [← pow_succ', Nat.sub_add_cancel hp1]
  rw [frobLiftPsi_spec hL hF (w := F y - (p : Kt) ^ (p - 1) * y ^ p)
    (by rw [map_mul, map_natCast, mul_pow]; linear_combination (y ^ p) * e)]
  simp [hpK, hF y, kaehlerD_pow_char p, zero_pow hp2]

theorem frobLiftPsi_congr (hL : IsFlatLift p π) (hF : IsFrob p π F) {z z' : Kt} (h : π z = π z') :
    frobLiftPsi p π F hL hF z = frobLiftPsi p π F hL hF z' := by
  obtain ⟨y, hy⟩ := (hL.ker (z - z')).1 (by rw [map_sub, h, sub_self])
  rw [show z = z' + (p : Kt) * y by rw [← hy]; ring, frobLiftPsi_add, frobLiftPsi_natCast_mul, add_zero]

def frobLiftPhi (hL : IsFlatLift p π) (hF : IsFrob p π F) : K →+ Ω[K⁄ℤ] where
  toFun a := frobLiftPsi p π F hL hF (Function.surjInv hL.surj a)
  map_zero' := by
    have h0 : frobLiftPsi p π F hL hF 0 = 0 := by
      have := frobLiftPsi_add hL hF (0 : Kt) 0
      rw [add_zero] at this
      exact left_eq_add.mp this
    rw [frobLiftPsi_congr hL hF (z' := 0) (by rw [Function.surjInv_eq hL.surj, map_zero]), h0]
  map_add' a b := by
    rw [← frobLiftPsi_add, frobLiftPsi_congr hL hF (z' := Function.surjInv hL.surj a + Function.surjInv hL.surj b)
      (by rw [map_add (f := _), Function.surjInv_eq hL.surj, Function.surjInv_eq hL.surj, Function.surjInv_eq hL.surj])]

theorem frobLiftPhi_apply (hL : IsFlatLift p π) (hF : IsFrob p π F) (z : Kt) :
    frobLiftPhi hL hF (π z) = frobLiftPsi p π F hL hF z :=
  frobLiftPsi_congr hL hF (Function.surjInv_eq hL.surj _)

theorem frobLiftPhi_mul (hL : IsFlatLift p π) (hF : IsFrob p π F) (a b : K) :
    frobLiftPhi hL hF (a * b) = a ^ p • frobLiftPhi hL hF b + b ^ p • frobLiftPhi hL hF a := by
  obtain ⟨z, rfl⟩ := hL.surj a
  obtain ⟨z', rfl⟩ := hL.surj b
  rw [← map_mul, frobLiftPhi_apply, frobLiftPhi_apply, frobLiftPhi_apply, frobLiftPsi_mul]

theorem exists_isF_of_flatLift : ∀ {K Kt : Type} [CommRing K] [CommRing Kt] (p : ℕ) [Fact p.Prime] [CharP K p]
    (π : Kt →+* K) (F : Kt →+* Kt), IsFlatLift p π → IsFrob p π F → ∃ f, IsF p π F f := by
  intro K Kt _ _ p _ _ π F hL hF
  have univ : ∀ (M : Type) [AddCommGroup M] [Module K M] (D' : K →+ M),
      (∀ a b, D' (a * b) = a • D' b + b • D' a) →
      ∃ g : Ω[K⁄ℤ] →+ M, (∀ a, g (KaehlerDifferential.D ℤ K a) = D' a) ∧
        ∀ (c : K) (v : Ω[K⁄ℤ]), g (c • v) = c • g v := by
    intro M _ _ D' hD'
    let Dv : Derivation ℤ K M := Derivation.mk' D'.toIntLinearMap hD'
    exact ⟨Dv.liftKaehlerDifferential.toAddMonoidHom,
      fun a => Dv.liftKaehlerDifferential_comp_D a,
      fun c v => Dv.liftKaehlerDifferential.map_smul c v⟩
  have hmul : ∀ a b : K, frobLiftPhi hL hF (a * b) =
      frobenius K p a • frobLiftPhi hL hF b + frobenius K p b • frobLiftPhi hL hF a := by
    intro a b
    rw [frobenius_def p a, frobenius_def p b]
    exact frobLiftPhi_mul hL hF a b
  obtain ⟨g, hg, hsm⟩ :=
    @univ (Ω[K⁄ℤ]) _ (Module.compHom _ (frobenius K p)) (frobLiftPhi hL hF) hmul
  refine ⟨g, ?_, ?_⟩
  · intro c v
    have h0 : g (c • v) = frobenius K p c • g v := hsm c v
    rw [frobenius_def p c] at h0
    exact h0
  · intro z w hzw
    have := hg (π z)
    rw [frobLiftPhi_apply, frobLiftPsi_spec hL hF hzw] at this
    exact this

end FrobDiff

end GlobalTheory.DI
end
end

section

open CategoryTheory Limits Filter GlobalTheory
theorem _root_.GlobalTheory.T.cech_complex_direct_limit : ∀ {ι : Type} [LinearOrder ι] [Fintype ι] (A : ℕ → Cube.{0} ι ℤ) (B : Cube.{0} ι ℤ) (μ : ∀ (j c d : ℕ), c + j = d → (A c ⟶ A d)) (ρ : ∀ c, A c ⟶ B), (∀ j c d h, μ j c d h ≫ ρ d = ρ c) → (∀ (j j' c d e : ℕ) (h : c + j = d) (h' : d + j' = e) (h'' : c + (j + j') = e), μ j c d h ≫ μ j' d e h' = μ (j + j') c e h'') → (∀ s : Finset ι, s.Nonempty → ∀ b : B.obj s, ∃ c, ∃ a : (A c).obj s, (ρ c).app s a = b) → (∀ s : Finset ι, s.Nonempty → ∀ c (a : (A c).obj s), (ρ c).app s a = 0 → ∃ j, (μ j c (c + j) rfl).app s a = 0) → ∀ n : ℕ, (∀ᶠ c in atTop, IsZero ((cechComplex (A c)).homology n)) → IsZero ((cechComplex B).homology n) := by
  first | exact @_root_.GlobalTheory.cechComplex_homology_isZero_of_colimit | exact _root_.GlobalTheory.cechComplex_homology_isZero_of_colimit | (intros; apply _root_.GlobalTheory.cechComplex_homology_isZero_of_colimit <;> assumption)
end

section

theorem _root_.GlobalTheory.T.associated_of_height_one_agree : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] {n : ℕ} (π : Fin n → R) (J : Finset (Fin n)) (a b : R), a ≠ 0 → b ≠ 0 → (∀ j ∈ J, IsUnit (π j) ∨ Prime (π j)) → (∀ j ∈ J, Prime (π j) → ¬ π j ∣ a ∧ ¬ π j ∣ b) → (∀ Q : Ideal R, Q.IsPrime → Q.height = 1 → (∀ j ∈ J, π j ∉ Q) → ∃ c d : R, c ∉ Q ∧ d ∉ Q ∧ a * d = b * c) → ∃ u : Rˣ, a = u * b := by
  first | exact @_root_.GlobalTheory.exists_unit_eq_mul_of_height_one_avoiding | exact _root_.GlobalTheory.exists_unit_eq_mul_of_height_one_avoiding | (intros; apply _root_.GlobalTheory.exists_unit_eq_mul_of_height_one_avoiding <;> assumption)
end

section

open scoped TensorProduct Polynomial
theorem _root_.GlobalTheory.T.etale_coordinates_differentials : ∀ (R B K : Type) [CommRing R] [CommRing B] [Field K] [Algebra R B] [Algebra B K] (d : ℕ) (t : Fin d → B), (MvPolynomial.eval₂Hom (algebraMap R B) t).Etale → Module.finrank K (K ⊗[B] Ω[B⁄R]) = d ∧ ∀ (ι : Type) (e : ι ↪ Fin d) (u : ι → Bˣ), (∀ i, algebraMap B K (t (e i)) = 0) → LinearIndependent K (fun i => (1 : K) ⊗ₜ[B] KaehlerDifferential.D R B ((u i : B) * t (e i))) := by
  first | exact @_root_.GlobalTheory.EtaleCoordRank.finrank_and_linearIndependent_D_unit_mul | exact _root_.GlobalTheory.EtaleCoordRank.finrank_and_linearIndependent_D_unit_mul | (intros; apply _root_.GlobalTheory.EtaleCoordRank.finrank_and_linearIndependent_D_unit_mul <;> assumption)
end
