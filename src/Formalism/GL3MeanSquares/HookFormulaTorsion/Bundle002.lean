module

public import Formalism.GL3MeanSquares.Bundle001
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
public import Mathlib.NumberTheory.NumberField.Norm
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

section

namespace Formalism.HermitianLattices.IntegralLatticeDensity

open Finset

theorem no_form_of_bidegree_one_one : PowerCongruenceIffEqual := by
  unfold PowerCongruenceIffEqual
  intro l d s s' hl hs hs' hdiv
  have h1 : l ^ s < l ^ d := Nat.pow_lt_pow_right (by omega) hs
  have h2 : l ^ s' < l ^ d := Nat.pow_lt_pow_right (by omega) hs'
  have h3 : 1 ≤ l ^ s := Nat.one_le_pow _ _ (by omega)
  have h4 : 1 ≤ l ^ s' := Nat.one_le_pow _ _ (by omega)
  have h5 : 1 ≤ l ^ d := Nat.one_le_pow _ _ (by omega)
  rw [Nat.cast_sub h5, Nat.cast_pow, Nat.cast_one] at hdiv
  have h1' : (l : ℤ) ^ s < (l : ℤ) ^ d := by exact_mod_cast h1
  have h2' : (l : ℤ) ^ s' < (l : ℤ) ^ d := by exact_mod_cast h2
  have h3' : (1 : ℤ) ≤ (l : ℤ) ^ s := by exact_mod_cast h3
  have h4' : (1 : ℤ) ≤ (l : ℤ) ^ s' := by exact_mod_cast h4
  have hz := Int.eq_zero_of_abs_lt_dvd hdiv (by rw [abs_lt]; constructor <;> linarith)
  have h6 : (l : ℤ) ^ s = (l : ℤ) ^ s' := by linarith
  have h7 : l ^ s = l ^ s' := by exact_mod_cast h6
  exact Nat.pow_right_injective hl h7

end Formalism.HermitianLattices.IntegralLatticeDensity
end

section

open DirichletCharacter

namespace Formalism.HermitianLattices.ThinSetIntegral

private lemma qc_ne_one (q : ℕ) [Fact q.Prime] (h2 : q ≠ 2) : Formalism.HermitianLattices.ZeroFreeRegionGL2.qc q ≠ 1 := by
  intro h
  apply quadraticChar_ne_one (F := ZMod q) (by rwa [ZMod.ringChar_zmod_n])
  refine MulChar.ext fun a => ?_
  have h1 := congrArg (fun χ : DirichletCharacter ℂ q => χ (a : ZMod q)) h
  simp only [Formalism.HermitianLattices.ZeroFreeRegionGL2.qc, MulChar.ringHomComp_apply, Int.coe_castRingHom,
    MulChar.one_apply_coe] at h1
  rw [MulChar.one_apply_coe]
  exact_mod_cast h1

private lemma qc_prim (q : ℕ) [Fact q.Prime] (h2 : q ≠ 2) : (Formalism.HermitianLattices.ZeroFreeRegionGL2.qc q).IsPrimitive := by
  have hd := conductor_dvd_level (Formalism.HermitianLattices.ZeroFreeRegionGL2.qc q)
  rcases (Nat.dvd_prime (Fact.out : q.Prime)).1 hd with h | h
  · exact absurd (eq_one_iff_conductor_eq_one.2 h) (qc_ne_one q h2)
  · exact h

private lemma qc_sq (q : ℕ) [Fact q.Prime] : Formalism.HermitianLattices.ZeroFreeRegionGL2.qc q ^ 2 = 1 := by
  refine MulChar.ext fun a => ?_
  rw [MulChar.pow_apply_coe, MulChar.one_apply_coe]
  simp only [Formalism.HermitianLattices.ZeroFreeRegionGL2.qc, MulChar.ringHomComp_apply, Int.coe_castRingHom]
  rw [← Int.cast_pow, quadraticChar_sq_one a.ne_zero, Int.cast_one]

private lemma prim_mul {N m n : ℕ} [NeZero N] (hm : m ∣ N) (hn : n ∣ N) (hco : m.Coprime n) (hN : N = m * n)
    (χ₁ : DirichletCharacter ℂ m) (χ₂ : DirichletCharacter ℂ n) (h1 : χ₁.IsPrimitive) (h2 : χ₂.IsPrimitive) :
    (changeLevel hm χ₁ * changeLevel hn χ₂).IsPrimitive := by
  have cA : (changeLevel hm χ₁).conductor = m := by rw [conductor_changeLevel]; exact h1
  have cB : (changeLevel hn χ₂).conductor = n := by rw [conductor_changeLevel]; exact h2
  generalize changeLevel hm χ₁ = A at *
  generalize changeLevel hn χ₂ = B at *
  have d1 : m ∣ (A * B).conductor.lcm n := by
    have h := conductor_mul_dvd_lcm_conductor (A * B) B⁻¹
    rwa [mul_inv_cancel_right, conductor_inv, cA, cB] at h
  have d2 : n ∣ (A * B).conductor.lcm m := by
    have h := conductor_mul_dvd_lcm_conductor (B * A) A⁻¹
    rwa [mul_inv_cancel_right, conductor_inv, cA, cB, mul_comm B A] at h
  have e1 : m ∣ (A * B).conductor :=
    hco.dvd_of_dvd_mul_right (d1.trans (Nat.lcm_dvd_mul _ _))
  have e2 : n ∣ (A * B).conductor :=
    hco.symm.dvd_of_dvd_mul_right (d2.trans (Nat.lcm_dvd_mul _ _))
  rw [isPrimitive_def]
  have e3 : N ∣ (A * B).conductor := by
    have h := hco.mul_dvd_of_dvd_of_dvd e1 e2
    rwa [← hN] at h
  exact Nat.dvd_antisymm (conductor_dvd_level _) e3

private lemma chi_eight_sq : Formalism.HermitianLattices.ZeroFreeRegionGL2.chi8 ^ 2 = 1 := by
  refine MulChar.ext fun a => ?_
  rw [MulChar.pow_apply_coe, MulChar.one_apply_coe]
  simp only [Formalism.HermitianLattices.ZeroFreeRegionGL2.chi8, MulChar.ringHomComp_apply, Int.coe_castRingHom]
  have hu : IsUnit (ZMod.χ₈ (a : ZMod 8)) := by
    rw [← MulChar.coe_toUnitHom]
    exact Units.isUnit _
  rcases ZMod.isQuadratic_χ₈ (a : ZMod 8) with h | h | h
  · rw [h] at hu
    exact absurd hu not_isUnit_zero
  · rw [h]
    norm_num
  · rw [h]
    norm_num

private lemma chi_eight_primitive : Formalism.HermitianLattices.ZeroFreeRegionGL2.chi8.IsPrimitive := by
  rw [isPrimitive_def]
  by_contra hne
  have hd := conductor_dvd_level Formalism.HermitianLattices.ZeroFreeRegionGL2.chi8
  have h4 : Formalism.HermitianLattices.ZeroFreeRegionGL2.chi8.conductor ∣ 4 := by
    have hle : Formalism.HermitianLattices.ZeroFreeRegionGL2.chi8.conductor ≤ 8 := Nat.le_of_dvd (by norm_num) hd
    generalize Formalism.HermitianLattices.ZeroFreeRegionGL2.chi8.conductor = k at *
    interval_cases k <;> omega
  obtain ⟨hd4, χ₀, h0⟩ : Formalism.HermitianLattices.ZeroFreeRegionGL2.chi8.FactorsThrough 4 :=
    (mem_conductorSet_iff_conductor_dvd _ (by norm_num)).2 h4
  have h5 : changeLevel hd4 χ₀ ((5 : ℤ) : ZMod 8) = χ₀ ((5 : ℤ) : ZMod 4) :=
    changeLevel_eq_cast_of_dvd' χ₀ hd4 (by
      rw [Int.isCoprime_iff_gcd_eq_one]; decide)
  rw [← h0] at h5
  have h6 : ((5 : ℤ) : ZMod 4) = 1 := by decide
  have h7 : ZMod.χ₈ ((5 : ℤ) : ZMod 8) = -1 := by decide
  rw [h6, map_one, Formalism.HermitianLattices.ZeroFreeRegionGL2.chi8, MulChar.ringHomComp_apply, h7] at h5
  norm_num at h5

theorem twist_is_primitive_character : Formalism.HermitianLattices.ZeroFreeRegionGL2.TwPrimitive := by
  refine ⟨⟨chi_eight_primitive, chi_eight_sq⟩, ?_⟩
  intro t θ q _ hθ h2 hco
  have hq : q.Prime := Fact.out
  have ht : t ≠ 0 := by
    rintro rfl
    rw [Nat.coprime_zero_right] at hco
    exact hq.one_lt.ne' hco
  have : NeZero t := ⟨ht⟩
  have hp : (Formalism.HermitianLattices.ZeroFreeRegionGL2.tw θ q).IsPrimitive :=
    prim_mul _ _ hco.symm rfl θ (Formalism.HermitianLattices.ZeroFreeRegionGL2.qc q) hθ (qc_prim q h2)
  refine ⟨hp, ?_, ?_⟩
  · intro h1
    rw [isPrimitive_def, h1, conductor_one] at hp
    have h3 : 2 ≤ q := hq.two_le
    have h4 : 1 ≤ t := Nat.pos_of_ne_zero ht
    nlinarith
  · intro hs
    rw [Formalism.HermitianLattices.ZeroFreeRegionGL2.tw, mul_pow, ← map_pow, ← map_pow, hs, qc_sq, map_one, map_one, one_mul]

end Formalism.HermitianLattices.ThinSetIntegral
end

section

namespace Formalism.HermitianLattices.IntegralLatticeDensity

open Finset

theorem integer_mean_log_bound : IntegerMeanLog := by
  intro K _ _ x hx
  have hx' : (x : K) ≠ 0 := by exact_mod_cast hx
  have hne : ∀ φ : K →+* ℂ, ‖φ (x : K)‖ ≠ 0 := fun φ => by
    rw [norm_ne_zero_iff]
    exact (map_ne_zero φ).mpr hx'
  rw [← Real.log_prod (fun φ _ => hne φ)]
  apply Real.log_nonneg
  rw [← norm_prod]
  have key : (∏ φ : K →+* ℂ, φ (x : K)) = algebraMap ℚ ℂ (Algebra.norm ℚ (x : K)) := by
    rw [Algebra.norm_eq_prod_embeddings ℚ ℂ]
    exact Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) _ _ (fun φ => rfl)
  rw [key, ← Algebra.coe_norm_int x]
  have hN0 : Algebra.norm ℤ x ≠ 0 := by
    intro h0
    have h5 : Algebra.norm ℚ (x : K) ≠ 0 := Algebra.norm_ne_zero_iff.mpr hx'
    apply h5
    rw [← Algebra.coe_norm_int x, h0, Int.cast_zero]
  rw [eq_ratCast, Rat.cast_intCast, Complex.norm_intCast]
  exact_mod_cast Int.one_le_abs hN0

theorem weber_function_root : WeberRoot := by
  intro x j s hs hj hx
  have hs0 : (s : ℂ) ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
  refine ⟨?_, ?_⟩
  · let R := integralClosure ℤ ℂ
    let jR : R := ⟨j, hj⟩
    let q : Polynomial R := (Polynomial.X - Polynomial.C (s : R)) ^ 3 - Polynomial.C jR * Polynomial.X
    have hq : q.Monic := by
      apply Polynomial.Monic.sub_of_left ((Polynomial.monic_X_sub_C _).pow 3)
      rw [Polynomial.degree_pow, Polynomial.degree_X_sub_C]
      refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_le _) ?_
      norm_num
    have hxR : IsIntegral R x := by
      refine ⟨q, hq, ?_⟩
      simp only [q, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_C, Polynomial.eval₂_mul]
      simp only [map_intCast]
      have hjR : algebraMap R ℂ jR = j := rfl
      rw [hjR]
      linear_combination hx
    exact isIntegral_trans x hxR
  · intro h
    rw [h] at hx
    apply hs0
    have h3 : (s : ℂ) ^ 3 = 0 := by linear_combination -hx
    exact (pow_eq_zero_iff (by norm_num)).mp h3

end Formalism.HermitianLattices.IntegralLatticeDensity
end

section

namespace Formalism.HermitianLattices.IntegralLatticeDensity.PD

open Finset Formalism.HermitianLattices.IntegralLatticeDensity

section calculus

variable {M Q : Type} [AddCommGroup M] [AddCommGroup Q] {φ : M → Q}

theorem cob_symm' (a b : M) : cob φ a b = cob φ b a := by
  simp only [cob]
  rw [add_comm a b]
  abel

theorem phi_add' (a b : M) : φ (a + b) = φ a + φ b + cob φ a b := by
  simp only [cob]
  abel

theorem cob_add_right' (h1 : ∀ a a' b, cob φ (a + a') b = cob φ a b + cob φ a' b) (a b b' : M) :
    cob φ a (b + b') = cob φ a b + cob φ a b' := by
  rw [cob_symm', h1, cob_symm' b, cob_symm' b']

theorem cob_zero_left' (h1 : ∀ a a' b, cob φ (a + a') b = cob φ a b + cob φ a' b) (b : M) :
    cob φ 0 b = 0 := by
  have h := h1 0 0 b
  rw [add_zero] at h
  calc cob φ 0 b = (cob φ 0 b + cob φ 0 b) - cob φ 0 b := by abel
    _ = cob φ 0 b - cob φ 0 b := by rw [← h]
    _ = 0 := sub_self _

theorem cob_zero_right' (h1 : ∀ a a' b, cob φ (a + a') b = cob φ a b + cob φ a' b) (a : M) :
    cob φ a 0 = 0 := by
  rw [cob_symm', cob_zero_left' h1]

theorem phi_zero' (h1 : ∀ a a' b, cob φ (a + a') b = cob φ a b + cob φ a' b) : φ 0 = 0 := by
  have h := cob_zero_left' h1 (0 : M)
  simp only [cob, add_zero, sub_self, zero_sub, neg_eq_zero] at h
  exact h

theorem cob_sum_right' (h1 : ∀ a a' b, cob φ (a + a') b = cob φ a b + cob φ a' b)
    {J : Type} (a : M) (s : Finset J) (x : J → M) :
    cob φ a (∑ j ∈ s, x j) = ∑ j ∈ s, cob φ a (x j) := by
  induction s using Finset.cons_induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, cob_zero_right' h1]
  | cons j s hj ih => rw [Finset.sum_cons, Finset.sum_cons, cob_add_right' h1, ih]

theorem cob_sum_left' (h1 : ∀ a a' b, cob φ (a + a') b = cob φ a b + cob φ a' b)
    {J : Type} (b : M) (s : Finset J) (x : J → M) :
    cob φ (∑ j ∈ s, x j) b = ∑ j ∈ s, cob φ (x j) b := by
  induction s using Finset.cons_induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, cob_zero_left' h1]
  | cons j s hj ih => rw [Finset.sum_cons, Finset.sum_cons, h1, ih]

variable {O : Type} [CommRing O] [StarRing O] [Module O M]

theorem cross' (h1 : ∀ a a' b, cob φ (a + a') b = cob φ a b + cob φ a' b)
    (h2 : ∀ (α : O) a b, cob φ (α • a) b = cob φ a (star α • b))
    {n J : Type} [Fintype n] (c : n → O) (d : n → J → O) (a : M) (s : Finset J) (x : J → M) :
    ∑ i, cob φ (c i • a) (∑ j ∈ s, d i j • x j) =
      ∑ j ∈ s, cob φ a ((∑ i, star (c i) * d i j) • x j) := by
  simp_rw [h2, Finset.smul_sum, smul_smul, cob_sum_right' h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_smul, cob_sum_right' h1]

variable {Z : Type} [CommRing Z] [Module Z Q] {nm : O → Z}

theorem diag' (h1 : ∀ a a' b, cob φ (a + a') b = cob φ a b + cob φ a' b)
    (h2 : ∀ (α : O) a b, cob φ (α • a) b = cob φ a (star α • b))
    (h3 : ∀ (α : O) u, φ (α • u) = nm α • φ u)
    {n J : Type} [Fintype n] (c : n → J → O)
    (hG : ∀ a j, a ≠ j → ∑ i, star (c i a) * c i j = 0) (u : J → M) (s : Finset J) :
    ∑ i, φ (∑ j ∈ s, c i j • u j) = ∑ j ∈ s, (∑ i, nm (c i j)) • φ (u j) := by
  induction s using Finset.cons_induction with
  | empty => simp [phi_zero' h1]
  | cons k s hk ih =>
    have hcross : ∑ i, cob φ (c i k • u k) (∑ j ∈ s, c i j • u j) = 0 := by
      rw [cross' h1 h2 (fun i => c i k) c (u k) s u]
      refine Finset.sum_eq_zero fun j hj => ?_
      have hne : k ≠ j := by
        rintro rfl
        exact hk hj
      rw [hG k j hne, zero_smul, cob_zero_right' h1]
    simp only [Finset.sum_cons]
    simp only [phi_add', Finset.sum_add_distrib, h3]
    rw [hcross, ih, ← Finset.sum_smul, add_zero]

end calculus

end Formalism.HermitianLattices.IntegralLatticeDensity.PD

namespace Formalism.HermitianLattices.IntegralLatticeDensity

open Finset PD

theorem unitary_invariance : UnitaryInvariance := by
  intro Z O M Q _ _ _ _ _ _ _ _ φ nm hinj hnm h1 h2 h3 n _ _ δ hδ u
  have hG : ∀ a j, a ≠ j → ∑ i, star (δ i a) * δ i j = 0 := by
    intro a j hne
    have := congrFun (congrFun hδ a) j
    simpa [Matrix.mul_apply, Matrix.one_apply_ne hne] using this
  have hN : ∀ j, ∑ i, nm (δ i j) = 1 := by
    intro j
    apply hinj
    have := congrFun (congrFun hδ j) j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at this

    rw [map_sum, map_one]
    simpa [hnm] using this
  rw [diag' h1 h2 h3 δ hG u Finset.univ]
  simp [hN]

theorem hyperbolic_plane_split : HyperbolicSplit := by
  intro Z O M Q _ _ _ _ _ _ _ _ φ nm hinj hnm h1 h2 h3 n ι _ _ _ f f' hff hf'f' hff' t t'

  have hiso : ∀ (g : ι → n → O) (w : ι → M), (∀ e e', ∑ i, star (g e i) * g e' i = 0) →
      ∑ i, φ (∑ e, g e i • w e) = 0 := by
    intro g w hg
    have hz : ∀ e, ∑ i, nm (g e i) = 0 := by
      intro e
      apply hinj

      rw [map_sum, map_zero]
      simpa [hnm] using hg e e
    rw [diag' h1 h2 h3 (fun i e => g e i) (fun a j _ => hg a j) w Finset.univ]
    simp [hz]

  have hcross : ∑ i, cob φ (∑ e, f e i • t e) (∑ e, f' e i • t' e) = ∑ e, cob φ (t e) (t' e) := by
    simp_rw [cob_sum_left' h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [cross' h1 h2 (fun i => f e i) (fun i e' => f' e' i) (t e) Finset.univ t',
      Finset.sum_eq_single e]
    · rw [hff' e e, if_pos rfl, one_smul]
    · intro e' _ hne
      rw [hff' e e', if_neg (fun h => hne h.symm), zero_smul, cob_zero_right' h1]
    · intro h
      exact absurd (Finset.mem_univ e) h
  calc ∑ i, φ (∑ e, (f e i • t e + f' e i • t' e))
      = ∑ i, (φ (∑ e, f e i • t e) + φ (∑ e, f' e i • t' e) +
          cob φ (∑ e, f e i • t e) (∑ e, f' e i • t' e)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_add_distrib, phi_add' (φ := φ)]
    _ = ∑ e, cob φ (t e) (t' e) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hiso f t hff, hiso f' t' hf'f', hcross,
          zero_add, zero_add]

end Formalism.HermitianLattices.IntegralLatticeDensity
end

section

namespace Formalism.HermitianLattices.IntegralLatticeDensity

open Finset

theorem norm_for_all_alpha : NormAllAlpha := by
  intro Z O M Q _ _ _ _ _ _ _ _ φ nm tr hinj hnm htr hadd hlin hadj h2 α α' u hu2 hα hα'
  have symm : ∀ a b, cob φ a b = cob φ b a := by
    intro a b; unfold cob; rw [add_comm a b]; abel
  have add2 : ∀ a b b', cob φ a (b + b') = cob φ a b + cob φ a b' := by
    intro a b b'; rw [symm, hadd, symm b, symm b']
  have e1 : φ ((α + α') • u) = φ (α • u) + φ (α' • u) + cob φ (α • u) (α' • u) := by
    unfold cob; rw [add_smul]; abel
  have e2 : cob φ (α • u) (α' • u) = cob φ u ((star α * α') • u) := by rw [hadj, smul_smul]
  have e3 : cob φ u ((star α * α') • u) + cob φ u ((star α * α') • u)
      = (tr (star α * α')) • cob φ u u := by
    have h : cob φ u ((star α * α') • u) = cob φ u (star (star α * α') • u) := by
      rw [symm, hadj]
    nth_rewrite 1 [h]; rw [← add2, ← add_smul, ← htr, hlin]
  have e4 : cob φ u u = φ u + φ u := by
    unfold cob; rw [← two_smul O u, hu2]
    have : (4 : Z) • φ u = φ u + φ u + φ u + φ u := by
      rw [show (4 : Z) = 1 + 1 + 1 + 1 by norm_num]; simp [add_smul]
    rw [this]; abel
  have e5 : cob φ u ((star α * α') • u) = tr (star α * α') • φ u := by
    apply sub_eq_zero.1; apply h2
    have : ∀ x y : Q, (x - y) + (x - y) = (x + x) - (y + y) := by intro x y; abel
    rw [this, e3, e4, smul_add, sub_self]
  have e6 : nm (α + α') = nm α + nm α' + tr (star α * α') := by
    apply hinj; simp only [map_add (f := _), hnm, htr, star_add, star_mul, star_star]; ring
  rw [e1, e2, e5, hα, hα', e6, add_smul, add_smul]

end Formalism.HermitianLattices.IntegralLatticeDensity
end

section

namespace Formalism.HermitianLattices.LocalLatticeBases

open Finset

theorem length_average_bound : LemmaB'_avg := by
  intro k n S mult hS hm hn j
  have key : ∀ i : Fin k, ∑ w ∈ S, mult w * w i = ∑ w ∈ S, mult w * w j := by
    intro i
    apply Finset.sum_nbij' (fun w => w ∘ Equiv.swap i j) (fun w => w ∘ Equiv.swap i j)
    · intro w hw; exact hS _ w hw
    · intro w hw; exact hS _ w hw
    · intro w _; funext a; simp [Function.comp]
    · intro w _; funext a; simp [Function.comp]
    · intro w _; simp [hm]
  have : ∑ i : Fin k, ∑ w ∈ S, mult w * w i = k * ∑ w ∈ S, mult w * w j := by
    rw [Finset.sum_congr rfl (fun i _ => key i)]; simp
  rw [← this, Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  rw [← Finset.mul_sum, hn w hw, mul_comm]

end Formalism.HermitianLattices.LocalLatticeBases
end
