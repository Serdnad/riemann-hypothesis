module

public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle001
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

@[expose] public section

section

open Polynomial

namespace Formalism.IrreducibleCountingLemmas.Z

theorem twist_invertible_holds : TwistInvertible := by
  intro k V _ _ _ _ γ₀ c hc hne
  let L : Module.End k V := c⁻¹ • γ₀ - 1
  have hL : ∀ v, L v = c⁻¹ • γ₀ v - v := fun v => rfl
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    rw [hL, sub_eq_zero] at hv
    have h2 : γ₀ v = c • v := by
      calc γ₀ v = c • (c⁻¹ • γ₀ v) := by rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
        _ = c • v := by rw [hv]
    by_contra hv0
    exact hne (Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr h2, hv0⟩)
  have hbij : Function.Bijective L := ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩
  exact hbij

theorem phi15_is_unit_holds : PrimitiveRootFifteenSubOneUnit := by
  intro R _ _ ζ hζ
  have hnp : ∀ {p : ℕ}, p.Prime → ∀ k : ℕ, p ^ k ≠ 15 := by
    intro p hp k h
    have h3 : 3 ∣ p := Nat.prime_three.dvd_of_dvd_pow (show 3 ∣ p ^ k by rw [h]; norm_num)
    have h5 : 5 ∣ p := (by norm_num : Nat.Prime 5).dvd_of_dvd_pow (show 5 ∣ p ^ k by rw [h]; norm_num)
    have e3 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h3
    have e5 := (Nat.prime_dvd_prime_iff_eq (by norm_num : Nat.Prime 5) hp).mp h5
    omega
  have hev : (Polynomial.cyclotomic 15 R).eval 1 = 1 := Polynomial.eval_one_cyclotomic_not_prime_pow hnp
  rw [Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ, Polynomial.eval_prod] at hev
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hev
  have hmem : ζ ∈ primitiveRoots 15 R := (mem_primitiveRoots (by norm_num)).mpr hζ
  have hdvd : (1 - ζ) ∣ 1 := (Finset.dvd_prod_of_mem (fun μ => (1 : R) - μ) hmem).trans hev.dvd
  have hu : IsUnit (1 - ζ) := isUnit_of_dvd_one hdvd
  rw [show ζ - 1 = -(1 - ζ) by ring]
  exact hu.neg

theorem g5b_multiplicity_holds : UnitEvalOfMultiplicity := by
  intro O _ _ t c s' hs hmult
  have hmap : (s' * (X - C c) ^ t).map (IsLocalRing.residue O) =
      s'.map (IsLocalRing.residue O) * (X - C (IsLocalRing.residue O c)) ^ t := by
    simp
  have hs0 : s'.map (IsLocalRing.residue O) ≠ 0 := (hs.map _).ne_zero
  rw [hmap, Polynomial.rootMultiplicity_mul
    (mul_ne_zero hs0 (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero _))),
    Polynomial.rootMultiplicity_X_sub_C_pow] at hmult
  have h0 : (s'.map (IsLocalRing.residue O)).rootMultiplicity (IsLocalRing.residue O c) = 0 := by
    omega
  rw [Polynomial.rootMultiplicity_eq_zero_iff] at h0
  have hne : (s'.map (IsLocalRing.residue O)).eval (IsLocalRing.residue O c) ≠ 0 :=
    fun e => hs0 (h0 e)
  rw [Polynomial.eval_map, Polynomial.eval₂_hom] at hne
  exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mp hne

theorem same_residue_holds : SameResidue := by
  intro O _ _ X _ T hT a ha x y
  let ev : X → (T →+* IsLocalRing.ResidueField O) := fun z =>
    (IsLocalRing.residue O).comp ((Pi.evalRingHom (fun _ : X => O) z).comp T.val.toRingHom)
  have hev : ∀ z (b : T), ev z b = IsLocalRing.residue O ((b : X → O) z) := fun z b => rfl
  have hsurj : ∀ z, Function.Surjective (ev z) := by
    intro z k
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective k
    exact ⟨algebraMap O T r, by rw [hev]; simp⟩
  have hmax : ∀ z, RingHom.ker (ev z) = IsLocalRing.maximalIdeal T := fun z =>
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ (hsurj z))
  have hmem : ((⟨a, ha⟩ : T) - algebraMap O T (a x)) ∈ RingHom.ker (ev x) := by
    rw [RingHom.mem_ker, map_sub, hev, hev]
    simp
  rw [hmax x, ← hmax y, RingHom.mem_ker, map_sub, hev, hev, sub_eq_zero] at hmem
  simpa using hmem.symm

end Formalism.IrreducibleCountingLemmas.Z
end

section

open Polynomial

namespace Formalism.IrreducibleCountingLemmas.Z

theorem goodCuspidal_holds : GoodCuspidal := by
  intro k _ P _ r f I _ n d h hdeg hsq hprod hhdeg hn hd hno
  obtain ⟨v0⟩ := ‹Nonempty P›

  have hdvd : ∀ v i, h v i ∣ f v := by
    intro v i
    rw [hprod v]
    exact (dvd_pow_self (h v i) (by have := hd i; omega)).trans
      (Finset.dvd_prod_of_mem (fun j => h v j ^ d j) (Finset.mem_univ i))

  have hd1 : ∀ i, d i = 1 := by
    intro i
    by_contra hne
    have h2 : 2 ≤ d i := by have := hd i; omega
    have hsq' : h v0 i * h v0 i ∣ f v0 := by
      rw [hprod v0]
      refine (?_ : h v0 i * h v0 i ∣ h v0 i ^ d i).trans
        (Finset.dvd_prod_of_mem (fun j => h v0 j ^ d j) (Finset.mem_univ i))
      rw [← pow_two]
      exact pow_dvd_pow _ h2
    have hu := hsq v0 _ hsq'
    have e1 := Polynomial.natDegree_eq_zero_of_isUnit hu
    have e2 := hhdeg v0 i
    have e3 := hn i
    omega
  refine ⟨hd1, ?_⟩
  by_contra hcard
  push_neg at hcard
  haveI : Nontrivial I := Fintype.one_lt_card_iff_nontrivial.mp hcard
  obtain ⟨i, j, hij⟩ := exists_pair_ne I
  have hf0 : f v0 ≠ 0 := (hsq v0).ne_zero
  have hne : ∀ l, h v0 l ≠ 0 := by
    intro l hl
    have := hdvd v0 l
    rw [hl, zero_dvd_iff] at this
    exact hf0 this

  have hr : r = ∑ l, n l := by
    rw [← hdeg v0, hprod v0, Polynomial.natDegree_prod _ _ (fun l _ => pow_ne_zero _ (hne l))]
    simp [Polynomial.natDegree_pow, hd1, hhdeg]
  have hle : n i + n j ≤ ∑ l, n l := by
    classical
    rw [← Finset.sum_pair hij]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  rcases le_total (n i) (n j) with hij' | hji'
  · exact hno ⟨n i, hn i, by omega, fun v => ⟨h v i, hdvd v i, hhdeg v i⟩⟩
  · exact hno ⟨n j, hn j, by omega, fun v => ⟨h v j, hdvd v j, hhdeg v j⟩⟩

end Formalism.IrreducibleCountingLemmas.Z
end

section

open Polynomial

namespace Formalism.IrreducibleCountingLemmas.Z

theorem charpolyFactorAnnihilator : CharpolyFactorAnnihilator := by
  intro K V _ _ _ _ A B γ₀ γ c cγ t P hAB hA₀ hA hB₀ hB ht hchar
  classical
  let gA : Module.End K A := γ₀.restrict hA₀
  let gB : Module.End K B := c • LinearMap.id
  let e : (A × B) ≃ₗ[K] V := Submodule.prodEquivOfIsCompl A B hAB

  have hconj : e.conj (gA.prodMap gB) = γ₀ := by
    apply LinearMap.ext
    intro v
    obtain ⟨⟨a, b⟩, rfl⟩ := e.surjective v
    rw [LinearEquiv.conj_apply]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    simp [e, gA, gB, Submodule.coe_prodEquivOfIsCompl', hB₀ b b.2]

  have hcB : gB.charpoly = (X - C c) ^ t := by
    rw [← LinearMap.charpoly_toMatrix gB (Module.finBasis K B)]
    have hm : LinearMap.toMatrix (Module.finBasis K B) (Module.finBasis K B) gB =
        Matrix.diagonal (fun _ => c) := by
      simp only [gB, map_smul, LinearMap.toMatrix_id]
      ext i j
      by_cases h : i = j <;> simp [h, Matrix.one_apply]
    rw [hm, Matrix.charpoly_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ht]
  have hPA : P = gA.charpoly := by
    have h1 : γ₀.charpoly = gA.charpoly * gB.charpoly := by
      rw [← hconj, LinearEquiv.charpoly_conj, LinearMap.charpoly_prodMap]
    rw [hchar, hcB] at h1
    exact mul_right_cancel₀ (pow_ne_zero _ (X_sub_C_ne_zero c)) h1

  have hrestr : ∀ (p : K[X]) (a : A), (aeval γ₀ p) (a : V) = ((aeval gA p) a : V) := by
    intro p
    induction p using Polynomial.induction_on with
    | C r => intro a; simp [Module.algebraMap_end_apply]
    | add p q hp hq => intro a; simp [hp, hq]
    | monomial n r ih =>
      intro a
      rw [pow_succ, ← mul_assoc, map_mul (aeval γ₀), map_mul (aeval gA), aeval_X, aeval_X,
        Module.End.mul_apply, Module.End.mul_apply]
      rw [show γ₀ (a : V) = ((gA a : A) : V) from rfl, ih]
  have h0 : aeval gA P = 0 := by
    rw [hPA]
    exact LinearMap.aeval_self_charpoly gA
  have hkill : ∀ w ∈ A, (aeval γ₀ P) w = 0 := by
    intro w hw
    have h2 := hrestr P ⟨w, hw⟩
    rw [h0] at h2
    simpa using h2
  apply LinearMap.ext
  intro v
  have hv : v ∈ A ⊔ B := by rw [hAB.sup_eq_top]; trivial
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
  rw [Module.End.mul_apply, LinearMap.zero_apply, LinearMap.sub_apply,
    Module.algebraMap_end_apply]
  have h3 : γ (a + b) - cγ • (a + b) = γ a - cγ • a := by
    rw [map_add (f := _), hB b hb, smul_add]
    abel
  rw [h3]
  exact hkill _ (A.sub_mem (hA a ha) (A.smul_mem cγ ha))

end Formalism.IrreducibleCountingLemmas.Z
end

section

namespace Formalism.IrreducibleCountingLemmas.WindowSums

theorem padicValIntShiftLe : DigitLemma := by
  intro l a c ρ m hl ha hc0 hcN hρ hdvd hm
  have := Fact.mk hl
  have hl2 : (2:ℤ) ≤ (l:ℤ) := by exact_mod_cast hl.two_le
  have hla : 1 ≤ l ^ a := Nat.one_le_pow _ _ hl.pos
  have hlr : 1 ≤ l ^ ρ := Nat.one_le_pow _ _ hl.pos
  have hNc : ((l ^ a - 1 : ℕ) : ℤ) = (l:ℤ) ^ a - 1 := by
    rw [Nat.cast_sub hla]; push_cast; rfl
  have hcN' : (c:ℤ) < (l:ℤ) ^ a - 1 := by rw [← hNc]; exact_mod_cast hcN
  have hc0' : (0:ℤ) < c := by exact_mod_cast hc0
  have hdvd' : ((l:ℤ) ^ a - 1) ∣ (c:ℤ) * ((l:ℤ) ^ ρ - 1) := by
    have h1 := Int.natCast_dvd_natCast.mpr hdvd
    rw [hNc] at h1
    have h2 : ((c * (l ^ ρ - 1) : ℕ) : ℤ) = (c:ℤ) * ((l:ℤ) ^ ρ - 1) := by
      rw [Nat.cast_mul, Nat.cast_sub hlr]; push_cast; rfl
    rw [h2] at h1; exact h1
  have hP : (2:ℤ) ≤ (l:ℤ) ^ ρ := by
    obtain ⟨r, rfl⟩ : ∃ r, ρ = r + 1 := ⟨ρ - 1, by omega⟩
    have : (1:ℤ) ≤ (l:ℤ) ^ r := one_le_pow₀ (by linarith)
    rw [pow_succ]; nlinarith
  by_contra hv
  push Not at hv
  have hdx : (l:ℤ) ^ (ρ + 1) ∣ (c:ℤ) + m * ((l:ℤ) ^ a - 1) :=
    (padicValInt_dvd_iff (ρ + 1) _).2 (Or.inr (by omega))
  obtain ⟨t, ht⟩ := hdx
  have hxN : ((l:ℤ) ^ a - 1) ∣ (l:ℤ) ^ (ρ + 1) * (t * ((l:ℤ) ^ ρ - 1)) := by
    have e : (l:ℤ) ^ (ρ + 1) * (t * ((l:ℤ) ^ ρ - 1))
        = (c:ℤ) * ((l:ℤ) ^ ρ - 1) + ((l:ℤ) ^ a - 1) * (m * ((l:ℤ) ^ ρ - 1)) := by
      rw [← mul_assoc, ← ht]; ring
    rw [e]; exact dvd_add hdvd' (dvd_mul_right _ _)
  have hcop : IsCoprime ((l:ℤ) ^ a - 1) ((l:ℤ) ^ (ρ + 1)) := by
    apply IsCoprime.pow_right
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    exact ⟨-1, (l:ℤ) ^ b, by ring⟩
  have hy : ((l:ℤ) ^ a - 1) ∣ t * ((l:ℤ) ^ ρ - 1) := by
    exact hcop.dvd_of_dvd_mul_left hxN
  have hm' := abs_lt.mp hm
  have hNpos : (0:ℤ) < (l:ℤ) ^ a - 1 := by linarith
  have hxlt : |(c:ℤ) + m * ((l:ℤ) ^ a - 1)| < (l:ℤ) * ((l:ℤ) ^ a - 1) := by
    have u1 : 0 ≤ ((l:ℤ) - 1 - m) * ((l:ℤ) ^ a - 1) :=
      mul_nonneg (by linarith) hNpos.le
    have u2 : 0 ≤ (m + (l:ℤ) - 1) * ((l:ℤ) ^ a - 1) :=
      mul_nonneg (by linarith) hNpos.le
    rw [abs_lt]; constructor <;> nlinarith
  have htlt : (l:ℤ) ^ ρ * |t| < (l:ℤ) ^ a - 1 := by
    rw [ht, abs_mul, abs_of_pos (by positivity : (0:ℤ) < (l:ℤ) ^ (ρ + 1)), pow_succ] at hxlt
    have hl0 : (0:ℤ) < l := by linarith
    nlinarith
  have hylt : |t * ((l:ℤ) ^ ρ - 1)| < (l:ℤ) ^ a - 1 := by
    rw [abs_mul, abs_of_pos (by linarith : (0:ℤ) < (l:ℤ) ^ ρ - 1)]
    nlinarith [abs_nonneg t]
  have hy0 := Int.eq_zero_of_abs_lt_dvd hy hylt
  have ht0 : t = 0 := by
    rcases mul_eq_zero.mp hy0 with h | h
    · exact h
    · linarith
  rw [ht0, mul_zero] at ht
  have hcd : ((l:ℤ) ^ a - 1) ∣ (c:ℤ) := ⟨-m, by linarith⟩
  have hcz := Int.eq_zero_of_abs_lt_dvd hcd (by rw [abs_of_pos hc0']; exact hcN')
  linarith

end Formalism.IrreducibleCountingLemmas.WindowSums
end

section

open Finset

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem dominant_numbers_sharp_holds : StretchedExponentialDominance := by
  intro C ε hε
  have ha : 0 < ε / 6 := by positivity
  have hab : 0 < ε / 6 - ε / 7 := by linarith
  have hc : (0 : ℝ) < 1 / (3 * (|C| + 1)) := by positivity
  filter_upwards [(tendsto_rpow_atTop hab).eventually_ge_atTop 3,
    (isLittleO_log_rpow_atTop ha).bound hc,
    (tendsto_rpow_atTop ha).eventually_ge_atTop (3 * Real.log 20),
    Filter.eventually_ge_atTop (1 : ℝ)] with x h1 h2 h3 h4
  have hx0 : 0 < x := by linarith
  have hsplit : x ^ (ε / 6) = x ^ (ε / 7) * x ^ (ε / 6 - ε / 7) := by
    rw [← Real.rpow_add hx0]
    ring_nf
  have hb0 : 0 ≤ x ^ (ε / 7) := Real.rpow_nonneg hx0.le _
  have hxb : 3 * x ^ (ε / 7) ≤ x ^ (ε / 6) := by
    rw [hsplit]
    nlinarith
  have ha0 : 0 ≤ x ^ (ε / 6) := Real.rpow_nonneg hx0.le _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha0] at h2
  have hlog : C * Real.log x ≤ x ^ (ε / 6) / 3 := by
    have hC0 : 0 ≤ |C| := abs_nonneg C
    have e1 : C * Real.log x ≤ |C| * |Real.log x| := by
      rw [← abs_mul]
      exact le_abs_self _
    have e2 : |C| * |Real.log x| ≤ |C| * (1 / (3 * (|C| + 1)) * x ^ (ε / 6)) :=
      mul_le_mul_of_nonneg_left h2 hC0
    have e3 : |C| * (1 / (3 * (|C| + 1)) * x ^ (ε / 6)) ≤ x ^ (ε / 6) / 3 := by
      rw [show |C| * (1 / (3 * (|C| + 1)) * x ^ (ε / 6)) = |C| / (|C| + 1) * (x ^ (ε / 6) / 3) by
        field_simp]
      have : |C| / (|C| + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith
      have h6 : 0 ≤ x ^ (ε / 6) / 3 := by positivity
      nlinarith
    linarith
  have h20 : (1 : ℝ) / 20 = Real.exp (-Real.log 20) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]
    norm_num
  rw [Real.rpow_def_of_pos hx0, ← Real.exp_add, h20, ← Real.exp_add]
  apply Real.exp_le_exp.2
  nlinarith

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section

namespace Formalism.IrreducibleCountingLemmas.WindowSums

theorem sum_one_add_val (l : ℕ) [Fact l.Prime] (n : ℕ) :
    ∑ i ∈ Finset.range n, (1 + padicValNat l (i + 1)) = n + padicValNat l n.factorial := by
  induction n with
  | zero => simp [Nat.padicValNat_def]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Nat.factorial_succ,
      (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (Nat.succ_ne_zero n) (Nat.factorial_ne_zero n)]
    simp only [Nat.succ_eq_add_one]
    omega

theorem two_mul_val_factorial_le (l : ℕ) [hl : Fact l.Prime] (h2 : l ≠ 2) (n : ℕ) :
    2 * padicValNat l n.factorial ≤ n := by
  have h3 : 3 ≤ l := by have := hl.out.two_le; omega
  have key : (l - 1) * padicValNat l n.factorial = n - (l.digits n).sum := by
    simpa only [Nat.padicValNat_def] using (hl.out.sub_one_mul_multiplicity_factorial (n := n))
  have hle : (l - 1) * padicValNat l n.factorial ≤ n := by rw [key]; exact Nat.sub_le _ _
  have h2le : 2 * padicValNat l n.factorial ≤ (l - 1) * padicValNat l n.factorial :=
    Nat.mul_le_mul_right _ (by omega)
  omega

private theorem padicValInt_neg_natCast_add_one (l i : ℕ) :
    padicValInt l (-((i : ℤ) + 1)) = padicValNat l (i + 1) := by
  simp only [padicValInt]
  rw [show (-((i : ℤ) + 1)).natAbs = i + 1 by omega, Nat.padicValNat_def]

private theorem padicValInt_natCast_add_one (l i : ℕ) :
    padicValInt l ((i : ℤ) + 1) = padicValNat l (i + 1) := by
  simp only [padicValInt]
  rw [show ((i : ℤ) + 1).natAbs = i + 1 by omega, Nat.padicValNat_def]

theorem valuationSumBound : LiftExp := by
  intro l h J hl hl2 hJ h0
  have : Fact l.Prime := ⟨hl⟩
  set f : ℤ → ℕ := fun j => 1 + padicValInt l j with hf
  set A : Finset ℤ := (Finset.range h).image (fun i : ℕ => -((i : ℤ) + 1)) with hA
  set B : Finset ℤ := (Finset.range (2 * h)).image (fun i : ℕ => (i : ℤ) + 1) with hB
  have hsub : J ⊆ A ∪ B := by
    intro j hj
    have hm := Finset.mem_Icc.mp (hJ hj)
    have hj0 : j ≠ 0 := fun e => h0 (e ▸ hj)
    rw [Finset.mem_union, hA, hB, Finset.mem_image, Finset.mem_image]
    rcases lt_or_gt_of_ne hj0 with hneg | hpos
    · left
      exact ⟨(-j - 1).toNat, by rw [Finset.mem_range]; omega, by omega⟩
    · right
      exact ⟨(j - 1).toNat, by rw [Finset.mem_range]; omega, by omega⟩
  have hA_sum : ∑ j ∈ A, f j = h + padicValNat l h.factorial := by
    rw [hA, Finset.sum_image (fun x _ y _ e => by simpa using e)]
    rw [← sum_one_add_val l h]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [hf, padicValInt_neg_natCast_add_one]
  have hB_sum : ∑ j ∈ B, f j = 2 * h + padicValNat l (2 * h).factorial := by
    rw [hB, Finset.sum_image (fun x _ y _ e => by simpa using e)]
    rw [← sum_one_add_val l (2 * h)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [hf, padicValInt_natCast_add_one]
  have hJle : ∑ j ∈ J, f j ≤ ∑ j ∈ A ∪ B, f j := Finset.sum_le_sum_of_subset hsub
  have hU := Finset.sum_union_inter (s₁ := A) (s₂ := B) (f := f)
  have e1 := two_mul_val_factorial_le l hl2 (2 * (2 * h))
  have e2 := two_mul_val_factorial_le l hl2 h
  have e3 := two_mul_val_factorial_le l hl2 (2 * h)
  have hJ' : ∑ j ∈ J, (1 + padicValInt l j) = ∑ j ∈ J, f j := rfl
  rw [hJ']
  omega

end Formalism.IrreducibleCountingLemmas.WindowSums
end

section

open Polynomial

namespace Formalism.IrreducibleCountingLemmas.Z

theorem factorOverLocalSubalgebra : FactorOverLocalSubalgebra := by
  intro O _ _ X' _ T hT t c F s hF hs
  have := hT
  let c' : T := algebraMap O T c
  have hev_c : ∀ x, ev T x c' = c := fun x => by simp [ev, c']
  have hq : ((X - C c') ^ t : T[X]).Monic := (monic_X_sub_C c').pow t
  have hqO : ((X - C c) ^ t : O[X]).Monic := (monic_X_sub_C c).pow t
  have hqmap : ∀ x, ((X - C c') ^ t : T[X]).map (ev T x) = (X - C c) ^ t := by
    intro x
    rw [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hev_c]
  have hR : F %ₘ (X - C c') ^ t = 0 := by
    ext n x
    have h1 : (F %ₘ (X - C c') ^ t).map (ev T x) = 0 := by
      rw [map_modByMonic _ hq, hqmap, hF, (modByMonic_eq_zero_iff_dvd hqO).mpr (dvd_mul_left _ _)]
    have h2 := congrArg (fun p => p.coeff n) h1
    simpa [Polynomial.coeff_map, ev] using h2
  have hmapP : ∀ x, (F /ₘ (X - C c') ^ t).map (ev T x) = s x := by
    intro x
    rw [map_divByMonic _ hq, hqmap, hF, mul_comm, mul_divByMonic_cancel_left _ hqO]
  refine ⟨F /ₘ (X - C c') ^ t, ?_, ?_, hmapP⟩
  · have h := modByMonic_add_div F ((X - C c') ^ t)
    rw [hR, zero_add] at h
    rw [mul_comm]
    exact h.symm
  · obtain ⟨x⟩ : Nonempty X' := by
      by_contra h
      rw [not_nonempty_iff] at h
      have hsub : Subsingleton T := ⟨fun a b => Subtype.ext (funext fun x => (IsEmpty.false x).elim)⟩
      exact not_subsingleton T hsub
    have := IsLocalHom.of_surjective (ev T x) (fun o => ⟨algebraMap O T o, by simp [ev]⟩)
    apply isUnit_of_map_unit (ev T x)
    rw [← Polynomial.eval₂_hom, ← Polynomial.eval_map, hmapP, hev_c]
    exact hs x

end Formalism.IrreducibleCountingLemmas.Z
end
