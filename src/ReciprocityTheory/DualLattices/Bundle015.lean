module

public import ReciprocityTheory.DualLattices.Bundle007
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.RingTheory.Valuation.Integers
public import ReciprocityTheory.DualLattices.Bundle009
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.DualLattices.VIntCastLtOneOfDvd
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import ReciprocityTheory.DualLattices.IsUnitDetOfSpanEq
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

@[expose] public section

section

noncomputable section

open Finset

namespace ReciprocityTheory.PGsh.Up.U3

open ReciprocityTheory.PGsh.L2

variable {p : ℕ} [hp : Fact p.Prime] {C : Type} [Field C] {v : Valuation C NNReal}
  {R : Type} [CommRing R] [Algebra R C]

theorem exists_charEquiv [NeZero p] {ζ : C} (hζ : IsPrimitiveRoot ζ p) :
    ∃ e : ZMod p ≃ AddChar (ZMod p) C, (∀ h h', e (h + h') = e h * e h') ∧
      ∀ h a, e h a = ζ ^ (h * a).val := by
  have hp1 : ζ ^ p = 1 := hζ.pow_eq_one
  let ψ : AddChar (ZMod p) C := AddChar.zmodChar p hp1
  have hψ : ∀ a, ψ a = ζ ^ a.val := fun a => AddChar.zmodChar_apply hp1 a
  let f : ZMod p → AddChar (ZMod p) C := fun h => ψ.mulShift h
  have hf : ∀ h a, f h a = ζ ^ (h * a).val := fun h a => by
    simp only [f, AddChar.mulShift_apply, hψ]
  have hgen : ∀ (χ : AddChar (ZMod p) C) (a : ZMod p), χ a = χ 1 ^ a.val := by
    intro χ a
    conv_lhs => rw [← ZMod.natCast_zmod_val a, ← nsmul_one]
    exact AddChar.map_nsmul_eq_pow χ _ _
  have hinj : Function.Injective f := by
    intro h h' hh
    have := congrArg (fun χ : AddChar (ZMod p) C => χ 1) hh
    simp only [hf, mul_one] at this
    exact ZMod.val_injective _ (hζ.pow_inj (ZMod.val_lt h) (ZMod.val_lt h') this)
  have hsurj : Function.Surjective f := by
    intro χ
    have h1 : χ 1 ^ p = 1 := by
      rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, mul_one, ZMod.natCast_self, AddChar.map_zero_eq_one]
    obtain ⟨k, hk, hkχ⟩ := hζ.eq_pow_of_pow_eq_one h1
    refine ⟨(k : ZMod p), ?_⟩
    ext a
    rw [hgen χ a, hgen (f k) a, hf, mul_one, ZMod.val_natCast, Nat.mod_eq_of_lt hk, hkχ]
  refine ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, ?_, ?_⟩
  · intro h h'
    ext a
    show (ψ.mulShift (h + h')) a = ψ.mulShift h a * ψ.mulShift h' a
    rw [AddChar.mulShift_apply, AddChar.mulShift_apply, AddChar.mulShift_apply, add_mul,
      AddChar.map_add_eq_mul]
  · intro h a
    exact hf h a

theorem v_gamma (hv : v.Integers R) (hpv : v (p : C) < 1) {ω : ZMod p → C} (hω : IsTeich v ω)
    {ζ : C} (hζ : IsPrimitiveRoot ζ p) :
    v (∑ a, u0 ω a * ζ ^ a.val) ^ (p - 1) = v (p : C) := by
  have hpp : 2 ≤ p := hp.out.two_le
  have hζ1 : v ζ ≤ 1 := by
    by_contra h
    push_neg at h
    have h2 := one_lt_pow₀ h (show p ≠ 0 by omega)
    rw [← map_pow, hζ.pow_eq_one, map_one] at h2
    exact lt_irrefl _ h2
  have hπ1 : v (ζ - 1) < 1 := by
    by_contra h
    push_neg at h
    have h2 := one_le_pow₀ (n := p - 1) h
    rw [val_prim_root hζ] at h2
    exact absurd hpv (not_lt.mpr h2)
  have hnat : ∀ n : ℕ, v (n : C) ≤ 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.cast_succ]; exact Valuation.map_add_le v ih (by rw [map_one])
  have hdec : ∀ n : ℕ, ∃ s : C, v s ≤ 1 ∧ ζ ^ n - 1 = (ζ - 1) * (n + (ζ - 1) * s) := by
    intro n
    induction n with
    | zero => exact ⟨0, by simp, by simp⟩
    | succ n ih =>
      obtain ⟨s, hs1, hs⟩ := ih
      refine ⟨n + ζ * s, Valuation.map_add_le v (hnat n) (by rw [map_mul]; exact mul_le_one' hζ1 hs1), ?_⟩
      push_cast
      linear_combination ζ * hs
  choose s hs1 hs using hdec
  have h1 : ∑ a, u0 ω a * ζ ^ a.val = ∑ a, wt ω a * (ζ ^ a.val - 1) := by
    have := hω.lam_eq (fun a => ζ ^ a.val)
    simpa [lam, ZMod.val_zero] using this
  have h2 : ∑ a, wt ω a * ω a = (p : C) - 1 := by
    have := hω.lam_eq ω
    rw [hω.lam_omega, hω.zero] at this
    simpa using this.symm
  have hγ : ∑ a, u0 ω a * ζ ^ a.val = (ζ - 1) * (((p : C) - 1) +
      (∑ a, wt ω a * ((a.val : C) - ω a) + (ζ - 1) * ∑ a, wt ω a * s a.val)) := by
    rw [h1, ← h2]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hs]
    ring
  have hδ : v (∑ a, wt ω a * ((a.val : C) - ω a) + (ζ - 1) * ∑ a, wt ω a * s a.val) < 1 := by
    apply Valuation.map_add_lt v
    · apply Valuation.map_sum_lt v one_ne_zero
      intro a _
      rw [map_mul]
      calc v (wt ω a) * v ((a.val : C) - ω a) ≤ 1 * v ((a.val : C) - ω a) := by
            gcongr; exact hω.wt_int a
        _ < 1 := by rw [one_mul, Valuation.map_sub_swap]; exact hω.cong a
    · rw [map_mul]
      have hsum : v (∑ a, wt ω a * s a.val) ≤ 1 :=
        Valuation.map_sum_le v fun a _ => by rw [map_mul]; exact mul_le_one' (hω.wt_int a) (hs1 _)
      calc v (ζ - 1) * v (∑ a, wt ω a * s a.val) ≤ v (ζ - 1) * 1 := by gcongr
        _ < 1 := by rw [mul_one]; exact hπ1
  have hp1 : v ((p : C) - 1) = 1 := by
    have hnd : ¬ (p : ℤ) ∣ (p : ℤ) - 1 := by
      intro hd
      have h1' : (p : ℤ) ∣ 1 := by simpa using dvd_sub (dvd_refl (p : ℤ)) hd
      have := Int.eq_one_of_dvd_one (by positivity) h1'
      omega
    have := v_intCast_eq_one hv hpv hnd
    push_cast at this
    exact this
  have hunit : v ((p : C) - 1 + (∑ a, wt ω a * ((a.val : C) - ω a) +
      (ζ - 1) * ∑ a, wt ω a * s a.val)) = 1 := by
    rw [Valuation.map_add_eq_of_lt_left v (by rw [hp1]; exact hδ), hp1]
  rw [hγ, map_mul, hunit, mul_one]
  exact val_prim_root hζ

theorem fourierMap_smul_lambdaWeight {ω : ZMod p → C} (hω : IsTeich v ω) {ζ : C}
    (e : ZMod p ≃ AddChar (ZMod p) C) (he2 : ∀ h a, e h a = ζ ^ (h * a).val) (c : C) :
    fourier (R := R) (fun h a => e h a) (fun a => c * u0 ω a) =
      fun h => (c * ∑ a, u0 ω a * ζ ^ a.val) * ω h := by
  have hω0 : ∀ h : ZMod p, h ≠ 0 → ω h ≠ 0 := by
    intro h hh
    have := hω.sep h 0 hh
    rw [hω.zero, sub_zero] at this
    intro h0
    rw [h0, map_zero] at this
    exact zero_ne_one this
  have hp2 : 2 ≤ p := hp.out.two_le
  have hpow1 : ∀ h : ZMod p, h ≠ 0 → ω h ^ (p - 1) = 1 := by
    intro h hh
    have e1 := hω.pow h
    have : ω h ^ (p - 1) * ω h = 1 * ω h := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega), one_mul, e1]
    exact mul_right_cancel₀ (hω0 h hh) this
  have hwt : ∀ h : ZMod p, h ≠ 0 → wt ω h * ω h = 1 := by
    intro h hh
    simp only [wt]
    rw [← pow_succ, show 2 * p - 3 + 1 = (p - 1) + (p - 1) by omega, pow_add, hpow1 h hh, one_mul]
  have hwtmul : ∀ a b : ZMod p, wt ω (a * b) = wt ω a * wt ω b := by
    intro a b; simp only [wt, hω.mul, mul_pow]
  have hwtinv : ∀ h : ZMod p, h ≠ 0 → wt ω h⁻¹ = ω h := by
    intro h hh
    have hi : h⁻¹ ≠ 0 := inv_ne_zero hh
    have e1 := hwt h⁻¹ hi
    have e2 : ω h⁻¹ * ω h = 1 := by rw [← hω.mul, inv_mul_cancel₀ hh, hω.one]
    calc wt ω h⁻¹ = wt ω h⁻¹ * (ω h⁻¹ * ω h) := by rw [e2, mul_one]
      _ = ω h := by rw [← mul_assoc, e1, one_mul]
  have hwt0 : wt ω 0 = 0 := by
    simp only [wt, hω.zero]; exact zero_pow (by omega)
  have hS : ∀ h : ZMod p, h ≠ 0 → sS ω = ω h * sS ω := by
    intro h hh
    have := Fintype.sum_bijective (h⁻¹ * ·) (mulLeft_bijective₀ h⁻¹ (inv_ne_zero hh))
      (fun b => wt ω (h⁻¹ * b)) (wt ω) (fun _ => rfl)
    simp only [hwtmul, hwtinv h hh, ← Finset.mul_sum] at this
    simp only [sS]; exact this.symm
  have hu : ∀ h : ZMod p, h ≠ 0 → ∀ b, u0 ω (h⁻¹ * b) = ω h * u0 ω b := by
    intro h hh b
    simp only [u0]
    by_cases hb : b = 0
    · subst hb
      simp only [mul_zero, if_true, hwt0]
      nth_rewrite 1 [hS h hh]; ring
    · have : h⁻¹ * b ≠ 0 := mul_ne_zero (inv_ne_zero hh) hb
      simp only [this, hb, if_false, sub_zero, hwtmul, hwtinv h hh]
  funext h
  simp only [L2.fourier, LinearMap.coe_mk, AddHom.coe_mk, he2]
  by_cases hh : h = 0
  · subst hh
    simp only [zero_mul, ZMod.val_zero, pow_zero, mul_one, hω.zero, mul_zero]
    rw [← Finset.mul_sum]
    simp only [u0, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp [sS]
  · have hb := Fintype.sum_bijective (h⁻¹ * ·) (mulLeft_bijective₀ h⁻¹ (inv_ne_zero hh))
      (fun b => c * u0 ω (h⁻¹ * b) * ζ ^ (h * (h⁻¹ * b)).val)
      (fun a => c * u0 ω a * ζ ^ (h * a).val) (fun _ => rfl)
    rw [← hb]
    simp only [hu h hh, ← mul_assoc, mul_inv_cancel₀ hh, one_mul]
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring

end ReciprocityTheory.PGsh.Up.U3
end
end

section

noncomputable section

open Matrix Finset

namespace ReciprocityTheory.PGsh.L2

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]

theorem apply_add_of_mem_map_pullbackQuotient (K : AddSubgroup N) (M : Submodule R (N ⧸ K → C)) {h : N → C}
    (hh : h ∈ M.map (pullQ (R := R) K)) (x : N) (k : K) : h (x + k) = h x := by
  obtain ⟨u, -, rfl⟩ := hh
  simp only [pullQ, LinearMap.funLeft_apply]
  rw [QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff _).mpr k.2, add_zero]

theorem pullbackQuotient_apply_out (K : AddSubgroup N) {h : N → C} (hinv : ∀ x (k : K), h (x + k) = h x) :
    pullQ (R := R) K (fun q => h q.out) = h := by
  funext x
  simp only [pullQ, LinearMap.funLeft_apply]
  have e : (((QuotientAddGroup.mk x : N ⧸ K).out : N) : N ⧸ K) = (x : N ⧸ K) := by
    exact Quotient.out_eq _
  have hk := QuotientAddGroup.eq.mp e
  calc h (QuotientAddGroup.mk x : N ⧸ K).out
      = h ((QuotientAddGroup.mk x : N ⧸ K).out + ((⟨_, hk⟩ : K) : N)) := (hinv _ _).symm
    _ = h x := by congr 1; simp

theorem mem_map_comap_pullbackQuotient (AA : HopfOrder (C := C) R N) (K : AddSubgroup N) {h : N → C}
    (hh : h ∈ AA.carrier) (hinv : ∀ x (k : K), h (x + k) = h x) :
    h ∈ (AA.carrier.comap (pullQ (R := R) K)).map (pullQ (R := R) K) := by
  refine Submodule.mem_map.mpr ⟨fun q => h q.out, ?_, pullbackQuotient_apply_out (R := R) K hinv⟩
  rw [Submodule.mem_comap, pullbackQuotient_apply_out (R := R) K hinv]
  exact hh

theorem mem_map_augmentationIdeal_comap_pullbackQuotient (AA : HopfOrder (C := C) R N) (K : AddSubgroup N) {h : N → C}
    (hh : h ∈ AA.carrier) (hinv : ∀ x (k : K), h (x + k) = h x) (h0 : h 0 = 0) :
    h ∈ (augIdeal (AA.carrier.comap (pullQ (R := R) K))).map (pullQ (R := R) K) := by
  refine Submodule.mem_map.mpr ⟨fun q => h q.out, ?_, pullbackQuotient_apply_out (R := R) K hinv⟩
  simp only [augIdeal, Submodule.mem_inf]
  refine ⟨?_, ?_⟩
  · rw [Submodule.mem_comap, pullbackQuotient_apply_out (R := R) K hinv]
    exact hh
  · have h1 := congrFun (pullbackQuotient_apply_out (R := R) K hinv) 0
    simp only [pullQ, LinearMap.funLeft_apply, QuotientAddGroup.mk_zero] at h1
    simp only [LinearMap.mem_ker, LinearMap.proj_apply]
    rw [h1, h0]

section family

variable (hv : v.Integers R) (AA : HopfOrder (C := C) R N) (K : AddSubgroup N)
  [DecidablePred (· ∈ K)] (β : Matrix K K C) (hβ : IsUnit β.det)
  (hAK : AA.carrier.map (resK (R := R) K) = Submodule.span R (Set.range fun j k => β k j))
  (f : K → N → C) (hf : ∀ j, f j ∈ AA.carrier) (hdet : ∀ x, v (h3mm K β f x).det = 1)

include hβ hdet in
theorem eq_zero_of_sum_mul_coset_eq_zero (x : N) (c : K → C) (h : ∀ k : K, ∑ j, c j * f j (x + k) = 0) : c = 0 := by
  have hM : (h3mm K β f x).det ≠ 0 := by
    intro h0
    have := hdet x
    rw [h0, map_zero] at this
    exact zero_ne_one this
  have hw : β *ᵥ (c ᵥ* h3mm K β f x) = 0 := by
    funext k
    rw [Pi.zero_apply, ← h k]
    have e : ∀ j, f j (x + k) = ∑ l, β k l * h3mm K β f x j l := fun j => by
      rw [cosetCoordinates_expand K β hβ (f j) x k]
      rfl
    simp only [e]
    simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hw0 : c ᵥ* h3mm K β f x = 0 := by
    have := congrArg (β⁻¹ *ᵥ ·) hw
    simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul β hβ] using this
  by_contra hc
  exact hM (Matrix.exists_vecMul_eq_zero_iff.mp ⟨c, hc, hw0⟩)

include hv hβ hAK hf hdet in
theorem exists_coset_invariant_coefficients {g : N → C} (hg : g ∈ AA.carrier) :
    ∃ b : K → N → C, (∀ j, b j ∈ AA.carrier) ∧ (∀ j x (k : K), b j (x + k) = b j x) ∧
      g = ∑ j, b j * f j := by
  have hDne : ∀ x, (h3mm K β f x).det ≠ 0 := fun x h0 => by
    have := hdet x
    rw [h0, map_zero] at this
    exact zero_ne_one this
  have hFu : ∀ x, IsUnit (h3mm K β f x).det := fun x =>
    isUnit_iff_ne_zero.mpr (hDne x)
  obtain ⟨b, hb⟩ : ∃ b : K → N → C, b = fun j x =>
      (h3co K β g x ᵥ* (h3mm K β f x)⁻¹) j := ⟨_, rfl⟩
  have hbx : ∀ j x, b j x = (h3co K β g x ᵥ* (h3mm K β f x)⁻¹) j :=
    fun j x => by rw [hb]
  let Fm : Matrix K K (N → C) := Matrix.of fun i j => fun x => h3co K β (f i) x j
  have hFm : ∀ i j, Fm i j ∈ AA.carrier := fun i j =>
    cosetCoordinates_mem AA K β hβ hAK (hf i) j
  have hDA := det_mem_and_adjugate_mem AA Fm hFm
  have hD : (fun x => (h3mm K β f x).det) ∈ AA.carrier := hDA.1
  have hAdj : ∀ l j, (fun x => (h3mm K β f x).adjugate l j) ∈ AA.carrier :=
    hDA.2
  obtain ⟨P, hP, hA⟩ := AA.lat
  have hDinv : (fun x => (h3mm K β f x).det)⁻¹ ∈ AA.carrier :=
    inv_mem_of_valuation_eq_one hv AA.carrier P hP hA AA.one_mem AA.mul_mem _ hD hdet
  have hG : ∀ l, (fun x => h3co K β g x l) ∈ AA.carrier := fun l =>
    cosetCoordinates_mem AA K β hβ hAK hg l
  refine ⟨b, ?_, ?_, ?_⟩
  · intro j
    have key : b j = (∑ l, (fun x => h3co K β g x l) *
        (fun x => (h3mm K β f x).adjugate l j)) *
        (fun x => (h3mm K β f x).det)⁻¹ := by
      funext x
      rw [hbx, Matrix.inv_def]
      simp only [Pi.mul_apply, Finset.sum_apply, Pi.inv_apply, Matrix.vecMul, dotProduct,
        Matrix.smul_apply, smul_eq_mul, Finset.sum_mul, Ring.inverse_eq_inv]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [key]
    exact AA.mul_mem _ _ (Submodule.sum_mem _ fun l _ => AA.mul_mem _ _ (hG l) (hAdj l j)) hDinv
  · intro j x k
    have hT : IsUnit (h3T K β k).det := by
      refine isUnit_iff_ne_zero.mpr fun h0 => hDne (x + k) ?_
      rw [cosetCoordinateMatrix_add K β hβ f x k, Matrix.det_mul, h0, mul_zero]
    rw [hbx, hbx, cosetCoordinates_add K β hβ g x k, cosetCoordinateMatrix_add K β hβ f x k,
      Matrix.mul_inv_rev, Matrix.vecMul_vecMul, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hT, Matrix.one_mul]
  · funext x
    have e1 := cosetCoordinates_expand K β hβ g x 0
    have e2 := fun j => cosetCoordinates_expand K β hβ (f j) x 0
    rw [show ((0 : K) : N) = 0 from rfl, add_zero] at e1
    simp only [show ((0 : K) : N) = 0 from rfl, add_zero] at e2
    have hv' : (h3co K β g x ᵥ* (h3mm K β f x)⁻¹) ᵥ*
        h3mm K β f x = h3co K β g x := by
      rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (hFu x), Matrix.vecMul_one]
    have hw : ∀ l, ∑ j, (h3co K β g x ᵥ* (h3mm K β f x)⁻¹) j *
        h3co K β (f j) x l = h3co K β g x l := fun l => by
      have := congrFun hv' l
      exact this
    rw [Finset.sum_apply]
    simp only [Pi.mul_apply, hbx, e2]
    rw [e1]
    generalize h3co K β g x ᵥ* (h3mm K β f x)⁻¹ = w at hw ⊢
    simp only [← hw]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end family

end ReciprocityTheory.PGsh.L2
end
end
