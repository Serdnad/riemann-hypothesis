module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam.TwistMem

variable {F : Type} [Field F] [NumberField F]

theorem vecMul_mem_std (B : Matrix (Fin 2) (Fin 2) ℤ) {y : Fin 2 → F} (hy : y ∈ stdLat F) :
    Matrix.vecMul y (B.map (Int.cast : ℤ → F)) ∈ stdLat F := by
  intro j _
  have h0 := hy 0 (Set.mem_univ _)
  have h1 := hy 1 (Set.mem_univ _)
  have : Matrix.vecMul y (B.map (Int.cast : ℤ → F)) j = B 0 j • y 0 + B 1 j • y 1 := by
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, mul_comm]
  rw [this]
  exact Submodule.add_mem _ (Submodule.smul_of_tower_mem _ _ h0) (Submodule.smul_of_tower_mem _ _ h1)

theorem exists_lift_diff (N : ℕ) (A : Matrix (Fin 2) (Fin 2) ℤ) :
    ∃ B : Matrix (Fin 2) (Fin 2) ℤ,
      ((A.map (Int.cast : ℤ → ZMod N)).map (ZMod.cast : ZMod N → ℤ)).map (Int.cast : ℤ → F)
        = A.map (Int.cast : ℤ → F) + (N : F) • B.map (Int.cast : ℤ → F) := by
  have h : ∀ a : ℤ, ∃ b : ℤ, (ZMod.cast (a : ZMod N) : ℤ) = a + N * b := by
    intro a
    have h1 : ((a : ℤ) : ZMod N) = (((ZMod.cast (a : ZMod N) : ℤ) : ℤ) : ZMod N) := by
      simp
    obtain ⟨b, hb⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ N).1 h1
    exact ⟨b, by linarith⟩
  choose f hf using h
  refine ⟨A.map f, ?_⟩
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hf]
  push_cast
  ring

theorem vecMul_scalar (N : ℕ) (w : Fin 2 → F) :
    Matrix.vecMul w ((((N : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ))).map (Int.cast : ℤ → F)) = (N : F) • w := by
  ext j
  fin_cases j <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.one_apply, Matrix.natCast_apply, mul_comm]

theorem mem_twist_iff (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : ℕ) (L : Lat F)
    (A : Matrix (Fin 2) (Fin 2) ℤ) (v : Fin 2 → F) (hL : L ≤ stdLat F) :
    (v ∈ twist N L (A.map (Int.cast : ℤ → ZMod N)) ↔
      ∃ y ∈ L, ∃ w ∈ stdLat F, v = Matrix.vecMul y (A.map (Int.cast : ℤ → F)) + (N : F) • w) := by
  obtain ⟨B, hB⟩ := exists_lift_diff (F := F) N A
  unfold twist mulMat
  simp only [Submodule.mem_sup, Submodule.mem_map, LinearMap.restrictScalars_apply,
    Matrix.vecMulLinear_apply, hB, vecMul_scalar, Matrix.vecMul_add, Matrix.vecMul_smul]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, _, ⟨w, hw, rfl⟩, rfl⟩
    refine ⟨y, hy, Matrix.vecMul y (B.map (Int.cast : ℤ → F)) + w,
      Submodule.add_mem _ (vecMul_mem_std B (hL hy)) hw, ?_⟩
    rw [smul_add, add_assoc]
  · rintro ⟨y, hy, w, hw, rfl⟩
    refine ⟨_, ⟨y, hy, rfl⟩, _, ⟨w - Matrix.vecMul y (B.map (Int.cast : ℤ → F)),
      Submodule.sub_mem _ hw (vecMul_mem_std B (hL hy)), rfl⟩, ?_⟩
    rw [smul_sub]
    abel

end GlobalTheory.HilbFam.TwistMem
end
end

section

set_option autoImplicit false

noncomputable section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

variable {F : Type} [Field F] [NumberField F]


set_option autoImplicit false in
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
variable {F : Type} [Field F] [NumberField F] in
theorem _root_.GlobalTheory.HilbFam.exists_eq_split_of_hasLevel (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
    (N : ℕ) (L : _root_.GlobalTheory.HilbFam.Lat F) (hN : 0 < N) (hL : _root_.GlobalTheory.HilbFam.HasLevel N L) :
    ∃ (𝔞 𝔟 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (x : F), L = _root_.GlobalTheory.HilbFam.split 𝔞 𝔟 x := by
  obtain ⟨hNL, hLstd⟩ := hL
  have hLint : ∀ v ∈ L, ∀ i, v i ∈ (1 : Submodule (𝓞 F) F) := fun v hv i =>
    (Submodule.mem_pi.1 (hLstd hv)) i (Set.mem_univ i)
  have hN0 : (N : F) ≠ 0 := by exact_mod_cast hN.ne'
  have hsingle : ∀ i, Pi.single i (N : F) ∈ L := by
    intro i
    have hstd : (Pi.single i (1 : F) : Fin 2 → F) ∈ _root_.GlobalTheory.HilbFam.stdLat F := by
      refine Submodule.mem_pi.2 fun j _ => ?_
      by_cases hj : j = i
      · subst hj; simpa using (1 : Submodule (𝓞 F) F).one_le.1 le_rfl
      · simp [hj]
    have := hNL _ hstd
    convert this using 1
    ext j
    by_cases hj : j = i
    · subst hj
      simp [Algebra.smul_def]
    · simp [hj]
  let B0 : Submodule (𝓞 F) F := L.map (LinearMap.proj (R := 𝓞 F) (φ := fun _ : Fin 2 => F) 0)
  let C0 : Submodule (𝓞 F) F := L.comap (LinearMap.single (𝓞 F) (fun _ : Fin 2 => F) 1)
  have hB0 : B0 ≤ 1 := by
    rintro _ ⟨v, hv, rfl⟩
    exact hLint v hv 0
  have hC0 : C0 ≤ 1 := by
    intro c hc
    simpa using hLint _ hc 1
  let Bf : FractionalIdeal (𝓞 F)⁰ F := ⟨B0, FractionalIdeal.isFractional_of_le_one B0 hB0⟩
  let Cf : FractionalIdeal (𝓞 F)⁰ F := ⟨C0, FractionalIdeal.isFractional_of_le_one C0 hC0⟩
  have hBne : Bf ≠ 0 := by
    intro h
    have hmem : (N : F) ∈ Bf := by
      show (N : F) ∈ B0
      exact ⟨_, hsingle 0, by simp⟩
    rw [h] at hmem
    exact hN0 ((FractionalIdeal.mem_zero_iff _).1 hmem)
  have hCne : Cf ≠ 0 := by
    intro h
    have hmem : (N : F) ∈ Cf := by
      show Pi.single 1 (N : F) ∈ L
      exact hsingle 1
    rw [h] at hmem
    exact hN0 ((FractionalIdeal.mem_zero_iff _).1 hmem)
  have key : ∀ t ∈ (Bf : Submodule (𝓞 F) F) * ((Bf⁻¹ : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F),
      ∃ y : F, ∀ b ∈ Bf, (![t * b, y * b] : Fin 2 → F) ∈ L := by
    intro t ht
    refine Submodule.mul_induction_on ht ?_ ?_
    · intro b' hb' c hc
      obtain ⟨w, hw, hw0⟩ := (show b' ∈ B0 from hb')
      refine ⟨c * w 1, fun b hb => ?_⟩
      have hcb : c * b ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
        rw [← inv_mul_cancel₀ hBne]
        exact FractionalIdeal.mul_mem_mul hc hb
      obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1 hcb
      convert L.smul_mem r hw using 1
      ext i
      fin_cases i
      · simp [Algebra.smul_def, hr, ← hw0]
        ring
      · simp [Algebra.smul_def, hr]
        ring
    · rintro t₁ t₂ ⟨y₁, hy₁⟩ ⟨y₂, hy₂⟩
      refine ⟨y₁ + y₂, fun b hb => ?_⟩
      convert L.add_mem (hy₁ b hb) (hy₂ b hb) using 1
      ext i
      fin_cases i <;> simp <;> ring
  have h1 : (1 : F) ∈ (Bf : Submodule (𝓞 F) F) *
      ((Bf⁻¹ : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F) := by
    rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ hBne]
    exact FractionalIdeal.one_mem_one _
  obtain ⟨x, hx⟩ := key 1 h1
  refine ⟨Units.mk0 (FractionalIdeal.dual ℤ ℚ Cf) (FractionalIdeal.dual_ne_zero ℤ ℚ hCne),
    Units.mk0 Bf hBne, x, ?_⟩
  have hlat : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM
      (Units.mk0 (FractionalIdeal.dual ℤ ℚ Cf) (FractionalIdeal.dual_ne_zero ℤ ℚ hCne)) = Cf := by
    rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM_eq_dual, Units.val_mk0, FractionalIdeal.dual_dual]
  ext v
  unfold _root_.GlobalTheory.HilbFam.split
  rw [Submodule.mem_mk]
  change v ∈ L ↔ v 0 ∈ ((Units.mk0 Bf hBne : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) ∧
    v 1 - v 0 * x ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM
      (Units.mk0 (FractionalIdeal.dual ℤ ℚ Cf) (FractionalIdeal.dual_ne_zero ℤ ℚ hCne))
  rw [hlat, Units.val_mk0]
  change v ∈ L ↔ v 0 ∈ B0 ∧ Pi.single 1 (v 1 - v 0 * x) ∈ L
  constructor
  · intro hv
    refine ⟨⟨v, hv, rfl⟩, ?_⟩
    convert L.sub_mem hv (hx (v 0) ⟨v, hv, rfl⟩) using 1
    ext i
    fin_cases i <;> simp <;> ring
  · rintro ⟨hb, hc⟩
    convert L.add_mem (hx (v 0) hb) hc using 1
    ext i
    fin_cases i <;> simp <;> ring

end GlobalTheory.HilbFam
end
end

section

set_option autoImplicit false

noncomputable section

open Filter Topology

namespace GlobalTheory.HilbFam.LagDeriv

set_option autoImplicit false in
open Filter Topology in
private lemma hasDerivAt_inv_pow_mul_exp_div_one_add_mul (c y : ℂ) (j : ℕ) {z : ℂ} (hz : 1 + z * c ≠ 0) :
    HasDerivAt (fun w : ℂ ↦ (1 + w * c)⁻¹ ^ j * Complex.exp (y * w / (1 + w * c)))
      (-(j * c) * ((1 + z * c)⁻¹ ^ (j + 1) * Complex.exp (y * z / (1 + z * c))) +
        y * ((1 + z * c)⁻¹ ^ (j + 2) * Complex.exp (y * z / (1 + z * c)))) z := by
  have hu : HasDerivAt (fun w : ℂ ↦ 1 + w * c) c z := by
    simpa using ((hasDerivAt_id z).mul_const c).const_add 1
  have hinv : HasDerivAt (fun w : ℂ ↦ (1 + w * c)⁻¹) (-c / (1 + z * c) ^ 2) z := hu.inv hz
  have hpow : HasDerivAt (fun w : ℂ ↦ (1 + w * c)⁻¹ ^ j)
      (j * (1 + z * c)⁻¹ ^ (j - 1) * (-c / (1 + z * c) ^ 2)) z := hinv.pow j
  have hq : HasDerivAt (fun w : ℂ ↦ y * w / (1 + w * c)) (y / (1 + z * c) ^ 2) z := by
    refine (((hasDerivAt_id z).const_mul y).div hu hz).congr_deriv ?_
    simp only [id, mul_one]
    field_simp
    ring
  refine (hpow.mul hq.cexp).congr_deriv ?_
  rcases j with _ | j
  · simp [div_eq_mul_inv]
    ring
  · simp only [Nat.cast_succ, Nat.add_sub_cancel, inv_pow]
    field_simp
    ring

set_option autoImplicit false in
open Filter Topology in
private lemma rco_eq_zero_of_lt (k n m : ℕ) (hm : n < m) :
    _root_.GlobalTheory.HilbFam.rco k n m = 0 := by
  unfold _root_.GlobalTheory.HilbFam.rco
  simp [Nat.choose_eq_zero_of_lt hm]

set_option autoImplicit false in
open Filter Topology in
private lemma ascFactorial_succ_eq_mul_succ_ascFactorial (a e : ℕ) :
    a.ascFactorial (e + 1) = a * (a + 1).ascFactorial e := by
  induction e with
  | zero => simp [Nat.ascFactorial_succ]
  | succ e ih =>
    rw [Nat.ascFactorial_succ, ih, Nat.ascFactorial_succ]
    ring

set_option autoImplicit false in
open Filter Topology in
private lemma rco_succ_succ (k n m : ℕ) (hm : m ≤ n) :
    (_root_.GlobalTheory.HilbFam.rco k (n + 1) (m + 1) : ℤ) =
      -((k + n + m + 1 : ℕ) : ℤ) * _root_.GlobalTheory.HilbFam.rco k n (m + 1) +
        _root_.GlobalTheory.HilbFam.rco k n m := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  unfold _root_.GlobalTheory.HilbFam.rco
  rcases d with _ | e
  · simp
  · have h1 : m + (e + 1) + 1 - (m + 1) = e + 1 := by omega
    have h2 : m + (e + 1) - (m + 1) = e := by omega
    have h3 : m + (e + 1) - m = e + 1 := by omega
    rw [h1, h2, h3]
    have hc := Nat.choose_succ_right_eq (m + (e + 1)) m
    have hc' : m + (e + 1) - m = e + 1 := by omega
    rw [hc'] at hc
    have hs : (m + (e + 1) + 1).choose (m + 1) = (m + (e + 1)).choose m + (m + (e + 1)).choose (m + 1) :=
      Nat.choose_succ_succ' _ _
    have ha1 : (k + (m + 1)).ascFactorial (e + 1) = (k + (m + 1) + e) * (k + (m + 1)).ascFactorial e :=
      Nat.ascFactorial_succ
    have ha2 := ascFactorial_succ_eq_mul_succ_ascFactorial (k + m) e
    rw [hs, ha1, ha2]
    have hkm : k + m + 1 = k + (m + 1) := by omega
    rw [hkm]
    push_cast
    have hcz : ((m + (e + 1)).choose (m + 1) : ℤ) * (m + 1) = ((m + (e + 1)).choose m : ℤ) * (e + 1) := by
      exact_mod_cast hc
    rw [pow_succ]
    linear_combination ((-1 : ℤ) ^ e * ((k + (m + 1)).ascFactorial e : ℤ)) * hcz

set_option autoImplicit false in
open Filter Topology in
private lemma rco_mul_pow_mul_pow_succ_succ (k n m : ℕ) (hm : m ≤ n) (c y : ℂ) :
    (_root_.GlobalTheory.HilbFam.rco k (n + 1) (m + 1) : ℂ) * c ^ (n + 1 - (m + 1)) * y ^ (m + 1) =
      -(((k + n + (m + 1) : ℕ) : ℂ) * c) *
          ((_root_.GlobalTheory.HilbFam.rco k n (m + 1) : ℂ) * c ^ (n - (m + 1)) * y ^ (m + 1)) +
        y * ((_root_.GlobalTheory.HilbFam.rco k n m : ℂ) * c ^ (n - m) * y ^ m) := by
  have hZ := congrArg (Int.cast : ℤ → ℂ) (rco_succ_succ k n m hm)
  push_cast at hZ
  rw [hZ]
  rcases hm.lt_or_eq with hlt | rfl
  · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    have e1 : m + t + 1 + 1 - (m + 1) = t + 1 := by omega
    have e2 : m + t + 1 - (m + 1) = t := by omega
    have e3 : m + t + 1 - m = t + 1 := by omega
    rw [e1, e2, e3]
    push_cast
    ring
  · rw [rco_eq_zero_of_lt k m (m + 1) (Nat.lt_succ_self m)]
    simp only [Nat.sub_self, pow_zero]
    push_cast
    ring

set_option autoImplicit false in
open Filter Topology in
private lemma rco_succ_zero (k n : ℕ) :
    (_root_.GlobalTheory.HilbFam.rco k (n + 1) 0 : ℤ) =
      -((k + n : ℕ) : ℤ) * _root_.GlobalTheory.HilbFam.rco k n 0 := by
  unfold _root_.GlobalTheory.HilbFam.rco
  simp only [Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, add_zero, Nat.ascFactorial_succ]
  push_cast
  ring

set_option autoImplicit false in
open Filter Topology in
private lemma rco_mul_pow_mul_pow_succ_zero (k n : ℕ) (c y : ℂ) :
    (_root_.GlobalTheory.HilbFam.rco k (n + 1) 0 : ℂ) * c ^ (n + 1 - 0) * y ^ 0 =
      -(((k + n + 0 : ℕ) : ℂ) * c) *
        ((_root_.GlobalTheory.HilbFam.rco k n 0 : ℂ) * c ^ (n - 0) * y ^ 0) := by
  have hZ := congrArg (Int.cast : ℤ → ℂ) (rco_succ_zero k n)
  push_cast at hZ
  rw [hZ]
  simp only [Nat.sub_zero, pow_zero, add_zero]
  push_cast
  ring

set_option autoImplicit false in
open Filter Topology in
private lemma iteratedDeriv_inv_pow_mul_exp_eq_sum_rco (c y : ℂ) (n : ℕ) :
    ∀ k : ℕ, ∀ z : ℂ, 1 + z * c ≠ 0 →
      iteratedDeriv n (fun w : ℂ ↦ (1 + w * c)⁻¹ ^ k * Complex.exp (y * w / (1 + w * c))) z =
        ∑ m ∈ Finset.range (n + 1), (_root_.GlobalTheory.HilbFam.rco k n m : ℂ) * c ^ (n - m) *
          y ^ m * ((1 + z * c)⁻¹ ^ (k + n + m) * Complex.exp (y * z / (1 + z * c))) := by
  induction n with
  | zero =>
    intro k z _
    simp [_root_.GlobalTheory.HilbFam.rco]
  | succ n ih =>
    intro k z hz
    have hopen : IsOpen {w : ℂ | 1 + w * c ≠ 0} :=
      isOpen_ne_fun (by fun_prop) continuous_const
    have hev : iteratedDeriv n (fun w : ℂ ↦ (1 + w * c)⁻¹ ^ k * Complex.exp (y * w / (1 + w * c))) =ᶠ[𝓝 z]
        fun w ↦ ∑ m ∈ Finset.range (n + 1), (_root_.GlobalTheory.HilbFam.rco k n m : ℂ) * c ^ (n - m) *
          y ^ m * ((1 + w * c)⁻¹ ^ (k + n + m) * Complex.exp (y * w / (1 + w * c))) :=
      Filter.eventually_of_mem (hopen.mem_nhds hz) fun w hw ↦ ih k w hw
    rw [iteratedDeriv_succ, hev.deriv_eq]
    have hd := HasDerivAt.fun_sum (u := Finset.range (n + 1)) (fun m _ ↦
      (hasDerivAt_inv_pow_mul_exp_div_one_add_mul c y (k + n + m) hz).const_mul
        ((_root_.GlobalTheory.HilbFam.rco k n m : ℂ) * c ^ (n - m) * y ^ m))
    rw [hd.deriv]
    set H : ℕ → ℂ := fun j ↦ (1 + z * c)⁻¹ ^ j * Complex.exp (y * z / (1 + z * c)) with hH
    set C : ℕ → ℕ → ℂ := fun n m ↦
      (_root_.GlobalTheory.HilbFam.rco k n m : ℂ) * c ^ (n - m) * y ^ m with hC
    change ∑ m ∈ Finset.range (n + 1), C n m * (-(((k + n + m : ℕ) : ℂ) * c) * H (k + n + m + 1) +
        y * H (k + n + m + 2)) = ∑ m ∈ Finset.range (n + 1 + 1), C (n + 1) m * H (k + (n + 1) + m)
    have hA : ∑ m ∈ Finset.range (n + 1 + 1), -(((k + n + m : ℕ) : ℂ) * c) * C n m * H (k + n + m + 1) =
        ∑ m ∈ Finset.range (n + 1), -(((k + n + m : ℕ) : ℂ) * c) * C n m * H (k + n + m + 1) := by
      rw [Finset.sum_range_succ]
      simp [hC, rco_eq_zero_of_lt k n (n + 1) (Nat.lt_succ_self n)]
    have hT : ∀ m ∈ Finset.range (n + 1), C (n + 1) (m + 1) * H (k + (n + 1) + (m + 1)) =
        -(((k + n + (m + 1) : ℕ) : ℂ) * c) * C n (m + 1) * H (k + n + (m + 1) + 1) +
          C n m * (y * H (k + n + m + 2)) := by
      intro m hm
      have hmn : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
      simp only [hC]
      rw [rco_mul_pow_mul_pow_succ_succ k n m hmn c y]
      have e1 : k + (n + 1) + (m + 1) = k + n + (m + 1) + 1 := by omega
      have e2 : k + n + m + 2 = k + n + (m + 1) + 1 := by omega
      rw [e1, e2]
      ring
    have h0 : C (n + 1) 0 * H (k + (n + 1) + 0) = -(((k + n + 0 : ℕ) : ℂ) * c) * C n 0 * H (k + n + 0 + 1) := by
      simp only [hC]
      rw [rco_mul_pow_mul_pow_succ_zero k n c y]
      have e1 : k + (n + 1) + 0 = k + n + 0 + 1 := by omega
      rw [e1]
    have hS : ∑ m ∈ Finset.range (n + 1), -(((k + n + (m + 1) : ℕ) : ℂ) * c) * C n (m + 1) *
          H (k + n + (m + 1) + 1) + -(((k + n + 0 : ℕ) : ℂ) * c) * C n 0 * H (k + n + 0 + 1) =
        ∑ m ∈ Finset.range (n + 1), -(((k + n + m : ℕ) : ℂ) * c) * C n m * H (k + n + m + 1) := by
      rw [← Finset.sum_range_succ' (fun m ↦ -(((k + n + m : ℕ) : ℂ) * c) * C n m * H (k + n + m + 1))]
      exact hA
    have hB : ∑ m ∈ Finset.range (n + 1), C n m * (-(((k + n + m : ℕ) : ℂ) * c) * H (k + n + m + 1)) =
        ∑ m ∈ Finset.range (n + 1), -(((k + n + m : ℕ) : ℂ) * c) * C n m * H (k + n + m + 1) :=
      Finset.sum_congr rfl fun m _ ↦ by ring
    conv_rhs => rw [Finset.sum_range_succ', Finset.sum_congr rfl hT, Finset.sum_add_distrib, h0]
    simp only [mul_add, Finset.sum_add_distrib]
    rw [hB, ← hS]
    ring


set_option autoImplicit false in
open Filter Topology in
theorem _root_.GlobalTheory.HilbFam.LagDeriv.iteratedDeriv_zero_eq_lag : ∀ (k n : ℕ) (c y : ℂ),
    iteratedDeriv n (fun z : ℂ ↦ (1 + z * c)⁻¹ ^ k * Complex.exp (y * z / (1 + z * c))) 0 =
      _root_.GlobalTheory.HilbFam.lag k n c y := by
  intro k n c y
  rw [iteratedDeriv_inv_pow_mul_exp_eq_sum_rco c y n k 0 (by simp)]
  unfold _root_.GlobalTheory.HilbFam.lag
  simp

end GlobalTheory.HilbFam.LagDeriv
end
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

theorem lag_homogeneous : ∀ (k n : ℕ) (c y v : ℂ), lag k n (v * c) (v * y) = v ^ n * lag k n c y ∧ lag k n 0 y = y ^ n := by
  intro k n c y v
  refine ⟨?_, ?_⟩
  · unfold lag
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hmn : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    have h : v ^ n = v ^ (n - m) * v ^ m := by rw [← pow_add, Nat.sub_add_cancel hmn]
    rw [h, mul_pow, mul_pow]; ring
  · unfold lag
    rw [Finset.sum_range_succ, Finset.sum_eq_zero]
    · simp [rco]
    · intro m hm
      have hmn : n - m ≠ 0 := Nat.sub_ne_zero_of_lt (Finset.mem_range.mp hm)
      simp [hmn]

end GlobalTheory.HilbFam
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

theorem count_word_eq (I : Type) [Fintype I] [DecidableEq I] (κ : I → ℕ) (i : I) :
    (word κ).count i = κ i := by
  unfold word
  rw [List.count_flatMap]
  simp [List.count_replicate, Function.comp_def]

end GlobalTheory.HilbFam
end
