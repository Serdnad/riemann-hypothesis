module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower

@[expose] public section

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ

private lemma exists_isDiam_of_coprime (N l d : ℕ) (hNl : Nat.Coprime N l) (hd : Nat.Coprime d N) :
    ∃ γ : SL(2, ℤ), IsDiam N l d γ := by
  obtain ⟨k, hkN, hkl⟩ := Nat.chineseRemainder hNl d 1
  have hk1 : Nat.Coprime k N := by
    unfold Nat.Coprime
    rw [Nat.ModEq.gcd_eq hkN]
    exact hd
  have hk2 : Nat.Coprime k l := by
    unfold Nat.Coprime
    rw [Nat.ModEq.gcd_eq hkl]
    simp
  have hk : Nat.Coprime k (N * l) := Nat.Coprime.mul_right hk1 hk2
  have hg : Int.gcd (k : ℤ) ((N * l : ℕ) : ℤ) = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact hk
  have hb := Int.gcd_eq_gcd_ab (k : ℤ) ((N * l : ℕ) : ℤ)
  rw [hg] at hb
  have hdet : (!![Int.gcdA (k : ℤ) ((N * l : ℕ) : ℤ), -Int.gcdB (k : ℤ) ((N * l : ℕ) : ℤ);
      ((N * l : ℕ) : ℤ), (k : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
    rw [Matrix.det_fin_two_of]
    push_cast at hb ⊢
    linarith
  refine ⟨(⟨_, hdet⟩ : SL(2, ℤ)), Subgroup.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
  · refine CongruenceSubgroup.Gamma0_mem.2 ?_
    simp
  · refine CongruenceSubgroup.Gamma0_mem.2 ?_
    simp
  · simp only [en]
    simp
    exact (ZMod.natCast_eq_natCast_iff _ _ _).2 hkN

theorem isDiam_sgD_of_prime : ∀ (N l d : ℕ), l.Prime → 0 < N → Nat.Coprime N l → Nat.Coprime d N →
    IsDiam N l d (sgD N l d) := by
  intro N l d _ _ hNl hd
  exact Classical.epsilon_spec (exists_isDiam_of_coprime N l d hNl hd)

end GlobalTheory.KZ
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory

theorem diam_exists : ∀ (N l d : ℕ), 0 < N → Nat.Coprime N l → Nat.Coprime d N → ∃ γ : SL(2, ℤ), IsDiam N l d γ := by
  intro N l d _ hNl hdN

  obtain ⟨d', hd'N, hd'l⟩ := Nat.chineseRemainder hNl d 1
  have h1 : Nat.Coprime d' N := by
    unfold Nat.Coprime; rw [Nat.ModEq.gcd_eq hd'N]; exact hdN
  have h2 : Nat.Coprime d' l := by
    unfold Nat.Coprime; rw [Nat.ModEq.gcd_eq hd'l]; simp
  have h3 : Nat.Coprime d' (N * l) := Nat.Coprime.mul_right h1 h2
  have hg : Int.gcd (d' : ℤ) ((N * l : ℕ) : ℤ) = 1 := by rw [Int.gcd_natCast_natCast]; exact h3
  have hb := Int.gcd_eq_gcd_ab (d' : ℤ) ((N * l : ℕ) : ℤ)
  rw [hg] at hb
  set a := Int.gcdA (d' : ℤ) ((N * l : ℕ) : ℤ)
  set b := Int.gcdB (d' : ℤ) ((N * l : ℕ) : ℤ)
  let M : Matrix (Fin 2) (Fin 2) ℤ := !![a, -b; ((N * l : ℕ) : ℤ), (d' : ℤ)]
  have hdet : M.det = 1 := by
    simp only [M, Matrix.det_fin_two_of]
    push_cast at hb ⊢
    linarith
  let γ : SL(2, ℤ) := ⟨M, hdet⟩
  have hγ : (γ : Matrix (Fin 2) (Fin 2) ℤ) = M := rfl
  refine ⟨γ, Subgroup.mem_inf.2 ⟨CongruenceSubgroup.Gamma0_mem.2 ?_, CongruenceSubgroup.Gamma0_mem.2 ?_⟩, ?_⟩
  · rw [hγ]; simp [M]
  · rw [hγ]; simp [M]
  · simp only [en, hγ, M]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.cons_val_zero]
    push_cast
    exact (ZMod.natCast_eq_natCast_iff _ _ _).2 hd'N

end GlobalTheory
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem det_leadingBlock_one_add_vecMulVec_rankOne {k : Type} [Field k] {n : ℕ} (p q : Fin n → k) (a : Fin n) (c : k)
    (hpq : ∀ i, p i * q i = if i = a then c else 0) (m : Fin n) :
    ((1 + Matrix.vecMulVec p q).toSquareBlockProp fun i => i ≤ m).det = if a ≤ m then 1 + c else 1 := by
  have hM : ((1 + Matrix.vecMulVec p q).toSquareBlockProp fun i => i ≤ m) =
      1 + Matrix.replicateCol Unit (fun i : {i // i ≤ m} => p i) * Matrix.replicateRow Unit (fun i : {i // i ≤ m} => q i) := by
    ext i j
    simp [Matrix.toSquareBlockProp_def, Matrix.one_apply, Subtype.ext_iff, Matrix.vecMulVec_apply, Matrix.mul_apply]
  rw [hM, Matrix.det_one_add_replicateCol_mul_replicateRow]
  have hs : (fun i : {i // i ≤ m} => q i) ⬝ᵥ (fun i : {i // i ≤ m} => p i) = ∑ i : {i // i ≤ m}, (if (i : Fin n) = a then c else 0) := by
    simp only [dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm, hpq]
  rw [hs]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨a, h⟩]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro e; exact hb (Subtype.ext e)
    · simp
  · rw [Finset.sum_eq_zero]
    · simp
    · intro b _
      rw [if_neg]
      intro e; exact h (e ▸ b.2)

theorem rankOne_ev_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (χ : kˣ →* ℂˣ) :
    ev χ (1 : k) = 1 := by
  unfold ev
  rw [dif_pos (by simp)]
  have : Units.mk0 (1 : k) one_ne_zero = 1 := by ext; simp
  simp [this]

theorem rankOne_ev_unit {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (χ : kˣ →* ℂˣ)
    (u : kˣ) (hu : valuation k (u : k) = 1) : ev χ (u : k) = (χ u : ℂ) := by
  unfold ev
  rw [dif_pos hu]
  simp

theorem rankOne_telescope {G : Type} [CommGroup G] (n : ℕ) (F : ℕ → G) (hF : F n = 1) (a : ℕ) (ha : a < n) :
    ∏ i ∈ Finset.range n, (if a ≤ i then F i / F (i + 1) else 1) = F a := by
  rw [← Finset.prod_filter]
  have hfil : (Finset.range n).filter (fun i => a ≤ i) = Finset.Ico a n := by
    ext i; simp [Finset.mem_Ico, and_comm]
  rw [hfil]
  have h2 : ∀ i, F i / F (i + 1) = (F (i + 1))⁻¹ / (F i)⁻¹ := fun i => by
    rw [div_eq_mul_inv, div_eq_mul_inv, inv_inv, mul_comm]
  simp_rw [h2]
  rw [Finset.prod_Ico_div (f := fun i => (F i)⁻¹) ha.le, hF]
  simp

theorem theta_rankOne : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ) (g : GL (Fin n) k) (p q : Fin n → k) (a : Fin n) (u : kˣ), valuation k (u : k) = 1 → g.val = 1 + Matrix.vecMulVec p q → (∀ i, p i * q i = if i = a then (u : k) - 1 else 0) → theta ψ g = (ψ a u : ℂ) := by
  intro k _ _ _ _ n ψ g p q a u hu hg hpq
  have hmin : ∀ m, minor g m = if a ≤ m then (u : k) else 1 := by
    intro m
    unfold minor
    rw [hg, det_leadingBlock_one_add_vecMulVec_rankOne p q a _ hpq m]
    simp
  let F : ℕ → ℂˣ := fun j => if h : j < n then ψ ⟨j, h⟩ u else 1
  have hterm : ∀ m : Fin n, ev (ψ m / nxt ψ m) (minor g m) = ((if a ≤ m then F m / F (m + 1) else 1 : ℂˣ) : ℂ) := by
    intro m
    rw [hmin]
    split_ifs with h
    · rw [rankOne_ev_unit _ _ hu]
      congr 1
      simp only [F, MonoidHom.div_apply, dif_pos m.2]
      congr 1
      unfold nxt
      split_ifs <;> rfl
    · rw [rankOne_ev_one]; simp
  unfold theta
  simp_rw [hterm, Fin.le_iff_val_le_val]
  rw [← Units.coe_prod, Fin.prod_univ_eq_prod_range (fun i => if (a : ℕ) ≤ i then F i / F (i + 1) else 1) n]
  · rw [rankOne_telescope n F (by simp [F]) a a.2]
    simp [F]

end GlobalTheory.PsType
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ.PolAct

variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]

def homF (A : Submodule R M) (w : ℕ) : Submodule R ((Fin 2 → R) → M) where
  carrier := {b | ∃ c : Fin (w + 1) → M, (∀ i, c i ∈ A) ∧
    ∀ u, b u = ∑ i : Fin (w + 1), (u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) • c i}
  zero_mem' := ⟨0, fun _ => A.zero_mem, fun u => by simp⟩
  add_mem' := by
    rintro a b ⟨c, hc, ha⟩ ⟨d, hd, hb⟩
    exact ⟨c + d, fun i => A.add_mem (hc i) (hd i), fun u => by
      simp [ha, hb, Finset.sum_add_distrib]⟩
  smul_mem' := by
    rintro r b ⟨c, hc, hb⟩
    exact ⟨r • c, fun i => A.smul_mem r (hc i), fun u => by
      simp only [Pi.smul_apply, hb, Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _⟩

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] in
private lemma const_mem_homF_zero {A : Submodule R M} {x : M} (hx : x ∈ A) :
    (fun _ : Fin 2 → R => x) ∈ _root_.GlobalTheory.KZ.PolAct.homF A 0 :=
  ⟨fun _ => x, fun _ => hx, fun u => by simp⟩

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] in
private lemma coord_zero_smul_mem_homF_succ {A : Submodule R M} {n : ℕ}
    {b : (Fin 2 → R) → M} (hb : b ∈ _root_.GlobalTheory.KZ.PolAct.homF A n) :
    (fun u => u 0 • b u) ∈ _root_.GlobalTheory.KZ.PolAct.homF A (n + 1) := by
  obtain ⟨c, hc, hbu⟩ := hb
  refine ⟨Fin.cons 0 c, fun i => ?_, fun u => ?_⟩
  · refine Fin.cases ?_ (fun j => ?_) i
    · simp [A.zero_mem]
    · simp [hc]
  · dsimp only
    rw [hbu, Finset.smul_sum]
    conv_rhs => rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, smul_zero, zero_add, Fin.val_succ,
      Nat.add_sub_add_right, smul_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    ring

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] in
private lemma coord_one_smul_mem_homF_succ {A : Submodule R M} {n : ℕ}
    {b : (Fin 2 → R) → M} (hb : b ∈ _root_.GlobalTheory.KZ.PolAct.homF A n) :
    (fun u => u 1 • b u) ∈ _root_.GlobalTheory.KZ.PolAct.homF A (n + 1) := by
  obtain ⟨c, hc, hbu⟩ := hb
  refine ⟨fun j => if h : (j : ℕ) < n + 1 then c ⟨j, h⟩ else 0, fun j => ?_, fun u => ?_⟩
  · dsimp only
    split_ifs
    · exact hc _
    · exact A.zero_mem
  · dsimp only
    rw [hbu, Finset.smul_sum]
    conv_rhs => rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.is_lt, dif_pos, Fin.val_last, lt_self_iff_false,
      dif_neg, not_false_eq_true, smul_zero, add_zero, Fin.eta, smul_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi : n + 1 - (i : ℕ) = n - (i : ℕ) + 1 := Nat.sub_add_comm (Nat.lt_succ_iff.mp i.isLt)
    rw [hi, pow_succ]
    congr 1
    ring

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] in
private lemma linear_form_smul_mem_homF_succ {A : Submodule R M} {n : ℕ}
    {b : (Fin 2 → R) → M} (hb : b ∈ _root_.GlobalTheory.KZ.PolAct.homF A n) (α β : R) :
    (fun u => (α * u 0 + β * u 1) • b u) ∈ _root_.GlobalTheory.KZ.PolAct.homF A (n + 1) := by
  have h := (_root_.GlobalTheory.KZ.PolAct.homF A (n + 1)).add_mem
    ((_root_.GlobalTheory.KZ.PolAct.homF A (n + 1)).smul_mem α
      (coord_zero_smul_mem_homF_succ hb))
    ((_root_.GlobalTheory.KZ.PolAct.homF A (n + 1)).smul_mem β
      (coord_one_smul_mem_homF_succ hb))
  convert h using 1
  funext u
  simp [add_smul, mul_smul]

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] in
private lemma linear_form_pow_smul_mem_homF_add {A : Submodule R M} {n : ℕ}
    {b : (Fin 2 → R) → M} (hb : b ∈ _root_.GlobalTheory.KZ.PolAct.homF A n) (α β : R) :
    ∀ k : ℕ, (fun u => (α * u 0 + β * u 1) ^ k • b u) ∈
      _root_.GlobalTheory.KZ.PolAct.homF A (n + k) := by
  intro k
  induction k with
  | zero => simpa using hb
  | succ k ih =>
    have h := linear_form_smul_mem_homF_succ ih α β
    show _ ∈ _root_.GlobalTheory.KZ.PolAct.homF A (n + k + 1)
    convert h using 1
    funext u
    rw [pow_succ, mul_comm]
    exact (smul_smul (α * u 0 + β * u 1)
      ((α * u 0 + β * u 1) ^ k) (b u)).symm


open scoped MatrixGroups TensorProduct in
open Matrix in
variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] in
theorem _root_.GlobalTheory.KZ.PolAct.subst_mem {A : Submodule R M} {w : ℕ} (φ : M →ₗ[R] M)
    (hφ : ∀ a ∈ A, φ a ∈ A)
    (m : Matrix (Fin 2) (Fin 2) R) {b : (Fin 2 → R) → M}
    (hb : b ∈ _root_.GlobalTheory.KZ.PolAct.homF A w) :
    (fun u => φ (b (m *ᵥ u))) ∈ _root_.GlobalTheory.KZ.PolAct.homF A w := by
  obtain ⟨c, hc, hbu⟩ := hb
  have hterm : ∀ i : Fin (w + 1), (fun u : Fin 2 → R =>
      ((m 0 0 * u 0 + m 0 1 * u 1) ^ (i : ℕ) * (m 1 0 * u 0 + m 1 1 * u 1) ^ (w - (i : ℕ))) •
        φ (c i)) ∈ _root_.GlobalTheory.KZ.PolAct.homF A w := by
    intro i
    have h0 := const_mem_homF_zero (hφ _ (hc i))
    have h1 := linear_form_pow_smul_mem_homF_add h0 (m 1 0) (m 1 1) (w - i)
    have h2 := linear_form_pow_smul_mem_homF_add h1 (m 0 0) (m 0 1) i
    have hdeg : 0 + (w - (i : ℕ)) + i = w := by
      have := i.isLt
      omega
    rw [hdeg] at h2
    convert h2 using 1
    funext u
    rw [mul_smul]
  have hsum := Submodule.sum_mem (_root_.GlobalTheory.KZ.PolAct.homF A w)
    (t := Finset.univ) (fun i _ => hterm i)
  convert hsum using 1
  funext u

  simp [hbu, map_sum, map_smul, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Finset.sum_apply]


open scoped MatrixGroups TensorProduct in
open Matrix in
variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] in
theorem _root_.GlobalTheory.KZ.PolAct.act_mem_pol {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    {ε : Ω →+* ℂ} (X : _root_.GlobalTheory.KZ.Tower Ω ε) (l w : ℕ) [Fact l.Prime]
    (m : Matrix (Fin 2) (Fin 2) ℤ)
    (h : ∀ a ∈ X.A l, X.kmap l
      (X.sl (_root_.GlobalTheory.KZ.toGQ m)).toRingEquiv a ∈ X.A l) :
    ∀ b ∈ X.Pol l w,
      X.act l m b ∈
        X.Pol l w := by
  intro b hb
  exact _root_.GlobalTheory.KZ.PolAct.subst_mem (A := X.A l) (w := w) _ h _ hb

end GlobalTheory.KZ.PolAct
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem minor_of_triangular (g : GL (Fin n) k) (m : Fin n)
    (h : (∀ i j : Fin n, i < j → g.val i j = 0) ∨ ∀ i j : Fin n, j < i → g.val i j = 0) :
    minor g m = ∏ i ∈ Finset.univ.filter (fun i => i ≤ m), g.val i i := by
  unfold minor
  have hdet : (g.val.toSquareBlockProp fun i => i ≤ m).det = ∏ i : {i : Fin n // i ≤ m}, g.val i i := by
    rcases h with h | h
    · rw [Matrix.det_of_lowerTriangular]
      · rfl
      · intro i j hij
        exact h i j (OrderDual.toDual_lt_toDual.1 hij)
    · rw [Matrix.det_of_upperTriangular]
      · rfl
      · intro i j hij
        exact h i j hij
  rw [hdet]
  exact (Finset.prod_subtype (Finset.univ.filter (fun i => i ≤ m)) (p := fun i => i ≤ m)
    (fun x => by simp) (fun i => g.val i i)).symm

theorem prod_div_nxt (ψ : Fin n → kˣ →* ℂˣ) (a : Fin n) (u : kˣ) :
    ∏ m ∈ Finset.univ.filter (fun m => a ≤ m), (ψ m / nxt ψ m) u = ψ a u := by
  let f : ℕ → ℂˣ := fun j => if h : j < n then ψ ⟨j, h⟩ u else 1
  have hf : ∀ m : Fin n, f m = ψ m u := fun m => by
    show (if h : (m : ℕ) < n then ψ ⟨m, h⟩ u else 1) = ψ m u
    rw [dite_eq_left m.isLt]
  have hnx : ∀ m : Fin n, nxt ψ m u = f (m + 1) := by
    intro m
    unfold nxt
    split_ifs with h
    · simp [f, h]
    · simp [f, h]
  let G : ℕ → ℂˣ := fun j => if (a : ℕ) ≤ j then (f (j + 1))⁻¹ / (f j)⁻¹ else 1
  rw [Finset.prod_filter]
  have hterm : ∀ m : Fin n, (if a ≤ m then (ψ m / nxt ψ m) u else 1) = G m := by
    intro m
    simp only [G, Fin.le_def, MonoidHom.div_apply, hnx, ← hf m, inv_div_inv]
  rw [Finset.prod_congr rfl fun m _ => hterm m, Fin.prod_univ_eq_prod_range G n, ← Finset.prod_filter]
  have hs : (Finset.range n).filter (fun j => (a : ℕ) ≤ j) = Finset.Ico (a : ℕ) n := by
    ext j; simp; omega
  rw [hs, Finset.prod_Ico_div (f := fun j => (f j)⁻¹) a.isLt.le]
  simp [f, hf a]

theorem theta_of_triangular : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ) (g : GL (Fin n) k) (t : Fin n → kˣ), (∀ i, valuation k (t i : k) = 1) → (∀ i, g.val i i = t i) → ((∀ i j : Fin n, i < j → g.val i j = 0) ∨ ∀ i j : Fin n, j < i → g.val i j = 0) → theta ψ g = ∏ i, (ψ i (t i) : ℂ) := by
  intro k _ _ _ _ n ψ g t ht hd htri
  have hmin : ∀ m, minor g m = ((∏ i ∈ Finset.univ.filter (fun i => i ≤ m), t i : kˣ) : k) := by
    intro m
    rw [minor_of_triangular g m htri, Units.coe_prod]
    exact Finset.prod_congr rfl fun i _ => hd i
  have hev : ∀ (χ : kˣ →* ℂˣ) (u : kˣ), valuation k (u : k) = 1 → ev χ u = χ u := by
    intro χ u hu
    unfold ev
    rw [dite_eq_left hu]
    congr 2
    ext
    rfl
  have hval : ∀ s : Finset (Fin n), valuation k ((∏ i ∈ s, t i : kˣ) : k) = 1 := by
    intro s
    rw [Units.coe_prod, map_prod]
    exact Finset.prod_eq_one fun i _ => ht i
  unfold theta
  rw [Finset.prod_congr rfl fun m _ => by rw [hmin m, hev _ _ (hval _)]]
  rw [← Units.coe_prod, ← Units.coe_prod]
  congr 1
  simp only [map_prod]
  rw [Finset.prod_comm' (t' := Finset.univ) (s' := fun i => Finset.univ.filter (fun m => i ≤ m))
    (by intro x y; simp)]
  exact Finset.prod_congr rfl fun i _ => prod_div_nxt ψ i (t i)

end GlobalTheory.PsType
end

section

open GlobalTheory.AlmostEt

namespace GlobalTheory.AlmostEt

theorem derOn_adjoin_mem_span : ∀ (A S M : Type) [CommRing A] [CommRing S] [Algebra A S]
    [AddCommGroup M] [Module S M] (s : Set S) (D : S → M), IsDerOn (Algebra.adjoin A s) D →
    ∀ x ∈ Algebra.adjoin A s, D x ∈ Submodule.span S (D '' s) := by
  intro A S M _ _ _ _ _ s D hD x hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | algebraMap r => rw [hD.alg]; exact zero_mem _
  | add x y hx hy ihx ihy => rw [hD.add x hx y hy]; exact add_mem ihx ihy
  | mul x y hx hy ihx ihy =>
    rw [hD.mul x hx y hy]
    exact add_mem (Submodule.smul_mem _ _ ihy) (Submodule.smul_mem _ _ ihx)

end GlobalTheory.AlmostEt
end

section

namespace GlobalTheory.CyclotomicQExpansion
open GlobalTheory.KZ

theorem exp_sl_upper (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (g : GQ) (hg : ent g 1 0 = 0) (f : X.K) :
    X.exp (X.sl g f) = sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) (X.exp f) := by
  apply GlobalTheory.CyclotomicQExpansion.Api.exp_sl_upper <;> assumption

end GlobalTheory.CyclotomicQExpansion
end
