module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardExponentTuplesModEqOneOfPrimeNotDvd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle259
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle260
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle254
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
import Aesop.Main
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle003

@[expose] public section

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.card_exponent_tuples_modEq_one_of_prime_not_dvd : ∀ q l m k : ℕ, 2 ≤ q → l.Prime → 0 < m → ¬ l ∣ m → Reg q m k → (Finset.univ.filter fun a : Fin l → Fin m => k * ∑ i ∈ Finset.range l, q ^ (m * i) ≡ ∑ j : Fin l, k * q ^ (j : ℕ) * (q ^ l) ^ (a j : ℕ) [MOD (q ^ l) ^ m - 1]).card ≡ 1 [MOD l] := by
  first | (exact @GlobalTheory.ExpCount.count_one_mod) | (exact GlobalTheory.ExpCount.count_one_mod) | (intros; apply GlobalTheory.ExpCount.count_one_mod  <;> assumption)
end

section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef


theorem _root_.GlobalTheory.T.isRat_of_hankel_eventually_eq_zero : ∀ (F : Type) [Field F] (φ : PowerSeries F) (N : ℕ), (∀ n, N ≤ n → hankel (fun i => PowerSeries.coeff i φ) n = 0) → IsRat φ := by
  first | exact @GlobalTheory.Nef.isRat_of_hankel_eventually_zero | exact GlobalTheory.Nef.isRat_of_hankel_eventually_zero | (intros; apply GlobalTheory.Nef.isRat_of_hankel_eventually_zero <;> assumption)
end

section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef


theorem _root_.GlobalTheory.T.functionFieldPlaceOrder_calculus : ∀ (k F : Type) [Field k] [Field F] [Algebra k F], ∀ v : Place k F, (∀ x y : F, x ≠ 0 → y ≠ 0 → ord v (x * y) = ord v x + ord v y) ∧ (∀ x : F, x ≠ 0 → ∀ m : ℤ, ord v (x ^ m) = m * ord v x) ∧ (∀ x : F, x ≠ 0 → (v.1 x ≤ 1 ↔ 0 ≤ ord v x)) ∧ (∀ x : F, x ≠ 0 → (v.1 x = 1 ↔ ord v x = 0)) ∧ (∀ x y : F, x ≠ 0 → y ≠ 0 → (v.1 x ≤ v.1 y ↔ ord v y ≤ ord v x)) ∧ (∃ π : F, π ≠ 0 ∧ ord v π = 1) ∧ (∀ (n : ℕ) (x : Fin n → F), x ≠ 0 → ∃ i, x i ≠ 0 ∧ nrm v x = v.1 (x i) ∧ ordVec v x = ord v (x i) ∧ ∀ j, v.1 (x j) ≤ v.1 (x i)) ∧ (∀ (n : ℕ) (x : Fin n → F) (c : F), nrm v (c • x) = v.1 c * nrm v x) ∧ (∀ (n : ℕ) (u : Matrix (Fin n) (Fin n) F) (x : Fin n → F), Unimod v u → nrm v (u.mulVec x) = nrm v x) ∧ (∀ (n : ℕ) (u u' : Matrix (Fin n) (Fin n) F), Unimod v u → Unimod v u' → Unimod v (u * u') ∧ Unimod v u⁻¹) := by
  first | exact @GlobalTheory.Nef.ord_calculus | exact GlobalTheory.Nef.ord_calculus | (intros; apply GlobalTheory.Nef.ord_calculus <;> assumption)
end

section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef


theorem _root_.GlobalTheory.T.hankelDeterminant_integral_of_quotient : ∀ (O F : Type) [CommRing O] [Field F] (ι : O →+* F) (e ψ : PowerSeries O) (φ : PowerSeries F) (n : ℕ), PowerSeries.map ι e * φ = PowerSeries.map ι ψ → ∃ z : O, ι z = ι (PowerSeries.constantCoeff e) ^ (2 * (n + 1)) * hankel (fun i => PowerSeries.coeff i φ) n := by
  first | exact @GlobalTheory.Nef.hankel_integral | exact GlobalTheory.Nef.hankel_integral | (intros; apply GlobalTheory.Nef.hankel_integral <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SquareLiftLemmas

open CategoryTheory GlobalTheory.AnPer GlobalTheory.AnPer.Charts

def liftSq {g : ℕ} {O C : Type} [CommRing O] [CommRing C] (ρ : O →+* C) (n : Fin g → C)
    (hn : ∀ a b, n a * n b = 0) : TrivSqZeroExt O (Fin g → O) →+* C where
  toFun x := ρ x.fst + ∑ a, ρ (x.snd a) * n a
  map_one' := by simp
  map_zero' := by simp
  map_add' x y := by
    simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, Pi.add_apply, map_add (f := _), add_mul,
      Finset.sum_add_distrib]
    ring
  map_mul' x y := by
    have h0 : (∑ a, ρ (x.snd a) * n a) * (∑ b, ρ (y.snd b) * n b) = 0 := by
      rw [Finset.sum_mul_sum]
      refine Finset.sum_eq_zero fun a _ ↦ Finset.sum_eq_zero fun b _ ↦ ?_
      rw [mul_mul_mul_comm, hn, mul_zero]
    have h1 : ∀ a, ρ ((x * y).snd a) * n a =
        ρ x.fst * (ρ (y.snd a) * n a) + (ρ (x.snd a) * n a) * ρ y.fst := fun a ↦ by
      have : (x * y).snd a = x.fst * y.snd a + x.snd a * y.fst := by
        simp [TrivSqZeroExt.snd_mul, mul_comm]
      rw [this, map_add (f := _), map_mul, map_mul]; ring
    rw [add_mul, mul_add, mul_add, h0, add_zero, TrivSqZeroExt.fst_mul, map_mul]
    simp only [h1, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    ring

theorem liftSq_apply {g : ℕ} {O C : Type} [CommRing O] [CommRing C] (ρ : O →+* C) (n : Fin g → C)
    (hn : ∀ a b, n a * n b = 0) (x : TrivSqZeroExt O (Fin g → O)) :
    liftSq ρ n hn x = ρ x.fst + ∑ a, ρ (x.snd a) * n a := rfl

theorem liftSq_inl {g : ℕ} {O C : Type} [CommRing O] [CommRing C] (ρ : O →+* C) (n : Fin g → C)
    (hn : ∀ a b, n a * n b = 0) (h : O) : liftSq ρ n hn (TrivSqZeroExt.inl h) = ρ h := by
  simp [liftSq_apply]

theorem liftSq_sec {g : ℕ} {O C : Type} [CommRing O] [Algebra ℂ O] [CommRing C] (ρ : O →+* C) (n : Fin g → C)
    (hn : ∀ a b, n a * n b = 0) (D : Fin g → Derivation ℂ O O) (h : O) :
    liftSq ρ n hn (tszeSec D h) = ρ h + ∑ a, ρ (D a h) * n a := by
  rw [liftSq_apply, fst_tszeSec]
  simp only [snd_tszeSec]

theorem exists_hom_jet {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}
    (K : Charts F) {k : K.K} {T : K.Obj} (f₁ f₂ : K.triv k ⟶ T) (n : Fin g → T.C)
    (hdeg : Hom.deg f₁ = Hom.deg f₂) (hJ : ∀ a, n a ∈ T.J) (hn : ∀ a b, n a * n b = 0)
    (h : ∀ x : Hol (K.W k), Hom.φ f₂ x = Hom.φ f₁ x + ∑ a, Hom.φ f₁ (dw a x) * n a) :
    ∃ χ : K.jet k ⟶ T, Hom.deg χ = Hom.deg f₁ ∧ jet0 k ≫ χ = f₁ ∧ jet1 k ≫ χ = f₂ ∧
      ∀ x : TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k)),
        Hom.φ χ x = Hom.φ f₁ x.fst + ∑ a, Hom.φ f₁ (x.snd a) * n a := by
  let ρ : Hol (K.W k) →+* T.C := (Hom.φ f₁ : (K.triv k).C →+* T.C)
  letI := (K.jet k).alg
  letI := (K.triv k).alg
  let φ : (K.jet k).C →ₐ[Hol F.V] T.C :=
    { liftSq ρ n hn with
      commutes' := fun f ↦ (liftSq_inl ρ n hn (K.cst k f)).trans ((Hom.φ f₁).commutes f) }
  have hφ : ∀ x : TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k)), φ x = liftSq ρ n hn x := fun _ ↦ rfl
  have hcomp : (φ : (K.jet k).C →+* T.C).comp (K.jet k).ρ = (Hom.φ f₁ : (K.triv k).C →+* T.C).comp (K.triv k).ρ :=
    RingHom.ext fun x ↦ liftSq_inl ρ n hn x
  let χ : K.jet k ⟶ T :=
    { φ := φ
      deg := Hom.deg f₁
      le := Hom.le f₁
      mem := fun c hc ↦ by
        have hc' : TrivSqZeroExt.fst c = 0 := hc
        rw [hφ, liftSq_apply, hc', map_zero, zero_add]
        exact T.J.sum_mem fun a _ ↦ T.J.mul_mem_left _ (hJ a)
      close := by rw [hcomp]; exact Hom.close f₁ }
  refine ⟨χ, rfl, hom_ext (fun c ↦ ?_) (zero_add _), hom_ext (fun c ↦ ?_) ((zero_add _).trans hdeg), fun _ ↦ rfl⟩
  · change liftSq ρ n hn (TrivSqZeroExt.inl (sh (K.le_refl k) c)) = _
    rw [sh_refl, liftSq_inl]; rfl
  · change liftSq ρ n hn (tszeSec dw c) = _
    refine Eq.trans ?_ (h c).symm
    exact liftSq_sec ρ n hn dw c

end GlobalTheory.SquareLiftLemmas
end
end

section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

set_option autoImplicit false

namespace GlobalTheory.PD.CupAdj

variable {k : Type} [Field k] {E : Type} [AddCommGroup E] [Module k E] {ι : Type} [LinearOrder ι]

theorem cech_apply_mem {F : Finset ι → Submodule k E} {n : ℤ} {a : Finset ι → E} (ha : a ∈ cechC F n)
    (s : Finset ι) : a s ∈ (if s.Nonempty ∧ (s.card : ℤ) = n + 1 then F s else ⊥) :=
  (Submodule.mem_pi.1 ha) s (Set.mem_univ _)

theorem cech_apply_eq_zero {F : Finset ι → Submodule k E} {n : ℤ} {a : Finset ι → E} (ha : a ∈ cechC F n)
    {s : Finset ι} (h : ¬ (s.Nonempty ∧ (s.card : ℤ) = n + 1)) : a s = 0 := by
  have := cech_apply_mem ha s
  rw [if_neg h] at this
  exact (Submodule.mem_bot k).1 this

theorem cech_apply_mem_of_subset {F : Finset ι → Submodule k E} (hF : ∀ s t, s.Nonempty → s ⊆ t → F s ≤ F t)
    {n : ℤ} {a : Finset ι → E} (ha : a ∈ cechC F n) {s t : Finset ι} (hst : s ⊆ t) : a s ∈ F t := by
  by_cases h : s.Nonempty ∧ (s.card : ℤ) = n + 1
  · have := cech_apply_mem ha s
    rw [if_pos h] at this
    exact hF s t h.1 hst this
  · rw [cech_apply_eq_zero ha h]; exact zero_mem _

end GlobalTheory.PD.CupAdj

namespace GlobalTheory.PD.CupAdj

theorem cupPair_apply {k : Type} [Field k] {d : ℕ} {E : Type} [AddCommGroup E] [Module k E] {E' : Type}
    [AddCommGroup E'] [Module k E'] (β : E →ₗ[k] E' →ₗ[k] k) (a : Finset (Fin (d+1)) → E)
    (b : Finset (Fin (d+1)) → E') :
    cupPair β a b = ∑ j, β (a (Finset.univ.filter (· ≤ j))) (b (Finset.univ.filter (j ≤ ·))) := by
  simp [cupPair]

theorem deltaL_apply {k : Type} [Field k] {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E] [Module k E]
    (a : Finset ι → E) (t : Finset ι) :
    deltaL k ι E a t = ∑ i ∈ t, GlobalTheory.cubeSign t i • a (t.erase i) := rfl

theorem card_le (d : ℕ) (j : Fin (d+1)) : (Finset.univ.filter (· ≤ j)).card = j.val + 1 := by
  rw [show Finset.univ.filter (· ≤ j) = Finset.Iic j by ext; simp, Fin.card_Iic]

theorem card_ge (d : ℕ) (j : Fin (d+1)) : (Finset.univ.filter (j ≤ ·)).card = d + 1 - j.val := by
  rw [show Finset.univ.filter (j ≤ ·) = Finset.Ici j by ext; simp, Fin.card_Ici]

theorem cech_adj (k : Type) [Field k] (d : ℕ) (E : Type) [AddCommGroup E] [Module k E] (E' : Type)
    [AddCommGroup E'] [Module k E'] (A : Finset (Fin (d + 1)) → Submodule k E)
    (B : Finset (Fin (d + 1)) → Submodule k E') (β : E →ₗ[k] E' →ₗ[k] k)
    (hA : ∀ s t, s.Nonempty → s ⊆ t → A s ≤ A t) (hB : ∀ s t, s.Nonempty → s ⊆ t → B s ≤ B t)
    (hβ : ∀ i, (Finset.univ.erase i).Nonempty → ∀ a ∈ A (Finset.univ.erase i), ∀ b ∈ B (Finset.univ.erase i),
      β a b = 0) :
    Adj (cech A) (cech B) (cupPair β) d := by
  intro n
  have van : ∀ {m m' : ℤ} {a : Finset (Fin (d+1)) → E} {b : Finset (Fin (d+1)) → E'},
      a ∈ cechC A m → b ∈ cechC B m' → ∀ i s t, s ⊆ Finset.univ.erase i → t ⊆ Finset.univ.erase i →
      β (a s) (b t) = 0 := by
    intro m m' a b ha hb i s t hs ht
    by_cases hne : s.Nonempty
    · exact hβ i (hne.mono hs) _ (cech_apply_mem_of_subset hA ha hs) _ (cech_apply_mem_of_subset hB hb ht)
    · rw [cech_apply_eq_zero ha (fun h => hne h.1), map_zero, LinearMap.zero_apply]
  by_cases hn : 0 ≤ n ∧ n + 1 ≤ d
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m := ⟨n.toNat, (Int.toNat_of_nonneg hn.1).symm⟩
    have hmd : m + 1 ≤ d := by exact_mod_cast hn.2
    set j : Fin (d+1) := ⟨m + 1, by omega⟩ with hj
    set j' : Fin (d+1) := ⟨m, by omega⟩ with hj'
    refine ⟨(-1 : ℤˣ) ^ ((Finset.univ.filter (· ≤ j)).filter (· < j)).card, ?_⟩
    intro a ha b hb
    change cupPair β (deltaL k _ E a) b = _ • cupPair β a (deltaL k _ E' b)
    have L1 : cupPair β (deltaL k _ E a) b =
        β (deltaL k _ E a (Finset.univ.filter (· ≤ j))) (b (Finset.univ.filter (j ≤ ·))) := by
      rw [cupPair_apply]
      refine Finset.sum_eq_single j (fun j0 _ hj0 => ?_) (by simp)
      rw [cech_apply_eq_zero hb (s := Finset.univ.filter (j0 ≤ ·)), map_zero]
      rintro ⟨-, h⟩
      have := j0.isLt
      rw [card_ge, Nat.cast_sub (by omega)] at h
      push_cast at h
      apply hj0; ext; simp only [hj]; omega
    have L2 : cupPair β a (deltaL k _ E' b) =
        β (a (Finset.univ.filter (· ≤ j'))) (deltaL k _ E' b (Finset.univ.filter (j' ≤ ·))) := by
      rw [cupPair_apply]
      refine Finset.sum_eq_single j' (fun j0 _ hj0 => ?_) (by simp)
      rw [cech_apply_eq_zero ha (s := Finset.univ.filter (· ≤ j0)), map_zero, LinearMap.zero_apply]
      rintro ⟨-, h⟩
      rw [card_le] at h
      push_cast at h
      apply hj0; ext; simp only [hj']; omega
    have L3 : β (deltaL k _ E a (Finset.univ.filter (· ≤ j))) (b (Finset.univ.filter (j ≤ ·))) =
        GlobalTheory.cubeSign (Finset.univ.filter (· ≤ j)) j •
          β (a ((Finset.univ.filter (· ≤ j)).erase j)) (b (Finset.univ.filter (j ≤ ·))) := by

      rw [deltaL_apply, map_sum, LinearMap.sum_apply]
      refine (Finset.sum_eq_single j (fun i hi hij => ?_) (by simp)).trans ?_
      · rw [map_zsmul, LinearMap.smul_apply]
        have hi' : i < j := lt_of_le_of_ne (by simpa using hi) hij
        rw [van ha hb i _ _ ?_ ?_, smul_zero]
        · intro x hx
          simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
          exact ⟨hx.1, trivial⟩
        · intro x hx
          simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
          exact ⟨fun h => by subst h; exact absurd hx (not_le.2 hi'), trivial⟩
      · rw [map_zsmul, LinearMap.smul_apply]
    have L4 : β (a (Finset.univ.filter (· ≤ j'))) (deltaL k _ E' b (Finset.univ.filter (j' ≤ ·))) =
        β (a (Finset.univ.filter (· ≤ j'))) (b ((Finset.univ.filter (j' ≤ ·)).erase j')) := by

      rw [deltaL_apply, map_sum]
      refine (Finset.sum_eq_single j' (fun i hi hij => ?_) (by simp)).trans ?_
      · rw [map_zsmul]
        have hi' : j' < i := lt_of_le_of_ne (by simpa using hi) (Ne.symm hij)
        rw [van ha hb i _ _ ?_ ?_, smul_zero]
        · intro x hx
          simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
          exact ⟨fun h => by subst h; exact absurd hx (not_le.2 hi'), trivial⟩
        · intro x hx
          simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
          exact ⟨hx.1, trivial⟩
      · have : GlobalTheory.cubeSign (Finset.univ.filter (j' ≤ ·)) j' = 1 := by
          rw [GlobalTheory.cubeSign]
          have : ((Finset.univ.filter (j' ≤ ·)).filter (· < j')) = ∅ := by
            ext x; simp
          rw [this]; simp
        rw [this, one_smul]
    have e1 : (Finset.univ.filter (· ≤ j)).erase j = Finset.univ.filter (· ≤ j') := by
      ext x
      simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, Fin.ext_iff, Fin.le_iff_val_le_val, hj, hj']
      omega
    have e2 : Finset.univ.filter (j ≤ ·) = (Finset.univ.filter (j' ≤ ·)).erase j' := by
      ext x
      simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, Fin.ext_iff, Fin.le_iff_val_le_val, hj, hj']
      omega
    rw [L1, L2, L3, L4, e1, e2, GlobalTheory.cubeSign, Units.smul_def]
    push_cast
    rfl
  · refine ⟨1, ?_⟩
    intro a ha b hb
    rw [one_smul]
    rcases not_and_or.1 hn with h | h
    · have : a = 0 := by
        funext s
        refine cech_apply_eq_zero ha ?_
        rintro ⟨hs, hc⟩
        have := hs.card_pos
        omega
      change cupPair β (deltaL k _ E a) b = cupPair β a (deltaL k _ E' b)
      simp [this]
    · have : b = 0 := by
        funext s
        refine cech_apply_eq_zero hb ?_
        rintro ⟨hs, hc⟩
        have := hs.card_pos
        omega
      change cupPair β (deltaL k _ E a) b = cupPair β a (deltaL k _ E' b)
      simp [this]

end GlobalTheory.PD.CupAdj
end

section

set_option autoImplicit false

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.PD

theorem cech_isCx_of_mono : ∀ (k : Type) [Field k] (ι : Type) [LinearOrder ι] (E : Type) [AddCommGroup E] [Module k E]
    (A : Finset ι → Submodule k E), (∀ s t, s.Nonempty → s ⊆ t → A s ≤ A t) → (cech A).IsCx := by
  intro k _ ι _ E _ _ A hA n a ha
  have ha' : ∀ s, a s ∈ (if s.Nonempty ∧ (s.card : ℤ) = n + 1 then A s else ⊥) :=
    fun s => (Submodule.mem_pi.1 ha) s (Set.mem_univ _)
  refine ⟨?_, ?_⟩
  · show GlobalTheory.DI.delta a ∈ cechC A (n + 1)
    refine Submodule.mem_pi.2 fun t _ => ?_
    show ∑ i ∈ t, GlobalTheory.cubeSign t i • a (t.erase i) ∈ _
    split_ifs with ht
    · refine Submodule.sum_mem _ fun i _ => zsmul_mem ?_ _
      have h := ha' (t.erase i)
      split_ifs at h with h2
      · exact hA _ _ h2.1 (Finset.erase_subset _ _) h
      · rw [Submodule.mem_bot] at h; rw [h]; exact zero_mem _
    · rw [Submodule.mem_bot]
      refine Finset.sum_eq_zero fun i hi => ?_
      have h := ha' (t.erase i)
      split_ifs at h with h2
      · exfalso
        apply ht
        refine ⟨⟨i, hi⟩, ?_⟩
        have h3 := Finset.card_erase_add_one hi
        have h4 := h2.2
        omega
      · rw [Submodule.mem_bot] at h; rw [h, smul_zero]
  · exact GlobalTheory.DI.delta_delta a

end GlobalTheory.PD
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC


set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem exists_filtered_colimit_etale_of_indEt : ∀ (A O : Type) [CommRing A] [CommRing O] [Algebra A O], IndEt A O → ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ Under (CommRingCat.of A)) (ι : D ⟶ (Functor.const J).obj (Under.mk (CommRingCat.ofHom (algebraMap A O)))), Nonempty (IsColimit (Cocone.mk _ ι)) ∧ ∀ j, (D.obj j).hom.hom.Etale := by
  intro A O _ _ _ h
  obtain ⟨J, _, _, D, t, s, hs, hst⟩ := h
  have : Nonempty J := IsFiltered.nonempty
  refine ⟨J, inferInstance, inferInstance, Under.lift D t,
    { app j := Under.homMk (s.app j) (by simp [hst]) },
    ⟨Under.isColimitLiftCocone _ _ _ _ (by simp [hst]) hs⟩, fun j => (hst j).1⟩

end GlobalTheory.EtC
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem pointwise_absorption_twisted :
    ∀ (T x u g t k1 k2 E : ℝ), 0 ≤ u → 0 ≤ g → 0 < k2 → 0 < E → |t| ≤ 3 / 4 →
      wT T x / 8 ≤ (1 - k1 ^ 2 / k2) * E →
      ((-T - 1 ≤ x ∧ x ≤ -T + 1) → E / k2 ≤ 16 / 3 ∧ wT T x / 8 ≤ (1 - 5 * (k1 ^ 2 / k2)) * E) →
      (¬ (-T - 1 ≤ x ∧ x ≤ -T + 1) → t = 0) →
      (Real.sqrt (t ^ 2 * g ^ 2 / k2) + u * Real.sqrt (k1 ^ 2 / k2)) ^ 2 * E + u ^ 2 * (wT T x / 8)
        ≤ u ^ 2 * E + (if (-T - 1 ≤ x ∧ x ≤ -T + 1) then 15 / 4 * g ^ 2 else 0) := by
  intro T x u g t k1 k2 E hu hg hk2 hE ht hw hwin hoff
  have ha : 0 ≤ t ^ 2 * g ^ 2 / k2 := by positivity
  have hb : 0 ≤ k1 ^ 2 / k2 := by positivity
  have hA := Real.sq_sqrt ha
  have hB := Real.sq_sqrt hb
  have hA0 := Real.sqrt_nonneg (t ^ 2 * g ^ 2 / k2)
  have hB0 := Real.sqrt_nonneg (k1 ^ 2 / k2)
  by_cases h : (-T - 1 ≤ x ∧ x ≤ -T + 1)
  · rw [if_pos h]
    obtain ⟨h1, h2⟩ := hwin h
    have ht2 : t ^ 2 ≤ 9 / 16 := by
      have h0 : 0 ≤ |t| := abs_nonneg t
      have : |t| ^ 2 ≤ (3 / 4) ^ 2 := by nlinarith
      rw [sq_abs] at this
      linarith
    have haE : t ^ 2 * g ^ 2 / k2 * E ≤ 3 * g ^ 2 := by
      have e : t ^ 2 * g ^ 2 / k2 * E = t ^ 2 * g ^ 2 * (E / k2) := by ring
      rw [e]
      calc t ^ 2 * g ^ 2 * (E / k2) ≤ (9 / 16) * g ^ 2 * (16 / 3) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_right ht2 (sq_nonneg g)) h1
              (by positivity) (by positivity)
        _ = 3 * g ^ 2 := by ring
    have key : (Real.sqrt (t ^ 2 * g ^ 2 / k2) + u * Real.sqrt (k1 ^ 2 / k2)) ^ 2
        ≤ 5 / 4 * (t ^ 2 * g ^ 2 / k2) + 5 * (k1 ^ 2 / k2) * u ^ 2 := by
      nlinarith [sq_nonneg (Real.sqrt (t ^ 2 * g ^ 2 / k2) / 2 - 2 * u * Real.sqrt (k1 ^ 2 / k2))]
    have k1' := mul_le_mul_of_nonneg_right key hE.le
    have k2' := mul_le_mul_of_nonneg_left h2 (sq_nonneg u)
    nlinarith
  · rw [if_neg h]
    have t0 := hoff h
    subst t0
    have z : Real.sqrt ((0:ℝ) ^ 2 * g ^ 2 / k2) = 0 := by simp
    rw [z]
    have k2' := mul_le_mul_of_nonneg_left hw (sq_nonneg u)
    have e : (0 + u * Real.sqrt (k1 ^ 2 / k2)) ^ 2 * E = u ^ 2 * (k1 ^ 2 / k2) * E := by
      rw [zero_add, mul_pow, hB]
    rw [e]
    nlinarith

end GlobalTheory
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem isOpen_nz_and_mem_nz_iff : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (Λ : La) (τ : ι → Y → ℂ), A.IsSec Λ τ → IsOpen (nz A τ) ∧ ∀ i y, y ∈ (A.chart i).source → (y ∈ nz A τ ↔ τ i y ≠ 0) := by
  intro n Y _ _ _ _ _ ι La _ A Λ τ h
  have key : ∀ i y, y ∈ (A.chart i).source → (y ∈ nz A τ ↔ τ i y ≠ 0) := by
    intro i y hy
    have e := h.2 i (A.pick y) y (Set.mem_univ _) hy (A.mem_pick y)
    have g := A.g_ne Λ i (A.pick y) y hy (A.mem_pick y)
    simp only [nz, Set.mem_setOf_eq, e, ne_eq, mul_eq_zero, g, false_or]
  refine ⟨?_, key⟩
  have cont : ∀ i, ContinuousOn (τ i) (A.chart i).source := by
    intro i
    have h1 : ContinuousOn (τ i ∘ (A.chart i).symm) (A.chart i).target := by
      simpa using (h.1 i).continuousOn
    have h2 := h1.comp (A.chart i).continuousOn (A.chart i).mapsTo
    refine h2.congr ?_
    intro y hy
    simp [(A.chart i).left_inv hy]
  rw [isOpen_iff_mem_nhds]
  intro y hy
  have hs := (A.chart (A.pick y)).open_source.mem_nhds (A.mem_pick y)
  have hc : ContinuousAt (τ (A.pick y)) y := (cont _).continuousAt hs
  have hne : τ (A.pick y) y ≠ 0 := hy
  filter_upwards [hs, hc.eventually_ne hne] with x hx hx'
  exact (key _ x hx).2 hx'

end GlobalTheory.OTY
end
