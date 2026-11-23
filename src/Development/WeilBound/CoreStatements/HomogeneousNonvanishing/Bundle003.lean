module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle001
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
public import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Data.Nat.Factorization.Induction
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

@[expose] public section

section

open NumberField TensorProduct GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.UnitarySelfGeneration

theorem crt_div {M : Type} [AddCommGroup M] (x : M) : ∀ n : ℕ, 0 < n →
    (∀ p k : ℕ, p.Prime → p ^ k ∣ n → ∃ e, x = p ^ k • e) → ∃ e, x = n • e := by
  intro n
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp _ => intro _ h; exact h p k hp dvd_rfl
  | zero => intro h; omega
  | one => intro _ _; exact ⟨x, by simp⟩
  | coprime a b ha hb hab iha ihb =>
    intro _ h
    obtain ⟨e, he⟩ := iha (by omega) fun p k hp hk => h p k hp (hk.mul_right b)
    obtain ⟨f, hf⟩ := ihb (by omega) fun p k hp hk => h p k hp (hk.mul_left a)
    obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hab
    refine ⟨u • f + v • e, ?_⟩
    have h1 : x = (u * a) • x + (v * b) • x := by rw [← add_smul, huv, one_smul]
    have h2 : (u * a) • x = (a * b) • (u • f) := by
      rw [hf, ← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul]
      congr 1; push_cast; ring
    have h3 : (v * b) • x = (a * b) • (v • e) := by
      rw [he, ← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul]
      congr 1; push_cast; ring
    rw [smul_add, ← h2, ← h3, ← h1]

theorem crt_le {p : ℕ} {O : Type} [CommRing O] {L L' : Type} [AddCommGroup L] [Module O L] [AddCommGroup L']
    [Module O L'] {B : LinearMap.BilinForm ℤ L} {B' : LinearMap.BilinForm ℤ L'} (f : ProIsoAt p O B B')
    (k j : ℕ) (x : L) : ∃ e, f.a (k + j) x = f.a k x + p ^ k • e := by
  induction j with
  | zero => exact ⟨0, by simp⟩
  | succ j ih =>
    obtain ⟨e, he⟩ := ih
    obtain ⟨e', he'⟩ := f.compat (k + j) x
    refine ⟨e + p ^ j • e', ?_⟩
    rw [← add_assoc, he', he, smul_add, smul_smul, ← pow_add, add_assoc]

theorem crt_good {O : Type} [CommRing O] {L L' : Type} [AddCommGroup L] [Module O L] [AddCommGroup L']
    [Module O L'] {B : LinearMap.BilinForm ℤ L} {B' : LinearMap.BilinForm ℤ L'}
    (f : ∀ p : ℕ, p.Prime → ProIsoAt p O B B') : ∀ n : ℕ, ∃ a : L →ₗ[O] L', 0 < n →
      ∀ (p k : ℕ) (hp : p.Prime), p ^ k ∣ n → ∀ x, ∃ e, a x = (f p hp).a k x + p ^ k • e := by
  intro n
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow q m hq _ =>
    refine ⟨(f q hq).a m, fun _ p k hp hk x => ?_⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact ⟨(f q hq).a m x - (f p hp).a 0 x, by simp⟩
    · have hpq : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).1
        (hp.dvd_of_dvd_pow ((dvd_pow_self p hk0.ne').trans hk))
      subst hpq
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le ((Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 hk)
      exact crt_le _ k j x
  | zero => exact ⟨0, fun h => by omega⟩
  | one =>
    refine ⟨0, fun _ p k hp hk x => ?_⟩
    rw [Nat.dvd_one.1 hk]
    exact ⟨-(f p hp).a k x, by simp⟩
  | coprime a b ha hb hab iha ihb =>
    obtain ⟨A, hA⟩ := iha
    obtain ⟨C, hC⟩ := ihb
    obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hab
    refine ⟨(v * b) • A + (u * a) • C, fun _ p k hp hk x => ?_⟩
    have hor : p ^ k ∣ a ∨ p ^ k ∣ b := by
      by_cases hpa : p ∣ a
      · left
        have : Nat.Coprime (p ^ k) b := Nat.Coprime.pow_left k (Nat.Coprime.coprime_dvd_left hpa hab)
        exact this.dvd_of_dvd_mul_right hk
      · right
        have : Nat.Coprime (p ^ k) a := Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hpa)
        exact this.dvd_of_dvd_mul_left hk
    rcases hor with h | h
    · obtain ⟨e, he⟩ := hA (by omega) p k hp h x
      obtain ⟨c, hc⟩ := h
      refine ⟨e + (u * c) • (C x - A x), ?_⟩
      have h1 : v * b = 1 - u * a := by linarith
      have h2 : p ^ k • ((u * c) • (C x - A x)) = (u * a) • (C x - A x) := by
        rw [← natCast_zsmul, smul_smul]; congr 1; rw [hc]; push_cast; ring
      rw [smul_add, h2, ← add_assoc, ← he, h1]
      simp only [LinearMap.add_apply, LinearMap.smul_apply, sub_smul, one_smul, smul_sub, LinearMap.sub_apply]
      abel
    · obtain ⟨e, he⟩ := hC (by omega) p k hp h x
      obtain ⟨c, hc⟩ := h
      refine ⟨e + (v * c) • (A x - C x), ?_⟩
      have h1 : u * a = 1 - v * b := by linarith
      have h2 : p ^ k • ((v * c) • (A x - C x)) = (v * b) • (A x - C x) := by
        rw [← natCast_zsmul, smul_smul]; congr 1; rw [hc]; push_cast; ring
      rw [smul_add, h2, ← add_assoc, ← he, h1]
      simp only [LinearMap.add_apply, LinearMap.smul_apply, sub_smul, one_smul, smul_sub, LinearMap.sub_apply]
      abel

theorem tw_crt : ∀ (O : Type) [CommRing O] (L L' : Type) [AddCommGroup L] [Module O L] [AddCommGroup L'] [Module O L'] (B : LinearMap.BilinForm ℤ L) (B' : LinearMap.BilinForm ℤ L'), (∀ p : ℕ, p.Prime → Nonempty (ProIsoAt p O B B')) → Nonempty (ProIso O B B') := by
  intro O _ L L' _ _ _ _ B B' h
  let f : ∀ p : ℕ, p.Prime → ProIsoAt p O B B' := fun p hp => (h p hp).some
  choose a ha using crt_good f
  refine ⟨⟨a, ?_, ?_, ?_, ?_⟩⟩
  · intro n hn x
    constructor
    · rintro ⟨y, hy⟩
      refine crt_div x n hn fun p k hp hk => ?_
      obtain ⟨e, he⟩ := ha n hn p k hp hk x
      obtain ⟨c, hc⟩ := hk
      refine ((f p hp).inj k x).1 ⟨c • y - e, ?_⟩
      rw [smul_sub, smul_smul, ← hc, ← hy, he]; abel
    · rintro ⟨y, rfl⟩
      exact ⟨a n y, map_nsmul _ _ _⟩
  · intro n hn y
    obtain ⟨e, he⟩ := crt_div ((LinearMap.range (a n)).mkQ y) n hn fun p k hp hk => by
      obtain ⟨x, e, rfl⟩ := (f p hp).surj k y
      obtain ⟨e', he'⟩ := ha n hn p k hp hk x
      refine ⟨(LinearMap.range (a n)).mkQ (e - e'), ?_⟩
      rw [← map_nsmul, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
      exact ⟨x, by rw [he', smul_sub]; abel⟩
    obtain ⟨e, rfl⟩ := Submodule.mkQ_surjective _ e
    rw [← map_nsmul, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at he
    obtain ⟨x, hx⟩ := he
    exact ⟨x, e, by rw [hx]; abel⟩
  · intro n hn x y
    obtain ⟨e, he⟩ := crt_div (B' (a n x) (a n y) - B x y) n hn fun p k hp hk => by
      obtain ⟨e, he⟩ := ha n hn p k hp hk x
      obtain ⟨e', he'⟩ := ha n hn p k hp hk y
      obtain ⟨c, hc⟩ := (f p hp).isom k x y
      refine ⟨c + B' e (a n y) + B' ((f p hp).a k x) e', ?_⟩
      have h1 : B' (a n x) (a n y) = B' ((f p hp).a k x) (a n y) + p ^ k • B' e (a n y) := by
        rw [he, map_add (f := _), map_nsmul]; rfl
      have h2 : B' ((f p hp).a k x) (a n y) = B' ((f p hp).a k x) ((f p hp).a k y)
          + p ^ k • B' ((f p hp).a k x) e' := by
        rw [he', map_add (f := _), map_nsmul]
      rw [h1, h2]
      simp only [nsmul_eq_mul]
      push_cast
      linear_combination hc
    exact ⟨e, by rw [he, nsmul_eq_mul]⟩
  · intro n m hn hm x
    obtain ⟨e, he⟩ := crt_div (a (n * m) x - a n x) n hn fun p k hp hk => by
      obtain ⟨e, he⟩ := ha n hn p k hp hk x
      obtain ⟨e', he'⟩ := ha (n * m) (Nat.mul_pos hn hm) p k hp (hk.mul_right m) x
      exact ⟨e' - e, by rw [he, he', smul_sub]; abel⟩
    exact ⟨e, by rw [← he]; abel⟩

end PositivityTheory.UnitarySelfGeneration
end

section

open NumberField TensorProduct GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.UnitarySelfGeneration

theorem lift_dense (p : ℕ) [Fact p.Prime] (M : Type) [AddCommGroup M] (k : ℕ) (w : ℤ_[p] ⊗[ℤ] M) :
    ∃ (y : M) (w' : ℤ_[p] ⊗[ℤ] M), w = 1 ⊗ₜ y + (p : ℤ_[p]) ^ k • w' := by
  refine TensorProduct.induction_on (motive := fun w : ℤ_[p] ⊗[ℤ] M =>
    ∃ (y : M) (w' : ℤ_[p] ⊗[ℤ] M), w = 1 ⊗ₜ y + (p : ℤ_[p]) ^ k • w') w ?_ ?_ ?_
  · exact ⟨0, 0, by simp⟩
  · intro a m
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp (PadicInt.appr_spec k a)
    have ha : a = ((PadicInt.appr a k : ℕ) : ℤ) • (1 : ℤ_[p]) + (p : ℤ_[p]) ^ k • c := by
      rw [smul_eq_mul, ← hc, zsmul_eq_mul, mul_one, Int.cast_natCast]
      ring
    refine ⟨((PadicInt.appr a k : ℕ) : ℤ) • m, c ⊗ₜ[ℤ] m, ?_⟩
    calc a ⊗ₜ[ℤ] m = (((PadicInt.appr a k : ℕ) : ℤ) • (1 : ℤ_[p]) + (p : ℤ_[p]) ^ k • c) ⊗ₜ[ℤ] m :=
          congrArg (· ⊗ₜ[ℤ] m) ha
      _ = 1 ⊗ₜ[ℤ] (((PadicInt.appr a k : ℕ) : ℤ) • m) + (p : ℤ_[p]) ^ k • c ⊗ₜ[ℤ] m := by
          rw [TensorProduct.add_tmul, TensorProduct.smul_tmul ((PadicInt.appr a k : ℕ) : ℤ) (1 : ℤ_[p]) m,
            ← TensorProduct.smul_tmul' ((p : ℤ_[p]) ^ k) c m]
  · rintro w1 w2 ⟨y1, w1', rfl⟩ ⟨y2, w2', rfl⟩
    exact ⟨y1 + y2, w1' + w2', by rw [TensorProduct.tmul_add, smul_add]; abel⟩

theorem lift_sat (p : ℕ) [Fact p.Prime] (M : Type) [AddCommGroup M] [Module.Finite ℤ M] [Module.Free ℤ M] (k : ℕ)
    (y : M) (w : ℤ_[p] ⊗[ℤ] M) (h : 1 ⊗ₜ y = (p : ℤ_[p]) ^ k • w) : ∃ e, y = p ^ k • e := by
  classical
  let b := Module.Free.chooseBasis ℤ M
  have hdiv : ∀ i, (p : ℤ) ^ k ∣ b.repr y i := by
    intro i
    have h1 := congrArg (fun z => (b.baseChange ℤ_[p]).repr z i) h
    rw [← PadicInt.pow_p_dvd_int_iff]
    refine Dvd.intro ((b.baseChange ℤ_[p]).repr w i) ?_
    simpa [Module.Basis.baseChange_repr_tmul] using h1.symm
  choose c hc using hdiv
  refine ⟨∑ i, c i • b i, ?_⟩
  conv_lhs => rw [← b.sum_repr y]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hc i, mul_smul, ← Nat.cast_pow, natCast_zsmul]

theorem tw_lift : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (L L' : Type) [AddCommGroup L] [Module O L] [AddCommGroup L'] [Module O L'] (B : LinearMap.BilinForm ℤ L) (B' : LinearMap.BilinForm ℤ L') [Module.Projective O L] [Module.Finite ℤ L] [Module.Free ℤ L] [Module.Finite ℤ L'] [Module.Free ℤ L'] (φ : (ℤ_[p] ⊗[ℤ] L) ≃ₗ[ℤ_[p]] (ℤ_[p] ⊗[ℤ] L')), (∀ (a : O) (x : L), φ (1 ⊗ₜ (a • x)) = LinearMap.baseChange ℤ_[p] (LinearMap.lsmul O L' a).toAddMonoidHom.toIntLinearMap (φ (1 ⊗ₜ x))) → (∀ u v, B'.baseChange ℤ_[p] (φ u) (φ v) = B.baseChange ℤ_[p] u v) → Nonempty (ProIsoAt p O B B') := by
  intro p _ O _ L L' _ _ _ _ B B' _ _ _ _ _ φ hO hB
  have htm : ∀ (n : ℕ) (y : L'),
      (1 : ℤ_[p]) ⊗ₜ[ℤ] (n • y) = (n : ℤ_[p]) • ((1 : ℤ_[p]) ⊗ₜ[ℤ] y) := by
    intro n y
    rw [Nat.cast_smul_eq_nsmul]
    exact map_nsmul (TensorProduct.mk ℤ ℤ_[p] L' 1) n y
  have hls : ∀ (c : O) (y : L'),
      LinearMap.baseChange ℤ_[p] (LinearMap.lsmul O L' c).toAddMonoidHom.toIntLinearMap
        ((1 : ℤ_[p]) ⊗ₜ[ℤ] y) = (1 : ℤ_[p]) ⊗ₜ[ℤ] (c • y) := by
    intro c y
    rw [LinearMap.baseChange_tmul]
    rfl
  obtain ⟨G, hG⟩ : ∃ G : ℕ → Submodule O (L' × L), ∀ k z, z ∈ G k ↔
      ∃ w : ℤ_[p] ⊗[ℤ] L', (1 : ℤ_[p]) ⊗ₜ[ℤ] z.1 = φ ((1 : ℤ_[p]) ⊗ₜ[ℤ] z.2) + (p : ℤ_[p]) ^ k • w :=
    ⟨fun k =>
      { carrier := {z | ∃ w : ℤ_[p] ⊗[ℤ] L',
          (1 : ℤ_[p]) ⊗ₜ[ℤ] z.1 = φ ((1 : ℤ_[p]) ⊗ₜ[ℤ] z.2) + (p : ℤ_[p]) ^ k • w}
        add_mem' := by
          rintro z1 z2 ⟨w1, hw1⟩ ⟨w2, hw2⟩
          show ∃ w : ℤ_[p] ⊗[ℤ] L', _
          refine ⟨w1 + w2, ?_⟩
          rw [Prod.fst_add, Prod.snd_add, TensorProduct.tmul_add, TensorProduct.tmul_add, map_add (f := _),
            hw1, hw2, smul_add]
          abel
        zero_mem' := by
          show ∃ w : ℤ_[p] ⊗[ℤ] L', _
          exact ⟨0, by simp⟩
        smul_mem' := by
          rintro c z ⟨w, hw⟩
          show ∃ w : ℤ_[p] ⊗[ℤ] L', _
          refine ⟨LinearMap.baseChange ℤ_[p] (LinearMap.lsmul O L' c).toAddMonoidHom.toIntLinearMap w,
            ?_⟩
          rw [Prod.smul_fst, Prod.smul_snd, hO c z.2, ← hls c z.1, hw, map_add (f := _), map_smul] },
      fun k z => Iff.rfl⟩
  have hsurj : ∀ k, Function.Surjective ((LinearMap.snd O L' L).comp (G k).subtype) := by
    intro k x
    obtain ⟨y, w, hw⟩ := PositivityTheory.UnitarySelfGeneration.lift_dense p L' k (φ ((1 : ℤ_[p]) ⊗ₜ[ℤ] x))
    refine ⟨⟨(y, x), (hG k (y, x)).mpr ⟨-w, ?_⟩⟩, rfl⟩
    show (1 : ℤ_[p]) ⊗ₜ[ℤ] y = φ ((1 : ℤ_[p]) ⊗ₜ[ℤ] x) + (p : ℤ_[p]) ^ k • -w
    rw [hw, smul_neg]
    abel
  choose h hh using fun k => Module.projective_lifting_property
    ((LinearMap.snd O L' L).comp (G k).subtype) LinearMap.id (hsurj k)
  obtain ⟨a, ha⟩ : ∃ a : ℕ → L →ₗ[O] L', ∀ k x, ∃ w : ℤ_[p] ⊗[ℤ] L',
      (1 : ℤ_[p]) ⊗ₜ[ℤ] a k x = φ ((1 : ℤ_[p]) ⊗ₜ[ℤ] x) + (p : ℤ_[p]) ^ k • w := by
    refine ⟨fun k => (LinearMap.fst O L' L).comp ((G k).subtype.comp (h k)), fun k x => ?_⟩
    have h2 : (h k x : L' × L).2 = x := LinearMap.congr_fun (hh k) x
    have hmem := (hG k _).mp (h k x).prop
    rw [h2] at hmem
    exact hmem
  refine ⟨⟨a, ?_, ?_, ?_, ?_⟩⟩
  · intro k x
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨w, hw⟩ := ha k x
      rw [hy, htm, Nat.cast_pow] at hw
      have h1 : (1 : ℤ_[p]) ⊗ₜ[ℤ] x = (p : ℤ_[p]) ^ k • φ.symm ((1 : ℤ_[p]) ⊗ₜ[ℤ] y - w) := by
        apply φ.injective
        rw [map_smul, LinearEquiv.apply_symm_apply, smul_sub, hw]
        abel
      exact PositivityTheory.UnitarySelfGeneration.lift_sat p L k x _ h1
    · rintro ⟨y, rfl⟩
      exact ⟨a k y, map_nsmul (a k) (p ^ k) y⟩
  · intro k y
    obtain ⟨x, v, hv⟩ := PositivityTheory.UnitarySelfGeneration.lift_dense p L k (φ.symm ((1 : ℤ_[p]) ⊗ₜ[ℤ] y))
    obtain ⟨w, hw⟩ := ha k x
    have h1 : (1 : ℤ_[p]) ⊗ₜ[ℤ] y = φ ((1 : ℤ_[p]) ⊗ₜ[ℤ] x) + (p : ℤ_[p]) ^ k • φ v := by
      rw [← map_smul, ← map_add (f := _), ← hv, LinearEquiv.apply_symm_apply]
    have h2 : (1 : ℤ_[p]) ⊗ₜ[ℤ] (y - a k x) = (p : ℤ_[p]) ^ k • (φ v - w) := by
      rw [TensorProduct.tmul_sub, h1, hw, smul_sub]
      abel
    obtain ⟨e, he⟩ := PositivityTheory.UnitarySelfGeneration.lift_sat p L' k _ _ h2
    exact ⟨x, e, by rw [← he]; abel⟩
  · intro k x y
    obtain ⟨w1, hw1⟩ := ha k x
    obtain ⟨w2, hw2⟩ := ha k y
    rw [← PadicInt.pow_p_dvd_int_iff, Int.cast_sub]
    have e1 : ((B' (a k x) (a k y) : ℤ) : ℤ_[p]) =
        B'.baseChange ℤ_[p] ((1 : ℤ_[p]) ⊗ₜ[ℤ] a k x) ((1 : ℤ_[p]) ⊗ₜ[ℤ] a k y) := by
      rw [LinearMap.BilinForm.baseChange_tmul]
      simp
    have e2 : ((B x y : ℤ) : ℤ_[p]) =
        B'.baseChange ℤ_[p] (φ ((1 : ℤ_[p]) ⊗ₜ[ℤ] x)) (φ ((1 : ℤ_[p]) ⊗ₜ[ℤ] y)) := by
      rw [hB, LinearMap.BilinForm.baseChange_tmul]
      simp
    rw [e1, e2, hw1, hw2]
    refine Dvd.intro (B'.baseChange ℤ_[p] (φ ((1 : ℤ_[p]) ⊗ₜ[ℤ] x)) w2 +
      B'.baseChange ℤ_[p] w1 (φ ((1 : ℤ_[p]) ⊗ₜ[ℤ] y) + (p : ℤ_[p]) ^ k • w2)) ?_
    simp only [map_add (f := _), LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  · intro k x
    obtain ⟨w1, hw1⟩ := ha (k + 1) x
    obtain ⟨w2, hw2⟩ := ha k x
    have h1 : (1 : ℤ_[p]) ⊗ₜ[ℤ] (a (k + 1) x - a k x) =
        (p : ℤ_[p]) ^ k • ((p : ℤ_[p]) • w1 - w2) := by
      rw [TensorProduct.tmul_sub, hw1, hw2, smul_sub, smul_smul, ← pow_succ]
      abel
    obtain ⟨e, he⟩ := PositivityTheory.UnitarySelfGeneration.lift_sat p L' k _ _ h1
    exact ⟨e, by rw [← he]; abel⟩

end PositivityTheory.UnitarySelfGeneration
end

section

open NumberField TensorProduct

namespace PositivityTheory.UnitarySelfGeneration

theorem hermitian_form_standard_basis (Z R : Type) [CommRing Z] [CommRing R] [Algebra Z R] (σ : R →ₐ[Z] R) (hσ : ∀ r, σ (σ r) = r)
    (N : ℕ) (A g : Matrix (Fin N) (Fin N) R) (hg : IsUnit g.det) (h : (g.map σ).transpose * A * g = 1) :
    ∃ φ : (Fin N → R) ≃ₗ[R] (Fin N → R), ∀ x y,
      ∑ i, ∑ j, φ x i * A i j * σ (φ y j) = ∑ i, x i * σ (y i) := by
  have hM : IsUnit (g.map σ).det := by
    have e : σ g.det = (g.map σ).det := AlgHom.map_det σ g
    rw [← e]
    exact hg.map σ
  refine ⟨Matrix.toLinearEquiv' (g.map σ) (Matrix.invertibleOfIsUnitDet (g.map σ) hM), fun x y => ?_⟩
  have hs : (fun j => σ (Matrix.mulVec (g.map σ) y j)) = Matrix.mulVec g (fun k => σ (y k)) := by
    ext j

    simp [Matrix.mulVec, dotProduct, map_sum, map_mul, hσ]
  have key : ∀ u w : Fin N → R, ∑ i, ∑ j, u i * A i j * w j = dotProduct u (Matrix.mulVec A w) := by
    intro u w
    simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have hT : (A * g).transpose * g.map σ = 1 := by
    rw [← Matrix.transpose_transpose (g.map σ), ← Matrix.transpose_mul, ← Matrix.mul_assoc, h,
      Matrix.transpose_one]
  change ∑ i, ∑ j, Matrix.mulVec (g.map σ) x i * A i j * σ (Matrix.mulVec (g.map σ) y j) = _
  rw [key _ (fun j => σ (Matrix.mulVec (g.map σ) y j)), hs, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hT, Matrix.one_mulVec]
  simp [dotProduct]

theorem tw_g_std : ∀ (Z R : Type) [CommRing Z] [CommRing R] [Algebra Z R] (σ : R →ₐ[Z] R), (∀ r, σ (σ r) = r) → ∀ lam : R →ₗ[Z] Z, (∀ r, lam (σ r) = -lam r) → Function.Bijective (fun r : R => lam.comp (LinearMap.mulLeft Z r)) → ∀ (N : ℕ), (∀ A : Matrix (Fin N) (Fin N) R, (A.map σ).transpose = A → IsUnit A.det → ∃ g : Matrix (Fin N) (Fin N) R, IsUnit g.det ∧ (g.map σ).transpose * A * g = 1) → ∀ ψ ψ' : LinearMap.BilinForm Z (Fin N → R), (∀ x, ψ x x = 0) → Function.Bijective ψ → (∀ (a : R) x y, ψ (a • x) y = ψ x (σ a • y)) → (∀ x, ψ' x x = 0) → Function.Bijective ψ' → (∀ (a : R) x y, ψ' (a • x) y = ψ' x (σ a • y)) → ∃ φ : (Fin N → R) ≃ₗ[R] (Fin N → R), ∀ x y, ψ' (φ x) (φ y) = ψ x y := by
  intro Z R _ _ _ σ hσ lam hlam hbij N hstd ψ ψ' hψ0 hψb hψs hψ'0 hψ'b hψ's
  obtain ⟨A, hAh, hAu, hAψ⟩ := tw_g_herm Z R σ hσ lam hlam hbij N ψ hψ0 hψb hψs
  obtain ⟨A', hA'h, hA'u, hA'ψ⟩ := tw_g_herm Z R σ hσ lam hlam hbij N ψ' hψ'0 hψ'b hψ's
  obtain ⟨g, hg, hgA⟩ := hstd A hAh hAu
  obtain ⟨g', hg', hgA'⟩ := hstd A' hA'h hA'u
  obtain ⟨φ, hφ⟩ := hermitian_form_standard_basis Z R σ hσ N A g hg hgA
  obtain ⟨φ', hφ'⟩ := hermitian_form_standard_basis Z R σ hσ N A' g' hg' hgA'
  refine ⟨φ.symm.trans φ', fun x y => ?_⟩
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, hA'ψ, hφ', ← hφ, φ.apply_symm_apply,
    φ.apply_symm_apply, ← hAψ]

end PositivityTheory.UnitarySelfGeneration
end
