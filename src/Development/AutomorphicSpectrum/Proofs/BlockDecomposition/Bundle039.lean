module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle001
public import Mathlib.Algebra.Colimit.Ring
public import Mathlib.Data.Nat.Prime.Defs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormLaws
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Algebra.CharP.Frobenius

@[expose] public section

section

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.Coproduct

theorem bijective_algebraMap_zero {A B K : Type} [CommRing A] [CommRing B] [CommRing K]
    [Algebra A B] [Algebra A K] {ι : Fin 0 → (B →ₐ[A] K)} (h : IsWP ι) :
    Function.Bijective (algebraMap A K) := by
  obtain ⟨z, hz, -⟩ := h.ex A (RingHom.id A) (fun i => i.elim0) (fun i => i.elim0)
  have hzx : ∀ a, z (algebraMap A K a) = a := fun a => by
    simpa using congrArg (fun f : A →+* A => f a) hz
  have hid : (algebraMap A K).comp z = RingHom.id K := by
    refine h.uniq K _ _ ?_ (fun i => i.elim0)
    ext a
    simp [hzx]
  refine Function.bijective_iff_has_inverse.mpr ⟨z, hzx, fun k => ?_⟩
  simpa using congrArg (fun f : K →+* K => f k) hid

theorem bijective_one {A B K : Type} [CommRing A] [CommRing B] [CommRing K]
    [Algebra A B] [Algebra A K] {ι : Fin 1 → (B →ₐ[A] K)} (h : IsWP ι) :
    Function.Bijective (ι 0) := by
  obtain ⟨z, hz, hy⟩ := h.ex B (algebraMap A B) (fun _ => RingHom.id B)
    (fun _ => RingHom.id_comp _)
  have hzi : ∀ b, z (ι 0 b) = b := fun b => by
    simpa using congrArg (fun f : B →+* B => f b) (hy 0)
  have hza : ∀ a, z (algebraMap A K a) = algebraMap A B a := fun a => by
    simpa using congrArg (fun f : A →+* B => f a) hz
  have hid : ((ι 0 : B →ₐ[A] K) : B →+* K).comp z = RingHom.id K := by
    refine h.uniq K _ _ ?_ (fun i => ?_)
    · ext a
      simp [hza]
    · obtain rfl : i = 0 := Subsingleton.elim _ _
      ext b
      simp [hzi]
  refine Function.bijective_iff_has_inverse.mpr ⟨z, hzi, fun k => ?_⟩
  simpa using congrArg (fun f : K →+* K => f k) hid

theorem exists_coface {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
    (K : ℕ → Type) [∀ n, CommRing (K n)] [∀ n, Algebra A (K n)]
    (ι : ∀ n, Fin n → (B →ₐ[A] K n)) (h : ∀ n, IsWP (ι n)) :
    ∃ δ : ∀ n, Fin (n + 1) → (K n →ₐ[A] K (n + 1)),
      ∀ n k i, (δ n k).comp (ι n i) = ι (n + 1) (k.succAbove i) := by
  have key : ∀ (n : ℕ) (k : Fin (n + 1)), ∃ d : K n →ₐ[A] K (n + 1),
      ∀ i, d.comp (ι n i) = ι (n + 1) (k.succAbove i) := by
    intro n k
    obtain ⟨z, hz, hy⟩ := (h n).ex (K (n + 1)) (algebraMap A (K (n + 1)))
      (fun i => (ι (n + 1) (k.succAbove i) : B →+* K (n + 1)))
      (fun i => by ext a; simp)
    refine ⟨{ z with commutes' := fun a => congrArg (fun f : A →+* K (n + 1) => f a) hz },
      fun i => ?_⟩
    ext b
    exact congrArg (fun f : B →+* K (n + 1) => f b) (hy i)
  choose δ hδ using key
  exact ⟨δ, hδ⟩

theorem coproduct_low_and_coface : ∀ (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (K : ℕ → Type) [∀ n, CommRing (K n)] [∀ n, Algebra A (K n)] (ι : ∀ n, Fin n → (B →ₐ[A] K n)), (∀ n, IsWP (ι n)) → Function.Bijective (algebraMap A (K 0)) ∧ Function.Bijective (ι 1 0) ∧ ∃ δ : ∀ n, Fin (n + 1) → (K n →ₐ[A] K (n + 1)), ∀ n k i, (δ n k).comp (ι n i) = ι (n + 1) (k.succAbove i) := by
  intro A _ B _ _ K _ _ ι h
  exact ⟨bijective_algebraMap_zero (h 0), bijective_one (h 1), exists_coface K ι h⟩

end GlobalTheory.CompanionTheory.Coproduct
end

section

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.Colim

theorem iota_tr {A : Type} [CommRing A] {G : ℕ → Type} [∀ n, CommRing (G n)] [∀ n, Algebra A (G n)]
    {f : ∀ n, G n →ₐ[A] G (n + 1)} {L : Type} [CommRing L] [Algebra A L] {ι : ∀ n, G n →ₐ[A] L}
    (hc : IsColim f ι) (n : ℕ) : ∀ (k : ℕ) (x : G n), ι (n + k) (tr f n k x) = ι n x
  | 0, _ => rfl
  | k + 1, x => by
    show ι (n + k + 1) (f (n + k) (tr f n k x)) = ι n x
    rw [hc.comm, iota_tr hc n k x]

theorem aic_of_isColim {A : Type} [CommRing A] {G : ℕ → Type} [∀ n, CommRing (G n)] [∀ n, Algebra A (G n)]
    {f : ∀ n, G n →ₐ[A] G (n + 1)} {L : Type} [CommRing L] [Algebra A L] {ι : ∀ n, G n →ₐ[A] L}
    (hc : IsColim f ι) (hA : ∀ n, AICm (f n : G n →+* G (n + 1))) : AIC L := by
  intro P hP hd
  obtain ⟨n, y, hy⟩ := hc.surj P.natDegree (fun i => P.coeff i)
  set Q : Polynomial (G n) := Polynomial.X ^ P.natDegree + ∑ i : Fin P.natDegree, Polynomial.C (y i) * Polynomial.X ^ (i : ℕ) with hQ
  have hQm : Q.Monic := Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt y)
  have hmap : Q.map (ι n : G n →+* L) = P := by

    rw [hQ, Polynomial.map_add (f := _), Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum]
    simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, RingHom.coe_coe, hy]
    conv_rhs => rw [hP.as_sum]
    rw [Fin.sum_univ_eq_sum_range (fun i => Polynomial.C (P.coeff i) * Polynomial.X ^ i) P.natDegree]
  have hQd : 0 < Q.natDegree := by
    have := Polynomial.natDegree_map_le (f := (ι n : G n →+* L)) (p := Q)
    rw [hmap] at this; omega
  obtain ⟨x, hx⟩ := hA n Q hQm hQd
  refine ⟨ι (n + 1) x, ?_⟩
  have h2 : (Q.map (f n : G n →+* G (n + 1))).map (ι (n + 1) : G (n + 1) →+* L) = P := by
    rw [Polynomial.map_map, ← hmap]; congr 1; ext z; simp [hc.comm]
  rw [← h2]
  exact Polynomial.IsRoot.map (ι (n + 1) : G (n + 1) →+* L) hx

theorem val_of_isColim {A : Type} [CommRing A] (π : A) {G : ℕ → Type} [∀ n, CommRing (G n)] [∀ n, Algebra A (G n)]
    {f : ∀ n, G n →ₐ[A] G (n + 1)} {L : Type} [CommRing L] [Algebra A L] {ι : ∀ n, G n →ₐ[A] L}
    (hc : IsColim f ι) (hV : ∀ n, VALm (algebraMap A (G n) π) (f n : G n →+* G (n + 1))) :
    VAL (algebraMap A L π) := by
  intro u v ⟨N, hN⟩
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hN
  obtain ⟨n, y, hy⟩ := hc.surj 4 ![a, b, u, v]
  have h0 := hy 0; have h1 := hy 1; have h2 := hy 2; have h3 := hy 3
  simp only [Matrix.cons_val] at h0 h1 h2 h3
  obtain ⟨k, hk⟩ := hc.ker n 1 (fun _ => y 0 * y 2 + y 1 * y 3 - algebraMap A (G n) π ^ N)
    (fun _ => by simp [h0, h1, h2, h3, hab])
  have hk0 := hk 0
  set m := n + k
  set t := tr f n k
  have hspan : algebraMap A (G m) π ^ N ∈ Ideal.span {t (y 2), t (y 3)} := by
    refine Ideal.mem_span_pair.mpr ⟨t (y 0), t (y 1), ?_⟩
    have := hk0
    simp only [map_sub, map_add (f := _), map_mul, map_pow, AlgHom.commutes] at this
    exact (sub_eq_zero.mp this)
  obtain ⟨e, he, he1, he2⟩ := hV m (t (y 2)) (t (y 3)) ⟨N, hspan⟩
  have hu : ι (m + 1) (f m (t (y 2))) = u := by rw [hc.comm, iota_tr hc n k, h2]
  have hv : ι (m + 1) (f m (t (y 3))) = v := by rw [hc.comm, iota_tr hc n k, h3]
  refine ⟨ι (m + 1) e, he.map (ι (m + 1)), ?_, ?_⟩
  · rw [Ideal.mem_span_singleton] at he1 ⊢
    have := map_dvd (ι (m + 1)) he1
    simpa [map_mul, hu, hv] using this
  · rw [Ideal.mem_span_singleton] at he2 ⊢
    have := map_dvd (ι (m + 1)) he2
    simpa [map_mul, map_sub, hu, hv] using this

theorem aic_val_of_isColim : ∀ (A : Type) [CommRing A] (π : A) (G : ℕ → Type) [∀ n, CommRing (G n)] [∀ n, Algebra A (G n)] (f : ∀ n, G n →ₐ[A] G (n + 1))(L : Type) [CommRing L] [Algebra A L] (ι : ∀ n, G n →ₐ[A] L), IsColim f ι → (∀ n, AICm (f n : G n →+* G (n + 1))) → (∀ n, VALm (algebraMap A (G n) π) (f n : G n →+* G (n + 1))) → AIC L ∧ VAL (algebraMap A L π) :=
  fun _ _ π _ _ _ _ _ _ _ _ hc hA hV => ⟨aic_of_isColim hc hA, val_of_isColim π hc hV⟩
end GlobalTheory.CompanionTheory.Colim
end

section

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.ComplVal

theorem side {T : Type} [CommRing T] (t : T) (hu : ∀ x : T, IsUnit (1 + t * x))
    (f f' a b w E : T) (N : ℕ) (hE : E * E = E) (hab : a * f + b * f' = t ^ N)
    (hw : E * f = t ^ (N + 1) * w) : ∃ c, c * f' = E * f := by
  obtain ⟨v, hv⟩ := (hu (-(w * a))).exists_left_inv
  have key : (1 + t * -(w * a)) * (E * f) = E * t * w * b * f' := by
    linear_combination E * hw - E * t * w * hab - f * hE
  exact ⟨v * (E * t * w * b), by linear_combination -v * key + E * f * hv⟩

theorem mid {T : Type} [CommRing T] (P Q E f F f' F' k v v' u' : T) (hP : P * P = P) (hQ : Q * Q = Q)
    (hA : P * f = P * F * v) (hB : Q * f' = Q * F' * v') (hu : v' * u' = 1)
    (hk : k * F' = P * Q * E * F) : ∃ c, c * f' = P * Q * E * f := by
  exact ⟨v * k * Q * u', by
    linear_combination v * k * u' * hB + v * k * Q * F' * hu + v * Q * hk + v * P * E * F * hQ - Q * E * hA⟩

theorem core {T : Type} [CommRing T] (t : T) (hu : ∀ x : T, IsUnit (1 + t * x))
    (f f' F F' a b s s' c c' d d' k k' E₁ E₂ E : T) (N : ℕ)
    (h₁ : E₁ * E₁ = E₁) (h₂ : E₂ * E₂ = E₂) (hE : E * E = E)
    (hab : a * f + b * f' = t ^ N)
    (hs : s * t ^ (N + 2) = f - F) (hs' : s' * t ^ (N + 2) = f' - F')
    (hc : c * t ^ (N + 1) = E₁ * F) (hc' : c' * t ^ (N + 1) = E₂ * F')
    (hd : d * F = (1 - E₁) * t ^ (N + 1)) (hd' : d' * F' = (1 - E₂) * t ^ (N + 1))
    (hk : k * F' = (1 - E₁) * (1 - E₂) * E * F)
    (hk' : k' * F = (1 - E₁) * (1 - E₂) * (1 - E) * F') :
    ∃ e : T, IsIdempotentElem e ∧ e * f ∈ Ideal.span {f'} ∧ (1 - e) * f' ∈ Ideal.span {f} := by
  obtain ⟨c₁, hc₁⟩ := GlobalTheory.CompanionTheory.ComplVal.side t hu f f' a b (c + E₁ * s * t) E₁ N h₁ hab
    (by linear_combination -E₁ * hs - hc)
  obtain ⟨c₂, hc₂⟩ := GlobalTheory.CompanionTheory.ComplVal.side t hu f' f b a (c' + E₂ * s' * t) E₂ N h₂
    (by linear_combination hab) (by linear_combination -E₂ * hs' - hc')
  have hP : (1 - E₁) * (1 - E₁) = 1 - E₁ := by linear_combination h₁
  have hQ : (1 - E₂) * (1 - E₂) = 1 - E₂ := by linear_combination h₂
  have hA : (1 - E₁) * f = (1 - E₁) * F * (1 + t * (s * d)) := by
    linear_combination -(1 - E₁) * hs - s * t ^ (N + 2) * h₁ - s * t * (1 - E₁) * hd
  have hB : (1 - E₂) * f' = (1 - E₂) * F' * (1 + t * (s' * d')) := by
    linear_combination -(1 - E₂) * hs' - s' * t ^ (N + 2) * h₂ - s' * t * (1 - E₂) * hd'
  obtain ⟨u₁, hu₁⟩ := (hu (s' * d')).exists_right_inv
  obtain ⟨u₂, hu₂⟩ := (hu (s * d)).exists_right_inv
  obtain ⟨c₃, hc₃⟩ := GlobalTheory.CompanionTheory.ComplVal.mid (1 - E₁) (1 - E₂) E f F f' F' k (1 + t * (s * d))
    (1 + t * (s' * d')) u₁ hP hQ hA hB hu₁ hk
  obtain ⟨c₄, hc₄⟩ := GlobalTheory.CompanionTheory.ComplVal.mid (1 - E₂) (1 - E₁) (1 - E) f' F' f F k' (1 + t * (s' * d'))
    (1 + t * (s * d)) u₂ hQ hP hB hA hu₂ (by linear_combination hk')
  refine ⟨E₁ + (1 - E₁) * (1 - E₂) * E, ?_, ?_, ?_⟩
  · show (E₁ + (1 - E₁) * (1 - E₂) * E) * (E₁ + (1 - E₁) * (1 - E₂) * E) = E₁ + (1 - E₁) * (1 - E₂) * E
    linear_combination (1 - 2 * (1 - E₂) * E + (1 - E₂) ^ 2 * E ^ 2) * h₁ + (1 - E₁) * E ^ 2 * h₂
      + (1 - E₁) * (1 - E₂) * hE
  · exact Ideal.mem_span_singleton'.2 ⟨c₁ + c₃, by linear_combination hc₁ + hc₃⟩
  · exact Ideal.mem_span_singleton'.2 ⟨(1 - E₁) * c₂ + c₄, by linear_combination (1 - E₁) * hc₂ + hc₄⟩

theorem compl_val : ∀ (B : Type) [CommRing B] (T : Type) [CommRing T] (π : B) (g : B →+* T), CrystallineSemistableComparison.D.IsCompl π g → VAL π → VAL (g π) := by
  intro B _ T _ π g hC hV
  unfold CrystallineSemistableComparison.D.VAL at hV ⊢
  have := hC.compl
  have hJ : g π ∈ (⊥ : Ideal T).jacobson :=
    IsAdicComplete.le_jacobson_bot (I := Ideal.span {g π}) (Ideal.mem_span_singleton_self (g π))
  have hu : ∀ x : T, IsUnit (1 + g π * x) := fun x => by
    rw [add_comm]; exact Ideal.mem_jacobson_bot.1 hJ x
  intro f₀ f₁ hN
  obtain ⟨N, hN⟩ := hN
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.1 hN
  obtain ⟨x₁, hx₁⟩ := hC.surj (N + 2) f₀
  obtain ⟨x₂, hx₂⟩ := hC.surj (N + 2) f₁
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 hx₁
  obtain ⟨s', hs'⟩ := Ideal.mem_span_singleton'.1 hx₂
  obtain ⟨e₁, he₁, h1a, h1b⟩ := hV x₁ (π ^ (N + 1)) ⟨N + 1, Ideal.mem_span_pair.2 ⟨0, 1, by ring⟩⟩
  obtain ⟨e₂, he₂, h2a, h2b⟩ := hV x₂ (π ^ (N + 1)) ⟨N + 1, Ideal.mem_span_pair.2 ⟨0, 1, by ring⟩⟩
  obtain ⟨c₀, hc₀⟩ := Ideal.mem_span_singleton'.1 h1a
  obtain ⟨d₀, hd₀⟩ := Ideal.mem_span_singleton'.1 h1b
  obtain ⟨c₁, hc₁⟩ := Ideal.mem_span_singleton'.1 h2a
  obtain ⟨d₁, hd₁⟩ := Ideal.mem_span_singleton'.1 h2b
  obtain ⟨P, hPdef⟩ : ∃ P : B, P = (1 - e₁) * (1 - e₂) := ⟨_, rfl⟩
  have hPP : P * P = P := by
    rw [hPdef]; linear_combination (1 - e₂) ^ 2 * he₁.eq + (1 - e₁) * he₂.eq
  have hPe : P * (1 - e₁) = P := by
    rw [hPdef]; linear_combination (1 - e₂) * he₁.eq
  obtain ⟨e, he, ha, hb⟩ := hV (P * x₁ + (1 - P)) (P * x₂) ⟨N + 1, Ideal.mem_span_pair.2
    ⟨P * d₀ + (1 - P) * π ^ (N + 1), 0, by
      linear_combination P * hd₀ + π ^ (N + 1) * hPe
        + (d₀ * x₁ - d₀ - π ^ (N + 1) * x₁ + π ^ (N + 1)) * hPP⟩⟩
  obtain ⟨m, hm⟩ := Ideal.mem_span_singleton'.1 ha
  obtain ⟨m', hm'⟩ := Ideal.mem_span_singleton'.1 hb
  have hkB : m * P * x₂ = (1 - e₁) * (1 - e₂) * e * x₁ := by
    linear_combination P * hm - (m * x₂ - e * x₁ + e) * hPP + e * x₁ * hPdef
  have hk'B : m' * P * x₁ = (1 - e₁) * (1 - e₂) * (1 - e) * x₂ := by
    linear_combination P * hm' - (m' * x₁ - m' - (1 - e) * x₂) * hPP + (1 - e) * x₂ * hPdef
  have i₁ : g e₁ * g e₁ = g e₁ := by rw [← map_mul, he₁.eq]
  have i₂ : g e₂ * g e₂ = g e₂ := by rw [← map_mul, he₂.eq]
  have i₃ : g e * g e = g e := by rw [← map_mul, he.eq]
  have hc : g c₀ * g π ^ (N + 1) = g e₁ * g x₁ := by
    have h := congrArg g hc₀; simp only [map_mul, map_pow] at h; linear_combination h
  have hc' : g c₁ * g π ^ (N + 1) = g e₂ * g x₂ := by
    have h := congrArg g hc₁; simp only [map_mul, map_pow] at h; linear_combination h
  have hd : g d₀ * g x₁ = (1 - g e₁) * g π ^ (N + 1) := by
    have h := congrArg g hd₀; simp only [map_mul, map_pow, map_sub, map_one] at h; linear_combination h
  have hd' : g d₁ * g x₂ = (1 - g e₂) * g π ^ (N + 1) := by
    have h := congrArg g hd₁; simp only [map_mul, map_pow, map_sub, map_one] at h; linear_combination h
  have hk : g m * g P * g x₂ = (1 - g e₁) * (1 - g e₂) * g e * g x₁ := by
    have h := congrArg g hkB; simp only [map_mul, map_sub, map_one] at h; linear_combination h
  have hk' : g m' * g P * g x₁ = (1 - g e₁) * (1 - g e₂) * (1 - g e) * g x₂ := by
    have h := congrArg g hk'B; simp only [map_mul, map_sub, map_one] at h; linear_combination h
  exact GlobalTheory.CompanionTheory.ComplVal.core (g π) hu f₀ f₁ (g x₁) (g x₂) a b s s' (g c₀) (g c₁) (g d₀) (g d₁)
    (g m * g P) (g m' * g P) (g e₁) (g e₂) (g e) N i₁ i₂ i₃ hab hs hs' hc hc' hd hd' hk hk'

end GlobalTheory.CompanionTheory.ComplVal
end

section

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.ColimEx

variable {A : Type} [CommRing A] {G : ℕ → Type} [∀ n, CommRing (G n)] [∀ n, Algebra A (G n)]
  (f : ∀ n, G n →ₐ[A] G (n + 1))

def trA (i j : ℕ) (h : i ≤ j) : G i →ₐ[A] G j :=
  Nat.leRecOn (motive := fun k => G i →ₐ[A] G k) h (fun {k} g => (f k).comp g)
    (AlgHom.id A (G i))

theorem trA_self (i : ℕ) (h : i ≤ i) : trA f i i h = AlgHom.id A (G i) :=
  Nat.leRecOn_self (motive := fun k => G i →ₐ[A] G k) _

theorem trA_succ (i k : ℕ) (h : i ≤ k) (h2 : i ≤ k + 1) :
    trA f i (k + 1) h2 = (f k).comp (trA f i k h) :=
  Nat.leRecOn_succ (motive := fun k => G i →ₐ[A] G k) h _

theorem trA_trans (i j k : ℕ) (hij : i ≤ j) (hjk : j ≤ k) (x : G i) :
    trA f j k hjk (trA f i j hij x) = trA f i k (hij.trans hjk) x := by
  induction k, hjk using Nat.le_induction with
  | base => rw [trA_self]; rfl
  | succ k hjk ih =>
    rw [trA_succ f j k hjk, trA_succ f i k (hij.trans hjk)]
    simp only [AlgHom.comp_apply, ih]

theorem tr_eq_trA (n k : ℕ) (x : G n) : tr f n k x = trA f n (n + k) (Nat.le_add_right n k) x := by
  induction k with
  | zero =>
    show tr f n 0 x = trA f n n (Nat.le_refl n) x
    rw [trA_self]; rfl
  | succ k ih =>
    have h := trA_succ f n (n + k) (Nat.le_add_right n k) (Nat.le_add_right n (k + 1))
    show f (n + k) (tr f n k x) = trA f n (n + k + 1) (Nat.le_add_right n (k + 1)) x
    rw [h, AlgHom.comp_apply, ih]

def trR (i j : ℕ) (h : i ≤ j) : G i →+* G j := (trA f i j h).toRingHom

instance directedSystem_trR : DirectedSystem G fun i j h => trR f i j h where
  map_self i x := by simp [trR, trA_self]
  map_map k j i hij hjk x := trA_trans f i j k hij hjk x

abbrev Lim := Ring.DirectLimit G fun i j h => trR f i j h

instance : Algebra A (Lim f) :=
  ((Ring.DirectLimit.of G (fun i j h => trR f i j h) 0).comp (algebraMap A (G 0))).toAlgebra

def ι (n : ℕ) : G n →ₐ[A] Lim f :=
  { Ring.DirectLimit.of G (fun i j h => trR f i j h) n with
    commutes' := fun a => by
      show Ring.DirectLimit.of G (fun i j h => trR f i j h) n (algebraMap A (G n) a) =
        Ring.DirectLimit.of G (fun i j h => trR f i j h) 0 (algebraMap A (G 0) a)
      rw [← Ring.DirectLimit.of_f (G := G) (f := fun i j h => trR f i j h) (Nat.zero_le n)
        (algebraMap A (G 0) a)]
      simp [trR] }

theorem ι_apply (n : ℕ) (x : G n) :
    ι f n x = Ring.DirectLimit.of G (fun i j h => trR f i j h) n x := rfl

theorem ι_trA (i j : ℕ) (h : i ≤ j) (x : G i) : ι f j (trA f i j h x) = ι f i x := by
  rw [ι_apply, ι_apply]
  exact Ring.DirectLimit.of_f (G := G) (f := fun i j h => trR f i j h) h x

theorem ι_tr (n k : ℕ) (x : G n) : ι f (n + k) (tr f n k x) = ι f n x := by
  rw [tr_eq_trA, ι_trA]

theorem isColim : IsColim f (ι f) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n x
    have := ι_tr f n 1 x
    simpa [tr] using this
  · intro m x
    choose n y hy using fun i => Ring.DirectLimit.exists_of (x i)
    refine ⟨Finset.univ.sup n, fun i => trA f (n i) _ (Finset.le_sup (Finset.mem_univ i)) (y i),
      fun i => ?_⟩
    rw [ι_trA, ι_apply, hy]
  · intro n m y hy
    have h0 : ∀ i, ∃ j, ∃ hij : n ≤ j, trR f n j hij (y i) = 0 := fun i =>
      Ring.DirectLimit.of.zero_exact (f' := fun i j h => trR f i j h) (hy i)
    choose j hj hz using h0
    refine ⟨Finset.univ.sup fun i => j i - n, fun i => ?_⟩
    have hle : j i ≤ n + Finset.univ.sup fun i => j i - n := by
      have := Finset.le_sup (f := fun i => j i - n) (Finset.mem_univ i)
      omega
    rw [tr_eq_trA, ← trA_trans f n (j i) _ (hj i) hle]
    have : trA f n (j i) (hj i) (y i) = 0 := hz i
    rw [this, map_zero]

end GlobalTheory.CompanionTheory.ColimEx

theorem GlobalTheory.CompanionTheory.ColimEx.exists_isColim : ∀ (A : Type) [CommRing A](G : ℕ → Type) [∀ n, CommRing (G n)] [∀ n, Algebra A (G n)] (f : ∀ n, G n →ₐ[A] G (n + 1)), ∃ (L : Type) (_ : CommRing L) (_ : Algebra A L), ∃ ι : ∀ n, G n →ₐ[A] L, IsColim f ι :=
  fun A _ G _ _ f => ⟨GlobalTheory.CompanionTheory.ColimEx.Lim f, inferInstance, inferInstance, GlobalTheory.CompanionTheory.ColimEx.ι f,
    GlobalTheory.CompanionTheory.ColimEx.isColim f⟩
end
end

section

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.PerfectQuotient

theorem exists_frobenius_iterate (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    (h : (p : R) = 0) (k : ℕ) : ∃ f : R →+* R, ∀ x, f x = x ^ p ^ k := by
  rcases subsingleton_or_nontrivial R with hs | hn
  · exact ⟨RingHom.id R, fun x => Subsingleton.elim _ _⟩
  · haveI : CharP R p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).2 h
    exact ⟨iterateFrobenius R p k, fun x => iterateFrobenius_def p k x⟩

theorem solv_pow : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](S : Type) [CommRing S] [Algebra A S] (B : Type) [CommRing B] [Algebra A B] (i : S →ₐ[A] B) (I : Ideal S) (m n : ℕ) (a : Fin m → Fin n → A) (c : Fin m → A), (p : A) = 0 → PQ p (i : S →+* B) I → Solv B a c → ∃ (k : ℕ) (s : Fin n → S), ∀ t, ∑ j, a t j ^ p ^ k • s j - algebraMap A S (c t ^ p ^ k) ∈ I := by
  intro p _ A _ S _ _ B _ _ i I m n a c hp hPQ hS
  obtain ⟨y, hy⟩ := hS
  have hpS : (p : S) = 0 := by
    have := congrArg (algebraMap A S) hp
    simpa using this
  choose k₀ x hx using fun j => hPQ.pow (y j)
  obtain ⟨K, hK⟩ : ∃ K, K = Finset.univ.sup k₀ := ⟨_, rfl⟩
  let s : Fin n → S := fun j => x j ^ p ^ (K - k₀ j)
  have hs : ∀ j, y j ^ p ^ K = i (s j) := by
    intro j
    have hle : k₀ j ≤ K := hK ▸ Finset.le_sup (Finset.mem_univ j)
    have hpow : p ^ K = p ^ k₀ j * p ^ (K - k₀ j) := by
      rw [← pow_add]; congr 1; omega
    have hxj : y j ^ p ^ k₀ j = i (x j) := hx j
    rw [hpow, pow_mul, hxj]
    simp [s, map_pow]
  obtain ⟨fB, hfB⟩ := exists_frobenius_iterate p B hPQ.pf.char K
  have he : ∀ t, i (∑ j, a t j ^ p ^ K • s j - algebraMap A S (c t ^ p ^ K)) = 0 := by
    intro t
    have h1 := congrArg fB (hy t)

    rw [map_sum] at h1
    have h2 : ∀ j, fB (a t j • y j) = a t j ^ p ^ K • i (s j) := by
      intro j
      rw [hfB, smul_pow, hs]
    simp only [h2] at h1
    rw [hfB, ← map_pow] at h1

    rw [map_sub, map_sum, AlgHom.commutes, sub_eq_zero, ← h1]
    exact Finset.sum_congr rfl fun j _ => map_smul i _ _
  choose k₁ hk₁ using fun t => (hPQ.ker _).1 (he t)
  obtain ⟨L, hL⟩ : ∃ L, L = Finset.univ.sup k₁ := ⟨_, rfl⟩
  obtain ⟨fS, hfS⟩ := exists_frobenius_iterate p S hpS L
  refine ⟨K + L, fun j => s j ^ p ^ L, fun t => ?_⟩
  have hle : k₁ t ≤ L := hL ▸ Finset.le_sup (Finset.mem_univ t)
  have hpow : p ^ L = p ^ k₁ t * p ^ (L - k₁ t) := by
    rw [← pow_add]; congr 1; omega
  have hmem : (∑ j, a t j ^ p ^ K • s j - algebraMap A S (c t ^ p ^ K)) ^ p ^ L ∈ I := by
    rw [hpow, pow_mul]
    exact I.pow_mem_of_mem (hk₁ t) _ (pow_pos (Fact.out : p.Prime).pos _)

  rw [← hfS, map_sub, map_sum] at hmem
  have h3 : ∀ j, fS (a t j ^ p ^ K • s j) = a t j ^ p ^ (K + L) • s j ^ p ^ L := by
    intro j
    rw [hfS, smul_pow, ← pow_mul, ← pow_add]
  simp only [h3] at hmem
  rw [hfS, ← map_pow, ← pow_mul, ← pow_add] at hmem
  exact hmem

end GlobalTheory.CompanionTheory.PerfectQuotient
end

section

open CrystallineSemistableComparison.Onto

namespace GlobalTheory.CompanionTheory.Forms

theorem dWedge_exists : CrystallineSemistableComparison.Onto.DWedge := by
  intro K A _ _ _ a f
  refine ⟨exteriorPower.alternatingMapLinearEquiv
    ((exteriorPower.ιMulti A (a + 1) (M := Ω[A⁄K])).curryLeft (KaehlerDifferential.D K A f)), ?_⟩
  intro g₀ g
  unfold CrystallineSemistableComparison.Onto.form
  rw [map_smul, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    AlternatingMap.curryLeft_apply_apply]
  congr 2
  funext k
  refine Fin.cases ?_ (fun i => ?_) k <;> simp

end GlobalTheory.CompanionTheory.Forms
end
