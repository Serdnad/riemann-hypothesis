module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle086
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle097
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle017
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle081
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle082
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle090
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Kernel
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.PhiImage

theorem exists_lim_series {R : Type} [CommRing R] (p : R) [IsPrecomplete (Ideal.span {p}) R] (f : ℕ → R) :
    ∃ L : R, ∀ k, p ^ k ∣ (∑ i ∈ Finset.range k, p ^ i * f i) - L := by
  first
  | exact @_root_.GlobalTheory.LimitSeriesPowSmul.target
  | exact _root_.GlobalTheory.LimitSeriesPowSmul.target
  | (apply _root_.GlobalTheory.LimitSeriesPowSmul.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.LimitSeriesPowSmul.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LimitSeriesPowSmul.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LimitSeriesPowSmul.target ..)

theorem approx {R A : Type} [CommRing R] [CommRing A] (ι : R →+* A) (p : ℕ)
    [IsPrecomplete (Ideal.span {(p : R)}) R] [IsAdicComplete (Ideal.span {(p : A)}) A]
    (φ : A → A) (w : A) (h : ∀ y, ∃ (a : R) (z y' : A), φ y = ι a + w * z + p * φ y') (y : A) :
    ∃ (a : R) (z : A), φ y = ι a + w * z := by
  choose a z nx h using h
  obtain ⟨α, hα⟩ := exists_lim_series (p : R) (fun i => a (nx^[i] y))
  obtain ⟨ζ, hζ⟩ := exists_lim_series (p : A) (fun i => z (nx^[i] y))
  have key : ∀ k, φ y = ι (∑ i ∈ Finset.range k, (p : R) ^ i * a (nx^[i] y)) +
      w * (∑ i ∈ Finset.range k, (p : A) ^ i * z (nx^[i] y)) + (p : A) ^ k * φ (nx^[k] y) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Function.iterate_succ_apply', map_add (f := _), map_mul,
        map_pow, map_natCast]
      linear_combination ih + (p : A) ^ k * h (nx^[k] y)
  refine ⟨α, ζ, sub_eq_zero.1 (IsHausdorff.haus (I := Ideal.span {(p : A)}) inferInstance _ fun k => ?_)⟩
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  obtain ⟨u, hu⟩ := hα k
  obtain ⟨v, hv⟩ := hζ k
  have hu' := congrArg ι hu
  rw [map_sub, map_mul, map_pow, map_natCast] at hu'
  exact ⟨ι u + w * v + φ (nx^[k] y), by linear_combination key k + hu' + w * hv⟩

theorem geom_sum_one_add {R : Type} [CommRing R] {p : ℕ} (hp : p.Prime) (x : R) :
    ∃ c : R, ∑ i ∈ Finset.range p, (x + 1) ^ i = p * c + x ^ (p - 1) := by
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp (Polynomial.X : Polynomial ℤ) 1
  have h1 := geom_sum_mul (Polynomial.X + 1 : Polynomial ℤ) p
  have h2 : (Polynomial.X : Polynomial ℤ) ^ p = Polynomial.X ^ (p - 1) * Polynomial.X := by
    rw [← pow_succ, Nat.sub_add_cancel hp.one_le]
  have h3 : ∑ i ∈ Finset.range p, (Polynomial.X + 1 : Polynomial ℤ) ^ i = (p : Polynomial ℤ) * r + Polynomial.X ^ (p - 1) := by
    refine mul_right_cancel₀ Polynomial.X_ne_zero ?_
    rw [one_pow] at hr
    linear_combination h1 + hr + h2
  refine ⟨Polynomial.aeval x r, ?_⟩
  simpa using congrArg (Polynomial.aeval x) h3

variable {l : ℕ} [Fact l.Prime]

theorem phi_xi (e : Per.Fl l) : ∃ c : Per.Ainf l, Per.φA l (xi e) = l * c + mu e ^ (l - 1) := by
  obtain ⟨c, hc⟩ := geom_sum_one_add (Fact.out : l.Prime) (mu e)
  refine ⟨c, ?_⟩

  rw [← hc, xi, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_pow, mu, sub_add_cancel]
  congr 1
  refine (GlobalTheory.RingIface.phiA_teich l _).trans ?_
  rw [← frobenius_def, ← frobeniusEquiv_apply, RingEquiv.apply_symm_apply]

theorem nat_cancel {A : Type} [CommRing A] (f : ℤ_[l] →+* A) (ht : ∀ x : A, (l : A) * x = 0 → x = 0)
    (m : ℕ) (hm : m ≠ 0) (x y : A) (h : (m : A) * x = m * y) : x = y := by
  have h0 : ((m : ℕ) : ℤ_[l]) ≠ 0 := by exact_mod_cast hm
  have h1 := congrArg f (PadicInt.unitCoeff_spec h0)
  rw [map_natCast, map_mul, map_pow, map_natCast] at h1
  have hp : ∀ (k : ℕ) (x : A), (l : A) ^ k * x = 0 → x = 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => exact fun x hx => ht x (ih _ (by linear_combination hx))
  refine sub_eq_zero.1 (hp ((m : ℕ) : ℤ_[l]).valuation _ ?_)
  refine ((PadicInt.unitCoeff h0).isUnit.map f).mul_left_cancel ?_
  rw [mul_zero, ← mul_assoc, ← h1]
  linear_combination h

theorem alg_tower (a : Per.Ainf l) :
    algebraMap (Per.Acris0 l) (Per.Acris l) (algebraMap (Per.Ainf l) (Per.Acris0 l) a) =
      algebraMap (Per.Ainf l) (Per.Acris l) a := (GlobalTheory.RingIface.tower l a).symm

theorem phiA_alg (a : Per.Ainf l) :
    phiA l (algebraMap (Per.Ainf l) (Per.Acris l) a) = algebraMap (Per.Ainf l) (Per.Acris l) (Per.φA l a) :=
  (GlobalTheory.CrisMaps.phiA_extends l).alg a

theorem on_span {R P A : Type} [CommRing R] [CommRing P] [Algebra R P] [CommRing A] (B : Subalgebra R P)
    (j : B →+* A) (zR : ℤ_[l] →+* R) (ht : ∀ x : A, (l : A) * x = 0 → x = 0)
    (φ : A →+* A) (φR : R → R) (hφ : ∀ a, φ (j (algebraMap R B a)) = j (algebraMap R B (φR a)))
    (ξ c : R) (w : A) (hξ : j (algebraMap R B (φR ξ)) = l * (j (algebraMap R B c) + w))
    (hB : ∀ s : P, s ∈ B ↔ s ∈ Submodule.span R {y : P | ∃ n : ℕ,
      ((n.factorial : ℕ) : P) * y = algebraMap R P ξ ^ n}) (s : B) :
    ∃ (a : R) (z : A), φ (j s) = j (algebraMap R B a) + w * z := by
  obtain ⟨s, hs⟩ := s
  have hs' := (hB s).1 hs
  induction hs' using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨n, hn⟩ := hy
    have h1 : ((n.factorial : ℕ) : B) * ⟨y, hs⟩ = algebraMap R B ξ ^ n := Subtype.ext (by simpa using hn)
    have h2 := congrArg (fun t => φ (j t)) h1
    simp only [map_mul, map_natCast, map_pow, hφ, hξ] at h2
    obtain ⟨d, hd⟩ := GlobalTheory.RingBasics.exists_pow_div_factorial l n
    have h3 := congrArg ((j.comp (algebraMap R B)).comp zR) hd
    rw [map_mul, map_natCast, map_pow, map_natCast] at h3
    have h4 : φ (j ⟨y, hs⟩) = j (algebraMap R B (zR d)) * (j (algebraMap R B c) + w) ^ n := by
      refine nat_cancel ((j.comp (algebraMap R B)).comp zR) ht _ n.factorial_ne_zero _ _ ?_
      rw [h2, mul_pow, ← h3, mul_assoc]
      rfl
    obtain ⟨u, hu⟩ := sub_dvd_pow_sub_pow (j (algebraMap R B c) + w) (j (algebraMap R B c)) n
    refine ⟨zR d * c ^ n, j (algebraMap R B (zR d)) * u, ?_⟩
    rw [h4, map_mul, map_mul, map_pow, map_pow]
    linear_combination j (algebraMap R B (zR d)) * hu
  | zero => exact ⟨0, 0, by
      have : (⟨0, hs⟩ : B) = 0 := rfl
      simp [this]⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨a, z, h⟩ := ihx ((hB x).2 hx)
    obtain ⟨a', z', h'⟩ := ihy ((hB y).2 hy)
    have : (⟨x + y, hs⟩ : B) = ⟨x, (hB x).2 hx⟩ + ⟨y, (hB y).2 hy⟩ := rfl
    refine ⟨a + a', z + z', ?_⟩
    rw [this, map_add (f := _), map_add (f := _), h, h', map_add (f := _), map_add (f := _)]
    ring
  | smul r x hx ihx =>
    obtain ⟨a, z, h⟩ := ihx ((hB x).2 hx)
    have : (⟨r • x, hs⟩ : B) = algebraMap R B r * ⟨x, (hB x).2 hx⟩ := Subtype.ext (Algebra.smul_def r x)
    refine ⟨φR r * a, j (algebraMap R B (φR r)) * z, ?_⟩
    rw [this, map_mul, map_mul, h, hφ, map_mul, map_mul]
    ring

end GlobalTheory.MemLoc.PhiImage

namespace GlobalTheory.MemLoc
open PhiImage

theorem phiA_mem_ainf_add : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, IsEps e → ∀ w : Per.Acris l, (l : Per.Acris l) * w = algebraMap (Per.Ainf l) (Per.Acris l) (mu e) ^ (l - 1) → ∀ y : Per.Acris l, ∃ (a : Per.Ainf l) (z : Per.Acris l), phiA l y = algebraMap (Per.Ainf l) (Per.Acris l) a + w * z := by
  intro l _ e he w hw
  obtain ⟨hc, ht, hd, -⟩ := acris_basic l
  obtain ⟨c, hc'⟩ := phi_xi e
  haveI : IsAdicComplete (Ideal.span {(l : Per.Ainf l)}) (Per.Ainf l) := WittVector.isAdicCompleteIdealSpanP
  refine approx (algebraMap (Per.Ainf l) (Per.Acris l)) l (phiA l) w fun y => ?_
  obtain ⟨s, y', hy⟩ := hd y 1
  obtain ⟨a, z, h⟩ := on_span (l := l) (Per.Acris0 l) (algebraMap (Per.Acris0 l) (Per.Acris l)) (Per.zA l) ht
    (phiA l) (Per.φA l) (fun a => by rw [alg_tower, alg_tower, phiA_alg]) (xi e) c w
    (by rw [alg_tower, alg_tower, hc', map_add (f := _), map_mul, map_natCast, map_pow, mul_add, hw])
    (mem_Acris0_iff_span l e he) s
  refine ⟨a, z, y', ?_⟩
  rw [hy, map_add (f := _), h, alg_tower, pow_one, map_mul, map_natCast]

end GlobalTheory.MemLoc
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem quot_pow_torsionFree_sep {A O : Type*} [CommRing A] [IsDomain A] [CommRing O] [IsDomain O]
    (θ : A →+* O) (ξ p : A) (hξ : ξ ≠ 0) (hker : ∀ a, θ a = 0 ↔ ξ ∣ a) (hp : θ p ≠ 0)
    (hsep : ∀ x : O, (∀ k : ℕ, θ p ^ k ∣ x) → x = 0) (n : ℕ) :
    (∀ a : A, ξ ^ n ∣ p * a → ξ ^ n ∣ a) ∧
      ∀ a : A, (∀ k : ℕ, ∃ b : A, ξ ^ n ∣ a - p ^ k * b) → ξ ^ n ∣ a := by
  have h0 : ∀ (m : ℕ) (x : A), ξ ^ (m + 1) ∣ x → θ x = 0 := fun m x hx =>
    (hker x).2 ((dvd_pow_self ξ m.succ_ne_zero).trans hx)
  have hθξ : θ ξ = 0 := (hker ξ).2 dvd_rfl
  induction n with
  | zero => simp
  | succ n ih =>
    refine ⟨fun a ha => ?_, fun a ha => ?_⟩
    · have h1 := h0 n _ ha
      rw [map_mul] at h1
      obtain ⟨a', rfl⟩ := (hker a).1 ((mul_eq_zero.1 h1).resolve_left hp)
      rw [pow_succ', mul_left_comm, mul_dvd_mul_iff_left hξ] at ha
      rw [pow_succ', mul_dvd_mul_iff_left hξ]
      exact ih.1 a' ha
    · have h1 : θ a = 0 := hsep _ fun k => by
        obtain ⟨b, hb⟩ := ha k
        have h2 := h0 n _ hb
        rw [map_sub, map_mul, map_pow, sub_eq_zero] at h2
        exact ⟨θ b, h2⟩
      obtain ⟨a', rfl⟩ := (hker a).1 h1
      rw [pow_succ', mul_dvd_mul_iff_left hξ]
      refine ih.2 a' fun k => ?_
      obtain ⟨b, hb⟩ := ha k
      have h2 := h0 n _ hb
      rw [map_sub, h1, map_mul, map_pow, zero_sub, neg_eq_zero] at h2
      obtain ⟨b', rfl⟩ := (hker b).1 ((mul_eq_zero.1 h2).resolve_left (pow_ne_zero k hp))
      refine ⟨b', ?_⟩
      rwa [pow_succ', mul_left_comm, ← mul_sub, mul_dvd_mul_iff_left hξ] at hb

theorem ainf_quot_xi_pow_torsionFree_sep : ∀ (l : ℕ) [Fact l.Prime] (e : Per.Fl l), IsEps e → ∀ n : ℕ, (∀ a : Per.Ainf l, xi e ^ n ∣ ((l : ℕ) : Per.Ainf l) * a → xi e ^ n ∣ a) ∧ ∀ a : Per.Ainf l, (∀ k : ℕ, ∃ b : Per.Ainf l, xi e ^ n ∣ a - ((l : ℕ) : Per.Ainf l) ^ k * b) → xi e ^ n ∣ a := by
  intro l _ e he n
  obtain ⟨-, hdom, -, hk⟩ := theta_ker_facts l
  obtain ⟨h1, h2⟩ := hk e he
  refine quot_pow_torsionFree_sep (Per.θ l) (xi e) _ h2 (fun a => ?_) ?_ (fun x hx => ?_) n
  · rw [← RingHom.mem_ker, h1, Ideal.mem_span_singleton]
  · rw [map_natCast]
    exact fun h => GlobalTheory.RingBasics.p_ne_zero (p := l) (by simpa using congrArg Subtype.val h)
  · rw [map_natCast] at hx
    refine IsHausdorff.haus (I := Ideal.span {((l : ℕ) : Per.OC l)}) inferInstance x fun k => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact hx k

end GlobalTheory.MemLoc
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.PdModP

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A]

def low (R : Type) {A : Type} [CommRing R] [CommRing A] [Algebra R A] (γ : ℕ → A) (N : ℕ) : Submodule R A :=
  Submodule.span R (γ '' {m | m < N})

theorem low_mono (γ : ℕ → A) {M N : ℕ} (h : M ≤ N) : low R γ M ≤ low R γ N :=
  Submodule.span_mono (Set.image_mono fun _ hm => lt_of_lt_of_le hm h)

theorem mem_low_succ (γ : ℕ → A) (N : ℕ) (s : A) (hs : s ∈ low R γ (N + 1)) :
    ∃ (a : R) (y : A), y ∈ low R γ N ∧ s = a • γ N + y := by
  have e : {m | m < N + 1} = insert N {m | m < N} := by
    ext m; simp only [Set.mem_ofPred_eq, Set.mem_insert_iff]; omega
  rw [low, e, Set.image_insert_eq, Submodule.mem_span_insert] at hs
  exact hs

section
variable (hu : ∀ n : ℕ, IsUnit ((n.factorial : ℕ) : A)) (ξ : R) (γ : ℕ → A)
  (hγ : ∀ n : ℕ, ((n.factorial : ℕ) : A) * γ n = algebraMap R A ξ ^ n)
include hu hγ

theorem pow_dvd_gamma {m n : ℕ} (h : m ≤ n) : algebraMap R A ξ ^ m ∣ γ n := by
  obtain ⟨v, hv⟩ := (hu n).exists_left_inv
  have : γ n = v * algebraMap R A ξ ^ n := by rw [← hγ, ← mul_assoc, hv, one_mul]
  rw [this]
  exact Dvd.dvd.mul_left (pow_dvd_pow _ h) _

theorem mul_gamma (n : ℕ) : algebraMap R A ξ * γ n = ((n + 1 : ℕ) : A) * γ (n + 1) := by
  refine (hu n).mul_left_cancel ?_
  have h1 := hγ n
  have h2 := hγ (n + 1)
  rw [Nat.factorial_succ, Nat.cast_mul, pow_succ] at h2
  linear_combination (algebraMap R A ξ) * h1 - h2

theorem low_inter (hreg : ∀ y : A, algebraMap R A ξ * y = 0 → y = 0)
    (hsat : ∀ a : R, algebraMap R A ξ ∣ algebraMap R A a → ξ ∣ a) (N : ℕ) :
    ∀ s ∈ low R γ N, algebraMap R A ξ ^ N ∣ s → ∃ c : R, s = c • ((N : A) * γ N) := by
  have hregn : ∀ (n : ℕ) (y : A), algebraMap R A ξ ^ n * y = 0 → y = 0 := by
    intro n
    induction n with
    | zero => intro y hy; simpa using hy
    | succ n ih => intro y hy; exact hreg y (ih _ (by rw [← hy]; ring))
  induction N with
  | zero =>
    intro s hs _
    refine ⟨0, ?_⟩
    simpa [low] using hs
  | succ N ih =>
    intro s hs hd
    obtain ⟨a, y, hy, rfl⟩ := mem_low_succ γ N s hs
    have h1 : algebraMap R A ξ ^ N ∣ a • γ N := by
      rw [Algebra.smul_def]
      exact Dvd.dvd.mul_left (pow_dvd_gamma hu ξ γ hγ le_rfl) _
    obtain ⟨c, rfl⟩ := ih y hy ((dvd_add_right h1).1 ((pow_dvd_pow _ N.le_succ).trans hd))
    obtain ⟨z, hz⟩ := hd
    have h2 : algebraMap R A ξ ∣ algebraMap R A (a + c * N) := by
      refine ⟨(N.factorial : ℕ) * z, sub_eq_zero.1 (hregn N _ ?_)⟩
      rw [Algebra.smul_def, Algebra.smul_def] at hz
      rw [map_add (f := _), map_mul, map_natCast]
      have h3 := hγ N
      linear_combination ((N.factorial : ℕ) : A) * hz - (algebraMap R A a + algebraMap R A c * N) * h3
    obtain ⟨d, hd⟩ := hsat _ h2
    refine ⟨d, ?_⟩
    have h4 := congrArg (algebraMap R A) hd
    rw [map_add (f := _), map_mul, map_natCast, map_mul] at h4
    rw [← mul_gamma hu ξ γ hγ, Algebra.smul_def, Algebra.smul_def, Algebra.smul_def]
    linear_combination γ N * h4

theorem split_low (N : ℕ) (w : A) (hw : w ∈ Submodule.span R (Set.range γ)) :
    ∃ w₁ ∈ low R γ N, algebraMap R A ξ ^ N ∣ w - w₁ := by
  first
  | exact @_root_.GlobalTheory.IsolatedTheoremThree.main
  | exact _root_.GlobalTheory.IsolatedTheoremThree.main
  | (apply _root_.GlobalTheory.IsolatedTheoremThree.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IsolatedTheoremThree.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IsolatedTheoremThree.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IsolatedTheoremThree.main ..)

end

theorem exists_low (γ : ℕ → A) (s : A) (hs : s ∈ Submodule.span R (Set.range γ)) : ∃ M, s ∈ low R γ M := by
  induction hs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, rfl⟩ := hx
    exact ⟨m + 1, Submodule.subset_span ⟨m, m.lt_succ_self, rfl⟩⟩
  | zero => exact ⟨0, zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨M, h1⟩ := hx
    obtain ⟨N, h2⟩ := hy
    exact ⟨max M N, add_mem (low_mono γ (le_max_left _ _) h1) (low_mono γ (le_max_right _ _) h2)⟩
  | smul a x _ hx =>
    obtain ⟨M, h1⟩ := hx
    exact ⟨M, Submodule.smul_mem _ _ h1⟩

theorem mem_of_forall (hu : ∀ n : ℕ, IsUnit ((n.factorial : ℕ) : A)) (ξ : R) (γ : ℕ → A)
    (hγ : ∀ n : ℕ, ((n.factorial : ℕ) : A) * γ n = algebraMap R A ξ ^ n)
    (hreg : ∀ y : A, algebraMap R A ξ * y = 0 → y = 0)
    (hsat : ∀ a : R, algebraMap R A ξ ∣ algebraMap R A a → ξ ∣ a) (p : ℕ) (hp : 0 < p)
    (s : A) (hs : s ∈ Submodule.span R (Set.range γ))
    (h : ∀ n : ℕ, ∃ u : A, ∃ w ∈ Submodule.span R (Set.range γ), s = u + p * w ∧ algebraMap R A ξ ^ n ∣ u) :
    ∃ w ∈ Submodule.span R (Set.range γ), s = p * w := by
  obtain ⟨M, hM⟩ := exists_low γ s hs
  obtain ⟨u, w, hw, e, hd⟩ := h (p * M)
  obtain ⟨w₁, h1, h2⟩ := split_low hu ξ γ hγ (p * M) w hw
  have h3 : s - p * w₁ ∈ low R γ (p * M) := by
    refine sub_mem (low_mono γ (Nat.le_mul_of_pos_left M hp) hM) ?_
    rw [← nsmul_eq_mul]
    exact nsmul_mem h1 p
  obtain ⟨c, hc⟩ := low_inter hu ξ γ hγ hreg hsat (p * M) _ h3
    (by convert dvd_add hd (Dvd.dvd.mul_left h2 (p : A)) using 1; rw [e]; ring)
  refine ⟨w₁ + (c * M) • γ (p * M), add_mem (Submodule.span_mono (Set.image_subset_range _ _) h1)
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)), ?_⟩
  rw [Algebra.smul_def] at hc
  rw [Algebra.smul_def, map_mul, map_natCast]
  push_cast at hc
  linear_combination hc

theorem exists_eps (l : ℕ) [Fact l.Prime] : ∃ e : Per.Fl l, IsEps e := by
  obtain ⟨ζ, e, h0, -, h1, hr⟩ := exists_zeta_eps l
  refine ⟨e, ?_, fun h => ?_⟩
  · have h := hr 0
    rw [h0, map_one] at h
    exact Subtype.ext h
  · have h' := hr 1
    have h2 : rootT e 1 = 1 := h
    rw [h2] at h'
    apply h1
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [map_one, ← h']
    rfl

theorem xi_sat_pow {l : ℕ} [Fact l.Prime] {e : Per.Fl l} (he : IsEps e) (k : ℕ) (a : Per.Ainf l)
    (h : xi e ∣ (l : Per.Ainf l) ^ k * a) : xi e ∣ a := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    apply ih
    have := XiHaus.xi_sat he 1 ((l : Per.Ainf l) ^ k * a) (by rwa [pow_one, ← mul_assoc, ← pow_succ'])
    rwa [pow_one] at this

end GlobalTheory.MemLoc.PdModP

namespace GlobalTheory.MemLoc

open PdModP in
theorem dvd_of_forall_fil_add : ∀ (l : ℕ) [Fact l.Prime], ∀ s : Per.Acris0 l,
    (∀ n : ℕ, ∃ (u w : Per.Acris0 l), s = u + (l : Per.Acris0 l) * w ∧ (u : Per.AinfP l) ∈ Per.kerP l ^ n) →
    (l : Per.Acris0 l) ∣ s := by
  intro l hl s h
  obtain ⟨e, he⟩ := exists_eps l
  have hu : ∀ n : ℕ, IsUnit ((n.factorial : ℕ) : Per.AinfP l) := fun n => GlobalTheory.RingBasics.isUnit_nat l _ n.factorial_ne_zero
  have hex : ∀ n : ℕ, ∃ g : Per.AinfP l,
      ((n.factorial : ℕ) : Per.AinfP l) * g = algebraMap (Per.Ainf l) (Per.AinfP l) (xi e) ^ n := fun n => by
    obtain ⟨v, hv⟩ := (hu n).exists_right_inv
    exact ⟨v * _, by rw [← mul_assoc, hv, one_mul]⟩
  choose γ hγ using hex
  have hspan : ∀ x : Per.AinfP l, x ∈ Per.Acris0 l ↔ x ∈ Submodule.span (Per.Ainf l) (Set.range γ) := by
    intro x
    rw [mem_Acris0_iff_span l e he]
    congr! 2
    ext y
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, (hu n).mul_left_cancel (by rw [hγ, hn])⟩
    · rintro ⟨n, rfl⟩
      exact ⟨n, hγ n⟩
  have := XiHaus.isDomain_Fl (l := l)
  have hle : Submonoid.powers (l : Per.Ainf l) ≤ nonZeroDivisors _ :=
    powers_le_nonZeroDivisors_of_noZeroDivisors (WittVector.p_nonzero l (Per.Fl l))
  have hdom : IsDomain (Per.AinfP l) := IsLocalization.isDomain_of_le_nonZeroDivisors _ hle
  have hinj := IsLocalization.injective (Per.AinfP l) hle
  have hx0 : algebraMap (Per.Ainf l) (Per.AinfP l) (xi e) ≠ 0 := by
    rw [map_ne_zero_iff _ hinj]
    intro h0
    exact XiHaus.xi_coeff_zero_ne he (by rw [h0, WittVector.zero_coeff])
  obtain ⟨w, hw, e1⟩ := mem_of_forall hu (xi e) γ hγ (fun y hy => (mul_eq_zero.1 hy).resolve_left hx0)
    (by
      rintro a ⟨z, hz⟩
      obtain ⟨⟨b, ⟨_, k, rfl⟩⟩, hb⟩ := IsLocalization.surj (Submonoid.powers (l : Per.Ainf l)) z
      refine xi_sat_pow he k a ⟨b, hinj ?_⟩
      simp only at hb
      rw [map_mul, map_mul, hz, ← hb]
      ring)
    l hl.out.pos s ((hspan _).1 s.2) (fun n => by
      obtain ⟨u, w, h1, h2⟩ := h n
      refine ⟨u, w, (hspan _).1 w.2, by rw [h1]; simp, ?_⟩
      rwa [ker_localizedTheta_eq_span_xi l e he, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h2)
  exact ⟨⟨w, (hspan _).2 hw⟩, Subtype.ext (by simpa using e1)⟩

end GlobalTheory.MemLoc
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.acris_membership_span_iff : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, IsEps e → ∀ s : Per.AinfP l, s ∈ Per.Acris0 l ↔ s ∈ Submodule.span (Per.Ainf l) {y : Per.AinfP l | ∃ n : ℕ, ((n.factorial : ℕ) : Per.AinfP l) * y = algebraMap (Per.Ainf l) (Per.AinfP l) (xi e) ^ n} := by
  first | exact @GlobalTheory.MemLoc.mem_Acris0_iff_span | exact GlobalTheory.MemLoc.mem_Acris0_iff_span | (intros; apply GlobalTheory.MemLoc.mem_Acris0_iff_span <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.bdRPlus_simple_roots_section_unique_equivariant : ∀ (l : ℕ) [Fact l.Prime], ∀ o : Om l →+* Per.BdRp l, IsSec o → (∀ (x : Om l) (y : Per.BdRp l) (f : Polynomial (Om l)), Per.θD l y = (x : ℂ_[l]) → f.eval x = 0 → f.derivative.eval x ≠ 0 → (f.map o).eval y = 0 → y = o x) ∧ (∀ o' : Om l →+* Per.BdRp l, IsSec o' → o' = o) ∧ ∀ (g : Per.Gq l) (x : Om l), Per.σDp g (o x) = o (g x) := by
  first | exact @GlobalTheory.MemLoc.SecUniq.main | exact GlobalTheory.MemLoc.SecUniq.main | (intros; apply GlobalTheory.MemLoc.SecUniq.main <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.rootOfUnity_prime_to_teichmuller_lift : ∀ (l : ℕ) [Fact l.Prime], ∀ o : Om l →+* Per.BdRp l, IsSec o → ∀ (c : Om l) (m : ℕ), 0 < m → ¬ l ∣ m → c ^ m = 1 → (∃ xb : Per.Fl l, IsTiltOf c m xb) ∧ ∀ xb : Per.Fl l, IsTiltOf c m xb → xb ^ m = 1 ∧ ((xb.untilt : Per.OC l) : ℂ_[l]) = (c : ℂ_[l]) ∧ aDp l (Per.tm xb) = o c := by
  first | exact @GlobalTheory.MemLoc.rootOfUnity_teichmuller | exact GlobalTheory.MemLoc.rootOfUnity_teichmuller | (intros; apply GlobalTheory.MemLoc.rootOfUnity_teichmuller <;> assumption)
end
