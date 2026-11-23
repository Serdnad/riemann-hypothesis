module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle049
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle055
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle072
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.Bell
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
public import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Mathlib.RingTheory.Smooth.AdicCompletion
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Etale.Basic

@[expose] public section

section

noncomputable section
namespace GlobalTheory.MemLoc
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

theorem zeta_pow_iter {M : Type*} [Monoid M] {p : ℕ} {ζ : ℕ → M} (hζ : ∀ n, ζ (n + 1) ^ p = ζ n)
    (m n : ℕ) : ζ (m + n) ^ p ^ n = ζ m := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_mul, ← add_assoc, hζ, ih]

theorem zeta_exists_system (K : Type*) [Field K] [IsAlgClosed K] [CharZero K] (p : ℕ)
    [hp : Fact p.Prime] :
    ∃ ζ : ℕ → K, ζ 0 = 1 ∧ (∀ m, ζ (m + 1) ^ p = ζ m) ∧ ζ 1 ≠ 1 := by
  have : NeZero (p : K) := ⟨Nat.cast_ne_zero.2 hp.out.ne_zero⟩
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic p K)
    (ne_of_gt (Polynomial.degree_cyclotomic_pos p K hp.out.pos))
  have hzp : IsPrimitiveRoot z p := Polynomial.isRoot_cyclotomic_iff.1 hz
  choose r hr using fun x : K => IsAlgClosed.exists_pow_nat_eq x hp.out.pos
  refine ⟨fun n => Nat.casesOn n 1 (fun m => r^[m] z), rfl, fun n => ?_,
    hzp.ne_one hp.out.one_lt⟩
  cases n with
  | zero => exact hzp.pow_eq_one
  | succ m =>
    show r^[m + 1] z ^ p = r^[m] z
    rw [Function.iterate_succ_apply', hr]

section Tilt

variable {p : ℕ} [hp : Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]

theorem zeta_coeff_root_iterate (x : PreTilt O p) (n m : ℕ) :
    PreTilt.coeff m ((frobeniusEquiv (PreTilt O p) p).symm^[n] x) = PreTilt.coeff (m + n) x := by
  induction n generalizing m with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', PreTilt.coeff_frobeniusEquiv_symm, ih]
    congr 2
    omega

theorem zeta_exists_tilt [IsAdicComplete (Ideal.span {(p : O)}) O] (x : ℕ → O)
    (hx : ∀ n, x (n + 1) ^ p = x n) :
    ∃ e : PreTilt O p, ∀ n, ((frobeniusEquiv (PreTilt O p) p).symm^[n] e).untilt = x n := by
  let e : PreTilt O p := ⟨fun n => Ideal.Quotient.mk (Ideal.span {(p : O)}) (x n), fun n => by
    show (Ideal.Quotient.mk (Ideal.span {(p : O)}) (x (n + 1))) ^ p = _
    rw [← map_pow, hx]⟩
  refine ⟨e, fun n => Perfection.teichmuller_spec fun m => ⟨x (n + m), ?_, by rw [zeta_pow_iter hx]⟩⟩
  have := zeta_coeff_root_iterate e n m
  rw [add_comm] at this
  exact this.symm

end Tilt

theorem exists_zeta_eps (l : ℕ) [hl : Fact l.Prime] :
    ∃ (ζ : ℕ → Om l) (ε : Per.Fl l), ζ 0 = 1 ∧ (∀ m, ζ (m + 1) ^ l = ζ m) ∧ ζ 1 ≠ 1 ∧
      ∀ m, (rootT ε m : ℂ_[l]) = algebraMap (Om l) ℂ_[l] (ζ m) := by
  obtain ⟨ζ, h0, hs, h1⟩ := zeta_exists_system (Om l) l
  have hmem : ∀ m, algebraMap (Om l) ℂ_[l] (ζ m) ∈ PadicComplexInt l := fun m => by
    have h : algebraMap (Om l) ℂ_[l] (ζ m) ^ l ^ m = 1 := by
      have := zeta_pow_iter hs 0 m
      rw [zero_add, h0] at this
      rw [← map_pow, this, map_one]
    have h2 : Valued.v (algebraMap (Om l) ℂ_[l] (ζ m)) ^ l ^ m ≤ 1 := by
      rw [← map_pow, h, map_one]
    change Valued.v (algebraMap (Om l) ℂ_[l] (ζ m)) ≤ 1
    exact (pow_le_one_iff_of_nonneg zero_le (pow_ne_zero _ hl.out.ne_zero)).1 h2
  obtain ⟨e, he⟩ := zeta_exists_tilt (p := l) (O := Per.OC l)
    (fun m => ⟨algebraMap (Om l) ℂ_[l] (ζ m), hmem m⟩) (fun m => Subtype.ext (by
      show algebraMap (Om l) ℂ_[l] (ζ (m + 1)) ^ l = algebraMap (Om l) ℂ_[l] (ζ m)
      rw [← map_pow, hs]))
  exact ⟨ζ, e, h0, hs, h1, fun m => congrArg Subtype.val (he m)⟩

end GlobalTheory.MemLoc
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem pow_sub_one_pow_congr_geom_sum_pow {R : Type} [CommRing R] {l : ℕ} (hl : l.Prime) (x : R) :
    (l : R) ∣ (x ^ l - 1) ^ (l - 1) - (∑ i ∈ Finset.range l, x ^ i) ^ l := by
  have key : (l : Polynomial ℤ) ∣ (Polynomial.X ^ l - 1) ^ (l - 1) -
      (∑ i ∈ Finset.range l, (Polynomial.X : Polynomial ℤ) ^ i) ^ l := by
    set y : Polynomial ℤ := Polynomial.X - 1 with hy
    have hy0 : y ≠ 0 := Polynomial.X_sub_C_ne_zero (1 : ℤ)
    obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hl y 1
    have hX : y + 1 = Polynomial.X := by rw [hy]; ring
    rw [hX, one_pow] at hr
    obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, (Nat.sub_add_cancel hl.one_le).symm⟩
    set s : Polynomial ℤ := ∑ i ∈ Finset.range (k + 1), (Polynomial.X : Polynomial ℤ) ^ i with hs
    have h1 : s * y = Polynomial.X ^ (k + 1) - 1 := geom_sum_mul _ _
    have h2 : s = y ^ k + ((k + 1 : ℕ) : Polynomial ℤ) * r := by
      refine mul_right_cancel₀ hy0 ?_
      rw [h1, hr]; ring
    have h3 : ((k + 1 : ℕ) : Polynomial ℤ) ∣ s - y ^ k := ⟨r, by rw [h2]; ring⟩
    have h4 : ((k + 1 : ℕ) : Polynomial ℤ) ∣ (Polynomial.X ^ (k + 1) - 1) - y ^ (k + 1) :=
      ⟨y * r, by rw [hr]; ring⟩
    have h5 := h3.trans (sub_dvd_pow_sub_pow s (y ^ k) (k + 1))
    have h6 := h4.trans (sub_dvd_pow_sub_pow _ (y ^ (k + 1)) k)
    have h7 := dvd_sub h6 h5
    rw [← pow_mul, ← pow_mul, mul_comm k (k + 1), sub_sub_sub_cancel_right] at h7
    simpa using h7

  simpa [map_sum] using map_dvd (Polynomial.aeval (R := ℤ) x) key

theorem exists_div_prime_pow_dvd {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {l : ℕ} (hl : l.Prime)
    (hu : ∀ n : ℕ, IsUnit ((n.factorial : ℕ) : A)) (S : Subalgebra R A) (η z : R)
    (hη : ∀ n : ℕ, ∃ g ∈ S, ((n.factorial : ℕ) : A) * g = algebraMap R A η ^ n)
    (hz : ∀ n : ℕ, ∃ g ∈ S, ((n.factorial : ℕ) : A) * g = algebraMap R A z ^ n) :
    ∃ w : S, (l : A) * (w : A) = algebraMap R A (η ^ l + l * z) ∧ (l : S) ∣ w ^ l := by
  obtain ⟨g₁, m₁, h₁⟩ := hη l
  obtain ⟨g₂, m₂, h₂⟩ := hη (l * l)
  obtain ⟨g₃, m₃, h₃⟩ := hz l
  have hf : ((l.factorial : ℕ) : A) = (l : A) * ((l - 1).factorial : ℕ) := by
    rw [← Nat.mul_factorial_pred hl.ne_zero]; push_cast; rfl
  have hb : (((l * l).factorial : ℕ) : A) =
      (Nat.uniformBell l l : A) * ((l.factorial : ℕ) : A) ^ l * ((l.factorial : ℕ) : A) := by
    rw [← Nat.uniformBell_mul_eq l hl.ne_zero]; push_cast; rfl
  have hg : g₁ ^ l = (Nat.uniformBell l l : A) * ((l.factorial : ℕ) : A) * g₂ := by
    refine ((hu l).pow l).mul_left_cancel ?_
    rw [← mul_pow, h₁, ← pow_mul, ← h₂, hb]; ring
  let a : S := (((l - 1).factorial : ℕ) : S) * ⟨g₁, m₁⟩
  let b : S := algebraMap R S z
  refine ⟨a + b, ?_, ?_⟩
  · rw [map_add (f := _), map_mul, map_pow, map_natCast, ← h₁, hf]
    simp only [a, b]
    push_cast
    ring
  · obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hl a b
    have ha : (l : S) ∣ a ^ l := by
      refine ⟨(((l - 1).factorial : ℕ) : S) ^ l * (Nat.uniformBell l l : S) * (((l - 1).factorial : ℕ) : S) *
        ⟨g₂, m₂⟩, Subtype.ext ?_⟩
      simp only [a]
      push_cast
      rw [mul_pow, hg, hf]; ring
    have hb : (l : S) ∣ b ^ l := by
      refine ⟨(((l - 1).factorial : ℕ) : S) * ⟨g₃, m₃⟩, Subtype.ext ?_⟩
      simp only [b]
      push_cast
      rw [← h₃, hf]; ring
    rw [hr]
    exact dvd_add (dvd_add ha hb) ⟨a * b * r, by ring⟩

theorem exists_dividedPower_mem_Acris0 (l : ℕ) [Fact l.Prime] (x : Per.Ainf l) (hx : Per.θ l x = 0) (n : ℕ) :
    ∃ g ∈ Per.Acris0 l, ((n.factorial : ℕ) : Per.AinfP l) * g = algebraMap (Per.Ainf l) (Per.AinfP l) x ^ n := by
  obtain ⟨u, hu⟩ := (GlobalTheory.RingBasics.isUnit_nat l _ n.factorial_ne_zero).exists_right_inv
  have h : ((n.factorial : ℕ) : Per.AinfP l) * (u * algebraMap (Per.Ainf l) (Per.AinfP l) x ^ n) =
      algebraMap (Per.Ainf l) (Per.AinfP l) x ^ n := by rw [← mul_assoc, hu, one_mul]
  refine ⟨_, ?_, h⟩
  apply GlobalTheory.RingIface.dividedPower_mem_Acris0 <;> assumption

theorem tm_root_pow (l : ℕ) [Fact l.Prime] (e : Per.Fl l) :
    Per.tm ((frobeniusEquiv (Per.Fl l) l).symm e) ^ l = Per.tm e := by
  rw [← map_pow]
  congr 1
  exact frobeniusEquiv_symm_pow_p (Per.Fl l) l e

theorem exists_mu_pow_div_of_isEps (l : ℕ) [hl : Fact l.Prime] (e : Per.Fl l) (he : IsEps e) :
    ∃ w : Per.Acris0 l, (l : Per.AinfP l) * (w : Per.AinfP l) =
      algebraMap (Per.Ainf l) (Per.AinfP l) (mu e) ^ (l - 1) ∧ (l : Per.Acris0 l) ∣ w ^ l := by
  set x := Per.tm ((frobeniusEquiv (Per.Fl l) l).symm e) with hx
  have hxl : x ^ l = Per.tm e := tm_root_pow l e
  have hmu : mu e = x ^ l - 1 := by rw [hxl]; rfl
  have hθmu : Per.θ l (x ^ l - 1) = 0 := by
    rw [hxl, map_sub, map_one, WittVector.fontaineTheta_teichmuller, he.1, sub_self]
  have hθx : Per.θ l (x - 1) ≠ 0 := by
    rw [hx, map_sub, map_one, WittVector.fontaineTheta_teichmuller, sub_ne_zero]
    exact he.2
  have hη : Per.θ l (∑ i ∈ Finset.range l, x ^ i) = 0 := by
    rw [← geom_sum_mul, map_mul] at hθmu
    exact (mul_eq_zero.1 hθmu).resolve_right hθx
  obtain ⟨z, hz⟩ := pow_sub_one_pow_congr_geom_sum_pow hl.out x
  have hθz : Per.θ l z = 0 := by
    have h := congrArg (Per.θ l) hz
    have h1 : l - 1 ≠ 0 := by have := hl.out.two_le; omega
    rw [map_sub, map_pow, map_pow, hθmu, hη, zero_pow h1, zero_pow hl.out.ne_zero, sub_self, map_mul,
      map_natCast] at h
    refine (mul_eq_zero.1 h.symm).resolve_left ?_
    exact_mod_cast hl.out.ne_zero
  obtain ⟨w, hw, hd⟩ := exists_div_prime_pow_dvd hl.out
    (fun n => GlobalTheory.RingBasics.isUnit_nat l _ n.factorial_ne_zero) (Per.Acris0 l) _ z
    (exists_dividedPower_mem_Acris0 l _ hη) (exists_dividedPower_mem_Acris0 l _ hθz)
  refine ⟨w, ?_, hd⟩
  rw [hw, ← hz, add_sub_cancel, map_pow, hmu]

theorem exists_mu_pow_div : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, e.untilt = 1 →
    ∃ w : Per.Acris0 l, (l : Per.AinfP l) * (w : Per.AinfP l) =
      algebraMap (Per.Ainf l) (Per.AinfP l) (mu e) ^ (l - 1) ∧ (l : Per.Acris0 l) ∣ w ^ l := by
  intro l hl e he
  have step : ∀ m : ℕ, ∀ e : Per.Fl l, e.untilt = 1 →
      (((frobeniusEquiv (Per.Fl l) l).symm)^[m] e).untilt ≠ 1 →
      ∃ w : Per.Acris0 l, (l : Per.AinfP l) * (w : Per.AinfP l) =
        algebraMap (Per.Ainf l) (Per.AinfP l) (mu e) ^ (l - 1) ∧ (l : Per.Acris0 l) ∣ w ^ l := by
    intro m
    induction m with
    | zero => exact fun e h1 h2 => absurd h1 h2
    | succ m ih =>
      intro e h1 h2
      by_cases h : ((frobeniusEquiv (Per.Fl l) l).symm e).untilt = 1
      · obtain ⟨w, hw, hd⟩ := ih _ h h2
        have hmu : mu e = xi e * mu ((frobeniusEquiv (Per.Fl l) l).symm e) := by
          rw [xi, mu, mu, geom_sum_mul, tm_root_pow]
        refine ⟨algebraMap _ _ (xi e ^ (l - 1)) * w, ?_, ?_⟩
        · rw [hmu, map_mul, mul_pow, ← hw, ← map_pow, Subalgebra.coe_mul, Subalgebra.coe_algebraMap]
          ring
        · rw [mul_pow]
          exact hd.mul_left _
      · exact exists_mu_pow_div_of_isEps l e ⟨h1, h⟩
  by_cases h : ∃ m : ℕ, (((frobeniusEquiv (Per.Fl l) l).symm)^[m] e).untilt ≠ 1
  · obtain ⟨m, hm⟩ := h
    exact step m e he hm
  · push Not at h
    have h1 : e = 1 := by
      refine Perfection.ext fun n => ?_
      have h2 := PreTilt.mk_untilt_eq_coeff_zero (((frobeniusEquiv (Per.Fl l) l).symm)^[n] e)
      rw [h n, map_one, PreTilt.coeff_iterate_frobeniusEquiv_symm, zero_add] at h2
      exact h2.symm.trans (map_one (PreTilt.coeff (O := Per.OC l) (p := l) n)).symm
    have h0 : l - 1 ≠ 0 := by have := hl.out.two_le; omega
    refine ⟨0, ?_, by rw [zero_pow hl.out.ne_zero]; exact dvd_zero _⟩
    have hm : mu e = 0 := by
      rw [h1]
      exact sub_eq_zero.2 (map_one (WittVector.teichmuller l))
    rw [hm, map_zero, zero_pow h0]
    simp

end GlobalTheory.MemLoc
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.MemLoc.SecEx

theorem exists_lift {K L S C : Type} [Field K] [Field L] [Algebra K L] [Algebra.IsSeparable K L]
    [CommRing S] [CommRing C] (q : K →+* S) (T : S →+* C) (hT : Function.Surjective T) (I : Ideal S)
    (hI : I = RingHom.ker T) (f : L →+* C) (hf : ∀ k, f (algebraMap K L k) = T (q k)) :
    ∃ g : L →+* AdicCompletion I S,
      (∀ x, ∃ s, AdicCompletion.evalₐ I 1 (g x) = Ideal.Quotient.mk _ s ∧ T s = f x) ∧
      ∀ k, g (algebraMap K L k) = algebraMap S _ (q k) := by
  subst hI
  letI : Algebra K S := q.toAlgebra
  haveI : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
  let e := RingHom.quotientKerEquivOfSurjective hT
  have he : ∀ s, e (Ideal.Quotient.mk _ s) = T s := fun s => rfl
  let f' : L →ₐ[K] S ⧸ RingHom.ker T :=
    { (e.symm : C →+* S ⧸ RingHom.ker T).comp f with
      commutes' := fun k => by
        change e.symm (f (algebraMap K L k)) = Ideal.Quotient.mk _ (q k)
        rw [hf, ← he, RingEquiv.symm_apply_apply] }
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.exists_adicCompletionEvalOneₐ_comp_eq f'
  refine ⟨g.toRingHom, fun x => ?_, fun k => ?_⟩
  · obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (RingHom.ker T) 1 (g x))
    refine ⟨s, hs.symm, ?_⟩
    have h1 : AdicCompletion.evalOneₐ (RingHom.ker T) (g x) = e.symm (f x) := congr($hg x)
    rw [← AdicCompletion.factorₐ_evalₐ_one, ← hs] at h1
    rw [← he]
    exact (e.eq_symm_apply).1 h1
  · exact g.commutes k

variable (l : ℕ) [Fact l.Prime]

theorem ker_localizedTheta_eq_span_eisenstein : Per.kerP l = RingHom.ker (Per.θP l) := by
  ext a
  refine ⟨fun h => GlobalTheory.RingBasics.fontaineTheta_eq_zero_of_mem_ker l a (by rwa [pow_one]), fun h => ?_⟩
  obtain ⟨⟨x, s⟩, hx⟩ := IsLocalization.surj (Submonoid.powers ((l : ℕ) : Per.Ainf l)) a
  have h0 : Per.θP l a = 0 := h
  have h1 := congrArg (Per.θP l) hx
  rw [map_mul, h0, zero_mul, GlobalTheory.RingIface.fontaineTheta_algebraMap] at h1
  have h2 : Per.θ l x = 0 := Subtype.ext h1.symm
  have h3 := GlobalTheory.RingIface.alg_mem_kerP l h2
  rw [← hx] at h3
  exact (Ideal.mul_unit_mem_iff_mem _ (IsLocalization.map_units (Per.AinfP l) s)).1 h3

theorem fontaineTheta_algebraMap₂ (a : Per.Ainf l) : Per.θP l (algebraMap _ _ a) = (Per.θ l a : ℂ_[l]) :=
  GlobalTheory.RingIface.fontaineTheta_algebraMap l a

theorem θ_surjective : Function.Surjective (Per.θ l) := by
  refine surjective_fontaineTheta fun x => ?_
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (y : ℂ_[l]) (Fact.out : l.Prime).pos
  have hz1 : ‖z‖ ≤ 1 := by
    have := (GlobalTheory.RingBasics.mem_OC _).1 y.2
    rw [← hz, norm_pow] at this
    exact (pow_le_one_iff_of_nonneg (norm_nonneg _) (Fact.out : l.Prime).ne_zero).1 this
  refine ⟨Ideal.Quotient.mk _ ⟨z, (GlobalTheory.RingBasics.mem_OC _).2 hz1⟩, ?_⟩
  rw [frobenius_def]
  exact (map_pow (Ideal.Quotient.mk _) _ _).symm.trans (congrArg _ (Subtype.ext hz))

theorem fontaineTheta_surjective : Function.Surjective (Per.θP l) := by
  intro c
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ‖(l : ℂ_[l])‖ ^ n * ‖c‖ ≤ 1 := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (GlobalTheory.RingBasics.norm_p_lt (p := l))).mul_const ‖c‖
    rw [zero_mul] at h
    exact (h.eventually (ge_mem_nhds one_pos)).exists
  obtain ⟨a, ha⟩ := θ_surjective l ⟨(l : ℂ_[l]) ^ n * c, (GlobalTheory.RingBasics.mem_OC _).2 (by rwa [norm_mul, norm_pow])⟩
  obtain ⟨u, hu⟩ := (GlobalTheory.RingBasics.isUnit_l l).exists_right_inv
  have h1 := congrArg (Per.θP l) hu
  rw [map_mul, map_natCast, map_one] at h1
  refine ⟨u ^ n * algebraMap _ _ a, ?_⟩
  rw [map_mul, map_pow, fontaineTheta_algebraMap₂, ha]
  change Per.θP l u ^ n * ((l : ℂ_[l]) ^ n * c) = c
  rw [← mul_assoc, ← mul_pow, mul_comm _ (l : ℂ_[l]), h1, one_pow, one_mul]

theorem θ_zA (z : ℤ_[l]) :
    (Per.θ l (Per.zA l z) : ℂ_[l]) = ((algebraMap ℚ_[l] (Om l) (z : ℚ_[l]) : Om l) : ℂ_[l]) := by
  let F : ℤ_[l] →+* ℂ_[l] := (algebraMap (Per.OC l) ℂ_[l]).comp ((Per.θ l).comp (Per.zA l))
  let G : ℤ_[l] →+* ℂ_[l] :=
    (algebraMap (Om l) ℂ_[l]).comp ((algebraMap ℚ_[l] (Om l)).comp (algebraMap ℤ_[l] ℚ_[l]))
  have hF : ∀ w, ‖F w‖ ≤ 1 := fun w => (GlobalTheory.RingBasics.mem_OC _).1 (Per.θ l (Per.zA l w)).2
  have hG : ∀ w, ‖G w‖ ≤ 1 := fun w => by
    change ‖((algebraMap ℚ_[l] (Om l) (w : ℚ_[l]) : Om l) : ℂ_[l])‖ ≤ 1
    rw [PadicComplex.norm_extends, PadicAlgCl.norm_extends]
    exact w.2
  change F z = G z
  have hb : ∀ n : ℕ, ‖F z - G z‖ ≤ ‖(l : ℂ_[l])‖ ^ n * 2 := fun n => by
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n z)
    have hz : z = (z.appr n : ℤ_[l]) + (l : ℤ_[l]) ^ n * w := by rw [mul_comm, hw]; ring
    have : F z - G z = (l : ℂ_[l]) ^ n * (F w - G w) := by
      rw [hz]
      simp only [map_add (f := _), map_mul, map_pow, map_natCast]
      ring
    rw [this, norm_mul, norm_pow]
    refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans ?_) (by positivity)
    linarith [hF w, hG w]
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (GlobalTheory.RingBasics.norm_p_lt (p := l))).mul_const 2
  rw [zero_mul] at h
  exact sub_eq_zero.1 (norm_le_zero_iff.1 (ge_of_tendsto' h hb))

theorem isUnit_padicIntMap (y : nonZeroDivisors ℤ_[l]) : IsUnit (Per.zP l y) := by
  have h0 : (y : ℤ_[l]) ≠ 0 := nonZeroDivisors.ne_zero y.2
  have h1 := congrArg (Per.zP l) (PadicInt.unitCoeff_spec h0)
  rw [map_mul, map_pow, map_natCast] at h1
  rw [h1]
  exact ((PadicInt.unitCoeff h0).isUnit.map _).mul ((GlobalTheory.RingBasics.isUnit_l l).pow _)

def qP : ℚ_[l] →+* Per.AinfP l := IsLocalization.lift (isUnit_padicIntMap l)

theorem qP_coe (z : ℤ_[l]) : qP l (z : ℚ_[l]) = Per.zP l z := IsLocalization.lift_eq (isUnit_padicIntMap l) z

theorem algebraMap_eq_fontaineTheta_padicMap (k : ℚ_[l]) :
    algebraMap (Om l) ℂ_[l] (algebraMap ℚ_[l] (Om l) k) = Per.θP l (qP l k) := by
  refine RingHom.congr_fun (IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[l])
    (j := (algebraMap (Om l) ℂ_[l]).comp (algebraMap ℚ_[l] (Om l)))
    (k := (Per.θP l).comp (qP l)) (RingHom.ext fun z => ?_)) k
  change algebraMap (Om l) ℂ_[l] (algebraMap ℚ_[l] (Om l) (z : ℚ_[l])) = Per.θP l (qP l (z : ℚ_[l]))
  rw [qP_coe, GlobalTheory.RingIface.padicIntMap_eq_algebraMap_comp]
  exact ((fontaineTheta_algebraMap₂ l _).trans (θ_zA l z)).symm

theorem exists_isSec (l : ℕ) [Fact l.Prime] : ∃ o : Om l →+* Per.BdRp l, IsSec o := by
  obtain ⟨g, h1, h2⟩ := exists_lift (qP l) (Per.θP l) (fontaineTheta_surjective l) (Per.kerP l) (ker_localizedTheta_eq_span_eisenstein l)
    (algebraMap (Om l) ℂ_[l]) (algebraMap_eq_fontaineTheta_padicMap l)
  obtain ⟨e, he1, he2⟩ := GlobalTheory.RingIface.exists_bdRp_equiv l
  refine ⟨(e.symm : _ →+* Per.BdRp l).comp g, fun x => ?_, fun z => ?_⟩
  · obtain ⟨s, hs, hs'⟩ := h1 x
    have h3 : Per.ev l 1 (e.symm (g x)) = Ideal.Quotient.mk _ s := by
      rw [← he2, RingEquiv.apply_symm_apply, hs]
    have h4 : e.symm (g x) - algebraMap (Per.AinfP l) (Per.BdRp l) s ∈ Per.FilP l 1 := by
      rw [GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow, map_sub, h3, GlobalTheory.RingIface.ev_alg, sub_self]
    have h5 := GlobalTheory.RingIface.thetaD_of_mem_FilP l h4
    rw [map_sub, GlobalTheory.RingIface.thetaD_alg, sub_eq_zero] at h5
    exact h5.trans hs'
  · have h3 : e.symm (g (algebraMap ℚ_[l] (Om l) (z : ℚ_[l]))) =
        algebraMap (Per.AinfP l) (Per.BdRp l) (algebraMap (Per.Ainf l) (Per.AinfP l) (Per.zA l z)) := by
      rw [h2, qP_coe, GlobalTheory.RingIface.padicIntMap_eq_algebraMap_comp, ← he1, RingEquiv.symm_apply_apply]
    exact h3

end GlobalTheory.MemLoc.SecEx
end
end

section

open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

namespace GlobalTheory.AlgWtHW

theorem evM_change_of_basis : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : AlgWt L n) (ι : Type) [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ a.W) (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ) (ι' : Type) [Fintype ι'] [DecidableEq ι'] (b' : Module.Basis ι' ℂ a.W) (P' : ι' → ι' → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ), Agrees a b P → Agrees a b' P' → ∀ (τ : L →+* ℂ) (B : GL (Fin n) ℂ), evM P' (evPt τ B) = b'.toMatrix b * evM P (evPt τ B) * b.toMatrix b' := by
  intro L _ _ _ n a ι _ _ b P ι' _ _ b' P' hP hP' τ B

  have key : ∀ x, evM P' x - b'.toMatrix b * evM P x * b.toMatrix b' =
      Matrix.of fun i j => MvPolynomial.eval x (P' i j - ∑ k, ∑ l,
        MvPolynomial.C (b'.toMatrix b i k) * P k l * MvPolynomial.C (b.toMatrix b' l j)) := by
    intro x
    ext i j

    simp only [evM, Matrix.sub_apply, Matrix.mul_apply, Matrix.of_apply, map_sub, map_sum, map_mul, MvPolynomial.eval_C, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hrat : ∀ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n →
      evM P' (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) =
        b'.toMatrix b * evM P (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) * b.toMatrix b' := by
    intro γ₀ h
    obtain ⟨γ, hγ⟩ := exists_gq γ₀ h
    have e1 := hP γ γ₀ hγ
    have e2 := hP' γ γ₀ hγ
    have e3 := (basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix (b := b') (c := b') (b' := b) (c' := b) (f := a.ρ γ)).symm
    have f1 : evM P (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) = LinearMap.toMatrix b b (a.ρ γ) := by
      rw [e1]; rfl
    have f2 : evM P' (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) = LinearMap.toMatrix b' b' (a.ρ γ) := by
      rw [e2]; rfl
    rw [f1, f2, e3]
  have hz : ∀ i j, MvPolynomial.eval (evPt τ B) (P' i j - ∑ k, ∑ l,
        MvPolynomial.C (b'.toMatrix b i k) * P k l * MvPolynomial.C (b.toMatrix b' l j)) = 0 := by
    intro i j
    rw [evPt_eq_upt]
    refine GlobalTheory.T.eval_unitaryCoordinate_zero_of_rational_points L n _ ?_ (tauPt τ B) (isUPt_tauPt τ B)
    intro γ₀ h
    have := congrArg (fun M => M i j) (key (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))))
    simp only [hrat γ₀ h, sub_self] at this
    simpa using this.symm
  rw [← sub_eq_zero, key]
  ext i j
  simpa using hz i j

end GlobalTheory.AlgWtHW
end

section

open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

theorem _root_.GlobalTheory.T.exists_borelEigenvector_of_polynomialRepGLComplex : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ), IsPolyRep Φ → ∃ (v : ι → ℂ) (lam : Fin n → ℤ), IsBEig Φ v lam := by
  first | exact @GlobalTheory.AlgWtHW.exists_isBEig_of_isPolyRep | exact GlobalTheory.AlgWtHW.exists_isBEig_of_isPolyRep | (intros; apply GlobalTheory.AlgWtHW.exists_isBEig_of_isPolyRep <;> assumption)
end
