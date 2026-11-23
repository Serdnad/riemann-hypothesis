module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.WittVector.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle066
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle510
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle523
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle136
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfinitelyManyPrimesInRayClass
public import Mathlib.RingTheory.PicardGroup
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BijectiveOfRetract
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle524
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
public import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.Domain
public import Mathlib.RingTheory.WittVector.Teichmuller
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory

theorem wittVector_exists_eq_pow_add_natCast_mul (l : ℕ) [Fact l.Prime] (k : Type) [CommRing k]
    [CharP k l] [PerfectRing k l] (w : WittVector l k) :
    ∃ a b : WittVector l k, w = a ^ l + (l : WittVector l k) * b := by

  obtain ⟨c, hc⟩ : ∃ c : k, c ^ l = w.coeff 0 := ⟨_, frobeniusEquiv_symm_pow_p k l _⟩
  set a : WittVector l k := WittVector.teichmuller l c with ha

  have h0 : ∀ i < 1, (w - a ^ l).coeff i = 0 := by
    intro i hi
    obtain rfl : i = 0 := Nat.lt_one_iff.mp hi
    change WittVector.constantCoeff (w - a ^ l) = 0
    rw [map_sub, map_pow]
    change w.coeff 0 - (WittVector.teichmuller l c).coeff 0 ^ l = 0
    rw [WittVector.teichmuller_coeff_zero, hc, sub_self]
  have hV : w - a ^ l = WittVector.verschiebung ((w - a ^ l).shift 1) :=
    WittVector.eq_iterate_verschiebung h0

  set y := (w - a ^ l).shift 1 with hy
  set b := (WittVector.frobeniusEquiv l k).symm y with hb
  have hFb : WittVector.frobenius b = y := (WittVector.frobeniusEquiv l k).apply_symm_apply y
  refine ⟨a, b, ?_⟩
  have hVb : WittVector.verschiebung y = b * (l : WittVector l k) := by
    rw [← hFb, WittVector.verschiebung_frobenius]
  calc w = (w - a ^ l) + a ^ l := by ring
    _ = b * (l : WittVector l k) + a ^ l := by rw [hV, hVb]
    _ = a ^ l + (l : WittVector l k) * b := by ring

theorem wittVector_ringHom_eq_of_sub_mem : ∀ (l : ℕ) [Fact l.Prime] (k : Type) [CommRing k] [CharP k l] [PerfectRing k l] (C : Type) [CommRing C] (J : Ideal C), (l : C) ∈ J → IsHausdorff J C → ∀ ω ω' : WittVector l k →+* C, (∀ w, ω w - ω' w ∈ J) → ω = ω' := by
  intro l _ k _ _ _ C _ J hl hJ ω ω' h

  have key : ∀ n : ℕ, ∀ w, ω w - ω' w ∈ J ^ (n + 1) := by
    intro n
    induction n with
    | zero => intro w; simpa using h w
    | succ n ih =>
      intro w
      obtain ⟨a, b, rfl⟩ := wittVector_exists_eq_pow_add_natCast_mul l k w
      obtain ⟨d, hdJ, hda⟩ : ∃ d, d ∈ J ^ (n + 1) ∧ ω a = ω' a + d := ⟨_, ih a, by ring⟩
      obtain ⟨r, hr⟩ := exists_add_pow_prime_eq (Fact.out : l.Prime) (ω' a) d
      have e : ω (a ^ l + (l : WittVector l k) * b) - ω' (a ^ l + (l : WittVector l k) * b) =
          d ^ l + (l : C) * (ω' a * d * r) + (l : C) * (ω b - ω' b) := by
        simp only [map_add (f := _), map_mul, map_pow, map_natCast]
        rw [hda, hr]
        ring
      rw [e]
      have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
      refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_
      ·
        have hpow : d ^ l ∈ J ^ ((n + 1) * l) := by
          rw [pow_mul]
          exact Ideal.pow_mem_pow hdJ l
        exact Ideal.pow_le_pow_right (by nlinarith) hpow
      · rw [pow_succ']
        exact Ideal.mul_mem_mul hl (Ideal.mul_mem_right r _ (Ideal.mul_mem_left _ (ω' a) hdJ))
      · rw [pow_succ']
        exact Ideal.mul_mem_mul hl (ih b)

  refine RingHom.ext fun w => ?_
  rw [← sub_eq_zero]
  refine hJ.haus _ fun n => ?_
  rw [SModEq.zero]
  have hn : ω w - ω' w ∈ J ^ n := by
    cases n with
    | zero => simp
    | succ n => exact key n w
  simpa using Submodule.smul_mem_smul hn (Submodule.mem_top : (1 : C) ∈ ⊤)

end GlobalTheory
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.WittLift

variable (l : ℕ) [hl : Fact l.Prime] {C : Type} [CommRing C] (J : Ideal C)

theorem ghost_eq (n : ℕ) (x : _root_.WittVector l C) :
    _root_.WittVector.ghostComponent n x =
      ∑ i ∈ Finset.range (n + 1), (l : C) ^ i * x.coeff i ^ l ^ (n - i) := by
  rw [_root_.WittVector.ghostComponent_apply, aeval_wittPolynomial]

theorem ghost_mem_pow (hlJ : (l : C) ∈ J) (n : ℕ) (x : _root_.WittVector l C)
    (hx : ∀ i, x.coeff i ∈ J) : _root_.WittVector.ghostComponent n x ∈ J ^ n := by
  rw [ghost_eq]
  refine Ideal.sum_mem _ fun i _ => ?_
  have h1 : (l : C) ^ i ∈ J ^ i := Ideal.pow_mem_pow hlJ i
  have h2 : x.coeff i ^ l ^ (n - i) ∈ J ^ (l ^ (n - i)) := Ideal.pow_mem_pow (hx i) _
  have h3 : (l : C) ^ i * x.coeff i ^ l ^ (n - i) ∈ J ^ (i + l ^ (n - i)) := by
    rw [pow_add]; exact Ideal.mul_mem_mul h1 h2
  refine Ideal.pow_le_pow_right ?_ h3
  have : n - i < l ^ (n - i) := Nat.lt_pow_self hl.out.one_lt
  omega

def liftW (y : _root_.WittVector l (C ⧸ J)) : _root_.WittVector l C :=
  _root_.WittVector.mk l (fun i => Function.surjInv Ideal.Quotient.mk_surjective (y.coeff i))

theorem map_liftW (y : _root_.WittVector l (C ⧸ J)) :
    _root_.WittVector.map (Ideal.Quotient.mk J) (liftW l J y) = y := by
  ext i
  rw [_root_.WittVector.map_coeff]
  simp only [liftW, _root_.WittVector.coeff_mk]
  exact Function.surjInv_eq Ideal.Quotient.mk_surjective _

def gh (hlJ : (l : C) ∈ J) (n : ℕ) : _root_.WittVector l (C ⧸ J) →+* C ⧸ J ^ n :=
  RingHom.liftOfRightInverse (_root_.WittVector.map (Ideal.Quotient.mk J)) (liftW l J) (map_liftW l J)
    ⟨(Ideal.Quotient.mk (J ^ n)).comp (_root_.WittVector.ghostComponent n), fun x hx => by
      rw [RingHom.mem_ker] at hx ⊢
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      refine ghost_mem_pow l J hlJ n x fun i => ?_
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← _root_.WittVector.map_coeff, hx,
        _root_.WittVector.zero_coeff]⟩

theorem gh_map (hlJ : (l : C) ∈ J) (n : ℕ) (x : _root_.WittVector l C) :
    gh l J hlJ n (_root_.WittVector.map (Ideal.Quotient.mk J) x) =
      Ideal.Quotient.mk (J ^ n) (_root_.WittVector.ghostComponent n x) :=
  RingHom.liftOfRightInverse_comp_apply _ _ _ _ x

end GlobalTheory.WittLift

namespace GlobalTheory.WittLift

variable (l : ℕ) [hl : Fact l.Prime] {C : Type} [CommRing C] (J : Ideal C)
variable (k : Type) [CommRing k] [CharP k l] [PerfectRing k l]

theorem symm_iter_pow (n : ℕ) (x : k) :
    (iterateFrobeniusEquiv k l (n + 1)).symm x ^ l = (iterateFrobeniusEquiv k l n).symm x := by
  apply (iterateFrobeniusEquiv k l n).injective
  rw [RingEquiv.apply_symm_apply, iterateFrobeniusEquiv_def, ← pow_mul, ← pow_succ',
    ← iterateFrobeniusEquiv_def k l (n + 1), RingEquiv.apply_symm_apply]

theorem symm_iter_zero (x : k) : (iterateFrobeniusEquiv k l 0).symm x = x := by
  apply (iterateFrobeniusEquiv k l 0).injective
  rw [RingEquiv.apply_symm_apply, iterateFrobeniusEquiv_zero_apply]

variable {k} (ψ : k →+* C ⧸ J)

def wn (n : ℕ) : _root_.WittVector l k →+* _root_.WittVector l (C ⧸ J) :=
  _root_.WittVector.map (ψ.comp (iterateFrobeniusEquiv k l n).symm.toRingHom)

def yh (n : ℕ) (w : _root_.WittVector l k) : _root_.WittVector l C := liftW l J (wn l J ψ n w)

theorem mk_yh_coeff (n : ℕ) (w : _root_.WittVector l k) (i : ℕ) :
    Ideal.Quotient.mk J ((yh l J ψ n w).coeff i) = ψ ((iterateFrobeniusEquiv k l n).symm (w.coeff i)) := by
  rw [← _root_.WittVector.map_coeff, yh, map_liftW, wn, _root_.WittVector.map_coeff]
  rfl

def fn (hlJ : (l : C) ∈ J) (n : ℕ) : _root_.WittVector l k →+* C ⧸ J ^ n :=
  (gh l J hlJ n).comp (wn l J ψ n)

theorem fn_apply (hlJ : (l : C) ∈ J) (n : ℕ) (w : _root_.WittVector l k) :
    fn l J ψ hlJ n w = Ideal.Quotient.mk (J ^ n) (_root_.WittVector.ghostComponent n (yh l J ψ n w)) := by
  rw [fn, RingHom.comp_apply, ← gh_map l J hlJ n, yh, map_liftW]

theorem step (hlJ : (l : C) ∈ J) (n : ℕ) (w : _root_.WittVector l k) :
    _root_.WittVector.ghostComponent (n + 1) (yh l J ψ (n + 1) w) -
      _root_.WittVector.ghostComponent n (yh l J ψ n w) ∈ J ^ n := by
  set y := yh l J ψ (n + 1) w with hy
  let z : _root_.WittVector l C := _root_.WittVector.mk l (fun i => y.coeff i ^ l)
  have hz : _root_.WittVector.map (Ideal.Quotient.mk J) z = wn l J ψ n w := by
    ext i
    rw [_root_.WittVector.map_coeff, _root_.WittVector.coeff_mk, map_pow, hy, mk_yh_coeff, ← map_pow,
      symm_iter_pow, wn, _root_.WittVector.map_coeff]
    rfl
  have h1 : _root_.WittVector.ghostComponent n (yh l J ψ n w) - _root_.WittVector.ghostComponent n z ∈ J ^ n := by
    rw [← Ideal.Quotient.eq, ← fn_apply, ← gh_map l J hlJ, hz, fn, RingHom.comp_apply]
  have h2 : _root_.WittVector.ghostComponent (n + 1) y - _root_.WittVector.ghostComponent n z =
      (l : C) ^ (n + 1) * y.coeff (n + 1) := by
    have ha : _root_.WittVector.ghostComponent (n + 1) y =
        (∑ i ∈ Finset.range (n + 1), (l : C) ^ i * y.coeff i ^ l ^ (n + 1 - i)) +
          (l : C) ^ (n + 1) * y.coeff (n + 1) := by
      rw [ghost_eq, Finset.sum_range_succ, Nat.sub_self, pow_zero, pow_one]
    have hb : _root_.WittVector.ghostComponent n z =
        ∑ i ∈ Finset.range (n + 1), (l : C) ^ i * y.coeff i ^ l ^ (n + 1 - i) := by
      rw [ghost_eq]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' := Finset.mem_range.mp hi
      simp only [z, _root_.WittVector.coeff_mk]
      rw [← pow_mul, ← pow_succ']
      congr 3
      omega
    rw [ha, hb]; ring
  have h3 : (l : C) ^ (n + 1) * y.coeff (n + 1) ∈ J ^ n :=
    Ideal.pow_le_pow_right (Nat.le_succ n) (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hlJ _))
  rw [← h2] at h3
  have := Ideal.sub_mem _ h3 h1
  convert this using 1
  abel

theorem compat (hlJ : (l : C) ∈ J) (w : _root_.WittVector l k) {m n : ℕ} (hle : m ≤ n) :
    _root_.WittVector.ghostComponent n (yh l J ψ n w) -
      _root_.WittVector.ghostComponent m (yh l J ψ m w) ∈ J ^ m := by
  induction n, hle using Nat.le_induction with
  | base => rw [sub_self]; exact Ideal.zero_mem _
  | succ n hmn ih =>
    have := Ideal.add_mem _ (Ideal.pow_le_pow_right hmn (step l J ψ hlJ n w)) ih
    convert this using 1
    abel

end GlobalTheory.WittLift

namespace GlobalTheory.WittLift

variable (l : ℕ) [hl : Fact l.Prime] {C : Type} [CommRing C] (J : Ideal C)
variable {k : Type} [CommRing k] [CharP k l] [PerfectRing k l] (ψ : k →+* C ⧸ J)

theorem fn_compat (hlJ : (l : C) ∈ J) {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow J hle).comp (fn l J ψ hlJ n) = fn l J ψ hlJ m := by
  refine RingHom.ext fun w => ?_
  rw [RingHom.comp_apply, fn_apply, fn_apply, Ideal.Quotient.factor_mk, Ideal.Quotient.eq]
  exact compat l J ψ hlJ w hle

end GlobalTheory.WittLift

namespace GlobalTheory

theorem exists_wittVector_lift_of_isAdicComplete :
    ∀ (l : ℕ) [Fact l.Prime] (k : Type) [CommRing k] [CharP k l] [PerfectRing k l] (C : Type) [CommRing C]
      (J : Ideal C), (l : C) ∈ J → IsAdicComplete J C → ∀ ψ : k →+* C ⧸ J,
      ∃ ω : WittVector l k →+* C, ∀ w, Ideal.Quotient.mk J (ω w) = ψ (w.coeff 0) := by
  intro l _ k _ _ _ C _ J hlJ hC ψ
  haveI := hC
  refine ⟨IsAdicComplete.liftRingHom J (WittLift.fn l J ψ hlJ) (WittLift.fn_compat l J ψ hlJ), fun w => ?_⟩
  have h0 : Ideal.Quotient.mk (J ^ 1)
      (IsAdicComplete.liftRingHom J (WittLift.fn l J ψ hlJ) (WittLift.fn_compat l J ψ hlJ) w) =
      Ideal.Quotient.mk (J ^ 1) (_root_.WittVector.ghostComponent 1 (WittLift.yh l J ψ 1 w)) := by
    rw [IsAdicComplete.mk_liftRingHom, WittLift.fn_apply]
  have h1 := Ideal.Quotient.eq.mp h0
  rw [pow_one] at h1
  rw [Ideal.Quotient.eq.mpr h1, WittLift.ghost_eq, Finset.sum_range_succ, Finset.sum_range_one]
  simp only [pow_zero, one_mul, Nat.sub_zero, pow_one, Nat.sub_self, map_add (f := _), map_mul, map_pow]
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hlJ, zero_mul, add_zero, WittLift.mk_yh_coeff, ← map_pow,
    WittLift.symm_iter_pow, WittLift.symm_iter_zero]

end GlobalTheory
end
end

section

open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical

namespace GlobalTheory.CyclotomicPrimes

theorem summable_subset_union_finite {ι : Type} (f : ι → ℝ) (A B C : Set ι) (hB : B.Finite) (h : C ⊆ A ∪ B)
    (hA : Summable fun x : A => f x) : Summable fun x : C => f x := by
  have h1 : Summable (f ∘ ((↑) : ↥(A ∪ B) → ι)) := by
    rw [← Set.union_sdiff_self]
    exact (HasSum.add_disjoint Set.disjoint_sdiff_right hA.hasSum ((hB.subset Set.sdiff_subset).summable f).hasSum).summable
  exact h1.comp_injective (i := Set.inclusion h) (Set.inclusion_injective h)

theorem exists_prime_absNorm_eq_of_irreducible_cyclotomic : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ), m.Prime → Irreducible (cyclotomic m K) → ∀ (τ : (ZMod m)ˣ) (S : Set (HeightOneSpectrum (𝓞 K))), S.Finite → ∃ P : HeightOneSpectrum (𝓞 K), P ∉ S ∧ (Ideal.absNorm P.asIdeal).Prime ∧ ((Ideal.absNorm P.asIdeal : ℕ) : ZMod m) = (τ : ZMod m) := by
  classical
  intro K _ _ m hm hirr τ S hS
  have : Fact m.Prime := ⟨hm⟩
  let cl : HeightOneSpectrum (𝓞 K) → (ZMod m)ˣ := fun P =>
    if h : ((Ideal.absNorm P.asIdeal : ℕ) : ZMod m) = 0 then 1 else Units.mk0 _ h
  have hcl : ∀ P, ¬ m ∣ Ideal.absNorm P.asIdeal → (cl P : ZMod m) = (Ideal.absNorm P.asIdeal : ℕ) := by
    intro P hP
    simp only [cl]
    rw [dite_eq_right (by rwa [ZMod.natCast_eq_zero_iff])]
    rfl
  by_contra hcon
  push Not at hcon
  obtain ⟨Z, hZ, hZ1, hZs⟩ := GlobalTheory.T.exists_entire_sub_one_mul_euler_exp_ne_zero_one K
  refine GlobalTheory.Mem.RayPrimes.not_summable_class (fun P : HeightOneSpectrum (𝓞 K) => Ideal.absNorm P.asIdeal)
    GlobalTheory.Mem.RayPrimes.two_le_absNorm cl
    (fun s hs => ((GlobalTheory.countable_ideal_and_summable_absNorm_rpow K).2 s hs).2) ?_ Z hZ.continuous hZ1 ?_ τ ?_
  · intro χ hχ
    obtain ⟨P, u, hu, hχu⟩ := GlobalTheory.T.exists_prime_norm_cyclotomicChar_ne_one K m hm hirr χ hχ
    have hP : ¬ m ∣ Ideal.absNorm P.asIdeal := by
      rw [← ZMod.natCast_eq_zero_iff, ← hu]; exact u.ne_zero
    refine GlobalTheory.T.exists_continuous_normCharLFunction_ne_zero_one K m hm χ cl hcl ⟨P, hP, ?_⟩
    rwa [show cl P = u from Units.ext ((hcl P hP).trans hu.symm)]
  · intro s hs
    simpa using hZs s (by simpa using hs)
  · have hfin : (S ∪ {P : HeightOneSpectrum (𝓞 K) | Ideal.absNorm P.asIdeal ≤ m}).Finite :=
      hS.union ((Ring.HasFiniteQuotients.finite_absNorm_le (S := 𝓞 K) m).preimage
        (f := fun P : HeightOneSpectrum (𝓞 K) => P.asIdeal) (fun a _ b _ h => HeightOneSpectrum.ext h))
    refine summable_subset_union_finite (fun P : HeightOneSpectrum (𝓞 K) => ((Ideal.absNorm P.asIdeal : ℕ) : ℝ)⁻¹)
      {P | ¬ (Ideal.absNorm P.asIdeal).Prime} _ {P | cl P = τ} hfin ?_ (GlobalTheory.T.summable_inv_absNorm_primes_of_not_prime_norm K)
    intro P hP
    by_contra hn
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le, not_not] at hn hP
    have hd : ¬ m ∣ Ideal.absNorm P.asIdeal := fun h =>
      hn.2.2.ne ((Nat.prime_dvd_prime_iff_eq hm hn.1).1 h)
    exact hcon P hn.2.1 hn.1 (by rw [← hcl P hd, hP])

end GlobalTheory.CyclotomicPrimes
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory

theorem ideal_dual_symm {A : Type} [CommRing A] (I : Ideal A) (f : Module.Dual A ↥I)
    (x y : ↥I) : f x * (y : A) = f y * (x : A) := by
  have h : (x : A) • y = (y : A) • x := Subtype.ext (by simp [mul_comm])
  have := congrArg f h
  simp only [map_smul, smul_eq_mul] at this
  rw [mul_comm (f x), ← this, mul_comm]

theorem invertible_ideal_eq_of_not_le_maximal_mul (A : Type) [CommRing A] (I N : Ideal A) :
    Module.Invertible A ↥I → N ≤ I → (∀ m : Ideal A, m.IsMaximal → ¬ N ≤ m * I) → N = I := by
  intro hI hNI hm

  set c : Ideal A := N.colon I with hc
  have key : ∀ (f : Module.Dual A ↥I) (n : ↥I), (n : A) ∈ N → f n ∈ c := by
    intro f n hn
    rw [hc, Submodule.mem_colon]
    intro p hp
    rw [smul_eq_mul, ideal_dual_symm I f n ⟨p, hp⟩]
    exact N.mul_mem_left _ hn
  have hcTop : c = ⊤ := by
    by_contra hne
    obtain ⟨m, hmax, hcm⟩ := Ideal.exists_le_maximal c hne
    apply hm m hmax
    intro n hn
    obtain ⟨t, ht⟩ := hI.bijective.2 1
    have hall : ∀ t : Module.Dual A ↥I ⊗[A] ↥I, contractLeft A ↥I t * n ∈ m * I := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul f x =>
        rw [contractLeft_apply, ideal_dual_symm I f x ⟨n, hNI hn⟩]
        exact Ideal.mul_mem_mul (hcm (key f ⟨n, hNI hn⟩ hn)) x.2
      | add s u hs hu => rw [map_add (f := _), add_mul]; exact Ideal.add_mem _ hs hu
    simpa [ht] using hall t
  apply le_antisymm hNI
  intro y hy
  have h1 : (1 : A) ∈ c := hcTop ▸ Submodule.mem_top
  rw [hc, Submodule.mem_colon] at h1
  simpa using h1 y hy

end GlobalTheory
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.ZarPrincipal

theorem form_mul_comm {A : Type} [CommRing A] (I : Ideal A) (f : Module.Dual A ↥I)
    (y x : ↥I) : f y * (x : A) = f x * (y : A) := by
  have h : (x : A) • y = (y : A) • x := by
    ext; simp [mul_comm]
  have := congrArg f h
  simp only [map_smul, smul_eq_mul] at this
  rw [mul_comm, this, mul_comm]

theorem one_mem_span_values {A : Type} [CommRing A] (I : Ideal A) [Module.Invertible A ↥I] :
    (1 : A) ∈ Ideal.span {a | ∃ (f : Module.Dual A ↥I) (y : ↥I), f y = a} := by
  obtain ⟨t, ht⟩ := (Module.Invertible.bijective (R := A) (M := ↥I)).2 1
  rw [← ht]
  clear ht
  induction t with
  | tmul f y => exact Ideal.subset_span ⟨f, y, by simp [contractLeft_apply]⟩
  | add a b ha hb => rw [map_add (f := _)]; exact Ideal.add_mem _ ha hb

end GlobalTheory.BSP.ZarPrincipal


open GlobalTheory.BSP.ZarPrincipal in
theorem GlobalTheory.BSP.invertible_ideal_principal_on_cover :
    ∀ (A : Type) [CommRing A] (I : Ideal A), Module.Invertible A ↥I → ∃ (n : ℕ) (s t : Fin n → A),
      Ideal.span (Set.range s) = ⊤ ∧ ∀ i, t i ∈ I ∧ ∀ x ∈ I, ∃ c, s i * x = c * t i := by
  intro A _ I hI
  set S : Set A := {a | ∃ (f : Module.Dual A ↥I) (y : ↥I), f y = a} with hS
  have h1 : (1 : A) ∈ Ideal.span S := one_mem_span_values I
  obtain ⟨T, hTS, hT⟩ := Submodule.mem_span_finite_of_mem_span h1
  have hmem : ∀ a : T, ∃ (f : Module.Dual A ↥I) (y : ↥I), f y = (a : A) := fun a => hTS a.2
  choose f y hfy using hmem
  let e := T.equivFin
  refine ⟨T.card, fun i => ((e.symm i : T) : A), fun i => (y (e.symm i) : A), ?_, ?_⟩
  · rw [Ideal.eq_top_iff_one]
    refine Submodule.span_mono ?_ hT
    intro a ha
    exact ⟨e ⟨a, ha⟩, by simp⟩
  · intro i
    refine ⟨(y (e.symm i)).2, fun x hx => ⟨f (e.symm i) ⟨x, hx⟩, ?_⟩⟩
    show ((e.symm i : T) : A) * x = _ * (y (e.symm i) : A)
    rw [← hfy (e.symm i)]
    exact form_mul_comm I (f (e.symm i)) (y (e.symm i)) ⟨x, hx⟩
end

section

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2

theorem _root_.GlobalTheory.T.every_generator_H2_twist : ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] {G : Type} [Group G] [TopologicalSpace G], Formalism.GaloisCohomology.LocalTateDualityK → FiniteDimensional ℚ_[p] K → PadicCoeff p O → ∀ (i : G ≃ₜ* GK p K) {ε : G →* Oˣ}, IsCyc p K (carry i ε) → ∀ z : H2 (twist ε O), Function.Bijective (fun a : O => a • z) → ∀ k : ℕ, Function.Bijective (phi ε z (O ⧸ IsLocalRing.maximalIdeal O ^ k)) := by
  first | exact @GlobalTheory.FunctorialityH2.bijective_phi_quot_pow | exact GlobalTheory.FunctorialityH2.bijective_phi_quot_pow | (intros; apply GlobalTheory.FunctorialityH2.bijective_phi_quot_pow <;> assumption)
end
