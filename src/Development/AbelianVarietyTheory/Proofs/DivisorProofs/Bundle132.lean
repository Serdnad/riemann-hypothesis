module

public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Smooth.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Mathlib.RingTheory.Smooth.IntegralClosure
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
import Std.Tactic.BVDecide.Normalize.BitVec
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.TensorProduct.Maps

@[expose] public section

section

universe u

namespace GlobalTheory

theorem eigenIdempotents_of_comaximal
    {C : Type} [CommRing C] {A : Type} [CommRing A] {W : Type u} [AddCommGroup W] [Module C W]
    (σ : A →+* Module.End C W) (a : ℕ) (χ : Fin a → A →+* C) :
    (∀ i j, i ≠ j → Ideal.span (Set.range fun x => χ i x - χ j x) = ⊤) →
    ∃ e : Fin a → Module.End C W,
      (∀ i (T : Module.End C W), (∀ c, T * σ c = σ c * T) → T * e i = e i * T) ∧
      (∀ i w, (∀ c, σ c w = χ i c • w) → e i w = w) ∧
      (∀ i j w, j ≠ i → (∀ c, σ c w = χ j c • w) → e i w = 0) := by
  classical
  intro hcom
  have hc : ∀ i j, ∃ c : A →₀ C, i ≠ j → (c.sum fun x r => r * (χ i x - χ j x)) = 1 := by
    intro i j
    by_cases h : i = j
    · exact ⟨0, fun h' => absurd h h'⟩
    · have h1 : (1 : C) ∈ Ideal.span (Set.range fun x => χ i x - χ j x) := by
        rw [hcom i j h]; trivial
      obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 h1
      exact ⟨c, fun _ => by simpa [smul_eq_mul] using hc⟩
  choose c hc using hc
  let Z : Fin a → Fin a → Module.End C W := fun i j =>
    (c i j).sum fun x r => r • (σ x - χ j x • (1 : Module.End C W))
  have hZ : ∀ i j k (w : W), (∀ x, σ x w = χ k x • w) →
      Z i j w = ((c i j).sum fun x r => r * (χ k x - χ j x)) • w := by
    intro i j k w hw
    simp only [Z, Finsupp.sum, LinearMap.sum_apply, Finset.sum_smul]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp [hw, sub_smul, mul_smul, smul_sub]
  have hZc : ∀ i j (T : Module.End C W), (∀ c, T * σ c = σ c * T) → Commute T (Z i j) := by
    intro i j T hT
    simp only [Z, Finsupp.sum]
    refine Commute.sum_right _ _ _ fun x _ => ?_
    exact ((show Commute T (σ x) from hT x).sub_right ((Commute.one_right T).smul_right _)).smul_right _
  have hlist : ∀ (i : Fin a) (s : Fin a → C) (w : W) (L : List (Fin a)),
      (∀ j ∈ L, Z i j w = s j • w) → (L.map (Z i)).prod w = (L.map s).prod • w := by
    intro i s w L hL
    induction L with
    | nil => simp
    | cons j L ih =>
      have ih' := ih (fun k hk => hL k (List.mem_cons_of_mem _ hk))
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, ih', map_smul,
        hL j List.mem_cons_self, smul_smul]
      rw [mul_comm]
  refine ⟨fun i => (((List.finRange a).filter (· ≠ i)).map (Z i)).prod, ?_, ?_, ?_⟩
  · intro i T hT
    exact (Commute.list_prod_right _ _ fun y hy => by
      obtain ⟨j, _, rfl⟩ := List.mem_map.1 hy
      exact hZc i j T hT).eq
  · intro i w hw
    rw [hlist i (fun j => (c i j).sum fun x r => r * (χ i x - χ j x)) w _
      (fun j _ => hZ i j i w hw)]
    rw [List.prod_eq_one, one_smul]
    intro y hy
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
    have hji : j ≠ i := by simpa using (List.mem_filter.1 hj).2
    exact hc i j (Ne.symm hji)
  · intro i j w hji hw
    rw [hlist i (fun k => (c i k).sum fun x r => r * (χ j x - χ k x)) w _
      (fun k _ => hZ i k j w hw)]
    rw [List.prod_eq_zero, zero_smul]
    refine List.mem_map.2 ⟨j, ?_, ?_⟩
    · exact List.mem_filter.2 ⟨List.mem_finRange j, by simpa using hji⟩
    · simp

end GlobalTheory
end

section

open scoped TensorProduct

namespace GlobalTheory

theorem eigenProjections_of_comaximal :
    ∀ (R F : Type) [CommRing R] [CommRing F] (a : ℕ) (t : Fin a → (F →+* R)),
      (∀ i j, i ≠ j → Ideal.span (Set.range fun x => t i x - t j x) = ⊤) →
      ∃ e : Fin a → R ⊗[ℤ] F, ∀ (M : Type) [AddCommGroup M] (Θ : R ⊗[ℤ] F →+* AddMonoid.End M)
        (i l : Fin a) (m : M), (∀ c : F, Θ (1 ⊗ₜ c) m = Θ (t l c ⊗ₜ 1) m) →
          Θ (e i) m = if i = l then m else 0 := by
  intro R F _ _ a t ht
  have hf : ∀ i j : Fin a, ∃ f : F →₀ R, i ≠ j → (f.sum fun c r => r * (t i c - t j c)) = 1 := by
    intro i j
    by_cases hij : i = j
    · exact ⟨0, fun h => (h hij).elim⟩
    · have h1 : (1 : R) ∈ Ideal.span (Set.range fun x => t i x - t j x) := by
        rw [ht i j hij]; trivial
      obtain ⟨f, hf⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 h1
      exact ⟨f, fun _ => by simpa [smul_eq_mul] using hf⟩
  choose f hf using hf
  let χ : Fin a → (R ⊗[ℤ] F →ₐ[ℤ] R) := fun l =>
    Algebra.TensorProduct.productMap (AlgHom.id ℤ R) (t l).toIntAlgHom
  have hχ : ∀ l r c, χ l (r ⊗ₜ c) = r * t l c := by
    intro l r c; simp [χ, Algebra.TensorProduct.productMap_apply_tmul]
  refine ⟨fun i => ∏ j, if j = i then 1 else
    (f i j).sum fun c r => (r ⊗ₜ (1:F)) * ((1:R) ⊗ₜ c - t j c ⊗ₜ (1:F)), ?_⟩
  intro M _ Θ i l m hm
  have key : ∀ z, Θ z m = Θ (χ l z ⊗ₜ (1:F)) m := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul r c =>
      have e1 : (r ⊗ₜ c : R ⊗[ℤ] F) = (r ⊗ₜ (1:F)) * ((1:R) ⊗ₜ c) := by
        simp [Algebra.TensorProduct.tmul_mul_tmul]
      have e2 : ((r * t l c) ⊗ₜ (1:F) : R ⊗[ℤ] F) = (r ⊗ₜ (1:F)) * (t l c ⊗ₜ (1:F)) := by
        simp [Algebra.TensorProduct.tmul_mul_tmul]
      rw [hχ, e1, e2, map_mul, map_mul]
      change Θ (r ⊗ₜ 1) (Θ (1 ⊗ₜ c) m) = Θ (r ⊗ₜ 1) (Θ (t l c ⊗ₜ 1) m)
      rw [hm c]
    | add x y hx hy =>
      rw [map_add (f := _), map_add (f := _), TensorProduct.add_tmul, map_add (f := _)]
      change Θ x m + Θ y m = Θ (χ l x ⊗ₜ 1) m + Θ (χ l y ⊗ₜ 1) m
      rw [hx, hy]
  rw [key, map_prod]
  split_ifs with hil
  · subst hil
    rw [Finset.prod_eq_one]
    · rw [← Algebra.TensorProduct.one_def, map_one]; rfl
    intro j _
    split_ifs with hji
    · exact map_one _
    · unfold Finsupp.sum

      rw [map_sum]
      have := hf i j (Ne.symm hji)
      unfold Finsupp.sum at this
      refine Eq.trans ?_ this
      apply Finset.sum_congr rfl
      intro c _
      rw [map_mul, map_sub, hχ, hχ, hχ]
      simp
  · rw [Finset.prod_eq_zero (Finset.mem_univ l)]
    · rw [TensorProduct.zero_tmul, map_zero]; rfl
    rw [if_neg (Ne.symm hil)]
    unfold Finsupp.sum

    rw [map_sum]
    apply Finset.sum_eq_zero
    intro c _
    rw [map_mul, map_sub, hχ, hχ, hχ]
    simp

end GlobalTheory
end

section

open IsLocalRing
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory

open Polynomial

theorem exists_mul_mul_eq_self_of_isArtinian_isReduced {A : Type} [CommRing A] [IsArtinianRing A]
    [IsReduced A] (a : A) : ∃ y : A, a * a * y = a := by
  obtain ⟨n, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd a (1 : A)
  simp only [smul_eq_mul, mul_one] at hy
  have hy' : a ^ (n + 1) * y = a ^ n := hy
  refine ⟨y, ?_⟩
  have hc : IsNilpotent (a - a * a * y) := ⟨n + 1, by
    calc (a - a * a * y) ^ (n + 1) = (a * (1 - a * y)) ^ (n + 1) := by ring
    _ = a ^ (n + 1) * (1 - a * y) ^ (n + 1) := mul_pow _ _ _
    _ = (a ^ (n + 1) - a * (a ^ (n + 1) * y)) * (1 - a * y) ^ n := by rw [pow_succ (1 - a * y)]; ring
    _ = 0 := by rw [hy', ← pow_succ', sub_self, zero_mul]⟩
  exact (sub_eq_zero.mp hc.eq_zero).symm

theorem idempotent_mul_aeval_mul {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {f : A}
    (hf : IsIdempotentElem f) (x : A) (p : R[X]) : f * aeval (f * x) p = f * aeval x p := by
  simp only [aeval_eq_sum_range, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_smul_comm, mul_smul_comm, mul_pow, ← mul_assoc, ← pow_succ', hf.pow_succ_eq]

theorem isIntegral_of_isIdempotentElem {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {e : A}
    (he : IsIdempotentElem e) : IsIntegral R e :=
  ⟨X * (X - C 1), monic_X.mul (monic_X_sub_C 1), by
    simp only [eval₂_mul, eval₂_X, eval₂_sub, eval₂_C, eval₂_one, map_one, mul_sub, mul_one,
      he.eq, sub_self]⟩

theorem localization_integralClosure_isDomain_isIntegrallyClosed
    (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [IsArtinianRing A] [IsReduced A]
    (Q : Ideal (integralClosure R A)) [Q.IsPrime] :
    IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q) := by
  classical
  have hidem : ∀ e : A, IsIdempotentElem e → e ∈ integralClosure R A := fun e he =>
    (show IsIntegral R e from isIntegral_of_isIdempotentElem he)
  have hcompl : ∀ e : integralClosure R A, e ∈ Q → (1 - e) ∈ Q.primeCompl := by
    intro e he h1
    exact (Ideal.IsPrime.ne_top inferInstance) ((Ideal.eq_top_iff_one _).mpr (by
      simpa using Q.add_mem he h1))
  let T : Submonoid A := Algebra.algebraMapSubmonoid A Q.primeCompl
  let J : Ideal A := RingHom.ker (algebraMap A (Localization T))
  have memJ : ∀ a : A, a ∈ J ↔ ∃ s ∈ Q.primeCompl, (s : A) * a = 0 := by
    intro a
    rw [RingHom.mem_ker, IsLocalization.map_eq_zero_iff T]
    constructor
    · rintro ⟨⟨m, hm⟩, hma⟩
      obtain ⟨s, hs, rfl⟩ := Submonoid.mem_map.mp hm
      exact ⟨s, hs, hma⟩
    · rintro ⟨s, hs, hsa⟩
      exact ⟨⟨(s : A), Submonoid.mem_map.mpr ⟨s, hs, rfl⟩⟩, hsa⟩
  have hS : ∀ s ∈ Q.primeCompl, (s : A) ∉ J := by
    intro s hs h
    obtain ⟨t, ht, hts⟩ := (memJ _).mp h
    have h0 : t * s = 0 := Subtype.ext (by simpa using hts)
    exact (Q.primeCompl.mul_mem ht hs) (h0 ▸ Q.zero_mem)
  have hJprime : J.IsPrime := by
    refine ⟨?_, ?_⟩
    · intro htop
      exact hS 1 Q.primeCompl.one_mem (by simp [htop])
    · intro a c hac
      obtain ⟨y, hy⟩ := exists_mul_mul_eq_self_of_isArtinian_isReduced a
      have hei : IsIdempotentElem (a * y) := by
        unfold IsIdempotentElem
        calc a * y * (a * y) = (a * a * y) * y := by ring
        _ = a * y := by rw [hy]
      let e : integralClosure R A := ⟨a * y, hidem _ hei⟩
      by_cases he : e ∈ Q
      · left
        refine (memJ a).mpr ⟨1 - e, hcompl e he, ?_⟩
        simp only [e, Subalgebra.coe_sub, OneMemClass.coe_one]
        linear_combination -hy
      · right
        obtain ⟨s, hs, hsac⟩ := (memJ _).mp hac
        refine (memJ c).mpr ⟨s * e, Q.primeCompl.mul_mem hs he, ?_⟩
        simp only [e, MulMemClass.coe_mul]
        linear_combination y * hsac
  haveI : J.IsPrime := hJprime
  haveI hJm : J.IsMaximal := IsArtinianRing.isMaximal_of_isPrime J
  letI : Field (A ⧸ J) := Ideal.Quotient.field J
  let g : integralClosure R A →+* A ⧸ J := algebraMap (integralClosure R A) (A ⧸ J)
  have g_eq : ∀ b, g b = Ideal.Quotient.mk J (b : A) := fun b => rfl
  have hunit : ∀ s : Q.primeCompl, IsUnit (g s) := by
    intro s
    rw [isUnit_iff_ne_zero, g_eq, Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact hS s.1 s.2
  have hB0 : ∀ b : integralClosure R A,
      algebraMap (integralClosure R A) (Localization.AtPrime Q) b = 0 ↔ g b = 0 := by
    intro b
    rw [IsLocalization.map_eq_zero_iff Q.primeCompl, g_eq, Ideal.Quotient.eq_zero_iff_mem, memJ]
    constructor
    · rintro ⟨⟨s, hs⟩, hsb⟩
      exact ⟨s, hs, by simpa using congrArg Subtype.val hsb⟩
    · rintro ⟨s, hs, hsb⟩
      exact ⟨⟨s, hs⟩, Subtype.ext (by simpa using hsb)⟩
  let ψ : Localization.AtPrime Q →+* A ⧸ J := IsLocalization.lift (M := Q.primeCompl) hunit
  have hinj : Function.Injective ψ := by
    rw [IsLocalization.lift_injective_iff]
    intro x y
    rw [← sub_eq_zero, ← map_sub, hB0, map_sub, sub_eq_zero]
  haveI hdom : IsDomain (Localization.AtPrime Q) := Function.Injective.isDomain ψ hinj
  refine ⟨hdom, ?_⟩
  letI : Algebra (Localization.AtPrime Q) (A ⧸ J) := ψ.toAlgebra
  haveI : IsScalarTower (integralClosure R A) (Localization.AtPrime Q) (A ⧸ J) :=
    IsScalarTower.of_algebraMap_eq fun b => (IsLocalization.lift_eq hunit b).symm
  have hclosed : ∀ z : A ⧸ J, IsIntegral (Localization.AtPrime Q) z → ∃ w, ψ w = z := by
    intro z hz
    obtain ⟨⟨s, hs⟩, hint⟩ :=
      IsIntegral.exists_multiple_integral_of_isLocalization Q.primeCompl z hz
    have hint' : IsIntegral R ((⟨s, hs⟩ : Q.primeCompl) • z) := isIntegral_trans _ hint
    obtain ⟨p, hpm, hp⟩ := hint'
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective ((⟨s, hs⟩ : Q.primeCompl) • z)
    have hpa : aeval a p ∈ J := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.mkₐ_eq_mk R, ← aeval_algHom_apply,
        Ideal.Quotient.mkₐ_eq_mk, ha]
      exact hp
    obtain ⟨t, ht, htp⟩ := (memJ _).mp hpa
    obtain ⟨w, hw⟩ := exists_mul_mul_eq_self_of_isArtinian_isReduced (t : A)
    have hfi : IsIdempotentElem ((t : A) * w) := by
      unfold IsIdempotentElem
      calc (t : A) * w * ((t : A) * w) = ((t : A) * t * w) * w := by ring
      _ = (t : A) * w := by rw [hw]
    let f : integralClosure R A := ⟨(t : A) * w, hidem _ hfi⟩
    have hf : f ∈ Q.primeCompl := by
      intro hfQ
      apply hS t ht
      refine (memJ _).mpr ⟨1 - f, hcompl f hfQ, ?_⟩
      simp only [f, Subalgebra.coe_sub, OneMemClass.coe_one]
      linear_combination -hw
    have hfp : (t : A) * w * aeval a p = 0 := by linear_combination w * htp
    have hfa : IsIntegral R ((t : A) * w * a) := by
      refine ⟨X * p, monic_X.mul hpm, ?_⟩
      rw [← aeval_def, map_mul, aeval_X]
      calc (t : A) * w * a * aeval ((t : A) * w * a) p
          = a * ((t : A) * w * aeval ((t : A) * w * a) p) := by ring
      _ = 0 := by rw [idempotent_mul_aeval_mul hfi, hfp, mul_zero]
    let c : integralClosure R A := ⟨(t : A) * w * a, (show IsIntegral R ((t : A) * w * a) from hfa)⟩
    refine ⟨IsLocalization.mk' (Localization.AtPrime Q) c (⟨s, hs⟩ : Q.primeCompl), ?_⟩
    rw [IsLocalization.lift_mk'_spec]
    have hf1 : g f = 1 := by
      have hne : g f ≠ 0 := by
        rw [g_eq, Ne, Ideal.Quotient.eq_zero_iff_mem]; exact hS f hf
      have hid : g f * g f = g f := by
        rw [← map_mul]; exact congrArg g (Subtype.ext hfi.eq)
      have : g f * (g f - 1) = 0 := by rw [mul_sub, hid, mul_one, sub_self]
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hne)
    have hsz : (⟨s, hs⟩ : Q.primeCompl) • z = g s * z := by
      rw [Submonoid.smul_def, Algebra.smul_def]
    have hgc : g c = g f * Ideal.Quotient.mk J a := by
      rw [g_eq, g_eq, ← map_mul]
    rw [hgc, hf1, one_mul, ha, hsz]
  rw [isIntegrallyClosed_iff (FractionRing (Localization.AtPrime Q))]
  intro x hx
  have hinj' : Function.Injective (algebraMap (Localization.AtPrime Q) (A ⧸ J)) := hinj
  let ι := IsFractionRing.liftAlgHom (R := Localization.AtPrime Q) (A := Localization.AtPrime Q)
    (K := FractionRing (Localization.AtPrime Q)) (L := A ⧸ J)
    (g := Algebra.ofId (Localization.AtPrime Q) (A ⧸ J)) hinj'
  obtain ⟨w, hw⟩ := hclosed (ι x) (hx.map ι)
  refine ⟨w, ι.toRingHom.injective ?_⟩
  change ι (algebraMap _ _ w) = ι x
  rw [AlgHom.commutes]
  exact hw

end GlobalTheory
end

section

open IsLocalRing

namespace GlobalTheory

theorem atPrime_tensor_isDomain_isIntegrallyClosed_faithfulSMul : ∀ (R A : Type) [CommRing R] [IsDomain R] [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Algebra R A] [FaithfulSMul R A] (p : Ideal R) [p.IsPrime], IsDomain (TensorProduct R (Localization.AtPrime p) A) ∧ IsIntegrallyClosed (TensorProduct R (Localization.AtPrime p) A) ∧ FaithfulSMul (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A) := by
  intro R A _ _ _ _ _ _ _ p _
  set Rp := Localization.AtPrime p
  set B := TensorProduct R Rp A
  letI : Algebra A B := Algebra.TensorProduct.rightAlgebra
  have hpush : Algebra.IsPushout R A Rp B := TensorProduct.isPushout'
  haveI hloc : IsLocalization (Algebra.algebraMapSubmonoid A p.primeCompl) B :=
    (Algebra.isLocalization_iff_isPushout p.primeCompl Rp).mpr hpush
  have hinj : Function.Injective (algebraMap R A) := FaithfulSMul.algebraMap_injective R A
  have hle : Algebra.algebraMapSubmonoid A p.primeCompl ≤ nonZeroDivisors A := by
    rintro _ ⟨r, hr, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero ?_
    intro h0
    apply hr
    have : r = 0 := hinj (by simpa using h0)
    rw [this]; exact p.zero_mem
  haveI hdom : IsDomain B := IsLocalization.isDomain_of_le_nonZeroDivisors B hle
  refine ⟨hdom, isIntegrallyClosed_of_isLocalization B _ hle, ?_⟩
  have hAB : Function.Injective (algebraMap A B) := IsLocalization.injective B hle
  refine (faithfulSMul_iff_algebraMap_injective Rp B).mpr ?_
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl x
  have hcomp : ∀ r : R, algebraMap Rp B (algebraMap R Rp r) = algebraMap A B (algebraMap R A r) := by
    intro r
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have h1 : algebraMap Rp B (algebraMap R Rp r) = 0 := by
    have := congrArg (algebraMap Rp B) (IsLocalization.mk'_spec Rp r s)
    rw [map_mul, hx, zero_mul] at this
    exact this.symm
  rw [hcomp] at h1
  have hr : r = 0 := hinj ((hAB (h1.trans (map_zero _).symm)).trans (map_zero _).symm)
  simp [hr]

end GlobalTheory
end

section

open TensorProduct

namespace GlobalTheory.IdempotentTensorOne

theorem isIntegral_of_isIdempotentElem {S B : Type} [CommRing S] [CommRing B] [Algebra S B]
    {e : B} (he : IsIdempotentElem e) : IsIntegral S e := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.X, Polynomial.monic_X_pow_sub (Polynomial.degree_X_le.trans_lt (by norm_num)), ?_⟩
  simp [sq, he.eq]

theorem exists_idempotent_tmul_one_eq (R A : Type) [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [CommRing A] [Algebra R A] (hA : Algebra.Smooth R A)
    (ε : A ⊗[R] FractionRing R) (hε : IsIdempotentElem ε) :
    ∃ a : A, IsIdempotentElem a ∧ a ⊗ₜ[R] (1 : FractionRing R) = ε := by
  have : Algebra.Smooth R A := hA

  have hint : ε ∈ integralClosure A (A ⊗[R] FractionRing R) := isIntegral_of_isIdempotentElem hε
  obtain ⟨t, ht⟩ := (TensorProduct.toIntegralClosure_bijective_of_smooth
    (R := R) (S := A) (B := FractionRing R)).2 ⟨ε, hint⟩
  have hε' : Algebra.TensorProduct.map (AlgHom.id A A) (integralClosure R (FractionRing R)).val t = ε :=
    congrArg Subtype.val ht
  have hdesc : ∀ u : A ⊗[R] integralClosure R (FractionRing R), ∃ a : A,
      a ⊗ₜ[R] (1 : FractionRing R) =
        Algebra.TensorProduct.map (AlgHom.id A A) (integralClosure R (FractionRing R)).val u := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul x y =>
      obtain ⟨r, hr⟩ := (IsIntegrallyClosed.isIntegral_iff (R := R) (K := FractionRing R)).1
        ((mem_integralClosure_iff _ _).1 y.2)
      refine ⟨r • x, ?_⟩
      rw [Algebra.TensorProduct.map_tmul, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one, hr]
      rfl
    | add u w hu hw =>
      obtain ⟨a, ha⟩ := hu
      obtain ⟨b, hb⟩ := hw
      exact ⟨a + b, by rw [TensorProduct.add_tmul, ha, hb, map_add (f := _)]⟩
  obtain ⟨a, ha⟩ := hdesc t
  rw [hε'] at ha
  refine ⟨a, ?_, ha⟩

  have hinj : Function.Injective (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] FractionRing R) :=
    Algebra.TensorProduct.includeLeft_injective (IsFractionRing.injective R (FractionRing R))
  apply hinj
  show (a * a) ⊗ₜ[R] (1 : FractionRing R) = a ⊗ₜ[R] (1 : FractionRing R)
  rw [← mul_one (1 : FractionRing R), ← Algebra.TensorProduct.tmul_mul_tmul, mul_one, ha, hε.eq]

end GlobalTheory.IdempotentTensorOne
end
