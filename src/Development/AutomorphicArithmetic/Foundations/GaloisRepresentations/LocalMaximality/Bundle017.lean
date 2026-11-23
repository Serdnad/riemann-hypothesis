module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ResidueOfTraceIsFiberSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle639
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle002
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma red_art {R : Type} [CommRing R] [IsArtinianRing R] [IsReduced R] (y : R) :
    ∃ z, y * (1 - y * z) = 0 := by
  obtain ⟨n, w, hw⟩ := IsArtinian.exists_pow_succ_smul_dvd y (1 : R)
  simp only [smul_eq_mul, mul_one] at hw
  refine ⟨w, IsReduced.eq_zero _ ⟨n + 1, ?_⟩⟩
  have h : y ^ n * (1 - y * w) = 0 := by
    rw [mul_sub, mul_one, ← mul_assoc, ← pow_succ, hw, sub_self]
  rw [mul_pow, pow_succ, pow_succ]
  calc y ^ n * y * ((1 - y * w) ^ n * (1 - y * w))
      = y * (1 - y * w) ^ n * (y ^ n * (1 - y * w)) := by ac_rfl
    _ = 0 := by rw [h, mul_zero]

private theorem exists_const_sub_mem_span_tco_of_mem_rA {F L : Type} [Field F] [Field L] [Algebra ℂ F] [Algebra ℂ L] [Algebra F L]
    [IsScalarTower ℂ F L] (d : ℕ) (x : Fin (d + 1) → Fˣ) (f : F) (hf : f ∈ rA ℂ (xv x) {0}) :
    ∃ c : ℂ, ∃ hb : algebraMap F L f ∈ rB ℂ L (xv x) {0},
      (⟨_, hb⟩ : rB ℂ L (xv x) {0}) - algebraMap ℂ _ c ∈ Ideal.span (Set.range fun j : Fin d =>
        (⟨_, tco_mem ℂ L (xv x) j⟩ : rB ℂ L (xv x) {0})) := by
  have memB : ∀ g ∈ rA ℂ (xv x) {0}, algebraMap F L g ∈ rB ℂ L (xv x) {0} := by
    intro g hg
    rw [rB, Subalgebra.mem_restrictScalars, mem_integralClosure_iff]
    exact isIntegral_algebraMap (x := (⟨g, hg⟩ : rA ℂ (xv x) {0}))
  unfold rA at hf
  induction hf using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨i, hi, j, rfl⟩ := hy
    rw [Finset.mem_singleton] at hi
    subst hi
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨k, rfl⟩
    · refine ⟨1, memB _ (Algebra.subset_adjoin ⟨0, Finset.mem_singleton_self 0, 0, rfl⟩), ?_⟩
      convert Ideal.zero_mem _
      rw [sub_eq_zero]
      apply Subtype.ext
      simp
    · refine ⟨0, tco_mem ℂ L (xv x) k, ?_⟩
      rw [map_zero, sub_zero]
      exact Ideal.subset_span ⟨k, rfl⟩
  | algebraMap c0 =>
    refine ⟨c0, memB _ (Subalgebra.algebraMap_mem _ c0), ?_⟩
    convert Ideal.zero_mem _
    rw [sub_eq_zero]
    apply Subtype.ext
    simp [IsScalarTower.algebraMap_apply ℂ F L]
  | add f g _ _ ihf ihg =>
    obtain ⟨c, hb, h⟩ := ihf
    obtain ⟨c', hb', h'⟩ := ihg
    refine ⟨c + c', by rw [map_add (f := _)]; exact Subalgebra.add_mem _ hb hb', ?_⟩
    convert Ideal.add_mem _ h h' using 1
    apply Subtype.ext
    simp only [map_add (f := _), Subalgebra.coe_sub, Subalgebra.coe_add, Subalgebra.coe_algebraMap]
    ring
  | mul f g _ _ ihf ihg =>
    obtain ⟨c, hb, h⟩ := ihf
    obtain ⟨c', hb', h'⟩ := ihg
    refine ⟨c * c', by rw [map_mul]; exact Subalgebra.mul_mem _ hb hb', ?_⟩
    convert Ideal.add_mem _ (Ideal.mul_mem_right (⟨_, hb'⟩ : rB ℂ L (xv x) {0}) _ h)
      (Ideal.mul_mem_left _ (algebraMap ℂ (rB ℂ L (xv x) {0}) c) h') using 1
    apply Subtype.ext
    simp only [map_mul, Subalgebra.coe_sub, Subalgebra.coe_add, Subalgebra.coe_mul,
      Subalgebra.coe_algebraMap]
    ring

private lemma fin_quot {F L : Type} [Field F] [Field L] [Algebra ℂ F] [Algebra ℂ L] [Algebra F L]
    [IsScalarTower ℂ F L] (d : ℕ) (x : Fin (d + 1) → Fˣ) (hc : IsFinCover ℂ L (xv x)) :
    Module.Finite ℂ ((rB ℂ L (xv x) {0}) ⧸ (Ideal.span (Set.range fun j : Fin d =>
      (⟨_, tco_mem ℂ L (xv x) j⟩ : rB ℂ L (xv x) {0})))) := by
  classical
  have hfin := (GlobalTheory.T.finite_cover_chart_smooth_normal ℂ F L d (xv x) hc {0} (Finset.singleton_nonempty 0)).1
  obtain ⟨s, hs⟩ := hfin.fg_top
  refine ⟨⟨s.image (fun z => Ideal.Quotient.mk _ (⟨z.1, z.2⟩ : rB ℂ L (xv x) {0})), ?_⟩⟩
  rw [eq_top_iff]
  rintro q -
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
  have hy : (⟨y.1, y.2⟩ : integralClosure (rA ℂ (xv x) {0}) L) ∈
      Submodule.span (rA ℂ (xv x) {0}) (s : Set (integralClosure (rA ℂ (xv x) {0}) L)) := by
    rw [hs]
    trivial
  change Ideal.Quotient.mk _ (⟨(⟨y.1, y.2⟩ : integralClosure (rA ℂ (xv x) {0}) L).1,
    (⟨y.1, y.2⟩ : integralClosure (rA ℂ (xv x) {0}) L).2⟩ : rB ℂ L (xv x) {0}) ∈ _
  generalize (⟨y.1, y.2⟩ : integralClosure (rA ℂ (xv x) {0}) L) = z at hy ⊢
  induction hy using Submodule.span_induction with
  | mem w hw => exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hw))
  | zero =>
    convert Submodule.zero_mem _ using 1
    exact map_zero (Ideal.Quotient.mk _)
  | add u w _ _ hu hw =>
    convert Submodule.add_mem _ hu hw using 1
    exact map_add (Ideal.Quotient.mk _) _ _
  | smul r u _ hu =>
    obtain ⟨c, hb, hc'⟩ := exists_const_sub_mem_span_tco_of_mem_rA (L := L) d x r.1 r.2
    set_option synthInstance.maxHeartbeats 200000 in
    have e : (⟨((r • u : integralClosure (rA ℂ (xv x) {0}) L) : L), (r • u).2⟩ : rB ℂ L (xv x) {0}) =
        ⟨_, hb⟩ * ⟨u.1, u.2⟩ := by
      apply Subtype.ext
      simp [Algebra.smul_def]
      exact Or.inl rfl
    rw [e, map_mul, Ideal.Quotient.eq.mpr hc', Ideal.Quotient.mk_algebraMap, ← Algebra.smul_def]
    exact Submodule.smul_mem _ c hu

theorem UpperTheory.Gal.productCup_of_system.locMax_of :
    ValBasic → LocMax := by
  intro _ F L _ _ _ _ _ _ d x hc hred e v hv
  obtain ⟨b, hb, hbv, heb, hev⟩ := hv
  rw [mul_zero] at hev
  haveI : Module.Finite ℂ ((rB ℂ L (xv x) {0}) ⧸ (Ideal.span (Set.range fun j : Fin d =>
      (⟨_, tco_mem ℂ L (xv x) j⟩ : rB ℂ L (xv x) {0})))) := fin_quot d x hc
  haveI : IsArtinianRing ((rB ℂ L (xv x) {0}) ⧸ (Ideal.span (Set.range fun j : Fin d =>
      (⟨_, tco_mem ℂ L (xv x) j⟩ : rB ℂ L (xv x) {0})))) := IsArtinianRing.of_finite ℂ _
  haveI : IsReduced ((rB ℂ L (xv x) {0}) ⧸ (Ideal.span (Set.range fun j : Fin d =>
      (⟨_, tco_mem ℂ L (xv x) j⟩ : rB ℂ L (xv x) {0})))) := hred
  obtain ⟨zq, hz⟩ := red_art (Ideal.Quotient.mk (Ideal.span (Set.range fun j : Fin d =>
      (⟨_, tco_mem ℂ L (xv x) j⟩ : rB ℂ L (xv x) {0}))) ⟨b * v, hbv⟩)
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective zq
  have hmem : (⟨b * v, hbv⟩ : rB ℂ L (xv x) {0}) * (1 - ⟨b * v, hbv⟩ * z) ∈
      Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem ℂ L (xv x) j⟩ : rB ℂ L (xv x) {0})) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_sub, map_one, map_mul]
    exact hz
  obtain ⟨c, hcsum⟩ := Ideal.mem_span_range_iff_exists_fun.mp hmem
  have he1 : e.1 (1 - ⟨b * v, hbv⟩ * z) = 1 := by
    rw [map_sub, map_one, map_mul]
    change 1 - e.1 ⟨b * v, hbv⟩ * e.1 z = 1
    rw [hev, zero_mul, sub_zero]
  have hes : e.1 (⟨b, hb⟩ * (1 - ⟨b * v, hbv⟩ * z)) ≠ 0 := by
    rw [map_mul, he1, mul_one]
    exact heb
  have hs0 : ((⟨b, hb⟩ * (1 - ⟨b * v, hbv⟩ * z) : rB ℂ L (xv x) {0}) : L) ≠ 0 := by
    intro h
    apply hes
    rw [show (⟨b, hb⟩ * (1 - ⟨b * v, hbv⟩ * z) : rB ℂ L (xv x) {0}) = 0 from Subtype.ext h, map_zero]
  have key : ((⟨b, hb⟩ * (1 - ⟨b * v, hbv⟩ * z) : rB ℂ L (xv x) {0}) : L) * v =
      ∑ l, (c l : L) * tt L x l := by
    have h1 : (((⟨b * v, hbv⟩ : rB ℂ L (xv x) {0}) * (1 - ⟨b * v, hbv⟩ * z) : rB ℂ L (xv x) {0}) : L) =
        ∑ l, (c l : L) * tt L x l := by
      rw [← hcsum]
      simp [tt]
    rw [← h1]
    simp only [Subalgebra.coe_mul, Subalgebra.coe_sub, Subalgebra.coe_one]
    ring
  refine ⟨fun l => (c l : L) * ((⟨b, hb⟩ * (1 - ⟨b * v, hbv⟩ * z) : rB ℂ L (xv x) {0}) : L)⁻¹,
    fun l => ⟨⟨b, hb⟩ * (1 - ⟨b * v, hbv⟩ * z), hes, ?_⟩, ?_⟩
  · rw [mul_comm, mul_assoc, inv_mul_cancel₀ hs0, mul_one]
    exact (c l).2
  · calc v = ((⟨b, hb⟩ * (1 - ⟨b * v, hbv⟩ * z) : rB ℂ L (xv x) {0}) : L)⁻¹ *
          (((⟨b, hb⟩ * (1 - ⟨b * v, hbv⟩ * z) : rB ℂ L (xv x) {0}) : L) * v) := by
          rw [← mul_assoc, inv_mul_cancel₀ hs0, one_mul]
      _ = _ := by
          rw [key, Finset.mul_sum]
          exact Finset.sum_congr rfl fun l _ => by ring
end

section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private theorem exists_of_li {Q ι : Type} [AddCommGroup Q] [Module ℂ Q] [Finite ι] (f : ι → Q →ₗ[ℂ] ℂ)
    (h : LinearIndependent ℂ f) (v : ι → ℂ) : ∃ q, ∀ i, f i q = v i :=
  _root_.UpperTheory.Reformulated.B.Qe54.exists_of_li f h v

private theorem chineseRemainder_finiteCover {F K : Type} [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K]
    [IsScalarTower ℂ F K] {d : ℕ} (x : Fin (d + 1) → F) (hc : IsFinCover ℂ K x) :
    Finite (fib ℂ K x) ∧ ∀ v : fib ℂ K x → ℂ, ∃ h : rB ℂ K x {0}, ∀ e, e.1 h = v e := by
  set_option synthInstance.maxHeartbeats 200000 in
    classical
    let I : Ideal (rB ℂ K x {0}) :=
      Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem ℂ K x j⟩ : rB ℂ K x {0}))
    let mk : rB ℂ K x {0} →ₐ[ℂ] (rB ℂ K x {0} ⧸ I) := Ideal.Quotient.mkₐ ℂ I
    have hfin := (GlobalTheory.T.finite_cover_chart_smooth_normal ℂ F K d x hc {0} (Finset.singleton_nonempty 0)).1
    have hmem : ∀ y (hy : y ∈ rA ℂ x {0}), algebraMap F K y ∈ rB ℂ K x {0} := fun y hy =>
      (integralClosure (rA ℂ x {0}) K).algebraMap_mem ⟨y, hy⟩
    have hA : ∀ y (hy : y ∈ rA ℂ x {0}), ∃ c : ℂ,
        mk ⟨algebraMap F K y, hmem y hy⟩ = algebraMap ℂ _ c := by
      intro y hy
      refine Algebra.adjoin_induction (p := fun y hy => ∃ c : ℂ,
        mk ⟨algebraMap F K y, hmem y hy⟩ = algebraMap ℂ _ c) ?_ ?_ ?_ ?_ hy
      · rintro _ ⟨i, hi, j, rfl⟩
        obtain rfl : i = 0 := Finset.mem_singleton.1 hi
        induction j using Fin.cases with
        | zero =>
          refine ⟨1, ?_⟩
          rw [map_one, ← map_one mk]
          congr 1
          ext
          simp [div_self (hc.pd.ne 0)]
        | succ j =>
          refine ⟨0, ?_⟩
          rw [map_zero]
          exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨j, rfl⟩)
      · intro r
        refine ⟨r, ?_⟩
        rw [← mk.commutes r]
        congr 1
        ext
        simp [← IsScalarTower.algebraMap_apply]
      · rintro a b ha hb ⟨c, hc1⟩ ⟨c', hc2⟩
        refine ⟨c + c', ?_⟩
        have e : (⟨algebraMap F K (a + b), hmem _ (add_mem ha hb)⟩ : rB ℂ K x {0}) =
            ⟨_, hmem a ha⟩ + ⟨_, hmem b hb⟩ := Subtype.ext (map_add _ _ _)
        exact (congrArg mk e).trans (by rw [map_add mk, hc1, hc2, map_add (algebraMap ℂ _)])
      · rintro a b ha hb ⟨c, hc1⟩ ⟨c', hc2⟩
        refine ⟨c * c', ?_⟩
        have e : (⟨algebraMap F K (a * b), hmem _ (mul_mem ha hb)⟩ : rB ℂ K x {0}) =
            ⟨_, hmem a ha⟩ * ⟨_, hmem b hb⟩ := Subtype.ext (map_mul _ _ _)
        exact (congrArg mk e).trans (by rw [map_mul, hc1, hc2, map_mul])
    have hQ : Module.Finite ℂ (rB ℂ K x {0} ⧸ I) := by
      obtain ⟨s, hs⟩ := hfin.fg_top
      let g : integralClosure (rA ℂ x {0}) K → (rB ℂ K x {0} ⧸ I) := fun y => mk ⟨y.1, y.2⟩
      have key : ∀ y, y ∈ Submodule.span (rA ℂ x {0}) (s : Set (integralClosure (rA ℂ x {0}) K)) →
          g y ∈ Submodule.span ℂ (g '' (s : Set (integralClosure (rA ℂ x {0}) K))) := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
        | zero =>
          have h0 : g 0 = 0 := map_zero mk
          rw [h0]
          exact Submodule.zero_mem _
        | add a b _ _ ha hb =>
          have : g (a + b) = g a + g b := by
            simp only [g, ← map_add (f := _)]
            rfl
          rw [this]
          exact Submodule.add_mem _ ha hb
        | smul a y _ hy =>
          obtain ⟨c, hc1⟩ := hA a.1 a.2
          have e : (⟨((a • y : integralClosure (rA ℂ x {0}) K)).1, ((a • y : integralClosure (rA ℂ x {0}) K)).2⟩ : rB ℂ K x {0}) = ⟨_, hmem a.1 a.2⟩ * ⟨y.1, y.2⟩ :=
            Subtype.ext (Algebra.smul_def a y.1)
          have : g (a • y) = c • g y :=
            (congrArg mk e).trans (by rw [map_mul, hc1, ← Algebra.smul_def])
          rw [this]
          exact Submodule.smul_mem _ _ hy
      refine ⟨⟨(s.image g), ?_⟩⟩
      rw [eq_top_iff]
      rintro q -
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
      have := key ⟨b.1, b.2⟩ (hs ▸ Submodule.mem_top)
      rw [Finset.coe_image]
      exact this
    have hker : ∀ e : fib ℂ K x, ∀ a ∈ I, e.1 a = 0 := by
      intro e a ha
      have : I ≤ RingHom.ker (e.1 : rB ℂ K x {0} →+* ℂ) := by
        refine Ideal.span_le.2 ?_
        rintro _ ⟨j, rfl⟩
        exact e.2 j
      exact this ha
    let L : fib ℂ K x → ((rB ℂ K x {0} ⧸ I) →ₐ[ℂ] ℂ) := fun e => Ideal.Quotient.liftₐ I e.1 (hker e)
    have hL : ∀ e b, L e (mk b) = e.1 b := fun e b => by
      first | rfl | exact Ideal.Quotient.lift_mk _ _ _
    have hinj : Function.Injective L := by
      intro e e' h
      refine Subtype.ext (AlgHom.ext fun b => ?_)
      rw [← hL, ← hL, h]
    have li : LinearIndependent ℂ (fun e => (L e).toLinearMap) :=
      (linearIndependent_algHom_toLinearMap' ℂ (rB ℂ K x {0} ⧸ I) ℂ).comp L hinj
    have hF : Finite (fib ℂ K x) := li.finite
    refine ⟨hF, fun v => ?_⟩
    obtain ⟨q, hq⟩ := exists_of_li _ li v
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
    refine ⟨b, fun e => ?_⟩
    rw [← hq e, ← hL]
    rfl

theorem UpperTheory.Gal.productCup_of_system.cRT_of :
    CRT := by
  intro F K _ _ _ _ _ _ d x hc
  exact chineseRemainder_finiteCover (xv x) hc
end
