module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ResidueOfTraceIsFiberSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle542
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle594
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle450
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

set_option autoImplicit false

private lemma int_range {L A : Type} [Field L] [Algebra ℂ L] [CommRing A] [Algebra ℂ A] [Algebra A L]
    [IsScalarTower ℂ A L] (hA : ∀ a : A, a ∈ (algebraMap ℂ A).range) {y : L} (h : IsIntegral A y) :
    y ∈ (algebraMap ℂ L).range := by
  haveI : Algebra.IsIntegral ℂ A := ⟨fun a => by
    obtain ⟨c, rfl⟩ := hA a
    exact isIntegral_algebraMap⟩
  have hy : IsIntegral ℂ y := isIntegral_trans y h
  exact minpoly.mem_range_of_degree_eq_one ℂ y
    (IsAlgClosed.degree_eq_one_of_irreducible ℂ (minpoly.irreducible hy))

private lemma int_mono {E L : Type} [CommRing E] [Algebra ℂ E] [CommRing L] [Algebra E L]
    {A B : Subalgebra ℂ E} (h : A ≤ B) {y : L} (hy : IsIntegral A y) : IsIntegral B y := by
  obtain ⟨p, hp, he⟩ := hy
  refine ⟨p.map (Subalgebra.inclusion h).toRingHom, hp.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  exact he

private lemma int_scale {L : Type} [Field L] [Algebra ℂ L] (A A' : Subalgebra ℂ L) (s : L) (hs : s ∈ A)
    (hc : ∀ c ∈ A', ∃ N : ℕ, s ^ N * c ∈ A) {y : L} (hy : IsIntegral A' y) :
    ∃ N : ℕ, IsIntegral A (y * s ^ N) := by
  obtain ⟨p, hp, he⟩ := hy
  set q : Polynomial L := p.map (algebraMap A' L) with hq
  have hqm : q.Monic := hp.map _
  have hqe : q.eval₂ (RingHom.id L) y = 0 := by
    rw [hq, Polynomial.eval₂_map]
    simpa using he
  have hcoef : ∀ i, q.coeff i ∈ A' := fun i => by
    rw [hq, Polynomial.coeff_map]
    exact (p.coeff i).2
  have hM : ∀ t : Finset ℕ, ∃ M : ℕ, ∀ i ∈ t, s ^ M * q.coeff i ∈ A := by
    intro t
    induction t using Finset.induction_on with
    | empty => exact ⟨0, by simp⟩
    | insert a t _ ih =>
      obtain ⟨M, hM⟩ := ih
      obtain ⟨N, hN⟩ := hc _ (hcoef a)
      refine ⟨M + N, fun i hi => ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · rw [pow_add, mul_assoc]
        exact A.mul_mem (A.pow_mem hs _) hN
      · rw [add_comm, pow_add, mul_assoc]
        exact A.mul_mem (A.pow_mem hs _) (hM i hi)
  obtain ⟨M, hM⟩ := hM (Finset.range (q.natDegree + 1))
  refine ⟨M, ?_⟩
  have hrm : (Polynomial.scaleRoots q (s ^ M)).Monic := (Polynomial.monic_scaleRoots_iff _).2 hqm
  have hre : (Polynomial.scaleRoots q (s ^ M)).eval₂ (RingHom.id L) (y * s ^ M) = 0 := by
    have := Polynomial.scaleRoots_eval₂_mul (p := q) (RingHom.id L) y (s ^ M)
    rw [hqe, mul_zero] at this
    rw [mul_comm]
    exact this
  have hA : ∀ i, (Polynomial.scaleRoots q (s ^ M)).coeff i ∈ A := by
    intro i
    rw [Polynomial.coeff_scaleRoots]
    rcases lt_trichotomy i q.natDegree with hi | hi | hi
    · obtain ⟨k, hk⟩ : ∃ k, q.natDegree - i = k + 1 := ⟨q.natDegree - i - 1, by omega⟩
      rw [hk, pow_succ, mul_comm, mul_assoc]
      refine A.mul_mem (A.pow_mem (A.pow_mem hs _) _) ?_
      rw [mul_comm]
      exact mul_comm (s ^ M) (q.coeff i) ▸ hM i (Finset.mem_range.2 (by omega))
    · subst hi
      simp [hqm.coeff_natDegree, A.one_mem]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hi, zero_mul]
      exact A.zero_mem
  have hlift : Polynomial.scaleRoots q (s ^ M) ∈ Polynomial.lifts (algebraMap A L) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    exact ⟨⟨_, hA i⟩, rfl⟩
  obtain ⟨r, hr, -, hrm'⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hrm
  refine ⟨r, hrm', ?_⟩
  rw [← hr, Polynomial.eval₂_map] at hre
  simpa using hre

private lemma omB_mono' {L : Type} [Field L] [Algebra ℂ L] {B B' : Subalgebra ℂ L} (h : B ≤ B') (q : ℕ) :
    omB ℂ L B q ≤ omB ℂ L B' q :=
  Submodule.span_mono fun _ ⟨b, hb, v, hv, e⟩ => ⟨b, h hb, v, fun j => h (hv j), e⟩

private lemma omB_stab {L : Type} [Field L] [Algebra ℂ L] (B : Subalgebra ℂ L) (q : ℕ) :
    Stab (Algebra.lsmul ℂ ℂ (DR ℂ L)) B (omB ℂ L B q) := by
  intro r hr m hm
  induction hm using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨b, hb, v, hv, rfl⟩ := hz
    exact Submodule.subset_span ⟨r * b, B.mul_mem hr hb, v, hv, by simp [mul_smul]⟩
  | zero => simp
  | add a c _ _ ha hc =>
    rw [map_add (f := _)]
    exact add_mem ha hc
  | smul t a _ ha =>
    rw [map_smul]
    exact Submodule.smul_mem _ _ ha

section
variable {F K K' : Type} [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] {d : ℕ} (x : Fin (d + 1) → F) (j2 : K →ₐ[ℂ] K')

private lemma rA_mono' {I I' : Finset (Fin (d + 1))} (h : I ⊆ I') : rA ℂ x I ≤ rA ℂ x I' :=
  Algebra.adjoin_mono fun _ ⟨i, hi, j, e⟩ => ⟨i, h hi, j, e⟩

private lemma rB_mono' {I I' : Finset (Fin (d + 1))} (h : I ⊆ I') : rB ℂ K x I ≤ rB ℂ K x I' :=
  fun _ hy => int_mono (rA_mono' x h) hy

private lemma integralClosure_mono_subset {J J' : Finset (Fin (d + 1))} (h : J ⊆ J') : R2 x j2 J ≤ R2 x j2 J' :=
  fun _ hy => int_mono (Subalgebra.map_mono (rB_mono' x h)) hy

private lemma ratio_mem {I : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∈ I) (a : Fin (d + 1)) :
    x a / x i ∈ rA ℂ x I :=
  Algebra.subset_adjoin ⟨i, hi, a, rfl⟩

private lemma rA_mem_rB {I : Finset (Fin (d + 1))} {f : F} (hf : f ∈ rA ℂ x I) :
    algebraMap F K f ∈ rB ℂ K x I :=
  show IsIntegral (rA ℂ x I) (algebraMap F K f) from
    isIntegral_algebraMap (R := rA ℂ x I) (A := K) (x := ⟨f, hf⟩)

private lemma rB_empty {b : K} (hb : b ∈ rB ℂ K x ∅) : b ∈ (algebraMap ℂ K).range := by
  refine int_range (A := rA ℂ x ∅) (fun a => ?_) hb
  have h0 : rA ℂ x ∅ = ⊥ := by simp [rA]
  have ha : (a : F) ∈ (⊥ : Subalgebra ℂ F) := h0 ▸ a.2
  obtain ⟨c, hc⟩ := Algebra.mem_bot.1 ha
  exact ⟨c, Subtype.ext hc⟩

private lemma integralClosure_empty_const {y : K'} (hy : y ∈ R2 x j2 ∅) : y ∈ (algebraMap ℂ K').range := by
  refine int_range (A := (rB ℂ K x ∅).map j2) (fun a => ?_) hy
  obtain ⟨b, hb, hba⟩ := a.2
  obtain ⟨c, rfl⟩ := rB_empty x hb
  exact ⟨c, Subtype.ext (by rw [← hba]; simp)⟩

private lemma j2_mem_R2_of_mem_rB {J : Finset (Fin (d + 1))} {b : K} (hb : b ∈ rB ℂ K x J) : j2 b ∈ R2 x j2 J :=
  show IsIntegral ((rB ℂ K x J).map j2) (j2 b) from
    isIntegral_algebraMap (R := (rB ℂ K x J).map j2) (A := K') (x := ⟨j2 b, b, hb, rfl⟩)

private lemma rB_shift (h : IsFinCover ℂ K x) {J : Finset (Fin (d + 1))} {j j' : Fin (d + 1)} (hj : j ∈ J) {b : K}
    (hb : b ∈ rB ℂ K x (insert j' J)) : ∃ N : ℕ, algebraMap F K (x j' / x j) ^ N * b ∈ rB ℂ K x J := by
  by_cases hj' : j' ∈ J
  · refine ⟨0, ?_⟩
    rw [Finset.insert_eq_of_mem hj'] at hb
    simpa using hb
  · obtain ⟨N, hN⟩ := ((GlobalTheory.T.finite_cover_ring_localization_chart ℂ F K d x h (insert j' J) j (Finset.mem_insert_of_mem hj)).2 b).1 hb
    refine ⟨N, ((GlobalTheory.T.finite_cover_ring_localization_chart ℂ F K d x h J j hj).2 _).2 ⟨N, ?_⟩⟩
    rw [Finset.prod_insert hj', map_mul, mul_pow] at hN
    convert hN using 1
    ring

private lemma integralClosure_shift_power (h : IsFinCover ℂ K x) {J : Finset (Fin (d + 1))} {j j' : Fin (d + 1)} (hj : j ∈ J) {y : K'}
    (hy : y ∈ R2 x j2 (insert j' J)) : ∃ N : ℕ, y * j2 (algebraMap F K (x j' / x j)) ^ N ∈ R2 x j2 J := by
  have hs : j2 (algebraMap F K (x j' / x j)) ∈ (rB ℂ K x J).map j2 :=
    ⟨_, rA_mem_rB x (ratio_mem x hj j'), rfl⟩
  obtain ⟨N, hN⟩ := int_scale ((rB ℂ K x J).map j2) ((rB ℂ K x (insert j' J)).map j2) _ hs (by
    rintro _ ⟨b, hb, rfl⟩
    obtain ⟨N, hN⟩ := rB_shift x h hj hb
    exact ⟨N, ⟨_, hN, by simp⟩⟩) hy
  exact ⟨N, hN⟩

end

theorem UpperTheory.Gal.productCup_of_system.rYBasic_of :
    RYBasic := by
  intro F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 hY
  have hpull : ∀ I, ∀ b ∈ rB ℂ K (xv x) I, algebraMap K K' b ∈ rB ℂ K' (xv x) I := by
    intro I b hb
    have hb' : IsIntegral (rA ℂ (xv x) I) b := hb
    exact (IsIntegral.algebraMap hb' : IsIntegral (rA ℂ (xv x) I) (algebraMap K K' b))
  have hmono : ∀ I I' J J', I ⊆ I' → J ⊆ J' → RY (xv x) j2 I J ≤ RY (xv x) j2 I' J' :=
    fun I I' J J' hI hJ => sup_le_sup (rB_mono' (xv x) hI) (integralClosure_mono_subset (xv x) j2 hJ)
  refine ⟨fun I => ?_, fun a => ?_, hmono, fun I b hb => ⟨hpull I b hb, j2_mem_R2_of_mem_rB (xv x) j2 hb⟩, ?_⟩
  · refine sup_eq_left.2 fun y hy => ?_
    obtain ⟨c, rfl⟩ := integralClosure_empty_const (xv x) j2 hy
    exact (rB ℂ K' (xv x) I).algebraMap_mem c
  · refine ⟨fun I I' J J' _ _ hI hJ => hmono I I' J J' hI hJ,
      fun I I' J J' _ _ hI hJ => omB_mono' (hmono I I' J J' hI hJ) a,
      fun I J _ _ => omB_stab _ a, fun I J _ i hi b => ?_, fun I J _ j hj b => ?_⟩
    · have e : (((sysY x j2 a).X b * ((sysY x j2 a).X i)⁻¹ : K'ˣ) : K') = algebraMap F K' (xv x b / xv x i) := by
        simp [sysY, map_div₀, div_eq_mul_inv]
      rw [e]
      exact (le_sup_left : rB ℂ K' (xv x) I ≤ RY (xv x) j2 I J) (rA_mem_rB (xv x) (ratio_mem (xv x) hi b))
    · have e : (((sysY x j2 a).Y b * ((sysY x j2 a).Y j)⁻¹ : K'ˣ) : K') = j2 (algebraMap F K (xv x b / xv x j)) := by
        simp [sysY, map_div₀, div_eq_mul_inv]
      rw [e]
      exact (le_sup_right : R2 (xv x) j2 J ≤ RY (xv x) j2 I J)
        (j2_mem_R2_of_mem_rB (xv x) j2 (rA_mem_rB (xv x) (ratio_mem (xv x) hj b)))
  · intro J j hj j' y hy
    exact integralClosure_shift_power (xv x) j2 hY.covZ hj hy
end

section

set_option autoImplicit false

noncomputable section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

namespace UpperTheory.Gal.productCup_of_system


open scoped IntermediateField.algebraAdjoinAdjoin in
private theorem tb_F {F : Type} [Field F] [Algebra ℂ F] {d : ℕ} {x : Fin (d + 1) → F} (pd : IsPd ℂ x) :
    IsTranscendenceBasis ℂ (fun j : Fin d => x j.succ / x 0) := by
  refine pd.indep.isTranscendenceBasis_iff_isAlgebraic.mpr ⟨fun a => ?_⟩
  refine (IsFractionRing.isAlgebraic_iff (Algebra.adjoin ℂ (Set.range fun j : Fin d => x j.succ / x 0))
    (IntermediateField.adjoin ℂ (Set.range fun j : Fin d => x j.succ / x 0)) F).mpr ?_
  have ha : a ∈ IntermediateField.adjoin ℂ (Set.range fun j : Fin d => x j.succ / x 0) := by
    rw [pd.gen]; trivial
  exact isAlgebraic_algebraMap (⟨a, ha⟩ : IntermediateField.adjoin ℂ (Set.range fun j : Fin d => x j.succ / x 0))

private theorem algHom_finite_of_proper {F K L : Type} [Field F] [Field K] [Field L] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ L]
    [Algebra F K] [IsScalarTower ℂ F K] [Algebra F L] [IsScalarTower ℂ F L] {d : ℕ} {x : Fin (d + 1) → F}
    (pd : IsPd ℂ x) [FiniteDimensional F K] [FiniteDimensional F L] (j2 : K →ₐ[ℂ] L) :
    j2.toRingHom.Finite := by
  have hF := tb_F pd
  set t : Fin d → F := fun j => x j.succ / x 0 with ht
  have hL : IsTranscendenceBasis ℂ (algebraMap F L ∘ t) := hF.algebraMap_comp
  have hK : IsTranscendenceBasis ℂ (algebraMap F K ∘ t) := hF.algebraMap_comp
  letI : Algebra K L := j2.toRingHom.toAlgebra
  haveI : IsScalarTower ℂ K L := IsScalarTower.of_algebraMap_eq fun c => (j2.commutes c).symm
  have hw : AlgebraicIndependent ℂ (algebraMap K L ∘ (algebraMap F K ∘ t)) :=
    hK.1.map' (f := IsScalarTower.toAlgHom ℂ K L) (algebraMap K L).injective
  have hwb : IsTranscendenceBasis ℂ (algebraMap K L ∘ (algebraMap F K ∘ t)) :=
    hw.isTranscendenceBasis_of_trdeg_le_of_finite (by rw [← hL.cardinalMk_eq_trdeg])
  have halg : Algebra.IsAlgebraic K L := hwb.isAlgebraic_iff.2 fun i => isAlgebraic_algebraMap _
  obtain ⟨s, hs⟩ := (Module.finite_def (R := F) (M := L)).1 inferInstance
  let S : Set L := (s : Set L) ∪ Set.range (algebraMap F L ∘ t)
  have hSfin : S.Finite := s.finite_toSet.union (Set.finite_range _)
  haveI : Finite S := hSfin
  have htop : IntermediateField.adjoin K S = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    let P : IntermediateField ℂ L := (IntermediateField.adjoin K S).restrictScalars ℂ
    have hP : ∀ f : F, algebraMap F L f ∈ P := by
      have hle : IntermediateField.adjoin ℂ (Set.range t) ≤ P.comap (IsScalarTower.toAlgHom ℂ F L) := by
        rw [IntermediateField.adjoin_le_iff]
        rintro _ ⟨j, rfl⟩
        exact IntermediateField.subset_adjoin K S (Or.inr ⟨j, rfl⟩)
      rw [pd.gen] at hle
      exact fun f => hle (IntermediateField.mem_top)
    have hy : y ∈ Submodule.span F (s : Set L) := by rw [hs]; trivial
    induction hy using Submodule.span_induction with
    | mem z hz => exact IntermediateField.subset_adjoin K S (Or.inl hz)
    | zero => exact zero_mem _
    | add a c _ _ ha hc => exact add_mem ha hc
    | smul r a _ ha =>
      rw [Algebra.smul_def]
      exact mul_mem (hP r) ha
  haveI : FiniteDimensional K (IntermediateField.adjoin K S) :=
    IntermediateField.finiteDimensional_adjoin fun z _ => (halg.isAlgebraic z).isIntegral
  rw [htop] at this
  change Module.Finite K L
  exact (IntermediateField.topEquiv (F := K) (E := L)).toLinearEquiv.finiteDimensional

private theorem fg_rB {F L : Type} [Field F] [Field L] [Algebra ℂ F] [Algebra ℂ L] [Algebra F L]
    [IsScalarTower ℂ F L] {d : ℕ} {x : Fin (d + 1) → F} (pd : IsPd ℂ x) [FiniteDimensional F L]
    (J : Finset (Fin (d + 1))) : (rB ℂ L x J).FG := by
  rcases J.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
  · have hbot : rB ℂ L x ∅ = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      haveI : Algebra.IsIntegral ℂ (rA ℂ x ∅) := Algebra.IsIntegral.adjoin (by simp)
      have h : IsIntegral ℂ y := isIntegral_trans (A := rA ℂ x ∅) y hy
      have := minpoly.mem_range_of_degree_eq_one ℂ y
        (IsAlgClosed.degree_eq_one_of_irreducible ℂ (minpoly.irreducible h))
      exact Algebra.mem_bot.2 this
    rw [hbot]
    exact Subalgebra.fg_bot
  · haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap ℂ F).injective
    haveI : IsFractionRing (rA ℂ x J) F := (GlobalTheory.T.standardOpenCoordinateRing_isFractionRing_isNoetherianRing ℂ F d x pd J ⟨i, hi⟩).1
    haveI : IsNoetherianRing (rA ℂ x J) := (GlobalTheory.T.standardOpenCoordinateRing_isFractionRing_isNoetherianRing ℂ F d x pd J ⟨i, hi⟩).2
    haveI := rA_isIntegrallyClosed pd hi
    set_option synthInstance.maxHeartbeats 200000 in
      haveI : Module.Finite (rA ℂ x J) (integralClosure (rA ℂ x J) L) :=
        IsIntegralClosure.finite (rA ℂ x J) F L (integralClosure (rA ℂ x J) L)
    have hfg : (rA ℂ x J).FG := by
      refine Subalgebra.fg_def.2 ⟨_, ?_, rfl⟩
      refine ((J.finite_toSet.prod (Set.finite_univ (α := Fin (d + 1)))).image
        fun p => x p.2 / x p.1).subset ?_
      rintro _ ⟨i', hi', j, rfl⟩
      exact ⟨(i', j), ⟨hi', trivial⟩, rfl⟩
    haveI : Algebra.FiniteType ℂ (rA ℂ x J) := (Subalgebra.fg_iff_finiteType _).1 hfg
    set_option synthInstance.maxHeartbeats 200000 in
      have hft : Algebra.FiniteType ℂ (integralClosure (rA ℂ x J) L) :=
        Algebra.FiniteType.trans (S := rA ℂ x J) inferInstance inferInstance
    exact (Subalgebra.fg_iff_finiteType (rB ℂ L x J)).2 hft

private theorem integralClosure_finiteGenerated {F K L : Type} [Field F] [Field K] [Field L] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ L]
    [Algebra F K] [IsScalarTower ℂ F K] {d : ℕ} {x : Fin (d + 1) → F} (pd : IsPd ℂ x) [FiniteDimensional F K]
    (j2 : K →ₐ[ℂ] L) (hf : j2.toRingHom.Finite) (J : Finset (Fin (d + 1))) : (R2 x j2 J).FG := by
  letI : Algebra K L := j2.toRingHom.toAlgebra
  letI : Algebra F L := ((algebraMap K L).comp (algebraMap F K)).toAlgebra
  haveI : IsScalarTower F K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower ℂ K L := IsScalarTower.of_algebraMap_eq fun c => (j2.commutes c).symm
  haveI : IsScalarTower ℂ F L := IsScalarTower.of_algebraMap_eq fun c => by
    change algebraMap ℂ L c = algebraMap K L (algebraMap F K (algebraMap ℂ F c))
    rw [← IsScalarTower.algebraMap_apply ℂ F K c]
    exact (j2.commutes c).symm
  haveI : Module.Finite K L := hf
  haveI : FiniteDimensional F L := Module.Finite.trans K L
  let A := rA ℂ x J
  let B := (rB ℂ K x J).map j2
  let φ : A →+* B :=
    { toFun := fun a => ⟨algebraMap K L (algebraMap F K a),
        Subalgebra.mem_map.2 ⟨algebraMap F K a, (integralClosure A K).algebraMap_mem a, rfl⟩⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  letI : Algebra A B := φ.toAlgebra
  haveI : IsScalarTower A B L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.IsIntegral A B := ⟨fun b => by
    obtain ⟨c, hc, hb⟩ := Subalgebra.mem_map.1 b.2
    have h1 : IsIntegral A (algebraMap K L c) := IsIntegral.algebraMap hc
    have h2 : algebraMap B L b = algebraMap K L c := hb.symm
    rw [← h2] at h1
    exact (isIntegral_algebraMap_iff ).1 h1⟩
  have e : R2 x j2 J = rB ℂ L x J := by
    ext y
    constructor
    · intro hy
      exact isIntegral_trans (A := B) y hy
    · intro hy
      exact IsIntegral.tower_top (A := B) hy
  rw [e]
  exact fg_rB pd J

theorem rYFT_of :
    RYFT := by
  intro F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 h I J hI
  have pd := h.covZ.pd
  haveI := h.covZ.fin
  haveI := h.covY.fin
  have h1 : (rB ℂ K' (xv x) I).FG := fg_rB h.covY.pd I
  have h2 : (R2 (xv x) j2 J).FG := integralClosure_finiteGenerated pd j2 (algHom_finite_of_proper pd j2) J
  exact (Subalgebra.fg_iff_finiteType _).1 (h1.sup h2)

end UpperTheory.Gal.productCup_of_system

end
end
