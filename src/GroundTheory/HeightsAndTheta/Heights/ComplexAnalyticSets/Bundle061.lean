module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle044
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle045
public import Mathlib.Algebra.MvPolynomial.Funext
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle046
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.TypeStar
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.Filtration

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing RingTheory.Sequence

theorem SerreRAt.of_ringEquiv {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B) {k : ℕ}
    (h : SerreRAt A k) : SerreRAt B k := fun hd => by
  have := h (by rwa [ringKrullDim_eq_of_ringEquiv e])
  exact IsRegularLocalRing.of_ringEquiv e

theorem SerreSAt.of_ringEquiv {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (e : A ≃+* B) {k : ℕ} (h : SerreSAt A k) : SerreSAt B k := by
  obtain ⟨rs, hmem, hreg, hlen⟩ := h
  refine ⟨rs.map e, ?_, ?_, ?_⟩
  · intro r hr
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
    have := hmem s hs
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at this ⊢
    exact fun hu => this ((isUnit_map_iff e s).mp hu)
  · refine (AddEquiv.isWeaklyRegular_congr (e := e.toAddEquiv) ?_).mp hreg
    exact List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr fun r _ x => by
      simp [smul_eq_mul])
  · rwa [List.length_map, ← ringKrullDim_eq_of_ringEquiv e]

noncomputable def localizationAtMaximalEquiv (B : Type*) [CommRing B] [IsLocalRing B] :
    Localization.AtPrime (maximalIdeal B) ≃+* B :=
  (IsLocalization.atUnits B (maximalIdeal B).primeCompl (fun x hx => by
    simpa [Ideal.primeCompl, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, IsUnit.mem_submonoid_iff] using hx)).toRingEquiv.symm

theorem normalRing_of_isIntegrallyClosed (B : Type*) [CommRing B] [IsDomain B] [IsIntegrallyClosed B] :
    NormalRing B := fun P _ =>
  ⟨inferInstance, isIntegrallyClosed_of_isLocalization (Localization.AtPrime P) P.primeCompl
    P.primeCompl_le_nonZeroDivisors⟩

theorem serreAt_of_isIntegrallyClosed (hC : SerreCriterion.Statement) (B : Type) [CommRing B] [IsLocalRing B]
    [IsNoetherianRing B] [IsDomain B] [IsIntegrallyClosed B] : SerreRAt B 1 ∧ SerreSAt B 2 := by
  obtain ⟨h1, h2⟩ := (hC B inferInstance).mp (normalRing_of_isIntegrallyClosed B)
  exact ⟨(h1 (maximalIdeal B)).of_ringEquiv (localizationAtMaximalEquiv B),
    (h2 (maximalIdeal B)).of_ringEquiv (localizationAtMaximalEquiv B)⟩

theorem FlatNormalFibres.proof (hC : SerreCriterion.Statement) (hR : SerreRFlatAscent.Statement)
    (hS : SerreSFlatAscent.Statement) : FlatNormalFibres.Statement := by
  intro R S _ _ _ hRn hSn hloc hflat hdom hic hfib
  obtain ⟨hR1, hR2⟩ := (hC R hRn).mp (normalRing_of_isIntegrallyClosed R)
  have hfib' : ∀ (P : Ideal S) [P.IsPrime],
      SerreRAt (primeFibreLocalRing R P) 1 ∧ SerreSAt (primeFibreLocalRing R P) 2 := fun P _ => by
    obtain ⟨h1, h2⟩ := hfib P
    exact serreAt_of_isIntegrallyClosed hC _
  have hN : NormalRing S := (hC S hSn).mpr
    ⟨hR R S hRn hSn hflat 1 hR1 fun P _ => (hfib' P).1, hS R S hRn hSn hflat 2 hR2 fun P _ => (hfib' P).2⟩
  obtain ⟨hd, hi⟩ := hN (maximalIdeal S)
  exact ⟨(localizationAtMaximalEquiv S).symm.toMulEquiv.isDomain,
    IsIntegrallyClosed.of_equiv (localizationAtMaximalEquiv S)⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology ComplexSets

noncomputable section

theorem exists_minimalPrime_mem_zeroSet {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) {x : Fin n → ℂ}
    (hx : x ∈ zeroSet J) : ∃ P ∈ J.minimalPrimes, x ∈ zeroSet P := by
  have hJ : J ≤ RingHom.ker (eval x) := fun q hq => (RingHom.mem_ker).2 (hx q hq)
  have : (RingHom.ker (eval x : MvPolynomial (Fin n) ℂ →+* ℂ)).IsPrime := RingHom.ker_isPrime _
  obtain ⟨P, hP, hPle⟩ := Ideal.exists_minimalPrimes_le hJ
  exact ⟨P, hP, fun q hq => (RingHom.mem_ker).1 (hPle hq)⟩

theorem mem_isolatedFibrePts_of_le {n m : ℕ} {J P : Ideal (MvPolynomial (Fin n) ℂ)} (hJP : J ≤ P)
    (Q : Fin m → MvPolynomial (Fin n) ℂ) (z : Fin m → ℂ) {x : Fin n → ℂ}
    (hx : x ∈ isolatedFibrePts J Q z) (hxP : x ∈ zeroSet P) : x ∈ isolatedFibrePts P Q z := by
  obtain ⟨-, hQ, V, hV, hiso⟩ := hx
  exact ⟨hxP, hQ, V, hV, fun x' hx' hQ' => hiso x' ⟨fun q hq => hx'.1 q (hJP hq), hx'.2⟩ hQ'⟩

theorem encard_biUnion_finset_le {ι α : Type*} (S : Finset ι) (f : ι → Set α) :
    (⋃ i ∈ S, f i).encard ≤ ∑ i ∈ S, (f i).encard := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.set_biUnion_insert]
    exact (Set.encard_union_le _ _).trans (add_le_add_right ih _)

theorem IsolatedPointsCount.proof (hPrime : IsolatedPointsCountPrime.Statement) :
    IsolatedPointsCount.Statement := by
  classical
  intro n m J Q
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin n) ℂ) J
  have hN : ∀ P ∈ J.minimalPrimes, ∃ N : ℕ, ∀ z : Fin m → ℂ, (isolatedFibrePts P Q z).encard ≤ N :=
    fun P hP => hPrime n m P hP.1.1 Q
  choose! N hN using hN
  refine ⟨∑ P ∈ hfin.toFinset, N P, fun z => ?_⟩
  have hsub : isolatedFibrePts J Q z ⊆ ⋃ P ∈ hfin.toFinset, isolatedFibrePts P Q z := by
    intro x hx
    obtain ⟨P, hP, hxP⟩ := exists_minimalPrime_mem_zeroSet J hx.1
    exact Set.mem_biUnion (hfin.mem_toFinset.2 hP) (mem_isolatedFibrePts_of_le hP.1.2 Q z hx hxP)
  calc (isolatedFibrePts J Q z).encard
      ≤ (⋃ P ∈ hfin.toFinset, isolatedFibrePts P Q z).encard := Set.encard_le_encard hsub
    _ ≤ ∑ P ∈ hfin.toFinset, (isolatedFibrePts P Q z).encard := encard_biUnion_finset_le _ _
    _ ≤ ∑ P ∈ hfin.toFinset, ((N P : ℕ) : ℕ∞) :=
        Finset.sum_le_sum fun P hP => hN P (hfin.mem_toFinset.1 hP) z
    _ = ((∑ P ∈ hfin.toFinset, N P : ℕ) : ℕ∞) := by push_cast; rfl

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix

noncomputable section

theorem exists_eval_ne_zero_of_isOpen_pi {σ : Type*} [Finite σ] {F : MvPolynomial σ ℂ} (hF : F ≠ 0)
    {S : Set (σ → ℂ)} (hS : IsOpen S) (hne : S.Nonempty) : ∃ y ∈ S, eval y F ≠ 0 := by
  obtain ⟨y₀, hy₀⟩ := hne
  obtain ⟨u, hu, hsub⟩ := isOpen_pi_iff'.mp hS y₀ hy₀
  by_contra h
  push Not at h
  apply hF
  have hinf : ∀ i, (u i).Infinite := fun i =>
    infinite_of_mem_nhds (y₀ i) ((hu i).1.mem_nhds (hu i).2)
  refine (funext_set_iff (p := F) (q := 0) u hinf).mpr fun y hy => ?_
  rw [map_zero]
  exact h y (hsub hy)

theorem SliceReducedAway.proof (hZ : SliceReducedAwayZariski.Statement) :
    SliceReducedAway.Statement := by
  intro n d J q hJ
  obtain ⟨F, hF, hgood⟩ := hZ n d J q hJ
  let e : Matrix (Fin d) (Fin n) ℂ → (Fin d × Fin n → ℂ) := fun L ij => L ij.1 ij.2
  let φ : (Fin d × Fin n → ℂ) → Matrix (Fin d) (Fin n) ℂ := fun y => Matrix.of fun i j => y (i, j)
  have he : Continuous e := continuous_pi fun ij => continuous_id.matrix_elem ij.1 ij.2
  have hφ : Continuous φ :=
    continuous_pi fun i => continuous_pi fun j => continuous_apply (i, j)
  refine ⟨{L | eval (e L) F ≠ 0}, ?_, ?_, fun L hL => hgood L hL⟩
  · exact isOpen_ne_fun ((MvPolynomial.continuous_eval F).comp he) continuous_const
  · rw [dense_iff_inter_open]
    rintro U hU ⟨L₀, hL₀⟩
    obtain ⟨y, hyU, hyF⟩ :=
      exists_eval_ne_zero_of_isOpen_pi hF (hU.preimage hφ) ⟨e L₀, hL₀⟩
    exact ⟨φ y, hyU, hyF⟩

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing RingTheory.Sequence Pointwise

theorem length_le_ringKrullDim_quotient_colon {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (rs : List R) : ∀ {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] (y : M), y ≠ 0 →
      (∀ r ∈ rs, r ∈ maximalIdeal R) → IsWeaklyRegular M rs →
        (rs.length : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ Submodule.colon (⊥ : Submodule R M) {y}) := by
  induction rs with
  | nil =>
    intro M _ _ _ y hy _ _
    have hne : Submodule.colon (⊥ : Submodule R M) {y} ≠ ⊤ := by
      intro h
      have h1 : (1 : R) ∈ Submodule.colon (⊥ : Submodule R M) {y} := h ▸ Submodule.mem_top
      rw [Submodule.mem_colon_singleton, one_smul] at h1
      exact hy ((Submodule.mem_bot R).mp h1)
    have := Ideal.Quotient.nontrivial_iff.mpr hne
    simpa using (ringKrullDim_nonneg_of_nontrivial : 0 ≤ ringKrullDim (R ⧸ _))
  | cons x rs ih =>
    intro M _ _ _ y hy hmem hreg
    have hx : x ∈ maximalIdeal R := hmem x List.mem_cons_self
    have hmem' : ∀ r ∈ rs, r ∈ maximalIdeal R := fun r hr => hmem r (List.mem_cons_of_mem x hr)
    obtain ⟨hxreg, hrs⟩ := (isWeaklyRegular_cons_iff M x rs).mp hreg

    have hspan : Ideal.span {x} ≠ ⊤ := fun h =>
      (maximalIdeal.isMaximal R).ne_top (top_le_iff.mp (h ▸ (Ideal.span_le.mpr (by simpa using hx))))
    have hK := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := M) (Ideal.span {x}) hspan
    have hpow : ∀ k : ℕ, (Ideal.span {x} ^ k • ⊤ : Submodule R M) = x ^ k • ⊤ := fun k => by
      rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul]
    have hex : ∃ n : ℕ, y ∉ (Ideal.span {x} ^ n • ⊤ : Submodule R M) := by
      by_contra! h
      exact hy ((Submodule.mem_bot R).mp (hK ▸ Submodule.mem_iInf _ |>.mpr h))
    classical
    let n := Nat.find hex
    have hn : y ∉ (Ideal.span {x} ^ n • ⊤ : Submodule R M) := Nat.find_spec hex
    have hn0 : n ≠ 0 := by
      intro h0
      apply hn
      rw [h0, pow_zero, Ideal.one_eq_top, Submodule.top_smul]
      exact Submodule.mem_top
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    have hyk : y ∈ (Ideal.span {x} ^ k • ⊤ : Submodule R M) := by
      have := Nat.find_min hex (show k < n by omega)
      simpa using this
    rw [hpow] at hyk hn
    obtain ⟨y₁, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hyk
    have hy₁ : y₁ ∉ (x • ⊤ : Submodule R M) := by
      intro h
      obtain ⟨z, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp h
      apply hn
      rw [hk, smul_smul, ← pow_succ]
      exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top
    have hcolon : Submodule.colon (⊥ : Submodule R M) {x ^ k • y₁} =
        Submodule.colon (⊥ : Submodule R M) {y₁} := by
      ext r
      simp only [Submodule.mem_colon_singleton, Submodule.mem_bot]
      rw [smul_comm]
      constructor
      · intro h
        exact (hxreg.pow k) (show x ^ k • r • y₁ = x ^ k • 0 by rw [h, smul_zero])
      · intro h
        rw [h, smul_zero]
    rw [hcolon]

    set I := Submodule.colon (⊥ : Submodule R M) {y₁} with hI
    set ybar : QuotSMulTop x M := Submodule.Quotient.mk y₁ with hybar
    have hybar0 : ybar ≠ 0 := by
      rw [hybar, Ne, Submodule.Quotient.mk_eq_zero]
      exact hy₁
    have hih := ih ybar hybar0 hmem' hrs

    have hle : I ⊔ Ideal.span {x} ≤ Submodule.colon (⊥ : Submodule R (QuotSMulTop x M)) {ybar} := by
      refine sup_le ?_ ?_
      · intro r hr
        rw [hI, Submodule.mem_colon_singleton, Submodule.mem_bot] at hr
        rw [Submodule.mem_colon_singleton, Submodule.mem_bot, hybar, ← Submodule.Quotient.mk_smul, hr,
          Submodule.Quotient.mk_zero]
      · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Submodule.mem_colon_singleton,
          Submodule.mem_bot, hybar, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
        exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top
    have hd1 : ringKrullDim (R ⧸ Submodule.colon (⊥ : Submodule R (QuotSMulTop x M)) {ybar}) ≤
        ringKrullDim (R ⧸ (I ⊔ Ideal.span {x})) :=
      ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective hle)

    have hnzd : Ideal.Quotient.mk I x ∈ nonZeroDivisors (R ⧸ I) := by
      rw [mem_nonZeroDivisors_iff_right]
      intro z hz
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, hI, Submodule.mem_colon_singleton,
        Submodule.mem_bot, mul_smul, smul_comm] at hz
      rw [Ideal.Quotient.eq_zero_iff_mem, hI, Submodule.mem_colon_singleton, Submodule.mem_bot]
      exact hxreg (show x • r • y₁ = x • 0 by rw [hz, smul_zero])
    have hd2 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hnzd
    have heq : (R ⧸ I) ⧸ Ideal.span {Ideal.Quotient.mk I x} ≃+* R ⧸ (I ⊔ Ideal.span {x}) := by
      have : Ideal.span {Ideal.Quotient.mk I x} = (Ideal.span {x}).map (Ideal.Quotient.mk I) := by
        rw [Ideal.map_span, Set.image_singleton]
      rw [this]
      exact DoubleQuot.quotQuotEquivQuotSup I (Ideal.span {x})
    rw [ringKrullDim_eq_of_ringEquiv heq] at hd2
    calc ((x :: rs).length : WithBot ℕ∞) = (rs.length : WithBot ℕ∞) + 1 := by simp
      _ ≤ ringKrullDim (R ⧸ Submodule.colon (⊥ : Submodule R (QuotSMulTop x M)) {ybar}) + 1 := by
          gcongr
      _ ≤ ringKrullDim (R ⧸ (I ⊔ Ideal.span {x})) + 1 := by gcongr
      _ ≤ ringKrullDim (R ⧸ I) := hd2

theorem ringKrullDim_quotient_eq_of_mem_minimalPrimes {B : Type*} [CommRing B] [IsCohenMacaulayLocalRing B]
    {P : Ideal B} (hP : P ∈ minimalPrimes B) : ringKrullDim (B ⧸ P) = ringKrullDim B := by
  obtain ⟨rs, hm, hreg, hdim⟩ := IsCohenMacaulayLocalRing.exists_isWeaklyRegular (B := B)
  have hann : Module.annihilator B B = ⊥ := Module.annihilator_eq_bot.mpr inferInstance
  have hP' : P ∈ (Module.annihilator B B).minimalPrimes := by
    rw [hann]
    exact hP
  have hA := Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes B B hP'
  obtain ⟨hprime, y, hy⟩ := (isAssociatedPrime_iff.mp hA)
  have hy0 : y ≠ 0 := by
    rintro rfl
    apply hprime.ne_top
    rw [hy, eq_top_iff]
    intro r _
    rw [Submodule.mem_colon_singleton, smul_zero]
    exact Submodule.zero_mem _
  have hD := length_le_ringKrullDim_quotient_colon rs y hy0 hm hreg
  rw [← hy, ← hdim] at hD
  exact le_antisymm (ringKrullDim_le_of_surjective _ Ideal.Quotient.mk_surjective) hD

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def euclBall {n : ℕ} (x : Fin n → ℂ) (ρ : ℝ) : Set (Fin n → ℂ) :=
  {y | Real.sqrt (euclPot (y - x)) < ρ}

theorem mem_euclBall_iff {n : ℕ} (x y : Fin n → ℂ) (ρ : ℝ) :
    y ∈ euclBall x ρ ↔ dist (WithLp.toLp 2 y : EuclideanSpace ℂ (Fin n)) (WithLp.toLp 2 x) < ρ := by
  rw [EuclideanSpace.dist_eq]
  simp [euclBall, euclPot, dist_eq_norm]

theorem mem_euclBall_self {n : ℕ} (x : Fin n → ℂ) {ρ : ℝ} (hρ : 0 < ρ) : x ∈ euclBall x ρ := by
  simp [euclBall, euclPot, hρ]

def RegLelongMono.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (u : Fin n → ℂ) (ε : ℝ) (x : Fin n → ℂ) (r s : ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    0 < ε → 0 < r → r ≤ s →
      s ^ (2 * d) * ∫ y, chartDens J A ((euclBall x r).indicator fun _ => 1)
          (vecCons (logReg u ε) fun _ => euclPot) y ≤
        r ^ (2 * d) * ∫ y, chartDens J A ((euclBall x s).indicator fun _ => 1)
          (vecCons (logReg u ε) fun _ => euclPot) y

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

def CMGeneralPoint.Statement : Prop :=
  ∀ (n : ℕ) (I W : Ideal (MvPolynomial (Fin n) ℂ)), W ∈ I.minimalPrimes →
    ∃ f : MvPolynomial (Fin n) ℂ, f ∉ W ∧ ∀ q ∈ zeroSet W, eval q f ≠ 0 →
      (∀ W' ∈ I.minimalPrimes, q ∈ zeroSet W' → W' = W) ∧ IsCohenMacaulayAt I q

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

def CMHeightOneGeneral.Statement : Prop :=
  ∀ (n : ℕ) (J W : Ideal (MvPolynomial (Fin n) ℂ)) (g : MvPolynomial (Fin n) ℂ),
    J.IsPrime → g ∉ J → W ∈ (J ⊔ Ideal.span {g}).minimalPrimes →
      ∃ f : MvPolynomial (Fin n) ℂ, f ∉ W ∧ ∀ q ∈ zeroSet W, eval q f ≠ 0 → IsCohenMacaulayAt J q

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

def CMLocusOpen.Statement : Prop :=
  ∀ (n : ℕ) (I P : Ideal (MvPolynomial (Fin n) ℂ)) [P.IsPrime], I ≤ P →
    IsCohenMacaulayLocalRing (Localization.AtPrime P ⧸
      I.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime P))) →
    ∃ g : MvPolynomial (Fin n) ℂ, g ∉ P ∧ ∀ (Q : Ideal (MvPolynomial (Fin n) ℂ)) [Q.IsPrime], I ≤ Q → g ∉ Q →
      IsCohenMacaulayLocalRing (Localization.AtPrime Q ⧸
        I.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime Q)))

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing

def CMParameterQuotient.Statement : Prop :=
  ∀ (B : Type) [CommRing B] [IsCohenMacaulayLocalRing B] (d : ℕ) (x : Fin d → B),
    (∀ i, x i ∈ maximalIdeal B) →
    ringKrullDim (B ⧸ Ideal.span (Set.range x)) + (d : WithBot ℕ∞) = ringKrullDim B →
      IsCohenMacaulayLocalRing (B ⧸ Ideal.span (Set.range x))

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial IsLocalRing

def CMQuotientUnmixed.Statement : Prop :=
  ∀ (B : Type) [CommRing B] [IsCohenMacaulayLocalRing B] (d : ℕ) (x : Fin d → B),
    (∀ i, x i ∈ maximalIdeal B) →
    ringKrullDim (B ⧸ Ideal.span (Set.range x)) + (d : WithBot ℕ∞) = ringKrullDim B →
      ∀ p ∈ associatedPrimes B (B ⧸ Ideal.span (Set.range x)),
        p ∈ (Ideal.span (Set.range x)).minimalPrimes ∧
          ringKrullDim (B ⧸ p) = ringKrullDim (B ⧸ Ideal.span (Set.range x))

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing

universe u

def CMRegularElement.Statement : Prop :=
  ∀ (B : Type u) [CommRing B] [IsCohenMacaulayLocalRing B] (y : B), y ∈ maximalIdeal B →
    (∀ p ∈ minimalPrimes B, y ∉ p) →
      y ∈ nonZeroDivisors B ∧ IsCohenMacaulayLocalRing (B ⧸ Ideal.span {y})

end GroundTheory.Heights₂.Heights
end
