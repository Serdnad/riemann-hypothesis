module

public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle068
public import GroundTheory.ArithmeticGeometry.ToricVarieties.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle001
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.RingTheory.Valuation.LocalSubring
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

theorem isFractionRing_of_subalgebra {A K : Type*} [CommRing A] [IsDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K] (B : Subalgebra A K) : IsFractionRing B K := by
  rw [IsFractionRing, isLocalization_iff]
  refine ⟨fun y => ?_, fun z => ?_, fun {u v} h => ⟨1, ?_⟩⟩
  · have hy : (y : B) ≠ 0 := nonZeroDivisors.coe_ne_zero y
    exact isUnit_iff_ne_zero.2 fun h => hy (Subtype.ext h)
  · obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj (nonZeroDivisors A) z
    have hs : algebraMap A B s ≠ 0 := fun h0 =>
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2 (congrArg Subtype.val h0)
    exact ⟨⟨algebraMap A B a, ⟨_, mem_nonZeroDivisors_of_ne_zero hs⟩⟩, h⟩
  · simpa using Subtype.ext h



theorem DominatingDVR.proof (hKA : KrullAkizuki.Statement) (hBU : BlowUpChart.Statement) :
    DominatingDVR.Statement := by
  intro A _ _ _ _ hAf K _ _ _

  obtain ⟨n, x, hx⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian (IsLocalRing.maximalIdeal A))
  have hx' : Ideal.span (Set.range x) = IsLocalRing.maximalIdeal A := hx
  have hx0 : ∃ j, x j ≠ 0 := by
    by_contra h
    push Not at h
    apply hAf
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, ← hx']
    exact Submodule.span_eq_bot.mpr (by rintro _ ⟨j, rfl⟩; exact h j)
  obtain ⟨i, hxi, hunit, -⟩ := hBU A K n x hx' hx0

  set B := blowUpChart K x i
  have : IsNoetherianRing B :=
    isNoetherianRing_of_fg (Subalgebra.fg_def.2 ⟨_, Set.finite_range _, rfl⟩)
  have : IsFractionRing B K := isFractionRing_of_subalgebra B

  set xi : B := algebraMap A B (x i)
  have hspan : Ideal.span {xi} ≠ ⊤ := fun h => hunit (Ideal.span_singleton_eq_top.mp h)
  obtain ⟨q, hq⟩ := Ideal.nonempty_minimalPrimes hspan
  have : q.IsPrime := hq.1.1
  have hxiq : xi ∈ q := hq.1.2 (Ideal.mem_span_singleton_self _)
  have hxi0 : xi ≠ 0 := fun h => hxi (IsFractionRing.injective A K (by
    simpa [xi] using congrArg Subtype.val h))
  have hq1 : q.height = 1 := le_antisymm
    (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ q hq)
    ((Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hxi0)).trans (Ideal.height_mono hq.1.2))
  have hmq : (IsLocalRing.maximalIdeal A).map (algebraMap A B) ≤ q := by
    rw [← hx', Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    have e : algebraMap A B (x j) =
        ⟨algebraMap A K (x j) / algebraMap A K (x i), Algebra.subset_adjoin ⟨j, rfl⟩⟩ * xi := by
      apply Subtype.ext
      have : algebraMap A K (x i) ≠ 0 := fun h => hxi (IsFractionRing.injective A K (by simpa using h))
      simp [xi, div_mul_cancel₀ _ this]
    exact e ▸ q.mul_mem_left _ hxiq

  set R := Localization.subalgebra.ofField K q.primeCompl q.primeCompl_le_nonZeroDivisors
  have : IsLocalization.AtPrime R q := (inferInstance : IsLocalization q.primeCompl R)
  have : IsLocalRing R := IsLocalization.AtPrime.isLocalRing R q
  have : IsNoetherianRing R := IsLocalization.isNoetherianRing q.primeCompl R inferInstance
  have hdimR : ringKrullDim R = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q R, hq1]
    rfl

  set C := integralClosure R K
  have : IsDedekindDomain C := hKA.2 R hdimR K
  have : IsFractionRing C K := isFractionRing_of_subalgebra C
  have hinj : Function.Injective (algebraMap R C) := fun a b h =>
    by
    have h' : ((algebraMap R C a : C) : K) = ((algebraMap R C b : C) : K) := congrArg _ h
    exact IsFractionRing.injective R K h'
  obtain ⟨P, hPmax, hPc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := C)
    (IsLocalRing.maximalIdeal R) (by rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]; exact bot_le)
  have : P.IsPrime := hPmax.isPrime
  have hPbot : P ≠ ⊥ := by
    rintro rfl
    have hF : IsField R := by
      rw [IsLocalRing.isField_iff_maximalIdeal_eq, ← hPc, Ideal.under_def, Ideal.comap_bot_of_injective _ hinj]
    have h0 := ringKrullDim_eq_zero_of_isField hF
    rw [hdimR] at h0
    exact one_ne_zero h0

  set V := Localization.subalgebra.ofField K P.primeCompl P.primeCompl_le_nonZeroDivisors
  letI : CommRing V := Subalgebra.toCommRing (R := C) (A := K) V
  have : IsDomain V := Subalgebra.isDomain (R := C) (A := K) V
  have : IsLocalization.AtPrime V P := (inferInstance : IsLocalization P.primeCompl V)
  have hV : IsDiscreteValuationRing V :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain C hPbot V
  let φ : A →+* V :=
    (algebraMap C V).comp ((algebraMap R C).comp ((algebraMap B R).comp (algebraMap A B)))
  have hφ : ∀ a, (φ a : K) = algebraMap A K a := fun a => rfl
  refine ⟨Subalgebra.toSubring (R := C) V, hV, fun a => ?_, fun a => ?_⟩
  · show algebraMap A K a ∈ V
    exact hφ a ▸ (φ a).2
  show ¬ IsUnit (φ a) ↔ _
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  refine ⟨fun h ha => h (ha.map φ), fun ha hu => ?_⟩
  have hb : algebraMap A B a ∈ q := hmq (Ideal.mem_map_of_mem _ (by
    rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]))
  have hr : algebraMap B R (algebraMap A B a) ∈ IsLocalRing.maximalIdeal R :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff R q _).mpr hb
  rw [← hPc, Ideal.mem_comap] at hr
  exact (IsLocalization.AtPrime.isUnit_to_map_iff V P _).mp hu hr

end GroundTheory.Heights₂.Heights.Model
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

theorem primeWeight_nonneg {p : ℕ} (hp : p.Prime) : 0 ≤ primeWeight p := by
  unfold primeWeight
  split_ifs
  · norm_num
  · have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    exact div_nonneg zero_le_one (by linarith)

theorem primeWeight_le {p : ℕ} (hp : p.Prime) : primeWeight p ≤ 4 / p := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  unfold primeWeight
  split_ifs with h
  · subst h; norm_num
  · rw [div_le_div_iff₀ (by linarith) (by linarith)]
    linarith

theorem SumCp.proof (hM : MertensUpper.Statement) : SumCp.Statement := by
  obtain ⟨CM, hCM⟩ := hM
  intro d hd
  set T := d.natAbs.primeFactors with hT
  set K1 : ℝ := ∑ p ∈ T, primeWeight p * Real.log p
  set K2 : ℝ := ∑ p ∈ T, 2 * (padicValInt p d : ℝ) * Real.log p
  set A : ℝ := |4 * CM + K1 + K2|
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨4 + A / Real.log 2, fun B hB S hS => ?_⟩
  set P := (Finset.Iic ⌊B⌋₊).filter Nat.Prime
  have hlogB : Real.log 2 ≤ Real.log B := Real.log_le_log (by norm_num) hB
  have hlog : ∀ p : ℕ, p.Prime → 0 ≤ Real.log p := fun p hp =>
    Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hTprime : ∀ p ∈ T, p.Prime := fun p hp => (Nat.mem_primeFactors.mp hp).1
  have hPprime : ∀ p ∈ P, p.Prime := fun p hp => (Finset.mem_filter.mp hp).2
  have hSsub : S ⊆ P ∪ T := by
    intro p hp
    obtain ⟨hpp, hpB | hpd⟩ := hS p hp
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
        ⟨Finset.mem_Iic.mpr (Nat.le_floor hpB), hpp⟩)
    · exact Finset.mem_union_right _ (Nat.mem_primeFactors.mpr
        ⟨hpp, Int.natCast_dvd.mp hpd, Int.natAbs_ne_zero.mpr hd⟩)

  have hW : ∑ p ∈ S, primeWeight p * Real.log p ≤ 4 * (Real.log B + CM) + K1 := by
    have hnn : ∀ p ∈ P ∪ T, 0 ≤ primeWeight p * Real.log p := by
      intro p hp
      have hpp : p.Prime := (Finset.mem_union.mp hp).elim (hPprime p) (hTprime p)
      exact mul_nonneg (primeWeight_nonneg hpp) (hlog p hpp)
    calc ∑ p ∈ S, primeWeight p * Real.log p
        ≤ ∑ p ∈ P ∪ T, primeWeight p * Real.log p :=
          Finset.sum_le_sum_of_subset_of_nonneg hSsub (fun p hp _ => hnn p hp)
      _ ≤ ∑ p ∈ P, primeWeight p * Real.log p + K1 := by
          rw [← Finset.sum_union_inter]
          have : 0 ≤ ∑ p ∈ P ∩ T, primeWeight p * Real.log p :=
            Finset.sum_nonneg fun p hp => hnn p (Finset.mem_union_left _ (Finset.mem_inter.mp hp).1)
          linarith
      _ ≤ ∑ p ∈ P, 4 * (Real.log p / p) + K1 := by
          have hsum : ∑ p ∈ P, primeWeight p * Real.log p ≤ ∑ p ∈ P, 4 * (Real.log p / p) := by
            refine Finset.sum_le_sum fun p hp => ?_
            have hpp := hPprime p hp
            have hw := mul_le_mul_of_nonneg_right (primeWeight_le hpp) (hlog p hpp)
            calc primeWeight p * Real.log p ≤ 4 / p * Real.log p := hw
              _ = 4 * (Real.log p / p) := by ring
          linarith
      _ ≤ 4 * (Real.log B + CM) + K1 := by
          rw [← Finset.mul_sum]
          linarith [hCM B hB]

  have hV : ∑ p ∈ S, 2 * (padicValInt p d : ℝ) * Real.log p ≤ K2 := by
    rw [← Finset.sum_filter_of_ne (p := fun p => p ∈ T)]
    · apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp; exact (Finset.mem_filter.mp hp).2
      · intro p hp _
        exact mul_nonneg (by positivity) (hlog p (hTprime p hp))
    · intro p hp hne
      by_contra hpT
      apply hne
      have hpp := (hS p hp).1
      have hnd : ¬ (p : ℤ) ∣ d := fun hpd => hpT (Nat.mem_primeFactors.mpr
        ⟨hpp, Int.natCast_dvd.mp hpd, Int.natAbs_ne_zero.mpr hd⟩)
      rw [padicValInt.eq_zero_of_not_dvd hnd]
      simp
  have hsplit : ∑ p ∈ S, (primeWeight p + 2 * padicValInt p d) * Real.log p
      = ∑ p ∈ S, primeWeight p * Real.log p + ∑ p ∈ S, 2 * (padicValInt p d : ℝ) * Real.log p := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  have hA : 4 * CM + K1 + K2 ≤ A := le_abs_self _
  have hA0 : 0 ≤ A := abs_nonneg _
  have habs : A ≤ A / Real.log 2 * Real.log B := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
    exact mul_le_mul_of_nonneg_left hlogB hA0
  rw [hsplit]
  nlinarith [hW, hV, hA, habs]

end GroundTheory.Heights₂.Heights.Model
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open IsLocalRing

theorem BlowUpChart.proof : BlowUpChart.Statement := by
  intro A _ _ _ _ K _ _ _ n x hx ⟨j, hj⟩
  obtain ⟨V, hV, hloc⟩ := IsLocalRing.exists_factor_valuationRing (algebraMap A K)
  set f := (algebraMap A K).codRestrict V.toSubring hV with hf
  have : Nonempty (Fin n) := ⟨j⟩
  obtain ⟨i, hi⟩ := Finite.exists_max fun k => V.valuation (algebraMap A K (x k))
  have hinj := IsFractionRing.injective A K
  have hxi : x i ≠ 0 := by
    intro h0
    apply hj
    have h1 := hi j
    rw [h0, map_zero, map_zero, le_zero_iff, Valuation.zero_iff] at h1
    exact hinj (by rw [h1, map_zero])
  have hvi : 0 < V.valuation (algebraMap A K (x i)) := by
    rw [zero_lt_iff, Valuation.ne_zero_iff]
    exact fun h => hxi (hinj (by rw [h, map_zero]))
  have hle : ∀ y ∈ blowUpChart K x i, y ∈ V := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨k, rfl⟩ := hy
      rw [← V.valuation_le_one_iff, map_div₀, div_le_one₀ hvi]
      exact hi k
    | algebraMap r => exact hV r
    | add _ _ _ _ h₁ h₂ => exact add_mem h₁ h₂
    | mul _ _ _ _ h₁ h₂ => exact mul_mem h₁ h₂
  let φ : blowUpChart K x i →+* V :=
    { toFun := fun y => ⟨y.1, hle y.1 y.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hφ : ∀ a : A, φ (algebraMap A (blowUpChart K x i) a) = f a := fun _ => rfl
  have hxm : x i ∈ maximalIdeal A := hx ▸ Ideal.subset_span ⟨i, rfl⟩
  have hnu : ¬ IsUnit (f (x i)) := by
    rw [isUnit_map_iff f]
    exact hxm
  refine ⟨i, hxi, fun hu => hnu (hφ (x i) ▸ hu.map φ), (maximalIdeal V).comap φ,
    Ideal.comap_isPrime _ _, ?_, ?_⟩
  · rw [Ideal.mem_comap, hφ]
    exact hnu
  · ext a
    rw [Ideal.mem_comap, Ideal.mem_comap, hφ, mem_maximalIdeal, mem_nonunits_iff,
      mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff f]

end GroundTheory.Heights₂.Heights.Model
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

variable {A : Type} [CommRing A] [IsDomain A]
  {K : Type} [Field K] [Algebra A K] [IsFractionRing A K]
  {V : Type} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]

theorem exists_ne_zero_smul_mem_of_span_eq_top (M : Submodule A V)
    (hM : Submodule.span K (M : Set V) = ⊤) (v : V) : ∃ d : A, d ≠ 0 ∧ d • v ∈ M :=
  _root_.UpperTheory.Reformulated.B.SmulMemOfSpanEqTop.exists_ne_zero_smul_mem_of_span_eq_top M hM v

theorem mem_of_forall_mem_localizedIn (hHOI : HeightOneIntersection.Statement)
    [IsNoetherianRing A] [IsIntegrallyClosed A] (M : Submodule A V) [Module.Projective A M]
    (hM : Submodule.span K (M : Set V) = ⊤) (v : V)
    (hv : ∀ p : PrimeSpectrum A, p.asIdeal.height = 1 → v ∈ localizedIn p.asIdeal M) : v ∈ M := by
  obtain ⟨d, hd, hdv⟩ := exists_ne_zero_smul_mem_of_span_eq_top (K := K) M hM v
  obtain ⟨c, hc⟩ := Module.projective_def.mp (inferInstance : Module.Projective A M)
  set x : M := ⟨d • v, hdv⟩ with hx
  have hdK : algebraMap A K d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hd

  have hdiv : ∀ y : M, ∃ a : A, c x y = d * a := by
    intro y
    have hq : algebraMap A K (c x y) / algebraMap A K d ∈
        Subalgebra.toSubmodule (⊥ : Subalgebra A K) := by
      rw [hHOI A K]
      simp only [Submodule.mem_iInf]
      intro p hp
      obtain ⟨s, hs, hsv⟩ := hv p hp
      refine ⟨s, hs, ?_⟩
      set x' : M := ⟨s • v, hsv⟩
      have hxx : d • x' = s • x := by
        ext; simp only [x', hx, SetLike.val_smul, smul_smul, mul_comm]
      have hcc : d * c x' y = s * c x y := by
        have := congrArg (fun z => c z y) hxx
        simpa [map_smul] using this
      refine Algebra.mem_bot.mpr ⟨c x' y, ?_⟩
      rw [Algebra.smul_def, ← mul_div_assoc, ← map_mul, ← hcc, map_mul,
        mul_div_right_comm, div_self hdK, one_mul]
    obtain ⟨a, ha⟩ := Algebra.mem_bot.mp hq
    refine ⟨a, IsFractionRing.injective A K ?_⟩
    rw [map_mul, ha, mul_div_cancel₀ _ hdK]
  choose a ha using hdiv
  have hw : (∑ y ∈ (c x).support, a y • (y : V)) ∈ M :=
    M.sum_mem fun y _ => M.smul_mem (a y) y.2
  have hsum : d • v = d • ∑ y ∈ (c x).support, a y • (y : V) := by
    have h1 : ((Finsupp.linearCombination A id (c x) : M) : V) = d • v := by rw [hc x]
    rw [← h1, Finsupp.linearCombination_apply, Finsupp.sum, Submodule.coe_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Submodule.coe_smul, id, ha y, mul_smul]
  have hvw : v = ∑ y ∈ (c x).support, a y • (y : V) := by
    rw [← algebraMap_smul K d v, ← algebraMap_smul K d (∑ y ∈ (c x).support, a y • (y : V))]
      at hsum
    exact smul_right_injective V hdK hsum
  rw [hvw]
  exact hw

theorem LatticesAgree.proof (hHOI : HeightOneIntersection.Statement) : LatticesAgree.Statement := by
  intro A _ _ _ _ K _ _ _ V _ _ _ _ _ M N _ hMp _ hNp hM hN hMN
  have sub : ∀ (P Q : Submodule A V), Module.Projective A P →
      Submodule.span K (P : Set V) = ⊤ →
      (∀ p : PrimeSpectrum A, p.asIdeal.height = 1 →
        localizedIn p.asIdeal Q = localizedIn p.asIdeal P) → Q ≤ P := by
    intro P Q hP hPs hQP v hvQ
    exact mem_of_forall_mem_localizedIn (K := K) hHOI P hPs v fun p hp =>
      hQP p hp ▸ ⟨1, fun h => p.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simpa using hvQ⟩
  exact le_antisymm (sub N M hNp hN fun p hp => hMN p hp)
    (sub M N hMp hM fun p hp => (hMN p hp).symm)

end GroundTheory.Heights₂.Heights.Model
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

theorem HeightOneIntersection.proof : HeightOneIntersection.Statement := by
  intro A _ _ _ _ K _ _ _
  apply le_antisymm
  · intro x hx
    simp only [Submodule.mem_iInf]
    intro p _
    exact ⟨1, (Ideal.ne_top_iff_one _).mp p.isPrime.ne_top, by rwa [one_smul]⟩
  · intro x hx
    simp only [Submodule.mem_iInf] at hx
    change x ∈ (⊥ : Subalgebra A K)
    rw [Algebra.mem_bot]
    obtain ⟨y, hy⟩ := GroundTheory.Arith.Toric.mem_range_of_forall_height_one (A := A) (K := K) x
      (fun p hp h1 => by
        obtain ⟨s, hs, hsx⟩ := hx ⟨p, hp⟩ h1
        change s • x ∈ (⊥ : Subalgebra A K) at hsx
        obtain ⟨a, ha⟩ := Algebra.mem_bot.mp hsx
        refine ⟨a, s, hs, ?_⟩
        rw [Algebra.smul_def] at ha
        rw [ha, mul_comm])
    exact ⟨y, hy⟩

end GroundTheory.Heights₂.Heights.Model
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

namespace KrullAkizuki

theorem noetherian_and_dimensionLEOne
    {R : Type} [CommRing R] [IsDomain R]
    {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
    {L : Type} [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra R L]
    [IsScalarTower R K L] (S : Subalgebra R L)
    (h : ∀ b : R, b ≠ 0 → IsFiniteLength R (S ⧸ Ideal.span {algebraMap R S b})) :
    IsNoetherianRing S ∧ Ring.DimensionLEOne S := by

  have hmeet : ∀ I : Ideal S, I ≠ ⊥ → ∃ b : R, b ≠ 0 ∧ algebraMap R S b ∈ I := by
    intro I hI
    obtain ⟨x, hxI, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    have halg : Algebra.IsAlgebraic R L :=
      (IsFractionRing.comap_isAlgebraic_iff (K := K)).mpr inferInstance
    have hx : IsAlgebraic R x :=
      Subalgebra.isAlgebraic_iff_isAlgebraic_val.mpr (halg.isAlgebraic _)
    obtain ⟨b, hb, hb0⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (Ideal.comap_ne_bot_of_algebraic_mem hx0 hxI hx)
    exact ⟨b, hb0, hb⟩
  refine ⟨(isNoetherianRing_iff_ideal_fg S).mpr fun I => ?_, ⟨fun {P} hP0 hP => ?_⟩⟩
  · rcases eq_or_ne I ⊥ with rfl | hI
    · exact Submodule.fg_bot
    obtain ⟨b, hb0, hbI⟩ := hmeet I hI
    have : IsNoetherian R (S ⧸ Ideal.span {algebraMap R S b}) :=
      (isFiniteLength_iff_isNoetherian_isArtinian.mp (h b hb0)).1
    have : IsNoetherian S (S ⧸ Ideal.span {algebraMap R S b}) :=
      isNoetherian_of_tower R inferInstance
    refine Submodule.fg_of_fg_map_of_fg_inf_ker (Ideal.span {algebraMap R S b}).mkQ
      (IsNoetherian.noetherian _) ?_
    rw [Submodule.ker_mkQ, inf_eq_right.mpr ((Ideal.span_singleton_le_iff_mem I).mpr hbI)]
    exact Submodule.fg_span_singleton _
  · obtain ⟨b, hb0, hbP⟩ := hmeet P hP0
    have hle : Ideal.span {algebraMap R S b} ≤ P := (Ideal.span_singleton_le_iff_mem P).mpr hbP
    have hfl : IsFiniteLength R (S ⧸ P) :=
      (h b hb0).of_surjective (f := (Ideal.Quotient.factorₐ R hle).toLinearMap)
        (Ideal.Quotient.factor_surjective hle)
    have : IsArtinian R (S ⧸ P) := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfl).2
    have : IsArtinianRing (S ⧸ P) := isArtinian_of_tower R inferInstance
    have : IsDomain (S ⧸ P) := Ideal.Quotient.isDomain P
    exact Ideal.Quotient.maximal_of_isField P (IsArtinianRing.isField_of_isDomain _)

theorem proof (h : KrullAkizukiQuotientLength.Statement) : KrullAkizuki.Statement := by
  refine ⟨fun R _ _ _ hR K _ _ _ L _ _ _ _ _ S => ?_, fun R _ _ _ hR K _ _ _ => ?_⟩
  · obtain ⟨h₁, h₂⟩ := noetherian_and_dimensionLEOne (K := K) S (h R hR K L S)
    refine ⟨h₁, ?_⟩
    have := (Ring.krullDimLE_iff (R := S) (n := 1)).mp inferInstance
    exact_mod_cast this
  · obtain ⟨h₁, h₂⟩ :=
      noetherian_and_dimensionLEOne (K := K) (L := K) (integralClosure R K) (h R hR K K _)
    have : IsIntegrallyClosed (integralClosure R K) :=
      integralClosure.isIntegrallyClosedOfFiniteExtension (R := R) K (L := K)
    exact { }

end KrullAkizuki

end GroundTheory.Heights₂.Heights.Model
end
