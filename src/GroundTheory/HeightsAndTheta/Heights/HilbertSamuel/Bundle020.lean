module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PHilbExactDivide
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle014
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.Order.Interval.Finset.Box
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.SectionModuleEqSpanPow
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle005
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.FieldNumbers

noncomputable section

universe u

theorem ringKrullDim_quot_add_one_le {K : Type*} {ι : K → Type*} {F : Type*} [Field F]
    {P Q : Ideal (MRing ι F)} [P.IsPrime] (hPQ : P ≤ Q)
    {f : MRing ι F} (hfP : f ∉ P) (hfQ : f ∈ Q) :
    ringKrullDim (MRing ι F ⧸ Q) + 1 ≤ ringKrullDim (MRing ι F ⧸ P) := by
  refine ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hPQ)
    (Ideal.Quotient.factor_surjective hPQ) (r := Ideal.Quotient.mk P f) ?_ ?_
  · exact mem_nonZeroDivisors_of_ne_zero (by rwa [ne_eq, Ideal.Quotient.eq_zero_iff_mem])
  · rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact hfQ

theorem le_of_add_one_le_natCast_add_one {x : WithBot ℕ∞} {n : ℕ}
    (h : x + 1 ≤ ((n + 1 : ℕ) : WithBot ℕ∞)) : x ≤ (n : WithBot ℕ∞) := by
  induction x using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe y =>
    induction y using ENat.recTopCoe with
    | top =>
      exfalso
      have h' : (((⊤ : ℕ∞) + 1 : ℕ∞) : WithBot ℕ∞) ≤ (((n + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
        exact_mod_cast h
      rw [top_add, WithBot.coe_le_coe] at h'
      exact absurd h' (by simp)
    | coe m =>
      have h' : (((m + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) ≤ (((n + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
        simpa using h
      have h'' : m + 1 ≤ n + 1 := by exact_mod_cast WithBot.coe_le_coe.mp h'
      have : m ≤ n := by omega
      exact_mod_cast this

theorem colon_span_singleton_eq_of_not_mem {R : Type*} [CommRing R] {q : Ideal R} [q.IsPrime]
    {s : R} (hs : s ∉ q) : q.colon (Ideal.span {s}) = q := by
  ext x
  rw [Submodule.mem_colon_span_singleton, smul_eq_mul]
  constructor
  · intro h
    exact (Ideal.IsPrime.mem_or_mem inferInstance h).resolve_right hs
  · intro h
    exact q.mul_mem_right _ h

theorem HilbertIncrement.closed : HilbertIncrement.Statement.{u} := by
  intro F _ K _ _ ι _ d q b i hq hdim hd hX
  have : q.IsPrime := hq.isPrime
  refine ⟨fun a => ?_, fun W _ hle => ?_⟩
  · have hhom : IsMultiHomog (X ⟨b, i⟩ : MRing ι F) (Pi.single b 1) :=
      isWeightedHomogeneous_X F (blockWeight ι) ⟨b, i⟩
    have h := HilbExactDivide.closed F K ι q hq.multiHomog (Pi.single b 1) (X ⟨b, i⟩) hhom a
    have hcast : (a - fun k => (((Pi.single b 1 : K → ℕ) k : ℕ) : ℤ)) = a - Pi.single b 1 := by
      funext k
      by_cases hk : k = b
      · subst hk
        simp
      · simp [Pi.single_apply, hk]
    rwa [colon_span_singleton_eq_of_not_mem hX, hcast] at h
  · have hXW : (X ⟨b, i⟩ : MRing ι F) ∈ W :=
      hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    have hstep := ringKrullDim_quot_add_one_le (le_sup_left.trans hle) hX hXW
    rw [hdim] at hstep
    have hn : d + Fintype.card K = (d - 1 + Fintype.card K) + 1 := by omega
    rw [hn] at hstep
    exact le_of_add_one_le_natCast_add_one hstep

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open scoped Pointwise

noncomputable section

namespace SectionsRank

theorem sec_eq_span (o : Type*) [CommRing o] {Ω : Type*} [CommRing Ω] [Algebra o Ω] {ι : Type*}
    (x : ι → Ω) (n : ℕ) : sec o x n = Submodule.span o (Set.range x ^ n) := by
  unfold sec
  rw [← MvPolynomial.homogeneousSubmodule_one_pow, Submodule.map_pow,
    MvPolynomial.homogeneousSubmodule_one_eq_span_X, Submodule.map_span, ← Set.range_comp,
    Submodule.span_pow]
  congr 3
  ext i
  simp

theorem exists_int_multiple {ι : Type*} (f : MvPolynomial ι ℚ) :
    ∃ N : ℕ, 0 < N ∧ ∃ p : MvPolynomial ι ℤ, map (Int.castRingHom ℚ) p = (N : ℚ) • f := by
  induction f using MvPolynomial.induction_on with
  | C q =>
    refine ⟨q.den, q.pos, C q.num, ?_⟩
    rw [map_C, smul_eq_C_mul, ← C_mul, Rat.den_mul_eq_num]
    rfl
  | add f g hf hg =>
    obtain ⟨a, ha, p, hp⟩ := hf
    obtain ⟨b, hb, r, hr⟩ := hg
    refine ⟨a * b, Nat.mul_pos ha hb, (b : ℤ) • p + (a : ℤ) • r, ?_⟩
    rw [map_add (f := _), smul_eq_C_mul, smul_eq_C_mul, map_mul, map_mul, hp, hr, map_C, map_C]
    simp only [smul_eq_C_mul, eq_intCast, Int.cast_natCast, Nat.cast_mul, map_mul]
    ring
  | mul_X f i hf =>
    obtain ⟨a, ha, p, hp⟩ := hf
    refine ⟨a, ha, p * X i, ?_⟩
    rw [map_mul, hp, map_X, smul_mul_assoc]

variable {Ω : Type} [Field Ω] [CharZero Ω] {J : Type}

theorem mem_map_coordIdeal_iff [Fintype J] (x : J → Ω) {n : ℕ} {f : MvPolynomial J ℚ}
    (hf : f.IsHomogeneous n) :
    f ∈ (coordIdeal ℤ x).map (MvPolynomial.map (Int.castRingHom ℚ)) ↔ aeval x f = 0 := by
  constructor
  · intro h
    have hle : (coordIdeal ℤ x).map (MvPolynomial.map (Int.castRingHom ℚ)) ≤
        RingHom.ker (aeval x : MvPolynomial J ℚ →ₐ[ℚ] Ω) := by
      rw [Ideal.map_le_iff_le_comap]
      intro p hp
      rw [Ideal.mem_comap, RingHom.mem_ker, ← algebraMap_int_eq]
      change aeval x (MvPolynomial.map (algebraMap ℤ ℚ) p) = 0
      rw [aeval_map_algebraMap]
      exact aeval_eq_zero_of_mem_coordIdeal hp
    exact hle h
  · intro h
    obtain ⟨N, hN, p, hp⟩ := exists_int_multiple f
    have hpn : p.IsHomogeneous n := by
      refine IsHomogeneous.of_map (f := Int.castRingHom ℚ) (RingHom.injective_int _) ?_
      rw [hp]
      exact (mem_homogeneousSubmodule n _).mp
        (Submodule.smul_mem _ _ ((mem_homogeneousSubmodule n f).mpr hf))
    have hp0 : aeval x p = 0 := by
      rw [← aeval_map_algebraMap ℚ, algebraMap_int_eq, hp, map_smul, h, smul_zero]
    have hmem := Ideal.mem_map_of_mem (MvPolynomial.map (Int.castRingHom ℚ))
      (mem_coordIdeal_of_isHomogeneous ℤ x hpn hp0)
    rw [hp, smul_eq_C_mul] at hmem
    have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
    have := Ideal.mul_mem_left _ (C (N : ℚ)⁻¹) hmem
    rwa [← mul_assoc, ← C_mul, inv_mul_cancel₀ hN', C_1, one_mul] at this

theorem finrank_map_eq {K M N N' : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] [AddCommGroup N'] [Module K N'] (V : Submodule K M)
    (f : M →ₗ[K] N) (g : M →ₗ[K] N') (h : ∀ v ∈ V, f v = 0 ↔ g v = 0) :
    Module.finrank K (V.map f) = Module.finrank K (V.map g) := by
  have ef : V.map f = LinearMap.range (f ∘ₗ V.subtype) := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have eg : V.map g = LinearMap.range (g ∘ₗ V.subtype) := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hk : LinearMap.ker (f ∘ₗ V.subtype) = LinearMap.ker (g ∘ₗ V.subtype) := by
    ext v
    simpa using h v v.2
  rw [ef, eg]
  exact ((f ∘ₗ V.subtype).quotKerEquivRange.symm.trans
    ((Submodule.quotEquivOfEq _ _ hk).trans (g ∘ₗ V.subtype).quotKerEquivRange)).finrank_eq

theorem finrank_sec_int [Fintype J] (x : J → Ω) (n : ℕ) :
    Module.finrank ℤ (sec ℤ x n) = Module.finrank ℚ (sec ℚ x n) := by
  have : Module.Finite ℤ (sec ℤ x n) := Module.Finite.iff_fg.mpr (sec_fg x n)
  let b := Module.Free.chooseBasis ℤ (sec ℤ x n)
  let v : Module.Free.ChooseBasisIndex ℤ (sec ℤ x n) → Ω := fun i => (b i : Ω)
  have hli : LinearIndependent ℤ v :=
    b.linearIndependent.map' (sec ℤ x n).subtype (Submodule.ker_subtype _)
  have hliQ : LinearIndependent ℚ v := (LinearIndependent.iff_fractionRing ℤ ℚ).mp hli
  have hspanZ : Submodule.span ℤ (Set.range v) = sec ℤ x n := by
    have : Set.range v = (sec ℤ x n).subtype '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
  have hspanQ : Submodule.span ℚ (Set.range v) = sec ℚ x n := by
    rw [← Submodule.span_span_of_tower ℤ, hspanZ, sec_eq_span ℤ, sec_eq_span ℚ,
      Submodule.span_span_of_tower]
  rw [Module.finrank_eq_card_chooseBasisIndex, ← hspanQ, finrank_span_eq_card hliQ]

end SectionsRank


open SectionsRank in
theorem SectionsRank.proof : SectionsRank.Statement := by
  intro Ω _ _ κ _ x n
  set q := (coordIdeal ℤ x).map (MvPolynomial.map (Int.castRingHom ℚ))
  have hw : GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight (GlobalTheory κ) = fun _ _ => 1 := by
    funext v u
    simp [GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight]
  have hV : weightedHomogeneousSubmodule ℚ (GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight (GlobalTheory κ))
      (fun _ => n) = homogeneousSubmodule (Ix κ) ℚ n := by
    ext f
    rw [mem_weightedHomogeneousSubmodule, mem_homogeneousSubmodule, hw]
    have hwt : ∀ d : Ix κ →₀ ℕ,
        Finsupp.weight (fun _ _ => (1 : ℕ) : Ix κ → Unit → ℕ) d = fun _ => Finsupp.weight 1 d := by
      intro d
      funext u
      simp [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
    simp only [IsHomogeneous, IsWeightedHomogeneous, hwt, funext_iff, forall_const]
  have hg : ∀ m : Unit → ℕ, m = (fun _ => n) →
      GroundTheory.Heights₂.Heights.NumbersDVR.gradedPiece q m =
        (homogeneousSubmodule (Ix κ) ℚ n).map (Ideal.Quotient.mkₐ ℚ q).toLinearMap := by
    rintro m rfl
    unfold GroundTheory.Heights₂.Heights.NumbersDVR.gradedPiece
    rw [hV]
  unfold GroundTheory.Heights₂.Heights.NumbersDVR.hilbFn
  rw [if_pos (fun _ => Int.natCast_nonneg n), hg _ (by funext; simp), finrank_sec_int]
  congr 1
  refine finrank_map_eq _ _ _ fun f hf => ?_
  rw [AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem,
    AlgHom.toLinearMap_apply]
  exact mem_map_coordIdeal_iff x ((mem_homogeneousSubmodule n f).mp hf)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Module Metric
open scoped ENNReal

noncomputable section

namespace MinkowskiCount

section Count

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]


omit [MeasurableSpace V] [BorelSpace V] in
theorem finite_latticePoints (La : Submodule ℤ V) [DiscreteTopology La] (ρ : ℝ) :
    {x : V | x ∈ La ∧ ‖x‖ ≤ ρ}.Finite := by
  have h : {x : V | x ∈ La ∧ ‖x‖ ≤ ρ} = closedBall 0 ρ ∩ (La : Set V) := by
    ext x; simp [and_comm]
  rw [h]
  refine Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete isBounded_closedBall ?_
  rw [← Submodule.coe_toAddSubgroup]
  exact AddSubgroup.isClosed_of_discrete

theorem unitBallVolume_pos (R : ℕ) : 0 < unitBallVolume R :=
  ENNReal.toReal_pos (measure_ball_pos volume _ one_pos).ne' measure_ball_lt_top.ne

theorem volume_ball_one :
    volume (ball (0 : V) 1) = ENNReal.ofReal (unitBallVolume (finrank ℝ V)) := by
  rw [unitBallVolume, ENNReal.ofReal_toReal measure_ball_lt_top.ne,
    ← (stdOrthonormalBasis ℝ V).measurePreserving_repr.measure_preimage
      measurableSet_ball.nullMeasurableSet]
  congr 1
  ext x
  simp

theorem volume_ball_half_le (La : Submodule ℤ V) [DiscreteTopology La] [IsZLattice ℝ La] (ρ : ℝ) {F : Set V}
    (fund : IsAddFundamentalDomain La F volume) :
    volume (ball (0 : V) (ρ / 2)) ≤
      ({x : V | x ∈ La ∧ ‖x‖ ≤ ρ}.ncard : ℝ≥0∞) * volume F := by
  have : MeasurableVAdd La V := (inferInstance : MeasurableVAdd La.toAddSubgroup V)
  have : VAddInvariantMeasure La V volume :=
    (inferInstance : VAddInvariantMeasure La.toAddSubgroup V volume)
  have : Countable La := inferInstance
  set S := ball (0 : V) (ρ / 2) with hSdef
  set A := {x : V | x ∈ La ∧ ‖x‖ ≤ ρ} with hAdef
  have hS : MeasurableSet S := measurableSet_ball
  have key : ∀ y : V, ∑' g : La, S.indicator (1 : V → ℝ≥0∞) (g +ᵥ y) ≤ (A.ncard : ℝ≥0∞) := by
    intro y
    set T : Set La := {g | (g : V) + y ∈ S} with hTdef
    have h1 : ∑' g : La, S.indicator (1 : V → ℝ≥0∞) (g +ᵥ y) =
        ∑' g : La, T.indicator (1 : La → ℝ≥0∞) g := by
      congr 1
    rw [h1, ← tsum_subtype]
    simp only [Pi.one_apply]
    rw [ENNReal.tsum_set_one]
    have hA : (A.ncard : ℝ≥0∞) = ((A.encard : ℕ∞) : ℝ≥0∞) := by
      rw [← (finite_latticePoints La ρ).cast_ncard_eq]; rfl
    rw [hA]
    refine ENat.toENNReal_le.mpr ?_
    rcases T.eq_empty_or_nonempty with hT | ⟨g₀, hg₀⟩
    · simp [hT]
    refine Set.encard_le_encard_of_injOn (f := fun g : La => (g : V) - g₀) ?_ ?_
    · intro g hg
      refine ⟨La.sub_mem g.2 g₀.2, ?_⟩
      have hg' : ‖(g : V) + y‖ < ρ / 2 := by simpa [T, S] using hg
      have hg₀' : ‖(g₀ : V) + y‖ < ρ / 2 := by simpa [T, S] using hg₀
      have : (g : V) - g₀ = ((g : V) + y) - ((g₀ : V) + y) := by abel
      show ‖(g : V) - g₀‖ ≤ ρ
      rw [this]
      linarith [norm_sub_le ((g : V) + y) ((g₀ : V) + y)]
    · intro g _ g' _ h
      exact Subtype.ext (sub_left_injective h)
  calc volume S = ∫⁻ z, S.indicator 1 z := (lintegral_indicator_one hS).symm
    _ = ∑' g : La, ∫⁻ z in F, S.indicator 1 (g +ᵥ z) := fund.lintegral_eq_tsum'' _
    _ = ∫⁻ z in F, ∑' g : La, S.indicator 1 (g +ᵥ z) :=
        (lintegral_tsum fun g => ((measurable_one.indicator hS).comp
          (measurable_const_vadd g)).aemeasurable).symm
    _ ≤ ∫⁻ _ in F, (A.ncard : ℝ≥0∞) := lintegral_mono fun z => key z
    _ = A.ncard * volume F := setLIntegral_const _ _

theorem log_count (La : Submodule ℤ V) [DiscreteTopology La] [IsZLattice ℝ La] (ρ : ℝ)
    (hρ : 0 < ρ) :
    Real.log (unitBallVolume (finrank ℝ V)) + (finrank ℝ V : ℝ) * Real.log (ρ / 2) -
        Real.log (ZLattice.covolume La) ≤
      Real.log ({x : V | x ∈ La ∧ ‖x‖ ≤ ρ}.ncard : ℝ) := by
  set b := Module.Free.chooseBasis ℤ La
  have fund := ZLattice.isAddFundamentalDomain b (volume : Measure V)
  have hcov := ZLattice.covolume_eq_measure_fundamentalDomain La volume fund
  have hFtop : volume (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)) ≠ ⊤ :=
    (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne
  have hle := volume_ball_half_le La ρ fund
  rw [Measure.addHaar_ball_of_pos volume 0 (half_pos hρ), volume_ball_one] at hle
  have hle' := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hFtop) hle
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (unitBallVolume_pos _).le, ENNReal.toReal_natCast, ← measureReal_def,
    ← hcov] at hle'
  have hcpos := ZLattice.covolume_pos La volume
  have hN : 0 < ({x : V | x ∈ La ∧ ‖x‖ ≤ ρ}.ncard : ℝ) := by
    have : 0 < {x : V | x ∈ La ∧ ‖x‖ ≤ ρ}.ncard :=
      (Set.ncard_pos (finite_latticePoints La ρ)).mpr ⟨0, La.zero_mem, by simp [hρ.le]⟩
    exact_mod_cast this
  have hdiv : (ρ / 2) ^ finrank ℝ V * unitBallVolume (finrank ℝ V) / ZLattice.covolume La ≤
      ({x : V | x ∈ La ∧ ‖x‖ ≤ ρ}.ncard : ℝ) := (div_le_iff₀ hcpos).mpr hle'
  have hlog := Real.log_le_log (by have := unitBallVolume_pos (finrank ℝ V); positivity) hdiv
  rw [Real.log_div (by have := unitBallVolume_pos (finrank ℝ V); positivity) hcpos.ne',
    Real.log_mul (by positivity) (unitBallVolume_pos _).ne', Real.log_pow] at hlog
  linarith

end Count

theorem cube_le_unitBallVolume (R : ℕ) : (2 / Real.sqrt R) ^ R ≤ unitBallVolume R := by
  set a := 1 / Real.sqrt R with ha_def
  have ha : 0 ≤ a := by positivity
  have hsub : (WithLp.ofLp : EuclideanSpace ℝ (Fin R) → Fin R → ℝ) ⁻¹'
      (Set.univ.pi fun _ => Set.Ioo (-a) a) ⊆ ball 0 1 := by
    intro x hx
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_Ioo] at hx
    rw [mem_ball_zero_iff, EuclideanSpace.norm_eq, Real.sqrt_lt' one_pos, one_pow]
    rcases Nat.eq_zero_or_pos R with rfl | hR
    · simp
    · calc ∑ i, ‖x i‖ ^ 2 < ∑ _i : Fin R, a ^ 2 :=
            Finset.sum_lt_sum_of_nonempty ⟨⟨0, hR⟩, Finset.mem_univ _⟩ fun i _ => by
              rw [Real.norm_eq_abs, sq_abs]
              exact sq_lt_sq' (hx i).1 (hx i).2
        _ = 1 := by
          have hR' : (0 : ℝ) < R := by exact_mod_cast hR
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ha_def,
            div_pow, one_pow, Real.sq_sqrt hR'.le]
          field_simp
  have hvol := measure_mono (μ := volume) hsub
  rw [(PiLp.volume_preserving_ofLp (Fin R)).measure_preimage
    (MeasurableSet.univ_pi fun _ => measurableSet_Ioo).nullMeasurableSet, Real.volume_pi_Ioo]
    at hvol
  simp only [sub_neg_eq_add, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hvol
  have h := ENNReal.toReal_mono measure_ball_lt_top.ne hvol
  rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity)] at h
  have h2 : 2 / Real.sqrt R = a + a := by rw [ha_def]; ring
  rw [h2]
  exact h

theorem proof : MinkowskiCount.Statement :=
  ⟨fun _ _ _ _ _ _ La _ _ ρ hρ => log_count La ρ hρ, cube_le_unitBallVolume⟩

end MinkowskiCount

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Filter Topology

theorem L1Convergence.proof : L1Convergence.Statement := by
  intro Ω _ μ _ g b C hg hb hC hlim hint

  have hp_int : ∀ n, Integrable (fun x => max (g n x - b x) 0) μ :=
    fun n => ((hg n).sub hb).pos_part
  have hbound_int : Integrable (fun x => C + |b x|) μ := (integrable_const C).add hb.abs
  have hpt : Tendsto (fun n => ∫ x, max (g n x - b x) 0 ∂μ) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (μ := μ)
      (F := fun n x => max (g n x - b x) 0) (f := fun _ => (0 : ℝ)) (fun x => C + |b x|)
      (fun n => (hp_int n).aestronglyMeasurable) hbound_int
      (fun n => Filter.Eventually.of_forall fun x => by
        have h1 := hC n x
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
        exact max_le (by linarith [neg_abs_le (b x)]) (by linarith [abs_nonneg (b x)]))
      (Filter.Eventually.of_forall fun x => by
        refine tendsto_order.2 ⟨fun a ha => Filter.Eventually.of_forall fun n =>
          lt_of_lt_of_le ha (le_max_right _ _), fun a ha => ?_⟩
        filter_upwards [hlim x (a / 2) (by linarith)] with n hn
        exact lt_of_le_of_lt (max_le (show g n x - b x ≤ a / 2 by linarith)
          (show (0 : ℝ) ≤ a / 2 by linarith)) (by linarith))
    simpa using h

  have hid : ∀ n, ∫ x, |g n x - b x| ∂μ =
      2 * ∫ x, max (g n x - b x) 0 ∂μ - (∫ x, g n x ∂μ - ∫ x, b x ∂μ) := by
    intro n
    have hpt' : ∀ x, |g n x - b x| = 2 * max (g n x - b x) 0 - (g n x - b x) := by
      intro x
      rcases le_total 0 (g n x - b x) with h | h
      · rw [abs_of_nonneg h, max_eq_left h]; ring
      · rw [abs_of_nonpos h, max_eq_right h]; ring
    simp_rw [hpt']
    have hgb : Integrable (fun x => g n x - b x) μ := (hg n).sub hb
    rw [integral_sub ((hp_int n).const_mul 2) hgb, integral_const_mul,
      integral_sub (hg n) hb]
  refine tendsto_order.2 ⟨fun a ha => Filter.Eventually.of_forall fun n =>
    lt_of_lt_of_le ha (integral_nonneg fun x => abs_nonneg _), fun a ha => ?_⟩
  filter_upwards [(tendsto_order.1 hpt).2 (a / 4) (by linarith), hint (a / 4) (by linarith)]
    with n hn1 hn2
  rw [hid n]
  linarith

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
