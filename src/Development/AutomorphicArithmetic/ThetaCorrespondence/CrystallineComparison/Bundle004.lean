module

public import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Comparison
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.EqZeroOfPMulEqZero
public import Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.Bundle003
public import Development.WeilBound.CoreStatements.PeriodRingComparison.RationalRingEquivalences.IsLogCore
public import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.DeRham
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace Formalism.BasicNotions.CmpTie.Incl

open Reformulated.AutPerF Ideal

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [Fact ¬IsUnit (p : R)]
  [IsAdicComplete (span {(p : R)}) R] [IsDomain R] [ValuationRing R] [CharZero R]
  [IsAlgClosed (FractionRing R)]

structure IsCrisDRF (f : Bcris p R →+* BdR p R) : Prop where
  on0 : ∀ a : AcrisZero p R, f (algebraMap (Acris p R) (Bcris p R) (algebraMap (AcrisZero p R) (Acris p R) a)) =
    algebraMap (BdRPlus p R) (BdR p R) (algebraMap (AinfInv p R) (BdRPlus p R) (a : AinfInv p R))
  bdd : ∀ n : ℕ, ∃ N : ℕ, ∀ x : Acris p R, ∃ (y : BdRPlus p R) (a : Ainf p R),
    f (algebraMap (Acris p R) (Bcris p R) x) = algebraMap (BdRPlus p R) (BdR p R) y ∧
      BdRPlus.eval p R n ((p : BdRPlus p R) ^ N * y) =
        Ideal.Quotient.mk _ (algebraMap (Ainf p R) (AinfInv p R) a)

theorem isCrisDRF_toBdR : IsCrisDRF (Bcris.toBdR p R) := by
  refine ⟨fun a => ?_, fun n => ⟨n, fun x => ?_⟩⟩
  · rw [Bcris.toBdR_algebraMap_acris, Acris.toBdRPlus_algebraMap_zero]
  · obtain ⟨b, hb⟩ := AcrisZero.exists_p_pow_mul_eq n (Acris.toRange p R n x)
    refine ⟨Acris.toBdRPlus p R x, b, Bcris.toBdR_algebraMap_acris x, ?_⟩
    have h1 := congrArg Subtype.val hb
    simp only [Subring.coe_mul, Subring.coe_pow, Subring.coe_natCast, RingHom.coe_rangeRestrict] at h1
    rw [map_mul, map_pow, map_natCast, Acris.eval_toBdRPlus, h1]
    rfl

theorem eval_eq_of_isCrisDRF {f : Bcris p R →+* BdR p R} (hf : IsCrisDRF f) (x : Acris p R) (y : BdRPlus p R)
    (hy : f (algebraMap (Acris p R) (Bcris p R) x) = algebraMap (BdRPlus p R) (BdR p R) y) (n : ℕ) :
    BdRPlus.eval p R n y = BdRPlus.eval p R n (Acris.toBdRPlus p R x) := by
  have hinj : Function.Injective (algebraMap (BdRPlus p R) (BdR p R)) := IsFractionRing.injective _ _
  obtain ⟨N, hN⟩ := hf.bdd n

  set T := (AcrisZero.toQuot p R n).range
  have key : ∀ k : ℕ, ∃ c : Ainf p R, BdRPlus.eval p R n y - BdRPlus.eval p R n (Acris.toBdRPlus p R x) =
      (p : AinfInv p R ⧸ AinfInv.kerTheta p R ^ n) ^ k *
        Ideal.Quotient.mk _ (algebraMap (Ainf p R) (AinfInv p R) c) := by
    intro k
    obtain ⟨a0, z, hz⟩ := Acris.exists_eq_add (N + n + k) x
    obtain ⟨yz, az, hyz, haz⟩ := hN z
    obtain ⟨bz, hbz⟩ := AcrisZero.exists_p_pow_mul_eq n (Acris.toRange p R n z)
    have hbz' := congrArg Subtype.val hbz
    simp only [Subring.coe_mul, Subring.coe_pow, Subring.coe_natCast, RingHom.coe_rangeRestrict] at hbz'
    have hy2 : y = algebraMap (AinfInv p R) (BdRPlus p R) (a0 : AinfInv p R) + (p : BdRPlus p R) ^ (N + n + k) * yz := by
      apply hinj
      rw [← hy, hz]
      simp only [map_add (f := _), map_mul, map_pow, map_natCast]
      rw [hf.on0 a0, hyz]
    have hx2 : Acris.toBdRPlus p R x =
        algebraMap (AinfInv p R) (BdRPlus p R) (a0 : AinfInv p R) + (p : BdRPlus p R) ^ (N + n + k) * Acris.toBdRPlus p R z := by
      rw [hz, map_add (f := _), map_mul, map_pow, map_natCast, Acris.toBdRPlus_algebraMap_zero]
    refine ⟨(p : Ainf p R) ^ n * az - (p : Ainf p R) ^ N * bz, ?_⟩
    have e1 : BdRPlus.eval p R n ((p : BdRPlus p R) ^ N * yz) =
        Ideal.Quotient.mk _ (algebraMap (Ainf p R) (AinfInv p R) az) := haz
    have e2 : (p : AinfInv p R ⧸ AinfInv.kerTheta p R ^ n) ^ n * BdRPlus.eval p R n (Acris.toBdRPlus p R z) =
        Ideal.Quotient.mk _ (algebraMap (Ainf p R) (AinfInv p R) bz) := by
      rw [Acris.eval_toBdRPlus, hbz']
      rfl
    rw [map_mul, map_pow, map_natCast] at e1
    rw [hy2, hx2]
    simp only [map_add (f := _), map_mul, map_pow, map_natCast, map_sub]
    rw [add_sub_add_left_eq_sub, ← mul_sub]
    calc (p : AinfInv p R ⧸ AinfInv.kerTheta p R ^ n) ^ (N + n + k) * (BdRPlus.eval p R n yz - BdRPlus.eval p R n (Acris.toBdRPlus p R z))
        = (p : AinfInv p R ⧸ AinfInv.kerTheta p R ^ n) ^ k *
            ((p : AinfInv p R ⧸ AinfInv.kerTheta p R ^ n) ^ n * ((p : AinfInv p R ⧸ AinfInv.kerTheta p R ^ n) ^ N * BdRPlus.eval p R n yz)
              - (p : AinfInv p R ⧸ AinfInv.kerTheta p R ^ n) ^ N * ((p : AinfInv p R ⧸ AinfInv.kerTheta p R ^ n) ^ n * BdRPlus.eval p R n (Acris.toBdRPlus p R z))) := by
          ring
      _ = _ := by rw [e1, e2]

  have hmem : ∀ c : Ainf p R, Ideal.Quotient.mk (AinfInv.kerTheta p R ^ n) (algebraMap (Ainf p R) (AinfInv p R) c) ∈ T :=
    fun c => ⟨algebraMap (Ainf p R) (AcrisZero p R) c, rfl⟩
  obtain ⟨c0, hc0⟩ := key 0
  rw [pow_zero, one_mul] at hc0
  have hH : IsHausdorff (span {(p : T)}) T := inferInstance
  have h0 : (⟨_, hmem c0⟩ : T) = 0 := by
    apply hH.haus
    intro k
    obtain ⟨c, hc⟩ := key k
    have hx : (⟨_, hmem c0⟩ : T) = ((p : T) ^ k) • (⟨_, hmem c⟩ : T) := by
      apply Subtype.ext
      simp only [smul_eq_mul, Subring.coe_mul, Subring.coe_pow, Subring.coe_natCast]
      rw [← hc0, hc]
    rw [SModEq.zero, hx]
    exact Submodule.smul_mem_smul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) k) Submodule.mem_top
  have h1 := congrArg Subtype.val h0
  simp only [ZeroMemClass.coe_zero] at h1
  rw [← hc0] at h1
  exact sub_eq_zero.1 h1

theorem eq_toBdR_of_isCrisDRF {f : Bcris p R →+* BdR p R} (hf : IsCrisDRF f) : f = Bcris.toBdR p R := by
  rw [← isCrisDRA_toBdRPlus_iff]
  intro x
  obtain ⟨N0, hN0⟩ := hf.bdd 0
  obtain ⟨y, -, hy, -⟩ := hN0 x
  rw [hy]
  congr 1
  exact BdRPlus.ext_eval fun n => eval_eq_of_isCrisDRF hf x y hy n

theorem isCrisDRF_iff (f : Bcris p R →+* BdR p R) : IsCrisDRF f ↔ f = Bcris.toBdR p R :=
  ⟨eq_toBdR_of_isCrisDRF, fun h => h ▸ isCrisDRF_toBdR⟩

end Formalism.BasicNotions.CmpTie.Incl
end
end

section

noncomputable section

namespace Formalism.BasicNotions.CmpTie.LogF

open Reformulated.AutPerF

variable (l : ℕ) [Fact l.Prime]

abbrev B : Type := BdRPlus l (Cmp6.OC l)

theorem mem_ker_pow_iff (x : B l) (n : ℕ) :
    x ∈ RingHom.ker (BdRPlus.thetaC l (PadicComplexInt l)) ^ n ↔ BdRPlus.eval l (Cmp6.OC l) n x = 0 := by
  rw [BdRPlus.ker_thetaC, ← RingHom.mem_ker, BdRPlus.ker_eval]
  rfl

theorem truncLog_eq (N : ℕ) (x : AinfInv l (Cmp6.OC l) ⧸ AinfInv.kerTheta l (Cmp6.OC l) ^ N) :
    truncLog N x = ∑ i ∈ Finset.Ico 1 (N + 1), algebraMap ℚ _ ((-1) ^ (i + 1) / i) * x ^ i := by
  unfold truncLog
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.smul_def]
  congr 2
  · push_cast
    ring
  · ring

abbrev u (ε : PreTilt ↥(PadicComplexInt l) l) : B l :=
  algebraMap (Ainf l (Cmp6.OC l)) (B l) (WittVector.teichmuller l ε)

abbrev sA (ε : PreTilt ↥(PadicComplexInt l) l) (n : ℕ) : B l :=
  ∑ i ∈ Finset.Ico 1 n, algebraMap ℚ (B l) ((-1) ^ (i + 1) / i) * (u l ε - 1) ^ i

theorem log_sub_mem (ε : PreTilt ↥(PadicComplexInt l) l) (h : BdRPlus.theta l (Cmp6.OC l) (u l ε) = 1) (n : ℕ) :
    BdRPlus.log (u l ε) h - sA l ε n ∈ RingHom.ker (BdRPlus.thetaC l (PadicComplexInt l)) ^ n := by
  have hk : u l ε - 1 ∈ RingHom.ker (BdRPlus.thetaC l (PadicComplexInt l)) := by
    rw [BdRPlus.ker_thetaC, RingHom.mem_ker, map_sub, h, map_one, sub_self]
  have hX : BdRPlus.eval l (Cmp6.OC l) n ((u l ε - 1) ^ n) = 0 :=
    (mem_ker_pow_iff l _ n).1 (Ideal.pow_mem_pow hk n)

  rw [mem_ker_pow_iff, map_sub, BdRPlus.eval_log, truncLog_eq, map_sum]
  simp only [map_mul, map_pow, RingHom.map_rat_algebraMap]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [Finset.sum_Ico_succ_top hn, add_sub_cancel_left, ← map_pow, hX, mul_zero]

theorem isLog_iff (ε : PreTilt ↥(PadicComplexInt l) l) (y : B l) :
    (∃ h : BdRPlus.theta l (Cmp6.OC l) (u l ε) = 1, y = BdRPlus.log (u l ε) h) ↔ Cmp6.IsLogA l ε y := by
  constructor
  · rintro ⟨h, rfl⟩ n
    exact log_sub_mem l ε h n
  · intro hy
    have h1 := hy 1
    have h2 := hy 2
    have hu : BdRPlus.theta l (Cmp6.OC l) (u l ε) = 1 := by
      have h3 := sub_mem (by simpa using h1) (Ideal.pow_le_self two_ne_zero h2)
      have h4 : u l ε - 1 ∈ RingHom.ker (BdRPlus.theta l (Cmp6.OC l)) := by
        rw [← BdRPlus.ker_thetaC]
        simpa using h3
      rw [RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at h4
      exact h4
    refine ⟨hu, ?_⟩
    apply BdRPlus.ext_eval
    intro n
    have h5 := sub_mem (hy n) (log_sub_mem l ε hu n)
    rw [sub_sub_sub_cancel_right, mem_ker_pow_iff, map_sub, sub_eq_zero] at h5
    exact h5

end Formalism.BasicNotions.CmpTie.LogF
end
end
