module

public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.SettingCharZeroAt
public import Formalism.SharpRestriction.GrowthBounds.ObjSeg
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.RingTheory.Ideal.GoingUp

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

theorem settingCZ : SettingCharZeroAt := by
  unfold SettingCharZeroAt
  intro p n' W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ jO w hS
  have hpW : ¬IsUnit (p : W) := hS.p_unif.1

  have hW : CharZero W := by
    rcases CharP.char_is_prime_or_zero W (ringChar W) with hq | hq
    · exfalso
      haveI hcp : CharP W (ringChar W) := ringChar.charP W
      by_cases hqp : ringChar W = p
      · apply hS.p_unif.ne_zero
        rw [← hqp]
        exact CharP.cast_eq_zero W (ringChar W)
      · have hcop : Nat.Coprime p (ringChar W) :=
          (Nat.coprime_primes hS.prime hq).mpr (Ne.symm hqp)
        apply hpW
        have hu : IsUnit (p : ZMod (ringChar W)) := by
          rw [← ZMod.coe_unitOfCoprime p hcop]
          exact Units.isUnit _
        have hu' := hu.map (ZMod.castHom (dvd_refl (ringChar W)) W)
        simpa using hu'
    · haveI : CharP W 0 := by
        rw [← hq]
        exact ringChar.charP W
      exact CharP.charP_to_charZero W
  haveI := hS.frac_alt
  have hQ : CharZero Qq := charZero_of_injective_algebraMap (IsFractionRing.injective W Qq)
  have hK : CharZero Kf := (RingHom.charZero_iff ι.injective).mp hQ

  have hpO : ¬IsUnit (p : O) := by
    intro hu
    have hint : jO.IsIntegral := RingHom.IsIntegral.of_finite hS.finite
    have hmax : ((IsLocalRing.maximalIdeal O).comap jO).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' jO hint (IsLocalRing.maximalIdeal O)
    have hle : (IsLocalRing.maximalIdeal O).comap jO = IsLocalRing.maximalIdeal W :=
      IsLocalRing.eq_maximalIdeal hmax
    have hpm : (p : W) ∈ IsLocalRing.maximalIdeal W := (IsLocalRing.mem_maximalIdeal _).mpr hpW
    rw [← hle, Ideal.mem_comap, map_natCast] at hpm
    exact (IsLocalRing.mem_maximalIdeal _).mp hpm hu
  exact ⟨hK, hpO⟩

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

theorem kf_coarseA_le {s r p : ℕ} (S : SegData s) (b : SegBlock s r) (i : Fin s) : coarseA p S b i ≤ S.bTop i := by
  unfold coarseA
  exact (Nat.div_le_self _ _).trans (Nat.sub_le _ _)

theorem kf_coarseC_le {s r p : ℕ} (S : SegData s) (aTop : Fin s → ℕ) (b : SegBlock s r) (i : Fin s) :
    coarseC p S aTop b i ≤ aTop i := by
  unfold coarseC
  exact (Nat.div_le_self _ _).trans (Nat.sub_le _ _)

def kfTuple {s r : ℕ} (b : SegBlock s r) :
    (Fin s → Fin (r + 1) → ℕ) × (Fin s → Fin (r + 1) → ℕ) × (Fin s → ℕ) × (Fin s → ℕ) × (Fin s → ℕ) × ℕ :=
  (b.rz, b.ry, b.o, b.w, b.sg, b.oPlus)

theorem kfTuple_inj {s r : ℕ} : Function.Injective (@kfTuple s r) := by
  rintro ⟨a1, a2, a3, a4, a5, a6⟩ ⟨b1, b2, b3, b4, b5, b6⟩ h
  simp only [kfTuple, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
  rfl

theorem kf_cap_le {s r p : ℕ} (S : SegData s) (b : SegBlock s r) (l : ℕ) :
    cap p S b l ≤ S.A0 p + ∑ i, (S.bTop i : ℤ) := by
  unfold cap
  gcongr with i
  split_ifs
  · have h1 := kf_coarseA_le (p := p) S b i
    omega
  · omega

theorem kf_kept_finite (p r : ℕ) {s : ℕ} (S : SegData s) (aTop : Fin s → ℕ) :
    {b : SegBlock s r | Kept p r S aTop b}.Finite := by
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = ((S.A0 p + ∑ i, (S.bTop i : ℤ) : ℤ) : ℝ) +
      (S.La / (r + 1) + 4 / (p : ℝ) ^ 2) * ∑ i, 2 * (S.a : ℝ) / (S.P p i : ℝ) +
      S.La * (S.bPlus : ℝ) / (r + 1) := ⟨_, rfl⟩
  have hT := Set.Finite.prod (Set.Finite.pi fun i => Set.Finite.pi fun (_ : Fin (r + 1)) => Set.finite_Iic (S.P p i))
    (Set.Finite.prod (Set.Finite.pi fun i => Set.Finite.pi fun (_ : Fin (r + 1)) => Set.finite_Iic (S.P p i))
    (Set.Finite.prod (Set.Finite.pi fun i => Set.finite_Iic (S.bTop i))
    (Set.Finite.prod (Set.Finite.pi fun i => Set.finite_Iic (S.bTop i))
    (Set.Finite.prod (Set.Finite.pi fun i => Set.finite_Iic (aTop i)) (Set.finite_Iic ⌈R⌉₊)))))
  refine (hT.preimage kfTuple_inj.injOn).subset ?_
  rintro b ⟨⟨hdig, -, -⟩, hge, hlt, hop⟩
  simp only [Set.mem_preimage, kfTuple, Set.mem_prod, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Iic,
    forall_const]
  refine ⟨fun i c => (hdig i c).1.le, fun i c => (hdig i c).2.le, fun i => ?_, fun i => ?_, fun i => ?_, ?_⟩
  · by_cases h : S.sigma ≤ (i : ℕ)
    · exact (hge i h).1.trans (kf_coarseA_le S b i)
    · rw [(hlt i (not_le.mp h)).1]
      exact Nat.zero_le _
  · by_cases h : (i : ℕ) < S.sigma
    · exact (hlt i h).2.1.trans (kf_coarseA_le S b i)
    · rw [(hge i (not_lt.mp h)).2.2.1]
      exact Nat.zero_le _
  · by_cases h : (i : ℕ) < S.sigma
    · exact (hlt i h).2.2.1.trans (kf_coarseC_le S aTop b i)
    · rw [(hge i (not_lt.mp h)).2.2.2]
      exact Nat.zero_le _
  · have hc : (cap p S b s : ℝ) ≤ ((S.A0 p + ∑ i, (S.bTop i : ℤ) : ℤ) : ℝ) := by
      exact_mod_cast kf_cap_le S b s
    have h1 : (b.oPlus : ℝ) ≤ R := by
      refine hop.trans ?_
      rw [hR]
      unfold Oplus
      linarith
    exact_mod_cast h1.trans (Nat.le_ceil R)

end Formalism.MainNotions.ColumnSystems.Pf
end
end
