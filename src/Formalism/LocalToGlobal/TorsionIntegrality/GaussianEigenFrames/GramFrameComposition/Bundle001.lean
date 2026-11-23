module

public import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementA
public import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.Several
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.FacShapeZero
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementB
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
open scoped BigOperators

namespace Formalism.L2.Th1.GD

open Formalism.L2.Th1.C
open Formalism.L2.Th1.G (linSub toZ phSum tens4 inBlock)
open Formalism.G (unitBall)

namespace ToZ

variable {K : Type} [Field K]

theorem phSum_one {n : Type} [Fintype n] (ph : PowerSeries K) :
    phSum (fun _ : n => (1 : K)) ph = Formalism.L2.Th1.E.phSum ph := by
  unfold Formalism.L2.Th1.G.phSum Formalism.L2.Th1.E.phSum Formalism.InvariantFactorPaths.G7.at1
  exact Finset.sum_congr rfl fun i _ => one_smul _ _

theorem hasSubst_block {n : Type} [Finite n] (a : Fin 4) :
    MvPowerSeries.HasSubst (fun i : n => (MvPowerSeries.X (a, i) : MvPowerSeries (Fin 4 × n) K)) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X _

theorem subst_four {n m : Type} [Finite n] {b : Fin 4 × n → MvPowerSeries m K}
    (hb : MvPowerSeries.HasSubst b) (f : MvPowerSeries n K) :
    MvPowerSeries.subst b
      (∏ a : Fin 4, MvPowerSeries.subst
        (fun i => (MvPowerSeries.X (a, i) : MvPowerSeries (Fin 4 × n) K)) f) =
      ∏ a : Fin 4, MvPowerSeries.subst (fun i => b (a, i)) f := by
  rw [← MvPowerSeries.substAlgHom_apply hb, map_prod]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [MvPowerSeries.substAlgHom_apply, MvPowerSeries.subst_comp_subst_apply (hasSubst_block a) hb]
  congr 1
  funext i
  exact MvPowerSeries.subst_X hb (a, i)

theorem cc_logForm {m : Type} [Fintype m] {l : PowerSeries K} (hl0 : PowerSeries.constantCoeff l = 0)
    (c : m → K) :
    MvPowerSeries.constantCoeff (∑ j, MvPowerSeries.C (c j) *
      PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries m K) l : MvPowerSeries m K) = 0 := by

  rw [map_sum]
  exact Finset.sum_eq_zero fun j _ => by
    rw [map_mul, PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X j) l hl0,
      mul_zero]

theorem cc_flin {m : Type} [Fintype m] {l linv : PowerSeries K}
    (hl0 : PowerSeries.constantCoeff l = 0) (hv0 : PowerSeries.constantCoeff linv = 0) (c : m → K) :
    MvPowerSeries.constantCoeff
      (flin l linv c (fun w' => (MvPowerSeries.X w' : MvPowerSeries m K))) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero (cc_logForm hl0 c) linv hv0

theorem toZ_flin {m : Type} [Fintype m] {l linv : PowerSeries K}
    (hl0 : PowerSeries.constantCoeff l = 0) (hv0 : PowerSeries.constantCoeff linv = 0)
    (hlv : PowerSeries.subst linv l = PowerSeries.X) (c : m → K) :
    toZ linv (flin l linv c (fun w' => (MvPowerSeries.X w' : MvPowerSeries m K))) =
      PowerSeries.subst (∑ x, MvPowerSeries.C (c x) * MvPowerSeries.X x : MvPowerSeries m K) linv := by
  have e : toZ linv (∑ j, MvPowerSeries.C (c j) *
      PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries m K) l : MvPowerSeries m K) =
      ∑ x, MvPowerSeries.C (c x) * MvPowerSeries.X x := by

    rw [← Formalism.L2.Th1.G.toZHom_apply hv0, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, MvPowerSeries.c_eq_algebraMap, AlgHom.commutes, Formalism.L2.Th1.G.toZHom_apply,
      Formalism.L2.Th1.G.toZ_subst_X hv0, hlv,
      PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X j))]
  rw [← e]
  exact Formalism.L2.Th1.G.mvSubst_subst (Formalism.L2.Th1.G.hasSubst_zPt hv0) (cc_logForm hl0 c) linv

theorem toZ_tensor4 {n : Type} [Fintype n] {l linv : PowerSeries K} (h : IsLogPair l linv)
    (T : MvPowerSeries n K) (γ : Matrix (Fin 4 × n) (Fin 4 × n) K) :
    toZ linv (MvPowerSeries.subst (Formalism.L2.Th1.E.matCoord l linv (RingHom.id K) γ)
      (Formalism.L2.Th1.E.tensor4 (MvPowerSeries.subst (fun i => Formalism.InvariantFactorPaths.G7.at1 i l) T))) =
      linSub (fun w w' => γ w w') (tens4 T) := by
  obtain ⟨hl0, -, hv0, -, hlv⟩ := h
  have hmc : MvPowerSeries.HasSubst (Formalism.L2.Th1.E.matCoord l linv (RingHom.id K) γ) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun w => cc_flin hl0 hv0 _
  have hat : MvPowerSeries.HasSubst (fun i : n => (Formalism.InvariantFactorPaths.G7.at1 i l : MvPowerSeries n K)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i =>
      PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X i) l hl0
  have hb : MvPowerSeries.HasSubst (fun w : Fin 4 × n =>
      toZ linv (Formalism.L2.Th1.E.matCoord l linv (RingHom.id K) γ w)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun w =>
      Formalism.L2.Th1.G.cc_toZ hv0 (cc_flin hl0 hv0 _)
  unfold Formalism.L2.Th1.G.toZ
  rw [MvPowerSeries.subst_comp_subst_apply hmc (Formalism.L2.Th1.G.hasSubst_zPt hv0)]
  change MvPowerSeries.subst (fun w : Fin 4 × n =>
      toZ linv (Formalism.L2.Th1.E.matCoord l linv (RingHom.id K) γ w)) _ = _
  unfold Formalism.L2.Th1.E.tensor4 Formalism.L2.Th1.G.linSub Formalism.L2.Th1.G.tens4 Formalism.L2.Th1.G.inBlock
  rw [subst_four hb, subst_four (Formalism.L2.Th1.G.hasSubst_lin _)]
  refine Finset.prod_congr rfl fun a _ => ?_
  have hb' : MvPowerSeries.HasSubst (fun i : n =>
      toZ linv (Formalism.L2.Th1.E.matCoord l linv (RingHom.id K) γ (a, i))) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i =>
      Formalism.L2.Th1.G.cc_toZ hv0 (cc_flin hl0 hv0 _)
  rw [MvPowerSeries.subst_comp_subst_apply hat hb']
  congr 1
  funext i
  unfold Formalism.InvariantFactorPaths.G7.at1
  rw [Formalism.L2.Th1.G.mvSubst_subst hb' (MvPowerSeries.constantCoeff_X i), MvPowerSeries.subst_X hb']
  unfold Formalism.L2.Th1.E.matCoord
  rw [toZ_flin hl0 hv0 hlv,
    ← PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hv0)
      (PowerSeries.HasSubst.of_constantCoeff_zero (Formalism.L2.Th1.G.cc_linForm _)), hlv,
    PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero (Formalism.L2.Th1.G.cc_linForm _))]
  rfl

end ToZ

theorem ShapeToZ_proof : ShapeToZ := by
  intro K _ _ _ l linv ph hlp hph n _ T γ hS
  obtain ⟨κ, _, r, V, hr, hV, e⟩ := hS
  obtain ⟨e1, hInt⟩ := Formalism.L2.Th1.E.prodInt K κ (Fin 4 × n) ph r V hph hr hV
  refine ⟨Formalism.L2.Th1.E.thetaProd r V, fun d => hInt d, ?_⟩
  rw [← ToZ.toZ_tensor4 hlp, e, e1, ToZ.phSum_one]
  rfl

end Formalism.L2.Th1.GD
end
end

section

noncomputable section

namespace Formalism.L2.Th1.GD

open Formalism.L2.Th1.H (cmL CmOK)
open Formalism.L2.Th1.CM (omegaK)

namespace GramFrameMultiplicativityLemmas

theorem indep_sqrt {d : ℕ} (hd : 0 < d) (P Q : ℤ)
    (h : (P : ℂ) + (Q : ℂ) * (Complex.I * ((Real.sqrt d : ℝ) : ℂ)) = 0) : P = 0 ∧ Q = 0 := by
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp at him hre
  refine ⟨hre, ?_⟩
  rcases him with h1 | h1
  · exact h1
  · exact absurd h1 (by positivity)

theorem sqrt_sq (d : ℕ) :
    (Complex.I * ((Real.sqrt d : ℝ) : ℂ)) * (Complex.I * ((Real.sqrt d : ℝ) : ℂ)) = -(d : ℂ) := by
  have h : ((Real.sqrt d : ℝ) : ℂ) * ((Real.sqrt d : ℝ) : ℂ) = (d : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg d)]; simp
  linear_combination Complex.I * Complex.I * h + (d : ℂ) * Complex.I_mul_I

theorem odd_b {a : ℕ} {b c : ℤ} {d : ℕ} (hOK : CmOK a b c d) : Odd b := by
  have h1 := hOK.1
  have h8 := hOK.2.2.1
  rcases Int.even_or_odd b with ⟨k, hk⟩ | h
  · exfalso
    have h2 : (d : ℤ) = 4 * ((a : ℤ) * c - k * k) := by
      rw [hk] at h1
      linear_combination (-1 : ℤ) * h1
    generalize (a : ℤ) * c - k * k = X at h2
    omega
  · exact h

theorem gcd_one {a : ℕ} {b c : ℤ} {d : ℕ} (hOK : CmOK a b c d) :
    Int.gcd (a : ℤ) (Int.gcd b c : ℤ) = 1 := by
  by_contra hne
  obtain ⟨r, hr, hrg⟩ := Nat.exists_prime_and_dvd hne
  have hg : (r : ℤ) ∣ (Int.gcd (a : ℤ) (Int.gcd b c : ℤ) : ℤ) := by exact_mod_cast hrg
  have h1 : (r : ℤ) ∣ (a : ℤ) := hg.trans (Int.gcd_dvd_left _ _)
  have h2 : (r : ℤ) ∣ (Int.gcd b c : ℤ) := hg.trans (Int.gcd_dvd_right _ _)
  have h3 : (r : ℤ) ∣ b := h2.trans (Int.gcd_dvd_left _ _)
  have h4 : (r : ℤ) ∣ c := h2.trans (Int.gcd_dvd_right _ _)
  obtain ⟨a', ha'⟩ := h1
  obtain ⟨b', hb'⟩ := h3
  obtain ⟨c', hc'⟩ := h4
  have h0 := hOK.1
  have hdv : ((r * r : ℕ) : ℤ) ∣ (d : ℤ) := by
    refine ⟨4 * a' * c' - b' * b', ?_⟩
    rw [ha', hb', hc'] at h0
    push_cast
    linear_combination (-1 : ℤ) * h0
  have hdv' : r * r ∣ d := by exact_mod_cast hdv
  have hu := (Irreducible.squarefree hOK.2.2.2) r hdv'
  exact hr.one_lt.ne' (Nat.isUnit_iff.mp hu)

theorem dvd_of_prim {a : ℕ} {b c : ℤ} {d : ℕ} (hOK : CmOK a b c d) (y : ℤ)
    (hb : (a : ℤ) ∣ y * b) (hc : (a : ℤ) ∣ y * c) : (a : ℤ) ∣ y := by
  have e1 := Int.gcd_eq_gcd_ab b c
  have e2 := Int.gcd_eq_gcd_ab (a : ℤ) (Int.gcd b c : ℤ)
  rw [gcd_one hOK] at e2
  set u := Int.gcdA b c
  set v := Int.gcdB b c
  set u' := Int.gcdA (a : ℤ) (Int.gcd b c : ℤ)
  set v' := Int.gcdB (a : ℤ) (Int.gcd b c : ℤ)
  have hy : y = (a : ℤ) * (y * u') + (y * b) * (u * v') + (y * c) * (v * v') := by
    push_cast at e2
    linear_combination y * e2 + y * v' * e1
  rw [hy]
  exact dvd_add (dvd_add (dvd_mul_right _ _) (hb.mul_right _)) (hc.mul_right _)

end GramFrameMultiplicativityLemmas

open GramFrameMultiplicativityLemmas in
theorem MulRing_proof : MulRing := by
  intro a b c d ha hd lam hlam hOK z hz
  have hw1 : (cmL a b d ha hd lam hlam).ω₁ = lam * (a : ℂ) := rfl
  have hw2 : (cmL a b d ha hd lam hlam).ω₂ = lam * Formalism.L2.Th1.F.cmTheta b d := rfl
  obtain ⟨x, y, e1⟩ := PeriodPair.mem_lattice.mp (hz _ (cmL a b d ha hd lam hlam).ω₁_mem_lattice)
  obtain ⟨x', y', e2⟩ := PeriodPair.mem_lattice.mp (hz _ (cmL a b d ha hd lam hlam).ω₂_mem_lattice)
  rw [hw1, hw2] at e1 e2
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hS := sqrt_sq d
  unfold Formalism.L2.Th1.F.cmTheta at e1 e2
  set S : ℂ := Complex.I * ((Real.sqrt d : ℝ) : ℂ) with hSdef
  have f1 : (x : ℂ) * a + y * (((b : ℂ) + S) / 2) = z * a := by
    apply mul_left_cancel₀ hlam
    linear_combination e1
  have f2 : (x' : ℂ) * a + y' * (((b : ℂ) + S) / 2) = z * (((b : ℂ) + S) / 2) := by
    apply mul_left_cancel₀ hlam
    linear_combination e2
  have key : (((4 * a * a * x' + 2 * a * y' * b - 2 * x * a * b - y * (b * b - d) : ℤ)) : ℂ)
      + ((2 * a * y' - 2 * x * a - 2 * y * b : ℤ) : ℂ) * S = 0 := by
    push_cast
    linear_combination 4 * (a : ℂ) * f2 - 2 * ((b : ℂ) + S) * f1 + (y : ℂ) * hS
  obtain ⟨k1, k2⟩ := indep_sqrt hd _ _ key
  have h0 := hOK.1
  have haZ : (a : ℤ) ≠ 0 := by exact_mod_cast ha.ne'
  have hb : (a : ℤ) ∣ y * b := by
    refine ⟨y' - x, ?_⟩
    have h2 : (2 : ℤ) * (y * b) = 2 * ((a : ℤ) * (y' - x)) := by linear_combination (-1 : ℤ) * k2
    exact mul_left_cancel₀ two_ne_zero h2
  have hc : (a : ℤ) ∣ y * c := by
    refine ⟨-x', ?_⟩
    have h2 : (4 * (a : ℤ)) * (y * c) = (4 * (a : ℤ)) * ((a : ℤ) * (-x')) := by
      linear_combination k1 - b * k2 + y * h0
    exact mul_left_cancel₀ (mul_ne_zero four_ne_zero haZ) h2
  obtain ⟨y₀, hy₀⟩ := dvd_of_prim hOK y hb hc
  obtain ⟨k, hk⟩ := odd_b hOK
  have hom : omegaK d = (1 + S) / 2 := rfl
  refine ⟨x + y₀ * k, y₀, ?_⟩
  rw [hom]
  apply mul_right_cancel₀ haC
  rw [← f1, hy₀, hk]
  push_cast
  ring

end Formalism.L2.Th1.GD
end
end
