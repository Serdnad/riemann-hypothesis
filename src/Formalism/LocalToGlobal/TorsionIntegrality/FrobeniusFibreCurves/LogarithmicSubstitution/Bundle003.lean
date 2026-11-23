module

public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.Bundle001
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.ConstantCoeffSeriesAtVariable
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.LogarithmEquivalence
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.Bundle004
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.IsogenyFormulaInstance
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.StatementT
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.Closure
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.Points
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.UnitaryInverseIdentity
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.PhNormFromDatum
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.SecondCoeffConsistency
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace Formalism.L2.Th1.B.ParE

open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob)
open Formalism.InvariantFactorPaths.G7.LogarithmEquivalence (integral_iff_lift integral_mul' integral_one' integral_of_mul_eq_one)

section Alg

variable {K : Type} [Field K] [CharZero K] {ι : Type}

theorem subst_inVar (x : ι) (f : PowerSeries K) {l : PowerSeries K}
    (hl : PowerSeries.constantCoeff l = 0) :
    at1 x (PowerSeries.subst l f) = PowerSeries.subst (at1 x l) f := by
  unfold at1
  exact PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero hl)
    (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X x)) f

end Alg

section Norm

variable {K : Type} [NormedField K] [IsUltrametricDist K] {ι : Type}

theorem integral_sub' {f g : MvPowerSeries ι K} (hf : Integral f) (hg : Integral g) :
    Integral (f - g) := by
  intro n
  rw [map_sub, sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hf n) ?_)
  rw [norm_neg]
  exact hg n

theorem integral_add' {f g : MvPowerSeries ι K} (hf : Integral f) (hg : Integral g) :
    Integral (f + g) := by
  intro n
  rw [map_add (f := _)]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hf n) (hg n))

theorem integral_C' {c : K} (hc : ‖c‖ ≤ 1) : Integral (MvPowerSeries.C c : MvPowerSeries ι K) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_C]
  split_ifs
  · exact hc
  · simp

end Norm

theorem weierstrass_series_integral : WIntegral := by
  intro K _ _ _ c0 e1 P l i ep F hLL hCH hce
  obtain ⟨hepI, hep1, hcurve, -⟩ := hCH
  have hl0 : PowerSeries.constantCoeff l = 0 := hLL.2.2.1
  have hl1 : PowerSeries.coeff 1 l = 1 := hLL.2.2.2.1
  have ha : PowerSeries.HasSubst l := PowerSeries.HasSubst.of_constantCoeff_zero hl0
  have hlne : l ≠ 0 := by
    rintro rfl
    simp at hl1
  have hD0c : PowerSeries.constantCoeff
      (1 + PowerSeries.X ^ 2 * P - PowerSeries.C e1 * PowerSeries.X ^ 2 : PowerSeries K) ≠ 0 := by
    simp
  have hCe : PowerSeries.subst l (PowerSeries.C e1 : PowerSeries K) = (PowerSeries.C e1 : PowerSeries K) := by
    have h := (PowerSeries.substAlgHom ha).commutes e1
    rw [PowerSeries.coe_substAlgHom] at h
    simpa [MvPowerSeries.algebraMap_apply, PowerSeries.algebraMap_apply] using h
  have hw : wOf e1 P * (1 + PowerSeries.X ^ 2 * P - PowerSeries.C e1 * PowerSeries.X ^ 2) =
      PowerSeries.X ^ 2 := by
    unfold wOf
    rw [mul_assoc, PowerSeries.inv_mul_cancel _ hD0c, mul_one]
  have hWD : PowerSeries.subst l (wOf e1 P) *
      (1 + l ^ 2 * PowerSeries.subst l P - PowerSeries.C e1 * l ^ 2) = l ^ 2 := by
    have h := congrArg (PowerSeries.subst l) hw
    rw [← PowerSeries.coe_substAlgHom ha] at h
    simp only [map_add (f := _), map_sub, map_one, map_mul, map_pow] at h
    rw [PowerSeries.coe_substAlgHom ha, PowerSeries.subst_X ha, hCe] at h
    exact h
  have hkey : PowerSeries.subst l (wOf e1 P) * (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2) * l ^ 2 =
      PowerSeries.X ^ 2 * l ^ 2 := by
    rw [map_sub]
    linear_combination (-PowerSeries.subst l (wOf e1 P)) * hcurve + PowerSeries.X ^ 2 * hWD
  have h1 : PowerSeries.subst l (wOf e1 P) * (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2) =
      PowerSeries.X ^ 2 := mul_right_cancel₀ (pow_ne_zero 2 hlne) hkey
  refine ⟨h1, ?_⟩
  have hX : Integral (ι := Unit) (PowerSeries.X : PowerSeries K) := law_integral_X ()
  have hX2 : Integral (ι := Unit) (PowerSeries.X ^ 2 : PowerSeries K) := by
    rw [pow_two]
    exact integral_mul' hX hX
  have hEI : Integral (ι := Unit) (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2) :=
    integral_add' hepI (integral_mul' (integral_C' hce) hX2)
  have hEc : MvPowerSeries.constantCoeff (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2 : PowerSeries K) = 1 := by
    have h : PowerSeries.constantCoeff (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2) = 1 := by
      simp [hep1]
    exact h
  have hEc' : PowerSeries.constantCoeff (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2) ≠ 0 := by
    simp [hep1]
  have hVI : Integral (ι := Unit) (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2)⁻¹ :=
    integral_of_mul_eq_one hEI hEc (PowerSeries.inv_mul_cancel _ hEc')
  have hWe : PowerSeries.subst l (wOf e1 P) =
      PowerSeries.X ^ 2 * (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2)⁻¹ := by
    calc PowerSeries.subst l (wOf e1 P)
        = PowerSeries.subst l (wOf e1 P) * ((ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2) *
            (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2)⁻¹) := by
          rw [PowerSeries.mul_inv_cancel _ hEc', mul_one]
      _ = (PowerSeries.subst l (wOf e1 P) * (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2)) *
            (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2)⁻¹ := by
          rw [mul_assoc]
      _ = _ := by rw [h1]
  rw [hWe]
  exact integral_mul' hX2 hVI

end Formalism.L2.Th1.B.ParE
end
end

section

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.B.KSum

open Formalism.L2.Th1.F (MulStable IsKerReps taylor0 pSeries)

theorem coeff_two_pSeries (L : PeriodPair) :
    PowerSeries.coeff 2 (pSeries L) = L.g₂ / 20 := by
  rw [Formalism.L2.Th1.F.pSeriesCoeff L 2, if_neg (by norm_num)]
  first
    | (simp only [PeriodPair.g₂]; push_cast; ring)
    | (unfold PeriodPair.g₂; push_cast; ring)
    | (norm_num [PeriodPair.g₂]; ring)

theorem coeff_two_shift (L : PeriodPair) (P : ℂ) (hP : P ∉ L.lattice) :
    PowerSeries.coeff 2 (taylor0 (fun z => L.weierstrassP (z + P)))
      = 3 * L.weierstrassP P ^ 2 - L.g₂ / 4 := by
  unfold taylor0
  rw [PowerSeries.coeff_mk]
  have hc : IsClosed (L.lattice : Set ℂ) := by
    first
      | exact L.isClosed_lattice
      | exact PeriodPair.isClosed_lattice L
      | (haveI : DiscreteTopology L.lattice.toAddSubgroup := inferInstanceAs (DiscreteTopology L.lattice)
         exact (L.lattice.toAddSubgroup).isClosed_of_discreteTopology)
  have hopen : ∀ᶠ w in nhds P, w ∉ L.lattice := hc.isOpen_compl.mem_nhds hP
  have hev : deriv L.weierstrassP =ᶠ[nhds P] L.derivWeierstrassP := by
    filter_upwards [hopen] with w hw
    first
      | exact (L.hasDerivAt_weierstrassP hw).deriv
      | exact (PeriodPair.hasDerivAt_weierstrassP L hw).deriv
      | exact congrFun L.deriv_weierstrassP w
  have h1 : deriv (fun z => L.weierstrassP (z + P)) = fun w => deriv L.weierstrassP (w + P) := by
    funext w
    rw [deriv_comp_add_const]
  have h2 : deriv (fun w => deriv L.weierstrassP (w + P)) 0 = 6 * L.weierstrassP P ^ 2 - L.g₂ / 2 := by
    rw [deriv_comp_add_const, zero_add, hev.deriv_eq]
    exact (Formalism.L2.Th1.F.pSecond L P hP).deriv
  have h3 : iteratedDeriv 2 (fun z => L.weierstrassP (z + P)) =
      deriv (deriv (fun z => L.weierstrassP (z + P))) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [h3, h1, h2, Nat.factorial_two]
  push_cast
  ring

theorem kappa_sum_holds : KappaSum := by
  intro L α S hα hst hS
  obtain ⟨neg, -, -, -, h3⟩ := Formalism.L2.Th1.F.endoZInstance L α S hα hst hS
  have h4 := congrArg (PowerSeries.coeff 2) h3

  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale, map_add (f := _), map_sum,
  coeff_two_pSeries] at h4
  have h5 : ∀ P : S, PowerSeries.coeff 2
      (taylor0 (fun z => L.weierstrassP (z + (P : ℂ))) - PowerSeries.C (L.weierstrassP (P : ℂ)))
        = 3 * L.weierstrassP (P : ℂ) ^ 2 - L.g₂ / 4 := by
    intro P
    rw [map_sub, coeff_two_shift L P (hS.1 P P.2).2, PowerSeries.coeff_C]
    simp
  rw [Finset.sum_congr rfl (fun P _ => h5 P),
    Finset.sum_coe_sort S (fun P => 3 * L.weierstrassP P ^ 2 - L.g₂ / 4)] at h4
  linear_combination -h4

end Formalism.L2.Th1.B.KSum
end
end

section

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.B.Split

open Formalism.L2.Th1.C Formalism.L2.Th1.C.Pts Formalism.L2.Th1.C.Calc

variable {K : Type} [Field K] [CharZero K] {R : Subring K} {l linv ph : PowerSeries K}

theorem cong_smul {σ : Type} {z : K} (hz : IsBinomScalar R z) {f g : MvPowerSeries σ K}
    (h : Cong R f g) : Cong R (z • f) (z • g) := by
  have := lGBinom K R σ z hz _ h
  unfold Cong
  rwa [← smul_sub]

theorem lg_of_smul {σ : Type} {c : K} (hc : c ≠ 0) (hz : IsBinomScalar R c⁻¹)
    {f : MvPowerSeries σ K} (h : LG R (c • f)) : LG R f := by
  have := lGBinom K R σ _ hz _ h
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this

theorem biextension_formal_mul_mul (hF : Frame R l linv ph) {a b : K} (hN : PhNormAt R l linv ph a b)
    {σ : Type} {x y : MvPowerSeries σ K} (hx : IsPt R x) (hy : IsPt R y) :
    Cong R (be0 l linv ph (fmul l linv a x) (fmul l linv a y)) ((a * b) • be0 l linv ph x y) := by
  have e1 := phNorm_pt hF.1 hN (isPt_fadd hF.1 hF.2.1 hx hy)
  have e2 := phNorm_pt hF.1 hN hx
  have e3 := phNorm_pt hF.1 hN hy
  rw [fmul_fadd hF.1 a hx.1 hy.1] at e1
  have := cong_sub (cong_sub e1 e2) e3
  rw [← smul_sub, ← smul_sub] at this
  exact this

theorem biextension_vanishes_split (hF : Frame R l linv ph) {a b : K} (ha : EndInt R l linv a)
    (hB : IsBinomScalar R a) (hZ : ZLinAt R l linv ph a) (hN : PhNormAt R l linv ph a b)
    (hc : a * (a - b) ≠ 0) (hinv : IsBinomScalar R (a * (a - b))⁻¹)
    {σ : Type} {x y : MvPowerSeries σ K} (hx : IsPt R x) (hy : IsPt R y) :
    LG R (be0 l linv ph x y) := by
  have hax : IsPt R (fmul l linv a x) := isPt_fmul hF.1 ha hx
  have e1 : Cong R (be0 l linv ph (fmul l linv a x) (fmul l linv a y))
      (a • be0 l linv ph (fmul l linv a x) y) := hZ σ _ _ hax hy
  have e2 : Cong R (be0 l linv ph (fmul l linv a x) y) (a • be0 l linv ph x y) := by
    have := hZ σ y x hy hx
    rwa [addDefect_comm ph y (fmul l linv a x), addDefect_comm ph y x] at this
  have e3 : Cong R (a • a • be0 l linv ph x y) ((a * b) • be0 l linv ph x y) :=
    cong_trans (cong_symm (cong_trans e1 (cong_smul hB e2))) (biextension_formal_mul_mul hF hN hx hy)
  refine lg_of_smul hc hinv ?_
  have e : (a * (a - b)) • be0 l linv ph x y =
      a • a • be0 l linv ph x y - (a * b) • be0 l linv ph x y := by
    rw [smul_smul, ← sub_smul, mul_sub]
  rw [e]
  exact e3

theorem phNorm_one_iff (c : K) :
    PhNormAt R l linv ph c 1 ↔
      Cong R (PowerSeries.subst (fmul l linv c (PowerSeries.X : MvPowerSeries Unit K)) ph)
        (c • (ph : MvPowerSeries Unit K)) := by
  rw [PhNormAt, mulBy_eq_fmul, mul_one]

theorem phNorm_natCast (hF : Frame R l linv ph)
    (key : ∀ x y : MvPowerSeries Unit K, IsPt R x → IsPt R y → LG R (be0 l linv ph x y)) (n : ℕ) :
    PhNormAt R l linv ph (n : K) 1 := by
  have hX : IsPt R (PowerSeries.X : MvPowerSeries Unit K) := isPt_X
  have hXs : PowerSeries.subst (PowerSeries.X : MvPowerSeries Unit K) ph = ph :=
    PowerSeries.X_subst ph
  rw [phNorm_one_iff]
  induction n with
  | zero =>
    rw [Nat.cast_zero, fmul_zero_left hF.1, PowerSeries.subst_zero_of_constantCoeff_zero hF.2.2,
      zero_smul]
    exact cong_refl _
  | succ n ih =>
    have k := key _ _ (isPt_fmul hF.1 (Clo.endInt_natCast hF.1 hF.2.1 n) hX) hX
    rw [be0, hXs] at k
    rw [Nat.cast_succ, fmul_add hF.1 _ _ hX.1, fmul_one hF.1 hX.1, add_smul, one_smul]
    have := lg_add k ih
    unfold Cong
    convert this using 1
    abel

theorem phNorm_intCast (hF : Frame R l linv ph)
    (key : ∀ x y : MvPowerSeries Unit K, IsPt R x → IsPt R y → LG R (be0 l linv ph x y)) (n : ℤ) :
    PhNormAt R l linv ph (n : K) 1 := by
  have hX : IsPt R (PowerSeries.X : MvPowerSeries Unit K) := isPt_X
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · rw [Int.cast_natCast]
    exact phNorm_natCast hF key m
  · rw [Int.cast_neg, Int.cast_natCast]
    have hm := Clo.endInt_natCast (R := R) hF.1 hF.2.1 m
    have k := key _ _ (isPt_fmul hF.1 hm hX) (isPt_fmul hF.1 (endInt_neg hF.1 hF.2.1 hm) hX)
    rw [be0, fadd_fmul_neg hF.1 _ hX.1, PowerSeries.subst_zero_of_constantCoeff_zero hF.2.2] at k
    have h1 := (phNorm_one_iff (R := R) (l := l) (linv := linv) (ph := ph) (m : K)).1
      (phNorm_natCast hF key m)
    rw [phNorm_one_iff, neg_smul]
    have := lg_neg (lg_add k h1)
    unfold Cong
    convert this using 1
    abel

theorem split_vanishing_at_two : Formalism.L2.Th1.G.SplitVanishTwo := by
  intro K _ _ _ _ R hR l linv ph a b hF hF1 ha hcl hN ha0 hab hb1 hi1 hi2
  have hl := hF.1.1
  have hli := hF.1.2.2.1
  have hph := hF.2.2
  have hB : IsBinomScalar R a := by
    refine closure_minimal ?_ (binomClosed K R hR) hcl
    rintro _ ⟨n, rfl⟩
    exact intBinomScalar K R n
  have hZ : ZLinAt R l linv ph a := by
    refine closure_minimal ?_ (zLinClosed K R hR l linv ph hl hli hph) hcl
    rintro _ ⟨n, rfl⟩
    exact zLinInt K R l linv ph hF hF1 n
  have key : ∀ x y : MvPowerSeries Unit K, IsPt R x → IsPt R y → LG R (be0 l linv ph x y) :=
    fun x y hx hy =>
      biextension_vanishes_split hF ha hB hZ hN (mul_ne_zero ha0 (sub_ne_zero.2 hab)) hi1 hx hy
  have hA : PhNormAt R l linv ph a 1 := by
    have hc : IsClosed {c : K | PhNormAt R l linv ph c 1} :=
      (phNormClosed K R hR l linv ph hl hli hph).preimage
        (continuous_id.prodMk continuous_const)
    refine closure_minimal ?_ hc hcl
    rintro _ ⟨n, rfl⟩
    exact phNorm_intCast hF key n
  refine lg_of_smul (mul_ne_zero ha0 (sub_ne_zero.2 (Ne.symm hb1))) hi2 ?_
  have e3 : Cong R ((a * 1) • (ph : MvPowerSeries Unit K)) ((a * b) • ph) :=
    cong_trans (cong_symm hA) hN
  have e : (a * (1 - b)) • (ph : MvPowerSeries Unit K) = (a * 1) • ph - (a * b) • ph := by
    rw [← sub_smul, mul_sub]
  rw [e]
  exact e3

end Formalism.L2.Th1.B.Split
end
end
