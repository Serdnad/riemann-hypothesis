module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle019
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle020
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle017
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle012
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle013
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.DpDual
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.ScalarSectionCompactBlockInvariant
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle005
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle021
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle011
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle004
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle006
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle007
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.FL

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt
open PositivityTheory.Rg.Sw.LVs.II (cE cE_hasDerivAt0 cE_add cE_zero cE_continuous mulL mulL_apply)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem fz_curve {X x : M2 n} (hX : IsLie X) (hx : InG x) (m : ℕ) (e : ℤ) (w : ℂ) (s : ℝ) :
    fz m e w (x * cE X s) = (x * cE X s).det ^ e * (u1 (x * cE X s)).det ^ (-(m : ℤ)) *
      Complex.exp (((Real.log (Complex.normSq (u1 (x * cE X s)).det) : ℝ) : ℂ) * (-w)) := by
  have hg : InG (x * cE X s) := inG_mul hx (inG_cE hX s)
  have hd := det_first_cayley_block_ne_zero hg
  have hmul : (u1 (x * cE X s)).det * (ub1 (x * cE X s)).det =
      ((Complex.normSq (u1 (x * cE X s)).det : ℝ) : ℂ) := by
    rw [inverse_first_block_eq_adjoint hg, Matrix.det_conjTranspose]
    exact Complex.mul_conj _
  have hpos : (0 : ℝ) < Complex.normSq (u1 (x * cE X s)).det := Complex.normSq_pos.mpr hd
  unfold fz
  rw [hmul, Complex.cpow_def_of_ne_zero (by exact_mod_cast hpos.ne'), Complex.ofReal_log hpos.le]

theorem fz_deriv {X x : M2 n} (hX : IsLie X) (hx : InG x) (m : ℕ) (e : ℤ) (w : ℂ) :
    ∃ R : ℂ, HasDerivAt (fun s : ℝ => fz m e w (x * cE X s)) R 0 ∧
      ‖R‖ ≤ ‖fz m e w x‖ * (|(e : ℝ)| * ‖rD X x‖ + ((m : ℝ) + 2 * ‖w‖) * ‖rA X x‖) := by
  have hd0 : det x ≠ 0 := (isUnit_det_of_InG hx).ne_zero
  have ha0 : (u1 x).det ≠ 0 := det_first_cayley_block_ne_zero hx
  have hfun : (fun s : ℝ => fz m e w (x * cE X s)) = fun s : ℝ =>
      (x * cE X s).det ^ e * (u1 (x * cE X s)).det ^ (-(m : ℤ)) *
        Complex.exp (((Real.log (Complex.normSq (u1 (x * cE X s)).det) : ℝ) : ℂ) * (-w)) :=
    funext fun s => fz_curve hX hx m e w s
  have hf0 : fz m e w x = (det x) ^ e * (u1 x).det ^ (-(m : ℤ)) *
      Complex.exp (((Real.log (Complex.normSq (u1 x).det) : ℝ) : ℂ) * (-w)) := by
    have h := fz_curve hX hx m e w 0
    rw [cE_zero, mul_one] at h
    exact h
  have hD : HasDerivAt (fun s : ℝ => det (x * cE X s))
      ((fderiv ℂ (fun y : M2 n => det y) x) (x * X)) 0 :=
    curve_deriv (fun y : M2 n => det y) cd_det X x
  have hA : HasDerivAt (fun s : ℝ => (u1 (x * cE X s)).det)
      ((fderiv ℂ (fun y : M2 n => (u1 y).det) x) (x * X)) 0 :=
    curve_deriv (fun y : M2 n => (u1 y).det) cd_detu1 X x
  have hD0 : det (x * cE X 0) = det x := by rw [cE_zero, mul_one]
  have hA0 : (u1 (x * cE X 0)).det = (u1 x).det := by rw [cE_zero, mul_one]
  have hzD : HasDerivAt (fun z : ℂ => z ^ e) (↑e * det x ^ (e - 1)) (det (x * cE X 0)) := by
    rw [hD0]
    exact hasDerivAt_zpow e (det x) (Or.inl hd0)
  have hzA : HasDerivAt (fun z : ℂ => z ^ (-(m : ℤ)))
      (↑(-(m : ℤ)) * (u1 x).det ^ (-(m : ℤ) - 1)) ((u1 (x * cE X 0)).det) := by
    rw [hA0]
    exact hasDerivAt_zpow _ _ (Or.inl ha0)
  have hDz := hzD.comp (0 : ℝ) hD
  have hAz := hzA.comp (0 : ℝ) hA
  have hre : HasDerivAt (fun s : ℝ => (u1 (x * cE X s)).det.re)
      ((fderiv ℂ (fun y : M2 n => (u1 y).det) x) (x * X)).re 0 := by
    have h2 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hA
    exact h2
  have him : HasDerivAt (fun s : ℝ => (u1 (x * cE X s)).det.im)
      ((fderiv ℂ (fun y : M2 n => (u1 y).det) x) (x * X)).im 0 := by
    have h2 := Complex.imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hA
    exact h2
  have hN := ((hre.mul hre).add (him.mul him)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun s => Complex.normSq_apply (u1 (x * cE X s)).det)
  have hNne : Complex.normSq (u1 (x * cE X 0)).det ≠ 0 := by
    rw [hA0]
    exact (Complex.normSq_pos.mpr ha0).ne'
  have hL := hN.log hNne
  have hE := (hL.ofReal_comp.mul_const (-w)).cexp
  have hfin := (hDz.mul hAz).mul hE
  rw [hfun]
  refine ⟨_, hfin, ?_⟩
  simp only [hA0, hD0, Function.comp_apply]
  have hd' : (fderiv ℂ (fun y : M2 n => det y) x) (x * X) = rD X x * det x := by
    unfold rD
    field_simp
  have ha' : (fderiv ℂ (fun y : M2 n => (u1 y).det) x) (x * X) = rA X x * (u1 x).det := by
    unfold rA
    field_simp
  have bound : ‖(det x ^ e * (u1 x).det ^ (-(m : ℤ)) *
      Complex.exp (((Real.log (Complex.normSq (u1 x).det) : ℝ) : ℂ) * (-w))) *
      ((e : ℂ) * rD X x + (-(m : ℂ)) * rA X x + ((2 * (rA X x).re : ℝ) : ℂ) * (-w))‖ ≤
      ‖fz m e w x‖ * (|(e : ℝ)| * ‖rD X x‖ + ((m : ℝ) + 2 * ‖w‖) * ‖rA X x‖) := by
    rw [norm_mul, hf0]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    refine norm_add₃_le.trans ?_
    have h1 : |(rA X x).re| ≤ ‖rA X x‖ := Complex.abs_re_le_norm _
    have h2 : 0 ≤ ‖w‖ := norm_nonneg _
    simp only [norm_mul, norm_neg, Complex.norm_intCast, Complex.norm_natCast, Complex.norm_real,
      Real.norm_eq_abs, abs_mul, abs_two]
    nlinarith [mul_le_mul_of_nonneg_right h1 h2]
  convert bound using 2
  rw [hd', ha']
  have hq : ((rA X x * (u1 x).det).re * (u1 x).det.re + (u1 x).det.re * (rA X x * (u1 x).det).re +
      ((rA X x * (u1 x).det).im * (u1 x).det.im + (u1 x).det.im * (rA X x * (u1 x).det).im)) /
      Complex.normSq (u1 x).det = 2 * (rA X x).re := by
    have hn : Complex.normSq (u1 x).det ≠ 0 := (Complex.normSq_pos.mpr ha0).ne'
    rw [div_eq_iff hn, Complex.normSq_apply]
    simp only [Complex.mul_re, Complex.mul_im]
    ring
  rw [hq]
  simp only [Pi.mul_apply, Function.comp_apply, cE_zero, mul_one]
  rw [zpow_sub_one₀ hd0, zpow_sub_one₀ ha0]
  push_cast
  field_simp

end PositivityTheory.Rg.Sw.HSt.FL
end
end

section

namespace PositivityTheory.Rg.Sw.HSt

theorem crLem : CRLem := CR.crLem_of locSec fib CR.cra2

end PositivityTheory.Rg.Sw.HSt
end

section

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.HSt.FarP

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt

variable {m n : ℕ} {e : ℤ} {G : Type} [Group G] [TopologicalSpace G]
  {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ} {Ht : G → ℝ≥0} {f : G → ℂ} {U : Set ℂ} {d : Polynomial ℂ}
  {Ê : ℂ → G → ℂ} {t : ℝ}

def trm (Ht : G → ℝ≥0) (f : G → ℂ) (s₀ z : ℂ) (x : G) : ℂ := ((Ht x : ℝ) : ℂ) ^ (z - s₀) * f x

theorem lift_mR (φ : GR n → ℂ) (y : GR n) : lift φ (mR y) = φ y := by
  unfold lift
  have h : IsUnit (mR y) ∧ InG (mR y) := ⟨y.1.isUnit, y.2⟩
  rw [dite_eq_left h]
  congr 1
  apply Subtype.ext
  apply Units.ext
  simp [mR]

theorem resG_mR (F : G → ℂ) (g : G) (y : GR n) : resG ι F g (mR y) = F (g * ι y) := lift_mR _ _

theorem termSplit (hS : SecFz) (h : HD m n e G Pp Γ ι s₀ Ht f U d Ê t) (z : ℂ) (x : G) :
    ∃ (y₀ : GR n) (C : ℂ), ∀ y : GR n, trm Ht f s₀ z (x * ι y) = C * fz m e (z - s₀) (mR (y₀ * y)) := by
  obtain ⟨x₀, y₀, S, r, hr, hx, hh⟩ := h.split x
  refine ⟨y₀, ((r : ℝ) : ℂ) ^ (z - s₀) * S, fun y => ?_⟩
  have hxy : x * ι y = x₀ * ι (y₀ * y) := by rw [hx, mul_assoc, ← map_mul]
  unfold trm
  rw [hxy, (hh _).1, (hh _).2, hS n m e (z - s₀) (y₀ * y), Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg hr.le (Vac.hLoc_nonneg _)]
  ring

theorem fz_mul_k (hS : SecFz) (w : ℂ) (y k : GR n) (hk : k ∈ KR n) :
    fz m e w (mR (y * k)) = fz m e w (mR y) * F0 m 0 e k := by
  obtain ⟨h1, h2⟩ := (mult n m 0 e).1 y k hk
  rw [hS n m e w (y * k), hS n m e w y, h1, h2]
  ring

theorem cosetSum_apply (Φ : G → ℂ) (x : G) :
    GlobalTheory.Eis.cosetSum Pp Γ Φ x = ∑' q : GlobalTheory.Eis.Cosets Pp Γ, Φ (((q.out : Γ) : G) * x) := rfl

theorem klaw (hS : SecFz) (h : HD m n e G Pp Γ ι s₀ Ht f U d Ê t) :
    ∀ z ∈ U, ∀ (g : G) (y k : GR n), k ∈ KR n → Ê z (g * ι (y * k)) = Ê z (g * ι y) * F0 m 0 e k := by
  intro z hz g y k hk
  have hfar : ∀ z' : ℂ, t < z'.re → Ê z' (g * ι (y * k)) = Ê z' (g * ι y) * F0 m 0 e k := by
    intro z' hz'
    rw [(h.far z' hz').2, (h.far z' hz').2, cosetSum_apply, cosetSum_apply, mul_assoc, ← tsum_mul_right]
    congr 1
    refine tsum_congr fun q => ?_
    obtain ⟨y₀, C, hC⟩ := termSplit hS h z' (((q.out : Γ) : G) * g)
    have e1 : ((q.out : Γ) : G) * (g * ι (y * k)) = ((q.out : Γ) : G) * g * ι (y * k) := by rw [mul_assoc]
    have e2 : ((q.out : Γ) : G) * (g * ι y) = ((q.out : Γ) : G) * g * ι y := by rw [mul_assoc]
    change trm Ht f s₀ z' _ = trm Ht f s₀ z' _ * _
    rw [e1, e2, hC, hC, ← mul_assoc y₀ y k, fz_mul_k hS _ _ _ hk]
    ring
  obtain ⟨σ, hσ⟩ := h.hR.1
  have hpre : IsPreconnected U := rightConn U h.hU h.hR
  have hA1 : AnalyticOnNhd ℂ (fun z => Ê z (g * ι (y * k))) U := (h.hol _).analyticOnNhd h.hU
  have hA2 : AnalyticOnNhd ℂ (fun z => Ê z (g * ι y) * F0 m 0 e k) U :=
    ((h.hol _).mul_const _).analyticOnNhd h.hU
  set z₀ : ℂ := ((max σ t + 1 : ℝ) : ℂ)
  have hz₀ : z₀ ∈ U := hσ (by simp [z₀, GlobalTheory.Cont.rightOf]; linarith [le_max_left σ t])
  have hev : (fun z => Ê z (g * ι (y * k))) =ᶠ[𝓝 z₀] fun z => Ê z (g * ι y) * F0 m 0 e k := by
    have ho : IsOpen {z : ℂ | t < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hm : z₀ ∈ {z : ℂ | t < z.re} := by simp [z₀]; linarith [le_max_right σ t]
    filter_upwards [ho.mem_nhds hm] with z hz using hfar z hz
  exact hA1.eqOn_of_preconnected_of_eventuallyEq hA2 hpre hz₀ hev hz

end PositivityTheory.Rg.Sw.HSt.FarP
end
end

section

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.HSt.FarP

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt

variable {m n : ℕ} {e : ℤ} {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ} {Ht : G → ℝ≥0} {f : G → ℂ} {U : Set ℂ} {d : Polynomial ℂ}
  {Ê : ℂ → G → ℂ} {t : ℝ}

theorem ιK_apply (k : KR n) : ιK n k = mR (k : GR n) := rfl

theorem continuous_fzG (hS : SecFz) (w : ℂ) : Continuous fun Y : GR n => fz m e w (mR Y) := by
  have h1 : (fun Y : GR n => fz m e w (mR Y)) = fun Y => F0 m 0 e Y * ((hLoc Y : ℝ) : ℂ) ^ w :=
    funext fun Y => hS n m e w Y
  rw [h1]
  refine (Vac.continuous_weight_factor detU1 m 0 e).mul ?_
  refine Continuous.cpow (Complex.continuous_ofReal.comp (Vac.continuous_hLoc detU1)) continuous_const fun Y => ?_
  exact Complex.ofReal_mem_slitPlane.mpr (Vac.hLoc_pos detU1 Y)

theorem integral_tsum_supp {X : Type} [MeasurableSpace X] {ν : Measure X} {ι' : Type} (F : ι' → X → ℂ) (u : ι' → ℝ)
    (hu : Summable u) (hu0 : ∀ q, 0 ≤ u q) (bd : X → ℝ) (hbd : Integrable bd ν)
    (hF : ∀ q x, ‖F q x‖ ≤ u q * bd x) (hFm : ∀ q, AEStronglyMeasurable (F q) ν) :
    Summable (fun q => ∫ x, F q x ∂ν) ∧ ∫ x, ∑' q, F q x ∂ν = ∑' q, ∫ x, F q x ∂ν := by
  have hFi : ∀ q, Integrable (F q) ν := fun q =>
    Integrable.mono' (hbd.const_mul (u q)) (hFm q) (ae_of_all _ (hF q))
  have hIn : ∀ q, ‖∫ x, F q x ∂ν‖ ≤ u q * ∫ x, bd x ∂ν := by
    intro q
    calc ‖∫ x, F q x ∂ν‖ ≤ ∫ x, u q * bd x ∂ν := norm_integral_le_of_norm_le (hbd.const_mul (u q)) (ae_of_all _ (hF q))
      _ = u q * ∫ x, bd x ∂ν := integral_const_mul _ _
  refine ⟨Summable.of_norm_bounded (hu.mul_right _) hIn, ?_⟩
  have hF0 : ∀ q, q ∉ Function.support u → ∀ x, F q x = 0 := by
    intro q hq x
    have h0 : u q = 0 := Function.notMem_support.mp hq
    have := hF q x
    rw [h0, zero_mul] at this
    exact norm_le_zero_iff.mp this
  have : Countable (Function.support u) := hu.countable_support.to_subtype
  have hL : ∀ x, ∑' q, F q x = ∑' s : Function.support u, F s x := by
    intro x
    refine (tsum_subtype_eq_of_support_subset (f := fun q => F q x) ?_).symm
    intro q hq
    by_contra h
    exact hq (hF0 q h x)
  have hN : ∀ q, ∫ x, ‖F q x‖ ∂ν ≤ u q * ∫ x, bd x ∂ν := by
    intro q
    calc ∫ x, ‖F q x‖ ∂ν ≤ ∫ x, u q * bd x ∂ν :=
          integral_mono (hFi q).norm (hbd.const_mul (u q)) (hF q)
      _ = u q * ∫ x, bd x ∂ν := integral_const_mul _ _
  have hsumn : Summable fun s : Function.support u => ∫ x, ‖F s x‖ ∂ν :=
    Summable.of_nonneg_of_le (fun s => integral_nonneg fun _ => norm_nonneg _) (fun s => hN s)
      ((hu.subtype _).mul_right _)
  simp_rw [hL]
  rw [← integral_tsum_of_summable_integral_norm (F := fun (s : Function.support u) x => F s x) (fun s => hFi s) hsumn]
  refine tsum_subtype_eq_of_support_subset (f := fun q => ∫ x, F q x ∂ν) ?_
  intro q hq
  by_contra h
  exact hq (by simp only [hF0 q h, integral_zero])

end PositivityTheory.Rg.Sw.HSt.FarP
end
end
