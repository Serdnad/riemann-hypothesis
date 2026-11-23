module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.Bundle001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle245
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.SplitCentreMulTor
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.OnlyIsotropic
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.ContinuousPA
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.LogAbsEqLogIdeleNorm
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiClosT
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.Bundle006
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
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

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open PositivityTheory.Rg.Rs
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

attribute [local instance] borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem centre_eq (τ : ℝ) : splitCentre E n τ = (An.tor E (fun _ : Fin n => τ) : GA E n) := by
  have h := GlobalTheory.CuspBoundSiegel.diagUnits_posIdele (E := E) n (Real.exp_pos τ)
  rw [Real.log_exp] at h
  rw [← h, DiscreteGroups.T1.G.Dcy.tor_eq]

private theorem logSize_centre (τ : ℝ) :
    logSize (splitCentre E n τ) ≤ 2 * Module.finrank ℚ E * |τ| := by
  rw [centre_eq]
  refine ((torNorm_holds E).2 n _).2.trans ?_
  have h : ‖(fun _ : Fin n => τ)‖ ≤ |τ| :=
    (pi_norm_le_iff_of_nonneg (abs_nonneg τ)).2 fun _ => by simp
  gcongr

private theorem logSize_inv' (g : GA E n) : logSize (g⁻¹) = logSize g := by
  unfold logSize
  rw [inv_inv, add_comm]

private theorem deg_top (g : GA E n) : deg g ⊤ = deg (1 : GA E n) ⊤ + logAbs g.val.det := by
  have e : (((1 : Matrix (Fin n) (Fin n) E)ᵀ : Matrix (Fin n) (Fin n) E) : Fin n → Fin n → E) =
      ⇑(Pi.basisFun E (Fin n)) := by
    ext i j
    simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  have hli : LinearIndependent E ((1 : Matrix (Fin n) (Fin n) E)ᵀ) := by
    rw [e]; exact (Pi.basisFun E (Fin n)).linearIndependent
  have hsp : Submodule.span E (Set.range ((1 : Matrix (Fin n) (Fin n) E)ᵀ)) = ⊤ := by
    rw [e]; exact (Pi.basisFun E (Fin n)).span_eq
  have h1 := D1.degBasis E n n g 1 hli
  have h2 := D1.degBasis E n n 1 1 hli
  have h3 := D1.degAdelic E n n 1 g g 1 hli (by simp)
  rw [mul_one] at h3
  rw [hsp] at h1 h2
  rw [← h1, ← h2, h3]

private theorem abs_logAbs_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ g : GA E n,
    |logAbs g.val.det| ≤ C * (1 + logSize g) := by
  obtain ⟨C, hC, h⟩ := degRight E n
  refine ⟨C, hC, fun g => abs_le.2 ⟨?_, ?_⟩⟩
  · have h1 := h g g⁻¹ ⊤
    rw [mul_inv_cancel, logSize_inv', deg_top g] at h1
    linarith
  · have h1 := h 1 g ⊤
    rw [one_mul, deg_top g] at h1
    linarith

private theorem sizes' : Sizes := by
  intro E _ _ _ n hn
  obtain ⟨C, hC, hdet⟩ := abs_logAbs_le (E := E) (n := n)
  obtain ⟨-, -, -, c₀, hc₀⟩ := D1.sizeBasic E n
  have hc : 0 ≤ 2 + |c₀| + C := by positivity
  refine ⟨2 + |c₀| + C, hc, fun x => ⟨?_, ?_, DiscreteGroups.T1.G.Dcy.redSize_nonneg _⟩⟩
  · set l := ldet x with hl
    set d : ℝ := (Module.finrank ℚ E : ℝ) with hd
    have hd0 : 0 < d := by
      rw [hd]; exact_mod_cast Module.finrank_pos (R := ℚ) (M := E)
    have hn0 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    set τ : ℝ := l / (n * d) with hτ
    set y : GA E n := splitCentre E n (-l / (n * d)) * x.1 with hy
    have hr : r0 x = redSize y := rfl
    have hx : x.1 = splitCentre E n τ * y := by
      rw [hy, ← mul_assoc, ← CuspidalL2GL.splitCentre_add]
      have : τ + -l / (n * d) = 0 := by rw [hτ]; ring
      rw [this, CuspidalL2GL.splitCentre_zero, one_mul]
    have hτle : 2 * d * |τ| ≤ 2 * |l| := by
      have hpos : 0 < (n : ℝ) * d := by positivity
      rw [hτ, abs_div, abs_of_pos hpos]
      have e : 2 * d * (|l| / (n * d)) = 2 * |l| / n := by field_simp
      rw [e]
      exact div_le_self (by positivity) hn0
    have hK : 2 * |l| + c₀ ≤ (2 + |c₀| + C) * (1 + |l|) := by
      have h1 := le_abs_self c₀
      have h2 := abs_nonneg l
      have h3 := abs_nonneg c₀
      nlinarith [mul_nonneg h3 h2, mul_nonneg hC h2]
    have key : redSize x.1 - (2 + |c₀| + C) * (1 + |l|) ≤ redSize y := by
      refine le_ciInf fun γ => ?_
      have h1 := DiscreteGroups.T1.G.Dcy.redSize_le x.1 γ
      have h2 : ratGL E n γ * x.1 = splitCentre E n τ * (ratGL E n γ * y) := by
        rw [hx, ← mul_assoc, ← CuspidalL2GL.splitCentre_comm, mul_assoc]
      rw [h2] at h1
      have h3 := hc₀ (splitCentre E n τ) (ratGL E n γ * y)
      have h4 : logSize (splitCentre E n τ) ≤ 2 * d * |τ| := logSize_centre τ
      linarith
    rw [hr]
    linarith
  · have h1 : |ldet x| ≤ C * (1 + logSize x.1) := hdet x.1
    have h2 := DiscreteGroups.T1.G.Dcy.logSize_nonneg x.1
    have h3 := abs_nonneg c₀
    nlinarith [mul_nonneg h3 h2]

theorem sizes_of_basic : Basic → Sizes := fun _ => sizes'

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

end
end

section

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1
open scoped ENNReal

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

section Meas

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem continuous_ac' : Continuous (ac E n) := by
  have hc : Continuous (splitCentre E n) := by
    have e : splitCentre E n = fun t : ℝ =>
        GeneralLinearGroup.scalar (Fin n) (infId E (expU fun _ : InfinitePlace E => (t : ℂ))) :=
      funext GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_eq_scalar
    rw [e]
    refine Continuous.units_map _ ?_ |>.comp ((continuous_infId E).comp
      (continuous_expU.comp (continuous_pi fun _ => Complex.continuous_ofReal)))
    change Continuous fun x : Ad E => Matrix.diagonal fun _ : Fin n => x
    exact (continuous_pi fun _ => continuous_id).matrix_diagonal
  exact (hc.comp (continuous_id.div_const _)).prodMk continuous_const

private theorem measurable_reduced_size : Measurable (r0 : H E n 0 → ℝ) := by
  have hc : Continuous fun x : H E n 0 => (ac E n (-ldet x) * x).1 :=
    continuous_fst.comp ((continuous_ac'.comp continuous_ldet.neg).mul continuous_id)
  haveI := borelSpace_H (E := E) (n := n)
  letI : MeasurableSpace (GA E n) := borel _
  haveI : BorelSpace (GA E n) := ⟨rfl⟩
  exact (redBasic E n).2.2.comp hc.measurable

private theorem measurable_cnt {Ω : Set (H E n 0)} (hΩ : IsCompact Ω) :
    Measurable (cnt (ratH E n 0) Ω) := by
  haveI := borelSpace_H (E := E) (n := n)
  haveI : Countable (ratH E n 0) := DiscreteGroups.T1.G.Dcy.countable_ratH'
  set_option synthInstance.maxHeartbeats 200000 in
    have hm : MeasurableSet Ω := hΩ.measurableSet
    refine Measurable.tsum fun γ => ?_
    have hc : Continuous fun x : H E n 0 => x⁻¹ * (γ : H E n 0) * x :=
      (continuous_inv.mul continuous_const).mul continuous_id
    exact (measurable_one.indicator hm).comp hc.measurable

end Meas

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.tailInt_of_bounds :
    GFac → GBound → Supp → DomInt → TailInt := by
  intro hF hB hS hD E _ _ _ n ι _ s
  haveI := borelSpace_H (E := E) (n := n)
  obtain ⟨p, hp⟩ := hF E n ι s
  obtain ⟨Ω, hΩ, hC⟩ := hB E n ι s
  choose Cb hCb0 hCb using fun b => hC (p.x b)
  choose Nb hNb using fun b => hD E n s.pos s.D s.π s.fix (p.w b) (p.mem b) Ω hΩ
  refine ⟨Finset.univ.sup Nb, fun L hL => ?_⟩
  choose Db hDb0 hDb using fun b => hNb b L hL
  refine ⟨∑ b, Cb b * Db b, Finset.sum_nonneg fun b _ => mul_nonneg (hCb0 b) (hDb0 b),
    fun m R ρ hR hφ A hA => ?_⟩
  set S : Set (H E n 0) := {x | |ldet x| ≤ R ∧ ρ ≤ r0 x} with hSdef
  have hSm : MeasurableSet S :=
    ((isClosed_le (continuous_abs.comp continuous_ldet) continuous_const).measurableSet).inter
      (measurableSet_le measurable_const measurable_reduced_size)
  set f : p.B → H E n 0 → ℝ≥0∞ := fun b =>
    S.indicator (fun x => ‖(p.w b).1 x.1‖ₑ * cnt (ratH E n 0) Ω x) with hf
  have hfm : ∀ b, Measurable (f b) := fun b => by
    refine Measurable.indicator ?_ hSm
    refine Measurable.mul ?_ (measurable_cnt hΩ)
    exact (((continuous_of_mem s.π (p.mem b)).comp continuous_fst).enorm).measurable
  have hpt : ∀ x, A.indicator (fun x => ‖m.G x x‖ₑ) x ≤
      ∑ b, ENNReal.ofReal (Cb b * ‖m.U‖) * f b x := by
    intro x
    by_cases hxA : x ∈ A
    · rw [Set.indicator_of_mem hxA]
      by_cases hx : |ldet x| ≤ R
      · have hxS : x ∈ S := ⟨hx, hA x hxA hx⟩
        rw [hp m x x]
        refine (enorm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
        rw [enorm_mul, hf]
        simp only [Set.indicator_of_mem hxS]
        calc ‖(p.w b).1 x.1‖ₑ * ‖m.G (ac E n (ldet x) * p.x b) x‖ₑ
            ≤ ‖(p.w b).1 x.1‖ₑ * (ENNReal.ofReal (Cb b * ‖m.U‖) * cnt (ratH E n 0) Ω x) := by
              gcongr; exact hCb b m _ x
          _ = _ := by ring
      · have h0 : m.G x x = 0 := by
          refine hS E n ι s m R hφ x x ?_
          have h1 : R < |ldet x| := not_le.mp hx
          have h2 : |ldet x + ldet x| = 2 * |ldet x| := by
            rw [← two_mul, abs_mul, abs_two]
          rw [h2]
          have := abs_nonneg (ldet x)
          linarith
        simp [h0]
    · rw [Set.indicator_of_notMem hxA]
      exact zero_le
  have h1R : (1 : ℝ) ≤ 1 + R := by linarith
  have hT : ∀ b, ENNReal.ofReal (Cb b * ‖m.U‖) * ∫⁻ x, f b x ∂s.D.ν ≤
      ENNReal.ofReal (Cb b * Db b * ‖m.U‖ * (1 + R) ^ (Finset.univ.sup Nb) * Real.exp (-(L * ρ))) := by
    intro b
    have hpow : (1 + R) ^ Nb b ≤ (1 + R) ^ (Finset.univ.sup Nb) :=
      pow_le_pow_right₀ h1R (Finset.le_sup (Finset.mem_univ b))
    have h2 : ∫⁻ x, f b x ∂s.D.ν ≤
        ENNReal.ofReal (Db b * (1 + R) ^ (Finset.univ.sup Nb) * Real.exp (-(L * ρ))) := by
      refine (hDb b R ρ hR).trans (ENNReal.ofReal_le_ofReal ?_)
      have := hDb0 b
      have he := (Real.exp_pos (-(L * ρ))).le
      gcongr
    calc _ ≤ ENNReal.ofReal (Cb b * ‖m.U‖) *
          ENNReal.ofReal (Db b * (1 + R) ^ (Finset.univ.sup Nb) * Real.exp (-(L * ρ))) := by gcongr
      _ = _ := by
        rw [← ENNReal.ofReal_mul (mul_nonneg (hCb0 b) (norm_nonneg _))]
        congr 1
        ring
  calc ∫⁻ x, A.indicator (fun x => ‖m.G x x‖ₑ) x ∂s.D.ν
      ≤ ∫⁻ x, ∑ b, ENNReal.ofReal (Cb b * ‖m.U‖) * f b x ∂s.D.ν := lintegral_mono hpt
    _ = ∑ b, ENNReal.ofReal (Cb b * ‖m.U‖) * ∫⁻ x, f b x ∂s.D.ν := by
        rw [lintegral_finsetSum _ fun b _ => (hfm b).const_mul _]
        exact Finset.sum_congr rfl fun b _ => lintegral_const_mul _ (hfm b)
    _ ≤ ∑ b, ENNReal.ofReal (Cb b * Db b * ‖m.U‖ * (1 + R) ^ (Finset.univ.sup Nb) * Real.exp (-(L * ρ))) :=
        Finset.sum_le_sum fun b _ => hT b
    _ = _ := by
        rw [← ENNReal.ofReal_sum_of_nonneg]
        · congr 1
          simp only [Finset.sum_mul]
        · intro b _
          have := mul_nonneg (hCb0 b) (hDb0 b)
          have he := (Real.exp_pos (-(L * ρ))).le
          have hp1 : 0 ≤ (1 + R) ^ (Finset.univ.sup Nb) := by positivity
          positivity

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1
open DiscreteGroups.T1.G
open scoped Classical ENNReal

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

attribute [local instance] borelH

private theorem pow_mul_exp_neg_le (N : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    (1 + r) ^ N * Real.exp (-r) ≤ N.factorial * Real.exp 1 := by
  have h := Real.pow_div_factorial_le_exp (1 + r) (by linarith) N
  rw [div_le_iff₀ (by exact_mod_cast N.factorial_pos)] at h
  have e : Real.exp r * Real.exp (-r) = 1 := by rw [← Real.exp_add]; simp
  calc (1 + r) ^ N * Real.exp (-r) ≤ (Real.exp (1 + r) * N.factorial) * Real.exp (-r) :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ = N.factorial * Real.exp 1 * (Real.exp r * Real.exp (-r)) := by rw [Real.exp_add]; ring
    _ = N.factorial * Real.exp 1 := by rw [e, mul_one]

private theorem point_bound {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (hB : Basic) (hS : Sizes)
    (hn : 1 ≤ n) {π : CuspSub E n} (hθ : ThetaFix π) {ψ : Sm E n} (hψ : ψ ∈ π.V) (M : ℕ) (L : ℝ) (hL : 0 ≤ L) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ R ρ : ℝ, 0 ≤ R → ∀ x : H E n 0, |ldet x| ≤ R → ρ ≤ r0 x →
      ‖ψ.1 x.1‖ ≤ A * (1 + R) ^ (2 * M) * Real.exp (-(L * ρ)) * wt x ^ (-(2 * M : ℤ)) := by
  obtain ⟨h1, h2, -⟩ := hB E n hn
  obtain ⟨c, hc0, hc⟩ := hS E n hn
  have hA := hθ.1 ψ hψ
  obtain ⟨C₀, hC₀⟩ := Dcy.cp_decay ψ (π.cusp ψ hψ) hA 0 (L + 1)
  set a : ℝ := redSize (1 : GA E 0) with ha
  have ha0 : 0 ≤ a := Dcy.redSize_nonneg _
  set c₁ : ℝ := 2 + a + c with hc₁
  have hc₁0 : 0 ≤ c₁ := by positivity
  set C : ℝ := max C₀ 0 with hC
  have hC0 : 0 ≤ C := le_max_right _ _
  set K : ℝ := ((2 * M).factorial : ℝ) * Real.exp 1 with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨C * c₁ ^ (2 * M) * K, by positivity, fun R ρ hR x hx hρ => ?_⟩
  obtain ⟨hs, -, hr⟩ := hc x
  set r : ℝ := r0 x with hrdef
  set y : H E n 0 := ac E n (-ldet x) * x with hy
  have hy0 : ldet y = 0 := by rw [hy, h2, h1]; ring
  have hψy : ψ.1 y.1 = ψ.1 x.1 := hA _ _
  have hdec : ‖ψ.1 x.1‖ ≤ C * Real.exp (-((L + 1) * r)) := by
    have h := hC₀ y.1 (by
      have : |ldet y| ≤ 0 := by rw [hy0]; simp
      exact this)
    rw [hψy] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  have hx2 : x.2 = 1 := Units.ext (Subsingleton.elim _ _)
  have hw : wt x = 1 + redSize x.1 + a := by rw [wt, hx2]
  have hrs := Dcy.redSize_nonneg x.1
  have hw1 : 1 ≤ wt x := by rw [hw]; linarith
  have hP : 1 ≤ (1 + r) * (1 + R) := by nlinarith [mul_nonneg hr hR]
  have hwle : wt x ≤ c₁ * ((1 + r) * (1 + R)) := by
    have h3 : c * (1 + |ldet x|) ≤ c * (1 + R) := mul_le_mul_of_nonneg_left (by linarith) hc0
    have h4 : 1 + R ≤ (1 + r) * (1 + R) := by nlinarith [mul_nonneg hr hR]
    have h5 : 1 + r ≤ (1 + r) * (1 + R) := by nlinarith [mul_nonneg hr hR]
    have h6 : c * (1 + R) ≤ c * ((1 + r) * (1 + R)) := mul_le_mul_of_nonneg_left h4 hc0
    have h7 : (1 + a) * 1 ≤ (1 + a) * ((1 + r) * (1 + R)) := mul_le_mul_of_nonneg_left hP (by linarith)
    rw [hw, hc₁]
    nlinarith
  have hexp : Real.exp (-((L + 1) * r)) ≤ Real.exp (-(L * ρ)) * Real.exp (-r) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    nlinarith [mul_le_mul_of_nonneg_left hρ hL]
  have hpow : wt x ^ (2 * M) ≤ c₁ ^ (2 * M) * ((1 + r) ^ (2 * M) * (1 + R) ^ (2 * M)) := by
    rw [← mul_pow, ← mul_pow]
    exact pow_le_pow_left₀ (by linarith) hwle _
  have hwpos : 0 < wt x ^ (2 * M) := pow_pos (by linarith) _
  have hz : wt x ^ (-(2 * M : ℤ)) = (wt x ^ (2 * M))⁻¹ := by
    rw [_root_.zpow_neg]
    congr 1
  have hr1 : 0 ≤ 1 + r := by linarith
  have hR1 : 0 ≤ 1 + R := by linarith
  have hmain : ‖ψ.1 x.1‖ * wt x ^ (2 * M) ≤ C * c₁ ^ (2 * M) * K * (1 + R) ^ (2 * M) * Real.exp (-(L * ρ)) := by
    have hq := pow_mul_exp_neg_le (2 * M) hr
    calc ‖ψ.1 x.1‖ * wt x ^ (2 * M)
        ≤ (C * (Real.exp (-(L * ρ)) * Real.exp (-r))) *
            (c₁ ^ (2 * M) * ((1 + r) ^ (2 * M) * (1 + R) ^ (2 * M))) :=
          mul_le_mul (hdec.trans (mul_le_mul_of_nonneg_left hexp hC0)) hpow hwpos.le (by positivity)
      _ = C * c₁ ^ (2 * M) * ((1 + r) ^ (2 * M) * Real.exp (-r)) * (1 + R) ^ (2 * M) * Real.exp (-(L * ρ)) := by ring
      _ ≤ C * c₁ ^ (2 * M) * K * (1 + R) ^ (2 * M) * Real.exp (-(L * ρ)) := by
          gcongr
  rw [hz, ← div_eq_mul_inv, le_div_iff₀ hwpos]
  exact hmain

theorem domInt_pf : Basic → Sizes → DomInt := by
  intro hB hS E _ _ _ n hn D π hθ ψ hψ Ω hΩ
  refine ⟨2 * (2 * n), fun L hL => ?_⟩
  obtain ⟨A, hA0, hA⟩ := point_bound hB hS hn hθ hψ (2 * n) L hL
  have hI := wtCount E n 0 D Ω hΩ (2 * n) (by omega)
  set I : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (wt x ^ (-(2 * ((2 * n : ℕ) : ℤ)))) * cnt (ratH E n 0) Ω x ∂D.ν with hIdef
  refine ⟨A * I.toReal, mul_nonneg hA0 ENNReal.toReal_nonneg, fun R ρ hR => ?_⟩
  set B : ℝ := A * (1 + R) ^ (2 * (2 * n)) * Real.exp (-(L * ρ)) with hBdef
  have hR1 : 0 ≤ 1 + R := by linarith
  have hB0 : 0 ≤ B := by positivity
  calc ∫⁻ x, {x | |ldet x| ≤ R ∧ ρ ≤ r0 x}.indicator (fun x => ‖ψ.1 x.1‖ₑ * cnt (ratH E n 0) Ω x) x ∂D.ν
      ≤ ∫⁻ x, ENNReal.ofReal B * (ENNReal.ofReal (wt x ^ (-(2 * ((2 * n : ℕ) : ℤ)))) * cnt (ratH E n 0) Ω x) ∂D.ν := by
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ {x : H E n 0 | |ldet x| ≤ R ∧ ρ ≤ r0 x}
        · rw [Set.indicator_of_mem hx, ← mul_assoc, ← ENNReal.ofReal_mul hB0, ← ofReal_norm]
          exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (hA R ρ hR x hx.1 hx.2)) _
        · rw [Set.indicator_of_notMem hx]
          exact zero_le
    _ = ENNReal.ofReal B * I := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (A * I.toReal * (1 + R) ^ (2 * (2 * n)) * Real.exp (-(L * ρ))) := by
        rw [show A * I.toReal * (1 + R) ^ (2 * (2 * n)) * Real.exp (-(L * ρ)) = B * I.toReal by rw [hBdef]; ring,
          ENNReal.ofReal_mul hB0, ENNReal.ofReal_toReal hI]

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

end
end

section

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G
open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

private theorem kerH_left {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
    (φ : H E n 0 → ℂ) (γ : ratH E n 0) (x y : H E n 0) :
    kerH φ ((γ : H E n 0) * x) y = kerH φ x y := by
  unfold kerH
  rw [← finsum_comp_equiv (Equiv.mulLeft γ)]
  refine finsum_congr fun δ => ?_
  congr 1
  simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, _root_.mul_inv_rev]
  group

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.pointRep_pf :
    AeEq → KInv → PointRep := by
  intro hA hK E _ _ _ n ι _ s Φ T hΦ hT h g hg x i
  obtain ⟨k, k', hk⟩ := vecsEx E n 0 s.D ι Φ Φ T T 0 hΦ hΦ hT hT
  have hF : Continuous fun x => inner ℂ (s.k₁ x i) h :=
    ((s.vecs.cont i).1).inner continuous_const
  have hG : Continuous fun x => inner ℂ (k x i) g := ((hk.cont i).1).inner continuous_const
  have hIF : Inv fun x => inner ℂ (s.k₁ x i) h := fun γ x => by
    simp only [(hK E n ι s).1 γ x]
  have hIG : Inv fun x => inner ℂ (k x i) g := fun γ x => by
    simp only [hk.rep₁, kerH_left]
  have hae : ∀ᵐ x ∂s.D.ν, ldet x ∈ (Set.univ : Set ℝ) →
      inner ℂ (s.k₁ x i) h = inner ℂ (k x i) g := by
    have h1 := s.o₁ h i
    have h2 := hT g i
    rw [hg] at h1
    filter_upwards [h1, h2] with y a1 a2 _
    rw [s.vecs.rep₁, hk.rep₁, ← a1, a2]
  have := hA E n s.D _ _ Set.univ hF hG hIF hIG isOpen_univ hae x (Set.mem_univ _)
  rw [this, hk.rep₁]
end
