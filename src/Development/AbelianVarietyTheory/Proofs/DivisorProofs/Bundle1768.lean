module

public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1730
import Formalism.LocalRingCardinality.DataHost
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle006
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.MeasUpq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.Real.Pi.Bounds
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
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1679
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.BridgeA
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle013
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle050
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_packingSet_measure_ge_covolume : ∀ (H : Type) [Group H] [MeasurableSpace H] [MeasurableMul H] (ν : Measure H) (Γ : Subgroup H), Countable Γ → ∃ F : Set H, MeasurableSet F ∧ covolume Γ H ν ≤ ν F ∧ ∀ γ ∈ Γ, ∀ y ∈ F, γ * y ∈ F → γ = 1 := by
  first | exact @GlobalTheory.packing_set_covolume_le | exact GlobalTheory.packing_set_covolume_le | (intros; apply GlobalTheory.packing_set_covolume_le <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

namespace GlobalTheory.LowRow

theorem volU_ge_inv_pow_of_formalDeg (r : ℕ) (hr : 1 ≤ r) :
    (((r : ℝ) ^ r)⁻¹) ^ r ≤ ReciprocityTheory.ChartRestriction.DS.volU r := by
  unfold ReciprocityTheory.ChartRestriction.DS.volU
  have hrpos : (0 : ℝ) < (r : ℝ) ^ r := by positivity
  rw [show (((r : ℝ) ^ r)⁻¹) ^ r = ∏ _i ∈ Finset.range r, ((r : ℝ) ^ r)⁻¹ by
    rw [Finset.prod_const, Finset.card_range]]
  apply Finset.prod_le_prod₀
  · intro i _; positivity
  · intro i hi
    have hi' : i < r := Finset.mem_range.mp hi
    have hfac : (i.factorial : ℝ) ≤ (r : ℝ) ^ r := by
      have h1 : i.factorial ≤ r.factorial := Nat.factorial_le hi'.le
      have h2 : r.factorial ≤ r ^ r := Nat.factorial_le_pow r
      exact_mod_cast h1.trans h2
    have hfpos : (0 : ℝ) < (i.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos i
    have hpi : (1 : ℝ) ≤ 2 * Real.pi ^ (i + 1) := by
      have : (1 : ℝ) ≤ Real.pi ^ (i + 1) := one_le_pow₀ (by linarith [Real.pi_gt_three])
      linarith
    calc ((r : ℝ) ^ r)⁻¹ ≤ (i.factorial : ℝ)⁻¹ := inv_anti₀ hfpos hfac
      _ = 1 / (i.factorial : ℝ) := by rw [one_div]
      _ ≤ 2 * Real.pi ^ (i + 1) / (i.factorial : ℝ) := by gcongr

theorem formalDeg_div_volU_log_bound : ∀ (r n : ℕ) (d : ℝ) (lam : Fin r → ℝ), 1 ≤ r → 3 ≤ n → 0 ≤ d → StrictAnti lam → (∀ a b, |lam a - lam b| ≤ d + n + 3) → 0 < ReciprocityTheory.ChartRestriction.DS.volU r ∧ 0 < (∏ a : Fin r, ∏ b ∈ Finset.univ.filter (fun b : Fin r => a < b), |lam a - lam b|) / (∏ a : Fin r, ∏ b ∈ Finset.univ.filter (fun b : Fin r => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))) ∧ Real.log ((∏ a : Fin r, ∏ b ∈ Finset.univ.filter (fun b : Fin r => a < b), |lam a - lam b|) / (∏ a : Fin r, ∏ b ∈ Finset.univ.filter (fun b : Fin r => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))) / ReciprocityTheory.ChartRestriction.DS.volU r) ≤ 2 + (r : ℝ) ^ 2 * Real.log (2 * Real.sqrt 2 * (r : ℝ) ^ 2 * n * (d + 2)) := by
  intro r n d lam hr hn hd hlam hbd
  set P : ℝ := ∏ a : Fin r, ∏ b ∈ Finset.univ.filter (fun b : Fin r => a < b), |lam a - lam b| with hPdef
  set D : ℝ := ∏ a : Fin r, ∏ b ∈ Finset.univ.filter (fun b : Fin r => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) with hDdef
  set V : ℝ := ReciprocityTheory.ChartRestriction.DS.volU r with hVdef
  set M : ℝ := d + n + 3 with hMdef
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hM1 : (1 : ℝ) ≤ M := by rw [hMdef]; linarith
  have hVlow := volU_ge_inv_pow_of_formalDeg r hr
  have hVpos : 0 < V := lt_of_lt_of_le (by positivity) hVlow
  have hPpos : 0 < P := by
    apply Finset.prod_pos
    intro a _
    apply Finset.prod_pos
    intro b hb
    have hab : a < b := (Finset.mem_filter.mp hb).2
    exact abs_pos.mpr (sub_ne_zero.mpr (hlam hab).ne')
  have hD1 : 1 ≤ D := by
    have : (∏ _a : Fin r, ∏ _b ∈ Finset.univ.filter (fun b : Fin r => _a < b), (1 : ℝ)) ≤ D := by
      apply Finset.prod_le_prod₀
      · intro a _; positivity
      · intro a _
        apply Finset.prod_le_prod₀
        · intro b _; positivity
        · intro b hb
          have hab : a < b := (Finset.mem_filter.mp hb).2
          have : (a : ℕ) + 1 ≤ (b : ℕ) := hab
          have : ((a : ℕ) : ℝ) + 1 ≤ ((b : ℕ) : ℝ) := by exact_mod_cast this
          linarith
    simpa using this
  have hDpos : 0 < D := lt_of_lt_of_le one_pos hD1
  have hPle : P ≤ M ^ (r * r) := by
    have : P ≤ ∏ _a : Fin r, M ^ r := by
      apply Finset.prod_le_prod₀
      · intro a _; exact Finset.prod_nonneg (fun b _ => abs_nonneg _)
      · intro a _
        calc (∏ b ∈ Finset.univ.filter (fun b : Fin r => a < b), |lam a - lam b|)
            ≤ ∏ _b ∈ Finset.univ.filter (fun b : Fin r => a < b), M :=
              Finset.prod_le_prod₀ (fun b _ => abs_nonneg _) (fun b _ => hbd a b)
          _ = M ^ (Finset.univ.filter (fun b : Fin r => a < b)).card := Finset.prod_const _
          _ ≤ M ^ r := by
              apply pow_le_pow_right₀ hM1
              calc (Finset.univ.filter (fun b : Fin r => a < b)).card ≤ (Finset.univ : Finset (Fin r)).card :=
                    Finset.card_filter_le _ _
                _ = r := by simp
    calc P ≤ ∏ _a : Fin r, M ^ r := this
      _ = M ^ (r * r) := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
  have hVinv : V⁻¹ ≤ (r : ℝ) ^ (r * r) := by
    have h := inv_anti₀ (by positivity) hVlow
    rw [inv_pow, inv_inv, ← pow_mul] at h
    exact h
  have hQpos : 0 < P / D / V := by positivity
  have hQle : P / D / V ≤ (M * r) ^ (r * r) := by
    calc P / D / V ≤ P / V := by
          gcongr
          exact div_le_self hPpos.le hD1
      _ = P * V⁻¹ := div_eq_mul_inv _ _
      _ ≤ M ^ (r * r) * (r : ℝ) ^ (r * r) := by
          apply mul_le_mul hPle hVinv (by positivity) (by positivity)
      _ = (M * r) ^ (r * r) := (mul_pow _ _ _).symm
  refine ⟨hVpos, div_pos hPpos hDpos, ?_⟩
  have hsq : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  have hMn : M ≤ n * (d + 2) := by
    rw [hMdef]; nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ n - 1) hd]
  have hr2 : (r : ℝ) ≤ 2 * Real.sqrt 2 * (r : ℝ) ^ 2 := by nlinarith
  have hX : M * r ≤ 2 * Real.sqrt 2 * (r : ℝ) ^ 2 * n * (d + 2) := by
    calc M * r ≤ (n * (d + 2)) * (2 * Real.sqrt 2 * (r : ℝ) ^ 2) :=
          mul_le_mul hMn hr2 (by positivity) (by positivity)
      _ = 2 * Real.sqrt 2 * (r : ℝ) ^ 2 * n * (d + 2) := by ring
  have hMr : 0 < M * r := by positivity
  calc Real.log (P / D / V) ≤ Real.log ((M * r) ^ (r * r)) := Real.log_le_log hQpos hQle
    _ = ((r * r : ℕ) : ℝ) * Real.log (M * r) := Real.log_pow _ _
    _ = (r : ℝ) ^ 2 * Real.log (M * r) := by push_cast; ring
    _ ≤ (r : ℝ) ^ 2 * Real.log (2 * Real.sqrt 2 * (r : ℝ) ^ 2 * n * (d + 2)) := by
        gcongr
    _ ≤ 2 + (r : ℝ) ^ 2 * Real.log (2 * Real.sqrt 2 * (r : ℝ) ^ 2 * n * (d + 2)) := by linarith

end GlobalTheory.LowRow
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

noncomputable section

namespace GlobalTheory.LowRow.CompactDualScale

theorem omegaDensity_smul {P Q : ℕ} {μ : Measure (UpqT P Q)} {c : ENNReal} (a : ENNReal) (ha : a ≠ ⊤)
    (h : OmegaDensity μ c) : OmegaDensity (a • μ) (a * c) := by
  obtain ⟨lam, hlam, hl⟩ := h
  refine ⟨lam, hlam, ?_⟩
  refine (ENNReal.Tendsto.const_mul hl (Or.inr ha)).congr fun r => ?_
  rw [Measure.smul_apply, smul_eq_mul, mul_div_assoc]

theorem omegaDensity_unique {P Q : ℕ} {μ : Measure (UpqT P Q)} {c c' : ENNReal}
    (h : OmegaDensity μ c) (h' : OmegaDensity μ c') : c = c' := by
  obtain ⟨lam, hlam, hl⟩ := h
  obtain ⟨lam', hlam', hl'⟩ := h'
  rw [Formalism.IndefR.Eqv.MU.omegaLeb_unique hlam hlam'] at hl'
  exact tendsto_nhds_unique hl hl'

theorem isMinf_eq_volU_smul_cd : ∀ (cd : CDHaar) (p q : ℕ) (m : Measure (UpqT p q)), Lev.IsMinf m →
    m = ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.volU (p + q)) • cd.cd p q := by
  intro cd p q m hm
  obtain ⟨c, hc0, hctop, hpq, hN⟩ := cd.trick p q
  haveI := cd.haar (p + q) 0
  haveI := cd.prob (p + q)
  haveI := cd.haar p q
  have hmain := ReciprocityTheory.ChartRestriction.DS.PolarCoordinateComparison.omegaDensity_main (N := p + q) (cd.cd (p + q) 0)
  have hc := omegaDensity_unique hN hmain
  have hV : 0 < ReciprocityTheory.ChartRestriction.DS.volU (p + q) := ReciprocityTheory.ChartRestriction.DS.PolarCoordinateComparison.volU_pos (p + q)
  have hκ : (0 : ℝ) < 2 ^ ((p + q) * (p + q - 1) / 2) := by positivity
  have hmul : ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.volU (p + q)) * c = Formalism.L2.Theta.minfDensity (p + q) := by
    rw [hc, ← ENNReal.ofReal_mul hV.le, Formalism.L2.Theta.minfDensity]
    have e : ReciprocityTheory.ChartRestriction.DS.volU (p + q) * (1 / (2 ^ ((p + q) * (p + q - 1) / 2) * ReciprocityTheory.ChartRestriction.DS.volU (p + q)))
        = ((2 : ℝ) ^ ((p + q) * (p + q - 1) / 2))⁻¹ := by
      field_simp
    rw [e, ENNReal.ofReal_inv_of_pos hκ, ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
  have hV0 : ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.volU (p + q)) ≠ 0 := (ENNReal.ofReal_pos.2 hV).ne'
  have hm' : Lev.IsMinf (ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.volU (p + q)) • cd.cd p q) := by
    refine ⟨Measure.IsHaarMeasure.smul _ hV0 ENNReal.ofReal_ne_top, ?_⟩
    rw [← hmul]
    exact omegaDensity_smul _ ENNReal.ofReal_ne_top hpq
  exact Formalism.IndefR.Eqv.MU.isMinf_unique hm' hm

end GlobalTheory.LowRow.CompactDualScale
end
end
