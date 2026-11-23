module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSelfDualSiegelWeilMeasures
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle442
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDetSmulSubOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1294
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaCoefficientOfConvergence
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.LeftInvOfIsSection
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle260

@[expose] public section

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LThCoef

variable {D : D7}

abbrev Sp (W : HSp D) (n : ℕ) : Type := {x : Matrix (Fin W.rank) (Fin n) D.host.E // x.rank = W.rank}

instance countable_sp (W : HSp D) (n : ℕ) : Countable (Sp W n) := by
  have := GlobalTheory.ThetaTransformMeas.countable_field D.host.E
  have : Countable (Matrix (Fin W.rank) (Fin n) D.host.E) :=
    inferInstanceAs (Countable (Fin W.rank → Fin n → D.host.E))
  infer_instance

theorem ip_inv (W : HSp D) {n : ℕ} (h : GA D W) (y : Matrix (Fin W.rank) (Fin n) D.host.E) :
    ip W (mm (mt W h⁻¹) (rat y)) (mm (mt W h⁻¹) (rat y)) = rat (gramQ W y) := by
  have hu := GlobalTheory.RatAut.mt_unitary W h⁻¹
  have hr := GlobalTheory.CompanionTheory.ThetaCoefND.rat_gramQ W y
  show ((Formalism.L2.Theta.mt W h⁻¹ * y.map (Formalism.L2.Theta.incA D)).map (Formalism.L2.Theta.cA D)).transpose *
      ((Formalism.BasicNotions.HSpace.gram W).map (Formalism.L2.Theta.incA D) *
        (Formalism.L2.Theta.mt W h⁻¹ * y.map (Formalism.L2.Theta.incA D))) =
    (gramQ W y).map (Formalism.L2.Theta.incA D)
  rw [hr]
  show _ = ((y.map (Formalism.L2.Theta.incA D)).map (Formalism.L2.Theta.cA D)).transpose *
      ((Formalism.BasicNotions.HSpace.gram W).map (Formalism.L2.Theta.incA D) * y.map (Formalism.L2.Theta.incA D))
  rw [Matrix.map_mul, Matrix.transpose_mul]
  calc _ = ((y.map (Formalism.L2.Theta.incA D)).map (Formalism.L2.Theta.cA D)).transpose *
        ((((Formalism.L2.Theta.mt W h⁻¹).map (Formalism.L2.Theta.cA D)).transpose *
          (Formalism.BasicNotions.HSpace.gram W).map (Formalism.L2.Theta.incA D) * Formalism.L2.Theta.mt W h⁻¹) *
          y.map (Formalism.L2.Theta.incA D)) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hu]

theorem pch_rat (ψ : AddChar (AF D.host.F) ℂ) {n : ℕ} (x : hermA D n) (T : HermE D n) :
    pch ψ x.1 (rat T.1) = GlobalTheory.CompanionTheory.SiegelND.pairH ψ (GlobalTheory.CompanionTheory.HermPoisson.ofHermE T).1 x := by
  show ψ (GlobalTheory.StdUnn.halfTr (Matrix.trace (x.1 * rat T.1))) =
    ψ (GlobalTheory.StdUnn.halfTr (Matrix.trace (rat T.1 * x.1)))
  rw [Matrix.trace_mul_comm]

theorem conj_eq_inv {z : ℂ} (hz : ‖z‖ = 1) : conj z = z⁻¹ := by
  rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hz]
  simp

variable {W : HSp D} {n : ℕ} {m : Measure (GA D W)} {𝓕 : Set (GA D W)} {Ψ : Mx D W.rank n → ℂ}

theorem cont_term (hΨ : Continuous Ψ) (y : Matrix (Fin W.rank) (Fin n) D.host.E) :
    Continuous fun h : GA D W => Ψ (mm (mt W h⁻¹) (rat y)) := by
  exact hΨ.comp ((GlobalTheory.RealWeil.continuous_mt W).2.matrix_mul continuous_const)

def co (W : HSp D) (m : Measure (GA D W)) (𝓕 : Set (GA D W)) (Ψ : Mx D W.rank n → ℂ)
    (y : Matrix (Fin W.rank) (Fin n) D.host.E) : ℂ :=
  ∫ h in 𝓕, Ψ (mm (mt W h⁻¹) (rat y)) ∂m

theorem lint_fin (hvol : m 𝓕 < ⊤) (hΨ : Continuous Ψ) {C : ℝ≥0}
    (hC : ∀ h : GA D W, ∑' x : Sp W n, ‖Ψ (mm (mt W h⁻¹) (rat x.1))‖ₑ ≤ C) :
    ∑' y : Sp W n, ∫⁻ h in 𝓕, ‖Ψ (mm (mt W h⁻¹) (rat y.1))‖ₑ ∂m < ⊤ := by
  have hmeas : ∀ y : Sp W n, AEMeasurable (fun h : GA D W => ‖Ψ (mm (mt W h⁻¹) (rat y.1))‖ₑ)
      (m.restrict 𝓕) := fun y => (cont_term hΨ y.1).enorm.measurable.aemeasurable
  calc ∑' y : Sp W n, ∫⁻ h in 𝓕, ‖Ψ (mm (mt W h⁻¹) (rat y.1))‖ₑ ∂m
      = ∫⁻ h in 𝓕, ∑' y : Sp W n, ‖Ψ (mm (mt W h⁻¹) (rat y.1))‖ₑ ∂m :=
        (MeasureTheory.lintegral_tsum hmeas).symm
    _ ≤ ∫⁻ _ in 𝓕, (C : ℝ≥0∞) ∂m := MeasureTheory.lintegral_mono (fun h => hC h)
    _ = C * m 𝓕 := MeasureTheory.setLIntegral_const 𝓕 C
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.coe_lt_top hvol

theorem tsum_co_ne_top (hvol : m 𝓕 < ⊤) (hΨ : Continuous Ψ) {C : ℝ≥0}
    (hC : ∀ h : GA D W, ∑' x : Sp W n, ‖Ψ (mm (mt W h⁻¹) (rat x.1))‖ₑ ≤ C) :
    ∑' y : Sp W n, ‖co W m 𝓕 Ψ y.1‖ₑ ≠ ⊤ := by
  refine ne_top_of_le_ne_top (lint_fin hvol hΨ hC).ne (ENNReal.tsum_le_tsum (fun y => ?_))
  exact MeasureTheory.enorm_integral_le_lintegral_enorm _

theorem summable_co (hvol : m 𝓕 < ⊤) (hΨ : Continuous Ψ) {C : ℝ≥0}
    (hC : ∀ h : GA D W, ∑' x : Sp W n, ‖Ψ (mm (mt W h⁻¹) (rat x.1))‖ₑ ≤ C) :
    Summable fun y : Sp W n => ‖co W m 𝓕 Ψ y.1‖ := by
  have h := tsum_co_ne_top hvol hΨ hC
  simp only [enorm_eq_nnnorm] at h
  exact NNReal.summable_coe.mpr (ENNReal.tsum_coe_ne_top_iff_summable.mp h)

theorem exch (hvol : m 𝓕 < ⊤) (hΨ : Continuous Ψ) {C : ℝ≥0}
    (hC : ∀ h : GA D W, ∑' x : Sp W n, ‖Ψ (mm (mt W h⁻¹) (rat x.1))‖ₑ ≤ C) (c : Sp W n → ℂ) (hc : ∀ y, ‖c y‖ = 1) :
    ∫ h in 𝓕, ∑' y : Sp W n, c y * Ψ (mm (mt W h⁻¹) (rat y.1)) ∂m = ∑' y : Sp W n, c y * co W m 𝓕 Ψ y.1 := by
  have hf : ∀ y : Sp W n, MeasureTheory.AEStronglyMeasurable
      (fun h : GA D W => c y * Ψ (mm (mt W h⁻¹) (rat y.1))) (m.restrict 𝓕) :=
    fun y => (continuous_const.mul (cont_term hΨ y.1)).aestronglyMeasurable
  have hc' : ∀ y, ‖c y‖ₑ = 1 := fun y => by
    rw [← ofReal_norm, hc y, ENNReal.ofReal_one]
  have hf' : ∑' y : Sp W n, ∫⁻ h in 𝓕, ‖c y * Ψ (mm (mt W h⁻¹) (rat y.1))‖ₑ ∂m ≠ ⊤ := by
    simp_rw [enorm_mul, hc', one_mul]
    exact (lint_fin hvol hΨ hC).ne
  rw [MeasureTheory.integral_tsum hf hf']
  congr 1
  funext y
  rw [MeasureTheory.integral_const_mul]
  rfl

end PositivityTheory.Rg.Rsw.L.LThCoef

end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LCfRel

open Set GlobalTheory.Eis GlobalTheory.StdUnn.HeightExists GlobalTheory.StdUnn.PolesModel

variable {D : D7} {n : ℕ}

theorem law_fam {H : G D n → ℝ≥0} (hH : IsHt H) {χ : (AE D)ˣ →* Circle} {s₁ : ℂ} {φ : G D n → ℂ} (h : IsLaw χ s₁ φ)
    (z : ℂ) : IsLaw χ z (fam H φ s₁ z) := by
  intro q hq a ha g
  simp only [fam]
  rw [hH.2.2 q hq a ha g, h q hq a ha g, npow_mul]
  have e : npow (absA D (Matrix.GeneralLinearGroup.det a)) (z + (n : ℂ) / 2) =
      npow (absA D (Matrix.GeneralLinearGroup.det a)) (z - s₁) *
        npow (absA D (Matrix.GeneralLinearGroup.det a)) (s₁ + (n : ℂ) / 2) := by
    rw [← npow_add (hom_pos _ _)]; congr 1; ring
  rw [e]; ring

theorem cont_fam {H : G D n → ℝ≥0} (hH : IsHt H) {φ : G D n → ℂ} (hφ : Continuous φ) (s₁ : ℂ) :
    Continuous fun u : ℂ × G D n => fam H φ s₁ u.1 u.2 := by
  simp only [fam, npow_eq_exp (hH.2.1 _)]
  have h1 : Continuous fun u : ℂ × G D n => Real.log (H u.2 : ℝ) :=
    (NNReal.continuous_coe.comp (hH.1.comp continuous_snd)).log fun u => (NNReal.coe_pos.2 (hH.2.1 _)).ne'
  exact (((Complex.continuous_ofReal.comp h1).mul (continuous_fst.sub continuous_const)).cexp).mul
    (hφ.comp continuous_snd)

def cset (nb : hermA D n → G D n) {v : Pl D} (C : Cut D n v) (g : G D n) : Set (G D n) :=
  ⋃ x ∈ C.s, (fun k => g * k * nb x) '' (K D n : Set (G D n))

theorem isCompact_cset (nb : hermA D n → G D n) {v : Pl D} (C : Cut D n v) (g : G D n) : IsCompact (cset nb C g) :=
  C.s.isCompact_biUnion fun _ _ => isCompact_K.image ((continuous_const.mul continuous_id).mul continuous_const)

theorem mem_cset (nb : hermA D n → G D n) {v : Pl D} (C : Cut D n v) (g : G D n) (u : KAt D n v) {x : hermA D n}
    (hx : x ∈ C.s) : g * (u : G D n) * nb x ∈ cset nb C g :=
  mem_biUnion hx ⟨u, (Subgroup.mem_inf.1 u.2).1, rfl⟩

theorem farRight {χ : (AE D)ˣ →* Circle} {H : G D n → ℝ≥0} (hH : IsHt H) {s₀ : ℂ} {φ : G D n → ℂ}
    (hφc : Continuous φ) (hφl : IsLaw χ s₀ φ) (nb : hermA D n → G D n) {v : Pl D} (C : Cut D n v) (c : ℂ → ℂ)
    (νv : Measure (KAt D n v)) [IsFiniteMeasure νv]
    (hrel : ∀ z g, ∫ k, cutR nb C (fam H φ s₀ z) (g * k) ∂νv = c z * fam H φ s₀ z g)
    {z : ℂ} (hz : (n : ℝ) / 2 < z.re) (g : G D n) :
    ∫ u, cutR nb C (eisS (fam H φ s₀ z)) (g * u) ∂νv = c z * eisS (fam H φ s₀ z) g := by
  have := t2Space_adeleRing' (F := D.host.F)
  have hcont := cont_fam hH hφc s₀
  have hz' : Continuous (fam H φ s₀ z) := hcont.comp (continuous_const.prodMk continuous_id)
  obtain ⟨w, hw, hwb⟩ := exists_majorant (P := P D n) (Γ := GF D n) (χ := χ.comp detP) (ρ := (n : ℝ) / 2)
    (σ := (n : ℝ) / 2) (Φ := fam H φ s₀) isIwasawa isCompact_K hcont.continuousOn
    (fun s _ q g => by
      have := law_fam hH hφl s q q.2 (leviBlock (D := D) (n := n) q) rfl g
      push_cast
      exact this)
    (fun τ hτ => summable_spherical τ hτ) isCompact_singleton (singleton_subset_iff.2 hz) (isCompact_cset nb C g)
  have hb : ∀ q (u : KAt D n v) x, x ∈ C.s →
      ‖fam H φ s₀ z (((q.out : GF D n) : G D n) * g * u * nb x)‖ ≤ w q := fun q u x hx => by
    have := hwb q z rfl _ (mem_cset nb C g u hx)
    simpa only [term, mul_assoc] using this
  have hterm : ∀ u : KAt D n v, cutR nb C (eisS (fam H φ s₀ z)) (g * u) =
      ∑' q : Cosets (P D n) (GF D n), cutR nb C (fam H φ s₀ z) (((q.out : GF D n) : G D n) * g * u) := by
    intro u
    simp only [cutR, eisS, cosetSum]
    rw [Summable.tsum_finsetSum fun x hx => (Summable.of_norm_bounded hw fun q => by
      simpa only [term, mul_assoc] using hwb q z rfl _ (mem_cset nb C g u hx)).mul_left (C.co x)]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← tsum_mul_left]
    simp only [term, mul_assoc]
  calc ∫ u, cutR nb C (eisS (fam H φ s₀ z)) (g * u) ∂νv
      = ∫ u, ∑' q : Cosets (P D n) (GF D n), cutR nb C (fam H φ s₀ z) (((q.out : GF D n) : G D n) * g * u) ∂νv := by
        congr 1; funext u; exact hterm u
    _ = ∑' q : Cosets (P D n) (GF D n), ∫ u, cutR nb C (fam H φ s₀ z) (((q.out : GF D n) : G D n) * g * u) ∂νv := by
        refine integral_tsum_dom νv _ (fun q => (∑ x ∈ C.s, ‖C.co x‖) * w q) (hw.mul_left _) (fun q u => ?_)
          fun q => ?_
        · simp only [cutR]
          refine (norm_sum_le _ _).trans ?_
          rw [Finset.sum_mul]
          refine Finset.sum_le_sum fun x hx => ?_
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hb q u x hx) (norm_nonneg _)
        · refine Continuous.aestronglyMeasurable ?_
          simp only [cutR]
          exact continuous_finsetSum _ fun x _ => continuous_const.mul
            (hz'.comp ((continuous_const.mul continuous_subtype_val).mul continuous_const))
    _ = ∑' q : Cosets (P D n) (GF D n), c z * fam H φ s₀ z (((q.out : GF D n) : G D n) * g) := by
        congr 1; funext q; exact hrel z _
    _ = c z * eisS (fam H φ s₀ z) g := by
        rw [tsum_mul_left]; rfl

end PositivityTheory.Rg.Rsw.L.LCfRel

end
end
