module

public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle389
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle093
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.LeftInvOfIsSection
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockTranslateSchwartzMajorant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SigmaFiniteParameterProductMeasure
public import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2130
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.Bundle001
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaCoefficientOfConvergence
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle711
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle453
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle442
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle473
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Unfold2
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle712
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FineJacquetSegmentLengthTwo
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle713
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TypedSpaceApproximation
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle260
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle006

@[expose] public section

section

open scoped TensorProduct ENNReal Matrix Classical NNReal
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdelicU GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

noncomputable section

namespace GlobalTheory.CompanionTheory.Godement

open GlobalTheory.StdUnn.HeightExists GlobalTheory.StdUnn.PolesModel

theorem cosetConv_of_continuous_law : ∀ (D : D7) (n : ℕ) (χ : (AE D)ˣ →* Circle) (s₁ : ℂ) (φ : G D n → ℂ), Continuous φ →
    (∀ p ∈ P D n, ∀ a : GL (Fin n) (AE D), blkA (mat p) = a.1 → ∀ g,
      φ (p * g) = (χ (Matrix.GeneralLinearGroup.det a) : ℂ) *
        npow (absA D (Matrix.GeneralLinearGroup.det a)) (s₁ + (n : ℂ) / 2) * φ g) →
    (n : ℝ) / 2 < s₁.re → ∀ g : G D n, CosetConv (P D n) (GF D n) φ g := by
  intro D n χ s₁ φ hcont hlaw hs g
  obtain ⟨H, φ₀, -, -, hH, hsec, hne⟩ :=
    GlobalTheory.StdUnn.PolesModel.hypotheses_hold D n 0 (s₁.re : ℂ)
  have hconv0 := GlobalTheory.StdUnn.PolesModel.cosetConv_stdSec hH hsec
    (s := (s₁.re : ℂ)) (by simpa using hs) g
  have hstd : GlobalTheory.StdUnn.stdSec H φ₀ (s₁.re : ℂ) (s₁.re : ℂ) = φ₀ := by
    funext x
    simp [GlobalTheory.StdUnn.stdSec, GlobalTheory.Doubling.npow]
  rw [hstd] at hconv0
  have hK : IsCompact (↑(GlobalTheory.StdUnn.K D n) : Set (G D n)) :=
    GlobalTheory.StdUnn.HeightExists.isCompact_K
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 1 (GlobalTheory.StdUnn.K D n).one_mem)
  obtain ⟨k₀, -, hk₀⟩ := hK.exists_isMinOn ⟨1, (GlobalTheory.StdUnn.K D n).one_mem⟩
    hsec.2.1.norm.continuousOn
  have hc : 0 < ‖φ₀ k₀‖ := norm_pos_iff.mpr (hne k₀)
  have hχ : ∀ u : Circle, ‖(u : ℂ)‖ = 1 := fun u => by
    first
      | exact Circle.norm_coe u
      | exact mem_sphere_zero_iff_norm.mp u.2
      | simp [Circle.abs_coe]
  have key : ∀ x, ‖φ x‖ ≤ C / ‖φ₀ k₀‖ * ‖φ₀ x‖ := by
    intro x
    obtain ⟨p, hp, k, hk, rfl⟩ := GlobalTheory.StdUnn.Iwasawa.exists_mul D n x
    obtain ⟨a, ha⟩ := GlobalTheory.StdUnn.LeftInvSect.exists_blkA hp
    rw [hlaw p hp a ha k, hsec.1 p hp a ha k]
    have hu : IsUnit (GlobalTheory.Doubling.absA D (Matrix.GeneralLinearGroup.det a)) :=
      (Group.isUnit _).map _
    have hr : (0 : ℝ) < (GlobalTheory.Doubling.absA D (Matrix.GeneralLinearGroup.det a) : ℝ) :=
      NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hu.ne_zero)
    have hRR : ‖GlobalTheory.Doubling.npow (GlobalTheory.Doubling.absA D (Matrix.GeneralLinearGroup.det a))
          ((s₁.re : ℂ) + (n : ℂ) / 2)‖ =
        ‖GlobalTheory.Doubling.npow (GlobalTheory.Doubling.absA D (Matrix.GeneralLinearGroup.det a))
          (s₁ + (n : ℂ) / 2)‖ := by
      simp only [GlobalTheory.Doubling.npow]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hr, Complex.norm_cpow_eq_rpow_re_of_pos hr]
      congr 1 <;> simp
    have hb : ‖φ k‖ ≤ C / ‖φ₀ k₀‖ * ‖φ₀ k‖ := by
      refine le_trans (hC k hk) ?_
      calc C = C / ‖φ₀ k₀‖ * ‖φ₀ k₀‖ := (div_mul_cancel₀ C hc.ne').symm
        _ ≤ C / ‖φ₀ k₀‖ * ‖φ₀ k‖ :=
          mul_le_mul_of_nonneg_left (isMinOn_iff.mp hk₀ k hk) (div_nonneg hC0 hc.le)
    simp only [norm_mul, hχ, hRR]
    calc 1 * ‖GlobalTheory.Doubling.npow (GlobalTheory.Doubling.absA D (Matrix.GeneralLinearGroup.det a))
            (s₁ + (n : ℂ) / 2)‖ * ‖φ k‖
        ≤ 1 * ‖GlobalTheory.Doubling.npow (GlobalTheory.Doubling.absA D (Matrix.GeneralLinearGroup.det a))
            (s₁ + (n : ℂ) / 2)‖ * (C / ‖φ₀ k₀‖ * ‖φ₀ k‖) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = C / ‖φ₀ k₀‖ * (1 * ‖GlobalTheory.Doubling.npow (GlobalTheory.Doubling.absA D
            (Matrix.GeneralLinearGroup.det a)) (s₁ + (n : ℂ) / 2)‖ * ‖φ₀ k‖) := by ring
  unfold GlobalTheory.Eis.CosetConv at hconv0 ⊢
  refine Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => ?_)
    (hconv0.mul_left (C / ‖φ₀ k₀‖))
  simp only [GlobalTheory.Eis.term]
  exact key _

end GlobalTheory.CompanionTheory.Godement

end
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ThTot

theorem continuous_integral_mul_of_bdd {X Y : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] {ν : Measure Y}
    {f : X → Y → ℂ} (hf : Continuous fun w : X × Y => f w.1 w.2) {B : ℝ} (hB : ∀ x y, ‖f x y‖ ≤ B)
    {g : Y → ℂ} (hg : Integrable g ν) : Continuous fun x => ∫ y, f x y * g y ∂ν := by
  refine continuous_of_dominated (bound := fun y => B * ‖g y‖) (fun x => ?_)
    (fun x => ae_of_all _ fun y => ?_) (hg.norm.const_mul B) (ae_of_all _ fun y => ?_)
  · have h1 : Continuous (f x) := hf.comp (continuous_const.prodMk continuous_id)
    exact h1.aestronglyMeasurable.mul hg.1
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hB x y) (norm_nonneg _)
  · have h1 : Continuous fun x => f x y := hf.comp (continuous_id.prodMk continuous_const)
    exact h1.mul continuous_const

theorem integral_integral_mul_of_bdd {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
    [SFinite μ] [SFinite ν] {F : X × Y → ℂ} (hF : AEStronglyMeasurable F (μ.prod ν)) {B : ℝ} (hB : ∀ w, ‖F w‖ ≤ B)
    {a : X → ℂ} {c : Y → ℂ} (ha : Integrable a μ) (hc : Integrable c ν) :
    ∫ x, (∫ z, F (x, z) * c z ∂ν) * a x ∂μ = ∫ w, F w * (a w.1 * c w.2) ∂(μ.prod ν) := by
  have hI : Integrable (fun w : X × Y => F w * (a w.1 * c w.2)) (μ.prod ν) :=
    (ha.mul_prod hc).bdd_mul hF (ae_of_all _ hB)
  rw [integral_prod _ hI]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  show (∫ z, F (x, z) * c z ∂ν) * a x = ∫ z, F (x, z) * (a x * c z) ∂ν
  rw [← integral_mul_const]
  exact integral_congr_ae (ae_of_all _ fun z => by ring)

variable {D : D7} {r s p : ℕ}

theorem rowT_rowJ (x : Mx D r p) (z : Mx D s p) : rowT (rowJ x z) = x := by
  refine Matrix.ext fun i j => ?_
  simp [rowT, rowJ]

theorem rowB_rowJ (x : Mx D r p) (z : Mx D s p) : rowB (rowJ x z) = z := by
  refine Matrix.ext fun i j => ?_
  simp [rowB, rowJ]

theorem rowJ_rowT_rowB (y : Mx D (r + s) p) : rowJ (rowT y) (rowB y) = y := by
  refine Matrix.ext fun i j => ?_
  induction i using Fin.addCases with
  | left a => simp [rowT, rowJ]
  | right b => simp [rowB, rowJ]

theorem continuous_rowT : Continuous (rowT : Mx D (r + s) p → Mx D r p) :=
  continuous_matrix fun _ _ => continuous_id.matrix_elem _ _

theorem continuous_rowB : Continuous (rowB : Mx D (r + s) p → Mx D s p) :=
  continuous_matrix fun _ _ => continuous_id.matrix_elem _ _

theorem continuous_rowJ : Continuous fun w : Mx D r p × Mx D s p => rowJ w.1 w.2 := by
  refine continuous_matrix fun i j => ?_
  induction i using Fin.addCases with
  | left a =>
    simp only [rowJ, Fin.addCases_left]
    exact continuous_fst.matrix_elem a j
  | right b =>
    simp only [rowJ, Fin.addCases_right]
    exact continuous_snd.matrix_elem b j

theorem continuous_th_one {ρ : ℕ} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D} {b₀ : HermE D ρ}
    {μ : Measure (Mx D ρ p)} {Ω : G D p → Mx D ρ p → ℂ} (hΩ : IsTh ψ χ θ b₀ μ Ω) : Continuous (Ω 1) :=
  hΩ.cont.comp (continuous_const.prodMk continuous_id)

theorem integrable_conj {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → ℂ} (hf : Integrable f μ) :
    Integrable (fun x => conj (f x)) μ :=
  (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hf

theorem stepTotal : ProdTh → ProdMeas → StepTotal := by
  intro hP hM D r s p μr Fr μs Fs μ F hr hs h ψ hψ χr χs θ hθ br bs b hb Tr Ts u hu hbd horth
  obtain ⟨B, hB⟩ := hbd
  have hμ := hM D r s p μr Fr μs Fs μ F hr hs h
  subst hμ
  haveI : SecondCountableTopology (Mx D r p) := (GlobalTheory.MixModel.lattice_Mx D r p).2.2.1
  haveI : SecondCountableTopology (Mx D s p) := (GlobalTheory.MixModel.lattice_Mx D s p).2.2.1
  haveI : SecondCountableTopology (Mx D (r + s) p) := (GlobalTheory.MixModel.lattice_Mx D (r + s) p).2.2.1
  haveI : FirstCountableTopology (Mx D r p) :=
    TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _
  haveI : IsTopologicalAddGroup (Mx D r p) := (GlobalTheory.MixModel.lattice_Mx D r p).1
  haveI : IsTopologicalAddGroup (Mx D s p) := (GlobalTheory.MixModel.lattice_Mx D s p).1
  haveI : LocallyCompactSpace (Mx D r p) := (GlobalTheory.MixModel.lattice_Mx D r p).2.1
  haveI : LocallyCompactSpace (Mx D s p) := (GlobalTheory.MixModel.lattice_Mx D s p).2.1
  haveI : BorelSpace (Mx D r p) := ⟨rfl⟩
  haveI : BorelSpace (Mx D s p) := ⟨rfl⟩
  haveI : BorelSpace (Mx D (r + s) p) := ⟨rfl⟩
  haveI := hr.1
  haveI := hs.1
  have hcJ := continuous_rowJ (D := D) (r := r) (s := s) (p := p)
  have hcF : Continuous fun w : Mx D r p × Mx D s p => u (rowJ w.1 w.2) := hu.comp hcJ
  have key : ∀ Ωr Ωs, IsTh ψ χr θ br μr Ωr → IsTh ψ χs θ bs μs Ωs →
      ∫ x, (∫ z, u (rowJ x z) * conj (Ωs 1 z) ∂μs) * conj (Ωr 1 x) ∂μr = 0 := by
    intro Ωr Ωs hΩr hΩs
    have hT := hP D r s p μr Fr μs Fs hr hs ψ hψ χr χs θ hθ br bs b hb Ωr Ωs hΩr hΩs
    have h0 := horth _ hT
    have hm : Continuous fun y : Mx D (r + s) p => u y * conj (Ωr 1 (rowT y) * Ωs 1 (rowB y)) :=
      hu.mul (Complex.continuous_conj.comp (((continuous_th_one hΩr).comp continuous_rowT).mul
        ((continuous_th_one hΩs).comp continuous_rowB)))
    rw [integral_map hcJ.aemeasurable hm.aestronglyMeasurable] at h0
    rw [integral_integral_mul_of_bdd (F := fun w : Mx D r p × Mx D s p => u (rowJ w.1 w.2))
      hcF.aestronglyMeasurable (fun w => hB _)
      (integrable_conj (GlobalTheory.CompanionTheory.BigCellJ.integrable_schwartzA hθ hr (hΩr.mem 1)))
      (integrable_conj (GlobalTheory.CompanionTheory.BigCellJ.integrable_schwartzA hθ hs (hΩs.mem 1)))]
    simpa only [rowT_rowJ, rowB_rowJ, map_mul] using h0
  have hv : ∀ Ωs, IsTh ψ χs θ bs μs Ωs → ∀ x, ∫ z, u (rowJ x z) * conj (Ωs 1 z) ∂μs = 0 := by
    intro Ωs hΩs
    have hi : Integrable (fun z => conj (Ωs 1 z)) μs :=
      integrable_conj (GlobalTheory.CompanionTheory.BigCellJ.integrable_schwartzA hθ hs (hΩs.mem 1))
    refine congrFun (Tr (fun x => ∫ z, u (rowJ x z) * conj (Ωs 1 z) ∂μs) ?_ ?_ ?_)
    · exact continuous_integral_mul_of_bdd (f := fun x z => u (rowJ x z)) hcF (fun _ _ => hB _) hi
    · refine ⟨B * ∫ z, ‖conj (Ωs 1 z)‖ ∂μs, fun x => ?_⟩
      refine (norm_integral_le_integral_norm _).trans ?_
      rw [← integral_const_mul]
      refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) (hi.norm.const_mul B) (ae_of_all _ fun z => ?_)
      show ‖u (rowJ x z) * conj (Ωs 1 z)‖ ≤ B * ‖conj (Ωs 1 z)‖
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)
    · exact fun Ωr hΩr => key Ωr Ωs hΩr hΩs
  have hz : ∀ x, (fun z => u (rowJ x z)) = 0 := fun x =>
    Ts (fun z => u (rowJ x z)) (hu.comp (hcJ.comp (continuous_const.prodMk continuous_id))) ⟨B, fun _ => hB _⟩
      fun Ωs hΩs => hv Ωs hΩs x
  funext y
  rw [← rowJ_rowT_rowB y]
  exact congrFun (hz (rowT y)) (rowB y)

end GlobalTheory.CompanionTheory.ThTot

end
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ColumnSplitting.Cov

variable {D : D7} {n t : ℕ} {B W : HSp D}

theorem jn_bl {a r : ℕ} (hn : r + t = n) (w : Mx D a r) (v : Mx D a t) (g : Mx D t t) :
    mm (jn hn w v) (bl hn 1 0 0 g) = jn hn w (mm v g) := by
  simp only [jn, bl, mm]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromCols_mul_fromBlocks]
  simp

theorem jn_c (hn : W.rank + t = n) {a : ℕ} (U : Mx D a n) : jn hn (c1 hn U) (c2 hn U) = U := by
  ext i j
  obtain ⟨k, rfl⟩ := (finSumFinEquiv.trans (finCongr hn)).surjective j
  rcases k with k | k <;> simp [jn, c1, c2]

theorem first_columns_join_eq (hn : W.rank + t = n) {a : ℕ} (w : Mx D a W.rank) (v : Mx D a t) : c1 hn (jn hn w v) = w := by
  ext i j
  simp [jn, c1]

theorem second_columns_join_eq (hn : W.rank + t = n) {a : ℕ} (w : Mx D a W.rank) (v : Mx D a t) : c2 hn (jn hn w v) = v := by
  ext i j
  simp [jn, c2]

theorem first_columns_mul_block_diagonal (hn : W.rank + t = n) {a : ℕ} (U : Mx D a n) (g : Mx D t t) :
    c1 hn (mm U (bl hn 1 0 0 g)) = c1 hn U := by
  conv_lhs => rw [← jn_c hn U, jn_bl, first_columns_join_eq]

theorem second_columns_mul_block_diagonal (hn : W.rank + t = n) {a : ℕ} (U : Mx D a n) (g : Mx D t t) :
    c2 hn (mm U (bl hn 1 0 0 g)) = mm (c2 hn U) g := by
  conv_lhs => rw [← jn_c hn U, jn_bl, second_columns_join_eq]

theorem map_char {A : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [LocallyCompactSpace A]
    [SecondCountableTopology A] [T2Space A]
    [MeasurableSpace A] [BorelSpace A] (μ : Measure A) [μ.IsAddHaarMeasure] (φ : A ≃ₜ+ A) (c : ℝ≥0) (hc0 : c ≠ 0)
    (hc : addEquivAddHaarChar φ = c) : μ.map φ = c⁻¹ • μ := by
  haveI : TopologicalSpace.PseudoMetrizableSpace A := inferInstance
  haveI : μ.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  have h4 := addEquivAddHaarChar_smul_map μ φ
  rw [hc] at h4
  conv_rhs => rw [← h4]
  rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]



theorem map_right (a b : ℕ) (μ : Measure (Mx D a b)) (hμ : μ.IsAddHaarMeasure) (g : GL (Fin b) (AE D)) :
    μ.map (fun y => mm y g.1) =
      ((absA D (Matrix.GeneralLinearGroup.det g))⁻¹ ^ a : ℝ≥0) • μ := by
  haveI := hμ
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D a b
  haveI : IsTopologicalAddGroup (Mx D a b) := i1
  haveI : LocallyCompactSpace (Mx D a b) := i2
  haveI : SecondCountableTopology (Mx D a b) := i3
  haveI : T2Space (Mx D a b) := i4
  haveI : BorelSpace (Mx D a b) := ⟨rfl⟩
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have hc : addEquivAddHaarChar (GlobalTheory.ModuLR.lrCE (1 : GL (Fin a) (AE D)) g) = absA D (Matrix.GeneralLinearGroup.det g) ^ a := by
    have := GlobalTheory.ResidueEisenstein.ModMat.addEquivAddHaarChar_lrCE D.host.F D.host.E D.sp.cm.sig (isCMExt_host D) a b
      (1 : GL (Fin a) (AE D)) g
    simpa using this
  have hA : absA D (Matrix.GeneralLinearGroup.det g) ≠ 0 := (GlobalTheory.CompanionTheory.IwaAd.absA_pos _).ne'
  have e : (fun y : Mx D a b => mm y g.1) = GlobalTheory.ModuLR.lrCE (1 : GL (Fin a) (AE D)) g := by
    funext y
    rw [GlobalTheory.ModuLR.lrCE_apply, Units.val_one, Matrix.one_mul]
  rw [e, inv_pow]
  exact map_char μ _ _ (pow_ne_zero _ hA) hc

end GlobalTheory.CompanionTheory.ColumnSplitting.Cov

end
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.height_K_invariance : PositivityTheory.PfSWUS.HeightKInv := by
  first | exact @GlobalTheory.CompanionTheory.PfSWUS.height_mul_K | exact GlobalTheory.CompanionTheory.PfSWUS.height_mul_K | (intros; apply GlobalTheory.CompanionTheory.PfSWUS.height_mul_K <;> assumption)
end
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.theta_coefficient_of_convergence : GlobalTheory.Published.WeilThetaConvergence → PositivityTheory.PfSWUS.ThetaCoef := by
  first | exact @GlobalTheory.CompanionTheory.ThetaCoefND.thetaCoef | exact GlobalTheory.CompanionTheory.ThetaCoefND.thetaCoef | (intros; apply GlobalTheory.CompanionTheory.ThetaCoefND.thetaCoef <;> assumption)
end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.theta_integral_continuous : ∀ (D : D7) (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (μ : Measure (Mx D V.rank r)) (φ : Mx D V.rank r → ℂ), IsCharAF D.host.F ψ → IsInfFam θ → (∃ 𝓕, IsCovolOne (ratMx D V.rank r) μ 𝓕) → φ ∈ schwartzA θ V.rank r → Continuous (Jt ψ V μ φ) := by
  first | exact @GlobalTheory.CompanionTheory.BigCellJ.jt_continuous | exact GlobalTheory.CompanionTheory.BigCellJ.jt_continuous | (intros; apply GlobalTheory.CompanionTheory.BigCellJ.jt_continuous <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisCellsTheta

theorem thetaInv : PositivityTheory.GramSchwartzFunctions.EC.ThetaInv := by
  intro D n V ψ χ θ μ ω hS
  let S : Subgroup (G D n) :=
    { carrier := {γ | ∀ Φ : schwartzA θ V.rank n,
        ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, (ω γ Φ).1 (ξ.map (incA D)) =
          ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, Φ.1 (ξ.map (incA D))}
      one_mem' := fun Φ => by simp
      mul_mem' := fun {g h} hg hh Φ => by
        rw [map_mul, Module.End.mul_apply]
        exact (hg _).trans (hh Φ)
      inv_mem' := fun {g} hg Φ => by
        have := hg (ω g⁻¹ Φ)
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at this
        exact this.symm }
  have hle : GF D n ≤ S := GlobalTheory.T.rational_group_le_of_generators_mem D n S (fun g a hg Φ => GlobalTheory.T.theta_sum_invariant_levi_element D n V ψ χ θ μ ω hS g a hg Φ)
    (fun g b hg Φ => GlobalTheory.T.theta_sum_invariant_unipotent_translate D n V ψ χ θ μ ω hS g b hg Φ)
    (fun g hg Φ => GlobalTheory.T.theta_sum_invariant_weyl_involution D n V ψ χ θ μ ω hS g hg Φ)
  intro Φ γ hγ
  exact hle hγ Φ

end GlobalTheory.CompanionTheory.EisCellsTheta
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.eisenstein_unfolding_second_term : PositivityTheory.GramSchwartzFunctions.EC.Unfold2 := by
  first | exact @GlobalTheory.CompanionTheory.EisUnfold.unfold2 | exact GlobalTheory.CompanionTheory.EisUnfold.unfold2 | (intros; apply GlobalTheory.CompanionTheory.EisUnfold.unfold2 <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

theorem _root_.GlobalTheory.T.fine_jacquet_segment_length_two : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hZ : GlobalTheory.Published.SegmentRepresentation) (Δ : Segment k) (h : Δ.len = 2), FineJac Δ := by
  first | exact @GlobalTheory.CompanionTheory.SegFine2.fineJac_of_len_eq_two | exact GlobalTheory.CompanionTheory.SegFine2.fineJac_of_len_eq_two | (intros; apply GlobalTheory.CompanionTheory.SegFine2.fineJac_of_len_eq_two <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

theorem _root_.GlobalTheory.T.segment_product_word_in_shuffle : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL), LSegJacquet k → ∀ {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) (Δ : Fin h → Segment k), (∀ i, IsLSeg (Δ i) (x i).rep) → ∀ w : List (IrrGL (k := k)), (∀ c ∈ w, c.IsCusp) → Wd (prodIrr x hd) w → InShW (Finset.univ.val.map Δ) w := by
  first | exact @GlobalTheory.CompanionTheory.CuspShuffle.inShW_of_wd | exact GlobalTheory.CompanionTheory.CuspShuffle.inShW_of_wd | (intros; apply GlobalTheory.CompanionTheory.CuspShuffle.inShW_of_wd <;> assumption)
end

section

open scoped Classical
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation

theorem _root_.GlobalTheory.T.typed_space_approximation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)]
  (μ : Measure (GA E N)) [μ.IsHaarMeasure] (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ))
  (R ε δ : ℝ) (α : GA E N → ℂ) (F : Set (GA E N)), IsOpen (K : Set (GL (Fin N) (Af E))) → FiniteDimensional ℂ W → 0 < ε →
  Continuous α → HasCompactSupport α → 0 < δ → IsFundamentalDomain (latticeGL E N) F μ →
  ∃ Ω : Set (GA E N), IsCompact Ω ∧ ∀ (V : Submodule ℂ (Sm E N)) (ψ : Sm E N), IsDiscrete V → ψ ∈ V → TypeB K W ψ →
    InfBdd R V → (∀ r, 0 < r → r < N → ∀ c ∈ ExpV r V, pE E N r c ≤ -ε * (r * ((N : ℝ) - r))) →
    (∃ s : ℂ, δ ≤ ‖s‖ ∧ ∀ x, ∫ y, α y * ψ.1 (x * y) ∂μ = s * ψ.1 x) →
    (∫⁻ x in F, ‖ψ.1 x‖ₑ ^ 2 ∂μ) = 1 → 1 ≤ 2 * ∫⁻ x in Ω, ‖ψ.1 x‖ₑ ^ 2 ∂μ := by
  first | exact @GlobalTheory.CompanionTheory.Conc.conc | exact GlobalTheory.CompanionTheory.Conc.conc | (intros; apply GlobalTheory.CompanionTheory.Conc.conc <;> assumption)
end
