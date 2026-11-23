module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle017
public import Formalism.SatakeDualWeyl.Statement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle616
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameStabilizerFlagConverse
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle459
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle037
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle056
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle054
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle018
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle053
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle621
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdicIntegersCompact.IsCompactAdicCompletionIntegers
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.Bundle002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle430
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle081
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle608
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle431

@[expose] public section

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal


theorem _root_.GlobalTheory.T.frame_stabilizer_flag_criterion : ∀ (L : Type) [Field L] (s : L →+* L), (∀ x, s (s x) = x) → ∀ (n r m : ℕ) (J : Matrix (Fin n) (Fin n) L) (X Y : Matrix (Fin n) (Fin r) L) (Z : Matrix (Fin n) (Fin m) L) (Qi : Matrix (Idx r m) (Fin n) L), cT s J = J → cT s X * J * X = 0 → cT s Y * J * Y = 0 → cT s X * J * Y = 1 → cT s X * J * Z = 0 → cT s Y * J * Z = 0 → Qi * frm X Z Y = 1 → frm X Z Y * Qi = 1 → ∀ (S : Finset (Fin r)) (g : Matrix (Fin n) (Fin n) L), IsUnit g → cT s g * J * g = J → (∀ j ∈ S, StabUpTo X g j) → (Qi * g * frm X Z Y).BlockTriangular (lev m S) := by
  first | exact @GlobalTheory.CompanionTheory.CFin.Tri.witt_blockTriangular | exact GlobalTheory.CompanionTheory.CFin.Tri.witt_blockTriangular | (intros; apply GlobalTheory.CompanionTheory.CFin.Tri.witt_blockTriangular <;> assumption)
end

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal


theorem _root_.GlobalTheory.T.frame_stabilizer_flag_converse : ∀ (L : Type) [Field L] (s : L →+* L), (∀ x, s (s x) = x) → ∀ (n r m : ℕ) (J : Matrix (Fin n) (Fin n) L) (X Y : Matrix (Fin n) (Fin r) L) (Z : Matrix (Fin n) (Fin m) L) (Qi : Matrix (Idx r m) (Fin n) L), cT s J = J → cT s X * J * X = 0 → cT s Y * J * Y = 0 → cT s X * J * Y = 1 → cT s X * J * Z = 0 → cT s Y * J * Z = 0 → Qi * frm X Z Y = 1 → frm X Z Y * Qi = 1 → ∀ (S : Finset (Fin r)) (g : Matrix (Fin n) (Fin n) L), IsUnit g → cT s g * J * g = J → (Qi * g * frm X Z Y).BlockTriangular (lev m S) → IsUnit (frm X Z Y * bd (lev m S) (Qi * g * frm X Z Y) * Qi) ∧ cT s (frm X Z Y * bd (lev m S) (Qi * g * frm X Z Y) * Qi) * J * (frm X Z Y * bd (lev m S) (Qi * g * frm X Z Y) * Qi) = J := by
  first | exact @GlobalTheory.CompanionTheory.CFin.BdU.bd_unitary | exact GlobalTheory.CompanionTheory.CFin.BdU.bd_unitary | (intros; apply GlobalTheory.CompanionTheory.CFin.BdU.bd_unitary <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WhitFree.Euler

theorem pureN_eq_indicator {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n M : ℕ}
    (φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ)
    (A : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
      Set (Fin n → Fin M → Fv F v ⊗[F] E))
    (X : Fin n → Fin M → AF F ⊗[F] E) :
    pureN φ A X = {X : Fin n → Fin M → AF F ⊗[F] E |
      ∀ v, HeckeCharacterZeroLocus.SiegelWeilU.projV v (HeckeCharacterZeroLocus.SiegelWeilU.projFin X) ∈ A v}.indicator
        (fun X => φ (HeckeCharacterZeroLocus.SiegelWeilU.projInf X)) X := by
  change φ (HeckeCharacterZeroLocus.SiegelWeilU.projInf X) *
    (boxF A).indicator (fun _ => (1 : ℂ)) (HeckeCharacterZeroLocus.SiegelWeilU.projFin X) = _
  by_cases hX : ∀ v, HeckeCharacterZeroLocus.SiegelWeilU.projV v (HeckeCharacterZeroLocus.SiegelWeilU.projFin X) ∈ A v
  · have h1 : HeckeCharacterZeroLocus.SiegelWeilU.projFin X ∈ boxF A := hX
    rw [Set.indicator_of_mem (show X ∈ {X : Fin n → Fin M → AF F ⊗[F] E |
      ∀ v, HeckeCharacterZeroLocus.SiegelWeilU.projV v (HeckeCharacterZeroLocus.SiegelWeilU.projFin X) ∈ A v} from hX),
      Set.indicator_of_mem h1, mul_one]
  · have h1 : HeckeCharacterZeroLocus.SiegelWeilU.projFin X ∉ boxF A := hX
    rw [Set.indicator_of_notMem (show X ∉ {X : Fin n → Fin M → AF F ⊗[F] E |
      ∀ v, HeckeCharacterZeroLocus.SiegelWeilU.projV v (HeckeCharacterZeroLocus.SiegelWeilU.projFin X) ∈ A v} from hX),
      Set.indicator_of_notMem h1, mul_zero]

theorem integrable_integral_pureN : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (M n d : ℕ) (b : Module.Basis (Fin d) F E) (I : Measure (Fin n → Fin M → AF F ⊗[F] E)) (c : NNReal) (minf : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (m : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)), GlobalTheory.CompanionTheory.SW.IsEulerProd b I c minf m → ∃ S₀ : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)), ∀ S, S₀ ⊆ S → ∀ φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ, Measurable φ → Integrable φ minf → ∀ A : (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Set (Fin n → Fin M → Fv F v ⊗[F] E)), (∀ v, MeasurableSet (A v)) → (∀ v, m v (A v) ≠ ⊤) → (∀ v, v ∉ S → A v = latV b v) → Integrable (pureN φ A) I ∧ ∫ X, pureN φ A X ∂I = (c : ℂ) * (∫ X, φ X ∂minf) * (∏ v ∈ S, ((m v (A v)).toReal : ℂ)) * ((∏' v : {v // v ∉ S}, (m v.1 (latV b v.1)).toReal : ℝ) : ℂ) := by
  intro F E _ _ _ _ _ M n d b I c minf m hE
  obtain ⟨-, -, S₀, hS₀⟩ := hE
  refine ⟨S₀, fun S hS φ hφ hφi A hA hfin hoff => ?_⟩
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
  have hB := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Euler.measurableSet_box b n M S A hA hoff
  have hp := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Euler.measurable_projInf (E := E) b n M
  set B : Set (Fin n → Fin M → AF F ⊗[F] E) :=
    {X | ∀ v, HeckeCharacterZeroLocus.SiegelWeilU.projV v (HeckeCharacterZeroLocus.SiegelWeilU.projFin X) ∈ A v} with hBdef
  set P : ℝ := ∏' v : {v // v ∉ S}, (m v.1 (latV b v.1)).toReal with hP
  have hP0 : 0 ≤ P := tprod_nonneg fun _ => ENNReal.toReal_nonneg
  set K : ℝ≥0∞ := (c : ℝ≥0∞) * (∏ v ∈ S, m v (A v)) * ENNReal.ofReal P with hK
  have hKtop : K ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ENNReal.prod_ne_top fun v _ => hfin v)) ENNReal.ofReal_ne_top
  have hmap : (I.restrict B).map HeckeCharacterZeroLocus.SiegelWeilU.projInf = K • minf := by
    ext T hT
    rw [Measure.map_apply hp hT, Measure.restrict_apply (hp hT), Measure.smul_apply, smul_eq_mul]
    have hform := hS₀ S hS (T.indicator 1) (fun v => (A v).indicator 1)
      (measurable_one.indicator hT) (fun v => measurable_one.indicator (hA v))
    simp_rw [GlobalTheory.CompanionTheory.SW.EulerBox.pureL_indicator_eq b S _ A hoff] at hform
    rw [lintegral_indicator hB, lintegral_indicator_one hT] at hform
    have hl : ∫⁻ X in B, T.indicator 1 (HeckeCharacterZeroLocus.SiegelWeilU.projInf X) ∂I =
        I (HeckeCharacterZeroLocus.SiegelWeilU.projInf ⁻¹' T ∩ B) := by
      have : (fun X => T.indicator (1 : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞) (HeckeCharacterZeroLocus.SiegelWeilU.projInf X)) =
          (HeckeCharacterZeroLocus.SiegelWeilU.projInf ⁻¹' T).indicator 1 := by
        funext X
        by_cases h : HeckeCharacterZeroLocus.SiegelWeilU.projInf X ∈ T
        · rw [Set.indicator_of_mem h,
            Set.indicator_of_mem (show X ∈ HeckeCharacterZeroLocus.SiegelWeilU.projInf ⁻¹' T from h)]
          rfl
        · rw [Set.indicator_of_notMem h,
            Set.indicator_of_notMem (show X ∉ HeckeCharacterZeroLocus.SiegelWeilU.projInf ⁻¹' T from h)]
      rw [this, lintegral_indicator_one (hp hT), Measure.restrict_apply (hp hT)]
    rw [hl] at hform
    change _ = _ * _ * ENNReal.ofReal P at hform
    rw [hform]
    simp_rw [lintegral_indicator_one (hA _)]
    rw [hK]; ring
  have hfun : pureN φ A = B.indicator (fun X => φ (HeckeCharacterZeroLocus.SiegelWeilU.projInf X)) :=
    funext fun X => pureN_eq_indicator φ A X
  refine ⟨?_, ?_⟩
  · have h1 : Integrable φ ((I.restrict B).map HeckeCharacterZeroLocus.SiegelWeilU.projInf) := by
      rw [hmap]; exact hφi.smul_measure hKtop
    have h2 := (integrable_map_measure hφ.aestronglyMeasurable hp.aemeasurable).1 h1
    rw [hfun]
    exact IntegrableOn.integrable_indicator h2 hB
  · have h1 : ∫ X, pureN φ A X ∂I = ∫ Y, φ Y ∂((I.restrict B).map HeckeCharacterZeroLocus.SiegelWeilU.projInf) := by
      rw [integral_map hp.aemeasurable hφ.aestronglyMeasurable, hfun]
      exact integral_indicator hB
    rw [h1, hmap, integral_smul_measure]
    have hKr : K.toReal = (c : ℝ) * (∏ v ∈ S, (m v (A v)).toReal) * P := by
      rw [hK, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_prod, ENNReal.toReal_ofReal hP0]
      simp
    rw [hKr, Complex.real_smul]
    push_cast
    ring

end GlobalTheory.CompanionTheory.WhitFree.Euler
end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.PfSWUS.FockSplit.Box

open NumberField IsDedekindDomain GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Dec
open PI.VolStabS.PositiveNearLattice PI.VolStabS.AdmissibleCompactSupport
open scoped _root_.Topology

variable {F : Type} [Field F] [NumberField F]
variable {E : Type} [Field E] [Algebra F E] [FiniteDimensional F E] {d : ℕ} (b : Module.Basis (Fin d) F E)

def lvN (v : HeightOneSpectrum (𝓞 F)) (P : AddSubgroup (Fv F v)) (n M : ℕ) :
    AddSubgroup (Fin n → Fin M → Fv F v ⊗[F] E) where
  carrier := {Z | ∀ a i k, crd b (Fv F v) (Z a i) k ∈ P}
  add_mem' hx hy a i k := by
    rw [Pi.add_apply, Pi.add_apply, crd_add]
    exact add_mem (hx a i k) (hy a i k)
  zero_mem' a i k := by
    rw [Pi.zero_apply, Pi.zero_apply, crd_zero]
    exact zero_mem P
  neg_mem' hx a i k := by
    rw [Pi.neg_apply, Pi.neg_apply, crd_neg]
    exact neg_mem (hx a i k)

theorem isClopen_lvN (v : HeightOneSpectrum (𝓞 F)) (P : OpenAddSubgroup (Fv F v)) (n M : ℕ) :
    IsClopen (lvN b v (P : AddSubgroup (Fv F v)) n M : Set (Fin n → Fin M → Fv F v ⊗[F] E)) := by
  have hc : ∀ (x : Fin n) (i : Fin M) (k : Fin d),
      Continuous (fun Y : Fin n → Fin M → Fv F v ⊗[F] E => crd b (Fv F v) (Y x i) k) :=
    fun x i k => (continuous_crd b (Fv F v) k).comp ((continuous_apply i).comp (continuous_apply x))
  have e : (lvN b v (P : AddSubgroup (Fv F v)) n M : Set (Fin n → Fin M → Fv F v ⊗[F] E)) = ⋂ x, ⋂ i, ⋂ k,
      (fun Y : Fin n → Fin M → Fv F v ⊗[F] E => crd b (Fv F v) (Y x i) k) ⁻¹' (P : Set (Fv F v)) := by
    ext Y
    simp [lvN]
  rw [e]
  exact ⟨isClosed_iInter fun x => isClosed_iInter fun i => isClosed_iInter fun k =>
    P.isClosed.preimage (hc x i k), isOpen_iInter_of_finite fun x =>
    isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun k => P.isOpen.preimage (hc x i k)⟩

theorem isCompact_lvN (v : HeightOneSpectrum (𝓞 F)) (P : OpenAddSubgroup (Fv F v)) (hP : P ≤ intSub v) (n M : ℕ) :
    IsCompact (lvN b v (P : AddSubgroup (Fv F v)) n M : Set (Fin n → Fin M → Fv F v ⊗[F] E)) :=
  (isCompact_latV b v n M).of_isClosed_subset (isClopen_lvN b v P n M).isClosed
    fun _ hZ a i k => hP (hZ a i k)

theorem projV_subN (v : HeightOneSpectrum (𝓞 F)) {n M : ℕ} (X Y : Fin n → Fin M → Af F ⊗[F] E) :
    projV v (X - Y) = projV v X - projV v Y := by
  funext a i
  simp [projV, map_sub]

def cosVN (v : HeightOneSpectrum (𝓞 F)) (P : OpenAddSubgroup (Fv F v)) {n M : ℕ}
    (a : Fin n → Fin M → Fv F v ⊗[F] E) : Set (Fin n → Fin M → Fv F v ⊗[F] E) :=
  {Z | Z - a ∈ lvN b v (P : AddSubgroup (Fv F v)) n M}

theorem isCompact_isOpen_cosVN (v : HeightOneSpectrum (𝓞 F)) (P : OpenAddSubgroup (Fv F v)) (hP : P ≤ intSub v)
    {n M : ℕ} (a : Fin n → Fin M → Fv F v ⊗[F] E) : IsCompact (cosVN b v P a) ∧ IsOpen (cosVN b v P a) := by
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _
  have e : cosVN b v P a = (Homeomorph.subRight a) ⁻¹' (lvN b v (P : AddSubgroup (Fv F v)) n M : Set _) := rfl
  rw [e]
  exact ⟨(Homeomorph.subRight a).isCompact_preimage.2 (isCompact_lvN b v P hP n M),
    (isClopen_lvN b v P n M).isOpen.preimage (Homeomorph.subRight a).continuous⟩

theorem cosVN_intSub (v : HeightOneSpectrum (𝓞 F)) {n M : ℕ} {a : Fin n → Fin M → Fv F v ⊗[F] E}
    (ha : a ∈ latV b v) : cosVN b v (intSub v) a = latV b v := by
  have ha' : a ∈ lvN b v ((intSub v : OpenAddSubgroup (Fv F v)) : AddSubgroup (Fv F v)) n M := ha
  ext Z
  have e1 : Z ∈ cosVN b v (intSub v) a ↔ Z - a ∈ lvN b v ((intSub v : OpenAddSubgroup (Fv F v)) : AddSubgroup (Fv F v)) n M :=
    Iff.rfl
  have e2 : Z ∈ latV b v ↔ Z ∈ lvN b v ((intSub v : OpenAddSubgroup (Fv F v)) : AddSubgroup (Fv F v)) n M := Iff.rfl
  rw [e1, e2, sub_eq_add_neg]
  exact add_mem_cancel_right (neg_mem ha')

theorem exists_box_combN {n M : ℕ} (g : (Fin n → Fin M → Af F ⊗[F] E) → ℂ) (hg : IsSB g) :
    ∃ (s : Finset (Fin n → Fin M → Af F ⊗[F] E))
      (A : (Fin n → Fin M → Af F ⊗[F] E) → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))
      (S : Finset (HeightOneSpectrum (𝓞 F))),
      (∀ a v, IsCompact (A a v) ∧ IsOpen (A a v)) ∧ (∀ a ∈ s, ∀ v, v ∉ S → A a v = latV b v) ∧
        ∀ Y, g Y = ∑ a ∈ s, g a * (boxF (A a)).indicator (fun _ => (1 : ℂ)) Y := by
  classical
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Af F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Af F) _
  have hU := invariant_mem_nhds hg.1 hg.2
  let Lc : (Fin n → Fin M → Fin d → Af F) → (Fin n → Fin M → Af F ⊗[F] E) :=
    fun c x i => ∑ k, c x i k • ((1 : Af F) ⊗ₜ[F] b k)
  have hL : Continuous Lc := by
    refine continuous_pi fun x => continuous_pi fun i => continuous_finsetSum _ fun k _ => ?_
    exact continuous_smul.comp
      (((continuous_apply k).comp ((continuous_apply i).comp (continuous_apply x))).prodMk
        continuous_const)
  have hL0 : Lc (fun _ _ _ => 0) = 0 := by
    funext x i
    simp [Lc]
  have hp : Lc ⁻¹' {u | ∀ x, g (x + u) = g x} ∈ 𝓝 (fun _ => fun _ => fun _ => (0 : Af F)) :=
    hL.continuousAt.preimage_mem_nhds (by rw [hL0]; exact hU)
  obtain ⟨W1, hW1, h1⟩ := exists_nhds_of_pi hp
  obtain ⟨W2, hW2, h2⟩ := exists_nhds_of_pi hW1
  obtain ⟨W, hW, h3⟩ := exists_nhds_of_pi hW2
  obtain ⟨T, P, hPO, hPT, hsub⟩ := exists_box_subset hW
  let B : AddSubgroup (Af F) :=
    { carrier := {y | ∀ v, y v ∈ P v}
      add_mem' := fun hx hy v => add_mem (hx v) (hy v)
      zero_mem' := fun v => zero_mem (P v)
      neg_mem' := fun hx v => neg_mem (hx v) }
  have hBo : IsOpen (B : Set (Af F)) := by
    have e : (B : Set (Af F)) = {y : Af F | ∀ v, y v ∈ v.adicCompletionIntegers F} ∩
        ⋂ v ∈ T, (fun y : Af F => y v) ⁻¹' (P v : Set (Fv F v)) := by
      ext y
      constructor
      · intro hy
        exact ⟨fun v => hPO v (hy v), Set.mem_iInter₂.2 fun v _ => hy v⟩
      · rintro ⟨hy1, hy2⟩ v
        by_cases hv : v ∈ T
        · exact Set.mem_iInter₂.1 hy2 v hv
        · rw [hPT v hv]
          exact hy1 v
    rw [e]
    refine IsOpen.inter ?_ (T.finite_toSet.isOpen_biInter fun v _ => (P v).isOpen.preimage
      (RestrictedProduct.continuous_eval (R := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) v))
    exact RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
      (fun v => Valued.isOpen_valuationSubring _)
  let L : AddSubgroup (Fin n → Fin M → Af F ⊗[F] E) :=
    { carrier := {X | ∀ a i k, crd b (Af F) (X a i) k ∈ B}
      add_mem' := fun {x y} hx hy a i k => by
        rw [Pi.add_apply, Pi.add_apply, crd_add]
        exact add_mem (hx a i k) (hy a i k)
      zero_mem' := fun a i k => by
        rw [Pi.zero_apply, Pi.zero_apply, crd_zero]
        exact zero_mem B
      neg_mem' := fun {x} hx a i k => by
        rw [Pi.neg_apply, Pi.neg_apply, crd_neg]
        exact neg_mem (hx a i k) }
  have hLo : IsOpen (L : Set (Fin n → Fin M → Af F ⊗[F] E)) := by
    have e : (L : Set (Fin n → Fin M → Af F ⊗[F] E)) = ⋂ a, ⋂ i, ⋂ k,
        (fun X : Fin n → Fin M → Af F ⊗[F] E => crd b (Af F) (X a i) k) ⁻¹' (B : Set (Af F)) := by
      ext X
      simp [L]
    rw [e]
    exact isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun k =>
      hBo.preimage ((continuous_crd b (Af F) k).comp ((continuous_apply i).comp (continuous_apply a)))
  have hinv : ∀ x, ∀ l ∈ L, g (x + l) = g x := by
    intro x l hl
    have hl' : l = Lc fun a i k => crd b (Af F) (l a i) k := by
      funext a i
      exact eq_sum_crd b (Af F) (l a i)
    rw [hl']
    refine h1 _ (fun a => h2 _ fun i => h3 _ fun k => hsub (hl a i k)) x
  obtain ⟨s, hs⟩ := eq_sum_cosets hg.2 L hLo hinv
  have hbad : ∀ a : Fin n → Fin M → Af F ⊗[F] E, {v | ¬ projV v a ∈ latV b v}.Finite := fun a =>
    Filter.eventually_cofinite.1 (eventually_mem_latV b a)
  refine ⟨s, fun a v => cosVN b v (P v) (projV v a), T ∪ s.biUnion fun a => (hbad a).toFinset,
    fun a v => isCompact_isOpen_cosVN b v (P v) (hPO v) _, fun a ha v hv => ?_, fun Y => ?_⟩
  · have hvT : v ∉ T := fun h => hv (Finset.mem_union_left _ h)
    have hva : projV v a ∈ latV b v := by
      by_contra h
      exact hv (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨a, ha, (hbad a).mem_toFinset.2 h⟩))
    show cosVN b v (P v) (projV v a) = latV b v
    rw [hPT v hvT]
    exact cosVN_intSub b v hva
  · rw [hs Y]
    refine Finset.sum_congr rfl fun a _ => ?_
    congr 2
    ext X
    show X - a ∈ L ↔ ∀ v, projV v X - projV v a ∈ lvN b v ((P v : OpenAddSubgroup (Fv F v)) : AddSubgroup (Fv F v)) n M
    constructor
    · intro h v i j k
      rw [← projV_subN]
      have := crd_projV b (X - a) v i j k
      rw [this]
      exact h i j k v
    · intro h i j k v
      have := crd_projV b (X - a) v i j k
      rw [← this, projV_subN]
      exact h v i j k

end GlobalTheory.CompanionTheory.PfSWUS.FockSplit.Box

end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
open scoped TensorProduct ENNReal

theorem _root_.GlobalTheory.T.covolume_one_invariant_under_matrix : ∀ (F : Type) [Field F] [NumberField F] (ν : Measure (AF F)), GlobalTheory.CompanionTheory.Hypotheses₂.OneV.IsCovolOne ν → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F), A.det ≠ 0 → (Measure.pi fun _ : ι => ν).map (fun x => (A.map (algebraMap F (AF F))).mulVec x) = Measure.pi fun _ : ι => ν := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.piCovol_map_matrix | exact GlobalTheory.CompanionTheory.SiegelND.piCovol_map_matrix | (intros; apply GlobalTheory.CompanionTheory.SiegelND.piCovol_map_matrix <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.TestC

variable {F : Type} [Field F] [NumberField F]

def boxW (S : Finset (HeightOneSpectrum (𝓞 F))) (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v))
    (v : HeightOneSpectrum (𝓞 F)) : Set (Fv F v) :=
  {x | (v ∈ S → x ∈ U v) ∧ (v ∉ S → x ∈ v.adicCompletionIntegers F)}

theorem isOpen_integers (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) :=
  Valued.isOpen_integer _

theorem isCompact_integers (v : HeightOneSpectrum (𝓞 F)) :
    IsCompact (v.adicCompletionIntegers F : Set (Fv F v)) := by
  exact isCompact_iff_compactSpace.2 inferInstance

theorem isOpen_boxA (S : Finset (HeightOneSpectrum (𝓞 F)))
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (hU : ∀ v, IsOpen (U v)) :
    IsOpen (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.boxA S U) := by
  have h1 : IsOpen {y : Af F | ∀ v ∈ S, y v ∈ U v} := by
    have : {y : Af F | ∀ v ∈ S, y v ∈ U v} = ⋂ v ∈ S, (fun y : Af F => y v) ⁻¹' U v := by
      ext y; simp
    rw [this]
    exact isOpen_biInter_finset fun v _ => (hU v).preimage (RestrictedProduct.continuous_eval v)
  have h2 : IsOpen {y : Af F | ∀ v, v ∉ S → y v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_imp_mem (fun v => isOpen_integers v)
  exact h1.inter h2

theorem isCompact_boxW (S : Finset (HeightOneSpectrum (𝓞 F)))
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (hU : ∀ v, IsCompact (U v))
    (v : HeightOneSpectrum (𝓞 F)) : IsCompact (boxW S U v) := by
  by_cases hv : v ∈ S
  · have : boxW S U v = U v := by
      ext x; simp [boxW, hv]
    rw [this]; exact hU v
  · have : boxW S U v = (v.adicCompletionIntegers F : Set (Fv F v)) := by
      ext x; simp [boxW, hv]
    rw [this]; exact isCompact_integers v

theorem isCompact_boxA (S : Finset (HeightOneSpectrum (𝓞 F)))
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (hU : ∀ v, IsCompact (U v)) :
    IsCompact (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.boxA S U) := by
  haveI : ∀ v, CompactSpace (boxW S U v) := fun v => isCompact_iff_compactSpace.1 (isCompact_boxW S U hU v)
  have hle : (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 F))) ≤ Filter.principal ((S : Set _)ᶜ) :=
    Filter.le_principal_iff.2 S.finite_toSet.compl_mem_cofinite
  let gP : (∀ v, boxW S U v) → RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => Fv F v)
      (fun v => (v.adicCompletionIntegers F : Set (Fv F v))) (Filter.principal ((S : Set _)ᶜ)) :=
    fun x => ⟨fun v => (x v).1, Filter.eventually_principal.2 fun v hv => (x v).2.2 (by simpa using hv)⟩
  have hgP : Continuous gP :=
    RestrictedProduct.isEmbedding_coe_of_principal.continuous_iff.2
      (continuous_pi fun v => continuous_subtype_val.comp (continuous_apply v))
  let g : (∀ v, boxW S U v) → Af F := fun x => RestrictedProduct.inclusion _ _ hle (gP x)
  have hg : Continuous g := (RestrictedProduct.continuous_inclusion hle).comp hgP
  have hr : GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.boxA S U = Set.range g := by
    ext y
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun v => ⟨y v, fun hv => h1 v hv, fun hv => h2 v hv⟩, by ext v; rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨fun v hv => (x v).2.1 hv, fun v hv => (x v).2.2 hv⟩
  rw [hr]
  exact isCompact_range hg

theorem isClopen_boxA (S : Finset (HeightOneSpectrum (𝓞 F)))
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (hU : ∀ v, IsCompact (U v) ∧ IsOpen (U v)) :
    IsClopen (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.boxA S U) :=
  ⟨(isCompact_boxA S U fun v => (hU v).1).isClosed, isOpen_boxA S U fun v => (hU v).2⟩

theorem testT_continuous_hasCompactSupport : ∀ (F : Type) [Field F] [NumberField F] (ρ : Ainf F → ℝ)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)),
    Continuous ρ → HasCompactSupport ρ → (∀ v, IsCompact (U v) ∧ IsOpen (U v)) →
    Continuous (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.testT ρ S U) ∧
      HasCompactSupport (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.testT ρ S U) := by
  intro F _ _ ρ S U hρ hρc hU
  have hB := isClopen_boxA S U hU
  have hBc := isCompact_boxA S U fun v => (hU v).1
  have hfst : Continuous (fun y : AF F => fstA F y) := continuous_fst
  have hsnd : Continuous (fun y : AF F => sndA F y) := continuous_snd
  refine ⟨?_, ?_⟩
  · unfold GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.testT
    refine (Complex.continuous_ofReal.comp (hρ.comp hfst)).mul ?_
    exact (IsClopen.continuous_indicator hB continuous_const).comp hsnd
  · have hK : IsCompact ((tsupport ρ) ×ˢ (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.boxA S U) : Set (Ainf F × Af F)) :=
      hρc.isCompact.prod hBc
    refine HasCompactSupport.intro (K := ((tsupport ρ) ×ˢ (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.boxA S U) : Set (Ainf F × Af F))) hK ?_
    intro y hy
    unfold GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.testT
    by_cases h1 : sndA F y ∈ GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.boxA S U
    · have h2 : ρ (fstA F y) = 0 := by
        by_contra h3
        exact hy ⟨subset_tsupport ρ h3, h1⟩
      simp [h2]
    · simp [Set.indicator_of_notMem h1]

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.TestC
end
end
