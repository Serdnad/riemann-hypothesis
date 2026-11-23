module

import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle627
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle608
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle037
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle056
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanHermitianScalingByUnits
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Mathlib.Order.Sigma
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle257
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle134
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle052
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleSubquotientTwoBlockConstituents
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle254
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle025
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.EopV
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle133
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle612
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle623
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle089
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle453
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle622
import Formalism.LocalRingCardinality.DataHost
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle607
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle625
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.Bundle002
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle459
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle431
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle430
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle120
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle107

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.Euler

theorem pureN_eq_indicator {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n M : ℕ}
    (φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ)
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))
    (X : Fin n → Fin M → AF F ⊗[F] E) :
    pureN φ A X = {X : Fin n → Fin M → AF F ⊗[F] E |
      ∀ v, HeckeCharacterZeroLocus.SiegelWeilU.projV v (HeckeCharacterZeroLocus.SiegelWeilU.projFin X) ∈ A v}.indicator
        (fun X => φ (HeckeCharacterZeroLocus.SiegelWeilU.projInf X)) X := by
  change φ (HeckeCharacterZeroLocus.SiegelWeilU.projInf X) *
    (boxFN A).indicator (fun _ => (1 : ℂ)) (HeckeCharacterZeroLocus.SiegelWeilU.projFin X) = _
  by_cases hX : ∀ v, HeckeCharacterZeroLocus.SiegelWeilU.projV v (HeckeCharacterZeroLocus.SiegelWeilU.projFin X) ∈ A v
  · have h1 : HeckeCharacterZeroLocus.SiegelWeilU.projFin X ∈ boxFN A := hX
    rw [Set.indicator_of_mem (show X ∈ {X : Fin n → Fin M → AF F ⊗[F] E |
      ∀ v, HeckeCharacterZeroLocus.SiegelWeilU.projV v (HeckeCharacterZeroLocus.SiegelWeilU.projFin X) ∈ A v} from hX),
      Set.indicator_of_mem h1, mul_one]
  · have h1 : HeckeCharacterZeroLocus.SiegelWeilU.projFin X ∉ boxFN A := hX
    rw [Set.indicator_of_notMem (show X ∉ {X : Fin n → Fin M → AF F ⊗[F] E |
      ∀ v, HeckeCharacterZeroLocus.SiegelWeilU.projV v (HeckeCharacterZeroLocus.SiegelWeilU.projFin X) ∈ A v} from hX),
      Set.indicator_of_notMem h1, mul_zero]

theorem integrable_integral_pureN : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (M n d : ℕ) (b : Module.Basis (Fin d) F E) (I : Measure (Fin n → Fin M → AF F ⊗[F] E)) (c : NNReal) (minf : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (m : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)), GlobalTheory.CompanionTheory.SW.IsEulerProd b I c minf m → ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₀ ⊆ S → ∀ φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ, Measurable φ → Integrable φ minf → ∀ A : (∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E)), (∀ v, MeasurableSet (A v)) → (∀ v, m v (A v) ≠ ⊤) → (∀ v, v ∉ S → A v = latV b v) → Integrable (pureN φ A) I ∧ ∫ X, pureN φ A X ∂I = (c : ℂ) * (∫ X, φ X ∂minf) * (∏ v ∈ S, ((m v (A v)).toReal : ℂ)) * ((∏' v : {v // v ∉ S}, (m v.1 (latV b v.1)).toReal : ℝ) : ℂ) := by
  apply _root_.GlobalTheory.CompanionTheory.WhitFree.Euler.integrable_integral_pureN <;> assumption

end GlobalTheory.CompanionTheory.SiegelND.Coef.Euler
end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.archimedean_hermitian_scaling_by_units : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure (Ainf F)), lam.IsAddHaarMeasure → ∀ e : Ainf F ≃+* (NumberField.InfinitePlace F → ℝ), IsHomeomorph e → ∀ t : Fin n → Ainf F, (∀ a, IsUnit (t a)) → ∀ τ : HeckeCharacterZeroLocus.SiegelWeilU.HermR (Ainf F) σ n → HeckeCharacterZeroLocus.SiegelWeilU.HermR (Ainf F) σ n, Measurable τ → (∀ S i j, (τ S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) i j = algebraMap (Ainf F) (Ainf F ⊗[F] E) (t i) * (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) i j * algebraMap (Ainf F) (Ainf F ⊗[F] E) (t j)) → (GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b lam n).map τ = (∏ a, ((∏ w, ‖e (t a) w‖₊)⁻¹) ^ (2 * n)) • GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b lam n := by
  first | exact @GlobalTheory.CompanionTheory.SW.DiagScale.coordHerm_map_diag_ainf | exact GlobalTheory.CompanionTheory.SW.DiagScale.coordHerm_map_diag_ainf | (intros; apply GlobalTheory.CompanionTheory.SW.DiagScale.coordHerm_map_diag_ainf <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.archimedean_measure_scaling_by_units : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n M d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure (Ainf F)), lam.IsAddHaarMeasure → ∀ e : Ainf F ≃+* (NumberField.InfinitePlace F → ℝ), IsHomeomorph e → ∀ t : Fin n → Ainf F, (∀ a, IsUnit (t a)) → (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam n M).map (fun X a i => algebraMap (Ainf F) (Ainf F ⊗[F] E) (t a) * X a i) = (∏ a, ((∏ w, ‖e (t a) w‖₊)⁻¹) ^ (d * M)) • GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam n M := by
  first | exact @GlobalTheory.CompanionTheory.SW.Dil.coordW_map_units | exact GlobalTheory.CompanionTheory.SW.Dil.coordW_map_units | (intros; apply GlobalTheory.CompanionTheory.SW.Dil.coordW_map_units <;> assumption)
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil

namespace GlobalTheory.CompanionTheory.BZSwap

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem prodIrr_congr {r r' N : ℕ} (hr : r = r') (v : Fin r → IrrGL (k := k)) (w : Fin r' → IrrGL (k := k))
    (hvw : ∀ i, v i = w (Fin.cast hr i)) (hv : ∑ a, (v a).1 = N) (hw : ∑ a, (w a).1 = N) :
    Nonempty ((prodIrr v hv).Equiv (prodIrr w hw)) := by
  subst hr
  have e : v = w := funext fun i => (hvw i).trans (congrArg w (Fin.ext rfl))
  subst e
  exact ⟨Representation.Equiv.refl _⟩

theorem flatten {s h N : ℕ} (t : Fin s → ℕ) (u : ∀ a, Fin (t a) → IrrGL (k := k)) (d : Fin s → ℕ)
    (hd : ∀ a, ∑ b, (u a b).1 = d a) (hN : ∑ a, d a = N) (F : Fin h ≃o Σₗ a, Fin (t a))
    (x : Fin h → IrrGL (k := k)) (hx : ∀ c, u (ofLex (F c)).1 (ofLex (F c)).2 = x c) (hxN : ∑ a, (x a).1 = N) :
    Nonempty ((multiProd (stdBlocks d hN) fun a => prodIrr (u a) (hd a)).Equiv (prodIrr x hxN)) := by
  have e : (fun c => u (ofLex (F c)).1 (ofLex (F c)).2) = x := funext hx
  subst e
  have hS := GlobalTheory.SmGL.Stages.stages_equiv (k := k) s d t (fun a b => (u a b).1)
    (fun a => stdBlocks (fun b => (u a b).1) (hd a)) (fun a b => (u a b).2.rep.V) (fun a b => (u a b).rep)
    (Fin N) (stdBlocks d hN)
  refine Exists.elim hS fun E0 hχ => ?_
  let E : (Σ c : Fin h, Fin (u (ofLex (F c)).1 (ofLex (F c)).2).1) ≃ Fin N :=
    (Equiv.sigmaCongrLeft (β := fun c : Σₗ a, Fin (t a) => Fin (u (ofLex c).1 (ofLex c).2).1) F.toEquiv).trans E0
  have hω := GlobalTheory.T.parabolicInductionProduct_block_renaming_equiv (k := k) F F.strictMono F.surjective E0 E
    (fun _ _ => rfl) fun c => (u (ofLex c).1 (ofLex c).2).rep
  refine hχ.elim fun χ => hω.elim fun ω => ?_
  refine (GlobalTheory.ProdReorder.multiProd_placing (k := k) E (stdBlocks (fun c => (u (ofLex (F c)).1 (ofLex (F c)).2).1) hxN)
    fun c => (u (ofLex (F c)).1 (ofLex (F c)).2).rep).elim fun p => ?_
  exact ⟨(χ.trans ω).trans p⟩

def grp (h j : ℕ) : Fin 3 → ℕ := ![j, 2, h - (j + 2)]

def off (j : ℕ) : Fin 3 → ℕ := ![0, j, j + 2]

theorem off_add_grp_le {h j : ℕ} (hj : j + 1 < h) (a : Fin 3) : off j a + grp h j a ≤ h := by
  fin_cases a <;> simp [off, grp] <;> omega

theorem off_add_grp_le_off {h j : ℕ} (hj : j + 1 < h) {a a' : Fin 3} (haa : a < a') :
    off j a + grp h j a ≤ off j a' := by
  fin_cases a <;> fin_cases a' <;> simp [off, grp] at haa ⊢

def place {h j : ℕ} (hj : j + 1 < h) (c : Σₗ a, Fin (grp h j a)) : Fin h :=
  ⟨off j (ofLex c).1 + (ofLex c).2, by
    have := off_add_grp_le hj (ofLex c).1
    have := (ofLex c).2.2
    omega⟩

theorem place_strictMono {h j : ℕ} (hj : j + 1 < h) : StrictMono (place hj) := by
  intro c c' hc
  obtain ⟨a, b⟩ := c
  obtain ⟨a', b'⟩ := c'
  rcases Sigma.Lex.lt_def.1 hc with hlt | ⟨e, hlt⟩
  · have h1 : off j a + grp h j a ≤ off j a' := off_add_grp_le_off hj hlt
    have h2 : (b : ℕ) < grp h j a := b.2
    show off j a + b < off j a' + b'
    omega
  · obtain rfl : a = a' := e
    have : (b : ℕ) < b' := hlt
    show off j a + b < off j a + b'
    omega

theorem card_lex {h j : ℕ} (hj : j + 1 < h) : Fintype.card (Σₗ a, Fin (grp h j a)) = h := by
  rw [Fintype.card_lex, Fintype.card_sigma]
  simp only [Fintype.card_fin, Fin.sum_univ_three]
  show j + 2 + (h - (j + 2)) = h
  omega

theorem place_bijective {h j : ℕ} (hj : j + 1 < h) : Function.Bijective (place hj) :=
  (Fintype.bijective_iff_injective_and_card _).2 ⟨(place_strictMono hj).injective, by simp [card_lex hj]⟩

def order {h j : ℕ} (hj : j + 1 < h) : Fin h ≃o Σₗ a, Fin (grp h j a) :=
  ((place_strictMono hj).orderIsoOfSurjective _ (place_bijective hj).2).symm

theorem place_order {h j : ℕ} (hj : j + 1 < h) (c : Fin h) : place hj (order hj c) = c :=
  ((place_strictMono hj).orderIsoOfSurjective _ (place_bijective hj).2).apply_symm_apply c

theorem sum_place {h j : ℕ} (hj : j + 1 < h) (g : Fin h → ℕ) :
    ∑ a, ∑ b : Fin (grp h j a), g (place hj (toLex ⟨a, b⟩)) = ∑ c, g c := by
  rw [← Fintype.sum_sigma (fun p : Σ a, Fin (grp h j a) => g (place hj (toLex p)))]
  exact Equiv.sum_comp (toLex.trans (Equiv.ofBijective _ (place_bijective hj))) g

theorem fin_three_forall {P : Fin 3 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) (a : Fin 3) : P a := by
  fin_cases a
  exacts [h0, h1, h2]

section Main

variable {h N j M : ℕ} (hj : j + 1 < h) (x : Fin h → IrrGL (k := k))

def fac (a : Fin 3) (b : Fin (grp h j a)) : IrrGL (k := k) := x (place hj (toLex ⟨a, b⟩))

def fac' (a : Fin 3) (b : Fin (grp h j a)) : IrrGL (k := k) :=
  x (Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩ (place hj (toLex ⟨a, b⟩)))

theorem fac'_zero : fac' hj x 0 = fac hj x 0 := by
  funext b
  have hb : (b : ℕ) < j := b.2
  refine congrArg x (Equiv.swap_apply_of_ne_of_ne (Fin.ne_of_val_ne ?_) (Fin.ne_of_val_ne ?_))
  · show off j 0 + b ≠ j
    simp [off]; omega
  · show off j 0 + b ≠ j + 1
    simp [off]; omega

theorem fac'_two : fac' hj x 2 = fac hj x 2 := by
  funext b
  refine congrArg x (Equiv.swap_apply_of_ne_of_ne (Fin.ne_of_val_ne ?_) (Fin.ne_of_val_ne ?_))
  · show off j 2 + b ≠ j
    simp [off]; omega
  · show off j 2 + b ≠ j + 1
    simp [off]; omega

theorem place_one_zero : place hj (toLex ⟨1, (0 : Fin 2)⟩) = ⟨j, by omega⟩ := Fin.ext (by
  show off j 1 + 0 = j
  simp [off])

theorem place_one_one : place hj (toLex ⟨1, (1 : Fin 2)⟩) = ⟨j + 1, hj⟩ := Fin.ext (by
  show off j 1 + 1 = j + 1
  simp [off])

theorem fac_one : (fac hj x 1 : Fin 2 → IrrGL (k := k)) = ![x ⟨j, by omega⟩, x ⟨j + 1, hj⟩] := by
  funext b
  fin_cases b
  · exact congrArg x (place_one_zero hj)
  · exact congrArg x (place_one_one hj)

theorem fac'_one : (fac' hj x 1 : Fin 2 → IrrGL (k := k)) = ![x ⟨j + 1, hj⟩, x ⟨j, by omega⟩] := by
  funext b
  fin_cases b
  · refine congrArg x ?_
    refine (congrArg _ (place_one_zero hj)).trans (Equiv.swap_apply_left _ _)
  · refine congrArg x ?_
    refine (congrArg _ (place_one_one hj)).trans (Equiv.swap_apply_right _ _)

end Main

end GlobalTheory.CompanionTheory.BZSwap
end
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.SmGL.Exponents

namespace GlobalTheory.CompanionTheory.ProdSubquot
open TensorProduct

section General
variable {G H V V' W W' : Type} [Group G] [Group H]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
  [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

theorem isSubquotient_extTensor_left {σ : Representation ℂ G V} {σ' : Representation ℂ G V'}
    (B : Representation ℂ H W) (h : IsSubquotient σ σ') :
    IsSubquotient (extTensor σ B) (extTensor σ' B) := by
  obtain ⟨S, f, hf⟩ := h
  let ι : S.toRepresentation.IntertwiningMap σ' :=
    { toLinearMap := S.toSubmodule.subtype, isIntertwining' := fun _ => rfl }
  have hι : Function.Injective ι := Subtype.val_injective
  obtain ⟨ι', hι'⟩ := GlobalTheory.ParIndExact.extTensor_injective_left B ι hι
  have hs : Function.Surjective (GlobalTheory.ParIndExact.extTensorMapLeft B f) :=
    LinearMap.rTensor_surjective W hf
  exact (IsSubquotient.of_surjective _ hs).trans (IsSubquotient.of_injective ι' hι')

theorem isSubquotient_extTensor_right {ρ : Representation ℂ H W} {ρ' : Representation ℂ H W'}
    (A : Representation ℂ G V) (h : IsSubquotient ρ ρ') :
    IsSubquotient (extTensor A ρ) (extTensor A ρ') := by
  obtain ⟨S, f, hf⟩ := h
  let ι : S.toRepresentation.IntertwiningMap ρ' :=
    { toLinearMap := S.toSubmodule.subtype, isIntertwining' := fun _ => rfl }
  have hι : Function.Injective ι := Subtype.val_injective
  obtain ⟨ι', hι'⟩ := GlobalTheory.ParIndExact.extTensor_injective_right A ι hι
  have hs : Function.Surjective (GlobalTheory.ParIndExact.extTensorMapRight A f) :=
    LinearMap.lTensor_surjective V hf
  exact (IsSubquotient.of_surjective _ hs).trans (IsSubquotient.of_injective ι' hι')

theorem isSubquotient_comp {L : Type} [Group L] {σ : Representation ℂ G V}
    {σ' : Representation ℂ G V'} (s : L →* G) (h : IsSubquotient σ σ') :
    IsSubquotient (σ.comp s) (σ'.comp s) := by
  obtain ⟨S, f, hf⟩ := h
  let T : Subrepresentation (σ'.comp s) :=
    ⟨S.toSubmodule, fun x _ hv => S.apply_mem_toSubmodule (s x) hv⟩
  exact ⟨T, ⟨f.toLinearMap, fun x => f.isIntertwining' (s x)⟩, hf⟩

end General

theorem prod₂_isSubquotient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (U U' W W' : Type) [AddCommGroup U] [Module ℂ U] [AddCommGroup U'] [Module ℂ U'] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (σ : Representation ℂ (GL (Fin r) k) U) (σ' : Representation ℂ (GL (Fin r) k) U') (ρ : Representation ℂ (GL (Fin t) k) W) (ρ' : Representation ℂ (GL (Fin t) k) W'), IsSmooth σ' → IsSmooth ρ' → IsSubquotient σ σ' → IsSubquotient ρ ρ' → IsSubquotient (prod₂ σ ρ) (prod₂ σ' ρ') := by
  intro k _ _ _ _ r t U U' W W' _ _ _ _ _ _ _ _ σ σ' ρ ρ' hσ' hρ' hs hr
  have hext : IsSubquotient (extTensor σ ρ) (extTensor σ' ρ') :=
    (isSubquotient_extTensor_left ρ hs).trans (isSubquotient_extTensor_right σ' hr)
  have hsm : IsSmooth ((extTensor σ' ρ').comp (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom) :=
    isSmooth_comp (isSmooth_extTensor hσ' hρ') _
      (show Continuous fun g : Levi k (Two (Fin r) (Fin t)) => (g false, g true) from
        (continuous_apply false).prodMk (continuous_apply true))
  exact GlobalTheory.ParIndSubquot.parInd_isSubquotient k _ _ _ _ _ _ _ _ hsm
    (isSubquotient_comp _ hext)

end GlobalTheory.CompanionTheory.ProdSubquot
end

section

noncomputable section

open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC

namespace GlobalTheory.CompanionTheory.CuspGL

theorem cuspDiscreteDecompositionGL_of_compact
    (hc : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure]
      [μ.IsMulRightInvariant] (f : GA E a → ℂ), Continuous f → HasCompactSupport f →
      IsCompactOperator (repOp (Rcusp μ) μ f)) :
    GlobalTheory.Published.CuspDiscreteDecompositionGL := by
  intro E _ _ _ a μ _ _
  have : BorelSpace (GA E a) := GlobalTheory.CuspRep.CuspidalL2GL.borelSpace_GA E a
  have : LocallyCompactSpace (GA E a) := GlobalTheory.CuspRep.CuspidalL2GL.locallyCompactSpace_GA E a
  have : T2Space (GA E a) := GlobalTheory.CuspRep.CuspidalL2GL.t2Space_GA E a
  have : CompleteSpace (L2cusp μ) := GlobalTheory.CuspRep.CuspidalL2GL.completeSpace_L2cusp μ
  have hU := GlobalTheory.CuspRep.CuspidalL2GL.isUnitaryRep_Rcusp μ
  refine GlobalTheory.CuspSpectrum.isDiscreteSum_of_repOp hU μ fun v hv => ?_
  have hpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have cc : Continuous fun g => inner ℂ v ((Rcusp μ g) v) := continuous_const.inner (hU.continuous_apply v)
  have h1pos : 0 < (inner ℂ v ((Rcusp μ 1) v)).re := by
    rw [map_one, ContinuousLinearMap.one_apply]
    have h3 : RCLike.re (inner ℂ v v) = ‖v‖ ^ 2 := inner_self_eq_norm_sq v
    have h4 : (inner ℂ v v).re = ‖v‖ ^ 2 := h3
    rw [h4]
    exact pow_pos hpos 2
  have hN : {g | 0 < (inner ℂ v ((Rcusp μ g) v)).re} ∈ 𝓝 (1 : GA E a) :=
    (isOpen_lt continuous_const (Complex.continuous_re.comp cc)).mem_nhds h1pos
  obtain ⟨φ, hφc, hφs, hφ0, hφ1, hφN⟩ := GlobalTheory.CompanionTheory.Bump.exists_nonneg_bump (1 : GA E a) _ hN
  have hfc : Continuous fun g => (φ g : ℂ) := Complex.continuous_ofReal.comp hφc
  have hfs : HasCompactSupport fun g => (φ g : ℂ) := hφs.comp_left Complex.ofReal_zero
  refine ⟨fun g => (φ g : ℂ), hfc, hfs, hc E a μ _ hfc hfs, fun h0 => ?_⟩
  have key := hU.inner_repOp (μ := μ) hfc hfs v v
  rw [h0, inner_zero_right] at key
  have hint : Integrable (fun g => (φ g : ℂ) * inner ℂ v ((Rcusp μ g) v)) μ :=
    (hfc.mul cc).integrable_of_hasCompactSupport hfs.mul_right
  have h8 := Complex.reCLM.integral_comp_comm hint
  simp only [Complex.reCLM_apply, Complex.re_ofReal_mul] at h8
  rw [← key, Complex.zero_re] at h8
  have h9 : 0 < ∫ g, φ g * (inner ℂ v ((Rcusp μ g) v)).re ∂μ := by
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1)
      (hφc.mul (Complex.continuous_re.comp cc)) hφs.mul_right (fun g => ?_) (mul_ne_zero hφ1 h1pos.ne')
    by_cases hg : φ g = 0
    · simp [hg]
    · exact mul_nonneg (hφ0 g) (hφN hg).le
  linarith

end GlobalTheory.CompanionTheory.CuspGL

end
end

section

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel

namespace GlobalTheory.CompanionTheory.ClozelHerm

def petersson {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (μ : Measure (GA E a))
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (π : CuspSub E a)
    (hm : ∀ φ ∈ π.V, GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ φ.1) :
    π.V →ₗ[ℂ] π.V →ₗ⋆[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun φ ψ => inner ℂ (toL2ₗ μ π.V hm ψ) (toL2ₗ μ π.V hm φ))
    (fun φ φ' ψ => by simp only [map_add (f := _), inner_add_right])
    (fun c φ ψ => by simp only [map_smul, inner_smul_right, smul_eq_mul, RingHom.id_apply])
    (fun φ ψ ψ' => by simp only [map_add (f := _), inner_add_left])
    (fun c φ ψ => by simp only [map_smul, inner_smul_left, smul_eq_mul])

theorem exists_isHerm : GlobalTheory.Published.CuspFormsBoundedGL → ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (π : CuspSub E a), GlobalTheory.DiscSpec.IsNormalised π → ∃ B : π.V →ₗ[ℂ] π.V →ₗ⋆[ℂ] ℂ, IsHerm π B := by
  intro hB E _ _ _ a μ _ _ π hπ
  have hl := GlobalTheory.T.normalised_cusp_form_L2_bounded hB E a μ π hπ
  have hm : ∀ φ ∈ π.V, GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ φ.1 := fun φ hφ => (hl φ hφ).1
  have hb : ∀ φ ∈ π.V, ∃ C : ℝ, ∀ g, ‖φ.1 g‖ ≤ C := fun φ hφ => (hl φ hφ).2
  refine ⟨petersson μ π hm, fun X φ ψ => GlobalTheory.T.lie_action_skew_adjoint_L2 E a μ π hm hb X φ ψ, ?_⟩
  obtain ⟨φ, hφ, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot π.ne_bot
  have hi : Function.Injective (toL2ₗ μ π.V hm) :=
    toL2ₗ_injective hm fun ψ hψ => ContAut.continuous_of_isOpen_stab E a ψ (π.cusp ψ hψ).1.level
  have hT : toL2ₗ μ π.V hm ⟨φ, hφ⟩ ≠ 0 := fun h =>
    hne (congrArg Subtype.val (hi (h.trans (map_zero _).symm)))
  refine ⟨⟨φ, hφ⟩, ?_⟩
  show inner ℂ (toL2ₗ μ π.V hm ⟨φ, hφ⟩) (toL2ₗ μ π.V hm ⟨φ, hφ⟩) ≠ 0
  exact inner_self_ne_zero.2 hT

end GlobalTheory.CompanionTheory.ClozelHerm

end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStage

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypWitt

theorem e0_linearIndependent (K : Type) [CommRing K] (M : ℕ) : LinearIndependent K (e0 K M) := by
  refine Fintype.linearIndependent_iff.mpr fun g hg i => ?_
  rw [Subsingleton.elim i 0]
  have h := congrFun hg 0
  simpa [e0] using h

theorem gramR_e0 {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    gramR R σ (hypOne J) (e0 (R ⊗[F] E) M) = 0 := by
  ext a b
  simp [gramR, hR, hform, JR, e0, Fin.sum_univ_succ, hypOne_zero_zero]

theorem witt_e0 : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ x : Fin 1 → Fin (M + 2) → R ⊗[F] E, LinearIndependent (R ⊗[F] E) x → gramR R σ (hypOne J) x = 0 → ∃ g : HA R σ (hypOne J), actW R σ (hypOne J) g (e0 _ M) = x := by
  intro F E _ _ _ _ _ σ hσ M J hJ R _ _ _ _ _ hL x hx gx
  exact FreeTrans.transitive_free_isotropic F E σ hσ (M + 2) (hypOne J) (isHermND_hypOne σ hJ) R hL
    (e0 _ M) x (e0_linearIndependent _ M) hx (gramR_e0 R σ J) gx

end GlobalTheory.CompanionTheory.WeilSiegel.HypWitt
end
end

section

open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.CompanionTheory.QKAvg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_right_invariant_haar_levi : ∀ (D : D7) (B W : HSp D) (t : ℕ) (d : HypDec B W t) [LocallyCompactSpace (levM d)], ∃ νM : Measure (levM d), νM.IsHaarMeasure ∧ νM.IsMulRightInvariant := by
  first | exact @GlobalTheory.CompanionTheory.QKAvg.exists_levM_haar | exact GlobalTheory.CompanionTheory.QKAvg.exists_levM_haar | (intros; apply GlobalTheory.CompanionTheory.QKAvg.exists_levM_haar <;> assumption)
end
