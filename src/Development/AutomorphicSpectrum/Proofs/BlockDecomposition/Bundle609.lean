module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle431
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.Bundle002
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle596
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Formalism.SatakeDualWeyl.Bundle001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle601
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.CuspInvariantsFinite.CuspInvFin
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle311
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle133
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle229
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFiniteMeasureQuotMeasure
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle537
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalL2NormOneIsometry
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle476
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KFiniteVectorsDense
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermConvolutionHecke
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.LeftInv
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle005
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.IsTransl
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.IsSliceMap
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.SchGlue

open GlobalTheory.Published.SiegelOneVector

variable {D : D7}

theorem exists_homeomorph_of_sections {A Y Z : Type} [TopologicalSpace A] [TopologicalSpace Y] [TopologicalSpace Z]
    (p : A → Y) (s : Y → A) (c : Y → Z) (σ : Z → A) (hp : Continuous p) (hs : Continuous s)
    (hc : Continuous fun a => c (p a)) (hσ : Continuous σ) (h1 : ∀ y, p (s y) = y)
    (h2 : ∀ z, c (p (σ z)) = z) (h3 : ∀ y, p (σ (c y)) = y) :
    ∃ P : Y ≃ₜ Z, ∀ y, P y = c y := by
  have hcc : Continuous c := by
    have : c = (fun a => c (p a)) ∘ s := funext fun y => by simp only [Function.comp, h1]
    rw [this]
    exact hc.comp hs
  exact ⟨{ toFun := c, invFun := fun z => p (σ z), left_inv := h3, right_inv := h2,
           continuous_toFun := hcc, continuous_invFun := hp.comp hσ }, fun _ => rfl⟩



theorem exists_infHomeo {θ : InfFam D} (hθ : IsInfFam θ) :
    ∃ P : (Ainf D.host.F ⊗[D.host.F] D.host.E) ≃ₜ (D.what₂.Tau → ℂ), ∀ y τ, P y τ = θ τ y := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨e, he, hec, hec'⟩ : ∃ e : AE D ≃+* (Ainf D.host.F ⊗[D.host.F] D.host.E) × (Af D.host.F ⊗[D.host.F] D.host.E),
      (∀ z, (e z).1 = infPart D z ∧ (e z).2 = finPart D z) ∧ Continuous e ∧ Continuous e.symm :=
    GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have hinf : ∀ y, infPart D (e.symm (y, 0)) = y := fun y => by
    have := (he (e.symm (y, 0))).1
    rw [RingEquiv.apply_symm_apply] at this
    exact this.symm
  have hfin : ∀ y, finPart D (e.symm (y, 0)) = 0 := fun y => by
    have := (he (e.symm (y, 0))).2
    rw [RingEquiv.apply_symm_apply] at this
    exact this.symm
  have hci : Continuous (infPart D) := by
    have : (infPart D : AE D → _) = fun z => (e z).1 := funext fun z => ((he z).1).symm
    rw [this]
    exact continuous_fst.comp hec
  have hs : Continuous fun y : Ainf D.host.F ⊗[D.host.F] D.host.E => e.symm (y, 0) :=
    hec'.comp (continuous_id.prodMk continuous_const)
  have hback : ∀ a : AE D, finPart D a = 0 → a = σ fun τ => θ τ (infPart D a) := fun a ha => by
    refine sub_eq_zero.1 (hσ.ext _ ?_ fun τ => ?_)
    · rw [(finPart D).map_sub, ha, hσ.fin, sub_zero]
    · rw [(infPart D).map_sub, (θ τ).map_sub, hσ.comp, sub_self]
  obtain ⟨P, hP⟩ := exists_homeomorph_of_sections (infPart D : AE D → _) (fun y => e.symm (y, 0))
    (fun (y : Ainf D.host.F ⊗[D.host.F] D.host.E) (τ : D.what₂.Tau) => θ τ y) σ hci hs
    (continuous_pi fun τ => GlobalTheory.FockCompare.continuous_comp hθ τ) hσ.cont hinf
    (fun z => funext fun τ => hσ.comp z τ)
    (fun y => by
      obtain ⟨a, ha⟩ : ∃ a : AE D, a = e.symm (y, 0) := ⟨_, rfl⟩
      have h1 : infPart D a = y := ha ▸ hinf y
      have h2 : finPart D a = 0 := ha ▸ hfin y
      subst h1
      exact congrArg (infPart D) (hback a h2).symm)
  exact ⟨P, fun y τ => congrFun (hP y) τ⟩

theorem isSchwartzArch_comp {θ : InfFam D} (hθ : IsInfFam θ) {m r : ℕ}
    (f : SchwartzMap (D.what₂.Tau → Fin m → Fin r → ℂ) ℂ) :
    IsSchwartzArch (F := D.host.F) (E := D.host.E) (M := m) (n := r)
      fun Y => f fun τ i j => θ τ (Y j i) := by
  obtain ⟨P, hP⟩ := exists_infHomeo hθ
  let Q : (Fin r → Fin m → Ainf D.host.F ⊗[D.host.F] D.host.E) ≃ₜ (D.what₂.Tau → Fin m → Fin r → ℂ) :=
    { toFun := fun Y τ i j => P (Y j i) τ
      invFun := fun c j i => P.symm fun τ => c τ i j
      left_inv := fun Y => by simp
      right_inv := fun c => by simp
      continuous_toFun := continuous_pi fun τ => continuous_pi fun i => continuous_pi fun j =>
        (continuous_apply τ).comp (P.continuous.comp ((continuous_apply i).comp (continuous_apply j)))
      continuous_invFun := continuous_pi fun j => continuous_pi fun i => P.symm.continuous.comp
        (continuous_pi fun τ => (continuous_apply j).comp ((continuous_apply i).comp (continuous_apply τ))) }
  have hQ : ∀ Y τ i j, Q Y τ i j = θ τ (Y j i) := fun Y τ i j => hP _ _
  have hadd : ∀ X Y, Q (X + Y) = Q X + Q Y := fun X Y => by
    funext τ i j
    simp only [hQ, Pi.add_apply, map_add (f := _)]
  let B : (D.what₂.Tau → Fin m → Fin r → ℂ) ≃L[ℝ]
      (Fin (Module.finrank ℝ (D.what₂.Tau → Fin m → Fin r → ℂ)) → ℝ) :=
    (Module.finBasis ℝ (D.what₂.Tau → Fin m → Fin r → ℂ)).equivFun.toContinuousLinearEquiv
  refine ⟨_, (AddEquiv.mk' Q.toEquiv hadd).trans B.toLinearEquiv.toAddEquiv,
    B.continuous.comp Q.continuous, Q.symm.continuous.comp B.symm.continuous,
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ B.symm f, fun Y => ?_⟩
  show _ = f (B.symm (B (Q Y)))
  rw [ContinuousLinearEquiv.symm_apply_apply]
  exact congrArg f (funext fun τ => funext fun i => funext fun j => (hQ Y τ i j).symm)

theorem isSB_swap {m r : ℕ} {g : (Fin m → Fin r → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ}
    (hg : g ∈ GlobalTheory.WeilM.SB (Fin m → Fin r → Af D.host.F ⊗[D.host.F] D.host.E)) :
    IsSB fun Y : Fin r → Fin m → Af D.host.F ⊗[D.host.F] D.host.E => g fun i j => Y j i := by
  let S : (Fin r → Fin m → Af D.host.F ⊗[D.host.F] D.host.E) ≃ₜ
      (Fin m → Fin r → Af D.host.F ⊗[D.host.F] D.host.E) :=
    { toFun := fun Y i j => Y j i
      invFun := fun Y j i => Y i j
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := continuous_pi fun i => continuous_pi fun j =>
        (continuous_apply i).comp (continuous_apply j)
      continuous_invFun := continuous_pi fun j => continuous_pi fun i =>
        (continuous_apply j).comp (continuous_apply i) }
  exact ⟨hg.1.comp_continuous S.continuous, hg.2.comp_homeomorph S⟩

theorem isSchwartzArch_smul {M n : ℕ} (c : ℂ) {Φ : (Fin n → Fin M → Ainf D.host.F ⊗[D.host.F] D.host.E) → ℂ}
    (h : IsSchwartzArch (F := D.host.F) (E := D.host.E) Φ) :
    IsSchwartzArch (F := D.host.F) (E := D.host.E) fun X => c * Φ X := by
  obtain ⟨N, e, h1, h2, f, hf⟩ := h
  exact ⟨N, e, h1, h2, c • f, fun X => by simp [hf]⟩

theorem sb_zero {M n : ℕ} :
    IsSchwartzBruhat (F := D.host.F) (E := D.host.E) (0 : (Fin n → Fin M → AE D) → ℂ) :=
  ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun _ => by simp⟩

theorem sb_add {M n : ℕ} {Φ Ψ : (Fin n → Fin M → AE D) → ℂ}
    (hΦ : IsSchwartzBruhat (F := D.host.F) (E := D.host.E) Φ)
    (hΨ : IsSchwartzBruhat (F := D.host.F) (E := D.host.E) Ψ) :
    IsSchwartzBruhat (F := D.host.F) (E := D.host.E) (Φ + Ψ) := by
  obtain ⟨k, a, b, ha, hb, hs⟩ := hΦ
  obtain ⟨k', a', b', ha', hb', hs'⟩ := hΨ
  refine ⟨k + k', Fin.append a a', Fin.append b b', fun i => ?_, fun i => ?_, fun X => ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [Fin.append_left]; exact ha i
    · rw [Fin.append_right]; exact ha' i
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [Fin.append_left]; exact hb i
    · rw [Fin.append_right]; exact hb' i
  · rw [Fin.sum_univ_add, Pi.add_apply, hs, hs']
    simp only [Fin.append_left, Fin.append_right]

theorem sb_smul {M n : ℕ} (c : ℂ) {Φ : (Fin n → Fin M → AE D) → ℂ}
    (hΦ : IsSchwartzBruhat (F := D.host.F) (E := D.host.E) Φ) :
    IsSchwartzBruhat (F := D.host.F) (E := D.host.E) (c • Φ) := by
  obtain ⟨k, a, b, ha, hb, hs⟩ := hΦ
  refine ⟨k, fun i X => c * a i X, b, fun i => isSchwartzArch_smul c (ha i), hb, fun X => ?_⟩
  rw [Pi.smul_apply, hs, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

end GlobalTheory.CompanionTheory.SiegelND.SchGlue

namespace GlobalTheory.CompanionTheory.SiegelND

open GlobalTheory.CompanionTheory.SiegelND.SchGlue

theorem isSchwartzBruhat_tupOf_of_mem_schwartzA : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m r : ℕ) (φ : Mx D m r → ℂ), φ ∈ schwartzA θ m r →
  GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat (F := D.host.F) (E := D.host.E) (fun X : Fin r → Fin m → AE D => φ (tupOf X)) := by
  intro D θ hθ m r φ hφ
  induction hφ using Submodule.span_induction with
  | mem φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    refine ⟨1, fun _ Y => f fun τ i j => θ τ (Y j i), fun _ Y => g fun i j => Y j i,
      fun _ => isSchwartzArch_comp hθ f, fun _ => isSB_swap hg, fun X => ?_⟩
    simp only [Finset.univ_unique, Finset.sum_singleton]
    rfl
  | zero => exact sb_zero
  | add a b _ _ ha hb => exact sb_add ha hb
  | smul c a _ ha => exact sb_smul c ha

end GlobalTheory.CompanionTheory.SiegelND
end
end

section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem _root_.GlobalTheory.T.satake_eigenvalue_pair_decomposition : ∀ (q n a b : ℕ) (c : ℂˣ) (Ba Bb : Multiset ℂˣ), q ≠ 0 → a + b = n → Ba.card = a → Bb.card = b → ∀ k ≤ n, satEig q n (Ba.map (· * c ^ b) + Bb.map (· * c ^ a)) k = ∑ p ∈ pairs a b k, coef q c a b p.1 p.2 * (satEig q a Ba p.1 * satEig q b Bb p.2) := by
  first | exact @GlobalTheory.CompanionTheory.CtS.SatConv.satEig_join | exact GlobalTheory.CompanionTheory.CtS.SatConv.satEig_join | (intros; apply GlobalTheory.CompanionTheory.CtS.SatConv.satEig_join <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem _root_.GlobalTheory.T.det_order_bounded_hecke_support : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (ϖ : w.adicCompletion E), IsUnifV E w ϖ → ∀ g : GL (Fin n) (w.adicCompletion E), IsInt w g.val → IsInt w (ϖ • (g⁻¹).val) → ∃ i ≤ n, ordL g.val.det = (i : ℤ) := by
  first | exact @GlobalTheory.CompanionTheory.CtS.ordL_det_range | exact GlobalTheory.CompanionTheory.CtS.ordL_det_range | (intros; apply GlobalTheory.CompanionTheory.CtS.ordL_det_range <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem _root_.GlobalTheory.T.hecke_indicator_formula : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n k : ℕ) (ϖ : w.adicCompletion E), IsUnifV E w ϖ → k ≤ n → ∀ g : GL (Fin n) (w.adicCompletion E), Tj ℂ n (Ov E w) ϖ k g = if IsInt w g.val ∧ IsInt w (ϖ • (g⁻¹).val) ∧ ordL g.val.det = (k : ℤ) then 1 else 0 := by
  first | exact @GlobalTheory.CompanionTheory.CtS.Tj_eq_ite | exact GlobalTheory.CompanionTheory.CtS.Tj_eq_ite | (intros; apply GlobalTheory.CompanionTheory.CtS.Tj_eq_ite <;> assumption)
end

section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC PositivityTheory.Affgl

noncomputable section

namespace GlobalTheory.CompanionTheory.CuspInvariant

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem memL2_of_bounded_continuous_invariant (μ : Measure (GA E a)) [μ.IsHaarMeasure] {φ : GA E a → ℂ} (hc : Continuous φ)
    (hl : LeftInv (latticeGL E a) φ) {C : ℝ} (hC : ∀ g, ‖φ g‖ ≤ C) : MemL2Quotient (latticeGL E a) μ φ := by
  have hfin := GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E a μ
  refine ⟨hl, MemLp.of_bound ?_ C (.of_forall fun q => hC _)⟩
  refine aestronglyMeasurable_quotMeasure_iff_lift.2 ?_
  rw [hl.lift_descend]
  exact hc.aestronglyMeasurable

theorem repOp_toL2cusp (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {f φ : GA E a → ℂ}
    (hf : Continuous f) (hs : HasCompactSupport f) (h : MemL2Quotient (latticeGL E a) μ φ) (hm : φ ∈ cuspCont E a)
    (hφ : ∀ x, convR μ f φ x = φ x) :
    repOp (Rcusp μ) μ f ⟨h.toL2, toL2_mem_cuspidal h hm⟩ = ⟨h.toL2, toL2_mem_cuspidal h hm⟩ := by
  have hi : Integrable f μ := hf.integrable_of_hasCompactSupport hs
  have hT : IsRepOp (R (latticeGL E a) μ) μ f (Rop (latticeGL E a) μ f) := isRepOp_Rop hi
  refine Subtype.ext (((isSubrep_L2cusp μ).coe_repOp_rep hT).2 _ |>.trans ?_)
  refine l2DiscreteQuotient_ext_iff_lift_ae_eq.2 ?_
  have e := h.lift_toL2_ae_eq
  refine (GlobalTheory.AutomorphicL2Pointwise.lift_Rop_eq_convR _ _ μ f hi h.toL2).2.trans
    (Filter.EventuallyEq.trans (.of_forall fun x => ?_) e.symm)
  rw [← hφ x]
  refine integral_congr_ae ?_
  filter_upwards [(measurePreserving_mul_left μ x).quasiMeasurePreserving.ae e] with y hy
  rw [hy]

theorem finiteDimensional_span (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {f : GA E a → ℂ}
    (hf : Continuous f) (hs : HasCompactSupport f) (S : Set (GA E a → ℂ))
    (hS : ∀ φ ∈ S, φ ∈ cuspCont E a ∧ (∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C) ∧ ∀ x, convR μ f φ x = φ x) :
    FiniteDimensional ℂ (Submodule.span ℂ S) := by
  have hA := GlobalTheory.CompanionTheory.CuspidalCompact.isCompactOperator_repOp_Rcusp E a μ f hf hs
  have hK := GlobalTheory.CompanionTheory.CompactFix.finiteDimensional_ker_sub_id _ hA
  set K := LinearMap.ker (((repOp (Rcusp μ) μ f : L2cusp μ →L[ℂ] L2cusp μ) : L2cusp μ →ₗ[ℂ] L2cusp μ) - LinearMap.id)
  let t := GlobalTheory.CompanionTheory.CuspTransfer.toL2cusp μ
  have ht : Function.Injective t := (injective_iff_map_eq_zero _).2 fun φ e => Subtype.ext (by
    by_contra h0
    exact toL2_ne_zero φ.2.2 φ.2.1.1 h0 (congrArg Subtype.val e))
  let Q := K.comap t
  have hQ : FiniteDimensional ℂ Q := FiniteDimensional.of_injective (t.restrict (q := K) fun x hx => hx)
    fun x y e => Subtype.ext (ht (congrArg Subtype.val e))
  have hle : Submodule.span ℂ S ≤ Q.map (GlobalTheory.CompanionTheory.CuspTransfer.cuspidalL2Functions μ).subtype := Submodule.span_le.2 fun φ hφ => by
    obtain ⟨h1, ⟨C, hC⟩, h3⟩ := hS φ hφ
    have hm := memL2_of_bounded_continuous_invariant μ h1.1 (leftInv_of_mem_cuspCont h1) hC
    refine ⟨⟨φ, h1, hm⟩, ?_, rfl⟩
    change _ ∈ K
    simp only [K, LinearMap.mem_ker, LinearMap.sub_apply, ContinuousLinearMap.coe_coe, LinearMap.id_apply]
    exact sub_eq_zero.2 (repOp_toL2cusp μ hf hs hm h1 h3)
  exact Submodule.finiteDimensional_of_le hle

theorem exists_compact_open {L : Subgroup (GL (Fin a) (Af E))} (hL : IsOpen (L : Set (GL (Fin a) (Af E)))) :
    ∃ U : Subgroup (GL (Fin a) (Af E)), U ≤ L ∧ IsOpen (U : Set (GL (Fin a) (Af E))) ∧
      IsCompact (U : Set (GL (Fin a) (Af E))) := by
  obtain ⟨C, hC, hC1⟩ := exists_compact_mem_nhds (1 : GA E a)
  have hc := ContAut.continuous_map_pFin E a
  have hW : (GeneralLinearGroup.map (pFin E) '' C : Set (GL (Fin a) (Af E))) ∈ 𝓝 (1 : GL (Fin a) (Af E)) := by
    set_option synthInstance.maxHeartbeats 200000 in
      have h1 : finGL E a ⁻¹' C ∈ 𝓝 (1 : GL (Fin a) (Af E)) :=
        (GlobalTheory.CompanionTheory.DenseKFin.continuous_finGL (E := E) (a := a)).continuousAt.preimage_mem_nhds (by simpa using hC1)
    exact Filter.mem_of_superset h1 fun k hk => ⟨_, hk, pFin_finGL k⟩
  obtain ⟨U, hU, hUW⟩ := GlobalTheory.CompanionTheory.DenseKFin.exists_openSubgroup_GLAf (Filter.inter_mem hW (hL.mem_nhds (one_mem L)))
  exact ⟨U, fun k hk => (hUW hk).2, hU, (hC.image hc).of_isClosed_subset (Subgroup.isClosed_of_isOpen U hU)
    fun k hk => (hUW hk).1⟩

abbrev pI (g : GA E a) : GL (Fin a) (Cinf E) := GeneralLinearGroup.map (pInf E) g

def levelSet (U : Subgroup (GL (Fin a) (Af E))) : Set (GA E a) := {g | GeneralLinearGroup.map (pFin E) g ∈ U}

theorem isClopen_levelSet {U : Subgroup (GL (Fin a) (Af E))} (hU : IsOpen (U : Set (GL (Fin a) (Af E)))) :
    IsClopen (levelSet U : Set (GA E a)) :=
  ⟨(Subgroup.isClosed_of_isOpen U hU).preimage (ContAut.continuous_map_pFin E a),
    hU.preimage (ContAut.continuous_map_pFin E a)⟩

theorem isCompact_levelSet_inter {U : Subgroup (GL (Fin a) (Af E))} (hU : IsCompact (U : Set (GL (Fin a) (Af E))))
    {K : Set (GL (Fin a) (Cinf E))} (hK : IsCompact K) : IsCompact ((levelSet U : Set (GA E a)) ∩ pI ⁻¹' K) := by
  have e : (levelSet U : Set (GA E a)) ∩ pI ⁻¹' K =
      (GASplit.splitEquiv E a).toHomeomorph ⁻¹' (K ×ˢ (U : Set (GL (Fin a) (Af E)))) := by
    ext g
    exact and_comm
  rw [e]
  exact (Homeomorph.isCompact_preimage _).2 (hK.prod hU)

section Measure

variable [MeasurableSpace (GL (Fin a) (Cinf E))] [BorelSpace (GL (Fin a) (Cinf E))]

def levelMeasure (μ : Measure (GA E a)) (U : Subgroup (GL (Fin a) (Af E))) : Measure (GL (Fin a) (Cinf E)) :=
  (μ.restrict (levelSet U)).map pI

theorem measurable_pI : Measurable (pI : GA E a → GL (Fin a) (Cinf E)) :=
  (ContAut.continuous_map_pInf E a).measurable

theorem isHaarMeasure_levelMeasure (μ : Measure (GA E a)) [μ.IsHaarMeasure] {U : Subgroup (GL (Fin a) (Af E))}
    (hU : IsOpen (U : Set (GL (Fin a) (Af E)))) (hUc : IsCompact (U : Set (GL (Fin a) (Af E)))) :
    (levelMeasure μ U).IsHaarMeasure := by
  haveI : T2Space (GL (Fin a) (Cinf E)) := Units.isEmbedding_embedProduct.t2Space
  have hH := (isClopen_levelSet hU).isOpen.measurableSet
  have hp := measurable_pI (E := E) (a := a)
  have hmeas : ∀ {K : Set (GL (Fin a) (Cinf E))}, MeasurableSet K →
      levelMeasure μ U K = μ (pI ⁻¹' K ∩ levelSet U) := fun hK => by
    rw [levelMeasure, Measure.map_apply hp hK, Measure.restrict_apply (hp hK)]
  refine { lt_top_of_isCompact := ?_, map_mul_left_eq_self := ?_, open_pos := ?_ }
  · intro K hK
    rw [hmeas hK.measurableSet, Set.inter_comm]
    exact (isCompact_levelSet_inter hUc hK).measure_lt_top
  · intro y
    have hpre : (fun g : GA E a => infGL E a y * g) ⁻¹' levelSet U = levelSet U := by
      ext g
      simp [levelSet]
    have hmp := (measurePreserving_mul_left μ (infGL E a y)).restrict_preimage hH
    rw [hpre] at hmp
    rw [levelMeasure, Measure.map_map (measurable_const_mul y) hp]
    have e : ((fun x => y * x) ∘ pI : GA E a → _) = pI ∘ fun g => infGL E a y * g := by
      funext g
      simp
    rw [e, ← Measure.map_map hp (measurable_const_mul _), hmp.map_eq]
  · intro V hV hne
    obtain ⟨y, hy⟩ := hne
    rw [hmeas hV.measurableSet]
    refine ((hV.preimage (ContAut.continuous_map_pInf E a)).inter (isClopen_levelSet hU).isOpen).measure_ne_zero μ
      ⟨infGL E a y, by simpa using hy, ?_⟩
    simp [levelSet, one_mem]

theorem integral_levelMeasure (μ : Measure (GA E a)) {U : Subgroup (GL (Fin a) (Af E))}
    (hU : IsOpen (U : Set (GL (Fin a) (Af E)))) {α : GL (Fin a) (Cinf E) → ℂ} (hα : Continuous α) {φ : GA E a → ℂ}
    (hφ : Continuous φ) (hfix : ∀ k ∈ U, ∀ x, φ (x * finGL E a k) = φ x) (g : GA E a) :
    ∫ y, φ (g * infGL E a y) * α y ∂levelMeasure μ U = convR μ ((levelSet U).indicator (α ∘ pI)) φ g := by
  have hH := (isClopen_levelSet (E := E) hU).isOpen.measurableSet
  have hc : Continuous fun y => φ (g * infGL E a y) * α y :=
    (hφ.comp (continuous_const.mul GlobalTheory.CompanionTheory.DenseKFin.continuous_infGL)).mul hα
  rw [levelMeasure, integral_map measurable_pI.aemeasurable hc.aestronglyMeasurable]
  have e : (fun y => (levelSet U).indicator (α ∘ pI) y * φ (g * y)) =
      (levelSet U).indicator fun y => α (pI y) * φ (g * y) := by
    funext y
    by_cases h : y ∈ levelSet U <;> simp [h]
  rw [convR, e, integral_indicator hH]
  refine setIntegral_congr_fun hH fun y hy => ?_
  have h := hfix _ hy (g * infGL E a (pI y))
  rw [mul_assoc, infGL_mul_finGL] at h
  simp only [h, mul_comm]

end Measure

theorem continuous_test {U : Subgroup (GL (Fin a) (Af E))} (hU : IsOpen (U : Set (GL (Fin a) (Af E))))
    {α : GL (Fin a) (Cinf E) → ℂ} (hα : Continuous α) :
    Continuous ((levelSet U : Set (GA E a)).indicator (α ∘ pI)) :=
  (hα.comp (ContAut.continuous_map_pInf E a)).indicator fun x hx => by
    rw [(isClopen_levelSet hU).frontier_eq] at hx
    exact absurd hx (Set.notMem_empty x)

theorem hasCompactSupport_test {U : Subgroup (GL (Fin a) (Af E))} (hU : IsCompact (U : Set (GL (Fin a) (Af E))))
    {α : GL (Fin a) (Cinf E) → ℂ} (hα : HasCompactSupport α) :
    HasCompactSupport ((levelSet U : Set (GA E a)).indicator (α ∘ pI)) := by
  set_option synthInstance.maxHeartbeats 200000 in
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_levelSet_inter hU hα) fun g hg => ?_
  rw [Function.mem_support] at hg
  have h1 : g ∈ levelSet U := by
    by_contra h
    exact hg (Set.indicator_of_notMem h _)
  refine ⟨h1, subset_tsupport _ ?_⟩
  rw [Function.mem_support]
  rwa [Set.indicator_of_mem h1] at hg

theorem cuspInvFin (hb : GlobalTheory.Published.CuspFormsBoundedGL)
    (hu : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), UnifAlpha E a) :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), CuspInvFin E a := by
  intro E _ _ _ a L hL W _ _ _ ρ hρ J hJ
  obtain ⟨U, hUL, hUo, hUc⟩ := exists_compact_open hL
  letI : MeasurableSpace (GL (Fin a) (Cinf E)) := borel _
  haveI : BorelSpace (GL (Fin a) (Cinf E)) := ⟨rfl⟩
  let μ : Measure (GA E a) := Measure.haar
  haveI := GlobalTheory.CovolGL.isMulRightInvariant E a μ
  obtain ⟨α, hαc, hαs, hα⟩ := hu E a W ρ hρ J hJ (levelMeasure μ U) (isHaarMeasure_levelMeasure μ hUo hUc)
  set S : Set (Sm E a) := {φ | φ ∈ genSpace L ρ J ∧ IsCuspidal φ.1 ∧
    ∀ t g, φ.1 (GlobalTheory.UnitaryBC.splitCentre E a t * g) = φ.1 g} with hSdef
  have key := finiteDimensional_span μ (continuous_test hUo hαc) (hasCompactSupport_test hUc hαs)
    ((Sm E a).subtype '' S) (by
      rintro _ ⟨φ, ⟨hφ, hcusp, hz⟩, rfl⟩
      have hcf : IsCuspForm φ := ⟨hφ.1, hcusp⟩
      have hm := mem_cuspCont_of_isCuspForm hcf hz
      refine ⟨hm, hb.of_invariant hcf hz, fun x => ?_⟩
      refine (integral_levelMeasure μ hUo hαc hm.1 (fun k hk y => ?_) x).symm.trans (hα L φ hφ x).symm
      exact congrFun (congrArg Subtype.val (hφ.2.1 k (hUL hk))) y)
  rw [← Submodule.map_span] at key
  exact (Submodule.equivMapOfInjective _ (Submodule.injective_subtype _) _).symm.finiteDimensional

end GlobalTheory.CompanionTheory.CuspInvariant

end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcN.F2
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.constant_term_convolution_hecke : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (K' : Subgroup (GLw n w)), IsOpen (K' : Set (GLw n w)) → K' ≤ GlobalTheory.LFun.KGL w (n := n) → (∀ k ∈ GlobalTheory.LFun.KGL w (n := n), ∀ k' ∈ K', k * k' * k⁻¹ ∈ K') → ∀ X : Finset (GLw n w), (∀ x ∈ X, x ∈ GlobalTheory.LFun.KGL w (n := n)) → (∀ k ∈ GlobalTheory.LFun.KGL w (n := n), ∃! x ∈ X, x⁻¹ * k ∈ K') → ∀ f₁ f₂ : GLw n w → ℂ, IsHk K' f₁ → IsHk K' f₂ → ∀ x ∈ X, ∀ z ∈ X, ∀ m, phi3 h w (gconv f₁ f₂) x z m = ((X.card : ℂ))⁻¹ * ∑ y ∈ X, mconv (phi3 h w f₁ x y) (phi3 h w f₂ y z) m := by
  first | exact @GlobalTheory.CompanionTheory.ConvMat.constant_term_convolution | exact GlobalTheory.CompanionTheory.ConvMat.constant_term_convolution | (intros; apply GlobalTheory.CompanionTheory.ConvMat.constant_term_convolution <;> assumption)
end
