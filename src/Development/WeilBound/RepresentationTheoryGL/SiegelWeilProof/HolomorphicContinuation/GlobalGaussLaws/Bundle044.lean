module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatAdelicMatrixOfMemAdelicSchwartz
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatAdelicMatrixContinuousLeMajorantStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1998
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1294
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle007
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2258
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle017
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle237
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BlockMatrixTwoByTwoFinStandardSkewMap
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MoveRationalInvariant
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle035
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle012

@[expose] public section

section

noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct ENNReal Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn GlobalTheory.SiegelFormula
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.DHolH

variable {D : D7} {n : ℕ}

def thS (V : HSp D) (f : Mx D V.rank n → ℂ) (h : GA D V) : ℂ := ∑' ξ, f (invPt V h ξ)

theorem leftInv_thS (V : HSp D) (f : Mx D V.rank n → ℂ) : LeftInv (GQ V) (thS V f) := by
  intro γ hγ h
  obtain ⟨δ, -, hδ⟩ : ∃ δ : GL (Fin V.rank) D.host.E, _ ∧ Formalism.UG.bc (incA D) δ = Formalism.L2.Theta.matHom V γ⁻¹ := inv_mem hγ
  let e : Matrix (Fin V.rank) (Fin n) D.host.E ≃ Matrix (Fin V.rank) (Fin n) D.host.E :=
    ⟨fun ξ => δ.1 * ξ, fun ξ => δ⁻¹.1 * ξ, fun ξ => by simp, fun ξ => by simp⟩
  have h1 : Formalism.L2.Theta.mt V γ⁻¹ = δ.1.map (incA D) := (congrArg Units.val hδ).symm
  have h2 : Formalism.L2.Theta.mt V (γ * h)⁻¹ = Formalism.L2.Theta.mt V h⁻¹ * Formalism.L2.Theta.mt V γ⁻¹ := by rw [mul_inv_rev]; rfl
  refine (tsum_congr fun ξ => ?_).trans (e.tsum_eq fun ξ => f (invPt V h ξ))
  simp only [invPt, e, Equiv.coe_fn_mk, h2, h1, Matrix.mul_assoc, Matrix.map_mul]

theorem enorm_thS_le (V : HSp D) (f : Mx D V.rank n → ℂ) (h : GA D V) : ‖thS V f h‖ₑ ≤ absTheta V f h :=
  enorm_tsum_le_tsum_enorm

theorem absTheta_mono (V : HSp D) {f M : Mx D V.rank n → ℂ} (hfM : ∀ x, ‖f x‖ ≤ ‖M x‖) (h : GA D V) :
    absTheta V f h ≤ absTheta V M h :=
  ENNReal.tsum_le_tsum fun _ => enorm_le_iff_norm_le.2 (hfM _)

theorem absThetaInt_mono (V : HSp D) (ν : Measure (GA D V)) {f M : Mx D V.rank n → ℂ} (hfM : ∀ x, ‖f x‖ ≤ ‖M x‖) :
    absThetaInt V ν f ≤ absThetaInt V ν M :=
  lintegral_mono fun q => absTheta_mono V hfM _

theorem absThetaInt_smul_lt (V : HSp D) (ν : Measure (GA D V)) (c : ℂ) {M : Mx D V.rank n → ℂ}
    (hM : absThetaInt V ν M < ⊤) : absThetaInt V ν (c • M) < ⊤ := by
  unfold absThetaInt
  have : ∀ q, descend (GQ V) (absTheta V (c • M)) q = ‖c‖ₑ * descend (GQ V) (absTheta V M) q := fun q =>
    GlobalTheory.AbsThetaSemi.absTheta_smul V c M q.out
  simp_rw [this]
  rw [lintegral_const_mul' _ _ enorm_ne_top]
  exact ENNReal.mul_lt_top enorm_lt_top hM

theorem aestronglyMeasurable_thS (V : HSp D) (ν : Measure (GA D V)) [ν.IsHaarMeasure] {f : Mx D V.rank n → ℂ} (hf : Continuous f)
    (hfin : absThetaInt V ν f < ⊤) : AEStronglyMeasurable (descend (GQ V) (thS V f)) (autMeasure V ν) := by
  rw [autMeasure, aestronglyMeasurable_quotMeasure_iff_lift, (leftInv_thS V f).lift_descend]
  have hae : ∀ᵐ q ∂autMeasure V ν, descend (GQ V) (absTheta V f) q < ⊤ :=
    ae_lt_top (GlobalTheory.AbsThetaSemi.measurable_descend_absTheta V hf) hfin.ne
  have hae' : ∀ᵐ h ∂ν, absTheta V f h < ⊤ := by
    have := MeasureTheory.QuasiMeasurePreserving.ae (quasiMeasurePreserving_mk (Γ := GQ V) (μ := ν)) hae
    filter_upwards [this] with h hh
    rwa [(leftInv_absTheta V f).descend_mk] at hh
  have := GlobalTheory.ThetaTransformMeas.countable_field D.host.E
  have : Countable (Matrix (Fin V.rank) (Fin n) D.host.E) :=
    inferInstanceAs (Countable (Fin V.rank → Fin n → D.host.E))
  have hsum : ∀ᵐ h ∂ν, Summable fun ξ : Matrix (Fin V.rank) (Fin n) D.host.E => f (invPt V h ξ) :=
    hae'.mono fun h hh => Summable.of_enorm hh.ne
  exact aestronglyMeasurable_of_tendsto_ae (μ := ν)
    (Filter.atTop : Filter (Finset (Matrix (Fin V.rank) (Fin n) D.host.E)))
    (f := fun F h => ∑ ξ ∈ F, f (invPt V h ξ))
    (fun F => (continuous_finsetSum F fun ξ _ =>
      hf.comp (GlobalTheory.AbsThetaSemi.continuous_invPt V ξ)).aestronglyMeasurable)
    (hsum.mono fun h hh => hh.hasSum)

theorem ae_absTheta_lt (V : HSp D) (ν : Measure (GA D V)) [ν.IsHaarMeasure] {M : Mx D V.rank n → ℂ} (hM : Continuous M)
    (hfin : absThetaInt V ν M < ⊤) : ∀ᵐ q ∂autMeasure V ν, descend (GQ V) (absTheta V M) q < ⊤ :=
  ae_lt_top (GlobalTheory.AbsThetaSemi.measurable_descend_absTheta V hM) hfin.ne

theorem integrable_absTheta_toReal (V : HSp D) (ν : Measure (GA D V)) [ν.IsHaarMeasure] {M : Mx D V.rank n → ℂ} (hM : Continuous M)
    (hfin : absThetaInt V ν M < ⊤) :
    Integrable (fun q => (descend (GQ V) (absTheta V M) q).toReal) (autMeasure V ν) :=
  integrable_toReal_of_lintegral_ne_top (GlobalTheory.AbsThetaSemi.measurable_descend_absTheta V hM).aemeasurable hfin.ne

theorem sch_facts (hP : GlobalTheory.Published.WeilThetaConvergence) (V : HSp D) (hn : 1 ≤ n) (hr : n + Formalism.MainNotions.SchurIrreducible.wittIdx V < V.rank)
    (θ : InfFam D) (hθ : IsInfFam θ) (ν : Measure (GA D V)) (hν : ν.IsHaarMeasure) {M : Mx D V.rank n → ℂ}
    (hM : M ∈ schwartzA θ V.rank n) : Continuous M ∧ absThetaInt V ν M < ⊤ :=
  ⟨(GlobalTheory.T.schwartzBruhatAdelicMatrix_continuous_le_majorant D θ hθ _ _ M (GlobalTheory.SchwartzPure.isSchwartzBruhat_of_mem_schwartzA D θ hθ _ _ M hM)).1,
    hP D n V hn (Or.inr hr) θ hθ ν hν ⟨M, hM⟩⟩

end PositivityTheory.Rg.Sw.Glob.DHolH
end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open Formalism.IndefR.Eqv (psiT eq_thetaC)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.FTH

open PositivityTheory.Rg.Sw.Glob.FTP
open Classical

variable {D : D7} {n m : ℕ}


theorem compAt_add (θ : InfFam D) (τ : D.what₂.Tau) (a b : Mx D m n) :
    compAt θ τ (a + b) = compAt θ τ a + compAt θ τ b := by
  ext i j; simp only [compAt, Matrix.map_apply, Matrix.add_apply, RingHom.map_add (f := _)]


theorem finMap_add (a b : Mx D m n) : (a + b).map (finPart D) = a.map (finPart D) + b.map (finPart D) := by
  ext i j; simp only [Matrix.map_apply, Matrix.add_apply, RingHom.map_add (f := _)]

theorem away_add {θ : InfFam D} (hθ : IsInfFam θ) {τ : D.what₂.Tau} {fr : Matrix (Fin m) (Fin m) ℂ}
    {Ψ : Mx D m n → ℂ} (hΨ : AwayCls θ τ fr Ψ) (y : Mx D m n) (u : Fin m → Fin n → ℂ) :
    Ψ (y + sIns τ fr u) = Ψ y := by
  refine hΨ.1 _ _ (fun τ' hne => ?_) ?_
  · rw [compAt_add, show sIns (D := D) τ fr u = insT τ (fr * Matrix.of u) from rfl, compAt_insT hθ, ite_eq_right hne,
      add_zero]
  · rw [finMap_add, show sIns (D := D) τ fr u = insT τ (fr * Matrix.of u) from rfl, finMap_insT, add_zero]

theorem cont_of_away {θ : InfFam D} (hθ : IsInfFam θ) {τ : D.what₂.Tau} {fr : Matrix (Fin m) (Fin m) ℂ}
    {Ψ : Mx D m n → ℂ} (hΨ : AwayCls θ τ fr Ψ) : Continuous Ψ := by
  obtain ⟨S, hS⟩ := gs_sch (m := m) (n := n) 1 one_pos
  have hmem := hΨ.2 (gs 1) ⟨S, funext hS⟩
  have hc := GlobalTheory.RegSch.CentreWeilComm.continuous_of_mem hθ ⟨_, hmem⟩
  have hg : Continuous fun x : Mx D m n => gs (n := n) 1 (fr⁻¹ * compAt θ τ x) := by
    have h1 : Continuous fun x : Mx D m n => (S (piF θ τ fr x)) := S.continuous.comp (continuous_piF hθ τ fr)
    refine h1.congr fun x => ?_
    rw [hS]; rfl
  have hne : ∀ x : Mx D m n, gs (n := n) 1 (fr⁻¹ * compAt θ τ x) ≠ 0 := fun x => Complex.exp_ne_zero _
  have e : Ψ = fun x => tens θ τ fr (gs 1) Ψ x / gs (n := n) 1 (fr⁻¹ * compAt θ τ x) := by
    funext x
    simp only [tens]
    field_simp [hne x]
  rw [e]
  exact hc.div hg hne

def Bw (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) (θ : InfFam D) (τ : D.what₂.Tau) (fr : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (Ψ : Mx D V.rank n → ℂ) (x y : Mx D V.rank n) : ℂ :=
  Ψ y * ψ (trA (Matrix.trace (GlobalTheory.StdUnn.inner V x (y - sIns τ fr (piF θ τ fr y)))))

theorem Bw_add {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hdet : IsUnit fr.det) (ψ : AddChar (AF D.host.F) ℂ) {Ψ : Mx D V.rank n → ℂ} (hΨ : AwayCls θ τ fr Ψ)
    (x y : Mx D V.rank n) (u : Fin V.rank → Fin n → ℂ) :
    Bw ψ V θ τ fr Ψ x (y + sIns τ fr u) = Bw ψ V θ τ fr Ψ x y := by
  have e : y + sIns τ fr u - sIns τ fr (piF θ τ fr (y + sIns τ fr u)) = y - sIns τ fr (piF θ τ fr y) := by
    rw [map_add (piF θ τ fr), piF_sIns hθ τ hdet, map_add (sIns τ fr)]
    abel
  unfold Bw
  rw [away_add hθ hΨ, e]

set_option synthInstance.maxHeartbeats 800000 in
theorem continuous_Bw {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau}
    {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ)
    {Ψ : Mx D V.rank n → ℂ} (hΨ : AwayCls θ τ fr Ψ) (x : Mx D V.rank n) :
    Continuous (Bw ψ V θ τ fr Ψ x) := by
  have := GlobalTheory.Doubling.isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have : ContinuousSub (Mx D V.rank n) := inferInstance
  refine (cont_of_away hθ hΨ).mul ?_
  have htr : Continuous (trA (D := D)) := by
    have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
    exact IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF D.host.F) (AE D))
  have hinner : Continuous (fun y : Mx D V.rank n => GlobalTheory.StdUnn.inner V x y) := by
    unfold GlobalTheory.StdUnn.inner
    exact continuous_const.matrix_mul (continuous_const.matrix_mul continuous_id)
  have h := hψ.1.comp (htr.comp hinner.matrix_trace)
  exact h.comp (continuous_id.sub ((continuous_sIns τ fr).comp (continuous_piF hθ τ fr)))

theorem norm_Bw {V : HSp D} {θ : InfFam D} {τ : D.what₂.Tau} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (Ψ : Mx D V.rank n → ℂ) (x y : Mx D V.rank n) :
    ‖Bw ψ V θ τ fr Ψ x y‖ = ‖Ψ y‖ := by
  unfold Bw; rw [norm_mul, hψ.2.1, mul_one]

end PositivityTheory.Rg.Sw.Glob.FTH
end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.OG

variable {D : D7}

theorem g_ext {n : ℕ} {g h : G D n} (e : mat g = mat h) : g = h := by
  unfold mat at e
  exact Subtype.ext (Units.ext e)

theorem exists_slice {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (τ : D.what₂.Tau) (x0 : Mx D m n)
    (z : Matrix (Fin m) (Fin n) ℂ) : ∃ x : Mx D m n, compAt θ τ x = z ∧
      (∀ τ', τ' ≠ τ → compAt θ τ' x = compAt θ τ' x0) ∧ x.map (finPart D) = x0.map (finPart D) := by
  classical
  obtain ⟨h1, h2⟩ := GlobalTheory.AdForm.RatMove.realPt_spec hθ (fun τ' => if τ' = τ then z - compAt θ τ x0 else 0)
  refine ⟨x0 + GlobalTheory.AdForm.realPt θ (fun τ' => if τ' = τ then z - compAt θ τ x0 else 0), ?_, ?_, ?_⟩
  · rw [GlobalTheory.RealParamSize.compAt_add, h2]
    simp
  · intro τ' h
    rw [GlobalTheory.RealParamSize.compAt_add, h2]
    simp [h]
  · rw [Matrix.map_add _ (map_add (finPart D)), h1, add_zero]

theorem tens_at {θ : InfFam D} {m n : ℕ} (τ : D.what₂.Tau) {fr : Matrix (Fin m) (Fin m) ℂ} (hfr : IsUnit fr.det)
    (f : (Fin m → Fin n → ℂ) → ℂ) (Ψ : Mx D m n → ℂ) (x : Mx D m n) (u : Matrix (Fin m) (Fin n) ℂ)
    (hx : compAt θ τ x = fr * u) : tens θ τ fr f Ψ x = f u * Ψ x := by
  simp only [tens, hx, Matrix.nonsing_inv_mul_cancel_left _ _ hfr]

theorem awayCls_zero {θ : InfFam D} {m n : ℕ} (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) :
    AwayCls θ τ fr (0 : Mx D m n → ℂ) := by
  refine ⟨fun _ _ _ _ => rfl, fun f _ => ?_⟩
  have : tens θ τ fr f (0 : Mx D m n → ℂ) = 0 := by
    funext x
    simp [tens]
  rw [this]
  exact zero_mem _

theorem exists_nU (n : ℕ) (b : Matrix (Fin n) (Fin n) ℂ) (hb : bᴴ = b) : ∃ y : GR n, mR y = nU b := by
  let u : GL (Fin n ⊕ Fin n) ℂ :=
    ⟨nU b, nU (-b), by simp [nU, Matrix.fromBlocks_multiply], by simp [nU, Matrix.fromBlocks_multiply]⟩
  have hu : u ∈ GR n := by
    show InG (nU b)
    simp only [InG, nU, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hb]
    simp
  exact ⟨⟨u, hu⟩, rfl⟩

theorem component_block_matrix (θ : InfFam D) (τ : D.what₂.Tau) {n : ℕ} (a b c d : Mx D n n) :
    compAt θ τ (blk4 a b c d) = blk4 (compAt θ τ a) (compAt θ τ b) (compAt θ τ c) (compAt θ τ d) := by
  exact GlobalTheory.StdUnn.Frame.block_matrix_map _ a b c d

theorem finite_part_block_matrix {n : ℕ} (a b c d : Mx D n n) :
    (blk4 a b c d).map (finPart D) = blk4 (a.map (finPart D)) (b.map (finPart D)) (c.map (finPart D)) (d.map (finPart D)) := by
  exact GlobalTheory.StdUnn.Frame.block_matrix_map _ a b c d

theorem neg_block_matrix {R : Type} [CommRing R] {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) R) :
    -blk4 a b c d = blk4 (-a) (-b) (-c) (-d) := by
  unfold blk4
  rw [← Matrix.fromBlocks_neg]
  rfl

theorem jsq {R : Type} [CommRing R] {n : ℕ} :
    (blk4 (0 : Matrix (Fin n) (Fin n) R) 1 (-1) 0) * blk4 0 1 (-1) 0 = -1 := by
  rw [GlobalTheory.StdUnn.Frame.submatrix_fromBlocks_mul, ← GlobalTheory.StdUnn.Frame.block_matrix_one, neg_block_matrix]
  simp

theorem mat_inv_w {n : ℕ} (w : G D n) (hw : mat w = blk4 0 1 (-1) 0) : mat w⁻¹ = -blk4 0 1 (-1) 0 := by
  have h1 : mat w⁻¹ * mat w = 1 := by
    show mat (w⁻¹ * w) = 1
    rw [inv_mul_cancel]
    rfl
  have h2 : mat w * (-mat w) = 1 := by rw [mul_neg, hw, jsq, neg_neg]
  calc mat w⁻¹ = mat w⁻¹ * (mat w * (-mat w)) := by rw [h2, mul_one]
    _ = -mat w := by rw [← mul_assoc, h1, one_mul]
    _ = _ := by rw [hw]

end PositivityTheory.Rg.Sw.Glob.OG
end
end
