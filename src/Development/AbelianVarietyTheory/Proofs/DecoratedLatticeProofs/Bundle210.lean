module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContinuesConst
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle237
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle177
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle308
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle219
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle245
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle251
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle194
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle155
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
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
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinIsotropicLine
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle385
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth

@[expose] public section

section

open scoped NNReal Matrix TensorProduct Topology
open Filter NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.EisCont GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Core.Rk.SWLaw (dblDec zeroSp)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EisCont

open Matrix Formalism.IndefR.Datum

variable {D : D7}

theorem jX_dblDec_mulVec (V : HSp D) (y : Fin V.rank → AE D) :
    (dblDec V).jX *ᵥ y = pairVec finSumFinEquiv (GlobalTheory.MixModel.giA V *ᵥ y) (GlobalTheory.MixModel.giA V *ᵥ y) := by
  funext k
  obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective k
  · rw [pairVec_inl]
    simp only [mulVec, HypDec.jX, dblDec, GlobalTheory.Core.Rk.SWLaw.stackRows,
      GlobalTheory.MixModel.giA, GlobalTheory.MixModel.rat, Matrix.map_apply,
      Matrix.submatrix_apply, id, Equiv.symm_apply_apply, fromRows_apply_inl, fromRows_apply_inr]
  · rw [pairVec_inr]
    simp only [mulVec, HypDec.jX, dblDec, GlobalTheory.Core.Rk.SWLaw.stackRows,
      GlobalTheory.MixModel.giA, GlobalTheory.MixModel.rat, Matrix.map_apply,
      Matrix.submatrix_apply, id, Equiv.symm_apply_apply, fromRows_apply_inl, fromRows_apply_inr]

theorem mem_siegel_of_mem_stab (V : HSp D) {p : GA D (dblSp V)} (h : p ∈ stab (dblDec V)) : p ∈ siegel V := by
  obtain ⟨α, hα⟩ := h
  refine mem_siegelOf.2 (keepsDiag_of_mulVec fun w hw => ?_)
  obtain ⟨x, rfl⟩ := (mem_diagSub _).1 hw
  have hx : pairVec finSumFinEquiv x x = (dblDec V).jX *ᵥ (GlobalTheory.MixModel.gA V *ᵥ x) := by
    rw [jX_dblDec_mulVec, mulVec_mulVec, GlobalTheory.MixModel.giA_mul_gA, one_mulVec]
  change mt (dblSp V) p *ᵥ _ ∈ _
  rw [hx, mulVec_mulVec, hα, ← mulVec_mulVec, jX_dblDec_mulVec]
  exact (pairVec_mem_diagSub _).2 rfl

theorem mul_jX_dblDec (V : HSp D) {p : GA D (dblSp V)} (h : p ∈ siegel V) :
    mt (dblSp V) p ⬝ (dblDec V).jX = (dblDec V).jX ⬝
      (GlobalTheory.MixModel.gA V * leviMat finSumFinEquiv (mt (dblSp V) p) * GlobalTheory.MixModel.giA V) := by
  have hk : KeepsDiag finSumFinEquiv (mt (dblSp V) p) := mem_siegelOf.1 h
  refine Matrix.ext_of_mulVec_single fun j => ?_
  rw [← mulVec_mulVec, ← mulVec_mulVec, jX_dblDec_mulVec, jX_dblDec_mulVec, hk.mulVec_diag, mulVec_mulVec,
    mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, GlobalTheory.MixModel.giA_mul_gA, Matrix.one_mul]

def gramGL (V : HSp D) : GL (Fin V.rank) (AE D) :=
  ⟨GlobalTheory.MixModel.gA V, GlobalTheory.MixModel.giA V, GlobalTheory.MixModel.gA_mul_giA V, GlobalTheory.MixModel.giA_mul_gA V⟩

theorem mem_stab_of_mem_siegel (V : HSp D) {p : GA D (dblSp V)} (h : p ∈ siegel V) : p ∈ stab (dblDec V) :=
  ⟨gramGL V * leviOf finSumFinEquiv (Formalism.L2.Theta.matHom (dblSp V)) ⟨p, h⟩ * (gramGL V)⁻¹,
    mul_jX_dblDec V h⟩

theorem onX_dblDec (V : HSp D) {p : GA D (dblSp V)} (h : p ∈ siegel V) (h' : p ∈ stab (dblDec V)) :
    onX (dblDec V) ⟨p, h'⟩ =
      gramGL V * leviOf finSumFinEquiv (Formalism.L2.Theta.matHom (dblSp V)) ⟨p, h⟩ * (gramGL V)⁻¹ :=
  Units.ext ((eq_of_mul_jX _ (mul_jX (dblDec V) ⟨p, h'⟩)).trans (eq_of_mul_jX _ (mul_jX_dblDec V h)).symm)

theorem isAniso_zeroSp (D : D7) : IsAniso (zeroSp D) := by
  rintro r C ⟨hr, hC, -⟩
  exact hC.ne_zero ⟨0, hr⟩ (funext fun i => Fin.elim0 i)

theorem siegel_eq_stab_dblDec : ∀ (D : D7) (V : HSp D), siegel V = stab (dblDec V) ∧ (∀ (p : GA D (dblSp V)) (h : p ∈ siegel V) (h' : p ∈ stab (dblDec V)), aP V ⟨p, h⟩ = Matrix.GeneralLinearGroup.det (onX (dblDec V) ⟨p, h'⟩)) ∧ IsAniso (zeroSp D) ∧ ∀ a : GL (Fin V.rank) (AE D), IsMaj V a → ∃ (L : Submodule (𝓞 D.host.E) (Fin (dblSp V).rank → D.host.E)) (b : GL (Fin (dblSp V).rank) (AE D)), IsLevel (dblSp V) L b ∧ Khat V a = lev (dblSp V) L b := by
  intro D V
  refine ⟨Subgroup.ext fun p => ⟨mem_stab_of_mem_siegel V, mem_siegel_of_mem_stab V⟩, fun p h h' => ?_,
    isAniso_zeroSp D, fun a ha => ⟨frameLat (dblSp V), blkGL finSumFinEquiv (a, a),
      ⟨(isLattice_frameLat_host (dblSp V)).toIsLattice, SelfDual.isSelfDualAt_frameLat D (dblSp V), ha.dbl⟩, Khat_eq V a⟩⟩
  rw [onX_dblDec V h h', map_mul, map_mul, map_inv, mul_inv_cancel_comm]
  rfl

end GlobalTheory.EisCont

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt

namespace GlobalTheory.ChartSplitIso

variable {D : D7}

def projEmb {v : HeightOneSpectrum (𝓞 D.host.F)} (φ : SplitProj D v) : D.host.E →ₐ[D.host.F] Fv D.host.F v :=
  (φ.restrictScalars D.host.F).comp Algebra.TensorProduct.includeRight

theorem splitProj_projEmb {v : HeightOneSpectrum (𝓞 D.host.F)} (φ : SplitProj D v)
    (x : Fv D.host.F v ⊗[D.host.F] D.host.E) : GlobalTheory.AdelicU.splitProj (projEmb φ) x = φ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a x =>
    have e : (a ⊗ₜ[D.host.F] x : Fv D.host.F v ⊗[D.host.F] D.host.E) = a • ((1 : Fv D.host.F v) ⊗ₜ[D.host.F] x) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [GlobalTheory.AdelicU.splitProj_tmul, e, map_smul, smul_eq_mul]
    rfl

def reindexGL {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (K : Type) [Field K]
    [TopologicalSpace K] [IsTopologicalRing K] (ε : ι ≃ κ) : GL κ K ≃ₜ* GL ι K where
  toMulEquiv := Units.mapEquiv (Matrix.reindexAlgEquiv K K ε.symm).toMulEquiv
  continuous_toFun := Units.continuous_iff.2
    ⟨(Units.continuous_val).matrix_submatrix _ _, (Units.continuous_coe_inv).matrix_submatrix _ _⟩
  continuous_invFun := Units.continuous_iff.2
    ⟨(Units.continuous_val).matrix_submatrix _ _, (Units.continuous_coe_inv).matrix_submatrix _ _⟩

theorem reindexGL_val {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (K : Type) [Field K]
    [TopologicalSpace K] [IsTopologicalRing K] (ε : ι ≃ κ) (x : GL κ K) : (reindexGL K ε x).1 = x.1.submatrix ε ε := rfl

theorem grpCo_eq {v : HeightOneSpectrum (𝓞 D.host.F)} (φ : SplitProj D v) (V : HSp D)
    (hJ : IsHermND D.sp.cm.sig V.gram) (B : GL (Fin V.rank) (Fv D.host.F v)) (g : GA D V) :
    grpCo φ V B g = GlobalTheory.AdelicU.splitEquivIn (GlobalTheory.AdelicU.isCMExt_host D) hJ (projEmb φ) B
      (GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g) := by
  refine Units.ext ?_
  rw [GlobalTheory.AdelicU.splitEquivIn_apply]
  simp only [grpCo, Units.val_mul]
  congr 2
  exact Matrix.ext fun i j => (splitProj_projEmb φ _).symm

end GlobalTheory.ChartSplitIso

namespace GlobalTheory.ChartSplitIso

theorem exists_equiv_emb : ∀ (D : D7) (s : PiLocalization₂ D) (k : ℕ) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v)
    (ι : GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) →* GA D s.V), IsSelfDualC s.V s.Λ → Formalism.L2.DIV.IsFrame s.β s.Λ →
    IsChart s k φ ι → ∃ e : GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) ≃ₜ* GlobalTheory.FinZeta.Gv s.V v,
      ∀ y, ι y = GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v (e y) := by
  intro D s k v φ ι _ _ hι
  obtain ⟨ε, -, hε⟩ := hι
  have hJ : IsHermND D.sp.cm.sig s.V.gram := (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm).2 s.V
  let Ψ := GlobalTheory.AdelicU.splitEquivIn (GlobalTheory.AdelicU.isCMExt_host D) hJ (projEmb φ) (frCo φ s.β)
  refine ⟨(reindexGL (Fv D.host.F v) ε).symm.trans Ψ.symm, fun y => (hε y).1.symm.trans ?_⟩
  change GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v (ι y)) = _
  congr 1
  apply Ψ.injective
  apply (reindexGL (Fv D.host.F v) ε).injective
  refine Units.ext ?_
  rw [reindexGL_val, ContinuousMulEquiv.trans_apply, ContinuousMulEquiv.apply_symm_apply,
    ContinuousMulEquiv.apply_symm_apply, ← (hε y).2, grpCo_eq φ s.V hJ]

end GlobalTheory.ChartSplitIso

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt

noncomputable section
namespace GlobalTheory.ChartStab



theorem mem_splitLat_iff {D : D7} {n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {β : GL (Fin n) (EAf D)}
    (hβ : Formalism.L2.DIV.IsFrame β Λ) {v : HeightOneSpectrum (𝓞 D.host.F)} (φ : SplitProj D v) (u : Fin n → Fv D.host.F v) :
    u ∈ GlobalTheory.AdelicU.splitLat (GlobalTheory.SplitProjChart.emb φ) Λ ↔
      ∀ i, Valued.v ((((frCo φ β)⁻¹ : GL (Fin n) (Fv D.host.F v)).1 *ᵥ u) i) ≤ 1 := by
  set e := GlobalTheory.EmbChart.idem (GlobalTheory.SplitProjChart.emb φ) with he_def
  have hπ : GlobalTheory.SplitHecke.Chart e v (rdA φ) := GlobalTheory.SplitProjChart.chart_idem φ
  have he : IsSplitIdem D e := GlobalTheory.EmbChart.isSplitIdem_idem _
  have hemb : GlobalTheory.AdelicU.chartEmb hπ = GlobalTheory.SplitProjChart.emb φ := AlgHom.ext fun x => by
    rw [GlobalTheory.AdelicU.chartEmb_apply, GlobalTheory.SplitProjChart.rdA_incA]; rfl
  choose y hy using fun k => hπ.1 (u k)
  obtain ⟨Λ₁, hle, hfg, heq⟩ := GlobalTheory.ChainOnto.LStab.exists_fg_sub hβ
  have hsl : GlobalTheory.AdelicU.splitLat (GlobalTheory.SplitProjChart.emb φ) Λ₁ = GlobalTheory.AdelicU.splitLat (GlobalTheory.SplitProjChart.emb φ) Λ := by
    ext w
    rw [GlobalTheory.AdelicU.mem_splitLat, GlobalTheory.AdelicU.mem_splitLat, GlobalTheory.ChainOnto.LStab.latLoc_eq hle hfg heq v]
  have h1 := GlobalTheory.AdelicU.SplitFrame.mem_latHat_iff_of_support (GlobalTheory.AdelicU.isCMExt_host D) _ hfg
    (GlobalTheory.AdelicU.SplitFrame.vecLoc_self he hπ y) (GlobalTheory.AdelicU.SplitFrame.vecLoc_ne he hπ y)
  rw [hemb, hsl, show (fun k => rdA φ (y k)) = u from funext hy] at h1
  rw [← h1, GlobalTheory.SplitFrameColumn.latHat_iff_hatL, heq]
  have hβ' := hβ (fun k => Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E (finPart D (e * y k)))
  rw [hβ']
  have hsw : (fun k => Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E (finPart D (e * y k))) =
      toEAf D e • fun k => toEAf D (y k) := funext fun k => (toEAf D).map_mul e (y k)
  rw [hsw, Matrix.mulVec_smul]
  set w : Fin n → EAf D := (β⁻¹).1 *ᵥ fun k => toEAf D (y k) with hw
  refine forall_congr' fun i => ?_
  have h2 : (toEAf D e • w) i = toEAf D (e * GlobalTheory.AdelicLatMove.finEmb D (w i)) := by
    rw [map_mul, GlobalTheory.SplitFrameColumn.toEAf_finEmb]; rfl
  have h3 : rdA φ (GlobalTheory.AdelicLatMove.finEmb D (w i)) =
      ((((frCo φ β)⁻¹ : GL (Fin n) (Fv D.host.F v)).1 *ᵥ u) i) := by
    rw [← GlobalTheory.SplitProjChart.rdE_toEAf, GlobalTheory.SplitFrameColumn.toEAf_finEmb, hw, RingHom.map_mulVec]
    unfold frCo
    rw [← map_inv]
    congr 1
    funext k
    exact (GlobalTheory.SplitProjChart.rdE_toEAf φ (y k)).trans (hy k)
  rw [h2, show toEAf D (e * GlobalTheory.AdelicLatMove.finEmb D (w i)) =
      Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E (finPart D (e * GlobalTheory.AdelicLatMove.finEmb D (w i))) from rfl,
    GlobalTheory.SplitFrameColumn.comm_mem_intAf_iff, hπ.2.2.2, GlobalTheory.SplitHecke.isInt_Ov, HeightOneSpectrum.mem_adicCompletionIntegers, h3]

theorem hermND (D : D7) (V : HSp D) : IsHermND D.sp.cm.sig V.gram :=
  (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm).2 V

theorem isSelfDualAt_of_isSelfDualC {D : D7} (V : HSp D) {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hΛ : IsSelfDualC V Λ) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    GlobalTheory.AdelicU.IsSelfDualAt D.sp.cm.sig V.gram Λ v := by
  refine (GlobalTheory.AdelicU.SelfDual.forall_isSelfDualAt_iff (hermND D V).2 (Formalism.IndefR.Fin.PDA.selfDual_isFullLattice V Λ hΛ)).2 (fun y => ?_) v
  refine (hΛ.2 y).trans (forall₂_congr fun x _ => ?_)
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, hb⟩
  · rintro ⟨b, hb⟩
    exact ⟨b, hb⟩

theorem isSplitBasis_frCo {D : D7} {n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {β : GL (Fin n) (EAf D)}
    (hβ : Formalism.L2.DIV.IsFrame β Λ) {v : HeightOneSpectrum (𝓞 D.host.F)} (φ : SplitProj D v) :
    GlobalTheory.AdelicU.IsSplitBasis (GlobalTheory.SplitProjChart.emb φ) Λ (frCo φ β) := fun u => by
  rw [mem_splitLat_iff hβ φ, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  simp only [HeightOneSpectrum.mem_adicCompletionIntegers]

theorem grpCo_emb {D : D7} (V : HSp D) {v : HeightOneSpectrum (𝓞 D.host.F)} (φ : SplitProj D v)
    (B : GL (Fin V.rank) (Fv D.host.F v)) (x : GlobalTheory.FinZeta.Gv V v) :
    grpCo φ V B (GlobalTheory.AdelicU.emb D.sp.cm.sig V.gram v x) =
      GlobalTheory.AdelicU.splitEquivIn (GlobalTheory.AdelicU.isCMExt_host D) (hermND D V) (GlobalTheory.SplitProjChart.emb φ) B x := by
  rw [GlobalTheory.AdelicU.splitEquivIn_apply, ← GlobalTheory.SplitChartLink.rdA_matHom_embV]
  rfl

section Reindex

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem reindex_mem_KO {m ι : Type} [Fintype m] [DecidableEq m] [Fintype ι] [DecidableEq ι] (ε : ι ≃ m)
    {x : GL m K} (hx : x ∈ GlobalTheory.SplitWeil.KO K m) (y : GL ι K) (h : ∀ i j, y.1 i j = x.1 (ε i) (ε j)) :
    y ∈ GlobalTheory.SplitWeil.KO K ι := by
  obtain ⟨a, rfl⟩ := hx
  refine ⟨Units.map (Matrix.reindexAlgEquiv (ValuativeRel.valuation K).integer (ValuativeRel.valuation K).integer ε.symm).toMonoidHom a, ?_⟩
  ext i j
  rw [h]
  simp [Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply]

theorem mem_KO_iff_reindex {m ι : Type} [Fintype m] [DecidableEq m] [Fintype ι] [DecidableEq ι] (ε : ι ≃ m)
    (x : GL m K) (y : GL ι K) (h : ∀ i j, y.1 i j = x.1 (ε i) (ε j)) :
    x ∈ GlobalTheory.SplitWeil.KO K m ↔ y ∈ GlobalTheory.SplitWeil.KO K ι :=
  ⟨fun hx => reindex_mem_KO ε hx y h,
    fun hy => reindex_mem_KO ε.symm hy x fun i j => by rw [h]; simp⟩

end Reindex

theorem chart_stab : ∀ (D : D7) (s : PiLocalization₂ D) (k : ℕ) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v) (ι : GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) →* GA D s.V), IsSelfDualC s.V s.Λ → Formalism.L2.DIV.IsFrame s.β s.Λ → IsChart s k φ ι → ∀ e : GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) → GlobalTheory.FinZeta.Gv s.V v, (∀ y, ι y = GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v (e y)) → ∀ y, e y ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram s.Λ v ↔ y ∈ GlobalTheory.SplitWeil.KO (Fv D.host.F v) _ := by
  intro D s k v φ ι hsd hfr hch e he y
  obtain ⟨ε, -, hε⟩ := hch
  have hB := isSplitBasis_frCo hfr φ
  have hL := isSelfDualAt_of_isSelfDualC s.V hsd v
  rw [GlobalTheory.AdelicU.mem_stabLoc_iff_GLint (GlobalTheory.AdelicU.isCMExt_host D) (hermND D s.V) hL hB,
    (GlobalTheory.AdelicU.GLint_eq_KO_and_princ_eq_KOne v _).1]
  have h2 := (hε y).2
  rw [he y, grpCo_emb] at h2
  exact mem_KO_iff_reindex ε _ y fun i j => by rw [← h2]; rfl

end GlobalTheory.ChartStab
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt

noncomputable section

namespace GlobalTheory.TwistChart

variable {D : D7}

theorem isIdemOf_idem {v : HeightOneSpectrum (𝓞 D.host.F)} (φ : SplitProj D v) :
    IsIdemOf φ (GlobalTheory.EmbChart.idem (GlobalTheory.SplitProjChart.emb φ)) := by
  refine ⟨GlobalTheory.EmbChart.isSplitIdem_idem _, ?_, GlobalTheory.SplitProjChart.rdA_idem φ⟩
  rw [GlobalTheory.EmbChart.cA_idem, GlobalTheory.EmbChart.idem, ← LinearMap.map_add (f := _), add_sub_cancel]
  rfl

theorem exists_unif (v : HeightOneSpectrum (𝓞 D.host.F)) :
    ∃ ϖ : (Fv D.host.F v)ˣ, ValuativeRel.valuation (Fv D.host.F v) (ϖ : Fv D.host.F v) =
      ValuativeRel.uniformizer (Fv D.host.F v) := by
  obtain ⟨x, hx⟩ := ValuativeRel.valuation_surjective (ValuativeRel.uniformizer (Fv D.host.F v))
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx
    exact ValuativeRel.uniformizer_ne_zero hx.symm
  exact ⟨Units.mk0 x hx0, hx⟩

theorem unit_section {v : HeightOneSpectrum (𝓞 D.host.F)} (φ : SplitProj D v) {e : AE D} (he : IsIdemOf φ e) :
    ∃ U : (Fv D.host.F v)ˣ →* (AE D)ˣ, (∀ y, (1 - e) * (U y : AE D) = 1 - e ∧ rdA φ (U y : AE D) = y) ∧
      ∀ (x : AE D) (y : (Fv D.host.F v)ˣ), (1 - e) * x = 1 - e → rdA φ x = y → x = U y := by
  have hπ := (GlobalTheory.SplitProjChart.chart_rdA D v φ e he).1
  have hee : e * e = e := he.1.1
  obtain ⟨sec, hsec⟩ : ∃ sec : Fv D.host.F v → AE D, ∀ y, rdA φ (sec y) = y :=
    ⟨fun y => (hπ.1 y).choose, fun y => (hπ.1 y).choose_spec⟩
  have hf1 : ∀ y, (1 - e) * ((1 - e) + e * sec y) = 1 - e := fun y => by
    linear_combination (1 - sec y) * hee
  have hf2 : ∀ y, rdA φ ((1 - e) + e * sec y) = y := fun y => by
    rw [map_add (f := _), map_sub, map_mul, map_one, he.2.2, hsec]; ring
  have key : ∀ x y, (1 - e) * x = 1 - e → rdA φ x = y → x = (1 - e) + e * sec y := by
    intro x y h1 h2
    have h3 : e * (x - sec y) = 0 := (hπ.2.1 _).1 (by rw [map_sub, h2, hsec, sub_self])
    have h4 : e * x = e * sec y := by rw [mul_sub] at h3; exact sub_eq_zero.1 h3
    calc x = (1 - e) * x + e * x := by ring
      _ = (1 - e) + e * sec y := by rw [h1, h4]
  have hmul : ∀ y z, (1 - e) + e * sec (y * z) = ((1 - e) + e * sec y) * ((1 - e) + e * sec z) := fun y z =>
    (key _ _ (by rw [← mul_assoc, hf1, hf1]) (by rw [map_mul, hf2, hf2])).symm
  have hone : (1 - e) + e * sec 1 = 1 := (key 1 1 (mul_one _) (map_one _)).symm
  let f : (Fv D.host.F v)ˣ → (AE D)ˣ := fun y =>
    ⟨(1 - e) + e * sec y, (1 - e) + e * sec ((y⁻¹ : (Fv D.host.F v)ˣ) : Fv D.host.F v),
      by rw [← hmul, Units.mul_inv, hone], by rw [← hmul, Units.inv_mul, hone]⟩
  exact ⟨MonoidHom.mk' f fun y z => Units.ext (by simp only [f, Units.val_mul]; exact hmul y z),
    fun y => ⟨hf1 y, hf2 y⟩, fun x y h1 h2 => key x y h1 h2⟩

end GlobalTheory.TwistChart

namespace GlobalTheory.TwistChart

variable {D : D7}

def blockEquiv (n r k t : ℕ) (h : n = r + k * t) : Fin r ⊕ Blocks k t ≃ Fin n :=
  (Equiv.sumCongr (Equiv.refl _) ((Equiv.sigmaEquivProd _ _).trans finProdFinEquiv)).trans
    (finSumFinEquiv.trans (finCongr h.symm))

theorem blockEquiv_inl (n r k t : ℕ) (h : n = r + k * t) (i : Fin r) : ((blockEquiv n r k t h (.inl i) : Fin n) : ℕ) = i := by
  simp [blockEquiv]

theorem exists_isChart (s : PiLocalization₂ D) (k : ℕ) (hrank : s.V.rank = D.R.r + k * D.R.t) {v : HeightOneSpectrum (𝓞 D.host.F)}
    (φ : SplitProj D v) {e : AE D} (he : IsIdemOf φ e) : ∃ ι, IsChart s k φ ι := by
  have hπ := (GlobalTheory.SplitProjChart.chart_rdA D v φ e he).1
  have hJ := GlobalTheory.NoExcl.isHermND_gram s.V
  let ε := blockEquiv s.V.rank D.R.r k D.R.t hrank
  let re : GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) ≃* GL (Fin s.V.rank) (Fv D.host.F v) :=
    Units.mapEquiv (Matrix.reindexAlgEquiv (Fv D.host.F v) (Fv D.host.F v) ε).toRingEquiv.toMulEquiv
  let L := GlobalTheory.AdelicU.splitEquivIn (GlobalTheory.AdelicU.isCMExt_host D) hJ (GlobalTheory.AdelicU.chartEmb hπ) (frCo φ s.β)
  let ι : GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) →* GA D s.V :=
    (GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v).comp (L.symm.toMulEquiv.toMonoidHom.comp re.toMonoidHom)
  refine ⟨ι, ε, blockEquiv_inl _ _ _ _ hrank, fun y => ⟨?_, ?_⟩⟩
  · change GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v (ι y)) = ι y
    simp only [ι, MonoidHom.comp_apply, GlobalTheory.AdelicU.proj_emb_self]
  · have h1 : grpCo φ s.V (frCo φ s.β) (ι y) = GlobalTheory.SplitHecke.rho s.V (rdA φ) (frCo φ s.β) (ι y) := by
      refine Units.ext ?_
      rw [GlobalTheory.SplitHecke.rho_val]
      rfl
    rw [h1, GlobalTheory.AdelicU.rho_eq_splitEquivIn hπ s.V hJ]
    simp only [ι, L, MonoidHom.comp_apply, GlobalTheory.AdelicU.proj_emb_self]
    have h2 : L (L.symm (re y)) = re y := L.apply_symm_apply _
    change (L (L.symm (re y))).1.submatrix ε ε = y.1
    rw [h2]
    ext i j
    simp [re]

end GlobalTheory.TwistChart

namespace GlobalTheory.TwistChart

open GlobalTheory.ChainOnto GlobalTheory.ChainTw

theorem charts_at_twist : ∀ D : D7, ForStageQ D fun c w j s => ∀ PP ∈ w.Q, (∃ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP) ∧ ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP → (∃ e, IsIdemOf φ e) ∧ (∃ x ϖ, IsLocUnif φ x ϖ) ∧ (∃ ι, IsChart s j φ ι) ∧ ∀ χ : (AE D)ˣ →* Circle, ∃ μ : (Fv D.host.F v)ˣ →* ℂˣ, GlobalTheory.SmGL.IsUnitaryChar μ ∧ (∀ (x : (AE D)ˣ) (y : (Fv D.host.F v)ˣ), (∃ e, IsIdemOf φ e ∧ (1 - e) * (x : AE D) = 1 - e ∧ rdA φ (x : AE D) = y) → μ y = Circle.toUnits (χ x)) := by
  intro D c w hw j _ s hs PP hPP
  classical
  have hPg : PP ∈ c.Pg := by rw [hw.union]; exact Finset.mem_union_right _ hPP
  obtain ⟨-, ⟨es, hes, -⟩, -⟩ := hw.com.split
  refine ⟨?_, fun v φ _ => ?_⟩
  · obtain ⟨v, φ, -, h⟩ := (GlobalTheory.SplitIdemDict.idem_dictionary D).1 _ _ (hes PP hPg)
    exact ⟨v, φ, h⟩
  have he := isIdemOf_idem φ
  obtain ⟨U, hU1, hU2⟩ := unit_section φ he
  have huniq := (GlobalTheory.SplitProjChart.chart_rdA D v φ _ he).2.2.2.2
  obtain ⟨hr, -, hst⟩ := hs
  refine ⟨⟨_, he⟩, ?_, exists_isChart s j hst.rank φ he, fun χ => ?_⟩
  · obtain ⟨ϖ, hϖ⟩ := exists_unif (D := D) v
    exact ⟨U ϖ, ϖ, _, he, (hU1 ϖ).1, (hU1 ϖ).2, hϖ⟩
  · refine ⟨(Circle.toUnits.comp χ).comp U, fun y => ?_, fun x y ⟨e', he', h1, h2⟩ => ?_⟩
    · exact Circle.norm_coe _
    · obtain rfl := huniq e' he'
      have hx : x = U y := Units.ext (hU2 _ _ h1 h2)
      rw [hx]
      rfl

end GlobalTheory.TwistChart
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing

namespace GlobalTheory.FinPl.SuppTwoAsm


theorem ginf_le_grpOff {D : D7} (V : HSp D) (P : Pl D → Prop) : GinfC V ≤ grpOff V P := by
  intro a ha
  rw [GinfC, MonoidHom.mem_ker] at ha
  rw [grpOff, congGrp, MonoidHom.mem_ker]
  have h1 := Units.ext_iff.mp ha
  simp only [finHom, Formalism.UG.bc, MonoidHom.comp_apply, Units.coe_map, Units.val_one] at h1
  apply Units.ext
  ext i j
  have h2 := congrFun (congrFun h1 i) j
  simp only [MonoidHom.coe_coe, RingHom.mapMatrix_apply, Matrix.map_apply, RingHom.toMonoidHom_eq_coe] at h2
  simp only [MonoidHom.comp_apply, Matrix.GeneralLinearGroup.map, Units.coe_map, Units.val_one, MonoidHom.coe_coe,
    RingHom.mapMatrix_apply, Matrix.map_apply, RingHom.toMonoidHom_eq_coe]
  have hf : (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom = finPart D := rfl
  rw [hf] at h2
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq] at h2 ⊢
    rw [← map_one (Ideal.Quotient.mk (idOff D P)), Ideal.Quotient.eq, idOff, Ideal.mem_iInf]
    intro w
    have h3 : compAt D w.1 ((matHom V a).val i i) = compAt D w.1 1 := by
      rw [compAt, RingHom.comp_apply, RingHom.comp_apply, h2, RingHom.map_one]
      exact (RingHom.map_one _).symm
    rw [RingHom.mem_ker, RingHom.map_sub, h3, sub_self]
  · rw [Matrix.one_apply_ne hij] at h2 ⊢
    rw [Ideal.Quotient.eq_zero_iff_mem, idOff, Ideal.mem_iInf]
    intro w
    rw [RingHom.mem_ker, compAt, RingHom.comp_apply, h2, map_zero]

end GlobalTheory.FinPl.SuppTwoAsm
end
