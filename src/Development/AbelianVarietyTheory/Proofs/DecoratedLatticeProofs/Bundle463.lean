module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle423
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle401
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle402
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsConjAdjointPullbackBijection
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle496
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle462
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle012
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle410
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle430
import Formalism.LocalToGlobal.HilbertRowConditions.IsHilbertCF

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatLine

open GlobalTheory.FinPl.FrameLat GlobalTheory.SeeSaw.IdVMul

variable {D : D7}

theorem mul_idV_int {𝔠 : FI D} {v : GlobalTheory.FinPl.Pl D} {a : AE D}
    (h : ∀ c ∈ 𝔠, incA D c * a ∈ intAt D (· = v)) {y : AE D} (hy : y ∈ idV 𝔠 v) : y * a ∈ intAt D (· = v) := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, h0, c, hc, rfl⟩ := hy
    have e := incA_mul_tmul (D := D) c (pairA D.host.F 0 α) 1
    rw [mul_one] at e
    rw [← e, mul_comm (incA D c), mul_assoc]
    exact intAt_mul (tmul_one_mem_intAt hα h0) (h c hc)
  | zero => rw [zero_mul]; exact intAt_zero
  | add x y _ _ hx hy => rw [add_mul]; exact intAt_add hx hy
  | neg x _ hx => rw [neg_mul]; exact intAt_neg hx

theorem mem_idV_inv {𝔠 : FI D} (h𝔠 : 𝔠 ≠ 0) {v : GlobalTheory.FinPl.Pl D} {a : AE D} (ha : a ∈ idAt D (· = v))
    (h : ∀ c ∈ 𝔠, incA D c * a ∈ intAt D (· = v)) : a ∈ idV 𝔠⁻¹ v := by
  obtain ⟨b, hb0, hb⟩ := GlobalTheory.IdVGen.idV_gen D v 𝔠⁻¹ (inv_ne_zero h𝔠)
  obtain ⟨c, hc0, hc⟩ := GlobalTheory.IdVGen.idV_gen D v 𝔠 h𝔠
  have hm := idV_mul_gen D v 𝔠⁻¹ 𝔠 b c hb0 hc0 hb hc (GlobalTheory.FinPlLoc.idem D (· = v))
  rw [inv_mul_cancel₀ h𝔠, GlobalTheory.SeeSaw.idV_one_eq_intAt] at hm
  obtain ⟨h1, h2⟩ := hm.1 (GlobalTheory.FinPlLoc.idem_mem_intAt _)
  have h3 : incA D b⁻¹ * GlobalTheory.FinPlLoc.idem D (· = v) ∈ idV 𝔠 v := by
    refine (hc _).2 ⟨?_, Ideal.mul_mem_left _ _ h2⟩
    rw [← mul_assoc, ← map_mul, ← mul_inv, mul_comm c b]
    exact h1
  have h4 := mul_idV_int h h3
  rw [mul_assoc, (GlobalTheory.FinPlLoc.mem_idAt_iff _ a).1 ha] at h4
  exact (hb a).2 ⟨h4, ha⟩

theorem pairing_smul_ratV (S : HSp D) (s x : Fin S.rank → D.host.E) (a : AE D) :
    pairing S s (a • ratV x) = incA D (∑ b, row S s b * x b) * a := by

  simp only [pairing, ratV, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun b _ => by ring

theorem incA_inj : Function.Injective (incA D) := GlobalTheory.MixModel.incA_injective

theorem smul_mem_latV {S : HSp D} {L : Lat S} {x : Fin S.rank → D.host.E} {𝔞 : FI D} (h : ∀ t ∈ 𝔞, t • x ∈ L)
    {v : GlobalTheory.FinPl.Pl D} {a : AE D} (ha : a ∈ idV 𝔞 v) : a • ratV x ∈ latV S L (· = v) := by
  induction ha using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, h0, t, ht, rfl⟩ := hy
    have e := incA_mul_tmul (D := D) t (pairA D.host.F 0 α) 1
    rw [mul_one] at e
    have := int_mul_mem (tmul_one_mem_intAt hα h0) (h t ht)
    convert this using 1
    funext i
    rw [← e]
    simp only [ratV, Pi.smul_apply, smul_eq_mul, map_mul]
    ring
  | zero => rw [zero_smul]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_smul]; exact add_mem hx hy
  | neg x _ hx => rw [neg_smul]; exact neg_mem hx

theorem line_trace : ∀ (D : D7) (S : HSp D) (L : Lat S) (x : Fin S.rank → D.host.E), IsSelfDualC S L → x ≠ 0 → ∃ 𝔞 : FI D, 𝔞 ≠ 0 ∧ (∀ t : D.host.E, t • x ∈ L ↔ t ∈ 𝔞) ∧ ∀ v : GlobalTheory.FinPl.Pl D, ∀ a ∈ idAt D (· = v), a • ratV x ∈ latV S L (· = v) ↔ a ∈ idV 𝔞 v := by
  intro D S L x hL hx
  obtain ⟨m, s, s', hs, hs', hexp⟩ := exists_expansion hL
  set c : Fin m → D.host.E := fun l => ∑ b, row S (s' l) b * x b with hc
  have hx' : ∀ i, x i = ∑ l, c l * s l i := by
    intro i
    apply incA_inj (D := D)
    have := hexp ((1 : AE D) • ratV x) i
    simp only [pairing_smul_ratV, mul_one] at this

    rw [map_sum]
    simpa only [one_smul, ratV, map_mul] using this
  set 𝔠 : FI D := FractionalIdeal.spanFinset (𝓞 D.host.E) Finset.univ c with h𝔠def
  have hmem : ∀ y, y ∈ 𝔠 ↔ y ∈ Submodule.span (𝓞 D.host.E) (Set.range c) := by
    intro y
    rw [← FractionalIdeal.mem_coe, h𝔠def, FractionalIdeal.spanFinset_coe, Finset.coe_univ, Set.image_univ]
  have h𝔠 : 𝔠 ≠ 0 := by
    intro h0
    apply hx
    funext i
    rw [hx' i]
    refine Finset.sum_eq_zero fun l _ => ?_
    have : c l ∈ 𝔠 := (hmem _).2 (Submodule.subset_span ⟨l, rfl⟩)
    rw [h0, FractionalIdeal.mem_zero_iff] at this
    rw [this, zero_mul]
  have hglob : ∀ t : D.host.E, t • x ∈ L ↔ t ∈ 𝔠⁻¹ := by
    intro t
    rw [FractionalIdeal.mem_inv_iff h𝔠]
    constructor
    · intro ht y hy
      rw [hmem] at hy
      rw [← FractionalIdeal.mem_coe]
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨l, rfl⟩ := hy
        obtain ⟨o, ho⟩ := (hL.2 _).1 ht (s' l) (hs' l)
        rw [FractionalIdeal.mem_coe, FractionalIdeal.mem_one_iff]
        refine ⟨o, ho.trans ?_⟩
        rw [Finset.sum_comm]
        simp only [hc, GlobalTheory.FinPl.FrameLat.row, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
      | zero => rw [mul_zero]; exact zero_mem _
      | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
      | smul o y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hy
    · intro ht
      have ho : ∀ l, ∃ o : 𝓞 D.host.E, algebraMap _ D.host.E o = t * c l := fun l =>
        (FractionalIdeal.mem_one_iff _).1 (ht _ ((hmem _).2 (Submodule.subset_span ⟨l, rfl⟩)))
      choose o ho using ho
      have : t • x = ∑ l, o l • s l := by
        funext i
        rw [Pi.smul_apply, smul_eq_mul, hx' i, Finset.mul_sum, Finset.sum_apply]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Pi.smul_apply, Algebra.smul_def, ho, mul_assoc]
      rw [this]
      exact Submodule.sum_mem _ fun l _ => L.smul_mem _ (hs l)
  refine ⟨𝔠⁻¹, inv_ne_zero h𝔠, hglob, fun v a ha => ⟨fun h => ?_, smul_mem_latV fun t ht => (hglob t).2 ht⟩⟩
  refine mem_idV_inv h𝔠 ha fun y hy => ?_
  rw [hmem] at hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, rfl⟩ := hy
    refine ⟨Ideal.mul_mem_left _ _ ha, ?_⟩
    have := pairing_int hL (hs' l) h
    rwa [pairing_smul_ratV] at this
  | zero => rw [map_zero, zero_mul]; exact intAt_zero
  | add y z _ _ hy hz => rw [map_add (f := _), add_mul]; exact intAt_add hy hz
  | smul o y hy' hy =>
    have h1 := GlobalTheory.IdVGen.gen_mem_intAt (v := v) (GlobalTheory.FinPlLoc.ePl_int (· = v))
      (fun w hw => by rw [GlobalTheory.FinPlLoc.evalV_ePl, if_neg hw]) o
    have e := incA_mul_tmul (D := D) (algebraMap (𝓞 D.host.E) D.host.E o) (pairA D.host.F 0 (GlobalTheory.FinPlLoc.ePl D (· = v))) 1
    rw [mul_one] at e
    have h2 := intAt_mul h1 hy
    rw [← e] at h2
    have h3 : GlobalTheory.FinPlLoc.idem D (· = v) * a = a := (GlobalTheory.FinPlLoc.mem_idAt_iff _ a).1 ha
    convert h2 using 1
    rw [Algebra.smul_def, map_mul]
    conv_lhs => rw [← h3]
    simp only [GlobalTheory.FinPlLoc.idem]
    ring

end GlobalTheory.Core.Mi.LatLine

end
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

open GlobalTheory.PairLift

noncomputable section

namespace GlobalTheory.KernelFlip

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

theorem annih_dag (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (L : AdjLaw ψ S T)
    {aS : Matrix (Fin S.rank) (Fin S.rank) ℂ} {bT : Matrix (Fin T.rank) (Fin T.rank) ℂ} (τ : D.what₂.Tau)
    (hS : IsCartanInv (gramAt D S τ) aS) (hT : IsCartanInv (gramAt D T τ) bT)
    (w : Matrix (Fin S.rank) (Fin T.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    annih (heisO ψ T S) θ τ (cplxO bT aS) w (dag S T f) =
      dag S T (annih (heisO ψ S T) θ τ (cplxO aS bT) (GlobalTheory.FockAdjoint.cdag S T τ w) f) := by
  unfold annih
  rw [GlobalTheory.FockAdjoint.dRho_dag hθ L, GlobalTheory.FockAdjoint.dRho_dag hθ L, GlobalTheory.FockAdjoint.cdag_cplx τ hS hT,
    GlobalTheory.FockAdjoint.dRho_neg' hψ hθ hf]
  funext x
  simp only [dag, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, map_add (f := _), map_mul, map_neg, Complex.conj_I]
  ring

theorem annih_theta (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (τ : D.what₂.Tau)
    (J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    IsThetaFunO ψ S T (annih (heisO ψ S T) θ τ J z f) :=
  GlobalTheory.OrientedHeis.theta_add (GlobalTheory.OrientedHeis.theta_dRho hθ hψ τ z hf)
    (GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.OrientedHeis.theta_dRho hθ hψ τ (J z) hf))

theorem foldr_theta (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (sS : RealMat S) (sT : RealMat T)
    (l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin S.rank) ℂ)) {g : WO S T → ℂ} (hg : IsThetaFunO ψ S T g) :
    IsThetaFunO ψ S T (l.foldr (fun p f => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 f) g) := by
  induction l with
  | nil => exact hg
  | cons p l ih => exact annih_theta hψ hθ _ _ _ ih

theorem foldr_dag (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (L : AdjLaw ψ S T) (sS : RealMat S) (sT : RealMat T)
    (hS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (hT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
    (l : List (D.what₂.Tau × Matrix (Fin S.rank) (Fin T.rank) ℂ)) {g : WO S T → ℂ} (hg : IsThetaFunO ψ S T g) :
    l.foldr (fun p f => annih (heisO ψ T S) θ p.1 (cplxO (sT p.1) (sS p.1)) p.2 f) (dag S T g) =
      dag S T ((l.map fun p => (p.1, GlobalTheory.FockAdjoint.cdag S T p.1 p.2)).foldr
        (fun p f => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 f) g) := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    simp only [List.foldr_cons, List.map_cons]
    rw [ih, annih_dag hψ hθ L p.1 (hS p.1) (hT p.1) _ (foldr_theta hψ hθ sS sT _ hg)]

theorem fock_dag (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (L : AdjLaw ψ S T) (sS : RealMat S) (sT : RealMat T)
    (hS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (hT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) {Φ : WO S T → ℂ}
    (h : IsFockVec ψ θ S T sS sT Φ) : IsFockVec ψ θ T S sT sS (dag S T Φ) := by
  obtain ⟨hth, N, hN⟩ := h
  refine ⟨L.theta Φ hth, N, fun l hl => ?_⟩
  rw [foldr_dag hψ hθ L sS sT hS hT l hth, hN _ (by simpa using hl)]
  funext x
  simp [dag]

theorem coef_dag (hST : AdjLaw ψ S T) (hTS : AdjLaw ψ T S) {X : Type} (x : X → WO T S → ℂ) (x' : X → WO S T → ℂ)
    (hx : ∀ p, x' p = dag T S (x p)) (Φ : WO T S → ℂ) (c : X → ℂ) (h : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsCoef T S x Φ c) :
    GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsCoef S T x' (dag T S Φ) fun p => starRingEnd ℂ (c p) := by
  obtain ⟨μ, 𝓕, ⟨hμ, h𝓕, h1⟩, hc⟩ := h
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.MixModel.lattice_Mx D S.rank T.rank
  obtain ⟨j1, j2, j3, j4, -⟩ := GlobalTheory.MixModel.lattice_Mx D T.rank S.rank
  have : BorelSpace (WO T S) := ⟨rfl⟩
  have : BorelSpace (WO S T) := ⟨rfl⟩
  let eA : WO T S ≃+ WO S T :=
    { toFun := adjO S T
      invFun := adjO T S
      left_inv := fun x => hTS.invol x
      right_inv := fun y => hST.invol y
      map_add' := hST.add }
  let eH : WO T S ≃ₜ WO S T := ⟨eA.toEquiv, hST.cont, hTS.cont⟩
  let eM : WO T S ≃ᵐ WO S T := eH.toMeasurableEquiv
  have hHaar : (μ.map eM).IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map μ eA hST.cont hTS.cont
  have hmp : MeasurePreserving eM μ (μ.map eM) := ⟨eM.measurable, rfl⟩
  have hmp' : MeasurePreserving eM.symm (μ.map eM) μ := MeasurePreserving.symm eM hmp
  let eG : ratL S T → ratL T S := fun g => ⟨adjO S T g, (hST.rat g).2 g.2⟩
  have hbij : Function.Bijective eG := by
    refine ⟨fun g g' hg => ?_, fun g => ⟨⟨adjO T S g, (hTS.rat g).2 g.2⟩, Subtype.ext (hST.invol g)⟩⟩
    have e := congrArg (fun x : ratL T S => adjO T S (x : WO S T)) hg
    simp only [eG, hTS.invol] at e
    exact Subtype.ext e
  have hF : IsAddFundamentalDomain (ratL T S) (eM.symm ⁻¹' 𝓕) (μ.map eM) := by
    refine h𝓕.preimage_of_equiv hmp'.quasiMeasurePreserving hbij fun g x => ?_
    show adjO T S (adjO S T g + x) = (g : WO T S) + adjO T S x
    rw [hTS.add, hTS.invol]
  have hpre : eM ⁻¹' (eM.symm ⁻¹' 𝓕) = 𝓕 := by
    ext a; simp
  refine ⟨μ.map eM, eM.symm ⁻¹' 𝓕, ⟨hHaar, hF, ?_⟩, fun p => ?_⟩
  · rw [MeasurableEquiv.map_apply, hpre, h1]
  · show starRingEnd ℂ (c p) = _
    rw [hc p, MeasurableEquiv.restrict_map, hpre, integral_map_equiv, ← integral_conj, hx p]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    have ew : eM.symm (eM w) = w := eM.symm_apply_apply w
    show starRingEnd ℂ (x p w * starRingEnd ℂ (Φ w)) =
      dag T S (x p) (eM w) * starRingEnd ℂ (dag T S Φ (eM w))
    simp only [dag]
    have e2 : adjO T S (eM w) = w := hTS.invol w
    rw [e2, map_mul]

end GlobalTheory.KernelFlip


open GlobalTheory.KernelFlip in
theorem GlobalTheory.KernelFlip.kernelPair_flip : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A) (sB : RealMat B) (K₁ K₂ : GA D A → GA D B → ℂ) (c : GA D A → ℂ), IsInfFam θ → (∀ τ, IsCartanInv (gramAt D A τ) (sA τ)) → (∀ τ, IsCartanInv (gramAt D B τ) (sB τ)) → GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsKernelPair ψ θ A B χA χB sA sB true (fun _ => True) (fun _ => True) K₁ K₂ c → GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsKernelPair ψ θ A B χA χB sA sB false (fun _ => True) (fun _ => True) K₁ K₂ c := by
  intro D ψ θ A B χA χB sA sB K₁ K₂ c hθ hsA hsB hK
  obtain ⟨om, Φ₁, Φ₂, H, hF₁, hF₂, -, -, hK₁, hK₂, hc⟩ := hK
  have hψ : IsStdChar D ψ (-1) := H.std
  have hBA : AdjLaw ψ B A := GlobalTheory.T.hermitianAdjoint_laws_standardCharacter D ψ hψ B A
  have hAB : AdjLaw ψ A B := GlobalTheory.T.hermitianAdjoint_laws_standardCharacter D ψ hψ A B
  obtain ⟨om', H', hom'⟩ := GlobalTheory.WeilConj.exists_conj_weilDatum D ψ B A χB χA om H
  have hθK : ∀ (g : GA D A) (h : GA D B) (Φ : WO B A → ℂ),
      starRingEnd ℂ (thetaKO om' g h (dag B A Φ)) = thetaKO om h g Φ := by
    intro g h Φ
    simp only [thetaKO]
    rw [hom' h g Φ]
    simp only [dag]
    rw [GlobalTheory.WeilConj.adjO_zero hBA, Complex.conj_conj]
  refine ⟨om', dag B A Φ₁, dag B A Φ₂, H', fock_dag hψ hθ hBA sB sA hsB hsA hF₁,
    fock_dag hψ hθ hBA sB sA hsB hsA hF₂, trivial, trivial, fun g h => ?_, fun g h => ?_, ?_⟩
  · rw [hθK, hK₁]
  · rw [hθK, hK₂]
  · exact coef_dag hAB hBA (fun g : GA D A => om (1, g) Φ₁) (fun g : GA D A => om' (g, 1) (dag B A Φ₁))
      (fun g => hom' 1 g Φ₁) Φ₂ c hc
end
end

section

noncomputable section

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

namespace GlobalTheory.MiTop

theorem oneBlock_lev {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : LevDat D.host.E ℂ V.rank)
    (hn : V.rank ≤ Λ.r) (hs : Λ.s = 0) (hQ : Λ.Q = ∅) (κ : GA D V) :
    (κ ∈ levS V β Λ ↔ κ ∈ GfC V ∧ Lev.finE V κ ∈ Formalism.L2.DIV.St (F := D.host.F) (E := D.host.E) β ∧
      Formalism.L2.DIV.rTup (F := D.host.F) (E := D.host.E) β Λ (Lev.finE V κ) ∈ Λ.P.H) ∧
    Lev.levChi V β Λ κ = ((Formalism.L2.DIV.ext1 Λ.P.H Λ.P.chi
      (Formalism.L2.DIV.rTup (F := D.host.F) (E := D.host.E) β Λ (Lev.finE V κ)) : ℂˣ) : ℂ) := by
  refine ⟨⟨fun h => ?_, fun h => ⟨h.1, ?_⟩⟩, ?_⟩
  · have hl := mem_lev.1 h.2
    exact ⟨h.1, (mem_parLev.1 hl.1).2.1, hl.2⟩
  · refine mem_lev.2 ⟨mem_parLev.2 ⟨GlobalTheory.LevSplit.finE_mem_UA _ κ, h.2.1,
      fun PP _ => GlobalTheory.SeeConjRead.blockTri_blkOf_top _ hn _, fun PP hPP => ?_⟩, h.2.2⟩
    rw [hQ] at hPP
    exact absurd hPP (Finset.notMem_empty _)
  · unfold Lev.levChi levFn
    simp only [hs, hQ, Finset.range_zero, Finset.prod_empty, Finset.prod_const_one, mul_one]


end GlobalTheory.MiTop

end
end
