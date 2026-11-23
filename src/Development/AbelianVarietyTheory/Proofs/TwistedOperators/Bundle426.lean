module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle337
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle324
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle345
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle373
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle051
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle350
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle390
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle392
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergOrbitCoefficientSmooth
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle378
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralMulRightOfCompact
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle293
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle005
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedBessel
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle396
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle287
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

noncomputable section
namespace GlobalTheory.StepLeft
open Classical

theorem affine {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
    (g : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (x₀ : Matrix n n' k) (e : StepVar n c n' → k) :
    (fun a : StepVar n c n' => (g * stepPt x₀ e) a.1.1 a.1.2) =
      (stepLin n' g).mulVec e + fun a => (g * stepPt x₀ (0 : StepVar n c n' → k) : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) a.1.1 a.1.2 := by
  funext a
  obtain ⟨⟨r, s⟩, ha⟩ := a
  have h1 : (stepLin n' g).mulVec e ⟨(r, s), ha⟩ =
      ∑ t, g r t * (if h : (Free (c / 2 + 1) (t, s) ∨ Kept (t, s)) then e ⟨(t, s), h⟩ else 0) := by
    have h2 : (stepLin n' g).mulVec e ⟨(r, s), ha⟩ = ∑ b : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)),
        (if s = b.2 then g r b.1 else 0) * (if h : (Free (c / 2 + 1) b ∨ Kept b) then e ⟨b, h⟩ else 0) := by
      rw [← Fintype.sum_subtype_add_sum_subtype (fun b => Free (c / 2 + 1) b ∨ Kept b)]
      rw [Finset.sum_eq_zero (s := Finset.univ) (f := fun b : {b // ¬ (Free (c / 2 + 1) b ∨ Kept b)} => _)
        (fun b _ => by rw [dite_eq_right b.2, mul_zero]), add_zero]
      simp only [Matrix.mulVec, dotProduct, stepLin, of_apply]
      refine Finset.sum_congr rfl fun b _ => by rw [dite_eq_left b.2]
    rw [h2, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_eq_single s]
    · simp
    · intro s' _ hs
      simp [Ne.symm hs]
    · simp
  simp only [Pi.add_apply]
  rw [h1]
  simp only [stepPt, Matrix.mul_apply, Matrix.add_apply, of_apply, mul_add, Finset.sum_add_distrib, Pi.zero_apply,
    dite_eq_ite, ite_self, mul_zero, Finset.sum_const_zero, add_zero]
  ring

theorem det_unip {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
    (u : GL (n ⊕ Fin c) k) (hu : u ∈ symN k n c) : (stepLin n' u.val).det = 1 := by
  apply GlobalTheory.RootExSource.det_eq_one_of_unip (fun a : StepVar n c n' => GlobalTheory.DiagVol.ordL c a.1.1)
  intro a b hab
  have hu' : u.val a.1.1 b.1.1 = (1 : Matrix _ _ k) a.1.1 b.1.1 := GlobalTheory.DiagVol.symN_le_unipSub hu a.1.1 b.1.1 hab
  simp only [stepLin, of_apply]
  by_cases hab' : a = b
  · subst hab'; simp [hu']
  · rw [Matrix.one_apply_ne hab']
    split_ifs with h
    · rw [hu', Matrix.one_apply_ne]
      intro hr
      exact hab' (Subtype.ext (Prod.ext hr h))
    · rfl

theorem var_inl_iff {n n' : Type} {c : ℕ} (r t : n) (s : n' ⊕ Fin (c + 1)) :
    (Free (c / 2 + 1) ((Sum.inl r : n ⊕ Fin c), s) ∨ Kept ((Sum.inl r : n ⊕ Fin c), s)) ↔
      (Free (c / 2 + 1) ((Sum.inl t : n ⊕ Fin c), s) ∨ Kept ((Sum.inl t : n ⊕ Fin c), s)) := by
  rcases s with s | s <;> simp [Free, Kept]

theorem embX_apply_eq_zero {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] {c : ℕ} (κ : GL n k)
    (r t : n ⊕ Fin c) (s : n' ⊕ Fin (c + 1)) (hr : Free (c / 2 + 1) (r, s) ∨ Kept (r, s))
    (ht : ¬ (Free (c / 2 + 1) (t, s) ∨ Kept (t, s))) : (embX c κ).val r t = 0 := by
  change (fromBlocks κ.val 0 0 1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r t = 0
  rcases r with r | r <;> rcases t with t | t
  · exact absurd ((var_inl_iff r t s).1 hr) ht
  · rfl
  · rfl
  · simp only [fromBlocks_apply₂₂]
    rw [Matrix.one_apply_ne]
    rintro rfl
    exact ht hr

theorem mul_embX {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
    (κ : GL n k) (g : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) :
    stepLin n' ((embX c κ).val * g) = stepLin n' (embX c κ).val * stepLin n' g := by
  ext a b
  obtain ⟨⟨r, s⟩, ha⟩ := a
  obtain ⟨⟨r', s'⟩, hb⟩ := b
  set E := (embX c κ).val
  set F : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) → k := fun d =>
    (if s = d.2 then E r d.1 else 0) * (if d.2 = s' then g d.1 r' else 0) with hF
  have hF0 : ∀ d : {d : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // ¬ (Free (c / 2 + 1) d ∨ Kept d)}, F d.1 = 0 := by
    rintro ⟨⟨t, s''⟩, hd⟩
    by_cases h1 : s = s''
    · subst h1
      have hz : E r t = 0 := embX_apply_eq_zero κ r t s ha hd
      simp [hF, hz]
    · simp [hF, h1]
  have hR : (stepLin n' E * stepLin n' g) ⟨(r, s), ha⟩ ⟨(r', s'), hb⟩ = ∑ d, F d := by
    rw [← Fintype.sum_subtype_add_sum_subtype (fun d => Free (c / 2 + 1) d ∨ Kept d),
      Finset.sum_eq_zero (s := Finset.univ) (fun d _ => hF0 d), add_zero]
    simp only [Matrix.mul_apply, stepLin, of_apply, hF]
  rw [hR, Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_eq_single s]
  · simp only [stepLin, of_apply, hF, Matrix.mul_apply]
    split_ifs with h
    · simp
    · simp [h]
  · intro s'' _ hs
    refine Finset.sum_eq_zero fun t _ => ?_
    simp [hF, Ne.symm hs]
  · simp

theorem mp_affine {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι k) (hM : valuation k M.det = 1) (b : ι → k) :
    MeasurePreserving (fun e => M.mulVec e + b) (Measure.pi fun _ : ι => ν) (Measure.pi fun _ : ι => ν) := by
  haveI := GlobalTheory.SplitWeil.secondCountable k
  have hU : IsUnit M.det := isUnit_iff_ne_zero.2 fun h => by rw [h, map_zero] at hM; exact zero_ne_one hM
  have h1 := GlobalTheory.WeilM.smul_map_mulVec_pi ν M hU.unit hU.unit_spec
  have h2 : distribHaarChar k hU.unit = 1 := by
    have := nabs_of_valuation_eq_one (k := k) (x := hU.unit) (by rw [hU.unit_spec]; exact hM)
    exact NNReal.coe_eq_one.1 this
  rw [h2, ENNReal.coe_one, one_smul] at h1
  have hm : Measurable M.mulVec := (continuous_const.matrix_mulVec continuous_id).measurable
  exact (measurePreserving_add_right (Measure.pi fun _ : ι => ν) b).comp ⟨hm, h1⟩

end GlobalTheory.StepLeft

namespace GlobalTheory.StepLeft
open Classical

theorem left_change : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ} (ν : Measure k) [ν.IsAddHaarMeasure],
    ∀ v ∈ symN k n c, ∀ κ : GL n k, valuation k (gdet κ : k) = 1 → ∀ x₀ : Matrix n n' k,
      ∃ φ : (StepVar n c n' → k) ≃ᵐ (StepVar n c n' → k), MeasurePreserving φ (stepVol ν n c n') (stepVol ν n c n') ∧
        ∀ e, ((v * embX c κ)⁻¹).val * stepPt x₀ e = stepPt ((κ⁻¹).val * x₀) (φ e) := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c ν _ v hv κ hκ x₀
  haveI := GlobalTheory.SplitWeil.secondCountable k
  set g := ((v * embX c κ)⁻¹).val with hgdef
  set M := stepLin n' g with hMdef
  set b : StepVar n c n' → k := fun a =>
    (g * stepPt x₀ (0 : StepVar n c n' → k) : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) a.1.1 a.1.2 with hb
  have hg : g = (embX c κ⁻¹).val * (v⁻¹).val := by
    rw [hgdef, _root_.mul_inv_rev, map_inv, Units.val_mul]
  have hκ' : valuation k (gdet κ⁻¹ : k) = 1 := by
    rw [gdet, map_inv, Units.val_inv_eq_inv_val, map_inv₀]
    exact (congrArg (·⁻¹) hκ).trans inv_one
  have hdet : valuation k M.det = 1 := by
    rw [hMdef, hg, mul_embX, det_mul, map_mul, det_unip _ (inv_mem hv), map_one, mul_one]
    exact GlobalTheory.T.valuation_det_stageVariables_embedGL_eq_one (n' := n') (c := c) κ⁻¹ hκ'
  have hM0 : IsUnit M.det := isUnit_iff_ne_zero.2 fun h => by rw [h, map_zero] at hdet; exact zero_ne_one hdet
  have hcont : ∀ (A : Matrix (StepVar n c n') (StepVar n c n') k) (w : StepVar n c n' → k),
      Continuous fun e : StepVar n c n' → k => A.mulVec e + w := fun A w =>
    (continuous_const.matrix_mulVec continuous_id).add continuous_const
  let φ : (StepVar n c n' → k) ≃ᵐ (StepVar n c n' → k) :=
    { toFun := fun e => M.mulVec e + b
      invFun := fun e => M⁻¹.mulVec e + M⁻¹.mulVec (-b)
      left_inv := fun e => by
        simp only [mulVec_add, mulVec_mulVec, nonsing_inv_mul _ hM0, one_mulVec, mulVec_neg, add_neg_cancel_right]
      right_inv := fun e => by
        simp only [mulVec_add, mulVec_mulVec, mul_nonsing_inv _ hM0, one_mulVec, mulVec_neg, neg_add_cancel_right]
      measurable_toFun := (hcont M b).measurable
      measurable_invFun := (hcont M⁻¹ _).measurable }
  refine ⟨φ, mp_affine ν M hdet b, fun e => ?_⟩
  change g * stepPt x₀ e = stepPt ((κ⁻¹).val * x₀) (M.mulVec e + b)
  rw [hMdef, hb, ← affine]
  exact GlobalTheory.T.periodStep_inv_mul_point_shape v hv κ x₀ e

end GlobalTheory.StepLeft

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical
open GlobalTheory.HeisOrbit

theorem _root_.GlobalTheory.T.contDiff_heisenbergArchimedeanDiffOperator_family : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (G : ℝ → SInf F κ) (P Q : ℝ → (κ → mixedEmbedding.mixedSpace F)),
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (κ → mixedEmbedding.mixedSpace F) => G p.1 p.2) →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) P → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Q →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (κ → mixedEmbedding.mixedSpace F) => GlobalTheory.HeisOrbit.dOp (P p.1) (Q p.1) (G p.1) p.2) := by
  first | exact @GlobalTheory.HeisOrbit.dOp_contDiff_family | exact GlobalTheory.HeisOrbit.dOp_contDiff_family | (intros; apply GlobalTheory.HeisOrbit.dOp_contDiff_family <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical
open GlobalTheory.HeisOrbit

theorem _root_.GlobalTheory.T.heisenbergArchimedeanDiffOperator_hasDerivAt_family : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (G : ℝ → SInf F κ) (P Q : ℝ → (κ → mixedEmbedding.mixedSpace F))
    (g' : SInf F κ) (P' Q' : κ → mixedEmbedding.mixedSpace F),
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (κ → mixedEmbedding.mixedSpace F) => G p.1 p.2) →
    (∀ y, HasDerivAt (fun t => G t y) (g' y) 0) → HasDerivAt P P' 0 → HasDerivAt Q Q' 0 → ∀ y,
    HasDerivAt (fun t => GlobalTheory.HeisOrbit.dOp (P t) (Q t) (G t) y) (GlobalTheory.HeisOrbit.dOp (P 0) (Q 0) g' y + GlobalTheory.HeisOrbit.dOp P' Q' (G 0) y) 0 := by
  first | exact @GlobalTheory.HeisOrbit.DOpDeriv.dOp_hasDerivAt | exact GlobalTheory.HeisOrbit.DOpDeriv.dOp_hasDerivAt | (intros; apply GlobalTheory.HeisOrbit.DOpDeriv.dOp_hasDerivAt <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical
open GlobalTheory.HeisOrbit

theorem _root_.GlobalTheory.T.weil_operator_right_intertwines_heisenberg_derivative : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    IsStd ψ → M.IsWeil ψ χX χW om → ∀ (h : UA σ W.J) (Th : SInf F (Fin n × Fin d) → SInf F (Fin n × Fin d)),
    (∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (1, h)) f (Th f)) → ∀ u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) u →
    ∀ f f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine ψ u) f f₁ → ∀ y,
      Th f₁ y = GlobalTheory.HeisOrbit.dOp (GlobalTheory.HeisOrbit.archCo M.co (u * (mat h)ᵀ)).1 (GlobalTheory.HeisOrbit.archCo M.co (u * (mat h)ᵀ)).2 (Th f) y := by
  first | exact @GlobalTheory.HeisOrbit.weil_heisDeriv_intertw | exact GlobalTheory.HeisOrbit.weil_heisDeriv_intertw | (intros; apply GlobalTheory.HeisOrbit.weil_heisDeriv_intertw <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical
open GlobalTheory.HeisOrbit

theorem _root_.GlobalTheory.T.heisenberg_orbit_coefficient_smooth : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W), ∀ γ ∈ Lines σ W, ∀ u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) u →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => GlobalTheory.HeisOrbit.archCo M.co (u * (mat (γ (Multiplicative.ofAdd t)))ᵀ)) ∧
    ∃ u' : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) u' ∧
      HasDerivAt (fun t : ℝ => GlobalTheory.HeisOrbit.archCo M.co (u * (mat (γ (Multiplicative.ofAdd t)))ᵀ)) (GlobalTheory.HeisOrbit.archCo M.co u') 0 := by
  first | exact @GlobalTheory.HeisOrbitSmooth.archCo_orbit_smooth | exact GlobalTheory.HeisOrbitSmooth.archCo_orbit_smooth | (intros; apply GlobalTheory.HeisOrbitSmooth.archCo_orbit_smooth <;> assumption)
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.TrIdem

noncomputable section
namespace GlobalTheory.TrIdem

theorem conv_normInd_self (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (H : Subgroup G)
    (hHo : IsOpen (H : Set G)) (hHc : IsCompact (H : Set G)) :
    conv μ (normInd μ (H : Set G)) (normInd μ (H : Set G)) = normInd μ (H : Set G) := by
  have hm : MeasurableSet (H : Set G) := hHo.measurableSet
  have hpos : μ (H : Set G) ≠ 0 := (hHo.measure_pos μ ⟨1, H.one_mem⟩).ne'
  have hfin : μ (H : Set G) ≠ ⊤ := hHc.measure_lt_top.ne
  have hr : (μ.real (H : Set G) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero, measureReal_def]
    exact (ENNReal.toReal_pos hpos hfin).ne'
  funext y
  simp only [conv, normInd]
  set c : ℂ := (μ.real (H : Set G) : ℂ)⁻¹ with hc
  by_cases hy : y ∈ H
  · have key : (fun x => (c • (H : Set G).indicator (1 : G → ℂ)) x * (c • (H : Set G).indicator (1 : G → ℂ)) (x⁻¹ * y))
        = (H : Set G).indicator (fun _ => c * c) := by
      funext x
      by_cases hx : x ∈ H
      · have : x⁻¹ * y ∈ H := H.mul_mem (H.inv_mem hx) hy
        simp [Set.indicator_of_mem (show x ∈ (H : Set G) from hx),
          Set.indicator_of_mem (show x⁻¹ * y ∈ (H : Set G) from this)]
      · simp [Set.indicator_of_notMem (show x ∉ (H : Set G) from hx)]
    rw [key, integral_indicator_const _ hm]
    simp only [Pi.smul_apply, Set.indicator_of_mem (show y ∈ (H : Set G) from hy), Pi.one_apply, smul_eq_mul, mul_one]
    rw [Complex.real_smul, hc]
    field_simp
  · have key : (fun x => (c • (H : Set G).indicator (1 : G → ℂ)) x * (c • (H : Set G).indicator (1 : G → ℂ)) (x⁻¹ * y))
        = fun _ => 0 := by
      funext x
      by_cases hx : x ∈ H
      · have : x⁻¹ * y ∉ H := fun h => hy (by simpa using H.mul_mem hx h)
        simp [Set.indicator_of_notMem (show x⁻¹ * y ∉ (H : Set G) from this)]
      · simp [Set.indicator_of_notMem (show x ∉ (H : Set G) from hx)]
    rw [key, integral_zero]
    simp [Set.indicator_of_notMem (show y ∉ (H : Set G) from hy)]

end GlobalTheory.TrIdem
end
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.TrIdem

noncomputable section

namespace GlobalTheory.TrIdem

theorem smoothOp_normInd_of_fixed : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (H : Subgroup G), IsOpen (H : Set G) → IsCompact (H : Set G) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W), GlobalTheory.PRep.IsSmooth ρ → ∀ x : W, (∀ h ∈ H, ρ h x = x) → smoothOp ρ μ (normInd μ (H : Set G)) x = x := by
  intro G _ _ _ _ _ _ μ _ H ho hK W _ _ ρ hρ x hx
  have hf : IsLocallyConstant ((H : Set G).indicator (1 : G → ℂ)) := by
    refine (IsLocallyConstant.iff_exists_open _).2 fun g => ?_
    by_cases hg : g ∈ (H : Set G)
    · exact ⟨H, ho, hg, fun y hy => by simp [Set.indicator_of_mem hy, Set.indicator_of_mem hg]⟩
    · exact ⟨(H : Set G)ᶜ, (H.isClosed_of_isOpen ho).isOpen_compl, hg, fun y hy => by
        rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hg]⟩
  have hc : HasCompactSupport ((H : Set G).indicator (1 : G → ℂ)) :=
    HasCompactSupport.intro hK fun y hy => Set.indicator_of_notMem hy _
  have h0 : (μ.real H : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero, Ne, measureReal_eq_zero_iff hK.measure_lt_top.ne]
    exact (ho.measure_pos μ ⟨1, one_mem H⟩).ne'
  have hf' : IsLocallyConstant (normInd μ (H : Set G)) := by
    unfold normInd; exact hf.comp ((μ.real H : ℂ)⁻¹ • ·)
  have hc' : HasCompactSupport (normInd μ (H : Set G)) := by
    unfold normInd; exact hc.comp_left (g := ((μ.real H : ℂ)⁻¹ • ·)) (smul_zero _)
  refine eq_of_forall_dual fun l => ?_
  have h1 : (fun g => normInd μ (H : Set G) g • l (ρ g x)) =
      (H : Set G).indicator fun _ => (μ.real H : ℂ)⁻¹ * l x := by
    ext g
    by_cases hg : g ∈ (H : Set G)
    · have : ρ g x = x := hx g hg
      simp [normInd, Set.indicator_of_mem hg, this]
    · simp [normInd, Set.indicator_of_notMem hg]
  rw [hρ.map_smoothOp hf' hc', h1, integral_indicator_const _ ho.measurableSet]
  rw [Complex.real_smul, ← mul_assoc, mul_inv_cancel₀ h0, one_mul]

end GlobalTheory.TrIdem
end
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.TrIdem

noncomputable section

namespace GlobalTheory.TrIdem

variable {D : D7} {V : HSp D}

theorem levelFam_open_compact (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    IsOpen (levelFam T U v : Set (GLoc D.sp.cm.sig V.gram v)) ∧
      IsCompact (levelFam T U v : Set (GLoc D.sp.cm.sig V.gram v)) := by
  by_cases hu : v = U.u
  · subst hu
    rw [levelFam_u]
    exact ⟨U.frame.isOpen_iwahori, U.frame.isCompact_iwahori⟩
  by_cases hv : v ∈ T.S
  · have e : levelFam T U v = kerSub T ⟨v, hv⟩ := by
      rw [levelFam, Function.update_of_ne hu, dite_eq_left hv]
    rw [e]
    have ho : IsOpen (kerSub T ⟨v, hv⟩ : Set (GLoc D.sp.cm.sig V.gram v)) := by
      rw [kerSub, Subgroup.coe_map]
      exact (isOpen_stabLoc D.sp.cm.sig V.gram (frameLat V) v).isOpenMap_subtype_val _
        (T.frame ⟨v, hv⟩).isOpen_ker_red
    refine ⟨ho, (isCompact_stabLoc D.sp.cm.sig V.gram (frameLat V) v).of_isClosed_subset
      (Subgroup.isClosed_of_isOpen _ ho) ?_⟩
    rintro _ ⟨k, -, rfl⟩
    exact k.2
  · rw [levelFam_of_notMem T U hv hu]
    exact ⟨isOpen_stabLoc D.sp.cm.sig V.gram (frameLat V) v, isCompact_stabLoc D.sp.cm.sig V.gram (frameLat V) v⟩

theorem isFinFamily_fam : ∀ (D : D7) (V : HSp D) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V)
    (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)), (∀ v, (μf v).IsHaarMeasure) →
    (∀ᶠ v in cofinite, μf v (Kv V v) = 1) → U.u ∉ T.S → ∀ A,
    IsFinFamily D.sp.cm.sig V.gram (frameLat V) (fam T U μf A) := by
  intro D V T U μf _ h1 _ A
  refine ⟨fun v => ?_, ?_⟩
  · by_cases hv : v ∈ T.S ∧ v ∈ A
    · rw [fam_of_mem T U μf A hv.1 hv.2]
      exact (T.frame ⟨v, hv.1⟩).idem_mem _ _
    · rw [fam_of_not T U μf A hv, normInd]
      obtain ⟨ho, hc⟩ := levelFam_open_compact T U v
      exact Submodule.smul_mem _ _ (indicator_mem_SB ho hc)
  · filter_upwards [T.S.eventually_cofinite_notMem, eventually_cofinite_ne U.u, h1] with v hS hU hK
    rw [fam_of_not T U μf A (fun h => hS h.1), levelFam_of_notMem T U hS hU, normInd, measureReal_def]
    funext g
    simp only [Pi.smul_apply, unitLoc]
    rw [hK]
    simp

end GlobalTheory.TrIdem
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isBesselFrame_of_besselDatum_realPlace : ∀ (D : D7) (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V), HSpace.IsIsomEmb A B ι → ∀ (d : BesDat A B ι) (τ : D.what₂.Tau),
  GlobalTheory.RealBessel.IsFrame (gramAt D B τ) (gramAt D A τ) ((frameMat B A ι).map (tauE D τ)) (d.e.map (tauE D τ)) (fun k => tauE D τ (d.z k)) := by
  first | exact @GlobalTheory.BesselFrameReal.isFrame_of_besDat | exact GlobalTheory.BesselFrameReal.isFrame_of_besDat | (intros; apply GlobalTheory.BesselFrameReal.isFrame_of_besDat <;> assumption)
end
