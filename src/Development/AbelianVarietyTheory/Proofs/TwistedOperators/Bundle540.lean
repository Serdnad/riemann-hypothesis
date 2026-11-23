module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle271
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GoodIdempotentBadPlaces
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddCharEqMulShiftUnitOfIsFieldStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle342
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle324
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteUnfSupportOfNeOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle354
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1968
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1545
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle512
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle476
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle491
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle459
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle520
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle307
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaFunctionThetaTransformRationalDarboux
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle372
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle391
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle437
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle523
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle362
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle526
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
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle281
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle287

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

theorem GlobalTheory.SeeConjChar.conjCharacter_eq_prod_symmetricEdge_characters : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → ∀ β : GL (Fin (Yc D 0).rank) (EAf D), IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → (∀ PP ∈ R.Pg, RedIs β PP (flagAt X h PP)) → ∃ (ψ' : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) (a : ∀ PP : Pl D.host.E, Fin D.R.r → Fin D.R.r → (kP PP)ˣ), IsGenericPsi R.Pg ψ' ∧ ∀ κ : GA D (Yc D 0), finE (Yc D 0) κ ∈ St β → ((iotaX X h).toMulEquiv κ).2 ∈ X.K2 → star (X.chi2 ((iotaX X h).toMulEquiv κ).2) = ∏ PP ∈ R.Pg, ψ' PP (∑ i, ∑ j, if symEdge D.R.rS D.R.k i j then (a PP i j : kP PP) * ((upperLeftBlock (r_le_Y (D := D) 0) (redFn β PP (finE (Yc D 0) κ)) : GL (Fin D.R.r) (kP PP)).val i j) else 0) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h hIs hGrp β hβ hred
  classical
  obtain ⟨ψ, hψ, hdec⟩ := GlobalTheory.T.levelCharacter_on_stabilizer_eq_prod_residue_characters_alt R F X h hIs hGrp
  have hc : ∀ PP ∈ R.Pg, ∃ c : (kP PP)ˣ, ∀ t, ψ (GlobalTheory.IdemSupport.cP PP) (GlobalTheory.SeeConjChar.conjRes PP t) = ψ PP ((c : kP PP) * t) := by
    intro PP hP
    refine GlobalTheory.T.exists_unit_addChar_eq_mulShift_of_isField ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 PP.isMaximal) (ψ PP)
      ((ψ (GlobalTheory.IdemSupport.cP PP)).compAddMonoidHom (GlobalTheory.SeeConjChar.conjRes PP).toAddMonoidHom) (hψ PP hP).1 ?_
    intro h1
    apply (hψ PP hP).2
    ext t
    obtain ⟨s, rfl⟩ := (GlobalTheory.SeeConjChar.conjRes PP).surjective t
    have := congrArg (fun χ : AddChar (kP PP) ℂ => χ s) h1
    simpa using this
  choose! c hc using hc
  refine ⟨fun PP => (ψ PP).mulShift (-1), fun PP i j =>
    if (i.1 < D.R.rS ∨ (i.1 + 1 < D.R.rS + D.R.k ∧ GlobalTheory.SeeConjChar.sideAt X h PP = true)) then 1
    else if i.1 = D.R.rS + D.R.k then c PP else -c PP, ?_, ?_⟩
  · intro PP hP h1
    apply (hψ PP hP).1
    ext t
    have := congrArg (fun χ : AddChar (kP PP) ℂ => χ (-t)) h1
    simpa [AddChar.mulShift_apply] using this
  · intro κ hS hK2
    have hK : ((iotaX X h).toMulEquiv κ).2 ∈ X.B.I.Kset := (Formalism.L2.SG.Closed.level_subgroup_properties X).2.1 _ hK2
    rw [hdec κ hK, ← starRingEnd_apply, map_prod]
    refine Finset.prod_congr rfl fun PP hP => ?_
    rw [GlobalTheory.T.residue_levelCharacterArgument_at_typePlace R F X h hIs hGrp β hβ hred PP hP κ hS, GlobalTheory.T.residue_conjugatePlace_characterArgument_signedSum R F X h hIs hGrp β hβ hred PP hP κ hS hK2, hc PP hP,
      map_mul, ← AddChar.map_neg_eq_conj, ← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul, AddChar.mulShift_apply]
    congr 1
    rw [Finset.mul_sum, ← neg_add, ← Finset.sum_add_distrib, neg_one_mul]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with hE
    · unfold GlobalTheory.SeeConjChar.wA GlobalTheory.SeeConjChar.wB
      simp only [apply_ite (fun u : (kP PP)ˣ => (u : kP PP)), Units.val_one, Units.val_neg]
      split_ifs <;> first | (exfalso; tauto) | (push_cast; ring1) | omega | (simp_all <;> omega)
    · simp
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

noncomputable section
namespace GlobalTheory.TopLevelInv.FlatStep
open GlobalTheory.FunObj.FiniteSupport

section Helpers
variable {k : Type} [Field k]

theorem reindex_mul_frameGL {a c b : ℕ} {ι : Type} {a' : ℕ} (h : a + c = b) (f : ι ≃ Fin a') (g : GL (Fin b) k)
    (D : Matrix ι (Fin a ⊕ Fin c) k) :
    D.reindex f (frame h) * g.val = (D * (frameGL h g).val).reindex f (frame h) := by
  ext r s
  simp only [reindex_apply, Matrix.mul_apply, submatrix_apply, frameGL_val]
  exact Fintype.sum_equiv (frame h).symm _ _ fun p => by simp

theorem frameGL_embX_congr {a c c' b : ℕ} (hc : c = c') (h : a + c = b) (h' : a + c' = b) {g : GL (Fin b) k}
    {κ : GL (Fin a) k} (H : frameGL h g = embX c κ) : frameGL h' g = embX c' κ := by
  subst hc; exact H

theorem eq_one_of_mem_symN_zero {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} {v : GL (n ⊕ Fin c) k}
    (hv : v ∈ symN k n c) (hc : c = 0) : v = 1 := by
  subst hc
  have key : ∀ p, N k n 0 p = ⊥ := fun p => by
    rw [N, Subgroup.closure_eq_bot_iff]
    intro g hg
    rw [Set.mem_singleton_iff]
    refine Units.ext (Matrix.ext fun r s => ?_)
    rcases r with r | r
    · rcases s with s | s
      · exact hg _ _ le_rfl
      · exact s.elim0
    · exact r.elim0
  rw [symN, key, key, sup_bot_eq, Subgroup.mem_bot] at hv
  exact hv

abbrev StepFam (Γ : Grid k) [MeasurableSpace k] : Type :=
  ∀ i : Fin (Γ.m - 1), (StepVar (Fin (topRank Γ (i + 1))) (Γ.m - 2 - i) (Fin (topRank Γ i)) → k) ≃ᵐ
    (StepVar (Fin (topRank Γ (i + 1))) (Γ.m - 2 - i) (Fin (topRank Γ i)) → k)

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]

theorem measurePreserving_stepFam {Γ : Grid k} (ν : Measure k) [ν.IsAddHaarMeasure] (φ : StepFam Γ)
    (hφ : ∀ i, MeasurePreserving (φ i) (stepVol ν _ _ _) (stepVol ν _ _ _)) :
    MeasurePreserving (MeasurableEquiv.piCongrRight φ) (varsVol Γ ν) (varsVol Γ ν) := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have : ∀ i : Fin (Γ.m - 1), SigmaFinite (stepVol ν (Fin (topRank Γ (i + 1))) (Γ.m - 2 - i) (Fin (topRank Γ i))) :=
    fun i => by unfold stepVol; infer_instance
  rw [varsVol_eq]
  exact measurePreserving_pi _ _ hφ

theorem measurePreserving_update {Γ : Grid k} (ν : Measure k) (Ψ : StepFam Γ)
    (hΨ : ∀ i, MeasurePreserving (Ψ i) (stepVol ν _ _ _) (stepVol ν _ _ _)) (i₀ : Fin (Γ.m - 1))
    (φ : (StepVar (Fin (topRank Γ (i₀ + 1))) (Γ.m - 2 - i₀) (Fin (topRank Γ i₀)) → k) ≃ᵐ
      (StepVar (Fin (topRank Γ (i₀ + 1))) (Γ.m - 2 - i₀) (Fin (topRank Γ i₀)) → k))
    (hφ : MeasurePreserving φ (stepVol ν _ _ _) (stepVol ν _ _ _)) :
    ∀ i, MeasurePreserving ((Function.update Ψ i₀ φ : StepFam Γ) i) (stepVol ν _ _ _) (stepVol ν _ _ _) := by
  intro i
  rcases eq_or_ne i i₀ with rfl | h
  · rw [Function.update_self]; exact hφ
  · rw [Function.update_of_ne h]; exact hΨ i

theorem flatTensor_comp_of_equiv {Γ : Grid k} (hs : 1 ≤ Γ.s) (ψ : AddChar k Circle) (ν : Measure k) (F : Γ.Args → ℂ)
    (A : Γ.Args → Γ.Args) (x x' : ColArgs Γ) (y : RowArgs Γ) (Φ : Vars Γ ≃ᵐ Vars Γ)
    (hΦ : MeasurePreserving Φ (varsVol Γ ν) (varsVol Γ ν))
    (hfill : ∀ e, A (fill hs x y e) = fill hs x' y (Φ e)) (hph : ∀ e, phase x e = phase x' (Φ e)) :
    flatTensor hs ψ ν (fun z => F (A z)) x y = flatTensor hs ψ ν F x' y := by
  rw [flatTensor, flatTensor, ← hΦ.integral_comp' (flatIntegrand hs ψ F x' y)]
  congr 1
  funext e
  simp only [flatIntegrand, hfill e, hph e]

theorem downMap_congr {Γ : Grid k} (hs : 1 ≤ Γ.s) {x x' : ColArgs Γ} {e e' : Vars Γ} {l : ℕ} (hx : x' l = x l)
    (he : ∀ h : l < Γ.m - 1, e' ⟨l, h⟩ = e ⟨l, h⟩) : downMap hs x' e' l = downMap hs x e l := by
  unfold downMap
  split_ifs with h1
  · rw [hx, he h1]
  · rw [hx]
  · rfl

end Helpers

theorem flatTensor_moveArgs_mulSingle : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {Γ : Grid k} (hs : 1 ≤ Γ.s) (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure] (F : Γ.Args → ℂ)
    (j : ℕ) (hj : j + 1 < Γ.m) (g : GL (Fin (Γ.rank (Γ.m, j + 1))) k) (κ : GL (Fin (topRank Γ (j + 1))) k),
    valuation k (gdet κ : k) = 1 → ∀ v ∈ symN k (Fin (topRank Γ (j + 1))) (Γ.m - 1 - (j + 1)), toFrame hs hj g = v * embX _ κ →
    ∀ (x : ColArgs Γ) (y : RowArgs Γ),
      flatTensor hs ψ ν (fun z => F (Γ.moveArgs .one (Pi.mulSingle (Γ.m, j + 1) g) z)) x y = flatTensor hs ψ ν F (colMove j κ x) y := by
  intro k _ _ _ _ _ _ Γ hs ψ ν _ F j hj g κ hdet v hv hg x y
  have hcol : ∀ i, i ≠ j → i ≠ j + 1 → colMove j κ x i = x i := fun i h1 h2 => by
    simp only [colMove, Function.update_of_ne h1, Function.update_of_ne h2]
  have hcj : colMove j κ x j = (κ⁻¹).val * x j := by
    simp only [colMove, Function.update_of_ne (show j ≠ j + 1 by omega), Function.update_self]
  have hcj1 : colMove j κ x (j + 1) = x (j + 1) * κ.val := by
    simp only [colMove, Function.update_self]
  rcases Nat.lt_or_ge (j + 2) Γ.m with hA | hB
  · obtain ⟨φ₀, hφ₀, φ₁, hφ₁, H⟩ := GlobalTheory.T.lastRowVertex_adjacentSteps_translate_frames (a₀ := topRank Γ j) (a₂ := topRank Γ (j + 1 + 1))
      (c := Γ.m - 2 - (j + 1)) (c₀ := Γ.m - 2 - j) ν (by omega) (by omega)
      (by have := topRank_add hs (j + 1); omega) (by have := topRank_add hs (j + 1); omega) _ g κ hdet v hv hg
      (x j) (x (j + 1))
    have h01 : (⟨j, by omega⟩ : Fin (Γ.m - 1)) ≠ ⟨j + 1, by omega⟩ := fun h => by simp at h
    let Ψ0 : StepFam Γ := fun i => MeasurableEquiv.refl _
    let Ψ1 : StepFam Γ := Function.update Ψ0 ⟨j, by omega⟩ φ₀
    let Ψ2 : StepFam Γ := Function.update Ψ1 ⟨j + 1, by omega⟩ φ₁
    let Φ : Vars Γ ≃ᵐ Vars Γ := MeasurableEquiv.piCongrRight Ψ2
    have hΦ0 : ∀ e, Φ e ⟨j, by omega⟩ = φ₀ (e ⟨j, by omega⟩) := fun e => by
      show Function.update Ψ1 ⟨j + 1, by omega⟩ φ₁ ⟨j, by omega⟩ (e ⟨j, by omega⟩) = _
      rw [Function.update_of_ne h01]
      show Function.update Ψ0 ⟨j, by omega⟩ φ₀ ⟨j, by omega⟩ (e ⟨j, by omega⟩) = _
      rw [Function.update_self]
    have hΦ1 : ∀ e, Φ e ⟨j + 1, by omega⟩ = φ₁ (e ⟨j + 1, by omega⟩) := fun e => by
      show Function.update Ψ1 ⟨j + 1, by omega⟩ φ₁ ⟨j + 1, by omega⟩ (e ⟨j + 1, by omega⟩) = _
      rw [Function.update_self]
    have hΦo : ∀ e (i : Fin (Γ.m - 1)), i.val ≠ j → i.val ≠ j + 1 → Φ e i = e i := fun e i h1 h2 => by
      show Function.update Ψ1 ⟨j + 1, by omega⟩ φ₁ i (e i) = _
      rw [Function.update_of_ne (fun h => h2 (by rw [h]))]
      show Function.update Ψ0 ⟨j, by omega⟩ φ₀ i (e i) = _
      rw [Function.update_of_ne (fun h => h1 (by rw [h]))]
      rfl
    have hMP : MeasurePreserving Φ (varsVol Γ ν) (varsVol Γ ν) :=
      measurePreserving_stepFam ν Ψ2 (measurePreserving_update ν Ψ1
        (measurePreserving_update ν Ψ0 (fun i => MeasurePreserving.id _) ⟨j, by omega⟩ φ₀ hφ₀) ⟨j + 1, by omega⟩ φ₁ hφ₁)
    refine flatTensor_comp_of_equiv hs ψ ν F _ x (colMove j κ x) y Φ hMP (fun e => ?_) (fun e => ?_)
    · refine GlobalTheory.T.unfoldingFilledArgs_moveInnerLastColumnVertex hs j hj g x (colMove j κ x) y e (Φ e) (fun l h1 h2 => ?_) ?_ ?_
      · exact downMap_congr hs (hcol l h1 h2) fun h => hΦo e ⟨l, h⟩ h1 h2
      · rw [downMap, dite_eq_left (show j < Γ.m - 1 by omega), downMap, dite_eq_left (show j < Γ.m - 1 by omega), hcj, hΦ0]
        exact ((H (e ⟨j, by omega⟩) (e ⟨j + 1, by omega⟩)).1 _).symm
      · rw [downMap, dite_eq_left (show j + 1 < Γ.m - 1 by omega), downMap, dite_eq_left (show j + 1 < Γ.m - 1 by omega),
          hcj1, hΦ1]
        exact ((H (e ⟨j, by omega⟩) (e ⟨j + 1, by omega⟩)).2.1 _).symm
    · have hrow : ∀ (x : ColArgs Γ) (e : Vars Γ) r, rowVar x e (j + 1) r = ∑ l : Fin (Γ.m - 2 - (j + 1)),
          if l.val = (Γ.m - 2 - (j + 1)) / 2 then stepPt (x (j + 1)) (e ⟨j + 1, by omega⟩) (.inr l) (.inl r) else 0 :=
        fun x e r => by rw [rowVar, dite_eq_left (by omega)]
      refine GlobalTheory.T.fourierJacobiPhase_adjacentInnerSteps_invariant j hA x (colMove j κ x) e (Φ e) hcol (fun i h1 h2 => hΦo e i h1 h2) ?_ ?_ ?_
      · simp only [hrow, colVar]
        rw [hcj, hcj1, hΦ0, hΦ1]
        exact (H (e ⟨j, by omega⟩) (e ⟨j + 1, by omega⟩)).2.2.1
      · intro ho s
        rw [rowVar, rowVar, dite_eq_left (by omega), dite_eq_left (by omega)]
        refine Finset.sum_congr rfl fun l _ => ?_
        split_ifs with hl
        · rw [hcj, hΦ0]
          exact (H (e ⟨j, by omega⟩) (e ⟨j + 1, by omega⟩)).2.2.2.1 ho l s hl
        · rfl
      · intro ho r
        simp only [colVar]
        rw [hcj1, hΦ1]
        exact (H (e ⟨j, by omega⟩) (e ⟨j + 1, by omega⟩)).2.2.2.2 ho r _ rfl
  · have hB' : j + 2 = Γ.m := by omega
    obtain rfl : v = 1 := eq_one_of_mem_symN_zero hv (by omega)
    have hg' : toFrame hs hj g = embX _ κ := by rw [hg, one_mul]
    obtain ⟨φ₀, hφ₀, H⟩ := GlobalTheory.T.fourierJacobiStep_leftChange_measurePreserving (n := Fin (topRank Γ (j + 1))) (n' := Fin (topRank Γ j)) (c := Γ.m - 2 - j)
      ν 1 (one_mem _) κ hdet (x j)
    let Ψ0 : StepFam Γ := fun i => MeasurableEquiv.refl _
    let Ψ1 : StepFam Γ := Function.update Ψ0 ⟨j, by omega⟩ φ₀
    let Φ : Vars Γ ≃ᵐ Vars Γ := MeasurableEquiv.piCongrRight Ψ1
    have hΦ0 : ∀ e, Φ e ⟨j, by omega⟩ = φ₀ (e ⟨j, by omega⟩) := fun e => by
      show Function.update Ψ0 ⟨j, by omega⟩ φ₀ ⟨j, by omega⟩ (e ⟨j, by omega⟩) = _
      rw [Function.update_self]
    have hΦo : ∀ e (i : Fin (Γ.m - 1)), i.val ≠ j → Φ e i = e i := fun e i h1 => by
      show Function.update Ψ0 ⟨j, by omega⟩ φ₀ i (e i) = _
      rw [Function.update_of_ne (fun h => h1 (by rw [h]))]
      rfl
    have hMP : MeasurePreserving Φ (varsVol Γ ν) (varsVol Γ ν) :=
      measurePreserving_stepFam ν Ψ1 (measurePreserving_update ν Ψ0 (fun i => MeasurePreserving.id _) ⟨j, by omega⟩ φ₀ hφ₀)
    have hf : frameGL (show topRank Γ (j + 1) + (Γ.m - 2 - j) = Γ.rank (Γ.m, j + 1) by
        have := topRank_add hs (j + 1); omega) g = embX (Γ.m - 2 - j) κ :=
      frameGL_embX_congr (by omega) _ _ hg'
    refine flatTensor_comp_of_equiv hs ψ ν F _ x (colMove j κ x) y Φ hMP (fun e => ?_) (fun e => ?_)
    · refine GlobalTheory.T.unfoldingFilledArgs_moveInnerLastColumnVertex hs j hj g x (colMove j κ x) y e (Φ e) (fun l h1 h2 => ?_) ?_ ?_
      · exact downMap_congr hs (hcol l h1 h2) fun h => hΦo e ⟨l, h⟩ h1
      · rw [downMap, dite_eq_left (show j < Γ.m - 1 by omega), downMap, dite_eq_left (show j < Γ.m - 1 by omega), hcj, hΦ0,
          ← H, one_mul, mul_reindex, map_inv, hf]
      · exact GlobalTheory.T.downwardVertexMap_lastVertex_mul_of_frame hs j hj hB' g κ hg' x (colMove j κ x) e (Φ e) hcj1
    · refine GlobalTheory.T.fourierJacobiPhase_lastInnerVertex_invariant j hB' κ x (colMove j κ x) e (Φ e) hcol hcj1 (fun i h1 => hΦo e i h1) ?_
      rw [hcj, hΦ0, ← H, one_mul]

end GlobalTheory.TopLevelInv.FlatStep
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

noncomputable section

namespace GlobalTheory.SquareAgree.SchDeriv

theorem exists_mem_algF_deriv : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → Bs.ψ = ψ →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws, M.IsGood Bs.ψ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      ∀ (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d)) (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (Fin S.rank × Fin d → v.adicCompletion D.host.F) → ℂ),
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
        ∀ f ∈ algF ψ θ ε A B, IsDatum M ψ cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ) f →
        ∀ u : Matrix (Fin S.rank) (Fin d) (AE D), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) u →
        ∀ g₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d),
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (M.heisLine Bs.ψ u) g g₁ →
        ∃ f₁ ∈ algF ψ θ ε A B, IsDatum M ψ cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g₁ φ) f₁ := by
  intro D ψ θ hθ ε S X A B d e Bs hBs hψB Vs Ws r s r' s' hJ hJW hV hW hemb M hM cS hcS g φ hφ hvac f hf hD u hu g₁ hg₁
  subst hψB
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd Bs.ψ := hBs.std
  have hψ : IsStdChar D Bs.ψ (-1) := GlobalTheory.StdCharFromIsStd.isStdChar_of_isStd D Bs.ψ hstd
  have hth : ∀ Φ ∈ algF Bs.ψ θ ε A B, IsThetaFunO Bs.ψ (sgn ε S) X Φ := by
    intro Φ hΦ
    induction hΦ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, P, hf, rfl⟩ := hx
      exact GlobalTheory.GalLift.Vec.theta_pureTensorO hψ hθ _ _ _ _ hf.1 P
    | zero => exact GlobalTheory.OrientedHeis.theta_zero
    | add x y _ _ hx hy => exact GlobalTheory.OrientedHeis.theta_add hx hy
    | smul c x _ hx => exact GlobalTheory.OrientedHeis.theta_smul c hx
  have hsm : ∀ (a : AF D.host.F) (v : Matrix (Fin S.rank) (Fin d) (AE D)), cS (a • v) = a • cS v := by
    intro a v
    rw [hcS, hcS]
    ext i j
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.smul_apply, Finset.smul_sum,
      smul_mul_assoc, id]
  have hAt : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (cS u) := by
    intro a ha
    rw [← hsm, hu a ha, map_zero]
  refine ⟨∑ τ, dRho (heisO Bs.ψ (sgn ε S) X) θ τ (compAt θ τ (cS u)) f,
    Submodule.sum_mem _ fun τ _ => GlobalTheory.T.heisenberg_derivative_mem_fockAlgebraicThetaVectors D Bs.ψ θ hψ hθ ε S X A B f hf τ _, ?_, fun u' => ?_⟩
  · exact GlobalTheory.TensUniq.pure_mem_schA g₁ φ hφ ((hvac.and hM.std).mono fun v hv => hv.1.trans hv.2)
  · have h2 := GlobalTheory.T.hasDerivAt_thetaSum_archimedeanHeisenbergLine M Bs.ψ hstd hM u hu g g₁ φ hφ hvac hg₁ u'
    have h3 := GlobalTheory.T.hasDerivAt_heisenbergOp_archimedean_sum_realPlaces D Bs.ψ θ hψ hθ (sgn ε S) X f (hth f hf) (cS u) hAt (cS u')
    have heq : (fun t : ℝ => GlobalTheory.WeilM.thetaSum D.host.F (M.co.rho Bs.ψ u' (M.heisLine Bs.ψ u t (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ)))) =
        fun t : ℝ => heisO Bs.ψ (sgn ε S) X (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • cS u) f (cS u') := by
      funext t
      have h4 := (GlobalTheory.T.schrodingerThetaDatum_heisenberg_oriented D Bs.ψ θ hθ ε S X A B e Bs hBs rfl Vs Ws r s r' s' hJ hJW hV hW hemb M hM cS hcS
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ) f hD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u)).2 u'
      rw [hsm] at h4
      exact h4
    rw [heq] at h2
    rw [h2.unique h3, Finset.sum_apply]

end GlobalTheory.SquareAgree.SchDeriv

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

noncomputable section

namespace GlobalTheory.GaussThetaFinite

theorem isDatum_smul {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd)
    (ψ : AddChar (AF F) ℂ) {Z : Type} (crd : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → Z)
    (Φ : (Fin n × Fin d → AF F) → ℂ) (f : Z → ℂ) (c : ℂ) (h : IsDatum M ψ crd Φ f) :
    IsDatum M ψ crd (c • Φ) (c • f) := by
  refine ⟨Submodule.smul_mem _ c h.1, fun u => ?_⟩
  have h2 := h.2 u
  simp only [Pi.smul_apply, smul_eq_mul, ← h2, GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr] at *
  rw [← tsum_mul_left]
  congr 1; ext ξ; ring

theorem eq_zero_of_isDatum_zero {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd)
    (ψ : AddChar (AF F) ℂ) {Z : Type} [AddCommGroup Z] (crd : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ≃+ Z)
    (f : Z → ℂ) (h : IsDatum M ψ crd 0 f) : f = 0 := by
  funext w
  have h2 := h.2 (crd.symm w)
  rw [AddEquiv.apply_symm_apply] at h2
  rw [← h2]
  simp [GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr]

theorem fockVac_of_isGauss : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → Bs.ψ = ψ →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws, M.IsGood Bs.ψ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      ∀ (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d)) (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (Fin S.rank × Fin d → v.adicCompletion D.host.F) → ℂ), M.IsGauss Bs.ψ Bs.emb g →
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
        ∀ f : WO S X → ℂ, IsDatum M ψ cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ) f →
        ∀ τ : D.what₂.Tau, IsFockVacAt (heisO ψ (sgn ε S) X) θ τ (cplxO ((frSgn ε A).cart τ) (B.cart τ)) f := by
  intro D ψ θ hθ ε S X A B d e Bs hBs hψ Vs Ws r s r' s' hJ hJW hV hW hemb M hM cS hcS g φ hg hφ hvac f hf τ
  unfold IsFockVacAt
  intro z
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd Bs.ψ := hBs.std
  obtain ⟨g₁, h₁⟩ := GlobalTheory.T.exists_heisenberg_derivative_archimedean_direction M Bs.ψ hstd g _ (GlobalTheory.T.archimedean_preimage_realPlace_line D θ hθ ε S X e cS hcS τ z)
  obtain ⟨g₁', h₁'⟩ := GlobalTheory.T.exists_heisenberg_derivative_archimedean_direction M Bs.ψ hstd g _ (GlobalTheory.T.archimedean_preimage_realPlace_line D θ hθ ε S X e cS hcS τ (cplxO ((frSgn ε A).cart τ) (B.cart τ) z))
  have d1 := GlobalTheory.T.heisenbergDerivative_realPlace_pureDatum D ψ θ hθ ε S X A B e Bs hBs hψ Vs Ws r s r' s' hJ hJW hV hW hemb M hM cS hcS g φ hφ hvac f hf τ z g₁ h₁
  have d2 := GlobalTheory.T.heisenbergDerivative_realPlace_pureDatum D ψ θ hθ ε S X A B e Bs hBs hψ Vs Ws r s r' s' hJ hJW hV hW hemb M hM cS hcS g φ hφ hvac f hf τ _ g₁' h₁'
  have h0 := GlobalTheory.T.gaussianVacuum_heisenbergDerivative_complexStructure_cancel D ψ θ hθ ε S X A B e Bs hBs hψ Vs Ws r s r' s' hJ hJW hV hW hemb M hM cS hcS g φ hg hφ hvac τ z g₁ g₁' h₁ h₁'
  have hsum := GlobalTheory.SquareAgree.isDatum_add M ψ (hψ ▸ hstd) cS _ _ _ _ d1 (isDatum_smul M ψ cS _ _ Complex.I d2)
  have hpure : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g₁ φ + Complex.I • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g₁' φ = 0 := by
    funext x
    have := congrArg (fun h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d) => h (fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F (x i))) h0
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this ⊢
    simp only [SchwartzMap.add_apply, SchwartzMap.smul_apply, SchwartzMap.zero_apply, smul_eq_mul] at this
    linear_combination (∏ᶠ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F)), φ v fun i ↦ (GlobalTheory.AdelicU.evFin D.host.F v) (x i)) * this
  rw [hpure] at hsum
  have := eq_zero_of_isDatum_zero M ψ cS _ hsum
  simpa [annih] using this

theorem isFinF_of_isGauss : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → Bs.ψ = ψ →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws, M.IsGood Bs.ψ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      ∀ (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d)) (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (Fin S.rank × Fin d → v.adicCompletion D.host.F) → ℂ), M.IsGauss Bs.ψ Bs.emb g →
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
        ∃ f : WO S X → ℂ, IsFinF ψ θ ε A B f ∧ IsDatum M ψ cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ) f := by
  intro D ψ θ hθ ε S X A B d e Bs hBs hψ Vs Ws r s r' s' hJ hJW hV hW hemb M hM cS hcS g φ hg hφ hvac
  have hsch : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin S.rank × Fin d) :=
    GlobalTheory.TensUniq.pure_mem_schA g φ hφ ((hvac.and hM.std).mono fun v hv => hv.1.trans hv.2)
  obtain ⟨ξ, JB, co, hξ, hrat, hiff⟩ := GlobalTheory.T.exists_rational_darboux_orientedPair_transport D ψ θ hθ ε S X A B e Bs hBs hψ Vs Ws r s r' s' hJ hJW hV hW hemb M hM cS hcS
  have hstd : IsStdChar D ψ (-1) := GlobalTheory.StdCharFromIsStd.isStdChar_of_isStd D ψ (hψ ▸ hBs.std)
  have hD : IsDatum M ψ cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ) (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ)) :=
    (hiff _ _).2 ⟨hsch, rfl⟩
  refine ⟨GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ), ⟨?_, fockVac_of_isGauss D ψ θ hθ ε S X A B e Bs hBs hψ Vs Ws r s r' s' hJ hJW hV hW hemb M hM cS hcS g φ hg hφ hvac _ hD⟩, hD⟩
  exact GlobalTheory.ThetaTransformTheta.isThetaFunO_thetaTr D ψ hstd (sgn ε S) X _ JB ξ rfl hξ _ co hrat _ hsch

end GlobalTheory.GaussThetaFinite

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.avgOverMaximalCompact_weighted_supNorm_bound : ∀ {D : D7} (θ : InfFam D), IsInfFam θ → ∀ (N : GlobalTheory.Grid.Node D) (τ : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), Continuous e → ∀ a : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : GA D N.V → ℂ) (B : ℝ), (∀ g, ‖f g‖ * GlobalTheory.Grow.quotHeight N.V g ^ a ≤ B) → ∀ g, ‖GlobalTheory.KFinCuspApprox.avgN θ N τ e f g‖ * GlobalTheory.Grow.quotHeight N.V g ^ a ≤ C * B := by
  first | exact @GlobalTheory.KFinCuspApprox.avgN_weighted_bound | exact GlobalTheory.KFinCuspApprox.avgN_weighted_bound | (intros; apply GlobalTheory.KFinCuspApprox.avgN_weighted_bound <;> assumption)
end
