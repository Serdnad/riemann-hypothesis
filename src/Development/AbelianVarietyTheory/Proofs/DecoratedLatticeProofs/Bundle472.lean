module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOneComb
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOpenKerUnramMulTame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle453
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle335
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle364
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle423
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle403
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle447
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle430
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MulVecSingleAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle455
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IkedaMapSchrodingerPartialIntegral
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.XiEqXiOffMul
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle456
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle088
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PiEqOfFinPart
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle145
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle457
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle381
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle459
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Formalism.LocalToGlobal.HilbertRowConditions.IsHilbertCF
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LastOmb

theorem isComp_inv {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {S : Dbl2 ψ σ} (Q : QStep S) :
    (ofSplit Q.q).IsComp S.χ₂ Q.μ₂⁻¹ := by
  intro t a ha
  have := Q.comp₂ t a ha
  rw [MonoidHom.inv_apply] at this
  rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, this, Circle.coe_inv, inv_inv]

theorem isLoc_one {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {S : Dbl2 ψ σ} (Q : QStep S) :
    (ofSplit Q.q).IsLoc Q.F.F₁ (1 : GA D S.J.W₀) (1 : GL Q.n₁ Q.k) := by
  refine ⟨?_, ?_⟩
  · intro i j
    simp [GlobalTheory.MixModel.mt_one]
  · rw [GlobalTheory.MixModel.mt_one, Units.val_one, Matrix.mul_one, Q.F.F₁.βγ, Matrix.map_one _ (map_zero _) (map_one _)]

theorem actO_one_of_away {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {S : Dbl2 ψ σ} (Q : QStep S) {g : GL Q.n₂ Q.k}
    {a₀ : GA D S.B'.A} (hloc : (ofSplit Q.q).IsLoc Q.F.F₂ a₀ g) (y : WO S.J.W₀ S.B'.A)
    (hy' : IsHalf (1 - (Q.q.e + cA D Q.q.e)) y) : actO S.J.W₀ S.B'.A 1 a₀ y = y := by
  have hsupp := GlobalTheory.LocGrp.suppAt_iff.1 hloc.1
  have he := Q.q.split
  set f : AE D := Q.q.e + cA D Q.q.e with hf
  have hce : cA D Q.q.e * cA D Q.q.e = cA D Q.q.e := by rw [← map_mul, he.1]
  have hff : f * (1 - f) = 0 := by
    rw [hf]; linear_combination (-1 : AE D) * he.1 - hce - 2 * he.2.1
  have hfy : f • y = 0 := by
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
    rw [← hy' i j, ← mul_assoc, hff, zero_mul]
  have hz : HMul.hMul (Formalism.L2.Theta.mt S.B'.A a₀ - 1) (show Matrix (Fin S.B'.A.rank) (Fin S.J.W₀.rank) (AE D) from y) = 0 := by
    rw [← hsupp, Matrix.smul_mul, ← Matrix.mul_smul]
    have h0 : ((ofSplit Q.q).e + cA D (ofSplit Q.q).e) • (show Matrix (Fin S.B'.A.rank) (Fin S.J.W₀.rank) (AE D) from y) = 0 := hfy
    rw [h0, Matrix.mul_zero]
  simp only [actO, inv_one, GlobalTheory.MixModel.mt_one, Matrix.mul_one]
  rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at hz
  exact hz

theorem biComb_eq_sum {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (c₁ : WO A S →₀ ℂ) (c₂ : WO S A' →₀ ℂ)
    (C : WO A S → WO S A' → ℂ) (u : WO A S) :
    biComb ψ A S A' c₁ c₂ C u =
      ∑ x ∈ c₁.support, (c₁ x * ψ (symplOH A S u x)) • GlobalTheory.SeeSaw.comb ψ S A' c₂ (C (u + x)) := by
  funext v
  simp only [biComb, GlobalTheory.SeeSaw.comb, heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

theorem weil_last_local : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ), Q.Away c₂ → ∀ (Λ : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k) →ₗ[ℂ] (WO S.B.A S.J.W₀ → WO S.J.W₀ S.B'.A → ℂ)), (ofSplit Q.q).IsBiModel ψ Q.F.F₀ Q.F.F₁ Q.F.F₂ Λ → ∀ (g : GL Q.n₂ Q.k) (a₀ : GA D S.B'.A), (ofSplit Q.q).IsLoc Q.F.F₂ a₀ g → ∀ (Ξ₁ : SB (Matrix Q.n₁ Q.n₀ Q.k)) (Ξ₂ Ξ₂' : SB (Matrix Q.n₂ Q.n₁ Q.k)), Ξ₂'.1 = om Q.μ₂ 1 g Ξ₂.1 → ∀ u, S.omb (1, a₀) (biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂)) u) = biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂')) u := by
  intro D ψ σ S Q c₁ c₂ hAway Λ hbi g a₀ hloc Ξ₁ Ξ₂ Ξ₂' hΞ u
  have hcomm : ∀ G, IsThetaFunO ψ S.J.W₀ S.B'.A G →
      S.omb (1, a₀) (GlobalTheory.SeeSaw.comb ψ S.J.W₀ S.B'.A c₂ G) = GlobalTheory.SeeSaw.comb ψ S.J.W₀ S.B'.A c₂ (S.omb (1, a₀) G) := by
    intro G hG

    simp only [GlobalTheory.SeeSaw.comb, map_sum, map_smul]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [S.weilb.om_heis 1 a₀ y G hG, actO_one_of_away Q hloc y (hAway y hy)]

  rw [biComb_eq_sum, biComb_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_smul]
  obtain ⟨T₂, hT₂, hΛ⟩ := hbi.2 Ξ₁ (u + x)
  have e1 : Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂) (u + x) = T₂ Ξ₂ :=
    funext fun v => hΛ Ξ₂ _ (fun q => GlobalTheory.LocFlat.CFac.prodSB_apply _ _ _) v
  have e2 : Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂') (u + x) = T₂ Ξ₂' :=
    funext fun v => hΛ Ξ₂' _ (fun q => GlobalTheory.LocFlat.CFac.prodSB_apply _ _ _) v
  have e3 : S.omb (1, a₀) (T₂ Ξ₂) = T₂ Ξ₂' := by
    refine GlobalTheory.LocOm.omLoc D Q.k (ofSplit Q.q) ψ S.J.W₀ S.B'.A S.χ₂ S.χ₂ S.omb S.weilb Q.μ₂⁻¹ Q.μ₂⁻¹ (isComp_inv Q)
      (isComp_inv Q) Q.n₂ Q.n₁ Q.F.F₁ Q.F.F₂ T₂ hT₂ 1 1 a₀ g (isLoc_one Q) hloc Ξ₂ Ξ₂' ?_
    rw [hΞ, inv_inv]
    simp
  rw [e1, e2, hcomm _ (hT₂.theta _), e3]

end GlobalTheory.LastOmb
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos SymDbl OneDbl comb)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.symmetricDoubleIntegrals_positionOne_eq_cellSum : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (n₀ n₁ n₂ : Type) [Fintype n₀] [DecidableEq n₀] [Fintype n₁] [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂] (c ρ : ℕ),
    c + 1 = 2 * ρ → ∀ (ψ : AddChar k Circle), Continuous ψ → HasConductor ψ 1 → ∀ (ν : Measure k), IsUnitVol ν →
  ∀ (μ₁ μ₂ : kˣ →* ℂˣ), IsOpen (μ₁.ker : Set kˣ) → IsOpen (μ₂.ker : Set kˣ) →
  ∀ (m₁ : Measure (GL n₁ k)) (G₁ : Measure (GL (n₁ ⊕ Fin (c + 1)) k)) (m₂ : Measure (GL n₂ k))
    (G₂ : Measure (GL (n₂ ⊕ Fin c) k)), m₁.IsHaarMeasure → G₁.IsHaarMeasure → m₂.IsHaarMeasure → G₂.IsHaarMeasure →
    G₁ (KO k (n₁ ⊕ Fin (c + 1))) = 1 → G₂ (KO k (n₂ ⊕ Fin c)) = 1 →
  ∀ (L₀ : Level (GL (n₀ ⊕ Fin (c + 1 + 1)) k)) (L₁ : Level (GL (n₁ ⊕ Fin (c + 1)) k)) (L₂ : Level (GL (n₂ ⊕ Fin c) k)),
    IsCO L₁.J → IsCO L₂.J → L₁.J ≤ KO k _ → L₂.J ≤ KO k _ →
  ∀ (A : Type) [AddCommGroup A] [Module ℂ A] (τ : Representation ℂ (GL (n₂ ⊕ Fin c) k) A), IsSmoothRep τ →
  ∀ (T : SB (Matrix n₁ n₀ k) →ₗ[ℂ] SB (Matrix n₂ n₁ k) →ₗ[ℂ] A →ₗ[ℂ] ℂ), TriPos ψ μ₁ μ₂ ρ τ T →
  ∀ (F : A), (∀ j : L₂.J, τ (j : GL (n₂ ⊕ Fin c) k) F = (L₂.lam j : ℂ) • F) →
  ∀ (P₁ : SB (Matrix (n₁ ⊕ Fin (c + 1)) (n₀ ⊕ Fin (c + 1 + 1)) k)) (P₂ : SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k)),
    HasTypes μ₁ L₀ L₁ P₁.1 → HasTypes μ₂ L₁ L₂ P₂.1 →
  ∀ (α : GL (n₀ ⊕ Fin (c + 1 + 1)) k) (A₁ : Finset (GL (n₁ ⊕ Fin (c + 1)) k)) (A₂ : Finset (GL (n₂ ⊕ Fin c) k)),
    Covers 1 L₁.J A₁ (fun h => GlobalTheory.StepData.flat ψ ν μ₁ P₁.1 α h) → (∀ γ ∈ A₁, Covers 1 L₂.J A₂ fun h => GlobalTheory.StepData.flat ψ ν μ₂ P₂.1 γ h) →
  ∀ (e₀ : GL (n₀ ⊕ Fin (c + 1 + 1)) k →₀ ℂ), IsOneComb ψ ν (ρ + 1) L₀ α e₀ →
  ∀ (e₂ : GL (n₂ ⊕ Fin c) k → (GL (n₂ ⊕ Fin c) k →₀ ℂ)), (∀ β ∈ A₂, IsOneComb ψ ν ρ L₂ β (e₂ β)) →
  ∀ (z : GL (n₀ ⊕ Fin (c + 1 + 1)) k → ℂ),
    (∀ a ∈ e₀.support, SymDbl ψ ν m₁ G₁ m₂ G₂ μ₁ μ₂ ρ τ T F (om μ₁ a 1 P₁.1) P₂.1 (z a)) →
    comb e₀ z = ((L₁.J.relIndex (KO k _) : ℂ) * (L₂.J.relIndex (KO k _) : ℂ))⁻¹ *
      ∑ γ ∈ A₁, ∑ β ∈ A₂, ((((m₁ (prX (Cgrp L₁.J γ))).toReal⁻¹ * (m₂ (prX (Cgrp L₂.J β))).toReal⁻¹ : ℝ) : ℂ) *
        comb (e₂ β) fun b => app (app T (xi ψ ν μ₁ P₁.1 L₁.J 1 α γ)) (xi ψ ν μ₂ P₂.1 L₂.J 1 γ β) (τ b F)) := by
  first | exact @GlobalTheory.PosOne.comb_eq_sum_cells | exact GlobalTheory.PosOne.comb_eq_sum_cells | (intros; apply GlobalTheory.PosOne.comb_eq_sum_cells <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw ValuativeRel
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_splitPlaceGeometryExtension_cosetOrbitReps : ∀ (D : D7) (c : Comm D) (v : VCom c) (B : GlobalTheory.Fam.Base c) (PP : Formalism.L2.DIV.Pl D.host.E) (G : QGeo v B PP) (χ : ℕ → (AE D)ˣ →* Circle), c.Is → ∀ (δ : G.kˣ →* ℂˣ) (hδ : IsTame δ) (η : ℕ → G.kˣ →* ℂˣ), (∀ j, IsUnram (η j)) → (∀ j, j ≤ G.s + 1 → (ofSplit G.q).IsComp (χ j)⁻¹ (η (j + 1) * δ)) → ∀ A, (G.T δ hδ η).IsRepSystem A G.ψk G.ν → ∀ M : ℕ, (G.T δ hδ η).Adapted A (box _ (G.ϖ ^ M)⁻¹) (box _ (G.ϖ ^ M)) → ∀ (C : Type) [Fintype C] (cs : C → XIx (Fin D.R.k) (Fin D.R.t) (G.s + 1) → G.k), (∀ y y', SameOrb ((G.T δ hδ η).lev (G.s + 1) 0 rfl).J (box _ (G.ϖ ^ M)) (Submodule.Quotient.mk (cs y)) (Submodule.Quotient.mk (cs y')) → y = y') → (∀ z ∈ box (XIx (Fin D.R.k) (Fin D.R.t) (G.s + 1)) (G.ϖ ^ M)⁻¹, ∃ y, SameOrb ((G.T δ hδ η).lev (G.s + 1) 0 rfl).J (box _ (G.ϖ ^ M)) (Submodule.Quotient.mk (cs y)) (Submodule.Quotient.mk z)) → ∃ E : QExt G χ, E.δ = δ ∧ E.η = η ∧ E.A = A ∧ E.M = M ∧ (∃ e : C ≃ E.Ch (G.s + 1), ∀ y, E.cos (e y) = Submodule.Quotient.mk (cs y)) ∧ ∀ j, G.s + 1 + 1 < j → Nonempty (Unique (E.Ch j)) := by
  first | exact @GlobalTheory.QTw.CosExt.exists_qExt_cos | exact GlobalTheory.QTw.CosExt.exists_qExt_cos | (intros; apply GlobalTheory.QTw.CosExt.exists_qExt_cos <;> assumption)
end

section

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix

noncomputable section

namespace GlobalTheory.MiTop.LineAtT

variable {D : D7}

def UnitScal (v : GlobalTheory.FinPl.Pl D) (t : D.host.E) : Prop :=
  ∀ a ∈ idAt D (· = v), incA D t * a ∈ intAt D (· = v) ↔ a ∈ intAt D (· = v)

theorem UnitScal.mul {v : GlobalTheory.FinPl.Pl D} {s t : D.host.E} (hs : UnitScal v s) (ht : UnitScal v t) : UnitScal v (s * t) := fun a ha => by
  rw [RingHom.map_mul, mul_assoc, hs _ (Ideal.mul_mem_left _ _ ha), ht a ha]

theorem UnitScal.cancel {v : GlobalTheory.FinPl.Pl D} {s t : D.host.E} (hst : UnitScal v (s * t)) (ht : UnitScal v t) : UnitScal v s := fun a ha => by
  rw [← hst a ha, ← ht _ (Ideal.mul_mem_left _ _ ha), RingHom.map_mul, ← mul_assoc, mul_comm (incA D t)]

theorem unitAt_one (v : GlobalTheory.FinPl.Pl D) : UnitScal v 1 := fun a _ => by rw [RingHom.map_one, one_mul]

theorem UnitScal.pow {v : GlobalTheory.FinPl.Pl D} {s : D.host.E} (hs : UnitScal v s) (n : ℕ) : UnitScal v (s ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact unitAt_one v
  | succ n ih => rw [pow_succ]; exact ih.mul hs

theorem UnitScal.neg {v : GlobalTheory.FinPl.Pl D} {s : D.host.E} (hs : UnitScal v s) : UnitScal v (-s) := fun a ha => by
  rw [← hs a ha, RingHom.map_neg, neg_mul]
  exact ⟨fun h => neg_neg (incA D s * a) ▸ GlobalTheory.IdVGen.intAt_neg' h, GlobalTheory.IdVGen.intAt_neg'⟩

theorem unitAt_of {v : GlobalTheory.FinPl.Pl D} {s : D.host.E} (hs : s ≠ 0)
    (h : ∀ a ∈ intAt D (· = v), incA D s * a ∈ intAt D (· = v) ∧ incA D s⁻¹ * a ∈ intAt D (· = v)) : UnitScal v s := fun a _ => by
  refine ⟨fun h1 => ?_, fun h1 => (h a h1).1⟩
  have := (h _ h1).2
  rwa [← mul_assoc, ← RingHom.map_mul, inv_mul_cancel₀ hs, RingHom.map_one, one_mul] at this

theorem unitAt_nat {v : GlobalTheory.FinPl.Pl D} {N : ℕ} (hv : (N : 𝓞 D.host.F) ∉ v.asIdeal) : UnitScal v (N : D.host.E) := by
  have hN : (N : D.host.E) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    rintro rfl
    exact hv (by simp)
  refine unitAt_of hN fun a ha => ⟨GlobalTheory.SeeSaw.StdOff.incA_mul_mem_intAt hv ?_ a ha, GlobalTheory.SeeSaw.StdOff.incA_mul_mem_intAt hv ?_ a ha⟩
  · rw [← Nat.cast_mul]; exact isIntegral_natCast _
  · rw [mul_inv_cancel₀ hN]; exact isIntegral_one

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem unitAt_val (p : SplitPt D k) {t : D.host.E} (h1 : valuation k (p.pr (incA D t)) = 1)
    (h2 : valuation k (p.pr (incA D (star t))) = 1) : UnitScal p.v t := fun a ha => by
  rw [GluedLine.mem_intAt_iff p (Ideal.mul_mem_left _ _ ha), GluedLine.mem_intAt_iff p ha, RingHom.map_mul, RingHom.map_mul (cA D),
    RingHom.map_mul, GlobalTheory.FinPl.FrameLat.cA_incA]
  simp only [Valuation.mem_integer_iff, map_mul, h1, h2, one_mul]

theorem psiE_triv {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (p : SplitPt D k) (hU : p.UnitAA) {s : AE D}
    (hs : s ∈ idAt D (· = p.v)) : (∀ o ∈ intAt D (· = p.v), psiE ψ (s * o) = 1) ↔ s ∈ intAt D (· = p.v) := by
  rw [← GlobalTheory.SeeSaw.DiffDual.idV_dI_iff D ψ hψ p.v s hs, ← (GlobalTheory.Core.Mi.LatMatch.idV_dI_pow_unit D k p hU 1 s).1, pow_one]

theorem psiE_ne {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (p : SplitPt D k) (hU : p.UnitAA)
    (q : GlobalTheory.LatPair.Unif k) : ∃ s, psiE ψ s ≠ 1 := by
  by_contra hc
  push_neg at hc
  have h := (psiE_triv hψ p hU (GlobalTheory.FinPl.FrameLat.sec_mem_idAt p q.inv)).1 fun o _ => hc _
  have h1 := GluedLine.pr_mem_of_intAt p h.2
  rw [p.pr_sec] at h1
  have h2 : IsUnit (q.1 : 𝒪[k]) := IsUnit.of_mul_eq_one ⟨_, h1⟩ (Subtype.ext (mul_inv_cancel₀ q.ne_zero))
  exact q.mem_max h2

theorem ne_zero_of_line {L : TH.HSp D} {ζ : Fin L.rank → D.host.E} (h : IsLineVec L ζ) : ζ ≠ 0 := by
  rintro rfl
  exact h.2 (by simp)

theorem vecB_ne {S A L : TH.HSp D} (o : OrthDec S A L) {ζ : Fin L.rank → D.host.E} (h : IsLineVec L ζ) : vecB o ζ ≠ 0 := fun e => by
  apply h.2
  have e' : o.iB *ᵥ ζ = 0 := e
  rw [← o.isoB, ← Matrix.mulVec_mulVec, e', Matrix.mulVec_zero, dotProduct_zero]

theorem wittDecomposition_inclusion_mulVec_rationalVector {S S₀ : TH.HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (z : Fin S₀.rank → D.host.E) :
    d.j0 *ᵥ ratV z = ratV (d.i₀ *ᵥ z) := funext fun r => (RingHom.map_mulVec (incA D) d.i₀ z r).symm

theorem first_scale (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word)
    {ψ : AddChar (AF D.host.F) ℂ} (F₀ : Formalism.L2.Forms.Forms0 D u) (tr : Formalism.L2.SG.ColDict.Transport X u F₀) (hE : _root_.GlobalTheory.Core.Mi.IdE X)
    (hψ : IsStdChar D ψ (-1)) (hne : ∃ s, psiE ψ s ≠ 1) (hr : 0 < D.R.rS) (B : SBes X h u ψ (D.sp.X 0)) {μ : D.host.E}
    (hμ : μ ≠ 0) (hz : ∀ r, (B.d.i₀ *ᵥ vecB B.o B.ζ) r = μ * X.ιE (X.zR u (Fin.cast (rank_eq X h) r))) :
    ∃ lam : D.host.E, (lam = (X.B.g : D.host.E) ∨ lam = -(X.B.g : D.host.E)) ∧ ∀ r, B.d.jX r ⟨0, hr⟩ =
      incA D (μ * lam ^ D.R.rS) * incA D (X.ιE (X.eR ⟨0, hr⟩ (Fin.cast (rank_eq X h) r))) := by
  obtain ⟨lam, hl, hB⟩ := exists_sBes_scaled_dual D X h u ψ F₀ tr hE hψ
  obtain ⟨B', -, -, hz', he, -⟩ := hB μ B.vA hμ
  refine ⟨lam, hl, fun r => ?_⟩
  rw [FirstVec.first_eq (d' := B'.d) (z := vecB B.o B.ζ) (z' := vecB B'.o B'.ζ) hne (vecB_ne _ B.line) (vecB_ne _ B'.line)
    (by rw [wittDecomposition_inclusion_mulVec_rationalVector, wittDecomposition_inclusion_mulVec_rationalVector, funext hz, funext hz']) (Subgroup.ext fun n => (B.tieN n).trans (B'.tieN n).symm)
    (fun n hn => star_injective ((B.tieψ n hn).trans (B'.tieψ n ((B'.tieN n).2 ((B.tieN n).1 hn))).symm)) hr r,
    ← RingHom.map_mul]
  exact congrArg (incA D) (he r ⟨0, hr⟩)

end GlobalTheory.MiTop.LineAtT


end
end

section

open Formalism.BasicNotions

theorem _root_.GlobalTheory.T.dataAsCombinationsAtSplitPlaces_proof : ∀ D : D7, GlobalTheory.FinPl.AllComb D := by
  first | exact @GlobalTheory.FinPl.allComb | exact GlobalTheory.FinPl.allComb | (intros; apply GlobalTheory.FinPl.allComb <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.lineProjection_mem_splitCoreCompletion : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (n : Type) [Fintype n] [DecidableEq n] (S₀ A L : HSp D) (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (α : ∀ i, Frame (p i) A n) (α₀ : ∀ i, Frame (p i) S₀ (n ⊕ Fin 1)) (M : Lat S₀) (Λ : ι → Submodule 𝒪[k] (n → k)), IsSelfDualC S₀ M → (∀ i, IsSumFrame o ζ (α i) (α₀ i) ∧ (α₀ i).IsLat M (lastKer (Λ i))) → ∀ m ∈ latV S₀ M P, o.jB *ᵥ (o.pB *ᵥ m) ∈ latV S₀ M P := by
  first | exact @GlobalTheory.LineProj.lineProj_mem | exact GlobalTheory.LineProj.lineProj_mem | (intros; apply GlobalTheory.LineProj.lineProj_mem <;> assumption)
end

section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.ikedaMap_schrodinger_partialIntegral : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A T T' : HSp D) (t : ℕ) (d : HypDec T T' t) (ν : Measure (WO A T)) (𝓨 : Set (WO A T)), IsCovolOne (ratL T A) ν 𝓨 → ∀ (ν' : Measure (WO A T')) (𝓨' : Set (WO A T')), IsCovolOne (ratL T' A) ν' 𝓨' → ∀ (μ₁ : Measure (Mx D t (dblSp A).rank)) (𝓕₁ : Set (Mx D t (dblSp A).rank)), IsCovolOne (ratMx D t (dblSp A).rank) μ₁ 𝓕₁ → ∀ (μ₂ : Measure (Mx D t A.rank)) (𝓕₂ : Set (Mx D t A.rank)), IsCovolOne (ratMx D t A.rank) μ₂ 𝓕₂ → ∀ φ, IsThetaFunO ψ (dblSp A) T φ → IsThetaFunO ψ (dblSp A) T' (ikeda ψ d μ₁ 𝓕₁ φ) ∧ sch ψ A T' ν' 𝓨' (ikeda ψ d μ₁ 𝓕₁ φ) = ikS d μ₂ (sch ψ A T ν 𝓨 φ) := by
  first | exact @GlobalTheory.IkedaSch.sch_ikeda | exact GlobalTheory.IkedaSch.sch_ikeda | (intros; apply GlobalTheory.IkedaSch.sch_ikeda <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.seeSaw_periods_linearRelations_doubleStep : ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), DoubleStep D → c.Is → (∀ s, (t s).Is) → (∀ s, (t s).LocFin) → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) P₁ P₂ (I : Type) [Fintype I] (s : I → 𝒯) (α : I → ℂ) (φ : ∀ i, (t (s i)).Ch j → GA D (c.X j) → ℂ) (f : I → GA D (c.V (j + 1 + 1)) → ℂ), (∀ i a, IsContAut (c.X j) (φ i a)) → (∀ i, RapidDec _ (f i)) → (∀ i, RapidDec _ (liftS ((t (s i)).om (j + 1)) (c.vol (j + 1 + 1)).μ (c.vol (j + 1 + 1)).𝓕 (f i) ((t (s i)).pt (j + 1) P₂))) → (∀ a ∈ GinfC (c.V (j + 1)), ∀ a' ∈ GinfC (c.V (j + 1 + 1)), ∃ v : I → ℂ, (∀ i, Iter2 (c.ρJ j (σ + 1) h) (c.μf (j + 1)) (c.ρB (j + 1 + 1) σ (idx_step h)) (c.μf (j + 1 + 1)) (fun q₁ q₂ => (t (s i)).integrand j σ h P₁ P₂ (φ i) (f i) (a * q₁.1) (a' * q₂.1)) (v i)) ∧ ∑ i, α i * v i = 0) → ∑ i, α i * (t (s i)).perF j (σ + 1) h (φ i) (liftS ((t (s i)).om j) (c.vol (j + 1)).μ (c.vol (j + 1)).𝓕 (liftS ((t (s i)).om (j + 1)) (c.vol (j + 1 + 1)).μ (c.vol (j + 1 + 1)).𝓕 (f i) ((t (s i)).pt (j + 1) P₂)) ((t (s i)).pt j P₁)) = 0 := by
  first | exact @GlobalTheory.SeeSaw.VanMany.vanMany | exact GlobalTheory.SeeSaw.VanMany.vanMany | (intros; apply GlobalTheory.SeeSaw.VanMany.vanMany <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open NumberField IsDedekindDomain Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LocMod GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.QTw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.step_inverse_character_local_component_chain_tame : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) (P : BadPr I a), P.1 ∉ (B.primes X).vGs → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt (I.rec7 l Z) k), Formalism.L2.NTheta.IsIdemAt (D := I.rec7 l Z) q.e P.1 → (∀ x, (ofSplit q).pr x ∈ 𝒪[k] ↔ Formalism.L2.Col.IntAt P.1 x) → DenseRange (ofSplit q).pr → ∀ (i : ℕ) (hi : i < B.R.m) (χ : (AE (I.rec7 l Z))ˣ →* Circle), ChrEq (D := I.rec7 l Z) χ (I.C.mu0 ⟨i, hi⟩ * I.xi a) → ∀ μ : kˣ →* ℂˣ, (ofSplit q).IsComp χ⁻¹ μ → (∀ (x : B.fields.E) (u : kˣ), (u : k) = (ofSplit q).pr x → (μ u : ℂ) = B.embLL (Formalism.L2.Col.muAt I.Ch I.sel (I.tup a) (I.cst a) i P x)) ∧ IsTame μ := by
  first | exact @GlobalTheory.QTw.StepChar.comp_eq_muAt_and_tame | exact GlobalTheory.QTw.StepChar.comp_eq_muAt_and_tame | (intros; apply GlobalTheory.QTw.StepChar.comp_eq_muAt_and_tame <;> assumption)
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.InertFrameLoc


theorem _root_.GlobalTheory.T.weilRep_latticeVacuum_mem_span_inertTranslates : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v), UnrAt χS w → UnrAt χT w → ∀ (c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E) (ϖ : w.adicCompletion D.host.E) (k : w.adicCompletion D.host.E) (aS : GL (Fin S.rank) (w.adicCompletion D.host.E)) (aT : GL (Fin T.rank) (w.adicCompletion D.host.E)), IsUnramInv ϖ c (qV D.host.F v) → IsConjAt D.sp.cm.sig h c → GlobalTheory.InertLoc.IsGen D w k → IsFrameAt w (frameLat S) aS → IsFrameAt w (frameLat T) aT → Formalism.UG.cT c aS.1 * S.gram.map (algebraMap D.host.E _) * aS.1 = Formalism.UG.antiJ _ S.rank → Formalism.UG.cT c aT.1 * T.gram.map (algebraMap D.host.E _) * aT.1 = Formalism.UG.antiJ _ T.rank → ∀ f, VacFin ψ S T v f → ∀ (gS : Gv S v) (gT : Gv T v), om (embV S v gS, embV T v gT) f ∈ Submodule.span ℂ (Set.range fun x => heisO ψ S T (uPt hw h k aS aT x) f) := by
  first | exact @GlobalTheory.InertFrameLoc.om_mem_span_uPt | exact GlobalTheory.InertFrameLoc.om_mem_span_uPt | (intros; apply GlobalTheory.InertFrameLoc.om_mem_span_uPt <;> assumption)
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
open GlobalTheory.FinPl GlobalTheory.FinPl.SrcGl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_bilinear_equivariant_orthogonalSummandLift : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ψ : AddChar (AF D.host.F) ℂ) (S A L T : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → CoCpt A → ∀ (vA : Vol A) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (α : Frame p A n') (α₀ : Frame p S (n' ⊕ Fin 1)) (β : Frame p T n), IsSumFrame o ζ α α₀ → ∃ lS : kˣ →* ℂˣ, (CharUnramAt D χT p.v → IsUnram lS) ∧ ∀ (LS : Lat S) (LT : Lat T) (f₀ : WO S T → ℂ), IsSelfDualC S LS → IsSelfDualC T LT → Vac ψ S T LS LT (· = p.v) f₀ → ∃ θ : GlobalTheory.FinPl.SrcGl.CA A →ₗ[ℂ] (Matrix n (n' ⊕ Fin 1) k → ℂ) →ₗ[ℂ] (GA D T → WO L T → ℂ), (∀ (v : GlobalTheory.FinPl.SrcGl.CA A) (Φ : Matrix n (n' ⊕ Fin 1) k → ℂ) (f : WO S T → ℂ), Over ψ α₀ β LS LT f₀ Φ f → θ v Φ = liftA o om vA v f) ∧ ∀ (g : GL n' k) (v : GlobalTheory.FinPl.SrcGl.CA A) (Φ : Matrix n (n' ⊕ Fin 1) k → ℂ), Φ ∈ SB (Matrix n (n' ⊕ Fin 1) k) → θ (GlobalTheory.FinPl.SrcGl.caRep α g v) (fun x => Φ (x * (GlobalTheory.FinPl.SrcGl.blk g).val)) = ((lS (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ • θ v Φ := by
  first | exact @GlobalTheory.FinPl.SrcTheta.exists_theta | exact GlobalTheory.FinPl.SrcTheta.exists_theta | (intros; apply GlobalTheory.FinPl.SrcTheta.exists_theta <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.QVal GlobalTheory.FinPl

theorem _root_.GlobalTheory.T.isCompactOpen_product_levels_family : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (S : Dbl2 ψ σ) (r : ℕ) (Q : Fin r → QStep S), Function.Injective (fun i => (Q i).q.v) → IsCO (levJ Q) ∧ IsCO (levB Q) := by
  first | exact @GlobalTheory.QVal.LevCO.isCO_levJ_levB | exact GlobalTheory.QVal.LevCO.isCO_levJ_levB | (intros; apply GlobalTheory.QVal.LevCO.isCO_levJ_levB <;> assumption)
end
