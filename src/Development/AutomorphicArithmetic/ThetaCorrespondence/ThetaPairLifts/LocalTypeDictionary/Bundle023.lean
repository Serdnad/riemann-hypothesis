module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle469
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle510
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpDiv
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle362
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle428
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelHermitianScaling
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle490
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelCharacterMatch
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelRationalStructure
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteInfinitePsiBounds
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleLevelFixesVector
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle443

@[expose] public section

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
namespace GlobalTheory.MovedDict.Entire
theorem differentiable_moved_operator_eval : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big),
    Differentiable ℂ (Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (ch.S.Z.e0 p)) := by
  intro _ _ D Γ _ _ Pl0 T A Ks _ _ _ R ch _ p hp x y
  exact differentiable_Iop' _ _ (ch.S.Z.e0_is p hp).1.1
end GlobalTheory.MovedDict.Entire
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

theorem _root_.GlobalTheory.T.twisted_moved_operator_entire : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big),
    Differentiable ℂ (Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (ch.S.Z.e0 p)) := by
  first | exact @_root_.GlobalTheory.MovedDict.Entire.differentiable_moved_operator_eval | exact _root_.GlobalTheory.MovedDict.Entire.differentiable_moved_operator_eval | (intros; apply _root_.GlobalTheory.MovedDict.Entire.differentiable_moved_operator_eval <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
namespace GlobalTheory.OmegaDer
section Mat
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
end Mat
variable {D : D7}
theorem line_deriv_theta_mem_coinvariants : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X) (χS χT : (AE D)ˣ →* Circle) (ω : WRep M X) (eS eT : D.what₂.Tau → ℚ),
  IsWeil ψ ε M X χS χT ω → (∀ τ, HasInfExp D χS τ (eS τ) ∧ HasInfExp D χT τ (eT τ)) →
  ∀ (Xs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank) (hJ : Xs.J = GlobalTheory.RealDict.sgE (D := D) ε • M.gram),
  ∀ (f₀ : WO (sgn ε M) X → ℂ), IsVacF ψ θ (frSgn ε A) B f₀ →
  ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Xs, ∃ g : ℝ → GA D M,
    (∀ t : ℝ, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M (GlobalTheory.RealDict.sgE (D := D) ε) hJ (g t) = γ (Multiplicative.ofAdd t)) ∧
    ∀ P : PolF D X.rank M.rank, ∃ Q ∈ GlobalTheory.RealQuot.coinv ε A B eT, ∀ z,
      HasDerivAt (fun t : ℝ => ω (g t, 1) (ptF (V := sgn ε M) ψ θ (frSgn ε A) B f₀ P) z) (ptF ψ θ (frSgn ε A) B f₀ Q z) 0 := by
  intro _ D ψ θ _ hθ ε M X A B χS χT ω eS eT hω he Xs hJ f₀ hf γ hγ
  have hc : GlobalTheory.RealDict.sgE (D := D) ε ≠ 0 := by cases ε <;> simp [GlobalTheory.RealDict.sgE]
  obtain ⟨g, h1, h2, h3, h4⟩ := exists_line M hc Xs hJ γ hγ
  refine ⟨g, h1, fun P => ?_⟩
  obtain ⟨Z, hZ, hd⟩ := der_line (V := sgn ε M) (ω := ω.toSgn ε) hθ hω (frSgn ε A) B he hf
    (fun t => (ofSgn ε M).symm (g t)) ((continuous_ofSgn_symm ε M).comp h2)
    (fun s t => by rw [h3, map_mul]) h4
  refine ⟨_, ?_, hd P⟩
  refine Submodule.sum_mem _ fun τ _ => Submodule.subset_span ⟨τ, Z τ, ?_, P, ?_⟩
  · rw [← GlobalTheory.SgnIdent.lieAt_sgn ε M τ]
    exact hZ τ
  · rw [neg_smul, ← sub_eq_add_neg]
    rfl
end GlobalTheory.OmegaDer
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.theta_lineDeriv_vanishes_on_coinvariants : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X) (χS χT : (AE D)ˣ →* Circle) (ω : WRep M X) (eS eT : D.what₂.Tau → ℚ),
  IsWeil ψ ε M X χS χT ω → (∀ τ, HasInfExp D χS τ (eS τ) ∧ HasInfExp D χT τ (eT τ)) →
  ∀ (Xs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank) (hJ : Xs.J = GlobalTheory.RealDict.sgE (D := D) ε • M.gram),
  ∀ (f₀ : WO (sgn ε M) X → ℂ), IsVacF ψ θ (frSgn ε A) B f₀ →
  ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Xs, ∃ g : ℝ → GA D M,
    (∀ t : ℝ, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M (GlobalTheory.RealDict.sgE (D := D) ε) hJ (g t) = γ (Multiplicative.ofAdd t)) ∧
    ∀ P : PolF D X.rank M.rank, ∃ Q ∈ GlobalTheory.RealQuot.coinv ε A B eT, ∀ z,
      HasDerivAt (fun t : ℝ => ω (g t, 1) (ptF (V := sgn ε M) ψ θ (frSgn ε A) B f₀ P) z) (ptF ψ θ (frSgn ε A) B f₀ Q z) 0 := by
  first | exact @_root_.GlobalTheory.OmegaDer.line_deriv_theta_mem_coinvariants | exact _root_.GlobalTheory.OmegaDer.line_deriv_theta_mem_coinvariants | (intros; apply _root_.GlobalTheory.OmegaDer.line_deriv_theta_mem_coinvariants <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
noncomputable section
namespace GlobalTheory.CompactStable
variable {D : D7}
theorem maximal_compact_stable_theta_subspace : _root_.GlobalTheory.FunPr.ThetaLocalInputs →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X) (χS χT : (AE D)ˣ →* Circle) (ω : WRep M X) (eS eT : D.what₂.Tau → ℚ),
  IsWeil ψ ε M X χS χT ω → (∀ τ, HasInfExp D χS τ (eS τ) ∧ HasInfExp D χT τ (eT τ)) →
  ∀ (Xs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E X.rank)
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Xs Ws) (ψ' : AddChar (AF D.host.F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Xs Ws)
    (τ : ∀ w : InfinitePlace D.host.F, GlobalTheory.AdelicU.EmbOver D.host.E w),
    GlobalTheory.RealDict.PublishedHyps D Xs Ws Mo ψ' χX χW om τ → GlobalTheory.RealDict.IsPairReading ψ ε A B ω Xs Ws Mo ψ' om τ →
    ∀ Φ : PolF D X.rank M.rank →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin X.rank),
    Function.Injective Φ → LinearMap.range Φ = Mo.Pol ψ' τ → GlobalTheory.RealDict.IsFockMap ψ θ ε A B Mo Φ →
      ∀ N : Submodule ℂ (PolF D X.rank M.rank),
        GlobalTheory.RealQuot.IsStab (fun i : GlobalTheory.RealQuot.LieIx X => GlobalTheory.RealQuot.actT ε A B eS i.1.1 i.1.2) N →
        ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf D.sp.cm.sig Ws τ, ∀ f ∈ N.map Φ, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin X.rank),
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (om (1, k)) f f₁ → f₁ ∈ N.map Φ := by
  intro _ D ψ θ _ hθ ε M X A B χS χT ω eS eT hω hE Xs Ws Mo ψ' χX χW om τ hH hR Φ hΦ _ hF N hN k hk f hf f₁ hact
  obtain ⟨-, hstd, -, hdX, -, hdW, -, -, -, -, hW, -, -⟩ := hH
  obtain ⟨f₀, r, hv, hv0, hP⟩ := hF
  obtain rfl := hR.psi
  obtain rfl := Eqv.eq_thetaC D hθ
  obtain ⟨T, hT, hTi⟩ := GlobalTheory.T.thetaTransform_darbouxModel_linear_injective D Mo ψ' (sgn ε M).gram (Equiv.refl (Fin X.rank)) hR.good hstd hdX hdW
    (gram_det_ne (sgn ε M))
  have hinj : ∀ a ∈ schA D.host.F (Fin M.rank × Fin X.rank), ∀ b ∈ schA D.host.F (Fin M.rank × Fin X.rank),
      GlobalTheory.TripleRead.thO Mo ψ' (sgn ε M).gram (Equiv.refl (Fin X.rank)) a =
        GlobalTheory.TripleRead.thO Mo ψ' (sgn ε M).gram (Equiv.refl (Fin X.rank)) b → a = b := by
    intro a ha b hb e
    rw [← hT a ha, ← hT b hb, ← sub_eq_zero, ← map_sub] at e
    exact sub_eq_zero.1 (hTi _ (Submodule.sub_mem _ ha hb) e)
  have hr0 : r ≠ 0 := by
    rintro rfl
    apply hv0
    have e1 : ptF ψ' (Eqv.thetaC D) (frSgn ε A) B f₀ 1 = f₀ := by
      have : (1 : PolF D X.rank M.rank) = MvPolynomial.basisMonomials _ ℂ 0 := by simp
      rw [this]
      exact (Module.Basis.constr_basis _ _ _ _).trans (by simp [opPow])
    have e2 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (Φ 1) 0 = 0 := by
      funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens]
    rw [← e1, ← (hP 1).2, e2, ← hT 0 (Submodule.zero_mem _), map_zero]
  have hcan : ∀ (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin X.rank)) (Q : PolF D X.rank M.rank),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) g r ∈ schA D.host.F (Fin M.rank × Fin X.rank) →
      GlobalTheory.TripleRead.thO Mo ψ' (sgn ε M).gram (Equiv.refl (Fin X.rank))
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) g r) = ptF ψ' (Eqv.thetaC D) (frSgn ε A) B f₀ Q → g = Φ Q := by
    intro g Q hg e
    exact DFunLike.coe_injective (tens_inj (hP Q).1.1 hr0 (hinj _ hg _ (hP Q).1.2 (e.trans (hP Q).2.symm)))
  have hi : Function.Injective (ptF ψ' (Eqv.thetaC D) (frSgn ε A) B f₀) := fun P Q e =>
    hΦ (hcan _ Q (hP P).1.2 ((hP P).2.trans e))
  obtain ⟨h, hh, rfl⟩ := exists_of_mem_KInf B hR.JW (fun w => (hR.cart w).imp fun t ht => ⟨ht.1, ht.2.2⟩) hk
  have key := closure_stable (frSgn ε A) B hθ hω hE hv hv0 hi N (fun t Y hY P hP => hN ⟨(t, Y), hY⟩ P hP) hh
  obtain ⟨P, hPN, rfl⟩ := hf
  obtain ⟨Q, hQ, e⟩ := key P hPN
  refine ⟨Q, hQ, (hcan f₁ Q ?_ ?_).symm⟩
  · rw [← hact r (hP P).1]
    letI := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.invTwo (F := D.host.F)
    exact hW.1.1.pres _ _ (hP P).1.2
  · have h1 : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M (GlobalTheory.RealDict.sgE (D := D) ε) hR.JX 1 = 1 :=
      Subtype.ext (by show GeneralLinearGroup.map (cA D) (Formalism.L2.Theta.matHom M 1) = 1; rw [map_one, map_one])
    have h2 := hR.transp _ (hP P).1.2 1 h
    rw [h1, (hP P).2] at h2
    have h3 : ω.toSgn ε (1, h) = ω (1, h) := congrArg ω (Prod.ext (map_one (ofSgn ε M)) rfl)
    rw [h3] at e
    rw [← hact r (hP P).1]
    exact h2.trans e
end GlobalTheory.CompactStable
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

theorem _root_.GlobalTheory.T.theta_subspace_stable_maximal_compact : _root_.GlobalTheory.FunPr.ThetaLocalInputs →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X) (χS χT : (AE D)ˣ →* Circle) (ω : WRep M X) (eS eT : D.what₂.Tau → ℚ),
  IsWeil ψ ε M X χS χT ω → (∀ τ, HasInfExp D χS τ (eS τ) ∧ HasInfExp D χT τ (eT τ)) →
  ∀ (Xs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E X.rank)
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Xs Ws) (ψ' : AddChar (AF D.host.F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Xs Ws)
    (τ : ∀ w : InfinitePlace D.host.F, GlobalTheory.AdelicU.EmbOver D.host.E w),
    GlobalTheory.RealDict.PublishedHyps D Xs Ws Mo ψ' χX χW om τ → GlobalTheory.RealDict.IsPairReading ψ ε A B ω Xs Ws Mo ψ' om τ →
    ∀ Φ : PolF D X.rank M.rank →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin X.rank),
    Function.Injective Φ → LinearMap.range Φ = Mo.Pol ψ' τ → GlobalTheory.RealDict.IsFockMap ψ θ ε A B Mo Φ →
      ∀ N : Submodule ℂ (PolF D X.rank M.rank),
        GlobalTheory.RealQuot.IsStab (fun i : GlobalTheory.RealQuot.LieIx X => GlobalTheory.RealQuot.actT ε A B eS i.1.1 i.1.2) N →
        ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf D.sp.cm.sig Ws τ, ∀ f ∈ N.map Φ, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin X.rank),
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (om (1, k)) f f₁ → f₁ ∈ N.map Φ := by
  first | exact @_root_.GlobalTheory.CompactStable.maximal_compact_stable_theta_subspace | exact _root_.GlobalTheory.CompactStable.maximal_compact_stable_theta_subspace | (intros; apply _root_.GlobalTheory.CompactStable.maximal_compact_stable_theta_subspace <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
noncomputable section
namespace GlobalTheory.RealDict.CompactCoinv
section Oriented
variable {D : D7} {V W : HSp D} {θ : InfFam D} {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle}
  {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)}
end Oriented
section Theta
end Theta
section Reading
variable {D : D7}
end Reading
end GlobalTheory.RealDict.CompactCoinv
namespace GlobalTheory.RealDict
open GlobalTheory.RealDict.CompactCoinv
theorem sub_mem_map_coinv_alt : _root_.GlobalTheory.FunPr.ThetaLocalInputs →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X) (χS χT : (AE D)ˣ →* Circle) (ω : WRep M X) (eS eT : D.what₂.Tau → ℚ),
  IsWeil ψ ε M X χS χT ω → (∀ τ, HasInfExp D χS τ (eS τ) ∧ HasInfExp D χT τ (eT τ)) →
  ∀ (Xs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E X.rank)
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Xs Ws) (ψ' : AddChar (AF D.host.F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Xs Ws)
    (τ : ∀ w : InfinitePlace D.host.F, GlobalTheory.AdelicU.EmbOver D.host.E w),
    GlobalTheory.RealDict.PublishedHyps D Xs Ws Mo ψ' χX χW om τ → GlobalTheory.RealDict.IsPairReading ψ ε A B ω Xs Ws Mo ψ' om τ →
    ∀ Φ : PolF D X.rank M.rank →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin X.rank),
    Function.Injective Φ → LinearMap.range Φ = Mo.Pol ψ' τ → GlobalTheory.RealDict.IsFockMap ψ θ ε A B Mo Φ →
      ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf D.sp.cm.sig Xs τ, ∀ f ∈ Mo.Pol ψ' τ, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin X.rank),
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (om (k, 1)) f f₁ → f₁ - f ∈ (GlobalTheory.RealQuot.coinv ε A B eT).map Φ := by
  intro _ D ψ θ hψ hθ ε M X A B χS χT ω eS eT hω he Xs Ws Mo ψ' χX χW om τ hP hR Φ _ hrange hΦ k hk f hf f₁ hA
  obtain ⟨f₀, r, hvac, h0, hr⟩ := hΦ
  obtain ⟨hCM, -, -, -, -, -, -, -, -, -, hW, -⟩ := hP
  rw [← hrange] at hf
  obtain ⟨P, rfl⟩ := hf
  have hc : sgE (D := D) ε ≠ 0 := by cases ε <;> simp [sgE]
  obtain ⟨g, hgk, hg⟩ := exists_conjU M hc hR.JX k
  obtain ⟨P', hP', hm⟩ := moves_sgn hθ A B hω he hvac h0 g (mem_GinfC_of_conj g _ hg hk.1) (fun t => by
    obtain ⟨t', h1, h2, -⟩ := hR.cart (InfinitePlace.mk ((tauE D t).comp (algebraMap D.host.F D.host.E)))
    obtain rfl := eq_of_conj_over t t' _ h1
    rw [infMat_of_conj hθ hCM g _ hg _ _ h1, ← h2]
    exact hk.2 _) P
  have h1 : GlobalTheory.TripleRead.toUX X (Equiv.refl (Fin X.rank)) hR.JW 1 = 1 := Subtype.ext (Units.ext rfl)
  have h2 := hR.transp _ (hr P).1.2 g 1
  rw [hgk, h1, (hr P).2] at h2
  have h3 := thO_inj Mo hψ (Formalism.L2.Theta.gram_det_ne (sgn ε M))
    (om_mem_schA hW (k, 1) (hr P).1.2) (hr P').1.2 (h2.trans (Eq.trans hP' (hr P').2.symm))
  have hr0 : r ≠ 0 := by
    rintro rfl
    apply h0
    rw [← GlobalTheory.LieScalar.ptF_one (ψ := ψ) (θ := θ) (frSgn ε A) B f₀, ← (hr 1).2]
    funext x
    simp [GlobalTheory.TripleRead.thO, thetaSum, Darboux.rho, schr, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens]
  have h4 : (f₁ : _ → ℂ) = Φ P' := eq_of_tens (hr P).1.1 hr0 ((hA r (hr P).1).symm.trans h3)
  rw [DFunLike.coe_injective h4, ← map_sub]
  exact ⟨_, hm, rfl⟩
end GlobalTheory.RealDict
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

theorem _root_.GlobalTheory.T.weil_model_rational_structure_alt : _root_.GlobalTheory.FunPr.ThetaLocalInputs →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X) (χS χT : (AE D)ˣ →* Circle) (ω : WRep M X) (eS eT : D.what₂.Tau → ℚ),
  IsWeil ψ ε M X χS χT ω → (∀ τ, HasInfExp D χS τ (eS τ) ∧ HasInfExp D χT τ (eT τ)) →
  ∀ (Xs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E X.rank)
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Xs Ws) (ψ' : AddChar (AF D.host.F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Xs Ws)
    (τ : ∀ w : InfinitePlace D.host.F, GlobalTheory.AdelicU.EmbOver D.host.E w),
    GlobalTheory.RealDict.PublishedHyps D Xs Ws Mo ψ' χX χW om τ → GlobalTheory.RealDict.IsPairReading ψ ε A B ω Xs Ws Mo ψ' om τ →
    ∀ Φ : PolF D X.rank M.rank →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin X.rank),
    Function.Injective Φ → LinearMap.range Φ = Mo.Pol ψ' τ → GlobalTheory.RealDict.IsFockMap ψ θ ε A B Mo Φ →
      ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf D.sp.cm.sig Xs τ, ∀ f ∈ Mo.Pol ψ' τ, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin X.rank),
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (om (k, 1)) f f₁ → f₁ - f ∈ (GlobalTheory.RealQuot.coinv ε A B eT).map Φ := by
  first | exact @_root_.GlobalTheory.RealDict.sub_mem_map_coinv_alt | exact _root_.GlobalTheory.RealDict.sub_mem_map_coinv_alt | (intros; apply _root_.GlobalTheory.RealDict.sub_mem_map_coinv_alt <;> assumption)
end
end

section

section
namespace TestFunctionNorms
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.CoefModel
open Formalism.UG
open scoped ComplexOrder
namespace GlobalTheory.CompanionTheory.TestVal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Lat
variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ}
end Lat
section Cast
variable {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ}
end Cast
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}
theorem test_value_psi_finite_infinite : _root_.GlobalTheory.FunPr.ThetaLocalInputs → FinPsiK ∧ InfPsiK := by
  intro _
  constructor
  · refine ⟨0, fun CF _ => ⟨0, fun ε C _ => ⟨0, ?_⟩⟩⟩
    intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch _ _ _ w c u hu x
    exact pullback_fin_relation _ _ w c u hu x
  · refine ⟨0, fun CF _ => ⟨0, fun ε C _ => ⟨0, ?_⟩⟩⟩
    intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch _ _ _ σ c u x
    exact inf_aux _ _ σ c u x
end GlobalTheory.CompanionTheory.TestVal
end
end
end TestFunctionNorms
section
open GlobalTheory.SumSize GlobalTheory.RowClaim
theorem _root_.GlobalTheory.Adopt.test_vector_value_factorization : _root_.GlobalTheory.FunPr.ThetaLocalInputs → FinPsiK ∧ InfPsiK := by
  first | exact @_root_.TestFunctionNorms.GlobalTheory.CompanionTheory.TestVal.test_value_psi_finite_infinite | exact _root_.TestFunctionNorms.GlobalTheory.CompanionTheory.TestVal.test_value_psi_finite_infinite | (intros; apply _root_.TestFunctionNorms.GlobalTheory.CompanionTheory.TestVal.test_value_psi_finite_infinite <;> assumption)
end
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


noncomputable section
namespace GlobalTheory.BotFinLevel
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter GlobalTheory.RowVacScalar Formalism.L2.DIV
open Formalism.IndefR.Fin.LevelGroupLemmas.Lat (frG intM)
variable {D : D7}
end GlobalTheory.BotFinLevel
theorem GlobalTheory.BotFinLevel.bottom_finite_level_fixed : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW), IsBottomTri W i j X → ∀ (s : T), ∀ k ∈ Lev.levA A' (Formalism.L2.DIV.St X.rA'.β), X.ω' s (k, 1) (X.f' s) = X.f' s := by
  intro _ _ _ _ _
  refine ⟨0, fun _ _ _ => ⟨0, 0, fun _ _ D large₂ _ _ _ T Lc μ₀ hμ G => ?_⟩⟩
  intro W _ i j A A' WW X hX s k hk
  exact GlobalTheory.BotFinLevel.fix_of_unram hX.is s (fun v hv => GlobalTheory.BotFinLevel.unram_off G hμ s i j _ hv) hk
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.bottom_layer_finite_level : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW), IsBottomTri W i j X → ∀ (s : T), ∀ k ∈ Lev.levA A' (Formalism.L2.DIV.St X.rA'.β), X.ω' s (k, 1) (X.f' s) = X.f' s := by
  first | exact @_root_.GlobalTheory.BotFinLevel.bottom_finite_level_fixed | exact _root_.GlobalTheory.BotFinLevel.bottom_finite_level_fixed | (intros; apply _root_.GlobalTheory.BotFinLevel.bottom_finite_level_fixed <;> assumption)
end
end
