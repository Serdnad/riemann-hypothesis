module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle001
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle342
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1282
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1803
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2173
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle311
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle592
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle469
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstStandardPairMemberHasThetaFunction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle240
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle428
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle154
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle226
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle589
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle033
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle594
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralRightTranslate
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle032
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle519
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1195
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComparisonCharacterDetEqOneInertPlace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle237
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle518
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle132
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
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle026
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section
open scoped ComplexOrder Kronecker Matrix
namespace GlobalTheory.BottomRealChar
open GlobalTheory.Grid (neg sgn ofSgn)
theorem exists_real_character_of_bottom : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ → IsBottomTri W i j X → ∃ χ : GinfC A →* ℂ, Continuous χ ∧ (∀ (t : T) (g : GinfC A), (X.ω t).toSgn true ((GlobalTheory.Grid.ofSgn true A).symm g.1, 1) (X.f t) = χ g • X.f t) ∧ ∀ g : GinfC A, (∀ τ a b, IsAlgebraic ℚ (compAt W.θ τ (Formalism.L2.Theta.mt A g.1) a b)) → IsAlgebraic ℚ (χ g) := by
  intro D T _ L μ₀ sc G W i j A A' WW X _ _ hL hX
  have hI := hX.is
  have hθ : IsInfFam W.θ := hI.isVac.2.inf
  have hψ : IsStdChar D W.ψ (-1) := hI.isVac.1
  have hW := fun t => hI.weil t
  have hxi : ∀ t τ, HasInfExp D (L.xi t) τ 0 := fun t τ => by
    obtain ⟨n, hn, ho⟩ := hL.xi_fin t
    exact GlobalTheory.Chain.StepVac.hasInfExp_of_order hθ (hL.xi t) hn ho τ
  choose b hb using fun τ => GlobalTheory.SplitCharExp.exists_hasInfExp D W.θ _ WW.rank τ hθ (hW μ₀).hecT (hW μ₀).resT
  have hbt : ∀ t τ, HasInfExp D ((G.ch.chi (D.R.m - ↑i) * L.eta ^ (rankV D ↑i ↑j % 2)) /
      (L.mu t (↑j + 1) * L.eta ^ (rankV D ↑i ↑j % 2))) τ (b τ) := by
    intro t τ
    have hrel : (G.ch.chi (D.R.m - ↑i) * L.eta ^ (rankV D ↑i ↑j % 2)) / (L.mu t (↑j + 1) * L.eta ^ (rankV D ↑i ↑j % 2)) =
        (G.ch.chi (D.R.m - ↑i) * L.eta ^ (rankV D ↑i ↑j % 2)) / (L.mu μ₀ (↑j + 1) * L.eta ^ (rankV D ↑i ↑j % 2)) *
          (L.xi μ₀ * (L.xi t)⁻¹) := by
      simp only [LevCh.mu, Lift.tup]
      exact commGroup_div_eq_div_mul_ratio _ _ _ _ _
    rw [hrel]
    have := GlobalTheory.Mem.HeckeExp.hasInfExp_mul (hb τ)
      (GlobalTheory.Mem.HeckeExp.hasInfExp_mul (hxi μ₀ τ) (GlobalTheory.Mem.HeckeExp.hasInfExp_inv (hxi t τ)))
    simpa using this
  choose k hk using fun τ => GlobalTheory.SplitParity.exists_int_add_half D _ WW.rank τ (b τ) (hW μ₀).hecT (hW μ₀).resT (hb τ)
  refine ⟨detChar W.θ A fun τ => -(k τ - WW.rank), continuous_detChar hθ _ _, fun t g => ?_,
    fun g hg => isAlgebraic_detChar _ _ _ g hg⟩
  have hsA : ∀ τ, X.rA.s τ = 1 := fun τ => (hX.std.2.2 τ).1
  have hsW : ∀ τ, X.rW.s τ = 1 := fun τ => (hX.stdW.2.2 τ).1
  have hf : IsThetaFunO W.ψ (neg A) WW (X.f t) := by
    have hne : X.ideal (locPl G) t ≠ ⊥ := Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ w.ne_bot
    obtain ⟨f, h1, h2⟩ := GlobalTheory.Adopt.first_standard_pair_member_has_theta_function D W.ψ W.θ A WW X.rA X.rW _ _ _ _ _ hI.rigA hI.rigW (hI.weil' t).hecT
      (hI.idem t) hne hI.isVac
    obtain ⟨Tm, hT⟩ := h1.1
    exact ((hI.fst t).2 Tm hT).trans (h1.2 Tm hT).symm ▸ h2
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (hI.idem t)
  have hfock : ∀ τ, IsFockVacAt (heisO W.ψ (neg A) WW) W.θ τ (cplxO (-X.rA.s τ) (X.rW.s τ)) (X.f t) := fun τ =>
    GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hψ.1.1 hθ ho.infPart_eq ho.conj.infPart_eq (hI.fst t)
      hI.isVac.2.theta hf (hI.isVac.2.fock τ)
  have cS : ∀ τ, IsCartanInv (gramAt D (neg A) τ) (-X.rA.s τ) := fun τ => GlobalTheory.Grid.isCartanInv_sgn true A τ (hI.rigA.2.2 τ).1
  have cT : ∀ τ, IsCartanInv (gramAt D WW τ) (X.rW.s τ) := fun τ => (hI.rigW.2.2 τ).1
  have hdet : ∀ τ, (gramAt D (neg A) τ).det ≠ 0 := fun τ h0 => by
    have := (cS τ).2.2.det_pos.ne'
    rw [Matrix.det_mul, h0, zero_mul] at this
    exact this rfl
  have hg' : (ofSgn true A).symm g.1 ∈ GinfC (neg A) :=
    (GlobalTheory.SgnIdent.mem_GinfC_sgn true A _).2 (by rw [MulEquiv.apply_symm_apply]; exact g.2)
  have hmt : Formalism.L2.Theta.mt (neg A) ((ofSgn true A).symm g.1) = Formalism.L2.Theta.mt A g.1 := by
    rw [← GlobalTheory.Grid.mt_ofSgn, MulEquiv.apply_symm_apply]
  obtain ⟨x, hx, hxv⟩ := GlobalTheory.VacuumCharacter.exists_root hθ (neg A) hdet _ hg'
  have hy1 : IsDetRoot WW 1 1 := by
    show _ = _
    rw [Units.val_one, RingHom.map_one, mul_one]
    exact (Matrix.det_one).symm
  obtain ⟨η, hη⟩ := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  have one : ∀ τ, compAt W.θ τ (Formalism.L2.Theta.mt WW 1) = 1 := fun τ => GlobalTheory.StdUnn.CartanMove.compAt_mt_one W.θ τ WW
  rw [GlobalTheory.WeilVacChar.vacuum_character D W.ψ hψ (neg A) WW W.θ hθ _ _ _ η hη (hW t) (fun τ => -X.rA.s τ) X.rW.s cS cT
      _ hg' 1 (one_mem _) (fun τ => by rw [hsA, Matrix.neg_mul, Matrix.mul_neg, Matrix.one_mul, Matrix.mul_one])
      (fun τ => by rw [one, one_mul, mul_one]) x 1 hx hy1 (X.f t) hf hfock]
  congr 1
  have hx' : ∀ τ, HasInfExp D (((G.ch.chi (D.R.m - ↑i) * L.eta ^ (rankV D ↑i ↑j % 2)) /
      (L.mu t (↑j + 1) * L.eta ^ (rankV D ↑i ↑j % 2))) * (η ^ WW.rank)⁻¹) τ ((k τ - WW.rank : ℤ) : ℚ) := fun τ => by
    have e : ((k τ - WW.rank : ℤ) : ℚ) = b τ - (WW.rank : ℚ) / 2 := by push_cast; rw [hk]; ring
    rw [e]; exact GlobalTheory.VacuumCharacter.hasInfExp_twist (hbt t τ) (hη.2.2.2 τ) _
  simp only [hsA, hsW, detPlus_neg_one_one, Finset.prod_const_one, mul_one, map_one]
  rw [Circle.coe_inv, hxv _ (fun τ => k τ - WW.rank) hx', ← Finset.prod_inv_distrib, detChar_apply, hmt]
  exact Finset.prod_congr rfl fun τ _ => (_root_.zpow_neg _ _).symm
end GlobalTheory.BottomRealChar
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

theorem _root_.GlobalTheory.T.exists_real_character_twist : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ → IsBottomTri W i j X → ∃ χ : GinfC A →* ℂ, Continuous χ ∧ (∀ (t : T) (g : GinfC A), (X.ω t).toSgn true ((GlobalTheory.Grid.ofSgn true A).symm g.1, 1) (X.f t) = χ g • X.f t) ∧ ∀ g : GinfC A, (∀ τ a b, IsAlgebraic ℚ (compAt W.θ τ (Formalism.L2.Theta.mt A g.1) a b)) → IsAlgebraic ℚ (χ g) := by
  first | exact @_root_.GlobalTheory.BottomRealChar.exists_real_character_of_bottom | exact _root_.GlobalTheory.BottomRealChar.exists_real_character_of_bottom | (intros; apply _root_.GlobalTheory.BottomRealChar.exists_real_character_of_bottom <;> assumption)
end
end

section

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open GlobalTheory.Grid
namespace GlobalTheory.RowTest.BottomRat
theorem bottomIntegral_rational_left : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∀ t P, ∀ γ ∈ GQ WW, ∀ x, X.I W.ψ W.θ t P (γ * x) = X.I W.ψ W.θ t P x := by
  intro D T _ L μ₀ sc G W i j A A' WW X _ _ _ hX t P γ hγ x
  have hw := hX.is.weil t
  have hF : IsThetaFunO W.ψ (neg A) WW (pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) :=
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO (S := neg A) hX.is.isVac.1 hX.is.isVac.2.inf (fun τ => -X.rA.s τ) X.rA.B X.rW.s X.rW.B
      (GlobalTheory.ConstRatio.theta_f hX.is t).1 P
  unfold Tri.I
  congr 1
  funext g
  unfold Tri.ker thetaKO
  set F := pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P
  set ω' := (X.ω t).toSgn true
  have e : ∀ y, X.ω t (g, y) = ω' ((ofSgn true A).symm g, y) := fun y => by
    simp [ω', WRep.toSgn]
  rw [e, e]
  have e2 : (((ofSgn true A).symm g, γ * x) : GA D (sgn true A) × GA D WW) = (1, γ) * ((ofSgn true A).symm g, x) := by simp
  rw [e2, map_mul, Module.End.mul_apply]
  exact hw.om_aut 1 (one_mem _) γ hγ _ (hw.om_pres _ _ hF)
end GlobalTheory.RowTest.BottomRat
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

theorem _root_.GlobalTheory.T.bottomIntegral_leftInvariant_rationalPoints : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∀ t P, ∀ γ ∈ GQ WW, ∀ x, X.I W.ψ W.θ t P (γ * x) = X.I W.ψ W.θ t P x := by
  first | exact @_root_.GlobalTheory.RowTest.BottomRat.bottomIntegral_rational_left | exact _root_.GlobalTheory.RowTest.BottomRat.bottomIntegral_rational_left | (intros; apply _root_.GlobalTheory.RowTest.BottomRat.bottomIntegral_rational_left <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section
namespace GlobalTheory.MovedJet
open GlobalTheory.Grid (neg sgn ofSgn)
open MvPolynomial
end GlobalTheory.MovedJet
namespace GlobalTheory.MovedJet
open GlobalTheory.Grid (neg sgn ofSgn)
open MvPolynomial
end GlobalTheory.MovedJet
namespace GlobalTheory.MovedJet
open GlobalTheory.Grid (neg sgn ofSgn)
open MvPolynomial
theorem jet_moved_vacuum_algebraic : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X → ∀ (t : T), ∀ γ ∈ Formalism.L2.Theta.GQ A, ∀ a ∈ GinfC A, ∀ γ' ∈ Formalism.L2.Theta.GQ WW, ∀ a' ∈ GinfC WW,
      γ * a ∈ GfC A → γ' * a' ∈ GfC WW →
      ∀ k : FVar D WW.rank A.rank →₀ ℕ, ∃ (n : ℕ) (c : Fin n → ℂ) (k' : Fin n → FVar D WW.rank A.rank →₀ ℕ),
        (∀ p, IsAlgebraic ℚ (c p)) ∧ (∀ p, Finsupp.mapDomain Prod.fst (k' p) = Finsupp.mapDomain Prod.fst k) ∧
        pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.ω t (γ, γ') X.vac) (MvPolynomial.monomial k 1) 0 = ∑ p, c p * pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.vac) (MvPolynomial.monomial (k' p) 1) 0 := by
  intro D T _ L μ₀ sc G W i j A A' WW X _ _ _ hX t γ hγ a _ γ' hγ' a' _ _ _ k
  have hI := hX.is
  have hθ : IsInfFam W.θ := hI.isVac.2.inf
  have hom := hI.weil t
  set u : D.what₂.Tau → Matrix (Fin A.rank) (Fin A.rank) ℂ := fun τ => compAt W.θ τ (Formalism.L2.Theta.mt A γ) with hu
  set hm : D.what₂.Tau → Matrix (Fin WW.rank) (Fin WW.rank) ℂ :=
    fun τ => (compAt W.θ τ (Formalism.L2.Theta.mt WW γ')).map (starRingEnd ℂ) with hhm
  set H : D.what₂.Tau → Matrix (Fin WW.rank) (Fin WW.rank) ℂ := fun τ => Matrix.conjTranspose (hm τ) with hH
  set U : D.what₂.Tau → Matrix (Fin A.rank) (Fin A.rank) ℂ := fun τ => Matrix.conjTranspose (u τ) with hU
  set Q := GlobalTheory.CompactHowe.substF H U (MvPolynomial.monomial k 1) with hQdef
  have hHm : hm * H = fun _ => 1 := funext fun τ =>
    map_conj_mul_conjT (mul_conjT_of_unitary (conjT_mul_compAt hθ hX.stdW.1 γ' τ))
  have hUm : u * U = fun _ => 1 := funext fun τ => mul_conjT_of_unitary (conjT_mul_compAt hθ hX.std.1 γ τ)
  have hQ : GlobalTheory.CompactHowe.substF hm u Q = MvPolynomial.monomial k 1 := by
    rw [hQdef, GlobalTheory.CompactHowe.substF_mul, hHm, hUm, substF_one]
  have hact := om_pureTensorO_vac hX t γ γ' Q
  have hjet : pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.ω t (γ, γ') X.vac)
        (MvPolynomial.monomial k 1) 0 =
      pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B X.vac Q 0 := by
    rw [← hQ]
    change pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B
      ((X.ω t).toSgn true ((ofSgn true A).symm γ, γ') X.vac) _ 0 = _
    rw [← hact.2]
    exact hom.om_aut _ (GlobalTheory.SquareComm.ofSgn_symm_mem_GQ true hγ) γ' hγ' _ hact.1
  have hHalg : ∀ τ a b, IsAlgebraic ℚ (H τ a b) := by
    intro τ a b
    have e : H τ a b = compAt W.θ τ (Formalism.L2.Theta.mt WW γ') b a := by
      simp [hH, hhm, Matrix.conjTranspose_apply]
    rw [e]
    exact isAlgebraic_compAt_of_mem_GQ hθ hγ' τ b a
  have hUalg : ∀ τ a b, IsAlgebraic ℚ (U τ a b) := by
    intro τ a b
    have e : U τ a b = starRingEnd ℂ (compAt W.θ τ (Formalism.L2.Theta.mt A γ) b a) := by
      simp [hU, hu, Matrix.conjTranspose_apply]
    rw [e]
    exact isAlgebraic_conj (isAlgebraic_compAt_of_mem_GQ hθ hγ τ b a)
  let e := Q.support.equivFin
  refine ⟨Q.support.card, fun p => AddMonoidAlgebra.coeff Q (e.symm p).1, fun p => (e.symm p).1, fun p => ?_, fun p => ?_, ?_⟩
  · exact (GlobalTheory.SubstCoeff.coeff_substF_monomial_continuous_algebraic k (e.symm p).1).2 H U hHalg hUalg
  · exact GlobalTheory.CompactHowe.mapDomain_fst_eq_of_coeff_substF_ne_zero H U k (e.symm p).1
      (MvPolynomial.mem_support_iff.1 (e.symm p).2)
  · rw [hjet]
    calc pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B X.vac Q 0
        = ∑ x ∈ Q.support, AddMonoidAlgebra.coeff Q x *
            pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B X.vac (MvPolynomial.monomial x 1) 0 := by
          conv_lhs => rw [Q.as_sum]

          rw [map_sum, Finset.sum_apply]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [show MvPolynomial.monomial x (AddMonoidAlgebra.coeff Q x) = AddMonoidAlgebra.coeff Q x • MvPolynomial.monomial x 1 by
            rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one], map_smul, Pi.smul_apply, smul_eq_mul]
      _ = _ := by
          rw [← Finset.sum_coe_sort]
          exact (Equiv.sum_comp e.symm (fun x : Q.support => AddMonoidAlgebra.coeff Q x.1 *
            pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B X.vac (MvPolynomial.monomial x.1 1) 0)).symm
end GlobalTheory.MovedJet
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

theorem _root_.GlobalTheory.T.moved_vacuum_jet_algebraic_combination : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X → ∀ (t : T), ∀ γ ∈ Formalism.L2.Theta.GQ A, ∀ a ∈ GinfC A, ∀ γ' ∈ Formalism.L2.Theta.GQ WW, ∀ a' ∈ GinfC WW,
      γ * a ∈ GfC A → γ' * a' ∈ GfC WW →
      ∀ k : FVar D WW.rank A.rank →₀ ℕ, ∃ (n : ℕ) (c : Fin n → ℂ) (k' : Fin n → FVar D WW.rank A.rank →₀ ℕ),
        (∀ p, IsAlgebraic ℚ (c p)) ∧ (∀ p, Finsupp.mapDomain Prod.fst (k' p) = Finsupp.mapDomain Prod.fst k) ∧
        pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.ω t (γ, γ') X.vac) (MvPolynomial.monomial k 1) 0 = ∑ p, c p * pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.vac) (MvPolynomial.monomial (k' p) 1) 0 := by
  first | exact @_root_.GlobalTheory.MovedJet.jet_moved_vacuum_algebraic | exact _root_.GlobalTheory.MovedJet.jet_moved_vacuum_algebraic | (intros; apply _root_.GlobalTheory.MovedJet.jet_moved_vacuum_algebraic <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section
open scoped ComplexOrder Classical
namespace GlobalTheory.BotClassFin
variable {D : D7}
theorem bottomClass_exists_finite_reps : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∀ J : Subgroup (GA D WW), IsOpen (J : Set (GA D WW)) → ∃ H : Finset (GA D WW), (∀ h ∈ H, h ∈ GfC WW) ∧
      ∀ h ∈ GfC WW, ∃ γ ∈ GQ WW, ∃ r ∈ GinfC WW, ∃ h₀ ∈ H, ∃ κ ∈ J, κ ∈ GfC WW ∧ h = γ * r * h₀ * κ := by
  intro D T _ L μ₀ sc G W i j A A' WW X _ _ _ hX J hJ
  have hg : WW.gram = 1 := hX.stdW.1
  have hV : ∀ τ, (gramAt D WW τ).PosDef := by
    intro τ
    have : gramAt D WW τ = 1 := by
      unfold gramAt
      rw [hg]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    rw [this]
    exact Matrix.PosDef.one
  exact exists_reps_of_open WW hV J hJ
end GlobalTheory.BotClassFin
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

theorem _root_.GlobalTheory.T.bottomClasses_finite : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∀ J : Subgroup (GA D WW), IsOpen (J : Set (GA D WW)) → ∃ H : Finset (GA D WW), (∀ h ∈ H, h ∈ GfC WW) ∧
      ∀ h ∈ GfC WW, ∃ γ ∈ GQ WW, ∃ r ∈ GinfC WW, ∃ h₀ ∈ H, ∃ κ ∈ J, κ ∈ GfC WW ∧ h = γ * r * h₀ * κ := by
  first | exact @_root_.GlobalTheory.BotClassFin.bottomClass_exists_finite_reps | exact _root_.GlobalTheory.BotClassFin.bottomClass_exists_finite_reps | (intros; apply _root_.GlobalTheory.BotClassFin.bottomClass_exists_finite_reps <;> assumption)
end
end

section

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
noncomputable section
namespace GlobalTheory.SplitDetChr
open GlobalTheory.LFun GlobalTheory.Doubling
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
end GlobalTheory.SplitDetChr
theorem GlobalTheory.SplitDetChr.split_det_character_eq_one : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → v ∉ X.T → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    G.M'.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 →
    ∀ t : GL (Fin (a + a')) (AE F E), (At (evFin F v) ((t : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) - 1) ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, (t : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v ∧
        ((t⁻¹ : GL (Fin (a + a')) (AE F E)) : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) →
      X.α (Matrix.GeneralLinearGroup.det t) = 1 := by
  intro _ F E _ _ _ _ _ σ B a a' G X om om' hTr v _ hvT _ _ _ t ht
  obtain ⟨ht1, ht2⟩ := ht
  have e1 := GlobalTheory.InertDetChr.eq_ideleAt (GlobalTheory.InertDetChr.at_det_sub_one v t ht1)
  haveI : Submodule.IsFullLattice E G.W.L := hTr.geo.hW.lat
  obtain ⟨P0, h1, h2⟩ := GlobalTheory.AdelicU.Frames.exists_rational_frame G.W.L v
  have hP := GlobalTheory.AdelicU.Frames.frame_of_rational P0 h1 h2
  set T := Formalism.UG.bc (compFin F E v) t with hTdef
  have hT : ∀ y ∈ latLoc F G.W.L v, T.1 *ᵥ y ∈ latLoc F G.W.L v :=
    GlobalTheory.SplitDetChr.mulVec_mem_latLoc G.W v _ (fun z hz => (ht2 z hz).1)
  have hT' : ∀ y ∈ latLoc F G.W.L v, (T⁻¹).1 *ᵥ y ∈ latLoc F G.W.L v := by
    rw [hTdef, ← map_inv]
    exact GlobalTheory.SplitDetChr.mulVec_mem_latLoc G.W v _ (fun z hz => (ht2 z hz).2)
  have hd : GlobalTheory.Doubling.unitFin F E v (Matrix.GeneralLinearGroup.det t) = Matrix.GeneralLinearGroup.det T := by
    refine Units.ext ?_
    show compFin F E v ((Matrix.GeneralLinearGroup.det t : (AE F E)ˣ) : AE F E) = _
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
    rfl
  have hy := GlobalTheory.SplitDetChr.det_mem_intLoc _ hP T hT
  have hy' := GlobalTheory.SplitDetChr.det_mem_intLoc _ hP T⁻¹ hT'
  rw [e1]
  show GlobalTheory.Doubling.charAt X.α v _ = 1
  rw [hd]
  refine GlobalTheory.LFun.charAt_eq_one_of_unrAt X.α v _ hy (by rwa [← map_inv]) (fun w hw => hTr.chars.unrα w ?_)
  show ¬ (w.under (𝓞 F) ∈ (X.T : Set (Pl F)))
  rw [hw]; exact_mod_cast hvT
end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.split_det_character_trivial : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → v ∉ X.T → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    G.M'.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 →
    ∀ t : GL (Fin (a + a')) (AE F E), (At (evFin F v) ((t : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) - 1) ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, (t : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v ∧
        ((t⁻¹ : GL (Fin (a + a')) (AE F E)) : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) →
      X.α (Matrix.GeneralLinearGroup.det t) = 1 := by
  first | exact @_root_.GlobalTheory.SplitDetChr.split_det_character_eq_one | exact _root_.GlobalTheory.SplitDetChr.split_det_character_eq_one | (intros; apply _root_.GlobalTheory.SplitDetChr.split_det_character_eq_one <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.DefiniteLiftZfin
open Matrix
theorem definite_unitary_lift_finite_adeles : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (Φ : WO S T → ℂ) (φ : GA D S → ℂ) (ν : Measure (GA D S))
    (𝓕 : Set (GA D S)), _root_.GlobalTheory.FunPr.ThetaLocalInputs → IsWeilDatumO ψ S T χS χT om → IsInfFam θ → IsThetaFunO ψ S T Φ →
    (∀ τ, (gramAt D S τ).PosDef) → (∀ τ, (gramAt D T τ).PosDef) → ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν →
    IsAutFunSm θ S φ → ∃ W : Submodule ℂ (GA D T → ℂ), FiniteDimensional ℂ W ∧
      (fun h : GA D T => ∫ g in 𝓕, thetaKO om g h Φ * φ g ∂ν) ∈ W ∧ ∀ τ k, ∀ f ∈ W, gelf θ T τ k f ∈ W := by
  intro D ψ θ S T χS χT om Φ φ ν 𝓕 hP hω hθ hΦ hS _ hH hF hφ
  have hK := GlobalTheory.Mem.Lift.isKerSys_thKer (θ := θ) hθ hω.std (GlobalTheory.Ker.isWeak_of_datum hω) hω.om_cont
  exact (hK.lift hP.cuspRapidDecay hθ ⟨hH, hF⟩ ⟨hφ, isCuspFun_of_posDef hS φ⟩ ⟨Φ, hΦ⟩).2.zfin
end GlobalTheory.DefiniteLiftZfin
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.twist_definite_lift_finite_adeles : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (Φ : WO S T → ℂ) (φ : GA D S → ℂ) (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), _root_.GlobalTheory.FunPr.ThetaLocalInputs → IsWeilDatumO ψ S T χS χT om → IsInfFam θ → IsThetaFunO ψ S T Φ → (∀ τ, (gramAt D S τ).PosDef) → (∀ τ, (gramAt D T τ).PosDef) → ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν → IsAutFunSm θ S φ → ∃ W : Submodule ℂ (GA D T → ℂ), FiniteDimensional ℂ W ∧ (fun h : GA D T => ∫ g in 𝓕, thetaKO om g h Φ * φ g ∂ν) ∈ W ∧ ∀ τ k, ∀ f ∈ W, gelf θ T τ k f ∈ W := by
  first | exact @_root_.GlobalTheory.DefiniteLiftZfin.definite_unitary_lift_finite_adeles | exact _root_.GlobalTheory.DefiniteLiftZfin.definite_unitary_lift_finite_adeles | (intros; apply _root_.GlobalTheory.DefiniteLiftZfin.definite_unitary_lift_finite_adeles <;> assumption)
end
end
