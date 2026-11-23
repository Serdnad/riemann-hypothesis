module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle001
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle659
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumValueAlgebraicCongruence
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomTriangleRationalCoefficients
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle240
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle589
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle075
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle660
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle335
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle428
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle233
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle604
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle508
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle609
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle026
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle505
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle039
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle187
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle014
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
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
namespace GlobalTheory.LevelVac
variable {D : D7}


theorem level_vacuum_vector_algebraic : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X → ∀ (t : T), ∃ N : ℕ, 0 < N ∧ ∀ k ∈ GfC A, ∀ k' ∈ GfC WW, GlobalTheory.Member.FinCong A N k →
      GlobalTheory.Member.FinCong WW N k' → ∃ ζ : ℂ, IsAlgebraic ℚ ζ ∧ X.ω t (k, k') X.vac = ζ • X.vac := by
  intro D T _ L μ₀ sc G W i j A A' WW X _ _ _ hX t
  have hI := hX.is
  obtain ⟨N, hN, h⟩ := exists_level_fix (S := GlobalTheory.Grid.neg A) (T := WW) (om := (X.ω t).toSgn true) (hI.weil t)
    (sS := fun τ => -X.rA.s τ) (fun τ => GlobalTheory.Grid.isCartanInv_sgn true A τ (hI.rigA.2.2 τ).1)
    (fun τ => (hI.rigW.2.2 τ).1) (GlobalTheory.RowTest.isSelfDualC_neg' hI.rigA.1) hI.rigW.1 hI.rigA.2.1 hI.rigW.2.1 hI.isVac
  refine ⟨N, hN, fun k hk k' hk' hc hc' => ⟨1, isAlgebraic_one, ?_⟩⟩
  rw [one_smul]
  exact h ((GlobalTheory.Grid.ofSgn true A).symm k) hk k' hk' hc hc'
end GlobalTheory.LevelVac
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

theorem _root_.GlobalTheory.T.vacuum_vector_at_level_mem_fockAlgebraic : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X → ∀ (t : T), ∃ N : ℕ, 0 < N ∧ ∀ k ∈ GfC A, ∀ k' ∈ GfC WW, GlobalTheory.Member.FinCong A N k →
      GlobalTheory.Member.FinCong WW N k' → ∃ ζ : ℂ, IsAlgebraic ℚ ζ ∧ X.ω t (k, k') X.vac = ζ • X.vac := by
  first | exact @_root_.GlobalTheory.LevelVac.level_vacuum_vector_algebraic | exact _root_.GlobalTheory.LevelVac.level_vacuum_vector_algebraic | (intros; apply _root_.GlobalTheory.LevelVac.level_vacuum_vector_algebraic <;> assumption)
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
open Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting
open scoped ComplexOrder
noncomputable section
namespace GlobalTheory.RealRatAct
variable {σ : Type}
end GlobalTheory.RealRatAct
namespace GlobalTheory.RealRatAct
open Formalism.L2.Theta
variable {D : D7}
end GlobalTheory.RealRatAct
namespace GlobalTheory.RealRatAct
open Formalism.L2.Theta
variable {D : D7}
end GlobalTheory.RealRatAct
namespace GlobalTheory.RealRatAct
open Formalism.L2.Theta
variable {D : D7}
section Act
variable {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
variable (hW : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ) (hgS : ∀ τ, gramAt D S τ = -1)
  (hgT : ∀ τ, gramAt D T τ = 1) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
  (hv : ∀ ρ, IsFockVacAt (heisO ψ S T) θ ρ (cplxO (-1) 1) f) {K : IntermediateField ℚ ℂ}
  (hK : ∀ z ∈ K, starRingEnd ℂ z ∈ K)
include hW hθ hgS hgT hf hv
end Act
end GlobalTheory.RealRatAct
namespace GlobalTheory.RealRatAct
open Formalism.L2.Theta
variable {D : D7}
section Act
variable {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
  (hW : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ) (hgS : ∀ τ, gramAt D S τ = -1)
  (hgT : ∀ τ, gramAt D T τ = 1) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
  (hv : ∀ ρ, IsFockVacAt (heisO ψ S T) θ ρ (cplxO (-1) 1) f) {K : IntermediateField ℚ ℂ}
  (hK : ∀ z ∈ K, starRingEnd ℂ z ∈ K)
include hW hθ hgS hgT hf hv hK
end Act
end GlobalTheory.RealRatAct
namespace GlobalTheory.RealRatAct
open Formalism.L2.Theta
theorem rationalAction_real_translate : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ M₁ : IntermediateField ℚ ℂ, FiniteDimensional ℚ M₁ ∧ ∀ t, ∀ γ ∈ GQ WW, ∀ r ∈ GinfC WW, γ * r ∈ GfC WW → ∀ x k,
      ∃ c : (FVar D WW.rank A.rank →₀ ℕ) →₀ ℂ, (∀ k', c k' ∈ M₁) ∧
        X.I W.ψ W.θ t (MvPolynomial.monomial k 1) (x * r) = ∑ k' ∈ c.support, c k' * X.I W.ψ W.θ t (MvPolynomial.monomial k' 1) x := by
  intro D T _ L μ₀ sc G W i j A A' WW X _ _ _ hX
  refine ⟨galFld D.host.E, galFld_fin _, fun t γ hγ r hr hγr x k => ?_⟩
  have h := hX.is
  have hθ : IsInfFam W.θ := h.isVac.2.inf
  have hWd := h.weil t
  have hgS : ∀ τ, gramAt D (GlobalTheory.Grid.neg A) τ = -1 := fun τ => by
    rw [gramAt, GlobalTheory.Grid.neg_gram, hX.std.1]
    ext a b
    simp only [Matrix.map_apply, Matrix.neg_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hgT : ∀ τ, gramAt D WW τ = 1 := fun τ => by
    rw [gramAt, hX.stdW.1]; simp
  have hf := (GlobalTheory.ConstRatio.theta_f h t).1
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (h.idem t)
  have hv : ∀ ρ, IsFockVacAt (heisO W.ψ (GlobalTheory.Grid.neg A) WW) W.θ ρ (cplxO (-1) 1) (X.f t) := fun ρ => by
    have := GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt h.isVac.1.1.1 hθ ho.infPart_eq ho.conj.infPart_eq (h.fst t)
      h.isVac.2.theta hf (h.isVac.2.fock ρ)
    simpa [(hX.std.2.2 ρ).1, (hX.stdW.2.2 ρ).1] using this
  obtain ⟨c, hc, Q, hQ, hact⟩ := act_fin hWd hθ hgS hgT hf hv (fun z hz => conj_mem_galFld hz) Finset.univ r hr
    (fun ρ hρ => absurd (Finset.mem_univ ρ) hρ) (compAt_mem W.θ hθ hγ hγr) _ (monomial_mem _ k)
  have hPT : ∀ P, pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P =
      PT W.ψ W.θ (GlobalTheory.Grid.neg A) WW (X.f t) P := fun P => by
    have e1 : (fun τ => -X.rA.s τ) = fun _ => (-1 : Matrix (Fin A.rank) (Fin A.rank) ℂ) :=
      funext fun τ => by rw [(hX.std.2.2 τ).1]
    have e2 : X.rW.s = fun _ => 1 := funext fun τ => (hX.stdW.2.2 τ).1
    have e3 : X.rA.B = fun _ => 1 := funext fun τ => (hX.std.2.2 τ).2
    have e4 : X.rW.B = fun _ => 1 := funext fun τ => (hX.stdW.2.2 τ).2
    rw [e1, e2, e3, e4]
  have e1r : (X.ω t) (1, r) = ((X.ω t).toSgn true) (1, r) := by
    show _ = (X.ω t) ((GlobalTheory.Grid.ofSgn true A).toMonoidHom 1, r)
    rw [map_one]
  have hQs : Q = ∑ k' ∈ Q.support, Q.coeff k' • MvPolynomial.monomial k' (1 : ℂ) := by
    have h1 := MvPolynomial.as_sum Q
    have h2 : ∑ v ∈ Q.support, MvPolynomial.monomial v (AddMonoidAlgebra.coeff Q v) =
        ∑ k' ∈ Q.support, Q.coeff k' • MvPolynomial.monomial k' (1 : ℂ) :=
      Finset.sum_congr rfl fun k' _ => by rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    exact h1.trans h2
  have hker : ∀ g, X.ker W.ψ W.θ t (MvPolynomial.monomial k 1) (x * r) g =
      ∑ k' ∈ Q.support, (c * Q.coeff k') * X.ker W.ψ W.θ t (MvPolynomial.monomial k' 1) x g := by
    intro g
    unfold Tri.ker thetaKO
    have e : (X.ω t) (g, x * r) = (X.ω t) (g, x) * (X.ω t) (1, r) := by
      rw [← map_mul, Prod.mk_mul_mk, mul_one]
    simp only [hPT]
    rw [e, Module.End.mul_apply, e1r, hact]
    conv_lhs => rw [hQs]

    rw [map_sum, Finset.smul_sum, map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun k' _ => ?_
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
  have hint := (hX.integrable t).1
  classical
  let cc : (FVar D WW.rank A.rank →₀ ℕ) →₀ ℂ :=
    Finsupp.onFinset Q.support (fun k' => c * Q.coeff k') fun k' hk' => by
      by_contra hn
      exact hk' (by rw [MvPolynomial.notMem_support_iff.1 hn, mul_zero])
  have hcc : ∀ k', cc k' = c * Q.coeff k' := fun k' => Finsupp.onFinset_apply
  have hsub : cc.support ⊆ Q.support := Finsupp.support_onFinset_subset
  refine ⟨cc, fun k' => ?_, ?_⟩
  · rw [hcc]
    exact (galFld D.host.E).mul_mem hc (coeff_mem hQ k')
  · unfold Tri.I
    simp_rw [hker]
    rw [integral_finsetSum _ fun k' _ => (hint _ x).const_mul _]
    rw [← Finset.sum_subset hsub fun k' _ hk' => by
      rw [← hcc, Finsupp.notMem_support_iff.1 hk']; simp]
    refine Finset.sum_congr rfl fun k' _ => ?_
    rw [integral_const_mul, hcc]
end GlobalTheory.RealRatAct
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

theorem _root_.GlobalTheory.T.realTranslate_preserves_rationalAction : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ M₁ : IntermediateField ℚ ℂ, FiniteDimensional ℚ M₁ ∧ ∀ t, ∀ γ ∈ GQ WW, ∀ r ∈ GinfC WW, γ * r ∈ GfC WW → ∀ x k,
      ∃ c : (FVar D WW.rank A.rank →₀ ℕ) →₀ ℂ, (∀ k', c k' ∈ M₁) ∧
        X.I W.ψ W.θ t (MvPolynomial.monomial k 1) (x * r) = ∑ k' ∈ c.support, c k' * X.I W.ψ W.θ t (MvPolynomial.monomial k' 1) x := by
  first | exact @_root_.GlobalTheory.RealRatAct.rationalAction_real_translate | exact _root_.GlobalTheory.RealRatAct.rationalAction_real_translate | (intros; apply _root_.GlobalTheory.RealRatAct.rationalAction_real_translate <;> assumption)
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
namespace GlobalTheory.MovedJetNZ
open GlobalTheory.Grid (neg ofSgn)
end GlobalTheory.MovedJetNZ
end
namespace GlobalTheory.MovedJetNZ
open GlobalTheory.Grid (neg ofSgn)
theorem moved_vacuum_jet_ne_zero : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X → ∀ (t : T), ∀ γ ∈ Formalism.L2.Theta.GQ A, ∀ a ∈ GinfC A, ∀ γ' ∈ Formalism.L2.Theta.GQ WW, ∀ a' ∈ GinfC WW,
      γ * a ∈ GfC A → γ' * a' ∈ GfC WW →
      ∃ k : FVar D WW.rank A.rank →₀ ℕ, pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.ω t (γ, γ') X.vac) (MvPolynomial.monomial k 1) 0 ≠ 0 := by
  intro D T _ L μ₀ sc G W i j A A' WW X _ hI _ hX t γ hγ _ _ γ' hγ' _ _ _ _
  classical
  have hIs := hX.is
  have hψ : IsStdChar D W.ψ (-1) := hIs.isVac.1
  have hθ : IsInfFam W.θ := hIs.isVac.2.inf
  set om' := (X.ω t).toSgn true with hom'
  have hom := hIs.weil t
  have hsA : ∀ τ, X.rA.s τ = 1 := fun τ => (hX.std.2.2 τ).1
  have hsW : ∀ τ, X.rW.s τ = 1 := fun τ => (hX.stdW.2.2 τ).1
  have hBA : ∀ τ, X.rA.B τ = 1 := fun τ => by rw [(hX.std.2.2 τ).2]
  obtain ⟨k₀, hk₀⟩ := vac_jet_ne_zero hI hX
  by_contra hall
  push_neg at hall
  set γs := (ofSgn true A).symm γ with hγs
  have hγsQ : γs ∈ GQ (neg A) :=
    (GlobalTheory.SgnIdent.mem_GQ_sgn true A γs).2 (by rw [hγs, MulEquiv.apply_symm_apply]; exact hγ)
  have hg : X.ω t (γ, γ') X.vac = om' (γs, γ') X.vac := by
    show _ = (X.ω t) ((ofSgn true A) ((ofSgn true A).symm γ), γ') X.vac
    rw [MulEquiv.apply_symm_apply]
  simp only [hg] at hall
  have hvθ : IsThetaFunO W.ψ (neg A) WW X.vac := hIs.isVac.2.theta
  have hgθ : IsThetaFunO W.ψ (neg A) WW (om' (γs, γ') X.vac) := hom.om_pres _ _ hvθ
  have hzero : ∀ P, pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (om' (γs, γ') X.vac) P 0 = 0 := by
    intro P

    rw [P.as_sum, map_sum, Finset.sum_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    have e : MvPolynomial.monomial k (P.coeff k) = P.coeff k • MvPolynomial.monomial k 1 := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [e, map_smul, Pi.smul_apply, hall k, smul_zero]
  have hop := GlobalTheory.OrientedHeis.om_pureTensorO D W.ψ W.θ (neg A) WW _ _ om' hom hθ (fun τ => -X.rA.s τ) (fun τ => -X.rA.s τ)
    X.rA.B (fun τ => compAt W.θ τ (Formalism.L2.Theta.mt (neg A) γs) * X.rA.B τ) X.rW.s X.rW.s X.rW.B
    (fun τ => compAt W.θ τ (Formalism.L2.Theta.mt WW γ') * X.rW.B τ) γs γ' (fun τ => by rw [hsA]; simp) (fun τ => by rw [hsW]; simp)
    (fun τ => rfl) (fun τ => rfl) X.vac hvθ (MvPolynomial.monomial k₀ 1)
  have haut := hom.om_aut γs hγsQ γ' hγ' _ hop.1
  apply hk₀
  rw [← haut, hop.2]
  have hBW : ∀ τ, X.rW.B τ = 1 := fun τ => by rw [(hX.stdW.2.2 τ).2]
  have e1 : (fun τ => compAt W.θ τ (Formalism.L2.Theta.mt (neg A) γs) * X.rA.B τ) =
      fun τ => X.rA.B τ * compAt W.θ τ (Formalism.L2.Theta.mt (neg A) γs) := by
    funext τ; rw [hBA, Matrix.mul_one, Matrix.one_mul]
  have e2 : (fun τ => compAt W.θ τ (Formalism.L2.Theta.mt WW γ') * X.rW.B τ) =
      fun τ => X.rW.B τ * compAt W.θ τ (Formalism.L2.Theta.mt WW γ') := by
    funext τ; rw [hBW, Matrix.mul_one, Matrix.one_mul]
  have es : (fun τ => -X.rA.s τ) = fun _ => (-1 : Matrix (Fin A.rank) (Fin A.rank) ℂ) := funext fun τ => by rw [hsA]
  have et : X.rW.s = fun _ => (1 : Matrix (Fin WW.rank) (Fin WW.rank) ℂ) := funext hsW
  rw [e1, e2]
  rw [es, et] at hzero ⊢
  change pureTensorO W.ψ W.θ (negSp A) WW (fun _ => -1) (fun _ => 1) _ _ _ _ _ = _
  rw [GlobalTheory.FockNegSubst.pureTensorO_negSp_subst D W.ψ W.θ A WW hψ hθ _ _ _ _ _ hgθ]
  exact hzero _
end GlobalTheory.MovedJetNZ
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

theorem _root_.GlobalTheory.T.jet_of_moved_vacuum_nonvanishing : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X → ∀ (t : T), ∀ γ ∈ Formalism.L2.Theta.GQ A, ∀ a ∈ GinfC A, ∀ γ' ∈ Formalism.L2.Theta.GQ WW, ∀ a' ∈ GinfC WW,
      γ * a ∈ GfC A → γ' * a' ∈ GfC WW →
      ∃ k : FVar D WW.rank A.rank →₀ ℕ, pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.ω t (γ, γ') X.vac) (MvPolynomial.monomial k 1) 0 ≠ 0 := by
  first | exact @_root_.GlobalTheory.MovedJetNZ.moved_vacuum_jet_ne_zero | exact _root_.GlobalTheory.MovedJetNZ.moved_vacuum_jet_ne_zero | (intros; apply _root_.GlobalTheory.MovedJetNZ.moved_vacuum_jet_ne_zero <;> assumption)
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
namespace GlobalTheory.RealAvg
open MvPolynomial
variable {D : D7}
end GlobalTheory.RealAvg
namespace GlobalTheory.RealAvg
open MvPolynomial
open GlobalTheory.Grid (neg sgn ofSgn)
theorem real_average_kernel_isAlgebraic : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ dg : D.what₂.Tau →₀ ℕ, ∀ (κ : Measure (GinfC A)), κ.IsMulLeftInvariant → IsProbabilityMeasure κ →
      ∀ (t : T), ∀ x ∈ GfC A, ∀ h ∈ GfC WW, ∀ k : FVar D WW.rank A.rank →₀ ℕ,
        ∃ (m : ℕ) (r : Fin m → ℂ) (kk : Fin m → (FVar D WW.rank A.rank →₀ ℕ)), (∀ p, IsAlgebraic ℚ (r p)) ∧
          (∀ p, Finsupp.mapDomain Prod.fst (kk p) = dg) ∧
          ∫ g, X.ker W.ψ W.θ t (MvPolynomial.monomial k 1) h (x * (g : GA D A)) ∂κ =
            ∑ p, r p * X.ker W.ψ W.θ t (MvPolynomial.monomial (kk p) 1) h x := by
  intro D T _ L μ₀ sc G W i j A A' WW X hPr hN hL hX
  have hI := hX.is
  have hθ : IsInfFam W.θ := hI.isVac.2.inf
  have hgA : A.gram = 1 := hX.std.1
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig A.gram
  haveI : BorelSpace (GA D A) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig A.gram
  haveI : CompactSpace (GinfC A) := isCompact_iff_compactSpace.1 (GlobalTheory.T.isCompact_unitaryRealPoints_of_gram_eq_one D A hgA)
  haveI : BorelSpace (GinfC A) := Subtype.borelSpace _
  obtain ⟨χ, hχc, hχ, hχa⟩ := _root_.GlobalTheory.T.exists_real_character_twist hPr hN hL hX
  have hΓ := GlobalTheory.T.dense_unitaryRealPoints_algebraicEntries D W.θ hθ A
  let ρ : ∀ d : D.what₂.Tau →₀ ℕ, GinfC A →* Matrix (Mon D WW.rank A.rank d) (Mon D WW.rank A.rank d) ℂ := fun d =>
    { toFun := fun g => χ g • substMat W.θ A WW.rank d g.1
      map_one' := by simp only [map_one, OneMemClass.coe_one, substMat_one, one_smul]
      map_mul' := fun a b => by
        simp only [map_mul, Subgroup.coe_mul, substMat_mul]
        rw [smul_mul_smul_comm] }
  have hρ : ∀ d g, ρ d g = χ g • substMat W.θ A WW.rank d g.1 := fun _ _ => rfl
  have hρc : ∀ d, Continuous (ρ d) := fun d => by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [hρ, Matrix.smul_apply, smul_eq_mul]
    exact hχc.mul (substMat_cont hθ A WW.rank d a b)
  have hρa : ∀ d, ∀ γ ∈ {g : GinfC A | ∀ τ a b, IsAlgebraic ℚ (compAt W.θ τ (Formalism.L2.Theta.mt A g.1) a b)}, ∀ a b,
      IsAlgebraic ℚ (ρ d γ a b) := fun d γ hγ a b => by
    simp only [hρ, Matrix.smul_apply, smul_eq_mul]
    exact (hχa γ hγ).mul (substMat_alg W.θ A WW.rank d a b γ.1 hγ)
  have hker : ∀ t P h (g : GA D A), X.ker W.ψ W.θ t P h g = thetaKO ((X.ω t).toSgn true) ((ofSgn true A).symm g) h
      (pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) := fun t P h g => by
    show thetaKO (X.ω t) g h _ = (X.ω t) ((ofSgn true A) ((ofSgn true A).symm g), h) _ 0
    rw [MulEquiv.apply_symm_apply]
    rfl
  have hform : ∀ d t (x : GA D A) h (g : GinfC A) (k : Mon D WW.rank A.rank d),
      X.ker W.ψ W.θ t (monomial k.1 1) h (x * g.1) =
        ∑ k'' : Mon D WW.rank A.rank d, ρ d g k'' k * X.ker W.ψ W.θ t (monomial k''.1 1) h x := by
    intro d t x h g k
    rw [hker, map_mul]
    unfold thetaKO
    have e : ((ofSgn true A).symm x * (ofSgn true A).symm g.1, h) =
        ((ofSgn true A).symm x, h) * ((ofSgn true A).symm g.1, (1 : GA D WW)) := by
      rw [Prod.mk_mul_mk, mul_one]
    rw [e, map_mul, Module.End.mul_apply, GlobalTheory.T.definiteBottom_weilAction_fockPureTensor_substitution hX t g.1, hχ t g, GlobalTheory.FiniteFock.pureTensorO_smul]
    conv_lhs => rw [eq_sum_mon (d := d) (GlobalTheory.CompactHowe.substF _ _ (monomial k.1 1))
      (fun k'' hk => (GlobalTheory.T.mapDomain_fst_eq_of_coeff_matrixFamilyBilateralSubstitution_ne_zero _ _ _ _ hk).trans k.2)]

    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hρ, Matrix.smul_apply]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k'' _ => ?_
    rw [hker]
    unfold thetaKO substMat
    ring
  have he : ‖Complex.exp Complex.I‖ = 1 := by simpa using Complex.norm_exp_ofReal_mul_I 1
  choose z hz _hzc h1 h2 using fun τ => GlobalTheory.CentralUnit.exists_central_of_norm_one D W.θ hθ A τ (Complex.exp Complex.I) he
  let c : D.what₂.Tau → ℂ := fun τ => χ ⟨z τ, hz τ⟩
  have hcen : ∀ d τ, ρ d ⟨z τ, hz τ⟩ = (c τ * Complex.exp Complex.I ^ d τ) • 1 := fun d τ => by
    rw [hρ, substMat_central W.θ A WW.rank d (z τ) τ _ (h1 τ) (h2 τ), smul_smul]
  obtain ⟨dg, hdg⟩ : ∃ dg : D.what₂.Tau →₀ ℕ, ∀ d, d ≠ dg → ∃ τ, c τ * Complex.exp Complex.I ^ d τ ≠ 1 := by
    by_cases hex : ∃ d : D.what₂.Tau →₀ ℕ, ∀ τ, c τ * Complex.exp Complex.I ^ d τ = 1
    · obtain ⟨d₀, hd₀⟩ := hex
      refine ⟨d₀, fun d hd => ?_⟩
      by_contra hall
      push_neg at hall
      refine hd (Finsupp.ext fun τ => ?_)
      have hc0 : c τ ≠ 0 := fun h0 => by have := hd₀ τ; rw [h0, zero_mul] at this; exact zero_ne_one this
      exact GlobalTheory.ExpPow.pow_exp_I_or_inv_injective _ _ _ (Or.inl rfl)
        (mul_left_cancel₀ hc0 ((hall τ).trans (hd₀ τ).symm))
    · push_neg at hex
      exact ⟨0, fun d _ => hex d⟩
  refine ⟨dg, fun κ hκ hκp t x _ h _ k => ?_⟩
  haveI := hκp
  set d := Finsupp.mapDomain Prod.fst k with hd
  let kM : Mon D WW.rank A.rank d := ⟨k, hd.symm⟩
  have hexp := integral_expand κ (fun g => ρ d g) (hρc d) (fun k'' => X.ker W.ψ W.θ t (monomial k''.1 1) h x)
    (fun g : GinfC A => X.ker W.ψ W.θ t (monomial k 1) h (x * g.1)) kM (fun g => hform d t x h g kM)
  by_cases hdd : d = dg
  · let e := Fintype.equivFin (Mon D WW.rank A.rank d)
    refine ⟨Fintype.card (Mon D WW.rank A.rank d), fun p => ∫ g, ρ d g (e.symm p) kM ∂κ, fun p => (e.symm p).1,
      fun p => GlobalTheory.HaarAlg.isAlgebraic_integral κ (ρ d) (hρc d) _ hΓ (hρa d) _ _,
      fun p => (show Finsupp.mapDomain Prod.fst (e.symm p).1 = d from (e.symm p).2).trans hdd, ?_⟩
    rw [hexp, ← Equiv.sum_comp e.symm]
  · obtain ⟨τ, hτ⟩ := hdg d hdd
    refine ⟨0, Fin.elim0, Fin.elim0, fun p => p.elim0, fun p => p.elim0, ?_⟩
    rw [hexp, Fin.sum_univ_zero]
    refine Finset.sum_eq_zero fun k'' _ => ?_
    rw [integral_eq_zero_of_scalar κ (ρ d) (hρc d) ⟨z τ, hz τ⟩ _ hτ (hcen d τ), zero_mul]
end GlobalTheory.RealAvg
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

theorem _root_.GlobalTheory.T.twisted_real_average_kernel_isAlgebraic : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ dg : D.what₂.Tau →₀ ℕ, ∀ (κ : Measure (GinfC A)), κ.IsMulLeftInvariant → IsProbabilityMeasure κ →
      ∀ (t : T), ∀ x ∈ GfC A, ∀ h ∈ GfC WW, ∀ k : FVar D WW.rank A.rank →₀ ℕ,
        ∃ (m : ℕ) (r : Fin m → ℂ) (kk : Fin m → (FVar D WW.rank A.rank →₀ ℕ)), (∀ p, IsAlgebraic ℚ (r p)) ∧
          (∀ p, Finsupp.mapDomain Prod.fst (kk p) = dg) ∧
          ∫ g, X.ker W.ψ W.θ t (MvPolynomial.monomial k 1) h (x * (g : GA D A)) ∂κ =
            ∑ p, r p * X.ker W.ψ W.θ t (MvPolynomial.monomial (kk p) 1) h x := by
  first | exact @_root_.GlobalTheory.RealAvg.real_average_kernel_isAlgebraic | exact _root_.GlobalTheory.RealAvg.real_average_kernel_isAlgebraic | (intros; apply _root_.GlobalTheory.RealAvg.real_average_kernel_isAlgebraic <;> assumption)
end
end
