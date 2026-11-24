module

import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.RhoNuRhoReducibleC
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.Complementary
public import GroundTheory.AutomorphicForms.InductionParabolicGroups
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrreducibleSecondFactorOfIrreducibleProduct
public import GroundTheory.AutomorphicForms.IwahoriFactorization
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfHasValueAtInfinite
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantModulus
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSupercuspidalOfIsCuspidal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitarizableComplexRepOfSupercuspidalUnitaryCentralCharacter
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitarisableSegmentTwistPrecedesAddOneLe
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRealExponentAbsSmoothCharacterLocalField
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitarisableOfSquareIntegrable
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.HasFiniteLengthJacSub
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspLinesIrr
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentralExponentBoundOver
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothIterPhi
public import GroundTheory.LocalFields.PadicLogSeries
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.GKLocal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassTwistNeg
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsSocleOfOrderFree
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalLanglandsOfIrreducibleAdmissible
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.ConjDual
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.ConjProd
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.CuspPairIrr
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedAbsCharacterization
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.Compact
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.Tactic.Linter.Style
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.PiTensorTwist
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
import Formalism.ConjugateSelfDual.Statement
import ReciprocityTheory.GaloisValuations.GlobalA
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.PosMkIff
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.SimpleRing.Principal
import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.RhoNuRhoOfC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductTransposeInverseDualReverse
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.BoundB, Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.Compact, Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SesquilinearFlipConj, Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.ComplementaryOf, Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.PiTensorTwist, Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.PosMkIff, Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.RhoNuRhoOfC, Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SomeRed, Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.ThetaContra, Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.RhoNuRhoReducibleC

-- ===== clump member: Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.BoundB =====
-- clump-header: {"m": "Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.BoundB", "h": "module\n\npublic import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.Complementary\npublic import GroundTheory.AutomorphicForms.InductionParabolicGroups\nimport Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrreducibleSecondFactorOfIrreducibleProduct\nimport Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedAbsCharacterization\npublic import GroundTheory.AutomorphicForms.IwahoriFactorization\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Henselian\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil ValuativeRel Matrix

namespace PositivityTheory.RgGu.NR.BoundB

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_le_one (t : kˣ) (h : nabs k t ≤ 1) : valuation k (t : k) ≤ 1 := by
  have h1 : nabs k 1 = 1 := (nabs_eq_one_iff (1 : kˣ)).2 (by simp)
  have h2 := (nabs_le_iff t 1).1 (h1 ▸ h)
  simpa using h2

def zd (d : ℕ) (t : kˣ) (i : Fin (d + d)) : kˣ := if blk (blk2 d) i = 0 then t else 1

def Zt (d : ℕ) (t : kˣ) : GL (Fin (d + d)) k := diagT k (Fin (d + d)) (zd d t)

theorem Zt_val (d : ℕ) (t : kˣ) : ((Zt d t : GL (Fin (d + d)) k) : Matrix (Fin (d + d)) (Fin (d + d)) k) =
    diagonal fun i => ((zd d t i : kˣ) : k) := by
  rw [Zt, val_diagT]

theorem Zt_inv_val (d : ℕ) (t : kˣ) :
    (((Zt d t)⁻¹ : GL (Fin (d + d)) k) : Matrix (Fin (d + d)) (Fin (d + d)) k) =
      diagonal fun i => (((zd d t i)⁻¹ : kˣ) : k) := by
  rw [Matrix.coe_units_inv, Zt_val]
  apply Matrix.inv_eq_right_inv
  rw [Matrix.diagonal_mul_diagonal]
  simp

theorem Zt_mem (d : ℕ) (t : kˣ) : Zt d t ∈ parab k (blk2 d) := by
  change ((Zt d t : GL (Fin (d + d)) k) : Matrix _ _ k).BlockTriangular (blk (blk2 d))
  rw [Zt_val]
  exact Matrix.blockTriangular_diagonal _

theorem leviProj_Zt (d : ℕ) (t : kˣ) :
    leviProj k (blk2 d) ⟨Zt d t, Zt_mem d t⟩ = ![Matrix.GeneralLinearGroup.scalar (Fin d) t, 1] := by
  funext a
  ext i j
  simp only [leviProj, diagBlock, MonoidHom.pi_apply, MonoidHom.coe_toHomUnits, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.submatrix_apply, Zt_val, Matrix.diagonal_apply]
  fin_cases a <;> simp [zd, blk, Matrix.diagonal_apply, Matrix.one_apply]

theorem conj_mem (d : ℕ) (t : kˣ) (ht : valuation k (t : k) ≤ 1) {m : ℕ} {z : GL (Fin (d + d)) k}
    (hz : z ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k (d + d) m)
    (hzo : z ∈ GroundTheory.Automorphic.Parabolic.oppositeUnipotentRadical k (d + d) (blk (blk2 d))) :
    ∀ i j, valuation k ((((Zt d t)⁻¹ * z * Zt d t : GL (Fin (d + d)) k) : Matrix _ _ k) i j -
        (1 : Matrix (Fin (d + d)) (Fin (d + d)) k) i j) ≤
          valuation k (GroundTheory.Automorphic.GLnLocal.uniformizer k : k) ^ m ∧
      (((Zt d t)⁻¹ * z * Zt d t : GL (Fin (d + d)) k) : Matrix _ _ k) i j ∈ 𝒪[k] :=
  _root_.CompanionTheory.RgGu.NR.BoundB.conj_mem d t ht hz hzo

theorem conj_mem' (d : ℕ) (t : kˣ) (ht : valuation k (t : k) ≤ 1) {m : ℕ} {z : GL (Fin (d + d)) k}
    (hz : z ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k (d + d) m ⊓
      GroundTheory.Automorphic.Parabolic.oppositeUnipotentRadical k (d + d) (blk (blk2 d))) :
    (Zt d t)⁻¹ * z * Zt d t ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k (d + d) m := by
  obtain ⟨hz1, hz2⟩ := Subgroup.mem_inf.1 hz
  refine (GroundTheory.Automorphic.GLnLocal.mem_congruenceSubgroup_iff k (d + d)).2 ⟨?_, fun i j => (conj_mem d t ht hz1 hz2 i j).1⟩
  refine (GroundTheory.Automorphic.GLnLocal.mem_integralGL_iff k (d + d)).2 ⟨fun i j => (conj_mem d t ht hz1 hz2 i j).2, ?_⟩
  intro i j
  have e : ((Zt d t)⁻¹ * z * Zt d t)⁻¹ = (Zt d t)⁻¹ * z⁻¹ * Zt d t := by group
  rw [e]
  exact (conj_mem d t ht (inv_mem hz1) (inv_mem hz2) i j).2

section Rep

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

def avL (π : Representation ℂ G V) (K : Subgroup G) (H : Subgroup K) [Fintype (K ⧸ H)] : Module.End ℂ V :=
  ∑ q : K ⧸ H, π ((q.out : K) : G)

theorem avL_apply (π : Representation ℂ G V) (K : Subgroup G) (H : Subgroup K) [Fintype (K ⧸ H)] (x : V) :
    avL π K H x = ∑ q : K ⧸ H, π ((q.out : K) : G) x := by
  simp [avL, LinearMap.sum_apply]

theorem avL_fixed (π : Representation ℂ G V) (K : Subgroup G) (H : Subgroup K) [Fintype (K ⧸ H)] {x : V}
    (hx : ∀ h ∈ H, π ((h : K) : G) x = x) (κ : G) (hκ : κ ∈ K) : π κ (avL π K H x) = avL π K H x := by

  rw [avL_apply, map_sum]
  let κ' : K := ⟨κ, hκ⟩
  refine Fintype.sum_equiv (MulAction.toPerm κ' : K ⧸ H ≃ K ⧸ H) _ _ ?_
  intro q
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H (κ' * q.out)
  have e : (κ' • q : K ⧸ H) = ((κ' * q.out : K) : K ⧸ H) := by
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  simp only [MulAction.toPerm_apply]
  rw [e, hh]
  simp only [Subgroup.coe_mul, map_mul, Module.End.mul_apply]
  rw [hx h h.2]

end Rep

section Gen

variable {G X : Type} [Group G] [AddCommGroup X] [Module ℂ X]

theorem hfixH (π : Representation ℂ G X) (K : Subgroup G) (Z : G) (x : X) (hx : ∀ κ ∈ K, π κ x = x)
    (h : K) (hh : h ∈ (K.map (MulAut.conj Z).toMonoidHom).subgroupOf K) :
    π (h : G) (π Z x) = π Z x := by
  obtain ⟨κ, hκ, e⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hh)
  rw [← e]
  change π (Z * κ * Z⁻¹) (π Z x) = π Z x
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, map_mul, Module.End.mul_apply, hx κ hκ]

theorem ineq (π : Representation ℂ G X) (B : X →ₗ[ℂ] X →ₗ⋆[ℂ] ℂ)
    (hB1 : ∀ v w, B w v = starRingEnd ℂ (B v w)) (hB2 : ∀ v, v ≠ 0 → 0 < (B v v).re)
    (hB3 : ∀ g v w, B (π g v) (π g w) = B v w) (K : Subgroup G) (H : Subgroup K) [Fintype (K ⧸ H)] (Z : G)
    (v : X) (hv : v ≠ 0) (lam : ℂ)
    (hT : (Fintype.card (K ⧸ H) : ℂ)⁻¹ • avL π K H (π Z v) = lam • v)
    (hfix : ∀ κ ∈ K, π κ (lam • v) = lam • v) : ‖lam‖ ≤ 1 :=
  _root_.CompanionTheory.RgGu.NR.BoundB.ineq π B hB1 hB2 hB3 K H Z v hv lam hT hfix

end Gen

theorem fixval {d : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ (Levi k fun _ : Fin 2 => Fin d) W) (K : Subgroup (GL (Fin (d + d)) k))
    (v : IndSp (blk2 d) τ) (hv : v ∈ fixed (parInd (blk2 d) τ) K) (g κ : GL (Fin (d + d)) k) (hκ : κ ∈ K) :
    v.1.1 (g * κ) = v.1.1 g := by
  have h2 : parInd (blk2 d) τ κ v = v := by
    have := hv ⟨κ, hκ⟩
    simpa using this
  have h3 : (parInd (blk2 d) τ κ v).1.1 g = v.1.1 (g * κ) := rfl
  rw [← h3, h2]

theorem law {d : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ (Levi k fun _ : Fin 2 => Fin d) W) (p : parab k (blk2 d)) (g : GL (Fin (d + d)) k)
    (f : IndSp (blk2 d) τ) : f.1.1 ((p : GL (Fin (d + d)) k) * g) =
      (deltaHalf k (fun _ : Fin 2 => Fin d) (leviProj k (blk2 d) p) : ℂ) • τ (leviProj k (blk2 d) p) (f.1.1 g) :=
  f.1.2 p g

theorem act {d : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ (Levi k fun _ : Fin 2 => Fin d) W) (g x : GL (Fin (d + d)) k) (f : IndSp (blk2 d) τ) :
    (parInd (blk2 d) τ g f).1.1 x = f.1.1 (x * g) := rfl

theorem zval {d : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ (Levi k fun _ : Fin 2 => Fin d) W) (t : kˣ) (c : ℂ) (htv : valuation k (t : k) ≤ 1)
    (hc : ∀ w, τ ![Matrix.GeneralLinearGroup.scalar (Fin d) t, 1] w = c • w) {m : ℕ} (hm : 1 ≤ m)
    (v : IndSp (blk2 d) τ) (hv : v ∈ fixed (parInd (blk2 d) τ) (GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k (d + d) m))
    (κ : GL (Fin (d + d)) k) (hκ : κ ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k (d + d) m) :
    (parInd (blk2 d) τ (Zt d t) v).1.1 κ =
      ((deltaHalf k (fun _ : Fin 2 => Fin d) ![Matrix.GeneralLinearGroup.scalar (Fin d) t, 1] : ℂ) * c) • v.1.1 1 :=
  _root_.CompanionTheory.RgGu.NR.BoundB.zval τ t c htv hc hm v hv κ hκ

theorem modulus_scalar_block (d : ℕ) (t : kˣ) :
    modulus k (fun _ : Fin 2 => Fin d) ![Matrix.GeneralLinearGroup.scalar (Fin d) t, 1] = nabs k t ^ (d * d) := by
  have c0 : (Finset.univ.filter (fun b : Fin 2 => 0 < b)).card = 1 := by decide
  have c1 : (Finset.univ.filter (fun b : Fin 2 => 1 < b)).card = 0 := by decide
  have c2 : (Finset.univ.filter (fun b : Fin 2 => b = 0)).card = 1 := by decide
  have c3 : (Finset.univ.filter (fun b : Fin 2 => b < 0)).card = 0 := by decide
  have c4 : (Finset.univ.filter (fun b : Fin 2 => b < 1)).card = 1 := by decide
  have e0 : modExp (fun _ : Fin 2 => Fin d) 0 = d := by
    simp [modExp, c0]
  have e1 : modExp (fun _ : Fin 2 => Fin d) 1 = -d := by
    simp [modExp, c1, c2]
  have hn1 : nabs k 1 = 1 := (nabs_eq_one_iff (1 : kˣ)).2 (by simp)
  have hpow : ∀ n : ℕ, nabs k (t ^ n) = nabs k t ^ n := by
    intro n
    induction n with
    | zero => simpa using hn1
    | succ n ih => rw [pow_succ, nabs_mul', ih, pow_succ]
  have hdet : nabs k (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin d) t)) = nabs k t ^ d := by
    have : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin d) t) = t ^ d := by
      ext
      simp
    rw [this, hpow]
  have h1 : nabs k (Matrix.GeneralLinearGroup.det (1 : GL (Fin d) k)) = 1 := by
    rw [map_one]; exact hn1
  simp only [modulus, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, e0, e1, hdet, h1]
  rw [_root_.one_zpow, mul_one, zpow_natCast, ← pow_mul]


theorem bound_main : Bound k := by
  classical
  intro d W _ _ _ τ hsm hadm hunit t c ht hc
  obtain ⟨B, hB1, hB2, hB3⟩ := hunit
  have htv := val_le_one t ht
  obtain ⟨u, hu⟩ := exists_ne (0 : W)
  obtain ⟨f, hf1, -⟩ := GlobalTheory.SmGL.ProdIrr.exists_indSp_apply_one (blk2 d) τ hsm u
  have hopen : IsOpen {g : GL (Fin (d + d)) k | parInd (blk2 d) τ g f = f} := hadm.1 f
  obtain ⟨m0, -, hm0⟩ := (GroundTheory.Automorphic.GLnLocal.hasBasis_nhds_one k (d + d)).mem_iff.1
    (hopen.mem_nhds (by simp))
  set K := GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k (d + d) (m0 + 1) with hKdef
  have hKle : K ≤ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k (d + d) m0 :=
    GroundTheory.Automorphic.GLnLocal.congruenceSubgroup_antitone k (d + d) (Nat.le_succ m0)
  have hfK : f ∈ fixed (parInd (blk2 d) τ) K := by
    intro h
    have := hm0 (hKle h.2)
    simpa using this
  have hKo : IsOpen (K : Set (GL (Fin (d + d)) k)) :=
    GroundTheory.Automorphic.GLnLocal.isOpen_congruenceSubgroup k (d + d) (m0 + 1)
  have hKc : IsCompact (K : Set (GL (Fin (d + d)) k)) :=
    GroundTheory.Automorphic.GLnLocal.isCompact_congruenceSubgroup k (d + d) (m0 + 1)
  haveI hfd : FiniteDimensional ℂ (fixed (parInd (blk2 d) τ) K) := hadm.2 K hKo hKc
  set Z := Zt d t with hZ
  set H := (K.map (MulAut.conj Z).toMonoidHom).subgroupOf K with hH
  have hHo : IsOpen (H : Set K) := by
    have e : ((K.map (MulAut.conj Z).toMonoidHom : Subgroup _) : Set (GL (Fin (d + d)) k)) =
        (fun x => Z⁻¹ * x * Z) ⁻¹' (K : Set _) := by
      ext x
      simp only [Subgroup.coe_map, Set.mem_image, SetLike.mem_coe, Set.mem_preimage,
        MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      constructor
      · rintro ⟨κ, hκ, rfl⟩
        simpa [mul_assoc] using hκ
      · intro hx
        exact ⟨Z⁻¹ * x * Z, hx, by group⟩
    have ho : IsOpen ((K.map (MulAut.conj Z).toMonoidHom : Subgroup _) : Set (GL (Fin (d + d)) k)) := by
      rw [e]
      exact hKo.preimage (by fun_prop)
    exact ho.preimage continuous_subtype_val
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hKc
  haveI : Finite (K ⧸ H) := Subgroup.quotient_finite_of_isOpen H hHo
  letI : Fintype (K ⧸ H) := Fintype.ofFinite _
  have hfixV : ∀ y ∈ fixed (parInd (blk2 d) τ) K, ∀ κ ∈ K, parInd (blk2 d) τ κ y = y := by
    intro y hy κ hκ
    simpa using hy ⟨κ, hκ⟩
  let A : Module.End ℂ (IndSp (blk2 d) τ) :=
    (Fintype.card (K ⧸ H) : ℂ)⁻¹ • (avL (parInd (blk2 d) τ) K H ∘ₗ parInd (blk2 d) τ Z)
  have hAV : ∀ y ∈ fixed (parInd (blk2 d) τ) K, A y ∈ fixed (parInd (blk2 d) τ) K := by
    intro y hy h
    simp only [MonoidHom.one_apply, Units.val_one, one_smul, A, LinearMap.smul_apply, LinearMap.comp_apply, map_smul]
    rw [avL_fixed (parInd (blk2 d) τ) K H
      (fun h' hh' => hfixH (parInd (blk2 d) τ) K Z y (hfixV y hy) h' hh') h h.2]
  let A' : Module.End ℂ (fixed (parInd (blk2 d) τ) K) := A.restrict hAV
  let evI : IndSp (blk2 d) τ →ₗ[ℂ] W :=
    { toFun := fun y => y.1.1 1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let μ : ℂ := (deltaHalf k (fun _ : Fin 2 => Fin d) ![Matrix.GeneralLinearGroup.scalar (Fin d) t, 1] : ℂ) * c
  have hev : ∀ y ∈ fixed (parInd (blk2 d) τ) K, evI (A y) = μ • evI y := by
    intro y hy
    have e1 : ∀ q : K ⧸ H, evI (parInd (blk2 d) τ ((q.out : K) : GL (Fin (d + d)) k) (parInd (blk2 d) τ Z y)) =
        μ • evI y := by
      intro q
      have := zval τ t c htv hc (m := m0 + 1) (by omega) y hy _ (q.out).2
      simp only [evI, LinearMap.coe_mk, AddHom.coe_mk]
      rw [act, one_mul]
      exact this

    simp only [A, LinearMap.smul_apply, LinearMap.comp_apply, avL_apply, map_smul, map_sum]
    rw [Finset.sum_congr rfl (fun q _ => e1 q), Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ,
      smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 Fintype.card_ne_zero), one_smul]
  let S : Module.End ℂ (fixed (parInd (blk2 d) τ) K) := A' - μ • 1
  have hSval : ∀ y : fixed (parInd (blk2 d) τ) K, ((S y : fixed (parInd (blk2 d) τ) K) : IndSp (blk2 d) τ) =
      A y - μ • (y : IndSp (blk2 d) τ) := by
    intro y
    rfl
  have hns : ¬ Function.Surjective S := by
    intro hs
    obtain ⟨y, hy⟩ := hs ⟨f, hfK⟩
    have h1 : evI ((S y : fixed (parInd (blk2 d) τ) K) : IndSp (blk2 d) τ) = 0 := by
      rw [hSval, map_sub, map_smul, hev _ y.2, sub_self]
    rw [hy] at h1
    exact hu (hf1.symm.trans h1)
  have hni : ¬ Function.Injective S := fun hi => hns (LinearMap.injective_iff_surjective.1 hi)
  rw [injective_iff_map_eq_zero] at hni
  push_neg at hni
  obtain ⟨y, hSy, hy0⟩ := hni
  have hAy : A y = μ • (y : IndSp (blk2 d) τ) := by
    have := congrArg Subtype.val hSy
    rw [hSval] at this
    exact sub_eq_zero.1 this
  have hμ := ineq (parInd (blk2 d) τ) B hB1 hB2 hB3 K H Z (y : IndSp (blk2 d) τ)
    (fun h => hy0 (Subtype.ext h)) μ (by simpa only [A, LinearMap.smul_apply, LinearMap.comp_apply] using hAy)
    (fun κ hκ => by rw [map_smul, hfixV y y.2 κ hκ])
  have hδ : ((deltaHalf k (fun _ : Fin 2 => Fin d) ![Matrix.GeneralLinearGroup.scalar (Fin d) t, 1] : ℂˣ) : ℂ) =
      ((Real.sqrt (nabs k t ^ (d * d)) : ℝ) : ℂ) := by
    rw [val_deltaHalf, modulus_scalar_block]
  have hs : Real.sqrt (nabs k t ^ (d * d)) = nabs k t ^ (((d * d : ℕ) : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt (nabs_pos k t))]
    ring_nf
  simp only [μ] at hμ
  rw [norm_mul, hδ, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), hs] at hμ
  rw [mul_comm]
  exact hμ

end PositivityTheory.RgGu.NR.BoundB

namespace PositivityTheory.RgGu.NR

theorem boundB (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    Bound k := BoundB.bound_main

end PositivityTheory.RgGu.NR
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.BoundB =====

-- ===== clump member: Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.Compact =====
-- clump-header: {"m": "Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.Compact", "h": "module\n\nimport CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.Compact\npublic import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.Complementary\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfHasValueAtInfinite\nimport Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantModulus\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Coalgebra.CoassocSimps\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil

namespace PositivityTheory.RgGu.NR.Compact

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {d : ℕ}

theorem isOpen_fix {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ G V) (v : V) (U : Set G) (hU : IsOpen U) (h1 : (1 : G) ∈ U)
    (hfix : ∀ u ∈ U, ρ u v = v) : IsOpen {g : G | ρ g v = v} := by
  rw [isOpen_iff_mem_nhds]
  intro g hg
  have hgU : (fun x => g * x) '' U ∈ nhds g := by
    have ho : IsOpen ((fun x => g * x) '' U) := (Homeomorph.mulLeft g).isOpenMap U hU
    exact ho.mem_nhds ⟨1, h1, mul_one g⟩
  refine Filter.mem_of_superset hgU ?_
  rintro _ ⟨u, hu, rfl⟩
  show ρ (g * u) v = v
  rw [map_mul, Module.End.mul_apply, hfix u hu]
  exact hg

def rc (m : Levi k fun _ : Fin 2 => Fin d) : ℝ :=
  (nabs k (Matrix.GeneralLinearGroup.det (m 0)))⁻¹ * nabs k (Matrix.GeneralLinearGroup.det (m 1))

theorem rc_pos (m : Levi k fun _ : Fin 2 => Fin d) : 0 < rc m := by
  unfold rc
  have h0 := nabs_pos' k (Matrix.GeneralLinearGroup.det (m 0))
  have h1 := nabs_pos' k (Matrix.GeneralLinearGroup.det (m 1))
  positivity

theorem rc_mul (m m' : Levi k fun _ : Fin 2 => Fin d) : rc (m * m') = rc m * rc m' := by
  unfold rc
  simp only [Pi.mul_apply, map_mul, nabs_mul', mul_inv]
  ring

theorem chi_val (s : ℝ) (m : Levi k fun _ : Fin 2 => Fin d) :
    ((chi k d s m : ℂˣ) : ℂ) = ((rc m ^ s : ℝ) : ℂ) := by
  have e : -(s : ℂ) = ((-s : ℝ) : ℂ) := by push_cast; ring
  simp only [chi, MonoidHom.mul_apply, Units.val_mul, MonoidHom.comp_apply, Pi.evalMonoidHom_apply,
    detChar_apply]
  rw [e, val_absPow_ofReal, val_absPow_ofReal, ← Complex.ofReal_mul]
  congr 1
  unfold rc
  have h0 := (nabs_pos' k (Matrix.GeneralLinearGroup.det (m 0))).le
  have h1 := (nabs_pos' k (Matrix.GeneralLinearGroup.det (m 1))).le
  rw [Real.mul_rpow (inv_nonneg.2 h0) h1, Real.inv_rpow h0, Real.rpow_neg h0]

theorem rc_of_KO (q : parab k (blk2 d)) (hq : (q : GL (Fin (d + d)) k) ∈ KO k (Fin (d + d))) :
    rc (leviProj k (blk2 d) q) = 1 := by
  have hK : ∀ a, leviProj k (blk2 d) q a ∈ KO k (Fin d) := by
    intro a
    rw [GlobalTheory.SplitFlip.mem_KO_iff]
    obtain ⟨h1, h2⟩ := (GlobalTheory.SplitFlip.mem_KO_iff _).1 hq
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [leviProj_apply]; exact h1 _ _
    · have e : (leviProj k (blk2 d) q a)⁻¹ = leviProj k (blk2 d) q⁻¹ a := by rw [map_inv]; rfl
      rw [e, leviProj_apply]
      exact h2 _ _
  unfold rc
  rw [GlobalTheory.LGrp.nabs_det_of_mem_KO (hK 0), GlobalTheory.LGrp.nabs_det_of_mem_KO (hK 1)]
  simp

theorem exists_pw (x : GL (Fin (d + d)) k) :
    ∃ p : parab k (blk2 d), ∃ w ∈ KO k (Fin (d + d)), x = (p : GL (Fin (d + d)) k) * w := by
  obtain ⟨u, g, w, hw, rfl⟩ := GlobalTheory.SmGL.UnitInd.exists_iwasawa (blk2 d) x
  have hg : leviEmb k (blk2 d) g ∈ parab k (blk2 d) :=
    mem_parab_iff.2 fun _ _ i j hab => by
      simp [leviEmb, Matrix.blockDiagonal'_apply', hab.ne']
  exact ⟨⟨(u : GL (Fin (d + d)) k) * leviEmb k (blk2 d) g,
    mul_mem (unipRad_le_parab k (blk2 d) u.2) hg⟩, w, hw, rfl⟩

def hh (x : GL (Fin (d + d)) k) : ℝ := rc (leviProj k (blk2 d) (Classical.choose (exists_pw x)))

theorem hh_spec (p : parab k (blk2 d)) (w : GL (Fin (d + d)) k) (hw : w ∈ KO k (Fin (d + d))) :
    hh ((p : GL (Fin (d + d)) k) * w) = rc (leviProj k (blk2 d) p) := by
  obtain ⟨w', hw', e⟩ := Classical.choose_spec (exists_pw ((p : GL (Fin (d + d)) k) * w))
  set p' := Classical.choose (exists_pw ((p : GL (Fin (d + d)) k) * w))
  have hq : ((p'⁻¹ * p : parab k (blk2 d)) : GL (Fin (d + d)) k) ∈ KO k (Fin (d + d)) := by
    have : ((p'⁻¹ * p : parab k (blk2 d)) : GL (Fin (d + d)) k) = w' * w⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_eq_iff_eq_mul, ← mul_assoc, ← e]
      group
    rw [this]
    exact mul_mem hw' (inv_mem hw)
  have h1 : p = p' * (p'⁻¹ * p) := by group
  show rc (leviProj k (blk2 d) p') = _
  conv_rhs => rw [h1, map_mul, rc_mul, rc_of_KO _ hq, mul_one]

theorem hh_pos (x : GL (Fin (d + d)) k) : 0 < hh x := rc_pos _

theorem hh_mul_left (p : parab k (blk2 d)) (x : GL (Fin (d + d)) k) :
    hh ((p : GL (Fin (d + d)) k) * x) = rc (leviProj k (blk2 d) p) * hh x := by
  obtain ⟨p', w, hw, rfl⟩ := exists_pw (d := d) x
  rw [← mul_assoc, ← Subgroup.coe_mul, hh_spec _ _ hw, hh_spec _ _ hw, map_mul, rc_mul]

theorem hh_mul_right (x w : GL (Fin (d + d)) k) (hw : w ∈ KO k (Fin (d + d))) : hh (x * w) = hh x := by
  obtain ⟨p', w', hw', rfl⟩ := exists_pw (d := d) x
  rw [mul_assoc, hh_spec _ _ (mul_mem hw' hw), hh_spec _ _ hw']

variable {W : Type} [AddCommGroup W] [Module ℂ W]

def mulFun (a : ℝ) (f : GL (Fin (d + d)) k → W) : GL (Fin (d + d)) k → W := fun x => ((hh x ^ a : ℝ) : ℂ) • f x

theorem mulFun_mem (a : ℝ) (τ₁ τ₂ : Representation ℂ (Levi k fun _ : Fin 2 => Fin d) W)
    (hrel : ∀ m v, τ₂ m v = ((rc m ^ a : ℝ) : ℂ) • τ₁ m v) (f : IndSp (blk2 d) τ₁) :
    mulFun a f.1.1 ∈ indSpace (parab k (blk2 d)) ((twist τ₂ (deltaHalf k fun _ : Fin 2 => Fin d)).comp
      (leviProj k (blk2 d))) := by
  intro p g
  show ((hh ((p : GL (Fin (d + d)) k) * g) ^ a : ℝ) : ℂ) • f.1.1 ((p : GL (Fin (d + d)) k) * g) =
    (deltaHalf k (fun _ : Fin 2 => Fin d) (leviProj k (blk2 d) p) : ℂ) •
      τ₂ (leviProj k (blk2 d) p) (((hh g ^ a : ℝ) : ℂ) • f.1.1 g)
  have hf : f.1.1 ((p : GL (Fin (d + d)) k) * g) =
      (deltaHalf k (fun _ : Fin 2 => Fin d) (leviProj k (blk2 d) p) : ℂ) • τ₁ (leviProj k (blk2 d) p) (f.1.1 g) :=
    f.1.2 p g
  rw [hf, hrel, hh_mul_left, Real.mul_rpow (rc_pos _).le (hh_pos _).le]
  simp only [map_smul, smul_smul, Complex.ofReal_mul]
  congr 1
  ring

theorem mulFun_smooth (a : ℝ) (τ₁ τ₂ : Representation ℂ (Levi k fun _ : Fin 2 => Fin d) W)
    (hrel : ∀ m v, τ₂ m v = ((rc m ^ a : ℝ) : ℂ) • τ₁ m v) (f : IndSp (blk2 d) τ₁) :
    (⟨mulFun a f.1.1, mulFun_mem a τ₁ τ₂ hrel f⟩ : indSpace _ _) ∈ smoothPart (ind (parab k (blk2 d))
      ((twist τ₂ (deltaHalf k fun _ : Fin 2 => Fin d)).comp (leviProj k (blk2 d)))) := by
  have hf2 : IsOpen {g : GL (Fin (d + d)) k | ind (parab k (blk2 d))
      ((twist τ₁ (deltaHalf k fun _ : Fin 2 => Fin d)).comp (leviProj k (blk2 d))) g f.1 = f.1} := f.2
  refine isOpen_fix (ind (parab k (blk2 d)) ((twist τ₂ (deltaHalf k fun _ : Fin 2 => Fin d)).comp
      (leviProj k (blk2 d)))) _ _ (hf2.inter GlobalTheory.SplitFlip.isOpen_KO) ⟨by simp, one_mem _⟩ ?_
  rintro u ⟨hu1, hu2⟩
  apply Subtype.ext
  funext x
  show ((hh (x * u) ^ a : ℝ) : ℂ) • f.1.1 (x * u) = ((hh x ^ a : ℝ) : ℂ) • f.1.1 x
  have hf : f.1.1 (x * u) = f.1.1 x := congrFun (congrArg Subtype.val hu1) x
  rw [hh_mul_right x u hu2, hf]

def mulMap (a : ℝ) (τ₁ τ₂ : Representation ℂ (Levi k fun _ : Fin 2 => Fin d) W)
    (hrel : ∀ m v, τ₂ m v = ((rc m ^ a : ℝ) : ℂ) • τ₁ m v) : IndSp (blk2 d) τ₁ →ₗ[ℂ] IndSp (blk2 d) τ₂ where
  toFun f := ⟨⟨mulFun a f.1.1, mulFun_mem a τ₁ τ₂ hrel f⟩, mulFun_smooth a τ₁ τ₂ hrel f⟩
  map_add' f g := by
    apply Subtype.ext; apply Subtype.ext; funext x
    show ((hh x ^ a : ℝ) : ℂ) • (f.1.1 x + g.1.1 x) = ((hh x ^ a : ℝ) : ℂ) • f.1.1 x + ((hh x ^ a : ℝ) : ℂ) • g.1.1 x
    rw [smul_add]
  map_smul' c f := by
    apply Subtype.ext; apply Subtype.ext; funext x
    show ((hh x ^ a : ℝ) : ℂ) • (c • f.1.1 x) = c • (((hh x ^ a : ℝ) : ℂ) • f.1.1 x)
    rw [smul_comm]

theorem rel_symm (a : ℝ) (τ₁ τ₂ : Representation ℂ (Levi k fun _ : Fin 2 => Fin d) W)
    (hrel : ∀ m v, τ₂ m v = ((rc m ^ a : ℝ) : ℂ) • τ₁ m v) :
    ∀ m v, τ₁ m v = ((rc m ^ (-a) : ℝ) : ℂ) • τ₂ m v := by
  intro m v
  rw [hrel, smul_smul, ← Complex.ofReal_mul, ← Real.rpow_add (rc_pos m), neg_add_cancel, Real.rpow_zero,
    Complex.ofReal_one, one_smul]

def mulEquiv (a : ℝ) (τ₁ τ₂ : Representation ℂ (Levi k fun _ : Fin 2 => Fin d) W)
    (hrel : ∀ m v, τ₂ m v = ((rc m ^ a : ℝ) : ℂ) • τ₁ m v) : IndSp (blk2 d) τ₁ ≃ₗ[ℂ] IndSp (blk2 d) τ₂ :=
  { mulMap a τ₁ τ₂ hrel with
    invFun := mulMap (-a) τ₂ τ₁ (rel_symm a τ₁ τ₂ hrel)
    left_inv := fun f => by
      apply Subtype.ext; apply Subtype.ext; funext x
      show ((hh x ^ (-a) : ℝ) : ℂ) • ((hh x ^ a : ℝ) : ℂ) • f.1.1 x = f.1.1 x
      rw [smul_smul, ← Complex.ofReal_mul, ← Real.rpow_add (hh_pos x), neg_add_cancel, Real.rpow_zero,
        Complex.ofReal_one, one_smul]
    right_inv := fun f => by
      apply Subtype.ext; apply Subtype.ext; funext x
      show ((hh x ^ a : ℝ) : ℂ) • ((hh x ^ (-a) : ℝ) : ℂ) • f.1.1 x = f.1.1 x
      rw [smul_smul, ← Complex.ofReal_mul, ← Real.rpow_add (hh_pos x), add_neg_cancel, Real.rpow_zero,
        Complex.ofReal_one, one_smul] }

variable (τ : Representation ℂ (Levi k fun _ : Fin 2 => Fin d) W)

theorem relChi (s : ℝ) : ∀ m v, twist τ (chi k d s) m v = ((rc m ^ s : ℝ) : ℂ) • τ m v := by
  intro m v
  show ((chi k d s m : ℂˣ) : ℂ) • τ m v = _
  rw [chi_val]

def E (s : ℝ) : IndSp (blk2 d) τ ≃ₗ[ℂ] IndSp (blk2 d) (twist τ (chi k d s)) :=
  mulEquiv s τ (twist τ (chi k d s)) (relChi τ s)

def F (s : ℝ) : Representation ℂ (GL (Fin (d + d)) k) (IndSp (blk2 d) τ) where
  toFun g := (E τ s).symm.toLinearMap ∘ₗ parInd (blk2 d) (twist τ (chi k d s)) g ∘ₗ (E τ s).toLinearMap
  map_one' := by
    ext f : 1
    simp
  map_mul' g g' := by
    ext f : 1
    simp [map_mul]

theorem F_apply (s : ℝ) (g : GL (Fin (d + d)) k) (f : IndSp (blk2 d) τ) (y : GL (Fin (d + d)) k) :
    (F τ s g f).1.1 y = ((hh y ^ (-s) : ℝ) : ℂ) • ((hh (y * g) ^ s : ℝ) : ℂ) • f.1.1 (y * g) := rfl

def cc (g y : GL (Fin (d + d)) k) : ℝ := hh (y * g) / hh y

theorem cc_left (g : GL (Fin (d + d)) k) (p : parab k (blk2 d)) (y : GL (Fin (d + d)) k) :
    cc g ((p : GL (Fin (d + d)) k) * y) = cc g y := by
  unfold cc
  rw [mul_assoc, hh_mul_left, hh_mul_left, mul_div_mul_left _ _ (rc_pos _).ne']

def K1 (g : GL (Fin (d + d)) k) : Set (GL (Fin (d + d)) k) :=
  (KO k (Fin (d + d)) : Set _) ∩ (fun w => g⁻¹ * w * g) ⁻¹' (KO k (Fin (d + d)) : Set _)

theorem isOpen_compact_open_subgroup (g : GL (Fin (d + d)) k) : IsOpen (K1 (k := k) g) :=
  GlobalTheory.SplitFlip.isOpen_KO.inter (GlobalTheory.SplitFlip.isOpen_KO.preimage (by fun_prop))

theorem cc_right (g y w : GL (Fin (d + d)) k) (hw : w ∈ K1 g) : cc g (y * w) = cc g y := by
  unfold cc
  have e : y * w * g = y * g * (g⁻¹ * w * g) := by group
  rw [e, hh_mul_right _ _ hw.2, hh_mul_right _ _ hw.1]

theorem cc_finite (g : GL (Fin (d + d)) k) : (Set.range (cc (k := k) g)).Finite := by
  apply CompanionTheory.RgGu.NR.Compact.cc_finite

theorem ind_val_sum {σ : Representation ℂ (parab k (blk2 d)) W} {ι : Type} (s : Finset ι) (c : ι → ℂ)
    (u : ι → smoothPart (ind (parab k (blk2 d)) σ)) (y : GL (Fin (d + d)) k) :
    (∑ i ∈ s, c i • u i).1.1 y = ∑ i ∈ s, c i • (u i).1.1 y := by
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply]

def piece (g : GL (Fin (d + d)) k) (v : ℝ) (f : IndSp (blk2 d) τ) : IndSp (blk2 d) τ :=
  ⟨⟨fun y => if cc g y = v then f.1.1 (y * g) else 0, by
      intro p y
      show (if cc g ((p : GL (Fin (d + d)) k) * y) = v then f.1.1 ((p : GL (Fin (d + d)) k) * y * g) else 0) =
        ((twist τ (deltaHalf k fun _ : Fin 2 => Fin d)).comp (leviProj k (blk2 d))) p
          (if cc g y = v then f.1.1 (y * g) else 0)
      rw [cc_left]
      split_ifs
      · rw [mul_assoc]; exact f.1.2 p (y * g)
      · rw [map_zero]⟩, by
      have hf2 : IsOpen {x : GL (Fin (d + d)) k | ind (parab k (blk2 d))
          ((twist τ (deltaHalf k fun _ : Fin 2 => Fin d)).comp (leviProj k (blk2 d))) x f.1 = f.1} := f.2
      refine isOpen_fix (ind (parab k (blk2 d)) ((twist τ (deltaHalf k fun _ : Fin 2 => Fin d)).comp
          (leviProj k (blk2 d)))) _ (((fun w => g⁻¹ * w * g) ⁻¹' {x : GL (Fin (d + d)) k | ind (parab k (blk2 d))
          ((twist τ (deltaHalf k fun _ : Fin 2 => Fin d)).comp (leviProj k (blk2 d))) x f.1 = f.1}) ∩ K1 g)
        ((hf2.preimage (by fun_prop)).inter (isOpen_compact_open_subgroup g)) ⟨?_, ?_⟩ ?_
      · show ind _ _ (g⁻¹ * 1 * g) f.1 = f.1
        rw [mul_one, inv_mul_cancel, map_one]; rfl
      · show (1 : GL (Fin (d + d)) k) ∈ K1 g
        exact ⟨one_mem _, by simp⟩
      rintro w ⟨hu1, hu2⟩
      apply Subtype.ext
      funext y
      show (if cc g (y * w) = v then f.1.1 (y * w * g) else 0) = (if cc g y = v then f.1.1 (y * g) else 0)
      have hf : f.1.1 (y * g * (g⁻¹ * w * g)) = f.1.1 (y * g) :=
        congrFun (congrArg Subtype.val (show ind _ _ (g⁻¹ * w * g) f.1 = f.1 from hu1)) (y * g)
      have e : y * w * g = y * g * (g⁻¹ * w * g) := by group
      rw [cc_right _ _ _ hu2, e, hf]⟩

theorem expo (g : GL (Fin (d + d)) k) (f : IndSp (blk2 d) τ) :
    ∃ (m : ℕ) (r : Fin m → ℝ) (u : Fin m → IndSp (blk2 d) τ),
      ∀ s, F τ s g f = ∑ i, ((Real.exp (r i * s) : ℝ) : ℂ) • u i := by
  apply CompanionTheory.RgGu.NR.Compact.expo

end PositivityTheory.RgGu.NR.Compact

namespace PositivityTheory.RgGu.NR

open PositivityTheory.RgGu.NR.Compact in
theorem compact (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    Compact k := by
  intro d W _ _ τ
  refine ⟨KO k (Fin (d + d)), F τ, GlobalTheory.SplitFlip.isOpen_KO, GlobalTheory.SplitFlip.isCompact_KO, ⟨?_, ?_⟩, ?_⟩
  · intro s x hx
    ext f : 1
    apply Subtype.ext; apply Subtype.ext; funext y
    rw [F_apply, F_apply, hh_mul_right y x hx, smul_smul, smul_smul, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
      ← Real.rpow_add (hh_pos y), ← Real.rpow_add (hh_pos y)]
    simp
  · exact fun g f => expo τ g f
  · intro s
    exact ⟨Representation.Equiv.mk (E τ s) fun g => by
      ext f : 1
      simp [F]⟩

end PositivityTheory.RgGu.NR
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.Compact =====

-- ===== clump member: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SesquilinearFlipConj =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SesquilinearFlipConj", "h": "module\n\npublic import Mathlib.Basic.Complex.Basic\npublic import Mathlib.RepresentationTheory.Basic\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable def UpperTheory.Reformulated.B.SesquilinearFlipConj.HasSesq :
    {G V : Type} → [inst : Group G] → [inst_1 : AddCommGroup V] → [inst_2 : _root_.Module ℂ V] → Representation ℂ G V → Prop :=
    fun {G V : Type} [Group G] [AddCommGroup V] [_root_.Module ℂ V] (π : Representation ℂ G V) ↦
      ∃ (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ),
        B ≠ (0 : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) ∧
          ∀ (g : G) (v w : V),
            ((B : V → V →ₗ⋆[ℂ] ℂ) (((π : G → V →ₗ[ℂ] V) g : V → V) v) : V → ℂ) (((π : G → V →ₗ[ℂ] V) g : V → V) w) =
              ((B : V → V →ₗ⋆[ℂ] ℂ) v : V → ℂ) w

namespace UpperTheory.Reformulated.B.SesquilinearFlipConj.Helpers

private noncomputable def flipConj {V : Type} [AddCommGroup V] [Module ℂ V]
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun v w => starRingEnd ℂ (B w v))
    (by intro v₁ v₂ w; simp [map_add (f := _)])
    (by intro c v w; simp [map_smulₛₗ, smul_eq_mul])
    (by intro v w₁ w₂; simp [map_add (f := _)])
    (by intro c v w; simp [map_smulₛₗ, smul_eq_mul])

private theorem flipConj_apply {V : Type} [AddCommGroup V] [Module ℂ V]
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (v w : V) :
    flipConj B v w = starRingEnd ℂ (B w v) := rfl

end UpperTheory.Reformulated.B.SesquilinearFlipConj.Helpers

open UpperTheory.Reformulated.B.SesquilinearFlipConj.Helpers in
theorem UpperTheory.Reformulated.B.SesquilinearFlipConj.main :
    ∀ {G V : Type} [inst : Group G] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module ℂ V] {ρ : Representation ℂ G V},
      UpperTheory.Reformulated.B.SesquilinearFlipConj.HasSesq ρ →
        ∃ (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ),
          B ≠ (0 : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) ∧
            (∀ (v w : V),
                ((B : V → V →ₗ⋆[ℂ] ℂ) w : V → ℂ) v = (starRingEnd ℂ : ℂ → ℂ) (((B : V → V →ₗ⋆[ℂ] ℂ) v : V → ℂ) w)) ∧
              ∀ (g : G) (v w : V),
                ((B : V → V →ₗ⋆[ℂ] ℂ) (((ρ : G → V →ₗ[ℂ] V) g : V → V) v) : V → ℂ) (((ρ : G → V →ₗ[ℂ] V) g : V → V) w) =
                  ((B : V → V →ₗ⋆[ℂ] ℂ) v : V → ℂ) w := by
  intro G V _ _ _ ρ hS
  obtain ⟨B, hB0, hBinv⟩ := hS
  classical
  by_cases hH : B + flipConj B = 0
  · have hrel : ∀ v w, B v w + starRingEnd ℂ (B w v) = 0 := by
      intro v w
      have := congrArg (fun F : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ => F v w) hH
      simpa [flipConj_apply] using this
    refine ⟨Complex.I • B, ?_, ?_, ?_⟩
    · intro h
      apply hB0
      have : (-Complex.I) • (Complex.I • B) = B := by
        rw [smul_smul]; simp
      rw [← this, h, smul_zero]
    · intro v w
      have h1 := hrel v w
      have h2 : starRingEnd ℂ (B v w) = - B w v := by
        have := congrArg (starRingEnd ℂ) h1
        simp at this
        linear_combination this
      simp only [LinearMap.smul_apply, smul_eq_mul, map_mul, Complex.conj_I, h2]
      ring
    · intro g v w
      simp only [LinearMap.smul_apply, smul_eq_mul, hBinv]
  · refine ⟨B + flipConj B, hH, ?_, ?_⟩
    · intro v w
      simp only [LinearMap.add_apply, flipConj_apply, map_add (f := _), Complex.conj_conj]
      ring
    · intro g v w
      simp only [LinearMap.add_apply, flipConj_apply, hBinv]
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SesquilinearFlipConj =====

-- ===== clump member: Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.ComplementaryOf =====
-- clump-header: {"m": "Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.ComplementaryOf", "h": "module\n\npublic import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.Complementary\npublic import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SesquilinearFlipConj\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil

namespace PositivityTheory.RgGu.NR

namespace Compl

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

theorem irr_sub {ρ : Representation ℂ G V} (h : ρ.IsIrreducible) (W : Submodule ℂ V)
    (hW : ∀ g, ∀ v ∈ W, ρ g v ∈ W) : W = ⊥ ∨ W = ⊤ :=
  (eq_bot_or_eq_top (⟨W, hW⟩ : Subrepresentation ρ)).imp (congrArg Subrepresentation.toSubmodule)
    (congrArg Subrepresentation.toSubmodule)

theorem irr_nontrivial {ρ : Representation ℂ G V} (h : ρ.IsIrreducible) : Nontrivial V := by
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  have : (⊥ : Subrepresentation ρ) = ⊤ := Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _)
  exact bot_ne_top this

def starF {M : Type} [AddCommGroup M] [Module ℂ M] (B : M →ₗ[ℂ] M →ₛₗ[starRingEnd ℂ] ℂ) :
    M →ₗ[ℂ] M →ₛₗ[starRingEnd ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun v w => starRingEnd ℂ (B w v))
    (fun _ _ _ => by simp) (fun _ _ _ => by simp) (fun _ _ _ => by simp) (fun _ _ _ => by simp)

def resF {M : Type} [AddCommGroup M] [Module ℂ M] (B : M →ₗ[ℂ] M →ₛₗ[starRingEnd ℂ] ℂ) (W : Submodule ℂ M) :
    W →ₗ[ℂ] W →ₛₗ[starRingEnd ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun v w => B v w)
    (fun _ _ _ => by simp) (fun _ _ _ => by simp) (fun _ _ _ => by simp) (fun _ _ _ => by simp)

@[simp] theorem resF_apply {M : Type} [AddCommGroup M] [Module ℂ M] (B : M →ₗ[ℂ] M →ₛₗ[starRingEnd ℂ] ℂ)
    (W : Submodule ℂ M) (v w : W) : resF B W v w = B v w := rfl

theorem exists_herm {ρ : Representation ℂ G V} (h : HasSesq ρ) :
    ∃ B : V →ₗ[ℂ] V →ₛₗ[starRingEnd ℂ] ℂ, B ≠ 0 ∧ (∀ v w, B w v = starRingEnd ℂ (B v w)) ∧
      ∀ g v w, B (ρ g v) (ρ g w) = B v w :=
  _root_.UpperTheory.Reformulated.B.SesquilinearFlipConj.main h

def stabG (ρ : Representation ℂ G V) (v : V) : Subgroup G where
  carrier := {g | ρ g v = v}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at *
    rw [map_mul, Module.End.mul_apply, hb, ha]
  one_mem' := by simp
  inv_mem' {a} ha := by
    simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem nondeg {ρ : Representation ℂ G V} (hi : ρ.IsIrreducible) (C : V →ₗ[ℂ] V →ₛₗ[starRingEnd ℂ] ℂ) (hC0 : C ≠ 0)
    (hCi : ∀ g v w, C (ρ g v) (ρ g w) = C v w) (v : V) (hv : v ≠ 0) : ∃ x, C v x ≠ 0 :=
  _root_.CompanionTheory.RgGu.NR.Compl.nondeg hi C hC0 hCi v hv

end Compl

open _root_.PositivityTheory.RgGu.NR.Compl in
theorem complementary_of (h : Signature) : Complementary := by
  intro G V _ _ _ _ _ K₀ hK₀o hK₀c F hF hall h0 s hs
  exact _root_.CompanionTheory.RgGu.NR.complementary_of h G V K₀ hK₀o hK₀c F
    ⟨hF.const, hF.expo⟩ hall h0 s hs


end PositivityTheory.RgGu.NR
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.ComplementaryOf =====

-- ===== clump member: Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.PiTensorTwist =====
-- clump-header: {"m": "Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.PiTensorTwist", "h": "module\n\nimport CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.PiTensorTwist\npublic import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.Complementary\nimport Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton\npublic import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSupercuspidalOfIsCuspidal\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitarizableComplexRepOfSupercuspidalUnitaryCentralCharacter\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitarisableSegmentTwistPrecedesAddOneLe\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRealExponentAbsSmoothCharacterLocalField\npublic import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive\npublic import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitarisableOfSquareIntegrable\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\npublic import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Formalism.ConjugateSelfDual.Statement\nimport ReciprocityTheory.GaloisValuations.GlobalA\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow\nimport Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
  GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.RgGu.NR

namespace Model

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem prodIrr_congr {h N : ℕ} {y z : Fin h → IrrGL (k := k)} (e : y = z) (hy : ∑ a, (y a).1 = N) (hz : ∑ a, (z a).1 = N) :
    Nonempty ((prodIrr y hy).Equiv (prodIrr z hz)) := by
  subst e
  exact ⟨Representation.Equiv.refl _⟩

theorem piTensor_twist (x : IrrGL (k := k)) (s : ℝ) :
    piTensor (fun a : Fin 2 => twist x.rep (detChar (Fin x.1) (absPow k (![-(s : ℂ), (s : ℂ)] a)))) =
      twist (piTensor fun _ : Fin 2 => x.rep) (chi k x.1 s) := by
  ext g : 1
  refine PiTensorProduct.ext (MultilinearMap.ext fun v => ?_)
  have ht : ∀ {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) k) V)
      (χ : GL (Fin n) k →* ℂˣ) (g : GL (Fin n) k), twist ρ χ g = ((χ g : ℂ) • ρ g) := fun _ _ _ => rfl
  have ht2 : ∀ (g : Levi k fun _ : Fin 2 => Fin x.1), twist (piTensor fun _ : Fin 2 => x.rep) (chi k x.1 s) g =
      ((chi k x.1 s g : ℂ) • (piTensor fun _ : Fin 2 => x.rep) g) := fun _ => rfl
  simp only [LinearMap.compMultilinearMap_apply, piTensor_tprod, ht, ht2, LinearMap.smul_apply]
  rw [MultilinearMap.map_smul_univ]
  congr 1
  simp [chi, Fin.prod_univ_two, Units.val_mul]

end Model

open Model in
theorem prodModel (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    ProdModel k := by
  apply CompanionTheory.RgGu.NR.prodModel

theorem cuspUnit (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    CuspUnit k := by
  apply CompanionTheory.RgGu.NR.cuspUnit

end PositivityTheory.RgGu.NR

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.PiTensorTwist =====

-- ===== clump member: Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.PosMkIff =====
-- clump-header: {"m": "Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.PosMkIff", "h": "module\n\nimport CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.PosMkIff\npublic import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.Complementary\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\npublic import Mathlib.LinearAlgebra.Eigenspace.Triangularizable\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Coalgebra.IsFrobenius\nimport Mathlib.RingTheory.HopfAlgebra.Basic\nimport Mathlib.RingTheory.PiTensorProduct\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Filter Topology Module

namespace PositivityTheory.RgGu.NR.Sig

def qf {n : ℕ} (M : Fin n → Fin n → ℂ) (x y : Fin n → ℂ) : ℂ := ∑ i, ∑ j, x i * (star (y j) * M i j)

theorem cont_qf {n : ℕ} :
    Continuous fun p : (Fin n → Fin n → ℂ) × (Fin n → ℂ) × (Fin n → ℂ) => qf p.1 p.2.1 p.2.2 := by
  unfold qf
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact ((continuous_apply i).comp (continuous_fst.comp continuous_snd)).mul
    ((continuous_star.comp ((continuous_apply j).comp (continuous_snd.comp continuous_snd))).mul
      ((continuous_apply j).comp ((continuous_apply i).comp continuous_fst)))

theorem qf_smul {n : ℕ} (M : Fin n → Fin n → ℂ) (a : ℂ) (x y : Fin n → ℂ) :
    qf M (a • x) (a • y) = a * star a * qf M x y := by
  simp only [qf, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem qf_single {n : ℕ} (M : Fin n → Fin n → ℂ) (i j : Fin n) :
    qf M (Pi.single i 1) (Pi.single j 1) = M i j := by
  classical
  simp [qf, Pi.single_apply]

variable {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

abbrev Sq (W : Type) [AddCommGroup W] [Module ℂ W] := W →ₗ[ℂ] W →ₛₗ[starRingEnd ℂ] ℂ

abbrev ef (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] :
    W ≃ₗ[ℂ] (Fin (finrank ℂ W) → ℂ) := (Module.finBasis ℂ W).equivFun

def gram (B : Sq W) : Fin (finrank ℂ W) → Fin (finrank ℂ W) → ℂ :=
  fun i j => B (Module.finBasis ℂ W i) (Module.finBasis ℂ W j)

def mk (M : Fin (finrank ℂ W) → Fin (finrank ℂ W) → ℂ) : Sq W :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun v w => qf M (ef W v) (ef W w))
    (fun v v' w => by simp only [qf, map_add (f := _), Pi.add_apply, add_mul, Finset.sum_add_distrib])
    (fun c v w => by
      simp only [qf, map_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)
    (fun v w w' => by
      simp only [qf, map_add (f := _), Pi.add_apply, star_add, add_mul, mul_add, Finset.sum_add_distrib])
    (fun c v w => by
      simp only [qf, map_smul, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum, starRingEnd_apply]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)

theorem mk_apply (M : Fin (finrank ℂ W) → Fin (finrank ℂ W) → ℂ) (v w : W) :
    mk M v w = qf M (ef W v) (ef W w) := rfl

theorem expand (B : Sq W) (v w : W) : B v w = qf (gram B) (ef W v) (ef W w) := by
  conv_lhs => rw [← (Module.finBasis ℂ W).sum_equivFun v, ← (Module.finBasis ℂ W).sum_equivFun w]

  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul,
  qf, gram, starRingEnd_apply, Finset.mul_sum, ef]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem mk_gram (B : Sq W) : mk (gram B) = B := by
  ext v w
  rw [mk_apply, expand]

theorem gram_mk (M : Fin (finrank ℂ W) → Fin (finrank ℂ W) → ℂ) : gram (mk M : Sq W) = M := by
  funext i j
  have h : ∀ a, (Module.finBasis ℂ W).equivFun (Module.finBasis ℂ W a) = Pi.single a 1 := fun a => by
    funext b
    rw [Module.Basis.equivFun_self]
    simp [Pi.single_apply, eq_comm]
  simp only [gram, mk_apply, ef, h]
  exact qf_single M i j

theorem gram_smul (c : ℂ) (B : Sq W) : gram (c • B) = c • gram B := by
  funext i j
  simp [gram]

section Fam

variable {I : Type} (ι : I → I) (T : I → Module.End ℂ W)

def Inv (B : Sq W) : Prop := ∀ i v w, B (T i v) w = B v (T (ι i) w)

def Herm (B : Sq W) : Prop := ∀ v w, B w v = starRingEnd ℂ (B v w)

def Pos (B : Sq W) : Prop := ∀ v, v ≠ 0 → 0 < (B v v).re

variable {ι T}

theorem ker_bot (hsim : ∀ U : Submodule ℂ W, (∀ i, ∀ w ∈ U, T i w ∈ U) → U = ⊥ ∨ U = ⊤) (B : Sq W) (hB : B ≠ 0)
    (hinv : Inv ι T B) : LinearMap.ker B = ⊥ := by
  have hst : ∀ i, ∀ w ∈ LinearMap.ker B, T i w ∈ LinearMap.ker B := by
    intro i w hw
    rw [LinearMap.mem_ker] at hw ⊢
    ext u
    rw [hinv, hw]
    rfl
  rcases hsim (LinearMap.ker B) hst with h | h
  · exact h
  · exact absurd (LinearMap.ker_eq_top.1 h) hB

theorem inv_sub {B B' : Sq W} (h : Inv ι T B) (h' : Inv ι T B') (c : ℂ) : Inv ι T (B - c • B') := by
  intro i v w
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, h i v w, h' i v w]

theorem uniq (hsim : ∀ U : Submodule ℂ W, (∀ i, ∀ w ∈ U, T i w ∈ U) → U = ⊥ ∨ U = ⊤) (B₀ B : Sq W) (h0 : B₀ ≠ 0)
    (hinv0 : Inv ι T B₀) (hinv : Inv ι T B) : ∃ c : ℂ, B = c • B₀ := by
  apply CompanionTheory.RgGu.NR.Sig.uniq <;> assumption

theorem real_of {B₀ B : Sq W} (h0 : B₀ ≠ 0) (hh0 : Herm B₀) (hh : Herm B) (c : ℂ) (hc : B = c • B₀) :
    starRingEnd ℂ c = c := by
  obtain ⟨v, w, hvw⟩ : ∃ v w, B₀ v w ≠ 0 := by
    by_contra hn
    push Not at hn
    exact h0 (by ext v w; simp [hn])
  have e1 := hh v w
  rw [hc] at e1
  simp only [LinearMap.smul_apply, smul_eq_mul, map_mul, hh0 v w] at e1
  have hz : starRingEnd ℂ (B₀ v w) ≠ 0 := (map_ne_zero _).2 hvw
  exact (mul_right_cancel₀ hz e1).symm

theorem pos_of (B : Sq W) (hh : Herm B) (hk : LinearMap.ker B = ⊥) (hsd : ∀ v, 0 ≤ (B v v).re) : Pos B := by
  apply CompanionTheory.RgGu.NR.Sig.pos_of <;> assumption

end Fam

theorem pos_mk_iff (M : Fin (finrank ℂ W) → Fin (finrank ℂ W) → ℂ) :
    (∀ v : W, v ≠ 0 → 0 < ((mk M : Sq W) v v).re) ↔ ∀ c, c ≠ 0 → 0 < (qf M c c).re := by
  constructor
  · intro h c hc
    have := h ((ef W).symm c) (((ef W).symm.map_ne_zero_iff).2 hc)
    rwa [mk_apply, LinearEquiv.apply_symm_apply] at this
  · intro h v hv
    rw [mk_apply]
    exact h _ ((LinearEquiv.map_ne_zero_iff _).2 hv)

theorem pos_open {n : ℕ} (M : Fin n → Fin n → ℂ) (hM : ∀ c : Fin n → ℂ, c ≠ 0 → 0 < (qf M c c).re) :
    ∀ᶠ M' in 𝓝 M, ∀ c : Fin n → ℂ, c ≠ 0 → 0 < (qf M' c c).re := by
  apply CompanionTheory.RgGu.NR.Sig.pos_open <;> assumption

theorem mk_smul (a : ℂ) (M : Fin (finrank ℂ W) → Fin (finrank ℂ W) → ℂ) : (mk (a • M) : Sq W) = a • mk M := by
  ext v w
  simp only [mk_apply, qf, Pi.smul_apply, smul_eq_mul, LinearMap.smul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

section Real

variable {I : Type} {ι : I → I} {T : I → Module.End ℂ W}

omit [FiniteDimensional ℂ W] in
theorem herm_smul {B : Sq W} (h : Herm B) (r : ℝ) : Herm ((r : ℂ) • B) := by
  intro v w
  simp only [LinearMap.smul_apply, smul_eq_mul, map_mul, Complex.conj_ofReal, h v w]

omit [FiniteDimensional ℂ W] in
theorem inv_smul {B : Sq W} (h : Inv ι T B) (c : ℂ) : Inv ι T (c • B) := by
  intro i v w
  simp only [LinearMap.smul_apply, h i v w]

theorem normalize (B : Sq W) (hB : B ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ‖gram ((r : ℂ) • B)‖ = 1 := by
  have hg : gram B ≠ 0 := by
    intro h
    apply hB
    rw [← mk_gram B, h]
    ext v w
    simp [mk_apply, qf]
  refine ⟨‖gram B‖⁻¹, inv_pos.2 (norm_pos_iff.2 hg), ?_⟩
  rw [gram_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (norm_pos_iff.2 hg)),
    inv_mul_cancel₀ (norm_ne_zero_iff.2 hg)]

end Real


theorem lim_form {I : Type} (ι : I → I) (T : ℝ → I → Module.End ℂ W)
    (hc : ∀ (i : I) (w : W) (l : Module.Dual ℂ W), Continuous fun s => l (T s i w))
    (s : ℕ → ℝ) (p : ℝ) (hs : Tendsto s atTop (𝓝 p)) (B : ℕ → Sq W) (hinv : ∀ k, Inv ι (T (s k)) (B k))
    (hh : ∀ k, Herm (B k)) (hn : ∀ k, ‖gram (B k)‖ = 1) :
    ∃ (φ : ℕ → ℕ) (M : Fin (finrank ℂ W) → Fin (finrank ℂ W) → ℂ), StrictMono φ ∧ ‖M‖ = 1 ∧
      Tendsto (fun k => gram (B (φ k))) atTop (𝓝 M) ∧ Inv ι (T p) (mk M) ∧ Herm (mk M) ∧
      ∀ v w, Tendsto (fun k => B (φ k) v w) atTop (𝓝 (mk M v w)) := by
  apply CompanionTheory.RgGu.NR.Sig.lim_form <;> assumption

end PositivityTheory.RgGu.NR.Sig

namespace PositivityTheory.RgGu.NR

open Sig


theorem signature : Signature := by
  apply CompanionTheory.RgGu.NR.signature

end PositivityTheory.RgGu.NR
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.PosMkIff =====

-- ===== clump member: Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.RhoNuRhoOfC =====
-- clump-header: {"m": "Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.RhoNuRhoOfC", "h": "module\n\nimport CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.RhoNuRhoOfC\npublic import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.Complementary\npublic import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.HasFiniteLengthJacSub\npublic import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspLinesIrr\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.Published

namespace PositivityTheory.RgGu.NR

namespace RedC

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem irr_congr {h N : ℕ} {x x' : Fin h → IrrGL (k := k)} (e : x = x') (hd : ∑ a, (x a).1 = N) :
    ∃ hd' : ∑ a, (x' a).1 = N, ((prodIrr x hd).IsIrreducible ↔ (prodIrr x' hd').IsIrreducible) := by
  subst e
  exact ⟨hd, Iff.rfl⟩

theorem irr_tw {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) (s : ℂ)
    (hi : (prodIrr x hd).IsIrreducible) : (prodIrr (fun a => (x a).nu s) hd).IsIrreducible :=
  GlobalTheory.Parabolic.isIrreducible_of_equiv (prodIrrTwistEquiv x hd (absPow k s) (isSmoothChar_absPow s))
    (isIrreducible_twist hi _)

end RedC

open RedC in

theorem redCl_ofC (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (h1 : SomeRed k) (h2 : CuspUnit k) (h3 : GlobalTheory.BZSeg.CuspPairIrr k) : RedCl k := by
  apply CompanionTheory.RgGu.NR.redCl_ofC <;> assumption

theorem rhoNuRho_ofC (h : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    RedCl k) : PositivityTheory.Pf1.SegRepC.SegTwo.RhoNuRhoReducible :=
  _root_.CompanionTheory.RgGu.NR.rhoNuRho_ofC h

end PositivityTheory.RgGu.NR
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.RhoNuRhoOfC =====

-- ===== clump member: Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SomeRed =====
-- clump-header: {"m": "Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SomeRed", "h": "module\n\npublic import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.Complementary\nimport Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentralExponentBoundOver\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantModulus\npublic import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothIterPhi\nimport GroundTheory.LocalFields.PadicLogSeries\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil

namespace PositivityTheory.RgGu.NR

namespace SomeRed

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem intw {π : Representation ℂ G V} {σ : Representation ℂ G W} (E : π.Equiv σ) (g : G) (v : V) :
    E.toLinearEquiv (π g v) = σ g (E.toLinearEquiv v) :=
  Representation.IntertwiningMap.isIntertwining _ _ E.toIntertwiningMap g v

theorem intw' {π : Representation ℂ G V} {σ : Representation ℂ G W} (E : π.Equiv σ) (g : G) (v : V) :
    E.toIntertwiningMap.toLinearMap (π g v) = σ g (E.toIntertwiningMap.toLinearMap v) :=
  Representation.IntertwiningMap.isIntertwining _ _ E.toIntertwiningMap g v

theorem intw_symm {π : Representation ℂ G V} {σ : Representation ℂ G W} (E : π.Equiv σ) (g : G) (w : W) :
    E.toLinearEquiv.symm (σ g w) = π g (E.toLinearEquiv.symm w) := by
  apply E.toLinearEquiv.injective
  rw [intw E, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

theorem smooth_of_equiv [TopologicalSpace G] {π : Representation ℂ G V} {σ : Representation ℂ G W} (E : π.Equiv σ)
    (h : IsSmooth π) : IsSmooth σ := by
  intro w
  have e : {g : G | σ g w = w} = {g : G | π g (E.toLinearEquiv.symm w) = E.toLinearEquiv.symm w} := by
    ext g
    simp only [Set.mem_setOf_eq]
    rw [← intw_symm E]
    exact ⟨fun h => by rw [h], fun h => E.toLinearEquiv.symm.injective h⟩
  rw [e]
  exact h _

theorem admissible_of_equiv [TopologicalSpace G] {π : Representation ℂ G V} {σ : Representation ℂ G W} (E : π.Equiv σ)
    (h : IsAdmissible π) : IsAdmissible σ := by
  refine ⟨smooth_of_equiv E h.1, fun K hK hc => ?_⟩
  haveI := h.2 K hK hc
  have hle : fixed σ K ≤ (fixed π K).map E.toLinearEquiv.toLinearMap := by
    intro w hw
    refine ⟨E.toLinearEquiv.symm w, ?_, E.toLinearEquiv.apply_symm_apply w⟩
    intro x
    have hx := hw x
    show π (x : G) (E.toLinearEquiv.symm w) = _
    rw [← intw_symm E]
    simp only [MonoidHom.one_apply, Units.val_one, one_smul] at hx ⊢
    rw [hx]
  exact Submodule.finiteDimensional_of_le hle

theorem sesq_of_equiv {π : Representation ℂ G V} {σ : Representation ℂ G W} (E : π.Equiv σ) (h : HasSesq σ) :
    HasSesq π :=
  _root_.CompanionTheory.RgGu.NR.SomeRed.sesq_of_equiv E h

theorem unit_of_equiv {π : Representation ℂ G V} {σ : Representation ℂ G W} (E : π.Equiv σ) (h : IsUnitarisable π) :
    IsUnitarisable σ :=
  GlobalTheory.GenericUnitary.isUnitarisable_of_equiv E h

theorem irr_of_equiv {π : Representation ℂ G V} {σ : Representation ℂ G W} (E : π.Equiv σ) (h : π.IsIrreducible) :
    σ.IsIrreducible :=
  GlobalTheory.Parabolic.isIrreducible_of_equiv E h

theorem unit_twist {ρ : Representation ℂ G V} (h : IsUnitarisable ρ) (χ : G →* ℂˣ) (hχ : ∀ g, ‖(χ g : ℂ)‖ = 1) :
    IsUnitarisable (twist ρ χ) := by
  obtain ⟨B, h1, h2, h3⟩ := h
  refine ⟨B, h1, h2, fun g v w => ?_⟩
  show B ((χ g : ℂ) • ρ g v) ((χ g : ℂ) • ρ g w) = B v w
  rw [B.map_smul, LinearMap.smul_apply, (B _).map_smulₛₗ, h3, smul_eq_mul, smul_eq_mul, ← mul_assoc,
    Complex.mul_conj', hχ g]
  simp

end SomeRed

open SomeRed

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem chi_apply (d : ℕ) (s : ℝ) (g : Levi k fun _ : Fin 2 => Fin d) :
    (chi k d s g : ℂ) = ((nabs k (Matrix.GeneralLinearGroup.det (g 0)) : ℝ) : ℂ) ^ (-(s : ℂ)) *
      ((nabs k (Matrix.GeneralLinearGroup.det (g 1)) : ℝ) : ℂ) ^ (s : ℂ) := by
  simp [chi, val_absPow]

theorem norm_chi (d : ℕ) (s : ℝ) (g : Levi k fun _ : Fin 2 => Fin d) :
    ‖(chi k d s g : ℂ)‖ = nabs k (Matrix.GeneralLinearGroup.det (g 0)) ^ (-s) *
      nabs k (Matrix.GeneralLinearGroup.det (g 1)) ^ s := by
  rw [chi_apply, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (nabs_pos' k _),
    Complex.norm_cpow_eq_rpow_re_of_pos (nabs_pos' k _)]
  simp


theorem someRed_of (h1 : Complementary) (h2 : Compact k) (h3 : Bound k) (h4 : Herm k) (h5 : ProdModel k) :
    SomeRed k := by
  have hComplementary : _root_.CompanionTheory.RgGu.NR.Complementary := by
    intro G V _ _ _ _ _ K₀ hK₀o hK₀c F hF hall h0 s hs
    exact h1 G V K₀ hK₀o hK₀c F ⟨hF.const, hF.expo⟩ hall h0 s hs
  have hCompact : _root_.CompanionTheory.RgGu.NR.Compact k := by
    intro d W _ _ τ
    obtain ⟨K₀, F, hK₀o, hK₀c, hF, hEquiv⟩ := h2 d W τ
    exact ⟨K₀, F, hK₀o, hK₀c, ⟨hF.const, hF.expo⟩, hEquiv⟩
  exact _root_.CompanionTheory.RgGu.NR.someRed_of k hComplementary hCompact h3 h4 h5


end PositivityTheory.RgGu.NR

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SomeRed =====

-- ===== clump member: Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.ThetaContra =====
-- clump-header: {"m": "Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.ThetaContra", "h": "module\n\npublic import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.Complementary\npublic import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.GKLocal\npublic import GroundTheory.LocalFields.PadicLogSeries\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassTwistNeg\npublic import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet\npublic import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsSocleOfOrderFree\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalLanglandsOfIrreducibleAdmissible\npublic import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm\nimport Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductTransposeInverseDualReverse\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil Zc Zc.Cos

namespace PositivityTheory.RgGu.NR

namespace HermB

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nontriv {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (h : ρ.IsIrreducible) : Nontrivial V := by
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  have hne : (⊥ : Subrepresentation ρ) ≠ ⊤ := bot_ne_top
  exact hne (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))

alias congrProd := _root_.GlobalTheory.CompanionTheory.LSocle.prodIrr_congr

def yy (x : IrrGL (k := k)) (s : ℝ) : Fin 2 → IrrGL (k := k) := ![x.nu (-(s : ℂ)), x.nu (s : ℂ)]

theorem eqv {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (e : ρ.Equiv σ) (g : G) (v : V) :
    e (ρ g v) = σ g (e v) :=
  Representation.IntertwiningMap.isIntertwining ρ σ e.toIntertwiningMap g v

theorem theta_contra (hGK : GKLocal k) {N : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (GL (Fin N) k) W) (hs : IsSmooth π) (hi : π.IsIrreducible) :
    Nonempty (Representation.Equiv (π.comp (thetaW k N)) (contra π)) := by
  have E := GlobalTheory.CompanionTheory.LSocle.equiv_contra_comp_thetaW hGK (π.comp (thetaW k N))
    (by rw [GlobalTheory.CompanionTheory.LSocle.comp_thetaW_thetaW π]; exact hs) (by rw [GlobalTheory.CompanionTheory.LSocle.comp_thetaW_thetaW π]; exact hi)
  rwa [GlobalTheory.CompanionTheory.LSocle.comp_thetaW_thetaW π] at E

theorem hasSesq_of {G V V₁ V₂ : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V]
    [Module ℂ V] [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂] (π : Representation ℂ G V)
    (π₁ : Representation ℂ G V₁) (π₂ : Representation ℂ G V₂) (hi : π.IsIrreducible) (e₁ : π.Equiv π₁)
    (hc : ConjEquiv π₁ π₂) (e₂ : π₂.Equiv (contra π)) : HasSesq π :=
  _root_.CompanionTheory.RgGu.NR.HermB.hasSesq_of π π₁ π₂ hi e₁ hc e₂

end HermB


open HermB in
theorem herm_ofB (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (h1 : ConjProd k) (h2 : ConjDual k) : Herm k := by
  intro x hxu s N hd hirr
  have hA := PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  have hGK : GKLocal k := _root_.GlobalTheory.CompanionTheory.GKLocalProof.gkLocal hA
  change HasSesq (prodIrr (yy x s) hd)
  change (prodIrr (yy x s) hd).IsIrreducible at hirr

  obtain ⟨E5⟩ := theta_contra hGK (prodIrr (yy x s) hd) (isSmooth_prodIrr _ _) hirr
  obtain ⟨hd', ⟨E4⟩⟩ := _root_.GlobalTheory.CompanionTheory.ThetaProd.prodIrr_comp_thetaW (k := k) (h := 2) (N := N) hA hGK (yy x s) hd

  let c : Fin 2 → ℝ := ![-s, s]
  have hM : ∑ _a : Fin 2, x.1 = N := by
    rw [← hd, Fin.sum_univ_two, Fin.sum_univ_two]; rfl
  let χ : Fin 2 → kˣ →* ℂˣ := fun a => absPow k ((c a : ℝ) : ℂ)
  have hχ : ∀ a, IsSmoothChar (χ a) := fun a => isSmoothChar_absPow _
  let πs : Fin 2 → Representation ℂ (GL (Fin x.1) k) x.2.rep.V := fun a => twist x.rep (detChar (Fin x.1) (χ a))
  let σs : Fin 2 → Representation ℂ (GL (Fin x.1) k) (smoothPart x.rep.dual) :=
    fun a => twist (contra x.rep) (detChar (Fin x.1) (χ a))
  have hsπ : ∀ a, IsSmooth (πs a) := fun a => isSmooth_twist x.2.rep.smooth (hχ a).detChar
  have hiπ : ∀ a, (πs a).IsIrreducible := fun a => isIrreducible_twist x.2.rep.irr _
  have hic : (contra x.rep).IsIrreducible :=
    GlobalTheory.CompanionTheory.ZcDual.isIrreducible_contra hA _ x.2.rep.smooth x.2.rep.irr
  have hsσ : ∀ a, IsSmooth (σs a) := fun a => isSmooth_twist (isSmooth_contra _) (hχ a).detChar
  have hiσ : ∀ a, (σs a).IsIrreducible := fun a => isIrreducible_twist hic _
  have hcj := h1 2 N (fun _ => x.1) hM (fun _ => x.2.rep.V) (fun _ => smoothPart x.rep.dual) πs σs
    (fun a => h2 x.1 x.2.rep.V x.rep x.2.rep.smooth x.2.rep.irr hxu (c a))
  have E1 := prodIrrEquiv hM πs hsπ hiπ
  have E2 := prodIrrEquiv hM σs hsσ hiσ
  have e0 : ((-s : ℝ) : ℂ) = -(s : ℂ) := by push_cast; ring
  have keyπ : ∀ (t : kˣ →* ℂˣ) (ht : IsSmoothChar t),
      IrrGL.of (twist x.rep (detChar (Fin x.1) t)) (isSmooth_twist x.2.rep.smooth ht.detChar)
        (isIrreducible_twist x.2.rep.irr _) = x.tw t ht := by
    intro t ht
    have := IrrGL.tw_of x.rep x.2.rep.smooth x.2.rep.irr t ht
    rw [IrrGL.of_rep] at this
    exact this.symm
  have keyσ : ∀ (t : kˣ →* ℂˣ) (ht : IsSmoothChar t),
      IrrGL.of (twist (contra x.rep) (detChar (Fin x.1) t)) (isSmooth_twist (isSmooth_contra _) ht.detChar)
        (isIrreducible_twist hic _) = (dualCl x).tw t ht := by
    intro t ht
    have := IrrGL.tw_of (contra x.rep) (isSmooth_contra _) hic t ht
    rw [← GlobalTheory.CompanionTheory.ZcDual.dualCl_eq hA x] at this
    exact this.symm
  have fπ : (fun a => IrrGL.of (πs a) (hsπ a) (hiπ a)) = yy x s := by
    funext a
    rw [keyπ _ (hχ a)]
    fin_cases a
    · show x.tw (absPow k ((-s : ℝ) : ℂ)) _ = x.nu (-(s : ℂ))
      simp only [IrrGL.nu, e0]
    · rfl
  have fσ : (fun a => IrrGL.of (σs a) (hsσ a) (hiσ a)) = fun a => dualCl (yy x s (Fin.rev a)) := by
    funext a
    rw [keyσ _ (hχ a)]
    fin_cases a
    · show (dualCl x).tw (absPow k ((-s : ℝ) : ℂ)) _ = dualCl (x.nu (s : ℂ))
      rw [_root_.GlobalTheory.CompanionTheory.ZcDual.dualCl_nu hA x (s : ℂ)]
      simp only [IrrGL.nu, e0]
    · show (dualCl x).tw (absPow k ((s : ℝ) : ℂ)) _ = dualCl (x.nu (-(s : ℂ)))
      rw [_root_.GlobalTheory.CompanionTheory.ZcDual.dualCl_nu hA x (-(s : ℂ)), neg_neg]
      rfl
  obtain ⟨E0⟩ := congrProd fπ.symm hd hM
  obtain ⟨E3⟩ := congrProd fσ hM hd'
  exact hasSesq_of _ _ _ hirr (E0.trans E1.symm) hcj ((E2.trans E3).trans (E4.symm.trans E5))

end PositivityTheory.RgGu.NR

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.ThetaContra =====

-- ===== clump member: Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.RhoNuRhoReducibleC =====
-- clump-header: {"m": "Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.RhoNuRhoReducibleC", "h": "module\n\npublic import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.Complementary\npublic import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.HasFiniteLengthJacSub\npublic import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.BoundB\npublic import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.Compact\npublic import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.ComplementaryOf\npublic import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.ConjDual\npublic import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.ConjProd\npublic import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.CuspPairIrr\npublic import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.PiTensorTwist\npublic import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.PosMkIff\npublic import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.RhoNuRhoOfC\npublic import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SomeRed\npublic import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.ThetaContra\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

namespace PositivityTheory.RgGu.NR

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem redClC : RedCl k :=
  redCl_ofC k (someRed_of k (complementary_of signature) (compact k) (boundB k) (herm_ofB k (conjProd k) (conjDual k))
    (prodModel k)) (cuspUnit k) (cuspPairIrr k)

theorem rhoNuRhoReducibleC : PositivityTheory.Pf1.SegRepC.SegTwo.RhoNuRhoReducible := rhoNuRho_ofC fun k _ _ _ _ => redClC k

end PositivityTheory.RgGu.NR
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.RhoNuRhoReducibleC =====
