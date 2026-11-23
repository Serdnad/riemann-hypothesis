module

public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Formalism.LocalRingCardinality.DataHost
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle403
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle424
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle418
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ValRPullbackTwistingSheafTransition
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.MapAcrFromBase
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle421
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsCompactOperatorOfIsHilbertSchmidt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr

@[expose] public section

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.IwaAd

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

theorem holValueAt_finset_sum {ι : Type*} (T : Finset ι) {f : ι → ℂ → ℂ} {c : ι → ℂ} {s₀ : ℂ}
    (a : ∀ i ∈ T, HolValueAt (f i) s₀ (c i)) :
    HolValueAt (fun z => ∑ i ∈ T, f i z) s₀ (∑ i ∈ T, c i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using holValueAt_const 0 s₀
  | insert i T hi ih =>
    have h := (a i (Finset.mem_insert_self i T)).add
      (ih fun j hj => a j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.sum_insert hi] using h

end GlobalTheory.CompanionTheory.IwaAd

end
end

section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

theorem _root_.GlobalTheory.T.exists_nonneg_test_function_near_one : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (N : Set (GL (Fin a) (Cinf E))), N ∈ 𝓝 1 → ∃ β₀ : Lie E a → ℝ, 0 ≤ β₀ ∧ 0 < β₀ (oneL E a) ∧ IsTest (fun x => (β₀ x : ℂ)) ∧ ConjInv (fun x => (β₀ x : ℂ)) ∧ ∀ x, β₀ x ≠ 0 → ∃ y ∈ N, toL y.val = x := by
  first | exact @GlobalTheory.CompanionTheory.SmoothRep.exists_bump_conjInv | exact GlobalTheory.CompanionTheory.SmoothRep.exists_bump_conjInv | (intros; apply GlobalTheory.CompanionTheory.SmoothRep.exists_bump_conjInv <;> assumption)
end

section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

theorem _root_.GlobalTheory.T.test_function_derivative_is_test : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (β : Lie E a → ℂ), IsTest β → ∀ X : Lie E a, IsTest (dTest X β) := by
  first | exact @GlobalTheory.CompanionTheory.SmoothRep.isTest_dTest | exact GlobalTheory.CompanionTheory.SmoothRep.isTest_dTest | (intros; apply GlobalTheory.CompanionTheory.SmoothRep.isTest_dTest <;> assumption)
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict

theorem exists_isUnder_of_cxPt (m : ℕ) (n : Fin (m + 1) → ℕ) (y : CxPts (mpStr ℤ m n) σ₀) :
    ∃ z : (Σ k, Bk n k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) ∧ IsUnder y z := by
  have hc : ∀ k, ∃ i, y ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k i) := fun k =>
    ⟨ptChart _ k, CxPts.mem_ptsIn.2 (mem_ptChart _ k)⟩
  choose c hc using hc
  let z : (Σ k, Bk n k) → ℂ := fun p =>
    CxPts.ev (mpStr ℤ m n) σ₀ (blockChart n p.1 (c p.1)) (pullRatio (prB n p.1) _ (c p.1) le_rfl p.2) y
  have hz1 : ∀ k, z ⟨k, c k⟩ = 1 := fun k => by
    change CxPts.ev (mpStr ℤ m n) σ₀ (blockChart n k (c k)) (pullRatio (prB n k) _ (c k) le_rfl (c k)) y = 1
    rw [pullRatio_self, CxPts.ev_eq (hc k), map_one]
  refine ⟨z, fun k => ⟨c k, by rw [hz1]; exact one_ne_zero⟩, fun k i => ?_⟩
  have hmem : y ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k i) ↔ z ⟨k, i⟩ ≠ 0 := by
    have e := CxPts.mem_ptsIn_basicOpen (hc k) (pullRatio (prB n k) _ (c k) le_rfl i)
    rw [basicOpen_pullRatio, CxPts.mem_ptsIn_inf] at e
    exact ⟨fun h => e.1 ⟨hc k, h⟩, fun h => (e.2 h).2⟩
  refine ⟨hmem, fun j hi => ?_⟩
  have hW : y ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k (c k) ⊓ blockChart n k i) :=
    CxPts.mem_ptsIn_inf.2 ⟨hc k, hi⟩
  have r1 : ∀ l, CxPts.ev (mpStr ℤ m n) σ₀ (blockChart n k (c k) ⊓ blockChart n k i)
      (pullRatio (prB n k) _ (c k) inf_le_left l) y = z ⟨k, l⟩ := fun l => by
    rw [← resG_pullRatio (φ := prB n k) (W := blockChart n k (c k)) (i := c k) (hi := le_rfl) inf_le_left]
    exact CxPts.ev_res inf_le_left hW _
  have r2 : CxPts.ev (mpStr ℤ m n) σ₀ (blockChart n k (c k) ⊓ blockChart n k i)
      (pullRatio (prB n k) _ i inf_le_right j) y =
      CxPts.ev (mpStr ℤ m n) σ₀ (blockChart n k i) (pullRatio (prB n k) _ i le_rfl j) y := by
    rw [← resG_pullRatio (φ := prB n k) (W := blockChart n k i) (i := i) (hi := le_rfl) inf_le_right]
    exact CxPts.ev_res inf_le_right hW _
  have e := congrArg (fun f => CxPts.ev (mpStr ℤ m n) σ₀ (blockChart n k (c k) ⊓ blockChart n k i) f y)
    (pullRatio_mul_pullRatio (φ := prB n k) (W := blockChart n k (c k) ⊓ blockChart n k i) (i := c k) (j := i)
      (k := j) (hi := inf_le_left) (hj := inf_le_right))
  simp only [CxPts.ev_mul, r1, r2] at e
  rw [eq_div_iff (hmem.1 hi), mul_comm]
  exact e

end GlobalTheory.CompanionTheory.MPDict
end
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict.Inhab

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem val_blockUnit {k : Fin (m + 1)} (i j : Bk n k) {W : (MP ℤ m n).Opens}
    (h : W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) i ⊓ chart ℤ (n k) j)) :
    ((blockUnit i j h : Γ(MP ℤ m n, W)ˣ) : Γ(MP ℤ m n, W)) =
      pullRatio (prB n k) W i (h.trans ((prB n k).preimage_mono inf_le_left)) j := by
  rw [← appLE_ratioOn (φ := prB n k) (W := W) (U := chart ℤ (n k) i ⊓ chart ℤ (n k) j)
    (i := i) (j := j) inf_le_left h]
  rfl

theorem blockUnit_mul {k : Fin (m + 1)} (i j l : Bk n k) {W : (MP ℤ m n).Opens}
    (h₁ : W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) i ⊓ chart ℤ (n k) j))
    (h₂ : W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) j ⊓ chart ℤ (n k) l))
    (h₃ : W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) i ⊓ chart ℤ (n k) l)) :
    blockUnit i j h₁ * blockUnit j l h₂ = blockUnit i l h₃ := by
  refine Units.ext ?_
  rw [Units.val_mul, val_blockUnit, val_blockUnit, val_blockUnit]
  exact pullRatio_mul_pullRatio

theorem prod_blockUnit_single {W : (MP ℤ m n).Opens} (k : Fin (m + 1)) (c c' : ∀ k, Bk n k)
    (h : ∀ k', W ≤ prB n k' ⁻¹ᵁ (chart ℤ (n k') (c k') ⊓ chart ℤ (n k') (c' k'))) :
    (∏ k', blockUnit (c k') (c' k') (h k') ^ (Pi.single k (1 : ℤ) : Fin (m + 1) → ℤ) k') =
      blockUnit (c k) (c' k) (h k) := by
  refine (Finset.prod_eq_single k (fun b _ hb => ?_) (fun hk => (hk (Finset.mem_univ _)).elim)).trans ?_
  · rw [Pi.single_eq_of_ne hb, zpow_zero]
  · rw [Pi.single_eq_same, zpow_one]

end GlobalTheory.CompanionTheory.MPDict.Inhab

end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict.Unique

theorem pullRatio_top_eq {N : ℕ} {x x' : Sp ℂ ⟶ PSpace ℤ N} (i j : Fin (N + 1))
    (h : ⊤ ≤ x ⁻¹ᵁ chart ℤ N i) (h' : ⊤ ≤ x' ⁻¹ᵁ chart ℤ N i)
    (e : valR x (chart ℤ N i) (ratio ℤ N i j) = valR x' (chart ℤ N i) (ratio ℤ N i j)) :
    pullRatio x ⊤ i h j = pullRatio x' ⊤ i h' j := by
  rw [valR, valR, dite_eq_left h, dite_eq_left h'] at e
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).1 e

theorem valR_comp_prB {m : ℕ} {n : Fin (m + 1) → ℕ} (x : Sp ℂ ⟶ MP ℤ m n) {k : Fin (m + 1)} (i j : Bk n k)
    (h : ⊤ ≤ x ⁻¹ᵁ blockChart n k i) :
    valR (x ≫ prB n k) (chart ℤ (n k) i) (ratio ℤ (n k) i j) =
      valR x (blockChart n k i) (pullRatio (prB n k) _ i le_rfl j) := by
  have h' : ⊤ ≤ (x ≫ prB n k) ⁻¹ᵁ chart ℤ (n k) i := h
  rw [valR, valR, dite_eq_left h, dite_eq_left h', pullRatio,
    ← Scheme.Hom.appLE_comp_appLE x (prB n k) (chart ℤ (n k) i) (blockChart n k i) ⊤ le_rfl h]
  rfl

end GlobalTheory.CompanionTheory.MPDict.Unique


open GlobalTheory.CompanionTheory.MPDict.Unique in
theorem GlobalTheory.CompanionTheory.MPDict.isUnder_unique : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (z : (Σ k, Bk n k) → ℂ)
    (y y' : CxPts (mpStr ℤ m n) σ₀), IsUnder y z → IsUnder y' z → y = y' := by
  intro m n z y y' h h'
  refine Subtype.ext (GroundTheory.Arith.SchemeCoh.ProjSpace.hom_ext m n _ _ fun k => ?_)
  have hy : y ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k (ptChart (y.1 (IsLocalRing.closedPoint ℂ)) k)) :=
    mem_ptsIn.2 (mem_ptChart _ k)
  obtain ⟨i, hi⟩ : ∃ i, y ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k i) := ⟨_, hy⟩
  have hz : z ⟨k, i⟩ ≠ 0 := ((h k i).1).1 hi
  have hi' : y' ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k i) := ((h' k i).1).2 hz
  refine GlobalTheory.ProjSpace.hom_ext ?_ fun t => ⟨⊤, trivial, i, hi, hi', fun j => ?_⟩
  · have s : pr ℤ m n k ≫ PSpace.str ℤ (n k) = mpStr ℤ m n := pr_toSpecBase ℤ m n k
    rw [Category.assoc, Category.assoc, s, y.2, y'.2]
  · have a : ⊤ ≤ y.1 ⁻¹ᵁ blockChart n k i := hi
    have a' : ⊤ ≤ y'.1 ⁻¹ᵁ blockChart n k i := hi'
    refine pullRatio_top_eq (x := y.1 ≫ prB n k) (x' := y'.1 ≫ prB n k) i j a a' ?_
    rw [valR_comp_prB y.1 i j a, valR_comp_prB y'.1 i j a']
    exact ((h k i).2 j hi).trans ((h' k i).2 j hi').symm
end
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict.TensRep

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem res_blockUnit {k : Fin (m + 1)} (i j : Bk n k) {W W' : (MP ℤ m n).Opens} (h : W' ≤ W)
    (h' : W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) i ⊓ chart ℤ (n k) j)) :
    Semi.res h (blockUnit i j h') = blockUnit i j (h.trans h') :=
  DVR.res_res' _ _ _

def mulUnit {P Q C : (MP ℤ m n).Opens} (u : Γ(MP ℤ m n, P ⊓ C)ˣ) (v : Γ(MP ℤ m n, Q ⊓ C)ˣ) :
    Γ(MP ℤ m n, P ⊓ Q ⊓ C)ˣ :=
  Semi.res (inf_le_inf_right _ inf_le_left) u * Semi.res (inf_le_inf_right _ inf_le_right) v

theorem ev_mulUnit {P Q C : (MP ℤ m n).Opens} (u : Γ(MP ℤ m n, P ⊓ C)ˣ) (v : Γ(MP ℤ m n, Q ⊓ C)ˣ)
    {y : CxPts (mpStr ℤ m n) σ₀} (hy : y ∈ ptsIn (mpStr ℤ m n) σ₀ (P ⊓ Q ⊓ C)) :
    CxPts.ev (mpStr ℤ m n) σ₀ (P ⊓ Q ⊓ C) (mulUnit u v : Γ(MP ℤ m n, P ⊓ Q ⊓ C)ˣ) y =
      CxPts.ev (mpStr ℤ m n) σ₀ (P ⊓ C) (u : Γ(MP ℤ m n, P ⊓ C)) y *
        CxPts.ev (mpStr ℤ m n) σ₀ (Q ⊓ C) (v : Γ(MP ℤ m n, Q ⊓ C)) y := by
  rw [mulUnit, Units.val_mul, CxPts.ev_mul]
  exact congrArg₂ (· * ·) (CxPts.ev_res _ hy _) (CxPts.ev_res _ hy _)

theorem frame_mulUnit {P P' Q Q' C : (MP ℤ m n).Opens} (g : Γ(MP ℤ m n, P ⊓ P')ˣ) (g' : Γ(MP ℤ m n, Q ⊓ Q')ˣ)
    (u : Γ(MP ℤ m n, P ⊓ C)ˣ) (u' : Γ(MP ℤ m n, P' ⊓ C)ˣ) (v : Γ(MP ℤ m n, Q ⊓ C)ˣ) (v' : Γ(MP ℤ m n, Q' ⊓ C)ˣ)
    (a₁ : P ⊓ P' ⊓ C ≤ P' ⊓ C) (a₂ : P ⊓ P' ⊓ C ≤ P ⊓ P') (a₃ : P ⊓ P' ⊓ C ≤ P ⊓ C)
    (b₁ : Q ⊓ Q' ⊓ C ≤ Q' ⊓ C) (b₂ : Q ⊓ Q' ⊓ C ≤ Q ⊓ Q') (b₃ : Q ⊓ Q' ⊓ C ≤ Q ⊓ C)
    (hu : Semi.res a₁ u' = Semi.res a₂ g * Semi.res a₃ u) (hv : Semi.res b₁ v' = Semi.res b₂ g' * Semi.res b₃ v)
    (d₁ : P ⊓ Q ⊓ (P' ⊓ Q') ⊓ C ≤ P' ⊓ Q' ⊓ C) (d₂ : P ⊓ Q ⊓ (P' ⊓ Q') ⊓ C ≤ P ⊓ Q ⊓ (P' ⊓ Q'))
    (d₃ : P ⊓ Q ⊓ (P' ⊓ Q') ⊓ C ≤ P ⊓ Q ⊓ C) (f₁ : P ⊓ Q ⊓ (P' ⊓ Q') ≤ P ⊓ P') (f₂ : P ⊓ Q ⊓ (P' ⊓ Q') ≤ Q ⊓ Q') :
    Semi.res d₁ (mulUnit u' v') = Semi.res d₂ (Semi.res f₁ g * Semi.res f₂ g') * Semi.res d₃ (mulUnit u v) := by
  have l₁ : P ⊓ Q ⊓ (P' ⊓ Q') ⊓ C ≤ P ⊓ P' ⊓ C := inf_le_inf_right _ (inf_le_inf inf_le_left inf_le_left)
  have l₂ : P ⊓ Q ⊓ (P' ⊓ Q') ⊓ C ≤ Q ⊓ Q' ⊓ C := inf_le_inf_right _ (inf_le_inf inf_le_right inf_le_right)
  have e₁ := congrArg (Semi.res l₁) hu
  have e₂ := congrArg (Semi.res l₂) hv
  simp only [map_mul, DVR.res_res'] at e₁ e₂
  simp only [mulUnit, map_mul, DVR.res_res']
  exact (congrArg₂ (· * ·) e₁ e₂).trans (mul_mul_mul_comm _ _ _ _)

theorem mono_mulUnit {P Q : (MP ℤ m n).Opens} {c c' : ∀ k, Bk n k} (a b : Fin (m + 1) → ℤ)
    (u : Γ(MP ℤ m n, P ⊓ mchart c)ˣ) (u' : Γ(MP ℤ m n, P ⊓ mchart c')ˣ)
    (v : Γ(MP ℤ m n, Q ⊓ mchart c)ˣ) (v' : Γ(MP ℤ m n, Q ⊓ mchart c')ˣ)
    (a₁ : P ⊓ (mchart c ⊓ mchart c') ≤ P ⊓ mchart c) (a₂ : P ⊓ (mchart c ⊓ mchart c') ≤ P ⊓ mchart c')
    (b₁ : Q ⊓ (mchart c ⊓ mchart c') ≤ Q ⊓ mchart c) (b₂ : Q ⊓ (mchart c ⊓ mchart c') ≤ Q ⊓ mchart c')
    (ta : ∀ k, P ⊓ (mchart c ⊓ mchart c') ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (c k) ⊓ chart ℤ (n k) (c' k)))
    (tb : ∀ k, Q ⊓ (mchart c ⊓ mchart c') ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (c k) ⊓ chart ℤ (n k) (c' k)))
    (hu : Semi.res a₁ u = Semi.res a₂ u' * ∏ k, blockUnit (c k) (c' k) (ta k) ^ a k)
    (hv : Semi.res b₁ v = Semi.res b₂ v' * ∏ k, blockUnit (c k) (c' k) (tb k) ^ b k)
    (d₁ : P ⊓ Q ⊓ (mchart c ⊓ mchart c') ≤ P ⊓ Q ⊓ mchart c) (d₂ : P ⊓ Q ⊓ (mchart c ⊓ mchart c') ≤ P ⊓ Q ⊓ mchart c')
    (td : ∀ k, P ⊓ Q ⊓ (mchart c ⊓ mchart c') ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (c k) ⊓ chart ℤ (n k) (c' k))) :
    Semi.res d₁ (mulUnit u v) = Semi.res d₂ (mulUnit u' v') * ∏ k, blockUnit (c k) (c' k) (td k) ^ (a k + b k) := by
  have l₁ : P ⊓ Q ⊓ (mchart c ⊓ mchart c') ≤ P ⊓ (mchart c ⊓ mchart c') := inf_le_inf_right _ inf_le_left
  have l₂ : P ⊓ Q ⊓ (mchart c ⊓ mchart c') ≤ Q ⊓ (mchart c ⊓ mchart c') := inf_le_inf_right _ inf_le_right
  have e₁ := congrArg (Semi.res l₁) hu
  have e₂ := congrArg (Semi.res l₂) hv
  simp only [map_mul, map_prod, map_zpow, DVR.res_res'] at e₁ e₂
  simp only [mulUnit, map_mul, DVR.res_res']
  refine ((congrArg₂ (· * ·) e₁ e₂).trans (mul_mul_mul_comm _ _ _ _)).trans (congrArg (HMul.hMul _) ?_)
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [res_blockUnit, res_blockUnit, ← zpow_add]

end GlobalTheory.CompanionTheory.MPDict.TensRep

namespace GlobalTheory.CompanionTheory.MPDict

open TensRep

theorem isHermRep_tens : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (M N : HermLB (mpStr ℤ m n)) (A B : Geo.HermLine (Bk n)),
    IsHermRep M A → IsHermRep N B → IsHermRep (M.tens N) (A.tensor B) := by
  rintro m n M N A B ⟨u, hu₁, hu₂, hu₃⟩ ⟨v, hv₁, hv₂, hv₃⟩
  refine ⟨fun p c => mulUnit (u p.1 c) (v p.2 c), ?_, ?_, ?_⟩
  · rintro ⟨i, i'⟩ ⟨j, j'⟩ c
    exact frame_mulUnit _ _ _ _ _ _ _ _ _ _ _ _ (hu₁ i j c) (hv₁ i' j' c) _ _ _ _ _
  · rintro ⟨i, i'⟩ c c'
    exact mono_mulUnit A.a B.a _ _ _ _ _ _ _ _ _ _ (hu₂ i c c') (hv₂ i' c c') _ _ _
  · rintro ⟨i, i'⟩ c y z hz hy
    have hy' := mem_ptsIn_inf.1 hy
    have h₁ := mem_ptsIn_inf.1 hy'.1
    have e₁ := hu₃ i c y z hz (mem_ptsIn_inf.2 ⟨h₁.1, hy'.2⟩)
    have e₂ := hv₃ i' c y z hz (mem_ptsIn_inf.2 ⟨h₁.2, hy'.2⟩)
    have hz0 : ∀ k, z ⟨k, c k⟩ ≠ 0 := fun k => (hz k (c k)).1.1 (ptsIn_mono (mchart_le c k) hy'.2)
    have hp : ∏ k, ‖z ⟨k, c k⟩‖ ^ (A.a k + B.a k) =
        (∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k) * ∏ k, ‖z ⟨k, c k⟩‖ ^ B.a k := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun k _ => zpow_add₀ (norm_ne_zero_iff.2 (hz0 k)) _ _
    have hev := ev_mulUnit (u i c) (v i' c) hy
    change A.h z * B.h z = (∏ k, ‖z ⟨k, c k⟩‖ ^ (A.a k + B.a k)) *
      ‖CxPts.ev (mpStr ℤ m n) σ₀ (M.B.U i ⊓ N.B.U i' ⊓ mchart c)
        (mulUnit (u i c) (v i' c) : Γ(MP ℤ m n, M.B.U i ⊓ N.B.U i' ⊓ mchart c)ˣ) y‖ *
      Real.exp (((M.φ σ₀).φ i y + (N.φ σ₀).φ i' y) / 2)
    rw [e₁, e₂, hev, hp, norm_mul, add_div, Real.exp_add]
    ring

end GlobalTheory.CompanionTheory.MPDict
end
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict.Under

open GlobalTheory.TuplePoint GlobalTheory.Points

theorem spZ_ext (f g : Sp ℂ ⟶ Sp ℤ) : f = g := by
  rw [← Spec.map_preimage f, ← Spec.map_preimage g]
  congr 1
  ext1
  exact Subsingleton.elim _ _

theorem top_ext {s s' : Γ(Sp ℂ, ⊤)} (h : valR (𝟙 (Sp ℂ)) ⊤ s = valR (𝟙 (Sp ℂ)) ⊤ s') : s = s' :=
  ext_of_dense (𝟙 (Sp ℂ)) fun _ => h

theorem hom_eq_of_val {N : ℕ} {φ ψ : Sp ℂ ⟶ PSpace ℤ N} (i : Fin (N + 1))
    (h₁ : ⊤ ≤ φ ⁻¹ᵁ chart ℤ N i) (h₂ : ⊤ ≤ ψ ⁻¹ᵁ chart ℤ N i)
    (h : ∀ j, valR φ (chart ℤ N i) (ratio ℤ N i j) = valR ψ (chart ℤ N i) (ratio ℤ N i j)) : φ = ψ := by
  refine GlobalTheory.ProjSpace.hom_ext (spZ_ext _ _) fun y => ⟨⊤, trivial, i, h₁, h₂, fun j => top_ext ?_⟩
  have e₁ := valR_appLE (𝟙 (Sp ℂ)) φ h₁ le_rfl (ratio ℤ N i j)
  have e₂ := valR_appLE (𝟙 (Sp ℂ)) ψ h₂ le_rfl (ratio ℤ N i j)
  rw [Category.id_comp] at e₁ e₂
  exact e₁.trans ((h j).trans e₂.symm)

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

abbrev blockVec (z : (Σ k, Bk n k) → ℂ) (k : Fin (m + 1)) : Fin (n k + 1) → ℂ := fun i => z ⟨k, i⟩

theorem blockVec_ne_zero {z : (Σ k, Bk n k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (k : Fin (m + 1)) :
    blockVec z k ≠ 0 := fun h => by
  obtain ⟨i, hi⟩ := hz k
  exact hi (congrFun h i)

theorem isUnder_of_comp {z : (Σ k, Bk n k) → ℂ} (hz : ∀ k, blockVec z k ≠ 0) (y : CxPts (mpStr ℤ m n) σ₀)
    (h : ∀ k, y.1 ≫ prB n k = point ℤ (blockVec z k) (hz k)) : IsUnder y z := fun k i => by
  refine ⟨⟨fun hy => ne_zero_of_le (h k) hy le_rfl, fun hi => le_preimage_chart (h k) hi⟩, fun j hy => ?_⟩
  exact valR_pullRatio (h k) hy le_rfl j

theorem comp_of_isUnder {z : (Σ k, Bk n k) → ℂ} (hz : ∀ k, blockVec z k ≠ 0) (hz' : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    {y : CxPts (mpStr ℤ m n) σ₀} (H : IsUnder y z) (k : Fin (m + 1)) :
    y.1 ≫ prB n k = point ℤ (blockVec z k) (hz k) := by
  obtain ⟨i, hi⟩ := hz' k
  have hy : y ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k i) := ((H k i).1).2 hi
  refine hom_eq_of_val i (le_preimage_comp y.1 _ le_rfl hy)
    ((le_point_preimage_iff (o := ℤ) (ht := hz k) i).2 hi) fun j => ?_
  refine (valR_appLE y.1 (prB n k) le_rfl hy (ratio ℤ (n k) i j)).symm.trans ?_
  exact ((H k i).2 j hy).trans (valR_point_ratio (t := blockVec z k) (ht := hz k) hi j).symm

theorem existsUnique_isUnder (m : ℕ) (n : Fin (m + 1) → ℕ) (z : (Σ k, Bk n k) → ℂ)
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : ∃! y : CxPts (mpStr ℤ m n) σ₀, IsUnder y z := by
  have ht := blockVec_ne_zero hz
  let a : ∀ k, Sp ℂ ⟶ PSpace ℤ (n k) := fun k => point ℤ (blockVec z k) (ht k)
  have ha : ∀ k, a k ≫ toSpecBase ℤ (n k) = spMap σ₀ := fun _ => spZ_ext _ _
  let y : CxPts (mpStr ℤ m n) σ₀ := ⟨lift m n (spMap σ₀) a ha, lift_mpStr m n _ a ha⟩
  have hy : ∀ k, y.1 ≫ prB n k = a k := lift_pr m n _ a ha
  refine ⟨y, isUnder_of_comp ht y hy, fun y' H => Subtype.ext ?_⟩
  exact GroundTheory.Arith.SchemeCoh.ProjSpace.hom_ext m n _ _ fun k =>
    (comp_of_isUnder ht hz H k).trans (hy k).symm

end GlobalTheory.CompanionTheory.MPDict.Under
end
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict

theorem isHermRep_triv : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ), IsHermRep (HermLB.triv (mpStr ℤ m n)) (GlobalTheory.CompanionTheory.Ar.Top.trivLine (Bk n)) := by
  intro m n
  refine ⟨fun _ _ => 1, ?_, ?_, ?_⟩
  · intro i j c
    simp only [map_one, mul_one]
    exact (map_one (Semi.res _)).symm
  · intro i c c'
    simp [GlobalTheory.CompanionTheory.Ar.Top.trivLine]
  · intro i c y z _ hy
    have e : CxPts.ev (mpStr ℤ m n) σ₀ ((HermLB.triv (mpStr ℤ m n)).B.U i ⊓ mchart c)
        (((1 : Γ(MP ℤ m n, (HermLB.triv (mpStr ℤ m n)).B.U i ⊓ mchart c)ˣ)) :
          Γ(MP ℤ m n, (HermLB.triv (mpStr ℤ m n)).B.U i ⊓ mchart c)) y = 1 := by
      rw [CxPts.ev_eq hy, Units.val_one, map_one]
    rw [e]
    simp [GlobalTheory.CompanionTheory.Ar.Top.trivLine, HermLB.triv, Weight.ofFun]

end GlobalTheory.CompanionTheory.MPDict
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

theorem _root_.GlobalTheory.T.period_ring_base_change_from_universal : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ), (∃ π : A.A →+* A.Acr n ⧸ A.PFil n, (∀ a, π a = Ideal.Quotient.mk _ (A.toAcr n (WittVector.teichmuller l a))) ∧ Function.Surjective π ∧ π A.pi = 0 ∧ (n ≠ 0 → RingHom.ker π = Ideal.span {A.pi})) ∧ (∀ r, A.Fil n r = ((base l).Fil n r).map (mapAcr A.fromBase n)) ∧ (∀ k, JJ k A n = (JJ k (base l) n).map (mapAcr A.fromBase n)) ∧ (∀ r, fil (A.pdFil n) r = A.Fil n r) ∧ (∀ k r, fil (DD k A n) r = (fil (DD k (base l) n) r).map (mapAcr A.fromBase n)) ∧ (∀ x ∈ A.PFil n, IsNilpotent x ∧ x ^ l ∈ Ideal.span {(l : A.Acr n)}) ∧ ∀ k, n ≠ 0 → Function.Surjective (uJ k A n) ∧ RingHom.ker (uJ k A n) ≤ (⊥ : Ideal A.U).jacobson := by
  first | exact @GlobalTheory.CompanionTheory.AcrMod.acr_modp | exact GlobalTheory.CompanionTheory.AcrMod.acr_modp | (intros; apply GlobalTheory.CompanionTheory.AcrMod.acr_modp <;> assumption)
end
