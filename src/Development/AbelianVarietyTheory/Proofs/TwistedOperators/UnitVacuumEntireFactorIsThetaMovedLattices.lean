module

public import Mathlib.NumberTheory.NumberField.Basic
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramAtPosDef
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrT
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmAtSmulRight
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ApplyAddInfRat
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HomSymplecticHalfFormAlgebraicLawsContinuousStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalFrameCoordsOfMemTorusLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePointSignEqThetaLawSemicharacter
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualImageOrthonormalFrameLattice
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Formalism.LocalRingCardinality.DataTheta
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDualStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalPointFinitePartIsotropicPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHermitianFormScaledCoordinateEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegerMapEqHalfOneAddSqrt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaLatticeImageRationalHomLattice
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsIsArchimedeanAdeleChartOfRealChart
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelDataX
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImportsLast

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCommonDenominator, Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualLatticeResolutionOfIdentity, Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualLatticeResolutionOfIdentityStatement, Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitVacuumEntireFactorIsThetaMovedLattices

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCommonDenominator =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCommonDenominator", "h": "module\n\npublic import Mathlib.NumberTheory.NumberField.Basic\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

namespace GlobalTheory.CommonDenominatorLemma

open NumberField

theorem exists_common_denominator {E : Type} [inst : Field E] [NumberField E] [StarRing E] {N : ℕ}
    (L : Submodule (NumberField.RingOfIntegers E) (Fin N → E)) (hL : Submodule.FG L) :
    ∃ (b : NumberField.RingOfIntegers E), b ≠ (0 : NumberField.RingOfIntegers E) ∧
      ∀ x ∈ L, ∀ (i : Fin N), ∃ (u : NumberField.RingOfIntegers E), (↑u : E) = (↑b : E) * x i := by
  apply _root_.GlobalTheory.SmallIntegerVanishing.exists_denominator <;> assumption

end GlobalTheory.CommonDenominatorLemma
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCommonDenominator =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualLatticeResolutionOfIdentity =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualLatticeResolutionOfIdentity", "h": "module\n\npublic import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCommonDenominator\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Formalism.LocalRingCardinality.DataTheta\nimport Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SelfDualIdDecomp

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem star_mem_range (a : 𝓞 E) : star (a : E) ∈ (algebraMap (𝓞 E) E).range := by
  have h : IsIntegral ℤ (star (a : E)) := by
    exact (RingOfIntegers.isIntegral_coe a).map (starRingEnd E).toIntAlgHom
  exact ⟨⟨star (a : E), h⟩, rfl⟩

theorem exists_extension {N : ℕ} (L : Submodule (𝓞 E) (Fin N → E)) (hL : IsSDLat E N L)
    (φ : L →ₗ[𝓞 E] 𝓞 E) : ∃ u ∈ L, ∀ x (hx : x ∈ L), stdH E N u x = (φ ⟨x, hx⟩ : E) := by
  classical
  obtain ⟨hfg, -, hdual⟩ := hL
  obtain ⟨b, hb0, hb⟩ := _root_.GlobalTheory.CommonDenominatorLemma.exists_common_denominator L hfg
  obtain ⟨c', hc'⟩ := star_mem_range b
  have hbE : (b : E) ≠ 0 := by
    intro h; apply hb0; exact RingOfIntegers.coe_injective (by simpa using h)
  have hc0 : star (b : E) ≠ 0 := star_ne_zero.2 hbE
  have hce : ∀ i, (Pi.single i (star (b : E)) : Fin N → E) ∈ L := by
    intro i
    rw [hdual]
    intro x hx
    obtain ⟨u, hu⟩ := hb x hx i
    have h1 : stdH E N x (Pi.single i (star (b : E))) = star (u : E) := by
      rw [hu, star_mul]
      simp [stdH, Pi.single_apply]
    rw [h1]; exact star_mem_range u
  let w : Fin N → E := fun i => (φ ⟨Pi.single i (star (b : E)), hce i⟩ : E) / star (b : E)
  have hw : ∀ x (hx : x ∈ L), (φ ⟨x, hx⟩ : E) = ∑ i, w i * x i := by
    intro x hx
    choose ub hub using hb x hx
    have h1 : (b * c') • (⟨x, hx⟩ : L) = ∑ i, ub i • (⟨Pi.single i (star (b : E)), hce i⟩ : L) := by
      apply Subtype.ext; funext j
      simp only [Submodule.coe_smul, Submodule.coe_sum, Finset.sum_apply, Pi.smul_apply,
        Algebra.smul_def, Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      have := hub j
      simp only [map_mul, hc']
      rw [show (algebraMap (𝓞 E) E) (ub j) = (b : E) * x j from this]
      ring
    have h2 := congrArg (fun z => ((φ z : 𝓞 E) : E)) h1

    simp only [map_smul, map_sum, smul_eq_mul] at h2
    push_cast at h2
    apply mul_left_cancel₀ (mul_ne_zero hbE hc0)
    have h3 : (b : E) * star (b : E) * (φ ⟨x, hx⟩ : E) =
        ∑ i, ((ub i : 𝓞 E) : E) * (φ ⟨Pi.single i (star (b : E)), hce i⟩ : E) := by
      rw [← h2, ← hc']
    rw [h3, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hub i]
    simp only [w]
    first | (field_simp; ring) | field_simp
  refine ⟨fun i => star (w i), ?_, ?_⟩
  · rw [hdual]
    intro y hy
    have : stdH E N y (fun i => star (w i)) = star (φ ⟨y, hy⟩ : E) := by
      rw [hw y hy, star_sum]
      simp [stdH, star_mul, mul_comm]
    rw [this]; exact star_mem_range _
  · intro x hx
    rw [hw x hx]
    simp [stdH]

theorem exists_decomp {N : ℕ} (L : Submodule (𝓞 E) (Fin N → E)) (hL : IsSDLat E N L) :
    ∃ (r : ℕ) (s u : Fin r → Fin N → E), (∀ k, s k ∈ L) ∧ (∀ k, u k ∈ L) ∧
      ∑ k, Matrix.vecMulVec (s k) (star (u k)) = 1 := by
  classical
  have hspan := hL.2.1
  have : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.2 hL.1
  have : Module.FinitePresentation (𝓞 E) L := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 E) L := Module.Flat.projective_of_finitePresentation
  obtain ⟨m, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective (𝓞 E) L
  choose u hu hux using fun k : Fin m => exists_extension L hL ((LinearMap.proj k) ∘ₗ g)
  refine ⟨m, fun k => (f (Pi.single k 1) : Fin N → E), u, fun k => (f _).2, hu, ?_⟩
  have hrec : ∀ y : L, (y : Fin N → E) = ∑ k, ((g y k : 𝓞 E) : E) • (f (Pi.single k 1) : Fin N → E) := by
    intro y
    have h1 : f (g y) = y := LinearMap.congr_fun hfg y

    conv_lhs => rw [← h1, pi_eq_sum_univ' (g y), map_sum]
    simp only [map_smul, Submodule.coe_sum, Submodule.coe_smul, algebraMap_smul]
  apply Matrix.toLin'.injective
  apply LinearMap.ext_on hspan
  rintro x hx
  rw [Matrix.toLin'_one, LinearMap.id_apply, Matrix.toLin'_apply]
  funext i
  have e1 : x i = ∑ k, ((g ⟨x, hx⟩ k : 𝓞 E) : E) * (f (Pi.single k 1) : Fin N → E) i := by
    conv_lhs => rw [show x = ((⟨x, hx⟩ : L) : Fin N → E) from rfl, hrec ⟨x, hx⟩]
    simp only [Finset.sum_apply, Pi.smul_apply]
    exact Finset.sum_congr rfl fun k _ => Algebra.smul_def _ _
  rw [e1]
  simp only [Matrix.mulVec, dotProduct, Matrix.sum_apply, vecMulVec_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  have := hux k x hx
  simp only [stdH, LinearMap.comp_apply, LinearMap.proj_apply] at this
  rw [← this, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.star_apply]
  ring

theorem iddecomp : ∀ {D : D7} {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)),
    Formalism.MainNotions.StandardLatticesGL3.SD D L → ∃ (r : ℕ) (s u : Fin r → Fin N → D.host.E), (∀ k, s k ∈ L) ∧ (∀ k, u k ∈ L) ∧
      ∑ k, Matrix.vecMulVec (s k) (star (u k)) = 1 := by
  intro D N L hL
  exact exists_decomp L hL

end GlobalTheory.SelfDualIdDecomp
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualLatticeResolutionOfIdentity =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualLatticeResolutionOfIdentityStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualLatticeResolutionOfIdentityStatement", "h": "module\n\npublic import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualLatticeResolutionOfIdentity\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Formalism.LocalRingCardinality.DataTheta\nimport Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.self_dual_lattice_resolution_of_identity : ∀ {D : D7} {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)), Formalism.MainNotions.StandardLatticesGL3.SD D L → ∃ (r : ℕ) (s u : Fin r → Fin N → D.host.E), (∀ k, s k ∈ L) ∧ (∀ k, u k ∈ L) ∧ ∑ k, Matrix.vecMulVec (s k) (star (u k)) = 1 := by
  first | exact @GlobalTheory.SelfDualIdDecomp.iddecomp
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualLatticeResolutionOfIdentityStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitVacuumEntireFactorIsThetaMovedLattices =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitVacuumEntireFactorIsThetaMovedLattices", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramAtPosDef\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrT\npublic import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmAtSmulRight\npublic import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight\npublic import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ApplyAddInfRat\nimport Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart\npublic import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HomSymplecticHalfFormAlgebraicLawsContinuousStatement\nimport Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDualStatement\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalFrameCoordsOfMemTorusLattice\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePointSignEqThetaLawSemicharacter\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalPointFinitePartIsotropicPairing\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHermitianFormScaledCoordinateEq\nimport Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegerMapEqHalfOneAddSqrt\nimport Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaLatticeImageRationalHomLattice\nimport Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsIsArchimedeanAdeleChartOfRealChart\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualImageOrthonormalFrameLattice\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualLatticeResolutionOfIdentityStatement\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelDataX\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped TensorProduct

noncomputable section
namespace GlobalTheory.ThetaLawMoved
variable {D : D7}

theorem gen_mem {S T : HSp D} (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E)
    (hS : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1)
    (Ls : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (Lt : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (a : D.host.E) (ha : a ∈ (D.host.AA : Submodule (𝓞 D.host.E) D.host.E)) (s : Fin S.rank → D.host.E) (hs : s ∈ Ls)
    (t : Fin T.rank → D.host.E) (ht : t ∈ Lt) :
    GlobalTheory.VacUnique.finRat S T (frT.1 * (a • Matrix.vecMulVec t (star s)) * (frS⁻¹).1) ∈
      latO S T (GlobalTheory.MovedDict.inV frS Ls) (GlobalTheory.MovedDict.inV frT Lt) (fun _ => True) := by
  refine AddSubgroup.subset_closure ⟨1, GlobalTheory.ThetaLawLat.one_mem_intAf', fun v h => (h trivial).elim, a, ha,
    frS.1 *ᵥ s, ⟨s, hs, rfl⟩, frT.1 *ᵥ t, ⟨t, ht, rfl⟩, ?_⟩
  ext i j
  show (pairA D.host.F 0 1) ⊗ₜ[D.host.F] (frT.1 * (a • Matrix.vecMulVec t (star s)) * (frS⁻¹).1) i j = _
  rw [Matrix.of_apply]
  congr 1
  rw [GlobalTheory.ThetaLawLat.inv_frame frS hS]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Matrix.mulVec,
    dotProduct, Pi.star_apply, star_sum, star_mul', Finset.mul_sum, Finset.sum_mul, smul_eq_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem finRat_frame_mem_latO_sd {S T : HSp D} (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E)
    (hS : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1)
    (Ls : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (Lt : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (hLs : Formalism.MainNotions.StandardLatticesGL3.SD D Ls) (z : Matrix (Fin T.rank) (Fin S.rank) D.host.E)
    (hz : z ∈ GlobalTheory.InertSign.RL D D.host.ccK Ls Lt) :
    GlobalTheory.VacUnique.finRat S T (frT.1 * z * (frS⁻¹).1) ∈
      latO S T (GlobalTheory.MovedDict.inV frS Ls) (GlobalTheory.MovedDict.inV frT Lt) (fun _ => True) := by
  obtain ⟨r, s, u, hs, hu, hsu⟩ := GlobalTheory.T.self_dual_lattice_resolution_of_identity Ls hLs
  have hA : ∀ a ∈ (D.host.AA : Submodule (𝓞 D.host.E) D.host.E), ∀ A ∈ Formalism.MainNotions.TaylorLogMetric.homL D Ls Lt,
      GlobalTheory.VacUnique.finRat S T (frT.1 * (a • A) * (frS⁻¹).1) ∈
        latO S T (GlobalTheory.MovedDict.inV frS Ls) (GlobalTheory.MovedDict.inV frT Lt) (fun _ => True) := by
    intro a ha A hA
    have eA : A = ∑ k, Matrix.vecMulVec (A *ᵥ s k) (star (u k)) := by
      conv_lhs => rw [← Matrix.mul_one A, ← hsu]
      ext i j
      simp only [Matrix.mul_apply, Matrix.sum_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Finset.mul_sum,
        Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

    rw [eA, Finset.smul_sum, Matrix.mul_sum, Matrix.sum_mul, map_sum]
    exact AddSubgroup.sum_mem _ fun k _ => gen_mem frS frT hS Ls Lt a ha (u k) (hu k) (A *ᵥ s k)
      (GlobalTheory.ThetaLatImage.mem_homL.1 hA _ (hs k))
  have hI : ∀ t ∈ GlobalTheory.InertSign.Iid D D.host.ccK, t ∈ (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) := by
    intro t ht
    induction ht using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨c, hc, a, ha, rfl⟩ := ht
      have hc' : ((c : D.host.K) : D.host.E) ∈ (D.host.ccE : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :=
        FractionalIdeal.mem_coeIdeal_of_mem _ (Ideal.mem_map_of_mem (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) hc)
      exact FractionalIdeal.mul_mem_mul hc' ha
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul o x _ hx => exact Submodule.smul_mem _ o hx
  suffices h : ∀ o : 𝓞 D.host.E, GlobalTheory.VacUnique.finRat S T (frT.1 * (o • z) * (frS⁻¹).1) ∈
      latO S T (GlobalTheory.MovedDict.inV frS Ls) (GlobalTheory.MovedDict.inV frT Lt) (fun _ => True) by
    have := h 1
    rwa [one_smul] at this
  induction hz using Submodule.span_induction with
  | mem z hz =>
    intro o
    obtain ⟨t, ht, A, hA', rfl⟩ := hz
    rw [← smul_assoc]
    exact hA _ (Submodule.smul_mem _ o (hI t ht)) A hA'
  | zero => intro o; rw [smul_zero, Matrix.mul_zero, Matrix.zero_mul, map_zero]; exact zero_mem _
  | add x y _ _ hx hy =>
    intro o
    rw [smul_add, Matrix.mul_add, Matrix.add_mul, map_add (f := _)]
    exact add_mem (hx o) (hy o)
  | smul o' x _ hx => intro o; rw [smul_smul]; exact hx _

theorem mem_La_frame_sd {D : D7} (S T : HSp D) (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E)
    (hS : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1)
    (hT : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1)
    (Ls : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (Lt : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (hLs : Formalism.MainNotions.StandardLatticesGL3.SD D Ls) (δ : ℂ) (x : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank)
    (hx : x ∈ Formalism.MainNotions.TaylorLogMetric.La D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) Ls Lt) :
    ∃ v : Matrix (Fin T.rank) (Fin S.rank) D.host.E, GlobalTheory.VacUnique.finRat S T v ∈
      latO S T (GlobalTheory.MovedDict.inV frS Ls) (GlobalTheory.MovedDict.inV frT Lt) (fun _ => True) ∧
      x = δ • (fun τ a b => ((GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (GlobalTheory.VacUnique.infRat S T v τ) *
        GlobalTheory.FockPos.frAt frS τ) a b) := by
  obtain ⟨z, hz, rfl⟩ := GlobalTheory.ThetaLatImage.La_sub hx
  refine ⟨frT.1 * z * (frS⁻¹).1, finRat_frame_mem_latO_sd frS frT hS Ls Lt hLs z hz, ?_⟩
  have hmap : ∀ τ, Matrix.of (GlobalTheory.VacUnique.infRat S T (frT.1 * z * (frS⁻¹).1) τ) =
      GlobalTheory.FockPos.frAt frT τ * Matrix.of (fun i j => tauE D τ (z i j)) * (GlobalTheory.FockPos.frAt frS τ)⁻¹ := by
    intro τ
    have hi : (GlobalTheory.FockPos.frAt frS τ)⁻¹ = (frS⁻¹).1.map (tauE D τ) := by
      refine Matrix.inv_eq_right_inv ?_
      rw [GlobalTheory.FockPos.frAt, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [hi]
    show (frT.1 * z * (frS⁻¹).1).map (tauE D τ) = _
    rw [Matrix.map_mul, Matrix.map_mul]
    rfl
  funext τ a b
  rw [GlobalTheory.ThetaLatImage.pt_apply]
  show _ = δ * ((GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (GlobalTheory.VacUnique.infRat S T (frT.1 * z * (frS⁻¹).1) τ) *
    GlobalTheory.FockPos.frAt frS τ) a b
  rw [hmap τ, GlobalTheory.ThetaLawOF.coord_back frS frT (fun τ i j => tauE D τ (z i j)) τ]
  rfl

section
open GlobalTheory.ThetaSignLat

theorem sign_eq_alpha_sd : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1 → IsStdChar D ψ (-1) → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ δ : ℂ, δ ≠ 0 → ∀ v : Matrix (Fin T.rank) (Fin S.rank) D.host.E, GlobalTheory.VacUnique.finRat S T v ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) → ∀ ε : ℂ, (∀ g : WO S T → ℂ, IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) g → heisO ψ S T (GlobalTheory.VacUnique.finRat S T (-v)) g = ε • g) → ψ (-symplOH S T (ratW T S v) (GlobalTheory.VacUnique.finRat S T (-v))) * ε = Formalism.MainNotions.TaylorLogMetric.al D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (δ • (fun τ a b => ((GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (GlobalTheory.VacUnique.infRat S T v τ) * GlobalTheory.FockPos.frAt frS τ) a b)) :=
  GlobalTheory.ThetaSignLat.sign_eq_alpha_of_selfDual

end

section
open GlobalTheory.ThetaLawOF

theorem theta_of_vacuum_on_selfDual : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1 → ∀ δ : ℂ, δ ≠ 0 → ∀ (Ls : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (Lt : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), Formalism.MainNotions.StandardLatticesGL3.SD D Ls → Formalism.MainNotions.StandardLatticesGL3.SD D Lt → ∀ f : WO S T → ℂ, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (GlobalTheory.MovedDict.inV frS Ls) (GlobalTheory.MovedDict.inV frT Lt) f → ∀ Φ : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ, Differentiable ℂ Φ → (∀ w : WO S T, w.map (finPart D) = 0 → f w = GlobalTheory.FockPos.gaussO θ frS frT w * Φ (GlobalTheory.FockPos.zCo θ frS frT w)) → (fun Y => Φ (δ⁻¹ • Y)) ∈ Formalism.MainNotions.TaylorLogMetric.Th D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) Ls Lt := by
  intro D ψ θ S T frS frT hS hT δ hδ Ls Lt hLs hLt f hf Φ hΦd hΦ
  obtain ⟨ΛS, hΛS, hSd⟩ := GlobalTheory.MovedDict.isSelfDualC_inV S frS hS Ls hLs
  obtain ⟨ΛT, hΛT, hTd⟩ := GlobalTheory.MovedDict.isSelfDualC_inV T frT hT Lt hLt
  rw [← hΛS, ← hΛT] at hf
  have hψ := hf.1
  have hθ := hf.2.inf
  obtain ⟨σ, hch⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨-, -, h3⟩ := GlobalTheory.T.self_dual_lattice_pairing_dual D ψ S T ΛS ΛT hψ hSd hTd
  refine ⟨hΦd.comp ((differentiable_id).const_smul δ⁻¹), ?_⟩
  intro x hx Y
  obtain ⟨v, hv, rfl⟩ := mem_La_frame_sd S T frS frT hS hT Ls Lt hLs δ x hx
  rw [← hΛS, ← hΛT] at hv
  have hv' : GlobalTheory.VacUnique.finRat S T (-v) ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True) := by
    rw [AddMonoidHom.map_neg]; exact neg_mem hv
  obtain ⟨ε, -, hε⟩ := h3 f hf.2.lat _ hv'
  have hsign := sign_eq_alpha_sd ψ S T frS frT hS hT hψ ΛS ΛT hSd hTd δ hδ v hv ε (fun g hg => hε g hg)
  have hlaw := GlobalTheory.VacUnique.apply_add_infRat hch hψ hf.2.theta v (hε f hf.2.lat)
  set X : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank := fun τ a b => ((GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (GlobalTheory.VacUnique.infRat S T v τ) * GlobalTheory.FockPos.frAt frS τ) a b with hX
  set Z : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank := δ⁻¹ • Y with hZ
  have hZY : Y = δ • Z := by rw [hZ, smul_smul, mul_inv_cancel₀ hδ, one_smul]
  set z : GlobalTheory.FockCompare.RW T S := fun τ => GlobalTheory.FockPos.frAt frT τ * Matrix.of (Z τ) * (GlobalTheory.FockPos.frAt frS τ)⁻¹ with hz
  have hzτ : ∀ τ, (GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (z τ) * GlobalTheory.FockPos.frAt frS τ = Matrix.of (Z τ) :=
    fun τ => coord_back frS frT Z τ
  have hz1 : GlobalTheory.FockPos.zCo θ frS frT (GlobalTheory.FockCompare.iotaW σ T S z) = Z := by
    rw [zCo_iota hch]; funext τ; exact coord_back frS frT Z τ
  have hz2 : GlobalTheory.FockPos.zCo θ frS frT (GlobalTheory.FockCompare.iotaW σ T S (z + GlobalTheory.VacUnique.infRat S T v)) = Z + X := by
    rw [zCo_iota hch]; funext τ
    show (GlobalTheory.FockPos.frAt frT τ)⁻¹ * (Matrix.of (z τ) + Matrix.of (GlobalTheory.VacUnique.infRat S T v τ)) * GlobalTheory.FockPos.frAt frS τ = Z τ + X τ
    rw [Matrix.mul_add, Matrix.add_mul, hzτ τ]
    rfl
  have hom : GlobalTheory.VacUnique.omO S T (GlobalTheory.VacUnique.infRat S T v) z = ∑ τ, ∑ a, ∑ b, 2 * (Complex.I * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) *
      (starRingEnd ℂ (Z τ a b) * X τ a b)).re := by
    rw [omO_frame frS frT hS hT]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [hzτ τ]
    rfl
  have hl := hlaw z
  rw [hΦ _ (hch.real_iota T S _), hΦ _ (hch.real_iota T S _), GlobalTheory.FockPos.gaussO, GlobalTheory.FockPos.gaussO, hz1, hz2, hom, hsign] at hl

  simp only [Formalism.MainNotions.TaylorLogMetric.U]
  have e1 : δ⁻¹ • (Y + δ • X) = Z + X := by rw [smul_add, smul_smul, inv_mul_cancel₀ hδ, one_smul]
  rw [e1, hZY, torusHermitianForm_scaled_coordinate_eq hδ, torusHermitianForm_scaled_coordinate_eq hδ]
  have hZZ : δ⁻¹ • δ • Z = Z := by rw [smul_smul, inv_mul_cancel₀ hδ, one_smul]
  rw [hZZ]
  set a := Formalism.MainNotions.TaylorLogMetric.al D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (δ • X) with ha
  have kE : Complex.exp (-(Real.pi * Complex.I) * ((-∑ τ, ∑ a, ∑ b, 2 * (Complex.I * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) *
      (starRingEnd ℂ (Z τ a b) * X τ a b)).re : ℝ) : ℂ)) *
      Complex.exp (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖Z τ a b‖ ^ 2 : ℝ) : ℂ)) *
      Complex.exp (-(Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (X τ a b)) -
        (Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, X τ a b * starRingEnd ℂ (X τ a b)) / 2) =
      Complex.exp (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖(Z + X) τ a b‖ ^ 2 : ℝ) : ℂ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    simp only [Pi.add_apply]
    push_cast
    simp only [Finset.mul_sum, Finset.sum_div, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have h := entry (Z τ i j) (X τ i j) (Formalism.L2.Pj.xiR D)
    push_cast at h ⊢
    linear_combination h
  apply mul_left_cancel₀ (Complex.exp_ne_zero (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖(Z + X) τ a b‖ ^ 2 : ℝ) : ℂ)))
  rw [← kE]
  calc _ = a * Complex.exp (-(Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (X τ a b)) -
        (Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, X τ a b * starRingEnd ℂ (X τ a b)) / 2) *
        (Complex.exp (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖(Z + X) τ a b‖ ^ 2 : ℝ) : ℂ)) * Φ (Z + X)) := by
        rw [kE]; ring
    _ = _ := by
        rw [hl]
        have := al_mul_self (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (δ • X)
        rw [← ha] at this
        linear_combination (Complex.exp (-(Real.pi * Complex.I) * ((-∑ τ, ∑ a, ∑ b, 2 * (Complex.I * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) *
      (starRingEnd ℂ (Z τ a b) * X τ a b)).re : ℝ) : ℂ)) *
      Complex.exp (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖Z τ a b‖ ^ 2 : ℝ) : ℂ)) *
      Complex.exp (-(Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (X τ a b)) -
        (Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, X τ a b * starRingEnd ℂ (X τ a b)) / 2) * Φ Z) * this

theorem theta_of_vacuum_moved : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1 → ∀ δ : ℂ, Formalism.MainNotions.StandardLatticesGL3.Crv D D.host.ccK δ → δ ≠ 0 → ∀ (Ls : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (Lt : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), Formalism.MainNotions.StandardLatticesGL3.SD D Ls → Formalism.MainNotions.StandardLatticesGL3.SD D Lt → ∀ f : WO S T → ℂ, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (GlobalTheory.MovedDict.inV frS Ls) (GlobalTheory.MovedDict.inV frT Lt) f → ∀ Φ : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ, Differentiable ℂ Φ → (∀ w : WO S T, w.map (finPart D) = 0 → f w = GlobalTheory.FockPos.gaussO θ frS frT w * Φ (GlobalTheory.FockPos.zCo θ frS frT w)) → (fun Y => Φ (δ⁻¹ • Y)) ∈ Formalism.MainNotions.TaylorLogMetric.Th D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) Ls Lt := by
  intro D ψ θ S T frS frT hS hT δ _ hδ
  exact theta_of_vacuum_on_selfDual ψ θ S T frS frT hS hT δ hδ

end

end GlobalTheory.ThetaLawMoved

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitVacuumEntireFactorIsThetaMovedLattices =====
