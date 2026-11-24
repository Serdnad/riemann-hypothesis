module

import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertHeckeOperatorCompSphericalConvolution
public import Formalism.AlgebraicWeights.InertDatumExists
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMaxCompactOfTrivOutsideLocalIntegral
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.IsBichar
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC

noncomputable section

open TensorProduct

namespace GlobalTheory.InertKU

theorem compAt_mem_tensInt (L : Type) [Field L] [NumberField L] [IsCMField L]
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) {z : AL L} (hz : z ∈ ALint L) :
    compAt L v z ∈ Formalism.UG.tensInt (F := maximalRealSubfield L)
      (v.adicCompletion (maximalRealSubfield L)) (Formalism.UG.intOE L)
      (Formalism.UG.Ov (maximalRealSubfield L) v) := by
  intros
  apply _root_.GlobalTheory.InertUmaxInt.compAt_mem_tensInt <;> assumption

theorem mem_range_bc_of_entries {K : Type} [Field K] (S : Subring K) {n : ℕ} (g : GL (Fin n) K)
    (hg : ∀ i j, (g : Matrix (Fin n) (Fin n) K) i j ∈ S)
    (hg' : ∀ i j, ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j ∈ S) :
    g ∈ (Formalism.UG.bc (n := Fin n) S.subtype).range := by
  let M : Matrix (Fin n) (Fin n) S := fun i j => ⟨_, hg i j⟩
  let M' : Matrix (Fin n) (Fin n) S := fun i j => ⟨_, hg' i j⟩
  have hM : (RingHom.mapMatrix S.subtype) M = (g : Matrix (Fin n) (Fin n) K) := rfl
  have hM' : (RingHom.mapMatrix S.subtype) M' = ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := rfl
  have inj : Function.Injective (RingHom.mapMatrix (m := Fin n) S.subtype) := by
    intro A B h
    ext i j
    exact congrFun (congrFun h i) j
  have h1 : M * M' = 1 := inj (by rw [map_mul, map_one, hM, hM']; exact Units.mul_inv g)
  have h2 : M' * M = 1 := inj (by rw [map_mul, map_one, hM, hM']; exact Units.inv_mul g)
  refine ⟨⟨M, M', h1, h2⟩, ?_⟩
  ext i j
  rfl

theorem loc_inv (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L))
    (Dv : InertDatum L n v w) (x : GAf L n) : Dv.loc x⁻¹ = (Dv.loc x)⁻¹ := by
  unfold InertDatum.loc
  simp only [InvMemClass.coe_inv, map_inv]
  group

theorem loc_entries_mem (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L))
    (Dv : InertDatum L n v w) (y : GAf L n) (hy : y ∈ Umax L n) (i j : Fin n) :
    ((Dv.loc y : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) i j
      ∈ Formalism.UG.intL (w.adicCompletion L) := by
  apply _root_.GlobalTheory.InertUmaxInt.loc_integral_of_mem_Umax <;> assumption

theorem loc_mem_KU : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (x : GAf L n), x ∈ Umax L n → ∀ hg : Dv.loc x ∈ Formalism.UG.GU Dv.σw n, (⟨Dv.loc x, hg⟩ : Formalism.UG.GU Dv.σw n) ∈ Formalism.UG.KU Dv.σw n := by
  intro L _ _ _ n v w Dv x hx hg
  rw [Formalism.UG.KU, Subgroup.mem_subgroupOf]
  refine ⟨hg, ?_⟩
  apply mem_range_bc_of_entries
  · exact loc_entries_mem L n v w Dv x hx
  · intro i j
    rw [← loc_inv]
    exact loc_entries_mem L n v w Dv x⁻¹ (inv_mem hx) i j

end GlobalTheory.InertKU
