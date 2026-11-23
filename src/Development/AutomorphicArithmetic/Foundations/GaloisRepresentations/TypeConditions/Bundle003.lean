module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle017
public import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.AutomorphicGaloisAdmissible
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle380
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle009

@[expose] public section

section

noncomputable section

namespace UpperTheory.GalS

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain Formalism.MainNotions.SumRepresentations Formalism.MainNotions.SumRepresentations.At

section
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)

def DistinctAbsIrredConstituents (i : N.Loc) (r : N.X i → (G H.E N.Om →* GL (Fin R.nV) (N.O i))) : Prop :=
  ∃ (K' : Type) (_ : Field K') (_ : Algebra (Kf N i) K') (_ : FiniteDimensional (Kf N i) K'),
    ∀ x, (∀ W, IsIrrSub (mapRep ((algebraMap (Kf N i) K').comp (algebraMap (N.O i) (Kf N i))) (r x)) W →
        AbsIrrSub (mapRep ((algebraMap (Kf N i) K').comp (algebraMap (N.O i) (Kf N i))) (r x)) W) ∧
      ∀ W₁ W₂, IsIrrSub (mapRep ((algebraMap (Kf N i) K').comp (algebraMap (N.O i) (Kf N i))) (r x)) W₁ →
        IsIrrSub (mapRep ((algebraMap (Kf N i) K').comp (algebraMap (N.O i) (Kf N i))) (r x)) W₂ →
        W₁ ⊓ W₂ = ⊥ →
        ¬ IsoSub (mapRep ((algebraMap (Kf N i) K').comp (algebraMap (N.O i) (Kf N i))) (r x)) W₁ W₂

def G3a (i : N.Loc) (r : N.X i → (G H.E N.Om →* GL (Fin R.nV) (N.O i))) : Prop :=
  ((N.l i ≠ H.g 0 ∧ N.l i ≠ H.g 1) ∨ GlobalTheory.CoefDuty.Live N i) → DistinctAbsIrredConstituents N i r

def ResidualCharpolyIndependent (i : N.Loc) (r : N.X i → (G H.E N.Om →* GL (Fin R.nV) (N.O i))) : Prop :=
  ∀ (x y : N.X i) (g : G H.E N.Om),
    ((redRep N i (r x) g : GL (Fin R.nV) (IsLocalRing.ResidueField (N.O i))) :
        Matrix (Fin R.nV) (Fin R.nV) (IsLocalRing.ResidueField (N.O i))).charpoly =
      ((redRep N i (r y) g : GL (Fin R.nV) (IsLocalRing.ResidueField (N.O i))) :
        Matrix (Fin R.nV) (Fin R.nV) (IsLocalRing.ResidueField (N.O i))).charpoly

def G3 (i : N.Loc) (r : N.X i → (G H.E N.Om →* GL (Fin R.nV) (N.O i))) : Prop := G3a N i r ∧ ResidualCharpolyIndependent N i r

variable {N}
theorem g3 {i : N.Loc} {r : N.X i → (G H.E N.Om →* GL (Fin R.nV) (N.O i))} (h : At.G3 N i r) : G3 N i r := ⟨fun _ => h.1, h.2⟩
theorem g3' {i : N.Loc} {r : N.X i → (G H.E N.Om →* GL (Fin R.nV) (N.O i))} (h : G3 N i r) : G3 N i r := h
end

def DeRhamJumpsDistinctCondition (D : D7) : Prop :=
  (∀ i r, GoodR D.nd i r → (D.nd.l i = D.host.g 0 ∨ D.nd.l i = D.host.g 1) →
    ∀ w ∈ placesOver D.host.E (D.nd.l i), ∀ x,
      D.naut.IsdRW i (AdmissibleParameterJ.rQ D i r x) w ∧
      ∀ τ₀, InducesW D.nd i τ₀ w → D.naut.jumpsW i (AdmissibleParameterJ.rQ D i r x) τ₀ = D.naut.locAutHodgeTateWeightsLevelZero i τ₀) ∧
  ∀ i r, GoodR D.nd i r → DistinctAbsIrredConstituents D.nd i r

end UpperTheory.GalS
end
end

section

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

noncomputable section

namespace UpperTheory.GalS

theorem nonCritical_localParam_of_full_dim (D : D7) (h4 : SumRepresentations.ArchimedeanSignatureMatching D) (i : D.nd.Loc) (P : D.naut.AV i) (w : PlE D.host) (hw : w ∈ D.nd.S i ∨ w ∈ D.nd.Q i)
    (hA : w ∈ D.nd.Q i ∨ (w ∈ D.nd.S i ∧ (w ∈ placesOver D.host.E D.host.pde ∨
      (D.nd.l i = D.host.pde ∧ w ∈ placesOver D.host.E D.host.pde')))) (hd : D.naut.lpDim (D.naut.locV i P w) = D.R.nV) :
    Nc D.nd D.naut (D.naut.locV i P w) := by
  obtain ⟨hχ, hDel⟩ := (GlobalTheory.T.tame_descent_conditions_every_localisation D i).1
  obtain ⟨m, p⟩ := h4.1 i P w hw (hA.imp id fun h => ⟨hDel, h.2⟩)
  refine ⟨fun σ hσ hW => ?_, m, fun γ hγ z hz => ?_⟩
  · have e : chi1 D.nd i σ = 1 := by
      show ((D.nd.chi i 1 σ : (D.nd.O i)ˣ) : D.nd.O i) = 1
      rw [hχ w hA σ hW, Units.val_one]
    rw [p σ hσ, e, map_one, map_one, ← pow_add, hd]; rfl
  · have h1 : (D.naut.inePol (D.naut.locV i P w) γ).IsRoot z := (rootMultiplicity_pos'.1 (lt_of_lt_of_le (thr_pos w) hz)).2
    rw [p γ hγ.1] at h1
    simp only [IsRoot, eval_mul, eval_pow, eval_sub, eval_X, eval_one, eval_C, mul_eq_zero] at h1
    rcases h1 with h1 | h1
    · rw [sub_eq_zero.1 (pow_eq_zero_iff'.1 h1).1, one_pow]
    · have k := char_pow_ine (D.nd.plOm.2 w) (D.nd.chi i 1) (hχ w hA) γ hγ.1
      rw [sub_eq_zero.1 (pow_eq_zero_iff'.1 h1).1, ← map_pow]
      show iotaO D.nd D.naut i (((D.nd.chi i 1 γ : (D.nd.O i)ˣ) : D.nd.O i) ^ _) = 1
      rw [← Units.val_pow_eq_pow_val, k, Units.val_one, map_one]

end UpperTheory.GalS
end
end
