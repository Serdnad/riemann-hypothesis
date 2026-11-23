module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.RelIndexSmulSub
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle005
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensCntRes
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle001

@[expose] public section

section

noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.VolStabSW

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

private theorem le_ofAdd_neg_one_of_lt_one_local_unitary_orbits {a : WithZero (Multiplicative ℤ)} (h : a < 1) :
    a ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  by_cases ha : a = 0
  · simp [ha]
  · have h1 : a < ((Multiplicative.ofAdd (0 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
      simpa using h
    rw [WithZero.lt_ofAdd_iff ha] at h1
    rw [WithZero.le_ofAdd_iff ha]
    omega

theorem mem_unifO_iff {ϖ : Fv F v} (hϖ : IsUnif v ϖ) (x : v.adicCompletionIntegers F) :
    x ∈ unifO v ϖ ↔ Valued.v (x : Fv F v) < 1 := by
  have hv : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := hϖ
  have hlt : Valued.v ϖ < 1 := by
    rw [hv]
    exact_mod_cast (by decide : (Multiplicative.ofAdd (-1 : ℤ)) < 1)
  have hne : ϖ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hv
    exact WithZero.zero_ne_coe hv
  constructor
  · rintro ⟨d, hd⟩
    have hd1 : Valued.v (d : Fv F v) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 d.2
    rw [hd, map_mul]
    calc Valued.v ϖ * Valued.v (d : Fv F v) ≤ Valued.v ϖ * 1 := by gcongr
      _ < 1 := by rwa [mul_one]
  · intro hx
    have hle : Valued.v (x : Fv F v) ≤ Valued.v ϖ := by
      rw [hv]; exact le_ofAdd_neg_one_of_lt_one_local_unitary_orbits hx
    have hmem : (x : Fv F v) / ϖ ∈ v.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀]
      exact div_le_one_of_le₀ hle zero_le'
    refine ⟨⟨_, hmem⟩, ?_⟩
    simp only
    field_simp

def redO : v.adicCompletionIntegers F →+ 𝓞 F ⧸ v.asIdeal where
  toFun x := red v (x : Fv F v)
  map_zero' := red_zero v
  map_add' x y := red_add v x.2 y.2

theorem resIdx_holds : ResIdx v := by
  intro ϖ hϖ
  have hker : unifO v ϖ = (redO v).ker := by
    ext x
    rw [mem_unifO_iff v hϖ x, AddMonoidHom.mem_ker]
    exact (red_eq_zero_iff v x.2).symm
  have hsurj : Function.Surjective (redO v) := by
    intro t
    obtain ⟨y, hy, hyt⟩ := red_surj v t
    exact ⟨⟨y, hy⟩, hyt⟩
  rw [hker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hsurj, Ideal.absNorm_apply,
    Submodule.cardQuot_apply]
  simp

end PI.OmLocU
end
end

section

noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.LocVol NumberField IsDedekindDomain

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem sdVolW_of (a : ℕ) (hC : CondV σ J ψ v) (hD : DualW σ J ψ v Λ a) (hI : IdxW v Λ a)
    (hFull : ∃ L : Submodule (𝓞 E) (Fin n → E),
      Submodule.IsFullLattice E L ∧ (L : Set (Fin n → E)) = Λ) :
    SdVolW σ J ψ v Λ a :=
  sdVolW_of_top σ J ψ v Λ a hC (topW_holds v Λ a hFull) hD hI

theorem sdVolH_of (a : ℕ) (hC : CondV σ J ψ v) (hD : DualH σ J ψ v a) (hI : IdxHO σ v a) :
    SdVolH σ J ψ v a :=
  sdVolH_of_top σ J ψ v a hC (topH_holds v σ a) hD hI

theorem sdVolW_of_pi (a : ℕ) (hC : CondV σ J ψ v) (hD : DualW σ J ψ v Λ a) (hI : IdxPiW v Λ a)
    (hFull : ∃ L : Submodule (𝓞 E) (Fin n → E),
      Submodule.IsFullLattice E L ∧ (L : Set (Fin n → E)) = Λ) :
    SdVolW σ J ψ v Λ a :=
  sdVolW_of σ J ψ v Λ a hC hD (idxW_of v Λ a hI) hFull

theorem sdVolH_of_pi (a : ℕ) (hC : CondV σ J ψ v) (hD : DualH σ J ψ v a) (hI : IdxPiH σ v a) :
    SdVolH σ J ψ v a :=
  sdVolH_of σ J ψ v a hC hD (idxHO_of σ v a hI)

end PI.OmLocU
end
end
