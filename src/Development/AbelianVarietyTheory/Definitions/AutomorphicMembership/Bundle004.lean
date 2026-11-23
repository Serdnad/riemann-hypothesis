module

public import Development.AbelianVarietyTheory.Definitions.Foundations.AbsCharNotUnitary
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Matrix Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host
open GlobalTheory.Mem.Chr.CharModel

namespace GlobalTheory.CuspRep.Model

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


variable (E) in
omit [_root_.NumberField.IsTotallyComplex E] in
def absC (s : ℂ) : HChar E := ⟨absHom E s, (absChar E s).2⟩

theorem logNorm_infId (u : (Cinf E)ˣ) : logNorm E (infId E u) = ∑ w, 2 * Real.log ‖(u : Cinf E) w‖ := by
  have h1 : GlobalTheory.Mem.Chr.CharModel.finPart E (infId E u) = 1 := Units.ext (by
    change (1 : Af E) - 0 + 0 = 1
    simp)
  rw [logNorm, h1, logFin_one, sub_zero, logInf]
  refine Finset.sum_congr rfl fun w _ => ?_
  have h2 : ((infPart E (infId E u) : (InfiniteAdeleRing E)ˣ) : InfiniteAdeleRing E) = infEq E u := by
    change (1 : InfiniteAdeleRing E) - infEq E 1 + infEq E u = _
    simp
  rw [h2, InfinitePlace.mult, if_neg (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w))]
  have h3 : ‖infEq E u w‖ = ‖(u : Cinf E) w‖ :=
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).symm.isometry.norm_map_of_map_zero
      (map_zero (InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).symm) _
  rw [h3]; norm_num

theorem expo_absC (s : ℂ) (τ : E →+* ℂ) : expo (absC E s) τ = s := by
  classical
  refine expo_eq_of_exp _ τ s s fun z => ?_
  change Complex.exp (s * logNorm E (infId E (expU (atEmb τ z)))) = _
  rw [logNorm_infId, Finset.sum_eq_single (InfinitePlace.mk τ)]
  · change Complex.exp (s * ((2 * Real.log ‖Complex.exp (atEmb τ z _)‖ : ℝ) : ℂ)) = _
    rw [Complex.norm_exp, Real.log_exp, ← mul_add, Complex.add_conj]
    congr 3
    unfold atEmb
    split_ifs <;> simp
  · intro w _ hw
    change 2 * Real.log ‖Complex.exp (atEmb τ z w)‖ = 0
    simp [atEmb, hw]
  · simp

section CM

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

end CM

end GlobalTheory.CuspRep.Model
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric NumberField

namespace GlobalTheory.Mem.Per

def posOr1 (x : ℝ) : ℝ := if 0 < x then x else 1

theorem posOr1_pos (x : ℝ) : 0 < posOr1 x := by
  unfold posOr1
  split_ifs with h
  · exact h
  · exact one_pos

def jLat (Λ : AddSubgroup ℂ) : ℂ := 1728 * g2 Λ ^ 3 / discr Λ

variable {R : Ranks} (H : Host R) {LL : Type} [Field LL] [NumberField LL]

def baseLat : AddSubgroup ℂ :=
  AddSubgroup.closure {w | ∃ c ∈ H.ccK, w = H.φ₀ (((c : H.K) : H.E))}

def IsConjLat (emb s : LL →+* ℂ) (Λ Λ' : AddSubgroup ℂ) : Prop :=
  discr Λ' = 1 ∧ ∃ a : LL, emb a = jLat Λ ∧ s a = jLat Λ'

def conjLat (emb s : LL →+* ℂ) : AddSubgroup ℂ := Classical.epsilon (IsConjLat emb s (baseLat H))

def ellLat (embE : H.E →+* LL) (g : R.GG) : Submodule (𝓞 LL) LL :=
  Submodule.span (𝓞 LL) {y | ∃ a ∈ (H.AA0 : Submodule (𝓞 H.E) H.E),
    ∃ b ∈ differentIdeal (𝓞 H.K) (𝓞 H.E), y = embE (H.sigmaOf g (a * (b : H.E)))}

def IsGen (embE : H.E →+* LL) (g : R.GG) (x : LL) : Prop :=
  Submodule.span (𝓞 LL) {x} = ellLat H embE g

def gen (embE : H.E →+* LL) (g : R.GG) : LL := Classical.epsilon (IsGen H embE g)

def FieldOK (emb : LL →+* ℂ) (embE : H.E →+* LL) : Prop :=
  (∃ a : LL, emb a = jLat (baseLat H)) ∧ ∀ g, ∃ x, IsGen H embE g x

def IsHalfPt (d : ℕ) (Λ : AddSubgroup ℂ) (t : ℂ) : Prop :=
  2 * t ∈ Λ ∧ ((1 + Complex.I * (Real.sqrt d : ℂ)) / 2) * t ∉ Λ ∧ ((1 - Complex.I * (Real.sqrt d : ℂ)) / 2) * t ∉ Λ

def omAt (emb s : LL →+* ℂ) (x : LL) : ℝ := area (conjLat H emb s) / (Real.pi * ‖s x‖ ^ 2)

def thAt (emb s : LL →+* ℂ) : ℝ :=
  Real.sqrt (StandardLatticesGL3.nrm1Sq (conjLat H emb s)
    (GL3Theta.th0 (conjLat H emb s) (Classical.epsilon (IsHalfPt H.d (conjLat H emb s)))))

def trueGx (emb : LL →+* ℂ) (embE : H.E →+* LL) {I : Type} (e : I ≃ R.Psi) : GlobalExtra LL I where
  Om τ s := posOr1 (omAt H emb s (gen H embE (e τ).1))
  Om_pos _ _ := posOr1_pos _
  thOne s := posOr1 (thAt H emb s)
  thOne_pos _ := posOr1_pos _

end GlobalTheory.Mem.Per
end
end
