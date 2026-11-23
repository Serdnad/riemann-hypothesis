module

public import Formalism.HermitianCurvature.OperatorsCommuteTranslations
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianCovectors.HermBvecLeft
public import Formalism.HermitianCurvature.StatementQ
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ConjugateTransposeLeibniz.YOperatorLeibnizRule
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GeneralLinearLevel.ElementaryGeneratorsLevelGroup
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SkewAnalyticGroup.Analytic
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SkewAnalyticGroup.SkewReductionGroup
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TorusConjugationRule.SecondHermitianPartDiagonal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermDef
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermCarrierStability.TermStableHolds
public import Formalism.PeriodIntegrals.AutLzFinite
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismFiniteness.AutLzFinMain
public import Formalism.PeriodIntegrals.Bundle016
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle009
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarePairLocal.SqPairLocalOf
public import Formalism.PeriodIntegrals.Bundle025
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianClassFiniteness.CTFromBlocks
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianClassFiniteness.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianClassFiniteness.FrHformSumLeft
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianClassFiniteness.Bundle002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianClassFiniteness.RtUnitaryOf
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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

@[expose] public section

section

theorem covector_entries : Formalism.FourierDecayAlt.C3.XiYZhat := CovecW.covec_entries
end

section

theorem qnYLeibniz : Formalism.FourierDecayAlt.Q.YLeibniz := QnYLeibnizW.y_operator_leibniz_rule
end

section

private lemma single_one_mul_single_one {n : ℕ} (p q s t : Fin n) :
    Matrix.single p q (1 : ℂ) * Matrix.single s t 1 = if q = s then Matrix.single p t 1 else 0 := by
  split_ifs with h
  · subst h
    rw [Matrix.single_mul_single_same, mul_one]
  · exact Matrix.single_mul_single_of_ne (h := h) ..

private lemma posL_eq_posL_iff (k r : ℕ) (i : Fin (r + 1)) (x y : Fin (Formalism.FourierDecayAlt.Q.mdim k r i)) :
    Formalism.FourierDecayAlt.Q.posL k r i x = Formalism.FourierDecayAlt.Q.posL k r i y ↔ x = y := by
  constructor
  · intro h
    have h' := congrArg Fin.val h
    simp only [Formalism.FourierDecayAlt.Q.posL] at h'
    exact Fin.ext (by omega)
  · rintro rfl
    rfl

theorem qnEabGl : Formalism.FourierDecayAlt.Q.EabGlLev := by
  intro E _ _ k r i D a b c d f _ hf g hg
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g hg
  have hL : Formalism.FourierDecayAlt.Q.EabGlW.LocExt (Formalism.FourierDecayAlt.Q.Glev k r i) f F U := ⟨hU, hF, hfF⟩
  have good : ∀ x y : Fin (Formalism.FourierDecayAlt.Q.mdim k r i), Formalism.FourierDecayAlt.Q.EabGlW.Good k r i
      (Matrix.single (Formalism.FourierDecayAlt.Q.posL k r i x) (Formalism.FourierDecayAlt.Q.posL k r i y) (1 : ℂ)) :=
    fun x y => Formalism.FourierDecayAlt.Q.EabGlW.hpart_mem (Formalism.FourierDecayAlt.Q.EabGlW.inV_single x y)
  have good0 : Formalism.FourierDecayAlt.Q.EabGlW.Good k r i (0 : Formalism.FourierDecayAlt.Q.Mx k r) :=
    Formalism.FourierDecayAlt.Q.EabGlW.hpart_mem Formalism.FourierDecayAlt.Q.EabGlW.inV_zero
  have goodIf : ∀ (P : Prop) [Decidable P] (x y : Fin (Formalism.FourierDecayAlt.Q.mdim k r i)),
      Formalism.FourierDecayAlt.Q.EabGlW.Good k r i (if P then
        Matrix.single (Formalism.FourierDecayAlt.Q.posL k r i x) (Formalism.FourierDecayAlt.Q.posL k r i y) (1 : ℂ) else 0) := by
    intro P _ x y
    split_ifs
    · exact good x y
    · exact good0
  have hcomm := Formalism.FourierDecayAlt.Q.EabGlW.ec_comm (good a b) (good c d) hL hgU hg.1
  rw [single_one_mul_single_one, single_one_mul_single_one] at hcomm
  simp only [posL_eq_posL_iff] at hcomm
  rw [Formalism.FourierDecayAlt.Q.EabGlW.ec_sub (goodIf _ a d) (goodIf _ c b) hL hgU hg.1] at hcomm
  change _ = _ at hcomm
  refine hcomm.trans ?_
  congr 1
  · split_ifs
    · rfl
    · exact Formalism.FourierDecayAlt.Q.EabGlW.ec_zero f g
  · split_ifs
    · rfl
    · exact Formalism.FourierDecayAlt.Q.EabGlW.ec_zero f g
end

section

theorem qnRdSkew : Formalism.FourierDecayAlt.Q.RdSkew :=
  QnRdSkewW.rdSkew_of QnRdSkewW.skew_reduction_group QnRdSkewW.skew_reduction_analytic
end

section

theorem qnRuleTorus : Formalism.FourierDecayAlt.Q.RuleTorus := by
  open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q PI.QnRT in
  intro E _ _ k r l D f hD hf c hc g₁ hg₁ hmem
  have hcl : c l ≠ 0 := hc l
  have h1 : -((1 / 2 : ℝ) : ℂ) = -star ((1 / 2 : ℝ) : ℂ) := by simp
  have h2 : ((-1 / 2 : ℝ) : ℂ) * Complex.I = -star (((-1 / 2 : ℝ) : ℂ) * Complex.I) := by
    simp
  have h3 : ((1 / 2 : ℝ) : ℂ) = -star (-((1 / 2 : ℝ) : ℂ)) := by simp
  set φ : (Fin r → ℂ) → E := fun c' => f (w1 k r l (c' l) * g₁) with hφ
  set L := fderiv ℝ φ c with hL
  refine ⟨?_, ?_⟩
  · simp only [EH, EabH]
    rw [X1_eq, depthNumbers_threshold_eq, rdV_dz' l D f hf c hcl g₁ hg₁ hmem _ _ h1,
      rdV_dz' l D f hf c hcl g₁ hg₁ hmem _ _ h2]
    simp only [pOp, wirt, if_pos hc]
    rw [lin_single l L (c l * ((1 / 2 : ℝ) : ℂ)), lin_single l L (c l * (((-1 / 2 : ℝ) : ℂ) * Complex.I))]
    generalize L (Pi.single l 1) = A
    generalize L (Pi.single l Complex.I) = B
    obtain ⟨a, b, hab⟩ : ∃ a b : ℝ, c l = (a : ℂ) + (b : ℂ) * Complex.I :=
      ⟨_, _, (Complex.re_add_im _).symm⟩
    rw [hab]
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im]
    match_scalars <;> simp [Complex.ext_iff] <;> ring
  · simp only [EH, EabH]
    rw [first_hermitian_part_diagonal, second_hermitian_part_diagonal, rdV_dz' l D f hf c hcl g₁ hg₁ hmem _ _ h3,
      rdV_dz' l D f hf c hcl g₁ hg₁ hmem _ _ h2]
    simp only [pbOp, wirtBar, if_pos hc]
    rw [lin_single l L (c l * -((1 / 2 : ℝ) : ℂ)), lin_single l L (c l * (((-1 / 2 : ℝ) : ℂ) * Complex.I))]
    generalize L (Pi.single l 1) = A
    generalize L (Pi.single l Complex.I) = B
    obtain ⟨a, b, hab⟩ : ∃ a b : ℝ, c l = (a : ℂ) + (b : ℂ) * Complex.I :=
      ⟨_, _, (Complex.re_add_im _).symm⟩
    rw [hab]
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im]
    match_scalars <;> simp [Complex.ext_iff] <;> ring
end

section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem term_carrier_stable (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) : Formalism.L2.SG.TermDef.TermStable D u u' :=
  PI.TCS.termStable_holds D u u'
end

section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem automorphism_lattice_finite (D : Formalism.BasicNotions.D7) : PI.AutLzFinite.AutLzFin D :=
  PI.AutLzFinite.SlopeTestRemainingChoices.autLzFin_main D
end

section

theorem square_pair_local : PI.SqPair.PLocalAll := PI.SqPairLocal.sqPairLocal_of local_cartan_pair
end

section

theorem stabClassFinite : PI.InHHClassFin.StabClassFinite :=
  PI.UnitaryGroupMassFormula.InHHClassFin.stabClassFinite_of_steps
    (fun _ _ Γ K K' h => PI.UnitaryGroupMassFormula.InHHClassFin.classSet_mono Γ K K' h)
    (fun _ _ Γ K K' h hi => PI.UnitaryGroupMassFormula.InHHClassFin.classSet_finIdx Γ K K' h hi)
    (fun _ _ _ _ Φ Γ K => PI.UnitaryGroupMassFormula.InHHClassFin.classSet_map Φ Γ K)
    PI.UnitaryGroupMassFormula.InHHClassFin.kgNhd PI.UnitaryGroupMassFormula.InHHClassFin.sigConj PI.UnitaryGroupMassFormula.InHHClassFin.frameExists
    PI.UnitaryGroupMassFormula.InHHClassFin.frameIso PI.UnitaryGroupMassFormula.InHHClassFin.frameGram PI.UnitaryGroupMassFormula.InHHClassFin.frameRat
    PI.UnitaryGroupMassFormula.InHHClassFin.levelStep
end
