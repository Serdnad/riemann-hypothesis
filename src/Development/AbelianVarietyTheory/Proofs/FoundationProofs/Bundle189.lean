module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle021
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.Bundle006
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle057
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle185
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle180
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle178
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle179
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle181
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.NumberTheory.ModularForms.Bounds
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001

@[expose] public section

section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem petersson_self_eq (k : ℤ) (f : ℍ → ℂ) (z : ℍ) :
    petersson k f f z = ((‖f z‖ ^ 2 * z.im ^ k : ℝ) : ℂ) := by
  rw [petersson, mul_comm (starRingEnd ℂ (f z)), Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

end GlobalTheory.Hk

namespace GlobalTheory.Hk

theorem pet_self_pos (N l : ℕ) (k : ℤ) (hN : 0 < N) (hl : 0 < l) (f : CuspForm (lev N l) k)
    (hf : f ≠ 0) :
    0 < (pet (lev N l) k ⇑f ⇑f).re ∧ (pet (lev N l) k ⇑f ⇑f).im = 0 := by
  haveI := lev_finiteIndex N l hN hl
  haveI : Finite (SL(2, ℤ) ⧸ lev N l) := Subgroup.finite_quotient_of_finiteIndex
  haveI : Fintype (SL(2, ℤ) ⧸ lev N l) := Fintype.ofFinite _
  set r : ℍ → ℝ := fun z => ‖f z‖ ^ 2 * z.im ^ k with hr_def
  have hr0 : ∀ z, 0 ≤ r z := fun z => mul_nonneg (sq_nonneg _) (zpow_nonneg z.im_pos.le _)
  have hrc : Continuous r := by
    refine (f.holo'.continuous.norm.pow 2).mul ?_
    exact (continuous_im).zpow₀ k fun z => Or.inl z.im_ne_zero
  have hrp : ∀ z, petersson k f f z = (r z : ℂ) := fun z => petersson_self_eq k f z

  set I : SL(2, ℤ) ⧸ lev N l → ℝ := fun q => ∫ z in ModularGroup.fd, r (q.out⁻¹ • z) with hI
  have hpet : pet (lev N l) k ⇑f ⇑f = ((∑ q, I q : ℝ) : ℂ) := by
    rw [pet, finsum_eq_sum_of_fintype, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [hrp, hI]
    exact integral_ofReal
  have hI0 : ∀ q, 0 ≤ I q := fun q => integral_nonneg fun z => hr0 _

  obtain ⟨z₀, hz₀⟩ : ∃ z, f z ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf (CuspForm.ext h)
  obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd z₀
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (lev N l) g
  have hinv : ∀ z, r (((h⁻¹ : lev N l) : SL(2, ℤ)) • z) = r z := by
    intro z
    have e := SlashInvariantFormClass.norm_petersson_smul (f := f) (f' := f) (τ := z)
      (Γ := (lev N l : Subgroup (GL (Fin 2) ℝ)))
      (g := (((h⁻¹ : lev N l) : SL(2, ℤ)) : GL (Fin 2) ℝ)) ⟨_, (h⁻¹).2, rfl⟩
    rw [hrp, hrp, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (hr0 _),
      Real.norm_of_nonneg (hr0 _)] at e
    exact e
  have hpt : (((g : SL(2, ℤ) ⧸ lev N l)).out⁻¹ • (g • z₀)) = ((h⁻¹ : lev N l) : SL(2, ℤ)) • z₀ := by
    rw [hh, smul_smul, mul_inv_rev, inv_mul_cancel_right]
    rfl
  have hIpos : 0 < I (g : SL(2, ℤ) ⧸ lev N l) := by
    have hpos : 0 < r ((g : SL(2, ℤ) ⧸ lev N l).out⁻¹ • (g • z₀)) := by
      rw [hpt, hinv]
      exact mul_pos (pow_pos (norm_pos_iff.2 hz₀) 2) (zpow_pos z₀.im_pos _)
    have hc : Continuous fun z : ℍ => r ((g : SL(2, ℤ) ⧸ lev N l).out⁻¹ • z) :=
      hrc.comp (continuous_const_smul (((g : SL(2, ℤ) ⧸ lev N l).out⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ))
    have hint : IntegrableOn (fun z : ℍ => r ((g : SL(2, ℤ) ⧸ lev N l).out⁻¹ • z)) ModularGroup.fd := by
      obtain ⟨C, hC⟩ := CuspFormClass.petersson_bounded_left k (lev N l : Subgroup (GL (Fin 2) ℝ)) f f
      have fin := UpperTheory.V.Af.Rs.fdFin (UpperTheory.V.Af.Rs.stripIm UpperTheory.V.Af.Rs.volMap) UpperTheory.V.Af.Rs.volMap
      refine Measure.integrableOn_of_bounded (M := C) fin.2.ne hc.aestronglyMeasurable
        (Filter.Eventually.of_forall fun z => ?_)
      have := hC ((g : SL(2, ℤ) ⧸ lev N l).out⁻¹ • z)
      rw [hrp, Complex.norm_real] at this
      exact this
    exact UpperTheory.V.Af.Rs.fdPos UpperTheory.V.Af.Rs.volMap _ hc (fun z => hr0 _) hint _ hg hpos
  rw [hpet, Complex.ofReal_re, Complex.ofReal_im]
  exact ⟨Finset.sum_pos' (fun q _ => hI0 q) ⟨_, Finset.mem_univ _, hIpos⟩, rfl⟩

end GlobalTheory.Hk
end

section

open GlobalTheory.NeedB Polynomial

namespace GlobalTheory.NeedB

theorem tsen : Tsen := by
  intro k K _ _ _ _ _
  exact GlobalTheory.T.isFirstChernClass_of_finiteDimensional_of_forms_have_zeros (RatFunc k) K (GlobalTheory.T.exists_common_zero_homogeneous_ratFunc_of_mul_lt k)

end GlobalTheory.NeedB
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.cuspExpansion_coeff_conj_of_qExpansion_conj : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (s : Ω →+* Ω) (g : ℂ ≃+* ℂ) (N w : ℕ) (f f' : ℍ → ℂ) (h h' : HahnSeries ℚ Ω), (∀ x, g (ε x) = ε (s x)) → 0 < N → QAll (· ∈ ε.range) N (fun τ => DD τ ^ w * f τ) → QConj g N (fun τ => DD τ ^ w * f τ) (fun τ => DD τ ^ w * f' τ) → IsExp ε f h → IsExp ε f' h' → ∀ r, h'.coeff r = s (h.coeff r) := by
  first | exact @GlobalTheory.FN.exp_conj | exact GlobalTheory.FN.exp_conj | (intros; apply GlobalTheory.FN.exp_conj <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.cuspExpansion_coeff_mem_finitelyGenerated_subring : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (f : ℍ → ℂ) (h : HahnSeries ℚ Ω), InR ε.range f → IsExp ε f h → ∃ S : Finset Ω, ∀ r, h.coeff r ∈ Subring.closure (S : Set Ω) := by
  first | exact @GlobalTheory.FN.coeff_fg | exact GlobalTheory.FN.coeff_fg | (intros; apply GlobalTheory.FN.coeff_fg <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.exists_cuspExpansionAtInfinity_of_someLevel : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (f : ℍ → ℂ), InR ε.range f → ∃ h : HahnSeries ℚ Ω, IsExp ε f h := by
  first | exact @GlobalTheory.FN.exists_isExp | exact GlobalTheory.FN.exists_isExp | (intros; apply GlobalTheory.FN.exists_isExp <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

namespace GlobalTheory.Sieg

theorem act_S (x : Fin 2 → ℚ) : act x ModularGroup.S = ![x 1, -x 0] := by
  funext i
  fin_cases i <;> simp [act, ModularGroup.S, Fin.sum_univ_two]

theorem sg_S : ∀ (c : ℕ) (x : Fin 2 → ℚ) (τ : ℍ), admitted c x →
    sg c x (ModularGroup.S • τ) = sg c (act x ModularGroup.S) τ := by
  intro c x τ h
  obtain ⟨hc, hc6, hx⟩ := h
  set z : ℂ := (x 1 : ℂ) * (τ : ℂ) - (x 0 : ℂ) with hz
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  have h1 : pt x (ModularGroup.S • τ) = z / (τ : ℂ) := by
    rw [pt, UpperHalfPlane.modular_S_smul, hz]
    simp only [UpperHalfPlane.coe_mk]
    field_simp
    ring
  have h2 : pt (act x ModularGroup.S) τ = z := by
    rw [act_S, pt, hz]
    simp
    ring
  have hnot : ∀ m n : ℤ, (c : ℂ) * z ≠ (m : ℂ) * (τ : ℂ) + n := by
    intro m n heq
    apply hx
    have him := congrArg Complex.im heq
    have hre := congrArg Complex.re heq
    simp [hz, mul_sub] at him hre
    have hpos : 0 < τ.im := τ.im_pos
    have e1 : (c : ℝ) * (x 1 : ℝ) = m := by
      have : ((c : ℝ) * (x 1 : ℝ) - m) * τ.im = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · exact absurd h hpos.ne'
    have e0 : (c : ℝ) * (x 0 : ℝ) = ((-n : ℤ) : ℝ) := by
      rw [← mul_assoc, e1] at hre
      push_cast
      linarith
    refine ⟨⟨-n, ?_⟩, ⟨m, ?_⟩⟩
    · exact_mod_cast e0.symm
    · exact_mod_cast e1.symm
  unfold sg
  rw [h1, h2]
  exact GlobalTheory.T.smoothedThetaQProduct_modularS_transform c τ z hc hc6 hnot

end GlobalTheory.Sieg
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.saturation_levelFunctions_integralRelation : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (M n : ℕ) (a b : ℍ → ℂ) (p : ℕ → ℍ → ℂ), 0 < M → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) a → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) b → b ≠ 0 → (∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ τ : ℍ, a (γ • τ) * b τ = a τ * b (γ • τ)) → (∀ i, InR ε.range (p i)) → p n ≠ 0 → (∀ τ, ∑ i ∈ Finset.range (n + 1), p i τ * a τ ^ i * b τ ^ (n - i) = 0) → ∃ h : ℍ → ℂ, InR ε.range h ∧ ∀ τ, p n τ * a τ = h τ * b τ := by
  first | exact @GlobalTheory.FN.Sat.sat | exact GlobalTheory.FN.Sat.sat | (intros; apply GlobalTheory.FN.Sat.sat <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.exists_jInvariant_in_modularFunctionFractionField : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε), ∃ a : GlobalTheory.FN.ring ε.range, (a : ℍ → ℂ) = jT ∧ (∀ γ : SL(2, ℤ), T.sl (ofSL γ) (T.io a) = T.io a) ∧ (T.exp (T.io a)).coeff (-1) = 1 ∧ (∀ r : ℚ, r < -1 → (T.exp (T.io a)).coeff r = 0) ∧ ∀ r : ℚ, ∃ n : ℤ, (T.exp (T.io a)).coeff r = n := by
  first | exact @GlobalTheory.FN.j_in_frac | exact GlobalTheory.FN.j_in_frac | (intros; apply GlobalTheory.FN.j_in_frac <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.modularFunctionFractionField_an_sl_germ : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (g : GQ) (f : T.K) (φ : ℂ → ℂ), T.an f = (φ : Mero) → T.an (T.sl g f) = ((fun z => φ (mob g z)) : Mero) := by
  first | exact @GlobalTheory.FN.an_sl_germ | exact GlobalTheory.FN.an_sl_germ | (intros; apply GlobalTheory.FN.an_sl_germ <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.modularFunctionFractionField_sl_rightAction : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε), (∀ f, T.sl 1 f = f) ∧ ∀ g h f, T.sl (g * h) f = T.sl h (T.sl g f) := by
  first | exact @GlobalTheory.FN.frac_sl_right_action | exact GlobalTheory.FN.frac_sl_right_action | (intros; apply GlobalTheory.FN.frac_sl_right_action <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.modularFunctionFractionField_const_and_quotient : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε), (∀ c : Ω, T.an (algebraMap Ω T.K c) = ((fun _ => ε c : ℂ → ℂ) : Mero)) ∧ ∀ f : T.K, ∃ a b : ℂ → ℂ, DifferentiableOn ℂ a Hs ∧ DifferentiableOn ℂ b Hs ∧ (b : Mero) ≠ 0 ∧ T.an f * (b : Mero) = (a : Mero) := by
  first | exact @GlobalTheory.FN.frac_const_and_quot | exact GlobalTheory.FN.frac_const_and_quot | (intros; apply GlobalTheory.FN.frac_const_and_quot <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.modularFunctionFractionField_exp_upperTriangular : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (g : GQ), ent g 1 0 = 0 → ∀ (f : T.K) (r : ℚ), (T.exp (T.sl g f)).coeff (r * ent g 0 0 / ent g 1 1) = eOm ε (r * ent g 0 1 / ent g 1 1) * (T.exp f).coeff r := by
  first | exact @GlobalTheory.FN.exp_sl_coeff_upper | exact GlobalTheory.FN.exp_sl_coeff_upper | (intros; apply GlobalTheory.FN.exp_sl_coeff_upper <;> assumption)
end
