module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousMatQApply
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle207
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle344
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle361
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.CoeffSubstInvMemOfTwoLeOrder
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNormPrime
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle296
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle237
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PhAtMulByNorm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle336
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.AdditionIdentityOfSigmaFormulaUnit
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle007
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle001
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle004
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.CyclotomicDvdExpandOfCoprime
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle016
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle018
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgBasic

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.SelPerp

variable {l : ℕ} [Fact l.Prime]

def tau (c : Coef l) : c.O →ₗ[ℤ_[l]] ℤ_[l] := Classical.choose (coef_dual_free_rank_one l c)

theorem tau_spec (c : Coef l) : ∀ f : c.O →ₗ[ℤ_[l]] ℤ_[l], ∃! a : c.O, ∀ x, f x = tau c (a * x) :=
  Classical.choose_spec (coef_dual_free_rank_one l c)

theorem norm_unit (c : Coef l) (u : c.Oˣ) : ‖((u : c.O) : Qbar l)‖ = 1 := by
  have h1 := CupCob.norm_le_one_of_mem c (u : c.O).2
  have h2 := CupCob.norm_le_one_of_mem c ((u⁻¹ : c.Oˣ) : c.O).2
  have h3 : ((u : c.O) : Qbar l) * (((u⁻¹ : c.Oˣ) : c.O) : Qbar l) = 1 := by
    rw [← Subalgebra.coe_mul, Units.mul_inv]; rfl
  have h4 := congrArg norm h3
  rw [norm_mul, norm_one] at h4
  nlinarith [norm_nonneg ((u : c.O) : Qbar l), norm_nonneg (((u⁻¹ : c.Oˣ) : c.O) : Qbar l)]

theorem norm_l_lt_one : ‖((l : ℕ) : Qbar l)‖ < 1 := by
  have e : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (Qbar l) ((l : ℕ) : ℚ_[l]) := by simp
  rw [e, norm_algebraMap']
  exact Padic.norm_p_lt_one

theorem dvd_of_mem_Ik (c : Coef l) (n : ℕ) {x : c.O} (hx : x ∈ Ik c n) : ∃ y : c.O, x = (l : c.O) ^ n * y := by
  rcases eq_or_ne x 0 with rfl | hx0
  · exact ⟨0, by simp⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
  have hl0 : (l : c.O) ≠ 0 := by
    intro h
    have : ((l : c.O) : Qbar l) = 0 := by rw [h]; rfl
    rw [SubringClass.coe_natCast] at this
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) this
  obtain ⟨e, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ
  have nl : ‖((l : c.O) : Qbar l)‖ = ‖((ϖ : c.O) : Qbar l)‖ ^ e := by
    rw [hw, Subalgebra.coe_mul, Subalgebra.coe_pow, norm_mul, norm_pow, norm_unit, one_mul]
  have nx : ‖((x : c.O) : Qbar l)‖ = ‖((ϖ : c.O) : Qbar l)‖ ^ k := by
    rw [hu, Subalgebra.coe_mul, Subalgebra.coe_pow, norm_mul, norm_pow, norm_unit, one_mul]
  have hlt : ‖((l : c.O) : Qbar l)‖ < 1 := by rw [SubringClass.coe_natCast]; exact norm_l_lt_one
  have hϖ1 : ‖((ϖ : c.O) : Qbar l)‖ ≤ 1 := CupCob.norm_le_one_of_mem c ϖ.2
  have he : e ≠ 0 := by
    rintro rfl
    rw [nl, pow_zero] at hlt
    exact lt_irrefl _ hlt
  have hϖlt : ‖((ϖ : c.O) : Qbar l)‖ < 1 := by
    rcases hϖ1.lt_or_eq with h | h
    · exact h
    · rw [nl, h, one_pow] at hlt; exact absurd hlt (lt_irrefl _)
  have hϖ0 : 0 < ‖((ϖ : c.O) : Qbar l)‖ := by
    rw [norm_pos_iff]
    intro h
    exact hϖ.ne_zero (Subtype.ext h)
  have hle : e * n ≤ k := by
    have h := (mem_Ik.1 hx)
    have e2 : ‖((l : ℕ) : Qbar l) ^ n‖ = ‖((ϖ : c.O) : Qbar l)‖ ^ (e * n) := by
      rw [norm_pow, ← SubringClass.coe_natCast c.O, nl, pow_mul]
    rw [nx, e2] at h
    exact (pow_le_pow_iff_right_of_lt_one₀ hϖ0 hϖlt).1 h
  refine ⟨(u : c.O) * ϖ ^ (k - e * n) * ((w⁻¹ : c.Oˣ) : c.O) ^ n, ?_⟩
  rw [hu, hw]
  have hk : k = e * n + (k - e * n) := by omega
  conv_lhs => rw [hk]
  calc (u : c.O) * ϖ ^ (e * n + (k - e * n))
      = (u : c.O) * ϖ ^ (k - e * n) * (((w : c.O) * ((w⁻¹ : c.Oˣ) : c.O)) ^ n * ϖ ^ (e * n)) := by
        rw [Units.mul_inv, one_pow, one_mul, pow_add]; ring
    _ = _ := by ring

theorem tau_red_zero (c : Coef l) (n : ℕ) {x : c.O} (hx : x ∈ Ik c n) :
    PadicInt.toZModPow n (tau c x) = 0 := by
  obtain ⟨y, rfl⟩ := dvd_of_mem_Ik c n hx
  have e : (l : c.O) ^ n * y = ((l : ℤ_[l]) ^ n) • y := by
    rw [Algebra.smul_def, map_pow, map_natCast]
  rw [e, map_smul, smul_eq_mul, map_mul, map_pow, map_natCast, ← Nat.cast_pow, ZMod.natCast_self, zero_mul]

def lft (c : Coef l) (n : ℕ) : Qn c n → c.O := Function.surjInv (red_surjective c n)

theorem red_lft (c : Coef l) (n : ℕ) (b : Qn c n) : red c n (lft c n b) = b :=
  Function.surjInv_eq (red_surjective c n) b

theorem tau_congr (c : Coef l) (n : ℕ) {x y : c.O} (h : red c n x = red c n y) :
    PadicInt.toZModPow n (tau c x) = PadicInt.toZModPow n (tau c y) := by
  rw [← sub_eq_zero, ← map_sub, ← map_sub]
  refine tau_red_zero c n ?_
  rw [← red_eq_zero_iff_mem, map_sub, h, sub_self]

def tbA (c : Coef l) (n : ℕ) : Qn c n →+ ZMod (l ^ n) where
  toFun b := PadicInt.toZModPow n (tau c (lft c n b))
  map_zero' := by
    rw [← map_zero (red c n), tau_congr c n (red_lft c n _), map_zero, map_zero]
  map_add' a b := by
    obtain ⟨x, rfl⟩ := red_surjective c n a
    obtain ⟨y, rfl⟩ := red_surjective c n b
    rw [← map_add (f := _), tau_congr c n (red_lft c n _), tau_congr c n (red_lft c n _),
      tau_congr c n (red_lft c n _), map_add, map_add]

theorem tbA_red (c : Coef l) (n : ℕ) (x : c.O) : tbA c n (red c n x) = PadicInt.toZModPow n (tau c x) :=
  tau_congr c n (red_lft c n _)

def pairA (c : Coef l) (n : ℕ) (y : Mn c n) : Mn c n →+ ZMod (l ^ n) where
  toFun x := tbA c n (x 0 * y 1 - x 1 * y 0)
  map_zero' := by simp
  map_add' a b := by
    rw [← map_add (f := _)]; congr 1; simp only [Pi.add_apply]; ring

def Phi (c : Coef l) (n : ℕ) : Mn c n →ₗ[ZMod (l ^ n)] TDual (ZMod (l ^ n)) (Mn c n) :=
  (AddMonoidHom.mk' (fun y => TDual.mk ((pairA c n y).toZModLinearMap (l ^ n))) (fun a b => by
    refine DFunLike.ext _ _ fun x => ?_
    show tbA c n _ = tbA c n _ + tbA c n _
    rw [← map_add (f := _)]; congr 1; simp only [Pi.add_apply]; ring)).toZModLinearMap (l ^ n)

theorem Phi_apply (c : Coef l) (n : ℕ) (y x : Mn c n) : Phi c n y x = tbA c n (x 0 * y 1 - x 1 * y 0) := rfl

theorem red_mulVec (c : Coef l) (n : ℕ) (M : Matrix (Fin 2) (Fin 2) (Qbar l)) (hM : ∀ i j, M i j ∈ c.O)
    (v : Fin 2 → Qbar l) (hv : ∀ i, v i ∈ c.O) (i : Fin 2) :
    red c n ⟨(M *ᵥ v) i, CupCob.mulVec_mem c M v hM hv i⟩ =
      ((Matrix.of fun i j => red c n ⟨M i j, hM i j⟩) *ᵥ fun j => red c n ⟨v j, hv j⟩) i := by
  have e : (⟨(M *ᵥ v) i, CupCob.mulVec_mem c M v hM hv i⟩ : c.O) =
      (⟨M i 0, hM i 0⟩ : c.O) * ⟨v 0, hv 0⟩ + (⟨M i 1, hM i 1⟩ : c.O) * ⟨v 1, hv 1⟩ := by
    apply Subtype.ext
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Subalgebra.coe_add, Subalgebra.coe_mul]
  rw [e, map_add (f := _), map_mul, map_mul]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply]

def lftV (c : Coef l) (n : ℕ) (y : Mn c n) : Fin 2 → Qbar l := fun i => (lft c n (y i) : Qbar l)

theorem lftV_mem (c : Coef l) (n : ℕ) (y : Mn c n) (i : Fin 2) : lftV c n y i ∈ c.O := (lft c n (y i)).2

theorem red_lftV (c : Coef l) (n : ℕ) (y : Mn c n) (i : Fin 2) : red c n ⟨lftV c n y i, lftV_mem c n y i⟩ = y i :=
  red_lft c n (y i)

theorem cg_of_red {c : Coef l} {n : ℕ} {a b : Qbar l} (ha : a ∈ c.O) (hb : b ∈ c.O)
    (h : red c n ⟨a, ha⟩ = red c n ⟨b, hb⟩) : Cg n a b := (red_eq_iff ⟨a, ha⟩ ⟨b, hb⟩).1 h

theorem red_of_cg {c : Coef l} {n : ℕ} {a b : Qbar l} (ha : a ∈ c.O) (hb : b ∈ c.O)
    (h : Cg n a b) : red c n ⟨a, ha⟩ = red c n ⟨b, hb⟩ := (red_eq_iff ⟨a, ha⟩ ⟨b, hb⟩).2 h

end GlobalTheory.Ord2.SelPerp
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries

theorem _root_.GlobalTheory.T.exists_poly_in_root_of_inertia_cyclotomic_fixed : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω) (m : ℕ) (ζ : Ω), IsPrimitiveRoot ζ (l ^ m) → ∀ u : Ω, (∀ s ∈ Ine (F := ℚ) A, cycMod ℚ Ω l m s = 1 → s u = u) → ∃ Q : Polynomial Ω, (∀ x ∈ Q.coeffs, ∀ s ∈ Ine (F := ℚ) A, s x = x) ∧ Q.eval ζ = u := by
  first | exact @GlobalTheory.InertiaCycFixed.exists_poly_of_fixed | exact GlobalTheory.InertiaCycFixed.exists_poly_of_fixed | (intros; apply GlobalTheory.InertiaCycFixed.exists_poly_of_fixed <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col

theorem _root_.GlobalTheory.T.exists_polynomial_eval_eq_of_inertia_fixed : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω) (ζ u : Ω), (∀ s ∈ Ine (F := ℚ) A, s ζ = ζ → s u = u) → ∃ P : Polynomial Ω, (∀ s ∈ Ine (F := ℚ) A, ∀ d, s (P.coeff d) = P.coeff d) ∧ P.eval ζ = u := by
  first | exact @GlobalTheory.exists_polynomial_inertia_fixed_eval_eq | exact GlobalTheory.exists_polynomial_inertia_fixed_eval_eq | (intros; apply GlobalTheory.exists_polynomial_inertia_fixed_eval_eq <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section
namespace GlobalTheory.CMEndo

section Series
open Formalism.MainNotions.GL3Theta

variable {p : ℕ} [Fact p.Prime] (g : G1 p) {σ : Type*}

theorem const_l : PowerSeries.constantCoeff g.l = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [GL3Theta.G1.l, flog]

theorem ex_l (h : g.Ok) : PowerSeries.subst g.l g.ex = PowerSeries.X := by
  obtain ⟨-, -, h0, h1⟩ := h
  have hl : ∀ _ : Unit, MvPowerSeries.constantCoeff (g.l : MvPowerSeries Unit ℂ_[p]) = 0 := fun _ => const_l g
  have he : ∀ _ : Unit, MvPowerSeries.constantCoeff (g.ex : MvPowerSeries Unit ℂ_[p]) = 0 := fun _ => h0
  have h2 : ∀ i : Unit, MvPowerSeries.subst (fun _ : Unit => (g.ex : MvPowerSeries Unit ℂ_[p]))
      (g.l : MvPowerSeries Unit ℂ_[p]) = MvPowerSeries.X i := fun _ => h1
  have h3 := GlobalTheory.FormalInv.eq_substInv_of_right hl he h2
  have h4 := GlobalTheory.FormalInv.subst_substInv_left hl
    (IsUnit.of_mul_eq_one _ (GlobalTheory.FormalInv.linearPart_mul_eq_one hl he h2)) ()
  rw [← h3] at h4
  exact h4

theorem pt_lg (h : g.Ok) {a : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0) :
    g.pt (g.lg a) = a := by
  have ha' := PowerSeries.HasSubst.of_constantCoeff_zero ha
  rw [GL3Theta.G1.pt, GL3Theta.G1.lg, ← PowerSeries.subst_comp_subst_apply
    (PowerSeries.HasSubst.of_constantCoeff_zero' (const_l g)) ha', ex_l g h, PowerSeries.subst_X ha']

theorem subst_zero {f : PowerSeries ℂ_[p]} (hf : PowerSeries.constantCoeff f = 0) :
    PowerSeries.subst (0 : MvPowerSeries σ ℂ_[p]) f = 0 := by
  obtain ⟨k, rfl⟩ := PowerSeries.X_dvd_iff.2 hf
  have h0 : PowerSeries.HasSubst (0 : MvPowerSeries σ ℂ_[p]) := PowerSeries.HasSubst.of_constantCoeff_zero (map_zero _)
  rw [PowerSeries.subst_mul h0, PowerSeries.subst_X h0, zero_mul]

theorem mulBy_one (h : g.Ok) (i : σ) : g.mulBy 1 (GL3Theta.Xv i) = GL3Theta.Xv i := by
  rw [GL3Theta.G1.mulBy, map_one, one_mul, pt_lg g h (MvPowerSeries.constantCoeff_X i)]

theorem mulBy_zero (h : g.Ok) (a : MvPowerSeries σ ℂ_[p]) : g.mulBy 0 a = 0 := by
  rw [GL3Theta.G1.mulBy, map_zero, zero_mul, GL3Theta.G1.pt, subst_zero h.2.2.1]

theorem constantCoeff_subst_zero {f : PowerSeries ℂ_[p]} (hf : PowerSeries.constantCoeff f = 0)
    {a : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst a f) = 0 := by
  obtain ⟨k, rfl⟩ := PowerSeries.X_dvd_iff.2 hf
  have h0 : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero ha
  rw [PowerSeries.subst_mul h0, PowerSeries.subst_X h0, map_mul, ha, zero_mul]

theorem constantCoeff_lg {a : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0) :
    MvPowerSeries.constantCoeff (g.lg a) = 0 :=
  constantCoeff_subst_zero (const_l g) ha

theorem constantCoeff_pt (h : g.Ok) {a : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0) :
    MvPowerSeries.constantCoeff (g.pt a) = 0 :=
  constantCoeff_subst_zero h.2.2.1 ha

theorem lg_pt (h : g.Ok) {a : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0) :
    g.lg (g.pt a) = a := by
  have ha' := PowerSeries.HasSubst.of_constantCoeff_zero ha
  rw [G1.lg, G1.pt, ← PowerSeries.subst_comp_subst_apply
    (PowerSeries.HasSubst.of_constantCoeff_zero' h.2.2.1) ha', h.2.2.2, PowerSeries.subst_X ha']

theorem lg_mulBy (h : g.Ok) (c : ℂ_[p]) {a : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0) :
    g.lg (g.mulBy c a) = MvPowerSeries.C c * g.lg a := by
  rw [G1.mulBy, lg_pt g h]
  rw [map_mul, constantCoeff_lg g ha, mul_zero]

theorem mulBy_add (h : g.Ok) (c c' : ℂ_[p]) {a : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0) :
    g.mulBy (c + c') a = g.add (g.mulBy c a) (g.mulBy c' a) := by
  rw [G1.add, lg_mulBy g h c ha, lg_mulBy g h c' ha, G1.mulBy, map_add (f := _), add_mul]

theorem add_eq_subst (h : g.Ok) (A B : MvPowerSeries σ ℂ_[p]) (hA : MvPowerSeries.constantCoeff A = 0)
    (hB : MvPowerSeries.constantCoeff B = 0) :
    g.add A B = MvPowerSeries.subst ![A, B] (g.add (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) := by
  have hab : MvPowerSeries.HasSubst ![A, B] :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by fin_cases i <;> simp [hA, hB])
  have hs : MvPowerSeries.constantCoeff (g.lg (Xv 0) + g.lg (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := by
    rw [map_add (f := _), constantCoeff_lg g (MvPowerSeries.constantCoeff_X _),
      constantCoeff_lg g (MvPowerSeries.constantCoeff_X _), add_zero]
  have hsl : ∀ i : Fin 2, MvPowerSeries.subst ![A, B] (g.lg (Xv i) : MvPowerSeries (Fin 2) ℂ_[p]) =
      g.lg (![A, B] i) := by
    intro i
    have hX : PowerSeries.HasSubst (Xv i : MvPowerSeries (Fin 2) ℂ_[p]) :=
      PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X _)
    rw [G1.lg, G1.lg, PowerSeries.subst, PowerSeries.subst,
      MvPowerSeries.subst_comp_subst_apply
      (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => MvPowerSeries.constantCoeff_X i)) hab]
    congr 1
    funext _
    exact MvPowerSeries.subst_X hab i
  rw [G1.add, G1.add, G1.pt, G1.pt, PowerSeries.subst, PowerSeries.subst,
    MvPowerSeries.subst_comp_subst_apply
      (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hs)) hab]
  congr 1
  funext _
  rw [MvPowerSeries.subst_add hab, hsl 0, hsl 1]
  rfl

theorem integralMv_zero : IntegralMv (0 : MvPowerSeries σ ℂ_[p]) := fun n => by
  simp [IsIntP]

theorem integralMv_X (i : σ) : IntegralMv (Xv i : MvPowerSeries σ ℂ_[p]) := fun n => by
  unfold IsIntP
  rw [MvPowerSeries.coeff_X]
  split_ifs <;> simp

theorem integral_mulBy_semiring : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), g.Ok →
    IntegralMv (g.add (GL3Theta.Xv 0) (GL3Theta.Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) →
    IntegralMv (g.mulBy 0 (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p]) ∧
    IntegralMv (g.mulBy 1 (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p]) ∧
    ∀ c c' : ℂ_[p], IntegralMv (g.mulBy c (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p]) →
      IntegralMv (g.mulBy c' (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p]) →
      IntegralMv (g.mulBy (c + c') (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p]) := by
  intro p _ g h hadd
  have hX : MvPowerSeries.constantCoeff (Xv () : MvPowerSeries Unit ℂ_[p]) = 0 := MvPowerSeries.constantCoeff_X _
  refine ⟨?_, ?_, ?_⟩
  · rw [mulBy_zero g h]; exact integralMv_zero
  · rw [mulBy_one g h]; exact integralMv_X ()
  · intro c c' hc hc'
    have h0 : ∀ d : ℂ_[p], MvPowerSeries.constantCoeff (g.mulBy d (Xv ()) : MvPowerSeries Unit ℂ_[p]) = 0 :=
      fun d => constantCoeff_pt g h (by rw [map_mul, constantCoeff_lg g hX, mul_zero])
    rw [mulBy_add g h c c' hX, add_eq_subst g h _ _ (h0 c) (h0 c')]
    exact ReciprocityTheory.ChartRestriction.L1.integralMv_subst2 (fun d => hadd d)
      (fun i => by fin_cases i <;> simp [h0]) (fun i => by
        fin_cases i
        · exact fun d => hc d
        · exact fun d => hc' d)

end Series

theorem endInt_all (D : D7) : GL3Theta.endInt D := by
  intro p _ cc δ g hA α hα
  have hok : g.Ok := hA.2.2.2.2
  have hadd := ((GlobalTheory.ThetaCube.cube_addInt_beBiadd D).2.1 p cc δ g hA).1
  obtain ⟨h0, h1, hplus⟩ := integral_mulBy_semiring p g hok hadd
  set S : Set ℂ_[p] := {c | IntegralMv (g.mulBy c (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p])} with hS
  have hcl : IsClosed S := GlobalTheory.mulBy_integral_isClosed p g
  have hnat : ∀ n : ℕ, (n : ℂ_[p]) ∈ S := by
    intro n
    induction n with
    | zero => rw [Nat.cast_zero]; exact h0
    | succ n ih =>
      rw [Nat.cast_succ]; exact hplus _ _ ih h1
  by_cases hp : p = 2
  · subst hp
    have h2 := GlobalTheory.TwoAdicFirst.fst_mem_closure_natCast D g.lam α hα
    have hsub : closure (Set.range (Nat.cast : ℕ → ℂ_[2])) ⊆ S :=
      closure_minimal (by rintro _ ⟨n, rfl⟩; exact hnat n) hcl
    exact hsub h2
  · obtain ⟨β, hβ, γ, hγ, hb1, hb2, hc1, hc2, rfl⟩ := Formalism.MainNotions.Ext.CutA.okpTwoUnits2_holds D p g.lam hp α hα
    have hunit : ∀ β ∈ GL3Theta.OKp D g.lam, ‖β.1‖ = 1 → ‖β.2‖ = 1 → β.1 ∈ S := by
      intro β hβ h1 h2
      have hc := Formalism.MainNotions.Ext.CutA.okpUnitsDense_holds D p g.lam hp β hβ h1 h2
      have hm := map_mem_closure continuous_fst hc (t := S) (by
        rintro _ ⟨a, ha, rfl⟩
        exact GlobalTheory.CMUnit.unit_endo D p cc δ g hA hp a ha)
      rwa [hcl.closure_eq] at hm
    exact hplus _ _ (hunit β hβ hb1 hb2) (hunit γ hγ hc1 hc2)

theorem endo_all : ∀ D : D7, GL3Theta.endInt D ∧ GL3Theta.phNorm D ∧ GL3Theta.beConj D := by
  intro D
  have he := endInt_all D
  have ha := (GlobalTheory.ThetaCube.cube_addInt_beBiadd D).2.1
  have hB := (GlobalTheory.ThetaCube.cube_addInt_beBiadd D).2.2
  have hok : Formalism.MainNotions.Ext.CutA.PhNormOK D := GlobalTheory.CMNormPhi.phAt_mulBy_norm D he ha
  have hn := Formalism.MainNotions.Ext.CutA.phNorm_of' Formalism.MainNotions.Ext.CutA.phNormOfUnits_holds Formalism.MainNotions.Ext.CutA.phNormClosed_holds D hok he ha hB
  exact ⟨he, hn, Formalism.MainNotions.Ext.CutA.beConj_of' Formalism.MainNotions.Ext.CutA.beConjOfNorm_holds D he ha hn hB⟩

end GlobalTheory.CMEndo
end
end
