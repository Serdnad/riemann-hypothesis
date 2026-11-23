module

public import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.Bundle001
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle049
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FiltrationCocycleLiftCriterion
public import Formalism.LandauZeroFreeBounds.Statement
public import Mathlib.Analysis.Analytic.Order
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle031
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle034
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TruncatedPerronPsi
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle048
public import Formalism.SharpRestriction.GrowthBounds.IsResidueClassZero
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import GroundTheory.GlobalFields.Artin.Bundle001
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
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle003
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

theorem _root_.GlobalTheory.T.prime_pow_smul_goodLift_mem_setupLattice : ∀ (g : ℕ) (S : JMB.Setup g) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N₀ n : ℕ), S.Ok → ∀ y ∈ AddSubgroup.closure {y : Fin g → ℂ | ∃ κ ∈ JMB.OK S.d, ‖JMB.lamA lam ((starRingEnd ℂ) κ)‖ ≤ (p : ℝ) ^ (-(2 * n : ℤ)) ∧ ∃ x ∈ S.La, y = (κ * (N₀ : ℂ) / (p : ℂ) ^ n) • x}, ((p : ℂ) ^ n) • y ∈ S.La := by
  first | exact @GlobalTheory.goodLift_pow_smul_mem | exact GlobalTheory.goodLift_pow_smul_mem | (intros; apply GlobalTheory.goodLift_pow_smul_mem <;> assumption)
end

section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

theorem _root_.GlobalTheory.T.eq_on_padicInt_of_eq_on_naturals_moment : ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (Ω : ℂ_[p]) (g : ℕ) (S : JMB.Setup g) (r n k : ℕ) (bS : Fin r → Fin g → ℂ) (Y : Fin g → ℂ) (ys : Fin k → Fin g → ℂ) (f : C(Fin r → ℤ_[p], ℂ_[p])), (∀ a : Fin r → ℕ, f (fun i => (a i : ℤ_[p])) = JMB.lamA lam (JMB.kap S.Hm (JMB.vecA n bS (fun i => (a i : ℤ_[p]))) Y) * ∏ j, JMB.pairD lam Ω S.d S.Hm bS (ys j) (fun i => (a i : ℤ_[p]))) → ∀ a, f a = JMB.lamA lam (JMB.kap S.Hm (JMB.vecA n bS a) Y) * ∏ j, JMB.pairD lam Ω S.d S.Hm bS (ys j) a := by
  first | exact @GlobalTheory.MomentPinned.eq_of_natCast | exact GlobalTheory.MomentPinned.eq_of_natCast | (intros; apply GlobalTheory.MomentPinned.eq_of_natCast <;> assumption)
end

section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory

namespace GlobalTheory.ZeroFreeHalf

theorem inRegion_of_max {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 3 ≤ N) {ρ : ℂ}
    (h : 1 - c / 2 / Real.log (max (N : ℝ) (N * |ρ.im|)) ≤ ρ.re) : Formalism.ZeroFreeDirichlet.InRegion c N ρ := by
  unfold Formalism.ZeroFreeDirichlet.InRegion
  set M := max (N : ℝ) (N * |ρ.im|) with hM
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hMN : (N : ℝ) ≤ M := le_max_left _ _
  have hMt : (N : ℝ) * |ρ.im| ≤ M := le_max_right _ _
  have hMpos : 0 < M := by linarith
  have ht := abs_nonneg ρ.im
  have hA : (N : ℝ) * (|ρ.im| + 2) ≤ M ^ 2 := by nlinarith
  have hA1 : 1 < (N : ℝ) * (|ρ.im| + 2) := by nlinarith
  have hL : 0 < Real.log ((N : ℝ) * (|ρ.im| + 2)) := Real.log_pos hA1
  have hle : Real.log ((N : ℝ) * (|ρ.im| + 2)) ≤ 2 * Real.log M := by
    have e := Real.log_le_log (by linarith) hA
    rw [Real.log_pow] at e
    push_cast at e
    linarith
  have hdiv : c / (2 * Real.log M) ≤ c / Real.log ((N : ℝ) * (|ρ.im| + 2)) :=
    div_le_div_of_nonneg_left hc.le hL hle
  rw [div_div] at h
  linarith

theorem isRealChar_of_sq {N : ℕ} (χ : DirichletCharacter ℂ N) (h : χ ^ 2 = 1) : IsRealChar χ := by
  intro a
  by_cases ha : IsUnit a
  · have h2 : χ a * χ a = 1 := by
      rw [← pow_two, ← MulChar.pow_apply' χ two_ne_zero, h, MulChar.one_apply ha]
    rcases mul_self_eq_one_iff.mp h2 with e | e <;> simp [e]
  · simp [MulChar.map_nonunit χ ha]

theorem ne_one_of_isPrimitive {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hp : χ.IsPrimitive)
    (hN : 3 ≤ N) : χ ≠ 1 := by
  intro h1
  rw [DirichletCharacter.isPrimitive_def, h1, DirichletCharacter.conductor_one] at hp
  omega

theorem main : Formalism.ZeroFreeDirichlet.ZFRDirichlet → ∃ c : ℝ, 0 < c ∧ (∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → 3 ≤ N → ∀ ρ : ℂ, LFunction χ ρ = 0 → 1 - c / Real.log (max (N : ℝ) (N * |ρ.im|)) ≤ ρ.re → IsRealChar χ ∧ ρ.im = 0 ∧ analyticOrderNatAt (LFunction χ) ρ = 1 ∧ ∀ ρ' : ℂ, LFunction χ ρ' = 0 → 1 - c / Real.log (max (N : ℝ) (N * |ρ'.im|)) ≤ ρ'.re → ρ' = ρ) ∧ (∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≤ 1 - c / Real.log (|ρ.im| + 3)) := by
  intro hZ
  obtain ⟨c, hc, hZ⟩ := hZ
  refine ⟨c / 2, by positivity, ?_, ?_⟩
  · intro N _ χ hp hN ρ hρ hreg
    have hχ1 : χ ≠ 1 := ne_one_of_isPrimitive χ hp hN
    obtain ⟨hsq, -, him, hder, huniq⟩ :=
      hZ N χ ρ (inRegion_of_max hc hN hreg) ⟨Or.inl hχ1, hρ⟩
    refine ⟨isRealChar_of_sq χ hsq, him, ?_, ?_⟩
    · have han : AnalyticAt ℂ (LFunction χ) ρ :=
        (DirichletCharacter.differentiable_LFunction hχ1).analyticAt ρ
      simp [analyticOrderNatAt, han.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hρ hder]
    · intro ρ' hρ' hreg'
      exact (huniq χ ρ' (inRegion_of_max hc hN hreg') ⟨Or.inl hχ1, hρ'⟩).2
  · intro ρ hρ _ hre1
    by_contra hlt
    rw [not_le] at hlt
    have ht := abs_nonneg ρ.im
    have hR : Formalism.ZeroFreeDirichlet.InRegion c 1 ρ := by
      unfold Formalism.ZeroFreeDirichlet.InRegion
      have ha : 0 < Real.log (|ρ.im| + 2) := Real.log_pos (by linarith)
      have hab : Real.log (|ρ.im| + 2) ≤ 2 * Real.log (|ρ.im| + 3) := by
        have e := Real.log_le_log (by linarith) (by linarith : |ρ.im| + 2 ≤ |ρ.im| + 3)
        have e2 : 0 ≤ Real.log (|ρ.im| + 3) := Real.log_nonneg (by linarith)
        linarith
      have hdiv := div_le_div_of_nonneg_left hc.le ha hab
      rw [div_div] at hlt
      simp only [Nat.cast_one, one_mul]
      linarith
    have hne : ρ ≠ 1 := by
      rintro rfl
      simp at hre1
    have hZ0 : Formalism.ZeroFreeDirichlet.IsLZero (1 : DirichletCharacter ℂ 1) ρ :=
      ⟨Or.inr hne, by rw [DirichletCharacter.LFunction_modOne_eq]; exact hρ⟩
    exact (hZ 1 1 ρ hR hZ0).2.1 rfl

end GlobalTheory.ZeroFreeHalf
end

section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory

namespace GlobalTheory.ExplicitFormula

theorem truncated_explicit_formula : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∀ u T : ℝ, 2 ≤ T → T ≤ u → {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T ∧ LFunction χ ρ = 0}.Finite ∧ ‖psi0 χ u + ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T ∧ LFunction χ ρ = 0}, ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤ C * (u * Real.log (N * u * T) ^ 2 / T + Real.log (N * u) + ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1 ∧ LFunction χ ρ = 0}, ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℝ) / ‖ρ‖) := by
  obtain ⟨C₁, hC₁, h₁⟩ := GlobalTheory.PerronPsi.truncated_perron_psi
  obtain ⟨C₂, hC₂, h₂⟩ := GlobalTheory.T.perron_integral_shift_primitive_LFunction
  obtain ⟨C₃, hC₃, h₃⟩ := GlobalTheory.ZeroBand.zeros_band
  refine ⟨C₁ + C₂ + C₃, by positivity, fun N _ χ hχ u T hT hTu => ?_⟩
  obtain ⟨T', hT1, hT2, hs⟩ := h₂ N χ hχ u T hT hTu
  obtain ⟨hfin, hb⟩ := h₃ N χ hχ u T T' hT hTu hT1 hT2
  have hp := h₁ N χ u T' (by linarith) (by linarith) (by linarith)
  refine ⟨hfin, ?_⟩
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hiff : χ = 1 ↔ N = 1 := by
    constructor
    · intro h
      have h1 : χ.conductor = N := hχ
      rw [h, DirichletCharacter.conductor_one] at h1
      exact h1.symm
    · intro h
      subst h
      exact DirichletCharacter.level_one χ
  have hpsi : psi0 χ u = (∑ n ∈ Finset.Icc 1 ⌊u⌋₊, (Λ n : ℂ) * χ (n : ZMod N)) -
      (if N = 1 then (u : ℂ) else 0) := by
    unfold psi0
    by_cases h : N = 1
    · rw [if_pos h, if_pos (hiff.mpr h)]
    · rw [if_neg h, if_neg (fun h' => h (hiff.mp h'))]
  rw [hpsi]
  have hZ : 0 ≤ ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1 ∧ LFunction χ ρ = 0},
      ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℝ) / ‖ρ‖ :=
    finsum_nonneg fun ρ => finsum_nonneg fun _ => by positivity
  have hu : (2 : ℝ) ≤ u := hT.trans hTu
  have hlu : 0 ≤ Real.log u := Real.log_nonneg (by linarith)
  have hl1 : Real.log u ≤ Real.log (N * u) :=
    Real.log_le_log (by linarith) (by nlinarith)
  have hl2 : Real.log u ≤ Real.log (N * u * T) := by
    refine Real.log_le_log (by linarith) ?_
    have : u ≤ N * u := by nlinarith
    nlinarith
  have hA : u * Real.log u ^ 2 / T' ≤ u * Real.log (N * u * T) ^ 2 / T := by
    have : Real.log u ^ 2 ≤ Real.log (N * u * T) ^ 2 := pow_le_pow_left₀ hlu hl2 2
    gcongr
  have hA0 : 0 ≤ u * Real.log (N * u * T) ^ 2 / T := by
    have : 0 ≤ u := by linarith
    have : 0 ≤ T := by linarith
    positivity
  have key : ∀ S P m Z Z' : ℂ, ‖S - m + Z‖ ≤ ‖S - P‖ + ‖P - m + Z'‖ + ‖Z' - Z‖ := by
    intro S P m Z Z'
    have : S - m + Z = (S - P) + (P - m + Z') - (Z' - Z) := by ring
    rw [this]
    exact (norm_sub_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
  refine (key _ _ _ _ _).trans ((add_le_add (add_le_add hp hs) hb).trans ?_)
  generalize (∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1 ∧ LFunction χ ρ = 0},
      ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℝ) / ‖ρ‖) = Z at hZ ⊢
  generalize u * Real.log (N * u * T) ^ 2 / T = A at hA hA0 ⊢
  generalize u * Real.log u ^ 2 / T' = A' at hA ⊢
  generalize Real.log (N * u) = B at hl1 ⊢
  generalize Real.log u = B' at hl1 hlu ⊢
  have e1 : C₁ * (A' + B') ≤ C₁ * (A + B + Z) :=
    mul_le_mul_of_nonneg_left (by linarith) hC₁.le
  have e2 : C₃ * A ≤ C₃ * (A + B + Z) :=
    mul_le_mul_of_nonneg_left (by linarith) hC₃.le
  nlinarith

end GlobalTheory.ExplicitFormula
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct


theorem _root_.GlobalTheory.T.isFibreMeasureFamily_map_homeomorph : ∀ (V V' X X' : Type) [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace V'] [MeasurableSpace V'] [BorelSpace V'] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [TopologicalSpace X'] [MeasurableSpace X'] [BorelSpace X'] (e : V ≃ₜ V') (r : X ≃ₜ X') (μ : Measure V) (ν : Measure X) (f : V → X) (f' : V' → X') (B : Set X) (fib : X → Measure V), (∀ v, f' (e v) = r (f v)) → IsFibreFamily μ f id Set.univ ν B fib → IsFibreFamily (μ.map e) f' id Set.univ (ν.map r) (r '' B) fun b => (fib (r.symm b)).map e := by
  first | exact @GlobalTheory.isFibreFamily_map_homeomorph | exact GlobalTheory.isFibreFamily_map_homeomorph | (intros; apply GlobalTheory.isFibreFamily_map_homeomorph <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory

theorem goodTopCount_le_const_mul_log (r : ℕ) (de h x : ℝ) (hde : 0 < de) (hde1 : de ≤ 1)
    (hh : 0 ≤ h) (hL : 1 ≤ Real.log x) :
    (G.orbitWindowCount r de h x : ℝ) ≤
      (6 * Real.exp 1 * (((h + 3) * 10 ^ (6 * r + 1) + 6) * (((6 * r + 1 : ℕ) : ℝ) * 2)) +
        (h + 3) * 2 + 2) * Real.log x := by
  set L := Real.log x with hLdef
  have hu : (G.goodU de : ℝ) * de ≤ 2 := by
    unfold G.goodU
    have h1 : (⌈1 / de⌉₊ : ℝ) < 1 / de + 1 := Nat.ceil_lt_add_one (by positivity)
    have h2 : (⌈1 / de⌉₊ : ℝ) * de ≤ (1 / de + 1) * de := mul_le_mul_of_nonneg_right h1.le hde.le
    have h3 : (1 / de + 1) * de = 1 + de := by field_simp
    linarith
  have hT : (0 : ℝ) < 10 ^ (6 * r + 1) := by positivity
  have hM : (G.orbitSmallMultiplicity r h x : ℝ) + 5 ≤ ((h + 3) * 10 ^ (6 * r + 1) + 6) * L := by
    unfold G.orbitSmallMultiplicity
    have he : (h + 3) * Real.log x / (10 : ℝ) ^ (-((6 * r + 1 : ℕ) : ℤ)) =
        (h + 3) * 10 ^ (6 * r + 1) * L := by
      rw [zpow_neg, zpow_natCast, div_inv_eq_mul]; ring
    rw [he]
    have h1 : (⌈(h + 3) * 10 ^ (6 * r + 1) * L⌉₊ : ℝ) < (h + 3) * 10 ^ (6 * r + 1) * L + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    nlinarith
  have hG : (G.goodG' r de h x : ℝ) * de ≤
      (((h + 3) * 10 ^ (6 * r + 1) + 6) * (((6 * r + 1 : ℕ) : ℝ) * 2)) * L := by
    unfold G.goodG' G.goodEll
    have he : (((G.orbitSmallMultiplicity r h x + 5) * ((6 * r + 1) * G.goodU de) : ℕ) : ℝ) * de =
        ((G.orbitSmallMultiplicity r h x : ℝ) + 5) * (((6 * r + 1 : ℕ) : ℝ) * ((G.goodU de : ℝ) * de)) := by
      push_cast; ring
    rw [he]
    calc _ ≤ (((h + 3) * 10 ^ (6 * r + 1) + 6) * L) * (((6 * r + 1 : ℕ) : ℝ) * 2) := by
          apply mul_le_mul hM (mul_le_mul_of_nonneg_left hu (by positivity)) (by positivity)
          positivity
      _ = _ := by ring
  have hb : (h + 3) * Real.logb 2 x ≤ (h + 3) * 2 * L := by
    have h2 : (1 / 2 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
    have : Real.logb 2 x ≤ 2 * L := by
      unfold Real.logb
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left this (by linarith)
  unfold G.orbitWindowCount
  set A := ((h + 3) * 10 ^ (6 * r + 1) + 6) * (((6 * r + 1 : ℕ) : ℝ) * 2) with hA
  have hA0 : 0 ≤ A := by positivity
  have hE : 0 < 6 * Real.exp 1 := by positivity
  have h1 : 6 * Real.exp 1 * (G.goodG' r de h x : ℝ) * de ≤ 6 * Real.exp 1 * A * L := by
    rw [mul_assoc (6 * Real.exp 1), mul_assoc (6 * Real.exp 1)]
    exact mul_le_mul_of_nonneg_left hG hE.le
  have h1' : 0 ≤ 6 * Real.exp 1 * A * L := by positivity
  have h2' : 0 ≤ (h + 3) * 2 * L := by positivity
  have hmax : max (6 * Real.exp 1 * (G.goodG' r de h x : ℝ) * de) ((h + 3) * Real.logb 2 x) ≤
      6 * Real.exp 1 * A * L + (h + 3) * 2 * L := max_le (by linarith) (by linarith)
  have hc := Nat.ceil_lt_add_one (a := max (6 * Real.exp 1 * (G.goodG' r de h x : ℝ) * de)
    ((h + 3) * Real.logb 2 x)) (le_max_of_le_left (by positivity))
  rw [Nat.cast_add, Nat.cast_one]
  nlinarith

theorem topCount_and_lambda_bounds : ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ CN x0 : ℝ, ∀ s : Scale,
    s.eps = eps → x0 ≤ s.x → 1 ≤ G.N1 s ∧ (G.N1 s : ℝ) ≤ CN * Real.log s.x ∧
      ∀ K : G.Consts, 1 ≤ K.La → s.x ^ s.eps ≤ G.La K s ∧
        G.La K s ≤ K.La * CN ^ 2 * Real.log s.x ^ 2 * (2 * s.x ^ s.eps) := by
  intro eps he _
  obtain ⟨x1, hx1⟩ := Filter.eventually_atTop.1 ((isLittleO_log_rpow_atTop he).bound one_pos)
  set h : ℝ := 2 + 8 * eps with hh
  set r : ℕ := ⌈8 * (h + 2) / eps⌉₊ + 1 with hr
  refine ⟨6 * Real.exp 1 * (((h + 3) * 10 ^ (6 * r + 1) + 6) * (((6 * r + 1 : ℕ) : ℝ) * 2)) +
        (h + 3) * 2 + 2, max x1 (Real.exp 1), ?_⟩
  intro s hs hx
  have hx0 : 0 < s.x := lt_trans one_pos s.one_lt_alt
  have hL : 1 ≤ Real.log s.x := by
    rw [Real.le_log_iff_exp_le hx0]; exact le_trans (le_max_right _ _) hx
  have hP : 0 < s.x ^ s.eps := Real.rpow_pos_of_pos hx0 _
  have hlog : Real.log s.x ≤ s.x ^ s.eps := by
    have := hx1 s.x (le_trans (le_max_left _ _) hx)
    rw [one_mul, ← hs, Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg hP.le] at this
    exact this
  have hhG : G.hG s = h := by unfold G.hG; rw [hs]
  have hrG : G.rG s = r := by unfold G.rG G.KG; rw [hhG, hs]
  have hN1 : 1 ≤ G.N1 s := by unfold G.N1 G.orbitWindowCount; exact Nat.le_add_left _ _
  have hN := goodTopCount_le_const_mul_log r s.delta1 h s.x (Real.rpow_pos_of_pos hx0 _)
    (Real.rpow_le_one_of_one_le_of_nonpos s.one_lt_alt.le (by have := s.eps_pos; linarith))
    (by positivity) hL
  have hNe : G.N1 s = G.orbitWindowCount r s.delta1 h s.x := by unfold G.N1; rw [hhG, hrG]
  rw [← hNe] at hN
  generalize 6 * Real.exp 1 * (((h + 3) * 10 ^ (6 * r + 1) + 6) * (((6 * r + 1 : ℕ) : ℝ) * 2)) +
        (h + 3) * 2 + 2 = CN at hN ⊢
  refine ⟨hN1, hN, fun K hK => ?_⟩
  have ha : Real.log s.a = Real.log s.x + s.x ^ s.eps := by
    unfold Scale.a Scale.b Scale.L
    rw [Real.log_mul hx0.ne' (Real.exp_pos _).ne', Real.log_exp]
  have hN1' : (1 : ℝ) ≤ (G.N1 s : ℝ) := by exact_mod_cast hN1
  have hsq : (1 : ℝ) ≤ (G.N1 s : ℝ) ^ 2 := one_le_pow₀ hN1'
  have hsq' : (G.N1 s : ℝ) ^ 2 ≤ (CN * Real.log s.x) ^ 2 := pow_le_pow_left₀ (by linarith) hN 2
  unfold G.La
  rw [ha]
  constructor
  · have h1 : 1 ≤ K.La * (G.N1 s : ℝ) ^ 2 := one_le_mul_of_one_le_of_one_le hK hsq
    nlinarith
  · calc K.La * (G.N1 s : ℝ) ^ 2 * (Real.log s.x + s.x ^ s.eps)
        ≤ K.La * (CN * Real.log s.x) ^ 2 * (2 * s.x ^ s.eps) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hsq' (by linarith)) (by linarith) (by linarith)
          have : 0 ≤ K.La := by linarith
          positivity
      _ = _ := by ring

end GlobalTheory
end

section

open Formalism.MainNotions.N

namespace GlobalTheory.QuadKernelConj

section Restrict

variable {Γ k : Type} [Group Γ] [Field k] {n : ℕ}

def tr (ρ : Γ →* GL (Fin n) k) (g : Γ) (U : Submodule k (Fin n → k)) : Submodule k (Fin n → k) :=
  U.map (Matrix.toLin' ((ρ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))

theorem tr_mul (ρ : Γ →* GL (Fin n) k) (g h : Γ) (U : Submodule k (Fin n → k)) :
    tr ρ (g * h) U = tr ρ g (tr ρ h U) := by
  unfold tr
  rw [map_mul, Units.val_mul, Matrix.toLin'_mul, Submodule.map_comp]

theorem tr_mono (ρ : Γ →* GL (Fin n) k) (g : Γ) {U V : Submodule k (Fin n → k)} (h : U ≤ V) :
    tr ρ g U ≤ tr ρ g V := Submodule.map_mono h

theorem tr_sup (ρ : Γ →* GL (Fin n) k) (g : Γ) (U V : Submodule k (Fin n → k)) :
    tr ρ g (U ⊔ V) = tr ρ g U ⊔ tr ρ g V := Submodule.map_sup _ _ _

theorem tr_inf_le (ρ : Γ →* GL (Fin n) k) (g : Γ) (U V : Submodule k (Fin n → k)) :
    tr ρ g (U ⊓ V) ≤ tr ρ g U ⊓ tr ρ g V :=
  le_inf (tr_mono ρ g inf_le_left) (tr_mono ρ g inf_le_right)

theorem tr_le_iff (ρ : Γ →* GL (Fin n) k) (g : Γ) (U : Submodule k (Fin n → k)) :
    tr ρ g U ≤ U ↔ ∀ v ∈ U, ((ρ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec v ∈ U := by
  unfold tr
  rw [Submodule.map_le_iff_le_comap]
  rfl

theorem isInv_iff (ρ : Γ →* GL (Fin n) k) (U : Submodule k (Fin n → k)) :
    IsInv ρ U ↔ ∀ g, tr ρ g U ≤ U :=
  forall_congr' fun g => (tr_le_iff ρ g U).symm

theorem isInv_ker_iff (ρ : Γ →* GL (Fin n) k) (η : Γ →* ℤˣ) (U : Submodule k (Fin n → k)) :
    IsInv (ρ.comp η.ker.subtype) U ↔ ∀ g, η g = 1 → tr ρ g U ≤ U := by
  constructor
  · intro h g hg
    exact (tr_le_iff ρ g U).2 (h ⟨g, hg⟩)
  · intro h g
    exact (tr_le_iff ρ g.1 U).1 (h g.1 g.2)

theorem isSSRep_ker (ρ : Γ →* GL (Fin n) k) (η : Γ →* ℤˣ) (hρ : IsSSRep ρ) :
    IsSSRep (ρ.comp η.ker.subtype) := by
  intro W hW
  rw [isInv_ker_iff] at hW
  by_cases hη : ∀ g, η g = 1
  · obtain ⟨W', h1, h2⟩ := hρ W ((isInv_iff ρ W).2 fun g => hW g (hη g))
    exact ⟨W', (isInv_ker_iff ρ η W').2 fun g _ => (isInv_iff ρ W').1 h1 g, h2⟩
  obtain ⟨t, ht⟩ := not_forall.1 hη
  have ht' : η t = -1 := (Int.units_eq_one_or (η t)).resolve_left ht

  have hconj : ∀ U, (∀ g, η g = 1 → tr ρ g U ≤ U) → ∀ g, η g = 1 → tr ρ g (tr ρ t U) ≤ tr ρ t U := by
    intro U hU g hg
    have e : g * t = t * (t⁻¹ * g * t) := by group
    rw [← tr_mul, e, tr_mul]
    refine tr_mono ρ t (hU _ ?_)
    rw [map_mul, map_mul, hg, map_inv, mul_one, inv_mul_cancel]
  have hall : ∀ U, (∀ g, η g = 1 → tr ρ g U ≤ U) → tr ρ t U ≤ U → IsInv ρ U := by
    intro U hU hUt
    rw [isInv_iff]
    intro g
    rcases Int.units_eq_one_or (η g) with hg | hg
    · exact hU g hg
    · have e : g = t * (t⁻¹ * g) := by group
      rw [e, tr_mul]
      refine (tr_mono ρ t (hU _ ?_)).trans hUt
      rw [map_mul, map_inv, hg, ht', inv_mul_cancel]
  have htt : tr ρ t (tr ρ t W) ≤ W := by
    rw [← tr_mul]
    refine hW _ ?_
    rw [map_mul, ht']
    simp
  have hAt : tr ρ t (W ⊓ tr ρ t W) ≤ W ⊓ tr ρ t W :=
    (tr_inf_le ρ t _ _).trans (le_inf (inf_le_right.trans htt) inf_le_left)
  have hA : IsInv ρ (W ⊓ tr ρ t W) :=
    hall _ (fun g hg => (tr_inf_le ρ g _ _).trans (inf_le_inf (hW g hg) (hconj W hW g hg))) hAt
  have hB : IsInv ρ (W ⊔ tr ρ t W) := by
    refine hall _ (fun g hg => ?_) ?_
    · rw [tr_sup]
      exact sup_le_sup (hW g hg) (hconj W hW g hg)
    · rw [tr_sup]
      exact sup_le le_sup_right (htt.trans le_sup_left)
  obtain ⟨D, hD, hAD⟩ := hρ _ hA
  obtain ⟨C, hC, hBC⟩ := hρ _ hB
  rw [isInv_iff] at hD hC
  have hW1 : ∀ g, η g = 1 → tr ρ g (W ⊓ D) ≤ W ⊓ D := fun g hg =>
    (tr_inf_le ρ g _ _).trans (inf_le_inf (hW g hg) (hD g))
  have hWeq : (W ⊓ tr ρ t W) ⊔ (W ⊓ D) = W := by
    rw [inf_comm W D, ← sup_inf_assoc_of_le D (inf_le_left : W ⊓ tr ρ t W ≤ W), hAD.sup_eq_top,
      top_inf_eq]
  have hsup : W ⊔ tr ρ t (W ⊓ D) = W ⊔ tr ρ t W := by
    refine le_antisymm (sup_le_sup_left (tr_mono ρ t inf_le_left) _) (sup_le le_sup_left ?_)
    calc tr ρ t W = tr ρ t ((W ⊓ tr ρ t W) ⊔ (W ⊓ D)) := by rw [hWeq]
      _ ≤ W ⊔ tr ρ t (W ⊓ D) := by
        rw [tr_sup]
        exact sup_le_sup_right (hAt.trans inf_le_left) _
  have hdis : Disjoint W (tr ρ t (W ⊓ D)) := by
    rw [disjoint_iff_inf_le, ← hAD.inf_eq_bot]
    exact le_inf (inf_le_inf_left _ (tr_mono ρ t inf_le_left))
      (inf_le_right.trans ((tr_mono ρ t inf_le_right).trans (hD t)))
  refine ⟨tr ρ t (W ⊓ D) ⊔ C, (isInv_ker_iff ρ η _).2 fun g hg => ?_, ?_, ?_⟩
  · rw [tr_sup]
    exact sup_le_sup (hconj _ hW1 g hg) (hC g)
  · exact hdis.disjoint_sup_right_of_disjoint_sup_left (hsup ▸ hBC.disjoint)
  · rw [codisjoint_iff, ← sup_assoc, hsup, hBC.sup_eq_top]

end Restrict

theorem charpoly_eq_of_trace_pow {k : Type} [Field k] [CharZero k] {n : ℕ} (A B : Matrix (Fin n) (Fin n) k)
    (h : ∀ m : ℕ, (A ^ m).trace = (B ^ m).trace) : A.charpoly = B.charpoly := by
  have h1 := GroundTheory.Global.reverse_charpoly_eq_of_trace_pow_eq (Matrix.toLin' A) (Matrix.toLin' B)
    (fun m _ => by
      rw [← Matrix.toLin'_pow, ← Matrix.toLin'_pow, Matrix.trace_toLin'_eq, Matrix.trace_toLin'_eq, h m])
  rw [Matrix.charpoly_toLin', Matrix.charpoly_toLin', Polynomial.reverse, Polynomial.reverse,
    Matrix.charpoly_natDegree_eq_dim, Matrix.charpoly_natDegree_eq_dim] at h1
  have h2 := congrArg (Polynomial.reflect (Fintype.card (Fin n))) h1
  rwa [Polynomial.reflect_reflect, Polynomial.reflect_reflect] at h2

theorem conj_on_ker_inf_ker : ∀ (Γ k : Type) [Group Γ] [Field k] [CharZero k] (n : ℕ) (ρ ρ' : Γ →* GL (Fin n) k) (χ₁ χ₂ : Γ →* ℤˣ), IsSSRep ρ → IsSSRep ρ' → (∀ g, χ₁ g = 1 → χ₂ g = 1 → ((ρ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace = ((ρ' g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace) → ∃ P : GL (Fin n) k, ∀ g, χ₁ g = 1 → χ₂ g = 1 → ρ' g = P⁻¹ * ρ g * P := by
  intro Γ k _ _ _ n ρ ρ' χ₁ χ₂ hρ hρ' htr
  obtain ⟨P, hP⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix _ _
    (isSSRep_ker _ (χ₁.comp χ₂.ker.subtype) (isSSRep_ker ρ χ₂ hρ))
    (isSSRep_ker _ (χ₁.comp χ₂.ker.subtype) (isSSRep_ker ρ' χ₂ hρ')) (fun g => by
      refine charpoly_eq_of_trace_pow _ _ fun m => ?_
      rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← map_pow, ← map_pow]
      exact htr (g ^ m).1.1 (g ^ m).2 (g ^ m).1.2)
  exact ⟨P, fun g h1 h2 => hP ⟨⟨g, h2⟩, h1⟩⟩

end GlobalTheory.QuadKernelConj
end
