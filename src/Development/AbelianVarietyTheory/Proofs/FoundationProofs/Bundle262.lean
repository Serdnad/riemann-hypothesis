module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Formalism.HermitianCurvature.StatementB
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.Bundle001
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import Mathlib.NumberTheory.ModularForms.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle150
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle137
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle111
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle055
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle056
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle128
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle260
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle057
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle151
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle152
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle167
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle252
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle169
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle208
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntertwinerSelfDualVacuumIsVacuum
public import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle253
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform

@[expose] public section

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.levelN_function_galois_conj_qExpansion : ∀ (g : ℂ ≃+* ℂ) (E : Subring ℂ) (N : ℕ) [NeZero N] (d : (ZMod N)ˣ) (w : ℕ) (f : ℍ → ℂ), (∀ x ∈ E, g x ∈ E) → ZetaAct g N d → Lv E N w f → ∃ f' : ℍ → ℂ, Lv E N w f' ∧ ∀ γ γ' : SL(2, ℤ), dg d * redGL N γ' = redGL N γ * dg d → QConj g N (fun τ => DD τ ^ w * f (γ • τ)) (fun τ => DD τ ^ w * f' (γ' • τ)) := by
  first | exact @GlobalTheory.FN.lv_galois_conj | exact GlobalTheory.FN.lv_galois_conj | (intros; apply GlobalTheory.FN.lv_galois_conj <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.eigenfunctionalAllCharacters_of_atkinLehner : ∀ (k N l : ℕ) (χ : DirichletCharacter ℂ N) (g : ℕ → ℂ) (α : ℂ) (B : ℕ) (c : ℕ → ℂ) (a₀ b₀ c₀ d₀ : ℤ), N * a₀ * d₀ - l * b₀ * c₀ = 1 → 1 ≤ k → 0 < N → l.Prime → ¬ l ∣ N → EigF k N l χ⁻¹ (fun q => χ⁻¹ q * g q) α B c → ∃ (B' : ℕ) (c' : ℕ → ℂ), EigAll k N l χ g (χ l * α) B' c' ∧ ∀ a a', MF k (N * l) (ch χ) a → MF k (N * l) (ch χ⁻¹) a' → qs a' = slz k !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] (qs a) → lam B' c' a = lam B c a' := by
  first | exact @GlobalTheory.EisM.eigAll_of_atkinLehner | exact GlobalTheory.EisM.eigAll_of_atkinLehner | (intros; apply GlobalTheory.EisM.eigAll_of_atkinLehner <;> assumption)
end

section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices.EichlerShimura

theorem exists_of_finrank_le {A A' V : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup A'] [Module ℂ A']
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ A] [FiniteDimensional ℂ A']
    (Z B : Submodule ℂ V) [FiniteDimensional ℂ Z] (hBZ : B ≤ Z) (P : A → V) (Q : A' → V)
    (hPa : ∀ x y, P (x + y) = P x + P y) (hQa : ∀ x y, Q (x + y) = Q x + Q y)
    (hPs : ∀ (r : ℝ) x, P ((r : ℂ) • x) = (r : ℂ) • P x) (hQs : ∀ (r : ℝ) x, Q ((r : ℂ) • x) = (r : ℂ) • Q x)
    (hPZ : ∀ x, P x ∈ Z) (hQZ : ∀ x, Q x ∈ Z)
    (hinj : ∀ x y, P x + Q y ∈ B → x = 0 ∧ y = 0)
    (hdim : Module.finrank ℂ Z ≤ Module.finrank ℂ A + Module.finrank ℂ A' + Module.finrank ℂ B) :
    ∀ z ∈ Z, ∃ x y, z - P x - Q y ∈ B := by
  classical
  have : FiniteDimensional ℂ B := Submodule.finiteDimensional_of_le hBZ
  have hPs' : ∀ (r : ℝ) x, P (r • x) = (r : ℂ) • P x := fun r x => hPs r x
  have hQs' : ∀ (r : ℝ) x, Q (r • x) = (r : ℂ) • Q x := fun r x => hQs r x
  have hP0 : P 0 = 0 := by simpa using hPa 0 0
  have hQ0 : Q 0 = 0 := by simpa using hQa 0 0
  let Φ : (A × A') × B →ₗ[ℝ] Z :=
    { toFun := fun p => ⟨P p.1.1 + Q p.1.2 + (p.2 : V),
        Z.add_mem (Z.add_mem (hPZ _) (hQZ _)) (hBZ p.2.2)⟩
      map_add' := fun p q => by
        apply Subtype.ext
        change P (p.1.1 + q.1.1) + Q (p.1.2 + q.1.2) + ((p.2 : V) + q.2) =
          (P p.1.1 + Q p.1.2 + p.2) + (P q.1.1 + Q q.1.2 + q.2)
        rw [hPa, hQa]
        abel
      map_smul' := fun r p => by
        apply Subtype.ext
        change P (r • p.1.1) + Q (r • p.1.2) + (r : ℂ) • (p.2 : V) =
          (r : ℂ) • (P p.1.1 + Q p.1.2 + p.2)
        rw [hPs', hQs', smul_add, smul_add] }
  have hΦ : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨⟨x, y⟩, b⟩ h
    have h' : P x + Q y + (b : V) = 0 := congrArg Subtype.val h
    have hmem : P x + Q y ∈ B := by
      rw [eq_neg_of_add_eq_zero_left h']
      exact B.neg_mem b.2
    obtain ⟨rfl, rfl⟩ := hinj x y hmem
    have hb : b = 0 := Subtype.ext (by simpa [hP0, hQ0] using h')
    simp [hb]
  have hle : Module.finrank ℝ Z ≤ Module.finrank ℝ ((A × A') × B) := by
    have hZ : Module.finrank ℝ Z = 2 * Module.finrank ℂ Z := finrank_real_of_complex Z
    have hA : Module.finrank ℝ A = 2 * Module.finrank ℂ A := finrank_real_of_complex A
    have hA' : Module.finrank ℝ A' = 2 * Module.finrank ℂ A' := finrank_real_of_complex A'
    have hB : Module.finrank ℝ B = 2 * Module.finrank ℂ B := finrank_real_of_complex B
    rw [Module.finrank_prod, Module.finrank_prod, hZ, hA, hA', hB]
    omega
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (le_antisymm (LinearMap.finrank_le_finrank_of_injective hΦ) hle)).1 hΦ
  intro z hz
  obtain ⟨⟨⟨x, y⟩, b⟩, hp⟩ := hsurj ⟨z, hz⟩
  refine ⟨x, y, ?_⟩
  have hz' : P x + Q y + (b : V) = z := congrArg Subtype.val hp
  have : z - P x - Q y = b := by rw [← hz']; abel
  rw [this]
  exact b.2

theorem coboundaries_le_cocycles (Γ : Subgroup SL(2, ℤ)) (w : ℕ) : B1 Γ w ≤ Z1 Γ w := by
  intro z hz
  obtain ⟨p, rfl⟩ := LinearMap.mem_range.1 hz
  have hp : (p : ℂ[X]) ∈ degreeLT ℂ (w + 1) := p.2
  refine ⟨fun γ => ?_, fun γ δ => ?_⟩
  · change slP w (mat γ) p - p ∈ degreeLT ℂ (w + 1)
    exact Submodule.sub_mem _ (GlobalTheory.T.polyDegreeSlashAction_right_action_properties w (mat γ) 1 p hp).1 hp
  · change slP w (mat ((γ * δ : Γ) : SL(2, ℤ))) p - p =
      slP w (mat δ) (slP w (mat γ) p - p) + (slP w (mat δ) p - p)
    have hmat : mat ((γ * δ : Γ) : SL(2, ℤ)) = mat γ * mat δ := by simp [mat]
    rw [hmat, (GlobalTheory.T.polyDegreeSlashAction_right_action_properties w (mat γ) (mat δ) p hp).2.1, map_sub]
    abel

theorem integrable_seg {f : ℍ → ℂ} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (n : ℕ) (τ : ℍ) :
    IntervalIntegrable (fun t : ℝ => (f ∘ UpperHalfPlane.ofComplex) (Complex.I + t * ((τ : ℂ) - Complex.I)) *
      (-(Complex.I + t * ((τ : ℂ) - Complex.I))) ^ n * ((τ : ℂ) - Complex.I)) MeasureTheory.volume 0 1 := by
  have hd := UpperHalfPlane.mdifferentiable_iff.1 hf
  have him : ∀ t ∈ Set.uIcc (0 : ℝ) 1, 0 < (Complex.I + t * ((τ : ℂ) - Complex.I)).im := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    obtain ⟨h0, h1⟩ := ht
    have hτ := τ.im_pos
    have e : (Complex.I + t * ((τ : ℂ) - Complex.I)).im = (1 - t) + t * τ.im := by
      simp [Complex.mul_im]
      ring
    rw [e]
    rcases h1.lt_or_eq with h1 | rfl
    · nlinarith [mul_nonneg h0 hτ.le]
    · simpa using hτ
  have hpath : Continuous fun t : ℝ => Complex.I + t * ((τ : ℂ) - Complex.I) := by fun_prop
  have hc : ContinuousOn (fun t : ℝ => (f ∘ UpperHalfPlane.ofComplex) (Complex.I + t * ((τ : ℂ) - Complex.I)))
      (Set.uIcc 0 1) :=
    hd.continuousOn.comp hpath.continuousOn fun t ht => him t ht
  have hpow : Continuous fun t : ℝ => (-(Complex.I + t * ((τ : ℂ) - Complex.I))) ^ n := by fun_prop
  exact ((hc.mul hpow.continuousOn).mul continuousOn_const).intervalIntegrable

theorem per_add (Γ : Subgroup SL(2, ℤ)) (w : ℕ) {f g : ℍ → ℂ} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) : per Γ w (f + g) = per Γ w f + per Γ w g := by
  have he : ∀ τ : ℍ, eichler w (f + g) τ = eichler w f τ + eichler w g τ := by
    intro τ
    simp only [eichler, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hint : (∫ t in (0 : ℝ)..1, ((f + g) ∘ UpperHalfPlane.ofComplex) (Complex.I + t * ((τ : ℂ) - Complex.I)) *
          (-(Complex.I + t * ((τ : ℂ) - Complex.I))) ^ (w - j) * ((τ : ℂ) - Complex.I)) =
        (∫ t in (0 : ℝ)..1, (f ∘ UpperHalfPlane.ofComplex) (Complex.I + t * ((τ : ℂ) - Complex.I)) *
          (-(Complex.I + t * ((τ : ℂ) - Complex.I))) ^ (w - j) * ((τ : ℂ) - Complex.I)) +
        (∫ t in (0 : ℝ)..1, (g ∘ UpperHalfPlane.ofComplex) (Complex.I + t * ((τ : ℂ) - Complex.I)) *
          (-(Complex.I + t * ((τ : ℂ) - Complex.I))) ^ (w - j) * ((τ : ℂ) - Complex.I)) := by
      rw [← intervalIntegral.integral_add (integrable_seg hf (w - j) τ) (integrable_seg hg (w - j) τ)]
      refine intervalIntegral.integral_congr fun t _ => ?_
      simp only [Function.comp_apply, Pi.add_apply]
      ring
    rw [hint, mul_add, C_add, add_mul]
  funext γ
  simp only [per, Pi.add_apply, he, map_add (f := _)]

theorem cj_add {Γ : Type} (x y : Γ → ℂ[X]) : cj (x + y) = cj x + cj y := by
  funext γ
  simp [cj, Polynomial.map_add (f := _)]

theorem cj_real_smul {Γ : Type} (r : ℝ) (x : Γ → ℂ[X]) : cj ((r : ℂ) • x) = (r : ℂ) • cj x := by
  funext γ
  change ((r : ℂ) • x γ).map (starRingEnd ℂ) = (r : ℂ) • (x γ).map (starRingEnd ℂ)
  rw [Polynomial.map_smul, Complex.conj_ofReal]

theorem exists_per_add_cj_per : ∀ (N M : ℕ) (Γ : Subgroup SL(2, ℤ)) (k : ℕ), 5 ≤ N → 0 < M →
    CongruenceSubgroup.Gamma M ≤ Γ → Γ ≤ CongruenceSubgroup.Gamma1 N → Odd k → 3 ≤ k →
    ∀ z ∈ Z1 Γ (k - 2), ∃ (f : ModularForm Γ (k : ℤ)) (h : CuspForm Γ (k : ℤ)),
      z - per Γ (k - 2) ⇑f - cj (per Γ (k - 2) ⇑h) ∈ B1 Γ (k - 2) := by
  intro N M Γ k hN hM hΓM hΓN hk hk3 z hz
  have : NeZero M := ⟨hM.ne'⟩
  have hfi : Γ.FiniteIndex := Subgroup.finiteIndex_of_le hΓM
  obtain ⟨hfdM, hfdC, hcount⟩ := GlobalTheory.T.oddWeight_modular_cusp_dimension_lower_bound N M Γ k hN hM hΓM hΓN hk hk3
  obtain ⟨hfdZ, hZ⟩ := GlobalTheory.T.finrank_z1_le_of_le_gamma1_of_finiteIndex N Γ (k - 2) hN hΓN hfi
  have hB := GlobalTheory.T.finrank_b1_eq_of_gamma_le M Γ (k - 2) hM (by omega) hΓM
  have hk2 : 2 ≤ k := by omega
  have hsm := (GlobalTheory.T.eichlerShimura_conj_cocycles_coboundaries_period_smul Γ (k - 2)).2.2
  have hnegper : ∀ g : ℍ → ℂ, per Γ (k - 2) (-g) = -per Γ (k - 2) g := by
    intro g
    simpa using hsm g (-1)
  have hcjneg : ∀ x : Γ → ℂ[X], cj (-x) = -cj x := by
    intro x
    funext γ
    simp [cj, Polynomial.map_neg]
  have key := exists_of_finrank_le (A := ModularForm Γ k) (A' := CuspForm Γ k)
    (Z1 Γ (k - 2)) (B1 Γ (k - 2)) (coboundaries_le_cocycles Γ (k - 2))
    (fun f => per Γ (k - 2) ⇑f) (fun h => -cj (per Γ (k - 2) ⇑h))
    (fun x y => by
      simp only [FunLike.coe_add]
      exact per_add Γ _ (ModularFormClass.holo x) (ModularFormClass.holo y))
    (fun x y => by
      simp only [FunLike.coe_add, per_add Γ _ (ModularFormClass.holo x) (ModularFormClass.holo y), cj_add,
        neg_add])
    (fun r x => by
      simp only [FunLike.coe_smul]
      exact hsm _ _)
    (fun r x => by simp only [FunLike.coe_smul, hsm, cj_real_smul, smul_neg])
    (fun x => (GlobalTheory.T.eichlerPeriodCocycle_mem_cocycles_and_eq Γ k hk2 x).1)
    (fun y => Submodule.neg_mem _
      ((GlobalTheory.T.eichlerShimura_conj_cocycles_coboundaries_period_smul Γ (k - 2)).1 _ (GlobalTheory.T.eichlerPeriodCocycle_mem_cocycles_and_eq Γ k hk2 (ModularFormClass.modularForm y)).1))
    (fun x y hxy => by
      have hxy' : per Γ (k - 2) ⇑x - cj (per Γ (k - 2) ⇑y) ∈ B1 Γ (k - 2) := by
        simpa [sub_eq_add_neg] using hxy
      obtain ⟨f', hf'⟩ := GlobalTheory.T.cuspidal_of_eichlerPeriod_sub_conj_mem_coboundaries N Γ k hN hΓN hfi hk3 x y hxy'
      rw [← hf'] at hxy'
      obtain ⟨h1, h2⟩ := GlobalTheory.T.cuspForms_eq_zero_of_period_sub_conj_coboundary N Γ k hN hΓN hfi hk3 f' y hxy'
      refine ⟨DFunLike.coe_injective ?_, h2⟩
      rw [← hf', h1]
      simp)
    (by
      rw [hB]
      have e : k - 1 = k - 2 + 1 := by omega
      rw [e] at hcount
      rw [Nat.mul_add] at hZ
      omega)
  obtain ⟨f, h, hfh⟩ := key z hz
  refine ⟨f, -h, ?_⟩
  simpa [FunLike.coe_neg, hnegper, hcjneg, sub_eq_add_neg] using hfh

end GlobalTheory.HeckeFamilyMatrices.EichlerShimura
end

section

open GlobalTheory.NeedB Polynomial

theorem _root_.GlobalTheory.T.classGroup_affineCurve_divisible_charZero : GlobalTheory.NeedB.ClDiv := by
  first | exact @GlobalTheory.classGroup_ringOfIntegers_divisible | exact GlobalTheory.classGroup_ringOfIntegers_divisible | (intros; apply GlobalTheory.classGroup_ringOfIntegers_divisible <;> assumption)
end

section

open Matrix

noncomputable section

namespace GlobalTheory.SOrb.CCBridge

open Formalism.REAL Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity

lemma lin_bound {𝕜 L M : Type*} [RCLike 𝕜] [NormedAddCommGroup L] [NormedSpace 𝕜 L] [FiniteDimensional 𝕜 L]
    [NormedAddCommGroup M] [NormedSpace 𝕜 M] (u : L →ₗ[𝕜] M) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖u x‖ ≤ C * ‖x‖ :=
  ⟨‖LinearMap.toContinuousLinearMap u‖, norm_nonneg _, (LinearMap.toContinuousLinearMap u).le_opNorm⟩

def opEquiv (n : ℕ) :
    Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℂ] (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :=
  (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)).toAlgEquiv.toLinearEquiv

lemma opn_eq {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : opn g = ‖opEquiv n g‖ := rfl

section Frob

attribute [local instance] Matrix.frobeniusSeminormedAddCommGroup Matrix.frobeniusNormedAddCommGroup
  Matrix.frobeniusNormedSpace

lemma opn_frob_compare (n : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ g : Matrix (Fin n) (Fin n) ℂ, opn g ≤ K * ‖g‖ ∧ ‖g‖ ≤ K * opn g := by
  obtain ⟨a, ha, h3⟩ := lin_bound (opEquiv n).toLinearMap
  obtain ⟨b, hb, h4⟩ := lin_bound (opEquiv n).symm.toLinearMap
  refine ⟨1 + a + b, by positivity, fun g => ?_⟩
  have h3 : ‖opEquiv n g‖ ≤ a * ‖g‖ := h3 g
  have h4 : ‖(opEquiv n).symm (opEquiv n g)‖ ≤ b * ‖opEquiv n g‖ := h4 (opEquiv n g)
  rw [LinearEquiv.symm_apply_apply] at h4
  rw [opn_eq]
  have := norm_nonneg g
  have := norm_nonneg (opEquiv n g)
  constructor <;> nlinarith

lemma opn_gN_compare (k r : ℕ) : ∃ K : ℝ, 0 < K ∧ ∀ g : Mat k r, opn g ≤ K * gN g ∧ gN g ≤ K * opn g := by
  obtain ⟨K, hK, h⟩ := opn_frob_compare (2 * r + k + 1)
  exact ⟨K, hK, fun g => by rw [gN_eq_frob]; exact h g⟩

end Frob

lemma rpow_compare {K : ℝ} (hK : 0 < K) (A : ℝ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (h1 : x ≤ K * y)
    (h2 : y ≤ K * x) : x ^ A ≤ K ^ |A| * y ^ A := by
  rcases le_total 0 A with hA | hA
  · rw [abs_of_nonneg hA, ← Real.mul_rpow hK.le hy.le]
    exact Real.rpow_le_rpow hx.le h1 hA
  · have h3 : y / K ≤ x := by rw [div_le_iff₀ hK]; linarith
    have := Real.rpow_le_rpow_of_nonpos (by positivity) h3 hA
    rw [Real.div_rpow hy.le hK.le] at this
    rw [abs_of_nonpos hA, Real.rpow_neg hK.le]
    calc x ^ A ≤ y ^ A / K ^ A := this
      _ = _ := by ring

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

end GlobalTheory.SOrb.CCBridge

namespace GlobalTheory.SOrb

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity GlobalTheory.SOrb.CCBridge

end GlobalTheory.SOrb
end
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

lemma rpow_le_add_inv_of_mem_Icc {y s : ℝ} (hy : 0 < y) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    y ^ s ≤ y + y⁻¹ := by
  rcases le_or_gt 1 y with h | h
  · have : y ^ s ≤ y ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h hs1
    rw [Real.rpow_one] at this
    have : 0 ≤ y⁻¹ := inv_nonneg.mpr hy.le
    linarith
  · have h1 : y ^ s ≤ 1 := Real.rpow_le_one hy.le h.le hs0
    have h2 : 1 ≤ y⁻¹ := by rw [le_inv_comm₀ one_pos hy]; simpa using h.le
    linarith

lemma mod_ofReal_norm {F : ℍ → ℂ} (hF : Mod F) : Mod (fun τ => ((‖F τ‖ : ℝ) : ℂ)) := by
  obtain ⟨C, A, h⟩ := hF
  exact ⟨C, A, fun τ => by simpa using h τ⟩

lemma mod_im_pow (A : ℕ) : Mod (fun τ : ℍ => (((τ.im ^ A + (τ.im ^ A)⁻¹ : ℝ)) : ℂ)) := by
  refine ⟨1, A, fun τ => ?_⟩
  have h0 : 0 ≤ τ.im ^ A + (τ.im ^ A)⁻¹ := by
    have := τ.im_pos; positivity
  rw [Complex.norm_real, Real.norm_of_nonneg h0, one_mul]

lemma mod_im_add_inv : Mod (fun τ : ℍ => (((τ.im + τ.im⁻¹ : ℝ)) : ℂ)) := by
  refine ⟨1, 1, fun τ => ?_⟩
  have h0 : 0 ≤ τ.im + τ.im⁻¹ := by
    have := τ.im_pos; positivity
  rw [Complex.norm_real, Real.norm_of_nonneg h0, one_mul, pow_one]

theorem rankin_tendsto : ∀ (k j L L' N : ℕ) (ε : DirichletCharacter ℂ N) (Φ : ℤ × ℤ → ℂ) (ρ : ℍ → ℝ) (h b : ℕ → ℂ), 1 ≤ k → 2 ≤ j → 0 < L → 0 < L' → N ∣ L' → Wt L' ρ → CF k L' (ch ε) h → PolyB b → (∃ C : ℝ, ∀ x, ‖Φ x‖ ≤ C) → Tendsto (fun s : ℝ => pet k ρ (qs h) (fun τ => qs b τ * lat j s L (0, 1) Φ τ * ((τ.im ^ s : ℝ) : ℂ))) (𝓝[>] 0) (𝓝 (pet k ρ (qs h) (fun τ => qs b τ * lat j 0 L (0, 1) Φ τ))) := by
  intro k j L L' N ε Φ ρ h b hk hj hL hL' hN hρ hh hb hΦ
  obtain ⟨⟨C, A, hC⟩, hmeas, hlim⟩ := GlobalTheory.T.regularizedEisensteinLatticeSum_moderate_measurable_tendsto j L Φ hj hL hΦ
  have hbc : Continuous (qs b) := (GlobalTheory.T.qExpansion_polyGrowth_summable_continuous b hb).2
  have hhc : Continuous (qs h) := (GlobalTheory.T.qExpansion_polyGrowth_summable_continuous h hh.1.1).2
  have him : Continuous (fun τ : ℍ => τ.im) := UpperHalfPlane.continuous_im
  set G : ℍ → ℂ := fun τ => ((‖qs b τ‖ : ℝ) : ℂ) * ((C : ℂ) * (((τ.im ^ A + (τ.im ^ A)⁻¹ : ℝ)) : ℂ)) *
    (((τ.im + τ.im⁻¹ : ℝ)) : ℂ) with hG
  have hGc : Continuous G := by
    have h1 : Continuous (fun τ : ℍ => (τ.im ^ A)⁻¹) :=
      (him.pow A).inv₀ (fun τ => (pow_pos τ.im_pos A).ne')
    have h2 : Continuous (fun τ : ℍ => τ.im⁻¹) := him.inv₀ (fun τ => τ.im_pos.ne')
    simp only [hG]
    fun_prop
  have hGmod : Mod G := by
    have M := GlobalTheory.T.hasModerateGrowth_algebra_slash_stable
    exact (M.1 _ _ ((M.1 _ _ (mod_ofReal_norm (GlobalTheory.T.hasModerateGrowth_qExpansion_of_coeffPolynomialGrowth b hb))
      ((M.1 _ _ (M.2.1 (C : ℂ)) (mod_im_pow A)).2)).2) mod_im_add_inv).2
  have hint := GlobalTheory.T.integrable_petersson_integrand_moderateGrowth k L' L' N ε h ρ G hk hL' hN hρ hh hGc.aestronglyMeasurable hGmod
  have hρm : Measurable (fun τ => (ρ τ : ℂ)) := Complex.measurable_ofReal.comp hρ.meas
  simp only [pet]
  refine tendsto_integral_filter_of_dominated_convergence
    (fun τ => ‖(ρ τ : ℂ) * (conj (qs h τ) * G τ * (τ.im : ℂ) ^ k)‖) ?_ ?_ hint.norm ?_
  · refine Filter.Eventually.of_forall (fun s => ?_)
    have hs : Measurable (fun τ : ℍ => (((τ.im ^ s : ℝ)) : ℂ)) :=
      Complex.measurable_ofReal.comp ((him.measurable).pow_const s)
    exact (hρm.mul ((((Complex.continuous_conj.comp hhc).measurable).mul ((hbc.measurable.mul (hmeas s)).mul hs)).mul
      ((Complex.measurable_ofReal.comp him.measurable).pow_const k))).aestronglyMeasurable
  · have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ∈ Set.Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT one_pos
    filter_upwards [hev] with s hs
    refine Filter.Eventually.of_forall (fun τ => ?_)
    have hy := τ.im_pos
    have hρ0 := hρ.nonneg τ
    have hl := hC s τ hs.1.le hs.2.le
    have hys := rpow_le_add_inv_of_mem_Icc hy hs.1.le hs.2.le
    have hX : 0 ≤ C * (τ.im ^ A + (τ.im ^ A)⁻¹) := le_trans (norm_nonneg _) hl
    have hys0 : 0 ≤ τ.im ^ s := Real.rpow_nonneg hy.le s
    have key : ‖lat j s L (0, 1) Φ τ‖ * τ.im ^ s ≤
        |C * (τ.im ^ A + (τ.im ^ A)⁻¹)| * (τ.im + τ.im⁻¹) :=
      mul_le_mul (hl.trans (le_abs_self _)) hys hys0 (abs_nonneg _)
    simp only [hG, norm_mul, Complex.norm_real, Complex.norm_conj, norm_pow, Real.norm_eq_abs,
      norm_norm, abs_norm, Complex.ofReal_mul]
    rw [abs_of_nonneg hy.le, abs_of_nonneg (Real.rpow_nonneg hy.le s),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ τ.im + τ.im⁻¹)]
    have hcomb : |C| * |τ.im ^ A + (τ.im ^ A)⁻¹| = |C * (τ.im ^ A + (τ.im ^ A)⁻¹)| := (abs_mul _ _).symm
    have hP : 0 ≤ |ρ τ| * ‖qs h τ‖ * ‖qs b τ‖ * τ.im ^ k := by positivity
    calc |ρ τ| * (‖qs h τ‖ * (‖qs b τ‖ * ‖lat j s L (0, 1) Φ τ‖ * τ.im ^ s) * τ.im ^ k)
        = (|ρ τ| * ‖qs h τ‖ * ‖qs b τ‖ * τ.im ^ k) * (‖lat j s L (0, 1) Φ τ‖ * τ.im ^ s) := by ring
      _ ≤ (|ρ τ| * ‖qs h τ‖ * ‖qs b τ‖ * τ.im ^ k) * (|C * (τ.im ^ A + (τ.im ^ A)⁻¹)| * (τ.im + τ.im⁻¹)) :=
        mul_le_mul_of_nonneg_left key hP
      _ = |ρ τ| * (‖qs h τ‖ * (‖qs b τ‖ * (|C| * |τ.im ^ A + (τ.im ^ A)⁻¹|) * (τ.im + τ.im⁻¹)) * τ.im ^ k) := by
        rw [hcomb]; ring
  · refine Filter.Eventually.of_forall (fun τ => ?_)
    have hy := τ.im_pos
    have h1 : Tendsto (fun s : ℝ => (((τ.im ^ s : ℝ)) : ℂ)) (𝓝[>] 0) (𝓝 (((τ.im ^ (0:ℝ) : ℝ)) : ℂ)) := by
      have : ContinuousAt (fun s : ℝ => τ.im ^ s) 0 :=
        Real.continuousAt_const_rpow hy.ne'
      exact (Complex.continuous_ofReal.continuousAt.tendsto.comp this.tendsto).mono_left nhdsWithin_le_nhds
    have h2 := ((tendsto_const_nhds (x := (ρ τ : ℂ))).mul
      (((tendsto_const_nhds (x := conj (qs h τ))).mul (((tendsto_const_nhds (x := qs b τ)).mul (hlim τ)).mul h1)).mul
        (tendsto_const_nhds (x := (τ.im : ℂ) ^ k))))
    simpa only [Real.rpow_zero, Complex.ofReal_one, mul_one] using h2

end GlobalTheory.EisM
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

theorem _root_.GlobalTheory.T.principalSeriesCongruenceSubgroup_smoothCharacterDatum : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), (∀ i, IsSmoothChar (ψ i)) → Ordered ψ → Datum (grp ψ) (theta ψ) ∧ IsOpen (grp ψ) := by
  first | exact @GlobalTheory.PsType.grp_theta_datum | exact GlobalTheory.PsType.grp_theta_datum | (intros; apply GlobalTheory.PsType.grp_theta_datum <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.intertwiner_selfDual_vacuum_isVacuum : ∀ (D : D7), Inp D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ (a d : ℕ) L L' L₁ L₁', SD D L → SD D L' → SD D L₁ → SD D L₁' → ∀ G, ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' G → ThetaVectorUpToUnits D (tor0 D cc δ) t0 L₁ L₁' (Iop D (tor0 D cc δ) (La D (tor0 D cc δ) L L') (La D (tor0 D cc δ) L₁ L₁') (G : VC D a d → ℂ)) := by
  first | exact @GlobalTheory.VacuumMove.isVacuum_thetaIntertwiner_selfDual | exact GlobalTheory.VacuumMove.isVacuum_thetaIntertwiner_selfDual | (intros; apply GlobalTheory.VacuumMove.isVacuum_thetaIntertwiner_selfDual <;> assumption)
end

section

open Polynomial Classical GlobalTheory.BadShare

theorem _root_.GlobalTheory.T.badRows_share_bound_two_primes : ∀ (g₁ g₂ : ℕ) [Fact g₁.Prime] [Fact g₂.Prime] (N m q d : ℕ) (ι₁ ι₂ : Type) [Fintype ι₁] [Fintype ι₂], 100000 ≤ N → PrimeOK g₁ q d → PrimeOK g₂ q d → ∀ (L₁ : ι₁ → Lev g₁ N) (L₂ : ι₂ → Lev g₂ N) (τ₁ : ι₁ → (ZMod g₁)[X] → GG g₁ N → ℂ) (τ₂ : ι₂ → (ZMod g₂)[X] → GG g₂ N → ℂ), (∀ v, IsSeries (τ₁ v)) → (∀ v, IsSeries (τ₂ v)) → ∀ (ch₁ : ι₁ → Fin m → (ZMod g₁)ˣ) (ch₂ : ι₂ → Fin m → (ZMod g₂)ˣ) (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ ((ι₁ → GG g₁ N) × (ι₂ → GG g₂ N)) M) (ep : ℝ), 0 ≤ ep → ep < 1 → CountAt ρ ep → (1 - (1 + ep) / (1 - ep) * (max 0 (badBound g₁ (Fintype.card ι₁) m N ((min q d : ℕ) : ℝ)) + max 0 (badBound g₂ (Fintype.card ι₂) m N ((min q d : ℕ) : ℝ)))) * (rk ρ (tens2 (tens fun v => (L₁ v).e) (tens fun v => (L₂ v).e)) : ℝ) ≤ (rk ρ (conv (tens2 (eGood τ₁ ch₁) (eGood τ₂ ch₂)) (tens2 (tens fun v => (L₁ v).e) (tens fun v => (L₂ v).e))) : ℝ) := by
  first | exact @GlobalTheory.BadShare.ShareThm.bad_share | exact GlobalTheory.BadShare.ShareThm.bad_share | (intros; apply GlobalTheory.BadShare.ShareThm.bad_share <;> assumption)
end
