module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Complex.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle376
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Smooth.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle377
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle378
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle380
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle387
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle005
public import Mathlib.Algebra.CharP.Algebra

@[expose] public section

section

open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix

namespace GlobalTheory.FlagGram

theorem cube_cbrt (t : ℝ) (ht : 0 ≤ t) : (t ^ (1/3:ℝ)) ^ 3 = t := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht]; norm_num

theorem rpow_neg_four_thirds (t : ℝ) (ht : 0 ≤ t) :
    t ^ (-(4/3:ℝ)) = ((t ^ (1/3:ℝ)) ^ 4)⁻¹ := by
  rw [Real.rpow_neg ht, ← Real.rpow_natCast, ← Real.rpow_mul ht]; norm_num

theorem sq_mul_le_cubes (a w : ℝ) (ha : 1 ≤ a) (hw : 1 ≤ w) :
    a ^ 2 * w ≤ a ^ 3 + w ^ 3 - 1 := by
  have ha3 : 1 ≤ a ^ 3 := one_le_pow₀ ha
  have hw3 : 1 ≤ w ^ 3 := one_le_pow₀ hw
  rcases le_total a w with h | h
  · nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ w) (sub_nonneg.2 h)) (by linarith : (0:ℝ) ≤ w + a)]
  · nlinarith [mul_nonneg (sq_nonneg a) (sub_nonneg.2 h)]

theorem key (A B C D : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D) (hBD : B ≤ D) :
    ((1 + A + B) ^ 2 * (1 + C + D) ^ 2)⁻¹ ≤
      (1 + A) ^ (-(4 / 3 : ℝ)) * (1 + C) ^ (-(4 / 3 : ℝ)) *
        ((1 + B) ^ (-(4 / 3 : ℝ)) + (1 + D) ^ (-(4 / 3 : ℝ))) := by
  rw [rpow_neg_four_thirds _ (by linarith), rpow_neg_four_thirds _ (by linarith),
    rpow_neg_four_thirds _ (by linarith), rpow_neg_four_thirds _ (by linarith)]
  have eA := cube_cbrt (1 + A) (by linarith)
  have eB := cube_cbrt (1 + B) (by linarith)
  have eC := cube_cbrt (1 + C) (by linarith)
  have hα : 1 ≤ (1 + A) ^ (1/3:ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hβ : 1 ≤ (1 + B) ^ (1/3:ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hγ : 1 ≤ (1 + C) ^ (1/3:ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hδ : 0 < (1 + D) ^ (1/3:ℝ) := Real.rpow_pos_of_pos (by linarith) _
  generalize (1 + A) ^ (1/3:ℝ) = α at *
  generalize (1 + B) ^ (1/3:ℝ) = β at *
  generalize (1 + C) ^ (1/3:ℝ) = γ at *
  generalize (1 + D) ^ (1/3:ℝ) = δ at *
  have hx : α ^ 2 * β ≤ 1 + A + B := by have := sq_mul_le_cubes α β hα hβ; linarith
  have hy : γ ^ 2 * β ≤ 1 + C + D := by have := sq_mul_le_cubes γ β hγ hβ; linarith
  have hp1 : 0 < α ^ 2 * β := by positivity
  have hp2 : 0 < γ ^ 2 * β := by positivity
  have hprod : (α ^ 2 * β) ^ 2 * (γ ^ 2 * β) ^ 2 ≤ (1 + A + B) ^ 2 * (1 + C + D) ^ 2 := by
    gcongr
  have hδ4 : 0 < (δ ^ 4)⁻¹ := by positivity
  calc ((1 + A + B) ^ 2 * (1 + C + D) ^ 2)⁻¹ ≤ ((α ^ 2 * β) ^ 2 * (γ ^ 2 * β) ^ 2)⁻¹ :=
        inv_anti₀ (by positivity) hprod
    _ = (α ^ 4)⁻¹ * (γ ^ 4)⁻¹ * (β ^ 4)⁻¹ := by
        rw [← mul_inv, ← mul_inv]; congr 1; ring
    _ ≤ (α ^ 4)⁻¹ * (γ ^ 4)⁻¹ * ((β ^ 4)⁻¹ + (δ ^ 4)⁻¹) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity); linarith

end GlobalTheory.FlagGram

namespace GlobalTheory

theorem flagGram_density_ineq : ∀ a b c : ℂ, ((1 + ‖a‖ ^ 2 + ‖b‖ ^ 2) ^ 2 * (1 + ‖c‖ ^ 2 + ‖a * c - b‖ ^ 2) ^ 2)⁻¹ ≤ (1 + ‖a‖ ^ 2) ^ (-(4 / 3 : ℝ)) * (1 + ‖c‖ ^ 2) ^ (-(4 / 3 : ℝ)) * ((1 + ‖b‖ ^ 2) ^ (-(4 / 3 : ℝ)) + (1 + ‖a * c - b‖ ^ 2) ^ (-(4 / 3 : ℝ))) := by
  intro a b c
  rcases le_total (‖b‖ ^ 2) (‖a * c - b‖ ^ 2) with h | h
  · exact FlagGram.key _ _ _ _ (by positivity) (by positivity) (by positivity) (by positivity) h
  · have := FlagGram.key (‖c‖ ^ 2) (‖a * c - b‖ ^ 2) (‖a‖ ^ 2) (‖b‖ ^ 2)
      (by positivity) (by positivity) (by positivity) (by positivity) h
    calc _ = ((1 + ‖c‖ ^ 2 + ‖a * c - b‖ ^ 2) ^ 2 * (1 + ‖a‖ ^ 2 + ‖b‖ ^ 2) ^ 2)⁻¹ := by
          rw [mul_comm]
      _ ≤ _ := this
      _ = _ := by ring

end GlobalTheory
end

section

open Filter Topology

namespace GlobalTheory.ShiftHomomorphism

noncomputable def shiftHom (D : ℕ) (c : Fin D → ℂ) :
    MvPolynomial (Fin D) ℂ →ₐ[ℂ] MvPowerSeries (Fin D) ℂ :=
  MvPolynomial.aeval (fun i => MvPowerSeries.X i + MvPowerSeries.C (c i))

theorem shiftHom_X (D : ℕ) (c : Fin D → ℂ) (i : Fin D) :
    shiftHom D c (MvPolynomial.X i) = MvPowerSeries.X i + MvPowerSeries.C (c i) := by
  simp [shiftHom]

theorem constantCoeff_comp_shiftHom (D : ℕ) (c : Fin D → ℂ) :
    (MvPowerSeries.constantCoeff (σ := Fin D) (R := ℂ)).comp (shiftHom D c).toRingHom
      = MvPolynomial.eval c := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [shiftHom, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, MvPolynomial.aeval_C, MvPolynomial.eval_C]
    first | rfl | simp [MvPowerSeries.algebraMap_apply] | simp [Algebra.algebraMap_eq_smul_one]
  · intro i; simp [shiftHom]

theorem shiftHom_injective (D : ℕ) (c : Fin D → ℂ) : Function.Injective (shiftHom D c) := by
  let τ : MvPolynomial (Fin D) ℂ →ₐ[ℂ] MvPolynomial (Fin D) ℂ :=
    MvPolynomial.aeval (fun i => MvPolynomial.X i + MvPolynomial.C (c i))
  let τ' : MvPolynomial (Fin D) ℂ →ₐ[ℂ] MvPolynomial (Fin D) ℂ :=
    MvPolynomial.aeval (fun i => MvPolynomial.X i - MvPolynomial.C (c i))
  have hinv : τ'.comp τ = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext; intro i; simp [τ, τ']
  have hτ : Function.Injective τ := by
    intro a b h
    have := congrArg τ' h
    simpa [← AlgHom.comp_apply, hinv] using this
  have hfac : shiftHom D c = (MvPolynomial.coeToMvPowerSeries.algHom ℂ).comp τ := by
    apply MvPolynomial.algHom_ext; intro i; simp [shiftHom, τ]
  rw [hfac]
  exact (MvPolynomial.coe_injective _ _).comp hτ

end GlobalTheory.ShiftHomomorphism

namespace GlobalTheory


open GlobalTheory.ShiftHomomorphism in
theorem branches_of_unramified_point : ∀ (D : ℕ) (P : Polynomial (MvPolynomial (Fin D) ℂ)) (c : Fin D → ℂ), P.Monic → (P.map (MvPolynomial.eval c)).Separable → ∃ (n : ℕ) (φ : Fin n → (AdjoinRoot P →ₐ[ℂ] MvPowerSeries (Fin D) ℂ)), (∀ u, (∀ j, φ j u = 0) → u = 0) ∧ ∀ j i, φ j (AdjoinRoot.of P (MvPolynomial.X i)) = MvPowerSeries.X i + MvPowerSeries.C (c i) := by
  intro D P c hP hsep
  haveI : IsDomain (MvPowerSeries (Fin D) ℂ) := NoZeroDivisors.to_isDomain _
  set ψ := shiftHom D c with hψ
  set Q := P.map ψ.toRingHom with hQ
  have hQm : Q.Monic := hP.map _
  have hred : Q.map (MvPowerSeries.constantCoeff (σ := Fin D) (R := ℂ)) = P.map (MvPolynomial.eval c) := by
    rw [hQ, Polynomial.map_map, constantCoeff_comp_shiftHom]
  obtain ⟨θ, hθi, hθr⟩ := GlobalTheory.T.exists_lifts_of_separable_reduction D Q hQm (by rw [hred]; exact hsep)
  have hroot : ∀ j, P.eval₂ ψ.toRingHom (θ j) = 0 := by
    intro j
    have := hθr j
    rw [Polynomial.IsRoot.def, hQ, Polynomial.eval_map] at this
    exact this
  refine ⟨Q.natDegree, fun j => AdjoinRoot.liftAlgHom P ψ (θ j) (hroot j), ?_, ?_⟩
  · intro u hu
    obtain ⟨R, rfl⟩ := AdjoinRoot.mk_surjective u
    have hR : AdjoinRoot.mk P R = AdjoinRoot.mk P (R %ₘ P) := by
      rw [← AdjoinRoot.modByMonicHom_mk hP R, AdjoinRoot.mk_leftInverse hP]
    rw [hR] at hu ⊢
    by_contra hne
    have hR0 : R %ₘ P ≠ 0 := by
      intro h; apply hne; rw [h, map_zero]
    have hdeg : (R %ₘ P).natDegree < P.natDegree :=
      Polynomial.natDegree_lt_natDegree hR0 (Polynomial.degree_modByMonic_lt R hP)
    have hz : (R %ₘ P).map ψ.toRingHom = 0 := by
      refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hθi ?_ ?_
      · intro j
        have := hu j
        simpa [AdjoinRoot.liftAlgHom, AdjoinRoot.lift_mk, Polynomial.eval_map] using this
      · calc ((R %ₘ P).map ψ.toRingHom).natDegree ≤ (R %ₘ P).natDegree := Polynomial.natDegree_map_le
          _ < P.natDegree := hdeg
          _ = Q.natDegree := (hP.natDegree_map _).symm
          _ = Fintype.card (Fin Q.natDegree) := (Fintype.card_fin _).symm
    apply hR0
    exact Polynomial.map_injective _ (shiftHom_injective D c) (by rw [hz, Polynomial.map_zero])
  · intro j i
    simp [AdjoinRoot.liftAlgHom]
    rw [hψ]; exact shiftHom_X D c i

end GlobalTheory
end

section

open Polynomial

namespace GlobalTheory

theorem finiteDimensional_top_subfield (L : Type*) [Field L] :
    FiniteDimensional (⊤ : Subfield L) L := by
  refine ⟨⟨{1}, eq_top_iff.mpr fun l _ => ?_⟩⟩
  rw [Finset.coe_singleton, Submodule.mem_span_singleton]
  exact ⟨⟨l, Subfield.mem_top l⟩, mul_one l⟩

theorem exists_normal_finiteType_subring_of_valuationSubring : ∀ (K L : Type) [Field K] [Field L] (φ : K →+* L) (c : ℂ →+* K), (letI := φ.toAlgebra; FiniteDimensional K L) → ∀ (V : ValuationSubring L) (hc : ∀ a, φ (c a) ∈ V) (t : Finset L), (∀ x ∈ t, x ∈ V ∧ ∃ p : K[X], p.Monic ∧ (∀ i, p.coeff i ∈ V.comap φ) ∧ p.eval₂ φ x = 0) → (∀ s ∈ V, ∃ b ∈ Subring.closure (Set.range (φ.comp c) ∪ ↑t), ∃ d ∈ Subring.closure (Set.range (φ.comp c) ∪ ↑t), d ≠ 0 ∧ d⁻¹ ∈ V ∧ s = b / d) → ∃ R : Subring K, ∃ hcR : ∀ a, c a ∈ R, (c.codRestrict R hcR).FiniteType ∧ R ≤ (V.comap φ).toSubring ∧ IsNoetherianRing R ∧ IsIntegrallyClosed R ∧ IsFractionRing R K ∧ (∀ x ∈ t, ∃ p : R[X], p.Monic ∧ p.eval₂ (φ.comp R.subtype) x = 0) := by
  intro K L _ _ φ c hfin V hc t ht hgen
  classical
  letI : Algebra ℂ K := c.toAlgebra
  letI : Algebra K L := φ.toAlgebra
  letI : Algebra ℂ L := (φ.comp c).toAlgebra
  haveI : IsScalarTower ℂ K L := .of_algebraMap_eq fun _ => rfl
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℂ L).injective
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℂ K).injective
  have ht' : ∀ x : t, ∃ p : K[X], p.Monic ∧ (∀ i, p.coeff i ∈ V.comap φ) ∧ p.eval₂ φ x = 0 :=
    fun x => (ht x x.2).2
  choose p hpm hpc hpx using ht'
  let T : Set K := ⋃ x : t, ((p x).coeffs : Set K)
  have hT : T.Finite := Set.finite_iUnion fun x => (p x).coeffs.finite_toSet
  let A : Subalgebra ℂ K := Algebra.adjoin ℂ T
  haveI : Algebra.FiniteType ℂ A := .adjoin_of_finite hT
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℂ A
  have hcoefA : ∀ x : t, ∀ n, (p x).coeff n ∈ A := fun x n => by
    by_cases h : (p x).coeff n = 0
    · rw [h]; exact A.zero_mem
    · exact Algebra.subset_adjoin (Set.mem_iUnion.mpr ⟨x, Polynomial.coeff_mem_coeffs h⟩)
  have hAE : ∀ y ∈ A, y ∈ V.comap φ := fun y hy => by
    let E' : Subalgebra ℂ K := { (V.comap φ).toSubring with algebraMap_mem' := fun a => hc a }
    have : A ≤ E' := Algebra.adjoin_le (by
      intro y hy
      obtain ⟨x, hx⟩ := Set.mem_iUnion.mp hy
      obtain ⟨i, -, rfl⟩ := Polynomial.mem_coeffs_iff.mp hx
      exact hpc x i)
    exact this hy
  haveI : IsScalarTower A K L := .of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower ℂ A L := .of_algebraMap_eq fun _ => rfl
  have hint : ∀ x : t, IsIntegral A (x : L) := fun x => by
    obtain ⟨q, hq, -, hqm⟩ := lifts_and_natDegree_eq_and_monic (f := algebraMap A K)
      ((lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, hcoefA x n⟩, rfl⟩) (hpm x)
    refine ⟨q, hqm, ?_⟩
    rw [← hpx x, ← hq, eval₂_map]
    rfl

  have hsub : Subring.closure (Set.range (φ.comp c) ∪ (t : Set L)) ≤ (integralClosure A L).toSubring :=
    Subring.closure_le.mpr (Set.union_subset
      (by
        rintro _ ⟨a, rfl⟩
        exact isIntegral_algebraMap (R := A) (x := (⟨c a, A.algebraMap_mem a⟩ : A)))
      (fun x hx => hint ⟨x, hx⟩))
  have hall : ∀ l : L, ∃ b ∈ Subring.closure (Set.range (φ.comp c) ∪ (t : Set L)),
      ∃ d ∈ Subring.closure (Set.range (φ.comp c) ∪ (t : Set L)), (l = b / d ∨ l⁻¹ = b / d) := by
    intro l
    rcases V.mem_or_inv_mem l with h | h
    · obtain ⟨b, hb, d, hd, -, -, he⟩ := hgen l h
      exact ⟨b, hb, d, hd, Or.inl he⟩
    · obtain ⟨b, hb, d, hd, -, -, he⟩ := hgen _ h
      exact ⟨b, hb, d, hd, Or.inr he⟩
  haveI : Algebra.IsAlgebraic A L := ⟨fun l => by
    obtain ⟨b, hb, d, hd, h⟩ := hall l
    have hb' : IsAlgebraic A b := (hsub hb : IsIntegral A b).isAlgebraic
    have hd' : IsAlgebraic A d := (hsub hd : IsIntegral A d).isAlgebraic
    have hbd : IsAlgebraic A (b / d) := by rw [div_eq_mul_inv]; exact hb'.mul hd'.inv
    rcases h with h | h
    · rw [h]; exact hbd
    · rw [← inv_inv l, h]; exact hbd.inv⟩
  haveI : Algebra.IsAlgebraic A K := ⟨fun k =>
    (isAlgebraic_algHom_iff (IsScalarTower.toAlgHom A K L) φ.injective).mp
      (Algebra.IsAlgebraic.isAlgebraic (φ k))⟩
  have htop : Subfield.closure (Set.range (algebraMap ℂ L) ∪ (t : Set L)) = ⊤ := by
    refine eq_top_iff.mpr fun l _ => ?_
    have hle : Subring.closure (Set.range (φ.comp c) ∪ (t : Set L)) ≤
        (Subfield.closure (Set.range (algebraMap ℂ L) ∪ (t : Set L))).toSubring :=
      Subring.closure_le.mpr Subfield.subset_closure
    obtain ⟨b, hb, d, hd, h⟩ := hall l
    have hbd := Subfield.div_mem _ (hle hb) (hle hd)
    rcases h with h | h
    · rw [h]; exact hbd
    · rw [← inv_inv l, h]; exact Subfield.inv_mem _ hbd
  haveI : Algebra.EssFiniteType ℂ L := by
    refine essFiniteType_of_finiteDimensional_subfield_closure t.finite_toSet ?_
    rw [htop]
    exact finiteDimensional_top_subfield L
  haveI : Algebra.EssFiniteType A L := .of_comp ℂ A L
  haveI : Module.Finite A (integralClosure A L) :=
    GlobalTheory.finite_integralClosure_of_essFiniteType_field ℂ A L
  let S := integralClosure A K
  let f : S →ₐ[A] integralClosure A L :=
    ((IsScalarTower.toAlgHom A K L).comp S.val).codRestrict _ fun z =>
      (z.2.map (IsScalarTower.toAlgHom A K L) : IsIntegral A _)
  haveI : Module.Finite A S := Module.Finite.of_injective f.toLinearMap fun z w h =>
    Subtype.ext (φ.injective (congrArg Subtype.val h : _))
  set_option synthInstance.maxHeartbeats 200000 in
    haveI : Algebra.FiniteType ℂ S := Algebra.FiniteType.trans (S := A) inferInstance inferInstance
    haveI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing ℂ S
    haveI : IsFractionRing S K := integralClosure.isFractionRing_of_algebraic fun x hx => Subtype.ext hx
    haveI : IsIntegrallyClosed S := (isIntegrallyClosed_iff K).mpr fun {x} hx =>
      ⟨⟨x, isIntegral_trans x hx⟩, rfl⟩

    have hcR : ∀ a, c a ∈ S.toSubring := fun a => S.algebraMap_mem (⟨c a, A.algebraMap_mem a⟩ : A)
    refine ⟨S.toSubring, hcR, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact RingHom.finiteType_algebraMap.mpr (inferInstance : Algebra.FiniteType ℂ S)
    · intro x hx
      obtain ⟨q, hqm, hq⟩ := (hx : IsIntegral A x)
      let ι : A →+* V.comap φ :=
        { toFun := fun a => ⟨a, hAE a a.2⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl
          map_zero' := rfl
          map_add' := fun _ _ => rfl }
      have hE : IsIntegral (V.comap φ) x := by
        refine ⟨q.map ι, hqm.map ι, ?_⟩
        rw [eval₂_map]
        exact hq
      obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hE
      exact y.2
    · exact (inferInstance : IsNoetherianRing S)
    · exact (inferInstance : IsIntegrallyClosed S)
    · exact (inferInstance : IsFractionRing S K)
    · intro x hx
      obtain ⟨q, hq, -, hqm⟩ := lifts_and_natDegree_eq_and_monic (f := S.toSubring.subtype)
        ((lifts_iff_coeff_lifts _).mpr fun n =>
          ⟨⟨_, S.algebraMap_mem (⟨_, hcoefA ⟨x, hx⟩ n⟩ : A)⟩, rfl⟩) (hpm ⟨x, hx⟩)
      refine ⟨q, hqm, ?_⟩
      rw [← eval₂_map, hq]
      exact hpx ⟨x, hx⟩

end GlobalTheory
end

section

open TensorProduct

namespace GlobalTheory

theorem exists_pow_eq_of_kaehlerDifferential_eq_zero_of_smooth_domain :
    ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (S : Type)
      [CommRing S] [IsDomain S] [Algebra k S] [Algebra.Smooth k S] (f : S),
      KaehlerDifferential.D k S f = 0 → ∃ h : S, h ^ p = f := by
  intro p hp k _ _ hk S _ _ _ _ f hf
  have hS : IsIntegrallyClosed S :=
    IsIntegrallyClosed.of_localization_maximal fun m _ _ =>
      (isDomain_and_isIntegrallyClosed_atPrime_of_smooth k m _).2
  have hK : KaehlerDifferential.D k (FractionRing S) (algebraMap S (FractionRing S) f) = 0 := by
    rw [← KaehlerDifferential.map_D k k S (FractionRing S) f, hf, map_zero]
  obtain ⟨h, hh⟩ := GlobalTheory.T.exists_pow_eq_of_kaehler_D_eq_zero' p k hk (FractionRing S) _ hK
  have hint : IsIntegral S h :=
    IsIntegral.of_pow hp.out.pos (by rw [hh]; exact isIntegral_algebraMap)
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  refine ⟨y, IsFractionRing.injective S (FractionRing S) ?_⟩
  rw [map_pow, hh]

end GlobalTheory
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

theorem GlobalTheory.exists_pow_char_eq_of_isReduced_finite : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A] [IsReduced A], ∀ a : A, ∃ b : A, a = b ^ p := by
  intro p _ k _ _ _ A _ _ _ _ a
  haveI : IsArtinianRing A := IsArtinianRing.of_finite k A
  haveI : PerfectField k := PerfectRing.toPerfectField k p
  let e := IsArtinianRing.equivPi A
  have key : ∀ I : MaximalSpectrum A, ∃ c : A ⧸ I.asIdeal, e a I = c ^ p := by
    intro I
    haveI : I.asIdeal.IsMaximal := I.isMaximal
    letI : Field (A ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
    haveI : Module.Finite k (A ⧸ I.asIdeal) := Module.Finite.trans A (A ⧸ I.asIdeal)
    haveI : Algebra.IsAlgebraic k (A ⧸ I.asIdeal) := Algebra.IsAlgebraic.of_finite k _
    haveI : PerfectField (A ⧸ I.asIdeal) := Algebra.IsAlgebraic.perfectField k
    haveI : CharP (A ⧸ I.asIdeal) p :=
      charP_of_injective_algebraMap (algebraMap k (A ⧸ I.asIdeal)).injective p
    haveI : PerfectRing (A ⧸ I.asIdeal) p := PerfectField.toPerfectRing p
    obtain ⟨c, hc⟩ := surjective_frobenius (A ⧸ I.asIdeal) p (e a I)
    exact ⟨c, by rw [← hc, frobenius_def]⟩
  choose c hc using key
  refine ⟨e.symm c, e.injective ?_⟩
  rw [map_pow, AlgEquiv.apply_symm_apply]
  funext I
  rw [hc I, Pi.pow_apply]
end

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_separable_point_of_geometrically_domain : ∀ (k B : Type) [Field k] [CommRing B] [Algebra k B], Algebra.FiniteType k B → (∀ (K : Type) [Field K] [Algebra k K], FiniteDimensional k K → IsPurelyInseparable k K → IsDomain (K ⊗[k] B)) → ∃ (k' : Type) (_ : Field k') (_ : Algebra k k'), FiniteDimensional k k' ∧ Algebra.IsSeparable k k' ∧ Nonempty (B →ₐ[k] k') := by
  first | exact @GlobalTheory.SepPoint.exists_sepPoint | exact GlobalTheory.SepPoint.exists_sepPoint | (intros; apply GlobalTheory.SepPoint.exists_sepPoint <;> assumption)
end

section


theorem _root_.GlobalTheory.T.matrix_eq_aeval_of_commute_of_charpoly_separable : ∀ {k : Type} [Field k] (n : ℕ) (N X : Matrix (Fin n) (Fin n) k), N.charpoly.Separable → Commute X N → ∃ q : Polynomial k, X = Polynomial.aeval N q := by
  first | exact @GlobalTheory.CentralizerSeparable.matrix_eq_aeval_of_commute | exact GlobalTheory.CentralizerSeparable.matrix_eq_aeval_of_commute | (intros; apply GlobalTheory.CentralizerSeparable.matrix_eq_aeval_of_commute <;> assumption)
end

section

open scoped TensorProduct Polynomial

theorem _root_.GlobalTheory.T.exists_large_prime_sq_dvd_eval_of_separable : ∀ f : ℤ[X], 0 < f.natDegree → (f.map (Int.castRingHom ℚ)).Separable → ∀ n : ℕ, ∃ p : ℕ, p.Prime ∧ n < p ∧ ∃ x : ℤ, ((p : ℤ) ^ 2) ∣ f.eval x := by
  first | exact @GlobalTheory.sep_int_poly_root_mod_prime_sq | exact GlobalTheory.sep_int_poly_root_mod_prime_sq | (intros; apply GlobalTheory.sep_int_poly_root_mod_prime_sq <;> assumption)
end

section

open Polynomial Matrix Formalism.UG

namespace GlobalTheory.SepCharpoly

theorem charpoly_dvd_of_aeval_eq_zero :
    ∀ (R : Type) [CommRing R] [IsDomain R] (n : ℕ) (M : Matrix (Fin n) (Fin n) R) (p : R[X]),
      M.charpoly.Separable → aeval M p = 0 → M.charpoly ∣ p := by
  intro R _ _ n M p hs hp
  classical
  let K := FractionRing R
  let f : R →+* K := algebraMap R K
  have hf : Function.Injective f := IsFractionRing.injective R K
  rw [← Polynomial.map_dvd_map f hf M.charpoly_monic, ← Matrix.charpoly_map]
  refine GlobalTheory.ClassParam.charpoly_dvd_of_aeval (M.map f) ?_ (p.map f) ?_
  · rw [Matrix.charpoly_map]; exact hs.map
  · rw [show M.map f = (f.mapMatrix : Matrix (Fin n) (Fin n) R →+* _) M from rfl]
    have := congrArg (AlgHom.mapMatrix (m := Fin n) (Algebra.ofId R K)) hp
    rw [← aeval_algHom_apply, map_zero] at this
    rw [aeval_map_algebraMap]
    exact this

end GlobalTheory.SepCharpoly
end

section

open Polynomial Matrix

theorem _root_.GlobalTheory.T.exists_conj_of_charpoly_eq_of_separable_local : ∀ (R : Type) [CommRing R] [IsLocalRing R] (n : ℕ) (Y Y' : Matrix (Fin n) (Fin n) R), Y.charpoly = Y'.charpoly → Y.charpoly.Separable → ∃ g : GL (Fin n) R, Y' = (g⁻¹ : GL (Fin n) R).val * Y * g.val := by
  first | exact @GlobalTheory.ConjLocal.conj_of_charpoly_local | exact GlobalTheory.ConjLocal.conj_of_charpoly_local | (intros; apply GlobalTheory.ConjLocal.conj_of_charpoly_local <;> assumption)
end

section

open Matrix Polynomial

theorem _root_.GlobalTheory.T.conj_of_charpoly_eq_of_charpoly_separable : ∀ (R : Type) [Field R] (m : ℕ) (N U : Matrix (Fin m) (Fin m) R), N.charpoly = U.charpoly → N.charpoly.Separable → ∃ P : GL (Fin m) R, N * P.val = P.val * U := by
  first | exact @GlobalTheory.SimSep.conj_of_charpoly_eq_of_separable | exact GlobalTheory.SimSep.conj_of_charpoly_eq_of_separable | (intros; apply GlobalTheory.SimSep.conj_of_charpoly_eq_of_separable <;> assumption)
end
