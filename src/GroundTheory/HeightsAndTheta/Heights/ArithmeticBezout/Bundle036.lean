module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle019
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.OfFreeParAlgIndep
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle013
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

open Vertical.SecPointSeparable in
theorem ChartPointSeparable.proof (h : ChartFreeParAlgIndep.Statement) : ChartPointSeparable.Statement := by
  intro F _ _ n e K L _ _ _ _ _ _ u t η hu hK hη hrel hT htr
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, η j₀ ≠ 0 := by
    by_contra! h0
    simp [h0] at hT
  set z : Fin n → L := fun m => η m * (η j₀)⁻¹ with hz
  obtain ⟨hind, halg⟩ := h F n e K L u t η hu hK hη hrel hT j₀ hj₀ (htr j₀ hj₀)
  obtain ⟨r, hre, b, hb⟩ := Vertical.DerivSpanTrdeg.full F L (Fin n) z e (htr j₀ hj₀)
  have hfin : Module.Finite K L := by
    have h1 : FiniteDimensional K (IntermediateField.adjoin K (Set.range η)) :=
      IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
    rw [hη] at h1
    exact Module.Finite.equiv IntermediateField.topEquiv.toLinearEquiv
  have hadj : Algebra.adjoin K (Set.range η) = ⊤ := by
    rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
      (fun x _ => Algebra.IsAlgebraic.isAlgebraic x), hη, IntermediateField.top_toSubalgebra]
  apply isSeparable_of_derivation_eq_zero
  intro D
  obtain ⟨c, hc⟩ := hb (D.restrictScalars F)
  have hc' : ∀ j, D (z j) = ∑ m, c m * (b m j : L) := hc
  have hlin : ∀ (a : K) (y : L), D (algebraMap K L a * y) = algebraMap K L a * D y := by
    intro a y
    rw [D.leibniz, D.map_algebraMap, smul_zero, add_zero, smul_eq_mul]
  have hDz₀ : D (z j₀) = 0 := by
    simp only [z, mul_inv_cancel₀ hj₀, Derivation.map_one_eq_zero]
  have hUDz : ∀ i : Fin e, ∑ j, algebraMap K L (u (i, j)) * D (z j) = 0 := by
    intro i
    have h0 : ∑ j, algebraMap K L (u (i, j)) * z j = 0 := by
      simp only [z, ← mul_assoc, ← Finset.sum_mul, hrel i, zero_mul]
    have := congrArg D h0

    rw [map_sum, map_zero] at this
    rw [← this]
    exact Finset.sum_congr rfl fun j _ => (hlin _ _).symm
  have hDz : ∀ j, D (z j) = 0 := by
    have key := Vertical.GenericFormsKer.full (IntermediateField.adjoin F (Set.range z)) L
      {j : Fin n // j ≠ j₀} e r hre (fun p => algebraMap K L (u (p.1, p.2.1))) hind
      (fun m j => b m j.1) c (fun i => ?_)
    · intro j
      by_cases hj : j = j₀
      · rw [hj, hDz₀]
      · rw [hc' j]
        exact key ⟨j, hj⟩
    · have := hUDz i
      rw [Fintype.sum_eq_add_sum_subtype_ne _ j₀, hDz₀, mul_zero, zero_add] at this
      rw [← this]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hc' j.1]
      rfl
  have hη₀ : D (η j₀) = 0 := by
    have hs : ∑ m, algebraMap F L (t m) * z m = (η j₀)⁻¹ := by
      simp only [z, ← mul_assoc, ← Finset.sum_mul, hT, one_mul]
    have h1 := congrArg D hs

    rw [map_sum, Finset.sum_eq_zero fun m _ => by
      rw [IsScalarTower.algebraMap_apply F K L, hlin, hDz, mul_zero],
    Derivation.leibniz_inv, eq_comm, smul_eq_mul, neg_mul, neg_eq_zero, mul_eq_zero] at h1
    exact h1.resolve_left (pow_ne_zero _ (inv_ne_zero hj₀))
  have hηj : ∀ j, D (η j) = 0 := by
    intro j
    have hηz : η j = z j * η j₀ := by simp only [z, mul_assoc, inv_mul_cancel₀ hj₀, mul_one]
    rw [hηz, D.leibniz, hη₀, hDz, smul_zero, smul_zero, add_zero]
  exact Derivation.ext_of_adjoin_eq_top (Set.range η) hadj (by rintro _ ⟨j, rfl⟩; simpa using hηj j)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem ChartFracSeparable.proof (h : ChartPointSeparable.Statement) : ChartFracSeparable.Statement := by
  intro F _ _ n e I f t p _ K L _ _ _ _ _ _ _ _ _ _ hI hf _

  let S := MvPolynomial (Fin e × Fin n) F
  let O := Localization.AtPrime p
  let Sg := ChartInc I t e
  let CL := ChartLoc I t e p
  let φ : S →+* K := (algebraMap O K).comp (algebraMap S O)
  let _ : Algebra F K := (φ.comp (algebraMap F S)).toAlgebra
  let _ : Algebra F L := ((algebraMap K L).comp (algebraMap F K)).toAlgebra
  have : IsScalarTower F K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let u : Fin e × Fin n → K := fun q => φ (X q)
  let ψ : Sg →+* L := (algebraMap CL L).comp (algebraMap Sg CL)
  let mk : MvPolynomial (Fin n ⊕ Fin e × Fin n) F →+* Sg := Ideal.Quotient.mk (chartIncIdeal I t e)
  have hmk0 : ∀ P, P ∈ chartIncIdeal I t e → mk P = 0 := fun P hP => Ideal.Quotient.eq_zero_iff_mem.2 hP
  let η : Fin n → L := fun m => ψ (chartX I t e (X m))
  have hφinj : Function.Injective φ :=
    (IsFractionRing.injective O K).comp
      (IsLocalization.injective O (M := p.primeCompl) p.primeCompl_le_nonZeroDivisors)
  have hφ : ∀ a, φ a = aeval u a := by
    intro a
    have : φ = (aeval u : S →ₐ[F] K).toRingHom :=
      MvPolynomial.ringHom_ext (fun c => by simp; rfl) (fun q => by simp [u])
    rw [this]
    rfl

  have hψS : ∀ s : S, ψ (algebraMap S Sg s) = algebraMap K L (φ s) := by
    intro s
    simp only [ψ, φ, RingHom.comp_apply]
    rw [← IsScalarTower.algebraMap_apply S Sg CL, IsScalarTower.algebraMap_apply S O CL,
      ← IsScalarTower.algebraMap_apply O CL L, IsScalarTower.algebraMap_apply O K L]
  have hmkS : ∀ s : S, mk (rename Sum.inr s) = algebraMap S Sg s :=
    fun s => rfl
  have hC : ∀ c : F, ψ (mk (C c)) = algebraMap F L c := by
    intro c
    rw [← rename_C Sum.inr, hmkS, hψS]
    rfl
  have hXl : ∀ m, ψ (mk (X (Sum.inl m))) = η m := by
    intro m
    show ψ (mk (X (Sum.inl m))) = ψ (mk (rename Sum.inl (X m)))
    rw [rename_X]
  have hXr : ∀ q, ψ (mk (X (Sum.inr q))) = algebraMap K L (u q) := by
    intro q
    rw [← rename_X Sum.inr, hmkS, hψS]

  have hψX : ∀ g, ψ (chartX I t e g) = aeval η g := by
    intro g
    have : ψ.comp (chartX I t e) = (aeval η : MvPolynomial (Fin n) F →ₐ[F] L).toRingHom :=
      MvPolynomial.ringHom_ext (fun c => by
        show ψ (mk (rename Sum.inl (C c))) = _
        rw [rename_C, hC]
        simp) (fun m => by simp [η])
    exact congrArg (fun r : MvPolynomial (Fin n) F →+* L => r g) this
  have hzero : ∀ g ∈ I ⊔ Ideal.span {linForm t - 1}, chartX I t e g = 0 := by
    intro g hg
    exact hmk0 _ (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hg))
  have hIη : ∀ g ∈ I, aeval η g = 0 := fun g hg => by
    rw [← hψX, hzero g (Ideal.mem_sup_left hg), map_zero]

  have hU : ∀ i : Fin e, ∑ m, algebraMap K L (u (i, m)) * η m = 0 := by
    intro i
    have hmem : ∑ m, X (Sum.inr (i, m)) * X (Sum.inl m) ∈ chartIncIdeal I t e :=
      Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩)
    have := congrArg ψ (hmk0 _ hmem)

    rw [map_zero, map_sum, map_sum] at this
    rw [← this]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_mul, map_mul, hXr, hXl]
  have hT : ∑ m, algebraMap F L (t m) * η m = 1 := by
    have h1 := hzero (linForm t - 1) (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    rw [map_sub, map_one, sub_eq_zero] at h1
    have := congrArg ψ h1
    rw [map_one, hψX] at this
    rw [← this]
    simp [linForm]

  have hK : IntermediateField.adjoin F (Set.range u) = ⊤ := by
    have hmemS : ∀ s : S, φ s ∈ IntermediateField.adjoin F (Set.range u) := fun s => by
      rw [hφ]
      apply IntermediateField.algebra_adjoin_le_adjoin
      rw [Algebra.adjoin_range_eq_range_aeval]
      exact ⟨s, rfl⟩
    have hmemO : ∀ a : O, algebraMap O K a ∈ IntermediateField.adjoin F (Set.range u) := fun a => by
      obtain ⟨⟨s, s', hs'⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl a
      dsimp only
      have hs0 : φ s' ≠ 0 := fun h0 => hs' (by
        rw [hφinj (h0.trans (map_zero φ).symm)]
        exact p.zero_mem)
      have hspec := congrArg (algebraMap O K) (IsLocalization.mk'_spec O s ⟨s', hs'⟩)
      rw [map_mul] at hspec
      rw [eq_div_of_mul_eq hs0 hspec]
      exact div_mem (hmemS s) (hmemS s')
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := O) x
    exact div_mem (hmemO a) (hmemO b)

  have hη : IntermediateField.adjoin K (Set.range η) = ⊤ := by
    set E := IntermediateField.adjoin K (Set.range η)
    have hmemSg : ∀ σ : Sg, ψ σ ∈ E := by
      intro σ
      obtain ⟨P, rfl⟩ : ∃ P, mk P = σ := Ideal.Quotient.mk_surjective σ
      induction P using MvPolynomial.induction_on with
      | C c =>
        rw [hC, IsScalarTower.algebraMap_apply F K L]
        exact E.algebraMap_mem _
      | add a b ha hb =>
        rw [map_add (f := _), map_add (f := _)]
        exact add_mem ha hb
      | mul_X a v ha =>
        rw [map_mul, map_mul]
        refine mul_mem ha ?_
        rcases v with m | q
        · rw [hXl]
          exact IntermediateField.subset_adjoin K _ ⟨m, rfl⟩
        · rw [hXr]
          exact E.algebraMap_mem _
    have hmemCL : ∀ c : CL, algebraMap CL L c ∈ E := fun c => by
      obtain ⟨⟨σ, s⟩, rfl⟩ := IsLocalization.mk'_surjective
        (Algebra.algebraMapSubmonoid Sg p.primeCompl) c
      dsimp only
      obtain ⟨s0, hs0, hs⟩ := s.2
      have hne : ψ s.1 ≠ 0 := by
        rw [← hs]
        rw [hψS]
        refine (map_ne_zero _).2 fun h0 => hs0 ?_
        rw [hφinj (h0.trans (map_zero φ).symm)]
        exact p.zero_mem
      have hspec := congrArg (algebraMap CL L) (IsLocalization.mk'_spec CL σ s)
      rw [map_mul] at hspec
      rw [eq_div_of_mul_eq hne hspec]
      exact div_mem (hmemSg σ) (hmemSg _)
    refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := CL) y
    exact div_mem (hmemCL a) (hmemCL b)

  have halg : AlgebraicIndependent F u := by
    have hinj : Function.Injective (aeval u : S →ₐ[F] K) := fun a b hab =>
      hφinj (by rw [hφ, hφ]; exact hab)
    have h0 := (MvPolynomial.algebraicIndependent_X (Fin e × Fin n) F).map' hinj
    have hc : (⇑(aeval u : S →ₐ[F] K) ∘ X) = u := by
      funext q
      simp only [Function.comp_apply, aeval_X]
    rwa [hc] at h0
  exact h F n e K L u t η halg hK hη hU hT fun j₀ hj₀ =>
    Vertical.ChartPointTrdeg.full F L n e I f hI hf η j₀ hIη hj₀

end

end GroundTheory.Heights₂.Heights
end
