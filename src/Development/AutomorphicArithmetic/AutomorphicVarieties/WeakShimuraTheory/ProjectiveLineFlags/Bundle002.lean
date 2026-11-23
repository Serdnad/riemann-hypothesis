module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.P1.coefRes {l : ℕ} [hl : Fact l.Prime] (c : Coef l) :
    Finite (ResidueField c.O) ∧ CharP (ResidueField c.O) l ∧
      (∀ (c' : Coef l) (h : c.O ≤ c'.O), IsLocalHom (inc h)) ∧
      ∀ (m : ℕ) (x : c.O), l.Coprime m → x ^ m = 1 → residue c.O x = 1 → x = 1 := by
  haveI := c.dvr
  haveI := c.fin
  obtain ⟨-, hfin, hlm, -, -, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  have hchar : CharP (ResidueField c.O) l := by
    obtain ⟨p, hp⟩ := CharP.exists (ResidueField c.O)
    have hp0 := CharP.char_ne_zero_of_finite (ResidueField c.O) p
    haveI : NeZero p := ⟨hp0⟩
    have hpp := (CharP.char_is_prime_of_pos (ResidueField c.O) p).out
    have hl0 : ((l : ℕ) : ResidueField c.O) = 0 := by
      rw [← map_natCast (residue c.O)]
      exact (IsLocalRing.residue_eq_zero_iff _).2 hlm
    have hdvd : p ∣ l := (CharP.cast_eq_zero_iff (ResidueField c.O) p l).1 hl0
    have hpl : p = l := (Nat.prime_dvd_prime_iff_eq hpp hl.out).1 hdvd
    subst hpl
    exact hp
  refine ⟨hfin, hchar, ?_, ?_⟩
  · intro c' h
    haveI := c'.fin
    have hint : (inc h).IsIntegral := by
      intro y
      obtain ⟨p, hp, hpy⟩ := Algebra.IsIntegral.isIntegral (R := ℤ_[l]) y
      refine ⟨p.map (algebraMap ℤ_[l] c.O), hp.map _, ?_⟩
      rw [Polynomial.eval₂_map]
      have hcomp : (inc h).comp (algebraMap ℤ_[l] c.O) = algebraMap ℤ_[l] c'.O :=
        RingHom.ext fun a => (Subalgebra.inclusion h).commutes a
      rw [hcomp]
      exact hpy
    exact hint.isLocalHom (Subalgebra.inclusion_injective h)
  · intro m x hcop hxm hres
    have hnd : ¬ l ∣ m := (Nat.Prime.coprime_iff_not_dvd hl.out).1 hcop
    have hsum : IsUnit (∑ i ∈ Finset.range m, x ^ i) := by
      by_contra hnu
      have hmem : (∑ i ∈ Finset.range m, x ^ i) ∈ maximalIdeal c.O :=
        (IsLocalRing.mem_maximalIdeal _).2 hnu
      have h0 := (IsLocalRing.residue_eq_zero_iff _).2 hmem

      rw [map_sum] at h0
      simp only [map_pow, hres, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        mul_one] at h0
      exact hnd ((CharP.cast_eq_zero_iff (ResidueField c.O) l m).1 h0)
    have hg := geom_sum_mul x m
    rw [hxm, sub_self] at hg
    have hx1 : x - 1 = 0 := by
      rcases mul_eq_zero.1 hg with h | h
      · exact absurd (h ▸ hsum) not_isUnit_zero
      · exact h
    exact sub_eq_zero.1 hx1
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem mul_eq_one_of_card_eq_two_of_ne_one {H : Type*} [Group H] (hH : Nat.card H = 2)
    (x y : H) (hx : x ≠ 1) (hy : y ≠ 1) : x * y = 1 := by
  classical
  haveI : Finite H := Nat.finite_of_card_ne_zero (by omega)
  haveI := Fintype.ofFinite H
  rw [Nat.card_eq_fintype_card] at hH
  by_contra hxy
  have h3 : ({1, x, x * y} : Finset H).card = 3 := by
    refine Finset.card_eq_three.mpr ⟨1, x, x * y, fun h => hx h.symm, fun h => hxy h.symm, ?_, rfl⟩
    intro h
    exact hy (mul_left_cancel (a := x) (by rw [mul_one]; exact h.symm))
  have := Finset.card_le_univ ({1, x, x * y} : Finset H)
  omega


theorem UpperTheory.V.Ws.P1.towerGal :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), (resLe T.F_le).range = T.GalL ∧ Function.Injective (resLe T.F_le) ∧ Continuous (resLe T.F_le) ∧
          (∀ a b : G T.F Ω, a ∉ T.GalL → b ∉ T.GalL → a * b ∈ T.GalL) ∧
          (∀ g : G T.L Ω, resQ T.F (resLe T.F_le g) = resQ T.L g ∧ cycZ T.F Ω l (resLe T.F_le g) = cycZ T.L Ω l g ∧ cycZ ℚ Ω l (resQ T.L g) = cycZ T.L Ω l g) ∧
          ∀ (A : ValuationSubring Ω) (g : G T.L Ω), (resLe T.F_le g ∈ Dec (F := T.F) A ↔ g ∈ Dec (F := T.L) A) ∧ (resLe T.F_le g ∈ Ine (F := T.F) A ↔ g ∈ Ine (F := T.L) A) := by
  intro Ω _ _ _ l _ c D T
  have hKL : T.K ≤ T.L := by
    rw [T.hL]
    exact le_sup_right
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold UpperTheory.V.Ws.Tower.GalL
    apply le_antisymm
    · rintro _ ⟨g, rfl⟩
      rw [Subgroup.mem_comap, IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      exact g.commutes ⟨x, hKL hx⟩
    · intro a ha
      rw [Subgroup.mem_comap] at ha
      have hF : resQ T.F a ∈ T.F.fixingSubgroup := by
        rw [IntermediateField.mem_fixingSubgroup_iff]
        intro x hx
        exact a.commutes ⟨x, hx⟩
      have hL : resQ T.F a ∈ T.L.fixingSubgroup := by
        rw [T.hL, IntermediateField.fixingSubgroup_sup]
        exact ⟨hF, ha⟩
      rw [IntermediateField.mem_fixingSubgroup_iff] at hL
      exact ⟨{ a.toRingEquiv with commutes' := fun x => hL x x.2 }, by ext z; rfl⟩
  · intro g₁ g₂ h
    ext z
    exact congrArg (fun k => k z) h
  · letI : Algebra T.F T.L := (IntermediateField.inclusion T.F_le).toRingHom.toAlgebra
    haveI : IsScalarTower T.F T.L Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have he : (resLe T.F_le : G T.L Ω → G T.F Ω) = AlgEquiv.restrictScalarsHom T.F := by
      funext g
      ext
      rfl
    rw [he]
    exact UpperTheory.V.Af.continuous_restrictScalarsHom _ _ _
  · unfold UpperTheory.V.Ws.Tower.GalL
    haveI : Algebra.IsQuadraticExtension ℚ T.K := ⟨T.degK⟩
    haveI hN : Normal ℚ T.K := Algebra.IsQuadraticExtension.normal ℚ T.K
    haveI : IsGalois ℚ T.K := {}
    have hcard : Nat.card (T.K ≃ₐ[ℚ] T.K) = 2 := by
      rw [IsGalois.card_aut_eq_finrank, T.degK]
    have hker := @IntermediateField.restrictNormalHom_ker ℚ Ω _ _ _ T.K
      (by convert hN)
    intro a b ha hb
    rw [Subgroup.mem_comap, ← hker, MonoidHom.mem_ker] at ha hb ⊢
    rw [map_mul, map_mul]
    exact mul_eq_one_of_card_eq_two_of_ne_one (by convert hcard <;> first | rfl | exact Subsingleton.elim _ _) _ _ ha hb
  · intro g
    exact ⟨by ext; rfl, rfl, rfl⟩
  · intro A g
    exact ⟨Iff.rfl, Iff.rfl⟩
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.P1.ccEx :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D) (s : W.HidaSetting l T.L Ω), ∃ cF : G T.F Ω, IsCC cF ∧
          ∀ g : G T.L Ω, ∃ g' : G T.L Ω, W.resP T.L Ω g' = s.c * W.resP T.L Ω g * s.c⁻¹ ∧ resLe T.F_le g' = cF * resLe T.F_le g * cF⁻¹ := by
  intro Ω _ _ _ l _ c D T s
  haveI := T.nL
  haveI := T.cmL
  haveI := T.nF
  haveI := T.realF
  haveI : Normal (W.Lp T.L) T.L := by
    unfold UpperTheory.V.W.Lp
    infer_instance
  obtain ⟨j, hj⟩ := s.hc
  have hstab : ∀ τ : G (W.Lp T.L) Ω, ∀ x : T.L, ∃ y : T.L, τ (x : Ω) = (y : Ω) := by
    intro τ x
    exact ⟨τ.restrictNormal T.L x, (AlgEquiv.restrictNormal_commutes τ T.L x).symm⟩
  have hfixF : ∀ x : T.F, s.c (x : Ω) = x := by
    intro x
    have hmem : (⟨(x : Ω), T.F_le x.2⟩ : T.L) ∈ NumberField.maximalRealSubfield T.L := by
      intro φ
      have h := NumberField.IsTotallyReal.complexEmbedding_isReal
        (φ.comp (IntermediateField.inclusion T.F_le).toRingHom)
      have h2 := RingHom.congr_fun (NumberField.ComplexEmbedding.isReal_iff.mp h) x
      simp only [NumberField.ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply] at h2
      exact h2
    exact s.c.commutes (show W.Lp T.L from (⟨_, hmem⟩ : NumberField.maximalRealSubfield T.L))
  let cF : G T.F Ω := { s.c.toRingEquiv with commutes' := fun x => hfixF x }
  refine ⟨cF, ⟨j, fun x => hj x⟩, ?_⟩
  intro g
  let ρ : Ω ≃+* Ω := s.c.symm.toRingEquiv.trans (g.toRingEquiv.trans s.c.toRingEquiv)
  have hρ : ∀ x : T.L, ρ (algebraMap T.L Ω x) = algebraMap T.L Ω x := by
    intro x
    obtain ⟨y, hy⟩ := hstab s.c⁻¹ x
    have hy' : s.c.symm (x : Ω) = (y : Ω) := hy
    change s.c (g (s.c.symm (x : Ω))) = (x : Ω)
    rw [hy']
    have hg : g (y : Ω) = (y : Ω) := g.commutes y
    rw [hg, ← hy']
    exact s.c.apply_symm_apply _
  refine ⟨AlgEquiv.ofRingEquiv hρ, ?_, ?_⟩
  · ext z
    rfl
  · ext z
    rfl
end
