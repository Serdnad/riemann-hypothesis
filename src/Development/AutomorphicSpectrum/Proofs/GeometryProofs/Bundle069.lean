module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle052
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle053
import Mathlib.Algebra.Module.StablyFree.Basic
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle062
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle004
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle061
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.FarguesHodgeTate
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint.TiedMap

theorem tied_map_comp : ∀ (E : Type) [Field E] [NumberField E] (Ω Vs K C : Type) [Field Ω] [AddCommGroup Vs] [Module Ω Vs] [Field K] [Field C]
    (ρ : 𝓞 E →+* Module.End Ω Vs) (R' : Subring Ω) (g : ℕ) (ℓ : Fin g → Vs) (ψ : R' →+* K) (j : K →+* C)
    (ρK : 𝓞 E →+* Module.End K (Fin g → K)) (ρC : 𝓞 E →+* Module.End C (Fin g → C)),
    (∀ a i, ρ a (ℓ i) ∈ Submodule.span R' (Set.range ℓ)) → Tied ℓ ψ ρ ρK → Tied ℓ (j.comp ψ) ρ ρC →
    ∀ (a : 𝓞 E) (x : Fin g → K), ρC a (fun i => j (x i)) = fun i => j (ρK a x i) := by
  intro E _ _ Ω Vs K C _ _ _ _ _ ρ R' g ℓ ψ j ρK ρC hρ hK hC a x
  have hex : ∀ i, ∃ c : Fin g → R', ρ a (ℓ i) = comb ℓ c := by
    intro i
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R').1 (hρ a i)
    exact ⟨c, by rw [← hc]; rfl⟩
  choose c hc using hex
  have hs : ∀ i, comb ℓ (Pi.single i (1 : R') : Fin g → R') = ℓ i := by
    intro i
    unfold comb
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · simp
  have h1 : ∀ i, ρK a (Pi.single i (1 : K)) = fun k => ψ (c i k) := by
    intro i
    have := hK a (Pi.single i 1) (c i) (by rw [hs, hc])
    rw [← this]
    congr 1
    ext k
    by_cases h : k = i
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  have h2 : ∀ i, ρC a (Pi.single i (1 : C)) = fun k => j (ψ (c i k)) := by
    intro i
    have := hC a (Pi.single i 1) (c i) (by rw [hs, hc])
    simp only [RingHom.comp_apply] at this
    rw [← this]
    congr 1
    ext k
    by_cases h : k = i
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  have hxK : x = ∑ i, x i • (Pi.single i (1 : K) : Fin g → K) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  have hxC : (fun i => j (x i)) = ∑ i, j (x i) • (Pi.single i (1 : C) : Fin g → C) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]

  rw [hxC, map_sum]

  conv_rhs => rw [hxK, map_sum]
  ext k
  simp [Finset.sum_apply, h1, h2]

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint.TiedMap
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem norm_prime_padicComplex (p : Nat.Primes) : ‖((p : ℕ) : ℂ_[p])‖ = ((p : ℕ) : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap', Padic.norm_p]

theorem ocp_integers : ∀ p : Nat.Primes, (NormedField.valuation (K := ℂ_[p])).Integers (OCp p) ∧
    (∃ x : ℂ_[p], 0 < NormedField.valuation (K := ℂ_[p]) x ∧ NormedField.valuation (K := ℂ_[p]) x < 1) ∧
    ∀ x : ℂ_[p], x ∈ (algebraMap (OCp p) ℂ_[p]).range ↔ ‖x‖ ≤ 1 := by
  intro p
  have hI : (NormedField.valuation (K := ℂ_[p])).Integers (GlobalTheory.CompanionTheory.Ar.Flat.CPoint.OCp p) :=
    Valuation.valuationSubring.integers _
  refine ⟨hI, ⟨((p : ℕ) : ℂ_[p]), ?_, ?_⟩, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · rw [NormedField.valuation_apply, ← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_zero,
      GlobalTheory.CompanionTheory.Ar.Flat.CPoint.norm_prime_padicComplex]
    exact inv_pos.2 (by exact_mod_cast p.2.pos)
  · rw [NormedField.valuation_apply, ← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one,
      GlobalTheory.CompanionTheory.Ar.Flat.CPoint.norm_prime_padicComplex]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast p.2.one_lt)
  · obtain ⟨y, rfl⟩ := RingHom.mem_range.1 hx
    have h := hI.map_le_one y
    rwa [NormedField.valuation_apply, ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one] at h
  · refine RingHom.mem_range.2 (hI.exists_of_le_one ?_)
    rwa [NormedField.valuation_apply, ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem hodgeAt_stable : ∀ (E : Type) [Field E] [NumberField E] (Ω Vs : Type) [Field Ω] [AddCommGroup Vs] [Module Ω Vs]
    (ρ : 𝓞 E →+* Module.End Ω Vs) (ρH : 𝓞 E →+* Module.End Ω (Vs × Module.Dual Ω Vs))
    (R : Subring Ω) (g N : ℕ) (ℓ : Fin g → Vs) (t : Fin N → Vs × Module.Dual Ω Vs)
    (HL : Submodule R (Vs × Module.Dual Ω Vs)),
    (∀ a y, (ρH a y).1 = ρ a y.1) → HodgeAt ρH HL ℓ t →
    (∀ i, t i ∈ HL) ∧ (∀ a, ∀ h ∈ HL, ρH a h ∈ HL) ∧ ∀ a i, ρ a (ℓ i) ∈ Submodule.span R (Set.range ℓ) := by
  intro E _ _ Ω Vs _ _ _ ρ ρH R g N ℓ t HL h1 h
  obtain ⟨⟨-, -, hX⟩, hmap, -⟩ := h
  have key : ∀ (c : 𝓞 E) (i : Fin N), ρH c (t i) ∈ HL := by
    intro c i

    rw [hX, ← (RingOfIntegers.basis E).sum_repr c, map_sum, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [map_zsmul, LinearMap.smul_apply]
    exact zsmul_mem (Submodule.subset_span (Set.mem_range.2 ⟨(i, k), rfl⟩)) _
  have stable : ∀ a, ∀ y ∈ HL, ρH a y ∈ HL := by
    intro a y hy
    rw [hX] at hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨q, rfl⟩ := hx
      rw [← Module.End.mul_apply, ← map_mul]
      exact key _ _
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add (f := _)]
      exact add_mem hx hy
    | smul r x _ hx =>
      have e : ρH a (r • x) = r • ρH a x := map_smul (ρH a) (r : Ω) x
      rw [e]
      exact HL.smul_mem r hx
  refine ⟨fun i => ?_, stable, fun a i => ?_⟩
  · simpa using key 1 i
  · have hi : ℓ i ∈ HL.map ((LinearMap.fst Ω Vs (Module.Dual Ω Vs)).restrictScalars R) :=
      hmap ▸ Submodule.subset_span ⟨i, rfl⟩
    obtain ⟨y, hy, e⟩ := hi
    rw [← hmap]
    refine ⟨ρH a y, stable a y hy, ?_⟩
    have e' : y.1 = ℓ i := e
    change (ρH a y).1 = _
    rw [h1, e']

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint.EvalProj

theorem ev_eigProj : ∀ (E : Type) [Field E] [NumberField E] (Ω Vs C : Type) [Field Ω] [AddCommGroup Vs] [Module Ω Vs] [Field C]
    (R' : Subring Ω) (g : ℕ) (ℓ : Fin g → Vs) (ψ : R' →+* C)
    (ρH : 𝓞 E →+* Module.End Ω (Vs × Module.Dual Ω Vs))
    (ρHC : 𝓞 E →+* Module.End C ((Fin g → C) × Module.Dual C (Fin g → C)))
    (HL : Submodule R' (Vs × Module.Dual Ω Vs)) (ev : HL →ₛₗ[ψ] (Fin g → C) × Module.Dual C (Fin g → C))
    (σ : E →+* Ω) (σC : E →+* C) (h : HL) (hp : HT.eigProj ρH σ (h : Vs × Module.Dual Ω Vs) ∈ HL),
    IsEval ℓ ψ ρH ρHC HL ev → (∀ e : E, ∃ h : σ e ∈ R', ψ ⟨σ e, h⟩ = σC e) → (∀ a, ∀ h ∈ HL, ρH a h ∈ HL) →
    ev ⟨_, hp⟩ = HT.eigProj ρHC σC (ev h) := by
  intro E _ _ Ω Vs C _ _ _ _ R' g ℓ ψ ρH ρHC HL ev σ σC h hp hev htie hst
  choose hc hψ using htie
  have hsum : (⟨_, hp⟩ : HL) = ∑ k, (⟨σ (HT.dualInt E k), hc _⟩ : R') •
      (⟨ρH (RingOfIntegers.basis E k) (h : Vs × Module.Dual Ω Vs), hst _ _ h.2⟩ : HL) := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    simp only [HT.eigProj, LinearMap.sum_apply, LinearMap.smul_apply]
    rfl

  rw [hsum, map_sum]
  simp only [HT.eigProj, LinearMap.sum_apply, LinearMap.smul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.map_smulₛₗ, hψ, hev.1 _ h]

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint.EvalProj
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem fibAt_lat_eq_stdLat : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (Em : Type) [AddCommGroup Em] [Module Ω Em]
    (M : LieModel G ξ Em) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
    (x : Sp K ⟶ X) (z : Sp V ⟶ X) (h₁ : genPt ξ ⤳ centre x) (h₂ : genPt ξ ⤳ centre z) (ψ : regAt ξ ⟨_, h₁⟩ →+* K) (g : ℕ)
    (ℓ : Fin g → Em) (MX : LieModel G x (Fin g → K)) (MC : LieModel G (Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ z) (Fin g → K)),
    spMap (algebraMap V K) ≫ z = x → (∀ e, (MC.pt e).left = (MX.pt e).left) → IsCptGen ξ →
    regAt ξ ⟨_, h₂⟩ ≤ regAt ξ ⟨_, h₁⟩ →
    (∀ (a : Ω) (h : a ∈ regAt ξ ⟨_, h₁⟩), a ∈ regAt ξ ⟨_, h₂⟩ → ψ ⟨a, h⟩ ∈ (algebraMap V K).range) →
    M.lat.IsFrameAt ℓ ⟨_, h₂⟩ →
    (∀ w : Fin g → regAt ξ ⟨_, h₁⟩, M.ValAt x (comb ℓ w) (MX.pt (fun i => ψ (w i)))) →
    M.fibAt M.lat z MC = stdLat V K g := by
  intro X G _ Ω _ ξ Em _ _ M V K _ _ _ _ _ _ x z h₁ h₂ ψ g ℓ MX MC hx hpt hξ hle hint hfr hval
  subst hx
  have hMC : ∀ e, MC.pt e = MX.pt e := fun e => Over.OverMorphism.ext (hpt e)
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro w ⟨h, e, he, hv⟩
    have he' : e ∈ M.lat ⟨_, h₂⟩ := he
    rw [hfr.2] at he'
    obtain ⟨r, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 he'
    have hc : comb ℓ (fun i => (⟨(r i : Ω), hle (r i).2⟩ : regAt ξ ⟨_, h₁⟩)) = ∑ i, r i • ℓ i := rfl
    have h3 := hval (fun i => ⟨(r i : Ω), hle (r i).2⟩)
    rw [hc] at h3
    have e1 := LieModel.ValAt.unique hξ hv h3
    rw [hMC] at e1
    have e2 := MX.inj e1
    intro i
    rw [e2]
    exact hint _ _ (r i).2
  · intro w hw
    have hw' : ∀ i, w i ∈ (algebraMap V K).range := hw
    choose v hv using hw'
    have hsum : w = ∑ i, v i • (Pi.single i 1 : Fin g → K) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def, hv]
    rw [hsum]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨h₂, ℓ i, ?_, ?_⟩)
    · rw [hfr.2]
      exact Submodule.subset_span ⟨i, rfl⟩
    · have h3 := hval (Pi.single i 1)
      have hc : comb ℓ (Pi.single i 1 : Fin g → regAt ξ ⟨_, h₁⟩) = ℓ i := by
        unfold comb
        rw [Finset.sum_eq_single i]
        · simp
        · intro b _ hb
          simp [Pi.single_apply, hb]
        · intro hi
          exact absurd (Finset.mem_univ i) hi
      have hs : (fun j => ψ ((Pi.single i 1 : Fin g → regAt ξ ⟨_, h₁⟩) j)) = (Pi.single i 1 : Fin g → K) := by
        ext j
        by_cases hj : j = i
        · subst hj; simp
        · simp [Pi.single_apply, hj]
      rw [hc, hs] at h3
      rw [hMC]
      exact h3

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
end
end

section

namespace GlobalTheory.CompanionTheory.Ar.Flat.HTL

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT GlobalTheory.CompanionTheory.Ar.Flat

theorem eq_zero_of_forall_om' {A K : Type} [CommRing A] [Field K] [Algebra A K] [CharZero K] {E : Type} [Field E]
    [NumberField E] {c : E ≃+* E} {p R N : ℕ} [Fact p.Prime] {Li : Type} [AddCommGroup Li] [Module K Li]
    (D : HTChart A K c p R N (Module.Dual K Li))
    (hspan : Submodule.span K (D.om : Set (Module.Dual K Li)) = ⊤)
    {e : Li} (he : ∀ w ∈ D.om', w e = 0) : e = 0 := by
  have hp : (p : K) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have h1 : ∀ w ∈ D.om, w e = 0 := by
    intro w hw
    have hm : ((p : A) ^ R) • w ∈ D.om' := Submodule.mem_sup_right ⟨w, hw, rfl⟩
    have h := he _ hm
    rw [LinearMap.smul_apply, Algebra.smul_def, map_pow, map_natCast] at h
    exact (mul_eq_zero.1 h).resolve_left (pow_ne_zero _ hp)
  have h2 : Submodule.span K (D.om : Set (Module.Dual K Li)) ≤ LinearMap.ker (Module.Dual.eval K Li e) :=
    Submodule.span_le.2 fun w hw => h1 w hw
  rw [hspan] at h2
  exact (Module.forall_dual_apply_eq_zero_iff K e).1 fun w => h2 (Submodule.mem_top (x := w))

theorem exists_lift_retract : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Li : Type) [AddCommGroup Li] [Module K Li] (D : HTChart A K c p R N (Module.Dual K Li)) (ρ : 𝓞 E →+* Module.End K Li), (∀ (a : 𝓞 E) (w : Module.Dual K Li), D.ρΩ a w = w ∘ₗ ρ (RingOfIntegers.mapRingEquiv c a)) → ∀ (σ : E →+* K) (d : A) (m : ℕ) (i : Module.Dual A (D.omHT (σ.comp c.toRingHom)) →ₗ[A] (Fin N → A)), algebraMap A K d ≠ 0 → D.ExactMod σ m i → ∃ (J : Li →ₗ[K] (Fin N → K)) (Rr : (Fin N → K) →ₗ[K] Li), (∀ e ∈ HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ σ) (algebraMap A K d) (algebraMap A K).range, ∃ f : Module.Dual A (D.omHT (σ.comp c.toRingHom)), (∀ z : D.omHT (σ.comp c.toRingHom), algebraMap A K (f z) = algebraMap A K d * (z : Module.Dual K Li) e) ∧ ∀ l, J e l = algebraMap A K (i f l)) ∧ (∀ k, Rr (Pi.single k 1) ∈ HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ σ) (algebraMap A K d) (algebraMap A K).range) ∧ ∀ e ∈ HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ σ) (algebraMap A K d) (algebraMap A K).range, ∃ e' ∈ HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ σ) (algebraMap A K d) (algebraMap A K).range, Rr (J e) = e + ((p : K) ^ m) • e' := by
  intro A K _ _ _ _ _ _ _ E _ _ c hc p R N _ Li _ _ D ρ hact σ d m i hd hex
  classical
  have hττ : (σ.comp c.toRingHom).comp c.toRingHom = σ := by
    ext x
    simp [hc]
  have hinj := IsFractionRing.injective A K
  have hE : ∀ e ∈ _root_.GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ σ, ∀ w : Module.Dual K Li, eigProj D.ρΩ (σ.comp c.toRingHom) w e = w e :=
    fun e he w => eigProj_apply D ρ hc hact (σ.comp c.toRingHom) (by rw [hττ]; exact he) w
  have hvec0 : ∀ g : Module.Dual A (D.omHT (σ.comp c.toRingHom)), ∃ e ∈ _root_.GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ σ,
      ∀ z : D.omHT (σ.comp c.toRingHom),
        algebraMap A K d * (z : Module.Dual K Li) e = algebraMap A K (g z) := by
    intro g
    obtain ⟨e, he, hz⟩ := exists_vec D ρ hc hact (σ.comp c.toRingHom) g
    rw [hττ] at he
    refine ⟨(algebraMap A K d)⁻¹ • e, Submodule.smul_mem _ _ he, fun z => ?_⟩
    rw [map_smul, hz, smul_eq_mul, mul_inv_cancel_left₀ hd]
  choose vec hvecS hvec using hvec0
  have hmem : ∀ w ∈ D.om', ∃ z : D.omHT (σ.comp c.toRingHom),
      (z : Module.Dual K Li) = eigProj D.ρΩ (σ.comp c.toRingHom) w :=
    fun w hw => ⟨⟨_, w, hw, rfl⟩, rfl⟩
  let : Module A Li := Module.compHom Li (algebraMap A K)
  have : IsScalarTower A K Li := ⟨fun a k v => by
    change (a • k) • v = algebraMap A K a • (k • v)
    rw [Algebra.smul_def, mul_smul]⟩
  have hsmul : ∀ (a : A) (v : Li), a • v = algebraMap A K a • v := fun _ _ => rfl
  have hvW : ∀ g, vec g ∈ latOn D (_root_.GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ σ) (algebraMap A K d) (algebraMap A K).range := fun g =>
    ⟨hvecS g, fun w hw => by
      obtain ⟨z, hz⟩ := hmem w hw
      rw [← hE _ (hvecS g) w, ← hz, hvec]
      exact ⟨_, rfl⟩⟩
  let Wsub : Submodule A Li :=
    { carrier := latOn D (_root_.GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ σ) (algebraMap A K d) (algebraMap A K).range
      add_mem' := fun {a b} ha hb => ⟨Submodule.add_mem _ ha.1 hb.1, fun w hw => by
        rw [map_add (f := _), mul_add]
        exact add_mem (ha.2 w hw) (hb.2 w hw)⟩
      zero_mem' := ⟨Submodule.zero_mem _, fun w _ => by
        rw [map_zero, mul_zero]
        exact zero_mem _⟩
      smul_mem' := fun a x hx => ⟨by
          rw [hsmul]
          exact Submodule.smul_mem _ _ hx.1, fun w hw => by
        rw [hsmul, map_smul, smul_eq_mul, mul_left_comm]
        exact mul_mem ⟨a, rfl⟩ (hx.2 w hw)⟩ }
  have hF0 : ∀ (e : Wsub) (z : D.omHT (σ.comp c.toRingHom)), ∃ a : A,
      algebraMap A K a = algebraMap A K d * (z : Module.Dual K Li) e := by
    rintro ⟨e, he⟩ z
    obtain ⟨w, hw, hz⟩ := z.2
    have hz' : eigProj D.ρΩ (σ.comp c.toRingHom) w = (z : Module.Dual K Li) := hz
    change algebraMap A K d * (z : Module.Dual K Li) e ∈ (algebraMap A K).range
    rw [← hz', hE e he.1 w]
    exact he.2 w hw
  choose F hF using hF0
  let eval : Wsub →ₗ[A] Module.Dual A (D.omHT (σ.comp c.toRingHom)) :=
    { toFun := fun e =>
        { toFun := F e
          map_add' := fun x y => hinj <| by
            rw [map_add, hF, hF, hF, Submodule.coe_add, LinearMap.add_apply, mul_add]
          map_smul' := fun a x => hinj <| by
            rw [RingHom.id_apply, smul_eq_mul, map_mul, hF, hF, Submodule.coe_smul,
              LinearMap.smul_apply, Algebra.smul_def, mul_left_comm] }
      map_add' := fun x y => by
        ext z
        apply hinj
        change algebraMap A K (F (x + y) z) = algebraMap A K (F x z + F y z)
        rw [map_add, hF, hF, hF, Submodule.coe_add, map_add, mul_add]
      map_smul' := fun a x => by
        ext z
        apply hinj
        change algebraMap A K (F (a • x) z) = algebraMap A K (a * F x z)
        rw [map_mul, hF, hF, Submodule.coe_smul, hsmul, map_smul, smul_eq_mul, mul_left_comm] }
  obtain ⟨G, hG⟩ := exists_extend_lin (K := K) Wsub
    (((Algebra.linearMap A K).compLeft (Fin N)) ∘ₗ i ∘ₗ eval)
  obtain ⟨⟨r, hr⟩, -⟩ := hex
  let Rr : (Fin N → K) →ₗ[K] Li := Fintype.linearCombination K fun k => vec (r (Pi.single k 1))
  have hRrS (y : Fin N → K) : Rr y ∈ _root_.GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ σ := by
    simp only [Rr, Fintype.linearCombination_apply]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hvecS _)
  have hRr (y : Fin N → A) (z : D.omHT (σ.comp c.toRingHom)) :
      algebraMap A K d * (z : Module.Dual K Li) (Rr (fun l => algebraMap A K (y l))) =
        algebraMap A K (r y z) := by
    have hy : y = ∑ k, y k • Pi.single k (1 : A) := by
      ext l
      simp [Finset.sum_apply, Pi.single_apply]
    conv_rhs => rw [hy]
    simp only [Rr, Fintype.linearCombination_apply, map_sum, LinearMap.sum_apply,
      map_smul, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum, map_mul]
    apply Finset.sum_congr rfl
    intro k _
    rw [mul_left_comm, hvec]
  refine ⟨G, Rr, fun e he => ?_, fun k => ?_, fun e he => ?_⟩
  · exact ⟨eval ⟨e, he⟩, hF _, fun l => congrFun (hG ⟨e, he⟩) l⟩
  · have h1 : Rr (Pi.single k 1) = vec (r (Pi.single k 1)) := by
      simp [Rr, Fintype.linearCombination_apply_single]
    rw [h1]
    exact hvW _
  · let f := eval ⟨e, he⟩
    obtain ⟨w', hw'⟩ := hr f
    have hGe : G e = fun l => algebraMap A K (i f l) := hG ⟨e, he⟩
    let q := (p : K) ^ m
    have hq : q ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
    let e' := q⁻¹ • (Rr (G e) - e)
    have he'S : e' ∈ _root_.GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ σ :=
      Submodule.smul_mem _ _ (Submodule.sub_mem _ (hRrS _) he.1)
    refine ⟨e', ⟨he'S, ?_⟩, ?_⟩
    · intro w hw
      obtain ⟨z, hz⟩ := hmem w hw
      have hzEval : algebraMap A K d * (z : Module.Dual K Li) (Rr (G e) - e) =
          q * algebraMap A K (w' z) := by
        have hf : algebraMap A K (f z) = algebraMap A K d * (z : Module.Dual K Li) e := hF _ _
        rw [map_sub, mul_sub, hGe, hRr, hw', LinearMap.add_apply, LinearMap.smul_apply,
          smul_eq_mul, map_add, map_mul, map_pow, map_natCast, ← hf, add_sub_cancel_left]
      refine ⟨w' z, ?_⟩
      rw [← hE e' he'S w, ← hz]
      change algebraMap A K (w' z) = algebraMap A K d * (z : Module.Dual K Li) (q⁻¹ • (Rr (G e) - e))
      rw [map_smul, smul_eq_mul, mul_left_comm, hzEval, inv_mul_cancel_left₀ hq]
    · change Rr (G e) = e + q • (q⁻¹ • (Rr (G e) - e))
      rw [smul_inv_smul₀ hq]
      abel

end GlobalTheory.CompanionTheory.Ar.Flat.HTL
end

section

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

theorem _root_.GlobalTheory.T.chart_ring_mem_after_monomial_scaling : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (s t : ∀ k, J k), mseg y s ≠ 0 → mseg y t ≠ 0 → ∀ a ∈ chartRing o (mseg y) s, ∃ n : ℕ, (mseg y s / mseg y t) ^ n * a ∈ chartRing o (mseg y) t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.ChartOverlap.pow_mul_mem_chartRing_mseg | exact GlobalTheory.CompanionTheory.Ar.HT.ChartOverlap.pow_mul_mem_chartRing_mseg | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.ChartOverlap.pow_mul_mem_chartRing_mseg <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

theorem _root_.GlobalTheory.T.intersection_family_symmetric : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ), IsIntersectionFamily I → ∀ (P : Ideal (MRing ι)) (e : ℕ) (L : Fin (e + 1) → HermLine ι) (i : Fin (e + 1)), IsArithVar P (e + 1) → (∀ j, IsSmoothHerm (L j)) → I P (e + 1) L = I P (e + 1) (Fin.snoc (fun j : Fin e => L (i.succAbove j)) (L i)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.movePositionToLast | exact GlobalTheory.CompanionTheory.Ar.Cmp.movePositionToLast | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.movePositionToLast <;> assumption)
end
