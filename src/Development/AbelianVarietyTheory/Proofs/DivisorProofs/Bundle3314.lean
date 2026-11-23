module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle076
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle077
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3304
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3275
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3160
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3273
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3303
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2230
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2508
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3299
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1488
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1124
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1204
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle208
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle066
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle207
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle209
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle202
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle204
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle205
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2939
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3302
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2639
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle201
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteRootsOfBimul
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle932
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2789
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3305
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle071
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle075

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

theorem _root_.GlobalTheory.T.two_trait_uniformisations_matching_data : ∀ {X : Scheme.{0}} {g n : ℕ} {B : Type} [CommRing B] {ζ : B} {sX : X ⟶ Sp B} (c : SiegPre g n ζ sX) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ (D₁ : DegData V (maximalIdeal V)) (A₁ : PolAV (Sp (FractionRing V))) (G₁ : Over (Sp V)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : Unif (maximalIdeal V) D₁ A₁ G₁) (D₂ : DegData V (maximalIdeal V)) (A₂ : PolAV (Sp (FractionRing V))) (G₂ : Over (Sp V)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : Unif (maximalIdeal V) D₂ A₂ G₂), IsSemiAbelian G₁ → IsSemiAbelian G₂ → ∀ (y : Sp (FractionRing V) ⟶ X) (α₁ : A₁.A.left ⟶ c.A.left) (α₂ : A₂.A.left ⟶ c.A.left), OverPt c A₁ y α₁ → OverPt c A₂ y α₂ → ∃ (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (φ : D₁.toPre.X ≃+ D₂.toPre.X), Match D₁.toPre D₂.toPre b φ (AlgebraicClosure (FractionRing V)) ∧ ∀ k : ℕ, 1 ≤ k → ∀ (p₁ : QkPt D₁.toPre (AlgebraicClosure (FractionRing V)) k) (p₂ : QkPt D₂.toPre (AlgebraicClosure (FractionRing V)) k) (x₁ : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ A₁.A) (x₂ : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ A₂.A), QkToAkU U₁.toUnifPre (AlgebraicClosure (FractionRing V)) k p₁ x₁ → QkToAkU U₂.toUnifPre (AlgebraicClosure (FractionRing V)) k p₂ x₂ → x₁.left ≫ α₁ = x₂.left ≫ α₂ → QImg b φ p₁ p₂ := by
  first | exact @GlobalTheory.TInj.two_unif_match | exact GlobalTheory.TInj.two_unif_match | (intros; apply GlobalTheory.TInj.two_unif_match <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

theorem _root_.GlobalTheory.T.tautological_coords_eq_of_matching_data : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (V : Type) [CommRing V] [IsDomain V] (ω : W →+* V) (D₁ D₂ : DegPre V) (s₁ : I → V) (e₁ : D₁.X ≃+ (Fin T.r → ℤ)) (β₁ : D₁.P.A.left ⟶ T.B.left) (ββ₁ : (G2 D₁.P.A).left ⟶ (G2 T.B).left) (w₁ : LB.Iso (abelian₂ D₁.P.A D₁.P.L) ((abelian₂ T.B T.M.L).pull ββ₁)) (s₂ : I → V) (e₂ : D₂.X ≃+ (Fin T.r → ℤ)) (β₂ : D₂.P.A.left ⟶ T.B.left) (ββ₂ : (G2 D₂.P.A).left ⟶ (G2 T.B).left) (w₂ : LB.Iso (abelian₂ D₂.P.A D₂.P.L) ((abelian₂ T.B T.M.L).pull ββ₂)) (b : D₁.P.A ⟶ D₂.P.A) (φ : D₁.X ≃+ D₂.X) (F : Type) [Field F] [Algebra (FractionRing V) F], 1 ≤ n → (∃ ε₀ : Module.Basis I ℤ (balForms (id : ℤ → ℤ) (Fin T.r → ℤ)), ∀ i, ε i = ε₀ i) → D₁.TauBimult → D₂.TauBimult → From T ω s₁ ε n D₁ e₁ β₁ ββ₁ w₁ → From T ω s₂ ε n D₂ e₂ β₂ ββ₂ w₂ → (∀ i, s₁ i ≠ 0) → (∀ i, s₂ i ≠ 0) → Match D₁ D₂ b φ F → (∀ y, e₂ (φ y) = e₁ y) → b.left ≫ β₂ = β₁ → (∀ a : Fin T.r → ℤ, ∃ (p₁ : QkPt D₁ F n) (p₂ : QkPt D₂ F n), p₁.y = e₁.symm a ∧ TautPt T ω s₁ ε n D₁ e₁ β₁ ββ₁ w₁ F a p₁.g ∧ p₂.y = e₂.symm a ∧ TautPt T ω s₂ ε n D₂ e₂ β₂ ββ₂ w₂ F a p₂.g ∧ QImg b φ p₁ p₂) → s₁ = s₂ := by
  first | exact @GlobalTheory.TInj.coords_eq_of_match | exact GlobalTheory.TInj.coords_eq_of_match | (intros; apply GlobalTheory.TInj.coords_eq_of_match <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

theorem _root_.GlobalTheory.T.tautological_point_torus_extension_add : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (ω : W →+* V) (s : I → V) (e : D.X ≃+ (Fin T.r → ℤ)) (β : D.P.A.left ⟶ T.B.left) (ββ : (G2 D.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ T.B T.M.L).pull ββ)), D.TauBimult → From T ω s ε n D e β ββ w → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (a a' : Fin T.r → ℤ) (g g' g'' : GtPtF D F), TautPt T ω s ε n D e β ββ w F a g → TautPt T ω s ε n D e β ββ w F a' g' → TautPt T ω s ε n D e β ββ w F (a + a') g'' → g.IsAdd g' g'' := by
  first | exact @GlobalTheory.TInj.tautPt_isAdd | exact GlobalTheory.TInj.tautPt_isAdd | (intros; apply GlobalTheory.TInj.tautPt_isAdd <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.lowerDatumObject_comes_from_base_of_linearPoints : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D' : Datum H) {l : Geo.Tor.Level H} (c : Coeff l) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (bV : c.F →+* V) (o' : LowObj D' c bV) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X] (x : X → (𝟙_ (Over (Sp V)) ⟶ o'.t.G)), (∀ y z, x (y + z) = x y * x z) → (∀ (a : 𝓞 E) y, x (a • y) = x y ≫ o'.t.act.act a) → ∃ (L : LowBase D' c) (θ₀ : L.W →+* V) (e : X ≃ₗ[𝓞 E] L.D.X) (m : ObjMap o' L.o (spMap θ₀)), IsLocalHom θ₀ ∧ θ₀.comp L.b = bV ∧ ∀ y, (x y).left ≫ m.toSABMap.φ ≫ L.φB = spMap θ₀ ≫ (L.D.c (e y)).left := by
  first | exact @GlobalTheory.UCanon.lowBase_of_linearPoints | exact GlobalTheory.UCanon.lowBase_of_linearPoints | (intros; apply GlobalTheory.UCanon.lowBase_of_linearPoints <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.UCanon.canon_hasRigidCoords : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C), HasRigidCoords C := by
  intro E _ _ _ H Dw l Xo c φ R _ _ _ hB C Cn
  obtain ⟨ε', τ₀, hε', hFB, hTau⟩ := GlobalTheory.T.canonicalFamily_periods_in_coordinates Xo c φ R hB C Cn
  refine ⟨Cn.N, fun k => Cn.ψ (MvPolynomial.X k), ε', τ₀, fun i => Cn.bd i, ?_, fun k => Cn.tor k, hTau, ?_⟩
  · intro i
    rw [hε', Cn.cone i]
  · intro K _ _ ev k₀ hk₀ hemb hsep
    obtain ⟨h1, h2, h3⟩ := hsep
    have hbase : ∀ a, ev ((Cn.ψ.comp MvPolynomial.C) a) ∈ k₀ :=
      GlobalTheory.T.canonicalFamily_base_value_mem_descended_point Cn.L C.P.D.toPre C.P.oD (Cn.ψ.comp MvPolynomial.C) (fun k => Cn.ψ (MvPolynomial.X k))
        (fun k => (Cn.ε k : LinearMap.BilinForm ℤ Cn.L.D.X)) Cn.e Cn.data K ev k₀ hk₀ h2
    have htor := h3 Cn.L.W (Cn.ψ.comp MvPolynomial.C) hFB hbase
    have hX : ∀ k, ev (Cn.ψ (MvPolynomial.X k)) ∈ k₀ := by
      rintro (i | i)
      · have := h1 i
        simp only at this
        rw [this]; exact k₀.zero_mem
      · exact htor i
    have hall : ∀ a : MvPolynomial (Fin C.m ⊕ Fin Cn.N) Cn.L.W, ev (Cn.ψ a) ∈ k₀ := by
      intro a
      induction a using MvPolynomial.induction_on with
      | C a => exact hbase a
      | add p q hp hq => rw [map_add (f := _), map_add (f := _)]; exact k₀.add_mem hp hq
      | mul_X p k hp => rw [map_mul, map_mul]; exact k₀.mul_mem hp (hX k)
    have hft : ((MvPolynomial.C : Cn.L.W →+* MvPolynomial (Fin C.m ⊕ Fin Cn.N) Cn.L.W).comp Cn.L.b).EssFiniteType := by
      refine RingHom.EssFiniteType.comp Cn.L.ft ?_
      exact (RingHom.FiniteType.essFiniteType (by
        rw [← MvPolynomial.algebraMap_eq]
        exact RingHom.finiteType_algebraMap.mpr inferInstance))
    exact GlobalTheory.T.closedPoint_of_values_in_small_algClosed c.F (MvPolynomial (Fin C.m ⊕ Fin Cn.N) Cn.L.W) R K (MvPolynomial.C.comp Cn.L.b) hft Cn.ψ Cn.compl
      ev k₀ hemb hall
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem exists_prime_natCast_ne_zero_of_field (K : Type) [Field K] : ∃ l : ℕ, l.Prime ∧ (l : K) ≠ 0 := by
  by_cases h2 : (2 : K) = 0
  · refine ⟨3, Nat.prime_three, ?_⟩
    intro h3
    have : (1 : K) = 0 := by
      have e : (1 : K) = (3 : ℕ) - (2 : K) := by push_cast; ring
      rw [e, h3, h2, sub_zero]
    exact one_ne_zero this
  · exact ⟨2, Nat.prime_two, by exact_mod_cast h2⟩

noncomputable def vendRing {K : Type} [Field K] (l : ℕ) [Fact l.Prime] (A : AbVar K) : End A →+* Module.End ℚ_[l] (Vl l A) :=
  (Module.End.baseChangeHom ℤ_[l] ℚ_[l] (Tl l A)).toRingHom.comp (tend l A)

theorem vendRing_apply {K : Type} [Field K] (l : ℕ) [Fact l.Prime] (A : AbVar K) (f : End A) :
    vendRing l A f = vmap l f.asHom := rfl

theorem exists_isCharpoly {K : Type} [Field K] (A : AbVar K) (f : End A) : ∃ P, IsCharpoly f P := by
  obtain ⟨P, hPm, hPd, hPe⟩ := GlobalTheory.T.exists_monic_rat_charPoly_abelianVariety K A f
  obtain ⟨l, hl, hlK⟩ := exists_prime_natCast_ne_zero_of_field K
  have : Fact l.Prime := ⟨hl⟩
  have : Module.Finite ℚ_[l] (Vl l A) := (tl_free_finrank K l hlK A).2.2.2.1
  have hcp := GlobalTheory.T.abelianVariety_degreePolynomial_map_eq_charpoly_rationalTate K l hlK A f P hPm hPd hPe
  have : Module.Finite ℤ (A ⟶ A) :=
    (GlobalTheory.T.hom_finite_free_finrank_le_four_mul_dim K A A).1
  have : Module.Finite ℤ (End A) :=
    Module.Finite.of_surjective (End.linearEquiv (R := ℤ) (X := A)).symm.toLinearMap
      (End.linearEquiv (R := ℤ) (X := A)).symm.surjective
  obtain ⟨Q, hQm, hQ⟩ := (Algebra.IsIntegral.isIntegral f : IsIntegral ℤ f)
  have hQV : Polynomial.aeval (vmap l f.asHom) Q = 0 := by
    have h := congrArg (vendRing l A) hQ
    rw [Polynomial.hom_eval₂, map_zero,
      Subsingleton.elim ((vendRing l A).comp (algebraMap ℤ (End A))) (algebraMap ℤ _)] at h
    rw [Polynomial.aeval_def, ← vendRing_apply]
    exact h
  obtain ⟨P₀, hP₀⟩ := GlobalTheory.T.integral_charpoly_of_monic_integral_annihilator ℚ_[l] (Vl l A) (vmap l f.asHom) P Q hQm hQV hcp
  have hinj : Function.Injective (algebraMap ℤ ℚ) := (algebraMap ℤ ℚ).injective_int
  refine ⟨P₀, ?_, ?_, ?_⟩
  · have h := hPm
    rw [← hP₀] at h
    rw [Polynomial.Monic, Polynomial.leadingCoeff_map_of_injective hinj] at h
    exact hinj (by simpa using h)
  · rw [← Polynomial.natDegree_map_eq_of_injective hinj, hP₀, hPd]
  · intro n
    have h := hPe n
    rw [← hP₀, Polynomial.eval_map, show (n : ℚ) = algebraMap ℤ ℚ n by simp,
      Polynomial.eval₂_hom] at h
    rw [eq_intCast] at h
    exact_mod_cast h

theorem isCharpoly_charpoly_unique (K : Type) [Field K] (A : AbVar K) (f : End A) :
    IsCharpoly f (charpoly f) ∧ ∀ P, IsCharpoly f P → P = charpoly f := by
  have hex := exists_isCharpoly A f
  have hc : IsCharpoly f (charpoly f) := by
    classical
    rw [charpoly, dite_eq_left hex]
    exact hex.choose_spec
  refine ⟨hc, fun P hP => Polynomial.funext fun n => ?_⟩
  rw [hP.2.2 n, hc.2.2 n]

theorem charpoly_spec : ∀ (K : Type) [Field K] (A : AbVar K) (f : End A),
    IsCharpoly f (charpoly f) ∧ ∀ P, IsCharpoly f P → P = charpoly f :=
  fun K _ A f => isCharpoly_charpoly_unique K A f

end GlobalTheory.AV.AbVar
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem end_isogeny_algebra_finrank_le : ∀ (K : Type) [Field K] (A : AbVar K),
    Module.Finite ℚ (End0 A) ∧ Module.finrank ℚ (End0 A) ≤ 4 * A.dim * A.dim := by
  intro K _ A
  obtain ⟨hfin, hfree, hrk⟩ := GlobalTheory.T.hom_finite_free_finrank_le_four_mul_dim K A A
  let e : End A ≃ₗ[ℤ] (A ⟶ A) := End.addEquiv.toIntLinearEquiv
  haveI : Module.Finite ℤ (A ⟶ A) := hfin
  haveI : Module.Free ℤ (A ⟶ A) := hfree
  haveI : Module.Finite ℤ (End A) := Module.Finite.equiv e.symm
  haveI : Module.Free ℤ (End A) := Module.Free.of_equiv e.symm
  refine ⟨inferInstance, ?_⟩
  rw [Module.finrank_baseChange]
  rw [e.finrank_eq]
  exact hrk

end GlobalTheory.AV.AbVar
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option autoImplicit false

namespace GlobalTheory.MassDegree

theorem chernInt_eq_topSelf : ∀ (Y : Var ℂ) (L : LB Y.X) (φ : Weight Y.str (RingHom.id ℂ) L), φ.IsCInf → Weight.chernInt φ Y.dim Set.univ (fun _ => 1) = (topSelfIntersection ℂ L Y.dim : ℝ) := by
  intro Y L φ hφ
  let ψ : Weight Y.str (RingHom.id ℂ) ((ProjSpace.O1 ℂ Y.N).pull Y.ι) :=
    ((ProjSpace.hermitianTwistingSheaf ℂ Y.N).φ (RingHom.id ℂ)).pull Y.ι Y.ι_str
  have hψ : ψ.IsCInf := ((ProjSpace.hermitianTwistingSheaf ℂ Y.N).cInf (RingHom.id ℂ)).pull Y.ι Y.ι_str
  obtain ⟨P, hP0, hP⟩ := GlobalTheory.T.exists_polynomial_chernIntegral_tens_pow Y L _ φ ψ hφ hψ
  obtain ⟨Q, hQ0, hQ⟩ := GlobalTheory.SelfInterPoly.exists_polynomial_topSelf Y L _ φ.isLB ψ.isLB
  obtain ⟨m₀, hm₀⟩ := GlobalTheory.T.twist_ample_globally_generated Y L φ.isLB
  have key : ∀ m : ℕ, m₀ ≤ m → P.eval (m : ℝ) = Q.eval (m : ℝ) := by
    intro m hm
    obtain ⟨n, u, hu⟩ := hm₀ m hm
    rw [← hP m, ← hQ m]
    exact GlobalTheory.T.chernMass_eq_selfIntersection_of_generated Y _ (φ.tens (ψ.pow m)) (hφ.tens (hψ.zpow m)) n u hu
  have hPQ : P = Q := by
    refine Polynomial.eq_of_infinite_eval_eq P Q ?_
    refine Set.Infinite.mono ?_ ((Set.Ici_infinite m₀).image Nat.cast_injective.injOn)
    rintro _ ⟨m, hm, rfl⟩
    exact key m hm
  rw [← hP0, ← hQ0, hPQ]

end GlobalTheory.MassDegree
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory.UPoinc.ShortBound

theorem exists_not_dvd_le {X : Type} [AddCommGroup X] (β : LinearMap.BilinForm ℤ X)
    (hβ : ∀ y, y ≠ 0 → 0 < β y y) (m : ℕ) (hm : 2 ≤ m) :
    ∀ (k : ℕ) (x : X), (β x x).toNat = k → x ≠ 0 →
      ∃ x', x' ≠ 0 ∧ (¬ ∃ v, x' = m • v) ∧ β x' x' ≤ β x x := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro x hk hx
    by_cases hd : ∃ v, x = m • v
    · obtain ⟨v, rfl⟩ := hd
      have hv : v ≠ 0 := by rintro rfl; simp at hx
      have hvv := hβ v hv
      have e : β (m • v) (m • v) = (m : ℤ) * ((m : ℤ) * β v v) := by
        simp [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
      have hm' : (2 : ℤ) ≤ m := by exact_mod_cast hm
      have h2 : 2 * β v v ≤ (m : ℤ) * β v v := mul_le_mul_of_nonneg_right hm' hvv.le
      have h3 : 2 * ((m : ℤ) * β v v) ≤ (m : ℤ) * ((m : ℤ) * β v v) :=
        mul_le_mul_of_nonneg_right hm' (by linarith)
      have hlt : β v v < β (m • v) (m • v) := by rw [e]; linarith
      obtain ⟨x', h1, h2, h3⟩ := ih (β v v).toNat (by omega) v rfl hv
      exact ⟨x', h1, h2, h3.trans hlt.le⟩
    · exact ⟨x, hx, hd, le_rfl⟩

theorem exists_shortest {X : Type} [AddCommGroup X] (q : QuadraticMap ℤ X ℝ)
    (hq : Filter.Tendsto q Filter.cofinite Filter.atTop) (N : ℕ) (a : X) :
    ∃ v : X, ∀ v0, q (a + N • v) ≤ q (a + N • v + N • v0) := by
  have hfin : {x | ¬ q a < q x}.Finite := Filter.eventually_cofinite.1 (hq.eventually_gt_atTop (q a))
  obtain ⟨b, ⟨hb, v, rfl⟩, hmin⟩ := Set.exists_min_image ({x | ¬ q a < q x} ∩ Set.range fun v => a + N • v) q
    (hfin.inter_of_left _) ⟨a, lt_irrefl _, 0, by simp⟩
  refine ⟨v, fun v0 => ?_⟩
  by_cases h : q a < q (a + N • v + N • v0)
  · exact (not_lt.1 hb).trans h.le
  · exact hmin _ ⟨h, v + v0, by simp [add_assoc]⟩

theorem pos_of_tendsto {X : Type} [AddCommGroup X] [Module.Free ℤ X] (q : QuadraticMap ℤ X ℝ)
    (hq : Filter.Tendsto q Filter.cofinite Filter.atTop) (a : X) (ha : a ≠ 0) : 0 < q a := by
  by_contra h
  have h : q a ≤ 0 := not_lt.1 h
  have hfin : {x | ¬ (0 : ℝ) < q x}.Finite := Filter.eventually_cofinite.1 (hq.eventually_gt_atTop 0)
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℤ => n • a) (smul_left_injective ℤ ha) (fun n => ?_) hfin
  simp only [Set.mem_setOf_eq, not_lt, QuadraticMap.map_smul, zsmul_eq_mul]
  push_cast
  exact mul_nonpos_of_nonneg_of_nonpos (mul_self_nonneg _) h

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem be_pos (T : UTrait Xo c) (x : T.P.D.toPre.X) (hx : x ≠ 0) : 0 < T.be x x := by
  obtain ⟨j, hj⟩ := IsMonomial.exists_pos (IsLocalRing.maximalIdeal.isMaximal T.V).ne_top T.mono hx
  fin_cases j
  simpa using hj

theorem sc_pos {C : UCompact Xo c} {X₁ : USetup C} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z} (t : UCTrait X₁ p z₁) :
    0 < t.sc := by
  have hϖ0 : algebraMap t.T.V (FractionRing t.T.V) t.T.ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 t.T.irr.ne_zero
  have h0 : t.ι (algebraMap t.T.V (FractionRing t.T.V) t.T.ϖ) ≠ 0 := (map_ne_zero _).2 hϖ0
  have hlt : ‖t.ι (algebraMap t.T.V (FractionRing t.T.V) t.T.ϖ)‖ < 1 := by
    by_contra hge
    have hinv : ‖t.ι (algebraMap t.T.V (FractionRing t.T.V) t.T.ϖ)⁻¹‖ ≤ 1 := by
      rw [map_inv₀, norm_inv]
      exact inv_le_one_of_one_le₀ (not_lt.1 hge)
    obtain ⟨w, hw⟩ := (t.int _).1 hinv
    apply t.T.irr.not_isUnit
    refine isUnit_iff_exists_inv.2 ⟨w, IsFractionRing.injective t.T.V (FractionRing t.T.V) ?_⟩
    rw [map_mul, hw, map_one, mul_inv_cancel₀ hϖ0]
  unfold UCTrait.sc
  have := Real.log_neg (norm_pos_iff.2 h0) hlt
  linarith

theorem one_le_of_ne_zero (T : UTrait Xo c) {x : T.P.D.toPre.X} (hx : x ≠ 0) : 1 ≤ Dw.p + Dw.q := by
  haveI : Module.Projective (𝓞 E) T.P.D.toPre.X := GlobalTheory.Forms.projective_of_int (𝓞 E) _
  haveI : Module.Finite (𝓞 E) T.P.D.toPre.X := Module.Finite.of_restrictScalars_finite ℤ _ _
  haveI : Nontrivial T.P.D.toPre.X := ⟨x, 0, hx⟩
  have h1 : 0 < Module.finrank (𝓞 E) T.P.D.toPre.X := Module.finrank_pos
  have h2 := UTrait.finrank_le_min E H Dw l Xo c T
  omega

theorem exists_mem_maximalIdeal {C : UCompact Xo c} (X₁ : USetup C) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z)
    (hz : IsClosed ({z₁} : Set X₁.M.Z)) (t : UCTrait X₁ p z₁) (x : t.T.P.D.toPre.X) (hx : x ≠ 0) :
    ∃ h ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁),
      Real.exp (-(1 / (2 * X₁.S.N) * (t.sc * t.T.be x x))) ≤ ‖t.val h‖ := by
  obtain ⟨hL, hL2⟩ := GlobalTheory.abelianSchemeLaws_all
  obtain ⟨hU, hUT⟩ := GlobalTheory.ZH.thmU_and_uTors
  obtain ⟨x', hx', hnd, hle⟩ :=
    exists_not_dvd_le t.T.be (be_pos t.T) X₁.S.N X₁.S.N_ge _ x rfl hx
  obtain ⟨wi⟩ := nonempty_uWit X₁
  obtain ⟨yy, hyy⟩ := GlobalTheory.T.exists_labels_unitaryClassicalTrait E H Dw (one_le_of_ne_zero t.T hx) l Xo c C X₁ wi p z₁ t
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', u', -, -, -, hR, G, _, α, β, -, -, -, y₀, hat, u, lb, j, hq, -⟩ :=
    hyy.uIsLab
  let S' := X₁.S.rechart c₀ hc R' fg frac hth hev
  have hdiv' : X₁.M.HasDiv S'.th := fun z => (X₁.hasDiv z).imp fun k hk => (RatModel.div_mul_iff hc).2 hk
  have htests : S'.HasTests :=
    (hasTests_of_real GlobalTheory.SS.semistableReductionSt hU hL hL2 hUT X₁.o₁ X₁.Ω₁ S' ρ').1
  have hy : ∀ a : X₁.o₁, ‖y₀ (algebraMap X₁.o₁ S'.R a)‖ ≤ 1 := fun a => by
    rw [hat]
    exact RatModel.norm_val_le_one t.cen ((X₁.M.O z₁).algebraMap_mem a)
  obtain ⟨τ, e, hτ, -⟩ := exists_test_match X₁.o₁ X₁.Ω₁ S' ρ' p y₀ u lb
    (GlobalTheory.T.thetaConstant_bounded_by_shortestVector hL hL2 hUT _ _ S' ρ' p y₀ u lb hy) (GlobalTheory.T.unitThetaConstants_generate_integralTorsion hL hL2 hUT _ _ S' ρ' p y₀ u lb hy)
    (GlobalTheory.T.weightSpace_values_integralTorsion_bound_shortestVector hL hL2 hUT _ _ S' ρ' p y₀ u lb hy) (GlobalTheory.T.exists_norm_torsionSum_shortestVector_eq hL hL2 hUT _ _ S' ρ' p y₀ u lb hy)
    (GlobalTheory.T.exists_weightZeroSection_unit_integralTorsionPoint hL hL2 hUT _ _ S' ρ' p y₀ u lb hy)
  let α₀ : τ.X := e.symm (j.symm x')
  obtain ⟨v, hv⟩ := exists_shortest τ.q τ.pos X₁.S.N α₀
  have hne : α₀ + X₁.S.N • v ≠ 0 := fun h0 => hnd ⟨-(j (e v)), by
    have h1 := congrArg (fun s => j (e s)) h0
    simp only [α₀, map_add (f := _), map_nsmul, AddEquiv.apply_symm_apply, map_zero] at h1
    rw [smul_neg]
    exact eq_neg_of_add_eq_zero_left h1⟩
  have hqle : τ.q (α₀ + X₁.S.N • v) ≤ t.sc * t.T.be x' x' / 2 := by
    have h1 := hv (-v)
    rw [smul_neg, add_neg_cancel_right] at h1
    refine h1.trans_eq ?_
    rw [hτ, hq]
    simp only [α₀, AddEquiv.apply_symm_apply]
  obtain ⟨h, hm, hh⟩ := GlobalTheory.exists_mem_maximalIdeal_exp_le_norm_val X₁.o₁ X₁.Ω₁ S' X₁.M X₁.normal hdiv' htests z₁ hz p
    t.y y₀ t.cen (fun a ha => hR ha) hat τ _ hv (pos_of_tendsto τ.q τ.pos _ hne)
  refine ⟨h, hm, le_trans (Real.exp_le_exp.2 ?_) hh⟩
  have hsc := sc_pos t
  have hNpos : (0 : ℝ) < X₁.S.N := by
    have := X₁.S.N_ge
    exact_mod_cast (by omega : 0 < X₁.S.N)
  have hb : (t.T.be x' x' : ℝ) ≤ t.T.be x x := by exact_mod_cast hle
  have h1 : τ.q (α₀ + X₁.S.N • v) ≤ t.sc * t.T.be x x / 2 :=
    hqle.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb hsc.le) zero_le_two)
  rw [neg_le_neg_iff]
  refine (div_le_div_of_nonneg_right h1 hNpos.le).trans_eq ?_
  field_simp

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X' : USetup C) (p : ℕ) [Fact p.Prime], ∃ K : ℝ, ∀ (z' : X'.M.Z), IsClosed ({z'} : Set X'.M.Z) → ∀ t : UCTrait X' p z', X'.S.R ≤ X'.M.O ((gPt p ≫ t.y) (IsLocalRing.closedPoint (PadicAlgCl p))) → ∀ x : t.T.P.D.toPre.X, x ≠ 0 → ∃ h ∈ maximalIdeal (X'.M.Z.presheaf.stalk z'), Real.exp (-(K * (t.sc * t.T.be x x))) ≤ ‖t.val h‖ := by
  intro E _ _ _ H Dw l Xo c C X' p _
  exact ⟨1 / (2 * X'.S.N), fun z' hz t _ x hx => exists_mem_maximalIdeal X' p z' hz t x hx⟩

end GlobalTheory.UPoinc.ShortBound
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtsHoriz

theorem transl_horizontal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r)))  → ∀ (B' : Over (Sp (DualNumber k))) (_ : GrpObj B') (π₁ π₂ : B'.left ⟶ P.D.toPre.P.A.left), IsGrpPullback B' P.D.toPre.P.A (spMap ρ) π₁ → IsGrpPullback B' P.D.toPre.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → ∀ (y : P.D.toPre.X) (x : Sp (DualNumber k) ⟶ B'.left), x ≫ B'.hom = 𝟙 _ → x ≫ π₁ = spMap ρ ≫ (P.D.toPre.c y).left → x ≫ π₂ = spMap (constHom ρ) ≫ (P.D.toPre.c y).left := by
  intro E _ _ _ H k _ _ m d t P gam hmon hli hab
  letI := H.starRing
  intro Y n' v' dd hdd D q hq h hbas hdef hΘ ρ hρ B' _ π₁ π₂ h₁ h₂ hcl y x hx hx₁
  obtain ⟨_, hA₀, -, -⟩ := GlobalTheory.AbCoh.exists_grpObj_isGrpPullback_of_isPullback _ _
    ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ) P.D.toPre.P.A _ _ _
    (IsPullback.of_hasPullback P.D.toPre.P.A.hom (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)))
  obtain ⟨dl, hdl, hcomm⟩ := GlobalTheory.HeatTranslW.lift_commutes_translation E H k m d t P gam hmon hli hab Y n' v' dd hdd D q hq h hbas hdef hΘ ρ hρ _ _ _ hA₀
  have hw : (pullback.fst P.D.toPre.P.A.hom (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)) ≫
      (lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A]).left) ≫ P.D.toPre.P.A.hom =
      pullback.snd _ _ ≫ spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ) := by
    rw [Category.assoc, Over.w, pullback.condition]
  let T₀ := pullback.lift _ _ hw
  exact GlobalTheory.TranslHoriz.isHoriz_of_comm k _ P.D.toPre.P.A P.D.toPre.P.isAb ρ B' _ π₁ π₂ h₁ h₂ hcl _ _ _ hA₀ dl hdl (P.D.toPre.c y) T₀
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) (hcomm y T₀ (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)) x hx hx₁

end GlobalTheory.PtsHoriz
end
