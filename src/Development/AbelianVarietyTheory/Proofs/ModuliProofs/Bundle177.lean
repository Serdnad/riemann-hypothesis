module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle003
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle173
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle016
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle023
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle008
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPeriodsEighthPowerEvenUnimodularBundle
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle108
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle160
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle166
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle102
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle174
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHomogeneousPolynomialVolumePullbackCombina
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle175
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IterateEqIdOfTrivialOnFixedFibre
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

private theorem exists_monoidHom_aut_of_lies {𝒞 : Type*} [Category 𝒞] {U X : 𝒞} (j : U ⟶ X)
    {Γ : Type} [Group Γ] (ρ₀ : Γ →* Aut U) (r : Γ → (X ⟶ X)) (hr : ∀ g, j ≫ r g = (ρ₀ g).asIso.hom ≫ j)
    (lies : Γ → (X ⟶ X) → Prop) (h1 : lies 1 (𝟙 X)) (hrl : ∀ g, lies g (r g))
    (hml : ∀ g h, lies (g * h) (r h ≫ r g))
    (hj : ∀ g a b, lies g a → lies g b → j ≫ a = j ≫ b → a = b) :
    ∃ ρ : Γ →* Aut X, ∀ g, (ρ g).asIso.hom = r g := by
  have hone : r 1 = 𝟙 X := by
    refine hj 1 _ _ (hrl 1) h1 ?_
    rw [hr 1, map_one, Category.comp_id]
    exact Category.id_comp j
  have hmul : ∀ g h, r (g * h) = r h ≫ r g := by
    intro g h
    refine hj (g * h) _ _ (hrl _) (hml g h) ?_
    have hm : ∀ a b : Aut U, (a * b).asIso.hom = b.asIso.hom ≫ a.asIso.hom := fun _ _ => rfl
    rw [hr (g * h), map_mul, hm, Category.assoc, reassoc_of% (hr h), hr g]
  have hinv : ∀ g, r g ≫ r g⁻¹ = 𝟙 X ∧ r g⁻¹ ≫ r g = 𝟙 X := fun g =>
    ⟨by rw [← hmul, inv_mul_cancel, hone], by rw [← hmul, mul_inv_cancel, hone]⟩
  exact ⟨{ toFun := fun g => Aut.of ⟨r g, r g⁻¹, (hinv g).1, (hinv g).2⟩
           map_one' := Aut.ext (Iso.ext hone)
           map_mul' := fun g h => Aut.ext (Iso.ext (hmul g h)) }, fun g => rfl⟩

theorem exists_action_of_extends {U X : Scheme.{0}} (j : U ⟶ X) (hj : ∀ a b : X ⟶ X, j ≫ a = j ≫ b → a = b)
    {Γ : Type} [Group Γ] (ρ₀ : Γ →* Aut U) (r : Γ → (X ⟶ X)) (hr : ∀ g, j ≫ r g = (ρ₀ g).asIso.hom ≫ j) :
    ∃ ρ : Γ →* Aut X, ∀ g, (ρ g).asIso.hom = r g :=
  exists_monoidHom_aut_of_lies j ρ₀ r hr (fun _ _ => True) trivial (fun _ => trivial) (fun _ _ => trivial)
    (fun _ a b _ _ h => hj a b h)

theorem exists_action_model_of_ext {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {U : Scheme.{0}}
    {F O : Type} [Field F] [CommRing O] {c : U ⟶ Sp F} {t : SAB H U} {β : O →+* F} (C : Cpt c t β) {Z : Scheme.{0}}
    (q : C.X ⟶ Z) {Γ : Type} [Group Γ] (ρ₀ : Γ →* Aut U) (τ₀ : Γ →* Aut t.G.left)
    (ν : ∀ g, SABMap t t (ρ₀ g).asIso.hom) (hβ : IsDedFrac β) (hq : IsIntegralHom q) (hν : ∀ g, (ν g).φ = (τ₀ g).asIso.hom)
    (hZ : ∀ g, ∃ ρZ : Z ⟶ Z, C.j ≫ q ≫ ρZ = (ρ₀ g).asIso.hom ≫ C.j ≫ q)
    (hext : ∀ (r : U ⟶ U) (n : SABMap t t r) (f : C.X ⟶ C.X), C.j ≫ f = r ≫ C.j →
      ∃ mu : SABMap C.t C.t f, C.m.φ ≫ mu.φ = n.φ ≫ C.m.φ) :
    ∃ (ρ : Γ →* Aut C.X) (τ : Γ →* Aut C.t.G.left) (mu : ∀ g, SABMap C.t C.t (ρ g).asIso.hom),
      ∀ g, (mu g).φ = (τ g).asIso.hom ∧ C.j ≫ (ρ g).asIso.hom = (ρ₀ g).asIso.hom ≫ C.j ∧
        C.m.φ ≫ (τ g).asIso.hom = (τ₀ g).asIso.hom ≫ C.m.φ := by
  obtain ⟨⟨_, _⟩, _, hfr⟩ := hβ
  let _ : Algebra O F := β.toAlgebra
  have : IsFractionRing O F := hfr
  obtain ⟨hnoeth, _, hsep, hpre, hflat, hdom, hqc⟩ :=
    genericPart_dense_proOpen O F C.X U C.s C.jQ C.flat C.proj C.jQ_open C.jQ_dense
  have := hnoeth
  have := hsep
  have : QuasiCompact C.j := hqc
  have : IsReduced C.X := by
    have : ∀ x : C.X, _root_.IsReduced (C.X.presheaf.stalk x) := fun x => by
      have := (C.normal x).1
      infer_instance
    exact isReduced_of_isReduced_stalk _
  obtain ⟨-, -, hsd, -⟩ := densePart_basic C.X U C.j hpre hflat hdom hqc
  have : IsSchemeTheoreticallyDominant C.j := hsd ‹_›
  have hj1 : ∀ a b : C.X ⟶ C.X, C.j ≫ a = C.j ≫ b → a = b := fun a b h =>
    ExtUnique.hom_ext_of_dominant (terminal.from C.X) (terminal.hom_ext _ _) C.j h
  have hlift : ∀ g, ∃ a : C.X ⟶ C.X, C.j ≫ a = (ρ₀ g).asIso.hom ≫ C.j := by
    intro g
    obtain ⟨ρZ, hρZ⟩ := hZ g
    obtain ⟨a, ⟨ha, -⟩, -⟩ := existsUnique_lift_of_densePart C.X U Z C.X C.j C.normal hpre hflat hdom hqc
      q (q ≫ ρZ) ((ρ₀ g).asIso.hom ≫ C.j) hq (by rw [Category.assoc, hρZ])
    exact ⟨a, ha⟩
  choose r hr using hlift
  obtain ⟨ρ, hρ⟩ := exists_action_of_extends C.j hj1 ρ₀ r hr
  have hjρ : ∀ g, C.j ≫ (ρ g).asIso.hom = (ρ₀ g).asIso.hom ≫ C.j := fun g => by rw [hρ]; exact hr g
  have hmu : ∀ g, ∃ mu : SABMap C.t C.t (ρ g).asIso.hom, C.m.φ ≫ mu.φ = (ν g).φ ≫ C.m.φ :=
    fun g => hext _ (ν g) _ (hjρ g)
  choose mu hmu using hmu
  obtain ⟨hGf, hGs⟩ := ExtUnique.flat_and_isSeparated_of_isSemiAbelian C.t.G C.t.semi
  have := hGf
  have := hGs
  have hcan : ∀ (e : C.X ≅ C.X) (a b : C.t.G.left ⟶ C.t.G.left), a ≫ C.t.G.hom = C.t.G.hom ≫ e.hom →
      b ≫ C.t.G.hom = C.t.G.hom ≫ e.hom → C.m.φ ≫ a = C.m.φ ≫ b → a = b := by
    intro e a b ha hb hab
    have : IsSeparated (Over.mk (C.t.G.hom ≫ e.inv)).hom := by
      show IsSeparated (C.t.G.hom ≫ e.inv)
      infer_instance
    have key := ExtUnique.over_hom_ext_of_isPullback (j := C.j) (X := C.t.G)
      (Y := Over.mk (C.t.G.hom ≫ e.inv)) C.m.cart.1
      (f := Over.homMk a (by simp [reassoc_of% ha])) (g := Over.homMk b (by simp [reassoc_of% hb])) hab
    exact congrArg (fun k => k.left) key
  have hw : ∀ g, (mu g).φ ≫ C.t.G.hom = C.t.G.hom ≫ (ρ g).asIso.hom := fun g => (mu g).cart.1.w
  obtain ⟨τ, hτ⟩ := exists_monoidHom_aut_of_lies C.m.φ τ₀ (fun g => (mu g).φ)
    (fun g => by rw [hmu, hν]) (fun g a => a ≫ C.t.G.hom = C.t.G.hom ≫ (ρ g).asIso.hom)
    (by rw [map_one]; exact (Category.id_comp _).trans (Category.comp_id _).symm) hw
    (fun g h => by
      show ((mu h).φ ≫ (mu g).φ) ≫ C.t.G.hom = C.t.G.hom ≫ (ρ (g * h)).asIso.hom
      have hm : ∀ a b : Aut C.X, (a * b).asIso.hom = b.asIso.hom ≫ a.asIso.hom := fun _ _ => rfl
      rw [map_mul, hm, Category.assoc, hw g, reassoc_of% (hw h)])
    (fun g a b ha hb hab => hcan (ρ g).asIso a b ha hb hab)
  refine ⟨ρ, τ, mu, fun g => ⟨(hτ g).symm, hjρ g, ?_⟩⟩
  rw [hτ]
  exact (hmu g).trans (by rw [hν])

theorem exists_action_model : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (C : Cpt c t β) (Z : Scheme.{0}) (q : C.X ⟶ Z) (Γ : Type) [Group Γ] [Finite Γ] (ρ₀ : Γ →* Aut U) (τ₀ : Γ →* Aut t.G.left) (ν : ∀ g, SABMap t t (ρ₀ g).asIso.hom), IsDedFrac β → Algebra.FiniteType ℤ O → IsProper t.G.hom → IsIntegralHom q → (∀ g, (ν g).φ = (τ₀ g).asIso.hom) → (∀ g, ∃ ρZ : Z ⟶ Z, C.j ≫ q ≫ ρZ = (ρ₀ g).asIso.hom ≫ C.j ≫ q) → ∃ (ρ : Γ →* Aut C.X) (τ : Γ →* Aut C.t.G.left) (mu : ∀ g, SABMap C.t C.t (ρ g).asIso.hom), ∀ g, (mu g).φ = (τ g).asIso.hom ∧ C.j ≫ (ρ g).asIso.hom = (ρ₀ g).asIso.hom ≫ C.j ∧ C.m.φ ≫ (τ g).asIso.hom = (τ₀ g).asIso.hom ≫ C.m.φ := by
  intro hN E _ _ _ H U F O _ _ c t β C Z q Γ _ _ ρ₀ τ₀ ν hβ hfin hprop hq hν hZ
  exact exists_action_model_of_ext C q ρ₀ τ₀ ν hβ hq hν hZ
    (fun r n f h => Models.exists_sabMap_extending hN E H U F O c t β U F O c t β C C r n f hβ hfin hprop h)

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

theorem _root_.GlobalTheory.T.exists_semiAbelianTripleMap_extending_modelMap : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (U' : Scheme.{0}) (F' O' : Type) [Field F'] [CommRing O'] (c' : U' ⟶ Sp F') (t' : SAB H U') (β' : O' →+* F') (C : Cpt c t β) (C' : Cpt c' t' β') (r : U' ⟶ U) (ν : SABMap t' t r) (f : C'.X ⟶ C.X), IsDedFrac β' → Algebra.FiniteType ℤ O' → IsProper t'.G.hom → C'.j ≫ f = r ≫ C.j → ∃ mu : SABMap C'.t C.t f, C'.m.φ ≫ mu.φ = ν.φ ≫ C.m.φ := by
  first | exact @GlobalTheory.Models.exists_sabMap_extending | exact GlobalTheory.Models.exists_sabMap_extending | (intros; apply GlobalTheory.Models.exists_sabMap_extending <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.exists_periods_eighthPower_evenUnimodularBundle : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (em : o →+* ℂ) (w w' : J) (h : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (σ : Fin 8 × Fin h ≃ Fin g) (EF : LinearMap.BilinForm ℤ (Fin 8 → (Fin h ⊕ Fin h → ℤ))), IsE8 W → IsSharpBasis W bas → (W + W.transpose) * a w = W → (W + W.transpose) * a w' = W.transpose → (∀ x y, EF x y = ∑ u, ∑ v, (W + W.transpose) u v * omegaStd (x u) (y v)) → ∀ t : TObj g k J b (spMap em), SharpClass W a bas em t → ∃ (τ : Matrix (Fin h) (Fin h) ℂ) (m : (Fin h ⊕ Fin h → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (Q : (Fin 8 → (Fin h ⊕ Fin h → ℤ)) →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), ((τ).IsSymm ∧ ((τ).map Complex.im).PosDef) ∧ (∀ x y, Complex.exp (-(2 * Real.pi * Complex.I) * (omegaStd (m x) (m y) : ℂ) / k) = em (b.ζ : o) ^ omegaStd x y) ∧ (∀ x u i, Q x (σ (u, i)) = (τ).mulVec (fun i' => (x u (.inl i') : ℂ)) i + (x u (.inr i) : ℂ)) ∧ (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = EF x y) ∧ (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH Hm χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ (Q).range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = Q x → χ' l = (-1) ^ EF x ((fun j (x : (Fin 8 → (Fin h ⊕ Fin h → ℤ))) u => ∑ v, a j u v • x v) w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((k : ℕ) : ℂ)⁻¹ • Q ((fun i u => m (bas (Pi.single i 1) u)) i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q ((fun j (x : (Fin 8 → (Fin h ⊕ Fin h → ℤ))) u => ∑ v, a j u v • x v) j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) := by
  first | exact @GlobalTheory.exists_periods_of_sharpClass | exact GlobalTheory.exists_periods_of_sharpClass | (intros; apply GlobalTheory.exists_periods_of_sharpClass <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

namespace GlobalTheory.SymAmpleCount

theorem eq_of_scaling {h : ℕ → ℕ} {g q : ℕ} {v : ℝ} (hq : 2 ≤ q)
    (hs : ∀ e, 1 ≤ e → h (e * q) = q ^ g * h e)
    (ht : Filter.Tendsto (fun e : ℕ => (h e : ℝ) / (e : ℝ) ^ g) Filter.atTop (nhds v)) {e : ℕ} (he : 1 ≤ e) :
    (h e : ℝ) = v * (e : ℝ) ^ g := by
  have h₁ : ∀ i, h (e * q ^ i) = (q ^ i) ^ g * h e := fun i => by
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ, ← Nat.mul_assoc, hs _ (Nat.mul_pos he (by positivity)), ih, mul_pow]
      ring
  have h₂ : Filter.Tendsto (fun i : ℕ => e * q ^ i) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun i => Nat.le_mul_of_pos_left _ he) (tendsto_pow_atTop_atTop_of_one_lt hq)
  have he' : (e : ℝ) ^ g ≠ 0 := by positivity
  have h₃ : ((fun e : ℕ => (h e : ℝ) / (e : ℝ) ^ g) ∘ fun i : ℕ => e * q ^ i) =
      fun _ => (h e : ℝ) / (e : ℝ) ^ g := by
    funext i
    have : ((q : ℝ) ^ i) ^ g ≠ 0 := by positivity
    simp only [Function.comp, h₁]
    push_cast
    rw [mul_pow]
    field_simp
  have h₄ := ht.comp h₂
  rw [h₃] at h₄
  rw [← tendsto_nhds_unique tendsto_const_nhds h₄]
  field_simp

theorem exists_two_le_cast_ne_zero (K : Type) [Field K] : ∃ l : ℕ, 2 ≤ l ∧ (l : K) ≠ 0 := by
  by_cases h : ((2 : ℕ) : K) = 0
  · refine ⟨3, by norm_num, ?_⟩
    rw [show (3 : ℕ) = 2 + 1 from rfl, Nat.cast_add, h]
    simp
  · exact ⟨2, le_rfl, h⟩

theorem isIso_translation {S : Scheme.{0}} (A : Over S) [GrpObj A] (x : 𝟙_ (Over S) ⟶ A) :
    IsIso ((toUnit A ≫ x) * 𝟙 A) := by
  refine ⟨(toUnit A ≫ x)⁻¹ * 𝟙 A, ?_, ?_⟩
  · rw [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, comp_toUnit, Category.comp_id, inv_mul_cancel_left]
  · rw [MonObj.comp_mul, ← Category.assoc, comp_toUnit, Category.comp_id, mul_inv_cancel_left]

theorem sectionsDim_symmetricAmple_pow_sq (hL : Out.Laws) (hL' : Out.Laws2) (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K))
    (M : LB P.A.left) (hM : M.IsLB) (ha : Out.RelAmple P.A M) (hs : SymB M) {k : ℕ} (hk : (k : K) ≠ 0) {r : ℕ}
    (hr : SectionsHaveFiniteDimension P.A.hom M r) : SectionsHaveFiniteDimension P.A.hom (lbPow M (k ^ 2)) (k ^ (2 * P.g) * r) := by
  refine ((GlobalTheory.T.sectionsHaveFiniteDimension_invariance_isomorphisms K _ P.A.hom _ (LB.isLB_pull hM _)).2.1 _ (GlobalTheory.isLB_lbPow hM _)
    (GlobalTheory.T.mulA_pullback_iso_pow_sq_symmetric_abelianVariety K P M k hM hs)).1 _ (GlobalTheory.T.sectionsHaveFiniteDimension_lbDiv_linComb hL hL' K P M k r hM hk fun y _ => ?_)
  obtain ⟨x, hx⟩ := GlobalTheory.T.twist_ampleBundle_translationBundle_iso_translate hL hL' K P M y hM ha
  refine ((GlobalTheory.T.sectionsHaveFiniteDimension_invariance_isomorphisms K _ P.A.hom _ (LB.isLB_pull hM _)).2.1 _
    (LB.isLB_div hM (LB.isLB_linComb P.isLB _ _)) hx.symm).1 _ ?_
  have := isIso_translation P.A x
  have H := ((GlobalTheory.T.sectionsHaveFiniteDimension_invariance_isomorphisms K _ P.A.hom M hM).2.2.2.2.2 _
    ((Over.forget _).mapIso (asIso ((toUnit P.A ≫ x) * 𝟙 P.A))) r).1 hr
  have e : ((Over.forget _).mapIso (asIso ((toUnit P.A ≫ x) * 𝟙 P.A))).hom ≫ P.A.hom = P.A.hom := Over.w _
  exact (congrArg (fun q => SectionsHaveFiniteDimension q _ r) e).mp H

end GlobalTheory.SymAmpleCount

namespace GlobalTheory

theorem sectionsDim_symmetricAmple_pow_eq_mul_pow : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M : LB P.A.left), M.IsLB → Out.RelAmple P.A M → SymB M → ∃ δ : ℕ, 1 ≤ δ ∧ Vol P.A.hom M P.g δ ∧ ∀ e ≥ 1, SectionsHaveFiniteDimension P.A.hom (lbPow M e) (δ * e ^ P.g) := by
  intro hL hL' K _ _ P M hM ha hs
  obtain ⟨v, hv, h, hh, ht⟩ := GlobalTheory.T.polarizedAbelian_ample_exists_positive_volume hL hL' K P M hM ha
  obtain ⟨l, hl, hlK⟩ := SymAmpleCount.exists_two_le_cast_ne_zero K
  have B := GlobalTheory.T.sectionsHaveFiniteDimension_invariance_isomorphisms K _ P.A.hom M hM
  have sc : ∀ e, 1 ≤ e → h (e * l ^ 2) = (l ^ 2) ^ P.g * h e := fun e he => by
    have hMe := GlobalTheory.isLB_lbPow hM e
    have hae : Out.RelAmple P.A (lbPow M e) :=
      (GlobalTheory.relAmple_finite_pow_iso _ P.A P.A (𝟙 _) M e he P.isAb P.isAb hM
        (inferInstanceAs (IsFinite (𝟙 P.A.left)))).2.1.2 ha
    have hse : SymB (lbPow M e) :=
      LBIso.trans hMe (GlobalTheory.isLB_lbPow (LB.isLB_pull hM _) e) (LB.isLB_pull hMe _)
        ((B.2.1 _ (LB.isLB_pull hM _) hs).2 e) (B.2.2.2.2.1 _ _ e)
    have H := SymAmpleCount.sectionsDim_symmetricAmple_pow_sq hL hL' K P _ hMe hae hse hlK (hh e)
    have H' := ((GlobalTheory.T.sectionsHaveFiniteDimension_invariance_isomorphisms K _ P.A.hom _ (GlobalTheory.isLB_lbPow hMe _)).2.1 _ (GlobalTheory.isLB_lbPow hM _)
      (B.2.2.1 e (l ^ 2))).1 _ H
    rw [← pow_mul]
    exact (GlobalTheory.T.sectionsHaveFiniteDimension_invariance_isomorphisms K _ P.A.hom _ (GlobalTheory.isLB_lbPow hM _)).1 _ _ (hh _) H'
  have key : ∀ e, 1 ≤ e → (h e : ℝ) = v * (e : ℝ) ^ P.g := fun e he =>
    SymAmpleCount.eq_of_scaling (q := l ^ 2) (by nlinarith) sc ht he
  have h₁ : (h 1 : ℝ) = v := by simpa using key 1 le_rfl
  refine ⟨h 1, ?_, ⟨h, hh, h₁ ▸ ht⟩, fun e he => ?_⟩
  · have : (0 : ℝ) < h 1 := h₁ ▸ hv
    exact_mod_cast this
  · have : h e = h 1 * e ^ P.g := by
      have := key e he
      rw [← h₁] at this
      exact_mod_cast this
    exact this ▸ hh e

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem GlobalTheory.thetaFam_isPEL : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La), 1 ≤ D.p + D.q → IsSympBasis D bas → a w = H.w0 → a w' = H.bar H.w0 → Subring.closure (Set.range a) = ⊤ → ∀ (n N' : ℕ) (o : Type) [CommRing o] (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (ρ : o), em ρ = H.rt0 → ArBase em → ∀ F : ThetaFam n em (PELClass (b := b) D a bas ρ em), ∃ τ : SAB H F.MM, IsPEL D a bas ρ F.univ τ := by
  intro h1 h2 h3 E _ _ _ H D g J _ a w w' bas hpq hbas hw hw' hcl n N' o _ b em ρ hρ hem F
  obtain ⟨hded, -, hinj⟩ := hem
  have := F.reduced
  have : LocallyOfFiniteType F.s := by
    obtain ⟨N, i, hi, -, hs⟩ := F.qproj
    have := isProper_str o N
    rw [← hs]
    infer_instance
  have : IsLocallyNoetherian F.MM := LocallyOfFiniteType.isLocallyNoetherian F.s
  exact GlobalTheory.T.exists_isPELTriple_of_dense_fibres h1 h2 h3 E H D g J a bas w w' hpq hbas hw hw' hcl (N' ^ 2) o b em ρ F.MM F.s F.univ hρ hinj F.dense
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

theorem _root_.GlobalTheory.T.exists_homogeneousPolynomial_volume_pullback_combinations : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (I : Type) [Fintype I] (φ : I → (P.A.left ⟶ P.A.left)), ∃ Φ : MvPolynomial I ℚ, Φ.IsHomogeneous P.g ∧ ∀ ε : I → ℤ, Out.RelAmple P.A (LB.LinComb P.L φ ε) → Vol P.A.hom (LB.LinComb P.L φ ε) P.g ((MvPolynomial.eval (fun i => (ε i : ℚ)) Φ : ℚ) : ℝ) := by
  first | exact @GlobalTheory.VolPoly.exists_vol_linComb_poly | exact GlobalTheory.VolPoly.exists_vol_linComb_poly | (intros; apply GlobalTheory.VolPoly.exists_vol_linComb_poly <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.existsUnique_map_to_thetaFamily_openPart : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (em : o →+* ℂ) (C : TObj g ((n ^ j) ^ 2) J b (spMap em) → Prop) (d : ℕ), ArBase em → GoodClass em C Mat κ w w' d → ∀ (F : WFam n em C Mat κ) (S : Scheme.{0}) (s' : S ⟶ Sp o) (t : TObj g ((n ^ j) ^ 2) J b s'), IsReduced S → Dense (fromSet em C t) → t.FibShape Mat κ → ∃! f : S ⟶ F.U.toScheme, f ≫ F.U.ι ≫ F.Y.s = s' ∧ TMap t F.univ f := by
  first | exact @GlobalTheory.ZM.UnivProp.existsUnique_map_of_wFam | exact GlobalTheory.ZM.UnivProp.existsUnique_map_of_wFam | (intros; apply GlobalTheory.ZM.UnivProp.existsUnique_map_of_wFam <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.exists_periods_complexPELObject : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (em : o →+* ℂ) (w w' : J) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (ρ : o) (ty : Fin g → (E →+* ℂ)) (t : TObj g k J b (spMap em)), a w = H.w0 → a w' = H.bar H.w0 → em ρ = H.rt0 → IsTypeFn H D.p D.q ty → PELClass D a bas ρ em t → ∃ (D' : Datum H) (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν : ℕ → ℤ) (Q : D'.La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), (D'.p = D.p ∧ D'.q = D.q ∧ (∀ n m : ℕ, 0 < n → 0 < m → ∀ x, ∃ y, f (n * m) x = f n x + n • y) ∧ (∀ n : ℕ, 0 < n → (∀ x, (∃ y, f n x = n • y) ↔ ∃ y, x = n • y) ∧ ∀ x', ∃ x y, x' = f n x + n • y) ∧ ∀ n : ℕ, 0 < n → ∀ x x', (n : ℤ) ∣ D'.EF (f n x) (f n x') - ν n * D.EF x x') ∧ em (b.ζ : o) = Complex.exp (-(2 * Real.pi * Complex.I) * (ν k : ℂ) / k) ∧ IsPeriod D' ty Q ∧ (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = D'.EF x y) ∧ (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH Hm χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ (Q).range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = Q x → χ' l = (-1) ^ D'.EF x ((fun j x => a j • x) w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((k : ℕ) : ℂ)⁻¹ • Q ((fun i => f k (bas (Pi.single i 1))) i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q ((fun j x => a j • x) j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) := by
  first | exact @GlobalTheory.PELPeriod.exists_period | exact GlobalTheory.PELPeriod.exists_period | (intros; apply GlobalTheory.PELPeriod.exists_period <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.isPELObject_of_primitive_periodMap_uniformised : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (em : o →+* ℂ) (w w' : J) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (ρ : o) (ty : Fin g → (E →+* ℂ)) (t : TObj g k J b (spMap em)) (D' : Datum H) (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν : ℕ → ℤ) (Q : D'.La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), 1 ≤ D.p + D.q → a w = H.w0 → em ρ = H.rt0 → IsTypeFn H D.p D.q ty → (D'.p = D.p ∧ D'.q = D.q ∧ (∀ n m : ℕ, 0 < n → 0 < m → ∀ x, ∃ y, f (n * m) x = f n x + n • y) ∧ (∀ n : ℕ, 0 < n → (∀ x, (∃ y, f n x = n • y) ↔ ∃ y, x = n • y) ∧ ∀ x', ∃ x y, x' = f n x + n • y) ∧ ∀ n : ℕ, 0 < n → ∀ x x', (n : ℤ) ∣ D'.EF (f n x) (f n x') - ν n * D.EF x x') → em (b.ζ : o) = Complex.exp (-(2 * Real.pi * Complex.I) * (ν k : ℂ) / k) → IsPeriod D' ty Q → (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = D'.EF x y) → (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH Hm χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ (Q).range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = Q x → χ' l = (-1) ^ D'.EF x ((fun j x => a j • x) w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((k : ℕ) : ℂ)⁻¹ • Q ((fun i => f k (bas (Pi.single i 1))) i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q ((fun j x => a j • x) j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) → t.Prim w w' → PELClass D a bas ρ em t := by
  first | exact @GlobalTheory.PeriodObject.pelClass_of_period | exact GlobalTheory.PeriodObject.pelClass_of_period | (intros; apply GlobalTheory.PeriodObject.pelClass_of_period <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

theorem _root_.GlobalTheory.T.iterate_eq_id_of_trivial_on_fixed_fibre : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (S : ℕ) (β : RZ H S l.A →+* KA l) (C : Cpt Xo.s Xo.univ.t β) (r : Xo.X ≅ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t r.hom) (ρ : C.X ≅ C.X) (mu : SABMap C.t C.t ρ.hom), IsInc (RZ H S l.A).subtype (KA l).val.toRingHom β → 0 < S → (∃ e, l.A ∣ S ^ e) → C.j ≫ ρ.hom = r.hom ≫ C.j → C.m.φ ≫ mu.φ = ν.φ ≫ C.m.φ → r.hom ≫ Xo.s = Xo.s → (∀ x, (Xo.univ.eta x).left ≫ ν.φ = r.hom ≫ (Xo.univ.eta x).left) → ∀ g : D.La →ₗ[𝓞 E] D.La, (∀ x, (Xo.univ.etaA (g x)).left ≫ ν.φ = r.hom ≫ (Xo.univ.etaA x).left) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ C.X), x ≫ ρ.hom = x → pullback.fst C.t.G.hom x ≫ mu.φ = pullback.fst C.t.G.hom x → (fun f : Xo.X ⟶ Xo.X => f ≫ r.hom)^[l.A] (𝟙 _) = 𝟙 _ := by
  first | exact @GlobalTheory.StabTame.iterate_eq_id_of_fixes_fibre | exact GlobalTheory.StabTame.iterate_eq_id_of_fixes_fibre | (intros; apply GlobalTheory.StabTame.iterate_eq_id_of_fixes_fibre <;> assumption)
end
