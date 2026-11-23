module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2818
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2817
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2876
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2892
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle133
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2820
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2821
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2822
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem fnOf_app_const {Y Z : Scheme.{0}} [IsIntegral Y] {R₁ : Type} [CommRing R₁] (f : Y ⟶ Z) (c : Z ⟶ Sp R₁)
    (U : Z.Opens) (h : genericPoint Y ∈ f ⁻¹ᵁ U) (r : R₁) :
    fnOf (f ⁻¹ᵁ U) h ((f.app U).hom ((Z.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom
      (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom r)))) = GlobalTheory.Desc.cst (f ≫ c) r := by
  have hn := congrArg (fun φ => φ.hom (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom r)))
    (f.naturality (homOfLE (le_top : U ≤ ⊤)).op)
  simp only [CommRingCat.comp_apply] at hn
  rw [hn]
  exact fnOf_resG (X := Y) (le_top : f ⁻¹ᵁ U ≤ ⊤) h _

theorem app_surjective_of_factor {R F : Type} [CommRing R] [Field F] {c₀ : R →+* F} {N : ℕ → Set F}
    {P : Scheme.{0}} [IsIntegral P] {p : P ⟶ Sp R} {ψ : P.functionField →+* F} {Dp : ℕ → F → P.Opens}
    (hP : IsModel c₀ N p ψ Dp) {R₁ : Type} [CommRing R₁] {Y Z : Scheme.{0}} [IsIntegral Y] [CompactSpace Y]
    (f : Y ⟶ Z) (a : Z ⟶ P) (c : Z ⟶ Sp R₁) (θ : F →+* Y.functionField) (D₁ : CartierDiv Y)
    (hspan : ∀ k, Sec D₁ k = spanBy (GlobalTheory.Desc.cst (f ≫ c)) (θ '' N k)) (hff : PFF (𝟙 _) (f ≫ a) (θ.comp ψ))
    (k : ℕ) (hk : 1 ≤ k) (b : F) (hb : b ∈ N k) (hloc : ∀ y, (f ≫ a) y ∈ Dp k b ↔ y ∈ locus D₁ k (θ b)) :
    Function.Surjective (f.app (a ⁻¹ᵁ Dp k b)) := by
  intro s
  by_cases hW : genericPoint Y ∈ f ⁻¹ᵁ a ⁻¹ᵁ Dp k b
  swap
  · exact ⟨0, fn_ext fun h => absurd h hW⟩

  have hgen : genericPoint Y ∈ locus D₁ k (θ b) := (hloc _).1 hW
  have hθb0 : θ b ≠ 0 := CartierDiv.GeneratesAt.ne_zero (D := k • D₁) hgen
  have hb0 : b ≠ 0 := fun e => hθb0 (by rw [e, map_zero])
  have hPg : genericPoint P ∈ Dp k b := (hP.gen k hk b hb).2 hb0

  have hreg : ∀ y ∈ locus D₁ k (θ b), RegAt y (fnOf (f ⁻¹ᵁ a ⁻¹ᵁ Dp k b) hW s) :=
    fun y hy => regAt_fnOf (U := f ⁻¹ᵁ a ⁻¹ᵁ Dp k b) (x := y) ((hloc y).2 hy) hW s
  have hbsec : θ b ∈ Sec D₁ k := by
    rw [hspan k]
    exact subset_spanBy _ _ ⟨b, hb, rfl⟩
  obtain ⟨n, hn⟩ := GlobalTheory.T.exists_mul_pow_mem_cartierMultiple_of_regular_locus Y D₁ k (θ b) hbsec _ hreg
  rw [hspan] at hn
  obtain ⟨M, r, t, ht, hsum⟩ := hn
  choose u hu hut using ht

  have hv : ∀ i, ∃ v, (∀ z ∈ Dp k b, RegAt z v) ∧ ψ v = u i / b ^ n :=
    fun i => (hP.ring k hk b hb hb0 (u i / b ^ n)).2 ⟨n, u i, hu i, rfl⟩
  choose v hvreg hvψ using hv
  have hA : ∀ i, ∃ A : Γ(P, Dp k b), fnOf (Dp k b) hPg A = v i := fun i => exists_fnOf_eq hPg (hvreg i)
  choose A hA using hA
  have hterm : ∀ i, fnOf (f ⁻¹ᵁ a ⁻¹ᵁ Dp k b) hW ((f.app (a ⁻¹ᵁ Dp k b)).hom
      ((Z.presheaf.map (homOfLE (le_top : a ⁻¹ᵁ Dp k b ≤ ⊤)).op).hom
        (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (r i))) * (a.app (Dp k b)).hom (A i))) =
      cst (f ≫ c) (r i) * t i / θ b ^ n := by
    intro i
    rw [map_mul, map_mul, fnOf_app_const f c _ hW (r i)]
    have e := GlobalTheory.T.rationalFunction_app_of_preservesGenericPoint P Y (f ≫ a) (θ.comp ψ) hff (Dp k b) hPg hW (A i)
    rw [hA i, RingHom.comp_apply, hvψ i, map_div₀, map_pow, hut i] at e
    rw [mul_div_assoc, ← e]
    rfl
  refine ⟨∑ i, (Z.presheaf.map (homOfLE (le_top : a ⁻¹ᵁ Dp k b ≤ ⊤)).op).hom
      (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (r i))) * (a.app (Dp k b)).hom (A i),
    fnOf_injective _ hW ?_⟩

  rw [map_sum, map_sum]
  simp_rw [hterm]
  rw [← Finset.sum_div, ← hsum, mul_div_assoc, div_self (pow_ne_zero n hθb0), _root_.mul_one]

theorem lift_app_surjective : ∀ (R F : Type) [CommRing R] [IsDomain R] [Field F] (c₀ : R →+* F) (N : ℕ → Set F), GradedFam c₀ N → ∀ (P : Scheme.{0}) [IsIntegral P] (p : P ⟶ Sp R) (ψ : P.functionField →+* F) (Dp : ℕ → F → P.Opens), IsModel c₀ N p ψ Dp → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] (ρ : R →+* R₁), ρ.Flat → Function.Injective c₀ → ∀ (Y : Scheme.{0}) [IsIntegral Y] [CompactSpace Y] [QuasiSeparatedSpace Y] (q : Y ⟶ Sp R₁) (θ : F →+* Y.functionField) (D₁ : CartierDiv Y), θ.comp c₀ = (GlobalTheory.Desc.cst q).comp ρ → LinDisj c₀ (GlobalTheory.Desc.cst q) θ → AmpleDiv D₁ → (∀ k, Sec D₁ k = spanBy (GlobalTheory.Desc.cst q) (θ '' N k)) → ∀ m : Y ⟶ P, PFF (𝟙 _) m (θ.comp ψ) → (∀ k, 1 ≤ k → ∀ b ∈ N k, ∀ y, m y ∈ Dp k b ↔ y ∈ locus D₁ k (θ b)) → ∀ (hm : m ≫ p = q ≫ spMap ρ) (k : ℕ), 1 ≤ k → ∀ b ∈ N k, Function.Surjective ((pullback.lift m q hm).app ((pullback.fst p (spMap ρ)) ⁻¹ᵁ Dp k b)) := by
  intro R F _ _ _ c₀ N _ P _ p ψ Dp hP R₁ _ _ ρ _ _ Y _ _ _ q θ D₁ _ _ _ hspan m hff hloc hm k hk b hb
  have hfc : pullback.lift m q hm ≫ pullback.snd p (spMap ρ) = q := pullback.lift_snd _ _ _
  have hfa : pullback.lift m q hm ≫ pullback.fst p (spMap ρ) = m := pullback.lift_fst _ _ _
  exact app_surjective_of_factor hP (pullback.lift m q hm) (pullback.fst p (spMap ρ)) (pullback.snd p (spMap ρ)) θ D₁
    (by rw [hfc]; exact hspan) (by rw [hfa]; exact hff) k hk b hb (by rw [hfa]; exact hloc k hk b hb)

end GlobalTheory.Desc
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
open TensorProduct

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.SecFlatBC

section Helpers

variable {R₁ F₁ : Type} [CommRing R₁] [CommRing F₁]

theorem zero_mem_spanBy (c : R₁ →+* F₁) (T : Set F₁) : (0 : F₁) ∈ spanBy c T :=
  ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, by simp⟩

theorem add_mem_spanBy (c : R₁ →+* F₁) (T : Set F₁) {a b : F₁} (ha : a ∈ spanBy c T) (hb : b ∈ spanBy c T) :
    a + b ∈ spanBy c T := by
  obtain ⟨n, r, t, ht, rfl⟩ := ha
  obtain ⟨m, r', t', ht', rfl⟩ := hb
  refine ⟨n + m, Fin.append r r', Fin.append t t', fun i => ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa using ht i
    · simpa using ht' i
  · rw [Fin.sum_univ_add]; simp

theorem spanBy_mul (c : R₁ →+* F₁) (T : Set F₁) (w : F₁) :
    spanBy c ((w * ·) '' T) = (w * ·) '' spanBy c T := by
  ext v; constructor
  · rintro ⟨n, r, t, ht, rfl⟩
    choose s hs e using ht
    refine ⟨∑ i, c (r i) * s i, ⟨n, r, s, hs, rfl⟩, ?_⟩
    dsimp only
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [← e i]; ring
  · rintro ⟨_, ⟨n, r, t, ht, rfl⟩, rfl⟩
    refine ⟨n, r, fun i => w * t i, fun i => ⟨_, ht i, rfl⟩, ?_⟩
    dsimp only
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

end Helpers

theorem fnOf_algX {R : Type} [CommRing R] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp R) (U : X.Opens)
    (hg : genericPoint X ∈ U) (a : R) :
    GlobalTheory.Cartier.fnOf U hg (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U a) = GlobalTheory.Desc.cst p a := by
  simp only [ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX, GlobalTheory.Desc.cst, RingHom.comp_apply]
  have := X.presheaf.germ_res_apply (homOfLE (show U ≤ p ⁻¹ᵁ ⊤ from le_top)) (genericPoint X) hg
    ((p.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
  exact this

theorem span_chart {R R₁ : Type} [CommRing R] [CommRing R₁] {ρ : R →+* R₁} {X Y V : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] {p : X ⟶ Sp R} {q : Y ⟶ Sp R₁} {i : V ⟶ Y} [IsOpenImmersion i] {φ : V ⟶ X}
    {θ : X.functionField →+* Y.functionField} (H : IsPullback φ (i ≫ q) p (spMap ρ)) (hP : PFF i φ θ)
    {U : X.Opens} (hU : IsAffineOpen U) (hg : genericPoint X ∈ U) :
    spanBy (GlobalTheory.Desc.cst q) (θ '' Set.range (GlobalTheory.Cartier.fnOf U hg)) =
      {v | ∀ z : V, φ z ∈ U → GlobalTheory.Cartier.RegAt (i z) v} := by
  letI := (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U).toAlgebra
  letI := ρ.toAlgebra
  obtain ⟨β, -, hβ, hr⟩ := GlobalTheory.T.exists_tensor_sections_embed_functionField_regular R R₁ ρ X Y V p q i φ θ H hP U hU hg
  rw [← hr]
  ext v; constructor
  · rintro ⟨n, r, t, ht, rfl⟩
    choose a ha e using ht
    choose b hb using ha
    refine ⟨∑ j, b j ⊗ₜ[R] r j, ?_⟩

    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [hβ, hb, e, _root_.mul_comm]
  · rintro ⟨x, rfl⟩
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact zero_mem_spanBy _ _
    | tmul b r =>
      refine ⟨1, fun _ => r, fun _ => θ (GlobalTheory.Cartier.fnOf U hg b), fun _ => ⟨_, ⟨b, rfl⟩, rfl⟩, ?_⟩
      rw [hβ, Fin.sum_univ_one, _root_.mul_comm]
    | add x y hx hy => rw [map_add]; exact add_mem_spanBy _ _ hx hy

theorem sections_linDisj_flatBaseChange : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] (ρ : R →+* R₁), ρ.Flat → ∀ (X Y V : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp R) (q : Y ⟶ Sp R₁) (i : V ⟶ Y) [IsOpenImmersion i] (φ : V ⟶ X) (θ : X.functionField →+* Y.functionField), QuasiCompact p → QuasiSeparated p → IsPullback φ (i ≫ q) p (spMap ρ) → PFF i φ θ → ∀ (D : CartierDiv X) (D₁ : CartierDiv Y), PPull i φ θ D D₁ → LinDisj (GlobalTheory.Desc.cst p) (GlobalTheory.Desc.cst q) θ ∧ ∀ k : ℕ, {v | ∀ z : V, (k • D₁).RegularAt (i z) v} = spanBy (GlobalTheory.Desc.cst q) (θ '' Sec D k) := by
  intro R R₁ _ _ ρ hρ X Y V _ _ p q i _ φ θ _ _ H hP D D₁ hD
  letI : Algebra R X.functionField := (GlobalTheory.Desc.cst p).toAlgebra
  letI : Algebra R R₁ := ρ.toAlgebra
  haveI : Module.Flat R R₁ := hρ
  obtain ⟨U₀, hU₀, hg₀, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
    (show genericPoint X ∈ (⊤ : X.Opens) from trivial)
  have hc : ∀ a : R, θ (algebraMap R X.functionField a) = GlobalTheory.Desc.cst q (algebraMap R R₁ a) := by
    intro a
    letI := (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U₀).toAlgebra
    obtain ⟨β, -, hβ, -⟩ := GlobalTheory.T.exists_tensor_sections_embed_functionField_regular R R₁ ρ X Y V p q i φ θ H hP U₀ hU₀ hg₀
    have e : (algebraMap R Γ(X, U₀) a) ⊗ₜ[R] (1 : R₁) = (1 : Γ(X, U₀)) ⊗ₜ[R] (algebraMap R R₁ a) := by
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one a, TensorProduct.smul_tmul]
    have e' := congrArg β e
    simp only [hβ, _root_.map_one, _root_.mul_one, _root_.one_mul] at e'
    rw [← e']
    exact congrArg θ (fnOf_algX p U₀ hg₀ a).symm
  have hinj : ∀ (n : ℕ) (u : Fin n → X.functionField) (r : Fin n → R₁),
      ∑ j, GlobalTheory.Desc.cst q (r j) * θ (u j) = 0 → ∑ j, u j ⊗ₜ[R] r j = 0 := by
    letI := (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U₀).toAlgebra
    haveI : Nonempty U₀ := ⟨⟨_, hg₀⟩⟩
    haveI : IsFractionRing Γ(X, U₀) X.functionField := functionField_isFractionRing_of_isAffineOpen X U₀ hU₀
    have hal : ∀ b, algebraMap Γ(X, U₀) X.functionField b = GlobalTheory.Cartier.fnOf U₀ hg₀ b := fun b => rfl
    haveI : IsScalarTower R Γ(X, U₀) X.functionField :=
      IsScalarTower.of_algebraMap_eq fun a => ((hal _).trans (fnOf_algX p U₀ hg₀ a)).symm
    obtain ⟨β, hβi, hβ, -⟩ := GlobalTheory.T.exists_tensor_sections_embed_functionField_regular R R₁ ρ X Y V p q i φ θ H hP U₀ hU₀ hg₀
    exact GlobalTheory.T.tensor_fraction_injective_of_tensor_injective R R₁ Γ(X, U₀) X.functionField Y.functionField θ (GlobalTheory.Desc.cst q) β hβi
      (fun b r => (hβ b r).trans (by rw [hal]))
  refine ⟨GlobalTheory.T.linearlyDisjoint_of_flat_baseChange_embeds R R₁ X.functionField Y.functionField θ (GlobalTheory.Desc.cst q) hinj, fun k => ?_⟩
  have hloc : ∀ x : X, ∃ (U : X.Opens) (g : X.functionFieldˣ), IsAffineOpen U ∧ x ∈ U ∧ ∀ y ∈ U, D.IsEqn y g := by
    intro x
    obtain ⟨W, hxW, g, hg⟩ := D.exists_isEqn_nhds x
    obtain ⟨U, hU, hxU, hUW⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens hxW
    exact ⟨U, g, hU, hxU, fun y hy => hg y (hUW hy)⟩
  choose U g hUa hxU hUg using hloc
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (U x : Set X)) (fun x => (U x).isOpen)
    (fun x _ => Set.mem_iUnion.2 ⟨x, hxU x⟩)
  have cov : ∀ y : X, ∃ j : t, y ∈ U j.1 := fun y => by
    obtain ⟨a, ha, h⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
    exact ⟨⟨a, ha⟩, h⟩
  haveI : Nonempty t := ⟨(cov (genericPoint X)).choose⟩
  have hgen : ∀ j : t, genericPoint X ∈ U j.1 := fun j => GlobalTheory.Cartier.gen_mem (hxU j.1)
  let N : t → Submodule R X.functionField := fun j =>
    { carrier := {u | ∀ y ∈ U j.1, (k • D).RegularAt y u}
      add_mem' := fun ha hb y hy => (ha y hy).add (hb y hy)
      zero_mem' := fun y _ => ((k • D).vanishesAt_zero y).regularAt
      smul_mem' := fun a u hu y hy => by
        rw [Algebra.smul_def]
        exact (hu y hy).regAt_mul (GlobalTheory.Cartier.regAt_fnOf (U := ⊤) trivial trivial _) }
  have hSec : Sec D k = ⋂ j, (N j : Set X.functionField) := by
    ext u; rw [Set.mem_iInter]
    exact ⟨fun h j y _ => h y, fun h y => let ⟨j, hj⟩ := cov y; h j y hj⟩
  have hG : ∀ j : t, ∀ z : V, φ z ∈ U j.1 →
      (k • D₁).IsEqn (i z) (Units.map θ.toMonoidHom (g j.1 ^ k)) := by
    intro j z hz
    rw [map_pow]
    exact (hD z _ (hUg j.1 _ hz)).nsmul k
  have hN : ∀ j : t, (N j : Set X.functionField) =
      ((((g j.1 ^ k : X.functionFieldˣ) : X.functionField)⁻¹ * ·) '' Set.range (GlobalTheory.Cartier.fnOf (U j.1) (hgen j))) := by
    intro j; ext u; constructor
    · intro hu
      have hreg : ∀ y ∈ U j.1, GlobalTheory.Cartier.RegAt y (u * ((g j.1 ^ k : X.functionFieldˣ) : X.functionField)) :=
        fun y hy => ((hUg j.1 y hy).nsmul k).regularAt_iff.1 (hu y hy)
      obtain ⟨b, hb⟩ := GlobalTheory.Cartier.exists_fnOf_eq (hgen j) hreg
      exact ⟨_, ⟨b, rfl⟩, by dsimp only; rw [hb, _root_.mul_comm u, ← _root_.mul_assoc, inv_mul_cancel₀ (Units.ne_zero _), _root_.one_mul]⟩
    · rintro ⟨_, ⟨b, rfl⟩, rfl⟩ y hy
      dsimp only
      rw [((hUg j.1 y hy).nsmul k).regularAt_iff, _root_.mul_comm _ ((g j.1 ^ k : X.functionFieldˣ) : X.functionField),
        ← _root_.mul_assoc, mul_inv_cancel₀ (Units.ne_zero _), _root_.one_mul]
      exact GlobalTheory.Cartier.regAt_fnOf hy (hgen j) b
  have hspan : ∀ j : t, spanBy (GlobalTheory.Desc.cst q) (θ '' (N j : Set X.functionField)) =
      {v | ∀ z : V, φ z ∈ U j.1 → (k • D₁).RegularAt (i z) v} := by
    intro j
    set G : X.functionField := ((g j.1 ^ k : X.functionFieldˣ) : X.functionField) with hGdef
    have himg : θ '' ((G⁻¹ * ·) '' Set.range (GlobalTheory.Cartier.fnOf (U j.1) (hgen j))) =
        (θ G⁻¹ * ·) '' (θ '' Set.range (GlobalTheory.Cartier.fnOf (U j.1) (hgen j))) := by
      rw [Set.image_image, Set.image_image]; simp only [map_mul]
    rw [hN j, himg, spanBy_mul, span_chart H hP (hUa j.1) (hgen j)]
    have hGne : G ≠ 0 := Units.ne_zero _
    have hθG : θ G ≠ 0 := (map_ne_zero θ).2 hGne
    have hval : ∀ z : V, (((Units.map θ.toMonoidHom (g j.1 ^ k)) : Y.functionFieldˣ) : Y.functionField) = θ G :=
      fun _ => rfl
    ext v; constructor
    · rintro ⟨w, hw, rfl⟩ z hz
      rw [(hG j z hz).regularAt_iff, hval z, map_inv₀, _root_.mul_comm, ← _root_.mul_assoc, mul_inv_cancel₀ hθG, _root_.one_mul]
      exact hw z hz
    · intro hv
      refine ⟨v * θ G, fun z hz => ?_, ?_⟩
      · have := (hG j z hz).regularAt_iff.1 (hv z hz)
        rwa [hval z] at this
      · show θ G⁻¹ * (v * θ G) = v
        rw [map_inv₀, _root_.mul_comm, _root_.mul_assoc, mul_inv_cancel₀ hθG, _root_.mul_one]
  have hT : {v | ∀ z : V, (k • D₁).RegularAt (i z) v} =
      ⋂ j : t, {v | ∀ z : V, φ z ∈ U j.1 → (k • D₁).RegularAt (i z) v} := by
    ext v; rw [Set.mem_iInter]
    exact ⟨fun h j z _ => h z, fun h z => let ⟨j, hj⟩ := cov (φ z); h j z hj⟩
  rw [hT, hSec, GlobalTheory.T.span_iInter_submodules_of_flat_baseChange R R₁ X.functionField Y.functionField θ (GlobalTheory.Desc.cst q) hc hinj t N]
  exact Set.iInter_congr fun j => (hspan j).symm

end GlobalTheory.SecFlatBC
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Desc.GaussBC

theorem two_le_coheight_of_chain {X : Scheme.{0}} {x e g : X} (h₁ : e ⤳ x) (h₂ : g ⤳ e) (n₁ : e ≠ x)
    (n₂ : g ≠ e) : (2 : ℕ∞) ≤ Order.coheight x := by
  have l₁ : x < e := lt_of_le_not_ge h₁ (fun h => n₁ (h₁.antisymm h).eq)
  have l₂ : e < g := lt_of_le_not_ge h₂ (fun h => n₂ (h₂.antisymm h).eq)
  have a₁ := Order.coheight_add_one_le l₁
  have a₂ := Order.coheight_add_one_le l₂
  calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
    _ ≤ Order.coheight g + 1 + 1 := by gcongr; exact zero_le
    _ ≤ Order.coheight e + 1 := by gcongr
    _ ≤ Order.coheight x := a₁

theorem not_two_le_coheight_of_ringKrullDim_eq_one {X : Scheme.{0}} (x : X)
    (h : ringKrullDim (X.presheaf.stalk x) = 1) : ¬ (2 : ℕ∞) ≤ Order.coheight x := by
  intro h₂
  rw [ringKrullDim_stalk_eq_coheight] at h
  have : Order.coheight x = 1 := by exact_mod_cast h
  rw [this] at h₂
  exact absurd h₂ (by decide)

theorem apply_genericPoint_ne_closedPoint {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Sp R) [Flat f] : f (genericPoint X) ≠ closedPoint R := by
  intro h
  let p₀ : Sp R := ⟨⊥, Ideal.isPrime_bot⟩
  have hs : p₀ ⤳ f (genericPoint X) := by
    rw [h]; exact (PrimeSpectrum.le_iff_specializes p₀ (closedPoint R)).mp bot_le
  obtain ⟨w, hw, hfw⟩ := Flat.generalizingMap f hs
  have hw' : w = genericPoint X := (hw.antisymm (genericPoint_specializes w)).eq
  rw [hw', h] at hfw
  exact IsDiscreteValuationRing.not_a_field R (congrArg PrimeSpectrum.asIdeal hfw)

theorem apply_eq_of_closedFibre_dim_one : ∀ (T D : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [CommRing D] [IsDomain D] [IsDiscreteValuationRing D] (a : T →+* D), a.Flat → (maximalIdeal T).map a = maximalIdeal D → ∀ (H : Over (Sp T)) [GrpObj H] [IsIntegral H.left] (H' : Over (Sp D)) [GrpObj H'] [IsIntegral H'.left] (π : H'.left ⟶ H.left) (θ : H.left.functionField →+* H'.left.functionField), IsSemiAbelian H → IsPullback π H'.hom H.hom (spMap a) → PFF (𝟙 _) π θ → ∀ (y : H.left) (y' : H'.left), H.hom y = closedPoint T → H'.hom y' = closedPoint D → ringKrullDim (H.left.presheaf.stalk y) = 1 → ringKrullDim (H'.left.presheaf.stalk y') = 1 → π y' = y := by
  intro T D _ _ _ _ _ _ a ha hm H _ _ H' _ _ π θ hG hpb _ y y' hy hy' hdy hdy'
  haveI : Smooth H.hom := hG.smooth
  haveI : Flat H'.hom := MorphismProperty.of_isPullback hpb (inferInstanceAs (Flat H.hom))
  haveI : Flat (spMap a) := (HasRingHomProperty.Spec_iff (P := @Flat)).mpr ha
  haveI : Flat π := MorphismProperty.of_isPullback hpb.flip (inferInstanceAs (Flat (spMap a)))
  have hsq : ∀ z, H.hom (π z) = spMap a (H'.hom z) := fun z => by
    have := congrArg (fun f => f.base z) hpb.w
    simpa using this
  have hcl : spMap a (closedPoint D) = closedPoint T := by
    apply PrimeSpectrum.ext
    show Ideal.comap a (maximalIdeal D) = maximalIdeal T
    have hle : maximalIdeal T ≤ Ideal.comap a (maximalIdeal D) := Ideal.map_le_iff_le_comap.mp hm.le
    exact ((maximalIdeal.isMaximal T).eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle).symm
  have hback : ∀ p : Sp D, spMap a p = closedPoint T → p = closedPoint D := by
    intro p hp
    by_contra hne
    have hbot : p.asIdeal = ⊥ := by
      by_contra hb
      exact hne (PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal (p.isPrime.isMaximal hb)))
    have hker : Ideal.comap a ⊥ = maximalIdeal T := by
      rw [← hbot]; exact congrArg PrimeSpectrum.asIdeal hp
    apply IsDiscreteValuationRing.not_a_field D
    rw [← hm, ← hker]
    exact le_antisymm Ideal.map_comap_le bot_le
  set F : Set H.left := H.hom ⁻¹' {closedPoint T} with hFdef
  have hFc : IsClosed F := (isClosed_singleton_closedPoint T).preimage H.hom.continuous
  have hFi : IsIrreducible F := by
    haveI := GlobalTheory.SemiAbFibre.irreducibleSpace_fibre _ H hG _ ((Sp T).fromSpecResidueField (closedPoint T))
    haveI : IrreducibleSpace (H.hom.fiber (closedPoint T)) := this
    have hr := (IrreducibleSpace.isIrreducible_univ (H.hom.fiber (closedPoint T))).image _
      (Scheme.Hom.fiberι H.hom (closedPoint T)).continuous.continuousOn
    rw [Set.image_univ] at hr
    convert hr using 1
    exact (Scheme.Hom.range_fiberι H.hom (closedPoint T)).symm
  have hξ₀ := hFi.isGenericPoint_genericPoint_closure
  rw [hFc.closure_eq] at hξ₀
  set ξ₀ := hFi.genericPoint
  have hgH := apply_genericPoint_ne_closedPoint H.hom
  have hgH' := apply_genericPoint_ne_closedPoint H'.hom
  have hyξ₀ : y = ξ₀ := by
    by_contra hne
    refine not_two_le_coheight_of_ringKrullDim_eq_one y hdy
      (two_le_coheight_of_chain (hξ₀.specializes hy) (genericPoint_specializes ξ₀) (Ne.symm hne) ?_)
    intro h; apply hgH; rw [h]; exact hξ₀.mem
  have hzξ₀ : π y' = ξ₀ := by
    by_contra hne
    have hz : π y' ∈ F := by
      show H.hom (π y') = closedPoint T
      rw [hsq, hy', hcl]
    obtain ⟨w, hw, hπw⟩ := Flat.generalizingMap π (hξ₀.specializes hz)
    refine not_two_le_coheight_of_ringKrullDim_eq_one y' hdy'
      (two_le_coheight_of_chain hw (genericPoint_specializes w) ?_ ?_)
    · rintro rfl; exact hne hπw
    · intro h; apply hgH'; apply hback; rw [← hsq, h, hπw]; exact hξ₀.mem
  rw [hzξ₀, hyξ₀]

end GlobalTheory.Desc.GaussBC
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_generator_thetaConstants_fibre : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] (D : DegPre V₁) (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K)
  (o : Type) [CommRing o] (g m : ℕ) (J : Type) (b : TBase o (m ^ 2)) (s : Sp K ⟶ Sp o) (t : TObj g (m ^ 2) J b s)
  (ψ : ((Over.pullback (spMap ev)).obj D.P.A).left ⟶ t.A.left),
  IsGrpPullback ((Over.pullback (spMap ev)).obj D.P.A) t.A (𝟙 _) ψ →
  LBIso (D.P.L.pull (pullback.fst D.P.A.hom (spMap ev))) (t.L.pull ψ) →
  ∀ v : Ix g (m ^ 2) → K, t.HasTh (𝟙 _) v →
  ∃ (th : LB.Sec (LPow D.P.A D.P.L ((1 : ℕ) : ℤ) (Over.mk (spMap ev)))) (κ : K), IsGenSec D.P.A D.P.L ((1 : ℕ) : ℤ) th ∧ κ ≠ 0 ∧
    ∀ a, ∃ y : Over.mk (spMap ev) ⟶ D.P.A, GlobalTheory.Ex.OneGen.ThG D.P.A D.P.L D.rig m th y (GlobalTheory.Ex.fnOf (κ * v a)) := by
  first | exact @GlobalTheory.FibThetaMove.exists_gen_thG_fibre | exact GlobalTheory.FibThetaMove.exists_gen_thG_fibre | (intros; apply GlobalTheory.FibThetaMove.exists_gen_thG_fibre <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.eighthPowerPresentation_endomorphisms_pullback : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ) (T T' : Scheme.{0}) (P : PolAV T) (P' : PolAV T') (u : T ⟶ F.X) (f : T' ⟶ T) (φ : P'.A.left ⟶ P.A.left) (c : SiegPre g n ζ (u ≫ F.s)), SiegPB c F.univ u → ∀ pr : Fin 8 → (P.A ⟶ c.A), (∀ a, IsMonHom (pr a)) → (∀ (T₁ : Over T) (y : Fin 8 → (T₁ ⟶ c.A)), ∃! x : T₁ ⟶ P.A, ∀ a, x ≫ pr a = y a) → LBIso P.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → IsGrpPullback P'.A P.A f φ → LBIso P'.L (P.L.pull φ) → ∃ c' : SiegPre g n ζ ((f ≫ u) ≫ F.s), SiegPB c' F.univ (f ≫ u) ∧ ∃ pr' : Fin 8 → (P'.A ⟶ c'.A), (∀ a, IsMonHom (pr' a)) ∧ (∀ (T₁ : Over T') (y : Fin 8 → (T₁ ⟶ c'.A)), ∃! x : T₁ ⟶ P'.A, ∀ a, x ≫ pr' a = y a) ∧ LBIso P'.L (LB.LinComb c'.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr' ab.1) (pr' ab.2)).left) (fun ab => W ab.1 ab.2)) ∧ ∀ (b : P.A ⟶ P.A) (k : Fin 8 → Fin 8 → ℤ), (∀ a, b ≫ pr a = (List.ofFn fun v => pr v ^ k a v).prod) → ∃ b' : P'.A ⟶ P'.A, (∀ a, b' ≫ pr' a = (List.ofFn fun v => pr' v ^ k a v).prod) ∧ b'.left ≫ φ = φ ≫ b.left := by
  first | exact @GlobalTheory.Poinc.sharpOver_pullback_end | exact GlobalTheory.Poinc.sharpOver_pullback_end | (intros; apply GlobalTheory.Poinc.sharpOver_pullback_end <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.relAmple_of_mumfordBundle_iso_universal : ∀ {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) (R' : Type) [CommRing R'] [IsNoetherianRing R'] (T : Sp R' ⟶ F.X) (B : Over (Sp R')) [GrpObj B] [IsCommMonObj B] (β : B.left ⟶ F.univ.A.left) (β₂ : (G2 B).left ⟶ (G2 F.univ.A).left), IsGrpPullback B F.univ.A T β → IsSquare β β₂ → ∀ L : LB B.left, L.IsLB → LBIso (abelian₂ B L) (F.univ.P.pull β₂) → RelAmple B L := by
  first | exact @GlobalTheory.MumAmple.relAmple_of_lam_iso_univ | exact GlobalTheory.MumAmple.relAmple_of_lam_iso_univ | (intros; apply GlobalTheory.MumAmple.relAmple_of_lam_iso_univ <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.abelianScheme_descends_galoisCover_noetherian_base : ∀ (K : Type) [CommRing K] [IsNoetherianRing K] (X Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp K) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (G : Over X) [GrpObj G] (ν : Ga → (G.left ⟶ G.left)), IsGaloisCover Ga ρ π → IsQProjOver (G.hom ≫ π ≫ sY) → IsAbelianScheme G → (∀ a, IsGrpPullback G G (ρ a) (ν a)) → ν 1 = 𝟙 _ → (∀ a c, ν (a * c) = ν a ≫ ν c) → ∃ (G' : Over Y) (_ : GrpObj G') (φ : G.left ⟶ G'.left), IsAbelianScheme G' ∧ IsGrpPullback G G' π φ ∧ IsGaloisCover Ga ν φ := by
  first | exact @GlobalTheory.abelianScheme_descends_galoisCover_noetherian | exact GlobalTheory.abelianScheme_descends_galoisCover_noetherian | (intros; apply GlobalTheory.abelianScheme_descends_galoisCover_noetherian <;> assumption)
end
