module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

open scoped TensorProduct

namespace GlobalTheory.Desc

theorem tmul_sum_eq_zero_of_linDisj {R R₁ F K : Type} [CommRing R] [CommRing R₁] [Field F] [Field K] [Algebra R R₁]
    [Algebra R F] (c : R₁ →+* K) (θ : F →+* K) (hc₀ : Function.Injective (algebraMap R F))
    (hθ : θ.comp (algebraMap R F) = c.comp (algebraMap R R₁)) (hL : LinDisj (algebraMap R F) c θ) :
    ∀ (n : ℕ) (u : Fin n → F) (r : Fin n → R₁), ∑ i, θ (u i) * c (r i) = 0 → ∑ i, u i ⊗ₜ[R] r i = 0 := by
  have hθ' : ∀ b : R, θ (algebraMap R F b) = c (algebraMap R R₁ b) := fun b => RingHom.congr_fun hθ b
  intro n
  induction n with
  | zero => intro u r _; simp
  | succ n ih =>
    intro u r h
    by_cases hind : ∀ b : Fin (n+1) → R, ∑ i, algebraMap R F (b i) * u i = 0 → b = 0
    · have hr := hL (n+1) u hind r (by rw [← h]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _)
      subst hr; simp
    · push_neg at hind
      obtain ⟨b, hb, hb0⟩ := hind
      obtain ⟨j, hj⟩ : ∃ j, b j ≠ 0 := by
        by_contra hc; push_neg at hc; exact hb0 (funext hc)
      have hdj : algebraMap R F (b j) ≠ 0 := by
        intro h0; apply hj; apply hc₀; rw [h0, map_zero]
      obtain ⟨w, hw⟩ : ∃ w : Fin n → F, ∀ i, w i = u (j.succAbove i) / algebraMap R F (b j) := ⟨_, fun _ => rfl⟩
      have hrel : algebraMap R F (b j) * u j +
          ∑ i : Fin n, algebraMap R F (b (j.succAbove i)) * u (j.succAbove i) = 0 := by
        rw [← Fin.sum_univ_succAbove (fun i => algebraMap R F (b i) * u i) j]; exact hb
      have hu : ∀ i, u (j.succAbove i) = b j • w i := by
        intro i; rw [Algebra.smul_def, hw i]; field_simp
      have hsum : ∑ i : Fin n, algebraMap R F (b (j.succAbove i)) * w i = - u j := by
        have : ∑ i : Fin n, algebraMap R F (b (j.succAbove i)) * w i =
            (∑ i : Fin n, algebraMap R F (b (j.succAbove i)) * u (j.succAbove i)) / algebraMap R F (b j) := by
          rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by rw [hw i]; ring
        rw [this, eq_neg_of_add_eq_zero_right hrel]; field_simp
      have huj : u j = - ∑ i : Fin n, b (j.succAbove i) • w i := by
        simp only [Algebra.smul_def]; rw [hsum, neg_neg]
      have key : ∑ i, u i ⊗ₜ[R] r i =
          ∑ i : Fin n, w i ⊗ₜ[R] (b j • r (j.succAbove i) - b (j.succAbove i) • r j) := by
        rw [Fin.sum_univ_succAbove _ j]
        simp only [TensorProduct.tmul_sub, Finset.sum_sub_distrib, ← TensorProduct.smul_tmul, ← hu]
        rw [huj, TensorProduct.neg_tmul, TensorProduct.sum_tmul]
        abel
      rw [key]
      apply ih
      have e1 : ∀ i, θ (w i) * c (b j • r (j.succAbove i) - b (j.succAbove i) • r j) =
          θ (u (j.succAbove i)) * c (r (j.succAbove i)) - c (r j) * θ (algebraMap R F (b (j.succAbove i)) * w i) := by
        intro i
        rw [hu i]
        simp only [Algebra.smul_def, map_sub, map_mul, hθ']
        ring

      rw [Finset.sum_congr rfl (fun i _ => e1 i), Finset.sum_sub_distrib, ← Finset.mul_sum, ← map_sum, hsum, map_neg]
      have h' := h
      rw [Fin.sum_univ_succAbove _ j] at h'
      linear_combination h'

theorem tmul_sum_eq_zero_of_flat_linDisj : ∀ (R R₁ A F K : Type) [CommRing R] [CommRing R₁] [CommRing A] [Field F] [Field K] [Algebra R A] [Algebra R R₁], Module.Flat R R₁ → ∀ (c₀ : R →+* F) (e : A →+* F) (c : R₁ →+* K) (θ : F →+* K), Function.Injective c₀ → Function.Injective e → e.comp (algebraMap R A) = c₀ → θ.comp c₀ = c.comp (algebraMap R R₁) → LinDisj c₀ c θ → ∀ (n : ℕ) (a : Fin n → A) (r : Fin n → R₁), ∑ i, θ (e (a i)) * c (r i) = 0 → ∑ i, a i ⊗ₜ[R] r i = 0 := by
  intro R R₁ A F K _ _ _ _ _ _ _ hflat c₀ e c θ hc₀ he hec hθ hL n a r h
  letI : Algebra R F := c₀.toAlgebra
  let eA : A →ₐ[R] F := { e with commutes' := fun x => RingHom.congr_fun hec x }
  have hinj := Module.Flat.rTensor_preserves_injective_linearMap (M := R₁) eA.toLinearMap he
  apply hinj

  rw [map_sum, map_zero]
  simp only [LinearMap.rTensor_tmul]
  exact tmul_sum_eq_zero_of_linDisj (R := R) c θ hc₀ hθ hL n (fun i => e (a i)) r h

end GlobalTheory.Desc
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.Desc

theorem unitAt_of_mul_right {X : Scheme.{0}} [IsIntegral X] {x : X} {a b : X.functionField}
    (ha : RegAt x a) (hb : RegAt x b) (h : UnitAt x (a * b)) : UnitAt x b := by
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', rfl⟩ := hb
  obtain ⟨w, hw, e⟩ := h
  rw [← map_mul] at e
  obtain rfl := IsFractionRing.injective (X.presheaf.stalk x) X.functionField e
  exact ⟨b', isUnit_of_mul_isUnit_right hw, rfl⟩

theorem regAt_cst {R : Type} [CommRing R] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp R) (x : X) (r : R) :
    RegAt x (cst p r) :=
  regAt_fnOf (x := x) (U := ⊤) trivial trivial _

theorem exists_locus_of_span : ∀ (R₁ F : Type) [CommRing R₁] [Field F] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp R₁) (θ : F →+* Y.functionField) (N : ℕ → Set F) (D₁ : CartierDiv Y), AmpleDiv D₁ → (∀ k, Sec D₁ k = spanBy (GlobalTheory.Desc.cst q) (θ '' N k)) → ∀ y : Y, ∃ k, 1 ≤ k ∧ ∃ b ∈ N k, y ∈ locus D₁ k (θ b) := by
  intro R₁ F _ _ Y _ q θ N D₁ hA hS y
  obtain ⟨k, hk, u, hu, U, -, hU, hy⟩ := hA y
  have hyu : y ∈ locus D₁ k u := hU ▸ hy
  have hu' : u ∈ spanBy (cst q) (θ '' N k) := hS k ▸ hu
  obtain ⟨n, r, t, ht, rfl⟩ := hu'
  obtain ⟨g, hg⟩ := (k • D₁).exists_isEqn y
  have hunit : UnitAt y ((∑ i, cst q (r i) * t i) * g) := hg.generatesAt_iff.1 hyu
  have hsec : ∀ i, RegAt y (t i * g) := fun i => by
    have : t i ∈ Sec D₁ k := by rw [hS k]; exact subset_spanBy _ _ (ht i)
    exact hg.regularAt_iff.1 (this y)
  by_contra hne
  push_neg at hne
  apply (zeroAt_iff.1 ?_).2 hunit
  rw [Finset.sum_mul]
  refine Finset.sum_induction _ (ZeroAt y) (fun _ _ => ZeroAt.add) (zeroAt_zero y) fun i _ => ?_
  rw [_root_.mul_assoc]
  refine zeroAt_iff.2 ⟨(regAt_cst q y (r i)).mul (hsec i), fun hu => ?_⟩
  obtain ⟨b, hb, hbt⟩ := ht i
  apply hne k hk b hb
  show (k • D₁).GeneratesAt y (θ b)
  rw [hg.generatesAt_iff, hbt]
  exact unitAt_of_mul_right (regAt_cst q y (r i)) (hsec i) hu

end GlobalTheory.Desc
end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
open TensorProduct

namespace GlobalTheory.Desc.BCChart

def ev {T : Scheme.{0}} {K : Type} [CommRing K] (f : Sp K ⟶ T) (O : T.Opens) (h : ⊤ ≤ f ⁻¹ᵁ O) (u : Γ(T, O)) : K :=
  (Scheme.ΓSpecIso (CommRingCat.of K)).hom ((f.appLE O ⊤ h).hom u)

theorem ev_comp {T T' : Scheme.{0}} {K : Type} [CommRing K] (s : Sp K ⟶ T') (g : T' ⟶ T) {O : T.Opens}
    {O' : T'.Opens} (e : O' ≤ g ⁻¹ᵁ O) (h : ⊤ ≤ s ⁻¹ᵁ O') {g' : Sp K ⟶ T} (hg : s ≫ g = g')
    (h' : ⊤ ≤ g' ⁻¹ᵁ O) (u : Γ(T, O)) : ev g' O h' u = ev s O' h ((g.appLE O O' e).hom u) := by
  subst hg
  unfold ev
  congr 1
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

theorem appLE_top_top {A B : Scheme.{0}} (f : A ⟶ B) : f.appLE ⊤ ⊤ le_top = f.appTop := by
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  congr 1

theorem ev_spMap {T : Scheme.{0}} {A B : Type} [CommRing A] [CommRing B] (θ : A →+* B) (f : Sp A ⟶ T)
    (O : T.Opens) (h : ⊤ ≤ f ⁻¹ᵁ O) (h' : ⊤ ≤ (spMap θ ≫ f) ⁻¹ᵁ O) (u : Γ(T, O)) :
    ev (spMap θ ≫ f) O h' u = θ (ev f O h u) := by
  rw [ev_comp (spMap θ) f h le_top rfl]
  unfold ev
  rw [appLE_top_top, ← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality]
  rfl

theorem fromSpecStalk_top' {X : Scheme.{0}} (x : X) (U : X.Opens) (hx : x ∈ U) :
    ⊤ ≤ X.fromSpecStalk x ⁻¹ᵁ U := by
  intro z _
  have hz : X.fromSpecStalk x z ⤳ x := by
    have : X.fromSpecStalk x z ∈ Set.range (X.fromSpecStalk x) := ⟨z, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  exact hz.mem_open U.2 hx

theorem fromSpecStalk_appLE' {X : Scheme.{0}} (x : X) (U : X.Opens) (hx : x ∈ U) :
    (X.fromSpecStalk x).appLE U ⊤ (fromSpecStalk_top' x U hx) =
      X.presheaf.germ U x hx ≫ (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv := by
  rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hx]
  simp only [Category.assoc, ← Functor.map_comp]
  have e : ((homOfLE le_top).op ≫ (homOfLE (fromSpecStalk_top' x U hx)).op :
      Opposite.op (⊤ : (Spec (X.presheaf.stalk x)).Opens) ⟶ Opposite.op ⊤) = 𝟙 _ := rfl
  rw [e, CategoryTheory.Functor.map_id, Category.comp_id]

theorem fnOf_eq_ev {X : Scheme.{0}} [IsIntegral X] (O : X.Opens) (hO : genericPoint X ∈ O) (u : Γ(X, O)) :
    fnOf O hO u = ev (gp X) O (fromSpecStalk_top' _ O hO) u := by
  unfold ev gp
  rw [fromSpecStalk_appLE' (genericPoint X) O hO, CommRingCat.comp_apply]
  change _ = (Scheme.ΓSpecIso (X.presheaf.stalk (genericPoint X))).hom _
  rw [Iso.inv_hom_id_apply]
  rfl

theorem exists_tensor_fnOf : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] (ρ : R →+* R₁) (X Y V : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp R) (q : Y ⟶ Sp R₁) (i : V ⟶ Y) [IsOpenImmersion i] (φ : V ⟶ X) (θ : X.functionField →+* Y.functionField), IsPullback φ (i ≫ q) p (spMap ρ) → PFF i φ θ → ∀ (U : X.Opens), IsAffineOpen U → ∀ hg : genericPoint X ∈ U, letI := (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U).toAlgebra; letI := ρ.toAlgebra; ∃ β : Γ(X, U) ⊗[R] R₁ →+ Y.functionField, Function.Injective β ∧ (∀ b r, β (b ⊗ₜ[R] r) = θ (GlobalTheory.Cartier.fnOf U hg b) * GlobalTheory.Desc.cst q r) ∧ Set.range β = {v | ∀ z : V, φ z ∈ U → GlobalTheory.Cartier.RegAt (i z) v} := by
  intro R R₁ _ _ ρ X Y V _ _ p q i _ φ θ H hP U hU hg
  letI := (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U).toAlgebra
  letI := ρ.toAlgebra
  obtain ⟨l, hl1, hl2⟩ := hP
  let W : V.Opens := φ ⁻¹ᵁ U ⊓ (i ≫ q) ⁻¹ᵁ ⊤
  let O : Y.Opens := i ''ᵁ W
  have hmemW : ∀ z : V, z ∈ W ↔ φ z ∈ U := fun z => ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩
  have hmemO : ∀ y : Y, y ∈ O ↔ ∃ z : V, φ z ∈ U ∧ i z = y := by
    intro y
    constructor
    · rintro ⟨z, hz, rfl⟩; exact ⟨z, hz.1, rfl⟩
    · rintro ⟨z, hz, rfl⟩; exact ⟨z, (hmemW z).2 hz, rfl⟩
  let pt : Sp Y.functionField := IsLocalRing.closedPoint Y.functionField
  have hz1 : i (l pt) = genericPoint Y := by
    rw [← Scheme.Hom.comp_apply, hl1]
    exact Scheme.fromSpecStalk_closedPoint
  have hz2 : φ (l pt) = genericPoint X := by
    rw [← Scheme.Hom.comp_apply, hl2, Scheme.Hom.comp_apply]
    exact Scheme.fromSpecStalk_closedPoint (x := genericPoint X) ▸ congrArg _ (Subsingleton.elim _ _)
  have hO : genericPoint Y ∈ O := (hmemO _).2 ⟨l pt, hz2 ▸ hg, hz1⟩
  let e := ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.eTens p (i ≫ q) φ H U hU
  let j : Γ(V, W) →+* Γ(Y, O) := (i.appIso W).inv.hom
  have hj : ∀ s, j ((i.appIso W).hom.hom s) = s := fun s => Iso.hom_inv_id_apply _ _
  have hj' : ∀ s, (i.appIso W).hom.hom (j s) = s := fun s => Iso.inv_hom_id_apply _ _
  refine ⟨((fnOf O hO).comp (j.comp e.toRingHom)).toAddMonoidHom, ?_, ?_, ?_⟩
  · intro a b hab
    have h1 := congrArg (i.appIso W).hom.hom (fnOf_injective O hO hab)
    simp only [RingHom.comp_apply, hj'] at h1
    exact e.injective h1
  · intro b r
    have hlW : ⊤ ≤ l ⁻¹ᵁ W := by
      intro z _
      have hz : z = pt := Subsingleton.elim _ _
      subst hz
      exact (hmemW _).2 (hz2 ▸ hg)
    have hC : ∀ y : Γ(V, W), fnOf O hO (j y) = ev l W hlW y := by
      intro y
      rw [fnOf_eq_ev]
      refine (ev_comp l i (O := O) (O' := W) (i.preimage_image_eq W).ge hlW hl1 _ _).trans ?_
      congr 1
      rw [← CommRingCat.comp_apply, Scheme.Hom.appIso_inv_appLE]
      have : (homOfLE (le_refl W)).op = 𝟙 (Opposite.op W) := rfl
      erw [this, CategoryTheory.Functor.map_id]
      rfl
    have hX : ⊤ ≤ (spMap θ ≫ gp X) ⁻¹ᵁ U := fun z _ => fromSpecStalk_top' (genericPoint X) U hg (Set.mem_univ (spMap θ z))
    have hYq : ⊤ ≤ (gp Y ≫ q) ⁻¹ᵁ ⊤ := fun _ _ => trivial
    show fnOf O hO (j (e (b ⊗ₜ[R] r))) = _
    rw [ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.eTens_tmul, map_mul, map_mul, hC, hC]
    congr 1
    · rw [← ev_comp l φ inf_le_left hlW hl2 hX, ev_spMap θ (gp X) U (fromSpecStalk_top' _ U hg), ← fnOf_eq_ev]
    · unfold ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX cst
      rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, fnOf_eq_ev ⊤ trivial, ← appLE_top_top,
        ← ev_comp l (i ≫ q) le_top hlW (by rw [← Category.assoc, hl1]) hYq,
        ← ev_comp (gp Y) q le_top (fromSpecStalk_top' _ ⊤ trivial) rfl hYq]
  · ext v
    simp only [Set.mem_range, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨t, rfl⟩ z hz
      exact regAt_fnOf ((hmemO _).2 ⟨z, hz, rfl⟩) hO _
    · intro hv
      obtain ⟨s, hs⟩ := exists_fnOf_eq hO fun y hy => by
        obtain ⟨z, hz, rfl⟩ := (hmemO y).1 hy
        exact hv z hz
      refine ⟨e.symm ((i.appIso W).hom.hom s), ?_⟩
      show fnOf O hO (j (e (e.symm ((i.appIso W).hom.hom s)))) = v
      rw [RingEquiv.apply_symm_apply, hj, hs]

end GlobalTheory.Desc.BCChart
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc.Sat

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

theorem sp_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem sp_surj {A B : Type} [CommRing A] [CommRing B] (s : Sp B ⟶ Sp A) : ∃ u : A →+* B, spMap u = s :=
  ⟨(Spec.preimage s).hom, Spec.map_preimage s⟩

theorem isDominant_gp (X : Scheme.{0}) [IsIntegral X] : IsDominant (gp X) := by
  constructor
  have h : genericPoint X ∈ Set.range (gp X) :=
    ⟨closedPoint (X.presheaf.stalk (genericPoint X)), Scheme.fromSpecStalk_closedPoint⟩
  have h2 : Dense ({genericPoint X} : Set X) := by
    rw [dense_iff_closure_eq]; exact genericPoint_closure X
  exact h2.mono (Set.singleton_subset_iff.mpr h)

theorem pff_id {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] {φ : Y ⟶ X}
    {θ : X.functionField →+* Y.functionField} (h : PFF (𝟙 _) φ θ) : gp Y ≫ φ = spMap θ ≫ gp X := by
  obtain ⟨l, h1, h2⟩ := h
  rw [Category.comp_id] at h1
  rw [← h1, h2]

theorem transfer (σ : Setup) (E : Emb σ) (hC : σ.Common) (x x' : Sp σ.R) (Ω : Type) [Field Ω]
    (s : Sp Ω ⟶ Sp (σ.C x).R) (s' : Sp Ω ⟶ Sp (σ.C x').R) (o : Sp Ω) (hs' : s' o = closedPoint (σ.C x').R)
    (h : s ≫ spMap (σ.ρ x) = s' ≫ spMap (σ.ρ x')) :
    (∀ t : Sp Ω ⟶ (σ.C x).G.left, t ≫ (σ.C x).G.hom = s →
      ∃ t' : Sp Ω ⟶ (σ.C x').G.left, t' ≫ (σ.C x').G.hom = s' ∧ t' ≫ E.emb x' = t ≫ E.emb x) ∧
    (∀ t' : Sp Ω ⟶ (σ.C x').G.left, t' ≫ (σ.C x').G.hom = s' →
      ∃ t : Sp Ω ⟶ (σ.C x).G.left, t ≫ (σ.C x).G.hom = s ∧ t ≫ E.emb x = t' ≫ E.emb x') := by
  obtain ⟨u, rfl⟩ := sp_surj s
  obtain ⟨u', rfl⟩ := sp_surj s'
  have hk : RingHom.ker u' = maximalIdeal _ := by
    obtain rfl : o = closedPoint Ω := Subsingleton.elim (α := PrimeSpectrum Ω) _ _
    have h1 : (maximalIdeal Ω).comap u' = maximalIdeal _ := congrArg PrimeSpectrum.asIdeal hs'
    rw [← h1, maximalIdeal_eq_bot]; rfl
  rw [sp_comp, sp_comp] at h
  obtain ⟨R', _, _, _, a, b, v, H, _, _, πa, πb, θa, θb, -, -, hab, -, hva, hvb, -, -, ⟨pa, -⟩, ⟨pb, -⟩, fa, fb, hθ⟩ :=
    hC x x' Ω u u' hk (sp_inj h)
  have key : πa ≫ E.emb x = πb ≫ E.emb x' := by
    haveI := E.sep
    haveI := isDominant_gp H.left
    obtain ⟨w, -⟩ := E.openIn x
    obtain ⟨w', -⟩ := E.openIn x'
    refine ext_of_isDominant_of_isSeparated E.p ?_ (gp H.left) ?_
    · rw [Category.assoc, Category.assoc, w, w', pa.w_assoc, pb.w_assoc, sp_comp, sp_comp, hab]
    · rw [← Category.assoc, ← Category.assoc, pff_id fa, pff_id fb, Category.assoc, Category.assoc,
        pff_id (E.ff x), pff_id (E.ff x'), ← Category.assoc, ← Category.assoc, sp_comp, sp_comp,
        ← RingHom.comp_assoc, ← RingHom.comp_assoc, hθ]
  have ea : spMap v ≫ spMap a = spMap u := by rw [sp_comp, hva]
  have eb : spMap v ≫ spMap b = spMap u' := by rw [sp_comp, hvb]
  constructor
  · intro t ht
    refine ⟨pa.lift t (spMap v) (ht.trans ea.symm) ≫ πb, ?_, ?_⟩
    · rw [Category.assoc, pb.w, pa.lift_snd_assoc, eb]
    · rw [Category.assoc, ← key, pa.lift_fst_assoc]
  · intro t ht
    refine ⟨pb.lift t (spMap v) (ht.trans eb.symm) ≫ πa, ?_, ?_⟩
    · rw [Category.assoc, pa.w, pb.lift_snd_assoc, ea]
    · rw [Category.assoc, key, pb.lift_fst_assoc]

theorem exists_field_pt {X Y S : Scheme.{0}} (f : X ⟶ S) (g : Y ⟶ S) (x : X) (y : Y) (h : f x = g y) :
    ∃ (Ω : Type) (_ : Field Ω) (s : Sp Ω ⟶ X) (t : Sp Ω ⟶ Y) (o : Sp Ω), s ≫ f = t ≫ g ∧ s o = x ∧ t o = y := by
  obtain ⟨z, h1, h2⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := g) x y h
  let r : Sp ((pullback f g).residueField z) ⟶ pullback f g := (pullback f g).fromSpecResidueField z
  let o : Sp ((pullback f g).residueField z) := closedPoint _
  have hr : r o = z := Scheme.fromSpecResidueField_apply z _
  refine ⟨(pullback f g).residueField z, inferInstance, r ≫ pullback.fst f g, r ≫ pullback.snd f g, o, ?_, ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, pullback.condition]
  · rw [Scheme.Hom.comp_apply, hr, h1]
  · rw [Scheme.Hom.comp_apply, hr, h2]

end GlobalTheory.Desc.Sat

namespace GlobalTheory.Desc


open Sat in
theorem Emb.fst_mem_U_iff : ∀ (σ : Setup) (E : Emb σ), σ.Common → ∀ (x : Sp σ.R) (w : ↥(Limits.pullback E.p (spMap (σ.ρ x)))), (Limits.pullback.fst E.p (spMap (σ.ρ x)) w ∈ E.U ↔ ∃ y : (σ.C x).G.left, E.emb x y = Limits.pullback.fst E.p (spMap (σ.ρ x)) w ∧ (σ.C x).G.hom y = Limits.pullback.snd E.p (spMap (σ.ρ x)) w) := by
  intro σ E hC x w
  constructor
  · rintro ⟨x', y', hy', e⟩
    obtain ⟨Ω, _, s, t', o, hst, hs, ht⟩ := exists_field_pt (pullback.fst E.p (spMap (σ.ρ x))) (E.emb x') w y' e.symm
    obtain ⟨w', -⟩ := E.openIn x'
    obtain ⟨t, h1, h2⟩ := (transfer σ E hC x x' Ω (s ≫ pullback.snd _ _) (t' ≫ (σ.C x').G.hom) o
      (by rw [Scheme.Hom.comp_apply, ht]; exact hy')
      (by rw [Category.assoc, Category.assoc, ← pullback.condition, ← w', reassoc_of% hst])).2 t' rfl
    refine ⟨t o, ?_, ?_⟩
    · rw [← Scheme.Hom.comp_apply, h2, Scheme.Hom.comp_apply, ht, e]
    · rw [← Scheme.Hom.comp_apply, h1, Scheme.Hom.comp_apply, hs]
  · rintro ⟨y, e, -⟩
    rw [← e]
    let x' : Sp σ.R := ((σ.C x).G.hom ≫ spMap (σ.ρ x)) y
    have hx' : spMap (σ.ρ x') (closedPoint _) = x' := by rw [← σ.hρ]; exact (σ.C x').centre
    obtain ⟨Ω, _, t, s', o, hst, ht, hs⟩ :=
      exists_field_pt ((σ.C x).G.hom ≫ spMap (σ.ρ x)) (spMap (σ.ρ x')) y (closedPoint _) hx'.symm
    obtain ⟨t', h1, h2⟩ := (transfer σ E hC x x' Ω (t ≫ (σ.C x).G.hom) s' o hs
      (by rw [Category.assoc, hst])).1 t rfl
    refine ⟨x', t' o, ?_, ?_⟩
    · rw [← Scheme.Hom.comp_apply, h1, hs]
    · rw [← Scheme.Hom.comp_apply, h2, Scheme.Hom.comp_apply, ht]

end GlobalTheory.Desc
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem exists_ringHom_fnOf_eq {Y P : Scheme.{0}} [IsIntegral Y] [IsIntegral P] {U : Y.Opens}
    (hU : genericPoint Y ∈ U) {V : P.Opens} (hVη : genericPoint P ∈ V)
    (φ : P.functionField →+* Y.functionField) (h : ∀ s : Γ(P, V), ∀ y ∈ U, RegAt y (φ (fnOf V hVη s))) :
    ∃ ψ : Γ(P, V) →+* Γ(Y, U), ∀ s, fnOf U hU (ψ s) = φ (fnOf V hVη s) := by
  choose t ht using fun s => exists_fnOf_eq hU (h s)
  refine ⟨⟨⟨⟨t, ?_⟩, fun a b => ?_⟩, ?_, fun a b => ?_⟩, ht⟩ <;> apply fnOf_injective U hU
  · rw [ht, map_one, map_one, map_one]
  · rw [map_mul, ht, ht, ht, map_mul, map_mul]
  · exact (ht 0).trans (by rw [map_zero, map_zero, map_zero])
  · exact (ht (a + b)).trans (((congrArg φ (map_add _ a b)).trans (map_add φ _ _)).trans
      ((congrArg₂ (· + ·) (ht a) (ht b)).symm.trans (map_add (fnOf U hU) (t a) (t b)).symm))


set_option backward.isDefEq.respectTransparency false in
theorem exists_hom_of_regAt_fnOf : ∀ (Y P : Scheme.{0}) [IsIntegral Y] [IsIntegral P] (U : Y.Opens), genericPoint Y ∈ U → ∀ (V : P.Opens), IsAffineOpen V → ∀ (hVη : genericPoint P ∈ V) (φ : P.functionField →+* Y.functionField), (∀ s : Γ(P, V), ∀ y ∈ U, RegAt y (φ (fnOf V hVη s))) → ∃ f : U.toScheme ⟶ P, (∀ y : U.toScheme, f y ∈ V) ∧ ∀ l : Sp Y.functionField ⟶ U.toScheme, l ≫ U.ι = gp Y → l ≫ f = spMap φ ≫ gp P := by
  intro Y P _ _ U hU V hV hVη φ h
  obtain ⟨ψ, hψ⟩ := exists_ringHom_fnOf_eq hU hVη φ h
  refine ⟨U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ) ≫ hV.fromSpec, fun y => ?_, fun l hl => ?_⟩
  · rw [← Category.assoc, Scheme.Hom.comp_apply]
    change _ ∈ (V : Set P)
    rw [← hV.range_fromSpec]
    exact ⟨_, rfl⟩
  · obtain rfl : l = U.fromSpecStalkOfMem (genericPoint Y) hU := by
      rw [← cancel_mono U.ι, hl]
      exact (Scheme.Opens.fromSpecStalkOfMem_ι U _ hU).symm
    have e : CommRingCat.ofHom ψ ≫ Y.presheaf.germ U (genericPoint Y) hU =
        P.presheaf.germ V (genericPoint P) hVη ≫ CommRingCat.ofHom φ := by
      ext s
      exact hψ s
    have e₁ := Scheme.Opens.fromSpecStalkOfMem_toSpecΓ_assoc U (genericPoint Y) hU
      (Spec.map (CommRingCat.ofHom ψ) ≫ hV.fromSpec)
    refine e₁.trans ?_
    rw [← Spec.map_comp_assoc]
    refine (congrArg (fun z => Spec.map z ≫ hV.fromSpec) e).trans ?_
    rw [gp, ← hV.fromSpecStalk_eq_fromSpecStalk hVη, IsAffineOpen.fromSpecStalk, Spec.map_comp_assoc]

end GlobalTheory.Desc
end
end
