module

public import Development.EtaleCohomology.EtaleSheaves.Bundle070
public import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.EffectiveEpi.Comp
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

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.StandardEtaleChartsIdempotentGluing LateralTheory.E.ChartsGeom_vpaPf
  LateralTheory.E.GeometricData

namespace LateralTheory.E.EmbedNonDeg₂

theorem germ_res {Z : Scheme.{0}} [IsIntegral Z] (U W : Z.Opens) (h : W ≤ U) [Nonempty U] [Nonempty W]
    (s : Γ(Z, U)) : Z.germToFunctionField W (Z.presheaf.map (homOfLE h).op s) = Z.germToFunctionField U s := by
  simp only [Scheme.germToFunctionField]
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

theorem rA_res {A : Type} [CommRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) {W X : Z.Opens}
    (h : W ≤ X) (a : A) : Z.presheaf.map (homOfLE h).op (rA p X a) = rA p W a := by
  have e := Scheme.Hom.appLE_map p (U := ⊤) (V := X) le_top (homOfLE h).op
  simp only [rA, RingHom.comp_apply]
  exact congrArg (fun f => f.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)) e

theorem int_adjoin {A S K : Type} [CommRing A] [CommRing S] [Field K] [Algebra A K]
    (f : Polynomial A →+* S) (hf : f.IsIntegral) (φ : S →+* K) (t : K)
    (hc : ∀ a, φ (f (Polynomial.C a)) = algebraMap A K a) (hX : φ (f Polynomial.X) = t) (x : S) :
    IsIntegral (Algebra.adjoin A {t}) (φ x) := by
  obtain ⟨P, hm, hP⟩ := hf x
  let ψ : Polynomial A →+* Algebra.adjoin A {t} :=
    (Polynomial.aeval (⟨t, Algebra.self_mem_adjoin_singleton A t⟩ : Algebra.adjoin A {t})).toRingHom
  have key : (algebraMap (Algebra.adjoin A {t}) K).comp ψ = φ.comp f := by
    apply Polynomial.ringHom_ext
    · intro a; simp [ψ, hc]
    · simp [ψ, hX]
  refine ⟨P.map ψ, hm.map ψ, ?_⟩
  rw [Polynomial.eval₂_map, key, ← Polynomial.hom_eval₂, hP, map_zero]

theorem int_A {A S K : Type} [CommRing A] [CommRing S] [Field K] [Algebra A K]
    (f : A →+* S) (hf : f.IsIntegral) (φ : S →+* K) (hc : ∀ a, φ (f a) = algebraMap A K a) (x : S) :
    IsIntegral A (φ x) := by
  obtain ⟨P, hm, hP⟩ := hf x
  refine ⟨P, hm, ?_⟩
  have : algebraMap A K = φ.comp f := RingHom.ext fun a => (hc a).symm
  rw [this, ← Polynomial.hom_eval₂, hP, map_zero]

theorem range_loc {A K : Type} [CommRing A] [Field K] [Algebra A K] {Z : Scheme.{0}} {U W : Z.Opens}
    (hU : IsAffineOpen U) (s : Γ(Z, U)) (hW : Z.basicOpen s = W) (hle : W ≤ U)
    (φU : Γ(Z, U) →+* K) (φW : Γ(Z, W) →+* K)
    (hres : ∀ x, φW (Z.presheaf.map (homOfLE hle).op x) = φU x) (B : Subalgebra A K)
    (hB : ∀ k, k ∈ B ↔ ∃ x, φU x = k) (hs : φU s ≠ 0) (hinv : (φU s)⁻¹ ∈ φW.range) :
    φW.range = (AdjoinInv B (φU s)).toSubring := by
  subst hW
  have := hU.isLocalization_basicOpen s
  ext k; constructor
  · intro hk0
    obtain ⟨z, rfl⟩ := hk0
    obtain ⟨⟨x, ⟨_, n, rfl⟩⟩, e1⟩ := IsLocalization.surj (Submonoid.powers s) z
    have e2 := congrArg φW e1
    rw [map_mul] at e2
    change φW z * φW (Z.presheaf.map (homOfLE hle).op (s ^ n)) = φW (Z.presheaf.map (homOfLE hle).op x) at e2
    rw [hres, hres, map_pow] at e2
    have e3 : φW z = φU x * ((φU s)⁻¹) ^ n := by
      rw [← e2, mul_assoc, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hs), mul_one]
    change φW z ∈ AdjoinInv B (φU s)
    rw [e3]
    refine Subalgebra.mul_mem _ ?_ (Subalgebra.pow_mem _ ?_ _)
    · exact Algebra.subset_adjoin (Or.inl ((hB _).mpr ⟨x, rfl⟩))
    · exact Algebra.subset_adjoin (Or.inr rfl)
  · intro hk
    have hBW : ∀ k ∈ B, k ∈ φW.rangeS := by
      intro k hk; obtain ⟨x, rfl⟩ := (hB k).mp hk
      exact ⟨_, hres x⟩
    let R : Subalgebra A K :=
      { toSubsemiring := φW.rangeS, algebraMap_mem' := fun a => hBW _ (B.algebraMap_mem a) }
    have hle' : AdjoinInv B (φU s) ≤ R := by
      rw [AdjoinInv, Algebra.adjoin_le_iff]
      rintro k (hk | hk)
      · exact hBW k hk
      · rw [Set.mem_singleton_iff.mp hk]; obtain ⟨y, hy⟩ := hinv; exact ⟨y, hy⟩
    obtain ⟨y, hy⟩ := hle' hk
    exact ⟨y, hy⟩

theorem EmbedNonDeg_of : EmbedNonDeg := by
  intro A _ _ Z p hI hTop hN
  obtain ⟨U, V, s, s', hU, hV, hUV, hsU, hsV, ⟨z, hz⟩, hss, hiU, hiV⟩ := hN
  have hzU : z ∈ U := (inf_le_left : U ⊓ V ≤ U) hz
  have hzV : z ∈ V := (inf_le_right : U ⊓ V ≤ V) hz
  have : Nonempty U := ⟨⟨z, hzU⟩⟩
  have : Nonempty V := ⟨⟨z, hzV⟩⟩
  have : Nonempty (U ⊓ V : Z.Opens) := ⟨⟨z, hz⟩⟩
  have : Nonempty (U ⊔ V : Z.Opens) := ⟨⟨z, (le_sup_left : U ≤ U ⊔ V) hzU⟩⟩
  let φU : Γ(Z, U) →+* Z.functionField := (Z.germToFunctionField U).hom
  let φV : Γ(Z, V) →+* Z.functionField := (Z.germToFunctionField V).hom
  let φW : Γ(Z, U ⊓ V) →+* Z.functionField := (Z.germToFunctionField (U ⊓ V)).hom
  let φT : Γ(Z, U ⊔ V) →+* Z.functionField := (Z.germToFunctionField (U ⊔ V)).hom
  let _ : Algebra A Z.functionField := (φU.comp (rA p U)).toAlgebra
  have hcU : ∀ a, φU (rA p U a) = algebraMap A Z.functionField a := fun a => rfl
  have rL : ∀ x, φW (Z.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op x) = φU x :=
    fun x => germ_res U (U ⊓ V) inf_le_left x
  have rR : ∀ x, φW (Z.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op x) = φV x :=
    fun x => germ_res V (U ⊓ V) inf_le_right x
  have hcV : ∀ a, φV (rA p V a) = algebraMap A Z.functionField a := by
    intro a
    rw [← hcU a, ← rL, ← rR, rA_res, rA_res]
  have hmul : φU s * φV s' = 1 := by
    have h := congrArg φW hss
    rw [map_mul, map_one, rL, rR] at h
    exact h
  have ht : φU s ≠ 0 := left_ne_zero_of_mul_eq_one hmul
  have hs0' : φV s' ≠ 0 := right_ne_zero_of_mul_eq_one hmul
  have hs'inv : φV s' = (φU s)⁻¹ := eq_inv_of_mul_eq_one_right hmul
  let B : Subalgebra A Z.functionField :=
    { toSubsemiring := φU.rangeS, algebraMap_mem' := fun a => ⟨rA p U a, hcU a⟩ }
  let C : Subalgebra A Z.functionField :=
    { toSubsemiring := φV.rangeS, algebraMap_mem' := fun a => ⟨rA p V a, hcV a⟩ }
  have hWB : φW.range = (AdjoinInv B (φU s)).toSubring :=
    range_loc hU s hsU inf_le_left φU φW rL B (fun _ => Iff.rfl) ht ⟨_, (rR s').trans hs'inv⟩
  have hWC : φW.range = (AdjoinInv C (φV s')).toSubring :=
    range_loc hV s' hsV inf_le_right φV φW rR C (fun _ => Iff.rfl) hs0'
      ⟨_, (rL s).trans (by rw [hs'inv, inv_inv])⟩
  have hglue : AdjoinInv B (φU s) = Algebra.adjoin A ((C : Set Z.functionField) ∪ {φU s}) := by
    have h2 := Subalgebra.toSubring_injective (hWB.symm.trans hWC)
    rw [h2, AdjoinInv, hs'inv, inv_inv]
  have hTop' : (rA p (U ⊔ V)).IsIntegral := by rw [hUV]; exact hTop
  have hcT : ∀ a, φT (rA p (U ⊔ V) a) = algebraMap A Z.functionField a := by
    intro a
    rw [← hcU a, ← rA_res p (le_sup_left : U ≤ U ⊔ V) a]
    exact (germ_res (U ⊔ V) U le_sup_left _).symm
  have hBC : ∀ x ∈ B, x ∈ C → IsIntegral A x := by
    intro x hxB hxC
    obtain ⟨u, hu⟩ := hxB
    obtain ⟨v, hv⟩ := hxC
    have heq : Z.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op u =
        Z.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op v :=
      Z.germToFunctionField_injective (U ⊓ V) (((rL u).trans (hu.trans hv.symm)).trans (rR v).symm)
    let g := (Z.sheaf.objSupIsoProdEqLocus U V).inv ⟨(u, v), heq⟩
    have hg : Z.presheaf.map (homOfLE (le_sup_left : U ≤ U ⊔ V)).op g = u :=
      Z.sheaf.objSupIsoProdEqLocus_inv_fst U V _
    have hx : x = φT g := by
      rw [← hu, ← hg]; exact germ_res (U ⊔ V) U le_sup_left g
    rw [hx]
    exact int_A (rA p (U ⊔ V)) hTop' φT hcT g
  have intB : ∀ b ∈ B, IsIntegral (Algebra.adjoin A {φU s}) b := by
    intro b hb
    obtain ⟨x, rfl⟩ := hb
    exact int_adjoin (Polynomial.eval₂RingHom (rA p U) s) hiU φU (φU s)
      (fun a => by rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]; exact hcU a)
      (by rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]) x
  have intC : ∀ c ∈ C, IsIntegral (Algebra.adjoin A {(φU s)⁻¹}) c := by
    intro c hc
    obtain ⟨x, rfl⟩ := hc
    exact int_adjoin (Polynomial.eval₂RingHom (rA p V) s') hiV φV (φU s)⁻¹
      (fun a => by rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]; exact hcV a)
      (by rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]; exact hs'inv) x
  refine ⟨Z.functionField, inferInstance, inferInstance, B, C, φU s,
    ⟨ht, ⟨s, rfl⟩, ⟨s', hs'inv⟩, intB, intC, hglue⟩, hBC, ?_⟩
  exact ⟨U, V, φU, φV, φW, hU, hV, hsU ▸ hU.basicOpen s, hUV,
    Z.germToFunctionField_injective U, Z.germToFunctionField_injective V,
    Z.germToFunctionField_injective (U ⊓ V), SetLike.ext fun _ => Iff.rfl, SetLike.ext fun _ => Iff.rfl, hWB,
    rL, rR, fun a => rfl, hcV⟩

end LateralTheory.E.EmbedNonDeg₂
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.GeometricData

namespace LateralTheory.E.ProjectiveLineCharts₂

def ProjectiveLineTwoAffineChartsPolynomialGenerated : Prop :=
  ∃ (U V : P1.Opens) (s : Γ(P1, U)) (s' : Γ(P1, V)), IsAffineOpen U ∧ IsAffineOpen V ∧ U ⊔ V = ⊤ ∧
    P1.basicOpen s = U ⊓ V ∧ P1.basicOpen s' = U ⊓ V ∧
    P1.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op s *
      P1.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op s' = 1 ∧
    Function.Surjective (Polynomial.eval₂RingHom (Int.castRingHom Γ(P1, U)) s) ∧
    Function.Surjective (Polynomial.eval₂RingHom (Int.castRingHom Γ(P1, V)) s')

def ChartBC : Prop := ∀ (A : Type) [CommRing A] {L : Scheme.{0}} (l : L ⟶ Spec (CommRingCat.of A)) (f : L ⟶ P1),
  IsPullback f l (terminal.from P1) (terminal.from _) → ∀ (W : P1.Opens) (x : Γ(P1, W)), IsAffineOpen W →
  Function.Surjective (Polynomial.eval₂RingHom (Int.castRingHom Γ(P1, W)) x) →
  IsAffineOpen (f ⁻¹ᵁ W) ∧ Function.Surjective (Polynomial.eval₂RingHom (rA l (f ⁻¹ᵁ W)) (f.app W x))

theorem rA_comp {A : Type} [CommRing A] {Z L : Scheme.{0}} (u : Z ⟶ L) (l : L ⟶ Spec (CommRingCat.of A))
    (W : L.Opens) : rA (u ≫ l) (u ⁻¹ᵁ W) = (u.app W).hom.comp (rA l W) := by
  simp only [rA]
  rw [← Scheme.Hom.appLE_comp_appLE u l ⊤ W (u ⁻¹ᵁ W) le_top le_rfl, u.appLE_eq_app]
  rfl

theorem res_app {X Y : Scheme.{0}} (g : X ⟶ Y) {W W' : Y.Opens} (h : W' ≤ W) (x : Γ(Y, W)) :
    X.presheaf.map (homOfLE (g.preimage_mono h)).op (g.app W x) = g.app W' (Y.presheaf.map (homOfLE h).op x) := by
  have := congrArg (fun φ => φ.hom x) (g.naturality (homOfLE h).op)
  exact this.symm

theorem transport {X Y : Scheme.{0}} (g : X ⟶ Y) {U V : Y.Opens} (s : Γ(Y, U)) (s' : Γ(Y, V))
    (h1 : U ⊔ V = ⊤) (h2 : Y.basicOpen s = U ⊓ V) (h3 : Y.basicOpen s' = U ⊓ V)
    (h4 : Y.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op s *
      Y.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op s' = 1) :
    g ⁻¹ᵁ U ⊔ g ⁻¹ᵁ V = ⊤ ∧ X.basicOpen (g.app U s) = g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V ∧
    X.basicOpen (g.app V s') = g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V ∧
    X.presheaf.map (homOfLE (inf_le_left : g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V ≤ g ⁻¹ᵁ U)).op (g.app U s) *
      X.presheaf.map (homOfLE (inf_le_right : g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V ≤ g ⁻¹ᵁ V)).op (g.app V s') = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Scheme.Hom.preimage_sup, h1]; rfl
  · rw [← Scheme.preimage_basicOpen, h2]; rfl
  · rw [← Scheme.preimage_basicOpen, h3]; rfl
  · erw [res_app g inf_le_left s, res_app g inf_le_right s', ← map_mul, h4]
    exact map_one _

theorem LineOpens_of (hP : ProjectiveLineTwoAffineChartsPolynomialGenerated) (hB : ChartBC) : LineOpens := by
  intro A _ _ Z p hIL hZ
  obtain ⟨L, u, l, hu, ⟨_, f, hf⟩, rfl⟩ := hIL
  obtain ⟨U0, V0, x, y, hU0, hV0, h1, h2, h3, h4, hsx, hsy⟩ := hP
  obtain ⟨hU1, hsU⟩ := hB A l f hf U0 x hU0 hsx
  obtain ⟨hV1, hsV⟩ := hB A l f hf V0 y hV0 hsy
  obtain ⟨k1, k2, k3, k4⟩ := transport f x y h1 h2 h3 h4
  obtain ⟨m1, m2, m3, m4⟩ := transport u _ _ k1 k2 k3 k4
  have hUa : IsAffineOpen (u ⁻¹ᵁ (f ⁻¹ᵁ U0)) := hU1.preimage u
  have hVa : IsAffineOpen (u ⁻¹ᵁ (f ⁻¹ᵁ V0)) := hV1.preimage u
  have hint : ∀ (W : L.Opens) (z : Γ(L, W)), IsAffineOpen W →
      Function.Surjective (Polynomial.eval₂RingHom (rA l W) z) →
      (Polynomial.eval₂RingHom (rA (u ≫ l) (u ⁻¹ᵁ W)) (u.app W z)).IsIntegral := by
    intro W z hW hs
    have he : Polynomial.eval₂RingHom (rA (u ≫ l) (u ⁻¹ᵁ W)) (u.app W z) =
        (u.app W).hom.comp (Polynomial.eval₂RingHom (rA l W) z) := by
      apply Polynomial.ringHom_ext
      · intro a; simp [rA_comp]
      · simp
    rw [he]
    exact RingHom.IsIntegral.trans _ _ (RingHom.isIntegral_of_surjective _ hs) (u.isIntegral_app W hW)
  by_cases hne : ((u ⁻¹ᵁ (f ⁻¹ᵁ U0) ⊓ u ⁻¹ᵁ (f ⁻¹ᵁ V0) : Z.Opens) : Set Z).Nonempty
  · exact Or.inr ⟨_, _, _, _, hUa, hVa, m1, m2, m3, hne, m4, hint _ _ hU1 hsU, hint _ _ hV1 hsV⟩
  · left
    have : IsIntegral Z := hZ.1
    have hUV : ¬ (((u ⁻¹ᵁ (f ⁻¹ᵁ U0) : Z.Opens) : Set Z).Nonempty ∧
        ((u ⁻¹ᵁ (f ⁻¹ᵁ V0) : Z.Opens) : Set Z).Nonempty) := by
      rintro ⟨a, b⟩
      exact hne (nonempty_preirreducible_inter (u ⁻¹ᵁ (f ⁻¹ᵁ U0)).isOpen (u ⁻¹ᵁ (f ⁻¹ᵁ V0)).isOpen a b)
    rcases not_and_or.mp hUV with h | h
    · have : u ⁻¹ᵁ (f ⁻¹ᵁ V0) = ⊤ := by
        rw [eq_top_iff]; intro z _
        have hz : z ∈ u ⁻¹ᵁ (f ⁻¹ᵁ U0) ⊔ u ⁻¹ᵁ (f ⁻¹ᵁ V0) := m1 ▸ trivial
        rcases (TopologicalSpace.Opens.mem_sup.mp hz) with hz | hz
        · exact absurd ⟨z, hz⟩ h
        · exact hz
      exact this ▸ hVa
    · have : u ⁻¹ᵁ (f ⁻¹ᵁ U0) = ⊤ := by
        rw [eq_top_iff]; intro z _
        have hz : z ∈ u ⁻¹ᵁ (f ⁻¹ᵁ U0) ⊔ u ⁻¹ᵁ (f ⁻¹ᵁ V0) := m1 ▸ trivial
        rcases (TopologicalSpace.Opens.mem_sup.mp hz) with hz | hz
        · exact hz
        · exact absurd ⟨z, hz⟩ h
      exact this ▸ hUa

end LateralTheory.E.ProjectiveLineCharts₂
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC
open CochainComplex.HomComplex

namespace LateralTheory.E.TruncBijPf

section General
universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C] {K K' L : CochainComplex C ℤ}

def preC (g : K ⟶ K') {j : ℤ} (z : Cochain K' L j) : Cochain K L j := (Cochain.ofHom g).comp z (zero_add j)

theorem preC_v (g : K ⟶ K') {j : ℤ} (z : Cochain K' L j) (p q : ℤ) (h : p + j = q) :
    (preC g z).v p q h = g.f p ≫ z.v p q h := by
  simp [preC]

theorem δ_preC (g : K ⟶ K') {j : ℤ} (z : Cochain K' L j) (k : ℤ) : δ j k (preC g z) = preC g (δ j k z) :=
  δ_ofHom_comp g z k

theorem preC_zero (g : K ⟶ K') (j : ℤ) : preC g (0 : Cochain K' L j) = 0 := by
  simp [preC]

theorem preC_inj (g : K ⟶ K') (n : ℤ) (hg : ∀ p : ℤ, -(n + 1) ≤ p → IsIso (g.f p))
    (hL : ∀ q : ℤ, q < 0 → IsZero (L.X q)) {j : ℤ} (hj : j ≤ n + 1) {x y : Cochain K' L j}
    (h : preC g x = preC g y) : x = y := by
  ext p q hpq
  by_cases hq : q < 0
  · exact (hL q hq).eq_of_tgt _ _
  · have := hg p (by omega)
    have h' := congrArg (fun z : Cochain K L j => z.v p q hpq) h
    simp only [preC_v] at h'
    exact (cancel_epi (g.f p)).1 h'

theorem preC_surj (g : K ⟶ K') (n : ℤ) (hg : ∀ p : ℤ, -(n + 1) ≤ p → IsIso (g.f p))
    (hL : ∀ q : ℤ, q < 0 → IsZero (L.X q)) {j : ℤ} (hj : j ≤ n + 1) (y : Cochain K L j) :
    ∃ x : Cochain K' L j, preC g x = y := by
  refine ⟨Cochain.mk fun p q hpq =>
    if h : -(n + 1) ≤ p then (haveI := hg p h; inv (g.f p)) ≫ y.v p q hpq else 0, ?_⟩
  ext p q hpq
  by_cases hq : q < 0
  · exact (hL q hq).eq_of_tgt _ _
  · have hp : -(n + 1) ≤ p := by omega
    rw [preC_v, Cochain.mk_v, dite_eq_left hp, IsIso.hom_inv_id_assoc]

end General

theorem res_isZero (R : Type) [CommRing R] (F : Shv R) (q : ℤ) (hq : q < 0) : IsZero ((res R F).X q) :=
  CochainComplex.isZero_of_isStrictlyGE (injectiveResolution F).cochainComplex 0 q hq

theorem pull_mk (R : Type) [CommRing R] (F : Shv R) {K K' : Cx R} (g : K ⟶ K') (m : ℤ) (x : Cocycle K' (res R F) m) :
    ∃ y : Cocycle K (res R F) m, HK.pull R g F m (CohomologyClass.mk x) = CohomologyClass.mk y ∧
      (y : Cochain K (res R F) m) = preC g (x : Cochain K' (res R F) m) :=
  ⟨_, rfl, rfl⟩

end LateralTheory.E.TruncBijPf

open LateralTheory.E.TruncBijPf in
theorem LateralTheory.E.TruncPf.TruncBij_of : LateralTheory.E.TruncPf.TruncBij := by
  intro R _ F K K' g n hg m hm
  have hL := res_isZero R F
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨x, rfl⟩ := x.mk_surjective
    obtain ⟨y, hy, hy'⟩ := pull_mk R F g m x
    rw [hy, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (m - 1) (by omega)] at hx
    obtain ⟨β, hβ⟩ := hx
    obtain ⟨β', rfl⟩ := preC_surj g n hg hL (by omega) β
    rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (m - 1) (by omega)]
    refine ⟨β', preC_inj g n hg hL (by omega) ?_⟩
    rw [← δ_preC, hβ, hy']
  · intro y
    obtain ⟨y, rfl⟩ := y.mk_surjective
    obtain ⟨x, hx⟩ := preC_surj g n hg hL (j := m) (by omega) (y : Cochain K (res R F) m)
    have hδ : δ m (m + 1) x = 0 := by
      apply preC_inj g n hg hL (by omega)
      rw [← δ_preC, hx, preC_zero, Cocycle.δ_eq_zero]
    obtain ⟨y', hy, hy'⟩ := pull_mk R F g m (Cocycle.mk x (m + 1) rfl hδ)
    refine ⟨_, hy.trans (congrArg CohomologyClass.mk (Cocycle.ext ?_))⟩
    rw [hy', ← hx]
    rfl
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.SimplicialPieceRelations SimplicialObject SimplicialObject.Augmented

namespace LateralTheory.E.SimplicialPieceDiscrete

variable (R : Type) [CommRing R]

def aug (X : PSh) : SimplicialObject.Augmented (Shv R) where
  left := ((SimplicialObject.whiskering _ _).obj (free R)).obj (disc.obj X)
  right := (free R).obj X
  hom := { app := fun _ => 𝟙 _, naturality := by intros; (try simp); (try rfl) }

def augMap {X Y : PSh} (f : X ⟶ Y) : aug R X ⟶ aug R Y where
  left := ((SimplicialObject.whiskering _ _).obj (free R)).map (disc.map f)
  right := (free R).map f
  w := by
    apply NatTrans.ext; funext n; exact (Category.comp_id _).trans (Category.id_comp _).symm

def ed (X : PSh) : ExtraDegeneracy (aug R X) where
  s' := 𝟙 _
  s := fun _ => 𝟙 _
  s'_comp_ε := by simp [aug] <;> first | rfl | exact Category.id_comp _ | exact Category.comp_id _
  s₀_comp_δ₁ := by simp [aug, SimplicialObject.δ] <;> first | rfl | exact Category.id_comp _ | exact Category.comp_id _
  s_comp_δ₀ := by intro n; simp [aug, SimplicialObject.δ] <;> first | rfl | exact Category.id_comp _ | exact Category.comp_id _
  s_comp_δ := by intro n i; simp [aug, SimplicialObject.δ] <;> first | rfl | exact Category.id_comp _ | exact Category.comp_id _
  s_comp_σ := by intro n i; simp [aug, SimplicialObject.σ] <;> first | rfl | exact Category.id_comp _ | exact Category.comp_id _

variable {R}

def hext {K L : ChainComplex (Shv R) ℕ} (h : HomotopyEquiv K L) :
    HomotopyEquiv (K.extend ComplexShape.embeddingDownNat) (L.extend ComplexShape.embeddingDownNat) where
  hom := HomologicalComplex.extendMap h.hom _
  inv := HomologicalComplex.extendMap h.inv _
  homotopyHomInvId := (Homotopy.ofEq (by rw [HomologicalComplex.extendMap_comp])).trans
    ((h.homotopyHomInvId.extend _).trans (Homotopy.ofEq (HomologicalComplex.extendMap_id _ _)))
  homotopyInvHomId := (Homotopy.ofEq (by rw [HomologicalComplex.extendMap_comp])).trans
    ((h.homotopyInvHomId.extend _).trans (Homotopy.ofEq (HomologicalComplex.extendMap_id _ _)))

def sIso (A : Shv R) := HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat A 0 (0 : ℤ) (by simp)

theorem sIso_nat {A B : Shv R} (φ : A ⟶ B) :
    HomologicalComplex.extendMap ((ChainComplex.single₀ (Shv R)).map φ) ComplexShape.embeddingDownNat ≫ (sIso B).hom =
      (sIso A).hom ≫ (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map φ := by
  apply HomologicalComplex.to_single_hom_ext
  simp [sIso, HomologicalComplex.extendSingleIso_hom_f,
    HomologicalComplex.extendMap_f _ ComplexShape.embeddingDownNat (i := 0) (i' := (0 : ℤ)) (by simp),
    HomologicalComplex.single_map_f_self]

theorem disc0 : Disc0 := by
  intro R _ X Y f
  refine ⟨HomotopyCategory.isoOfHomotopyEquiv (hext (ed R X).homotopyEquiv) ≪≫ (Qt R).mapIso (sIso _),
    HomotopyCategory.isoOfHomotopyEquiv (hext (ed R Y).homotopyEquiv) ≪≫ (Qt R).mapIso (sIso _), ?_⟩
  have hn := (AlgebraicTopology.AlternatingFaceMapComplex.ε (C := Shv R)).naturality (augMap R f)
  have key : (chains R).map (disc.map f) ≫ HomologicalComplex.extendMap (AlgebraicTopology.AlternatingFaceMapComplex.ε.app (aug R Y)) ComplexShape.embeddingDownNat ≫ (sIso ((free R).obj Y)).hom =
      HomologicalComplex.extendMap (AlgebraicTopology.AlternatingFaceMapComplex.ε.app (aug R X)) ComplexShape.embeddingDownNat ≫ (sIso ((free R).obj X)).hom ≫
        (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map ((free R).map f) := by
    have h2 := congrArg (fun φ => HomologicalComplex.extendMap φ ComplexShape.embeddingDownNat) hn
    simp only [HomologicalComplex.extendMap_comp] at h2
    have h1 : HomologicalComplex.extendMap ((point ⋙ ChainComplex.single₀ (Shv R)).map (augMap R f)) ComplexShape.embeddingDownNat ≫
        (sIso ((free R).obj Y)).hom = (sIso ((free R).obj X)).hom ≫
          (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map ((free R).map f) := sIso_nat ((free R).map f)
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (sIso ((free R).obj Y)).hom) h2).trans
      ((Category.assoc _ _ _).trans (congrArg (HomologicalComplex.extendMap (AlgebraicTopology.AlternatingFaceMapComplex.ε.app (aug R X)) ComplexShape.embeddingDownNat ≫ ·) h1)))
  have := congrArg (Qt R).map key
  simp only [Functor.map_comp] at this
  simp only [Iso.trans_hom, Category.assoc]
  exact this

theorem Piece_of : LateralTheory.E.TruncationPieces.Piece := LateralTheory.E.SimplicialPieceRelations.piece_of disc0

end LateralTheory.E.SimplicialPieceDiscrete
end
end
