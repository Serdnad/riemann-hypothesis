module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle243
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle266
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.Etale
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul

@[expose] public section

section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Pinch

theorem alg_cancel {G : Type*} [CommGroup G] (c a b : G) : a * b⁻¹ = (c * a) * (c * b)⁻¹ := by
  apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]; abel

theorem alg_chain {G : Type*} [CommGroup G] (a b c : G) : (b * a⁻¹) * (c * b⁻¹) = c * a⁻¹ := by
  apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]; abel

theorem alg_swap {G : Type*} [CommGroup G] (c a b : G) : c * a = c * (b * a⁻¹)⁻¹ * b := by
  apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]; abel

theorem ratio_unit {Y : Scheme.{0}} {L : LB Y} (hL : L.IsLB) {V V₁ V₂ : Y.Opens} (h₁ : V ≤ V₁) (h₂ : V ≤ V₂)
    {a₁ : ∀ k, Γ(Y, V₁ ⊓ L.U k)ˣ} {a₂ : ∀ k, Γ(Y, V₂ ⊓ L.U k)ˣ} (ha₁ : LocGen L V₁ a₁) (ha₂ : LocGen L V₂ a₂) :
    ∃ s : Γ(Y, V)ˣ, ∀ (T : Scheme.{0}) (f : T ⟶ Y) (t : T) (k : L.ι), f t ∈ V → f t ∈ L.U k →
      gm f t V s = gm f t (V₂ ⊓ L.U k) (a₂ k) * (gm f t (V₁ ⊓ L.U k) (a₁ k))⁻¹ := by
  have l₁ : ∀ k, V ⊓ L.U k ≤ V₁ ⊓ L.U k := fun k => inf_le_inf_right _ h₁
  have l₂ : ∀ k, V ⊓ L.U k ≤ V₂ ⊓ L.U k := fun k => inf_le_inf_right _ h₂
  obtain ⟨s, hs⟩ := glue_unit V (fun k => V ⊓ L.U k) (fun k => inf_le_left)
    (fun y hy => by
      obtain ⟨k, hk⟩ := exists_chart hL y
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hy, hk⟩)
    (fun k => res (l₂ k) (a₂ k) * (res (l₁ k) (a₁ k))⁻¹)
    (fun k k' y hy => by
      rw [map_mul, map_inv, map_mul, map_inv, gm_res _ y (l₂ k) hy.1, gm_res _ y (l₁ k) hy.1,
        gm_res _ y (l₂ k') hy.2, gm_res _ y (l₁ k') hy.2, ha₁ y k k' (h₁ hy.1.1) hy.1.2 hy.2.2,
        ha₂ y k k' (h₂ hy.1.1) hy.1.2 hy.2.2]
      exact (alg_cancel _ _ _).symm)
  refine ⟨s, fun T f t k ht hk => ?_⟩
  have hm : f t ∈ V ⊓ L.U k := ⟨ht, hk⟩
  rw [← gm_res f t (inf_le_left : V ⊓ L.U k ≤ V) hm s, hs k, map_mul, map_inv, gm_res f t (l₂ k) hm,
    gm_res f t (l₁ k) hm]

theorem eq_of_gm {X X' : Scheme.{0}} (p : X' ⟶ X) {V : X.Opens} (hinj : Function.Injective (pullU p V))
    {u v : Γ(X, V)ˣ} (h : ∀ x' : X', p x' ∈ V → gm p x' V u = gm p x' V v) : u = v :=
  hinj (unit_ext fun x' hx' => by
    rw [gm_pull (𝟙 X') p x' V hx', gm_pull (𝟙 X') p x' V hx', Category.id_comp]
    exact h x' hx')

end GlobalTheory.Pinch

namespace GlobalTheory.Pinch

theorem exists_lb_of_matching_gens : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z),
    i' ≫ p = p' ≫ i → GlobalTheory.Pinch.UnitsPatch p i i' p' → ∀ (L' : LB X') (N : LB Z), L'.IsLB → N.IsLB →
    ∀ (w : LB.Iso (L'.pull i') (N.pull p')) (W : X → X.Opens) (a : ∀ x k, Γ(X', p ⁻¹ᵁ (W x) ⊓ L'.U k)ˣ)
      (b : ∀ x l, Γ(Z, i ⁻¹ᵁ (W x) ⊓ N.U l)ˣ), (∀ x, x ∈ W x) →
      (∀ x, GlobalTheory.Pinch.LocGen L' (p ⁻¹ᵁ (W x)) (a x)) → (∀ x, GlobalTheory.Pinch.LocGen N (i ⁻¹ᵁ (W x)) (b x)) →
      (∀ x, GlobalTheory.Pinch.Matches i' p' w (a x) (b x)) → ∃ L : LB X, L.IsLB ∧ LBIso (L.pull p) L' := by
  intro X X' Z Z' p i i' p' hsq hU L' N hL' hN w W a b hW ha hb hm
  have pt : ∀ z : Z', p (i' z) = i (p' z) := fun z => congrArg (fun f => f z) hsq
  have key : ∀ x y, ∃ g : Γ(X, W x ⊓ W y)ˣ, ∀ (x' : X') (k : L'.ι), p x' ∈ W x ⊓ W y → x' ∈ L'.U k →
      gm p x' _ g = gm (𝟙 X') x' _ (a y k) * (gm (𝟙 X') x' _ (a x k))⁻¹ := by
    intro x y
    obtain ⟨s, hs⟩ := ratio_unit hL' (V := p ⁻¹ᵁ (W x ⊓ W y)) (fun _ h => h.1) (fun _ h => h.2) (ha x) (ha y)
    obtain ⟨t, ht⟩ := ratio_unit hN (V := i ⁻¹ᵁ (W x ⊓ W y)) (fun _ h => h.1) (fun _ h => h.2) (hb x) (hb y)
    obtain ⟨u, hu⟩ := (hU (W x ⊓ W y)).2 s t (fun z hz => by
      obtain ⟨k, hk⟩ := exists_chart hL' (i' z)
      obtain ⟨l, hl⟩ := exists_chart hN (p' z)
      have hz' : i (p' z) ∈ W x ⊓ W y := pt z ▸ hz
      rw [hs Z' i' z k hz hk, ht Z' p' z l hz' hl, hm x z k l hz.1 hz'.1 hk hl, hm y z k l hz.2 hz'.2 hk hl]
      exact alg_cancel _ _ _)
    refine ⟨u, fun x' k hx hk => ?_⟩
    have e := gm_pull (𝟙 X') p x' _ hx u
    rw [Category.id_comp] at e
    rw [← e, hu]
    exact hs X' (𝟙 X') x' k hx hk
  choose g hg using key
  have hL : (⟨X, W, g⟩ : LB X).IsLB :=
    { cover := eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hW x⟩
      g_self := fun x => eq_of_gm p (hU (W x)).1 fun x' hx => by
        obtain ⟨k, hk⟩ := exists_chart hL' x'
        refine (gm_res p x' _ hx _).trans ((hg x x x' k ⟨hx, hx⟩ hk).trans ?_)
        rw [mul_inv_cancel, map_one]
      cocycle := fun x y z => eq_of_gm p (hU _).1 fun x' hx => by
        obtain ⟨k, hk⟩ := exists_chart hL' x'
        exact ((map_mul _ _ _).trans (congrArg₂ (· * ·)
          ((gm_res p x' _ hx _).trans (hg x y x' k ⟨hx.1.1, hx.1.2⟩ hk))
          ((gm_res p x' _ hx _).trans (hg y z x' k ⟨hx.1.2, hx.2⟩ hk)))).trans
          ((alg_chain _ _ _).trans ((gm_res p x' _ hx _).trans (hg x z x' k ⟨hx.1.1, hx.2⟩ hk)).symm) }
  refine ⟨⟨X, W, g⟩, hL, ⟨fun P => res (fun x' hx' => ⟨mem_pull.1 hx'.2, hx'.1⟩ :
    L'.U P.1 ⊓ ((⟨X, W, g⟩ : LB X).pull p).U P.2 ≤ p ⁻¹ᵁ W (P.2 PUnit.unit) ⊓ L'.U P.1) (a (P.2 PUnit.unit) P.1)⟩, ?_⟩
  rintro ⟨k, J⟩ ⟨k', J'⟩
  apply unit_ext
  intro x' hx'
  have hJ : p x' ∈ W (J PUnit.unit) := mem_pull.1 hx'.1.2
  have hJ' : p x' ∈ W (J' PUnit.unit) := mem_pull.1 hx'.2.2
  have e : gm (𝟙 X') x' (((⟨X, W, g⟩ : LB X).pull p).U J ⊓ ((⟨X, W, g⟩ : LB X).pull p).U J')
      (((⟨X, W, g⟩ : LB X).pull p).g J J') = gm p x' _ (g (J PUnit.unit) (J' PUnit.unit)) := by
    show gm (𝟙 X') x' _ (∏ _k : PUnit, (res _ (pullU p _ (g (J PUnit.unit) (J' PUnit.unit)))) ^ (1 : ℤ)) = _
    rw [Fintype.prod_unique, zpow_one]
    have hq : x' ∈ ((⟨X, W, g⟩ : LB X).pull p).U J ⊓ ((⟨X, W, g⟩ : LB X).pull p).U J' := ⟨hx'.1.2, hx'.2.2⟩
    exact (gm_res _ x' _ hq _).trans ((gm_pull (𝟙 X') p x' (W (J PUnit.unit) ⊓ W (J' PUnit.unit))
      (⟨hJ, hJ'⟩ : p x' ∈ W (J PUnit.unit) ⊓ W (J' PUnit.unit)) _).trans (congrArg (fun f => gm f x' _ (g (J PUnit.unit) (J' PUnit.unit))) (Category.id_comp p)))
  have hdiv : gm (𝟙 X') x' _ ((LB.div L' ((⟨X, W, g⟩ : LB X).pull p)).g (k, J) (k', J')) =
      gm (𝟙 X') x' _ (L'.g k k') * (gm p x' _ (g (J PUnit.unit) (J' PUnit.unit)))⁻¹ :=
    (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ x' _ hx' _)
      ((map_inv _ _).trans (congrArg (·⁻¹) ((gm_res _ x' _ hx' _).trans e))))
  refine (gm_res _ x' _ hx' _).trans ((gm_res _ x' _ hx'.1 _).trans ?_)
  refine Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·) hdiv
    ((gm_res _ x' _ hx' _).trans (gm_res _ x' _ hx'.2 _)))).symm
  have h2 := hg (J PUnit.unit) (J' PUnit.unit) x' k' ⟨hJ, hJ'⟩ hx'.2.1
  rw [h2]
  exact (ha (J PUnit.unit) x' k k' hJ hx'.1.1 hx'.2.1).trans (alg_swap _ _ _)

end GlobalTheory.Pinch
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Pinch

theorem locGen_near_fibre_of_finite : (∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (W : X.Opens), IsAffineOpen W → ∀ F : Set X, F.Finite → F ⊆ W → ∃ (V : X.Opens) (a : ∀ k, Γ(X, V ⊓ L.U k)ˣ), F ⊆ V ∧ GlobalTheory.Pinch.LocGen L V a) → ∀ (X X' : Scheme.{0}) (p : X' ⟶ X), IsFinite p → ∀ (L : LB X'), L.IsLB → ∀ x : X, ∃ (W : X.Opens) (a : ∀ k, Γ(X', p ⁻¹ᵁ W ⊓ L.U k)ˣ), x ∈ W ∧ GlobalTheory.Pinch.LocGen L (p ⁻¹ᵁ W) a := by
  intro H X X' p hp L hL x
  obtain ⟨W₀, hW₀, hxW₀, -⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) (show x ∈ (⊤ : X.Opens) from trivial)
  have hA : IsAffineOpen (p ⁻¹ᵁ W₀) := IsAffineOpen.preimage hW₀ p
  have hF : (p.base ⁻¹' {x}).Finite := Scheme.Hom.finite_preimage_singleton p x
  have hFW : p.base ⁻¹' {x} ⊆ (p ⁻¹ᵁ W₀ : Set X') := by
    intro y hy
    show p.base y ∈ W₀
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hy
    rw [hy]; exact hxW₀
  obtain ⟨V, a, hFV, ha⟩ := H X' L hL (p ⁻¹ᵁ W₀) hA _ hF hFW
  have hcl : IsClosed (p.base '' (V : Set X')ᶜ) := p.isClosedMap _ V.isOpen.isClosed_compl
  let W : X.Opens := ⟨(p.base '' (V : Set X')ᶜ)ᶜ, hcl.isOpen_compl⟩
  have hWV : p ⁻¹ᵁ W ≤ V := by
    intro y hy
    by_contra h
    exact hy ⟨y, h, rfl⟩
  have hxW : x ∈ W := by
    rintro ⟨y, hy, hyx⟩
    exact hy (hFV (show p.base y = x from hyx))
  refine ⟨W, fun k ↦ res (inf_le_inf_right _ hWV) (a k), hxW, ?_⟩
  intro y k k' hy hk hk'
  rw [gm_res (𝟙 X') y (inf_le_inf_right _ hWV) ⟨hy, hk⟩, gm_res (𝟙 X') y (inf_le_inf_right _ hWV) ⟨hy, hk'⟩]
  exact ha y k k' (hWV hy) hk hk'

end GlobalTheory.Pinch
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Pinch

theorem isLocalization_away_of_absorb {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
    (hinj : Function.Injective (algebraMap R R')) (c : Ideal R)
    (hc : ∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) {f : R} (hf : f ∈ c) :
    IsLocalization.Away f (Localization.Away (algebraMap R R' f)) := by
  have hmap : ∀ a : R, algebraMap R (Localization.Away (algebraMap R R' f)) a =
      algebraMap R' (Localization.Away (algebraMap R R' f)) (algebraMap R R' a) := fun a =>
    IsScalarTower.algebraMap_apply R R' _ a
  refine (isLocalization_iff _ _).2 ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    rw [hmap, map_pow, map_pow]
    exact IsUnit.pow n (IsLocalization.Away.algebraMap_isUnit (algebraMap R R' f))
  · intro z
    obtain ⟨⟨r', ⟨_, n, rfl⟩⟩, hz⟩ := IsLocalization.surj (Submonoid.powers (algebraMap R R' f)) z
    obtain ⟨y, -, hy⟩ := hc f hf r'
    refine ⟨⟨y, ⟨f ^ (n + 1), n + 1, rfl⟩⟩, ?_⟩
    simp only at hz ⊢
    rw [hmap, hmap, hy, map_pow, map_pow, pow_succ, map_mul, ← hz, map_pow]
    ring
  · intro a b h
    rw [hmap, hmap] at h
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers (algebraMap R R' f)) h
    refine ⟨⟨f ^ k, k, rfl⟩, hinj ?_⟩
    simp only [map_mul, map_pow] at hk ⊢
    exact hk

theorem pinched_off : ∀ (R : Type) [CommRing R] (R' : Type) [CommRing R'] [Algebra R R'], Function.Injective (algebraMap R R') → ∀ c : Ideal R, (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → ∀ (g : ℕ) (B' C Y : Scheme.{0}) (b' : B' ⟶ Sp R') (e : C ⟶ Sp (R ⧸ c)) (i : Y ⟶ B') (q : Y ⟶ C), SmoothOfRelativeDimension g b' → ∀ x : B', (b' ≫ spMap (algebraMap R R')) x ∉ Set.range (spMap (Ideal.Quotient.mk c)) → GlobalTheory.Pinch.Pinched g (spMap (algebraMap R R')) (spMap (Ideal.Quotient.mk c)) b' e i q x := by
  intro R _ R' _ _ hinj c hc g B' C Y b' e i q hsm x hx
  obtain ⟨f, hfc, hfx⟩ : ∃ f ∈ c, f ∉ ((b' ≫ spMap (algebraMap R R')) x).asIdeal := by
    by_contra hno
    push_neg at hno
    apply hx
    have hr : Set.range (spMap (Ideal.Quotient.mk c)) =
        PrimeSpectrum.zeroLocus (RingHom.ker (Ideal.Quotient.mk c)) :=
      range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective
    rw [hr, Ideal.mk_ker]
    exact hno
  haveI : IsLocalization.Away f (Localization.Away (algebraMap R R' f)) :=
    isLocalization_away_of_absorb hinj c hc hfc
  let l' : Sp (Localization.Away (algebraMap R R' f)) ⟶ Sp R' := spMap (algebraMap R' _)
  let h : Sp (Localization.Away (algebraMap R R' f)) ⟶ Sp R := spMap (algebraMap R _)
  haveI : IsOpenImmersion l' := IsOpenImmersion.of_isLocalization (algebraMap R R' f)
  haveI : IsOpenImmersion h := IsOpenImmersion.of_isLocalization f
  have hcomp : l' ≫ spMap (algebraMap R R') = h := by
    simp only [l', h, spMap, ← Spec.map_comp]
    congr 1
  have hrange : Set.range h = (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) :=
    PrimeSpectrum.localization_away_comap_range _ f
  have hrange' : Set.range l' =
      (PrimeSpectrum.basicOpen (algebraMap R R' f) : Set (PrimeSpectrum R')) :=
    PrimeSpectrum.localization_away_comap_range _ _
  let j : pullback b' l' ⟶ B' := pullback.fst b' l'
  let u : pullback b' l' ⟶ Sp R := pullback.snd b' l' ≫ h
  have hju : j ≫ b' ≫ spMap (algebraMap R R') = u := by
    simp only [j, u, ← hcomp]
    rw [← Category.assoc, pullback.condition, Category.assoc]
  have hsmu : SmoothOfRelativeDimension g u := by
    haveI : SmoothOfRelativeDimension g (pullback.snd b' l') :=
      (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback
        (IsPullback.of_hasPullback b' l') hsm
    haveI : SmoothOfRelativeDimension 0 h := inferInstance
    have := smoothOfRelativeDimension_comp g 0 (pullback.snd b' l') h
    simpa using this
  have hD : ∀ t : ↥(pullback b' l'), f ∉ (u t).asIdeal := fun t => by
    have : u t ∈ Set.range h := ⟨pullback.snd b' l' t, rfl⟩
    rw [hrange] at this
    exact this
  have hEmpty : ∀ (T : Scheme.{0}) (a : T ⟶ pullback b' l') (a' : T ⟶ Sp (R ⧸ c)),
      a ≫ u = a' ≫ spMap (Ideal.Quotient.mk c) → IsEmpty T := by
    intro T a a' w
    refine ⟨fun t => hD (a t) ?_⟩
    have e1 : u (a t) = spMap (Ideal.Quotient.mk c) (a' t) := by
      rw [← Scheme.Hom.comp_apply, w, Scheme.Hom.comp_apply]
    rw [e1]
    show Ideal.Quotient.mk c f ∈ (a' t).asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hfc]
    exact Ideal.zero_mem _
  have w1 : 𝟙 (pullback b' l') ≫ u = (j ≫ b') ≫ spMap (algebraMap R R') := by
    rw [Category.id_comp, Category.assoc, hju]
  have w2 : Scheme.emptyTo (pullback b' l') ≫ u = (Scheme.emptyTo C ≫ e) ≫ spMap (Ideal.Quotient.mk c) :=
    Scheme.empty_ext _ _
  refine ⟨pullback b' l', pullback b' l', ∅, u, 𝟙 _, j, Scheme.emptyTo _, Scheme.emptyTo C, hsmu,
    ⟨⟨w1⟩, ⟨PullbackCone.IsLimit.mk w1 (fun s => s.fst) (fun s => Category.comp_id _) (fun s => ?_)
      (fun s m h1 _ => by simpa using h1)⟩⟩, inferInstance, ?_,
    ⟨⟨w2⟩, ⟨PullbackCone.IsLimit.mk w2
      (fun s => haveI := hEmpty _ _ _ s.condition; isInitialOfIsEmpty.to _)
      (fun s => by haveI := hEmpty _ _ _ s.condition; exact isInitialOfIsEmpty.hom_ext _ _)
      (fun s => by haveI := hEmpty _ _ _ s.condition; exact isInitialOfIsEmpty.hom_ext _ _)
      (fun s m _ _ => by haveI := hEmpty _ _ _ s.condition; exact isInitialOfIsEmpty.hom_ext _ _)⟩⟩, ?_⟩
  · have hr : Set.range s.snd ⊆ Set.range l' := by
      rintro _ ⟨t, rfl⟩
      rw [hrange']
      have e1 : spMap (algebraMap R R') (s.snd t) = u (s.fst t) := by
        rw [← Scheme.Hom.comp_apply, ← s.condition, Scheme.Hom.comp_apply]
      have := hD (s.fst t)
      rw [← e1] at this
      exact this
    have hl : IsOpenImmersion.lift l' s.snd hr ≫ l' = s.snd := IsOpenImmersion.lift_fac l' s.snd hr
    have hl2 : IsOpenImmersion.lift l' s.snd hr = s.fst ≫ pullback.snd b' l' := by
      rw [← cancel_mono h, ← hcomp, ← Category.assoc, hl, ← s.condition]
      show s.fst ≫ (pullback.snd b' l' ≫ h) = _
      rw [← hcomp]
      simp only [Category.assoc]
    show s.fst ≫ j ≫ b' = s.snd
    rw [← hl, hl2]
    exact congrArg (s.fst ≫ ·) pullback.condition
  · rw [IsOpenImmersion.range_pullbackFst l' b']
    show b' x ∈ Set.range l'
    rw [hrange']
    exact hfx
  · intro T a a' _
    haveI : IsEmpty T := ⟨fun t => isEmptyElim (a' t)⟩
    exact ⟨isInitialOfIsEmpty.to Y, isInitialOfIsEmpty.hom_ext _ _, isInitialOfIsEmpty.hom_ext _ _⟩

end GlobalTheory.Pinch
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Pinch

theorem restrict_pinched : ∀ (g : ℕ) (S S' Z B' C Y : Scheme.{0}) (s' : S' ⟶ S) (z : Z ⟶ S) (b' : B' ⟶ S') (e : C ⟶ Z) (i : Y ⟶ B') (q : Y ⟶ C), IsPullback i (q ≫ e) (b' ≫ s') z → IsPullback q (i ≫ b') (e ≫ z) s' → ∀ (V' : B'.Opens) (V : C.Opens), i ⁻¹ᵁ V' = q ⁻¹ᵁ V → ∃ (q₀ : (i ⁻¹ᵁ V').toScheme ⟶ V.toScheme), IsPullback (i ∣_ V') (q₀ ≫ V.ι ≫ e) ((V'.ι ≫ b') ≫ s') z ∧ IsPullback q₀ ((i ∣_ V') ≫ V'.ι ≫ b') ((V.ι ≫ e) ≫ z) s' ∧ ∀ x : V'.toScheme, GlobalTheory.Pinch.Pinched g s' z (V'.ι ≫ b') (V.ι ≫ e) (i ∣_ V') q₀ x → GlobalTheory.Pinch.Pinched g s' z b' e i q (V'.ι x) := by
  intro g S S' Z B' C Y s' z b' e i q h₁ h₂ V' V hV
  refine ⟨(Y.isoOfEq hV).hom ≫ (q ∣_ V), ?_, ?_, ?_⟩
  · have hq : ((Y.isoOfEq hV).hom ≫ (q ∣_ V)) ≫ V.ι ≫ e = (i ⁻¹ᵁ V').ι ≫ q ≫ e := by
      simp [morphismRestrict_ι_assoc, Scheme.isoOfEq_hom_ι_assoc]
    rw [hq, Category.assoc]
    exact (isPullback_morphismRestrict i V').paste_vert h₁
  · have P := (isPullback_morphismRestrict q V).paste_vert h₂
    refine IsPullback.of_iso P (Y.isoOfEq hV).symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · simp [morphismRestrict_ι_assoc, Scheme.isoOfEq_inv_ι_assoc]
    · simp
    · simp
  · intro x hx
    obtain ⟨U, U', W₀, u, p, j, n, k, hu, hp, hj, hx, hn, hl⟩ := hx
    refine ⟨U, U', W₀, u, p, j ≫ V'.ι, n, k ≫ V.ι, hu, by simpa using hp, inferInstance, ?_, by simpa using hn, ?_⟩
    · obtain ⟨w, rfl⟩ := hx
      exact ⟨w, rfl⟩
    · intro T a a' haa
      obtain ⟨y, hy₁, hy₂⟩ := hl T a a' haa
      refine ⟨y ≫ (i ⁻¹ᵁ V').ι, ?_, ?_⟩
      · rw [Category.assoc, ← morphismRestrict_ι, ← Category.assoc, hy₁, Category.assoc]
      · have hq : (Y.isoOfEq hV).hom ≫ (q ∣_ V) ≫ V.ι = (i ⁻¹ᵁ V').ι ≫ q := by
          simp [morphismRestrict_ι, Scheme.isoOfEq_hom_ι_assoc]
        rw [Category.assoc, ← hq, reassoc_of% hy₂]

end GlobalTheory.Pinch
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.Pinch

theorem gm_id_val_germ {X : Scheme.{0}} (x : X) (U : X.Opens) (h : x ∈ U) (a : Γ(X, U)ˣ) :
    (gm (𝟙 X) x U a).val = (X.presheaf.germ U x h).hom a.val := by
  rw [gm_val (𝟙 X) x U h]
  rfl

theorem isUnit_res_basicOpen' {X : Scheme.{0}} {D : X.Opens} (e : Γ(X, D)) :
    IsUnit ((X.presheaf.map (homOfLE (X.basicOpen_le e)).op).hom e) :=
  X.toRingedSpace.isUnit_res_basicOpen e

def basicUnit {X : Scheme.{0}} {D : X.Opens} (e : Γ(X, D)) : Γ(X, X.basicOpen e)ˣ :=
  (isUnit_res_basicOpen' e).unit

theorem gm_basicUnit_val {X : Scheme.{0}} {D : X.Opens} (e : Γ(X, D)) (x : X) (hx : x ∈ X.basicOpen e) :
    (gm (𝟙 X) x _ (basicUnit e)).val = (X.presheaf.germ D x (X.basicOpen_le e hx)).hom e := by
  rw [gm_id_val_germ x _ hx]
  show (X.presheaf.germ (X.basicOpen e) x hx).hom ((X.presheaf.map (homOfLE (X.basicOpen_le e)).op).hom e) = _
  exact TopCat.Presheaf.germ_res_apply X.presheaf _ x hx e

theorem exists_locGen_of_secFam : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (J : Type) (D : J → X.Opens) (k : J → L.ι) (hD : ∀ j, D j ≤ L.U (k j)) (e : ∀ j, Γ(X, D j)), GlobalTheory.Pinch.IsSecFam L D k hD e → ∃ (V : X.Opens) (a : ∀ i, Γ(X, V ⊓ L.U i)ˣ), (∀ j (x : X) (h : x ∈ D j), IsUnit ((X.presheaf.germ (D j) x h).hom (e j)) → x ∈ V) ∧ GlobalTheory.Pinch.LocGen L V a := by
  intro X L hL J D k hD e he
  let B : J → X.Opens := fun j => X.basicOpen (e j)
  have hB : ∀ j, B j ≤ D j := fun j => X.basicOpen_le (e j)
  let V : X.Opens := ⨆ j, B j
  have hBV : ∀ j, B j ≤ V := fun j => le_iSup B j

  have ge : ∀ j j' (z : X) (hz : z ∈ B j) (hz' : z ∈ B j'),
      gm (𝟙 X) z (B j) (basicUnit (e j)) =
        gm (𝟙 X) z (L.U (k j) ⊓ L.U (k j')) (L.g (k j) (k j')) * gm (𝟙 X) z (B j') (basicUnit (e j')) := by
    intro j j' z hz hz'
    apply Units.ext
    rw [Units.val_mul, gm_basicUnit_val _ z hz, gm_basicUnit_val _ z hz',
      gm_id_val_germ z (L.U (k j) ⊓ L.U (k j')) ⟨hD j (hB j hz), hD j' (hB j' hz')⟩]
    exact he j j' z (hB j hz) (hB j' hz')
  let W : L.ι → J → X.Opens := fun i j => B j ⊓ L.U i
  have hWV : ∀ i j, W i j ≤ V ⊓ L.U i := fun i j => inf_le_inf_right _ (hBV j)
  have hWg : ∀ i j, W i j ≤ L.U i ⊓ L.U (k j) := fun i j z hz => ⟨hz.2, hD j (hB j hz.1)⟩
  have hWB : ∀ i j, W i j ≤ B j := fun i j => inf_le_left
  let u : ∀ i j, Γ(X, W i j)ˣ := fun i j => res (hWg i j) (L.g i (k j)) * res (hWB i j) (basicUnit (e j))
  have gu : ∀ i j (z : X) (hz : z ∈ W i j), gm (𝟙 X) z (W i j) (u i j) =
      gm (𝟙 X) z (L.U i ⊓ L.U (k j)) (L.g i (k j)) * gm (𝟙 X) z (B j) (basicUnit (e j)) := by
    intro i j z hz
    simp only [u, map_mul]
    rw [gm_res _ z (hWg i j) hz, gm_res _ z (hWB i j) hz]
  have key : ∀ i j j' (z : X), z ∈ L.U i → z ∈ B j → z ∈ B j' →
      gm (𝟙 X) z (L.U i ⊓ L.U (k j)) (L.g i (k j)) * gm (𝟙 X) z (B j) (basicUnit (e j)) =
      gm (𝟙 X) z (L.U i ⊓ L.U (k j')) (L.g i (k j')) * gm (𝟙 X) z (B j') (basicUnit (e j')) := by
    intro i j j' z hi hj hj'
    rw [ge j j' z hj hj', ← _root_.mul_assoc, gm_cocycle hL (𝟙 X) z hi (hD j (hB j hj)) (hD j' (hB j' hj'))]
  have glued : ∀ i, ∃ s : Γ(X, V ⊓ L.U i)ˣ, ∀ j, res (hWV i j) s = u i j := by
    intro i
    refine glue_unit (V ⊓ L.U i) (W i) (hWV i) (fun z hz => ?_) (u i) (fun j j' z hz => ?_)
    · obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hz.1
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, hj, hz.2⟩
    · rw [gu i j z hz.1, gu i j' z hz.2]
      exact key i j j' z hz.1.2 hz.1.1 hz.2.1
  choose a ha using glued
  refine ⟨V, a, fun j x hx hu => hBV j ((Scheme.mem_basicOpen X (e j) x hx).2 hu), ?_⟩
  intro y i i' hy hi hi'
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  have ga : ∀ i (hi : y ∈ L.U i), gm (𝟙 X) y (V ⊓ L.U i) (a i) =
      gm (𝟙 X) y (L.U i ⊓ L.U (k j)) (L.g i (k j)) * gm (𝟙 X) y (B j) (basicUnit (e j)) := by
    intro i hi
    rw [← gm_res _ y (hWV i j) ⟨hj, hi⟩, ha i j]
    exact gu i j y ⟨hj, hi⟩
  rw [ga i hi, ga i' hi', ← _root_.mul_assoc, gm_cocycle hL (𝟙 X) y hi hi' (hD j (hB j hj))]

end GlobalTheory.Pinch
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_lineBundleLocalSectionFamily_unit_at_point : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (W : X.Opens), IsAffineOpen W → ∀ (J : Type) [Fintype J] (f : J → Γ(X, W)) (k : J → L.ι) (hk : ∀ j, X.basicOpen (f j) ≤ L.U (k j)) (x : X), x ∈ W → ∃ e : ∀ j, Γ(X, X.basicOpen (f j)), GlobalTheory.Pinch.IsSecFam L (fun j => X.basicOpen (f j)) k hk e ∧ ∀ j (h : x ∈ X.basicOpen (f j)), IsUnit ((X.presheaf.germ (X.basicOpen (f j)) x h).hom (e j)) := by
  first | exact @GlobalTheory.Pinch.SemiLoc.exists_secFam_isUnit_germ | exact GlobalTheory.Pinch.SemiLoc.exists_secFam_isUnit_germ | (intros; apply GlobalTheory.Pinch.SemiLoc.exists_secFam_isUnit_germ <;> assumption)
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem _root_.GlobalTheory.T.pow_finrank_omega_le_finrank_frobeniusKernel : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0) (G : PDivGroup p K), ∀ r : ℕ, (p ^ r) ^ Module.finrank K G.omega ≤ Module.finrank K (G.A r ⧸ frobKerIdeal (p ^ r) K (G.A r)) := by
  first | exact @GlobalTheory.PDivGroup.pow_finrank_omega_le_finrank_frobKer | exact GlobalTheory.PDivGroup.pow_finrank_omega_le_finrank_frobKer | (intros; apply GlobalTheory.PDivGroup.pow_finrank_omega_le_finrank_frobKer <;> assumption)
end
