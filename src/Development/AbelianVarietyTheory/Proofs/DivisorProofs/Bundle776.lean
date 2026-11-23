module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle733
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle601
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMaximalIdealEqOrigin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle280
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle741
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle422
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle734
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle748
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle738
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.PhlaBlockWtCpt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle742
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtensionAcrossHypersurfaceValuesAtZeros
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.Smooth.IntegralClosure
import Mathlib.RingTheory.TotallySplit
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CechPosetDegreeOne
variable {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R)


open Classical in
def val {p : ℕ} (c : CC F p) (s : Finset κ) (b : (NE κ)ᵒᵖ) : F.obj b :=
  if h : s.card = p + 1 ∧ s ⊆ sub b then
    mp F (homOf (a := ne s (card_nonempty ⟨s, h.1⟩)) (b := b) h.2) (c ⟨s, h.1⟩) else 0

theorem val_eq {p : ℕ} (c : CC F p) (s : {s : Finset κ // s.card = p + 1}) (b : (NE κ)ᵒᵖ)
    (f : ne s.1 (card_nonempty s) ⟶ b) : mp F f (c s) = val F c s.1 b := by
  unfold val
  obtain ⟨s, hs⟩ := s
  have hsub : s ⊆ sub b := sub_subset f
  rw [dite_eq_left (⟨hs, hsub⟩ : s.card = p + 1 ∧ s ⊆ sub b)]
  exact congrArg (fun φ => mp F φ (c ⟨s, hs⟩)) (Subsingleton.elim _ _)

theorem mp_val {p : ℕ} (c : CC F p) (s : Finset κ) {b d : (NE κ)ᵒᵖ} (g : b ⟶ d)
    (h : s.card = p + 1) (hs : s ⊆ sub b) : mp F g (val F c s b) = val F c s d := by
  rw [← val_eq F c ⟨s, h⟩ b (homOf hs), ← mp_comp, val_eq]

theorem orderedCechToCatCochainsOne_apply_valueAtSubset (c : CC F 1) {a b : (NE κ)ᵒᵖ} (f : a ⟶ b) :
    e1 F c a b f = if mn b < mn a then - val F c {mn b, mn a} b else 0 := by
  simp only [e1, LinearMap.pi_apply]
  split_ifs with h
  · simp only [LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.proj_apply, AlgHom.toLinearMap_apply]
    exact congrArg Neg.neg (val_eq F c ⟨{mn b, mn a}, Finset.card_pair h.ne⟩ b _)
  · rfl

theorem alternatingToOrderedCechDegreeTwo_apply_valueAtSubset (c : CC F 2) {a b d : (NE κ)ᵒᵖ} (f : a ⟶ b) (g : b ⟶ d) :
    e2 F c a b d f g = if mn d < mn b ∧ mn b < mn a then - val F c {mn d, mn b, mn a} d else 0 := by
  simp only [e2, LinearMap.pi_apply]
  split_ifs with h
  · simp only [LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.proj_apply, AlgHom.toLinearMap_apply]
    exact congrArg Neg.neg (val_eq F c ⟨{mn d, mn b, mn a}, card_three h.1 h.2⟩ d _)
  · rfl

theorem val_δ {p : ℕ} (c : CC F p) (t : Finset κ) (d : (NE κ)ᵒᵖ) (h : t.card = p + 1 + 1)
    (ht : t ⊆ sub d) :
    val F (δ F p c) t d = ∑ i ∈ t, GlobalTheory.cubeSign t i • val F c (t.erase i) d := by

  rw [← val_eq F (δ F p c) ⟨t, h⟩ d (homOf ht), δ_apply, map_sum,
  ← Finset.sum_coe_sort t (fun i => GlobalTheory.cubeSign t i • val F c (t.erase i) d)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, ← mp_comp, val_eq]

theorem val_δ_three (c : CC F 1) {x y z : κ} (h₁ : x < y) (h₂ : y < z) (d : (NE κ)ᵒᵖ)
    (ht : ({x, y, z} : Finset κ) ⊆ sub d) :
    val F (δ F 1 c) {x, y, z} d = val F c {y, z} d - val F c {x, z} d + val F c {x, y} d := by
  have h₃ := h₁.trans h₂
  rw [val_δ F c _ d (card_three h₁ h₂) ht, Finset.sum_insert (by simp [h₁.ne, h₃.ne]),
    Finset.sum_pair h₂.ne]
  have e₁ : ({x, y, z} : Finset κ).erase x = {y, z} := by
    ext w; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · tauto
    · rintro (rfl | rfl) <;> simp [h₁.ne', h₃.ne']
  have e₂ : ({x, y, z} : Finset κ).erase y = {x, z} := by
    ext w; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · tauto
    · rintro (rfl | rfl) <;> simp [h₁.ne, h₂.ne']
  have e₃ : ({x, y, z} : Finset κ).erase z = {x, y} := by
    ext w; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · tauto
    · rintro (rfl | rfl) <;> simp [h₃.ne, h₂.ne]
  have s₁ : GlobalTheory.cubeSign ({x, y, z} : Finset κ) x = 1 := by
    simp [GlobalTheory.cubeSign, Finset.filter_insert, Finset.filter_singleton, h₁.not_gt, h₃.not_gt]
  have s₂ : GlobalTheory.cubeSign ({x, y, z} : Finset κ) y = -1 := by
    simp [GlobalTheory.cubeSign, Finset.filter_insert, Finset.filter_singleton, h₁, h₂.not_gt]
  have s₃ : GlobalTheory.cubeSign ({x, y, z} : Finset κ) z = 1 := by
    simp [GlobalTheory.cubeSign, Finset.filter_insert, Finset.filter_singleton, h₃, h₂, Finset.card_pair h₁.ne]
  rw [e₁, e₂, e₃, s₁, s₂, s₃]
  simp only [one_smul, neg_smul]
  ring

theorem orderedCechToCatCochainsOne_coboundary_comm {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R)
    (c : CC F 1) : d1 F (e1 F c) = e2 F (δ F 1 c) := by
  funext a b d f g
  rw [d1_apply, orderedCechToCatCochainsOne_apply_valueAtSubset, orderedCechToCatCochainsOne_apply_valueAtSubset, orderedCechToCatCochainsOne_apply_valueAtSubset, alternatingToOrderedCechDegreeTwo_apply_valueAtSubset]
  rcases (mn_le_of_hom f).lt_or_eq with h₂ | h₂ <;> rcases (mn_le_of_hom g).lt_or_eq with h₁ | h₁
  · rw [if_pos h₂, if_pos h₁, if_pos (h₁.trans h₂), if_pos ⟨h₁, h₂⟩, map_neg,
      mp_val F c _ g (Finset.card_pair h₂.ne) (pair_subset f),
      val_δ_three F c h₁ h₂ d (triple_subset f g)]
    ring
  · rw [if_pos h₂, if_neg h₁.not_lt, if_pos (h₁ ▸ h₂), if_neg (fun h => h₁.not_lt h.1), map_neg,
      mp_val F c _ g (Finset.card_pair h₂.ne) (pair_subset f), h₁]
    ring
  · rw [if_neg h₂.not_lt, if_pos h₁, if_pos (h₂ ▸ h₁), if_neg (fun h => h₂.not_lt h.2), map_zero, h₂]
    ring
  · rw [if_neg h₂.not_lt, if_neg h₁.not_lt, if_neg (h₁.trans h₂).not_lt,
      if_neg (fun h => h₂.not_lt h.2), map_zero]
    ring

end GlobalTheory.CechPosetDegreeOne
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

set_option autoImplicit false

namespace GlobalTheory.CechPoset

variable {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R)

theorem hom_eq_id {a : (NE κ)ᵒᵖ} (f : a ⟶ a) : f = 𝟙 a :=
  Quiver.Hom.unop_inj (Subsingleton.elim _ _)

theorem mp_single (c : CC F 0) (i j : κ) (hij : j = i) (h : sub (ne {j} (Finset.singleton_nonempty j)) ⊆
    sub (ne {i} (Finset.singleton_nonempty i))) (hc : ({j} : Finset κ).card = 0 + 1) :
    mp F (homOf h) (c ⟨{j}, hc⟩) = c ⟨{i}, Finset.card_singleton i⟩ := by
  subst hij
  rw [hom_eq_id (homOf h), mp_id]

theorem sum_cubeSign_two (t : Finset κ) (ht : t.card = 2) : ∑ i ∈ t, GlobalTheory.cubeSign t i = 0 := by
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.1 ht
  rw [Finset.sum_pair hxy]
  rcases lt_or_gt_of_ne hxy with h | h
  · simp [GlobalTheory.cubeSign, Finset.filter_insert, Finset.filter_singleton, h, h.not_gt]
  · simp [GlobalTheory.cubeSign, Finset.filter_insert, Finset.filter_singleton, h, h.not_gt]

theorem orderedCech_degreeZero_cocycles_correspond : (∀ c : CC F 0, δ F 0 c = 0 → e0 F c = 0 → c = 0) ∧
    ∀ g : C0 F, d0 F g = 0 → ∃ c : CC F 0, δ F 0 c = 0 ∧ e0 F c = g := by
  refine ⟨fun c _ he => ?_, fun g hg => ?_⟩
  · funext s
    obtain ⟨s, hs⟩ := s
    obtain ⟨i, rfl⟩ := Finset.card_eq_one.1 hs
    have H := congrFun he (ne {i} (Finset.singleton_nonempty i))
    have hm : mn (ne {i} (Finset.singleton_nonempty i)) = i := Finset.min'_singleton i
    have := mp_single F c i _ hm
    simp only [e0, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply] at H
    exact (this (Finset.singleton_subset_iff.2 (mn_mem _)) (Finset.card_singleton _)).symm.trans H
  · have hg' : ∀ {T T' : (NE κ)ᵒᵖ} (φ : T ⟶ T'), mp F φ (g T) = g T' := by
      intro T T' φ
      have := congrFun (congrFun (congrFun hg T) T') φ
      rw [amitsur_d0_apply] at this
      exact (sub_eq_zero.1 this).symm
    refine ⟨fun s => g (ne s.1 (card_nonempty s)), ?_, ?_⟩
    · funext t
      rw [δ_apply]
      simp only [hg']
      rw [← Finset.sum_smul, Finset.sum_coe_sort t.1 (fun i => GlobalTheory.cubeSign t.1 i),
        sum_cubeSign_two t.1 t.2, zero_smul]
      rfl
    · funext a
      simp only [e0, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply]
      exact hg' _

end GlobalTheory.CechPoset
end

section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh

namespace GlobalTheory.CechPoset

theorem pr_monotone {κ : Type} [LinearOrder κ] {X' X'' : Scheme.{0}} {ψ : X'' ⟶ X'} (D' : κ → X'.Opens)
    (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D' i)) (D'' : κ → X''.Opens)
    (hD'' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D'' i)) (hle : ∀ i, D'' i ≤ ψ ⁻¹ᵁ D' i) :
    Monotone (pr D' hD' D'' hD'' hle) := fun _ _ h =>
  Subtype.mk_le_mk.2 (Prod.mk_le_mk.2 ⟨cov_mono D'' hD'' h, cov_mono D' hD' h⟩)

theorem restrict_pull1_pullHO1 {R' R'' : Type} [CommRing R'] [CommRing R''] {X' X'' : Scheme.{0}}
    {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {σ : R' →+* R''} {ψ : X'' ⟶ X'}
    (w : ψ ≫ s' = s'' ≫ spMap σ) {κ : Type} [LinearOrder κ] (D' : κ → X'.Opens)
    (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D' i)) (D'' : κ → X''.Opens)
    (hD'' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D'' i)) (hle : ∀ i, D'' i ≤ ψ ⁻¹ᵁ D' i)
    (y : HO1 s') :
    (CoefMap.restrict (OAff s'') (cov_mono D'' hD'').functor.op).pull1 (pullHO1 w y) =
      (pullCoef w D' hD' D'' hD'' hle).pull1
        ((CoefMap.restrict (OAff s') (cov_mono D' hD').functor.op).pull1 y) := by
  have hp : (pairPull w).pull1 y = (pairRes ψ s'').pull1 (pullHO1 w y) := isPullO_pullHO1 w y
  generalize pullHO1 w y = z at hp
  let n := CoefMap.restrict (OPair ψ s'') (pr_monotone D' hD' D'' hD'' hle).functor.op
  have h1 : (CoefMap.restrict (OAff s'') (cov_mono D'' hD'').functor.op).pull1 z =
      n.pull1 ((pairRes ψ s'').pull1 z) := by
    refine Eq.trans ?_ ((pairRes ψ s'').pullCohomologyOne_comp n z)
    exact CoefMap.pullCohomologyOne_eq_of_natTrans _ ((pairRes ψ s'').comp n) { app U := 𝟙 _ }
      (fun U b ↦ mp_id (OAff s'') _ b) z
  rw [h1, ← hp]
  refine ((pairPull w).pullCohomologyOne_comp n y).symm.trans (Eq.trans ?_ (CoefMap.pullCohomologyOne_comp _ _ y))
  exact CoefMap.pullCohomologyOne_eq_of_natTrans _ _ { app U := 𝟙 _ } (fun U b ↦ by erw [mp_id]) y

end GlobalTheory.CechPoset
end

section

open IsLocalRing Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.etale_integralClosure_torsor_of_fraction_fields : (∀ (S S₁ K K₁ : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [CommRing S₁]
    [IsDomain S₁] [IsDiscreteValuationRing S₁] [Field K] [Algebra S K] [IsFractionRing S K] [Field K₁]
    [Algebra S₁ K₁] [IsFractionRing S₁ K₁] [Algebra S S₁] [Algebra K K₁] [Algebra S K₁]
    [IsScalarTower S K K₁] [IsScalarTower S S₁ K₁],
    Function.Injective (algebraMap S S₁) → ∀ (q : ℕ), 0 < q → IsUnit (q : S) →
    ∀ π : S, Irreducible π → ∀ y : S₁, y ^ q = algebraMap S S₁ π →
    ∀ (M : Type) [CommRing M] [Algebra K M] (act : Multiplicative (ZMod q) →* (M ≃ₐ[K] M)),
    GlobalTheory.KeyOriginCut.IsZTorsor K M q act →
    Algebra.Etale S₁ (integralClosure S₁ (K₁ ⊗[K] M))) →
  ∀ (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [IsDomain R] [Algebra A R],
    Function.Injective (algebraMap A R) →
    ∀ (A₁ R₁ : Type) [CommRing A₁] [IsDomain A₁] [CommRing R₁] [IsDomain R₁] [Algebra A₁ R₁],
    Function.Injective (algebraMap A₁ R₁) →
    ∀ (f : A →+* A₁), Function.Injective f → ∀ (φ : R →+* R₁),
    φ.comp (algebraMap A R) = (algebraMap A₁ R₁).comp f →
    ∀ (β : GlobalTheory.LocAcyc.GenFib A R →+* GlobalTheory.LocAcyc.GenFib A₁ R₁),
    β.comp (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) =
      (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)).comp φ →
    ∀ (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A R) DA] (q : ℕ)
      (act : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A R] DA)),
    0 < q → IsUnit (q : A) → GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A R) DA q act →
    ∀ (P₁ : Ideal R₁) [P₁.IsPrime],
    IsDiscreteValuationRing (Localization.AtPrime P₁) →
    IsDiscreteValuationRing (Localization.AtPrime (P₁.comap φ)) →
    ∀ π : A, Irreducible (algebraMap A (Localization.AtPrime (P₁.comap φ)) π) →
    ∀ y : R₁, y ^ q = φ (algebraMap A R π) →
    (letI := (GlobalTheory.KeyOriginNoeth.baseHom A₁ R₁ (GlobalTheory.KeyOriginBC.BC β DA)).toAlgebra;
      Algebra.Etale (Localization.AtPrime P₁)
        (integralClosure (Localization.AtPrime P₁) (Localization.AtPrime P₁ ⊗[R₁] GlobalTheory.KeyOriginBC.BC β DA))) := by
  first | (exact @GlobalTheory.KeyOriginTransport.etale_closure_of_field) | (exact GlobalTheory.KeyOriginTransport.etale_closure_of_field) | (intros; apply GlobalTheory.KeyOriginTransport.etale_closure_of_field  <;> assumption)
end

section

open IsLocalRing Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.KeyOriginBCEt

open GlobalTheory.LocAcyc GlobalTheory.KeyOriginNoeth GlobalTheory.KeyOriginBC

theorem closureEtaleAt_bc : ∀ (A R A₁ R₁ : Type) [CommRing A] [IsDomain A] [CommRing R] [Algebra A R]
    [CommRing A₁] [IsDomain A₁] [CommRing R₁] [IsDomain R₁] [IsIntegrallyClosed R₁] [Algebra A₁ R₁]
    (f : A →+* A₁), Function.Injective f → Function.Injective (algebraMap A₁ R₁) →
    ∀ (κ : R →+* R₁), κ.comp (algebraMap A R) = (algebraMap A₁ R₁).comp f →
    ∀ (β : GenFib A R →+* GenFib A₁ R₁),
    β.comp (algebraMap R (GenFib A R)) = (algebraMap R₁ (GenFib A₁ R₁)).comp κ →
    ∀ (DA : Type) [CommRing DA] [Algebra (GenFib A R) DA] [Algebra.IsIntegral (GenFib A R) DA]
    (P₁ : Ideal R₁) [P₁.IsPrime],
    GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A R DA (P₁.comap κ) →
    GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A₁ R₁ (BC β DA) P₁ := by
  intro A R A₁ R₁ _ _ _ _ _ _ _ _ _ _ f hf hA₁ κ hκ β hβ DA _ _ _ P₁ _ hP
  letI := closureAlg A R DA
  letI : Algebra R (Localization.AtPrime P₁) :=
    ((algebraMap R₁ (Localization.AtPrime P₁)).comp κ).toAlgebra
  letI : Algebra R₁ (BC β DA) := (baseHom A₁ R₁ (BC β DA)).toAlgebra
  haveI hE : Algebra.Etale (Localization.AtPrime P₁) (Localization.AtPrime P₁ ⊗[R] closure A R DA) :=
    GlobalTheory.T.etale_atPrime_baseChange_of_integralClosureEtale A R R₁ DA κ P₁ hP
  haveI : IsDomain (Localization.AtPrime P₁) :=
    IsLocalization.isDomain_localization P₁.primeCompl_le_nonZeroDivisors
  haveI : IsIntegrallyClosed (Localization.AtPrime P₁) :=
    isIntegrallyClosed_of_isLocalization _ P₁.primeCompl P₁.primeCompl_le_nonZeroDivisors
  have hinjS : Function.Injective (algebraMap R₁ (Localization.AtPrime P₁)) :=
    IsLocalization.injective _ P₁.primeCompl_le_nonZeroDivisors
  have hM : (nonZeroDivisors A₁).map ((algebraMap R₁ (Localization.AtPrime P₁)).comp (algebraMap A₁ R₁))
      ≤ nonZeroDivisors (Localization.AtPrime P₁) := by
    rintro _ ⟨a, ha, rfl⟩
    apply mem_nonZeroDivisors_of_ne_zero
    intro h
    have h1 : algebraMap A₁ R₁ a = 0 := hinjS (by simpa using h)
    exact nonZeroDivisors.ne_zero ha (hA₁ (by simpa using h1))
  obtain ⟨hinj, hint⟩ := GlobalTheory.T.etale_integrallyClosed_in_localization (Localization.AtPrime P₁)
    (Localization.AtPrime P₁ ⊗[R] closure A R DA) _ hM
  obtain ⟨φ, ψ, hψφ, hunit, hsurj⟩ := GlobalTheory.T.exists_closureBaseChange_maps_and_retraction A R A₁ R₁ f hf κ hκ β hβ DA (Localization.AtPrime P₁)
  have hψφ' : ∀ e, ψ (φ e) = algebraMap _ _ e := fun e => by
    rw [← AlgHom.comp_apply, hψφ]; rfl
  have hφinj : Function.Injective φ := by
    intro x y hxy
    apply hinj
    rw [← hψφ', ← hψφ', hxy]
  have hφint : ∀ x : Localization.AtPrime P₁ ⊗[R₁] BC β DA, IsIntegral (Localization.AtPrime P₁) x →
      x ∈ φ.range := by
    intro x hx
    obtain ⟨e, he⟩ := hint (ψ x) (hx.map ψ)
    obtain ⟨m, hm, e', he'⟩ := hsurj x
    have he'' : φ e' = x * algebraMap _ _ m := he'
    have h2 : e * algebraMap _ _ m = e' := by
      apply hinj
      rw [map_mul, he, ← hψφ' e', he'', map_mul, AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
    refine ⟨e, ?_⟩
    show φ e = x
    apply (hunit m hm).mul_right_cancel
    calc φ e * algebraMap _ _ m = φ (e * algebraMap _ _ m) := by rw [map_mul, AlgHom.commutes]
      _ = x * _ := by rw [h2, he'']
  haveI : Algebra.IsIntegral R (closure A R DA) := by
    letI := (baseHom A R DA).toAlgebra
    let ι : closure A R DA →ₐ[R] DA := { (closure A R DA).subtype with commutes' := fun _ => rfl }
    exact ⟨fun x => (isIntegral_algHom_iff ι Subtype.val_injective).1 x.2⟩
  haveI : Algebra.IsIntegral (Localization.AtPrime P₁) (Localization.AtPrime P₁ ⊗[R] closure A R DA) :=
    inferInstance
  let φ' : Localization.AtPrime P₁ ⊗[R] closure A R DA →ₐ[Localization.AtPrime P₁]
      integralClosure (Localization.AtPrime P₁) (Localization.AtPrime P₁ ⊗[R₁] BC β DA) :=
    φ.codRestrict _ (fun e => (Algebra.IsIntegral.isIntegral e).map φ)
  have hφ' : Function.Bijective φ' := by
    refine ⟨fun x y h => hφinj (congrArg Subtype.val h), fun ⟨x, hx⟩ => ?_⟩
    obtain ⟨e, he⟩ := hφint x hx
    exact ⟨e, Subtype.ext he⟩
  haveI : Algebra.Etale (Localization.AtPrime P₁)
      (integralClosure (Localization.AtPrime P₁) (Localization.AtPrime P₁ ⊗[R₁] BC β DA)) :=
    Algebra.Etale.of_equiv (AlgEquiv.ofBijective φ' hφ')
  have hloc := TensorProduct.toIntegralClosure_bijective_of_isLocalization (R := R₁)
    (S := Localization.AtPrime P₁) (B := BC β DA) P₁.primeCompl
  haveI : Algebra.Etale (Localization.AtPrime P₁)
      (Localization.AtPrime P₁ ⊗[R₁] integralClosure R₁ (BC β DA)) :=
    Algebra.Etale.of_equiv (AlgEquiv.ofBijective _ hloc).symm
  unfold GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt
  letI := closureAlg A₁ R₁ (BC β DA)
  let eC : closure A₁ R₁ (BC β DA) ≃ₐ[R₁] integralClosure R₁ (BC β DA) :=
    { toFun := fun x => ⟨x.1, x.2⟩, invFun := fun x => ⟨x.1, x.2⟩, left_inv := fun _ => rfl,
      right_inv := fun _ => rfl, map_mul' := fun _ _ => rfl, map_add' := fun _ _ => rfl,
      commutes' := fun _ => rfl }
  exact Algebra.Etale.of_equiv (Algebra.TensorProduct.congr AlgEquiv.refl eC).symm

theorem closureEtaleAt_baseChange : ∀ (T O : Type) [CommRing T] [CommRing O] [IsLocalRing O] [Algebra T O] [Algebra T[X] O]
    [IsScalarTower T T[X] O]
    (A A₁ : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [Algebra.EssFiniteType ℤ A] [CommRing A₁] [IsDomain A₁] [IsLocalRing A₁] [IsNoetherianRing A₁]
    [IsIntegrallyClosed A₁] [Algebra.EssFiniteType ℤ A₁] (f : A →+* A₁) (i : A →+* T)
    (i₁ : A₁ →+* T) (hf : Function.Injective f)
    (EA : Type) [CommRing EA] [Algebra A[X] EA] [Algebra A EA] [IsScalarTower A A[X] EA]
    [Algebra.Etale A[X] EA]
    (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O) (hcomp : i₁.comp f = i)
    (hj : jA.comp (algebraMap A[X] (Localization.AtPrime QA)) =
      (algebraMap T[X] O).comp (Polynomial.mapRingHom i))
    (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA] (q : ℕ)
    (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    0 < q → IsUnit (q : A) →
    GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA →
    ∀ a : A, a ≠ 0 →
    (∀ (P : Ideal (Localization.AtPrime QA)) [P.IsPrime],
      algebraMap A (Localization.AtPrime QA) a ∉ P →
      GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A (Localization.AtPrime QA) DA P) →
    ∀ (P₁ : Ideal (GlobalTheory.KeyOriginBC.Loc₁ f i i₁ EA QA jA hcomp hj)) [P₁.IsPrime], algebraMap A₁ (GlobalTheory.KeyOriginBC.Loc₁ f i i₁ EA QA jA hcomp hj) (f a) ∉ P₁ →
      GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A₁ (GlobalTheory.KeyOriginBC.Loc₁ f i i₁ EA QA jA hcomp hj) (GlobalTheory.KeyOriginBC.BC (GlobalTheory.KeyOriginBC.fibBC f i i₁ EA QA jA hcomp hj hf) DA) P₁ := by
  intro T O _ _ _ _ _ _ A A₁ _ _ _ _ _ _ _ _ _ _ _ _ f i i₁ hf EA _ _ _ _ _ QA _ jA hcomp hj DA _ _ q actA
    _ _ htors a _ hyp P₁ _ haP₁
  obtain ⟨hd, hn⟩ := GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_etale (Polynomial A₁)
    (ideal₁ f i i₁ EA QA jA hcomp hj) (Loc₁ f i i₁ EA QA jA hcomp hj)
  haveI := hd
  haveI := hn
  haveI : Module.Flat (Polynomial A₁) (Loc₁ f i i₁ EA QA jA hcomp hj) :=
    Module.Flat.trans (Polynomial A₁) (Ext f EA) (Loc₁ f i i₁ EA QA jA hcomp hj)
  have hA₁ : Function.Injective (algebraMap A₁ (Loc₁ f i i₁ EA QA jA hcomp hj)) := by
    have h1 : Function.Injective (algebraMap (Polynomial A₁) (Loc₁ f i i₁ EA QA jA hcomp hj)) := by

      exact FaithfulSMul.algebraMap_injective (Polynomial A₁) (Loc₁ f i i₁ EA QA jA hcomp hj)
    rw [IsScalarTower.algebraMap_eq A₁ (Polynomial A₁) (Loc₁ f i i₁ EA QA jA hcomp hj)]
    exact h1.comp Polynomial.C_injective
  haveI : Module.Finite (GenFib A (Localization.AtPrime QA)) DA := htors.1
  haveI : Algebra.IsIntegral (GenFib A (Localization.AtPrime QA)) DA := inferInstance
  have hκ : (locBC f i i₁ EA QA jA hcomp hj).comp (algebraMap A (Localization.AtPrime QA)) =
      (algebraMap A₁ (Loc₁ f i i₁ EA QA jA hcomp hj)).comp f :=
    RingHom.ext (locBC_algebraMap_base f i i₁ EA QA jA hcomp hj)
  have hβ : (fibBC f i i₁ EA QA jA hcomp hj hf).comp
      (algebraMap (Localization.AtPrime QA) (GenFib A (Localization.AtPrime QA))) =
      (algebraMap (Loc₁ f i i₁ EA QA jA hcomp hj) (GenFib A₁ (Loc₁ f i i₁ EA QA jA hcomp hj))).comp
        (locBC f i i₁ EA QA jA hcomp hj) :=
    RingHom.ext (fibBC_algebraMap f i i₁ EA QA jA hcomp hj hf)
  refine closureEtaleAt_bc A (Localization.AtPrime QA) A₁ (Loc₁ f i i₁ EA QA jA hcomp hj) f hf hA₁
    (locBC f i i₁ EA QA jA hcomp hj) hκ (fibBC f i i₁ EA QA jA hcomp hj hf) hβ DA P₁ ?_
  apply hyp
  rw [Ideal.mem_comap, ← RingHom.comp_apply, hκ, RingHom.comp_apply]
  exact haP₁

end GlobalTheory.KeyOriginBCEt
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

theorem _root_.GlobalTheory.T.leviMargin_orthonormal_chart_origin : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (x : Frame X.Ψ r) (g bb : ℝ), 0 < X.p0 → X.p0 < r → IsOrth X x → 0 ≤ g → 0 ≤ bb → (∀ τ (a b : Fin r), (b : ℕ) = a + 1 → (b : ℕ) ≠ X.p0 → g ≤ (la τ a : ℝ) - la τ b) → (∀ τ (a b : Fin r), (a : ℕ) = 0 → (b : ℕ) = r - 1 → g ≤ (la τ b : ℝ) - la τ a) → ∀ ξ : Fin (nd X) → ℂ, (g - bb - 2 * r) * ∑ j, ‖ξ j‖ ^ 2 ≤ leviM X (phla X la) x 0 ξ - bb * leviM X (phla X (GlobalTheory.CurvMargin.blockWt X)) x 0 ξ - leviM X (phla X (kapW X)) x 0 ξ := by
  first | exact @GlobalTheory.LeviOriginMargin.levi_margin_origin | exact GlobalTheory.LeviOriginMargin.levi_margin_origin | (intros; apply GlobalTheory.LeviOriginMargin.levi_margin_origin <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal Neutral.B1
open scoped nonZeroDivisors

theorem _root_.GlobalTheory.T.exists_continuous_bijective_abelianization_of_algEquiv : ∀ {K : Type} [Field K] [NumberField K] {Ω : Type} [Field Ω] [Algebra K Ω] (e : Ω ≃ₐ[K] AlgebraicClosure K), ∃ φ : GlobalTheory.HeckeGal.Gab K Ω →* Field.absoluteGaloisGroupAbelianization K, Continuous φ ∧ Function.Bijective φ ∧ ∀ σ : Formalism.ConjugateSelfDual.G K Ω, φ (GlobalTheory.HeckeGal.toAb K Ω σ) = Neutral.B1.toAb K ((e.symm.trans σ).trans e) := by
  first | exact @GlobalTheory.HeckeGal.exists_abMap_of_algEquiv | exact GlobalTheory.HeckeGal.exists_abMap_of_algEquiv | (intros; apply GlobalTheory.HeckeGal.exists_abMap_of_algEquiv <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal Neutral.B1
open scoped nonZeroDivisors

theorem _root_.GlobalTheory.T.ideleClass_identityComponent_iff_artin_kernel : ∀ {K : Type} [Field K] [NumberField K] {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] {art : Ideles K →* GlobalTheory.HeckeGal.Gab K Ω}, GlobalTheory.HeckeGal.IsGlobalArtin art → ∀ s : Ideles K, (QuotientGroup.mk s : IdeleClassGroup K) ∈ connectedComponent (1 : IdeleClassGroup K) ↔ art s = 1 := by
  first | exact @GlobalTheory.ArtinKernel.idele_class_mem_identity_component_iff | exact GlobalTheory.ArtinKernel.idele_class_mem_identity_component_iff | (intros; apply GlobalTheory.ArtinKernel.idele_class_mem_identity_component_iff <;> assumption)
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.extension_across_hypersurface_values_at_zeros : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), 1 ≤ n → ∀ (E L : La) (s : Fin n → ι → Y → ℂ), (∀ k, A.IsSec L (s k)) → ∀ hS : (A.zeroSet s).Finite, (∀ P ∈ A.zeroSet s, jacAt A s P ≠ 0) → (∀ y, A.sqn L s y ≤ 1) → ∀ δ : ℝ, 0 < δ → ∀ (Λ : La) (τ : ι → Y → ℂ), A.IsSec Λ τ → Dense (nz A τ) → ∀ (Ω : Set Y) (h : ι → Y → ℂ) (T : ℝ) (θ : ℝ → ℝ), (IsOpen Ω ∧ A.IsSecOn (A.kap + E) Ω h ∧ (∀ i y, y ∉ Ω → h i y = 0)) → A.zeroSet s ⊆ Ω → IsCut T θ → ∫⁻ y, ENNReal.ofReal (A.nsq (A.kap + E) h y) ∂A.mu < ⊤ → ∀ F : ι → Y → ℂ, A.IsSecOn (A.kap + E) (nz A τ) F → ∫⁻ y in nz A τ, ENNReal.ofReal (A.nsq (A.kap + E) (fun i x => (θ (δ * psi A L s x) : ℂ) * h i x - F i x) y * (wT T (δ * psi A L s y) * Real.exp (-psi A L s y))) ∂A.mu < ⊤ → ∃ G : ι → Y → ℂ, A.IsSec (A.kap + E) G ∧ (∀ i y, y ∈ nz A τ → y ∈ (A.chart i).source → G i y = F i y) ∧ ∀ P ∈ A.zeroSet s, G (A.pick P) P = h (A.pick P) P := by
  first | exact @GlobalTheory.OTY.extension_values_at_zeros | exact GlobalTheory.OTY.extension_values_at_zeros | (intros; apply GlobalTheory.OTY.extension_values_at_zeros <;> assumption)
end
