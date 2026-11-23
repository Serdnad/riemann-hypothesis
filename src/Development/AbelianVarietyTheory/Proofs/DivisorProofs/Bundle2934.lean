module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle071
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2680
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2744
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
import Batteries.Tactic.Lint.Basic
import Batteries.Tactic.Lint.Misc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle222
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle223
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1871
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1780
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2829
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2662
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2564
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
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
import Mathlib.RingTheory.TotallySplit
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

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Points
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.Special

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

section Model

variable {o Ω o' Ω' : Type} [CommRing o] [Field Ω] [Algebra o Ω] [CommRing o'] [Field Ω'] [Algebra o' Ω']
  [Algebra Ω Ω'] {M : RatModel o Ω} {M' : RatModel o' Ω'} {f : M'.Z ⟶ M.Z}

theorem valF_app_of (hf : M'.pt ≫ f = spMap (algebraMap Ω Ω') ≫ M.pt) {U : M.Z.Opens}
    (hU : (U : Set M.Z).Nonempty) (a : Γ(M.Z, U)) :
    valF M'.pt (f ⁻¹ᵁ U) (f.app U a) = algebraMap Ω Ω' (valF M.pt U a) := by
  refine (valR_comp M'.pt f U a).symm.trans ?_
  rw [hf]
  exact valR_spMap_comp _ M.pt U (M.top_le_preimage_pt hU) a

theorem map_mem_O_of (hf : M'.pt ≫ f = spMap (algebraMap Ω Ω') ≫ M.pt) {z : M'.Z} {x : Ω}
    (hx : x ∈ M.O (f z)) : algebraMap Ω Ω' x ∈ M'.O z := by
  obtain ⟨U, a, hz, rfl⟩ := hx
  exact ⟨f ⁻¹ᵁ U, f.app U a, hz, valF_app_of hf ⟨_, hz⟩ a⟩

theorem val_comp_of (hf : M'.pt ≫ f = spMap (algebraMap Ω Ω') ≫ M.pt) {K : Type} [Field K] (y : Sp K ⟶ M'.Z)
    (w : Sp K) {x : Ω} (hx : x ∈ M.O (f (y w))) : M.val (y ≫ f) x = M'.val y (algebraMap Ω Ω' x) := by
  obtain ⟨U, a, hz, rfl⟩ := hx
  have h1 : Set.range y ⊆ (f ⁻¹ᵁ U : M'.Z.Opens) := by
    rw [RatModel.range_eq_singleton y w, Set.singleton_subset_iff]
    exact hz
  rw [RatModel.val_eq h1 (valF_app_of hf ⟨_, hz⟩ a), RatModel.val_valF (U := U) (by rintro _ ⟨w', rfl⟩; exact h1 ⟨w', rfl⟩)]
  exact valR_comp y f U a

end Model

section Pts

variable {K C : Type} [CommRing K] [CommRing C] {A : Over (Sp K)}

theorem pt_iff_eq {R : Type} [CommRing R] {G : Over (Sp R)} {h : R →+* K} {a : A.left ⟶ G.left}
    (c : IsPullback a A.hom G.hom (spMap h)) (j : K →+* C) {s : Sp R ⟶ G.left} {w : Sp K ⟶ A.left}
    (hw : w ≫ A.hom = 𝟙 _) (hs : w ≫ a = spMap h ≫ s) (x : Sp C ⟶ A.left) (hx : x ≫ A.hom = spMap j) :
    x ≫ a = spMap (j.comp h) ≫ s ↔ x = spMap j ≫ w := by
  rw [spMap_comp', Category.assoc, ← hs]
  constructor
  · intro e
    exact c.hom_ext (by rw [e, Category.assoc]) (by rw [hx, Category.assoc, hw, Category.comp_id])
  · intro e
    rw [e, Category.assoc]

theorem end_iff_eq {S : Scheme.{0}} {G : Over S} {f : Sp K ⟶ S} {a : A.left ⟶ G.left}
    (c : IsPullback a A.hom G.hom f) {ε : G.left ⟶ G.left} {e : A.left ⟶ A.left} (he : e ≫ A.hom = A.hom)
    (he' : e ≫ a = a ≫ ε) {T : Scheme.{0}} (x x' : T ⟶ A.left) (hx : x' ≫ A.hom = x ≫ A.hom) :
    x' ≫ a = x ≫ a ≫ ε ↔ x' = x ≫ e := by
  rw [← he', ← Category.assoc]
  constructor
  · intro k
    exact c.hom_ext k (by rw [Category.assoc, he, hx])
  · intro k
    rw [k]

end Pts

end GlobalTheory.Poinc.Special

theorem GlobalTheory.Poinc.Special.specialise_sameAt : ∀ (R₁ R₂ B K M Γ : Type) [CommRing R₁] [CommRing R₂] [CommRing B] [CommRing K] (P₁ : PolAV (Sp R₁)) (P₂ : PolAV (Sp R₂)) (f₁ : R₁ →+* B) (f₂ : R₂ →+* B) (e₁ : M → (P₁.A ⟶ P₁.A)) (e₂ : M → (P₂.A ⟶ P₂.A)) (t₁ : Γ → (baseOver (Sp R₁) ⟶ P₁.A)) (t₂ : Γ → (baseOver (Sp R₂) ⟶ P₂.A)), SameAt P₁ P₂ f₁ f₂ e₁ e₂ t₁ t₂ → (∀ τ : B →+* B, τ.comp f₂ = f₂ → τ = RingHom.id B) → ∀ (v : B →+* K) (A₁ : PolAV (Sp K)) (a₁ : A₁.A.left ⟶ P₁.A.left), IsGrpPullback A₁.A P₁.A (spMap (v.comp f₁)) a₁ → LBIso A₁.L (P₁.L.pull a₁) → ∃ φ₂ : A₁.A.left ⟶ P₂.A.left, IsGrpPullback A₁.A P₂.A (spMap (v.comp f₂)) φ₂ ∧ LBIso A₁.L (P₂.L.pull φ₂) ∧ (∀ E, ∃ e : A₁.A.left ⟶ A₁.A.left, e ≫ A₁.A.hom = A₁.A.hom ∧ e ≫ a₁ = a₁ ≫ (e₁ E).left ∧ e ≫ φ₂ = φ₂ ≫ (e₂ E).left) ∧ ∀ x, ∃ w : Sp K ⟶ A₁.A.left, w ≫ A₁.A.hom = 𝟙 _ ∧ w ≫ a₁ = spMap (v.comp f₁) ≫ (t₁ x).left ∧ w ≫ φ₂ = spMap (v.comp f₂) ≫ (t₂ x).left := by
  intro R₁ R₂ B K M Γ _ _ _ _ P₁ P₂ f₁ f₂ e₁ e₂ t₁ t₂ hS hrig v A₁ a₁ ha₁ hL₁
  obtain ⟨P, b₁, b₂, hb₁, hb₂, hLb₁, hLb₂, hε, ht⟩ := hS
  have hv₁ : spMap (v.comp f₁) = spMap v ≫ spMap f₁ := GlobalTheory.Poinc.Special.spMap_comp' f₁ v
  have hv₂ : spMap (v.comp f₂) = spMap v ≫ spMap f₂ := GlobalTheory.Poinc.Special.spMap_comp' f₂ v
  have sq : a₁ ≫ P₁.A.hom = (A₁.A.hom ≫ spMap v) ≫ spMap f₁ := by
    rw [ha₁.1.w, hv₁, Category.assoc]
  let b : A₁.A.left ⟶ P.A.left := hb₁.1.lift a₁ (A₁.A.hom ≫ spMap v) sq
  have hb_a : b ≫ b₁ = a₁ := hb₁.1.lift_fst _ _ _
  have hb_s : b ≫ P.A.hom = A₁.A.hom ≫ spMap v := hb₁.1.lift_snd _ _ _
  have hbP : IsGrpPullback A₁.A P.A (spMap v) b :=
    IsGrpPullback.cancel hb₁ (ha₁.congr hv₁ hb_a.symm) hb_s
  refine ⟨b ≫ b₂, (hbP.comp hb₂).congr hv₂.symm rfl, ?_, fun E => ?_, fun x => ?_⟩
  · have i1 : LBIso (P.L.pull b) (P₁.L.pull a₁) := GlobalTheory.PolDeg.lbIso_pull_comp hLb₁ b hb_a.symm
    have i2 : LBIso (P.L.pull b) (P₂.L.pull (b ≫ b₂)) := GlobalTheory.PolDeg.lbIso_pull_comp hLb₂ b rfl
    exact (hL₁.trans A₁.isLB (pull_isLB P₁.isLB _) (pull_isLB P.isLB _) i1.symm).trans A₁.isLB
      (pull_isLB P.isLB _) (pull_isLB P₂.isLB _) i2
  · obtain ⟨eP, heP₁, heP₂⟩ := hε E
    have sqe : (a₁ ≫ (e₁ E).left) ≫ P₁.A.hom = A₁.A.hom ≫ spMap (v.comp f₁) := by
      rw [Category.assoc, Over.w (e₁ E), ha₁.1.w]
    let e : A₁.A.left ⟶ A₁.A.left := ha₁.1.lift (a₁ ≫ (e₁ E).left) A₁.A.hom sqe
    have he₁ : e ≫ a₁ = a₁ ≫ (e₁ E).left := ha₁.1.lift_fst _ _ _
    have he : e ≫ A₁.A.hom = A₁.A.hom := ha₁.1.lift_snd _ _ _
    have heb : e ≫ b = b ≫ eP.left := hb₁.1.hom_ext
      (by rw [Category.assoc, hb_a, he₁, Category.assoc, heP₁, ← Category.assoc, hb_a])
      (by rw [Category.assoc, hb_s, ← Category.assoc, he, Category.assoc, Over.w eP, hb_s])
    exact ⟨e, he, he₁, by rw [← Category.assoc, heb, Category.assoc, heP₂, Category.assoc]⟩
  · obtain ⟨w, hw₁, hw₂⟩ := ht x
    have hσ : spMap ((Spec.preimage (w ≫ P.A.hom)).hom) = w ≫ P.A.hom := by
      rw [spMap, CommRingCat.ofHom_hom, Spec.map_preimage]
    have hσ₂ : (w ≫ P.A.hom) ≫ spMap f₂ = spMap f₂ := by
      rw [Category.assoc, ← hb₂.1.w, ← Category.assoc, hw₂, Category.assoc, Over.w (t₂ x)]
      exact Category.comp_id _
    have hτ : (Spec.preimage (w ≫ P.A.hom)).hom.comp f₂ = f₂ := by
      have h1 : spMap ((Spec.preimage (w ≫ P.A.hom)).hom.comp f₂) = spMap f₂ := by
        rw [GlobalTheory.Poinc.Special.spMap_comp', hσ, hσ₂]
      exact congrArg CommRingCat.Hom.hom (Spec.map_inj.1 h1)
    have hwP : w ≫ P.A.hom = 𝟙 _ := by
      rw [← hσ, hrig _ hτ]
      exact Spec.map_id _
    have sqt : (spMap (v.comp f₁) ≫ (t₁ x).left) ≫ P₁.A.hom = 𝟙 _ ≫ spMap (v.comp f₁) := by
      rw [Category.assoc, Over.w (t₁ x), Category.id_comp]
      exact Category.comp_id _
    let w' : Sp K ⟶ A₁.A.left := ha₁.1.lift (spMap (v.comp f₁) ≫ (t₁ x).left) (𝟙 _) sqt
    have hw'₁ : w' ≫ a₁ = spMap (v.comp f₁) ≫ (t₁ x).left := ha₁.1.lift_fst _ _ _
    have hw' : w' ≫ A₁.A.hom = 𝟙 _ := ha₁.1.lift_snd _ _ _
    have hw'b : w' ≫ b = spMap v ≫ w := hb₁.1.hom_ext
      (by rw [Category.assoc, hb_a, hw'₁, hv₁, Category.assoc, Category.assoc, hw₁])
      (by rw [Category.assoc, hb_s, ← Category.assoc, hw', Category.id_comp, Category.assoc, hwP,
        Category.comp_id])
    exact ⟨w', hw', hw'₁, by rw [← Category.assoc, hw'b, Category.assoc, hw₂, hv₂, Category.assoc]⟩


open GlobalTheory.Poinc.Special in
theorem GlobalTheory.Poinc.special_transport : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (c : CTrait X₁ p z₁) (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y)
  (c₀ : X₁.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X₁.o₁ X₁.Ω₁) (fg : R'.FG) (frac : ∀ x : X₁.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X₁.S.th x ∈ R') (hev : ∀ x k, c₀ * X₁.S.ev x k ∈ R') (ρ' : (X₁.S.rechart c₀ hc R' fg frac hth hev).Real) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (ρ'.P.A ⟶ ρ'.P.A)), R' ≤ X₁.M.O ((gPt p ≫ c.y) (closedPoint (PadicAlgCl p))) → ∀ (y₀ : R' →+* PadicAlgCl p), (∀ a : R', y₀ a = X₁.M.val (gPt p ≫ c.y) a) →
  ∀ (c₂ : D.X.Ω₁) (hc₂ : c₂ ≠ 0) (R₂ : Subalgebra D.X.o₁ D.X.Ω₁) (fg₂ : R₂.FG) (frac₂ : ∀ x : D.X.Ω₁, ∃ a ∈ R₂, ∃ b ∈ R₂, x = a / b) (hth₂ : ∀ x, c₂ * D.X.S.th x ∈ R₂) (hev₂ : ∀ x k, c₂ * D.X.S.ev x k ∈ R₂) (ρ₂ : (D.X.S.rechart c₂ hc₂ R₂ fg₂ frac₂ hth₂ hev₂).Real) (ε₂ : Matrix (Fin 8) (Fin 8) ℤ → (ρ₂.P.A ⟶ ρ₂.P.A)), Same ρ' ε' ρ₂ ε₂ (fun a => D.lab a) (algebraMap X₁.Ω₁ D.X.Ω₁) → R₂ ≤ D.X.M.O ((gPt p ≫ y) (closedPoint (PadicAlgCl p))) → ∀ (y₂ : R₂ →+* PadicAlgCl p), (∀ a : R₂, y₂ a = D.X.M.val (gPt p ≫ y) a) →
  ∀ (K : Type) [Field K] (j : K →+* PadicAlgCl p) (f' : R' →+* K), j.comp f' = y₀ → (∀ a ∈ D.X.M.O ((gPt p ≫ y) (closedPoint (PadicAlgCl p))), D.X.M.val (gPt p ≫ y) a ∈ j.range) →
  ∀ (A₁ : PolAV (Sp K)) (a₁ : A₁.A.left ⟶ ρ'.P.A.left), IsGrpPullback A₁.A ρ'.P.A (spMap f') a₁ → LBIso A₁.L (ρ'.P.L.pull a₁) →
  ∃ (f₂ : R₂ →+* K) (φ₂ : A₁.A.left ⟶ ρ₂.P.A.left), j.comp f₂ = y₂ ∧ IsGrpPullback A₁.A ρ₂.P.A (spMap f₂) φ₂ ∧ LBIso A₁.L (ρ₂.P.L.pull φ₂) ∧
    (∀ (x : Sp (PadicAlgCl p) ⟶ A₁.A.left) (a : X₁.S.Gam), x ≫ A₁.A.hom = spMap j → (x ≫ φ₂ = spMap y₂ ≫ (ρ₂.pt (D.lab a)).left ↔ x ≫ a₁ = spMap y₀ ≫ (ρ'.pt a).left)) ∧
    (∀ (x x' : Sp (PadicAlgCl p) ⟶ A₁.A.left) (E : Matrix (Fin 8) (Fin 8) ℤ), x ≫ A₁.A.hom = spMap j → x' ≫ A₁.A.hom = spMap j → (x' ≫ φ₂ = x ≫ φ₂ ≫ (ε₂ E).left ↔ x' ≫ a₁ = x ≫ a₁ ≫ (ε' E).left)) := by
  intro g n F W Z i X₁ _ _ _ _ _ _ _ ε₁ _ D p _ z₁ c y h c₀ hc R' fg frac hth hev ρ' ε' hR' y₀ hy₀ c₂ hc₂ R₂ fg₂ frac₂
    hth₂ hev₂ ρ₂ ε₂ hsame hR₂ y₂ hy₂ K _ j f' hf' hval A₁ a₁ ha₁ hL₁

  set x₂ := (gPt p ≫ y) (closedPoint (PadicAlgCl p)) with hx₂
  have hx₁ : (gPt p ≫ c.y) (closedPoint (PadicAlgCl p)) = D.q x₂ := by
    rw [← h, ← Category.assoc]; rfl
  haveI : IsDedekindDomain D.X.o₁ := ArithBase.ded (Ω := D.X.Ω₁)
  haveI : IsNoetherianRing (D.X.M.O x₂) := D.X.M.isNoetherianRing_O x₂
  haveI : IsIntegrallyClosed (D.X.M.O x₂) := haveI := D.X.normal; RatModel.isIntegrallyClosed_O (GlobalTheory.IsNormalScheme.pred _) x₂
  have hmem : ∀ a : R', algebraMap X₁.Ω₁ D.X.Ω₁ a ∈ D.X.M.O x₂ := fun a =>
    map_mem_O_of D.gen (hx₁ ▸ hR' a.2)
  let g₁ : R' →+* D.X.M.O x₂ := ((algebraMap X₁.Ω₁ D.X.Ω₁).comp R'.val.toRingHom).codRestrict _ hmem
  let g₂ : R₂ →+* D.X.M.O x₂ := (Subalgebra.inclusion hR₂).toRingHom
  have e₁ : (algebraMap (D.X.M.O x₂) D.X.Ω₁).comp g₁ = (algebraMap X₁.Ω₁ D.X.Ω₁).comp R'.val.toRingHom :=
    RingHom.ext fun _ => rfl
  have e₂ : (algebraMap (D.X.M.O x₂) D.X.Ω₁).comp g₂ = R₂.val.toRingHom := RingHom.ext fun _ => rfl

  have hS₀ : SameAt ρ'.P ρ₂.P ((algebraMap (D.X.M.O x₂) D.X.Ω₁).comp g₁) ((algebraMap (D.X.M.O x₂) D.X.Ω₁).comp g₂)
      ε' ε₂ ρ'.pt (fun a => ρ₂.pt (D.lab a)) := by
    rw [e₁, e₂]
    obtain ⟨P₀, a, a', ε₀, h1, h2, h3, h4, h5, h6⟩ := hsame
    exact ⟨P₀, a, a', h1, h2, h3, h4, fun E => ⟨ε₀ E, (h5 E).1, (h5 E).2⟩, h6⟩
  have hSO := GlobalTheory.Poinc.sameAt_of_generic _ _ _ _ _ _ ρ'.P ρ₂.P g₁ g₂ ε' ε₂ _ _ hS₀

  let vO : D.X.M.O x₂ →+* PadicAlgCl p :=
    D.X.M.valHom (gPt p ≫ y) x₂ (RatModel.range_eq_singleton _ _)
  have hvr : ∀ a, vO a ∈ j.range := fun a => hval a a.2
  let jE : K ≃+* j.range := RingEquiv.ofBijective j.rangeRestrict ⟨fun a b hab => j.injective
    (congrArg Subtype.val hab), j.rangeRestrict_surjective⟩
  let v : D.X.M.O x₂ →+* K := jE.symm.toRingHom.comp (vO.codRestrict j.range hvr)
  have hjv : ∀ a, j (v a) = vO a := fun a => congrArg Subtype.val (jE.apply_symm_apply (vO.codRestrict j.range hvr a))
  have hf₂ : j.comp (v.comp g₂) = y₂ := RingHom.ext fun a => (hjv _).trans (hy₂ a).symm
  have hf'v : f' = v.comp g₁ := RingHom.ext fun a => j.injective <| by
    rw [← RingHom.comp_apply j f', hf', hy₀ a, RingHom.comp_apply, hjv]
    show X₁.M.val (gPt p ≫ c.y) a = D.X.M.val (gPt p ≫ y) (algebraMap X₁.Ω₁ D.X.Ω₁ a)
    rw [← h, ← Category.assoc]
    have hm : (a : X₁.Ω₁) ∈ X₁.M.O (D.q ((gPt p ≫ y) (closedPoint (PadicAlgCl p)))) := hx₁ ▸ hR' a.2
    exact val_comp_of D.gen (gPt p ≫ y) (closedPoint (PadicAlgCl p)) hm
  subst hf'v
  have hrig : ∀ τ : D.X.M.O x₂ →+* D.X.M.O x₂, τ.comp g₂ = g₂ → τ = RingHom.id _ := by
    intro τ hτ
    refine RingHom.ext fun x => ?_
    show τ x = x
    obtain ⟨a, ha, b, hb, hab⟩ := frac₂ x
    have hτa : ∀ r : R₂, τ (g₂ r) = g₂ r := fun r => RingHom.congr_fun hτ r
    by_cases hb0 : b = 0
    · have hx0 : x = 0 := Subtype.ext (by rw [hab, hb0, div_zero]; rfl)
      rw [hx0, map_zero]
    · have key : g₂ ⟨b, hb⟩ * x = g₂ ⟨a, ha⟩ := Subtype.ext (by
        show b * (x : D.X.Ω₁) = a
        rw [hab, mul_div_cancel₀ _ hb0])
      have h0 : g₂ ⟨b, hb⟩ ≠ 0 := fun h0 => hb0 (congrArg Subtype.val h0)
      have key' := congrArg τ key
      rw [map_mul, hτa, hτa, ← key] at key'
      exact mul_left_cancel₀ h0 key'
  obtain ⟨φ₂, hφ₂, hL₂, hε, ht⟩ := (GlobalTheory.Poinc.Special.specialise_sameAt) _ _ _ _ _ _ ρ'.P ρ₂.P g₁ g₂ ε' ε₂ _ _ hSO hrig v A₁ a₁ ha₁ hL₁
  refine ⟨v.comp g₂, φ₂, hf₂, hφ₂, hL₂, fun x a hx => ?_, fun x x' E hx hx' => ?_⟩
  · obtain ⟨w, hw, hw₁, hw₂⟩ := ht a
    rw [← hf₂, ← hf', pt_iff_eq hφ₂.1 j hw hw₂ x hx, pt_iff_eq ha₁.1 j hw hw₁ x hx]
  · obtain ⟨e, he, he₁, he₂⟩ := hε E
    rw [end_iff_eq hφ₂.1 he he₂ x x' (hx'.trans hx.symm), end_iff_eq ha₁.1 he he₁ x x' (hx'.trans hx.symm)]
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.LieTens

open GlobalTheory.Serre Matrix

theorem finrank_int_eq (E : Type) [Field E] [NumberField E] (N : Type) [AddCommGroup N]
    [Module (𝓞 E) N] [Module.Free ℤ N] [Module.Finite ℤ N] :
    Module.finrank ℤ N = Module.finrank (𝓞 E) N * Module.finrank ℚ E :=
  GlobalTheory.T.finrank_int_eq_finrank_ringOfIntegers_mul' E N

theorem isTorsionFree_of_int (E : Type) [Field E] [NumberField E] (N : Type) [AddCommGroup N]
    [Module (𝓞 E) N] [Module.IsTorsionFree ℤ N] : Module.IsTorsionFree (𝓞 E) N :=
  GlobalTheory.T.isTorsionFree_ringOfIntegers_of_isTorsionFree_int' E N

variable {E : Type} [Field E] [NumberField E] {r : ℕ}

@[nolint unusedArguments]
def Lat (_ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ) : Type := Fin r → 𝓞 ℚ

variable (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ)

instance : AddCommGroup (Lat ρ) := inferInstanceAs (AddCommGroup (Fin r → 𝓞 ℚ))
instance : Module (𝓞 ℚ) (Lat ρ) := inferInstanceAs (Module (𝓞 ℚ) (Fin r → 𝓞 ℚ))

def endOf : 𝓞 E →+* Module.End (𝓞 ℚ) (Fin r → 𝓞 ℚ) :=
  (Matrix.toLinAlgEquiv' : Matrix (Fin r) (Fin r) (𝓞 ℚ) ≃ₐ[𝓞 ℚ] _).toRingEquiv.toRingHom.comp
    ((Int.castRingHom (𝓞 ℚ)).mapMatrix.comp ρ)

instance : Module (𝓞 E) (Lat ρ) := Module.compHom (Fin r → 𝓞 ℚ) (endOf ρ)

def latEquiv : Lat ρ ≃ₗ[𝓞 ℚ] (Fin r → 𝓞 ℚ) := LinearEquiv.refl _ _

instance : IsScalarTower (𝓞 ℚ) (𝓞 E) (Lat ρ) := by
  refine ⟨fun q c v => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, q = n :=
    ⟨Rat.ringOfIntegersEquiv q, Rat.ringOfIntegersEquiv.injective (by rw [map_intCast, Int.cast_id])⟩
  show endOf ρ ((n : 𝓞 ℚ) • c) (show Fin r → 𝓞 ℚ from v) = (n : 𝓞 ℚ) • endOf ρ c (show Fin r → 𝓞 ℚ from v)
  rw [Algebra.smul_def, map_intCast, map_mul, map_intCast, Module.End.mul_apply, Module.End.intCast_apply,
    Int.cast_smul_eq_zsmul]

instance : Module.Finite (𝓞 ℚ) (Lat ρ) := inferInstanceAs (Module.Finite (𝓞 ℚ) (Fin r → 𝓞 ℚ))

instance : Module.Finite (𝓞 E) (Lat ρ) := Module.Finite.of_restrictScalars_finite (𝓞 ℚ) (𝓞 E) (Lat ρ)

def intEquiv : (Fin r → ℤ) ≃ₗ[ℤ] Lat ρ :=
  (LinearEquiv.piCongrRight fun _ => (Rat.ringOfIntegersEquiv.symm : ℤ ≃+* 𝓞 ℚ).toAddEquiv.toIntLinearEquiv)

instance : Module.Free ℤ (Lat ρ) := Module.Free.of_equiv (intEquiv ρ)

instance : Module.Finite ℤ (Lat ρ) := Module.Finite.equiv (intEquiv ρ)

theorem finrank_lat_int : Module.finrank ℤ (Lat ρ) = r := by
  rw [← LinearEquiv.finrank_eq (intEquiv ρ), Module.finrank_fin_fun]

instance : Module.Projective (𝓞 E) (Lat ρ) := by
  haveI : Module.IsTorsionFree (𝓞 E) (Lat ρ) := isTorsionFree_of_int E (Lat ρ)
  haveI : Module.FinitePresentation (𝓞 E) (Lat ρ) := Module.finitePresentation_of_finite _ _
  exact Module.Flat.projective_of_finitePresentation

end GlobalTheory.Mum.LieTens

namespace GlobalTheory.Mum.LieTens

open GlobalTheory.Serre

theorem eig_eq_top {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    (a : OAct (𝓞 ℚ) G) (τ₀ : 𝓞 ℚ →+* R) : Lie.eig a τ₀ = ⊤ := by
  refine eq_top_iff.mpr fun v _ x => ?_
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, x = n :=
    ⟨Rat.ringOfIntegersEquiv x, Rat.ringOfIntegersEquiv.injective (by rw [map_intCast, Int.cast_id])⟩
  rw [map_intCast, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]

theorem lieMult_int {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (a : OAct (𝓞 ℚ) G)
    {g : ℕ} (hG : SmoothOfRelativeDimension g G.hom) {F : Type} [Field F] (t : Sp F ⟶ S)
    (τ₀ : 𝓞 ℚ →+* F) : LieMult a t τ₀ g := by
  rw [Lie.lieMult_iff_finrank (isLinearPullback_pullback a t)]
  have hs : SmoothOfRelativeDimension g ((Over.pullback t).obj G).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) hG
  obtain ⟨v, hv⟩ := GlobalTheory.KeyPow.exists_isLieBasis ((Over.pullback t).obj G) hs
  have b := Lie.basis (a.pullback t) hv
  rw [eig_eq_top]
  refine ⟨?_, ?_⟩
  · haveI := Module.Finite.of_basis b
    exact Module.Finite.equiv (LinearEquiv.ofTop ⊤ rfl).symm
  · rw [finrank_top, Module.finrank_eq_card_basis b, Fintype.card_fin]

end GlobalTheory.Mum.LieTens

namespace GlobalTheory.Mum.LieTens

open GlobalTheory.Serre

theorem act_eq {S : Scheme.{0}} {O : Type} [CommRing O] {G : Over S} [GrpObj G] (x y : OAct O G)
    (h : ∀ c, x.act c = y.act c) : x = y := by
  obtain ⟨_, _, _, _, _⟩ := x
  obtain ⟨_, _, _, _, _⟩ := y
  simp only [OAct.mk.injEq]
  exact funext h

theorem comapAct_intCast {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (n : ℤ) :
    (comapAct (intAct G) (Rat.ringOfIntegersEquiv : 𝓞 ℚ →+* ℤ)).act (n : 𝓞 ℚ) = (𝟙 G) ^ n := by
  rw [comapAct_act, intAct_act, map_intCast, Int.cast_id]

end GlobalTheory.Mum.LieTens

namespace GlobalTheory.Mum

open GlobalTheory.Serre GlobalTheory.Mum.LieTens

theorem lieMult_tens : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) , ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det → ∀ T : Tens D.toPre D'.toPre W, ∀ (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ) [Module (𝓞 E) D'.toPre.X] (o : letI := H.starRing; D'.toPre.OAct (𝓞 E)), (letI := H.starRing; T.IsAct o ρ) → ∀ s : ℕ, r = s * Module.finrank ℚ E → Module.finrank (𝓞 E) D'.toPre.X = s * Module.finrank ℤ D.toPre.X ∧ ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (τ : 𝓞 E →+* F), LieMult (letI := H.starRing; ofRingAct o.onB.toRingAct) (spMap ((algebraMap (FractionRing R) F).comp (algebraMap R _))) τ (s * D.toPre.P.g) := by
  intro R _ _ _ hB E _ _ _ H D D' r W _ _ T ρ _ o hact s hrs
  refine ⟨?_, ?_⟩
  · have h1 := finrank_int_eq E D'.toPre.X
    have h2 : Module.finrank ℤ D'.toPre.X = r * Module.finrank ℤ D.toPre.X := by
      rw [LinearEquiv.finrank_eq T.xe.toIntLinearEquiv, Module.finrank_pi_fintype]
      simp
    rw [h2, hrs] at h1
    have hpos : 0 < Module.finrank ℚ E := Module.finrank_pos
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [← h1]
    ring
  · intro F _ _ _ τ
    letI := H.starRing
    haveI : CharZero R := hB.2
    haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap (FractionRing R) F).injective
    let p : IsPowGrp D'.toPre.P.A D.toPre.P.A r := ⟨T.pr, T.pr_hom, T.lim⟩
    let a₀ : OAct (𝓞 ℚ) D.toPre.P.A := comapAct (intAct D.toPre.P.A) (Rat.ringOfIntegersEquiv : 𝓞 ℚ →+* ℤ)
    let h₀ := IsTensor.pow p a₀
    let h := h₀.congrLeft (latEquiv ρ)
    have hn := lieMult_int a₀ D.toPre.P.smoothDim
      (spMap ((algebraMap (FractionRing R) F).comp (algebraMap R _))) (τ.comp (algebraMap (𝓞 ℚ) (𝓞 E)))
    have hm := h.lieMult (K := ℚ) _ τ hn
    have key : ∀ c : 𝓞 E, (h.algAct (𝓞 E)).act c = o.onB.act c := by
      intro c
      have e1 : (h.algAct (𝓞 E)).act c = h₀.mapLeft h₀ (Matrix.toLin' ((ρ c).map (Int.cast : ℤ → 𝓞 ℚ))) := by
        haveI := (h.algAct (𝓞 E)).hom c
        refine h.hom_ext fun m => ?_
        rw [IsTensor.tmul_algAct, IsTensor.congrLeft_tmul, IsTensor.congrLeft_tmul, IsTensor.tmul_mapLeft]
        rfl
      refine pow_hom_ext p fun i => ?_
      rw [e1, IsTensor.pow_mapLeft_pr]
      rw [show p.pr i = T.pr i from rfl, hact.2 c i]
      refine Finset.prod_congr rfl fun j _ => ?_
      show T.pr j ≫ a₀.act ((ρ c i j : ℤ) : 𝓞 ℚ) = T.pr j ^ ρ c i j
      rw [comapAct_intCast, GrpObj.comp_zpow, Category.comp_id]
    have hact' : h.algAct (𝓞 E) = (letI := H.starRing; ofRingAct o.onB.toRingAct) := act_eq _ _ key
    have hfr : Module.finrank (𝓞 E) (Lat ρ) = s := by
      have h1 := finrank_int_eq E (Lat ρ)
      rw [finrank_lat_int] at h1
      have h3 : s * Module.finrank ℚ E = Module.finrank (𝓞 E) (Lat ρ) * Module.finrank ℚ E := by
        rw [← hrs]; exact h1
      have hpos : 0 < Module.finrank ℚ E := Module.finrank_pos
      exact (Nat.eq_of_mul_eq_mul_right hpos h3).symm
    rwa [hact', hfr, Nat.mul_comm] at hm

end GlobalTheory.Mum
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct

namespace GlobalTheory.FunObj

open GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem commutesWith_of_isSquareConst_of_triple (hWC : GlobalTheory.SquareSt.WeilConvergence)
    (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree) (hP : GlobalTheory.Published.CuspDecayBound)
    {μ₀ : T} (hL : L.Is μ₀) {W : G.Weil} {B : Frames G} {ρ : RealMatch W} {t : T} {i j : Fin D.R.m}
    (hT : SquareTriple W t i j) {c : ℂ} (hc : IsSquareConst W B ρ t i j c) : CommutesWith W B ρ t i j c := by
  intro M hM Θ Θ' hΘ F hF hFc hFl hA hB
  funext g₁
  obtain ⟨hBa, hBe⟩ := GlobalTheory.T.thetaLift_eq_integral_routeKernel_fubini hWC hK hP hL W B ρ t i j hT M hM Θ Θ' hΘ F hF hFc hFl hA g₁
  obtain ⟨z, hz, hSa, hSe⟩ := GlobalTheory.T.exists_theta_translates_convergent_lift_degree hWC hK hP hL W B ρ t i j hT M hM Θ Θ' hΘ F hF hFc hFl hB g₁
  refine mul_left_cancel₀ hz ?_
  rw [Pi.smul_apply, smul_eq_mul, hBe, mul_left_comm, hSe, ← integral_const_mul, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hBa, hSa] with g hb hs
  have h := hc M hM Θ Θ' hΘ z g g₁ ⟨hb, hs⟩
  linear_combination F g * h

theorem commutesWith_of_isSquareConst (hWC : GlobalTheory.SquareSt.WeilConvergence) (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree)
    (hP : GlobalTheory.Published.CuspDecayBound) {μ₀ : T} (hL : L.Is μ₀) {W : G.Weil} {B : Frames G} {ρ : RealMatch W} {t : T}
    {i j : Fin D.R.m} (hS : SquareStanding G t) {c : ℂ} (hc : IsSquareConst W B ρ t i j c) : CommutesWith W B ρ t i j c :=
  commutesWith_of_isSquareConst_of_triple hWC hK hP hL (squareTriple_of_standing hL W t i j hS) hc

end GlobalTheory.FunObj

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.ZH GlobalTheory.UPoinc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UCovSep

def UAct {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
    (Xo : Moduli Dw l) (c : Coeff l) {R R' : Type} [CommRing R] [CommRing R'] (P : PolAV (Sp R))
    (act : 𝓞 E → (P.A ⟶ P.A)) (σ : R →+* R') (u : Sp R' ⟶ Xo.XF c) : Prop :=
  ∃ (G : Over (Sp R')) (_ : GrpObj G) (α : G.left ⟶ P.A.left) (β : G.left ⟶ Xo.univ.t.G.left),
    IsGrpPullback G P.A (spMap σ) α ∧ IsGrpPullback G Xo.univ.t.G (u ≫ pullback.fst _ _) β ∧
      LBIso (P.L.pull α) (Xo.univ.t.PP.L.pull β) ∧
      ∀ a, ∃ f : G ⟶ G, f.left ≫ α = α ≫ (act a).left ∧ f.left ≫ β = β ≫ (Xo.univ.t.act.act (H.bar a)).left

theorem UAct.uOver {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {R R' : Type} [CommRing R] [CommRing R'] {P : PolAV (Sp R)}
    {act : 𝓞 E → (P.A ⟶ P.A)} {σ : R →+* R'} {u : Sp R' ⟶ Xo.XF c} (h : UAct Xo c P act σ u) : UOver Xo c P σ u :=
  let ⟨G, i, α, β, h₁, h₂, h₃, _⟩ := h
  ⟨G, i, α, β, h₁, h₂, h₃⟩

end GlobalTheory.UCovSep
end
end
