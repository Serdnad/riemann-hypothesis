module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle049
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoefficientFieldIntegersDedekindFractionField
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GermDerivationUniformisedAbelianVarietyUniqueVec
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EvalEqZeroOfMemVanIdeal
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle051
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleGeneratorExtendingDensePart
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle011
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SemicharacterSqEqOneOfSymmetric
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstOfNormPeriodic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

theorem _root_.GlobalTheory.T.existsUnique_localDerivationAlongFibreField_of_affine : ∀ (K : Type) [Field K] (R : Type) [CommRing R] (Y X : Scheme.{0}) (q : Y ⟶ Sp K) (p : X ⟶ Sp R) (m : Y ⟶ X) (D : R → K) (W₀ : X.Opens), IsAffineOpen W₀ → (∀ d₀ : Γ(X, W₀) → Γ(Y, m ⁻¹ᵁ W₀), (∀ a b, d₀ (a + b) = d₀ a + d₀ b) → (∀ a b, d₀ (a * b) = (m.app W₀).hom a * d₀ b + (m.app W₀).hom b * d₀ a) → (∀ r, d₀ (constFn p W₀ r) = constFn q (m ⁻¹ᵁ W₀) (D r)) → ∃ d, LocDerK q p m D W₀ d ∧ d W₀ = d₀) ∧ ∀ d d', LocDerK q p m D W₀ d → LocDerK q p m D W₀ d' → d W₀ = d' W₀ → ∀ W, W ≤ W₀ → d W = d' W := by
  first | exact @GlobalTheory.LocDerExtK.exists_unique_locDerK | exact GlobalTheory.LocDerExtK.exists_unique_locDerK | (intros; apply GlobalTheory.LocDerExtK.exists_unique_locDerK <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS.ProdLift

def derHom {S B : Type} [CommRing S] [CommRing B] (a : S →+* B) (δ : S → B)
    (hadd : ∀ x y, δ (x + y) = δ x + δ y) (hmul : ∀ x y, δ (x * y) = a x * δ y + a y * δ x) :
    S →+* DualNumber B where
  toFun x := TrivSqZeroExt.inl (a x) + TrivSqZeroExt.inr (δ x)
  map_one' := by
    have h' := hmul 1 1
    rw [_root_.mul_one, map_one, _root_.one_mul] at h'
    have h : δ 1 = 0 := left_eq_add.mp h'
    ext <;> simp [h]
  map_zero' := by
    have h := hadd 0 0
    simp only [add_zero, left_eq_add] at h
    ext <;> simp [h]
  map_add' x y := by ext <;> simp [hadd]
  map_mul' x y := by ext <;> simp [hmul, mul_comm]

theorem exists_der_of_isPushout {R S T P : CommRingCat.{0}} {i : R ⟶ S} {j : R ⟶ T} {u : S ⟶ P}
    {v : T ⟶ P} (po : IsPushout i j u v) {B : Type} [CommRing B] (a : P →+* B) (δ : S → B) (δ' : T → B)
    (hadd : ∀ x y, δ (x + y) = δ x + δ y)
    (hmul : ∀ x y, δ (x * y) = a (u.hom x) * δ y + a (u.hom y) * δ x)
    (hadd' : ∀ x y, δ' (x + y) = δ' x + δ' y)
    (hmul' : ∀ x y, δ' (x * y) = a (v.hom x) * δ' y + a (v.hom y) * δ' x)
    (hR : ∀ r, δ (i.hom r) = δ' (j.hom r)) :
    ∃ d : P → B, (∀ x y, d (x + y) = d x + d y) ∧ (∀ x y, d (x * y) = a x * d y + a y * d x) ∧
      (∀ x, d (u.hom x) = δ x) ∧ ∀ x, d (v.hom x) = δ' x := by
  let φ₁ : S →+* DualNumber B := derHom (a.comp u.hom) δ hadd hmul
  let φ₂ : T →+* DualNumber B := derHom (a.comp v.hom) δ' hadd' hmul'
  have hw : i ≫ CommRingCat.ofHom φ₁ = j ≫ CommRingCat.ofHom φ₂ := by
    ext r
    have e : u.hom (i.hom r) = v.hom (j.hom r) := by
      rw [← CommRingCat.comp_apply, po.w, CommRingCat.comp_apply]
    · simp [φ₁, φ₂, derHom, e]
    · simp [φ₁, φ₂, derHom, hR]
  let Φ := po.desc (CommRingCat.ofHom φ₁) (CommRingCat.ofHom φ₂) hw
  have hΦu : ∀ x, Φ.hom (u.hom x) = φ₁ x := fun x => by
    rw [← CommRingCat.comp_apply, po.inl_desc]
    rfl
  have hΦv : ∀ x, Φ.hom (v.hom x) = φ₂ x := fun x => by
    rw [← CommRingCat.comp_apply, po.inr_desc]
    rfl
  have hfst : Φ ≫ CommRingCat.ofHom (TrivSqZeroExt.fstHom B B B).toRingHom = CommRingCat.ofHom a := by
    apply po.hom_ext
    · ext x
      simp [hΦu, φ₁, derHom]
    · ext x
      simp [hΦv, φ₂, derHom]
  have hf : ∀ x, (Φ.hom x).fst = a x := fun x => by
    have := congrArg (fun g => g.hom x) hfst
    simpa using this
  refine ⟨fun x => (Φ.hom x).snd, fun x y => ?_, fun x y => ?_, fun x => ?_, fun x => ?_⟩
  · simp
  · simp only [map_mul, TrivSqZeroExt.snd_mul, hf, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op]
    ring
  · simp [hΦu, φ₁, derHom]
  · simp [hΦv, φ₂, derHom]

theorem der_eq_of_isPushout {R S T P : CommRingCat.{0}} {i : R ⟶ S} {j : R ⟶ T} {u : S ⟶ P}
    {v : T ⟶ P} (po : IsPushout i j u v) {B : Type} [CommRing B] (a : P →+* B) (d d' : P → B)
    (hadd : ∀ x y, d (x + y) = d x + d y)
    (hmul : ∀ x y, d (x * y) = a x * d y + a y * d x)
    (hadd' : ∀ x y, d' (x + y) = d' x + d' y)
    (hmul' : ∀ x y, d' (x * y) = a x * d' y + a y * d' x)
    (hu : ∀ x, d (u.hom x) = d' (u.hom x)) (hv : ∀ x, d (v.hom x) = d' (v.hom x)) : d = d' := by
  have hext : u ≫ CommRingCat.ofHom (derHom a d hadd hmul) = u ≫ CommRingCat.ofHom (derHom a d' hadd' hmul') ∧
      v ≫ CommRingCat.ofHom (derHom a d hadd hmul) = v ≫ CommRingCat.ofHom (derHom a d' hadd' hmul') := by
    constructor
    · ext x
      · simp [derHom]
      · simp [derHom, hu]
    · ext x
      · simp [derHom]
      · simp [derHom, hv]
  have hφ := po.hom_ext hext.1 hext.2
  funext x
  have := congrArg (fun g => (g.hom x).snd) hφ
  simpa [derHom] using this

theorem pbT_eq {Z Y : Scheme.{0}} (f : Z ⟶ Y) {O₀ : Y.Opens} (s : Γ(Y, O₀)) {O : Z.Opens}
    (h : O ≤ f ⁻¹ᵁ O₀) : pbT f s O = (f.appLE O₀ O h).hom s := by
  unfold pbT
  rw [dite_eq_left h]

theorem appLE_constFn {R : Type} [CommRing R] {X Y : Scheme.{0}} (q : X ⟶ Sp R) (q' : Y ⟶ Sp R)
    (f : Y ⟶ X) (hf : f ≫ q = q') {U : X.Opens} {V : Y.Opens} (h : V ≤ f ⁻¹ᵁ U) (a : R) :
    (f.appLE U V h).hom (constFn q U a) = constFn q' V a := by
  subst hf
  unfold constFn
  have e := Scheme.Hom.appLE_comp_appLE f q ⊤ U V (by simp) h
  exact congrArg (fun g => g.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)) e

theorem app_appLE {Z Z₀ X Y : Scheme.{0}} {p : Z ⟶ X} {p₀ : Z₀ ⟶ Y} {m : Y ⟶ X} {m₂ : Z₀ ⟶ Z}
    (hp : m₂ ≫ p = p₀ ≫ m) {W : X.Opens} {Q : Z.Opens} (h : Q ≤ p ⁻¹ᵁ W)
    (h' : m₂ ⁻¹ᵁ Q ≤ p₀ ⁻¹ᵁ m ⁻¹ᵁ W) (f : Γ(X, W)) :
    (m₂.app Q).hom ((p.appLE W Q h).hom f) = (p₀.appLE _ _ h').hom ((m.app W).hom f) := by
  have key : ∀ (g g' : Z₀ ⟶ X) (e : g = g') (h₁ : m₂ ⁻¹ᵁ Q ≤ g ⁻¹ᵁ W) (h₂ : m₂ ⁻¹ᵁ Q ≤ g' ⁻¹ᵁ W),
      (g.appLE W (m₂ ⁻¹ᵁ Q) h₁).hom f = (g'.appLE W (m₂ ⁻¹ᵁ Q) h₂).hom f := by
    rintro g _ rfl _ _
    rfl
  have e₁ := Scheme.Hom.appLE_comp_appLE m₂ p W Q (m₂ ⁻¹ᵁ Q) h le_rfl
  have e₂ := Scheme.Hom.appLE_comp_appLE p₀ m W (m ⁻¹ᵁ W) (m₂ ⁻¹ᵁ Q) le_rfl h'
  rw [Scheme.Hom.app_eq_appLE m₂, Scheme.Hom.app_eq_appLE m]
  have l₁ := congrArg (fun g => g.hom f) e₁
  have l₂ := congrArg (fun g => g.hom f) e₂
  simp only [CommRingCat.comp_apply] at l₁ l₂
  rw [l₁, l₂]
  exact key _ _ hp _ _

theorem preimage_le {Z Z₀ X Y : Scheme.{0}} {p : Z ⟶ X} {p₀ : Z₀ ⟶ Y} {m : Y ⟶ X} {m₂ : Z₀ ⟶ Z}
    (hp : m₂ ≫ p = p₀ ≫ m) {W : X.Opens} {Q : Z.Opens} (h : Q ≤ p ⁻¹ᵁ W) :
    m₂ ⁻¹ᵁ Q ≤ p₀ ⁻¹ᵁ m ⁻¹ᵁ W := by
  intro x hx
  have h₁ : p (m₂ x) ∈ W := h hx
  change m (p₀ x) ∈ W
  rw [← Scheme.Hom.comp_apply, ← hp, Scheme.Hom.comp_apply]
  exact h₁

theorem finiteRing_sq_sub_mul_sq_eq_of_card {K : Type} [Field K] {R : Type} [CommRing R] {Z Z₀ X Y : Scheme.{0}}
    {p q : Z ⟶ X} {s : X ⟶ Sp R} (H : IsPullback p q s s) {z : Z ⟶ Sp R} (hz : p ≫ s = z)
    {p₀ q₀ : Z₀ ⟶ Y} {s₀ : Y ⟶ Sp K} {z₀ : Z₀ ⟶ Sp K} (hp₀ : p₀ ≫ s₀ = z₀) (hq₀ : q₀ ≫ s₀ = z₀)
    {m : Y ⟶ X} {m₂ : Z₀ ⟶ Z} (hp : m₂ ≫ p = p₀ ≫ m) (hq : m₂ ≫ q = q₀ ≫ m) (D : R → K)
    {W W' : X.Opens} (hW : IsAffineOpen W) (hW' : IsAffineOpen W') (Q : Z.Opens)
    (hQ : Q = p ⁻¹ᵁ W ⊓ q ⁻¹ᵁ W') :
    (∀ d d', LocDerK s₀ s m D W d → LocDerK s₀ s m D W' d' → ∃ d₂, LocDerK z₀ z m₂ D Q d₂ ∧
      (∀ f, d₂ Q (pbT p f Q) = pbT p₀ (d W f) _) ∧ ∀ f, d₂ Q (pbT q f Q) = pbT q₀ (d' W' f) _) ∧
    ∀ d₂ d₂', LocDerK z₀ z m₂ D Q d₂ → LocDerK z₀ z m₂ D Q d₂' →
      (∀ f : Γ(X, W), d₂ Q (pbT p f Q) = d₂' Q (pbT p f Q)) →
      (∀ f : Γ(X, W'), d₂ Q (pbT q f Q) = d₂' Q (pbT q f Q)) → ∀ O, O ≤ Q → d₂ O = d₂' O := by
  have hWQ : Q ≤ p ⁻¹ᵁ W := by rw [hQ]; exact inf_le_left
  have hW'Q : Q ≤ q ⁻¹ᵁ W' := by rw [hQ]; exact inf_le_right
  have h₁ : m₂ ⁻¹ᵁ Q ≤ p₀ ⁻¹ᵁ m ⁻¹ᵁ W := preimage_le hp hWQ
  have h₂ : m₂ ⁻¹ᵁ Q ≤ q₀ ⁻¹ᵁ m ⁻¹ᵁ W' := preimage_le hq hW'Q
  have hz' : q ≫ s = z := H.w.symm.trans hz
  have : IsAffine W.toScheme := hW
  have : IsAffine W'.toScheme := hW'
  have : IsAffine (⊤ : (Sp R).Opens).toScheme := isAffineOpen_top (Sp R)
  have hPb := Scheme.Hom.isPullback_resLE H (US := ⊤) (UT := W') (UX := W) (by simp) (by simp) hQ
  have : IsAffine Q.toScheme := IsAffine.of_isPullback hPb
  have hQa : IsAffineOpen Q := this
  have hPo : IsPushout (s.appLE ⊤ W (by simp)) (s.appLE ⊤ W' (by simp)) (p.appLE W Q hWQ)
      (q.appLE W' Q hW'Q) :=
    (isPushout_appTop_of_isPullback hPb).of_iso (Scheme.Opens.topIso ⊤) W.topIso W'.topIso Q.topIso
      (Arrow.w (arrowResLEAppIso s ⊤ W _).hom).symm (Arrow.w (arrowResLEAppIso s ⊤ W' _).hom).symm
      (Arrow.w (arrowResLEAppIso p W Q _).hom).symm (Arrow.w (arrowResLEAppIso q W' Q _).hom).symm
  refine ⟨fun d d' hd hd' => ?_, fun d₂ d₂' e₁ e₂ ef ef' O hO => ?_⟩
  · let δ : Γ(X, W) → Γ(Z₀, m₂ ⁻¹ᵁ Q) := fun f => (p₀.appLE (m ⁻¹ᵁ W) (m₂ ⁻¹ᵁ Q) h₁).hom (d W f)
    let δ' : Γ(X, W') → Γ(Z₀, m₂ ⁻¹ᵁ Q) := fun f => (q₀.appLE (m ⁻¹ᵁ W') (m₂ ⁻¹ᵁ Q) h₂).hom (d' W' f)
    have hb : ∀ r, δ (constFn s W r) = constFn z₀ (m₂ ⁻¹ᵁ Q) (D r) := fun r => by
      simp only [δ]
      rw [hd.base W le_rfl r]
      exact appLE_constFn s₀ z₀ p₀ hp₀ h₁ (D r)
    have hb' : ∀ r, δ' (constFn s W' r) = constFn z₀ (m₂ ⁻¹ᵁ Q) (D r) := fun r => by
      simp only [δ']
      rw [hd'.base W' le_rfl r]
      exact appLE_constFn s₀ z₀ q₀ hq₀ h₂ (D r)
    have hR : ∀ r, δ ((s.appLE ⊤ W (by simp)).hom r) = δ' ((s.appLE ⊤ W' (by simp)).hom r) := by
      intro r
      obtain ⟨r', rfl⟩ : ∃ r', (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r' = r :=
        ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r, by simp⟩
      change δ (constFn s W r') = δ' (constFn s W' r')
      rw [hb, hb']
    obtain ⟨d0, hadd0, hmul0, hu0, hv0⟩ := exists_der_of_isPushout hPo (m₂.app Q).hom δ δ'
      (fun x y => by simp only [δ]; rw [hd.add W le_rfl, map_add (f := _)])
      (fun x y => by
        simp only [δ]
        rw [hd.mul W le_rfl, map_add (f := _), map_mul, map_mul, app_appLE hp hWQ h₁ x, app_appLE hp hWQ h₁ y])
      (fun x y => by simp only [δ']; rw [hd'.add W' le_rfl, map_add (f := _)])
      (fun x y => by
        simp only [δ']
        rw [hd'.mul W' le_rfl, map_add (f := _), map_mul, map_mul, app_appLE hq hW'Q h₂ x, app_appLE hq hW'Q h₂ y])
      hR
    have hbQ : ∀ r, d0 (constFn z Q r) = constFn z₀ (m₂ ⁻¹ᵁ Q) (D r) := fun r => by
      rw [← appLE_constFn s z p hz hWQ r, hu0, hb]
    obtain ⟨d₂, hd₂, hd₂Q⟩ := GlobalTheory.LocDerExtK.exists_locDerK K R Z₀ Z z₀ z m₂ D Q hQa d0 hadd0 hmul0 hbQ
    refine ⟨d₂, hd₂, fun f => ?_, fun f => ?_⟩
    · rw [hd₂Q, pbT_eq p f hWQ, hu0, pbT_eq p₀ _ h₁]
    · rw [hd₂Q, pbT_eq q f hW'Q, hv0, pbT_eq q₀ _ h₂]
  · refine GlobalTheory.LocDerExtK.locDerK_unique hQa d₂ d₂' e₁ e₂ ?_ O hO
    exact der_eq_of_isPushout hPo (m₂.app Q).hom (d₂ Q) (d₂' Q) (e₁.add Q le_rfl) (e₁.mul Q le_rfl)
      (e₂.add Q le_rfl) (e₂.mul Q le_rfl)
      (fun x => by rw [← pbT_eq p x hWQ]; exact ef x) (fun x => by rw [← pbT_eq q x hW'Q]; exact ef' x)

theorem main : ∀ (K : Type) [Field K] (R : Type) [CommRing R] (x₀ : R →+* K) (A : Over (Sp R)) (A₀ : Over (Sp K)) (m : A₀.left ⟶ A.left) (m₂ : (A₀ ⊗ A₀).left ⟶ (A ⊗ A).left) (D : R → K) (W W' : A.left.Opens), m ≫ A.hom = A₀.hom ≫ spMap x₀ → IsSquare m m₂ → IsAffineOpen W → IsAffineOpen W' → ∀ Q, Q = (fst A A).left ⁻¹ᵁ W ⊓ (snd A A).left ⁻¹ᵁ W' → (∀ d d', LocDerK A₀.hom A.hom m D W d → LocDerK A₀.hom A.hom m D W' d' → ∃ d₂, LocDerK (A₀ ⊗ A₀).hom (A ⊗ A).hom m₂ D Q d₂ ∧ (∀ f, d₂ Q (pbT (fst A A).left f Q) = pbT (fst A₀ A₀).left (d W f) _) ∧ ∀ f, d₂ Q (pbT (snd A A).left f Q) = pbT (snd A₀ A₀).left (d' W' f) _) ∧ ∀ d₂ d₂', LocDerK (A₀ ⊗ A₀).hom (A ⊗ A).hom m₂ D Q d₂ → LocDerK (A₀ ⊗ A₀).hom (A ⊗ A).hom m₂ D Q d₂' → (∀ f : Γ(A.left, W), d₂ Q (pbT (fst A A).left f Q) = d₂' Q (pbT (fst A A).left f Q)) → (∀ f : Γ(A.left, W'), d₂ Q (pbT (snd A A).left f Q) = d₂' Q (pbT (snd A A).left f Q)) → ∀ O, O ≤ Q → d₂ O = d₂' O := by
  intro K _ R _ x₀ A A₀ m m₂ D W W' _ hsq hW hW' Q hQ
  obtain ⟨hs₁, hs₂⟩ := hsq
  exact finiteRing_sq_sub_mul_sq_eq_of_card (Over.isPullback_of_binaryFan_isLimit _
      (CartesianMonoidalCategory.tensorProductIsBinaryProduct A A))
    (Over.w (fst A A)) (Over.w (fst A₀ A₀)) (Over.w (snd A₀ A₀)) hs₁ hs₂ D hW hW' Q hQ

end GlobalTheory.KS.ProdLift
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
theorem _root_.GlobalTheory.T.coefficientField_integers_dedekind_fractionField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l), IsDedFrac (algebraMap (𝓞 c.F) c.F) ∧ Algebra.FiniteType ℤ (𝓞 c.F) ∧ (∀ A : ℕ, A ∣ l.A → ∃ b : RZ H 1 A →+* 𝓞 c.F, IsInc (RZ H 1 A).subtype (c.F.val.toRingHom.comp (algebraMap (𝓞 c.F) c.F)) b) ∧ ∀ (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → IsDedFrac (c.V W).subtype ∧ (∀ n : ℕ, n.Coprime p → IsUnit (n : c.V W)) ∧ ∀ S A : ℕ, S.Coprime p → 0 < A → zeta A ∈ c.F → ∃ b : RZ H S A →+* c.V W, IsInc (RZ H S A).subtype (c.F.val.toRingHom.comp (c.V W).subtype) b := by
  first | exact @GlobalTheory.CoeffRings.coeff_isDedFrac | exact GlobalTheory.CoeffRings.coeff_isDedFrac | (intros; apply GlobalTheory.CoeffRings.coeff_isDedFrac <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
theorem _root_.GlobalTheory.T.finrank_eigenspace_of_lieMultiplicity : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (O : Type) [CommRing O] (act : OAct O P₀.A) (F : O → Module.End ℂ (Fin P₀.g → ℂ)), (∀ a z, u.ex (F a z) = u.ex z ≫ act.act a) → ∀ (τ : O →+* ℂ) (n : ℕ), LieMult act (𝟙 _) τ n → Module.finrank ℂ ↥(⨅ a, Module.End.eigenspace (F a) (τ a)) = n := by
  first | exact @GlobalTheory.UnifEigenRank.finrank_eigenspace_of_lieMult | exact GlobalTheory.UnifEigenRank.finrank_eigenspace_of_lieMult | (intros; apply GlobalTheory.UnifEigenRank.finrank_eigenspace_of_lieMult <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

theorem _root_.GlobalTheory.T.germDerivation_uniformised_abelianVariety_unique_vector : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ z δ, PtDer (u.ex z).left δ → (∀ a, δ ⊤ (constFn P₀.A.hom ⊤ a) = 0) → ∃! w, ∀ O f, ⊤ ≤ (u.ex z).left ⁻¹ᵁ O → δ O f = fderiv ℂ (fun z' => valAt' (u.ex z').left O f) z w := by
  first | exact @GlobalTheory.KS.TangentAt.tangent_at_point | exact GlobalTheory.KS.TangentAt.tangent_at_point | (intros; apply GlobalTheory.KS.TangentAt.tangent_at_point <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
theorem _root_.GlobalTheory.T.exists_separated_galoisCover_of_free_action : ∀ (K : Type) [Field K] (X : Scheme.{0}) (s : X ⟶ Sp K) (Ga : Type) [Group Ga] [Finite Ga] (ρ : Ga → (X ⟶ X)), IsQProjOver s → ρ 1 = 𝟙 X → (∀ a c, ρ (a * c) = ρ a ≫ ρ c) → (∀ a, ρ a ≫ s = s) → (∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ X) (a : Ga), y ≫ ρ a = y → a = 1) → ∃ (Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp K), π ≫ sY = s ∧ IsGaloisCover Ga ρ π ∧ IsSeparated sY ∧ LocallyOfFiniteType sY ∧ QuasiCompact sY := by
  first | exact @GlobalTheory.ZM.exists_isGaloisCover_of_isQProjOver | exact GlobalTheory.ZM.exists_isGaloisCover_of_isQProjOver | (intros; apply GlobalTheory.ZM.exists_isGaloisCover_of_isQProjOver <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
theorem _root_.GlobalTheory.T.galoisCover_descent_and_cartesian_squares : ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)), IsGaloisCover Ga ρ π → (∀ (Z : Scheme.{0}) (f : X ⟶ Z), (∀ a, ρ a ≫ f = f) → ∃! f' : Y ⟶ Z, π ≫ f' = f) ∧ (∀ (T : Scheme.{0}) (x x' : T ⟶ X), x ≫ π = x' ≫ π → ∀ p : T, ∃ (V : T.Opens) (a : Ga), p ∈ V ∧ V.ι ≫ x ≫ ρ a = V.ι ≫ x') ∧ ∀ (X' Y' : Scheme.{0}) (π' : X' ⟶ Y') (ρ' : Ga → (X' ⟶ X')) (u : X' ⟶ X) (v : Y' ⟶ Y), (∀ a, ρ' a ≫ u = u ≫ ρ a) → u ≫ π = π' ≫ v → (IsGaloisCover Ga ρ' π' → IsPullback u π' π v) ∧ (IsPullback u π' π v → (∀ a, ρ' a ≫ π' = π') → IsGaloisCover Ga ρ' π') := by
  first | exact @GlobalTheory.ZM.galoisCover_descent | exact GlobalTheory.ZM.galoisCover_descent | (intros; apply GlobalTheory.ZM.galoisCover_descent <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.FormsFamily

theorem exists_const_near {R α : Type} [CommRing R] [PartialOrder α] {P : Set (Ideal R)} (hP : DenseP P)
    (r : ∀ (K : Type) [Field K], (R →+* K) → α) (ρ : α) (g : R)
    (hsc : ∀ (K : Type) [Field K] (x : R →+* K), ∃ f : R, x f ≠ 0 ∧
      ∀ (L : Type) [Field L] (y : R →+* L), y f ≠ 0 → r L y ≤ r K x)
    (hρ : ∀ q ∈ P, g ∉ q → ∃ (K : Type) (_ : Field K) (x : R →+* K), RingHom.ker x = q ∧ r K x = ρ)
    (K : Type) [Field K] (x : R →+* K) (hg : x g ≠ 0) (hx : r K x = ρ) :
    ∃ f : R, x f ≠ 0 ∧ ∀ (L : Type) [Field L] (y : R →+* L), y f ≠ 0 → r L y = ρ := by
  obtain ⟨f, hf, h⟩ := hsc K x
  refine ⟨f * g, by rw [map_mul]; exact mul_ne_zero hf hg, fun L _ y hy => ?_⟩
  rw [map_mul] at hy
  refine le_antisymm (hx ▸ h L y (left_ne_zero_of_mul hy)) ?_
  obtain ⟨f', hf', h'⟩ := hsc L y
  have h0 : f' * g ≠ 0 := fun h0 => mul_ne_zero hf' (right_ne_zero_of_mul hy) (by rw [← map_mul, h0, map_zero])
  have h1 : ¬ ∀ q ∈ P, q.IsPrime → f' * g ∈ q := fun h1 => h0 (hP _ h1)
  push Not at h1
  obtain ⟨q, hq, -, hq'⟩ := h1
  obtain ⟨K', _, x', rfl, rfl⟩ := hρ q hq fun h2 => hq' (q.mul_mem_left _ h2)
  exact h' K' x' fun h2 => hq' (Ideal.mul_mem_right _ _ h2)

theorem exists_away_projective_vanIdeal : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (σ Hh : Type) [Finite σ] [Finite Hh] (p : Hh → σ → R) (Q : Polynomial ℚ) (d : ℕ) (P : Set (Ideal R)), DenseP P → (∀ q ∈ P, ∃ (K : Type) (_ : Field K) (x : R →+* K) (I : Ideal (MvPolynomial σ K)), RingHom.ker x = q ∧ CutBy I Q d (fun h i => x (p h i))) → ∀ q₀ ∈ P, ∃ f : R, f ∉ q₀ ∧ (∀ e ≥ d, Module.Projective (Localization.Away f) (↥(MvPolynomial.homogeneousSubmodule σ (Localization.Away f) e) ⧸ ((vanIdeal d (fun h i => (algebraMap R (Localization.Away f)) (p h i))).restrictScalars (Localization.Away f)).comap (MvPolynomial.homogeneousSubmodule σ (Localization.Away f) e).subtype)) ∧ ∀ (K : Type) [Field K] (x : (Localization.Away f) →+* K), (vanIdeal d (fun h i => (algebraMap R (Localization.Away f)) (p h i))).map (MvPolynomial.map x) = vanIdeal d (fun h i => x ((algebraMap R (Localization.Away f)) (p h i))) := by
  intro R _ _ _ σ Hh _ _ p Q d P hP hcut q₀ hq₀
  classical
  obtain ⟨K₀, _, x₀, I₀, rfl, hc₀⟩ := hcut q₀ hq₀
  have hI := component_mem_vanIdeal d p
  obtain ⟨f₁, hf₁, h₁⟩ := exists_const_near hP
    (fun K _ x => (dimDeg (vanIdeal d fun h i => x (p h i)) d : ℚ)) (Q.eval (d : ℚ)) 1
    (fun K _ x => (exists_dimDeg_vanIdeal_le d p K x).imp fun f hf =>
      ⟨hf.1, fun L _ y hy => Nat.cast_le.2 (hf.2 L y hy)⟩)
    (fun q hq _ => by
      obtain ⟨K, _, x, I, hx, hc⟩ := hcut q hq
      exact ⟨K, _, x, hx, dimDeg_eq_of_cutBy hc le_rfl⟩)
    K₀ x₀ (by simp) (dimDeg_eq_of_cutBy hc₀ le_rfl)
  have h₂ := map_vanIdeal_of_const_away d p _ f₁ h₁
  have h₃ : ∀ e ≥ d, ∃ g : R, x₀ g ≠ 0 ∧ ∀ (L : Type) [Field L] (y : R →+* L), y g ≠ 0 →
      (dimDeg ((vanIdeal d p).map (MvPolynomial.map y)) e : ℚ) = Q.eval (e : ℚ) := by
    intro e he
    obtain ⟨g, hg, h⟩ := exists_const_near hP
      (fun K _ x => -(dimDeg ((vanIdeal d p).map (MvPolynomial.map x)) e : ℚ)) (-Q.eval (e : ℚ)) f₁
      (fun K _ x => (exists_dimDeg_map_le _ hI e K x).imp fun f hf =>
        ⟨hf.1, fun L _ y hy => neg_le_neg (Nat.cast_le.2 (hf.2 L y hy))⟩)
      (fun q hq hq' => by
        obtain ⟨K, _, x, I, rfl, hc⟩ := hcut q hq
        exact ⟨K, _, x, rfl, by rw [h₂ K x hq', dimDeg_eq_of_cutBy hc he]⟩)
      K₀ x₀ hf₁ (by rw [h₂ K₀ x₀ hf₁, dimDeg_eq_of_cutBy hc₀ he])
    exact ⟨g, hg, fun L _ y hy => neg_injective (h L y hy)⟩
  have h₄ : ∀ φ : ℕ → ℕ, ∃ g : R, x₀ g ≠ 0 ∧ ∀ (L : Type) [Field L] (y : R →+* L), y g ≠ 0 →
      φ = dimDeg ((vanIdeal d p).map (MvPolynomial.map y)) → ∀ e ≥ d, (φ e : ℚ) = Q.eval (e : ℚ) := by
    intro φ
    by_cases hφ : ∀ e ≥ d, (φ e : ℚ) = Q.eval (e : ℚ)
    · exact ⟨1, by simp, fun _ _ _ _ _ => hφ⟩
    · push Not at hφ
      obtain ⟨e, he, hne⟩ := hφ
      obtain ⟨g, hg, h⟩ := h₃ e he
      exact ⟨g, hg, fun L _ y hy hφ => absurd (hφ ▸ h L y hy) hne⟩
  choose g hg h₅ using h₄
  have hfin := GlobalTheory.T.finite_setOf_hilbertFunctions_fibres R σ (vanIdeal d p) hI
  let f : R := f₁ * ∏ φ ∈ hfin.toFinset, g φ
  have h₆ : ∀ (L : Type) [Field L] (y : R →+* L), y f ≠ 0 → ∀ e ≥ d,
      (dimDeg (vanIdeal d fun h i => y (p h i)) e : ℚ) = Q.eval (e : ℚ) := by
    intro L _ y hy
    simp only [f, map_mul, map_prod, ne_eq, mul_eq_zero, not_or] at hy
    rw [← h₂ L y hy.1]
    exact h₅ _ L y (Finset.prod_ne_zero_iff.1 hy.2 _ (hfin.mem_toFinset.2 ⟨L, _, y, rfl⟩)) rfl
  have hf : f ∉ RingHom.ker x₀ := by
    rw [RingHom.mem_ker, map_mul, map_prod]
    exact mul_ne_zero hf₁ (Finset.prod_ne_zero_iff.2 fun φ _ => hg φ)
  haveI : IsReduced (Localization.Away f) :=
    isReduced_localizationPreserves (Submonoid.powers f) _ inferInstance
  have h₇ : ∀ (L : Type) [Field L] (y : Localization.Away f →+* L), ∀ e ≥ d,
      (dimDeg (vanIdeal d fun h i => y (algebraMap R (Localization.Away f) (p h i))) e : ℚ) = Q.eval (e : ℚ) :=
    fun L _ y => h₆ L (y.comp (algebraMap R _))
      ((IsLocalization.Away.algebraMap_isUnit (S := Localization.Away f) f).map y).ne_zero
  have h₈ := map_vanIdeal_of_const d (fun h i => algebraMap R (Localization.Away f) (p h i)) _
    fun L _ y => h₇ L y d le_rfl
  exact ⟨f, hf, fun e he => projective_of_const _ (component_mem_vanIdeal d _) e (Q.eval (e : ℚ))
    fun L _ y => by rw [h₈ L y]; exact h₇ L y e he, fun K _ x => h₈ K x⟩

end GlobalTheory.ZM.FormsFamily
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
theorem _root_.GlobalTheory.T.exists_lineBundleGenerator_extending_densePart : ∀ (X U : Scheme.{0}) [IsLocallyNoetherian X] (j : U ⟶ X), IsNormalScheme X → IsPreimmersion j → Flat j → IsDominant j → QuasiCompact j → ∀ (P : Over X) (e : X ⟶ P.left) (N : LB P.left), e ≫ P.hom = 𝟙 X → Smooth P.hom → GeometricallyIntegral P.hom → N.IsLB → (∃ r : (N.pull e).Gen, r.IsGen) → (∃ t : (N.pull (pullback.fst P.hom j)).Gen, t.IsGen) → ∃ t : N.Gen, t.IsGen := by
  first | exact @GlobalTheory.GenericExtend.exists_isGen_of_densePart | exact GlobalTheory.GenericExtend.exists_isGen_of_densePart | (intros; apply GlobalTheory.GenericExtend.exists_isGen_of_densePart <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.ThetaUnifCompare

open GlobalTheory.FrameValue CubeValues SymmetricSemicharacter EigenNorm

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} {u : HolUnif A L g}
  {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}

theorem chi_neg_of_sym (hL : L.IsLB) (hs : Out.Sym A L) (h : u.IsAH Hm χ) (l : u.Λ) : χ (-l) = χ l := by
  obtain ⟨U, hU, s, hs⟩ := hs (default : PrimeSpectrum ℂ)
  have hr : Set.range (𝟙 A.left : A.left ⟶ A.left) ⊆ Set.range (A.hom ⁻¹ᵁ U).ι := by
    rintro x -
    refine ⟨⟨x, ?_⟩, rfl⟩
    have e : A.hom x = (default : PrimeSpectrum ℂ) := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    show A.hom x ∈ U
    rw [e]; exact hU
  obtain ⟨p, hp⟩ : ∃ p : A.left ⟶ (A.hom ⁻¹ᵁ U).toScheme, p ≫ (A.hom ⁻¹ᵁ U).ι = 𝟙 _ :=
    ⟨_, IsOpenImmersion.lift_fac _ _ hr⟩
  have hz : ∀ w, IsLift u (K := Fin 2) ![(A.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : A ⟶ A).left, (A.hom ⁻¹ᵁ U).ι]
      ((u.ex w).left ≫ p) ![-w, w] := fun w k => by
    fin_cases k
    · show ((u.ex w).left ≫ p) ≫ (A.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : A ⟶ A).left = (u.ex (-w)).left
      rw [Category.assoc, reassoc_of% hp]
      exact ex_neg_left u w
    · show ((u.ex w).left ≫ p) ≫ (A.hom ⁻¹ᵁ U).ι = (u.ex w).left
      rw [Category.assoc, hp, Category.comp_id]
  have hd : Differentiable ℂ fun w => genVal u hL s ((u.ex w).left ≫ p) ![-w, w] :=
    differentiable_genVal hL hs p (q := id) differentiable_id (z := fun w => ![-w, w])
      (fun k => by fin_cases k <;> simp <;> fun_prop) hz
  have hper : ∀ (l : u.Λ) w, genVal u hL s ((u.ex (w + l)).left ≫ p) ![-(w + l), w + l] =
      χ (-l) / χ l * genVal u hL s ((u.ex w).left ≫ p) ![-w, w] := fun l w => by
    have e₂ : ![-(w + l), w + l] = fun k => ![-w, w] k + ((![-l, l] : Fin 2 → u.Λ) k : Fin g → ℂ) := by
      funext k
      fin_cases k <;> simp [add_comm]
    rw [ex_add_period u w l l.2, e₂, genVal_add_period hL h s (hz w)]
    congr 1
    have n := chi_ne_zero h l
    simp [ahFactor, hermForm_neg_left, hermForm_neg_right]
    field_simp
  have hc := const_of_norm_periodic u hd (fun l w => by
    rw [hper, norm_mul, norm_div, h.2.2.1, h.2.2.1, div_one, _root_.one_mul])
  have e := hper l 0
  rw [hc _ 0] at e
  exact (div_eq_one_iff_eq (chi_ne_zero h l)).1
    (mul_right_cancel₀ (genVal_ne_zero hL s (hz 0)) (e.symm.trans (_root_.one_mul _).symm))

theorem chi_eq_one_or_of_sym (hL : L.IsLB) (hs : Out.Sym A L) (h : u.IsAH Hm χ) (l : u.Λ) : χ l = 1 ∨ χ l = -1 := by
  have e := chi_add hL h l (-l)
  have hi : (hermForm Hm l l).im = 0 := Complex.conj_eq_iff_im.1 (hermForm_conj Hm h.1 l l).symm
  rw [add_neg_cancel, chi_zero hL h, chi_neg_of_sym hL hs h, Submodule.coe_neg, hermForm_neg_right, Complex.neg_im,
    hi] at e
  exact mul_self_eq_one_iff.1 (by simpa using e.symm)

end GlobalTheory.ThetaUnifCompare
end
end
