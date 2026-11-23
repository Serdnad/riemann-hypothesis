module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle002
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ComparisonTorusInvariant
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle028
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle039
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCommonField
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle007

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

noncomputable section

namespace GlobalTheory

local instance (priority := high) grpObjPreTorusThick {R : Type} [CommRing R] (I : Ideal R) (e : ℕ)
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G] : GrpObj (thickObj R I e G) :=
  letI : (Over.pullback (thick R I e)).Monoidal :=
    (Over.instBraidedPullback (f := thick R I e)).toMonoidal
  Functor.grpObjObj (F := Over.pullback (thick R I e))

namespace PreTorusInvariance

theorem cube_alg {V : Type} [CommGroup V] {A : Type} [CommGroup A] {a W W' d : A → V} (h : ∀ x, a x * W' x = W x * d x)
    {x y u : A} {C C' c c' : V}
    (h₁ : C * W (x * y) * W (x * u) * W (y * u) * W 1 = W (x * y * u) * W x * W y * W u * c)
    (h₂ : C' * W' (x * y) * W' (x * u) * W' (y * u) * W' 1 = W' (x * y * u) * W' x * W' y * W' u * c')
    (h₃ : c * d (x * y) * d (x * u) * d (y * u) * d 1 = d (x * y * u) * d x * d y * d u * c') :
    C = a (x * y * u) * (a (x * y))⁻¹ * (a (x * u))⁻¹ * (a (y * u))⁻¹ * a x * a y * a u * (a 1)⁻¹ * C' := by
  have E := fun {p q : V} (e : p = q) => congrArg Additive.ofMul e
  have a₁ := E h₁; have a₂ := E h₂; have a₃ := E h₃
  have b₁ := E (h (x * y * u)); have b₂ := E (h (x * y)); have b₃ := E (h (x * u)); have b₄ := E (h (y * u))
  have b₅ := E (h x); have b₆ := E (h y); have b₇ := E (h u); have b₈ := E (h 1)
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv] at *
  linear_combination (norm := abel) a₁ - a₂ + a₃ - b₁ + b₂ + b₃ + b₄ - b₅ - b₆ - b₇ + b₈

theorem even_alg {V : Type} [CommGroup V] {A : Type} [CommGroup A] {a W W' d : A → V} (h : ∀ x, a x * W' x = W x * d x)
    {x : A} {s s' c c' : V} (h₁ : s * W x = W x⁻¹ * c) (h₂ : s' * W' x = W' x⁻¹ * c') (h₃ : c * d x = d x⁻¹ * c') :
    s * a x = a x⁻¹ * s' := by
  have E := fun {p q : V} (e : p = q) => congrArg Additive.ofMul e
  have a₁ := E h₁; have a₂ := E h₂; have a₃ := E h₃
  have b₁ := E (h x); have b₂ := E (h x⁻¹)
  apply Additive.ofMul.injective
  simp only [ofMul_mul] at *
  linear_combination (norm := abel) a₁ - a₂ + a₃ + b₁ - b₂

theorem vals_id {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {P P' : CP G}
    {w : LB.Iso P'.L.L (P.L.L.pull (𝟙 G.left))} {hw : 𝟙 G.left ≫ G.hom = G.hom ≫ 𝟙 _}
    (h : IsCPMap P' P (𝟙 _) (𝟙 G.left) hw w) {T : Over S} {z : T.left} {N N'} (hN : Good P.L.L z N)
    (hN' : Good P'.L.L z N') (d : (T ⟶ G) → (T.left.presheaf.stalk z)ˣ)
    (hd : ∀ x, d x = gw w x.left z (N x.left) (N' x.left)) {B : Type} [CommGroup B] (β : B →* (T ⟶ G)) :
    (∀ x, val P.sym (β x).left z N * d (β x) = d (β x⁻¹) * val P'.sym (β x).left z N') ∧
    ∀ x y u, cubV P.c z N (β x) (β y) (β u) * d (β (x * y)) * d (β (x * u)) * d (β (y * u)) * d (β 1) =
      d (β (x * y * u)) * d (β x) * d (β y) * d (β u) * cubV P'.c z N' (β x) (β y) (β u) := by
  obtain ⟨-, s, c⟩ := h.vals T z N' N hN' hN d (fun x => by rw [hd, Category.comp_id])
  refine ⟨fun x => ?_, fun x y u => ?_⟩
  · have s := s (β x)
    rwa [Category.comp_id, ← map_inv] at s
  · have c := c (β x) (β y) (β u)
    rw [_root_.id, cubV_toBase_id] at c
    simp only [map_mul, map_one]
    exact c

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G] {e : ℕ} {D D' : DegPre R} {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {U : PreU I D A G} {U' : PreU I D' A' G}

def cubP (g : GtCoord I D e G) {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (z : T.left)
    (J : (T.left ⟶ D.P.A.left) → D.P.L.ι) (x y u : T ⟶ thickObj R I e G) : (T.left.presheaf.stalk z)ˣ :=
  cubV D.cub (T := (Over.map (thick R I e)).obj T) z J
    ((Over.map (thick R I e)).map x ≫ g.pG) ((Over.map (thick R I e)).map y ≫ g.pG)
    ((Over.map (thick R I e)).map u ≫ g.pG)

theorem cubP_congr (g : GtCoord I D e G) {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (z : T.left)
    (J : (T.left ⟶ D.P.A.left) → D.P.L.ι) {a b a' b' : T ⟶ thickObj R I e G} (c : T ⟶ thickObj R I e G)
    (ha : a ≫ g.q = a' ≫ g.q) (hb : b ≫ g.q = b' ≫ g.q) : cubP g z J a b c = cubP g z J a' b' c := by
  have k : ∀ {a a' : T ⟶ thickObj R I e G}, a ≫ g.q = a' ≫ g.q →
      (Over.map (thick R I e)).map a ≫ g.pG = (Over.map (thick R I e)).map a' ≫ g.pG := fun h =>
    Over.OverMorphism.ext (TorusInvariance.pG_congr g h)
  unfold cubP
  rw [k ha, k hb]

theorem vals (u : LB.Iso (D'.P.L.pull (U'.gt e).pG.left) (D.P.L.pull (U.gt e).pG.left))
    {wL : LB.Iso U'.P.L.L (U.P.L.L.pull (𝟙 G.left))} {hw : 𝟙 G.left ≫ G.hom = G.hom ≫ 𝟙 _}
    (hL : IsCPMap U'.P U.P (𝟙 _) (𝟙 G.left) hw wL)
    (sq : ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (jM : D.P.L.ι) (jM' : D'.P.L.ι)
      (jL : U.P.L.L.ι) (jL' : U'.P.L.L.ι), (U.gt e).pG.left (r z) ∈ D.P.L.U jM →
      (U'.gt e).pG.left (r z) ∈ D'.P.L.U jM' → (fstG I e G).left (r z) ∈ U.P.L.L.U jL →
      (fstG I e G).left (r z) ∈ U'.P.L.L.U jL' →
      gw u r z jM (fun _ => jM') * gw (U'.w e) r z jM' (fun _ => jL') =
        gw (U.w e) r z jM (fun _ => jL) * gw wL (r ≫ (fstG I e G).left) z jL jL')
    {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} {z : T.left} {J : (T.left ⟶ D.P.A.left) → D.P.L.ι}
    {J' : (T.left ⟶ D'.P.A.left) → D'.P.L.ι} (hJ : Good D.P.L z J) (hJ' : Good D'.P.L z J')
    (a : (T.left ⟶ (thickObj R I e G).left) → (T.left.presheaf.stalk z)ˣ)
    (ha : ∀ r, a r = gw u r z (J (r ≫ (U.gt e).pG.left)) (fun _ => J' (r ≫ (U'.gt e).pG.left))) :
    (∀ x : T ⟶ thickObj R I e G, val D.sym (x.left ≫ (U.gt e).pG.left) z J * a x.left =
      a (x⁻¹).left * val D'.sym (x.left ≫ (U'.gt e).pG.left) z J') ∧
    ∀ x y v : T ⟶ thickObj R I e G, cubP (U.gt e) z J x y v =
      a (x * y * v).left * (a (x * y).left)⁻¹ * (a (x * v).left)⁻¹ * (a (y * v).left)⁻¹ * a x.left * a y.left *
        a v.left * (a (1 : T ⟶ thickObj R I e G).left)⁻¹ * cubP (U'.gt e) z J' x y v := by
  obtain ⟨N, hN⟩ := exists_good_pt U.P.L.isLB z
  obtain ⟨N', hN'⟩ := exists_good_pt U'.P.L.isLB z
  obtain ⟨W, hW⟩ : ∃ W : (T ⟶ thickObj R I e G) → (T.left.presheaf.stalk z)ˣ, ∀ x, W x =
    gw (U.w e) x.left z (J (x.left ≫ (U.gt e).pG.left)) (fun _ => N (x.left ≫ (fstG I e G).left)) := ⟨_, fun _ => rfl⟩
  obtain ⟨W', hW'⟩ : ∃ W : (T ⟶ thickObj R I e G) → (T.left.presheaf.stalk z)ˣ, ∀ x, W x =
    gw (U'.w e) x.left z (J' (x.left ≫ (U'.gt e).pG.left)) (fun _ => N' (x.left ≫ (fstG I e G).left)) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : ((Over.map (thick R I e)).obj T ⟶ G) → (T.left.presheaf.stalk z)ˣ, ∀ x, d x =
    gw wL x.left z (N x.left) (N' x.left) := ⟨_, fun _ => rfl⟩
  obtain ⟨-, s₁, c₁⟩ := U.w_vals e T z N J hN hJ W hW
  obtain ⟨-, s₂, c₂⟩ := U'.w_vals e T z N' J' hN' hJ' W' hW'
  let β : (T ⟶ thickObj R I e G) →* ((Over.map (thick R I e)).obj T ⟶ G) :=
    MonoidHom.mk' (fun x => (Over.map (thick R I e)).map x ≫ fstG I e G) fun x y =>
      toBase_mul_pullback G (thick R I e) T x y
  obtain ⟨s₃, c₃⟩ := vals_id hL (T := (Over.map (thick R I e)).obj T) hN hN' d hd β
  have h : ∀ x : T ⟶ thickObj R I e G, a x.left * W' x = W x * d (β x) := fun x => by
    rw [ha, hW, hW', hd]
    exact sq _ x.left z _ _ _ _ (hJ _) (hJ' _) (hN _) (hN' _)
  refine ⟨fun x => ?_, fun x y v => ?_⟩
  · exact even_alg (a := fun x => a x.left) (d := fun x => d (β x)) h (s₁ x) (s₂ x) (s₃ x)
  · obtain ⟨c, hc⟩ : ∃ c : (T.left.presheaf.stalk z)ˣ,
      c = cubV U.P.c (T := (Over.map (thick R I e)).obj T) z N (β x) (β y) (β v) := ⟨_, rfl⟩
    obtain ⟨c', hc'⟩ : ∃ c : (T.left.presheaf.stalk z)ˣ,
      c = cubV U'.P.c (T := (Over.map (thick R I e)).obj T) z N' (β x) (β y) (β v) := ⟨_, rfl⟩
    have k₁ : cubP (U.gt e) z J x y v * W (x * y) * W (x * v) * W (y * v) * W 1 =
      W (x * y * v) * W x * W y * W v * c := (c₁ x y v).trans (congrArg (_ * ·) hc.symm)
    have k₂ : cubP (U'.gt e) z J' x y v * W' (x * y) * W' (x * v) * W' (y * v) * W' 1 =
      W' (x * y * v) * W' x * W' y * W' v * c' := (c₂ x y v).trans (congrArg (_ * ·) hc'.symm)
    have k₃ : c * d (β (x * y)) * d (β (x * v)) * d (β (y * v)) * d (β 1) =
        d (β (x * y * v)) * d (β x) * d (β y) * d (β v) * c' := by
      rw [hc, hc']; exact c₃ x y v
    have k := cube_alg (A := T ⟶ thickObj R I e G) (a := fun x => a x.left) (d := fun x => d (β x)) h k₁ k₂ k₃
    exact k

end PreTorusInvariance


open TorusInvariance PreTorusInvariance in

theorem preU_comparison_torus_invariant : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R) (D D' : DegPre R) (A A' : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (U' : PreU I D' A' G) (wL : LB.Iso U'.P.L.L (U.P.L.L.pull (𝟙 G.left))) (hw : 𝟙 G.left ≫ G.hom = G.hom ≫ 𝟙 _), IsCPMap U'.P U.P (𝟙 _) (𝟙 G.left) hw wL → ∀ (e : ℕ) (β : thickObj R I e D'.P.A ≅ thickObj R I e D.P.A), (U'.gt e).q ≫ β.hom = (U.gt e).q → ∀ u : LB.Iso (D'.P.L.pull (U'.gt e).pG.left) (D.P.L.pull (U.gt e).pG.left), u.IsGen → (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (jM : D.P.L.ι) (jM' : D'.P.L.ι) (jL : U.P.L.L.ι) (jL' : U'.P.L.L.ι), (U.gt e).pG.left (r z) ∈ D.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.P.L.U jM' → (fstG I e G).left (r z) ∈ U.P.L.L.U jL → (fstG I e G).left (r z) ∈ U'.P.L.L.U jL' → gw u r z jM (fun _ => jM') * gw (U'.w e) r z jM' (fun _ => jL') = gw (U.w e) r z jM (fun _ => jL) * gw wL (r ≫ (fstG I e G).left) z jL jL') → ∀ (Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (τ : Z ⟶ splitTorus _ D.X) (y : Z ⟶ thickObj R I e G) (z : Z.left) (jM : D.P.L.ι) (jM' : D'.P.L.ι), (U.gt e).pG.left (y.left z) ∈ D.P.L.U jM → (U'.gt e).pG.left (y.left z) ∈ D'.P.L.U jM' → gw u ((τ ≫ (U.gt e).i) * y).left z jM (fun _ => jM') = gw u y.left z jM (fun _ => jM') := by
  intro R _ _ _ I D D' A A' G _ _ U U' wL hw hL e β hβ u hu sq Z₀ τ₀ y₀ z₀ jM jM' m m'
  letI : IsIso β.hom := β.isIso_hom
  letI : Mono β.hom := IsIso.mono_of_iso β.hom
  have := (U.gt e).q_hom
  have := (U'.gt e).q_hom
  have := (U.gt e).i_hom
  have := U.semi.geomConnected
  have := connectedSpace_spec_quotient (I ^ (e + 1)) (Z₀.hom z₀)
  have : GeometricallyConnected (thickObj R I e G).hom :=
    inferInstanceAs (GeometricallyConnected (pullback.snd G.hom (thick R I e)))
  have : ConnectedSpace (thickObj R I e G).left :=
    GroupConn.connectedSpace_of_section (thickObj R I e G).hom (η : 𝟙_ _ ⟶ thickObj R I e G).left (Over.w _)
  have hq : ∀ {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (τ : Z ⟶ splitTorus _ D.X),
      (τ ≫ (U.gt e).i) ≫ (U.gt e).q = (1 : Z ⟶ thickObj R I e G) ≫ (U.gt e).q := fun τ => by
    rw [Category.assoc, (U.gt e).isKernel.w, MonObj.one_comp, ← Category.assoc, comp_toUnit, Hom.one_def]
  have hq' : ∀ {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (τ : Z ⟶ splitTorus _ D.X),
      (τ ≫ (U.gt e).i) ≫ (U'.gt e).q = (1 : Z ⟶ thickObj R I e G) ≫ (U'.gt e).q := fun τ => by
    rw [← cancel_mono β.hom, Category.assoc _ _ β.hom, Category.assoc _ _ β.hom, hβ]
    exact hq τ
  have hp : ∀ {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (τ : Z ⟶ splitTorus _ D.X)
      (y : Z ⟶ thickObj R I e G), ((τ ≫ (U.gt e).i) * y).left ≫ (U.gt e).pG.left = y.left ≫ (U.gt e).pG.left :=
    fun τ y => pG_congr _ (by rw [MonObj.mul_comp, hq, ← MonObj.mul_comp, _root_.one_mul])
  have hp' : ∀ {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (τ : Z ⟶ splitTorus _ D.X)
      (y : Z ⟶ thickObj R I e G), ((τ ≫ (U.gt e).i) * y).left ≫ (U'.gt e).pG.left = y.left ≫ (U'.gt e).pG.left :=
    fun τ y => pG_congr _ (by rw [MonObj.mul_comp, hq', ← MonObj.mul_comp, _root_.one_mul])
  obtain ⟨ρ, key⟩ := exists_ratio_translate (U.gt e).i D.P.isLB D'.P.isLB u hu (fun _ => hp) (fun _ => hp')
  have triv := ratio_eq_one (U.gt e).i ρ (fun Z z => by
    obtain ⟨J, hJ⟩ := exists_good_pt D.P.isLB z
    obtain ⟨J', hJ'⟩ := exists_good_pt D'.P.isLB z
    obtain ⟨a, ha⟩ : ∃ a : (Z.left ⟶ (thickObj R I e G).left) → (Z.left.presheaf.stalk z)ˣ,
      ∀ r, a r = gw u r z (J (r ≫ (U.gt e).pG.left)) (fun _ => J' (r ≫ (U'.gt e).pG.left)) := ⟨_, fun _ => rfl⟩
    obtain ⟨s, c⟩ := vals u hL sq hJ hJ' a ha
    refine ⟨a, fun t y => ?_, fun t t' y => ?_, fun t => ?_⟩
    · rw [ha, ha, hp, hp']
      exact key Z t y z _ _ (hJ _) (hJ' _)
    · have p := c (t ≫ (U.gt e).i) (t' ≫ (U.gt e).i) y
      have q := c 1 1 y
      rw [cubP_congr (U.gt e) z J y (hq t) (hq t'), cubP_congr (U'.gt e) z J' y (hq' t) (hq' t')] at p
      rw [prod_psum, prod_psum]
      exact mul_right_cancel (p.symm.trans q)
    · have p := s (t ≫ (U.gt e).i)
      have q := s 1
      rw [pG_congr (U.gt e) (hq t), pG_congr (U'.gt e) (hq' t)] at p
      exact cancel_even p q)
  rw [key Z₀ τ₀ y₀ z₀ jM jM' m m', triv, map_one, _root_.one_mul]

end GlobalTheory
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

namespace GlobalTheory.DegPullPackage

theorem isCPMap_of_rig (hG : GlobalFnsSt) {S S' : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B]
    {f : S' ⟶ S} {B' : Over S'} [GrpObj B'] [IsCommMonObj B'] (hB' : IsAbelianScheme B') (M : CP B) (M' : CP B')
    {β : B'.left ⟶ B.left} {hw : β ≫ B.hom = B'.hom ≫ f}
    (mul : ∀ (T : Over S') (x y : T ⟶ B'), toBase hw (x * y) = toBase hw x * toBase hw y)
    (w : LB.Iso M'.L.L (M.L.L.pull β)) (hg : w.IsGen)
    (he : eSec B' ≫ β = f ≫ eSec B)
    (hr' : PMaps w (fun _ : PUnit => eSec B') (fun _ => eSec B) (fun _ => 1) M'.L.rig M.L.rig f) :
    IsCPMap M' M f β hw w := by
  obtain ⟨rig, hr, c, s, hs, h₂, h₃, H⟩ := exists_isCPMap M mul M'.L.L M'.L.isLB w hg
  let N : CP B' := ⟨⟨M'.L.L, rig, M'.L.isLB, hr⟩, c, s, hs, h₂, h₃⟩
  have es : ∀ (Z : Scheme.{0}) (r : Z ⟶ B'.left) (z : Z) (J), Good M'.L.L z J → val s r z J = val M'.sym r z J :=
    gen_unique M'.L.isLB B'.hom (1 : 𝟙_ (Over S') ⟶ B').left (Over.w _) (hG _ _ hB').2 hs M'.sym_gen
      fun y J hJ => (N.val_sym_one hJ).trans (M'.val_sym_one hJ).symm
  have ec : ∀ (T : Over S') (z : T.left) (J), Good M'.L.L z J → ∀ x y u : T ⟶ B',
      cubV c z J x y u = cubV M'.c z J x y u := fun T z J hJ x y u =>
    gen_unique M'.L.isLB (φ := thφ B' (x3 B')) (ε := thε) (G3 B').hom
      (lift (1 : 𝟙_ (Over S') ⟶ B') (lift 1 1)).left (Over.w _) (surjective_cube hG hB') c.isGen M'.c.isGen
      (fun y J hJ => ((isCub_cubV c hJ).face 1 1).trans ((isCub_cubV M'.c hJ).face 1 1).symm) _ _ z J hJ
  refine ⟨mul, hg, fun T z J' J hJ' hJ W hW => ?_⟩
  obtain ⟨-, a₂, a₃⟩ := H.vals T z J' J hJ' hJ W hW
  refine ⟨?_, fun x => ?_, fun x y u => ?_⟩
  · have e := CubTransport.val_pmaps (fun _ => he) hr' T.hom hJ hJ'
    rw [Fintype.prod_unique, zpow_one] at e
    rw [hW, one_left]
    exact e
  · exact (a₂ x).trans (congrArg (W x⁻¹ * ·) (es _ x.left z J' hJ'))
  · exact (a₃ x y u).trans (congrArg (W (x * y * u) * W x * W y * W u * ·) (ec T z J' hJ' x y u))

theorem isCPMap_of_isPullDeg : ∀ (hG : GlobalFnsSt) (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (φ : R →+* V) (D : DegPre R) (D' : DegPre V) (hD : IsPullDeg φ D D'), IsCPMap (CP.ofDegPre hG D') (CP.ofDegPre hG D) (spMap φ) (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) (pull_grp hD).1.w hD.w := by
  intro hG R V _ _ _ _ φ D D' hD
  exact isCPMap_of_rig hG D'.P.isAb (CP.ofDegPre hG D) (CP.ofDegPre hG D')
    (fun T x y => Over.OverMorphism.ext ((pull_grp hD).2 T x y _ _ rfl rfl).symm) hD.w hD.w_gen hD.he
    ((maps_iff hD.w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf φ) _
      (rigPull_le (G' := D'.P.A) (G := D.P.A) _ (specOf φ) hD.he D.P.L) (fun _ => rfl)).1 hD.w_rig)

end GlobalTheory.DegPullPackage
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData

namespace GlobalTheory.TwistLabels
section
variable {O : Type} [CommRing O] {N : NumD O} {k : ℕ} {β : N.Form k} {u r : Oˣ} {j : ℕ}

theorem wp_eq {p q : N.QT j} {p' q' : (N.twist β u).QT j} (hp : TwRel β u r p p') (hq : TwRel β u r q q') :
    (N.twist β u).wp p' q' = N.wp p q := by
  have a : p'.1.2.s q'.1.1.toAdd = p.1.2.s q.1.1.toAdd * r ^ β.be p.1.1.toAdd q.1.1.toAdd := by
    rw [hq.1]; exact hp.2.2 _
  have b : q'.1.2.s p'.1.1.toAdd = q.1.2.s p.1.1.toAdd * r ^ β.be p.1.1.toAdd q.1.1.toAdd := by
    rw [hp.1, β.symm]; exact hq.2.2 _
  unfold NumD.wp NumD.tk
  rw [a, b, hp.2.1, hq.2.1]
  change _ * _ * cubN N.θ j 1 q.1.2.b p.1.2.b / (_ * _ * cubN N.θ j 1 p.1.2.b q.1.2.b) = _
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div]
  abel

theorem rel_mul {p q : N.QT j} {p' q' : (N.twist β u).QT j} (hp : TwRel β u r p p') (hq : TwRel β u r q q') :
    TwRel β u r (p * q) (p' * q') := by
  refine ⟨?_, ?_, fun z => ?_⟩
  · change p'.1.1 * q'.1.1 = p.1.1 * q.1.1
    rw [hp.1, hq.1]; rfl
  · change p'.1.2.b * q'.1.2.b = p.1.2.b * q.1.2.b
    rw [hp.2.1, hq.2.1]; rfl
  · change p'.1.2.s z * q'.1.2.s z / N.θ (N.c z) p'.1.2.b q'.1.2.b =
      p.1.2.s z * q.1.2.s z / N.θ (N.c z) p.1.2.b q.1.2.b * r ^ β.be (p.1.1.toAdd + q.1.1.toAdd) z
    rw [hp.2.2, hq.2.2, hp.2.1, hq.2.1, map_add (f := _), LinearMap.add_apply, zpow_add]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div]
    abel

theorem rel_inj {p q : N.QT j} {p' : (N.twist β u).QT j} (hp : TwRel β u r p p') (hq : TwRel β u r q p') : p = q := by
  have e : p.1.1 = q.1.1 := hp.1.symm.trans hq.1
  refine Subtype.ext (Prod.ext e (NumD.Gt.ext (hp.2.1.symm.trans hq.2.1) (funext fun z => ?_)))
  have := (hp.2.2 z).symm.trans (hq.2.2 z)
  rw [e] at this
  exact mul_right_cancel this

theorem rel_fun {p : N.QT j} {p' q' : (N.twist β u).QT j} (hp : TwRel β u r p p') (hq : TwRel β u r p q') : p' = q' :=
  Subtype.ext (Prod.ext (hp.1.trans hq.1.symm) (NumD.Gt.ext (hp.2.1.trans hq.2.1.symm)
    (funext fun z => (hp.2.2 z).trans (hq.2.2 z).symm)))

theorem rel_triv (h : r ^ j = u) (z : N.X) : TwRel β u r (N.qTriv j z) ((N.twist β u).qTriv j z) := by
  refine ⟨rfl, rfl, fun χ => ?_⟩
  change (N.twist β u).τ z χ = N.τ z χ * r ^ β.be (j • z) χ
  rw [N.twist_τ, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul, zpow_mul, zpow_natCast, h]

theorem qEq_iff (h : r ^ j = u) {p q : N.QT j} {p' q' : (N.twist β u).QT j} (hp : TwRel β u r p p')
    (hq : TwRel β u r q q') : (N.twist β u).QEq p' q' ↔ N.QEq p q := by
  rw [NumD.qEq_iff, NumD.qEq_iff]
  refine exists_congr fun (z : N.X) => ?_
  have t := rel_mul hp (rel_triv (β := β) h z)
  exact ⟨fun e => rel_inj hq (e ▸ t), fun e => rel_fun hq (e ▸ t)⟩

theorem pow_s_eq (g : N.Gt) (g' : (N.twist β u).Gt) (hb : g'.b = g.b) (z : N.X) (t : Oˣ) (hs : g'.s z = g.s z * t)
    (m : ℕ) : (g' ^ m).s z = (g ^ m).s z * t ^ m := by
  have a := g.pow_s m z
  have b := g'.pow_s m z
  rw [hs, hb, mul_pow, ← a, mul_right_comm] at b
  exact mul_right_cancel b

theorem zpow_pow_comm (x : Oˣ) (n : ℤ) (m : ℕ) : (x ^ n) ^ m = (x ^ m) ^ n := by
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]

theorem rel_surj (h : r ^ j = u) (p' : (N.twist β u).QT j) : ∃ p : N.QT j, TwRel β u r p p' := by
  let y : N.X := p'.1.1.toAdd
  let g : N.Gt := ⟨p'.1.2.b, fun z => p'.1.2.s z / r ^ β.be y z, fun χ χ' => by
    have a : p'.1.2.s (χ + χ') * N.θ (N.c χ) (N.c χ') p'.1.2.b = p'.1.2.s χ * p'.1.2.s χ' := p'.1.2.mult χ χ'
    rw [map_add (f := _), zpow_add, div_mul_eq_mul_div, a, div_mul_div_comm]⟩
  have hs : ∀ z : N.X, p'.1.2.s z = g.s z * r ^ β.be y z := fun z => (div_mul_cancel _ _).symm
  have hp : p'.1.2 ^ j = (N.twist β u).io y := p'.2
  refine ⟨⟨(Multiplicative.ofAdd y, g), ?_⟩, rfl, rfl, hs⟩
  refine NumD.Gt.ext ?_ (funext fun z => ?_)
  · exact (g.pow_b j).trans ((N.twist β u).QT_pow_b p')
  · have a := pow_s_eq g p'.1.2 rfl z _ (hs z) j
    rw [hp, zpow_pow_comm, h] at a
    exact mul_right_cancel (a.symm.trans (N.twist_τ β u y z))
end

theorem labels_twist : ∀ (C : Type) [Field C] (N : NumD C) (La : Type) [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (ζ : ℕ → Cˣ) (lab : ∀ k : ℕ, La → N.QT k) (k₀ : ℕ) (β : N.Form k₀) (u : Cˣ) (r : ℕ → Cˣ), Roots u r → Labels N EF ζ lab → ∀ p : ∀ k : ℕ, La → (N.twist β u).QT k, (∀ k, 0 < k → ∀ x, TwRel β u (r k) (lab k x) (p k x)) → Labels (N.twist β u) EF ζ p := by
  intro C _ N La _ EF ζ lab k₀ β u r hr ⟨h1, h2, h3, h4, h5⟩ p hp
  refine ⟨fun k hk a b => ?_, fun k hk a b => ?_, fun k hk q' => ?_, fun k m hk hm a q' e1 e2 => ?_, fun k hk a b => ?_⟩
  · exact (qEq_iff (hr.pow hk) (rel_mul (hp k hk a) (hp k hk b)) (hp k hk (a + b))).2 (h1 k hk a b)
  · exact (qEq_iff (hr.pow hk) (hp k hk a) (hp k hk b)).trans (h2 k hk a b)
  · obtain ⟨q, hq⟩ := rel_surj (hr.pow hk) q'
    obtain ⟨a, ha⟩ := h3 k hk q
    exact ⟨a, (qEq_iff (hr.pow hk) (hp k hk a) hq).2 ha⟩
  · obtain ⟨q, hq⟩ := rel_surj (hr.pow hk) q'
    have t := hp (k * m) (Nat.mul_pos hk hm) a
    have e : q.1.1 = (lab (k * m) a).1.1 := hq.1.symm.trans (e1.trans t.1)
    refine (qEq_iff (hr.pow hk) hq (hp k hk a)).2 (h4 k m hk hm a q e (NumD.Gt.ext ?_ (funext fun z => ?_)))
    · rw [← hq.2.1, e2, NumD.Gt.pow_b, NumD.Gt.pow_b, t.2.1]; rfl
    · have s := pow_s_eq _ _ t.2.1 z _ (t.2.2 z) m
      rw [← e2, hq.2.2, e, zpow_pow_comm, hr.2 k m hk hm] at s
      exact mul_right_cancel s
  · exact (wp_eq (hp k hk a) (hp k hk b)).trans (h5 k hk a b)

end GlobalTheory.TwistLabels
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData

noncomputable section
namespace GlobalTheory.ValuesStrictPull
open GlobalTheory.TorusExt GlobalTheory.ArcPull GlobalTheory.ArcTransport
open GlobalTheory.PsiEvenPull (proj)
open ReciprocityTheory.ChartRestriction.G.DVR (cP)

section Val
variable {F : Type} [Field F] {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

theorem const_vF (t : LB.Gen (LB.LinComb L φ ε)) (r : Sp F ⟶ Y) {z : Sp F} {J : (Sp F ⟶ X) → L.ι} (hJ : Good L z J) :
    stalkConst z (vF t r J) = (val t r z J).val :=
  ((gs_unit r z _ (hJ.mem φ r) _).symm.trans (gs_eq_stalkConst r z
    (fun w _ => (Subsingleton.elim (α := PrimeSpectrum F) z w) ▸ hJ.mem φ r) _)).symm

theorem const_sF (s : LB.Sec (LB.LinComb L φ ε)) (r : Sp F ⟶ Y) {z : Sp F} {J : (Sp F ⟶ X) → L.ι} (hJ : Good L z J) :
    stalkConst z (sF s r J) = sval s r z J :=
  (gs_eq_stalkConst r z (fun w _ => (Subsingleton.elim (α := PrimeSpectrum F) z w) ▸ hJ.mem φ r) _).symm

theorem vF_congr {X' Y' : Scheme.{0}} {L' : LB X'} {K' : Type} [Fintype K'] {φ' : K' → (Y' ⟶ X')} {ε' : K' → ℤ}
    {t : LB.Gen (LB.LinComb L φ ε)} {r : Sp F ⟶ Y} {z : Sp F} {J : (Sp F ⟶ X) → L.ι} (hJ : Good L z J)
    {t' : LB.Gen (LB.LinComb L' φ' ε')} {r' : Sp F ⟶ Y'} {J' : (Sp F ⟶ X') → L'.ι} (hJ' : Good L' z J')
    (h : val t r z J = val t' r' z J') : vF t r J = vF t' r' J' :=
  (stalkConst z).injective ((const_vF t r hJ).trans ((congrArg Units.val h).trans (const_vF t' r' hJ').symm))
end Val

theorem exists_numOf_strict_pull : GlobalFnsSt → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R') (D : DegPre R) (D' : DegPre R') (hD : IsPullDeg φ D D'), Strict hD.w → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F], (∀ x, algebraMap (FractionRing R') F (algebraMap R' _ (φ x)) = algebraMap (FractionRing R) F (algebraMap R _ x)) → ∀ (N : NumD F) (ν : NumOf D F N) (th' : H0 D'.P.L 1), (∀ s : H0 D'.P.L 1, ∃ r : R', ∀ j, s.f j = resTop _ (scal D'.P.A.hom r) * th'.f j) → (∀ (Z : Scheme.{0}) (r : Z ⟶ D'.P.A.left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D'.P.A.left) → D'.P.L.ι), Good D.P.L z J → Good D'.P.L z J' → sval ν.th (r ≫ PsiEvenPull.proj hD) z J = (gw hD.w r z (J (r ≫ PsiEvenPull.proj hD)) (J' r)).val * sval th' r z J') → ∃ ν' : NumOf D' F N, (∀ y, hD.xe (ν'.eX y) = ν.eX y) ∧ ∀ x, (ν'.eA x).left ≫ PsiEvenPull.proj hD = (ν.eA x).left := by
  intro hG R R' _ _ _ _ φ D D' hD hS F _ _ _ hF N ν th' hgen hth
  obtain ⟨c, hc⟩ := hS
  have hT : (TF (R := R') F).hom ≫ spMap φ = (TF (R := R) F).hom := base_comm fun r => (hF r).symm
  have hj : jFK (R := R') F ≫ jK R' ≫ spMap φ = jFK (R := R) F ≫ jK R := (Category.assoc _ _ _).symm.trans hT
  let z : Sp F := IsLocalRing.closedPoint F
  let J' : (Sp F ⟶ D'.P.A.left) → D'.P.L.ι := fun ψ => c (ν.J (ψ ≫ proj hD))
  have hJ : Good D.P.L z ν.J := fun ψ => ν.good ψ trivial
  have good' : ∀ ψ : Sp F ⟶ D'.P.A.left, ⊤ ≤ ψ ⁻¹ᵁ D'.P.L.U (J' ψ) := fun ψ y _ =>
    (hc _ ψ y _ (ν.good (ψ ≫ proj hD) (x := y) trivial)).1
  have hJ' : Good D'.P.L z J' := fun ψ => good' ψ trivial
  have one : ∀ ψ : Sp F ⟶ D'.P.A.left, Geo.Tor.gw hD.w ψ z (ν.J (ψ ≫ proj hD)) (J' ψ) = 1 := fun ψ =>
    (hc _ ψ z _ (hJ (ψ ≫ proj hD))).2
  have one' : ∀ ψ : Sp F ⟶ D'.P.A.left, om hD.w z ν.J J' ψ = 1 := one
  have one'' : ∀ x : TF (R := R') F ⟶ D'.P.A, wVal hD.w z ν.J J' x = 1 := fun x => one x.left
  let P : (TF (R := R') F ⟶ D'.P.A) ≃* (TF (R := R) F ⟶ D.P.A) :=
    MulEquiv.ofBijective (MonoidHom.mk' (pushF (pull_grp hD) hT) (pushF_mul _ _))
      ⟨pushF_injective (pull_grp hD) hT, pushF_surjective (pull_grp hD) hT⟩
  obtain ⟨eA, heA⟩ : ∃ eA : N.A ≃* (TF (R := R') F ⟶ D'.P.A), ∀ x, pushF (pull_grp hD) hT (eA x) = ν.eA x :=
    ⟨ν.eA.trans P.symm, fun x => P.apply_symm_apply _⟩
  have hl : ∀ x, (eA x).left ≫ proj hD = (ν.eA x).left := fun x => congrArg (fun q => q.left) (heA x)
  obtain ⟨eX, heX⟩ : ∃ eX : N.X ≃+ D'.X, ∀ y, hD.xe (eX y) = ν.eX y :=
    ⟨ν.eX.trans hD.xe.symm, fun y => hD.xe.apply_symm_apply _⟩
  have rig : vF (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig (TF (R := R) F).hom ν.J =
      vF (L := D'.P.L) (φ := fun _ : PUnit => eSec D'.P.A) (ε := fun _ => 1) D'.rig (TF (R := R') F).hom J' := by
    have e := ArcPull.rig_val hD (Z := Sp F) _ _ hj hJ hJ'
    rw [one', _root_.one_mul] at e
    exact vF_congr hJ hJ' ((val_pull hJ _ _ _).symm.trans (e.trans (val_pull hJ' _ _ _)))
  refine ⟨{
    J := J', good := good', th := th', th_gen := hgen, eA := eA, eX := eX
    c_eq := fun χ => ?_, θ_eq := fun x y u => ?_, σ_eq := fun x => ?_, th_eq := fun x => ?_
    ψ_eq := fun χ => ?_ }, heX, hl⟩
  · apply pushF_injective (pull_grp hD) hT
    rw [heA, ν.c_eq, ← heX]
    exact Over.OverMorphism.ext ((cPoint_proj hD (T := TF (R := R) F) (T' := TF (R := R') F) (𝟙 _)
      (hT.trans (Category.id_comp _).symm) _).trans (Category.id_comp _)).symm
  · have k := thS_push (pull_grp hD) hT ((isGen_iff _).1 hD.w_gen) hG hJ hJ' (eA x) (eA y) (eA u)
    simp only [one'', heA, inv_one, _root_.one_mul] at k
    exact (ν.θ_eq x y u).trans (vF_congr hJ hJ' k)
  · have k := PsiEvenPull.sym_pull hG hD (Z := Sp F) (eA x).left z hJ hJ'
    rw [one, one, inv_one, _root_.one_mul, _root_.one_mul] at k
    refine (ν.σ_eq x).trans (vF_congr hJ hJ' (Eq.trans ?_ k))
    exact congrArg (fun q => val (Z := Sp F) D.sym q z ν.J) (hl x).symm
  · have k := hth (Sp F) (eA x).left z ν.J J' hJ hJ'
    rw [one, Units.val_one, _root_.one_mul] at k
    rw [← rig, ν.th_eq x]
    refine (stalkConst z).injective ((const_sF _ _ hJ).trans (Eq.trans ?_ (k.trans (const_sF _ _ hJ').symm)))
    exact congrArg (fun q => sval (Z := Sp F) ν.th q z ν.J) (hl x).symm
  · have k := ArcPull.psi_val hD (Z := Sp F) _ _ hj hJ hJ' (eX χ)
    rw [one', inv_one, _root_.one_mul, heX] at k
    rw [← rig, ν.ψ_eq χ]
    exact congrArg (· * _) (vF_congr hJ hJ' k)

end GlobalTheory.ValuesStrictPull
end
end
