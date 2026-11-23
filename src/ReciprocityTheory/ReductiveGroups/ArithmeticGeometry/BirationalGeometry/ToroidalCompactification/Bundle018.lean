module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DualMapSCompScaleS
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle017

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj

def PullCubDescentSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V],
    IsAdicComplete (maximalIdeal V) V →
    ∀ (t t' : SAB H (Sp V)) (tK : SAB H (Sp (FractionRing V))), IsProper tK.G.hom →
    ∀ (m : SABMap tK t (spMap (algebraMap V (FractionRing V))))
      (m' : SABMap tK t' (spMap (algebraMap V (FractionRing V)))) (ψ : t.G ⟶ t'.G) [IsMonHom ψ],
      m.φ ≫ ψ.left = m'.φ → (CubeMap.ofHom ψ).IsPullCubical t.cub t'.cub

theorem extV_of (hHom : HomExtDvrSt) (hD : PullCubDescentSt) : ExtVStatement := by
  intro E _ _ _ H V _ _ _ hc t t' tK hK m m'
  obtain ⟨ψ, hψm, hψ, hact⟩ := extV_grp hHom t t' tK m m'
  have := hψm
  refine ⟨{ cm := CubeMap.ofHom ψ.hom
            cart := isGrpPullback_of_iso ψ
            base := rfl
            act := fun a => by
              show (t.act.act a).left ≫ ψ.hom.left = ψ.hom.left ≫ (t'.act.act a).left
              rw [← Over.comp_left, hact a, Over.comp_left]
            lin := hD E H V hc t t' tK hK m m' ψ.hom hψ }, hψ⟩

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.Chart

attribute [local instance] Over.cartesianMonoidalCategory

section Maps

variable {S : Type} [CommRing S]

def awayHom (u : S) (B : Type) [CommRing B] [Algebra S B] (hu : IsUnit (algebraMap S B u)) :
    Localization.Away u →ₐ[S] B :=
  { IsLocalization.Away.lift u hu with commutes' := fun r => IsLocalization.Away.lift_eq u hu r }

def qHom (u v : S) (B : Type) [CommRing B] [Algebra S B] (hu : IsUnit (algebraMap S B u))
    (hv : IsUnit (algebraMap S B v)) : Qv u v →ₐ[S] B :=
  { IsLocalization.Away.lift (algebraMap S (Localization.Away u) v) (g := (awayHom u B hu).toRingHom)
      (by rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]; exact hv) with
    commutes' := fun r => by
      show IsLocalization.Away.lift (algebraMap S (Localization.Away u) v) _
        (algebraMap (Localization.Away u) (Qv u v) (algebraMap S (Localization.Away u) r)) = algebraMap S B r
      rw [IsLocalization.Away.lift_eq]
      exact (awayHom u B hu).commutes r }

theorem away_unit (u : S) : IsUnit (algebraMap S (Localization.Away u) u) :=
  IsLocalization.Away.algebraMap_isUnit u

theorem unit_of_map {B B' : Type} [CommRing B] [Algebra S B] [CommRing B'] [Algebra S B'] [Algebra B B']
    [IsScalarTower S B B'] {u : S} (h : IsUnit (algebraMap S B u)) : IsUnit (algebraMap S B' u) := by
  rw [IsScalarTower.algebraMap_apply S B B']
  exact h.map _

end Maps

section Extend

variable {S : Type} [CommRing S] {G : Over (Spec (CommRingCat.of S))} [GrpObj G]

theorem scale_pow_add {A : Type} [CommRing A] [Algebra S A] (x : A) (a b : ℕ) (y : sp (R₀ := S) (DualNumber A) ⟶ G) :
    spMap (scaleS (S := S) (x ^ a)) ≫ spMap (scaleS (x ^ b)) ≫ y = spMap (scaleS (x ^ (a + b))) ≫ y := by
  rw [scale_scale, pow_add]

theorem scale_pow_mono {A : Type} [CommRing A] [Algebra S A] (x : A) {m M : ℕ} (hm : m ≤ M)
    {y₁ y₂ : sp (R₀ := S) (DualNumber A) ⟶ G} (h : spMap (scaleS (S := S) (x ^ m)) ≫ y₁ = spMap (scaleS (x ^ m)) ≫ y₂) :
    spMap (scaleS (S := S) (x ^ M)) ≫ y₁ = spMap (scaleS (x ^ M)) ≫ y₂ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [add_comm m d, ← scale_pow_add x d m y₁, ← scale_pow_add x d m y₂, h]

variable [∀ s : S, Smooth (Gs G s).hom]

include G in
theorem fp_chart {s : S} (C : Chart (Gs G s)) : Algebra.FinitePresentation (Localization.Away s) Γ((Gs G s).left, C.U) := by
  haveI := chart_smooth (C := C)
  infer_instance

theorem tanS_away_lift {s : S} (C : Chart (Gs G s)) {A : Type} [CommRing A] [Algebra S A]
    [Algebra (Localization.Away s) A] [IsScalarTower S (Localization.Away s) A] (t : S)
    {y' : sp (R₀ := S) (DualNumber (Localization.Away (algebraMap S A t))) ⟶ G} (hy' : TanS y') :
    ∃ N : ℕ, ∃ y : sp (R₀ := S) (DualNumber A) ⟶ G, TanS y ∧
      spMap (dualMapS (IsScalarTower.toAlgHom S A (Localization.Away (algebraMap S A t)))) ≫ y =
        spMap (scaleS (S := S) (algebraMap S (Localization.Away (algebraMap S A t)) t ^ N)) ≫ y' := by
  haveI := fp_chart C
  haveI : IsLocalization (Algebra.algebraMapSubmonoid A
      (Submonoid.powers (algebraMap S (Localization.Away s) t)))
      (Localization.Away (algebraMap S A t)) := by
    have e : Algebra.algebraMapSubmonoid A (Submonoid.powers (algebraMap S (Localization.Away s) t)) =
        Submonoid.powers (algebraMap S A t) := by
      rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers, ← IsScalarTower.algebraMap_apply]
    rw [e]
    infer_instance
  obtain ⟨m, hm, y, hy, heq⟩ := tanS_lift C (A := A) (A' := Localization.Away (algebraMap S A t))
    (Submonoid.powers (algebraMap S (Localization.Away s) t)) hy'
  obtain ⟨N, rfl⟩ := hm
  refine ⟨N, y, hy, ?_⟩
  rw [heq, map_pow, ← IsScalarTower.algebraMap_apply]

theorem tanS_away_uniq {s : S} (C : Chart (Gs G s)) {A : Type} [CommRing A] [Algebra S A]
    [Algebra (Localization.Away s) A] [IsScalarTower S (Localization.Away s) A] (t : S)
    {y₁ y₂ : sp (R₀ := S) (DualNumber A) ⟶ G} (h₁ : TanS y₁) (h₂ : TanS y₂)
    (he : spMap (dualMapS (IsScalarTower.toAlgHom S A (Localization.Away (algebraMap S A t)))) ≫ y₁ =
      spMap (dualMapS (IsScalarTower.toAlgHom S A (Localization.Away (algebraMap S A t)))) ≫ y₂) :
    ∃ N : ℕ, spMap (scaleS (S := S) (algebraMap S A t ^ N)) ≫ y₁ = spMap (scaleS (algebraMap S A t ^ N)) ≫ y₂ := by
  haveI := fp_chart C
  haveI : IsLocalization (Algebra.algebraMapSubmonoid A
      (Submonoid.powers (algebraMap S (Localization.Away s) t)))
      (Localization.Away (algebraMap S A t)) := by
    have e : Algebra.algebraMapSubmonoid A (Submonoid.powers (algebraMap S (Localization.Away s) t)) =
        Submonoid.powers (algebraMap S A t) := by
      rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers, ← IsScalarTower.algebraMap_apply]
    rw [e]
    infer_instance
  obtain ⟨m, hm, heq⟩ := tanS_uniq C (A := A) (A' := Localization.Away (algebraMap S A t))
    (Submonoid.powers (algebraMap S (Localization.Away s) t)) h₁ h₂ he
  obtain ⟨N, rfl⟩ := hm
  refine ⟨N, ?_⟩
  rw [map_pow, ← IsScalarTower.algebraMap_apply] at heq
  exact heq

end Extend

end ReciprocityTheory.ChartRestriction.G.Chart
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem sabMap_cubical {S S' : Scheme.{0}} {t : SAB H S} {t₁ t₂ : SAB H S'} {f : S' ⟶ S} (m₁ : SABMap t₁ t f)
    (m₂ : SABMap t₂ t f) (ψ : t₁.G ≅ t₂.G) [IsMonHom ψ.hom] (hφ : ψ.hom.left ≫ m₂.φ = m₁.φ) :
    (CubeMap.ofHom ψ.hom).IsPullCubical t₁.cub t₂.cub := by
  have hφ' : ψ.hom.left ≫ m₂.cm.F = m₁.cm.F := hφ
  have h3 : m₁.cm.F3 = (CubeMap.ofHom ψ.hom).F3 ≫ m₂.cm.F3 := hom_ext_triple _ fun i => by
    rw [cubeMap_comp_proj_three, Category.assoc, cubeMap_comp_proj_three]
    show _ = (ψ.hom ⊗ₘ ψ.hom ⊗ₘ ψ.hom).left ≫ _
    rw [← Category.assoc, ← Over.comp_left, ← cubeProj_comp_map, Over.comp_left, Category.assoc, hφ']
  exact pullCubCancel _ _ _ _ _ _ m₂.cm (CubeMap.ofHom ψ.hom) m₁.cm _ _ _ t.cub t₂.cub t₁.cub hφ'.symm h3
    (by show m₁.cm.e = 𝟙 _ ≫ m₂.cm.e; rw [Category.id_comp, m₁.base, m₂.base]) m₂.lin m₁.lin

theorem sabMap_iso {S S' : Scheme.{0}} {t : SAB H S} {t₁ t₂ : SAB H S'} {f : S' ⟶ S} (m₁ : SABMap t₁ t f)
    (m₂ : SABMap t₂ t f) {L₁ : RigLB t₁.G} {L₂ : RigLB t₂.G} (h₁ : L₁ = t₁.PP) (h₂ : L₂ = t₂.PP) :
    ∃ ψ : t₁.G ≅ t₂.G, IsMonHom ψ.hom ∧ ψ.hom.left ≫ m₂.φ = m₁.φ ∧
      (∀ x, t₁.act.act x ≫ ψ.hom = ψ.hom ≫ t₂.act.act x) ∧
      ∃ (he : eSec t₁.G ≫ ψ.hom.left = 𝟙 _ ≫ eSec t₂.G) (wL : LB.Iso L₁.L (L₂.L.pull ψ.hom.left)),
        wL.IsGen ∧ LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec t₁.G) (fun _ => 1)) L₁.rig
          (rigPullOf ψ.hom.left (𝟙 _) he L₂.L L₂.rig) := by
  subst h₁ h₂
  obtain ⟨ψ, hψ, hφ⟩ := grpPullback_iso m₁.cart m₂.cart
  have hφ' : ψ.hom.left ≫ m₂.cm.F = m₁.cm.F := hφ
  refine ⟨ψ, hψ, hφ, fun x => ?_, ?_⟩
  · apply Over.OverMorphism.ext
    apply m₂.cart.1.hom_ext
    · simp only [Over.comp_left, Category.assoc, m₂.act, reassoc_of% hφ', hφ', m₁.act]
    · rw [Over.w, Over.w]
  · have := hψ
    obtain ⟨w, h₀, hg, hm⟩ := rigIso_congr rfl (CubeMap.ofHom ψ.hom) (sabMap_cubical m₁ m₂ ψ hφ) rfl rfl
    exact ⟨h₀, w, hg, hm⟩

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem ArcWit.uwIso {Y : Model Xo c β} {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'} {a : ArcIn D l β O' b}
    {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {f : O' →+* R} {u : R} {χ : Sp R ⟶ Y.X}
    (W W' : ArcWit Y a I f u χ) :
    ∃ ψ : W.t.G ≅ W'.t.G, ψ.hom.left ≫ W'.m.φ = W.m.φ ∧ IsMonHom ψ.hom ∧
      (∀ x, W.t.act.act x ≫ ψ.hom = ψ.hom ≫ W'.t.act.act x) ∧
      (∀ (T : Scheme.{0}) (g : T ⟶ W.t.G.left) (g₁ : T ⟶ Y.oF.t.G.left) (g₂ : T ⟶ Y.oF.t.G.left),
        g ≫ W.m.φ = g₁ ≫ Y.m.φ → g₁ ≫ Y.m0.toSABMap.φ = g₂ ≫ Y.m0.toSABMap.φ →
        g₁ ≫ Y.oF.t.G.hom = g₂ ≫ Y.oF.t.G.hom → g ≫ ψ.hom.left ≫ W'.m.φ = g₂ ≫ Y.m.φ) ∧
      ∃ (he : eSec W.t.G ≫ ψ.hom.left = 𝟙 _ ≫ eSec W'.t.G)
        (wL : LB.Iso W.P.U.LG.L (W'.P.U.LG.L.pull ψ.hom.left)),
        wL.IsGen ∧ LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec W.t.G) (fun _ => 1)) W.P.U.LG.rig
          (rigPullOf ψ.hom.left (𝟙 _) he W'.P.U.LG.L W'.P.U.LG.rig) := by
  obtain ⟨ψ, hmon, hφ, hact, he, wL, hgen, hmaps⟩ :=
    sabMap_iso W.m W'.m (L₁ := W.P.U.LG) (L₂ := W'.P.U.LG) W.P.bundle W'.P.bundle
  refine ⟨ψ, hφ, hmon, hact, fun T g g₁ g₂ h1 h2 h3 => ?_, he, wL, hgen, hmaps⟩
  rw [hφ, h1]

  have hc := Y.m0.toSABMap.cart
  unfold IsGrpPullback at hc
  unfold SABMap.φ at h2
  rw [hc.1.hom_ext h2 h3]

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end
