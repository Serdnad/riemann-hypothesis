module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsHomOfThickenings
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsHomOfVeryAmpleBy
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle017
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle045
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorsionEqOneOfTranslationKeepsRatios
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle081
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle074
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle103
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle072
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle086
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle100
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle067
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle102
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle092
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle096
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle109
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle006
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle110
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle001
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle036
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.lineBundleKernel_flat_of_finite_noetherian_local : GlobalFnsSt → ∀ (V : Type) [CommRing V] [IsNoetherianRing V] [IsLocalRing V] (B : Over (Sp V)) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → IsProjBy B.hom → ∀ L : LB B.left, L.IsLB → (∃ t : LB.Gen (Theta B L), t.IsGen) → ∀ (H : Over (Sp V)) (j : H ⟶ B), IsClosedImmersion j.left → (∀ (T : Over (Sp V)) (x : T ⟶ B), GlobalTheory.MemKL B L x ↔ ∃ z : T ⟶ H, z ≫ j = x) → IsFinite H.hom → Flat H.hom := by
  first | exact @GlobalTheory.StabFlatLocal.flat_of_isFinite | exact GlobalTheory.StabFlatLocal.flat_of_isFinite | (intros; apply GlobalTheory.StabFlatLocal.flat_of_isFinite <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GrpAlg

theorem inv_one_of_isGrpPullback {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') :
    (∀ (x : T ⟶ G') (x₀ : Over.mk (T.hom ≫ f) ⟶ G), x₀.left = x.left ≫ φ →
      (x₀⁻¹).left = (x⁻¹).left ≫ φ) ∧
    (1 : Over.mk (T.hom ≫ f) ⟶ G).left = (1 : T ⟶ G').left ≫ φ := by
  let F : (T ⟶ G') → (Over.mk (T.hom ≫ f) ⟶ G) := fun x =>
    Over.homMk (x.left ≫ φ) (by
      change (x.left ≫ φ) ≫ G.hom = T.hom ≫ f
      rw [Category.assoc, h.1.w, ← Category.assoc, Over.w x])
  let Φ : (T ⟶ G') →* (Over.mk (T.hom ≫ f) ⟶ G) := MonoidHom.mk' F fun x y =>
    Over.OverMorphism.ext (h.2 T x y (F x) (F y) rfl rfl).symm
  refine ⟨fun x x₀ hx => ?_, congrArg (·.left) (map_one Φ).symm⟩
  obtain rfl : x₀ = Φ x := Over.OverMorphism.ext hx
  exact congrArg (·.left) (map_inv Φ x).symm

theorem exists_operation_of_extend {S : Scheme.{0}} {R : ℕ → Scheme.{0}} (s : ∀ e, R e ⟶ S)
    (r : ∀ e, R e ⟶ R (e + 1)) (Y : ∀ e, Over (R e)) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left)
    (hβ : ∀ e, β e ≫ (Y (e + 1)).hom = (Y e).hom ≫ r e)
    (B : Over S) (b : ∀ e, (Y e).left ⟶ B.left) (hb : ∀ e, IsPullback (b e) (Y e).hom B.hom (s e))
    (hβb : ∀ e, β e ≫ b (e + 1) = b e)
    (W : Over S) (Z : ∀ e, Over (R e)) (w : ∀ e, (Z e).left ⟶ W.left)
    (hw : ∀ e, IsPullback (w e) (Z e).hom W.hom (s e)) (ζ : ∀ e, (Z e).left ⟶ (Z (e + 1)).left)
    (hζ : ∀ e, ζ e ≫ (Z (e + 1)).hom = (Z e).hom ≫ r e) (hζw : ∀ e, ζ e ≫ w (e + 1) = w e)
    (ext : ∀ f : ∀ e, (Z e).left ⟶ B.left, (∀ e, f e ≫ B.hom = w e ≫ W.hom) →
      (∀ e, ζ e ≫ f (e + 1) = f e) → ∃ g : W ⟶ B, ∀ e, w e ≫ g.left = f e)
    (J : Type) (p : J → (W ⟶ B)) (op : ∀ e (T : Over (R e)), (J → (T ⟶ Y e)) → (T ⟶ Y e))
    (nat : ∀ e T T' (t : T' ⟶ T) (x : J → (T ⟶ Y e)), t ≫ op e T x = op e T' fun i => t ≫ x i)
    (cmp : ∀ e (T : Over (R e)) (x : J → (T ⟶ Y e)) (x₀ : J → (Over.mk (T.hom ≫ r e) ⟶ Y (e + 1))),
      (∀ i, (x₀ i).left = (x i).left ≫ β e) → (op (e + 1) _ x₀).left = (op e T x).left ≫ β e) :
    ∃ g : W ⟶ B, ∀ e (T : Over (R e)) (x : J → (T ⟶ Y e)) (t : Over.mk (T.hom ≫ s e) ⟶ W),
      (∀ i, (t ≫ p i).left = (x i).left ≫ b e) → (t ≫ g).left = (op e T x).left ≫ b e := by
  have hp : ∀ e i, (w e ≫ (p i).left) ≫ B.hom = (Z e).hom ≫ s e :=
    fun e i => by rw [Category.assoc, Over.w (p i), (hw e).w]
  obtain ⟨X, hX⟩ : ∃ X : ∀ e, J → (Z e ⟶ Y e), ∀ e i, (X e i).left ≫ b e = w e ≫ (p i).left :=
    ⟨fun e i => Over.homMk ((hb e).lift _ _ (hp e i)) ((hb e).lift_snd _ _ _),
      fun e i => (hb e).lift_fst _ _ (hp e i)⟩
  obtain ⟨g, hg⟩ := ext (fun e => (op e _ (X e)).left ≫ b e)
    (fun e => by rw [Category.assoc, (hb e).w, ← Category.assoc, Over.w (op e _ (X e)), (hw e).w])
    (fun e => by
      obtain ⟨tr, h₁⟩ : ∃ tr : Over.mk ((Z e).hom ≫ r e) ⟶ Z (e + 1), tr.left = ζ e :=
        ⟨Over.homMk (ζ e) (hζ e), rfl⟩
      have h₂ := cmp e _ (X e) (fun i => tr ≫ X (e + 1) i) fun i => by
        apply (hb (e + 1)).hom_ext
        · rw [Over.comp_left, Category.assoc, Category.assoc, hX, hβb, hX, ← Category.assoc, h₁]
          exact congrArg (· ≫ (p i).left) (hζw e)
        · rw [Over.w, Category.assoc, hβ, ← Category.assoc, Over.w (X e i)]
          rfl
      rw [← nat, Over.comp_left, h₁] at h₂
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ b (e + 1)) h₂).trans
        ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (hβb e)))))
  refine ⟨g, fun e T x t ht => ?_⟩
  obtain ⟨t', h₁⟩ : ∃ t' : T ⟶ Z e, t'.left ≫ w e = t.left :=
    ⟨Over.homMk ((hw e).lift t.left T.hom (Over.w t)) ((hw e).lift_snd _ _ _),
      (hw e).lift_fst _ _ (Over.w t)⟩
  have h₂ : x = fun i => t' ≫ X e i := funext fun i => Over.OverMorphism.ext <| by
    apply (hb e).hom_ext
    · rw [← ht, Over.comp_left, Over.comp_left, Category.assoc, hX, ← Category.assoc, h₁]
    · rw [Over.w, Over.w]
  rw [h₂, ← nat, Over.comp_left, Over.comp_left, Category.assoc, ← hg e, ← Category.assoc, h₁]

theorem exists_group_operations_of_extend {S : Scheme.{0}} {R : ℕ → Scheme.{0}} (s : ∀ e, R e ⟶ S)
    (r : ∀ e, R e ⟶ R (e + 1)) (Y : ∀ e, Over (R e)) [∀ e, GrpObj (Y e)]
    (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsGrpPullback (Y e) (Y (e + 1)) (r e) (β e))
    (B : Over S) (b : ∀ e, (Y e).left ⟶ B.left) (hb : ∀ e, IsPullback (b e) (Y e).hom B.hom (s e))
    (hβb : ∀ e, β e ≫ b (e + 1) = b e)
    (Z : Over S → ∀ e, Over (R e)) (w : ∀ W e, (Z W e).left ⟶ W.left)
    (hw : ∀ W e, IsPullback (w W e) (Z W e).hom W.hom (s e))
    (ζ : ∀ W e, (Z W e).left ⟶ (Z W (e + 1)).left)
    (hζ : ∀ W e, ζ W e ≫ (Z W (e + 1)).hom = (Z W e).hom ≫ r e)
    (hζw : ∀ W e, ζ W e ≫ w W (e + 1) = w W e) (P : Over S → Prop)
    (ext : ∀ W, P W → ∀ f : ∀ e, (Z W e).left ⟶ B.left, (∀ e, f e ≫ B.hom = w W e ≫ W.hom) →
      (∀ e, ζ W e ≫ f (e + 1) = f e) → ∃ g : W ⟶ B, ∀ e, w W e ≫ g.left = f e)
    (h₂ : P (B ⊗ B)) (h₁ : P B) (h₀ : P (𝟙_ _)) :
    ∃ (mu : B ⊗ B ⟶ B) (io : B ⟶ B) (un : 𝟙_ _ ⟶ B), (∀ e (T : Over (R e)) (x y : T ⟶ Y e) (x₀ y₀ : Over.mk (T.hom ≫ s e) ⟶ B), x₀.left = x.left ≫ b e → y₀.left = y.left ≫ b e → (lift x₀ y₀ ≫ mu).left = (x * y).left ≫ b e ∧ (x₀ ≫ io).left = (x⁻¹).left ≫ b e ∧ (toUnit (Over.mk (T.hom ≫ s e)) ≫ un).left = (1 : T ⟶ Y e).left ≫ b e) := by
  have key := fun W hW => exists_operation_of_extend s r Y β (fun e => (hβ e).1.w) B b hb hβb W (Z W) (w W)
    (hw W) (ζ W) (hζ W) (hζw W) (ext W hW)
  obtain ⟨mu, hmu⟩ := key _ h₂ Bool (fun i => cond i (fst B B) (snd B B))
    (fun _ _ x => x true * x false) (fun _ _ _ t x => comp_mul _ _ _)
    (fun e T x x₀ h => (hβ e).2 T _ _ _ _ (h true) (h false))
  obtain ⟨io, hio⟩ := key _ h₁ Unit (fun _ => 𝟙 B) (fun _ _ x => (x ())⁻¹)
    (fun _ _ _ t x => GrpObj.comp_inv _ _)
    (fun e T x x₀ h => (inv_one_of_isGrpPullback (hβ e) T).1 _ _ (h ()))
  obtain ⟨un, hun⟩ := key _ h₀ Empty Empty.elim (fun _ _ _ => 1) (fun _ _ _ t x => comp_one _)
    (fun e T x x₀ h => (inv_one_of_isGrpPullback (hβ e) T).2)
  refine ⟨mu, io, un, fun e T x y x₀ y₀ hx hy => ⟨?_, ?_, ?_⟩⟩
  · refine hmu e T (fun i => cond i x y) _ fun i => ?_
    cases i
    · exact (congrArg (·.left) (lift_snd x₀ y₀)).trans hy
    · exact (congrArg (·.left) (lift_fst x₀ y₀)).trans hx
  · exact hio e T (fun _ => x) _ fun _ => (congrArg (·.left) (Category.comp_id x₀)).trans hx
  · exact hun e T Empty.elim _ fun i => i.elim

theorem isPullback_fstG {R : Type} [CommRing R] (I : Ideal R) (e : ℕ) (W : Over (Spec (CommRingCat.of R))) :
    IsPullback (P := (thickObj R I e W).left) (fstG I e W).left (thickObj R I e W).hom W.hom (thick R I e) :=
  IsPullback.of_hasPullback W.hom (thick R I e)

theorem thickMap_hom {R : Type} [CommRing R] (I : Ideal R) (e : ℕ) (W : Over (Spec (CommRingCat.of R))) :
    thickMap R I e W ≫ (thickObj R I (e + 1) W).hom = (thickObj R I e W).hom ≫ thickTrans R I e :=
  pullback.lift_snd _ _ _

theorem thickMap_proj {R : Type} [CommRing R] (I : Ideal R) (e : ℕ) (W : Over (Spec (CommRingCat.of R))) :
    thickMap R I e W ≫ (fstG I (e + 1) W).left = (fstG I e W).left :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

end GlobalTheory.GrpAlg

theorem GlobalTheory.GrpAlg.exists_group_operations : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1))))) [∀ e, GrpObj (Y e)] (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsGrpPullback (Y e) (Y (e + 1)) (thickTrans V _ e) (β e)) → ∀ (B : Over (Spec (CommRingCat.of V))) (b : ∀ e, (Y e).left ⟶ B.left), IsProjBy B.hom → Flat B.hom → (∀ e, IsPullback (b e) (Y e).hom B.hom (thick V (IsLocalRing.maximalIdeal V) e)) → (∀ e, β e ≫ b (e + 1) = b e) → ∃ (mu : B ⊗ B ⟶ B) (io : B ⟶ B) (un : 𝟙_ _ ⟶ B), (∀ e (T : Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1))))) (x y : T ⟶ Y e) (x₀ y₀ : Over.mk (T.hom ≫ thick V (IsLocalRing.maximalIdeal V) e) ⟶ B), x₀.left = x.left ≫ b e → y₀.left = y.left ≫ b e → (lift x₀ y₀ ≫ mu).left = (x * y).left ≫ b e ∧ (x₀ ≫ io).left = (x⁻¹).left ≫ b e ∧ (toUnit (Over.mk (T.hom ≫ thick V (IsLocalRing.maximalIdeal V) e)) ≫ un).left = (1 : T ⟶ Y e).left ≫ b e) := by
  intro V _ _ _ _ Y _ β hβ B b hB hfl hb hβb
  have hfl₂ : Flat (B ⊗ B).hom := by
    change Flat (pullback.fst B.hom B.hom ≫ B.hom)
    infer_instance
  exact GlobalTheory.GrpAlg.exists_group_operations_of_extend (S := Spec (CommRingCat.of V))
    (R := fun e => Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1))))
    (thick V (IsLocalRing.maximalIdeal V)) (thickTrans V (IsLocalRing.maximalIdeal V)) Y β hβ B b hb hβb
    (fun W e => thickObj V (IsLocalRing.maximalIdeal V) e W)
    (fun W e => (fstG (IsLocalRing.maximalIdeal V) e W).left)
    (fun W e => GlobalTheory.GrpAlg.isPullback_fstG _ e W) (fun W e => thickMap V (IsLocalRing.maximalIdeal V) e W)
    (fun W e => GlobalTheory.GrpAlg.thickMap_hom _ e W) (fun W e => GlobalTheory.GrpAlg.thickMap_proj _ e W)
    (fun W => IsProjBy W.hom ∧ Flat W.hom) (fun W hW => GlobalTheory.MorAlg.exists_hom_of_thickenings V W B hW.1 hB hW.2)
    ⟨isProjBy_tensor V B B hB hB, hfl₂⟩ ⟨hB, hfl⟩
    ⟨isProjBy_id V, inferInstanceAs (Flat (𝟙 (Spec (CommRingCat.of V))))⟩
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.RankMap

theorem exists_hom_of_rank_one : ∀ (R : Type) [CommRing R] (Z : Scheme.{0}) (f : Z ⟶ Spec (CommRingCat.of R)) (H : LB Z) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ (X : Scheme.{0}) (f' : X ⟶ Spec (CommRingCat.of R)) (N : LB X) (m : ℕ) (w : Fin (n + 1) → Fin (m + 1) → LB.Sec N), N.IsLB → (⨆ i, ⨆ j, nonzeroLocus (w i j) = ⊤) → (∀ i i' j j' k, (w i j).f k * (w i' j').f k = (w i j').f k * (w i' j).f k) → (∀ (t : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous t → (∀ k, MvPolynomial.eval₂Hom (cst f (H.U k)) (fun i => (s i).f k) F = 0) → ∀ j k, MvPolynomial.eval₂Hom (cst f' (N.U k)) (fun i => (w i j).f k) F = 0) → ∃ φ : X ⟶ Z, φ ≫ f = f' ∧ ∀ (T : Scheme.{0}) (r : T ⟶ X) (ψ : T ⟶ Z), ψ ≫ f = r ≫ f' → (∀ z k k' i i' j, ψ z ∈ H.U k → r z ∈ N.U k' → gs ψ z (H.U k) ((s i).f k) * gs r z (N.U k') ((w i' j).f k') = gs ψ z (H.U k) ((s i').f k) * gs r z (N.U k') ((w i j).f k')) → r ≫ φ = ψ := by
  intro R _ Z f H n s hH hs X f' N m w hN hw hr he
  obtain ⟨H', s', hH', hs', hv⟩ := GlobalTheory.RankBundle.exists_rank_one_bundle X N n m w hN hw hr
  obtain ⟨φ, u, hφ, -, cu⟩ := GlobalTheory.exists_hom_of_veryAmpleBy R Z f H n s hH hs X f' H' s' hH' hs'
    fun t F hF h0 c => by
      refine fn_ext fun x hx => ?_
      obtain ⟨j, hj⟩ := hv x c hx
      obtain ⟨k, hk⟩ := exists_chart hN x
      obtain ⟨v, hvi⟩ := hj k hk
      have e := congrArg (gs (𝟙 X) x _) (he t F hF h0 j k)
      rw [MorAlg.gs_eval f' (𝟙 X) x _ hk, gs_eq (𝟙 X) x _ hk 0, map_zero, map_zero] at e
      simp only [hvi] at e
      rw [MorAlg.eval₂_scale _ _ _ hF] at e
      rw [MorAlg.gs_eval f' (𝟙 X) x _ hx, gs_eq (𝟙 X) x _ hx 0, map_zero, map_zero]
      exact ((Units.isUnit _).pow t).mul_right_eq_zero.1 e
  refine ⟨φ, hφ, fun T r ψ hψ hp => ?_⟩
  refine GlobalTheory.ProjUniq.hom_eq_of_proportional R Z f H n s hH hs T _ _
    (by rw [Category.assoc, hφ, hψ]) fun z k k' i i' hk hk' => ?_
  obtain ⟨c, hc⟩ := exists_chart hH' (r z)
  obtain ⟨d, hd⟩ := exists_chart hN (r z)
  obtain ⟨j, hj⟩ := hv (r z) c hc
  obtain ⟨v, hvi⟩ := hj d hd
  have hu : IsUnit ((r.stalkMap z).hom v.val) := v.isUnit.map _
  have e : ∀ l, gs r z (N.U d) ((w l j).f d) =
      (r.stalkMap z).hom v.val * gs r z (H'.U c) ((s' l).f c) := fun l => by
    have e := congrArg (r.stalkMap z).hom (hvi l)
    rwa [map_mul, MorAlg.gs_stalk r (𝟙 X) z _ hd, MorAlg.gs_stalk r (𝟙 X) z _ hc, Category.comp_id] at e
  have q := hp z k' d i i' j hk' hd
  rw [e, e] at q
  rw [MorAlg.Carries.at (w := u) cu r i z k c hk hc, MorAlg.Carries.at (w := u) cu r i' z k c hk hc]
  refine hu.mul_left_cancel ?_
  linear_combination (-(Geo.Tor.gw u r z k c).val) * q

end GlobalTheory.RankMap
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU.PrimeIndex

theorem exists_injective_character (F : Type) [Field F] [IsAlgClosed F] (l : ℕ) (hl : (l : F) ≠ 0) :
    ∃ φ : Multiplicative (ZMod l) →* Fˣ, Function.Injective φ := by
  have : NeZero (l : F) := ⟨hl⟩
  have : NeZero l := NeZero.of_neZero_natCast F
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot F l
  have hu : IsPrimitiveRoot (hζ.isUnit (NeZero.ne l)).unit l := hζ.isUnit_unit (NeZero.ne l)
  exact ⟨(Subgroup.subtype _).comp (AddEquiv.toMultiplicativeLeft hu.zmodEquivZPowers).toMonoidHom,
    Subtype.val_injective.comp (AddEquiv.toMultiplicativeLeft hu.zmodEquivZPowers).injective⟩

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem sval_pow_of_pullG (U : PreU I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F]
    {T : Over (Spec (CommRingCat.of R))} (φ : TF (R := R) F ⟶ T) (k : ℕ) (θ : U.SecGT T 1) (σ : U.SecGT T k)
    (th : LB.Sec (LPow A.A A.L ((1 : ℕ) : ℤ) (TFK (R := R) F))) (t : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F)))
    (h₁ : U.PullG F φ 1 θ th) (hk : U.PullG F φ k σ t)
    (hp : ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ G).left) (z : Z) (J), Good U.P.L.L z J → sval σ r z J = sval θ r z J ^ k)
    (z : (TFK (R := R) F ⊗ A.A).left) (JA) (hA : Good A.L z JA) :
    sval (L := A.L) (φ := fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) (ε := fun _ => (k : ℤ)) t (𝟙 _) z JA =
      sval (L := A.L) (φ := fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) (ε := fun _ => ((1 : ℕ) : ℤ)) th
        (𝟙 _) z JA ^ k := by
  let y₀ : (TFK (R := R) F ⊗ A.A).left ⟶ ((Over.pullback (jK R)).obj G).left :=
    (snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left
  have ih : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, U.gen.inv_hom_id]; rfl
  have ha : y₀ ≫ U.gen.hom.left = (snd (TFK (R := R) F) A.A).left :=
    (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ih).trans (Category.comp_id _))
  have hcomm : ((fst (TFK (R := R) F) A.A).left ≫ φ.left) ≫ T.hom = (y₀ ≫ pullback.fst G.hom (jK R)) ≫ G.hom := by
    have e₁ : φ.left ≫ T.hom = jFK (R := R) F ≫ jK R := Over.w φ
    have e₂ : U.gen.inv.left ≫ pullback.snd G.hom (jK R) = A.A.hom := Over.w U.gen.inv
    have e₃ : (fst (TFK (R := R) F) A.A).left ≫ jFK (R := R) F = (snd (TFK (R := R) F) A.A).left ≫ A.A.hom :=
      (Over.w (fst (TFK (R := R) F) A.A)).trans (Over.w (snd (TFK (R := R) F) A.A)).symm
    refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) e₁).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ jK R) e₃).trans ?_)))
    refine Eq.trans ?_ ((Category.assoc _ _ _).trans (congrArg (y₀ ≫ ·) pullback.condition)).symm
    rw [← e₂]
    simp only [y₀, Category.assoc]
  let h : (TFK (R := R) F ⊗ A.A).left ⟶ (T ⊗ G).left := pullback.lift _ _ hcomm
  have h₃ : h ≫ (fst T G).left = (fst (TFK (R := R) F) A.A).left ≫ φ.left := pullback.lift_fst _ _ _
  have h₂ : h ≫ (snd T G).left = y₀ ≫ pullback.fst G.hom (jK R) := pullback.lift_snd _ _ _
  obtain ⟨JG, hG⟩ := exists_good_pt U.P.L.isLB z
  have e₁ : 𝟙 _ ≫ (snd (TFK (R := R) F) A.A).left = y₀ ≫ U.gen.hom.left := (Category.id_comp _).trans ha.symm
  have e₃ : h ≫ (fst T G).left = 𝟙 _ ≫ (fst (TFK (R := R) F) A.A).left ≫ φ.left := h₃.trans (Category.id_comp _).symm
  have a := h₁ _ (𝟙 _) y₀ h e₁ h₂ e₃ z JA JG hA hG
  have b := (hk _ (𝟙 _) y₀ h e₁ h₂ e₃ z JA JG hA hG).trans ((hp _ h z JG hG).trans (congrArg (· ^ k) a.symm))
  rw [pow_one, mul_pow, ← Units.val_pow_eq_pow_val] at b
  exact (Units.mul_right_inj _).1 b

attribute [local instance] GlobalTheory.TorusExt.gtGroup

theorem hom_zmod_eq_zero_of_support : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ f, U.Theta θ f → ∀ (l : ℕ), l.Prime → ∀ g : D.X →+ ZMod l, (∀ α, (∃ j, (f α).f j ≠ 0) → g α = 0) → g = 0) := by
  intro L₁ L₂ V _ _ _ hV D A G _ _ U θ f hθ l hl g hg
  have := hV.1
  have := hV.2.2
  have : CharZero (FractionRing V) := IsFractionRing.charZero_of_isFractionRing V
  have hl0 : (l : Kbar V) ≠ 0 := Nat.cast_ne_zero.2 hl.ne_zero
  have hl1 : 1 ≤ l := hl.one_le
  obtain ⟨φ, hφ⟩ := exists_injective_character (Kbar V) l hl0
  let χ₀ : Multiplicative D.X →* (Kbar V)ˣ := φ.comp (AddMonoidHom.toMultiplicative g)
  have hχ : ∀ α, χ₀ (Multiplicative.ofAdd α) = φ (Multiplicative.ofAdd (g α)) := fun _ => rfl
  have hχl : χ₀ ^ l = 1 := MonoidHom.ext fun α => by
    show χ₀ (Multiplicative.ofAdd α.toAdd) ^ l = 1
    rw [hχ, ← map_pow, ← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, ofAdd_zero, map_one]
  suffices H : χ₀ = 1 by
    refine AddMonoidHom.ext fun α => ?_
    have e : φ (Multiplicative.ofAdd (g α)) = φ 1 := by rw [← hχ, H, map_one]; rfl
    exact congrArg Multiplicative.toAdd (hφ e)
  obtain ⟨p, pb, pv, pt, pz⟩ := exists_gtPt_of_character V D (Kbar V) χ₀
  obtain ⟨o, -, -, ot, oz⟩ := exists_gtPt_of_character V D (Kbar V) 1
  obtain ⟨m, minj, macts, madd⟩ := GlobalTheory.T.torusTorsion_to_abelianTorsion_theta_action L₁ L₂ V hV D A G U l hl1
  let P : {g : GtPtF D (Kbar V) // GtTors D l g} := ⟨p, pt l hχl⟩
  let O : {g : GtPtF D (Kbar V) // GtTors D l g} := ⟨o, ot l (one_pow l)⟩
  have ho : o = 0 := (TorusExt.isZero_iff_eq o).1 (oz.2 rfl)
  have mO : m O = 1 := by
    have := madd O O O ((TorusExt.isAdd_iff_eq o o o).2 (by rw [ho, add_zero]))
    exact left_eq_mul.1 this
  suffices H : m P = 1 by
    have e : p = o := congrArg Subtype.val (minj (H.trans mO.symm))
    exact pz.1 (e ▸ oz.2 rfl)
  obtain ⟨σ, fl, hσ, hfl, hpow⟩ := GlobalTheory.T.thetaPowers_expansion_support_subgroup L₁ L₂ V hV D A G U g.ker θ f hθ.1 (fun α hα j => by
    by_contra hj
    exact hα (hg α ⟨j, hj⟩)) l hl1
  obtain ⟨th, hth, -⟩ := PullSec.existsUnique_pullG U (Kbar V) (toUnit _) 1 θ
  obtain ⟨s₀, hs₀, -⟩ := PullSec.existsUnique_pullB D (Kbar V) (toUnit _) 1 f
  obtain ⟨t, ht, -⟩ := PullSec.existsUnique_pullG U (Kbar V) (toUnit _) l σ
  obtain ⟨s, hs, -⟩ := PullSec.existsUnique_pullB D (Kbar V) (toUnit _) l fl
  obtain ⟨⟨j₀, hj₀⟩, -, -⟩ := GlobalTheory.T.expF_of_theta_degree_one L₁ L₂ V hV D A G U θ f hθ th s₀ hth hs₀
  have hts := GlobalTheory.expF_of_pull V D _ A G U (Kbar V) l σ fl t s hσ ht hs
  obtain ⟨ex, ex₁, ex₂, ex₃, -⟩ := GlobalTheory.UU.ExpLinMap.exists_expansion_linear L₁ L₂ V hV D A G U (Kbar V) l hl1
  obtain ⟨hpl, hacts⟩ := macts P
  obtain ⟨ϑ, hϑ⟩ := (GlobalTheory.ThetaIrred.main L₁ L₂ _ A (Kbar V) (jFK (R := V) (Kbar V)) l hl0).1 (m P) hpl
  obtain ⟨w, hw, hΦ⟩ := hacts ϑ hϑ
  obtain ⟨t', ht'⟩ := ThetaScalar.exists_actVal A.isLB ϑ t
  have hact := ht'.isActOf A.isLB
  obtain ⟨c, hc⟩ := GlobalTheory.UU.phiRaw_torus V D (Kbar V) l p w pb hw
  have hs' := hc s _ (hΦ t t' s _ hts (ex₁ (SecMod.mk _ t')) hact) (fun α hα z J hJ => by
    obtain ⟨j, hj⟩ := (GlobalTheory.pullB_ne_zero_iff V D (Kbar V) l fl s hs α).1 hα
    have hm : g α = 0 := by
      by_contra h0
      exact hj (hfl α h0 j)
    refine Units.ext ((pv α z J hJ).trans ?_)
    have e₁ : scal (𝟙 (Spec (CommRingCat.of (Kbar V)))) ((1 : (Kbar V)ˣ) : Kbar V) = 1 := by simp [scal]
    rw [hχ, hm, ofAdd_zero, map_one, e₁]
    exact (gs_eq _ z ⊤ trivial _).trans ((congrArg _ (map_one _)).trans (map_one _)))
  have e : SecMod.mk _ t' = c.val • (SecMod.mk _ t : EA A (jFK (R := V) (Kbar V)) l) := by
    refine sub_eq_zero.1 (ex₃ _ fun α => ?_)
    rw [map_sub, map_smul, sub_eq_zero]
    refine DVR.SecOps.sec_ext fun j => (hs' α j).trans ?_
    rw [ex₂ t s hts α]
    rfl
  refine hϑ.symm.trans (GlobalTheory.T.thetaOperator_point_zero_of_power_eigen _ A (Kbar V) (jFK (R := V) (Kbar V)) l hl1 (SecMod.mk _ th) (SecMod.mk _ t) ϑ c
    (fun h0 => hj₀ ((SecMod.eq_zero_iff_coord _).1 h0 j₀))
    (fun z J hJ => sval_pow_of_pullG U (Kbar V) (toUnit _) l θ σ th t hth ht hpow z J hJ) ?_)
  rw [← e]
  exact hact

end GlobalTheory.UU.PrimeIndex
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
theorem _root_.GlobalTheory.T.exists_psi_thetaExpansionPsiRelation : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (f : ∀ α, SecBT D (𝟙_ _) 1 α), (∀ α, ∃ j, (f α).f j ≠ 0) → ∃ ψ h, PsiRel (setPsi D ψ h) (𝟙_ _) f := by
  first | exact @GlobalTheory.exists_psi_psiRel | exact GlobalTheory.exists_psi_psiRel | (intros; apply GlobalTheory.exists_psi_psiRel <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

theorem _root_.GlobalTheory.T.heckeOperator_multiplicative_on_section_products : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ (k : ℕ), 1 ≤ k → ∀ (p : QkPt D.toPre F k) (w : Frm D.toPre F k p.g.b), w.IsGen → ∀ (n : Fin 3 → ℕ) (N : Fin 3 → ℕ), (∀ i, 1 ≤ n i ∧ N i = k * n i) → n 2 = n 0 + n 1 → ∀ (q : ∀ i, QkPt D.toPre F (N i)) (ω : ∀ i, Frm D.toPre F (N i) (q i).g.b), (∀ i, (q i).y = n i • p.y ∧ (q i).g = p.g ∧ ((ω i).IsGen ∧ ∀ z J, Good D.toPre.P.L z J → val (ω i) (𝟙 _) z J = val w (𝟙 _) z J ^ n i)) → ∀ (t t' : ∀ i, SecA A F (N i)) (s s' : ∀ i, Fam D.toPre F (N i)), (∀ i, U.ExpandsF F (N i) w₀ (t i) (s i) ∧ U.ExpandsF F (N i) w₀ (t' i) (s' i) ∧ PhiRel D.toPre F (N i) (q i) (ω i) (s i) (s' i)) → (∀ z J, Good A.L z J → sA (t 2) (𝟙 _) z J = sA (t 0) (𝟙 _) z J * sA (t 1) (𝟙 _) z J) → ∀ z J, Good A.L z J → sA (t' 2) (𝟙 _) z J = sA (t' 0) (𝟙 _) z J * sA (t' 1) (𝟙 _) z J := by
  first | exact @GlobalTheory.UT.PhiMul.phi_mul | exact GlobalTheory.UT.PhiMul.phi_mul | (intros; apply GlobalTheory.UT.PhiMul.phi_mul <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.exists_integral_families_span_generate_valuationRings : PolBaseChangeSt → GlobalFnsSt → DVR.TwistBaseChangeStatement → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R), AdmBase R I → ∀ (φ : R →+* R') (D : DegData R I) (D' : DegPre R') (hD : IsPullDeg φ D.toPre D') (k : ℕ), 1 ≤ k → ∃ (n : ℕ) (F₀ : Fin n → Fam D.toPre (FractionRing R) k) (f : Fin n → ∀ α, D.toPre.SecB k α) (F₁ : Fin n → Fam D' (FractionRing R') k) (f' : Fin n → ∀ α, D'.SecB k α), (∀ i, (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k) ((F₀ i).s α) (D.toPre.famφB α) (DegPre.famε k) (f i α) (DegPre.prB D.toPre (FractionRing R)).left 1) ∧ (∀ α, GeneratorPullback.SecScal D'.P.L (DegPre.famφ D' (FractionRing R') α) (DegPre.famε k) ((F₁ i).s α) (D'.famφB α) (DegPre.famε k) (f' i α) (DegPre.prB D' (FractionRing R')).left 1) ∧ (∀ x : D'.X, (∀ (Z : Scheme.{0}) (r : Z ⟶ D'.P.A.left) (z : Z) (p : Fin 4 → D.toPre.P.L.ι) (q : Fin 4 → D'.P.L.ι), (∀ κ, ((hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ))) ((D'.famφB x) κ (r z)) ∈ D.toPre.P.L.U (p κ)) → (∀ κ, (D'.famφB x) κ (r z) ∈ D'.P.L.U (q κ)) → Geo.Tor.gs (r ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ))) z (LB.wchart D.toPre.P.L (D.toPre.famφB (hD.xe x)) p) ((f i (hD.xe x)).f p) = (∏ κ, Geo.Tor.gw hD.w (r ≫ (D'.famφB x) κ) z (p κ) (q κ) ^ (DegPre.famε k) κ).val * Geo.Tor.gs r z (LB.wchart D'.P.L (D'.famφB x) q) ((f' i x).f q)))) ∧ Submodule.span (FractionRing R') (Set.range F₁) = ⊤ ∧ (∀ (S : Type) [CommRing S] [IsDomain S] [ValuationRing S] (σ : R →+* S) (F : Type) [Field F] [Algebra (FractionRing R) F] (ιF : S →+* F), Function.Injective ιF → ∀ (ρ : TF (R := R) F ⟶ (Over.mk (specOf σ))), ρ.left = specOf ιF → ∀ (F' : Type) [Field F'] [Algebra (FractionRing R') F'] (π : S →+* F'), IsLocalHom π → (∀ r : R, π (σ r) = algebraMap (FractionRing R') F' (algebraMap R' (FractionRing R') (φ r))) → ∀ s : Fam D.toPre F k, (∃ g : ∀ α, LB.Sec (LB.LinComb D.toPre.P.L (fun i => (snd (Over.mk (specOf σ)) D.toPre.P.A).left ≫ D.toPre.famφB α i) (DegPre.famε k)), (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) (s.s α) (fun i => (snd (Over.mk (specOf σ)) D.toPre.P.A).left ≫ D.toPre.famφB α i) (DegPre.famε k) (g α) (ρ ▷ D.toPre.P.A).left 1)) → ∃ c : Fin n → S, ∀ α, GeneratorPullback.SecLin D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) (s.s α) (D.toPre.famφB α) (DegPre.famε k) (fun i => f i α) (DegPre.prB D.toPre F).left (fun i => scal (fst (TF (R := R) F) D.toPre.P.A).left (ιF (c i)))) := by
  first | exact @GlobalTheory.FamGen.exists_span_generate | exact GlobalTheory.FamGen.exists_span_generate | (intros; apply GlobalTheory.FamGen.exists_span_generate <;> assumption)
end

section

open ReciprocityTheory.ChartRestriction.G

namespace GlobalTheory

theorem homExtDvr_and_laws : Out.HomExtDvrSt ∧ Out.Laws7 := by
  have h : Out.HomExtDvrSt := fun T _ _ _ G G' _ _ hG hG' φ hφ =>
    GlobalTheory.existsUnique_hom_extension_semiAbelian T (FractionRing T) G G' hG hG' φ hφ
  exact ⟨h, ⟨h⟩⟩

end GlobalTheory
end
