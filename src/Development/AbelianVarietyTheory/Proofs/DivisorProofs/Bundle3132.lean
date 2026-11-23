module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle440
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle535
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrderTwoPointTorusExtensionTranslate
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3067
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EndoLbIsoSymmetryHypothesisExtendNormalModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle547
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle644
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.PowPolarizationIsoPullbackOfDescent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle788
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle821
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedThetaValueEqRootMulThetaOperatorValue
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

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

noncomputable section

namespace GlobalTheory.MumProd

private theorem torusHomOf_iff_appTop₂ {S : Scheme.{0}} {X X' : Type} [AddCommGroup X] [AddCommGroup X']
    (h : X' → X) (t : splitTorus S X ⟶ splitTorus S X') : TorusHomOf h t ↔
      ∀ χ, t.left.appTop.hom (charUnit S X' χ).val = (charUnit S X (h χ)).val := by
  refine forall_congr' fun χ => ?_
  have : (res (fun x _ => show t.left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial)
      (pullU t.left ⊤ (charUnit S X' χ)) : Γ((splitTorus S X).left, ⊤)ˣ).val =
      t.left.appTop.hom (charUnit S X' χ).val := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [← this, Units.ext_iff]

private theorem torus_eq₂ {S : Scheme.{0}} {X X' : Type} [AddCommGroup X] [AddCommGroup X']
    (h : X' → X) {s s' : splitTorus S X ⟶ splitTorus S X'} (hs : TorusHomOf h s) (hs' : TorusHomOf h s') :
    s = s' := by
  apply (GlobalTheory.splitTorusPointsEquiv S X' (splitTorus S X)).injective
  refine MonoidHom.ext fun χ => Units.ext ?_
  rw [show χ = Multiplicative.ofAdd χ.toAdd from rfl, GlobalTheory.splitTorusPointsEquiv_val,
    GlobalTheory.splitTorusPointsEquiv_val, (torusHomOf_iff_appTop₂ h s).1 hs, (torusHomOf_iff_appTop₂ h s').1 hs']

private theorem torus_eq_one₂ {S : Scheme.{0}} {X X' : Type} [AddCommGroup X] [AddCommGroup X']
    {s : splitTorus S X ⟶ splitTorus S X'} (hs : TorusHomOf (fun _ => (0 : X)) s) :
    s = toUnit _ ≫ η[splitTorus S X'] := by
  have h0 : (charUnit S X 0).val = 1 := by
    have k := GlobalTheory.splitTorusPointsEquiv_val S X (splitTorus S X) (𝟙 _) 0
    rw [ofAdd_zero, map_one, Units.val_one] at k
    rw [k]
    simp
  have : s = 1 := by
    apply (GlobalTheory.splitTorusPointsEquiv S X' (splitTorus S X)).injective
    rw [map_one]
    refine MonoidHom.ext fun χ => Units.ext ?_
    rw [show χ = Multiplicative.ofAdd χ.toAdd from rfl, GlobalTheory.splitTorusPointsEquiv_val,
      (torusHomOf_iff_appTop₂ _ s).1 hs, h0]
    rfl
  rw [this, Hom.one_def]

private theorem pullback_prod_ext₂ {S₀ C : Scheme.{0}} (f : C ⟶ S₀) {X Y : Over S₀} {Z : Over C}
    {a b : Z ⟶ (Over.pullback f).obj (X ⊗ Y)}
    (h₁ : a ≫ (Over.pullback f).map (fst X Y) = b ≫ (Over.pullback f).map (fst X Y))
    (h₂ : a ≫ (Over.pullback f).map (snd X Y) = b ≫ (Over.pullback f).map (snd X Y)) : a = b :=
  (isLimitOfPreserves (Over.pullback f) (tensorProductIsBinaryProduct X Y)).hom_ext (by
    rintro ⟨⟨⟩⟩
    · exact h₁
    · exact h₂)

private theorem map_eta₂ {S₀ C : Scheme.{0}} (f : C ⟶ S₀) (G : Over S₀) [MonObj G] :
    (Over.pullback f).map η[G] = toUnit _ ≫ η[(Over.pullback f).obj G] := by
  rw [Functor.obj.η_def, ← Category.assoc]
  have : toUnit ((Over.pullback f).obj (𝟙_ _)) ≫ Functor.LaxMonoidal.ε (Over.pullback f) = 𝟙 _ :=
    (IsTerminal.isTerminalObj (Over.pullback f) _ isTerminalTensorUnit).hom_ext _ _
  rw [this, Category.id_comp]

end GlobalTheory.MumProd

namespace GlobalTheory.MumProd

theorem linHom_lift_one_id : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D₁ : DegData R I) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : UnifPre I D₁ A₁ G₁) (D₂ : DegData R I) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : UnifPre I D₂ A₂ G₂) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (U : UnifPre I D A (G₁ ⊗ G₂)) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X) (a₁ : A.A ⟶ A₁.A) (a₂ : A.A ⟶ A₂.A), IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂ → IsProdUnif U₁ U₂ U p₁ p₂ q₁ q₂ a₁ a₂ → ∀ (i₂ : D₂.toPre.P.A ⟶ D.toPre.P.A), i₂ ≫ p₁ = toUnit _ ≫ η[D₁.toPre.P.A] → i₂ ≫ p₂ = 𝟙 _ → LinHom U₂ U i₂ q₂ (lift 1 (𝟙 G₂)) := by
  intro R _ _ I D₁ A₁ G₁ _ _ U₁ D₂ A₂ G₂ _ _ U₂ D A U p₁ p₂ q₁ q₂ a₁ a₂ hS hU i₂ hi₁ hi₂
  have := hS.lim
  let xe : D.toPre.X ≃+ D₁.toPre.X × D₂.toPre.X := AddEquiv.ofBijective (q₁.prod q₂) hS.xsum
  have hxe : ∀ x, xe x = (q₁ x, q₂ x) := fun x => rfl
  let j₁ : D₁.toPre.X → D.toPre.X := fun y => xe.symm (y, 0)
  let j₂ : D₂.toPre.X → D.toPre.X := fun y => xe.symm (0, y)
  have hj₁ : ∀ y, q₁ (j₁ y) = y ∧ q₂ (j₁ y) = 0 := fun y => by
    have k := hxe (j₁ y); simp only [j₁, AddEquiv.apply_symm_apply] at k
    exact ⟨(congrArg Prod.fst k).symm, (congrArg Prod.snd k).symm⟩
  have hj₂ : ∀ y, q₁ (j₂ y) = 0 ∧ q₂ (j₂ y) = y := fun y => by
    have k := hxe (j₂ y); simp only [j₂, AddEquiv.apply_symm_apply] at k
    exact ⟨(congrArg Prod.fst k).symm, (congrArg Prod.snd k).symm⟩
  have hone : IsMonHom (1 : G₂ ⟶ G₁) := by rw [Hom.one_def]; infer_instance
  refine ⟨inferInstance, fun e => ?_, fun e => ?_⟩
  ·
    have hq₁ := (U₁.gt e).q_hom
    have hq₂ := (U₂.gt e).q_hom
    have hiso : IsIso ((Over.pullback (thick R I e)).map (lift p₁ p₂)) := inferInstance
    rw [← cancel_mono ((Over.pullback (thick R I e)).map (lift p₁ p₂))]
    apply pullback_prod_ext₂
    · simp only [Category.assoc, ← Functor.map_comp, lift_fst]
      rw [hU.q_pr₁ e, ← Category.assoc, ← Functor.map_comp, lift_fst, hi₁, Hom.one_def]
      simp only [Functor.map_comp, map_eta₂, Category.assoc, IsMonHom.one_hom, comp_toUnit_assoc]
    · simp only [Category.assoc, ← Functor.map_comp, lift_snd]
      rw [hU.q_pr₂ e, ← Category.assoc, ← Functor.map_comp, lift_snd, hi₂]
      simp
  ·
    refine ⟨GlobalTheory.SplitTorusPow.torusMap _ q₂, (torusHomOf_iff_appTop₂ _ _).2 fun χ =>
      GlobalTheory.SplitTorusPow.torusMap_char q₂ χ, ?_⟩
    have hT : TorusHomOf q₂ (GlobalTheory.SplitTorusPow.torusMap (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) q₂) :=
      (torusHomOf_iff_appTop₂ _ _).2 fun χ => GlobalTheory.SplitTorusPow.torusMap_char q₂ χ
    obtain ⟨t₁, ht₁, e₁⟩ := hU.i_pr₁ e j₁ (fun y => (hj₁ y).1) (fun y => (hj₁ y).2)
    obtain ⟨t₂, ht₂, e₂⟩ := hU.i_pr₂ e j₂ (fun y => (hj₂ y).1) (fun y => (hj₂ y).2)
    have c₁ : GlobalTheory.SplitTorusPow.torusMap _ q₂ ≫ t₁ = toUnit _ ≫ η[splitTorus _ D₁.toPre.X] := by
      refine torus_eq_one₂ ?_
      have k := TorusHomOf.comp hT ht₁
      simp only [(hj₁ _).2] at k
      exact k
    have c₂ : GlobalTheory.SplitTorusPow.torusMap _ q₂ ≫ t₂ = 𝟙 _ := by
      refine torus_eq₂ (fun χ => χ) ?_ (TorusHomOf.id _)
      have k := TorusHomOf.comp hT ht₂
      simp only [(hj₂ _).2] at k
      exact k
    have hi₁' := (U₁.gt e).i_hom
    apply pullback_prod_ext₂
    · simp only [Category.assoc]
      rw [e₁, ← Category.assoc _ t₁, c₁, ← Functor.map_comp, lift_fst, Hom.one_def]
      simp only [Functor.map_comp, map_eta₂, Category.assoc, IsMonHom.one_hom, comp_toUnit_assoc]
    · simp only [Category.assoc]
      rw [e₂, ← Category.assoc _ t₂, c₂, ← Functor.map_comp, lift_snd]
      simp

end GlobalTheory.MumProd
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

noncomputable section

namespace GlobalTheory.MumProd.GAdjFst

open GlobalTheory.CechPic

variable {S : Scheme.{0}}

theorem psum_comp_hom {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] [IsCommMonObj H] (f : G ⟶ H) [IsMonHom f]
    {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ G)) (I : Finset (Fin n)) :
    psum G x I ≫ f = psum H (fun i => x i ≫ f) I :=
  psum_hom (MonoidHom.mk' (fun z : T ⟶ G => z ≫ f) fun a b => MonObj.mul_comp a b f) x I

theorem cubeCls_pull_hom {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] [IsCommMonObj H] (f : G ⟶ H)
    [IsMonHom f] {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ G)) (c : Pic H.left) :
    GlobalTheory.ZH.EndoExtend.cubeCls G x (pull f.left c) = GlobalTheory.ZH.EndoExtend.cubeCls H (fun i => x i ≫ f) c := by
  unfold GlobalTheory.ZH.EndoExtend.cubeCls
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [← pull_comp, ← Over.comp_left, psum_comp_hom]

theorem cubeCls_add {G : Over S} [GrpObj G] [IsCommMonObj G] {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ G))
    (a b : Pic G.left) :
    GlobalTheory.ZH.EndoExtend.cubeCls G x (a + b) = GlobalTheory.ZH.EndoExtend.cubeCls G x a + GlobalTheory.ZH.EndoExtend.cubeCls G x b := by
  unfold GlobalTheory.ZH.EndoExtend.cubeCls
  simp only [map_add (f := _), smul_add, Finset.sum_add_distrib]

theorem cubeCls_one_left {G : Over S} [GrpObj G] [IsCommMonObj G] {T : Over S} (y : T ⟶ G) (c : Pic G.left) :
    GlobalTheory.ZH.EndoExtend.cubeCls G ![1, y] c = 0 := by
  classical
  unfold GlobalTheory.ZH.EndoExtend.cubeCls
  refine (Fintype.sum_equiv (Equiv.ulift : ULift.{0} (Finset (Fin 2)) ≃ Finset (Fin 2)) _
    (fun I => ((-1 : ℤ) ^ (2 - I.card)) • pull (psum G ![1, y] I).left c) (fun _ => rfl)).trans ?_
  have u : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide
  have p₀ : psum G ![1, y] ∅ = 1 := rfl
  have p₁ : psum G ![1, y] {0} = 1 := _root_.mul_one 1
  have p₂ : psum G ![1, y] {1} = y := _root_.mul_one y
  have p₄ : psum G ![1, y] {0, 1} = 1 * y := congrArg (1 * ·) (_root_.mul_one y)
  rw [u, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, p₀, p₁, p₂, p₄, _root_.one_mul]
  have c₁ : ({0, 1} : Finset (Fin 2)).card = 2 := by decide
  simp only [c₁, Finset.card_singleton, Finset.card_empty]
  norm_num

end GlobalTheory.MumProd.GAdjFst

theorem GlobalTheory.MumProd.gAdj_prod_fst : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D₁ : DegData R I) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : UnifPre I D₁ A₁ G₁) (D₂ : DegData R I) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : UnifPre I D₂ A₂ G₂) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (U : UnifPre I D A (G₁ ⊗ G₂)) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X) (a₁ : A.A ⟶ A₁.A) (a₂ : A.A ⟶ A₂.A), IsProdUnif U₁ U₂ U p₁ p₂ q₁ q₂ a₁ a₂ → GAdj U₁.LG.L U.LG.L (lift (𝟙 G₁) 1) (fst G₁ G₂) := by
  intro R _ _ I D₁ A₁ G₁ _ _ U₁ D₂ A₂ G₂ _ _ U₂ D A U p₁ p₂ q₁ q₂ a₁ a₂ hU
  obtain ⟨w, hw⟩ := hU.wL
  have hL := U.LG.isLB
  have hL₁ := U₁.LG.isLB
  have hL₂ := U₂.LG.isLB
  have hE : (extLB U₁.LG.L U₂.LG.L (fst G₁ G₂).left (snd G₁ G₂).left).IsLB :=
    GlobalTheory.CechPic.isLB_tens (pull_isLB hL₁ _) (pull_isLB hL₂ _)
  have e0 : GlobalTheory.CechPic.cls _ hL = GlobalTheory.CechPic.pull (fst G₁ G₂).left (GlobalTheory.CechPic.cls _ hL₁) +
      GlobalTheory.CechPic.pull (snd G₁ G₂).left (GlobalTheory.CechPic.cls _ hL₂) :=
    (GlobalTheory.CechPic.cls_eq_iff hL hE).2 ⟨w, hw⟩
  unfold GAdj
  refine (GlobalTheory.CechPic.cls_eq_iff _ _).1 ((GlobalTheory.ZH.EndoExtend.cls_cubeLB (G₁ ⊗ G₂) _ hL).trans
    (Eq.trans ?_ (GlobalTheory.ZH.EndoExtend.cls_cubeLB G₁ _ hL₁).symm))
  rw [e0,
    GlobalTheory.MumProd.GAdjFst.cubeCls_add, GlobalTheory.MumProd.GAdjFst.cubeCls_pull_hom,
    GlobalTheory.MumProd.GAdjFst.cubeCls_pull_hom]
  have h₁ : (fun i => (![fst G₁ (G₁ ⊗ G₂) ≫ lift (𝟙 G₁) 1, snd G₁ (G₁ ⊗ G₂)] : Fin 2 → _) i ≫ fst G₁ G₂) =
      ![fst G₁ (G₁ ⊗ G₂), snd G₁ (G₁ ⊗ G₂) ≫ fst G₁ G₂] := by
    funext i; fin_cases i <;> simp
  have h₂ : (fun i => (![fst G₁ (G₁ ⊗ G₂) ≫ lift (𝟙 G₁) 1, snd G₁ (G₁ ⊗ G₂)] : Fin 2 → _) i ≫ snd G₁ G₂) =
      ![1, snd G₁ (G₁ ⊗ G₂) ≫ snd G₁ G₂] := by
    funext i; fin_cases i <;> simp
  rw [h₁, h₂, GlobalTheory.MumProd.GAdjFst.cubeCls_one_left, add_zero]
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

namespace GlobalTheory.MumProd.CubeIso

section

variable {X X₁ X₂ Y : Scheme.{0}} {L : LB X} {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : X ⟶ X₁} {f₂ : X ⟶ X₂}

theorem mem_ext {x : X} {j₁ : L₁.ι} {j₂ : L₂.ι} (h₁ : f₁ x ∈ L₁.U j₁) (h₂ : f₂ x ∈ L₂.U j₂) :
    x ∈ (extLB L₁ L₂ f₁ f₂).U (extIdx (f₁ := f₁) (f₂ := f₂) j₁ j₂) :=
  ⟨mem_pull.2 h₁, mem_pull.2 h₂⟩

theorem gm_ext_g {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (j₁ j₁' : L₁.ι) (j₂ j₂' : L₂.ι)
    (h₁ : f₁ (r z) ∈ L₁.U j₁) (h₁' : f₁ (r z) ∈ L₁.U j₁') (h₂ : f₂ (r z) ∈ L₂.U j₂) (h₂' : f₂ (r z) ∈ L₂.U j₂') :
    gm r z ((extLB L₁ L₂ f₁ f₂).U (extIdx (f₁ := f₁) (f₂ := f₂) j₁ j₂) ⊓
        (extLB L₁ L₂ f₁ f₂).U (extIdx (f₁ := f₁) (f₂ := f₂) j₁' j₂'))
      ((extLB L₁ L₂ f₁ f₂).g (extIdx (f₁ := f₁) (f₂ := f₂) j₁ j₂) (extIdx (f₁ := f₁) (f₂ := f₂) j₁' j₂')) =
      gm (r ≫ f₁) z (L₁.U j₁ ⊓ L₁.U j₁') (L₁.g j₁ j₁') * gm (r ≫ f₂) z (L₂.U j₂ ⊓ L₂.U j₂') (L₂.g j₂ j₂') := by
  have hm : r z ∈ (extLB L₁ L₂ f₁ f₂).U (extIdx (f₁ := f₁) (f₂ := f₂) j₁ j₂) ⊓
      (extLB L₁ L₂ f₁ f₂).U (extIdx (f₁ := f₁) (f₂ := f₂) j₁' j₂') := ⟨mem_ext h₁ h₂, mem_ext h₁' h₂'⟩
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res r z _ hm _).trans ?_) ((gm_res r z _ hm _).trans ?_))
  · exact gm_pull_g L₁ f₁ r z (fun _ => j₁) (fun _ => j₁') (mem_pull.2 h₁) (mem_pull.2 h₁')
  · exact gm_pull_g L₂ f₂ r z (fun _ => j₂) (fun _ => j₂') (mem_pull.2 h₂) (mem_pull.2 h₂')

def ev (w : LB.Iso L (extLB L₁ L₂ f₁ f₂)) {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (j₁ : L₁.ι) (j₂ : L₂.ι) (k : L.ι) :
    (Z.presheaf.stalk z)ˣ :=
  gm r z ((extLB L₁ L₂ f₁ f₂).U (extIdx (f₁ := f₁) (f₂ := f₂) j₁ j₂) ⊓ L.U k)
    (w.s (extIdx (f₁ := f₁) (f₂ := f₂) j₁ j₂, k))

theorem ev_trans {w : LB.Iso L (extLB L₁ L₂ f₁ f₂)} (hw : w.IsGen) {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z)
    (j₁ j₁' : L₁.ι) (j₂ j₂' : L₂.ι) (k k' : L.ι)
    (h₁ : f₁ (r z) ∈ L₁.U j₁) (h₁' : f₁ (r z) ∈ L₁.U j₁') (h₂ : f₂ (r z) ∈ L₂.U j₂) (h₂' : f₂ (r z) ∈ L₂.U j₂')
    (h : r z ∈ L.U k) (h' : r z ∈ L.U k') :
    ev w r z j₁ j₂ k = gm (r ≫ f₁) z (L₁.U j₁ ⊓ L₁.U j₁') (L₁.g j₁ j₁') *
      gm (r ≫ f₂) z (L₂.U j₂ ⊓ L₂.U j₂') (L₂.g j₂ j₂') * (gm r z (L.U k ⊓ L.U k') (L.g k k'))⁻¹ *
        ev w r z j₁' j₂' k' := by
  rw [← gm_ext_g r z j₁ j₁' j₂ j₂' h₁ h₁' h₂ h₂']
  exact AdjComp.gm_iso hw r z (extIdx (f₁ := f₁) (f₂ := f₂) j₁ j₂, k) (extIdx (f₁ := f₁) (f₂ := f₂) j₁' j₂', k')
    ⟨mem_ext h₁ h₂, h⟩ ⟨mem_ext h₁' h₂', h'⟩

theorem exists_linComb (hL : L.IsLB) (hL₁ : L₁.IsLB) (hL₂ : L₂.IsLB) (w₀ : LB.Iso L (extLB L₁ L₂ f₁ f₂))
    (hw₀ : w₀.IsGen) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (φ₁ : K → (Y ⟶ X₁)) (ε : K → ℤ) (σ : K → K)
    (h₁ : ∀ k, φ k ≫ f₁ = φ₁ k) (h₂ : ∀ k, φ k ≫ f₂ = φ (σ k) ≫ f₂)
    (hε : ∀ (G : Type) [CommGroup G] (a : K → G), (∀ k, a k = a (σ k)) → ∏ k, a k ^ ε k = 1) :
    ∃ w : LB.Iso (LB.LinComb L φ ε) (LB.LinComb L₁ φ₁ ε), w.IsGen ∧
      ∀ (Z : Scheme.{0}) (f : Z ⟶ Y) (z : Z) (jC : K → L₁.ι) (jA : K → L.ι) (β : K → L₂.ι),
        f z ∈ LB.wchart L₁ φ₁ jC → f z ∈ LB.wchart L φ jA → (∀ k, f₂ (φ k (f z)) ∈ L₂.U (β k)) →
        (∀ k, β k = β (σ k)) →
        gm f z (LB.wchart L₁ φ₁ jC ⊓ LB.wchart L φ jA) (w.s (jC, jA)) =
          ∏ k, ev w₀ (f ≫ φ k) z (jC k) (β k) (jA k) ^ ε k := by
  obtain rfl : (fun k => φ k ≫ f₁) = φ₁ := funext h₁
  have cover : ∀ y : Y, ∃ β : K → L₂.ι, (∀ k, f₂ (φ k y) ∈ L₂.U (β k)) ∧ ∀ k, β k = β (σ k) := fun y => by
    choose c hc using exists_chart hL₂
    exact ⟨fun k => c ((φ k ≫ f₂) y), fun k => hc _, fun k => congrArg (fun q : Y ⟶ X₂ => c (q y)) (h₂ k)⟩
  have glue : ∀ (jC : K → L₁.ι) (jA : K → L.ι),
      ∃ s : Γ(Y, LB.wchart L₁ (fun k => φ k ≫ f₁) jC ⊓ LB.wchart L φ jA)ˣ,
      ∀ (Z : Scheme.{0}) (f : Z ⟶ Y) (z : Z) (β : K → L₂.ι),
        f z ∈ LB.wchart L₁ (fun k => φ k ≫ f₁) jC → f z ∈ LB.wchart L φ jA → (∀ k, f₂ (φ k (f z)) ∈ L₂.U (β k)) →
        (∀ k, β k = β (σ k)) → gm f z _ s = ∏ k, ev w₀ (f ≫ φ k) z (jC k) (β k) (jA k) ^ ε k := by
    intro jC jA
    let W : {β : K → L₂.ι // ∀ k, β k = β (σ k)} → Y.Opens := fun β =>
      LB.wchart L₁ (fun k => φ k ≫ f₁) jC ⊓ LB.wchart L φ jA ⊓ LB.wchart L₂ (fun k => φ k ≫ f₂) β.1
    have l₀ : ∀ β, W β ≤ LB.wchart L₁ (fun k => φ k ≫ f₁) jC ⊓ LB.wchart L φ jA := fun β => inf_le_left
    have l₁ : ∀ β k, W β ≤ φ k ⁻¹ᵁ
        ((extLB L₁ L₂ f₁ f₂).U (extIdx (f₁ := f₁) (f₂ := f₂) (jC k) (β.1 k)) ⊓ L.U (jA k)) := fun β k y hy =>
      ⟨mem_ext (Set.mem_iInter.1 hy.1.1 k) (Set.mem_iInter.1 hy.2 k), Set.mem_iInter.1 hy.1.2 k⟩
    let u : ∀ β, Γ(Y, W β)ˣ := fun β => ∏ k, res (l₁ β k)
      (pullU (φ k) _ (w₀.s (extIdx (f₁ := f₁) (f₂ := f₂) (jC k) (β.1 k), jA k))) ^ ε k
    have hu : ∀ (Z : Scheme.{0}) (f : Z ⟶ Y) (z : Z) β (hz : f z ∈ W β),
        gm f z (W β) (u β) = ∏ k, ev w₀ (f ≫ φ k) z (jC k) (β.1 k) (jA k) ^ ε k := fun Z f z β hz =>
      (map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans (congrArg (· ^ ε k)
        ((gm_res f z (l₁ β k) hz _).trans (gm_pull f (φ k) z _ (l₁ β k hz) _))))
    obtain ⟨s, hs⟩ := glue_unit _ W l₀ (fun y hy => by
        obtain ⟨β, hβ, hβ'⟩ := cover y
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨β, hβ'⟩, hy, Set.mem_iInter.2 hβ⟩) u (fun β β' y hy => by
        rw [hu _ (𝟙 Y) y β hy.1, hu _ (𝟙 Y) y β' hy.2]
        have a : ∀ k, ev w₀ (𝟙 Y ≫ φ k) y (jC k) (β.1 k) (jA k) =
            gm (φ k ≫ f₂) y (L₂.U (β.1 k) ⊓ L₂.U (β'.1 k)) (L₂.g (β.1 k) (β'.1 k)) *
              ev w₀ (𝟙 Y ≫ φ k) y (jC k) (β'.1 k) (jA k) := fun k => by
          have m₁ : f₁ (φ k y) ∈ L₁.U (jC k) := Set.mem_iInter.1 hy.1.1.1 k
          have m : φ k y ∈ L.U (jA k) := Set.mem_iInter.1 hy.1.1.2 k
          rw [Category.id_comp, ev_trans hw₀ (φ k) y (jC k) (jC k) (β.1 k) (β'.1 k) (jA k) (jA k) m₁ m₁
            (Set.mem_iInter.1 hy.1.2 k) (Set.mem_iInter.1 hy.2.2 k) m m, gm_self hL₁ (φ k ≫ f₁) y m₁,
            gm_self hL (φ k) y m, _root_.one_mul, inv_one, _root_.mul_one]
        simp only [a, mul_zpow, Finset.prod_mul_distrib]
        rw [hε _ (fun k => gm (φ k ≫ f₂) y (L₂.U (β.1 k) ⊓ L₂.U (β'.1 k)) (L₂.g (β.1 k) (β'.1 k))) (fun k => by
          have key : ∀ (q q' : Y ⟶ X₂) (i i' j j' : L₂.ι), q = q' → i = i' → j = j' →
              gm q y (L₂.U i ⊓ L₂.U j) (L₂.g i j) = gm q' y (L₂.U i' ⊓ L₂.U j') (L₂.g i' j') := by
            rintro _ _ _ _ _ _ rfl rfl rfl; rfl
          exact key _ _ _ _ _ _ (h₂ k) (β.2 k) (β'.2 k)), _root_.one_mul])
    refine ⟨s, fun Z f z β hC hA hβ hβ' => ?_⟩
    have hy : f z ∈ W ⟨β, hβ'⟩ := ⟨⟨hC, hA⟩, Set.mem_iInter.2 hβ⟩
    exact (gm_res f z (l₀ ⟨β, hβ'⟩) hy s).symm.trans
      ((congrArg (gm f z (W ⟨β, hβ'⟩)) (hs ⟨β, hβ'⟩)).trans (hu Z f z ⟨β, hβ'⟩ hy))
  choose s hs using glue
  refine ⟨⟨fun p => s p.1 p.2⟩, fun i j => unit_ext fun y hy => ?_,
    fun Z f z jC jA β hC hA hβ hβ' => hs jC jA Z f z β hC hA hβ hβ'⟩
  obtain ⟨β, hβ, hβ'⟩ := cover y
  have e₁ := hs i.1 i.2 _ (𝟙 Y) y β hy.1.1 hy.1.2 hβ hβ'
  have e₂ := hs j.1 j.2 _ (𝟙 Y) y β hy.2.1 hy.2.2 hβ hβ'
  have gC := gm_linComb L₁ (fun k => φ k ≫ f₁) ε (𝟙 Y) y i.1 j.1 hy.1.1 hy.2.1
  have gA := gm_linComb L φ ε (𝟙 Y) y i.2 j.2 hy.1.2 hy.2.2
  refine (gm_res (𝟙 Y) y _ hy _).trans (e₁.trans (Eq.symm ((map_mul _ _ _).trans ?_)))
  refine (congrArg₂ (· * ·) ((gm_div (LB.LinComb L φ ε) (LB.LinComb L₁ (fun k => φ k ≫ f₁) ε) (𝟙 Y) y i j hy).trans
    (congrArg₂ (fun a b => a * b⁻¹) gC gA)) ((gm_res (𝟙 Y) y _ hy _).trans e₂)).trans ?_
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  simp only [Category.id_comp]
  rw [ev_trans hw₀ (φ k) y (i.1 k) (j.1 k) (β k) (β k) (i.2 k) (j.2 k) (Set.mem_iInter.1 hy.1.1 k)
    (Set.mem_iInter.1 hy.2.1 k) (hβ k) (hβ k) (Set.mem_iInter.1 hy.1.2 k) (Set.mem_iInter.1 hy.2.2 k),
    gm_self hL₂ (φ k ≫ f₂) y (hβ k), _root_.mul_one, mul_zpow, mul_zpow, inv_zpow]

end

theorem cancel_two (G : Type) [CommGroup G] (a : ULift.{0} (Finset (Fin 2)) → G)
    (h : ∀ I, a I = a ⟨insert 0 I.down⟩) : ∏ I, a I ^ ((-1 : ℤ) ^ (2 - I.down.card)) = 1 := by
  rw [← Equiv.prod_comp (Equiv.ulift.{0}.symm : Finset (Fin 2) ≃ ULift.{0} (Finset (Fin 2)))]
  have hu : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide
  rw [hu, Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  have e₀ : a ⟨∅⟩ = a ⟨{0}⟩ := h ⟨∅⟩
  have e₁ : a ⟨{1}⟩ = a ⟨{0, 1}⟩ := h ⟨{1}⟩
  show a ⟨∅⟩ ^ (1 : ℤ) * (a ⟨{0}⟩ ^ (-1 : ℤ) * (a ⟨{1}⟩ ^ (-1 : ℤ) * a ⟨{0, 1}⟩ ^ (1 : ℤ))) = 1
  rw [e₀, e₁]
  simp

end GlobalTheory.MumProd.CubeIso

namespace GlobalTheory.MumProd

theorem exists_cubeIso : ∀ (S : Scheme.{0}) (B B₁ B₂ T : Over S) [GrpObj B] [IsCommMonObj B] [GrpObj B₁] [IsCommMonObj B₁] [GrpObj B₂] [IsCommMonObj B₂] (M : LB B.left) (M₁ : LB B₁.left) (M₂ : LB B₂.left), M.IsLB → M₁.IsLB → M₂.IsLB → ∀ (p₁ : B ⟶ B₁) (p₂ : B ⟶ B₂) (wM : LB.Iso M (extLB M₁ M₂ p₁.left p₂.left)), wM.IsGen → ∀ (x : Fin 2 → (T ⟶ B)) (x₁ : Fin 2 → (T ⟶ B₁)), (∀ I : Finset (Fin 2), psum B x I ≫ p₁ = psum B₁ x₁ I) → (∀ I : Finset (Fin 2), psum B x I ≫ p₂ = psum B x (insert 0 I) ≫ p₂) → ∃ w : LB.Iso (cubeLB B x M) (cubeLB B₁ x₁ M₁), w.IsGen ∧ ∀ (Z : Scheme.{0}) (f : Z ⟶ T.left) (z : Z) (jC : ULift.{0} (Finset (Fin 2)) → M₁.ι) (jA : ULift.{0} (Finset (Fin 2)) → M.ι) (β : ULift.{0} (Finset (Fin 2)) → M₂.ι), f z ∈ (cubeLB B₁ x₁ M₁).U jC → f z ∈ (cubeLB B x M).U jA → (∀ I, (f ≫ (psum B x I.down).left ≫ p₂.left) z ∈ M₂.U (β I)) → (∀ I, β I = β ⟨insert 0 I.down⟩) → gm f z _ (w.s (jC, jA)) = ∏ I, gm (f ≫ (psum B x I.down).left) z _ (wM.s (extIdx (f₁ := p₁.left) (f₂ := p₂.left) (jC I) (β I), jA I)) ^ ((-1 : ℤ) ^ (2 - I.down.card)) := by
  intro S B B₁ B₂ T _ _ _ _ _ _ M M₁ M₂ hM hM₁ hM₂ p₁ p₂ wM hwM x x₁ h₁ h₂
  obtain ⟨w, hw, H⟩ := CubeIso.exists_linComb hM hM₁ hM₂ wM hwM (K := ULift.{0} (Finset (Fin 2)))
    (fun I => (psum B x I.down).left) (fun I => (psum B₁ x₁ I.down).left) (fun I => (-1) ^ (2 - I.down.card))
    (fun I => ⟨insert 0 I.down⟩) (fun I => by rw [← Over.comp_left, h₁])
    (fun I => by rw [← Over.comp_left, ← Over.comp_left, h₂]) CubeIso.cancel_two
  exact ⟨w, hw, fun Z f z jC jA β hC hA hβ hβ' => H Z f z jC jA β hC hA hβ hβ'⟩

end GlobalTheory.MumProd
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_order_two_point_torus_extension_translate : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₀ D : DegData R (maximalIdeal R))
  (β : D₀.toPre.P.A ≅ D.toPre.P.A) (xe : D₀.toPre.X ≃+ D.toPre.X), IsMonHom β.hom →
  (∀ χ, D₀.toPre.c χ ≫ β.hom = D.toPre.c (xe χ)) →
  ∀ wΛ : LB.Iso (abelian₂ D₀.toPre.P.A D₀.toPre.P.L)
      ((abelian₂ D.toPre.P.A D.toPre.P.L).pull
        (lift (fst D₀.toPre.P.A D₀.toPre.P.A ≫ β.hom) (snd D₀.toPre.P.A D₀.toPre.P.A ≫ β.hom) :
          G2 D₀.toPre.P.A ⟶ G2 D.toPre.P.A).left),
    wΛ.IsGen →
    (∀ (a a' : D₀.toPre.X) (z : (TK R).left) (J : ((TK R).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι)
        (J' : ((TK R).left ⟶ D₀.toPre.P.A.left) → D₀.toPre.P.L.ι), Good D.toPre.P.L z J → Good D₀.toPre.P.L z J' →
        val (D₀.toPre.tau a a') (𝟙 _) z J' =
          GlobalTheory.PolDeg.lamVal wΛ (lift (toUnit (TK R) ≫ D₀.toPre.c a) (toUnit (TK R) ≫ D₀.toPre.c a')).left z J J' *
            val (D.toPre.tau (xe a) (xe a')) (𝟙 _) z J) →
  ∀ b : 𝟙_ (Over (Sp R)) ⟶ D.toPre.P.A, padd D.toPre.P.A b b = η[D.toPre.P.A] →
  ∀ w : LB.Iso D₀.toPre.P.L (LB.LinComb D.toPre.P.L (GlobalTheory.MumCmp.twφ D₀.toPre D.toPre β.hom b) GlobalTheory.MumCmp.twε), w.IsGen →
  ∃ g : GtPt D.toPre (𝟙_ (Over (Sp R))), g.b = b ∧ (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) ∧
    GlobalTheory.MumCmp.IsTwist D₀.toPre D.toPre g := by
  first | exact @GlobalTheory.MumCmp.Point.exists_point | exact GlobalTheory.MumCmp.Point.exists_point | (intros; apply GlobalTheory.MumCmp.Point.exists_point <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.exists_tateSimilitude_hecke_translate_geometric : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (act' : OActN D.O A') (ψ : o.A ⟶ A'), IsAbelianScheme A' → IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover (GlobalTheory.UPel.HT.Hecke.heckeSub o g N) (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left → (∀ c' : D.O, o.act.act c' ≫ ψ = ψ ≫ act'.act c') → ∀ P' : LB (G2 A').left, P'.IsLB → (∃ t : (P'.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen) → (∃ t : (P'.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen) → LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) (P'.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) → ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (β : R →+* κ), x ≫ s = spMap β → ∃ I : TateIsoO D κ (Over.mk x ⟶ A') (fun c g => g ≫ act'.act c) (fun n g g' z => Out.WeilIs A' (P'.pull (lift (𝟙 A') (𝟙 A')).left) n g g' (unitOn z)), ∀ y, toUnit _ ≫ (o.eta (g y) ≫ ψ) = I.ev N y := by
  first | exact @GlobalTheory.UPel.HT.Hecke.TateTransl.exists_tateIsoO_transl | exact GlobalTheory.UPel.HT.Hecke.TateTransl.exists_tateIsoO_transl | (intros; apply GlobalTheory.UPel.HT.Hecke.TateTransl.exists_tateIsoO_transl <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.exists_finite_etale_level_lift_scheme : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N N' : ℕ), N'.Coprime p → N ∣ N' → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s), ∃ (Y : Over S) (ηu : D.La → (Y ⟶ o.A)), IsFinite Y.hom ∧ Etale Y.hom ∧ ∀ (T : Over S) (lv : D.La → (T ⟶ o.A)), (IsLift o N' T lv → ∃! f : T ⟶ Y, ∀ a, f ≫ ηu a = lv a) ∧ ((∃ f : T ⟶ Y, ∀ a, f ≫ ηu a = lv a) → IsLift o N' T lv) := by
  first | exact @GlobalTheory.UPel.HT.exists_liftScheme | exact GlobalTheory.UPel.HT.exists_liftScheme | (intros; apply GlobalTheory.UPel.HT.exists_liftScheme <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem _root_.GlobalTheory.T.pow_polarization_iso_pullback_of_descent : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → ∀ P' : LB (G2 B).left, IsAxesTriv B P' → LBIso (o.P.pull (Hecke.sq2 ψ')) (Hecke.lbPow P' c) → LBIso (Hecke.lbPow o.P c) (P'.pull (Hecke.sq2 ψ)) → ∀ act' : OActN D.O B, (∀ a : D.O, o.act.act a ≫ ψ = ψ ≫ act'.act a) → ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ Y) (β : R →+* κ), x ≫ s = spMap β → ∃ I : TateIsoO D κ (Over.mk x ⟶ B) (fun a g => g ≫ act'.act a) (fun n g g' z => Out.WeilIs B (P'.pull (lift (𝟙 B) (𝟙 B)).left) n g g' (unitOn z)), ∀ y, toUnit _ ≫ (o.eta y ≫ ψ) = I.ev N y := by
  first | exact @UpperTheory.Cb.pow_polarization_iso_pullback_of_descent | exact UpperTheory.Cb.pow_polarization_iso_pullback_of_descent
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.formBundle_pullback_adjointAction_eq_diagonalPower : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (Q : LB (A ⊗ A).left), QHyp A Q → ∀ (O : Type) [Ring O] (bar : O → O) (r : ℕ) (e : Fin r → O) (W : Matrix (Fin r) (Fin r) ℤ) (d : ℕ), (∀ a b, bar (a + b) = bar a + bar b) → Submodule.span ℤ (Set.range e) = ⊤ → ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → 0 < d → ∑ i, ∑ j, W i j • (e j * bar (e i)) = (d : O) → ∀ (T : Scheme.{0}) (t : T ⟶ S) (A' : Over T) [GrpObj A'] [IsCommMonObj A'] (φ' : A'.left ⟶ A.left) (φ₂' : (A' ⊗ A').left ⟶ (A ⊗ A).left) (B' : Over T) [GrpObj B'] (φB : B'.left ⟶ (Out.powObj A r).left) (pr' : Fin r → (B' ⟶ A')), IsGrpPullback A' A t φ' → IsSquare φ' φ₂' → IsGrpPullback B' (Out.powObj A r) t φB → (∀ u, IsMonHom (pr' u)) → (∀ u, (pr' u).left ≫ φ' = φB ≫ (Out.powPr A u).left) → (∀ (X : Over T) (y : Fin r → (X ⟶ A')), ∃! x : X ⟶ B', ∀ u, x ≫ pr' u = y u) → ∀ (act : O → (A' ⟶ A')), IsRAct A' act → Adj A' (Q.pull φ₂') bar act → ∀ Φ : A' ⟶ B', (∀ u, Φ ≫ pr' u = act (e u)) → LBIso ((diagPow A Q d).pull φ') (((formLB A Q (Out.powPr A (n := r)) W).pull φB).pull Φ.left) := by
  first | exact @GlobalTheory.ElRep.main | exact GlobalTheory.ElRep.main | (intros; apply GlobalTheory.ElRep.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc.USum


theorem _root_.GlobalTheory.T.twistedThetaValue_eq_root_mul_thetaOperatorValue : ∀ {o Ω o' Ω' : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] [CommRing o'] [Field Ω'] [Algebra o' Ω'] [ArithBase o' Ω'] {S : ThetaSys o Ω} {S' : ThetaSys o' Ω'} (ρ : S.Real) (ρ' : S'.Real) (lab : S.Gam → S'.Gam) (φ : Ω →+* Ω') (P₀ : PolAV (Sp Ω')) (a : P₀.A.left ⟶ ρ.P.A.left) (a' : P₀.A.left ⟶ ρ'.P.A.left) (x : S'.Gam → (genPt (φ.comp S.R.val.toRingHom) ⟶ ρ.P.A)), IsGenLab ρ ρ' lab φ P₀ a a' x → ∀ (m : ℕ), S'.N = m ^ 2 → ∀ (κ x₀ : S.Gam) (h : S'.Gam), m • h = lab κ → ∃ ξ : Ω', (∃ k : ℕ, 0 < k ∧ ξ ^ k = 1) ∧ ∀ (t : S'.Gam) (v : Ω'), IsTwVal ρ.P S'.N m ρ.th₁ (ρ.fr κ) (genTo _) (x (S'.r • t)) (x h) ((Scheme.ΓSpecIso (CommRingCat.of Ω')).inv.hom v) → v * S'.th (lab x₀) = ξ * φ (S.th x₀) * ∑ j, algebraMap o' Ω' (S'.ρ t j ρ'.i₀) * S'.ev h j := by
  first | exact @GlobalTheory.UPoinc.TwCompare.twVal_eq_root_mul | exact GlobalTheory.UPoinc.TwCompare.twVal_eq_root_mul | (intros; apply GlobalTheory.UPoinc.TwCompare.twVal_eq_root_mul <;> assumption)
end
