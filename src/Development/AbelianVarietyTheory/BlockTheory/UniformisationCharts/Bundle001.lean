module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.QSurjective
public import Mathlib.Tactic.ENatToNat
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
import Mathlib.RingTheory.Radical.NatInt
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

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IndefiniteRowSideFullHecke.TorusPointForms

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

attribute [local instance] SplitExt.free SplitExt.finite

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

abbrev cPt (T : Over (Spec (CommRingCat.of R))) (χ : D.X) : T ⟶ D.P.A := toUnit T ≫ D.c χ

def oφ {T : Over (Spec (CommRingCat.of R))} (b : T ⟶ D.P.A) (χ : D.X) :
    Fin 4 → (T.left ⟶ D.P.A.left) :=
  ![(padd D.P.A b (cPt D T χ)).left, (cPt D T χ).left, b.left, (pzero D.P.A T).left]

def oε : Fin 4 → ℤ := ![1, -1, -1, 1]

def oεInv : Fin 4 → ℤ := ![-1, 1, 1, -1]

abbrev oLB {T : Over (Spec (CommRingCat.of R))} (b : T ⟶ D.P.A) (χ : D.X) : LB T.left :=
  LB.LinComb D.P.L (oφ D b χ) oε

abbrev oInvLB {T : Over (Spec (CommRingCat.of R))} (b : T ⟶ D.P.A) (χ : D.X) : LB T.left :=
  LB.LinComb D.P.L (oφ D b χ) oεInv

def cubAt {T : Over (Spec (CommRingCat.of R))} (x x' x'' : T ⟶ D.P.A) :=
  LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift x (lift x' x'')).left

variable (F : Type) [Field F] [Algebra (FractionRing R) F]

structure GtPt where

  base : TF (R := R) F ⟶ D.P.A

  form : ∀ χ : D.X, LB.Gen (oInvLB D base χ)
  form_gen : ∀ χ : D.X, (form χ).IsGen
  form_mul : ∀ χ χ' : D.X, LB.Gen.Corr D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _ (form (χ + χ')) (cubAt D (cPt D _ χ) (cPt D _ χ') base))
    (LB.mulGen D.P.L _ _ _ _ (form χ) (form χ'))

namespace GtPt

variable {D F}

def IsAdd (g g' h : GtPt D F) : Prop :=
  h.base = padd D.P.A g.base g'.base ∧
    ∀ χ : D.X, LB.Gen.Corr D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (h.form χ) (cubAt D (cPt D _ χ) g.base g'.base))
      (LB.mulGen D.P.L _ _ _ _ (g.form χ) (g'.form χ))

def IsZero (g : GtPt D F) : Prop :=
  g.base = pzero D.P.A _ ∧
    ∀ χ : D.X, LB.Gen.Corr D.P.L _ _ _ _ (g.form χ) (LB.oneGen D.P.L)

inductive IsNsmul (g : GtPt D F) : ℕ → GtPt D F → Prop
  | zero (h : GtPt D F) : IsZero h → IsNsmul g 0 h
  | succ (k : ℕ) (h h' : GtPt D F) : IsNsmul g k h → IsAdd h g h' → IsNsmul g (k + 1) h'

def IsIo (y : D.X) (g : GtPt D F) : Prop :=
  g.base = cPt D _ y ∧
    ∀ χ : D.X, LB.Gen.Corr D.P.L _ _ _ _ (g.form χ)
      (LB.pullGen D.P.L _ _ (D.io y χ) (jFK (R := R) F))

end GtPt

def QPair (k : ℕ) : Type :=
  {p : D.X × GtPt D F // ∃ h : GtPt D F, p.2.IsNsmul k h ∧ GtPt.IsIo p.1 h}

def QRel (k : ℕ) (p p' : QPair D F k) : Prop :=
  ∃ (z : D.X) (w : GtPt D F), GtPt.IsIo z w ∧ p'.1.1 = p.1.1 + k • z ∧ GtPt.IsAdd p.1.2 w p'.1.2

def Qk (k : ℕ) : Type := Quot (QRel D F k)

namespace Qk

variable {D F} {k : ℕ}

def mk (p : QPair D F k) : Qk D F k := Quot.mk _ p

def IsAdd (a b c : Qk D F k) : Prop :=
  ∃ p p' p'' : QPair D F k, mk p = a ∧ mk p' = b ∧ mk p'' = c ∧
    p''.1.1 = p.1.1 + p'.1.1 ∧ GtPt.IsAdd p.1.2 p'.1.2 p''.1.2

def IsZero (a : Qk D F k) : Prop :=
  ∃ p : QPair D F k, mk p = a ∧ p.1.1 = 0 ∧ p.1.2.IsZero

end Qk

abbrev baseF : Over (Spec (CommRingCat.of F)) :=
  (Over.pullback (jFK (R := R) F ≫ jK R)).obj D.P.A

def toB {B' : Over (Spec (CommRingCat.of F))} (β : B' ≅ baseF D F) :
    Over.mk (B'.hom ≫ jFK (R := R) F ≫ jK R) ⟶ D.P.A :=
  Over.homMk (β.hom.left ≫ pullback.fst D.P.A.hom (jFK (R := R) F ≫ jK R)) (by
    have h : β.hom.left ≫ pullback.snd D.P.A.hom (jFK (R := R) F ≫ jK R) = B'.hom := Over.w β.hom
    simp only [Over.mk_hom, Category.assoc]
    erw [pullback.condition]
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ jFK (R := R) F ≫ jK R) h))

def IsDatumIso (E : SplitExt (Spec (CommRingCat.of F))) (β : E.B ≅ baseF D F)
    (ξ : E.X ≃+ D.X) : Prop :=
  IsMonHom β.hom ∧
    ∀ χ : E.X, ∃ t : LB.Iso (E.O χ).L (oLB D (toB D F β) (ξ χ)), t.IsGen

def IsPointCorr {E : SplitExt (Spec (CommRingCat.of F))} (β : E.B ≅ baseF D F)
    {G : Over (Spec (CommRingCat.of F))} [GrpObj G] (q : G ⟶ E.B)
    (e : (𝟙_ (Over (Spec (CommRingCat.of F))) ⟶ G) ≃ GtPt D F) : Prop :=
  (∀ x x', (e x).IsAdd (e x') (e (padd G x x'))) ∧
    (e η[G]).IsZero ∧
    ∀ x, (e x).base.left = (x ≫ q).left ≫ (toB D F β).left

def PointsOfGtSt : Prop :=
  ∀ (E : SplitExt (Spec (CommRingCat.of F))) (β : E.B ≅ baseF D F) (ξ : E.X ≃+ D.X),
    IsDatumIso D F E β ξ →
    ∀ (G : Over (Spec (CommRingCat.of F))) [GrpObj G] (d : E.GtDatum G),
      ∃ e : (𝟙_ (Over (Spec (CommRingCat.of F))) ⟶ G) ≃ GtPt D F, IsPointCorr D F β d.q e

def PointsOfGtCoordSt : Prop :=
  ∀ (E : SplitExt (Spec (CommRingCat.of F))) (β : E.B ≅ baseF D F) (ξ : E.X ≃+ D.X),
    IsDatumIso D F E β ξ →
    ∀ (G : Over (Spec (CommRingCat.of F))) [GrpObj G] (d : E.GtDatum G),
      ∃ (e : (𝟙_ (Over (Spec (CommRingCat.of F))) ⟶ G) ≃ GtPt D F)
        (t : ∀ k, LB.Iso (E.O (E.basis k)).L (oLB D (toB D F β) (ξ (E.basis k)))),
        IsPointCorr D F β d.q e ∧ (∀ k, (t k).IsGen) ∧
        ∀ (x : 𝟙_ (Over (Spec (CommRingCat.of F))) ⟶ G) (j : E.ChartIdx) (j' : Fin 4 → D.P.L.ι)
          (k : Module.Free.ChooseBasisIndex ℤ E.X) (W : (Spec (CommRingCat.of F)).Opens)
          (h₁ : W ≤ (oInvLB D (e x).base (ξ (E.basis k))).U j')
          (h₂ : W ≤ (x ≫ d.q).left ⁻¹ᵁ
            (LB.div (oLB D (toB D F β) (ξ (E.basis k))) (E.O (E.basis k)).L).U (j', j k))
          (h₃ : W ≤ x.left ⁻¹ᵁ (d.q.left ⁻¹ᵁ E.chart j)),
          res (X := Spec (CommRingCat.of F)) h₁ (((e x).form (ξ (E.basis k))).s j') *
              res (X := Spec (CommRingCat.of F)) h₂ (pullU (x ≫ d.q).left _ ((t k).s (j', j k))) =
            res (X := Spec (CommRingCat.of F)) h₃ (pullU x.left _ (d.u j k))

end GlobalTheory.IndefiniteRowSideFullHecke.TorusPointForms
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IndefiniteRowSideFullHecke.CanonicalRigidImages

def fnSec {Z Y : Scheme.{0}} (L : LB Z) (f : Γ(Y, ⊤)) :
    LB.Sec (LB.LinComb L (Y := Y) (K := PEmpty) PEmpty.elim PEmpty.elim) where
  f := fun _ => (Y.presheaf.map (homOfLE le_top).op).hom f
  compat := by
    intro i j
    have key : ∀ {U W : Y.Opens} (h : W ≤ U),
        (Y.presheaf.map (homOfLE h).op).hom ((Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom f) =
          (Y.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom f := by
      intro U W h
      rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]
      rfl
    have hg : (LB.LinComb L (Y := Y) (K := PEmpty) PEmpty.elim PEmpty.elim).g i j = 1 :=
      rfl
    rw [key, key, hg, Units.val_one, _root_.one_mul]

def unitGen {Z Y : Scheme.{0}} (L : LB Z) (u : Γ(Y, ⊤)ˣ) :
    LB.Gen (LB.LinComb L (Y := Y) (K := PEmpty) PEmpty.elim PEmpty.elim) where
  s := fun _ => res le_top u

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (I : Ideal R) (e : ℕ)

abbrev Se (R : Type) [CommRing R] (I : Ideal R) (e : ℕ) : Scheme.{0} :=
  Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))

abbrev Be : Over (Se R I e) := thickObj R I e D.P.A

abbrev up (T : Over (Se R I e)) : Over (Spec (CommRingCat.of R)) := Over.mk (T.hom ≫ thick R I e)

def down {T : Over (Se R I e)} (y : T ⟶ Be D I e) : up I e T ⟶ D.P.A :=
  Over.homMk (y.left ≫ pullback.fst D.P.A.hom (thick R I e)) (by
    have h := Over.w y
    dsimp at h ⊢
    rw [Category.assoc, pullback.condition, ← Category.assoc, h])

def cPt (T : Over (Se R I e)) (χ : D.X) : up I e T ⟶ D.P.A := toUnit _ ≫ D.c χ

def oφ {T : Over (Se R I e)} (y : T ⟶ Be D I e) (χ : D.X) : Fin 4 → (T.left ⟶ D.P.A.left) :=
  ![(padd D.P.A (cPt D I e T χ) (down D I e y)).left, (cPt D I e T χ).left, (down D I e y).left,
    (pzero D.P.A (up I e T)).left]

def oε : Fin 4 → ℤ := ![1, -1, -1, 1]

def oεinv : Fin 4 → ℤ := fun k => - oε k

def cubAt {T : Over (Se R I e)} (a b d : up I e T ⟶ D.P.A) :=
  LB.pullGen (Z := T.left) D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift a (lift b d)).left

def IsImage {H : Over (Se R I e)} (q : H ⟶ Be D I e) (χ : D.X)
    (x : LB.Gen (LB.LinComb D.P.L (oφ D I e q χ) oεinv)) (V : (Be D I e).left.Opens)
    (s : LB.Sec (LB.LinComb D.P.L (fun k => V.ι ≫ oφ D I e (𝟙 _) χ k) oε))
    (h : Γ((q.left ⁻¹ᵁ V).toScheme, ⊤)) : Prop :=
  GeneratorPullback.SecRel D.P.L _ _ (fnSec D.P.L h) _ _ s (q.left ∣_ V) _ _
    (LB.pullGen D.P.L _ _ x (q.left ⁻¹ᵁ V).ι)

structure GtIso (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] where

  q : thickObj R I e G ⟶ Be D I e
  q_hom : IsMonHom q
  q_affine : IsAffineHom q.left

  x : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (oφ D I e q χ) oεinv)
  x_gen : ∀ χ, (x χ).IsGen

  x_add : ∀ χ χ' : D.X, LB.Gen.Corr D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _ (x (χ + χ'))
      (cubAt D I e (cPt D I e _ χ) (cPt D I e _ χ') (down D I e q)))
    (LB.mulGen D.P.L _ _ _ _ (x χ) (x χ'))

  x_mul : ∀ χ : D.X, LB.Gen.Corr D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _
      (LB.pullGen D.P.L _ _ (x χ) (μ[thickObj R I e G]).left)
      (cubAt D I e (cPt D I e _ χ)
        (down D I e (fst (thickObj R I e G) (thickObj R I e G) ≫ q))
        (down D I e (snd (thickObj R I e G) (thickObj R I e G) ≫ q))))
    (LB.mulGen D.P.L _ _ _ _
      (LB.pullGen D.P.L _ _ (x χ) (fst (thickObj R I e G) (thickObj R I e G)).left)
      (LB.pullGen D.P.L _ _ (x χ) (snd (thickObj R I e G) (thickObj R I e G)).left))

  span : ∀ (V : (Be D I e).left.Opens), IsAffineOpen V →
    ∀ f : Γ((q.left ⁻¹ᵁ V).toScheme, ⊤),
      ∃ (F : Finset D.X)
        (s : ∀ χ, LB.Sec (LB.LinComb D.P.L (fun k => V.ι ≫ oφ D I e (𝟙 _) χ k) oε))
        (h : D.X → Γ((q.left ⁻¹ᵁ V).toScheme, ⊤)),
        (∀ χ ∈ F, IsImage D I e q χ (x χ) V (s χ) (h χ)) ∧ f = ∑ χ ∈ F, h χ

  indep : ∀ (V : (Be D I e).left.Opens), IsAffineOpen V →
    ∀ (F : Finset D.X)
      (s : ∀ χ, LB.Sec (LB.LinComb D.P.L (fun k => V.ι ≫ oφ D I e (𝟙 _) χ k) oε))
      (h : D.X → Γ((q.left ⁻¹ᵁ V).toScheme, ⊤)),
      (∀ χ ∈ F, IsImage D I e q χ (x χ) V (s χ) (h χ)) → ∑ χ ∈ F, h χ = 0 →
        ∀ χ ∈ F, ∀ j, (s χ).f j = 0

  i : splitTorus (Se R I e) D.X ⟶ thickObj R I e G
  i_hom : IsMonHom i
  i_q : i ≫ q = toUnit _ ≫ η[Be D I e]

  i_char : ∀ χ : D.X, LB.Gen.Corr D.P.L _ _ _ _
    (LB.pullGen D.P.L _ _ (x χ) i.left) (unitGen D.P.L (charUnit (Se R I e) D.X χ))

end GlobalTheory.IndefiniteRowSideFullHecke.CanonicalRigidImages
end
end
