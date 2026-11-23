module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle003
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
import Mathlib.Tactic.Lemma
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

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out

open Semi

section GtPoints

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
variable (T : Over (Spec (CommRingCat.of R)))

namespace DegPre

abbrev cT (χ : D.X) : T ⟶ D.P.A := toUnit T ≫ D.c χ

abbrev zeroT : T ⟶ D.P.A := toUnit T ≫ η[D.P.A]

def gtφT (b : T ⟶ D.P.A) (χ : D.X) : Fin 4 → (T.left ⟶ D.P.A.left) :=
  ![(padd D.P.A (cT D T χ) b).left, (cT D T χ).left, b.left, (zeroT D T).left]

def cubAtT (x x' y : T ⟶ D.P.A) :=
  LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift x (lift x' y)).left

end DegPre

structure GtPt where
  b : T ⟶ D.P.A
  s : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (DegPre.gtφT D T b χ) DegPre.gtε)
  isGen : ∀ χ, (s χ).IsGen
  s_zero : LB.Gen.Corr D.P.L _ _ _ _ (s 0) (LB.oneGen D.P.L)
  mult : ∀ χ χ' : D.X, LB.Gen.Corr D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _ (s (χ + χ'))
      (DegPre.cubAtT D T (DegPre.cT D T χ) (DegPre.cT D T χ') b))
    (LB.mulGen D.P.L _ _ _ _ (s χ) (s χ'))

namespace GtPt

variable {D T}

def IsZero (g : GtPt D T) : Prop :=
  g.b = DegPre.zeroT D T ∧ ∀ χ, LB.Gen.Corr D.P.L _ _ _ _ (g.s χ) (LB.oneGen D.P.L)

def IsAdd (g g' g'' : GtPt D T) : Prop :=
  g''.b = padd D.P.A g.b g'.b ∧ ∀ χ, LB.Gen.Corr D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _ (g''.s χ) (DegPre.cubAtT D T (DegPre.cT D T χ) g.b g'.b))
    (LB.mulGen D.P.L _ _ _ _ (g.s χ) (g'.s χ))

def IsNsmul (k : ℕ) (g h : GtPt D T) : Prop :=
  ∃ gs : Fin (k + 1) → GtPt D T, (gs 0).IsZero ∧
    (∀ i : Fin k, IsAdd (gs i.castSucc) g (gs i.succ)) ∧ gs (Fin.last k) = h

def IsPull {T' : Over (Spec (CommRingCat.of R))} (h : T'.left ⟶ T.left) (g : GtPt D T)
    (g' : GtPt D T') : Prop :=
  g'.b.left = h ≫ g.b.left ∧
    ∀ χ, LB.Gen.Corr D.P.L _ _ _ _ (g'.s χ) (LB.pullGen D.P.L _ _ (g.s χ) h)

variable (F : Type) [Field F] [Algebra (FractionRing R) F]

def IsPullF (x : Spec (CommRingCat.of F) ⟶ T.left) (g : GtPt D T) (g' : GtPtF D F) : Prop :=
  g'.b.left = x ≫ g.b.left ∧
    ∀ χ, LB.Gen.Corr D.P.L _ _ _ _ (g'.s χ) (LB.pullGen D.P.L _ _ (g.s χ) x)

end GtPt

end GtPoints

section OnW

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
variable (W : (Spec (CommRingCat.of R)).Opens)

abbrev TW : Over (Spec (CommRingCat.of R)) := Over.mk W.ι

abbrev overW (T : Over W.toScheme) : Over (Spec (CommRingCat.of R)) := (Over.map W.ι).obj T

structure PsiOn where
  psi : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit)
    (fun _ => (toUnit (TW W) ≫ D.c χ).left) (fun _ => -1))
  psi_gen : ∀ χ, (psi χ).IsGen
  psi_eq : ∀ χ, LB.Gen.Corr D.P.L _ _ _ _
    (LB.pullGen D.P.L _ _ (psi χ) (jK R ∣_ W))
    (LB.pullGen D.P.L _ _ (D.psi χ) (jK R ⁻¹ᵁ W).ι)

namespace DegPre

def rigW := LB.pullGen D.P.L _ _ D.rig (toUnit (TW W)).left

end DegPre

namespace PsiOn

variable {D W}

def tau (ψW : PsiOn D W) (a b : D.X) :=
  LB.mulGen D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (ψW.psi (a + b)) (LB.invGen D.P.L _ _ (ψW.psi a)))
      (LB.invGen D.P.L _ _ (ψW.psi b)))
    (LB.invGen D.P.L _ _ (D.rigW W))

end PsiOn

def GtPt.IsIotaW {D : DegPre R} {W : (Spec (CommRingCat.of R)).Opens} (ψW : PsiOn D W)
    {T : Over W.toScheme} (y : D.X) (g : GtPt D (overW W T)) : Prop :=
  g.b = DegPre.cT D (overW W T) y ∧ ∀ χ, LB.Gen.Corr D.P.L _ _ _ _ (g.s χ)
    (LB.pullGen D.P.L _ _ (ψW.tau y χ) T.hom)

structure QkPtW (ψW : PsiOn D W) (k : ℕ) (T : Over W.toScheme) where
  y : D.X
  g : GtPt D (overW W T)
  eq : ∃ h : GtPt D (overW W T), GtPt.IsNsmul k g h ∧ GtPt.IsIotaW ψW y h

namespace QkPtW

variable {D W} {ψW : PsiOn D W} {k : ℕ} {T : Over W.toScheme}

def IsAdd (p p' p'' : QkPtW D W ψW k T) : Prop :=
  p''.y = p.y + p'.y ∧ GtPt.IsAdd p.g p'.g p''.g

def IsPull {T' : Over W.toScheme} (h : T' ⟶ T) (p : QkPtW D W ψW k T) (p' : QkPtW D W ψW k T') :
    Prop :=
  p'.y = p.y ∧ GtPt.IsPull h.left p.g p'.g

def IsPullF (F : Type) [Field F] [Algebra (FractionRing R) F]
    (x : Spec (CommRingCat.of F) ⟶ T.left) (p : QkPtW D W ψW k T) (p' : QkPt D F k) : Prop :=
  p'.y = p.y ∧ GtPt.IsPullF F x p.g p'.g

end QkPtW

end OnW

end ReciprocityTheory.ChartRestriction.G.Out
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out

open Semi

open scoped CategoryTheory.Obj

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}

def TorusEndOf {S : Scheme.{0}} (X : Type) [AddCommGroup X] (h : X → X)
    (t : splitTorus S X ⟶ splitTorus S X) : Prop :=
  ∀ χ : X, res (fun x _ => show t.left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial)
      (pullU t.left ⊤ (charUnit S X χ)) = charUnit S X (h χ)

structure UnifPre.OLinear (O : Type) [Ring O] [StarRing O] {D : DegData R I}
    [Module O D.toPre.X] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
    (ιD : D.OAct O) (ιA : A.OAct O) (ιG : RingAct G O) : Prop where
  ext : ∀ a : O, (Over.pullback (jK R)).map (ιG.act a) ≫ U.gen.hom = U.gen.hom ≫ ιA.act a
  q_lin : ∀ (e : ℕ) (a : O), (Over.pullback (thick R I e)).map (ιG.act a) ≫ (U.gt e).q =
    (U.gt e).q ≫ (Over.pullback (thick R I e)).map (ιD.onB.act a)
  i_lin : ∀ (e : ℕ) (a : O), ∃ t : splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.toPre.X ⟶
      splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.toPre.X,
    TorusEndOf D.toPre.X (fun χ => star a • χ) t ∧
      (U.gt e).i ≫ (Over.pullback (thick R I e)).map (ιG.act a) = t ≫ (U.gt e).i

end ReciprocityTheory.ChartRestriction.G.Out
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out

open Semi

def scal {R : Type} [CommRing R] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) (r : R) :
    Γ(Y, ⊤) :=
  p.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)

abbrev resTop {Y : Scheme.{0}} (W : Y.Opens) (c : Γ(Y, ⊤)) : Γ(Y, W) :=
  (Y.presheaf.map (homOfLE le_top).op).hom c

abbrev H0 {Y : Scheme.{0}} (L : LB Y) (k : ℕ) : Type :=
  LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 Y) (fun _ => (k : ℤ)))

namespace GeneratorPullback

variable {X Y Y' : Scheme.{0}} (L : LB X) {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]

def SecScal (φ₁ : K₁ → (Y' ⟶ X)) (ε₁ : K₁ → ℤ) (s₁ : LB.Sec (LB.LinComb L φ₁ ε₁))
    (φ₂ : K₂ → (Y ⟶ X)) (ε₂ : K₂ → ℤ) (s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)) (h : Y' ⟶ Y)
    (c : Γ(Y', ⊤)) : Prop :=
  ∀ (j₁ : K₁ → L.ι) (j₂ : K₂ → L.ι),
    LB.Coh L (Sum.elim φ₁ (fun k => h ≫ φ₂ k)) (Sum.elim j₁ j₂) →
    (Y'.presheaf.map (homOfLE (inf_le_right.trans
        (fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k) :
        LB.wchart L φ₁ j₁ ⊓ LB.wchart L (fun k => h ≫ φ₂ k) j₂ ≤
          h ⁻¹ᵁ LB.wchart L φ₂ j₂)).op).hom ((h.app (LB.wchart L φ₂ j₂)).hom (s₂.f j₂)) =
      resTop _ c *
      (Y'.presheaf.map (homOfLE (inf_le_left :
        LB.wchart L φ₁ j₁ ⊓ LB.wchart L (fun k => h ≫ φ₂ k) j₂ ≤ LB.wchart L φ₁ j₁)).op).hom
        (s₁.f j₁)

end GeneratorPullback

namespace DegPre

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

def famφB (α : D.X) : Fin 4 → (D.P.A.left ⟶ D.P.A.left) :=
  ![𝟙 _, (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c α)).left, (toUnit D.P.A ≫ D.c α).left,
    (toUnit D.P.A ≫ η[D.P.A]).left]

abbrev SecB (k : ℕ) (α : D.X) : Type := LB.Sec (LB.LinComb D.P.L (famφB D α) (famε k))

end DegPre

def CohAll {X Y : Scheme.{0}} (L : LB X) {Idx : Type} (φ : Idx → (Y ⟶ X)) (j : Idx → L.ι) : Prop :=
  ∀ a b, φ a = φ b → j a = j b

section Expansion

open scoped CategoryTheory.Obj

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

namespace UnifPre

variable (U : UnifPre I D A G)

abbrev SecK (k : ℕ) : Type :=
  LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => pullback.fst G.hom (jK R)) (fun _ => (k : ℤ)))

abbrev expW (e : ℕ) (p : (PUnit.{1} → D.toPre.P.L.ι) × (PUnit.{1} → U.LG.L.ι))
    (j₁ : Fin 1 → U.LG.L.ι) (S : Finset D.toPre.X) (jf jt : D.toPre.X → Fin 4 → D.toPre.P.L.ι) :
    (thickObj R I e G).left.Opens :=
  (LB.div (D.toPre.P.L.pull (U.gt e).pG.left) (U.LG.L.pull (fstG I e G).left)).U p ⊓
    (fstG I e G).left ⁻¹ᵁ LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j₁ ⊓
    S.inf (fun α => (U.gt e).pG.left ⁻¹ᵁ LB.wchart D.toPre.P.L (D.toPre.famφB α) (jf α) ⊓
      LB.wchart D.toPre.P.L (D.toPre.Oφ (U.gt e).pG α) (jt α))

lemma expW_le_f (e : ℕ) (p) (j₁) {S : Finset D.toPre.X} (jf jt) {α : D.toPre.X} (hα : α ∈ S) :
    U.expW e p j₁ S jf jt ≤ (U.gt e).pG.left ⁻¹ᵁ LB.wchart D.toPre.P.L (D.toPre.famφB α) (jf α) :=
  inf_le_right.trans ((Finset.inf_le hα).trans inf_le_left)

lemma expWeight_le_chart_weight (e : ℕ) (p) (j₁) {S : Finset D.toPre.X} (jf jt) {α : D.toPre.X} (hα : α ∈ S) :
    U.expW e p j₁ S jf jt ≤ LB.wchart D.toPre.P.L (D.toPre.Oφ (U.gt e).pG α) (jt α) :=
  inf_le_right.trans ((Finset.inf_le hα).trans inf_le_right)

def ExpandsAt (e k : ℕ)
    (σ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))))
    (f : ∀ α : D.toPre.X, D.toPre.SecB k α) : Prop :=
  ∃ S : Finset D.toPre.X,
    (∀ α ∉ S, ∀ j : Fin 4 → D.toPre.P.L.ι, ((U.gt e).pG.left.app _).hom ((f α).f j) = 0) ∧
    ∀ (p : (PUnit.{1} → D.toPre.P.L.ι) × (PUnit.{1} → U.LG.L.ι)) (j₁ : Fin 1 → U.LG.L.ι)
      (jf jt : D.toPre.X → Fin 4 → D.toPre.P.L.ι),
      j₁ 0 = p.2 PUnit.unit →
      CohAll D.toPre.P.L
        (Sum.elim (fun _ : PUnit.{1} => (U.gt e).pG.left)
          (Sum.elim (fun a : S × Fin 4 => (U.gt e).pG.left ≫ D.toPre.famφB a.1.1 a.2)
            (fun a : S × Fin 4 => D.toPre.Oφ (U.gt e).pG a.1.1 a.2)))
        (Sum.elim (fun _ => p.1 PUnit.unit)
          (Sum.elim (fun a : S × Fin 4 => jf a.1.1 a.2) (fun a : S × Fin 4 => jt a.1.1 a.2))) →
      (res (inf_le_left.trans inf_le_left :
          U.expW e p j₁ S jf jt ≤ (LB.div (D.toPre.P.L.pull (U.gt e).pG.left)
            (U.LG.L.pull (fstG I e G).left)).U p) ((U.w e).s p)).val ^ k *
        ((thickObj R I e G).left.presheaf.map (homOfLE (inf_le_left.trans inf_le_right :
          U.expW e p j₁ S jf jt ≤
            (fstG I e G).left ⁻¹ᵁ LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j₁)).op).hom
          (((fstG I e G).left.app _).hom (σ.f j₁)) =
      ∑ α ∈ S.attach,
        ((thickObj R I e G).left.presheaf.map
            (homOfLE (U.expW_le_f e p j₁ jf jt α.2)).op).hom
            (((U.gt e).pG.left.app _).hom ((f α.1).f (jf α.1))) *
          (res (U.expWeight_le_chart_weight e p j₁ jf jt α.2) (((U.gt e).t α.1).s (jt α.1))).val

def Expands (k : ℕ) (s : U.SecK k) (F : Fam D.toPre (FractionRing R) k) : Prop :=
  ∃ (r : R) (_ : r ≠ 0)
    (σ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))))
    (f : ∀ α : D.toPre.X, D.toPre.SecB k α),
    GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) (fun _ => (k : ℤ)) s
      (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ)) σ (pullback.fst G.hom (jK R))
      (scal (pullback.snd G.hom (jK R) ≫ jK R) r) ∧
    (∀ α : D.toPre.X,
      GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k) (F.s α)
        (D.toPre.famφB α) (DegPre.famε k) (f α) (DegPre.prB D.toPre (FractionRing R)).left
        (scal (DegPre.BF D.toPre (FractionRing R)).hom r)) ∧
    ∀ e : ℕ, U.ExpandsAt e k σ f

def ExpBij (k : ℕ) : Prop :=
  (∀ s : U.SecK k, ∃! F : Fam D.toPre (FractionRing R) k, U.Expands k s F) ∧
    ∀ F : Fam D.toPre (FractionRing R) k, ∃! s : U.SecK k, U.Expands k s F

end UnifPre

end Expansion

structure Unif {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I)
    (A : PolAV (Spec (CommRingCat.of (FractionRing R))))
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G]
    extends UnifPre I D A G where
  expand : ∀ k : ℕ, 1 ≤ k → toUnifPre.ExpBij k

end ReciprocityTheory.ChartRestriction.G.Out
end
end
