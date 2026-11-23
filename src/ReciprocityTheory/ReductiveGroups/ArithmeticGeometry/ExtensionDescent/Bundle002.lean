module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle001
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out

open Semi

variable {S : Scheme.{0}} (A : Over S) [GrpObj A]

def liftHom {T : Over S} (W : (T ⊗ A).left.Opens) : Γ(T.left, ⊤) →+* Γ((T ⊗ A).left, W) :=
  ((T ⊗ A).left.presheaf.map (homOfLE le_top).op).hom.comp (fst T A).left.appTop.hom

theorem res_liftHom {T : Over S} {W W' : (T ⊗ A).left.Opens} (h : W' ≤ W) (r : Γ(T.left, ⊤)) :
    ((T ⊗ A).left.presheaf.map (homOfLE h).op).hom (liftHom A W r) = liftHom A W' r := by
  simp only [liftHom, RingHom.comp_apply]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

@[instance_reducible]
scoped instance secModule {A : Over S} [GrpObj A] {T : Over S} {W : (T ⊗ A).left.Opens} :
    Module Γ(T.left, ⊤) Γ((T ⊗ A).left, W) :=
  (liftHom A W).toModule

def SecM (L : LB A.left) (a : ℤ) (T : Over S) :
    Submodule Γ(T.left, ⊤) (∀ j, Γ((T ⊗ A).left, (LPow A L a T).U j)) where
  carrier := {f | ∀ i j,
    ((T ⊗ A).left.presheaf.map (homOfLE (inf_le_left :
        (LPow A L a T).U i ⊓ (LPow A L a T).U j ≤ (LPow A L a T).U i)).op).hom (f i) =
      ((LPow A L a T).g i j : Γ((T ⊗ A).left, (LPow A L a T).U i ⊓ (LPow A L a T).U j)) *
      ((T ⊗ A).left.presheaf.map (homOfLE (inf_le_right :
        (LPow A L a T).U i ⊓ (LPow A L a T).U j ≤ (LPow A L a T).U j)).op).hom (f j)}
  add_mem' := by
    intro f f' hf hf' i j
    simp only [Pi.add_apply, map_add (f := _), hf i j, hf' i j, mul_add]
  zero_mem' := by
    intro i j
    simp
  smul_mem' := by
    intro c f hf i j
    have hi : (c • f) i = liftHom A _ c * f i := rfl
    have hj : (c • f) j = liftHom A _ c * f j := rfl
    rw [hi, hj, map_mul, map_mul, hf i j, res_liftHom, res_liftHom]
    ring

def SecM.toSec {L : LB A.left} {a : ℤ} {T : Over S} (f : SecM A L a T) : LB.Sec (LPow A L a T) :=
  ⟨f.1, f.2⟩

def SecM.ofSec {L : LB A.left} {a : ℤ} {T : Over S} (s : LB.Sec (LPow A L a T)) : SecM A L a T :=
  ⟨s.f, s.compat⟩

def VVsub (P : PolAV S) (N m : ℕ) (T : Over S) :
    Submodule Γ(T.left, ⊤) (∀ j, Γ((T ⊗ P.A).left, (LPow P.A P.L N T).U j)) :=
  Submodule.span _ {f | ∃ h : f ∈ SecM P.A P.L N T, InVV P N m (SecM.toSec P.A ⟨f, h⟩)}

abbrev de (P : PolAV S) (T : Over S) : Type := Module.Dual Γ(T.left, ⊤) (SecM P.A P.L 1 T)

abbrev mulA (n : ℕ) : A ⟶ A := 𝟙 A ^ n

theorem rigT_le (L : LB A.left) {T : Over S} (j : Fin 1 → L.ι) :
    LB.wchart L (fun _ : Fin 1 => T.hom ≫ eSec A) j ≤
      T.hom ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => j 0) := by
  intro y hy
  exact Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy 0

def rigT (L : LB A.left) (rig : LB.Gen (L.pull (eSec A))) (T : Over S) (k : ℤ) :
    LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => T.hom ≫ eSec A) (fun _ => k)) where
  s := fun j => res (rigT_le A L j) (pullU T.hom _ (rig.s (fun _ => j 0))) ^ k

def powFrame (L : LB A.left) {T : Over S} (x : T ⟶ A)
    (τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => 1))) (k : ℤ) :
    LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => k)) where
  s := fun j => τ.s j ^ k

def rigPow (L : LB A.left) (rig : LB.Gen (L.pull (eSec A))) (k : ℤ) :
    LB.Gen (LB.LinComb L (K := PUnit) (fun _ => eSec A) (fun _ => k)) where
  s := fun j => rig.s j ^ k

def IsNormMul (L : LB A.left) (rig : LB.Gen (L.pull (eSec A))) (n : ℕ)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, (mulA A n).left] ![(n : ℤ) ^ 2, -1])) :
    Prop :=
  LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ α (eSec A))
    (LB.mulGen L _ _ _ _ (rigPow A L rig ((n : ℤ) ^ 2)) (LB.invGen L _ _ rig))

def IsTorsFrame (P : PolAV S) (rig : LB.Gen (P.L.pull (eSec P.A))) (n : ℕ) {T : Over S}
    (x : T ⟶ P.A)
    (τ : LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => 1))) :
    Prop :=
  x ^ n = 1 ∧ τ.IsGen ∧
    ∃ α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, (mulA P.A n).left] ![(n : ℤ) ^ 2, -1]),
      α.IsGen ∧ IsNormMul P.A P.L rig n α ∧
      LB.Gen.Corr P.L _ _ _ _ (powFrame P.A P.L x τ ((n : ℤ) ^ 2))
        (LB.mulGen P.L _ _ _ _ (LB.pullGen P.L _ _ α x.left) (rigT P.A P.L rig T 1))

def IsThetaFrame (P : PolAV S) (rig : LB.Gen (P.L.pull (eSec P.A))) (k : ℤ) {T : Over S}
    (θ : ThetaGrp P.A P.L k T)
    (τ : LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => θ.pt.left) (fun _ => k))) :
    Prop :=
  τ.IsGen ∧
    LB.Gen.Corr P.L _ _ _ _ (LB.mulGen P.L _ _ _ _ (LB.pullGen P.L _ _ θ.φ (ptSecT P.A 1).left) τ)
      (rigT P.A P.L rig T k)


def EvValSt : Prop :=
  ∀ (P : PolAV S) (N : ℕ) {T : Over S} (z : T ⟶ P.A)
    (e : LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => 1))),
    e.IsGen → ∀ s : LB.Sec (LPow P.A P.L N T),
      ∃! v, IsValueAt P.A P.L N s z (powFrame P.A P.L z e N) v

def VVRankSt : Prop :=
  ∀ (P : PolAV S) (m : ℕ) (ze : Γ(S, ⊤)ˣ), Odd m → IsUnit ((m : Γ(S, ⊤))) →
    Nonempty (Level P (m ^ 2) ze) → ∀ (T : Over S) (p : T.left), ∃ V : T.left.Opens, p ∈ V ∧
      IsAffineOpen V ∧ Module.Free Γ((overRes V).left, ⊤) (VVsub P (m ^ 2) m (overRes V)) ∧
      Module.finrank Γ((overRes V).left, ⊤) (VVsub P (m ^ 2) m (overRes V)) = (m ^ 2) ^ P.g

end ReciprocityTheory.ChartRestriction.G.Out
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out.InhVV

open Semi Inh

variable (S : Scheme.{0}) (T : Over S)

def rig1 : LB.Gen ((zeroPolAV S).L.pull (eSec (zeroPolAV S).A)) := ⟨fun _ => 1⟩

def one1 (x : T ⟶ (zeroPolAV S).A) (k : ℤ) :
    LB.Gen (LB.LinComb (zeroPolAV S).L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => k)) :=
  ⟨fun _ => 1⟩

def theta1 (k : ℤ) : ThetaGrp (zeroPolAV S).A (zeroPolAV S).L k T where
  pt := 1
  φ := ⟨fun _ => 1⟩
  isGen := by
    intro i j
    erw [linComb_triv_g, _root_.one_mul]; repeat erw [map_one]

def oneSec (a : ℤ) (T : Over S) : LB.Sec (LPow (zeroPolAV S).A (zeroPolAV S).L a T) :=
  ⟨fun _ => 1, by
    intro i j
    erw [linComb_triv_g]
    simp only [Units.val_one, map_one]
    exact (_root_.one_mul _).symm⟩

end ReciprocityTheory.ChartRestriction.G.Out.InhVV
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

section GtPoints

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
variable (F : Type) [Field F] [Algebra (FractionRing R) F]

namespace DegPre

abbrev cF (χ : D.X) : TF (R := R) F ⟶ D.P.A := toUnit _ ≫ D.c χ

abbrev zeroF : TF (R := R) F ⟶ D.P.A := toUnit _ ≫ η[D.P.A]

def gtφ (b : TF (R := R) F ⟶ D.P.A) (χ : D.X) : Fin 4 → ((TF (R := R) F).left ⟶ D.P.A.left) :=
  ![(padd D.P.A (cF D F χ) b).left, (cF D F χ).left, b.left, (zeroF D F).left]

def gtε : Fin 4 → ℤ := ![-1, 1, 1, -1]

def cubAt (x x' y : TF (R := R) F ⟶ D.P.A) :=
  LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift x (lift x' y)).left

end DegPre

structure GtPtF where
  b : TF (R := R) F ⟶ D.P.A
  s : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (DegPre.gtφ D F b χ) DegPre.gtε)
  isGen : ∀ χ, (s χ).IsGen
  s_zero : LB.Gen.Corr D.P.L _ _ _ _ (s 0) (LB.oneGen D.P.L)
  mult : ∀ χ χ' : D.X, LB.Gen.Corr D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _ (s (χ + χ')) (DegPre.cubAt D F (DegPre.cF D F χ) (DegPre.cF D F χ') b))
    (LB.mulGen D.P.L _ _ _ _ (s χ) (s χ'))

namespace GtPtF

variable {D F}

def IsZero (g : GtPtF D F) : Prop :=
  g.b = DegPre.zeroF D F ∧ ∀ χ, LB.Gen.Corr D.P.L _ _ _ _ (g.s χ) (LB.oneGen D.P.L)

def IsAdd (g g' g'' : GtPtF D F) : Prop :=
  g''.b = padd D.P.A g.b g'.b ∧ ∀ χ, LB.Gen.Corr D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _ (g''.s χ) (DegPre.cubAt D F (DegPre.cF D F χ) g.b g'.b))
    (LB.mulGen D.P.L _ _ _ _ (g.s χ) (g'.s χ))

def IsNsmul (k : ℕ) (g h : GtPtF D F) : Prop :=
  ∃ gs : Fin (k + 1) → GtPtF D F, (gs 0).IsZero ∧
    (∀ i : Fin k, IsAdd (gs i.castSucc) g (gs i.succ)) ∧ gs (Fin.last k) = h

def IsIota (y : D.X) (g : GtPtF D F) : Prop :=
  g.b = DegPre.cF D F y ∧ ∀ χ, LB.Gen.Corr D.P.L _ _ _ _ (g.s χ)
    (LB.pullGen D.P.L _ _ (D.io y χ) (jFK (R := R) F))

end GtPtF

structure QkPt (k : ℕ) where
  y : D.X
  g : GtPtF D F
  eq : ∃ h : GtPtF D F, GtPtF.IsNsmul k g h ∧ GtPtF.IsIota y h

def QkPt.Equiv {k : ℕ} (p p' : QkPt D F k) : Prop :=
  ∃ z : D.X, p'.y = p.y + k • z ∧ ∃ h : GtPtF D F, GtPtF.IsIota z h ∧ GtPtF.IsAdd p.g h p'.g

end GtPoints

section Phi

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
variable (F : Type) [Field F] [Algebra (FractionRing R) F]

namespace DegPre

def trPt (b : TF (R := R) F ⟶ D.P.A) : BF D F ⟶ BF D F :=
  lift (fst _ _) (padd D.P.A (prB D F) (fst _ _ ≫ b))

def phiφ (y α : D.X) (b : TF (R := R) F ⟶ D.P.A) : Fin 4 ⊕ Fin 4 → ((BF D F).left ⟶ D.P.A.left) :=
  Sum.elim (famφ D F (α + y)) (fun i => (trPt D F b).left ≫ famφ D F α i)

def lineφ (b : TF (R := R) F ⟶ D.P.A) : Fin 2 → ((TF (R := R) F).left ⟶ D.P.A.left) :=
  ![(zeroF D F).left, b.left]

def lineε (k : ℕ) : Fin 2 → ℤ := ![(k : ℤ), -(k : ℤ)]

def constBF (ζ : F) (W : (BF D F).left.Opens) : Γ((BF D F).left, W) :=
  ((BF D F).left.presheaf.map (homOfLE le_top).op).hom
    ((fst (TF (R := R) F) D.P.A).left.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ζ))

end DegPre

def PhiRel (k : ℕ) (p : QkPt D F k)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k)))
    (s s' : Fam D F k) : Prop :=
  ∀ (α : D.X) (u : LB.Gen (LB.LinComb D.P.L (DegPre.phiφ D F p.y α p.g.b) (DegPre.deltaε k))),
    u.IsGen →
    LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left)
      (LB.mulGen D.P.L _ _ _ _ (p.g.s α) w) →
    GeneratorPullback.SecRel D.P.L (DegPre.famφ D F (α + p.y)) (DegPre.famε k) (s'.s (α + p.y))
      (DegPre.famφ D F α) (DegPre.famε k) (s.s α) (DegPre.trPt D F p.g.b).left
      (DegPre.phiφ D F p.y α p.g.b) (DegPre.deltaε k) u

def Fam.IsSmul {k : ℕ} (ζ : F) (s s' : Fam D F k) : Prop :=
  ∀ (α : D.X) (j : Fin 4 → D.P.L.ι), (s'.s α).f j = DegPre.constBF D F ζ _ * (s.s α).f j

def WeilQkIs (k : ℕ) (p p' : QkPt D F k) (ζ : F) : Prop :=
  ∀ (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k)))
    (w' : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p'.g.b) (DegPre.lineε k))),
    w.IsGen → w'.IsGen →
    ∀ s s₁ s₂ s₃ s₄ : Fam D F k,
      PhiRel D F k p' w' s s₁ → PhiRel D F k p w s₁ s₂ →
      PhiRel D F k p w s s₃ → PhiRel D F k p' w' s₃ s₄ →
      Fam.IsSmul D F ζ s₄ s₂

end Phi

section QkToAk

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
variable (F : Type) [Field F] [Algebra (FractionRing R) F]

abbrev TFK : Over (TK R).left := Over.mk (jFK (R := R) F)

def QkToAk (P' : PolAV (TK R).left) (k : ℕ)
    (E : LB.Sec (LPow P'.A P'.L (k : ℤ) (TFK (R := R) F)) → Fam D F k → Prop)
    (p : QkPt D F k) (x : TFK (R := R) F ⟶ P'.A) : Prop :=
  x ^ k = 1 ∧
    ∀ θ : ThetaGrp P'.A P'.L (k : ℤ) (TFK (R := R) F), θ.pt = x →
      ∃ w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k)), w.IsGen ∧
        ∀ (t t' : LB.Sec (LPow P'.A P'.L (k : ℤ) (TFK (R := R) F))) (s s' : Fam D F k),
          E t s → E t' s' → IsActOf P'.A P'.L (k : ℤ) θ t t' → PhiRel D F k p w s s'

end QkToAk

section Bridge

open scoped CategoryTheory.Obj

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
variable (F : Type) [Field F] [Algebra (FractionRing R) F]

namespace DegPre

abbrev jFR : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of R) := jFK (R := R) F ≫ jK R

abbrev BFo : Over (Spec (CommRingCat.of F)) := (Over.pullback (jFR (R := R) F)).obj D.P.A

end DegPre

end Bridge

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

section Act

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A]

structure RingAct (O : Type) [Ring O] where

  act : O → (A ⟶ A)
  hom : ∀ a, IsMonHom (act a)
  map_one : act 1 = 𝟙 A
  map_mul : ∀ a b, act (a * b) = act b ≫ act a
  map_add : ∀ a b, act (a + b) = padd A (act a) (act b)

def rosatiφ (f g : A ⟶ A) : Fin 6 → ((A ⊗ A).left ⟶ A.left) :=
  ![(padd A (fst A A ≫ f) (snd A A)).left, (fst A A ≫ f).left, (snd A A).left,
    (padd A (fst A A) (snd A A ≫ g)).left, (fst A A).left, (snd A A ≫ g).left]

def rosatiε : Fin 6 → ℤ := ![1, -1, -1, -1, 1, 1]

def RosatiAdj (L : LB A.left) (f g : A ⟶ A) : Prop :=
  ∀ s : S, ∃ U : S.Opens, s ∈ U ∧
    ∃ t : LB.Gen (LB.LinComb L (K := Fin 6)
        (fun i => ((A ⊗ A).hom ⁻¹ᵁ U).ι ≫ rosatiφ A f g i) rosatiε), t.IsGen

abbrev zero2 : (𝟙_ (Over S)).left ⟶ (A ⊗ A).left := (lift η[A] η[A]).left

end Act

structure PolAV.OAct (O : Type) [Ring O] [StarRing O] {S : Scheme.{0}} (P : PolAV S)
    extends RingAct P.A O where
  rosati : ∀ a : O, RosatiAdj P.A P.L (act a) (act (star a))

namespace DegPre

variable {R : Type} [CommRing R] [IsDomain R]

def pt2 (D : DegPre R) (y y' : D.X) : (TK R).left ⟶ (D.P.A ⊗ D.P.A).left :=
  (lift (toUnit (TK R) ≫ D.c y) (toUnit (TK R) ≫ D.c y')).left

def TauBal (D : DegPre R) (f g : D.P.A ⟶ D.P.A) (a a' : D.X → D.X) : Prop :=
  ∀ (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A f g) rosatiε)), u.IsGen →
    LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L) →
    ∀ y y' : D.X, LB.Gen.Corr D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (D.tau (a y) y') (LB.pullGen D.P.L _ _ u (D.pt2 y y')))
      (D.tau y (a' y'))

structure OAct (O : Type) [Ring O] [StarRing O] (D : DegPre R) [Module O D.X] where
  onB : D.P.OAct O
  c_lin : ∀ (a : O) (y : D.X), D.c (a • y) = D.c y ≫ onB.act a
  tau_bal : ∀ a : O, D.TauBal (onB.act a) (onB.act (star a)) (fun y => a • y) (fun y => star a • y)

end DegPre

abbrev DegData.OAct (O : Type) [Ring O] [StarRing O] {R : Type} [CommRing R] [IsDomain R]
    {I : Ideal R} (D : DegData R I) [Module O D.toPre.X] := D.toPre.OAct O

namespace Inh

def zeroOAct (O : Type) [Ring O] [StarRing O] (S : Scheme.{0}) : (zeroPolAV S).OAct O where
  act := fun _ => 𝟙 _
  hom := fun _ => inferInstance
  map_one := rfl
  map_mul := fun _ _ => (Category.id_comp _).symm
  map_add := fun _ _ => toUnit_unique _ _
  rosati := fun _ _ => ⟨⊤, trivial, ⟨fun _ => 1⟩, by
    intro i j; erw [linComb_triv_g, _root_.one_mul]; dsimp only; repeat erw [map_one]⟩

end Inh

end ReciprocityTheory.ChartRestriction.G.Out
end
end
