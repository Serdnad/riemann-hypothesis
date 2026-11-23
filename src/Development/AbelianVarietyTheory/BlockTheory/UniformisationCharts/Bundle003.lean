module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle002
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

namespace GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

section Carries

variable {X X' Y : Scheme.{0}} (L : LB X) (L' : LB X') (F : X' ⟶ X)

lemma chart_le_target (p' : Y ⟶ X') (p : Y ⟶ X) (hp : p' ≫ F = p) (j : L.ι) (j' : L'.ι) :
    p' ⁻¹ᵁ (LB.div (L.pull F) L').U (fun _ => j, j') ≤
      LB.wchart L (fun _ : PUnit => p) (fun _ => j) := by
  intro y hy
  refine Set.mem_iInter.2 fun _ => ?_
  have h1 : p'.base y ∈ LB.wchart L (fun _ : PUnit => F) (fun _ => j) := hy.1
  have h2 : F.base (p'.base y) ∈ L.U j := Set.mem_iInter.1 h1 PUnit.unit
  subst hp
  exact h2

lemma chart_le_source (p' : Y ⟶ X') (j : L.ι) (j' : L'.ι) :
    p' ⁻¹ᵁ (LB.div (L.pull F) L').U (fun _ => j, j') ≤
      LB.wchart L' (fun _ : PUnit => p') (fun _ => j') :=
  fun _ hy => Set.mem_iInter.2 fun _ => hy.2

def CarriesAt (w : LB.Iso L' (L.pull F)) (p' : Y ⟶ X') (p : Y ⟶ X) (hp : p' ≫ F = p) (n : ℤ)
    (a : LB.Gen (LB.LinComb L' (K := PUnit) (fun _ => p') (fun _ => n)))
    (b : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => p) (fun _ => n))) : Prop :=
  ∀ (j : L.ι) (j' : L'.ι),
    res (chart_le_target L L' F p' p hp j j') (b.s (fun _ => j)) =
      (pullU p' _ (w.s (fun _ => j, j'))) ^ n *
        res (chart_le_source L L' F p' j j') (a.s (fun _ => j'))

end Carries

section Pull

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

abbrev specOf (φ : R →+* R') : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom φ)

lemma ptK_comp (φ : R →+* R') {B : Over (Spec (CommRingCat.of R))}
    {B' : Over (Spec (CommRingCat.of R'))} (F : B'.left ⟶ B.left)
    (x : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ B) (x' : 𝟙_ (Over (Spec (CommRingCat.of R'))) ⟶ B')
    (hx : x'.left ≫ F = specOf φ ≫ x.left) (W : (Spec (CommRingCat.of R)).Opens)
    (g : (TK R').left ⟶ (TW W).left) (hg : g ≫ W.ι = jK R' ≫ specOf φ) :
    ptK x' ≫ F = g ≫ (toUnit (TW W) ≫ x).left := by
  have h1 : ptK x' = jK R' ≫ x'.left := rfl
  have h2 : (toUnit (TW W) ≫ x).left = W.ι ≫ x.left := rfl
  rw [h1, h2]
  calc (jK R' ≫ x'.left) ≫ F = jK R' ≫ (x'.left ≫ F) := Category.assoc _ _ _
    _ = jK R' ≫ (specOf φ ≫ x.left) := by rw [hx]
    _ = (jK R' ≫ specOf φ) ≫ x.left := (Category.assoc _ _ _).symm
    _ = (g ≫ W.ι) ≫ x.left := by rw [hg]
    _ = g ≫ W.ι ≫ x.left := Category.assoc _ _ _

structure PullIdent (φ : R →+* R') (D : DegPre R) (D' : DegPre R') where
  F : D'.P.A.left ⟶ D.P.A.left
  cart : IsPullback F D'.P.A.hom D.P.A.hom (specOf φ)
  F_one : eSec D'.P.A ≫ F = specOf φ ≫ eSec D.P.A
  F_mul : (μ[D'.P.A]).left ≫ F =
    pullback.map D'.P.A.hom D'.P.A.hom D.P.A.hom D.P.A.hom F F (specOf φ) cart.w.symm cart.w.symm ≫
      (μ[D.P.A]).left
  w : LB.Iso D'.P.L (D.P.L.pull F)
  w_gen : w.IsGen
  w_rig : CarriesAt D.P.L D'.P.L F w (eSec D'.P.A) (specOf φ ≫ eSec D.P.A) F_one 1 D'.rig
    (LB.pullGen D.P.L _ _ D.rig (specOf φ))
  xe : D'.X ≃+ D.X
  c_eq : ∀ χ : D'.X, (D'.c χ).left ≫ F = specOf φ ≫ (D.c (xe χ)).left
  w_psi : ∃ (W : (Spec (CommRingCat.of R)).Opens) (ψW : PsiOn D W)
    (g : (TK R').left ⟶ (TW W).left) (hg : g ≫ W.ι = jK R' ≫ specOf φ),
    ∀ χ : D'.X, CarriesAt D.P.L D'.P.L F w (D'.xK χ) (g ≫ (toUnit (TW W) ≫ D.c (xe χ)).left)
      (ptK_comp φ F (D.c (xe χ)) (D'.c χ) (c_eq χ) W g hg) (-1) (D'.psi χ)
      (LB.pullGen D.P.L _ _ (ψW.psi (xe χ)) g)

end Pull

end GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IndefiniteRowSideFullHecke.BaseChangeCharts

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj

section FamBaseChange

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
variable (F : Type) [Field F] [Algebra (FractionRing R) F]

def overHom {S X Y : Scheme.{0}} (a : X ⟶ S) (b : Y ⟶ S) (h : X ⟶ Y) (w : h ≫ b = a) :
    Over.mk a ⟶ Over.mk b := Over.homMk h w

omit [IsDomain R] in
lemma specMap_algebraMap_self (K : Type) [CommRing K] :
    Spec.map (CommRingCat.ofHom (algebraMap K K)) = 𝟙 _ := by
  rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]

def specFK : TF (R := R) F ⟶ TF (R := R) (FractionRing R) :=
  overHom (X := Spec (CommRingCat.of F)) (Y := Spec (CommRingCat.of (FractionRing R))) _ _
    (Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) F)))
    (congrArg (fun z => Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) F)) ≫ z)
      ((congrArg (fun z => z ≫ jK R) (specMap_algebraMap_self (FractionRing R))).trans
        (Category.id_comp _)))

def bcB : DegPre.BF D F ⟶ DegPre.BF D (FractionRing R) := specFK (R := R) F ▷ D.P.A

lemma bcB_prB : bcB D F ≫ DegPre.prB D (FractionRing R) = DegPre.prB D F := by
  simp [bcB]

lemma bcB_famφ (α : D.X) (i : Fin 4) :
    (bcB D F).left ≫ DegPre.famφ D (FractionRing R) α i = DegPre.famφ D F α i := by
  have hu : ∀ x : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A,
      bcB D F ≫ toUnit _ ≫ x = toUnit _ ≫ x := fun x => by
    rw [← Category.assoc, comp_toUnit]
  fin_cases i
  · exact congrArg (·.left) (bcB_prB D F)
  · have : bcB D F ≫ padd D.P.A (DegPre.prB D (FractionRing R)) (toUnit _ ≫ D.c α) =
        padd D.P.A (DegPre.prB D F) (toUnit _ ≫ D.c α) := by
      unfold padd
      rw [← Category.assoc, comp_lift, bcB_prB, hu]
    exact congrArg (·.left) this
  · exact congrArg (·.left) (hu (D.c α))
  · exact congrArg (·.left) (hu η[D.P.A])

lemma chart_le_bcB (α : D.X) (j : Fin 4 → D.P.L.ι) :
    LB.wchart D.P.L (DegPre.famφ D F α) j ≤
      (bcB D F).left ⁻¹ᵁ LB.wchart D.P.L (DegPre.famφ D (FractionRing R) α) j := by
  intro y hy
  refine Set.mem_iInter.2 fun i => ?_
  have h1 : (DegPre.famφ D F α i).base y ∈ (D.P.L.U (j i) : Set D.P.A.left) :=
    Set.mem_iInter.1 hy i
  rw [← bcB_famφ D F α i] at h1
  exact h1

def FamComb (k : ℕ) {n : ℕ} (c : Fin n → F) (f : Fin n → Fam D (FractionRing R) k)
    (s : Fam D F k) : Prop :=
  ∀ (α : D.X) (j : Fin 4 → D.P.L.ι),
    @id Γ((DegPre.BF D F).left, LB.wchart D.P.L (DegPre.famφ D F α) j) ((s.s α).f j) =
      ∑ i, DegPre.constBF D F (c i) (LB.wchart D.P.L (DegPre.famφ D F α) j) *
        ((DegPre.BF D F).left.presheaf.map (homOfLE (chart_le_bcB D F α j)).op).hom
          (((bcB D F).left.app (LB.wchart D.P.L (DegPre.famφ D (FractionRing R) α) j)).hom
            (((f i).s α).f j))

end FamBaseChange

section Expansion

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

def Ident (U : UnifPre I D A G) : Type :=
  {w : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R))) // w.IsGen}

variable (F : Type) [Field F] [Algebra (FractionRing R) F]

abbrev AF (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) : Scheme.{0} :=
  (TFK (R := R) F ⊗ A.A).left

abbrev SecF (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (k : ℕ) : Type :=
  LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F))

def toGK (U : UnifPre I D A G) : AF F A ⟶ pullback G.hom (jK R) :=
  (snd (TFK (R := R) F) A.A ≫ U.gen.inv).left

lemma toGK_gen (U : UnifPre I D A G) :
    toGK F U ≫ U.gen.hom.left = (snd (TFK (R := R) F) A.A).left := by
  have : (snd (TFK (R := R) F) A.A ≫ U.gen.inv) ≫ U.gen.hom = snd (TFK (R := R) F) A.A := by
    simp
  exact congrArg (·.left) this

abbrev cmpW (U : UnifPre I D A G) (a : U.LG.L.ι) (b : A.L.ι) : (AF F A).Opens :=
  toGK F U ⁻¹ᵁ ((U.LG.L.pull (pullback.fst G.hom (jK R))).U (fun _ => a) ⊓
    (A.L.pull U.gen.hom.left).U (fun _ => b))

lemma cmpW_le_L (U : UnifPre I D A G) (k : ℕ) (a : U.LG.L.ι) (b : A.L.ι) :
    cmpW F U a b ≤ (LPow A.A A.L (k : ℤ) (TFK (R := R) F)).U (fun _ => b) := by
  intro y hy
  have h1 : (toGK F U ≫ U.gen.hom.left).base y ∈ (A.L.U b : Set A.A.left) :=
    Set.mem_iInter.1 hy.2 PUnit.unit
  rw [toGK_gen] at h1
  exact Set.mem_iInter.2 fun _ => h1

lemma cmpW_le_LG (U : UnifPre I D A G) (a : U.LG.L.ι) (b : A.L.ι) :
    cmpW F U a b ≤ toGK F U ⁻¹ᵁ
      LB.wchart U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) (fun _ => a) := by
  intro y hy
  exact Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy.1 PUnit.unit

def SecComb (U : UnifPre I D A G) (w : Ident U) (k : ℕ) {n : ℕ} (c : Fin n → F)
    (σ : Fin n → U.SecK k) (t : SecF F A k) : Prop :=
  ∀ (a : U.LG.L.ι) (b : A.L.ι),
    @id Γ(AF F A, cmpW F U a b) (pullU (toGK F U) _ (w.1.s (fun _ => a, fun _ => b))).val ^ k *
      ((AF F A).presheaf.map (homOfLE (cmpW_le_L F U k a b)).op).hom (t.f (fun _ => b)) =
    ∑ i, @id Γ(AF F A, cmpW F U a b) (liftFun A.A (T := TFK (R := R) F) (cmpW F U a b)
        ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c i))) *
      ((AF F A).presheaf.map (homOfLE (cmpW_le_LG F U a b)).op).hom
        (((toGK F U).app _).hom ((σ i).f (fun _ => a)))

def ExpandsF (U : UnifPre I D A G) (w : Ident U) (k : ℕ) (t : SecF F A k)
    (s : Fam D.toPre F k) : Prop :=
  ∃ (n : ℕ) (c : Fin n → F) (σ : Fin n → U.SecK k)
    (f : Fin n → Fam D.toPre (FractionRing R) k),
    (∀ i, U.Expands k (σ i) (f i)) ∧ SecComb F U w k c σ t ∧ FamComb D.toPre F k c f s

end Expansion

end GlobalTheory.IndefiniteRowSideFullHecke.BaseChangeCharts
end
end
