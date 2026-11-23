module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubicalPullBaseChangeSt
public import Development.AbelianVarietyTheory.BlockTheory.UniformisationCharts.Bundle001
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

namespace GlobalTheory.IndefiniteRowSideFullHecke.TranslatedLineGenerators

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.IndefiniteRowSideFullHecke.TorusPointForms

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
variable (F : Type) [Field F] [Algebra (FractionRing R) F]

def scal : F →+* Γ(Spec (CommRingCat.of F), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom

def trPt (b : TF (R := R) F ⟶ D.P.A) : D.BF F ⟶ D.BF F :=
  lift (fst _ _) (padd D.P.A (D.prB F) (fst _ _ ≫ b))

abbrev lineAt (k : ℕ) (b : TF (R := R) F ⟶ D.P.A) : LB (TF (R := R) F).left :=
  LB.LinComb D.P.L (K := PUnit) (fun _ => b.left) (fun _ => (k : ℤ))

def LineGen (k : ℕ) (b : TF (R := R) F ⟶ D.P.A) : Type :=
  {t : LB.Gen (lineAt D F k b) // t.IsGen}

def phφ (b : TF (R := R) F ⟶ D.P.A) (y α : D.X) : Fin 4 ⊕ Fin 4 → ((D.BF F).left ⟶ D.P.A.left) :=
  Sum.elim (D.famφ F (α + y)) (fun i => (trPt D F b).left ≫ D.famφ F α i)

def phMult (k : ℕ) (g : GtPt D F) (t : LineGen D F k g.base) (α : D.X) :=
  LB.mulGen D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _ (g.form α) (LB.invGen D.P.L _ _ t.1))
    (GeneratorPullback.powGen D.P.L _ _ (LB.pullGen D.P.L _ _ D.rig (toUnit (TF (R := R) F)).left) k)

variable {D F}

def IsPh {k : ℕ} (p : QPair D F k) (t : LineGen D F k p.1.2.base) (s s' : Fam D F k) : Prop :=
  ∀ α : D.X, ∃ u : LB.Gen (LB.LinComb D.P.L (phφ D F p.1.2.base p.1.1 α) (DegPre.deltaε k)),
    u.IsGen ∧
    LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (D.zF F).left) (phMult D F k p.1.2 t α) ∧
    GeneratorPullback.SecRel D.P.L (D.famφ F (α + p.1.1)) (DegPre.famε k) (s'.s (α + p.1.1))
      (D.famφ F α) (DegPre.famε k) (s.s α) (trPt D F p.1.2.base).left
      (phφ D F p.1.2.base p.1.1 α) (DegPre.deltaε k) u

def FamSmul {k : ℕ} (c : F) (s s' : Fam D F k) : Prop :=
  ∀ α j, (s'.s α).f j = liftFun D.P.A (T := TF (R := R) F) _ (scal F c) * (s.s α).f j

def FamAdd {k : ℕ} (s s' s'' : Fam D F k) : Prop :=
  ∀ α j, (s''.s α).f j = (s.s α).f j + (s'.s α).f j

variable (R F) in
abbrev TKF (R : Type) [CommRing R] [IsDomain R]
    (F : Type) [Field F] [Algebra (FractionRing R) F] :
    Over (Spec (CommRingCat.of (FractionRing R))) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) F)))

variable (F) in
abbrev SecA (F : Type) [Field F] [Algebra (FractionRing R) F]
    (P : PolAV (Spec (CommRingCat.of (FractionRing R)))) (k : ℕ) : Type :=
  LB.Sec (LPow P.A P.L (k : ℤ) (TKF R F))

variable {P : PolAV (Spec (CommRingCat.of (FractionRing R)))}

structure IsLinBij {k : ℕ} (E : SecA F P k → Fam D F k → Prop) : Prop where
  existsUnique_right : ∀ σ, ∃! s, E σ s
  existsUnique_left : ∀ s, ∃! σ, E σ s
  add : ∀ σ σ' σ'' s s' s'', E σ s → E σ' s' → E σ'' s'' →
    (∀ j, σ''.f j = σ.f j + σ'.f j) → FamAdd s s' s''
  smul : ∀ (c : F) σ σ' s s', E σ s → E σ' s' →
    (∀ j, σ'.f j = liftFun P.A (T := TKF R F) _ (scal F c) * σ.f j) → FamSmul c s s'

def Intertwines {k : ℕ} (E : SecA F P k → Fam D F k → Prop)
    (θ : ThetaGrp P.A P.L (k : ℤ) (TKF R F)) (p : QPair D F k) (t : LineGen D F k p.1.2.base) :
    Prop :=
  ∀ σ σ' s s', E σ s → E σ' s' → (IsActOf P.A P.L (k : ℤ) θ σ σ' ↔ IsPh p t s s')

def IsImage {k : ℕ} (E : SecA F P k → Fam D F k → Prop) (p : QPair D F k)
    (x : TKF R F ⟶ P.A) : Prop :=
  1 ≤ k ∧ D.TauBimult ∧ IsLinBij E ∧ x ^ k = 1 ∧
    (∀ θ : ThetaGrp P.A P.L (k : ℤ) (TKF R F), θ.pt = x → ∃ t, Intertwines E θ p t) ∧
    (∀ t, ∃ θ : ThetaGrp P.A P.L (k : ℤ) (TKF R F), θ.pt = x ∧ Intertwines E θ p t)

def IsImageQ {k : ℕ} (E : SecA F P k → Fam D F k → Prop) (a : Qk D F k)
    (x : TKF R F ⟶ P.A) : Prop :=
  ∀ p : QPair D F k, Qk.mk p = a → IsImage E p x

variable (D F)

variable (P)

end GlobalTheory.IndefiniteRowSideFullHecke.TranslatedLineGenerators
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

namespace GlobalTheory.IndefiniteRowSideFullHecke.SeparatedSymmetricModel

section BaseChange

variable {S S' : Scheme.{0}} (p : S' ⟶ S)

def dn {G : Over S} {T : Over S'} (y : T ⟶ (Over.pullback p).obj G) :
    Over.mk (T.hom ≫ p) ⟶ G :=
  Over.homMk (y.left ≫ pullback.fst G.hom p) (by
    have h := Over.w y
    dsimp at h ⊢
    rw [Category.assoc, pullback.condition, ← Category.assoc, h])

lemma dn_map {G G' : Over S} {T : Over S'} (y : T ⟶ (Over.pullback p).obj G) (f : G ⟶ G') :
    dn p (y ≫ (Over.pullback p).map f) = dn p y ≫ f := by
  ext
  have h : ((Over.pullback p).map f).left ≫ pullback.fst G'.hom p =
      pullback.fst G.hom p ≫ f.left := pullback.lift_fst _ _ _
  change (y.left ≫ ((Over.pullback p).map f).left) ≫ pullback.fst G'.hom p =
    (y.left ≫ pullback.fst G.hom p) ≫ f.left
  rw [Category.assoc, Category.assoc, h]

variable {G : Over S} [GrpObj G] [IsCommMonObj G]

instance isComm_baseChange : IsCommMonObj ((Over.pullback p).obj G) :=
  Functor.isCommMonObj_obj

lemma dn_padd {T : Over S'} (a b : T ⟶ (Over.pullback p).obj G) :
    dn p (padd _ a b) = padd G (dn p a) (dn p b) := by
  rw [padd, padd, Functor.obj.μ_def, ← Category.assoc, dn_map]
  congr 1
  apply CartesianMonoidalCategory.hom_ext
  · rw [← dn_map, Category.assoc, Functor.Monoidal.μ_fst, lift_fst, lift_fst]
  · rw [← dn_map, Category.assoc, Functor.Monoidal.μ_snd, lift_snd, lift_snd]

lemma dn_pzero (T : Over S') : dn p (pzero ((Over.pullback p).obj G) T) = pzero G _ := by
  rw [pzero, pzero, Functor.obj.η_def, ← Category.assoc, dn_map]
  congr 1
  exact toUnit_unique _ _

lemma dn_foldr {T : Over S'} {n : ℕ} (x : Fin n → (T ⟶ (Over.pullback p).obj G))
    (l : List (Fin n)) :
    dn p (l.foldr (fun k acc => padd _ (x k) acc) (pzero _ T)) =
      l.foldr (fun k acc => padd G (dn p (x k)) acc) (pzero G _) := by
  induction l with
  | nil => exact dn_pzero p T
  | cons a l ih => simp only [List.foldr_cons]; rw [dn_padd, ih]

variable {H : Over S'} [GrpObj H] [IsCommMonObj H]

def dn3 (f : H ⟶ (Over.pullback p).obj G) : Over.mk ((G3 H).hom ≫ p) ⟶ G3 G :=
  lift (dn p (x3 H 0 ≫ f)) (lift (dn p (x3 H 1 ≫ f)) (dn p (x3 H 2 ≫ f)))

omit [GrpObj G] [IsCommMonObj G] [GrpObj H] [IsCommMonObj H] in
lemma downThree_comp_proj (f : H ⟶ (Over.pullback p).obj G) (k : Fin 3) :
    dn3 p f ≫ x3 G k = dn p (x3 H k ≫ f) := by
  fin_cases k <;> simp [x3, dn3]

def bcMap (f : H ⟶ (Over.pullback p).obj G) [IsMonHom f] : CubeMap H G where
  F := (dn p f).left
  F3 := (dn3 p f).left
  e := p
  e_comm := by
    have h1 : eSec H ≫ (dn p f).left = (dn p (η[H] ≫ f)).left :=
      (Category.assoc _ _ _).symm
    have h2 : η[H] ≫ f = pzero _ (𝟙_ (Over S')) := by
      rw [IsMonHom.one_hom, pzero, toUnit_unit, Category.id_comp]
    rw [h1, h2, dn_pzero, pzero, Over.comp_left, eSec]
    congr 1
  psum_comm := fun I => by
    have h1 : (psum H (x3 H) I).left ≫ (dn p f).left = (dn p (psum H (x3 H) I ≫ f)).left :=
      (Category.assoc _ _ _).symm
    have h2 : (dn3 p f).left ≫ (psum G (x3 G) I).left = (dn3 p f ≫ psum G (x3 G) I).left := rfl
    rw [h1, h2]
    congr 1
    simp only [psum]
    rw [foldr_padd_comp, dn_foldr, ← foldr_padd_pre]
    simp only [downThree_comp_proj]


end BaseChange

section Sym

variable {S : Scheme.{0}} (G : Over S) [GrpObj G]

variable {G} {S' : Scheme.{0}} {H : Over S'} [GrpObj H]

end Sym

section IsoPull

variable {X X' Y Y' : Scheme.{0}} (L : LB X) (M : LB X')

end IsoPull

section Generic

variable (R : Type) [CommRing R] [IsDomain R]

end Generic

section Levels

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

abbrev toG (I : Ideal R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
    [IsCommMonObj G] : CubeMap (thickObj R I e G) G :=
  bcMap (thick R I e) (𝟙 (thickObj R I e G))

def toB {e : ℕ} (j : CanonicalRigidImages.GtIso D I e G) : CubeMap (thickObj R I e G) D.P.A :=
  haveI := j.q_hom
  bcMap (thick R I e) j.q




end Levels

end GlobalTheory.IndefiniteRowSideFullHecke.SeparatedSymmetricModel
end
end
