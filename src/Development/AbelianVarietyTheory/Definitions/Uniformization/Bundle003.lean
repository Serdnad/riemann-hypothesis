module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
public import Development.AbelianVarietyTheory.Definitions.Uniformization.SmulOneSecEqZeroIff
public import Mathlib.NumberTheory.Padics.PadicIntegers
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UU
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

structure Match (U : PreU I D.toPre A G) (U' : UnifPre I D A G) : Prop where
  gen : U'.gen = U.gen
  LG : U'.LG = U.P.L
  cub : HEq U'.cubG U.P.c
  sym : HEq U'.symG U.P.sym
  gt : U'.gt = U.gt
  w : HEq U'.w U.w

def SameG {L : LB G.left} {k : ℕ} (σ : H0 L k)
    (σ' : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => (snd (𝟙_ (Over (Spec (CommRingCat.of R)))) G).left) (fun _ => (k : ℤ)))) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over (Spec (CommRingCat.of R))) ⊗ G).left) (z : Z) (J), Good L z J →
    sval σ' r z J = sval σ (r ≫ (snd _ G).left) z J

def SameB {D : DegPre R} {k : ℕ} (f : ∀ α, D.SecB k α) (f' : ∀ α, SecBT D (𝟙_ _) k α) : Prop :=
  ∀ (α : D.X) (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over (Spec (CommRingCat.of R))) ⊗ D.P.A).left) (z : Z) (J), Good D.P.L z J →
    sval (f' α) r z J = sval (f α) (r ≫ (snd _ D.P.A).left) z J

def PreU.SameK {D : DegPre R} (U : PreU I D A G) {k : ℕ}
    (σ : LB.Sec (LB.LinComb U.P.L.L (K := Fin 1) (fun _ => pullback.fst G.hom (jK R)) (fun _ => (k : ℤ))))
    (t : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) (FractionRing R)))) : Prop :=
  ∀ (Z : Scheme.{0}) (rA : Z ⟶ (TFK (R := R) (FractionRing R) ⊗ A.A).left) (y : Z ⟶ ((Over.pullback (jK R)).obj G).left),
    rA ≫ (snd _ A.A).left = y ≫ U.gen.hom.left → ∀ (z : Z) (JA) (JG), Good A.L z JA → Good U.P.L.L z JG →
      (gw U.wA y z (JG (y ≫ pullback.fst G.hom (jK R))) (fun _ => JA (y ≫ U.gen.hom.left))).val ^ k *
          sval (L := A.L) (φ := fun _ : Fin 1 => (snd (TFK (R := R) (FractionRing R)) A.A).left) (ε := fun _ => (k : ℤ)) t rA z JA =
        sval σ y z JG
end GlobalTheory.UU
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.UU

local instance (priority := high) grpObjHidaThick {R : Type} [CommRing R] (I : Ideal R) (e : ℕ)
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G] : GrpObj (thickObj R I e G) :=
  letI : (Over.pullback (thick R I e)).Monoidal :=
    (Over.instBraidedPullback (f := thick R I e)).toMonoidal
  Functor.grpObjObj (F := Over.pullback (thick R I e))

instance (priority := high) thickComm {R : Type} [CommRing R] (I : Ideal R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
    [IsCommMonObj G] : IsCommMonObj (thickObj R I e G) := inferInstance

structure Lev {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
    (P : CP G) (X : Type) [AddCommGroup X] (e : ℕ) where
  Q : TQ (thickObj R I e G) X
  Pe : CP (thickObj R I e G)
  lev : IsLevelCP I e Pe P
  D : Q.Desc Pe

def Lev.B {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
    {P : CP G} {X : Type} [AddCommGroup X] {e : ℕ} (l : Lev I P X e) : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := l.Q.B

def IsCPPullback {S S' : Scheme.{0}} {B' : Over S'} {B : Over S} [GrpObj B'] [IsCommMonObj B'] [GrpObj B] [IsCommMonObj B]
    (M' : CP B') (M : CP B) (f : S' ⟶ S) (β : B'.left ⟶ B.left) : Prop :=
  ∃ h : IsGrpPullback B' B f β, ∃ v, IsCPMap M' M f β h.1.w v
variable {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V]

structure HidaSetting (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (A : PolAV (Spec (CommRingCat.of (FractionRing V))))
    (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] where
  cdvr : CDVR V
  semi : IsSemiAbelian G
  gen : (Over.pullback (jK V)).obj G ≅ A.A
  gen_hom : IsMonHom gen.hom
  P : CP G
  wA : LB.Iso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK V)))
  wA_gen : wA.IsGen
  X : Type
  [addX : AddCommGroup X]
  [freeX : Module.Free ℤ X]
  [finX : Module.Finite ℤ X]
  Q₀ : TQ (thickObj V (IsLocalRing.maximalIdeal V) 0 G) X
  P₀ : CP (thickObj V (IsLocalRing.maximalIdeal V) 0 G)
  lev₀ : IsLevelCP _ 0 P₀ P
  even₀ : ∃ σ : CubTriv P₀.c Q₀.i, σ.Even
attribute [instance] HidaSetting.addX HidaSetting.freeX HidaSetting.finX
variable {A : PolAV (Spec (CommRingCat.of (FractionRing V)))} {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G]

structure Tower (s : HidaSetting V A G) where
  l : ∀ e, Lev (IsLocalRing.maximalIdeal V) s.P s.X e
  tor : ∀ e, TorusCompat (thickTrans V _ e) (thickMap V _ e G) (l e).Q.i (l (e + 1)).Q.i
  β : ∀ e, (l e).Q.B.left ⟶ (l (e + 1)).Q.B.left
  β_pb : ∀ e,
    letI := grpObjHidaThick (IsLocalRing.maximalIdeal V) e G
    letI := grpObjHidaThick (IsLocalRing.maximalIdeal V) (e + 1) G
    letI := thickComm (IsLocalRing.maximalIdeal V) e G
    letI := thickComm (IsLocalRing.maximalIdeal V) (e + 1) G
    IsCPPullback (l e).D.M (l (e + 1)).D.M (thickTrans V _ e) (β e)
  β_q : ∀ e, (l e).Q.q.left ≫ β e = thickMap V _ e G ≫ (l (e + 1)).Q.q.left

structure Tower.Alg {s : HidaSetting V A G} (t : Tower s) where
  B : Over (Spec (CommRingCat.of V))
  [grp : GrpObj B]
  [comm : IsCommMonObj B]
  isAb : IsAbelianScheme B
  M : CP B
  ample : RelAmple B M.L.L
  b : ∀ e, (t.l e).Q.B.left ⟶ B.left
  b_pb : ∀ e, IsCPPullback (t.l e).D.M M (thick V _ e) (b e)
  b_β : ∀ e, t.β e ≫ b (e + 1) = b e
attribute [instance] Tower.Alg.grp Tower.Alg.comm

def AllSet (p : ∀ {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {A : PolAV (Spec (CommRingCat.of (FractionRing V)))}
    {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G], HidaSetting V A G → Prop) : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (A : PolAV (Spec (CommRingCat.of (FractionRing V))))
    (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (s : HidaSetting V A G), p s

def Tower.Alg.RepWt {s : HidaSetting V A G} {t : Tower s} (a : t.Alg) (c : 𝟙_ _ ⟶ a.B) (χ : s.X) (e : ℕ) : Prop :=
  ∃ u : LB.Gen ((LB.LinComb a.M.L.L (K := Fin 2) ![((toUnit a.B ≫ c) * 𝟙 a.B).left, 𝟙 a.B.left] ![-1, 1]).pull
      ((t.l e).Q.q.left ≫ a.b e)), u.IsGen ∧ ∀ j, IsWt (t.l e).Q.i _ (u.s j).val χ
end GlobalTheory.UU
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.UU

def kap0 {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L)
    (sym : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])) {T : Over S} (z : T.left)
    (J : (T.left ⟶ G.left) → L.L.ι) (x y : T ⟶ G) : (T.left.presheaf.stalk z)ˣ :=
  cubV c z J x y y⁻¹ * (val sym y.left z J)⁻¹ *
    val (L := L.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) L.rig T.hom z J ^ 2
section
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

abbrev cT (D : DegPre R) (T : Over (Spec (CommRingCat.of R))) (χ : D.X) : T ⟶ D.P.A := toUnit T ≫ D.c χ

def rigV (D : DegPre R) {T : Over (Spec (CommRingCat.of R))} (z : T.left) (J : (T.left ⟶ D.P.A.left) → D.P.L.ι) :
    (T.left.presheaf.stalk z)ˣ := val (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig T.hom z J

def kapV (D : DegPre R) (a b : D.X) {T : Over (Spec (CommRingCat.of R))} (z : T.left)
    (J : (T.left ⟶ D.P.A.left) → D.P.L.ι) (x y : T ⟶ D.P.A) : (T.left.presheaf.stalk z)ˣ :=
  kap0 D.cub D.sym z J x y * cubV D.cub z J (cT D T a) (cT D T b) x * cubV D.cub z J (cT D T b) y y⁻¹ *
    (cubV D.cub z J (cT D T a) x y * cubV D.cub z J (cT D T b) x y⁻¹ * cubV D.cub z J (cT D T (a - b)) (cT D T b) y)⁻¹

def PreU.AddG (U : PreU I D A G) (θ : U.SecGT (𝟙_ _) 1) (r : R) {n : ℕ} (σ σ' : Fin n → U.SecGT (𝟙_ _) 2) : Prop :=
  ∀ (T : Over (Spec (CommRingCat.of R))) (x y : T ⟶ G) (z : T.left) (J), Good U.P.L.L z J →
    ∑ i, sval (σ i) (lift (toUnit T) x).left z J * sval (σ' i) (lift (toUnit T) y).left z J =
      gs (𝟙 _) z ⊤ (scal T.hom r) * (kap0 U.P.c U.P.sym z J x y).val *
        (sval θ (lift (toUnit T) (x * y)).left z J * sval θ (lift (toUnit T) (x * y⁻¹)).left z J)

def AddB (D : DegPre R) (T₀ : Over (Spec (CommRingCat.of R))) (f₀ : ∀ α, SecBT D T₀ 1 α) (r : R) {n : ℕ}
    (f f' : Fin n → ∀ α, SecBT D T₀ 2 α) : Prop :=
  ∀ (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ T₀) (x y : T ⟶ D.P.A) (z : T.left) (J), Good D.P.L z J →
    (∀ a b α β : D.X, α = a + b → β = a - b →
      ∑ i, sval (f i α) (lift ρ x).left z J * sval (f' i β) (lift ρ y).left z J =
        gs (𝟙 _) z ⊤ (scal T.hom r) * (kapV D a b z J x y).val *
          (sval (f₀ a) (lift ρ (x * y)).left z J * sval (f₀ b) (lift ρ (x * y⁻¹)).left z J)) ∧
    ∀ α β : D.X, (¬ ∃ a b, α = a + b ∧ β = a - b) →
      ∑ i, sval (f i α) (lift ρ x).left z J * sval (f' i β) (lift ρ y).left z J = 0

def PreU.Theta (U : PreU I D A G) (θ : U.SecGT (𝟙_ _) 1) (f : ∀ α, SecBT D (𝟙_ _) 1 α) : Prop :=
  U.ExpT (𝟙_ _) 1 θ f ∧ ∃ j, θ.f j ≠ 0

def PsiRel (D : DegPre R) (T₀ : Over (Spec (CommRingCat.of R))) (f : ∀ α, SecBT D T₀ 1 α) : Prop :=
  ∀ (χ : D.X) (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ T₀) (κ : T ⟶ TK R) (y : T ⟶ D.P.A) (z : T.left) (J),
    Good D.P.L z J → sval (f χ) (lift ρ y).left z J =
      (val (D.psi χ) κ.left z J * rigV D z J).val * sval (f 0) (lift ρ (y * cT D T χ)).left z J

def setPsi (D : DegPre R)
    (ψ : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => ptK (D.c χ)) (fun _ => -1))) (h : ∀ χ, (ψ χ).IsGen) :
    DegPre R := { D with psi := ψ, psi_gen := h }

def PsiScal (D : DegPre R)
    (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1)))
    (a : D.X → (FractionRing R)ˣ) : Prop :=
  ∀ χ, (ga χ).IsGen ∧ ∀ (T : Over (Spec (CommRingCat.of R))) (κ : T ⟶ TK R) (z : T.left) (J), Good D.P.L z J →
    (val (D.psi χ) κ.left z J).val = gs (𝟙 _) z ⊤ (scal κ.left (a χ).val) * (val (ga χ) (toUnit T).left z J).val
end

def AddA {S : Scheme.{0}} (P : PolAV S) (T₀ : Over S) (th : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) T₀)) {n : ℕ}
    (t t' : Fin n → LB.Sec (LPow P.A P.L ((2 : ℕ) : ℤ) T₀)) : Prop :=
  ∃ κ : LB.Gen (LB.LinComb P.L (K := Fin 4)
      ![(snd T₀ (P.A ⊗ P.A) ≫ fst P.A P.A).left, (snd T₀ (P.A ⊗ P.A) ≫ snd P.A P.A).left,
        (snd T₀ (P.A ⊗ P.A) ≫ (fst P.A P.A * snd P.A P.A)).left,
        (snd T₀ (P.A ⊗ P.A) ≫ (fst P.A P.A * (snd P.A P.A)⁻¹)).left] ![2, 2, -1, -1]), κ.IsGen ∧
    ∀ (T : Over S) (ρ : T ⟶ T₀) (x y : T ⟶ P.A) (z : T.left) (J), Good P.L z J →
      ∑ i, sval (L := P.L) (φ := fun _ : Fin 1 => (snd T₀ P.A).left) (ε := fun _ => ((2 : ℕ) : ℤ)) (t i) (lift ρ x).left z J *
          sval (L := P.L) (φ := fun _ : Fin 1 => (snd T₀ P.A).left) (ε := fun _ => ((2 : ℕ) : ℤ)) (t' i) (lift ρ y).left z J =
        (val κ (lift ρ (lift x y)).left z J).val *
          (sval (L := P.L) (φ := fun _ : Fin 1 => (snd T₀ P.A).left) (ε := fun _ => ((1 : ℕ) : ℤ)) th (lift ρ (x * y)).left z J *
            sval (L := P.L) (φ := fun _ : Fin 1 => (snd T₀ P.A).left) (ε := fun _ => ((1 : ℕ) : ℤ)) th (lift ρ (x * y⁻¹)).left z J)

abbrev EA {S : Scheme.{0}} (P : PolAV S) {F : Type} [Field F] (p : Spec (CommRingCat.of F) ⟶ S) (k : ℕ) : Type :=
  SecMod (F := F) (fst (Over.mk p) P.A).left (LPow P.A P.L (k : ℤ) (Over.mk p))

abbrev WB {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ)
    (α : D.X) : Type :=
  SecMod (F := F) (fst (TF (R := R) F) D.P.A).left (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k))
end GlobalTheory.UU
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.UU

def AllPre (p : ∀ {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {D : DegPre V}
    {A : PolAV (Spec (CommRingCat.of (FractionRing V)))} {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G],
    PreU (IsLocalRing.maximalIdeal V) D A G → Prop) : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ (D : DegPre V)
    (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G]
    (U : PreU (IsLocalRing.maximalIdeal V) D A G), p U

abbrev TA (V W : Type) [CommRing V] [CommRing W] [Algebra V W] : Over (Spec (CommRingCat.of V)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W)))

abbrev Kbar (V : Type) [CommRing V] [IsDomain V] : Type := AlgebraicClosure (FractionRing V)

def FinExt (V W : Type) [CommRing V] [IsLocalRing V] [CommRing W] [IsLocalRing W] [Algebra V W] : Prop :=
  Module.Finite V W ∧ Module.Free V W ∧ IsDomain W ∧ IsLocalHom (algebraMap V W) ∧
    IsAdicComplete ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) W

theorem finExt_self (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V]
    (h : IsAdicComplete (IsLocalRing.maximalIdeal V) V) : FinExt V V := by
  have hmap : (IsLocalRing.maximalIdeal V).map (algebraMap V V) = IsLocalRing.maximalIdeal V := by
    rw [show algebraMap V V = RingHom.id V from rfl, Ideal.map_id]
  refine ⟨inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · rw [show algebraMap V V = RingHom.id V from rfl]
    infer_instance
  · rw [hmap]
    exact h

theorem cdvr_padicInt (p : ℕ) [Fact p.Prime] : CDVR ℤ_[p] := by
  refine ⟨inferInstance, inferInstance, inferInstance⟩

section
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

def PreU.PullG (U : PreU I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] {T : Over (Spec (CommRingCat.of R))}
    (φ : TF (R := R) F ⟶ T) (k : ℕ) (σ : U.SecGT T k) (t : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F))) : Prop :=
  ∀ (Z : Scheme.{0}) (rA : Z ⟶ (TFK (R := R) F ⊗ A.A).left) (y : Z ⟶ ((Over.pullback (jK R)).obj G).left)
    (rG : Z ⟶ (T ⊗ G).left), rA ≫ (snd _ A.A).left = y ≫ U.gen.hom.left →
    rG ≫ (snd _ G).left = y ≫ pullback.fst G.hom (jK R) → rG ≫ (fst T G).left = rA ≫ (fst (TFK (R := R) F) A.A).left ≫ φ.left →
    ∀ (z : Z) (JA) (JG), Good A.L z JA → Good U.P.L.L z JG →
      (gw U.wA y z (JG (y ≫ pullback.fst G.hom (jK R))) (fun _ => JA (y ≫ U.gen.hom.left))).val ^ k *
          sval (L := A.L) (φ := fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) (ε := fun _ => (k : ℤ)) t rA z JA =
        sval σ rG z JG

def PullB (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] {T : Over (Spec (CommRingCat.of R))}
    (φ : TF (R := R) F ⟶ T) (k : ℕ) (f : ∀ α, SecBT D T k α) (s : Raw D F k) : Prop :=
  ∀ (α : D.X) (z : (DegPre.BF D F).left) (J), Good D.P.L z J →
    sval (s α) (𝟙 _) z J = sval (f α) (φ ▷ D.P.A).left z J

def PreU.SamePt (U : PreU I D A G) {F : Type} [Field F] [Algebra (FractionRing R) F] (x : TFK (R := R) F ⟶ A.A)
    (y : TF (R := R) F ⟶ G) : Prop := x.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) = y.left

def PreU.Supp (U : PreU I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (α : D.X) : Prop :=
  ∃ t s, U.ExpF F k t s ∧ ∃ j, (s α).f j ≠ 0

def PreU.FE (U : PreU I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) : Prop :=
  ∀ t s, U.ExpF F k t s → DegPre.FamFE D F k s

def PreU.Acts (U : PreU I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (y : D.X) (g : GtPtF D F)
    (x : TFK (R := R) F ⟶ A.A) : Prop :=
  x ^ k = 1 ∧ ∀ θ : ThetaGrp A.A A.L (k : ℤ) (TFK (R := R) F), θ.pt = x →
    ∃ w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g.b) (DegPre.lineε k)), w.IsGen ∧
      ∀ t t' s s', U.ExpF F k t s → U.ExpF F k t' s' → IsActOf A.A A.L (k : ℤ) θ t t' → PhiRaw D F k y g w s s'

def GtTors (D : DegPre R) {F : Type} [Field F] [Algebra (FractionRing R) F] (k : ℕ) (g : GtPtF D F) : Prop :=
  ∃ h, GtPtF.IsNsmul k g h ∧ h.IsZero

def addε : Fin 10 → ℤ := ![1, 1, -1, 1, 1, -1, -1, 1, -1, 1]

end
end GlobalTheory.UU
end
end
