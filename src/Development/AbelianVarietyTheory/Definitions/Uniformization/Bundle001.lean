module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle009
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.UT.Cl
section
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

def Torsion (U : Unif I D A G) : Prop :=
  ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F], ∀ (k : ℕ), 1 ≤ k → ∃ f, Tors U.toUnifPre F k f ∧ ∀ p, f p ^ k = 1

def Galois (U : Unif I D A G) : Prop :=
  ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F], ∀ (F' : Type) [Field F'] [IsAlgClosed F'] [Algebra (FractionRing R) F'] (σ : F →ₐ[FractionRing R] F') (k : ℕ), 1 ≤ k →
    ∀ p : QkPt D.toPre F k, (∃ p' : QkPt D.toPre F' k, QkExt σ.toRingHom p p') ∧
      (∀ x : TFK (R := R) F ⟶ A.A, ∃ x' : TFK (R := R) F' ⟶ A.A, x'.left = spMap σ.toRingHom ≫ x.left) ∧
      ∀ (p' : QkPt D.toPre F' k) (x : TFK (R := R) F ⟶ A.A) (x' : TFK (R := R) F' ⟶ A.A), QkExt σ.toRingHom p p' →
        x'.left = spMap σ.toRingHom ≫ x.left → (QkToAkU U.toUnifPre F k p x ↔ QkToAkU U.toUnifPre F' k p' x')

def SymFrame (U : Unif I D A G) : Prop :=
  ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F], ∀ (N : ℕ), Odd N → ∀ p : QkPt D.toPre F N,
    ((∃ w, TXFrame N p w) ∧ ∀ w w', TXFrame N p w → TXFrame N p w' →
      ∀ z J, Good D.toPre.P.L z J → val w (𝟙 _) z J = val w' (𝟙 _) z J) ∧
    ∀ x, QkToAkU U.toUnifPre F N p x → (∃ θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F), SymLift A.A A.L N N x θ) ∧
      ∀ (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F)), SymLift A.A A.L N N x θ → ∀ (w₀ : W0 U.toUnifPre), w₀.IsGen →
        ∀ w, TXFrame N p w → ∀ t t' s s', U.ExpandsF F N w₀ t s → U.ExpandsF F N w₀ t' s' → IsActOf A.A A.L N θ t t' →
          PhiRel D.toPre F N p w s s'

def Functorial (U : Unif I D A G) : Prop :=
  (∀ (aG : G ⟶ G) (aA : A.A ⟶ A.A), IsMonHom aG → IsMonHom aA → (Over.pullback (jK R)).map aG ≫ U.gen.hom = U.gen.hom ≫ aA → ∃ E : EndU U.toUnifPre, E.aG = aG ∧ E.aA = aA) ∧
  ∀ E E' : EndU U.toUnifPre, LBIso (cubeLB G ![fst G G ≫ E.aG, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ E'.aG] U.LG.L) →
    (RosatiAdj A.A A.L E.aA E'.aA ∧ RosatiAdj D.toPre.P.A D.toPre.P.L E.aB E'.aB ∧
      (∀ χ, D.toPre.c (E.h χ) = D.toPre.c χ ≫ E'.aB) ∧ ∀ χ, D.toPre.c (E'.h χ) = D.toPre.c χ ≫ E.aB) ∧
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F], (∀ g : GtPtF D.toPre F, ∃! g', E.Act g g') ∧
      (∀ y (g g' : GtPtF D.toPre F), GtPtF.IsIota y g → E.Act g g' → GtPtF.IsIota (E'.h y) g') ∧
      ∀ (k : ℕ), 1 ≤ k → ∀ (p p' : QkPt D.toPre F k) x, p'.y = E'.h p.y → E.Act p.g p'.g → QkToAkU U.toUnifPre F k p x →
        QkToAkU U.toUnifPre F k p' (x ≫ E.aA)

def Determined (U : Unif I D A G) : Prop :=
  ∀ (D' : DegData R I) (A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G' : Over (Spec (CommRingCat.of R))) [GrpObj G']
    [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif I D' A' G') (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre),
    ∃ (ψ : G' ≅ G) (bc : G' ≅ (Over.pullback (specOf (RingHom.id R))).obj G) (φ : A'.A ≅ A.A), IsMonHom ψ.hom ∧ IsMonHom bc.hom ∧
      bc.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id R)) = ψ.hom.left ∧ IsPullUnif (RingHom.id R) hD bc U U' ∧
      IsMonHom φ.hom ∧ (Over.pullback (jK R)).map ψ.hom ≫ U.gen.hom = U'.gen.hom ≫ φ.hom ∧ LBIso A'.L (A.L.pull φ.hom.left)

def Balanced (U : Unif I D A G) : Prop :=
  (∀ (O : Type) [CommRing O] [StarRing O] (ιA : A.OAct O) (ιG : RingAct G O), (∀ a, (Over.pullback (jK R)).map (ιG.act a) ≫ U.gen.hom = U.gen.hom ≫ ιA.act a) → (∀ a, LBIso (cubeLB G ![fst G G ≫ ιG.act a, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ ιG.act (star a)] U.LG.L)) → ∃ (_ : Module O D.toPre.X) (ιD : D.toPre.OAct O), U.toUnifPre.OLinear O ιD ιA ιG) ∧
  ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (ιD : D.toPre.OAct O) (ιA : A.OAct O) (ιG : RingAct G O), U.toUnifPre.OLinear O ιD ιA ιG → (∀ a, LBIso (cubeLB G ![fst G G ≫ ιG.act a, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ ιG.act (star a)] U.LG.L)) → ∀ (w₀ : O) (ν : ℕ), w₀ + star w₀ = 1 → w₀ * star w₀ = (ν : O) → 1 ≤ ν → Even ν → LBIso U.LG.L (cubeLB G ![𝟙 G, ιG.act w₀] U.LG.L) → TraceFormTwistIso D.toPre ιD w₀
end

end GlobalTheory.UT.Cl
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.UT
section
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
  {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v)

def GenV {X : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → ((TF (R := V) F).left ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (r : ℚ) : Prop :=
  ∃ φ₀ : K → ((TWM.TO hϖ hv).left ⟶ X), (∀ i, φ i = (TWM.ιS hϖ hv).left ≫ φ₀ i) ∧
    ∃ t₀ : LB.Gen (LB.LinComb L φ₀ ε), t₀.IsGen ∧ ∃ x : F, v x = (r : WithTop ℚ) ∧
      ∀ z J, Good L z J → (val t (𝟙 _) z J).val = cst F z x * (val t₀ (TWM.ιS hϖ hv).left z J).val

def GtV {D : DegPre V} (g : GtPtF D F) (l : D.X → ℚ) : Prop := ∀ χ, GenV hϖ hv (g.s χ) (l χ)
end

def SumV {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) {Ix : Type} (x : Ix → F) (s : F) : Prop :=
  ∀ q : ℚ, ∃ S : Finset Ix, ∀ T : Finset Ix, S ⊆ T → (q : WithTop ℚ) ≤ v (s - ∑ i ∈ T, x i)

def NullV {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) {Ix : Type} (x : Ix → F) : Prop :=
  ∀ q : ℚ, {i | v (x i) < (q : WithTop ℚ)}.Finite

def Prim {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ)
    {F : Type} [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)) {k : ℕ} (s : Fam D.toPre F k) : Prop :=
  NuGe D Q F v k s 0 ∧ ∀ r : ℚ, 0 < r → ¬ NuGe D Q F v k s r

def AllDV (p : ∀ {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (_ : Irreducible ϖ)
    (D : DegData V (maximalIdeal V)) (_ : D.toPre.X → ℤ) {F : Type} [Field F] [Algebra (FractionRing V) F]
    {v : AddValuation F (WithTop ℚ)} (_ : ValOver ϖ F v), Prop) : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V →
    ∀ (ϖ : V) (hϖ : Irreducible ϖ) (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), QForm.IsQ D.toPre ϖ Q →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)) (hv : ValOver ϖ F v),
      p hϖ D Q hv

def AllUV (p : ∀ {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (_ : Irreducible ϖ)
    {D : DegData V (maximalIdeal V)} (_ : D.toPre.X → ℤ) {F : Type} [Field F] [Algebra (FractionRing V) F]
    {v : AddValuation F (WithTop ℚ)} (_ : ValOver ϖ F v) {A : PolAV (Spec (CommRingCat.of (FractionRing V)))}
    {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G], Unif (maximalIdeal V) D A G → Prop) : Prop :=
  AllDV fun {V} _ _ _ {_} hϖ D Q {_} _ _ {_} hv => ∀ (A : PolAV (Spec (CommRingCat.of (FractionRing V))))
    (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G →
    ∀ U : Unif (maximalIdeal V) D A G, p hϖ Q hv U

def ThC {R : Type} [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R))))
    {F : Type} [Field F] [Algebra (FractionRing R) F] (ρ : LB.Gen (A.L.pull (eSec A.A))) (m : ℕ) (th : SecA A F 1)
    (x : TFK (R := R) F ⟶ A.A) (t : SecA A F (m ^ 2)) (c : F) : Prop :=
  ∃ (α : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(snd (TFK (R := R) F) A.A).left, (snd (TFK (R := R) F) A.A ^ m).left]
      ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)])) (s₁ : SecA A F (m ^ 2)) (θ : ThetaGrp A.A A.L ((m ^ 2 : ℕ) : ℤ) (TFK (R := R) F)),
    α.IsGen ∧ LB.Gen.Corr A.L _ _ _ _ (LB.pullGen A.L _ _ α (ptSecT A.A 1).left) (rigT A.A A.L ρ (TFK (R := R) F) (((m ^ 2 : ℕ) : ℤ) - 1)) ∧
    IsTwistPull A.A A.L (mulT A.A _ m) (snd _ A.A ^ m) (lift_snd _ _) ((m ^ 2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α th s₁ ∧
    SymLift A.A A.L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) x θ ∧ IsActOf A.A A.L ((m ^ 2 : ℕ) : ℤ) θ s₁ t ∧
    ∀ z J, Good A.L z J → sA t (ptSecT A.A 1).left z J =
      @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z c) * (val (rigT A.A A.L ρ (TFK (R := R) F) ((m ^ 2 : ℕ) : ℤ)) (𝟙 _) z J).val
end GlobalTheory.UT
end
end
