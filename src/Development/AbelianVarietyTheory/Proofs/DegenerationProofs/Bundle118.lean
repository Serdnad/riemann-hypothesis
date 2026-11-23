module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaSystemOfPolarisedLevel
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaModelCoordinatesLocalBasis
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LinearIndependentOfIsExtension
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle115
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyTestModelToClosure
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CubicalBundleRelAmpleOfAmpleFibres
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle113
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle047
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle114
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle112
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_thetaSystem_of_polarised_level : Laws → Laws2 → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (R : Subalgebra o Ω), R.FG → (∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, x = a / b) → ∀ (P : PolAV (Sp R)) (n k j : ℕ) (ze : oˣ), n.Prime → Odd n → 2 ≤ k → 1 ≤ j → IsUnit (n : o) → HypS P.A P.L → ∀ lev : Out.Level P ((n ^ j * (n ^ k) ^ 2) ^ 2) (unitOn (Units.map (algebraMap o R).toMonoidHom ze)), ∃ (S : ThetaSys o Ω) (ρ : S.Real) (h : R ≤ S.R) (φ : ρ.P.A.left ⟶ P.A.left), S.ζ = ze ∧ S.N = (n ^ k) ^ 2 ∧ S.r = n ^ j ∧ S.g = P.g ∧ IsGrpPullback ρ.P.A P.A (spMap (Subalgebra.inclusion h).toRingHom) φ ∧ LBIso ρ.P.L (P.L.pull φ) ∧ ∀ (i : Fin S.g) (i₁ i₂ : Fin (2 * P.g)), (i₁ : ℕ) = i → (i₂ : ℕ) = i + P.g → (ρ.pt (Pi.single (.inl i) 1)).left ≫ φ = spMap (Subalgebra.inclusion h).toRingHom ≫ (lev.pt i₁ ^ (S.r * S.N)).left ∧ (ρ.pt (Pi.single (.inr i) 1)).left ≫ φ = spMap (Subalgebra.inclusion h).toRingHom ≫ (lev.pt i₂ ^ (S.r * S.N)).left := by
  first | exact @GlobalTheory.ThetaReal.exists_thetaSys_real | exact GlobalTheory.ThetaReal.exists_thetaSys_real | (intros; apply GlobalTheory.ThetaReal.exists_thetaSys_real <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.thetaModel_coordinates_local_basis : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Q : Clos ρ M U₀ EE) (ex : Q.Ext) (Z : ZHPre ρ M U₀), (∃ e : Z.G.left ≅ Q.G.toScheme, e.hom ≫ Q.G.ι ≫ Q.P.hom = Z.G.hom ∧ Z.u₀ = Q.u₀ ∧ HEq (Z.φ ≫ e.hom) ex.a) → BaseFacts S M U₀ EE → Z.Ab → (∀ l, ∀ z ∈ Q.W l, IsClosed ({z} : Set M.Z) → ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ M.Z), Set.range x = {z} ∧ ∀ c : S.J → K, (∀ (g : Sp K ⟶ (Q.P.hom ⁻¹ᵁ Q.W l).toScheme) (j), Set.range (g ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι) ⊆ Q.G → g ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom = x → ∑ i, c i * valF g _ ((Q.σ l i).f j) = 0) → c = 0) → Z.SecO EE := by
  first | exact @GlobalTheory.ZH.SecCoord.secO | exact GlobalTheory.ZH.SecCoord.secO | (intros; apply GlobalTheory.ZH.SecCoord.secO <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.theta_test_power_integral : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (a : u.PtC), ∃ k : ℕ, 1 ≤ k ∧ u.Int (a ^ k) := by
  first | exact @GlobalTheory.ZH.exists_int_pow | exact GlobalTheory.ZH.exists_int_pow | (intros; apply GlobalTheory.ZH.exists_int_pow <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.OneBasis
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex

section Geo
variable {S S' : Scheme.{0}}

def RigPull (G' : Over S') [GrpObj G'] (G : Over S) [GrpObj G] (f : S' ⟶ S) (φ : G'.left ⟶ G.left) {L' : LB G'.left}
    {L : LB G.left} (w : LB.Iso L' (L.pull φ)) (ρ' : LB.Gen (L'.pull (eSec G'))) (ρ : LB.Gen (L.pull (eSec G))) : Prop :=
  IsGrpPullback G' G f φ ∧ w.IsGen ∧ ρ'.IsGen ∧
    PMaps w (K := PUnit) (fun _ => eSec G') (fun _ => eSec G) (fun _ => 1) ρ' ρ f

def Thru {G' : Over S'} {G : Over S} {φ : G'.left ⟶ G.left} {L' : LB G'.left} {L : LB G.left} (w : LB.Iso L' (L.pull φ))
    (k : ℕ) {T' : Over S'} {T : Over S} (h : T'.left ⟶ T.left) (s : LB.Sec (LPow G L (k : ℤ) T))
    (s' : LB.Sec (LPow G' L' (k : ℤ) T')) : Prop :=
  ∀ (Z : Scheme.{0}) (r' : Z ⟶ (T' ⊗ G').left) (r : Z ⟶ (T ⊗ G).left),
    r ≫ (fst T G).left = r' ≫ (fst T' G').left ≫ h → r ≫ (snd T G).left = r' ≫ (snd T' G').left ≫ φ →
    ∀ (z : Z) (J) (J'), Good L z J → Good L' z J' →
      sval (L := L) (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => (k : ℤ)) s r z J =
        (GlobalTheory.ConstFam.wVal w z J J' (r' ≫ (snd T' G').left)).val ^ k *
          sval (L := L') (φ := fun _ : Fin 1 => (snd T' G').left) (ε := fun _ => (k : ℤ)) s' r' z J'

abbrev fnR {R : Type} [CommRing R] (x : R) : Γ(Sp R, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom x

def FrameAt (G : Over S) (L : LB G.left) (N : ℕ) {K : Type} [Field K] (x : Sp K ⟶ S) {W : Type} [CommRing W] [IsDomain W]
    (gam : K →+* FractionRing W) (χ : Sp W ⟶ S) (h : spMap gam ≫ x = jK W ≫ χ) {n : ℕ}
    (b : Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk x))) : Prop :=
  ∃ b' : Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk χ)), BasisAlong G L N (𝟙 _) b' ∧
    ∀ i, ∃ s : LB.Sec (LPow G L (N : ℤ) (Over.mk (jK W ≫ χ))),
      Lin G L N (Over.homMk (spMap gam) h : Over.mk (jK W ≫ χ) ⟶ Over.mk x) (fun _ : Fin 1 => b i) (fun _ => 1) s ∧
      Lin G L N (Over.homMk (jK W) rfl : Over.mk (jK W ≫ χ) ⟶ Over.mk χ) (fun _ : Fin 1 => b' i) (fun _ => 1) s

def BasisBy (G : Over S) (L : LB G.left) (N : ℕ) {K : Type} [Field K] (x : Sp K ⟶ S) {W : Type} [CommRing W] [IsDomain W]
    (gam : K →+* FractionRing W) (χ : Sp W ⟶ S) (h : spMap gam ≫ x = jK W ≫ χ) {n : ℕ}
    (τ : Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk x))) (B : Matrix (Fin n) (Fin n) (FractionRing W)) : Prop :=
  ∃ b : Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk χ)), BasisAlong G L N (𝟙 _) b ∧
    ∀ i, ∃ s : LB.Sec (LPow G L (N : ℤ) (Over.mk (jK W ≫ χ))),
      Lin G L N (Over.homMk (spMap gam) h : Over.mk (jK W ≫ χ) ⟶ Over.mk x) τ (fun j => fnR (B i j)) s ∧
      Lin G L N (Over.homMk (jK W) rfl : Over.mk (jK W ≫ χ) ⟶ Over.mk χ) (fun _ : Fin 1 => b i) (fun _ => 1) s

def AllBasis (G : Over S) (L : LB G.left) (N : ℕ) {K : Type} [Field K] (x : Sp K ⟶ S) {n : ℕ}
    (τ : Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk x))) : Prop :=
  ∀ (K' : Type) [Field K'] (ga : K →+* K') (x' : Sp K' ⟶ S) (h : spMap ga ≫ x = x'),
    BasisAlong G L N (Over.homMk (spMap ga) h : Over.mk x' ⟶ Over.mk x) τ
end Geo

section Tables

structure Tab (K : Type) (r : ℕ) where

  Pt : Type
  [grp : CommGroup Pt]

  E : Pt → (Fin r → K) → Prop

  C : ℕ → Pt → K → Prop

  Λ : ℕ → Pt → (Fin r → K) → Prop
attribute [instance] Tab.grp
variable {K K' : Type} [Field K] [Field K'] {r : ℕ}

def Tab.Full (T : Tab K r) (N n : ℕ) : Prop :=
  (∀ x, x ^ N = 1 → ∃ a, T.E x a) ∧ (∀ j x, x ^ ((n ^ j) ^ 2) = 1 → ∃ c, T.C (n ^ j) x c) ∧
    ∀ j h, h ^ (n ^ j) = 1 → ∃ l, T.Λ (n ^ j) h l

def Tab.Uniq (T : Tab K r) (N n : ℕ) : Prop :=
  (∀ x a, T.E x a → x ^ N = 1 ∧ ∀ a', T.E x a' → a' = a) ∧
    ∀ j x c, T.C (n ^ j) x c → x ^ ((n ^ j) ^ 2) = 1 ∧ ∀ c', T.C (n ^ j) x c' → c' = c

def Tab.Map (σ : K →+* K') (T : Tab K r) (T' : Tab K' r) : Prop :=
  ∃ β : T.Pt →* T'.Pt, (∀ k y, 1 ≤ k → y ^ k = 1 → ∃ x, x ^ k = 1 ∧ β x = y) ∧
    (∀ x a, T.E x a → T'.E (β x) (σ ∘ a)) ∧ (∀ k x c, T.C k x c → T'.C k (β x) (σ c)) ∧
    ∀ k h l, T.Λ k h l → T'.Λ k (β h) (σ ∘ l)

def Tab.Hs (T : Tab K r) (O : ValuationSubring K) (k : ℕ) : Subgroup T.Pt :=
  Subgroup.closure {y | ∃ x c, T.C k x c ∧ O.valuation c = 1 ∧ y = x ^ k}

def Tab.Loc (T : Tab K r) (O : ValuationSubring K) (B : Matrix (Fin r) (Fin r) K) (n d : ℕ) (κ : K) : Prop :=
  B.det ≠ 0 ∧ (∀ j x c, T.C (n ^ j) x c → c ∈ O) ∧
  (∀ j h l, h ∈ T.Hs O (n ^ j) → T.Λ (n ^ j) h l → ∀ i, B.mulVec l i ∈ O) ∧
  (∀ a : Fin r → K, (∀ i, a i ∈ O) → (∃ i, O.valuation (a i) = 1) →
    ∃ j h, h ∈ T.Hs O (n ^ j) ∧ ∀ l, T.Λ (n ^ j) h l → O.valuation (a ⬝ᵥ B.mulVec l) = 1) ∧
  ∃ π : Fin r → K, (∀ i, π i ≠ 0) ∧ O.valuation ((∏ i, π i) ^ d) = O.valuation κ ∧
    ∀ a : Fin r → K, (∀ i, a i / π i ∈ O) ↔ Matrix.vecMul a B ∈ Submodule.span O {e | ∃ x, T.E x e}

def Tab.Near (T : Tab K r) (N n d : ℕ) (κ : K) (σ : K →+* K') (O : ValuationSubring K') (T' : Tab K' r)
    (B : Matrix (Fin r) (Fin r) K') : Prop :=
  Tab.Map σ T T' ∧ T'.Uniq N n ∧ T'.Loc O B n d (σ κ)
end Tables

section Av
variable {R : Type} [CommRing R] [IsDomain R] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {F : Type} [Field F] [Algebra (FractionRing R) F]

def Cmb {k n : ℕ} (b : Fin n → SecA A F k) (a : Fin n → F) (t : SecA A F k) : Prop :=
  ∀ j, t.f j = ∑ i, liftFun A.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (a i)) * (b i).f j

def ValAt {k : ℕ} (t : SecA A F k) (x : TFK (R := R) F ⟶ A.A)
    (e : LB.Gen (LB.LinComb A.L (Y := (TFK (R := R) F).left) (K := Fin 1) (fun _ => x.left) (fun _ => 1))) (c : F) : Prop :=
  ∀ z J, Good A.L z J → sA t (ptSecT A.A x).left z J =
    @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z c) * (val (powFrame A.A A.L x e k) (𝟙 _) z J).val

def tab (ρ : LB.Gen (A.L.pull (eSec A.A))) (m : ℕ) (θ : SecA A F 1) {r : ℕ} (τ : Fin r → SecA A F (m ^ 2)) : Tab F r where
  Pt := TFK (R := R) F ⟶ A.A
  grp := Hom.commGroup
  E x a := x ^ (m ^ 2) = 1 ∧ ∃ t c, ThC A ρ m θ x t c ∧ Cmb τ a t
  C k x c := x ^ (k ^ 2) = 1 ∧ ∃ t, ThC A ρ k θ x t c
  Λ k h l := ∃ e, IsTorsFrame A ρ k h e ∧ ∀ j, ValAt (τ j) h e (l j)

def unitGrp (v : AddValuation F (WithTop ℚ)) (ρ : LB.Gen (A.L.pull (eSec A.A))) (θ : SecA A F 1) (k : ℕ) :
    Subgroup (TFK (R := R) F ⟶ A.A) :=
  Subgroup.closure {y | ∃ x t c, x ^ (k ^ 2) = 1 ∧ ThC A ρ k θ x t c ∧ v c = 0 ∧ y = x ^ k}

def FromGt {I : Ideal R} {D : DegData R I} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
    (U : UnifPre I D A G) (k : ℕ) (x : TFK (R := R) F ⟶ A.A) : Prop :=
  ∃ p : QkPt D.toPre F k, p.y = 0 ∧ QkToAkU U F k p x

def IsBasisH {G : Over (Spec (CommRingCat.of R))} {L : LB G.left} {k n : ℕ} (σ : Fin n → H0 L k) : Prop :=
  ∀ s : H0 L k, ∃! c : Fin n → R, ∀ j, s.f j = ∑ i, resTop _ (scal G.hom (c i)) * (σ i).f j
end Av

def Adapted {X : Type} [AddCommGroup X] (k : ℕ) (Q : X → ℤ) {r : ℕ} (cls : Fin r → X) (mu : ℕ) : Prop :=
  (∀ i z, Q (cls i) ≤ Q (cls i + k • z)) ∧ (∀ i i', (∃ z, cls i = cls i' + k • z) → cls i = cls i') ∧
    (∀ α, ∃ i z, α = cls i + k • z) ∧ ∀ i₀, Nat.card {i // cls i = cls i₀} = mu

section Dvr
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V))
  (Q : D.toPre.X → ℤ)

open Classical in
def AdFam (k : ℕ) {r : ℕ} (cls : Fin r → D.toPre.X) (mu : ℕ) (f : Fin r → ∀ α, D.toPre.SecB k α) : Prop :=
  Adapted k Q cls mu ∧ (∀ i, ∃ s : Fam D.toPre (FractionRing V) k, GlobalTheory.ZH.FamOf D.toPre _ (f i) s) ∧
    (∀ i α, (∀ z, α ≠ cls i + k • z) → ∀ j, (f i α).f j = 0) ∧
    ∀ i₀, GlobalTheory.ZH.IsBasisB D.toPre (fun i : {i // cls i = cls i₀} => f i (cls i₀))
variable {F : Type} [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ))

def IntGe {k : ℕ} (s : Fam D.toPre F k) (q : ℚ) : Prop := ∀ α, VGe D F v k α (s.s α) q

def Norms (k : ℕ) {r : ℕ} (cls : Fin r → D.toPre.X) (s : Fin r → Fam D.toPre F k) : Prop :=
  (∀ s' : Fam D.toPre F k, ∃! a : Fin r → F, s' = ∑ i, a i • s i) ∧ ∀ (a : Fin r → F) (q : ℚ),
    (NuGe D Q F v k (∑ i, a i • s i) q ↔ ∀ i, ((q + (Q (cls i) : ℚ) / k : ℚ) : WithTop ℚ) ≤ v (a i)) ∧
    (IntGe D v (∑ i, a i • s i) q ↔ ∀ i, (q : WithTop ℚ) ≤ v (a i)) ∧
    ∀ i, VGe D F v k (cls i) ((∑ i, a i • s i).s (cls i)) q → (q : WithTop ℚ) ≤ v (a i)
end Dvr

theorem exists_valuationSubring {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) :
    ∃ O : ValuationSubring F, ∀ x, x ∈ O ↔ 0 ≤ v x :=
  ⟨(AddValuation.toValuation v).valuationSubring, fun _ => Iff.rfl⟩

theorem valuation_eq_one_iff {F : Type} [Field F] {v : AddValuation F (WithTop ℚ)} {O : ValuationSubring F}
    (h : ∀ x, x ∈ O ↔ 0 ≤ v x) (x : F) : O.valuation x = 1 ↔ v x = 0 := by
  have e : O = (AddValuation.toValuation v).valuationSubring := ValuationSubring.ext _ _ h
  subst e
  exact (Valuation.isEquiv_valuation_valuationSubring (AddValuation.toValuation v)).eq_one_iff_eq_one.symm

end GlobalTheory.OneBasis
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.testModel_maps_into_openPart : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀) (c : Q.Fac y t.u) (tm : Q.TMap t c), S.Big → ⊤ ≤ (tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι) ⁻¹ᵁ Q.G := by
  first | exact @GlobalTheory.ZH.TestInOpen.top_le_preimage_G | exact GlobalTheory.ZH.TestInOpen.top_le_preimage_G | (intros; apply GlobalTheory.ZH.TestInOpen.top_le_preimage_G <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.nonempty_closureExtension_abelianScheme : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE), Nonempty Q.Ext := by
  first | exact @GlobalTheory.ZH.ClosureLifting.nonempty_ext | exact GlobalTheory.ZH.ClosureLifting.nonempty_ext | (intros; apply GlobalTheory.ZH.ClosureLifting.nonempty_ext <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.nonempty_testModel_to_closure : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀) (c : Q.Fac y t.u), S.Big → Nonempty (Q.TMap t c) := by
  first | exact @GlobalTheory.ZH.TestMap.nonempty_tMap | exact GlobalTheory.ZH.TestMap.nonempty_tMap | (intros; apply GlobalTheory.ZH.TestMap.nonempty_tMap <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

theorem _root_.GlobalTheory.T.cubical_bundle_relAmple_of_ample_fibres : Laws → Laws2 → ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsPrincipalIdealRing A], IsAdicComplete (IsLocalRing.maximalIdeal A) A → ∀ (B : Over (Spec (CommRingCat.of A))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ M : CP B, (∀ (k : Type) [Field k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A)), RelAmple ((Over.pullback x).obj B) (M.L.L.pull (pullback.fst B.hom x))) → RelAmple B M.L.L := by
  first | exact @GlobalTheory.CubicalFibreAmple.relAmple_of_fibres | exact GlobalTheory.CubicalFibreAmple.relAmple_of_fibres | (intros; apply GlobalTheory.CubicalFibreAmple.relAmple_of_fibres <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.TripleExt

open GlobalTheory.CechPic

section Cube

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

def cubeCls {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ G)) (c : Pic G.left) : Pic T.left :=
  ∑ I : ULift.{0} (Finset (Fin n)), ((-1 : ℤ) ^ (n - I.down.card)) • pull (psum G x I.down).left c

theorem isLB_cube {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ G)) {L : LB G.left} (hL : L.IsLB) : (cubeLB G x L).IsLB :=
  LB.isLB_linComb hL _ _

theorem cls_cube {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ G)) {L : LB G.left} (hL : L.IsLB) :
    cls _ (isLB_cube x hL) = cubeCls x (cls L hL) :=
  cls_linComb hL _ _ _

theorem pull_cubeCls_pre {T T' : Over S} (u : T' ⟶ T) {n : ℕ} (x : Fin n → (T ⟶ G)) (c : Pic G.left) :
    pull u.left (cubeCls x c) = cubeCls (fun i => u ≫ x i) c := by
  unfold cubeCls

  rw [map_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [map_zsmul, ← pull_comp, ← Over.comp_left]
  exact congrArg (fun z => _ • pull (CommaMorphism.left z) c) (psum_hom (preHom u) x I.down)

theorem pull_cubeCls_push (h : IsGrpPullback G' G f φ) {T' : Over S'} {T : Over S} {n : ℕ} (x' : Fin n → (T' ⟶ G'))
    (x : Fin n → (T ⟶ G)) (u : Over.mk (T'.hom ≫ f) ⟶ T) (hx : ∀ i, pushPt h.1.w (x' i) = u ≫ x i)
    (c : Pic G.left) : pull (Y := T'.left) u.left (cubeCls x c) = cubeCls x' (pull φ c) := by
  unfold cubeCls

  rw [map_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [map_zsmul, ← pull_comp, ← pull_comp, psum_push h x' x u hx]

theorem cubeCls_one {n : ℕ} (c : Pic G.left) (hc : pull (eSec G) c = 0) :
    cubeCls (fun _ : Fin n => η[G]) c = 0 := by
  refine Finset.sum_eq_zero fun I _ => ?_
  have e₁ : (1 : 𝟙_ (Over S) ⟶ G) = η[G] := by rw [Hom.one_def]; simp
  have e : psum G (fun _ : Fin n => η[G]) I.down = η[G] := by
    have := psum_hom (1 : (𝟙_ (Over S) ⟶ G) →* (𝟙_ (Over S) ⟶ G)) (fun _ : Fin n => η[G]) I.down
    simp only [MonoidHom.one_apply, e₁] at this
    exact this.symm
  rw [e]
  exact (congrArg _ hc).trans (smul_zero _)

end Cube

theorem pic_ext (S : Scheme.{0}) [IsIntegral S] [IsLocallyNoetherian S] (hS : Geo.Tor.IsNormalScheme S) {U H HU : Scheme.{0}}
    [Nonempty U] (j : U ⟶ S) [IsOpenImmersion j] (p : H ⟶ S) (e : S ⟶ H) (jH : HU ⟶ H) (pU : HU ⟶ U) (hp : Smooth p)
    (hg : GeometricallyIntegral p) (he : e ≫ p = 𝟙 _) (hj : IsPullback jH pU p j) (α β : Pic H)
    (h₁ : pull jH α = pull jH β) (h₂ : pull e α = pull e β) : α = β := by
  obtain ⟨A, hA, rfl⟩ := cls_surj α
  obtain ⟨B, hB, rfl⟩ := cls_surj β
  exact (cls_eq_iff hA hB).2 ((GlobalTheory.T.lineBundleIso_extend_of_normal_base S hS U H HU j p e jH pU hp hg he hj A B hA hB
    ((cls_eq_iff (pull_isLB hA _) (pull_isLB hB _)).1 h₁)).1 ((cls_eq_iff (pull_isLB hA _) (pull_isLB hB _)).1 h₂))

theorem exists_sab_extension : ∀ (S : Scheme.{0}) [IsIntegral S] [IsLocallyNoetherian S], Geo.Tor.IsNormalScheme S → ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Host E) (U : Scheme.{0}) [Nonempty U] (j : U ⟶ S) [IsOpenImmersion j] (G : Over S) [GrpObj G] [IsCommMonObj G] (semi : IsSemiAbelian G) (act : OAct (NumberField.RingOfIntegers E) G) (t₀ : SAB H U) (a : t₀.G.left ⟶ G.left), IsGrpPullback t₀.G G j a → (∀ x, (t₀.act.act x).left ≫ a = a ≫ (act.act x).left) → ∀ M : LB G.left, M.IsLB → LBIso (M.pull a) t₀.PP.L → ∃ (PP : RigLB G) (cub : CubicalStr G PP) (h₁ : _) (h₂ : _) (h₃ : _) (m : SABMap t₀ (SAB.mk G semi act PP cub h₁ h₂ h₃) j), m.φ = a := by
  intro S _ _ hS E _ _ _ H U _ j _ G _ _ semi act t₀ a h hact M hM hMa
  have := semi.smooth
  have := semi.geomConnected
  obtain ⟨PP, cub, m, rfl, hme, hlin, hsym⟩ := GlobalTheory.T.exists_rigidified_cubical_symmetric_extension_normalBase S hS U j G t₀.G a h t₀.PP t₀.cub M hM hMa
  have hc₀ : cls t₀.PP.L t₀.PP.isLB = pull m.F (cls PP.L PP.isLB) := by
    obtain ⟨w, hw, -⟩ := hlin
    exact (cls_eq_iff t₀.PP.isLB (pull_isLB PP.isLB _)).2 ⟨w, hw⟩
  have hrig : pull (eSec G) (cls PP.L PP.isLB) = 0 :=
    (cls_eq_zero_iff (pull_isLB PP.isLB _)).2 ⟨PP.rig, PP.rigGen⟩
  have pa : ∀ {T : Over U} (x : T ⟶ t₀.G) b,
      pushPt h.1.w (x ≫ t₀.act.act b) = pushPt h.1.w x ≫ act.act b := fun x b =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, hact, Category.assoc])
  have ha1 : ∀ b, η[G] ≫ act.act b = η[G] := fun b => by have := act.hom b; exact IsMonHom.one_hom _
  refine ⟨PP, cub, hsym t₀.sym, fun b => ?_, ?_, ⟨m, h, hme, hact, hlin⟩, rfl⟩
  · refine (cls_eq_iff (isLB_cube _ PP.isLB) (isLB_cube _ PP.isLB)).1 ?_
    rw [cls_cube _ PP.isLB, cls_cube _ PP.isLB]
    have hsm : Smooth (G ⊗ G).hom := by
      show Smooth (pullback.fst G.hom G.hom ≫ G.hom)
      infer_instance
    have hgc : GeometricallyConnected (G ⊗ G).hom := by
      show GeometricallyConnected (pullback.fst G.hom G.hom ≫ G.hom)
      exact GeometricallyConnected.comp _ _
    let T' : Over U := Over.mk (pullback.snd (G ⊗ G).hom j)
    let u : Over.mk (T'.hom ≫ j) ⟶ G ⊗ G := Over.homMk (pullback.fst (G ⊗ G).hom j) pullback.condition
    have hy : ∀ y : G ⊗ G ⟶ G, ∃ y' : T' ⟶ t₀.G, pushPt h.1.w y' = u ≫ y := fun y =>
      ⟨Over.homMk (h.1.lift (u ≫ y).left T'.hom (Over.w (u ≫ y))) (h.1.lift_snd _ _ _),
        Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩
    obtain ⟨y₁, hy₁⟩ := hy (fst G G)
    obtain ⟨y₂, hy₂⟩ := hy (snd G G)
    let e : 𝟙_ (Over S) ⟶ G ⊗ G := lift η[G] η[G]
    refine pic_ext S hS j (G ⊗ G).hom e.left u.left T'.hom hsm
      (geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres _) (Over.w e)
      (IsPullback.of_hasPullback _ _) _ _ ?_ ?_
    · have h₀ := (cls_eq_iff (isLB_cube _ t₀.PP.isLB) (isLB_cube _ t₀.PP.isLB)).2 (t₀.adj b)
      rw [cls_cube _ t₀.PP.isLB, cls_cube _ t₀.PP.isLB, hc₀] at h₀
      have h₁ := congrArg (pull (lift y₁ y₂).left) h₀
      rw [pull_cubeCls_pre, pull_cubeCls_pre] at h₁
      refine (pull_cubeCls_push h _ _ u (fun i => ?_) _).trans
        (h₁.trans (pull_cubeCls_push h _ _ u (fun i => ?_) _).symm)
      · fin_cases i
        · simp [pa, hy₁]
        · simp [hy₂]
      · fin_cases i
        · simp [hy₁]
        · simp [pa, hy₂]
    · refine (pull_cubeCls_pre e _ _).trans (Eq.trans ?_ (pull_cubeCls_pre e _ _).symm)
      congr 1
      funext i
      fin_cases i <;> simp [e, ha1]
  · refine (cls_eq_iff PP.isLB (isLB_cube _ PP.isLB)).1 ?_
    rw [cls_cube _ PP.isLB]
    refine pic_ext S hS j G.hom (eSec G) m.F t₀.G.hom inferInstance
      (geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres _) (Over.w η[G]) h.1 _ _ ?_ ?_
    · have h₀ := (cls_eq_iff t₀.PP.isLB (isLB_cube _ t₀.PP.isLB)).2 t₀.prim
      rw [cls_cube _ t₀.PP.isLB, hc₀] at h₀
      have h₁ := pull_cubeCls_push h ![𝟙 t₀.G, t₀.act.act H.w0] ![𝟙 G, act.act H.w0] (pushPt h.1.w (𝟙 t₀.G))
        (fun i => by
          fin_cases i
          · simp
          · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _ _)) (cls PP.L PP.isLB)
      have e : (pushPt h.1.w (𝟙 t₀.G)).left = m.F := Category.id_comp _
      rw [e] at h₁
      exact h₀.trans h₁.symm
    · refine hrig.trans (Eq.trans ?_ (pull_cubeCls_pre η[G] _ _).symm)
      refine (cubeCls_one (n := 2) _ hrig).symm.trans ?_
      congr 1
      funext i
      fin_cases i <;> simp [ha1]

end GlobalTheory.TripleExt
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_symmetric_spread_out_lineBundle_abelian_scheme : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (φ : A.left ⟶ G.left) (L : LB G.left) (L₀ : LB A.left), IsAbelianScheme G → IsGrpPullback A G (spMap (algebraMap R K)) φ → L.IsLB → L₀.IsLB → LBIso L₀ (L.pull φ) → Out.Sym A L₀ → ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (π : G'.left ⟶ G.left) (L' : LB G'.left), IsGrpPullback G' G (spMap g) π → L'.IsLB → LBIso L' (L.pull π) → Out.Sym G' L' := by
  first | exact @GlobalTheory.GenSpread.exists_sym | exact GlobalTheory.GenSpread.exists_sym | (intros; apply GlobalTheory.GenSpread.exists_sym <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

theorem _root_.GlobalTheory.T.polAV_descends_to_countable_subfield' : ∀ (K : Type) [Field K] (P : PolAV (Sp K)) (J I : Type) [Finite J] [Finite I] (a : J → (P.A ⟶ P.A)) (x : I → (𝟙_ (Over (Sp K)) ⟶ P.A)), ∃ (K₀ : Subfield K) (P₀ : PolAV (Sp K₀)) (Φ : P.A.left ⟶ P₀.A.left) (a₀ : J → (P₀.A ⟶ P₀.A)) (x₀ : I → (𝟙_ (Over (Sp K₀)) ⟶ P₀.A)), Countable K₀ ∧ IsGrpPullback P.A P₀.A (spMap K₀.subtype) Φ ∧ LBIso P.L (P₀.L.pull Φ) ∧ (∀ j, (a j).left ≫ Φ = Φ ≫ (a₀ j).left) ∧ ∀ i, (x i).left ≫ Φ = spMap K₀.subtype ≫ (x₀ i).left := by
  first | exact @GlobalTheory.PolCountableDescent.polAV_descends_to_countable_subfield | exact GlobalTheory.PolCountableDescent.polAV_descends_to_countable_subfield | (intros; apply GlobalTheory.PolCountableDescent.polAV_descends_to_countable_subfield <;> assumption)
end
