module

public import Development.AbelianVarietyTheory.Definitions.KeyFormula.DegProd
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
noncomputable section
namespace GlobalTheory.KeyKa
variable {R : Type} [CommRing R]

abbrev RR (x : KeyIn R) (l : ℕ) : Type := LB.Sec (pw x.P.L (l : ℤ))

def Coords (x : KeyIn R) {l N : ℕ} (b : Fin N → RR x l) (c : Fin N → R) (f : ∀ i, Γ(x.P.A.left, x.P.L.U i)) : Prop :=
  ∀ i, f i = ∑ k, cst x.P.A.hom (x.P.L.U i) (c k) * (show Γ(x.P.A.left, x.P.L.U i) from (b k).f i)

def IsBasis (x : KeyIn R) {l N : ℕ} (b : Fin N → RR x l) : Prop := ∀ s : RR x l, ∃! c, Coords x b c s.f

def SecVia {R' : Type} [CommRing R'] (x' : KeyIn R') (x : KeyIn R) (φ : x'.P.A.left ⟶ x.P.A.left)
    (w : LB.Iso x'.P.L (x.P.L.pull φ)) {l : ℕ} (s' : RR x' l) (s : RR x l) : Prop :=
  ∀ (j : (x.P.L.pull φ).ι) (i : x'.P.L.ι) (h : (x.P.L.pull φ).U j ⊓ x'.P.L.U i ≤ φ ⁻¹ᵁ x.P.L.U (j PUnit.unit)),
    (φ.appLE _ _ h).hom (s.f (j PUnit.unit)) =
      (show Γ(x'.P.A.left, (x.P.L.pull φ).U j ⊓ x'.P.L.U i) from (w.s (j, i)).val) ^ l * resG _ inf_le_right (s'.f i)

def KeyVia {R' : Type} [CommRing R'] (x' : KeyIn R') (x : KeyIn R) (f : R →+* R') (φ : x'.P.A.left ⟶ x.P.A.left)
    (w : LB.Iso x'.P.L (x.P.L.pull φ)) : Prop :=
  ∃ (he : eSec x'.P.A ≫ φ = spMap f ≫ eSec x.P.A) (hg : x'.P.g = x.P.g) (F : DualNumber R →+* DualNumber R'),
    IsGrpPullback x'.P.A x.P.A (spMap f) φ ∧ w.IsGen ∧
    LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec x'.P.A) (fun _ => 1)) x'.rig
      (rigPullOf φ (spMap f) he x.P.L x.rig) ∧
    (∀ (j : (x.P.L.pull φ).ι) (i : x'.P.L.ι)
      (h : (x.P.L.pull φ).U j ⊓ x'.P.L.U i ≤ φ ⁻¹ᵁ x.P.L.U (j PUnit.unit)),
      (φ.appLE _ _ h).hom (x.th.f (j PUnit.unit)) =
        (show Γ(x'.P.A.left, (x.P.L.pull φ).U j ⊓ x'.P.L.U i) from (w.s (j, i)).val) *
          resG _ inf_le_right (x'.th.f i)) ∧
    (∀ a, F (algebraMap R _ a) = algebraMap R' _ (f a)) ∧ F DualNumber.eps = DualNumber.eps ∧
    ∀ i, (x'.v i).left ≫ φ = spMap F ≫ (x.v (i.cast hg)).left


open Classical in
def valT {T : Type} [CommRing T] {X : Scheme.{0}} (w : Sp T ⟶ X) (U : X.Opens) (f : Γ(X, U)) : T :=
  if h : ⊤ ≤ w ⁻¹ᵁ U then (Scheme.ΓSpecIso (CommRingCat.of T)).hom.hom ((w.appLE U ⊤ h).hom f) else 0

abbrev Pt (x : KeyIn R) : Type := 𝟙_ (Over (Sp R)) ⟶ x.P.A

def jac (x : KeyIn R) {n : ℕ} (s : Fin x.P.g → RR x n) (z : Pt x) (c : x.P.L.ι) : R :=
  (Matrix.of fun i k => TrivSqZeroExt.snd
    (valT (T := DualNumber R) ((toUnit (epsR R) ≫ z) * x.v k).left (x.P.L.U c) ((s i).f c))).det

def FinZ (x : KeyIn R) {n r : ℕ} (s : Fin r → RR x n) : Prop :=
  Set.Finite {y : x.P.A.left | ∀ i, y ∉ Out.nonzeroLocus (s i)}

def IsMul (x : KeyIn R) {n : ℕ} (l : ℕ) (s : Fin x.P.g → RR x n) (b : ∀ j, Fin ((l - j * n) ^ x.P.g) → RR x (l - j * n))
    (m : Fin x.P.g → ∀ j j', Matrix (Fin ((l - j * n) ^ x.P.g)) (Fin ((l - j' * n) ^ x.P.g)) R) : Prop :=
  ∀ i j, j < x.P.g → ∀ k, Coords x (b j) (fun k' => m i j (j + 1) k' k)
    (fun c => (show Γ(x.P.A.left, x.P.L.U c) from (s i).f c) * (show Γ(x.P.A.left, x.P.L.U c) from (b (j + 1) k).f c))

def KosVal (x : KeyIn R) {n d : ℕ} (l : ℕ) (s : Fin x.P.g → RR x n) (z : Fin d → Pt x) (ch : Fin d → x.P.L.ι)
    (b : ∀ j, Fin ((l - j * n) ^ x.P.g) → RR x (l - j * n)) (t : R) : Prop :=
  ∃ m, IsMul x l s b m ∧ TorsSq kdeg
    (kosD (N := fun j => (l - j * n) ^ x.P.g) m
      (fun j => Matrix.of fun a k => valT (T := R) (z a).left (x.P.L.U (ch a)) ((b j k).f (ch a)))) t

def alMap (x : KeyIn R) (al : Matrix (Fin 4) (Fin 4) ℤ) (r : Fin 4) (ξ : Pt x) : Out.powObj x.P.A 4 ⟶ x.P.A :=
  (List.ofFn fun c : Fin 4 => Out.powPr x.P.A c ^ al r c).prod * (toUnit _ ≫ ξ)

def IsSquareDeterminantComparison (x : KeyIn R) (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ) (b : Fin (m ^ x.P.g) → RR x m) (lam : Rˣ) : Prop :=
  ∃ (ξ : (Fin 4 → Fin (m ^ x.P.g)) → Fin 4 → Pt x)
    (mu : LB.Gen (LB.LinComb x.P.L (K := Fin 2) ![((𝟙 x.P.A) ^ m).left, 𝟙 x.P.A.left] ![1, -(m : ℤ) ^ 2]))
    (w : ∀ I, LB.Gen (LB.LinComb x.P.L (K := Fin 4 ⊕ Fin 4)
      (Sum.elim (fun r => (alMap x al r (ξ I r)).left) (fun c => (Out.powPr x.P.A c).left))
      (Sum.elim (fun _ => 1) (fun _ => -(m : ℤ)))))
    (Q : Matrix (Fin 4 → Fin (m ^ x.P.g)) (Fin 4 → Fin (m ^ x.P.g)) R) (rho : (Fin 4 → Fin (m ^ x.P.g)) → Rˣ),
    (∀ I I', I ≠ I' → ∀ p : Sp R, ∃ r, (ξ I r).left p ≠ (ξ I' r).left p) ∧
    (∀ I c, (List.ofFn fun r : Fin 4 => ξ I r ^ al r c).prod = 1) ∧
    mu.IsGen ∧ (∀ I, (w I).IsGen) ∧
    (∀ (p : (𝟙_ (Over (Sp R))).left) J, Good x.P.L p J →
      val mu (eSec x.P.A) p J = val x.rig (𝟙 _) p J ^ (1 - (m : ℤ) ^ 2) ∧
      ∀ I, (val (w I) (eSec (Out.powObj x.P.A 4)) p J ^ (m ^ 2) * ∏ r, val mu (ξ I r).left p J).val =
        gs (𝟙_ (Over (Sp R))).hom p ⊤ (cst (𝟙 (Sp R)) ⊤ (rho I)) * (val x.rig (𝟙 _) p J ^ (4 - 4 * (m : ℤ) ^ 3)).val) ∧
    (∀ I (y : (Out.powObj x.P.A 4).left) J, Good x.P.L y J →
      ∏ r, gs (alMap x al r (ξ I r)).left y _ (x.th.f (J (alMap x al r (ξ I r)).left)) =
        (val (w I) (𝟙 _) y J).val * ∑ I', gs (𝟙 _) y ⊤ (cst (Out.powObj x.P.A 4).hom ⊤ (Q I I')) *
          ∏ c, gs (Out.powPr x.P.A c).left y (x.P.L.U (J (Out.powPr x.P.A c).left)) ((b (I' c)).f (J (Out.powPr x.P.A c).left))) ∧
    (lam : R) = Q.det ^ (2 * m ^ 2) * ∏ I, (rho I : R) ^ 2

def EtZ (x : KeyIn R) {n d : ℕ} (s : Fin x.P.g → RR x n) (z : Fin d → Pt x) (ch : Fin d → x.P.L.ι) : Prop :=
  (∀ a, ⊤ ≤ (z a).left ⁻¹ᵁ x.P.L.U (ch a)) ∧
  (∀ a i, valT (T := R) (z a).left (x.P.L.U (ch a)) ((s i).f (ch a)) = 0) ∧
  (∀ a, IsUnit (jac x s (z a) (ch a))) ∧
  (∀ a a', a ≠ a' → ∀ p : Sp R, (z a).left p ≠ (z a').left p) ∧
  ∀ y : x.P.A.left, (∀ i, y ∉ Out.nonzeroLocus (s i)) → ∃ a, ∃ p : Sp R, (z a).left p = y

def admitted (g n l l' : ℕ) (al : ℕ → Matrix (Fin 4) (Fin 4) ℤ) : Prop :=
  4 ≤ n ∧ g * n < l ∧ l < l' ∧ ∀ m, (al m).transpose * al m = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)

def KaVal (x : KeyIn R) (n l l' : ℕ) (al : ℕ → Matrix (Fin 4) (Fin 4) ℤ) (s : Fin x.P.g → RR x n) (κ : Rˣ) : Prop :=
  ∃ (z : Fin (x.P.g.factorial * n ^ x.P.g) → Pt x) (ch : _) (b : _) (b' : _) (t t' J : Rˣ) (lam lam' : ℕ → Rˣ),
    EtZ x s z ch ∧ (J : R) = ∏ a, jac x s (z a) (ch a) ∧
    (∀ j ≤ x.P.g, IsBasis x (b j) ∧ IsSquareDeterminantComparison x (l - j * n) (al (l - j * n)) (b j) (lam j)) ∧
    (∀ j ≤ x.P.g, IsBasis x (b' j) ∧ IsSquareDeterminantComparison x (l' - j * n) (al (l' - j * n)) (b' j) (lam' j)) ∧
    KosVal x l s z ch b t ∧ KosVal x l' s z ch b' t' ∧ κ = kaForm x.P.g n l l' t t' lam lam' J

end GlobalTheory.KeyKa
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.KeyFam
open GlobalTheory.KeyPow

def per {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (a : Fin g ⊕ Fin g → ℤ) : Fin g → ℂ :=
  τ.mulVec (fun i => (a (.inl i) : ℂ)) + fun i => (a (.inr i) : ℂ)

def PerLev (P : Out.PolAV (Sp ℂ)) {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (k : ℕ)
    (lev : (Fin g ⊕ Fin g → ℤ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)) : Prop :=
  P.g = g ∧ τ.IsSymm ∧ (τ.map Complex.im).PosDef ∧ ∃ u : HolUnif P.A P.L g,
    (∀ z, z ∈ u.Λ ↔ ∃ a, z = per τ a) ∧
    (∀ (n : ℕ) (a b : Fin g ⊕ Fin g → ℤ) (c : ℂˣ), 0 < n →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (omegaStd a b : ℂ) / n) →
      Out.WeilIs P.A P.L n (u.ex ((n : ℂ)⁻¹ • per τ a)) (u.ex ((n : ℂ)⁻¹ • per τ b)) (unitOn c)) ∧
    ∀ a, lev a = u.ex ((k : ℂ)⁻¹ • per τ a)

def PolPB {S S' : Scheme.{0}} (P' : Out.PolAV S') (P : Out.PolAV S) (f : S' ⟶ S) (φ : P'.A.left ⟶ P.A.left) : Prop :=
  IsGrpPullback P'.A P.A f φ ∧ P'.g = P.g ∧ LBIso P'.L (P.L.pull φ)

def LamIs {S S' : Scheme.{0}} (A : Over S') [GrpObj A] (L : LB A.left) (B : Over S) (Pb : LB (B ⊗ B).left)
    (φ : A.left ⟶ B.left) : Prop :=
  ∃ φ₂ : (A ⊗ A).left ⟶ (B ⊗ B).left, IsSquare φ φ₂ ∧ LBIso (abelian₂ A L) (Pb.pull φ₂)

variable {h k : ℕ} {o : Type} [CommRing o] {ζ : o} {S S' : Scheme.{0}} {s : S ⟶ Sp o}

def SqOf (P : Out.PolAV S') (c : SiegPre h k ζ s) (f : S' ⟶ S) (φ : P.A.left ⟶ c.A.left) : Prop :=
  IsGrpPullback P.A c.A f φ ∧ P.g = h ∧ LamIs P.A P.L c.A c.P φ

def PtAt (c : SiegPre h k ζ s) (p : Sp ℂ ⟶ S) (τ : Matrix (Fin h) (Fin h) ℂ) : Prop :=
  ∃ (P : Out.PolAV (Sp ℂ)) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)) (φ : P.A.left ⟶ c.A.left),
    PerLev P τ k lev ∧ SqOf P c p φ ∧ ∀ a, (lev a).left ≫ φ = p ≫ (c.lev a).left

def SameComp (s : S ⟶ Sp o) (σ : o →+* ℂ) (p q : Sp ℂ ⟶ S) : Prop :=
  ∃ (hp : p ≫ s = 𝟙 _ ≫ spMap σ) (hq : q ≫ s = 𝟙 _ ≫ spMap σ), ∀ z : Sp ℂ,
    pullback.lift p (𝟙 _) hp z ∈ connectedComponent (pullback.lift q (𝟙 _) hq z)

def TorsConst (A : Over S) [GrpObj A] (n : ℕ) : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (y : Over.mk x ⟶ A), y ^ n = 1 →
    ∃ t : 𝟙_ (Over S) ⟶ A, t ^ n = 1 ∧ y = toUnit _ ≫ t

def Val (x : KeyIn ℂ) (t : ℂ) : Prop :=
  ∃ (τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ) (c : ℂ),
    charHalf _ a b ∧ c ≠ 0 ∧ NormalAt x τ M a b c ∧ t = M.det ^ 4 / c ^ 8

def Known (K : Type) [Field K] (y : KeyIn K) : Prop :=
  ∃ t₀ : K, ∀ (e : K →+* ℂ) (x : KeyIn ℂ), KeyPB x y e → Val x (e t₀)

def PotKnown (K : Type) [Field K] (P : Out.PolAV (Sp K)) : Prop :=
  ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (j : K →+* K'),
    ∀ (K'' : Type) [Field K''] (j' : K' →+* K'') (y : KeyIn K'') (φ : y.P.A.left ⟶ P.A.left),
      PolPB y.P P (spMap (j'.comp j)) φ → Known K'' y

def GeomInt (K R : Type) [Field K] [CommRing R] [Algebra K R] : Prop :=
  Algebra.Smooth K R ∧ ∀ (K' : Type) [Field K'] [Algebra K K'], IsDomain (K' ⊗[K] R)

def PolFam : Prop :=
  ∀ P : Out.PolAV (Sp ℂ), 1 ≤ P.g →
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (R : Type) (_ : CommRing R) (_ : Algebra K R)
      (Q : Out.PolAV (Sp R)) (s : R →+* ℂ) (s₀ : R →ₐ[K] K) (φ : P.A.left ⟶ Q.A.left),
      GeomInt K R ∧ PolPB P Q (spMap s) φ ∧
      ∀ (P₀ : Out.PolAV (Sp K)) (φ₀ : P₀.A.left ⟶ Q.A.left), PolPB P₀ Q (spMap s₀.toRingHom) φ₀ → PotKnown K P₀

theorem per_add {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g ⊕ Fin g → ℤ) :
    per τ (a + b) = per τ a + per τ b := by
  have h₁ : (fun i => (((a + b) (Sum.inl i) : ℤ) : ℂ)) =
      (fun i => (a (.inl i) : ℂ)) + fun i => (b (.inl i) : ℂ) := by
    funext i; simp
  have h₂ : (fun i => (((a + b) (Sum.inr i) : ℤ) : ℂ)) =
      (fun i => (a (.inr i) : ℂ)) + fun i => (b (.inr i) : ℂ) := by
    funext i; simp
  unfold per
  rw [h₁, h₂, Matrix.mulVec_add]
  abel

end GlobalTheory.KeyFam
end
end
