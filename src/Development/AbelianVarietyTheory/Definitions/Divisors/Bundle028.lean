module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
public import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle028
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
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
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open GlobalTheory.Cartier

namespace GlobalTheory.LogDR

section Algebra

abbrev abelian₂ (K : Type) [Field K] : Type := ExteriorAlgebra K Ω[K⁄ℤ]

variable {K : Type} [Field K]

abbrev dK (f : K) : Ω[K⁄ℤ] := KaehlerDifferential.D ℤ K f


variable (K) in
def extD : abelian₂ K →+ abelian₂ K := (CechDR.dDR ℤ K).toAddMonoidHom

theorem extD_apply (η : abelian₂ K) : extD K η = CechDR.dDR ℤ K η := rfl

def dlog (g : Kˣ) : Ω[K⁄ℤ] := ((g⁻¹ : Kˣ) : K) • dK (g : K)

def spanForms (M : Set K) (H : Set Ω[K⁄ℤ]) (a : ℕ) : AddSubgroup (abelian₂ K) :=
  AddSubgroup.closure
    {η | ∃ c ∈ M, ∃ v : Fin a → Ω[K⁄ℤ], (∀ i, v i ∈ H) ∧ η = c • ExteriorAlgebra.ιMulti K a v}

def frame {n : ℕ} (x : Fin n → Kˣ) (J : Finset (Fin n)) (i : Fin n) : Ω[K⁄ℤ] :=
  if i ∈ J then dlog (x i) else dK (x i : K)

def logWedge {n : ℕ} (x : Fin n → Kˣ) (I : Finset (Fin n)) : abelian₂ K :=
  ((I.sort (· ≤ ·)).map fun i => ExteriorAlgebra.ι K (dlog (x i))).prod

def chartForms (A : Subring K) {n : ℕ} (x : Fin n → Kˣ) (J : Finset (Fin n)) (t : Kˣ) (a : ℕ) :
    AddSubgroup (abelian₂ K) :=
  spanForms {c | c * t ∈ A} (Set.range (frame x J)) a

def IsCoord {n : ℕ} (x : Fin n → Kˣ) : Prop :=
  LinearIndependent K (fun i => dK (x i : K)) ∧
    Submodule.span K (Set.range fun i => dK (x i : K)) = ⊤

structure AlgChart (A : Subring K) {n : ℕ} (x : Fin n → Kˣ) : Prop where

  mem : ∀ i, (x i : K) ∈ A

  coord : IsCoord x

  deriv : ∀ f ∈ A, ∃ c : Fin n → K, (∀ i, c i ∈ A) ∧ dK f = ∑ i, c i • dK (x i : K)

  root : ∀ (S : Finset (Fin n)) (g : K) (m : ℕ), 0 < m →
    g ^ m / ∏ j ∈ S, (x j : K) ∈ A → g / ∏ j ∈ S, (x j : K) ∈ A

def IsCartierMap (p : ℕ) {n : ℕ} (x : Fin n → Kˣ) (γ : abelian₂ K →+* abelian₂ K) : Prop :=
  (∀ c : K, γ (algebraMap K (abelian₂ K) c) = algebraMap K (abelian₂ K) (c ^ p)) ∧
    ∀ i, γ (ExteriorAlgebra.ι K (dlog (x i))) = ExteriorAlgebra.ι K (dlog (x i))

def IsEulerContraction {n : ℕ} (x : Fin n → Kˣ) (i : Fin n) (θ : abelian₂ K →ₗ[K] abelian₂ K) : Prop :=
  θ 1 = 0 ∧ (∀ (v : Ω[K⁄ℤ]) (η : abelian₂ K),
    θ (ExteriorAlgebra.ι K v * η) = θ (ExteriorAlgebra.ι K v) * η - ExteriorAlgebra.ι K v * θ η) ∧
    ∀ j, θ (ExteriorAlgebra.ι K (dlog (x j))) = if j = i then 1 else 0

end Algebra

section Scheme

variable {X : Scheme.{0}} [IsIntegral X]

def locRing (y : X) : Subring X.functionField :=
  (algebraMap (X.presheaf.stalk y) X.functionField).range

theorem mem_locRing {y : X} {f : X.functionField} : f ∈ locRing y ↔ RegAt y f := Iff.rfl

def LogUnit (Z : Set X) (y : X) (g : X.functionFieldˣ) : Prop :=
  ∀ z : X, z ⤳ y → z ∉ Z → UnitAt z (g : X.functionField)

def logAt (Z : Set X) (G : CartierDiv X) (a : ℕ) (y : X) : AddSubgroup (abelian₂ X.functionField) :=
  spanForms {c | G.RegularAt y c} (dlog '' {g | LogUnit Z y g}) a


omit [IsIntegral X] in
def latSec {V : Type} [AddCommGroup V] (M : X → AddSubgroup V) (U : X.Opens) : AddSubgroup V :=
  ⨅ y ∈ U, M y

abbrev logSec (Z : Set X) (G : CartierDiv X) (a : ℕ) (U : X.Opens) :
    AddSubgroup (abelian₂ X.functionField) :=
  latSec (logAt Z G a) U

structure IsLogChart (Z : Set X) (U : X.Opens) {n : ℕ} (x : Fin n → X.functionFieldˣ)
    (J : Finset (Fin n)) : Prop where

  chart : ∀ y ∈ U, AlgChart (locRing y) x

  logUnit : ∀ y ∈ U, ∀ g : X.functionFieldˣ, LogUnit Z y g ↔
    ∃ (u : X.functionFieldˣ) (m : Fin n → ℤ), UnitAt y (u : X.functionField) ∧ g = u * ∏ j ∈ J, x j ^ m j

def IsSncOn {C : Type} (E : C → CartierDiv X) (U : X.Opens) {n : ℕ} (x : Fin n → X.functionFieldˣ)
    (J : Finset (Fin n)) : Prop :=
  ∃ e : C → Option (Fin n), (∀ c c' j, e c = some j → e c' = some j → c = c') ∧
    (∀ j, j ∈ J ↔ ∃ c, e c = some j) ∧
    ∀ c, ∀ y ∈ U, (E c).IsEqn y ((e c).elim 1 x)

def suppAll {C : Type} (E : C → CartierDiv X) : Set X := ⋃ c, ((E c).supp : Set X)

structure SncAtlas {C : Type} (E : C → CartierDiv X) (n : ℕ) (ι : Type) where

  U : ι → X.Opens

  x : ι → Fin n → X.functionFieldˣ

  J : ι → Finset (Fin n)

  affine : ∀ i, IsAffineOpen (U i)

  gen : ∀ i, genericPoint X ∈ U i

  cover : ⨆ i, U i = ⊤

  chart : ∀ i, IsLogChart (suppAll E) (U i) (x i) (J i)

  snc : ∀ i, IsSncOn E (U i) (x i) (J i)

structure LatModel {V : Type} [AddCommGroup V] [Module X.functionField V] (M : X → AddSubgroup V)
    (F : X.Modules) where

  val : ∀ U : X.Opens, genericPoint X ∈ U → (Γ(F, U) →+ V)

  inj : ∀ U h, Function.Injective (val U h)

  range : ∀ U h, (val U h).range = latSec M U

  res : ∀ (U W : X.Opens) (e : W ≤ U) (h : genericPoint X ∈ W) (s : Γ(F, U)),
    val W h (F.presheaf.map (homOfLE e).op s) = val U (e h) s

  smul : ∀ U h (r : Γ(X, U)) (s : Γ(F, U)), val U h (r • s) = fnOf U h r • val U h s

end Scheme

end GlobalTheory.LogDR
end
end

section

noncomputable section

namespace GlobalTheory.LevPull

open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def IntAt (Xo : Moduli Dw l) (c : Coeff l) (f : Rul Xo c) : Prop := ∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v f

def Pull (d : DeltaDat Xo c 0) (f : Rul Xo c) (g : Rul d.Xo₂ d.c₂) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k],
    (∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) →
    ∀ (y₂ : FrPt d.Xo₂ d.c₂ k) (y : FrPt Xo c k), FrOver d y₂ y → evR d.Xo₂ d.c₂ g y₂ = evR Xo c f y

def FibConst (d : DeltaDat Xo c 0) (g : Rul d.Xo₂ d.c₂) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k],
    (∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) →
    ∀ (y₂ y₂' : FrPt d.Xo₂ d.c₂ k) (y : FrPt Xo c k), FrOver d y₂ y → FrOver d y₂' y →
      evR d.Xo₂ d.c₂ g y₂ = evR d.Xo₂ d.c₂ g y₂'

theorem Pull.fibConst {d : DeltaDat Xo c 0} {f : Rul Xo c} {g : Rul d.Xo₂ d.c₂} (h : Pull d f g) : FibConst d g :=
  fun k _ _ _ _ hk y₂ y₂' y h₁ h₂ => (h k hk y₂ y h₁).trans (h k hk y₂' y h₂).symm


variable (Dw l) in
abbrev LaQ : Type := Dw.La ⧸ (l.Mb • ⊤ : Submodule (𝓞 E) Dw.La)


variable (Dw l) in
abbrev Gam : Type := LaQ Dw l ≃ₗ[𝓞 E] LaQ Dw l

def IsLift (lift : Gam Dw l → Dw.La →ₗ[𝓞 E] Dw.La) : Prop :=
  ∀ γ, (Submodule.mkQ _) ∘ₗ lift γ = γ.toLinearMap ∘ₗ Submodule.mkQ _

def CongMod (I : Ideal (𝓞 E)) (h h' : Dw.La →ₗ[𝓞 E] Dw.La) : Prop :=
  ∀ a, h a - h' a ∈ (I • ⊤ : Submodule (𝓞 E) Dw.La)

end GlobalTheory.LevPull
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.LieHt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow

def IsPow8 {S : Scheme.{0}} (P P₈ : PolAV S) (d : ℕ) (pr : Fin 8 → (P₈.A ⟶ P.A)) (inc : P.A ⟶ P₈.A) : Prop :=
  (∀ u, IsMonHom (pr u)) ∧ IsMonHom inc ∧ (∀ (T : Over S) (y : Fin 8 → (T ⟶ P.A)), ∃! x : T ⟶ P₈.A, ∀ u, x ≫ pr u = y u) ∧
    (∀ u, inc ≫ pr u = if u = 0 then 𝟙 P.A else 1) ∧ LBIso (P₈.L.pull inc.left) (lbPow P.L d)

end GlobalTheory.MBLow

end
end
