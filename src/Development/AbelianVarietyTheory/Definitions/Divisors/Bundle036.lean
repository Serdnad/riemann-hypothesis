module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle133
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle004
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealCusp
public import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
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
import Mathlib.Topology.Sheaves.Init
import GroundTheory.AutomorphicForms.LocallyProfinite

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.Cartier

namespace GlobalTheory.VolBr

structure IsBallFam {G : Type} [AddCommGroup G] (Λ : AddSubgroup G) (B : ℝ → Set G) : Prop where

  subset : ∀ r, B r ⊆ Λ

  zero_mem : ∀ r, 0 ≤ r → (0 : G) ∈ B r

  sub_mem : ∀ r r' x y, x ∈ B r → y ∈ B r' → x - y ∈ B (r + r')

  nsmul_iff : ∀ (n : ℕ) (r : ℝ) (x : G), 0 < n → x ∈ Λ → (n • x ∈ B (n * r) ↔ x ∈ B r)

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

structure Pair (p : X ⟶ Sp k) where

  L : HermLB p

  A : HermLB p

  r : L.B.ι → X.functionFieldˣ

  r' : A.B.ι → X.functionFieldˣ

  hr : IsRatSec L.B r

  hr' : IsRatSec A.B r'

theorem exists_pair (L A : HermLB p) : ∃ P : Pair p, P.L = L ∧ P.A = A := by
  obtain ⟨r, hr⟩ := exists_isRatSec L.isLB
  obtain ⟨r', hr'⟩ := exists_isRatSec A.isLB
  exact ⟨⟨L, A, r, r', hr, hr'⟩, rfl, rfl⟩

namespace Pair

variable (P : Pair p)

def loc (a b : ℤ) (f : X.functionField) (i : P.L.B.ι) (j : P.A.B.ι) : X.functionField :=
  f * (P.r i : X.functionField) ^ a * (P.r' j : X.functionField) ^ b

def H (a b : ℤ) : AddSubgroup X.functionField where
  carrier := {f | ∀ (x : X) i j, x ∈ P.L.B.U i → x ∈ P.A.B.U j → RegAt x (P.loc a b f i j)}
  zero_mem' x i j _ _ := ⟨0, by simp [loc]⟩
  add_mem' {f g} hf hg x i j hi hj := by
    obtain ⟨u, hu⟩ := hf x i j hi hj
    obtain ⟨v, hv⟩ := hg x i j hi hj
    exact ⟨u + v, by rw [map_add (f := _), hu, hv]; simp only [loc]; ring⟩
  neg_mem' {f} hf x i j hi hj := by
    obtain ⟨u, hu⟩ := hf x i j hi hj
    exact ⟨-u, by rw [map_neg, hu]; simp only [loc]; ring⟩

def nu (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField) : ℝ :=
  ‖ratVal (P.loc a b f (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y)) y‖ *
    Real.exp (-(a * (P.L.φ σ).φ (pick (P.L.φ σ).isLB y) y + b * (P.A.φ σ).φ (pick (P.A.φ σ).isLB y) y) / 2)

def Bl (a b : ℤ) (R : ℝ) : Set X.functionField :=
  {f | f ∈ P.H a b ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ), P.nu a b σ y f ≤ R}

def lc (a b : ℤ) (R : ℝ) : ℝ := Real.log ((P.Bl a b R).ncard : ℝ)

def Rep (a b : ℤ) (M : HermLB p) : Prop :=
  ∃ ρ : M.B.ι → X.functionFieldˣ, IsRatSec M.B ρ ∧
    (∀ (x : X) c i j, x ∈ M.B.U c → x ∈ P.L.B.U i → x ∈ P.A.B.U j →
      UnitAt x ((ρ c : X.functionField) / P.loc a b 1 i j)) ∧
    ∀ (σ : k →+* ℂ) (y : CxPts p σ) c i j, y ∈ ptsIn p σ (M.B.U c) → y ∈ ptsIn p σ (P.L.B.U i) →
      y ∈ ptsIn p σ (P.A.B.U j) →
      Real.log ‖ratVal ((ρ c : X.functionField) / P.loc a b 1 i j) y‖ - (M.φ σ).φ c y / 2 =
        -(a * (P.L.φ σ).φ i y + b * (P.A.φ σ).φ j y) / 2

structure Good (D : ℕ) (b : ℕ) (s t : X.functionField) : Prop where

  ample : IsAmpleLB P.A.B

  nef : P.A.IsNef D

  pos : 0 < b

  s_mem : s ∈ P.Bl 0 1 1

  s_ne : s ≠ 0

  t_mem : t ∈ P.Bl (-1) b 1

  t_ne : t ≠ 0

  reg : ∀ (x : X) i j, x ∈ P.L.B.U i → x ∈ P.A.B.U j → ∀ g : X.functionField, RegAt x g →
    RegAt x (g * P.loc (-1) b t i j / P.loc 0 1 s i j) → RegAt x (g / P.loc 0 1 s i j)

end Pair

namespace IntExample

open GlobalTheory.Points GlobalTheory.CechPic

theorem ratVal_nat {σ : k →+* ℂ} (y : CxPts p σ) (n : ℕ) : ratVal (n : X.functionField) y = n := by
  have h : genericPoint X ∈ (⊤ : X.Opens) := trivial
  have e : (n : X.functionField) = fnOf ⊤ h (n : Γ(X, ⊤)) := (map_natCast _ n).symm
  rw [e, ratVal_fnOf mem_ptsIn_top h, ev_eq mem_ptsIn_top, map_natCast]

end IntExample

end GlobalTheory.VolBr
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

structure Core5 (R : RealDat D A Ks) (F : Face D A) : Prop where
  lev : R.toLevCh.Is A.μ0
  grp : R.IsGrp F
  fam : R.IsFam
  models : R.IsModels
  thP : R.IsThP

theorem Core5.of_core {R : RealDat D A Ks} {F : Face D A} (h : GlobalTheory.Hk3.Core R F) : Core5 R F :=
  ⟨h.lev, h.grp, h.fam, h.models, h.thP⟩

end GlobalTheory

end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin

def symTup {R : Type} [CommRing R] {N : ℕ} (c : Fin N → R) : Fin N → R :=
  fun j => (Finset.univ.val.map c).esymm ((j : ℕ) + 1) ^ (N.factorial / ((j : ℕ) + 1))

def Prim {V K : Type} [CommRing V] [Field K] (i : V →+* K) {J : Type} (c : J → K) : Prop :=
  (∀ a, i.IsIntegralElem (c a)) ∧ ∃ a, c a ≠ 0 ∧ i.IsIntegralElem (c a)⁻¹

abbrev PCrd {o R : Type} [CommRing o] [CommRing R] {n : ℕ} (x : Sp R ⟶ PSpace o n) (v : Fin (n + 1) → R) : Prop :=
  SecCoord (ProjSpace.O1 o n) (ProjSpace.coord o n) x v

section

variable {S : Scheme.{0}} (G : Over S) [GrpObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G)))

abbrev SecAt {R : Type} [CommRing R] (x : Sp R ⟶ S) : Type := LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk x))

def SecAt.pull {R K : Type} [CommRing R] [CommRing K] {x : Sp R ⟶ S} (θ : SecAt G L x) (i : R →+* K) :
    SecAt G L (spMap i ≫ x) :=
  VVRank.pullS G _ (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) θ

def ThList (m : ℕ) {K : Type} [Field K] (x : Sp K ⟶ S) (θ : SecAt G L x) {N : ℕ} (pt : Fin N → (Over.mk x ⟶ G))
    (c : Fin N → K) : Prop :=
  Function.Injective pt ∧ (∀ a, ThG G L ρ m θ (pt a) (GlobalTheory.ZH.fn (c a))) ∧
    ∀ (K' : Type) [Field K'] [IsAlgClosed K'] (i : K →+* K') (p : Over.mk (spMap i ≫ x) ⟶ G), p ^ (m ^ 2) = 1 →
      ∃ a, p.left = spMap i ≫ (pt a).left

def HasTh (m : ℕ) {K : Type} [Field K] (x : Sp K ⟶ S) {N : ℕ} (c : Fin N → K) : Prop :=
  ∃ (θ : SecAt G L x) (pt : Fin N → (Over.mk x ⟶ G)), IsGenSec G L _ θ ∧ ThList G L ρ m x θ pt c

def HasTh₂ (m m' : ℕ) {K : Type} [Field K] (x : Sp K ⟶ S) {N N' : ℕ} (c : Fin N → K) (c' : Fin N' → K) : Prop :=
  ∃ (θ : SecAt G L x) (pt : Fin N → (Over.mk x ⟶ G)) (pt' : Fin N' → (Over.mk x ⟶ G)),
    IsGenSec G L _ θ ∧ ThList G L ρ m x θ pt c ∧ ThList G L ρ m' x θ pt' c'

def SymAt (m : ℕ) {R : Type} [CommRing R] (x : Sp R ⟶ S) (θ : SecAt G L x) {N : ℕ} (e : Fin N → R) : Prop :=
  ∀ (K : Type) [Field K] (i : R →+* K) (pt : Fin N → (Over.mk (spMap i ≫ x) ⟶ G)) (c : Fin N → K),
    ThList G L ρ m (spMap i ≫ x) (SecAt.pull G L θ i) pt c → ∀ j, i (e j) = symTup c j

def ThMap (m : ℕ) {o : Type} [CommRing o] {n : ℕ} {X : Scheme.{0}} (q : X ⟶ S) (f : X ⟶ PSpace o n) : Prop :=
  ∀ (K : Type) [Field K] (x : Sp K ⟶ X) (c : Fin (n + 1) → K), HasTh G L ρ m (x ≫ q) c → PCrd (x ≫ f) (symTup c)

def PolFib (g : ℕ) {R : Type} [CommRing R] (x : Sp R ⟶ S) : Prop :=
  ∃ (P : PolAV (Sp R)) (α : P.A.left ⟶ G.left), P.g = g ∧ IsGrpPullback P.A G x α ∧ LBIso P.L (L.pull α)

variable {G L ρ}

theorem hasTh_iff {m : ℕ} {K : Type} [Field K] {x : Sp K ⟶ S} {N : ℕ} {c : Fin N → K} :
    HasTh G L ρ m x c ↔ HasTh₂ G L ρ m m x c c :=
  ⟨fun ⟨θ, pt, h, h'⟩ => ⟨θ, pt, pt, h, h', h'⟩, fun ⟨θ, pt, _, h, h', _⟩ => ⟨θ, pt, h, h'⟩⟩

end

end GlobalTheory.UMin
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host

namespace GlobalTheory.JSW

open GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


open Classical in
def sat (π : CG E a) (w : HeightOneSpectrum (𝓞 E)) : Multiset ℂˣ :=
  if h : ∃ B, π.HasSat w B then h.choose else 0

def UnrOutside (S : Finset (HeightOneSpectrum (𝓞 E))) (π : CG E a) : Prop := ∀ w ∉ S, ∃ B, π.HasSat w B

def locL (q : ℕ) (B B' : Multiset ℂˣ) (s : ℂ) : ℂ :=
  ((B ×ˢ B').map fun p : ℂˣ × ℂˣ => (1 - (p.1 : ℂ) * p.2 * (q : ℂ) ^ (-s))⁻¹).prod

def partialL (S : Finset (HeightOneSpectrum (𝓞 E))) {b : ℕ} (π : CG E a) (π' : CG E b) (s : ℂ) : ℂ :=
  ∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ S}, locL (Ideal.absNorm w.1.asIdeal) (sat π w.1) (sat π' w.1) s

end GlobalTheory.JSW
end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Polynomial GroundTheory.Automorphic UpperTheory.V
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin)
open UpperTheory.V.TR (Rinf Lie chart infGL pInf toL rmul invSet CuspSub)
open scoped ContDiff

namespace GlobalTheory.HenQ

section Fin

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

end Fin

section Inf

variable {K : Type} [Field K] [NumberField K] {n : ℕ}


open Classical in
def pdL (v : InfinitePlace K) (i j : Fin n) (F : Lie K n → ℂ) (x : Lie K n) : ℂ :=
  fderiv ℝ F x (toL (Matrix.single i j (Pi.single v 1)))


def detD (v : InfinitePlace K) (F : Lie K n → ℂ) (x : Lie K n) : ℂ :=
  ∑ p : Equiv.Perm (Fin n), (((Equiv.Perm.sign p : ℤˣ) : ℤ) : ℂ) * (List.finRange n).foldr (fun j G => pdL v (p j) j G) F x

def IsTest (Φ : Lie K n → ℂ) : Prop := ContDiff ℝ ∞ Φ ∧ HasCompactSupport Φ ∧ tsupport Φ ⊆ invSet K n

variable [IsTotallyReal K]

end Inf

end GlobalTheory.HenQ
end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict

abbrev Mt (n : ℕ) : Type := Matrix (Fin n) (Fin n) ℂ

section Local

variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

def frDom (Hm : Mt n) (q : ℕ) : Set (Mt n) :=
  {x | x.det ≠ 0 ∧ ∀ i : Fin (n + 1),
    0 < ReciprocityTheory.ChartRestriction.G.FD.psgn q i * (ReciprocityTheory.ChartRestriction.G.FD.lminor (-(xᴴ * Hm * x)) i).re}

def UpT (b : Mt n) : Prop := b.det ≠ 0 ∧ ∀ a c : Fin n, c < a → b a c = 0

def OrthFr (Hm : Mt n) (q : ℕ) (x₀ : Mt n) : Prop :=
  q ≤ n ∧ x₀ᴴ * Hm * x₀ = diagonal fun a : Fin n => -((ReciprocityTheory.ChartRestriction.G.FD.sgn q (a : ℕ) : ℝ) : ℂ)

def UG (Hm : ι → Mt n) : Set (ι → Mt n) := {u | ∀ τ, u τ ∈ Formalism.QuantumDeterminants.UH (Hm τ)}

def frDoms (Hm : ι → Mt n) (q : ι → ℕ) : Set (ι → Fin n → Fin n → ℂ) := {x | ∀ τ, Matrix.of (x τ) ∈ frDom (Hm τ) (q τ)}

def HolSec (Hm : ι → Mt n) (q : ι → ℕ) (w : ι → Fin n → ℤ) (P : (ι → Fin n → Fin n → ℂ) → ℂ) : Prop :=
  DifferentiableOn ℂ P (frDoms Hm q) ∧
    ∀ x ∈ frDoms Hm q, ∀ b : ι → Mt n, (∀ τ, UpT (b τ)) →
      P (fun τ => (Matrix.of (x τ) * b τ : Mt n)) = (∏ τ, ∏ a, b τ a a ^ w τ a) * P x

def HolFn (Hm : ι → Mt n) (q : ι → ℕ) (x₀ : ι → Mt n) (w : ι → Fin n → ℤ) (f : (ι → Mt n) → ℂ) : Prop :=
  ∃ P, HolSec Hm q w P ∧ ∀ u ∈ UG Hm, f u = P fun τ => (u τ * x₀ τ : Mt n)

def lieH (Hm : Mt n) : Set (Mt n) := {X | Xᴴ * Hm + Hm * X = 0}

def SmFn (Hm : ι → Mt n) (f : (ι → Mt n) → ℂ) : Prop :=
  ∀ (k : ℕ) (τs : Fin k → ι) (Xs : Fin k → Mt n), (∀ i, Xs i ∈ lieH (Hm (τs i))) → ∀ u ∈ UG Hm,
    ContDiff ℝ ∞ fun t : Fin k → ℝ =>
      f (u * (List.ofFn fun i => (Pi.mulSingle (τs i) (NormedSpace.exp (t i • Xs i)) : ι → Mt n)).prod)

def der (τ : ι) (X : Mt n) (f : (ι → Mt n) → ℂ) (u : ι → Mt n) : ℂ :=
  deriv (fun t : ℝ => f (u * (Pi.mulSingle τ (NormedSpace.exp (t • X)) : ι → Mt n))) 0

def conjH (Hm Z : Mt n) : Mt n := -(Hm⁻¹ * Zᴴ * Hm)

def derC (Hm : ι → Mt n) (τ : ι) (Z : Mt n) (f : (ι → Mt n) → ℂ) (u : ι → Mt n) : ℂ :=
  der τ ((1 / 2 : ℂ) • (Z + conjH (Hm τ) Z)) f u + Complex.I * der τ ((1 / (2 * Complex.I)) • (Z - conjH (Hm τ) Z)) f u

def KilledFn (Hm : ι → Mt n) (x₀ : ι → Mt n) (w : ι → Fin n → ℤ) (f : (ι → Mt n) → ℂ) : Prop :=
  ∀ τ (a c : Fin n), a ≤ c → ∀ u ∈ UG Hm,
    derC Hm τ (x₀ τ * Matrix.single a c 1 * (x₀ τ)⁻¹) f u = if a = c then (w τ a : ℂ) * f u else 0

def torEl (x₀ : ι → Mt n) (s : ι → Fin n → ℝ) : ι → Mt n :=
  fun τ => x₀ τ * diagonal (fun a => Complex.exp ((s τ a : ℂ) * Complex.I)) * (x₀ τ)⁻¹

def torCh (w : ι → Fin n → ℤ) (s : ι → Fin n → ℝ) : ℂ := ∏ τ, ∏ a, Complex.exp ((s τ a : ℂ) * Complex.I) ^ w τ a

def dRepC {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (Hm : Mt n) (σ : Mt n → (H →L[ℂ] H)) (Z : Mt n) (v : H) : H :=
  dRep σ ((1 / 2 : ℂ) • (Z + conjH Hm Z)) v + Complex.I • dRep σ ((1 / (2 * Complex.I)) • (Z - conjH Hm Z)) v

def gelfRep {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (Hm : Mt n) (σ : Mt n → (H →L[ℂ] H)) (k : ℕ) (v : H) : H :=
  ∑ idx : Fin (k + 1) → Fin n,
    (List.ofFn fun a : Fin (k + 1) => dRepC Hm σ (Matrix.single (idx a) (idx (a + 1)) 1)).foldr (fun f acc => f acc) v

def InZe (Hm : Mt n) (e : Fin n → ℂ) (m : Mt n) : Prop :=
  ∃ s : ℝ, m = 1 + ((s : ℂ) * Complex.I) • vecMulVec e (star e ᵥ* Hm)

end Local

section Adelic

variable {D : D7}

def HolShape {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) : Prop :=
  ∀ τ, Formalism.QuantumDeterminants.IsHCParam (M.lam τ) ∧ ∃ p ≤ V.rank, ∀ a, M.ε τ a = decide ((a : ℕ) < p)

def WtIs {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) : Prop :=
  ∀ τ c, (w τ c : ℝ) = extWt M τ (arr (nNeg (M.ε τ)) c)


open Classical in
def HolAd (θ : InfFam D) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ)
    (φ : GA D V → ℂ) : Prop :=
  ∀ g, ∃ f, HolFn (gramAt D V) (fun τ => nNeg (M.ε τ)) (x0Mat M) w f ∧
    ∀ u ∈ GinfC V, φ (g * u) = f fun τ => archM V (θ τ) u

def ZI (V : HSp D) (ξ : Fin V.rank → D.host.E) : Subgroup (GA D V) :=
  Subgroup.closure {g | ∃ a : AF D.host.F ⊗[D.host.F] D.host.E,
    ((matHom V g).1 - 1 : Matrix (Fin V.rank) (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E)) =
      a • (vecMulVec ξ ((fun i => (D.sp.cm.sig : D.host.E →+* D.host.E) (ξ i)) ᵥ* V.gram)).map (incA D)}

def IsoVec (V : HSp D) (ξ : Fin V.rank → D.host.E) : Prop :=
  ξ ≠ 0 ∧ (fun i => (D.sp.cm.sig : D.host.E →+* D.host.E) (ξ i)) ⬝ᵥ V.gram.mulVec ξ = 0

def ZCusp (V : HSp D) (φ : GA D V → ℂ) : Prop :=
  ∀ ξ, IsoVec V ξ → ∀ (μ : Measure (ZI V ξ)) (𝓕 : Set (ZI V ξ)), μ.IsHaarMeasure →
    IsFundamentalDomain ((GQ V).subgroupOf (ZI V ξ)) 𝓕 μ → ∀ g, ∫ z in 𝓕, φ ((z : GA D V) * g) ∂μ = 0

structure HolForm (θ : InfFam D) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ)
    (J : Set (GA D V)) (χ : GA D V → ℂ) (φ : GA D V → ℂ) : Prop where
  aut : IsAutFun V φ
  bdd : ∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C
  lev : ∀ k ∈ J, ∀ g, φ (g * k) = χ k * φ g
  hol : HolAd θ M w φ

structure FinPair (V : HSp D) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) : Prop where
  haar : μ.IsHaarMeasure
  right : μ.IsMulRightInvariant
  fd : IsFundamentalDomain (GQ V) 𝓕 μ
  fin : μ 𝓕 ≠ ⊤

def nuQ (V : HSp D) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) : Measure (AutQ V) := (μ.restrict 𝓕).map (autMk V)

def Repr (V : HSp D) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (F : Lp ℂ 2 (nuQ V μ 𝓕)) (ψ : GA D V → ℂ) : Prop :=
  ∀ᵐ x ∂μ, F (autMk V x) = ψ x

structure IsReg (V : HSp D) (μ : Measure (GA D V)) (𝓕 : Set (GA D V))
    (ρ : GA D V →* (Lp ℂ 2 (nuQ V μ 𝓕) →L[ℂ] Lp ℂ 2 (nuQ V μ 𝓕))) : Prop where
  val : ∀ g F, ∀ᵐ x ∂μ, ρ g F (autMk V x) = F (autMk V (x * g))
  iso : ∀ g F, ‖ρ g F‖ = ‖F‖
  cont : ∀ F, Continuous fun g => ρ g F

def IsSmoothVector' (θ : InfFam D) (V : HSp D) {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (ρ : GA D V →* (K →L[ℂ] K))
    (F : K) : Prop :=
  ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Mt V.rank), (∀ i, Xs i ∈ lieAt V (τs i)) →
    ContDiff ℝ ∞ fun t : Fin k → ℝ => ρ (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod F

def dL2 (θ : InfFam D) (V : HSp D) {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (ρ : GA D V →* (K →L[ℂ] K))
    (p : D.what₂.Tau × Mt V.rank) (F : K) : K :=
  deriv (fun t : ℝ => ρ (oneP θ V p.1 p.2 t) F) 0

structure GoodDict (θ : InfFam D) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ)
    {r : ℕ} (hr : V.rank = r) {Comp : Type} (X : Comp → ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E r)
    (la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r) (dict : GA D V → Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame (X k).Ψ r) (mu : GA D V → ℂ)
    (c : Comp → ℂ) (Kf : Subgroup (GA D V)) : Prop where
  inf : IsInfFam θ
  base : BaseFr M θ hr dict
  unif : ∃ th, (∀ k τ, IsInfEmb τ.1 (th k τ)) ∧ DictIsUnif V dict Kf th hr
  model : ∀ k, ModelW V hr (X k)
  muUnit : MuUnit V dict mu
  muCont : Continuous mu
  chi : ∀ k, ∀ γ ∈ (X k).Γ, (X k).χ (la k) γ = 1
  cNe : ∀ k, c k ≠ 0
  cBdd : ∃ C : ℝ, ∀ k, ‖c k‖ ≤ C
  fin : Finite Comp
  levFin : Kf ≤ GfC V
  levOpen : ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ k ∈ U, k ∈ GfC V → k ∈ Kf
  muK : ∀ k ∈ Kf, mu k = 1
  wt : ∃ e : D.what₂.Tau → ℤ, (∀ u ∈ GinfC V, mu u = ∏ ρ, (archM V (θ ρ) u).det ^ e ρ) ∧
    ∀ k ρ (τ : (X k).Ψ), τ.1 = tauE D ρ → ∀ a : Fin V.rank, w ρ a = la k τ (Fin.cast hr a) + e ρ

end Adelic

end GlobalTheory.HolDict
end
end
