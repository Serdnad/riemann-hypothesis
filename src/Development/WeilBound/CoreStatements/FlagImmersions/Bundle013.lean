module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle099
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle008
public import Development.AbelianVarietyTheory.Definitions.CMLattices.Bundle001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
import Mathlib.Algebra.AffineMonoid.Basic
public import Development.WeilBound.CoreStatements.FlagImmersions.Transport
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RiemannExtensionOfLogGrowth
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MvPolynomialEqZeroOfEventually
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle002
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle004

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl

namespace RootFieldNumerics.RF

def Tied {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
    {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ} {Ω : Type} [Field Ω]
    {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y) {F : Type} [Field F]
    (z : Spec (CommRingCat.of F) ⟶ 𝔐.X) (y₀ : Sp F ⟶ Xo.XF c) (vb : epsAt z ⟶ 𝔐.t.G)
    (v : epsAt (under y₀) ⟶ Xo.univ.t.G) : Prop :=
  ∃ v' : epsAt (y₀ ≫ Y.j) ⟶ Y.t.G, SameVec Y y₀ v v' ∧ vb.left ≫ 𝔐.m.φ = v'.left

def cP (p : ℕ) : ℝ := if p = 2 then 2 else 1 / ((p : ℝ) - 1)

def CptEx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) [NumberField c.F] (Y : Model Xo c (algebraMap (𝓞 c.F) c.F))
    (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)]
    (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y),
    ∃ (U : Set (Xo.XF c)) (Z : CptOver Y U), IsClopen U ∧ IsIrreducible U ∧ genPt 𝔐.ξ₀ = genPt (Z.ξ₀ ≫ Y.j)

def PeriodOf : Prop :=
  GlobalTheory.CompanionTheory.Ar.Top.Given →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) [NumberField c.F] (Y : Model Xo c (algebraMap (𝓞 c.F) c.F))
    (U : Set (Xo.XF c)) (Z : CptOver Y U), 1 ≤ D.p → 1 ≤ D.q → IsClopen U → IsIrreducible U → Z.IsGeom →
    ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n),
      IsTypeFn H D.p D.q ty ∧ ∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) →
        (Set.range y ⊆ U ↔ ∃ P, IsPeriod (FU.Di i) ty P ∧ under y = FU.u i P)

def SmoothLine : Prop :=
  ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type)
    [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (F' : Type) [Field F'] [NumberField F'] (ψ : F' →+* Ω) (L : Lat ξ Ω)
    (a : K → ℤ) (e₀ c₀ : Ω) (cinf : (F' →+* ℂ) → ℝ) (n : ℕ),
    (∀ q : X, genPt ξ ⤳ q) → (CoordTie ℤ ξ fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → NormalCpt ξ →
    OverInt y ψ → Birational y → IsArithVar (mCoordIdeal y) n → L.IsDegOn Set.univ y a e₀ →
    (∀ p ∈ genFibre ℤ ξ, L.IsGenAt p (c₀ * e₀)) → (∀ σ, 0 < cinf σ) →
    (∀ σ, cinf (ComplexEmbedding.conjugate σ) = cinf σ) →
    ∃ A : HermLine J, A.a = a ∧ IsSmoothHerm A ∧ IsConjInvariantH A ∧
      (∀ (σ : F' →+* ℂ) z (g h : MRing J) (dg dh : K → ℕ), PtOver y ψ σ z → IsMultiHomog g dg → IsMultiHomog h dh →
        (∀ k, (dg k : ℤ) - dh k = A.a k) → aeval y g = c₀ * aeval y h → ‖evC z g‖ = cinf σ * A.h z * ‖evC z h‖) ∧
      ∀ w ∈ mcPts (mCoordIdeal y), ∃ (g h : MRing J) (dg dh : K → ℕ), IsMultiHomog g dg ∧ IsMultiHomog h dh ∧
        (∀ k, (dg k : ℤ) - dh k = a k) ∧ aeval y g = c₀ * aeval y h ∧ evC w h ≠ 0

def PointEx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) [NumberField c.F] (Y : Model Xo c (algebraMap (𝓞 c.F) c.F))
    (U : Set (Xo.XF c)) (Z : CptOver Y U) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)]
    (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y)
    (F' : Type) [Field F'] [NumberField F'] (ψ : F' →+* Ω) (p : Nat.Primes) (κ' : F' →+* ℂ_[p]),
    genPt 𝔐.ξ₀ = genPt (Z.ξ₀ ≫ Y.j) →
    ∃ (V L : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field L) (_ : CharZero L)
      (_ : Algebra V L) (_ : IsFractionRing V L) (j : L →+* ℂ_[p]) (ψL : F' →+* L) (z : Spec (CommRingCat.of V) ⟶ 𝔐.X),
      (∀ a : L, ‖j a‖ ≤ 1 ↔ a ∈ (algebraMap V L).range) ∧ j.comp ψL = κ' ∧
      𝔐.Interior (Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ z) ∧
      (∀ a : F', ValAt 𝔐.ξ (Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ z) (ψ a) (ψL a)) ∧
      ∀ a : F', ‖κ' a‖ ≤ 1 → ψ a ∈ regAt 𝔐.ξ ⟨centre z, 𝔐.all _⟩

def ValuePhi : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) [NumberField c.F] (Y : Model Xo c (algebraMap (𝓞 c.F) c.F))
    (U : Set (Xo.XF c)) (Z : CptOver Y U) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)]
    (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y)
    (τ : CMType H) (i : Z.Ω →+* Ω) (j : Z.V →+ 𝔐.Li) (a : ⋀[Z.Ω]^D.p Z.V) (b : ⋀[Z.Ω]^D.q Z.V)
    (a' : ⋀[Ω]^D.p 𝔐.Li) (b' : ⋀[Ω]^D.q 𝔐.Li) (φ : FrameFn Xo c) (L : Type) [Field L] [CharZero L] (s : c.F →+* L)
    (z : Spec (CommRingCat.of L) ⟶ 𝔐.X) (bp : Fin D.p → 𝔐.Li) (bq : Fin D.q → 𝔐.Li)
    (vp : Fin D.p → (epsAt z ⟶ 𝔐.t.G)) (vq : Fin D.q → (epsAt z ⟶ 𝔐.t.G)) (α κ : Ω) (u : L),
    CptIn.IsTie Z 𝔐 i j → IsLineFn U τ.1 φ →
    IsLineGenOn (Z.eig τ.1) (Z.eig (ComplexEmbedding.conjugate τ.1)) D.p D.q a b Z.genFib →
    Represents Y U τ.1 Z.M a b φ → CptIn.IsPullWedge i j a a' → CptIn.IsPullWedge i j b b' → 𝔐.Interior z →
    (∀ x : c.F, ValAt 𝔐.ξ z (𝔐.cst x) (s x)) → (𝔐.V (.inl τ)).IsFrameAt bp ⟨centre z, 𝔐.all _⟩ →
    (𝔐.V (.inr τ)).IsFrameAt bq ⟨centre z, 𝔐.all _⟩ → (∀ k, 𝔐.M.ValAt z (bp k) (vp k)) →
    (∀ k, 𝔐.M.ValAt z (bq k) (vq k)) → a' = α • exteriorPower.ιMulti Ω _ bp → b' = κ • exteriorPower.ιMulti Ω _ bq →
    ValAt 𝔐.ξ z (α / κ) u →
    ∃ (y₀ : Sp L ⟶ Xo.XF c) (v : Vecs y₀ D.p) (w : Vecs y₀ D.q), z ≫ 𝔐.f = y₀ ≫ Y.j ∧ IsFramed U τ.1 s y₀ v w ∧
      φ L y₀ v w = u ∧ (∀ k, Tied 𝔐 z y₀ (vp k) (v k)) ∧ ∀ k, Tied 𝔐 z y₀ (vq k) (w k)

def IntFrames : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) [NumberField c.F] (Y : Model Xo c (algebraMap (𝓞 c.F) c.F))
    (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)]
    (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y)
    (V L : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field L] [CharZero L] [Algebra V L]
    [IsFractionRing V L] (z : Spec (CommRingCat.of V) ⟶ 𝔐.X) (y₀ : Sp L ⟶ Xo.XF c),
    (Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ z) ≫ 𝔐.f = y₀ ≫ Y.j →
    ∃ (T : SAB H (Sp V)) (tK : SAB H (Sp L)) (m : SABMap tK Xo.univ.t (under y₀))
      (m' : SABMap tK T (spMap (algebraMap V L))) (g : ℕ)
      (MC : LieModel 𝔐.t.G (Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ z) (Fin g → L))
      (MU : LieModel Xo.univ.t.G (under y₀) (Fin g → L)) (ρC : 𝓞 E →+* Module.End L (Fin g → L)),
      MC.IsActOf 𝔐.t.act.act ρC ∧ MU.IsActOf Xo.univ.t.act.act ρC ∧ (∀ e, Tied 𝔐 _ y₀ (MC.pt e) (MU.pt e)) ∧
      (∀ x, x ∈ 𝔐.M.fibAt 𝔐.M.lat z MC ↔ ∀ k, x k ∈ (algebraMap V L).range) ∧
      ∀ (σ : 𝓞 E →+* V) (n : ℕ) (x : Fin n → Fin g → L), LinearIndependent L x →
        Submodule.span V (Set.range x) =
          𝔐.M.fibAt 𝔐.M.lat z MC ⊓ (eigSp ρC ((algebraMap V L).comp σ)).restrictScalars V →
        IsIntFrame m m' ((algebraMap V L).comp σ) (fun k => MU.pt (x k))

def FibSandwich : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) [NumberField c.F] (Y : Model Xo c (algebraMap (𝓞 c.F) c.F))
    (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)]
    (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y)
    (V L : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field L] [CharZero L] [Algebra V L]
    [IsFractionRing V L] (p : Nat.Primes) (j : L →+* ℂ_[p]) (z : Spec (CommRingCat.of V) ⟶ 𝔐.X) (g : ℕ)
    (MC : LieModel 𝔐.t.G (Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ z) (Fin g → L))
    (ρC : 𝓞 E →+* Module.End L (Fin g → L)) (s : CMType H ⊕ CMType H) (σ : 𝓞 E →+* V)
    (b : Fin (labelRk D s) → 𝔐.Li),
    (∀ a : L, ‖j a‖ ≤ 1 ↔ a ∈ (algebraMap V L).range) → MC.IsActOf 𝔐.t.act.act ρC →
    (∀ a, ValAt 𝔐.ξ z (𝔐.emb s a) (σ a)) → (𝔐.V s).IsFrameAt b ⟨centre z, 𝔐.all _⟩ →
    ∃ x : Fin (labelRk D s) → Fin g → L,
      (∀ k, 𝔐.M.ValAt (Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ z) (b k) (MC.pt (x k))) ∧
      ((p : ℕ) ∉ S → ¬ ((p : ℕ) : ℤ) ∣ discr E → Submodule.span V (Set.range x) =
        𝔐.M.fibAt 𝔐.M.lat z MC ⊓ (eigSp ρC ((algebraMap V L).comp σ)).restrictScalars V) ∧
      ((p : ℕ) ∈ S → HT.HTFree 𝔐 p → ∀ (κ : Ω) (κz : V), HT.Sandwich 𝔐 p κ → ValAt 𝔐.ξ z κ κz →
        𝔐.M.fibAt 𝔐.M.lat z MC ⊓ (eigSp ρC ((algebraMap V L).comp σ)).restrictScalars V ≤
          Submodule.span V (Set.range x) ∧
        ∀ d : 𝓞 E, (s.isLeft → d ∈ differentIdeal ℤ (𝓞 E)) → ∀ w ∈ Submodule.span V (Set.range x),
          (κz * σ d) • w ∈ 𝔐.M.fibAt 𝔐.M.lat z MC ⊓ (eigSp ρC ((algebraMap V L).comp σ)).restrictScalars V)

def LocalCmp : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) [NumberField c.F] (Y : Model Xo c (algebraMap (𝓞 c.F) c.F))
    (U : Set (Xo.XF c)) (Z : CptOver Y U) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)]
    (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y)
    (Fl : 𝔐.Flag) (τ : CMType H) (i : Z.Ω →+* Ω) (j : Z.V →+ 𝔐.Li) (a : ⋀[Z.Ω]^D.p Z.V) (b : ⋀[Z.Ω]^D.q Z.V)
    (a' : ⋀[Ω]^D.p 𝔐.Li) (b' : ⋀[Ω]^D.q 𝔐.Li) (d₁ d₂ : Ω) (φ : FrameFn Xo c)
    (F' : Type) [Field F'] [NumberField F'] (ι : c.F →+* F') (ψ : F' →+* Ω) (p : Nat.Primes) (κ' : F' →+* ℂ_[p])
    (π : F') (m : ℕ) (k : ℤ) (t : ℝ),
    genPt 𝔐.ξ₀ = genPt (Z.ξ₀ ≫ Y.j) → CptIn.IsTie Z 𝔐 i j → IsLineFn U τ.1 φ →
    IsLineGenOn (Z.eig τ.1) (Z.eig (ComplexEmbedding.conjugate τ.1)) D.p D.q a b Z.genFib →
    Represents Y U τ.1 Z.M a b φ → CptIn.IsPullWedge i j a a' → CptIn.IsPullWedge i j b b' → d₁ ≠ 0 → d₂ ≠ 0 →
    a' = d₁ • (exteriorPower.ιMulti Ω _ (Fl.b (.inl τ))) → b' = d₂ • (exteriorPower.ιMulti Ω _ (Fl.b (.inr τ))) →
    a' ≠ 0 → b' ≠ 0 → ψ.comp ι = 𝔐.cst → π ≠ 0 → 0 < m →
    (∀ x : Cpt 𝔐.ξ, (∀ u : F', ‖κ' u‖ ≤ 1 → ψ u ∈ regAt 𝔐.ξ x) →
      OrderAt (lineLat (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) (labelRk D (.inl τ)) (labelRk D (.inr τ))
        (exteriorPower.ιMulti Ω _ (Fl.b (.inl τ))) (exteriorPower.ιMulti Ω _ (Fl.b (.inr τ)))) (d₁ / d₂) (ψ π) m k x) →
    HasFinNorm U τ.1 φ p (κ'.comp ι) t →
    ((p : ℕ) ∉ S → ¬ ((p : ℕ) : ℤ) ∣ discr E → (k : ℝ) / m * Real.log ‖κ' π‖ = t) ∧
    ((p : ℕ) ∈ S → HT.HTFree 𝔐 p → ∀ κ : Ω, HT.IsCp p κ → HT.Sandwich 𝔐 p κ →
      ∀ d ∈ differentIdeal ℤ (𝓞 E), d ≠ 0 → |(k : ℝ) / m * Real.log ‖κ' π‖ - t| ≤
        ((D.p + D.q : ℕ) : ℝ) * (cP p * Real.log (p : ℕ) - Real.log ‖κ' (ι (tauIn c τ.1 d))‖))

def ChiEx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [NeZero H.d], ∃ χ : DirichletCharacter ℂ H.d,
    GlobalTheory.IsKroneckerChar χ ∧ (GlobalTheory.CM.logOm E χ).re =
      Real.eulerMascheroniConstant + Real.log (2 * Real.pi) - Real.log (hostRd E) - hostLval H

def Numerics : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (p q : ℕ) (F F' : Type) [Field F] [NumberField F]
    [Field F'] [NumberField F'] (ι : F →+* F') (σ : 𝓞 E →+* F) (N : LogNorms F)
    (r : HeightOneSpectrum (𝓞 F') →₀ ℚ) (bad : Finset ℕ), Function.Injective σ → 2 ∈ bad → (∀ ℓ ∈ bad, ℓ.Prime) →
    N.IsAdelic → N.deg = ((p : ℝ) - q) / 2 *
      (Real.eulerMascheroniConstant + Real.log (2 * Real.pi) - Real.log (hostRd E) - hostLval H) →
    (∀ (ℓ : Nat.Primes) (κ' : F' →+* ℂ_[ℓ]) (v : HeightOneSpectrum (𝓞 F')) (π : F'),
      (∀ a : F', v.valuation F' a ≤ 1 ↔ ‖κ' a‖ ≤ 1) → v.valuation F' π = WithZero.exp (-1 : ℤ) →
      ((ℓ : ℕ) ∉ bad → (r v : ℝ) * Real.log ‖κ' π‖ = N.fin ℓ (κ'.comp ι)) ∧
      ((ℓ : ℕ) ∈ bad → ∀ d ∈ differentIdeal ℤ (𝓞 E), d ≠ 0 → |(r v : ℝ) * Real.log ‖κ' π‖ - N.fin ℓ (κ'.comp ι)| ≤
        ((p + q : ℕ) : ℝ) * (cP ℓ * Real.log (ℓ : ℕ) - Real.log ‖κ' (ι (σ d))‖))) →
    NearRecord (p + q) bad (hostRd E) (hostLval H)
      (((r.sum fun v x => (x : ℝ) * Real.log (Ideal.absNorm v.asIdeal)) - ∑ s : F' →+* ℂ, N.inf (s.comp ι)) /
        (Module.finrank ℚ F' : ℝ))

end RootFieldNumerics.RF
end
end

section

noncomputable section

namespace RootFieldNumerics

open Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M

namespace Desc

variable {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem contAt_of_holoOn (A : FinHolAtlas e X) {U : Set X} {f : X → ℂ} (hf : A.HoloOn U f) {x : X} (hx : x ∈ U) :
    ContinuousAt f x := by
  obtain ⟨k, hk⟩ := A.cover x
  have h1 := (hf k (A.chart k x) ⟨(A.chart k).map_source hk, by
    show (A.chart k).symm (A.chart k x) ∈ U
    rwa [(A.chart k).left_inv hk]⟩).continuousAt
  have h2 := h1.comp ((A.chart k).continuousAt hk)
  refine h2.congr ?_
  filter_upwards [(A.chart k).open_source.mem_nhds hk] with x' hx'
  simp [(A.chart k).left_inv hx']

theorem analytic_off {A : FinHolAtlas e X} {B : FinHolAtlas e Y} {h : Y → X} {S U : Set X} {f : Y → ℂ}
    (hh : HoloMap B A h) (hd : IsDegreeOff A B h 1 S) (hf : B.HoloOn (h ⁻¹' U) f) (σ : X → Y)
    (hσ : ∀ x ∉ S, h (σ x) = x) (hσ' : ∀ y, h y ∉ S → σ (h y) = y) (k : Fin A.n) {q : Fin e → ℂ}
    (hq : q ∈ (A.chart k).target) (hU : (A.chart k).symm q ∈ U) (hS : (A.chart k).symm q ∉ S) :
    AnalyticAt ℂ (fun t => f (σ ((A.chart k).symm t))) q := by
  have hSc : IsClosed S := isClosed_of_isAnalyticSubset' A hd.1
  set x := (A.chart k).symm q with hx
  obtain ⟨j, hj⟩ := B.cover (σ x)
  set p := B.chart j (σ x) with hp
  have hpt : p ∈ (B.chart j).target := (B.chart j).map_source hj
  have hsp : (B.chart j).symm p = σ x := (B.chart j).left_inv hj
  have hxs : x ∈ (A.chart k).source := (A.chart k).map_target hq
  have hhs : h ((B.chart j).symm p) ∈ (A.chart k).source := by rw [hsp, hσ x hS]; exact hxs
  let φ : (Fin e → ℂ) → Fin e → ℂ := A.chart k ∘ h ∘ (B.chart j).symm
  have hφ : AnalyticAt ℂ φ p := hh.2 j k p ⟨hpt, hhs⟩
  have hφp : φ p = q := by
    show A.chart k (h ((B.chart j).symm p)) = q
    rw [hsp, hσ x hS, hx, (A.chart k).right_inv hq]
  have hdet := hd.2.2.2.2.2 j k p hpt (by
    show h ((B.chart j).symm p) ∉ S
    rwa [hsp, hσ x hS]) hhs
  let L : (Fin e → ℂ) ≃L[ℂ] (Fin e → ℂ) := (fderiv ℂ φ p).toContinuousLinearEquivOfDetNeZero hdet
  have hL : HasFDerivAt φ (L : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) p := by
    have := hφ.differentiableAt.hasFDerivAt
    simpa [L] using this
  have hc : ContDiffAt ℂ ⊤ φ p := hφ.contDiffAt
  have hn : (⊤ : WithTop ℕ∞) ≠ 0 := by simp
  let ψ := hc.localInverse hL hn
  have hψ : AnalyticAt ℂ ψ q := by
    have := (hc.to_localInverse hL hn).analyticAt
    rwa [hφp] at this
  have hψq : ψ q = p := by
    rw [← hφp]
    exact hc.localInverse_apply_image hL hn
  have hri : ∀ᶠ t in 𝓝 q, φ (ψ t) = t := by
    have := (hc.hasStrictFDerivAt' hL hn).eventually_right_inverse
    rw [hφp] at this
    exact this
  have hfa : AnalyticAt ℂ (f ∘ (B.chart j).symm) (ψ q) := by
    rw [hψq]
    refine hf j p ⟨hpt, ?_⟩
    show h ((B.chart j).symm p) ∈ U
    rwa [hsp, hσ x hS]
  refine (hfa.comp hψ).congr ?_
  have c1 : ContinuousAt (fun t => h ((B.chart j).symm (ψ t))) q :=
    hh.1.continuousAt.comp (ContinuousAt.comp (by rw [hψq]; exact (B.chart j).continuousAt_symm hpt) hψ.continuousAt)
  have e1 : ∀ᶠ t in 𝓝 q, h ((B.chart j).symm (ψ t)) ∈ (A.chart k).source ∩ Sᶜ :=
    c1.eventually_mem (((A.chart k).open_source.inter hSc.isOpen_compl).mem_nhds (by
      show h ((B.chart j).symm (ψ q)) ∈ _
      rw [hψq, hsp, hσ x hS]
      exact ⟨hxs, hS⟩))
  filter_upwards [hri, e1] with t h1 h2
  have h3 : (A.chart k).symm t = h ((B.chart j).symm (ψ t)) := by
    rw [← (A.chart k).left_inv h2.1]
    exact congrArg _ h1.symm
  show f ((B.chart j).symm (ψ t)) = f (σ ((A.chart k).symm t))
  rw [h3, hσ' _ h2.2]

theorem local_ext {A : FinHolAtlas e X} {S U : Set X} {u : X → ℂ} (hS : A.IsAnalyticSubset S) (hi : interior S = ∅)
    (hU : IsOpen U) (k : Fin A.n)
    (ha : ∀ q ∈ (A.chart k).target, (A.chart k).symm q ∈ U → (A.chart k).symm q ∉ S →
      AnalyticAt ℂ (fun t => u ((A.chart k).symm t)) q)
    (hb : ∀ x ∈ U, ∃ C : ℝ, ∀ᶠ x' in 𝓝 x, x' ∉ S → ‖u x'‖ ≤ C) {q : Fin e → ℂ} (hq : q ∈ (A.chart k).target)
    (hqU : (A.chart k).symm q ∈ U) :
    ∃ w : (Fin e → ℂ) → ℂ, AnalyticAt ℂ w q ∧ ∀ᶠ t in 𝓝 q, (A.chart k).symm t ∉ S → w t = u ((A.chart k).symm t) := by
  by_cases hqS : (A.chart k).symm q ∈ S
  swap
  · exact ⟨_, ha q hq hqU hqS, Eventually.of_forall fun _ _ => rfl⟩
  obtain ⟨W, hW, hqW, hWc, φ, hφ, ⟨w₀, hw₀, hw₀'⟩, hz⟩ := analyticSubset_chart_local A hS hi k (z := q)
    ⟨_, ⟨hqS, (A.chart k).map_target hq⟩, (A.chart k).right_inv hq⟩
  let U' := W ∩ ((A.chart k).target ∩ (A.chart k).symm ⁻¹' U)
  have hU' : IsOpen U' := hW.inter ((A.chart k).isOpen_inter_preimage_symm hU)
  have hns : ∀ b ∈ U', φ b ≠ 0 → (A.chart k).symm b ∉ S := fun b hb h0 hs =>
    h0 (hz b ⟨⟨_, ⟨hs, (A.chart k).map_target hb.2.1⟩, (A.chart k).right_inv hb.2.1⟩, hb.1⟩)
  have hden : U' ⊆ closure {b ∈ U' | φ b ≠ 0} := fun b hb => by
    by_contra hn
    have h1 : ∀ᶠ b' in 𝓝 b, b' ∉ {b ∈ U' | φ b ≠ 0} := by
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hn] with b' hb' h using hb' (subset_closure h)
    have h2 : φ =ᶠ[𝓝 b] 0 := by
      filter_upwards [h1, hU'.mem_nhds hb] with b' h h'
      by_contra h0
      exact h ⟨h', h0⟩
    exact hw₀' (hφ.eqOn_zero_of_preconnected_of_eventuallyEq_zero hWc hb.1 h2 hw₀)
  obtain ⟨u', hu', he⟩ := GlobalTheory.LogExt.riemann_extension_log _ U' φ (fun t => u ((A.chart k).symm t)) hU'
    (hφ.differentiableOn.mono Set.inter_subset_left)
    (fun b hb => (ha b hb.1.2.1 hb.1.2.2 (hns b hb.1 hb.2)).differentiableAt.differentiableWithinAt) hden
    (fun b hb' => by
      obtain ⟨C, hC⟩ := hb _ hb'.2.2
      refine ⟨C, 0, ?_⟩
      filter_upwards [((A.chart k).continuousAt_symm hb'.2.1).eventually hC, hU'.mem_nhds hb'] with t h1 h2 h0
      simpa using h1 (hns t h2 h0))
  have hq' : q ∈ U' := ⟨hqW, hq, hqU⟩
  refine ⟨u', GlobalTheory.SCV.analyticOnNhd_of_differentiableOn hU' hu' q hq', ?_⟩
  filter_upwards [hU'.mem_nhds hq'] with t ht hts
  have : (𝓝[{b ∈ U' | φ b ≠ 0}] t).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (hden ht)
  refine tendsto_nhds_unique_of_eventuallyEq (l := 𝓝[{b ∈ U' | φ b ≠ 0}] t)
    ((hu'.continuousOn.continuousAt (hU'.mem_nhds ht)).tendsto.mono_left nhdsWithin_le_nhds)
    ((ha t ht.2.1 ht.2.2 hts).continuousAt.tendsto.mono_left nhdsWithin_le_nhds) ?_
  filter_upwards [self_mem_nhdsWithin] with b hb using he hb

theorem ext_manifold {A : FinHolAtlas e X} {S U : Set X} {u : X → ℂ} (hS : A.IsAnalyticSubset S) (hi : interior S = ∅)
    (hU : IsOpen U)
    (ha : ∀ k, ∀ q ∈ (A.chart k).target, (A.chart k).symm q ∈ U → (A.chart k).symm q ∉ S →
      AnalyticAt ℂ (fun t => u ((A.chart k).symm t)) q)
    (hb : ∀ x ∈ U, ∃ C : ℝ, ∀ᶠ x' in 𝓝 x, x' ∉ S → ‖u x'‖ ≤ C) :
    ∃ F : X → ℂ, A.HoloOn U F ∧ ∀ x ∈ U, x ∉ S → F x = u x := by
  have hden : Dense Sᶜ := interior_eq_empty_iff_dense_compl.1 hi
  let F : X → ℂ := fun x => limUnder (𝓝[Sᶜ] x) u
  have key : ∀ k, ∀ q ∈ (A.chart k).target, (A.chart k).symm q ∈ U → ∃ w : (Fin e → ℂ) → ℂ, AnalyticAt ℂ w q ∧
      (∀ᶠ t in 𝓝 q, (A.chart k).symm t ∉ S → w t = u ((A.chart k).symm t)) ∧
      ∀ᶠ t in 𝓝 q, w t = F ((A.chart k).symm t) := fun k q hq hqU => by
    obtain ⟨w, hw, he⟩ := local_ext hS hi hU k (ha k) hb hq hqU
    refine ⟨w, hw, he, ?_⟩
    filter_upwards [he.eventually_nhds, hw.eventually_analyticAt, (A.chart k).open_target.mem_nhds hq] with t h1 h2 h3
    have hs := (A.chart k).map_target h3
    have hr := (A.chart k).right_inv h3
    have : (𝓝[Sᶜ] ((A.chart k).symm t)).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (hden _)
    have hc : Tendsto (A.chart k) (𝓝 ((A.chart k).symm t)) (𝓝 t) := by
      have := ((A.chart k).continuousAt hs).tendsto
      rwa [hr] at this
    refine (Tendsto.limUnder_eq ?_).symm
    refine ((h2.continuousAt.tendsto.comp hc).mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [nhdsWithin_le_nhds (hc.eventually h1), nhdsWithin_le_nhds ((A.chart k).open_source.mem_nhds hs),
      self_mem_nhdsWithin] with x h4 h5 h6
    have h7 : (A.chart k).symm (A.chart k x) ∉ S → w (A.chart k x) = u ((A.chart k).symm (A.chart k x)) := h4
    rw [(A.chart k).left_inv h5] at h7
    exact h7 h6
  refine ⟨F, fun k q hq => ?_, fun x hx hxS => ?_⟩
  · obtain ⟨w, hw, -, he⟩ := key k q hq.1 hq.2
    exact hw.congr he
  · obtain ⟨k, hk⟩ := A.cover x
    have hl := (A.chart k).left_inv hk
    obtain ⟨w, -, h1, h2⟩ := key k _ ((A.chart k).map_source hk) (by rwa [hl])
    have h3 := h1.self_of_nhds
    have h4 := h2.self_of_nhds
    rw [hl] at h3 h4
    rw [← h4, h3 hxS]

end Desc

open Desc in
theorem descend : Descend := by
  intro e X Y _ _ _ _ _ _ A B h S U f hh hd hU hf
  classical
  rcases isEmpty_or_nonempty Y with hY | hY
  · refine ⟨0, fun k => ?_, fun y => isEmptyElim y⟩
    exact analyticOnNhd_const
  have hex : ∀ x, ∃ y, x ∉ S → h ⁻¹' {x} = {y} := fun x => by
    by_cases hx : x ∈ S
    · exact ⟨hY.some, fun h' => (h' hx).elim⟩
    · obtain ⟨y, hy⟩ := Set.ncard_eq_one.1 (hd.2.2.2.2.1 x hx)
      exact ⟨y, fun _ => hy⟩
  choose σ hσ₀ using hex
  have hσ : ∀ x ∉ S, h (σ x) = x := fun x hx => by
    have : σ x ∈ h ⁻¹' {x} := by rw [hσ₀ x hx]; rfl
    exact this
  have hσ' : ∀ y, h y ∉ S → σ (h y) = y := fun y hy => by
    have : y ∈ h ⁻¹' {h y} := rfl
    rw [hσ₀ _ hy] at this
    exact this.symm
  have hfc : ContinuousOn f (h ⁻¹' U) := fun y hy => (contAt_of_holoOn B hf hy).continuousWithinAt
  obtain ⟨F, hF, he⟩ := ext_manifold (u := fun x => f (σ x)) hd.1 hd.2.1 hU
    (fun k q hq h1 h2 => analytic_off hh hd hf σ hσ hσ' k hq h1 h2) (fun x hx => by
      obtain ⟨K, hK, hKU, hKc⟩ := local_compact_nhds (hU.mem_nhds hx)
      have hc : IsCompact (h ⁻¹' K) := (hKc.isClosed.preimage hh.1).isCompact
      obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn (hfc.mono (Set.preimage_mono hKU))
      refine ⟨C, ?_⟩
      filter_upwards [hK] with x' h1 h2
      exact hC _ (by show h (σ x') ∈ K; rwa [hσ x' h2]))
  refine ⟨F, hF, fun y hy => ?_⟩
  have hden : Dense (h ⁻¹' S)ᶜ := interior_eq_empty_iff_dense_compl.1 hd.2.2.2.1
  have ho : IsOpen (h ⁻¹' U) := hU.preimage hh.1
  refine Set.EqOn.of_subset_closure (f := fun y => F (h y)) (g := f) (s := h ⁻¹' U ∩ (h ⁻¹' S)ᶜ) (t := h ⁻¹' U)
    (fun y' hy' => ?_) (fun y' hy' => ?_) hfc Set.inter_subset_left (hden.open_subset_closure_inter ho) hy
  · show F (h y') = f y'
    rw [he _ hy'.1 hy'.2, hσ' _ hy'.2]
  · exact ((contAt_of_holoOn A hF hy').comp hh.1.continuousAt).continuousWithinAt

end RootFieldNumerics
end
end

section

namespace RootFieldNumerics

theorem rankLem : RankLem := fun _ _ _ _ hV hne hΦ hc =>
  GlobalTheory.CountableFibres.exists_injective_fderiv hV hne (fun z hz => (hΦ z hz).contDiffAt) hc

end RootFieldNumerics
end
