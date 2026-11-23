module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Bundle001
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
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

@[expose] public section

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

def IsCp {Ω : Type} [CommRing Ω] (p : ℕ) (κ : Ω) : Prop :=
  if p = 2 then κ = 4 else ∃ ζ : Ω, IsPrimitiveRoot ζ p ∧ κ = ζ - 1

abbrev cmConj (E : Type) [Field E] [NumberField E] [IsCMField E] : E ≃+* E := (IsCMField.complexConj E).toRingEquiv

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y)

abbrev omP (p : ℕ) : Lat 𝔐.ξ (Module.Dual Ω 𝔐.Li) := 𝔐.M.htOm 𝔐.t.PP.L (p ^ 𝔐.R p)

def HTFree (p : ℕ) : Prop :=
  (omP 𝔐 p).IsVBOn {q | InFibre 𝔐.ξ p q} (Module.finrank Ω 𝔐.Li) ⊤ ∧
    ∀ s, ((omP 𝔐 p).map (𝔐.Vgen s).dualRestrict).IsVBOn {q | InFibre 𝔐.ξ p q} (labelRk D s) ⊤

def OverZp (p : ℕ) (q : Cpt 𝔐.ξ) : Prop := ∀ r : ℕ, r.Prime → InFibre 𝔐.ξ r q → r = p

structure IsHTFamily (p : ℕ) (o : Type) [CommRing o] [Algebra o Ω]
    (Dc : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0},
      HTChart (chartRing o (mseg y) s.1) Ω (cmConj E) p (𝔐.R p) (D.p + D.q) (Module.Dual Ω 𝔐.Li)) : Prop where
  act : ∀ s (a : 𝓞 E) (w : Module.Dual Ω 𝔐.Li), (Dc s).ρΩ a w = w ∘ₗ 𝔐.ρ (H.bar a)
  e_eq : ∀ s t, (Dc s).e = (Dc t).e
  om_iff : ∀ s w, w ∈ (Dc s).om ↔ ∀ q, InChart 𝔐.ξ (mseg y) s.1 q → OverZp 𝔐 p q → w ∈ 𝔐.M.omLat q
  om_loc : ∀ s q, InChart 𝔐.ξ (mseg y) s.1 q → OverZp 𝔐 p q →
    𝔐.M.omLat q = Submodule.span (regAt 𝔐.ξ q) ((Dc s).om : Set (Module.Dual Ω 𝔐.Li))
  om'_loc : ∀ s q, InChart 𝔐.ξ (mseg y) s.1 q → InFibre 𝔐.ξ p q →
    omP 𝔐 p q = Submodule.span (regAt 𝔐.ξ q) ((Dc s).om' : Set (Module.Dual Ω 𝔐.Li))
  glue : ∀ s t q, InChart 𝔐.ξ (mseg y) s.1 q → InChart 𝔐.ξ (mseg y) t.1 q → OverZp 𝔐 p q →
    ∀ x, ∃ w ∈ 𝔐.M.omLat q, (Dc s).h x = (Dc t).h x + (p ^ 𝔐.R p) • w

def Sandwich (p : ℕ) (κ : Ω) : Prop :=
  ∀ q, InFibre 𝔐.ξ p q → κ ∈ regAt 𝔐.ξ q ∧ omP 𝔐 p q ≤ 𝔐.M.omLat q ∧ (∀ w ∈ 𝔐.M.omLat q, κ • w ∈ omP 𝔐 p q) ∧
    ∀ s, 𝔐.dR s q ≤ 𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s) q ∧
      ∀ e ∈ 𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s) q, κ • e ∈ 𝔐.dR s q

end GlobalTheory.CompanionTheory.Ar.HT
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

abbrev RootIx (D : Datum H) : Type := CMType H × Fin (D.p + D.q)

structure FixedData (Y : Model Xo c β)
    (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) where

  Ωf : Type
  [fld : Field Ωf]

  ξf : Spec (CommRingCat.of Ωf) ⟶ Y.X

  Lif : Type
  [acg : AddCommGroup Lif]
  [mod : Module Ωf Lif]
  Mf : LieModel Y.t.G ξf Lif

  bf : ∀ s, Fin (labelRk D s) → Lif

  m : ℕ

  yf : Fin (m + 1) → Ωf
  generate : Subfield.closure (Set.range fun ij : Fin (m + 1) × Fin (m + 1) => yf ij.1 / yf ij.2) = ⊤

  hf : (Fin (m + 1) → ℂ) → ℝ

  kA : ℕ

  pt : Sys.X → Fin (m + 1) → ℂ
  pt_ne : ∀ x, pt x ≠ 0
  pt_inj : ∀ x x' (a : ℂ), pt x = a • pt x' → x = x'
  pos : ReciprocityTheory.AnForm.M.IsPosPot Sys.A (Sys.th none)
  ph_none : ∀ x, Sys.ph none x = 0 ∧ ∀ t, Sys.phT none t x = 0

  q' : ℕ
  q'_pos : 0 < q'

  n : RootIx D → ℤ

  sE : Ωf
  sE_ne : sE ≠ 0

attribute [instance] FixedData.fld FixedData.acg FixedData.mod

structure RootOrigin (Y : Model Xo c β) (S : Finset ℕ) (RM : Top.RootModel (CMType H) (D.p + D.q))
    {Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))} (Fx : FixedData Y Sys) where

  𝔐 : HodgeCpt Y S RM.y

  Fl : 𝔐.Flag

  g : Fx.Ωf →+* RM.Ω
  g_over : 𝔐.ξ ≫ 𝔐.f = spMap g ≫ Fx.ξf
  g_flag : ∀ s i, (𝔐.M.pt (Fl.b s i)).left ≫ 𝔐.m.φ = spMap (dualMap g) ≫ (Fx.Mf.pt (Fx.bf s i)).left
  g_deg : letI := g.toAlgebra; Module.finrank Fx.Ωf RM.Ω = Fl.deg
  g_const : ∀ a : Fx.Ωf, IsAlgebraic ℤ a → g a ∈ 𝔐.cst.range
  δ_eq : RM.δ = Module.finrank ℚ c.F * Fl.deg

  e : RootIx D → RM.Ω
  lines : Fl.RootLines RM.xdeg e

  sing : RootIx D → HermLine RM.ι
  sing_deg : ∀ r, (sing r).a = RM.xdeg r
  hodge : ∀ r, Fl.IsHodgeLine r (e r) (sing r)

  k₀ : RM.K

  ix : Fin (Fx.m + 1) ≃ RM.ι k₀
  y_eq : ∀ i, RM.y ⟨k₀, ix i⟩ = g (Fx.yf i)
  kA_eq : RM.kA = Fx.kA
  A_deg : RM.A.a k₀ = 1 ∧ ∀ k, k ≠ k₀ → RM.A.a k = 0
  A_h : ∀ z ∈ mcPts RM.P, RM.A.h z = Fx.hf fun i => z ⟨k₀, ix i⟩

  eff : ∀ p : Cpt 𝔐.ξ, (∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r p) → ∀ (i : Fin (Fx.m + 1)) (t : RM.Ω),
    InChart 𝔐.ξ (fun i' => g (Fx.yf i')) i p → (Lat.tens Fl.rootLat fun r => -Fx.n r).IsGenAt p t →
      g Fx.sE * g (Fx.yf i) ^ Fx.q' / t ∈ regAt 𝔐.ξ p ∧
        (p.1 ∉ abLocus 𝔐.t.G → ¬ unitAt 𝔐.ξ p (g Fx.sE * g (Fx.yf i) ^ Fx.q' / t))

  Re : PB.Realis Sys RM.P
  Re_deg : Re.deg = Fl.deg
  π_pt : ∀ x, ∃ a : ℂ, (fun i => Re.R.lift x x ⟨k₀, ix i⟩) = a • Fx.pt (Re.π x)
  interior : ∀ x (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X), CoordsAt 𝔐.ξ RM.y z (Re.R.lift x x) →
    (𝔐.Interior z ↔ Re.π x ∈ Sys.open')
  fund_deg : ∀ τ i, (Re.ref (some (τ, i))).a = -∑ k ∈ Finset.Iic i, RM.xdeg (τ, k)
  fund_sing : ∀ τ i x, Re.π x ∈ Sys.open' →
    Real.log ((Re.ref (some (τ, i))).h (Re.R.lift x x)) + Sys.ph (some (τ, i)) (Re.π x) =
      -∑ k ∈ Finset.Iic i, Real.log ((sing (τ, k)).h (Re.R.lift x x))
  fund_reg : ∀ τ i t, 0 < t → t ≤ Sys.t₀ → ∀ z ∈ mcPts RM.P,
    Real.log ((Re.line (some (τ, i)) t).h z) = -∑ k ∈ Finset.Iic i, Real.log ((RM.x t (τ, k)).h z)
  ref_none : (Re.ref none).a = RM.A.a ∧ ∀ z ∈ mcPts RM.P, (Re.ref none).h z = RM.A.h z

structure TowerOrigin (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (T : Top.RootTower (CMType H) (D.p + D.q)) where
  j_eq : T.j = D.p
  bad_iff : ∀ r : ℕ, r ∈ T.bad ↔ r.Prime ∧ (r : ℤ) ∣ 2 * discr E * l.M'

  S : ℕ → Finset ℕ
  S_iff : ∀ B r, r ∈ S B ↔ T.InS B r

  Sys : T.Comp → PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))

  Fx : ∀ a, FixedData Y (Sys a)
  comp_inj : ∀ a a', genPt (Fx a).ξf = genPt (Fx a').ξf → a = a'
  comp_onto : ∀ x : Y.X, (∀ x' : Y.X, x' ⤳ x → x' = x) → ∃ a, genPt (Fx a).ξf = x
  nu_eq : ∀ a r, ((Fx a).n r : ℝ) = ((Fx a).kA * (Fx a).q' : ℕ) * T.nu r.1 r.2

  Or : ∀ B a, RootOrigin Y (S B) (T.M B a) (Fx a)

def hostRd (E : Type) [Field E] [NumberField E] : ℝ := |(discr E : ℝ)| ^ (1 / (Module.finrank ℚ E : ℝ))

def hostLval (H : Host E) : ℝ :=
  haveI : Fact H.d.Prime := ⟨H.d_prime⟩
  let χ : DirichletCharacter ℂ H.d := (quadraticChar (ZMod H.d)).ringHomComp (Int.castRingHom ℂ)
  (deriv χ.LFunction 1 / χ.LFunction 1).re

end GlobalTheory.CompanionTheory.Ar
end
end

section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar.Num

noncomputable section

section General

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

def overPrime (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : ℕ) : Set (Cpt ξ) :=
  {q | ∀ p' : ℕ, p'.Prime → p' ≠ p → ¬ InFibre ξ p' q}

def IsLatFlagPair {E : Type} [AddCommGroup E] [Module Ω E] {K : Type} [Fintype K] [DecidableEq K] {J : K → Type}
    (y : (Σ k, J k) → Ω) (T : Set (Cpt ξ)) (L L' : Lat ξ E) {r : ℕ} (b : Fin r → E) (Q : LocPair J ℤ (Fin r)) : Prop :=
  L.IsFlagVBOn T b ∧ L'.IsFlagVBOn T b ∧ ∀ i, ∃ e e' : Ω,
    (L.gr b i).IsDegOn T y (Q.x i) e ∧ (L'.gr b i).IsDegOn T y (Q.x' i) e' ∧
    (∃ bf bg : K → ℕ, GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (Q.f i) bf ∧
      GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (Q.g i) bg ∧ (fun k => (bf k : ℤ) - bg k) = Q.x i - Q.x' i) ∧
    aeval y (Q.g i) ≠ 0 ∧ aeval y (Q.f i) = e' / e * aeval y (Q.g i)

end General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

def IsFrobLabels (c : Coeff l) (p : ℕ) (φ : Equiv.Perm (CMType H ⊕ CMType H)) : Prop :=
  ∀ n : Ideal (𝓞 c.F), n.IsPrime → (p : 𝓞 c.F) ∈ n → ∀ s (a : 𝓞 E) (u v : 𝓞 c.F),
    (u : c.F) = labelEmb c (φ s) a → (v : c.F) = labelEmb c s a → u - v ^ p ∈ n

variable {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Y : Model Xo c β} {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type}
  {y : (Σ k, J k) → Ω}

namespace HodgeCpt

def VAt (𝔐 : HodgeCpt Y S y) (S₀ : Finset ℕ) (s : CMType H ⊕ CMType H) : Lat 𝔐.ξ 𝔐.Li :=
  Lat.patch S₀ (𝔐.dR s) fun p => 𝔐.HT p s

def shrink (𝔐 : HodgeCpt Y S y) (S₀ : Finset ℕ) (h : S₀ ⊆ S)
    (hvb : ∀ s, (𝔐.VAt S₀ s).IsVB (labelRk D s) (𝔐.Vgen s)) : HodgeCpt Y S₀ y :=
  { 𝔐 with
    S_prime := fun p hp => 𝔐.S_prime p (h hp)
    R_ge := fun p hp => 𝔐.R_ge p (h hp)
    tors := fun p hp => 𝔐.tors p (h hp)
    vb := hvb }

def Flag.shrink {𝔐 : HodgeCpt Y S y} (Fl : 𝔐.Flag) (S₀ : Finset ℕ) (h : S₀ ⊆ S)
    (hvb : ∀ s, (𝔐.VAt S₀ s).IsVB (labelRk D s) (𝔐.Vgen s))
    (hsub : ∀ s, (𝔐.VAt S₀ s).IsFlagVBOn Set.univ (Fl.b s)) : (𝔐.shrink S₀ h hvb).Flag :=
  @Flag.mk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (𝔐.shrink S₀ h hvb) Fl.b hsub Fl.Li₀ Fl.acg Fl.mod Fl.M₀ Fl.j
    Fl.j_pt Fl.V₀ Fl.V₀_mem Fl.deg Fl.generic

def Flag.TwoLevels [DecidableEq K] {𝔐 : HodgeCpt Y S y} (Fl : 𝔐.Flag) (S₀ : Finset ℕ)
    (T : LocPair J ℤ (CMType H × Fin (D.p + D.q))) : Prop :=
  ∃ (h : S₀ ⊆ S) (hvb : ∀ s, (𝔐.VAt S₀ s).IsVB (labelRk D s) (𝔐.Vgen s))
    (hsub : ∀ s, (𝔐.VAt S₀ s).IsFlagVBOn Set.univ (Fl.b s)) (e₀ e : CMType H × Fin (D.p + D.q) → Ω),
    (Fl.shrink S₀ h hvb hsub).RootLines T.x e₀ ∧ Fl.RootLines T.x' e ∧
    (∀ r, aeval y (T.f r) = e r / e₀ r * aeval y (T.g r)) ∧
    T.IsVertOff (mCoordIdeal y) ((S \ S₀).preimage (fun p : Nat.Primes => (p : ℕ)) Subtype.val_injective.injOn)

end HodgeCpt

end

end GlobalTheory.CompanionTheory.Ar
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

abbrev CFn (Xo : Moduli D l) (c : Coeff l) : Type := ∀ y : Sp ℂ ⟶ Xo.XF c, Vecs y D.p → Vecs y D.q → ℂ

variable {Xo : Moduli D l} {c : Coeff l}

def IsFlatAn (U : Set (Xo.XF c)) (τ τ' : E →+* ℂ) (σ : c.F →+* ℂ) (Φ : CFn Xo c) {σK : KA l →+* ℂ} {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} (FU : FamilyUnif Xo σK ty) (i : Fin FU.n)
    (e : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (ρ : ℂ) : Prop :=
  ∀ (P : (FU.Di i).La →+ (Fin g → ℂ)) (y : Sp ℂ ⟶ Xo.XF c) (v : Vecs y D.p) (w : Vecs y D.q)
    (V : Fin D.p → Fin g → ℂ) (W : Fin D.q → Fin g → ℂ) (C : Matrix (Fin D.p) (Fin D.p ⊕ Fin D.q) ℂ)
    (Fm B : Matrix (Fin D.q) (Fin D.p ⊕ Fin D.q) ℂ),
    IsPeriod (FU.Di i) ty P → under y = FU.u i P → IsFramed U τ σ y v w →
    (∀ a, IsDerivAt0 (fun z => (FU.ex i P z).left) (V a) (v a).left) →
    (∀ j, IsDerivAt0 (fun z => (FU.ex i P z).left) (W j) (w j).left) →
    (∀ a, tyPart ty τ' (∑ m, C a m • P (e m)) = V a) →
    (∀ n, tyPart ty (ComplexEmbedding.conjugate τ') (P (e n)) = ∑ j, B j n • W j) →
    (∀ j n, ∑ m, Fm j m * τ' (sesq (FU.Di i) (e m) (e n)) = B j n) →
    Φ y v w * (Matrix.fromRows C Fm).det = ρ

structure IsUnitAn (τ : E →+* ℂ) (σ : c.F →+* ℂ) (Φ : CFn Xo c) : Prop where

  ne : ∀ y v w, IsFramed Set.univ τ σ y v w → Φ y v w ≠ 0

  chg : ∀ y v w v' w' (A : Matrix (Fin D.p) (Fin D.p) ℂ) (B : Matrix (Fin D.q) (Fin D.q) ℂ),
    IsFramed Set.univ τ σ y v w → IsFramed Set.univ τ σ y v' w' →
    (∀ i, IsComb (A i) v (v' i)) → (∀ j, IsComb (B j) w (w' j)) → Φ y v' w' * A.det = Φ y v w * B.det

  norm : ∀ y v w (Γ : Matrix (Fin D.p) (Fin D.p) ℂ) (Δ : Matrix (Fin D.q) (Fin D.q) ℂ),
    IsFramed Set.univ τ σ y v w → IsHodgeGram Xo.univ.t.G Xo.univ.t.PP.L (under y) v Γ →
    IsHodgeGram Xo.univ.t.G Xo.univ.t.PP.L (under y) w Δ → ‖Φ y v w‖ ^ 2 * ‖Γ.det‖ = ‖Δ.det‖

  hol : ∀ (R : Type) [CommRing R] (x : Sp R ⟶ Xo.XF c) (vR : Fin D.p → (epsAt (under x) ⟶ Xo.univ.t.G))
    (wR : Fin D.q → (epsAt (under x) ⟶ Xo.univ.t.G)) (m : ℕ) (B : Set (Fin m → ℂ)) (ψ : (Fin m → ℂ) → (R →+* ℂ))
    (v : ∀ b, Vecs (spMap (ψ b) ≫ x) D.p) (w : ∀ b, Vecs (spMap (ψ b) ≫ x) D.q), IsOpen B →
    (∀ r, DifferentiableOn ℂ (fun b => ψ b r) B) →
    (∀ b ∈ B, IsFramed Set.univ τ σ (spMap (ψ b) ≫ x) (v b) (w b) ∧
      (∀ a, (v b a).left = spMap (dualMap (ψ b)) ≫ (vR a).left) ∧
      ∀ j, (w b j).left = spMap (dualMap (ψ b)) ≫ (wR j).left) →
    DifferentiableOn ℂ (fun b => Φ (spMap (ψ b) ≫ x) (v b) (w b)) B

def ExtendsUnitAt {K Ω : Type} [Field K] [Field Ω] {X : Scheme.{0}} (s : X ⟶ Sp K) (σ : K →+* ℂ) (ξ : Sp Ω ⟶ X)
    (W : X.Opens) (F : (Sp ℂ ⟶ X) → ℂ) (t : Ω) (x : Sp ℂ ⟶ X) : Prop :=
  ∀ (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)), IsOpen B → IsHolTo B y →
    (∀ b ∈ B, y b ≫ s = spMap σ) → ∀ b₀ ∈ B, y b₀ = x →
    ∃ (ε : ℝ) (h : (Fin m → ℂ) → ℂ), 0 < ε ∧ DifferentiableOn ℂ h (Metric.ball b₀ ε) ∧ h b₀ ≠ 0 ∧
      ∀ b ∈ B ∩ Metric.ball b₀ ε, ⊤ ≤ y b ⁻¹ᵁ W → ∀ r : ℂ, ValAt ξ (y b) t r → F (y b) = h b * r

variable {O : Type} [CommRing O] {β : O →+* c.F}

def SameVec (Y : Model Xo c β) {F : Type} [Field F] (y : Sp F ⟶ Xo.XF c) (v : epsAt (under y) ⟶ Xo.univ.t.G)
    (v' : epsAt (y ≫ Y.j) ⟶ Y.t.G) : Prop :=
  ∃ u : Sp (DualNumber F) ⟶ Y.oF.t.G.left, u ≫ Y.oF.t.G.hom = spMap (algebraMap F (DualNumber F)) ≫ y ∧
    u ≫ Y.m0.toSABMap.φ = v.left ∧ u ≫ Y.m.φ = v'.left

theorem exists_sameVec_left (Y : Model Xo c β) {F : Type} [Field F] (y : Sp F ⟶ Xo.XF c)
    (v' : epsAt (y ≫ Y.j) ⟶ Y.t.G) : ∃ v, SameVec Y y v v' := by
  have hp : IsPullback Y.m0.toSABMap.φ Y.oF.t.G.hom Xo.univ.t.G.hom (pullback.fst _ _) := Y.m0.cart.1
  have hq : IsPullback Y.m.φ Y.oF.t.G.hom Y.t.G.hom Y.j := Y.m.cart.1
  have hv : v'.left ≫ Y.t.G.hom = (spMap (algebraMap F (DualNumber F)) ≫ y) ≫ Y.j := by
    rw [Category.assoc]; exact Over.w v'
  refine ⟨Over.homMk (hq.lift _ _ hv ≫ Y.m0.toSABMap.φ) ?_, hq.lift _ _ hv, hq.lift_snd _ _ _, rfl,
    hq.lift_fst _ _ _⟩
  have : (hq.lift _ _ hv ≫ Y.m0.toSABMap.φ) ≫ Xo.univ.t.G.hom =
      spMap (algebraMap F (DualNumber F)) ≫ y ≫ pullback.fst _ _ := by
    rw [Category.assoc, hp.w, ← Category.assoc, hq.lift_snd, Category.assoc]
  exact this

theorem SameVec.unique {Y : Model Xo c β} {F : Type} [Field F] {y : Sp F ⟶ Xo.XF c}
    {v : epsAt (under y) ⟶ Xo.univ.t.G} {v₁ v₂ : epsAt (y ≫ Y.j) ⟶ Y.t.G}
    (h₁ : SameVec Y y v v₁) (h₂ : SameVec Y y v v₂) : v₁ = v₂ := by
  have hp : IsPullback Y.m0.toSABMap.φ Y.oF.t.G.hom Xo.univ.t.G.hom (pullback.fst _ _) := Y.m0.cart.1
  obtain ⟨u₁, a₁, b₁, c₁⟩ := h₁
  obtain ⟨u₂, a₂, b₂, c₂⟩ := h₂
  have : u₁ = u₂ := hp.hom_ext (b₁.trans b₂.symm) (a₁.trans a₂.symm)
  ext1
  rw [← c₁, ← c₂, this]

theorem SameVec.unique_left {Y : Model Xo c β} {F : Type} [Field F] {y : Sp F ⟶ Xo.XF c}
    {v₁ v₂ : epsAt (under y) ⟶ Xo.univ.t.G} {v' : epsAt (y ≫ Y.j) ⟶ Y.t.G}
    (h₁ : SameVec Y y v₁ v') (h₂ : SameVec Y y v₂ v') : v₁ = v₂ := by
  have hq : IsPullback Y.m.φ Y.oF.t.G.hom Y.t.G.hom Y.j := Y.m.cart.1
  obtain ⟨u₁, a₁, b₁, c₁⟩ := h₁
  obtain ⟨u₂, a₂, b₂, c₂⟩ := h₂
  have : u₁ = u₂ := hq.hom_ext (c₁.trans c₂.symm) (a₁.trans a₂.symm)
  ext1
  rw [← b₁, ← b₂, this]

def Represents (Y : Model Xo c β) (U : Set (Xo.XF c)) (τ : E →+* ℂ) {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ Y.X}
    {V : Type} [AddCommGroup V] [Module Ω V] (M : LieModel Y.t.G ξ V) (a : ⋀[Ω]^D.p V) (b : ⋀[Ω]^D.q V)
    (φ : FrameFn Xo c) : Prop :=
  ∀ (F : Type) [Field F] (βF : c.F →+* F) (y : Sp F ⟶ Xo.XF c) (v : Vecs y D.p) (w : Vecs y D.q)
    (b₁ : Fin D.p → V) (b₂ : Fin D.q → V) (α κ : Ω), IsFramed U τ βF y v w →
    a = α • exteriorPower.ιMulti Ω D.p b₁ → b = κ • exteriorPower.ιMulti Ω D.q b₂ →
    (∀ i, ∃ v', M.ValAt (y ≫ Y.j) (b₁ i) v' ∧ SameVec Y y (v i) v') →
    (∀ j, ∃ w', M.ValAt (y ≫ Y.j) (b₂ j) w' ∧ SameVec Y y (w j) w') →
    ValAt ξ (y ≫ Y.j) (α / κ) (φ F y v w)

structure CptOver (Y : Model Xo c β) (U : Set (Xo.XF c)) where

  Ω : Type
  [field : Field Ω]

  ξ₀ : Sp Ω ⟶ Xo.XF c

  inc : c.F →+* Ω

  over_inc : ξ₀ ≫ pullback.snd _ _ = spMap inc

  gen : IsCptGen (ξ₀ ≫ Y.j)

  closure : ∀ u : Xo.XF c, u ∈ U ↔ genPt ξ₀ ⤳ u

  V : Type
  [acg : AddCommGroup V]
  [mod : Module Ω V]

  M : LieModel Y.t.G (ξ₀ ≫ Y.j) V

  ρ : 𝓞 E →+* Module.End Ω V

  act : M.IsActOf Y.t.act.act ρ

attribute [instance] CptOver.field CptOver.acg CptOver.mod

def CptOver.eig {Y : Model Xo c β} {U : Set (Xo.XF c)} (Z : CptOver Y U) (τ : E →+* ℂ) : Lat (Z.ξ₀ ≫ Y.j) Z.V :=
  Z.M.eigLat Z.ρ (Z.inc.comp (tauIn c τ))

def CptOver.genFib {Y : Model Xo c β} {U : Set (Xo.XF c)} (Z : CptOver Y U) : Set (Cpt (Z.ξ₀ ≫ Y.j)) :=
  {x | x.1 ∈ Set.range (pullback.fst Y.s (spMap β))}

def FlatOnModel {Y : Model Xo c β} {U : Set (Xo.XF c)} (Z : CptOver Y U) (τ : E →+* ℂ) (φ : FrameFn Xo c) : Prop :=
  IsLineFn U τ φ ∧ ∃ (a : ⋀[Z.Ω]^D.p Z.V) (b : ⋀[Z.Ω]^D.q Z.V),
    IsLineGenOn (Z.eig τ) (Z.eig (ComplexEmbedding.conjugate τ)) D.p D.q a b Z.genFib ∧ Represents Y U τ Z.M a b φ

theorem FlatOnModel.isLineFn {Y : Model Xo c β} {U : Set (Xo.XF c)} {Z : CptOver Y U} {τ : E →+* ℂ}
    {φ : FrameFn Xo c} (h : FlatOnModel Z τ φ) : IsLineFn U τ φ := h.1

theorem FlatOnModel.exists_gen {Y : Model Xo c β} {U : Set (Xo.XF c)} {Z : CptOver Y U} {τ : E →+* ℂ}
    {φ : FrameFn Xo c} (h : FlatOnModel Z τ φ) : ∃ (a : ⋀[Z.Ω]^D.p Z.V) (b : ⋀[Z.Ω]^D.q Z.V),
    IsLineGenOn (Z.eig τ) (Z.eig (ComplexEmbedding.conjugate τ)) D.p D.q a b Z.genFib ∧
      Represents Y U τ Z.M a b φ := h.2

theorem FlatOnModel.of_gen {Y : Model Xo c β} {U : Set (Xo.XF c)} {Z : CptOver Y U} {τ : E →+* ℂ}
    {φ : FrameFn Xo c} {a : ⋀[Z.Ω]^D.p Z.V} {b : ⋀[Z.Ω]^D.q Z.V} (hφ : IsLineFn U τ φ)
    (hg : IsLineGenOn (Z.eig τ) (Z.eig (ComplexEmbedding.conjugate τ)) D.p D.q a b Z.genFib)
    (hr : Represents Y U τ Z.M a b φ) : FlatOnModel Z τ φ := ⟨hφ, a, b, hg, hr⟩

theorem CptOver.genPt_mem {Y : Model Xo c β} {U : Set (Xo.XF c)} (Z : CptOver Y U) : genPt Z.ξ₀ ∈ U :=
  (Z.closure _).2 specializes_rfl

def CptOver.IsGeom {Y : Model Xo c β} {U : Set (Xo.XF c)} (Z : CptOver Y U) : Prop :=
  ∀ x : Z.Ω, (∃ f : Polynomial c.F, f ≠ 0 ∧ f.eval₂ Z.inc x = 0) → x ∈ Set.range Z.inc

end GlobalTheory.CompanionTheory.Ar.Flat
end
end
