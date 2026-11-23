module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Formalism.LocalToGlobal.PlaceMapInjectivity.MapPlInjective

@[expose] public section

section

noncomputable section

open scoped Formalism.Per

namespace GlobalTheory.PMon.Gauss

variable (l : ℕ) [Fact l.Prime]

def gA (ρ : ℝ) (a : Formalism.Per.Ainf l) : ℝ :=
  ⨆ n : ℕ, ‖(((a.coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) * ρ ^ n

def IsGauss (ρ : ℝ) (N : Formalism.Per.Acris l → ℝ) : Prop :=
  (∀ x, 0 ≤ N x ∧ N x ≤ 1) ∧ (∀ x y, N (x + y) ≤ max (N x) (N y)) ∧ (∀ x, N (-x) = N x) ∧
    (∀ x y, N (x * y) = N x * N y) ∧
    ∀ a : Formalism.Per.Ainf l, N (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) a) = gA l ρ a


open Classical in
def gC (ρ : ℝ) (x : Formalism.Per.Acris l) : ℝ :=
  if h : ∃ N, IsGauss l ρ N then Classical.choose h x else 0

def vr (r : ℝ) (x : Formalism.Per.Acris l) : ℝ := -Real.logb l (gC l ((l : ℝ) ^ (-r)) x)

def zc : ℤ_[l] →+* Formalism.Per.Acris l := (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l)).comp (Formalism.Per.zA l)

def tc (y : Formalism.Per.Fl l) : Formalism.Per.Acris l := algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) (Formalism.Per.tm y)

abbrev φc : Formalism.Per.Acris l →+* Formalism.Per.Acris l := GlobalTheory.MemLoc.phiA l

end GlobalTheory.PMon.Gauss

end
end

section

noncomputable section
namespace GlobalTheory.WachUse
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions GlobalTheory.AdmLoc

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

def InvBasis : Prop := ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ →
  ∃ b : Fin (Module.finrank O ↥T.L.T) → W.DD T, (∀ j, b j ∈ W.NΔ T) ∧ LinearIndependent (LetA O n) b ∧
    W.N T = Submodule.span (LetA O n) (Set.range b)

def Heights : Prop := ∀ (T : LocLat G Qp LL O) (U : ZMod n → Multiset ℤ) (M h : ZMod n → ℕ),
  CrysWith PD W.emb T.ρ U → (∀ i, ∀ u ∈ U i, -(M i : ℤ) ≤ u ∧ u ≤ h i) →
  ∀ i, (∀ x ∈ W.N T, W.Q ^ M i • (letE i : LetA O n) • W.φD T x ∈ W.N T) ∧
    ∀ y ∈ W.N T, W.Q ^ h i • (letE i : LetA O n) • y ∈ W.φpull T

def RankOne : Prop := ∀ (T : LocLat G Qp LL O) (a : ZMod n → ℤ), CrysWith PD W.emb T.ρ (fun i => {a i}) →
  Module.finrank LL T.V = 1 → ∀ i : ZMod n,
    (∀ x ∈ W.φpull T, ∃ y ∈ W.N T,
      W.Q ^ (-a i).toNat • (letE i : LetA O n) • x = W.Q ^ (a i).toNat • (letE i : LetA O n) • y) ∧
    ∀ y ∈ W.N T, ∃ x ∈ W.φpull T,
      W.Q ^ (-a i).toNat • (letE i : LetA O n) • x = W.Q ^ (a i).toNat • (letE i : LetA O n) • y

def Saturated : Prop := ∀ (T' T : LocLat G Qp LL O) (f : LatHom T'.L T.L), IsCrys PD T.ρ → Function.Bijective f.f →
  ∀ x, W.map f x ∈ W.N T → x ∈ W.N T'

def Additive : Prop := ∀ (T T' S : LocLat G Qp LL O) (f : LatHom T.L S.L) (g : LatHom T'.L S.L),
  IsCrys PD T.ρ → IsCrys PD T'.ρ → Function.Bijective (f.f.coprod g.f) →
  (∀ z ∈ S.L.T, ∃ x ∈ T.L.T, ∃ y ∈ T'.L.T, z = f.f x + g.f y) →
  ∀ z ∈ W.N S, ∃ x ∈ W.N T, ∃ y ∈ W.N T', z = W.map f x + W.map g y

def IsC (PD : PeriodData G Qp K₀ K B BdR) (LL : Type) [Field LL] [Algebra O LL] (c : ℤ → O) : Prop :=
  ∀ a : ℤ, (PD.p : LL) * algebraMap O LL (c a) = 1 - (1 + (PD.p : LL)) ^ a

def SenOp : Prop := ∀ (T : LocLat G Qp LL O) (U : ZMod n → Multiset ℤ), CrysWith PD W.emb T.ρ U →
  ∀ (γ : W.Gam), (W.χΓ γ : O) = 1 + (PD.p : O) → ∀ c : ℤ → O, IsC PD LL c →
  ∃ ν : Module.End O ↥(W.NΔ T), (∀ y : ↥(W.NΔ T), W.γD T γ y - y = W.π₀ • ((ν y : ↥(W.NΔ T)) : W.DD T)) ∧
    (∀ (i : ZMod n) (s : ℕ) (y : ↥(W.NΔ T)), ∃ z ∈ W.N T, (letE i : LetA O n) •
      ((Polynomial.aeval ν (∏ m ∈ ((Finset.range s) ×ˢ (U i).toFinset).image (fun p => (p.1 : ℤ) - p.2),
        (Polynomial.X - Polynomial.C (c m))) y : ↥(W.NΔ T)) : W.DD T) = (W.π₀ + (PD.p : LetA O n)) ^ s • z) ∧
    ∀ (m : ℕ) (b : Fin m → ↥(W.NΔ T)), LinearIndependent (LetA O n) (fun j => (b j : W.DD T)) →
      W.N T = Submodule.span (LetA O n) (Set.range fun j => (b j : W.DD T)) →
      ∀ i : ZMod n, ∃ A : Matrix (Fin m) (Fin m) O,
        A.charpoly = ((U i).map fun u => Polynomial.X - Polynomial.C (c (-u))).prod ∧
        ∀ j, ∃ z ∈ W.N T, (letE i : LetA O n) • (((ν (b j) - ∑ j', A j' j • b j' : ↥(W.NΔ T))) : W.DD T) =
          (W.π₀ + (PD.p : LetA O n)) • z

def QN : Prop := InvBasis W ∧ Heights W ∧ RankOne W ∧ Saturated W ∧ Additive W ∧ SenOp W

end GlobalTheory.WachUse
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.L2

namespace GlobalTheory.HeightCounting

structure NTiedGPlaceholder (D : D7) : Type

end GlobalTheory.HeightCounting

end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GoodPts

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

def Good {T : CDVR} {io : c.F →+* T.Fr} (y : IntFr Xo c T io) : Prop :=
  letI := io.toAlgebra
  ∃ (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (_ : SABMap t' Xo.univ.t y.1.x)
    (_ : SABMap t' G (spMap (algebraMap T.V T.Fr))), IsProper G.G.hom

def InV (T : CDVR) (x : T.Fr) : Prop := x ∈ (algebraMap T.V T.Fr).range

variable (Xo c)

def BddGood (la : HeightOneSpectrum (𝓞 c.F)) (κ : c.F) (f : Rul Xo c) : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e →
    ∀ y : IntFr Xo c T io, y.IsAlg → Good y → InV T (io κ * evI y f)

def BddAll (la : HeightOneSpectrum (𝓞 c.F)) (κ : c.F) (f : Rul Xo c) : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e →
    ∀ y : IntFr Xo c T io, y.IsAlg → InV T (io κ * evI y f)

def supSet (la : HeightOneSpectrum (𝓞 c.F)) (W : Submodule c.F (Rul Xo c)) : Set (Rul Xo c) :=
  {f | f ∈ W ∧ BddAll Xo c la 1 f}

end GlobalTheory.GoodPts
end
end

section

noncomputable section

namespace GlobalTheory.Pass

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open Polynomial Module TensorProduct

def lenModN {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] (A H : Submodule O M) : ℕ∞ :=
  Module.length O (↥A ⧸ H.comap A.subtype)

section OnePD

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    (LL O : Type) [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]

def DualJumpAt : Prop :=
  ∀ (A A' : GRep G Qp LL O) (P : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDual1 PD A.ρ A'.ρ P → IsDR PD A.ρ →
    ∀ (τ : K →ₐ[Qp] LL) (a : ℤ), IsJumpV PD A'.ρ τ a ↔ IsJumpV PD A.ρ τ (-a - 1)

variable {LL O}

def IsSubFam {ι : Type} {k : ℕ} (Ms : ι → (G →* Matrix (Fin k) (Fin k) LL)) (W : GRep G Qp LL O) : Prop :=
  ∃ (a : ℕ) (x : Fin a → ι) (p : Fin a → W.V →ₗ[LL] (Fin k → LL)),
    (∀ j g v, p j (W.ρ g v) = (Ms (x j) g).mulVec (p j v)) ∧ ∀ v, (∀ j, p j v = 0) → v = 0

def LiftFam {ι : Type} {k : ℕ} (Ms : ι → (G →* Matrix (Fin k) (Fin k) LL)) (e : ℕ) : Prop :=
  ∀ W₁ W₂ : GRep G Qp LL O, IsSubFam Ms W₁ → IsSubFam Ms W₂ →
    ∀ (L₁ : Lattice (O := O) W₁.ρ) (L₂ : Lattice (O := O) W₂.ρ) (F : LatHom L₁ L₂), F.Onto → F.LiftF PD e

end OnePD

def DualJumpL (LT : LocTheory) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l), DualJumpAt ((LT l).PD K) ↥LL.1 ↥(OL LL)

def PotDRL (LT : LocTheory) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K K' LL : FinExt l) (h : K.1 ≤ K'.1) (A : GRep ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)),
    IsCrys ((LT l).PD K') (A.ρ.comp (Subgroup.inclusion (GK_le h))) → IsDR ((LT l).PD K) A.ρ

def PcrisTensorL (LT : LocTheory) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K K' LL : FinExt l) (h : K.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex)
    (hS : ∀ (g : ↥(GK K)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'),
      ((LT l).PD K).actB g (algebraMap ↥(K0 K') (LT l).R.B c) = algebraMap ↥(K0 K') (LT l).R.B c')
    (A A' : GRep ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (Sig Sig' : Finset ((pc (LT l) h hN hF hS).Iner →* (↥LL.1)ˣ)),
    (pc (LT l) h hN hF hS).IsPotCrys A.ρ → (pc (LT l) h hN hF hS).InertiaThrough A.ρ Sig →
    (∀ (χ : ↥(GK K) →* (↥LL.1)ˣ) (c : (pc (LT l) h hN hF hS).Iner →* (↥LL.1)ˣ),
      IsTwistRep χ⁻¹ A.ρ A'.ρ → (pc (LT l) h hN hF hS).IsPotCrys (WeaklyAdmissibleFiltrations.charRep χ) →
      (pc (LT l) h hN hF hS).InertiaThrough (WeaklyAdmissibleFiltrations.charRep χ) {c} →
      (∀ b, b ∈ Sig' ↔ ∃ a ∈ Sig, b = a * c⁻¹) →
      (pc (LT l) h hN hF hS).IsPotCrys A'.ρ ∧ (pc (LT l) h hN hF hS).InertiaThrough A'.ρ Sig') ∧
    (∀ P : A.V →ₗ[↥LL.1] A'.V →ₗ[↥LL.1] ↥LL.1, IsDual1 ((LT l).PD K) A.ρ A'.ρ P →
      (∀ b, b ∈ Sig' ↔ ∃ a ∈ Sig, b = a⁻¹) →
      (pc (LT l) h hN hF hS).IsPotCrys A'.ρ ∧ (pc (LT l) h hN hF hS).InertiaThrough A'.ρ Sig')

variable {D : D7}

set_option synthInstance.maxHeartbeats 400000 in
def TieInePoly (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (K' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).Kw.1 ≤ K'.1) (hN : (GKin h).Normal)
    (hF : (GKin h).FiniteIndex)
    (hS : ∀ (g : ↥(GK (D.nbr i w hw).Kw)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'),
      ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).actB g (algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c) =
        algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c')
    (m : ℕ) (r : GE D.nd →* GL (Fin m) (D.nd.O i)),
    Continuous (fun g => ((r g : GL _ _) : Matrix (Fin m) (Fin m) (D.nd.O i))) →
    (pc (D.loc (D.nd.l i)) h hN hF hS).IsPotCrys ((D.nbr i w hw).rep (r.comp (decS D.nd w))) →
    ∀ σ : Gw D.nd w, (σ : GE D.nd) ∈ Ine (F := D.host.E) (D.nd.plOm.1 w) →
      ∀ p : (D.nd.O i)[X],
        p.map (iotaO D.nd D.naut i) =
          D.naut.inePol (D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) r) w) (σ : GE D.nd) →
        ∀ d ∈ (pc (D.loc (D.nd.l i)) h hN hF hS).Dpcris ((D.nbr i w hw).rep (r.comp (decS D.nd w))),
          ∑ n ∈ Finset.range (p.natDegree + 1), (D.nbr i w hw).toLL (p.coeff n) •
            actVB ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw) ((D.nbr i w hw).rep (r.comp (decS D.nd w)))
              ((D.nbr i w hw).e (σ ^ n)) d = 0

def InertEq (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
    Br.inert D.nbr i w hw = IK (D.nbr i w hw).Kw

section AtW

variable (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

def PotFam {ι : Type} {k : ℕ} (Ms : ι → (GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))) (n : ℕ) : Prop :=
  ∃ (K' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).Kw.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex)
    (hS : ∀ (g : ↥(GK (D.nbr i w hw).Kw)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'),
      ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).actB g (algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c) =
        algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c')
    (Sig : Finset ((pc (D.loc (D.nd.l i)) h hN hF hS).Iner →* (Br.LL D.nbr i w hw)ˣ)) (Fr : Br.G D.nbr i w hw),
    (pc (D.loc (D.nd.l i)) h hN hF hS).IsFrob Fr ∧
    FrobStable (pc (D.loc (D.nd.l i)) h hN hF hS).Iner Fr Sig ∧ 1 ∈ Sig ∧ Sig.card ≤ n ∧
    ∀ x, (pc (D.loc (D.nd.l i)) h hN hF hS).IsPotCrys (matRep (Br.loc D.nbr i w hw (Ms x))) ∧
      (pc (D.loc (D.nd.l i)) h hN hF hS).InertiaThrough (matRep (Br.loc D.nbr i w hw (Ms x))) Sig

def JumpFam {ι : Type} {k : ℕ} (Ms : ι → (GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))) (n a b : ℕ) : Prop :=
  ∃ U : Finset ℤ, (∀ u ∈ U, -(a : ℤ) ≤ u ∧ u ≤ b) ∧ (0 : ℤ) ∈ U ∧ U.card ≤ n + 1 ∧
    ∀ x τ, JumpsInV (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw (Ms x))) τ (U : Set ℤ)

def LiftFamW {ι : Type} {k : ℕ} (Ms : ι → (GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))) (e : ℕ) : Prop :=
  LiftFam (O := Br.OLL D.nbr i w hw) (Br.PD D.loc D.nbr i w hw) (fun x => Br.loc D.nbr i w hw (Ms x)) e

variable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (Xs : Set (D.nd.X i))

def cutCoc {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) :
    Set (Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T) :=
  {c | ∃ (a : ℕ) (x : Fin a → D.nd.X i) (_ : ∀ j, x j ∈ Xs) (E : Fin a → Fin D.R.nV → KK D.nd i)
      (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i)) (_ : Y.FG)
      (hst : ∀ γ : GE D.nd, ∀ y ∈ Y,
        (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (y j)) ∈ Y)
      (hE : ∀ γ : GE D.nd,
        (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (E j) - E j) ∈ Y)
      (φ : ↥Y →ₗ[D.nd.O i] KOG (D.nd.O i) k),
      (∀ (γ : GE D.nd) (y : ↥Y), φ ⟨_, hst γ y.1 y.2⟩ = WKG M γ (φ y)) ∧
      c = fun g => Br.phi (D.nbr i w hw) k
        (φ ⟨_, hE ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd)⟩)}


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
def LocBound {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (e : ℕ) : Prop :=
  lenModN (Submodule.span (Br.OLL D.nbr i w hw) (cutCoc i w hw r Xs M))
      (HfD (Br.PD D.loc D.nbr i w hw) (Br.locLat D.nbr i w hw M)) ≤
    (e : ℕ∞) * lenOl (Br.PD D.loc D.nbr i w hw) (O := Br.OLL D.nbr i w hw)




def HfChar : Prop :=
  (∀ c ∈ Finset.Icc 2 D.R.t,
    HfD (Br.PD D.loc D.nbr i w hw) (Br.locLat D.nbr i w hw (chiRatO D.nd i c)) ≤
      BD (Br.locLat D.nbr i w hw (chiRatO D.nd i c))) ∧
  HfD (Br.PD D.loc D.nbr i w hw) (Br.locLat D.nbr i w hw (chiRatO D.nd i 1)) ≤
    Z1urD (Br.locLat D.nbr i w hw (chiRatO D.nd i 1)) (Br.inert D.nbr i w hw)

end AtW

def eMax (D : D7) (CT eta : ℕ) : ℕ :=
  CT * ((D.R.nV + 1) * ((D.R.nV + 1) ^ 2 / 4) + (eta + D.R.t + 1) * ((D.R.nV + 1) + (D.R.nV + 1) ^ 2 / 4))

def CentralIdemCoeff : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (e : MonoidAlgebra ℂ Γ), e * e = e → (∀ z, e * z = z * e) →
    ∀ ζ : ℂ, IsPrimitiveRoot ζ (Nat.card Γ) → ∀ h : Γ,
      (Nat.card Γ : ℂ) * e.coeff h ∈ Algebra.adjoin ℤ ({ζ} : Set ℂ)

def StepPotDual : Prop :=
  ∀ D : D7, PcrisTensorL D.loc → ∀ (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r →
    ∀ (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (n : ℕ),
      PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) n → PotFam i w hw (fun x : ↥Xs => rDuO D.nd i r x) n

def SubTw {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (Xs : Set (D.nd.X i))
    {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) : Prop :=
  (Continuous fun g => M g) ∧ ∃ x ∈ Xs, ∃ j : (Fin k → KK D.nd i) →ₗ[KK D.nd i] (Fin D.R.nV → KK D.nd i),
    Function.Injective j ∧ ∀ g v, j ((mapM (toK D.nd i) M g).mulVec v) =
      (mapM (toK D.nd i) (rTwO D.nd i r x) g).mulVec (j v)

def StepCont : Prop :=
  ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r →
    ∀ x, (Continuous fun g => rTwO D.nd i r x g) ∧ Continuous fun g => rDuO D.nd i r x g

def ResSpan {D : D7} (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) : Prop :=
  Submodule.span (kk D.nd i) (Set.range (mapM (IsLocalRing.residue (D.nd.O i)) (rhoO D.nd i ρ π))) = ⊤

end GlobalTheory.Pass

end
end
