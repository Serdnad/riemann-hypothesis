module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle009
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle001
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MarkWeightedFixedPointEqDefinitePairOdd
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PerCApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle267
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle060
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle853
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle885
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle007

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical

namespace UpperTheory.Gal.W2

def TateWit : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (gb : GBase D.toG ℂ) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp ℂ) (o : GObj gb N s)
    (hX : SmoothOfRelativeDimension D.g o.A.hom) (hL) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (D' : PLat D.O D.inv) (t : D.La → D'.La) P (x : Sp ℂ ⟶ S) e, 0 < N → N.Coprime p →
    UnifAt (gfam o hX hL) (RingHom.id ℂ) ρ N D' t P x e → ∀ I : TIs o x, (∀ y, toUnit _ ≫ o.eta y = I.ev N y) →
    ∃ (f : ℕ → D.La →+ D'.La) (nu : ℕ → ℤ), IsWit D' f nu ∧ (∀ a, ∃ u, f N a = t a + N • u) ∧
      ∀ n : ℕ, 0 < n → n.Coprime p → ∀ a, I.ev n a = e ((n : ℂ)⁻¹ • P (f n a))

def IsogAt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (gb : GBase D.toG ℂ) (N N' : ℕ) (h : G.GAf), LevOk L N N' h → ∀ (X : GenModel gb N) (X' : GenModel gb N') (c : Leg L h X' X) (hX : SmoothOfRelativeDimension D.g X.univ.A.hom) (hL) (hX' : SmoothOfRelativeDimension D.g X'.univ.A.hom) (hL') (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ),
    FineAt (gfam X.univ hX hL) (RingHom.id ℂ) ρ N (D.Cls N) →
    ∀ (D' : PLat D.O D.inv) (t : D.La → D'.La) P (x : Sp ℂ ⟶ X'.X) e, UnifAt (gfam X'.univ hX' hL') (RingHom.id ℂ) ρ N' D' t P x e →
    ∃ (D'' : PLat D.O D.inv) (t'' : D.La → D''.La) (P'' : D''.La →+ (Fin D.g → ℂ)) (e'' : _) (inc : D'.La →ₗ[D.O] D''.La) (d : ℕ),
      D.Cls N D'' t'' ∧ UnifAt (gfam X.univ hX hL) (RingHom.id ℂ) ρ N D'' t'' P'' (x ≫ c.q) e'' ∧ (∀ u, P'' (inc u) = P u) ∧
      (∀ z, (e'' z).left = (e z).left ≫ c.tot) ∧ d.Coprime p ∧ (∀ u'', ∃ u, inc u = d • u'') ∧
      ∃ (f : ℕ → D.La →+ D'.La) (nu : ℕ → ℤ) (f'' : ℕ → D.La →+ D''.La) (nu'' : ℕ → ℤ), IsWit D' f nu ∧ IsWit D'' f'' nu'' ∧ (∀ a, ∃ u, f N' a = t a + N' • u) ∧
        (∀ a, ∃ u, f'' N a = t'' a + N • u) ∧ ∀ n : ℕ, 0 < n → n.Coprime p → ∀ a b : D.La,
          (∃ u, inc (f n a) = f'' n b + n • u) ↔ ∃ w ∈ LaHat D, L.actG h (inAf D a) = inAf D b + n • w

def HeckeCoord : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (gb : GBase D.toG ℂ) (N N' : ℕ) (h : G.GAf), LevOk L N N' h → ∀ (X : GenModel gb N) (X' : GenModel gb N') (c : Leg L h X' X) (hX : SmoothOfRelativeDimension D.g X.univ.A.hom) (hL) (hX' : SmoothOfRelativeDimension D.g X'.univ.A.hom) (hL') (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ),
    FineAt (gfam X.univ hX hL) (RingHom.id ℂ) ρ N (D.Cls N) →
    ∀ (D' : PLat D.O D.inv) (t : D.La → D'.La) P (x : Sp ℂ ⟶ X'.X) e, UnifAt (gfam X'.univ hX' hL') (RingHom.id ℂ) ρ N' D' t P x e →
    ∀ (B : GlobalTheory.LKCx.Form G) (j : D'.La →+ VQ D) (h₁ : G.GAf) (M : AddSubgroup (VQ D)), IsPlace L B.β D' j → IsCoordA L (trivX B) N' D' t j h₁ →
    IsLocP D' j M → ∃ (D'' : PLat D.O D.inv) (t'' : D.La → D''.La) (P'' : D''.La →+ (Fin D.g → ℂ)) (e'' : _) (inc : D'.La →ₗ[D.O] D''.La)
      (j'' : D''.La →+ VQ D), D.Cls N D'' t'' ∧ UnifAt (gfam X.univ hX hL) (RingHom.id ℂ) ρ N D'' t'' P'' (x ≫ c.q) e'' ∧ (∀ u, P'' (inc u) = P u) ∧
      (∀ z, (e'' z).left = (e z).left ≫ c.tot) ∧ (∀ u'', ∃ (d : ℕ) (u : D'.La), d ≠ 0 ∧ inc u = d • u'') ∧ (∀ u, j'' (inc u) = j u) ∧
      IsPlace L B.β D'' j'' ∧ IsCoordA L (trivX B) N D'' t'' j'' (h₁ * h⁻¹) ∧ IsLocP D'' j'' M

def OneAt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (gb : GBase D.toG ℂ) (N N' : ℕ) (h : G.GAf), LevOk L N N' h → ∀ (X : GenModel gb N) (X' : GenModel gb N') (c₁ : Leg L 1 X' X) (hX : SmoothOfRelativeDimension D.g X.univ.A.hom) (hL) (hX' : SmoothOfRelativeDimension D.g X'.univ.A.hom) (hL') (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ),
    FineAt (gfam X.univ hX hL) (RingHom.id ℂ) ρ N (D.Cls N) →
    ∀ (B : GlobalTheory.LKCx.Form G) (PD : PDic L B.β) (D' : PLat D.O D.inv) (t : D.La → D'.La), D.Cls N' D' t → ∀ (j : D'.La →+ VQ D) (a : G.GAf × Gr G 1), IsPlace L B.β D' j →
    IsCoordA L (trivX B) N' D' t j a.1 → IsLocP D' j (PD.lat a.2) → ∀ P (x : Sp ℂ ⟶ X'.X) e, UnifAt (gfam X'.univ hX' hL') (RingHom.id ℂ) ρ N' D' t P x e →
    ∃ e₁, UnifAt (gfam X.univ hX hL) (RingHom.id ℂ) ρ N D' t P (x ≫ c₁.q) e₁ ∧ ∀ z, (e₁ z).left = (e z).left ≫ c₁.tot

def FixFwd : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (gb : GBase D.toG ℂ) (N N' : ℕ) (h : G.GAf), LevOk L N N' h → ∀ (X : GenModel gb N) (X' : GenModel gb N') (c₁ : Leg L 1 X' X) (c₂ : Leg L h X' X) (hX : SmoothOfRelativeDimension D.g X.univ.A.hom) (hL) (hX' : SmoothOfRelativeDimension D.g X'.univ.A.hom) (hL') (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ),
    FineAt (gfam X.univ hX hL) (RingHom.id ℂ) ρ N (D.Cls N) →
    ∀ (v : InfinitePlace G.F) (t₀ : D.F →+* ℂ) (B : GlobalTheory.LKCx.Form G) (PD : PDic L B.β) (RD : RDic L v B.β ρ t₀) (D' : PLat D.O D.inv) (t : D.La → D'.La), D.Cls N' D' t →
    ∀ (P : D'.La →+ (Fin D.g → ℂ)) (j : D'.La →+ VQ D) (a : GlobalTheory.LKCx.Dat G v B.β), IsCoord L B PD RD N' D' t P j a → ∀ (x : Sp ℂ ⟶ X'.X) e, UnifAt (gfam X'.univ hX' hL') (RingHom.id ℂ) ρ N' D' t P x e → x ≫ c₁.q = x ≫ c₂.q → ∃ y, Sees B {g | h * g ∈ L.KN N} a y

def FixGa : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (gb : GBase D.toG ℂ) (N N' : ℕ) (h : G.GAf), LevOk L N N' h → ∀ (X : GenModel gb N) (X' : GenModel gb N') (c₁ : Leg L 1 X' X) (c₂ : Leg L h X' X) (hX : SmoothOfRelativeDimension D.g X.univ.A.hom) (hL) (hX' : SmoothOfRelativeDimension D.g X'.univ.A.hom) (hL') (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ),
    FineAt (gfam X.univ hX hL) (RingHom.id ℂ) ρ N (D.Cls N) →
    ∀ (v : InfinitePlace G.F) (t₀ : D.F →+* ℂ) (B : GlobalTheory.LKCx.Form G) (PD : PDic L B.β) (RD : RDic L v B.β ρ t₀) (D' : PLat D.O D.inv) (t : D.La → D'.La), D.Cls N' D' t →
    ∀ (P : D'.La →+ (Fin D.g → ℂ)) (j : D'.La →+ VQ D) (a : GlobalTheory.LKCx.Dat G v B.β), IsCoord L B PD RD N' D' t P j a → ∀ (x : Sp ℂ ⟶ X'.X) e, UnifAt (gfam X'.univ hX' hL') (RingHom.id ℂ) ρ N' D' t P x e →
    ∀ y, Sees B {g | h * g ∈ L.KN N} a y → ∃ (ga : D'.La →ₗ[D.O] D'.La) (H : Matrix (Fin D.g) (Fin D.g) ℂ), (∀ u, j (ga u) = actY L y⁻¹ (j u)) ∧ FixesPer D' P ga H ∧
      ∀ w, ∀ Q : VQ D →+ (Fin D.g → ℂ), (∀ u, Q (j u) = P u) → ∀ hQ : IsPerQ L B.β ρ Q, Q (actY L y⁻¹ w) = H *ᵥ Q w

def FixEq : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (gb : GBase D.toG ℂ) (N N' : ℕ) (h : G.GAf), LevOk L N N' h → ∀ (X : GenModel gb N) (X' : GenModel gb N') (c₁ : Leg L 1 X' X) (c₂ : Leg L h X' X) (hX : SmoothOfRelativeDimension D.g X.univ.A.hom) (hL) (hX' : SmoothOfRelativeDimension D.g X'.univ.A.hom) (hL') (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ),
    FineAt (gfam X.univ hX hL) (RingHom.id ℂ) ρ N (D.Cls N) →
    ∀ (v : InfinitePlace G.F) (t₀ : D.F →+* ℂ) (B : GlobalTheory.LKCx.Form G) (PD : PDic L B.β) (RD : RDic L v B.β ρ t₀) (D' : PLat D.O D.inv) (t : D.La → D'.La), D.Cls N' D' t →
    ∀ (P : D'.La →+ (Fin D.g → ℂ)) (j : D'.La →+ VQ D) (a : GlobalTheory.LKCx.Dat G v B.β), IsCoord L B PD RD N' D' t P j a → ∀ y, Sees B {g | h * g ∈ L.KN N} a y → ∀ ga : D'.La →ₗ[D.O] D'.La, (∀ u, j (ga u) = actY L y⁻¹ (j u)) →
    ∀ P₁ P₂ (x₁ x₂ : Sp ℂ ⟶ X'.X) e₁ e₂, UnifAt (gfam X'.univ hX' hL') (RingHom.id ℂ) ρ N' D' t P₁ x₁ e₁ → UnifAt (gfam X'.univ hX' hL') (RingHom.id ℂ) ρ N' D' t P₂ x₂ e₂ → (∀ u, P₂ (ga u) = P₁ u) →
      x₁ ≫ c₂.q = x₂ ≫ c₁.q ∧ ∀ z, (e₁ z).left ≫ c₂.tot = (e₂ z).left ≫ c₁.tot

def PwOver : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (gb : GBase D.toG ℂ) (N N' : ℕ) (h : G.GAf) (X : GenModel gb N) (X' : GenModel gb N') (c : Leg L h X' X) (k : ℕ),
    c.pw k ≫ (GlobalTheory.KS.pow X.univ.A k).hom = (GlobalTheory.KS.pow X'.univ.A k).hom ≫ c.q ∧
    (∀ i, c.pw k ≫ (GlobalTheory.KS.pr X.univ.A i).left = (GlobalTheory.KS.pr X'.univ.A i).left ≫ c.tot) ∧
    (∀ b : D.O, (X'.univ.act.act b).left ≫ c.tot = c.tot ≫ (X.univ.act.act b).left) ∧
    ∀ α : Fin k → 𝓞 D.F, c.tw α ≫ (GlobalTheory.KS.pow X.univ.A k).hom = (GlobalTheory.KS.pow X'.univ.A k).hom ≫ c.q ∧ ∀ i, c.tw α ≫ (GlobalTheory.KS.pr X.univ.A i).left =
      (GlobalTheory.KS.pr X'.univ.A i).left ≫ c.tot ≫ (X.univ.act.act (algebraMap (𝓞 D.F) D.O (α i))).left

def PowCorr : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (gb : GBase D.toG ℂ) (N N' : ℕ) (h : G.GAf) (X : GenModel gb N) (X' : GenModel gb N') (c₁ : Leg L 1 X' X) (c₂ : Leg L h X' X)
    (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (D' : PLat D.O D.inv) (S : Sheet X'.s X'.univ.A D' ρ),
    (∀ P, IsPeriod D' ρ P → ∀ (b : D.O) z, (S.ex P (ρ b *ᵥ z)).left = (S.ex P z).left ≫ (X'.univ.act.act b).left) →
    ∀ ga : D'.La →ₗ[D.O] D'.La, (∀ P₁ P₂, IsPeriod D' ρ P₁ → IsPeriod D' ρ P₂ → (∀ u, P₂ (ga u) = P₁ u) →
      S.u P₁ ≫ c₂.q = S.u P₂ ≫ c₁.q ∧ ∀ z, (S.ex P₁ z).left ≫ c₂.tot = (S.ex P₂ z).left ≫ c₁.tot) →
    ∀ (k : ℕ) (α : Fin k → 𝓞 D.F), CorrEq S (c₁.pw k) (c₂.tw α) ga (diagAct (algebraMap (𝓞 D.F) D.O) ρ α) ∧
      ∀ P, IsPeriod D' ρ P → (∀ z z', (S.ex P z).left ≫ c₁.tot = (S.ex P z').left ≫ c₁.tot → z - z' ∈ P.range) →
        ∀ z z', S.pt k P z ≫ c₁.pw k = S.pt k P z' ≫ c₁.pw k → S.pt k P z = S.pt k P z'

def FixLoc : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), D.a = 1 → D.m = 1 → ∀ (v : InfinitePlace G.F), sigPosH (G.gram_herm v) = 1 → ∀ (t₀ : D.F →+* ℂ), (∀ i, D.tau i = t₀) → ∀ (gb : GBase D.toG ℂ) (N N' : ℕ) (h : G.GAf), LevOk L N N' h → ∀ (X : GenModel gb N) (X' : GenModel gb N') (c₁ : Leg L 1 X' X) (c₂ : Leg L h X' X) (hX : SmoothOfRelativeDimension D.g X.univ.A.hom) (hL) (hX' : SmoothOfRelativeDimension D.g X'.univ.A.hom) (hL') (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ),
    FineAt (gfam X.univ hX hL) (RingHom.id ℂ) ρ N (D.Cls N) → IsSigD D ρ t₀ →
    SmoothOfRelativeDimension (D.n - 1) X'.s → (∀ g, h * g ∈ L.KN N → GlobalTheory.LKCx.RegAf G g) →
    ∀ (U : Unif (gfamD X' hX' hL') (RingHom.id ℂ) ρ N' (D.Cls N')) (B : GlobalTheory.LKCx.Form G) (PD : PDic L B.β) (RD : RDic L v B.β ρ t₀)
      (i : Fin U.n) (P : (U.Di i).La →+ (Fin D.g → ℂ)) (j : (U.Di i).La →+ VQ D) (a : GlobalTheory.LKCx.Dat G v B.β), IsPeriod (U.Di i) ρ P →
      IsCoord L B PD RD N' (U.Di i) (U.t i) P j a → ∀ y, Sees B {g | h * g ∈ L.KN N} a y →
      ∀ (k : ℕ) (α : Fin k → 𝓞 D.F), (∀ s, (2 : 𝓞 D.F) ∣ α s) → ∀ (h₁ : c₁.pw k ≫ sZ X k = sZ X' k) (h₂ : c₂.tw α ≫ sZ X k = sZ X' k),
      ∃ Fx : Finset (CxPts (sZ X' k) (RingHom.id ℂ)), (∀ x, x ∈ Fx ↔ x.1 ≫ (GlobalTheory.KS.pow X'.univ.A k).hom = U.u i P ∧
          x.1 ≫ c₁.pw k = x.1 ≫ c₂.tw α) ∧ Fx.Nonempty ∧
        ∀ At : CxPts (sZ X' k) (RingHom.id ℂ) → Matrix (Fin (D.n - 1 + k * D.g)) (Fin (D.n - 1 + k * D.g)) ℂ, (∀ x ∈ Fx, GlobalTheory.W1.IsTan (D.n - 1 + k * D.g) (c₁.pw k) (c₂.tw α) h₁ h₂ x (At x)) → (∀ x ∈ Fx, (1 - At x).det ≠ 0) ∧ ∀ t : ℂ, ∑ x ∈ Fx, lefTerm (At x) t =
            wtFix L v t₀ α t (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) (GlobalTheory.RootSumWeights.eigL G v _ y a.2.1)

def PowSm : Prop :=
  ∀ (X : Scheme.{0}) (s : X ⟶ Sp ℂ) (d g : ℕ), SmoothOfRelativeDimension d s → QuasiCompact s → IsSeparated s →
    ∀ (A : Over X) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ k : ℕ,
    SmoothOfRelativeDimension (d + k * g) ((GlobalTheory.KS.pow A k).hom ≫ s) ∧ QuasiCompact ((GlobalTheory.KS.pow A k).hom ≫ s) ∧
      IsSeparated ((GlobalTheory.KS.pow A k).hom ≫ s) ∧ LocallyOfFiniteType ((GlobalTheory.KS.pow A k).hom ≫ s)

def HeckeFixedPointCMCycleClass : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), D.a = 1 → D.m = 1 → ∀ (v : InfinitePlace G.F), sigPosH (G.gram_herm v) = 1 → ∀ (t₀ : D.F →+* ℂ), (∀ i, D.tau i = t₀) → ∀ (gb : GBase D.toG ℂ), IsStd D gb → ∀ (N N' : ℕ) (h : G.GAf), LevOk L N N' h → ∀ (X : GenModel gb N) (X' : GenModel gb N')
    (c₁ : Leg L 1 X' X) (c₂ : Leg L h X' X), (∀ g, h * g ∈ L.KN N → GlobalTheory.LKCx.RegAf G g) →
    ∀ (k : ℕ) (α : Fin k → 𝓞 D.F), (∀ s, (2 : 𝓞 D.F) ∣ α s) → Etale (c₁.pw k) → ∀ (h₁ : c₁.pw k ≫ sZ X k = sZ X' k) (h₂ : c₂.tw α ≫ sZ X k = sZ X' k),
    SmoothOfRelativeDimension (D.n - 1 + k * D.g) (sZ X k) ∧
    ∃ (Fx : Finset (CxPts (sZ X' k) (RingHom.id ℂ))) (At : CxPts (sZ X' k) (RingHom.id ℂ) → Matrix (Fin (D.n - 1 + k * D.g)) (Fin (D.n - 1 + k * D.g)) ℂ),
      (∀ x, x ∈ Fx ↔ x.1 ≫ c₁.pw k = x.1 ≫ c₂.tw α) ∧ (∀ x ∈ Fx, GlobalTheory.W1.IsTan (D.n - 1 + k * D.g) (c₁.pw k) (c₂.tw α) h₁ h₂ x (At x) ∧ (1 - At x).det ≠ 0) ∧
      {x : GlobalTheory.LKCx.AllPts G v (L.KN N') (KHT p G.m G.n 1 G.Fw) | ∃ y, Sees (Quot.out x.1) {g | h * g ∈ L.KN N} (Quot.out x.2) y}.Finite ∧
      (∀ (B : GlobalTheory.LKCx.Form G) (a : GlobalTheory.LKCx.Dat G v B.β) y, Sees B (L.KN N : Set G.GAf) a y → y = 1) ∧
      ∀ t : ℂ, ∑ x ∈ Fx, lefTerm (At x) t =
        GlobalTheory.RootSumWeights.cxTotalM G v (wtFix L v t₀ α t) (L.KN N') ({g | h * g ∈ L.KN N}.indicator 1) (KHT p G.m G.n 1 G.Fw) (((KHT p G.m G.n 1 G.Fw) : Set (Gr G 1)).indicator 1)

def FixZ : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), D.a = 1 → D.m = 1 → ∀ (v : InfinitePlace G.F), sigPosH (G.gram_herm v) = 1 → ∀ (t₀ : D.F →+* ℂ), (∀ i, D.tau i = t₀) → ∀ (gb : GBase D.toG ℂ), IsStd D gb → ∀ (N N' : ℕ) (h : G.GAf), LevOk L N N' h → ∀ (X : GenModel gb N) (X' : GenModel gb N')
    (c₁ : Leg L 1 X' X) (c₂ : Leg L h X' X), (∀ g, h * g ∈ L.KN N → GlobalTheory.LKCx.RegAf G g) →
    ∀ (k : ℕ) (α : Fin k → 𝓞 D.F), (∀ s, (2 : 𝓞 D.F) ∣ α s) → Etale (c₁.pw k) → ∀ (h₁ : c₁.pw k ≫ sZ X k = sZ X' k) (h₂ : c₂.tw α ≫ sZ X k = sZ X' k),
    SmoothOfRelativeDimension (D.n - 1 + k * D.g) (sZ X k) ∧
    ∃ (Fx : Finset (CxPts (sZ X' k) (RingHom.id ℂ))) (At : CxPts (sZ X' k) (RingHom.id ℂ) → Matrix (Fin (D.n - 1 + k * D.g)) (Fin (D.n - 1 + k * D.g)) ℂ),
      (∀ x, x ∈ Fx ↔ x.1 ≫ c₁.pw k = x.1 ≫ c₂.tw α) ∧ (∀ x ∈ Fx, GlobalTheory.W1.IsTan (D.n - 1 + k * D.g) (c₁.pw k) (c₂.tw α) h₁ h₂ x (At x) ∧ (1 - At x).det ≠ 0) ∧
      ∀ t : ℂ, ∑ x ∈ Fx, lefTerm (At x) t = ((L.KN N').relIndex (GlobalTheory.HeckeCorr.heckeLevel (L.KN N) h⁻¹) : ℂ) *
        GlobalTheory.RootSumWeights.cxTotalM G v (wtFix L v t₀ α t) (L.KN N) (Formalism.UG.dosetInd ℂ (L.KN N) h⁻¹) (KHT p G.m G.n 1 G.Fw) (((KHT p G.m G.n 1 G.Fw) : Set (Gr G 1)).indicator 1)

end UpperTheory.Gal.W2
end
end

section

noncomputable section

open NumberField

namespace UpperTheory.Gal.W2

private theorem two_mul_card_places (F : Type) [Field F] [NumberField F] [IsTotallyComplex F] :
    2 * Fintype.card (InfinitePlace F) = Module.finrank ℚ F := by
  rw [← InfinitePlace.card_add_two_mul_card_eq_rank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyComplex.nrRealPlaces_eq_zero F]
  ring

open scoped Classical in
private theorem sum_fibre_place (F : Type) [Field F] [NumberField F] [IsTotallyComplex F] (x : F)
    (v : InfinitePlace F) :
    ∑ φ : F →+* ℂ with InfinitePlace.mk φ = v, φ x = ((2 * (v.embedding x).re : ℝ) : ℂ) :=
  _root_.UpperTheory.Reformulated.B.SumOverPlacesFibre.sum_fibre_place F x v

private theorem trace_eq_sum_places (F : Type) [Field F] [NumberField F] [IsTotallyComplex F] (x : F) :
    ((Algebra.trace ℚ F x : ℚ) : ℝ) = ∑ v : InfinitePlace F, 2 * (v.embedding x).re := by
  classical
  have h1 : ((Algebra.trace ℚ F x : ℚ) : ℂ) = ∑ φ : F →+* ℂ, φ x := by
    have h := trace_eq_sum_embeddings (K := ℚ) (L := F) ℂ (x := x)
    rw [eq_ratCast] at h
    let e : (F →ₐ[ℚ] ℂ) ≃ (F →+* ℂ) :=
      { toFun := fun σ => σ.toRingHom
        invFun := fun φ => φ.toRatAlgHom
        left_inv := fun σ => by ext a; rfl
        right_inv := fun φ => by ext a; rfl }
    exact h.trans (Fintype.sum_equiv e _ _ fun _ => rfl)
  have h2 : ∑ φ : F →+* ℂ, φ x =
      ∑ v : InfinitePlace F, ∑ φ : F →+* ℂ with InfinitePlace.mk φ = v, φ x :=
    (Finset.sum_fiberwise _ _ _).symm
  have h3 : ((Algebra.trace ℚ F x : ℚ) : ℂ) = ((∑ v : InfinitePlace F, 2 * (v.embedding x).re : ℝ) : ℂ) := by
    rw [h1, h2, Finset.sum_congr rfl fun v _ => sum_fibre_place F x v, Complex.ofReal_sum]
  have h4 : (((Algebra.trace ℚ F x : ℚ) : ℝ) : ℂ) = ((Algebra.trace ℚ F x : ℚ) : ℂ) := by
    push_cast
    rfl
  exact Complex.ofReal_injective (h4.trans h3)

private theorem span_top (F : Type) [Field F] [NumberField F] [IsTotallyComplex F] (n : ℕ) :
    Submodule.span ℝ (Set.range fun (x : Fin n → F) (v : InfinitePlace F) (i : Fin n) =>
      v.embedding (x i)) = ⊤ := by
  classical
  refine eq_top_iff.2 fun y _ => ?_
  set T := Submodule.span ℝ (Set.range fun (x : Fin n → F) (v : InfinitePlace F) (i : Fin n) =>
    v.embedding (x i)) with hT
  have hs : ∀ (i : Fin n) (g : InfinitePlace F → ℂ),
      (fun v => Pi.single i (g v) : InfinitePlace F → Fin n → ℂ) ∈ T := by
    intro i g
    let S : (InfinitePlace F → ℂ) →ₗ[ℝ] (InfinitePlace F → Fin n → ℂ) :=
      { toFun := fun g v => Pi.single i (g v)
        map_add' := fun a b => by funext v; simp [Pi.single_add]
        map_smul' := fun r a => by
          funext v j
          by_cases h : j = i
          · subst h
            simp
          · simp [h] }
    have hle : Submodule.span ℝ (Set.range fun (a : F) (v : InfinitePlace F) => v.embedding a) ≤
        T.comap S := by
      rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      refine Submodule.subset_span ⟨Pi.single i a, ?_⟩
      funext v j
      by_cases h : j = i
      · subst h
        simp [S]
      · simp [S, h]
    exact hle (by rw [GlobalTheory.LKTrip.HTGroup.span_real_embedding_places]; trivial)
  have hy : y = ∑ i : Fin n, fun v => (Pi.single i (y v i) : Fin n → ℂ) := by
    funext v j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hy]
  exact Submodule.sum_mem _ fun i _ => hs i fun v => y v i

theorem archSpan_of : ArchSpan := by
  intro F _ _ _ n
  refine ⟨span_top F n, ?_, trace_eq_sum_places F⟩
  rw [Module.finrank_pi_fintype]
  simp only [Module.finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  rw [← two_mul_card_places F]
  ring

end UpperTheory.Gal.W2
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical

namespace UpperTheory.Gal.W2

private theorem diag_comp' {S S' : Scheme.{0}} {A' : Over S'} {A : Over S} [GrpObj A'] [GrpObj A]
    {φ : A'.left ⟶ A.left} {φ₂ : (G2 A').left ⟶ (G2 A).left} (hs : IsSquare φ φ₂) :
    (lift (𝟙 A') (𝟙 A')).left ≫ φ₂ = φ ≫ (lift (𝟙 A) (𝟙 A)).left := by
  apply pullback.hom_ext
  · have h1 := hs.1
    have e1 : (lift (𝟙 A') (𝟙 A')).left ≫ (fst A' A').left = 𝟙 _ :=
      congrArg (fun z => z.left) (lift_fst (𝟙 A') (𝟙 A'))
    have e2 : (lift (𝟙 A) (𝟙 A)).left ≫ (fst A A).left = 𝟙 _ :=
      congrArg (fun z => z.left) (lift_fst (𝟙 A) (𝟙 A))
    show _ ≫ (fst A A).left = _ ≫ (fst A A).left
    rw [Category.assoc, h1, ← Category.assoc, e1, Category.assoc, e2, Category.id_comp, Category.comp_id]
  · have h2 := hs.2
    have e1 : (lift (𝟙 A') (𝟙 A')).left ≫ (snd A' A').left = 𝟙 _ :=
      congrArg (fun z => z.left) (lift_snd (𝟙 A') (𝟙 A'))
    have e2 : (lift (𝟙 A) (𝟙 A)).left ≫ (snd A A).left = 𝟙 _ :=
      congrArg (fun z => z.left) (lift_snd (𝟙 A) (𝟙 A))
    show _ ≫ (snd A A).left = _ ≫ (snd A A).left
    rw [Category.assoc, h2, ← Category.assoc, e1, Category.assoc, e2, Category.id_comp, Category.comp_id]

private theorem diag_lbIso' {S S' : Scheme.{0}} {A' : Over S'} {A : Over S} [GrpObj A'] [GrpObj A]
    {φ : A'.left ⟶ A.left} {φ₂ : (G2 A').left ⟶ (G2 A).left} (hs : IsSquare φ φ₂)
    {P' : LB (G2 A').left} {P : LB (G2 A).left} (hP' : P'.IsLB) (hP : P.IsLB) (hpol : LBIso P' (P.pull φ₂)) :
    LBIso (P'.pull (lift (𝟙 A') (𝟙 A')).left) ((P.pull (lift (𝟙 A) (𝟙 A)).left).pull φ) := by
  have h₁ : LBIso (P'.pull (lift (𝟙 A') (𝟙 A')).left) (P.pull (φ ≫ (lift (𝟙 A) (𝟙 A)).left)) :=
    MapComp.lbIso_pull_comp hpol _ (diag_comp' hs).symm
  have h₂ : LBIso ((P.pull (lift (𝟙 A) (𝟙 A)).left).pull φ) (P.pull (φ ≫ (lift (𝟙 A) (𝟙 A)).left)) :=
    MapComp.lbIso_pull_comp (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hP _)) φ rfl
  exact LBIso.trans (pull_isLB hP' _) (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) h₁ h₂.symm

theorem gFine_of : GFine := by
  intro p _ D b gb N M X ρ h hL f hf hG hpts hfine
  obtain ⟨φA, φ₂, hcart, hsq, hact, ⟨hpol⟩, heta⟩ := hG
  have hX : SmoothOfRelativeDimension D.g X.univ.A.hom := by
    have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} D.g
    exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension D.g) hcart.1 h
  have hL' : (X.univ.P.pull (lift (𝟙 X.univ.A) (𝟙 X.univ.A)).left).IsLB := pull_isLB X.univ.isLB _
  have hB := diag_lbIso' hsq X.univ.isLB M.univ.isLB hpol
  have hid : spMap (RingHom.id ℂ) = 𝟙 (Sp ℂ) := by
    simp [spMap, Sp]
  have key := fun (D' : PLat D.O D.inv) (t : D.La → D'.La) P (y : Sp ℂ ⟶ X.X) (hy : y ≫ X.s = spMap (RingHom.id ℂ)) =>
    GlobalTheory.T.uniformisationAt_correspond_of_cartesian D.O D.inv D.g ρ ℂ ℂ (RingHom.id ℂ) (RingHom.id ℂ) D.La (M.univ.fam h hL) (gfam X.univ hX hL') N f φA
      hcart hact hB heta D' t P y hy (by
        show (y ≫ f) ≫ M.s = _
        rw [Category.assoc, hf, hy])
  refine ⟨hX, hL', ?_, ?_, ?_⟩
  · intro (y : Sp ℂ ⟶ X.X) (hy : y ≫ X.s = spMap (RingHom.id ℂ))
    have hy' : (y ≫ f) ≫ M.s = spMap (RingHom.id ℂ) := by rw [Category.assoc, hf, hy]
    obtain ⟨D', t, P, e, hC, hU⟩ := hfine.pts (y ≫ f) hy'
    obtain ⟨e', he', -⟩ := (key D' t P y hy).2 e hU
    exact ⟨D', t, P, e', hC, he'⟩
  · intro D' t P hC hP
    obtain ⟨y', e, hU⟩ := hfine.occ D' t P hC hP
    obtain ⟨y, ⟨hy, rfl⟩, -⟩ := hpts y' (hU.1)
    obtain ⟨e', he', -⟩ := (key D' t P y (hy.trans hid.symm)).2 e hU
    exact ⟨y, e', he'⟩
  · intro D' D'' t t' P P' y y' e e' hU hU' w u hw hQ
    obtain ⟨e₁, he₁, -⟩ := (key D' t P y hU.1).1 e hU
    obtain ⟨e₂, he₂, -⟩ := (key D'' t' P' y' hU'.1).1 e' hU'
    have hyy := hfine.sep D' D'' t t' P P' (y ≫ f) (y' ≫ f) e₁ e₂ he₁ he₂ w u hw hQ
    obtain ⟨z, -, huniq⟩ := hpts (y ≫ f) he₁.1
    have a₁ : y = z := huniq y ⟨hU.1.trans hid, rfl⟩
    have a₂ : y' = z := huniq y' ⟨hU'.1.trans hid, hyy.symm⟩
    rw [a₁, a₂]

end UpperTheory.Gal.W2
end
end

section

noncomputable section

open NumberField GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open scoped Classical

namespace UpperTheory.Gal.W2

private theorem rho_ne_conj {p : ℕ} [Fact p.Prime] (D : Datum p) :
    (starRingEnd ℂ) D.ρc ≠ D.ρc := by
  intro h
  obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 h
  have h0 := D.ρc_root
  rw [hr] at h0
  have h1 : (r : ℝ) ^ 2 - D.tr * r + D.nm = 0 := by exact_mod_cast h0
  have h2 : ((D.tr : ℝ)) ^ 2 - 4 * D.nm < 0 := by exact_mod_cast D.disc_neg
  nlinarith [sq_nonneg (2 * r - D.tr)]

private theorem type_sum {p : ℕ} [Fact p.Prime] (D : Datum p) (t₀ : D.F →+* ℂ) (h₀ : t₀ (D.ω : D.F) = D.ρc)
    (hn : 1 ≤ D.n) (c : 𝓞 D.F) :
    ∑ τ : D.F →+* ℂ, (typeMult D.n t₀ (epsD D) τ : ℂ) * τ (c : D.F) =
      t₀ (c : D.F) + ∑ τ ∈ Finset.univ.filter (fun τ : D.F →+* ℂ => τ (D.ω : D.F) ≠ D.ρc), (D.n : ℂ) * τ (c : D.F) -
        (starRingEnd ℂ) (t₀ (c : D.F)) := by
  have hne : ComplexEmbedding.conjugate t₀ ≠ t₀ := by
    intro h
    apply rho_ne_conj D
    have := congrArg (fun τ : D.F →+* ℂ => τ (D.ω : D.F)) h
    simpa [ComplexEmbedding.conjugate_coe_eq, h₀] using this
  have hc : (ComplexEmbedding.conjugate t₀) (D.ω : D.F) ≠ D.ρc := by
    simpa [ComplexEmbedding.conjugate_coe_eq, h₀] using rho_ne_conj D
  have key : ∀ τ : D.F →+* ℂ, (typeMult D.n t₀ (epsD D) τ : ℂ) * τ (c : D.F) =
      (if τ = t₀ then τ (c : D.F) else 0) + (if τ (D.ω : D.F) ≠ D.ρc then (D.n : ℂ) * τ (c : D.F) else 0) -
        (if τ = ComplexEmbedding.conjugate t₀ then τ (c : D.F) else 0) := by
    intro τ
    unfold typeMult epsD
    by_cases h1 : τ = t₀
    · subst h1
      simp [hne.symm, h₀]
    · by_cases h2 : τ = ComplexEmbedding.conjugate t₀
      · subst h2
        have hc' : (starRingEnd ℂ) (t₀ (D.ω : D.F)) ≠ D.ρc := by
          simpa [ComplexEmbedding.conjugate_coe_eq] using hc
        simp [h1, hc', Nat.cast_sub hn]
        ring
      · by_cases h3 : τ (D.ω : D.F) = D.ρc <;> simp [h1, h2, h3]
  rw [Finset.sum_congr rfl fun τ _ => key τ, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.sum_ite_eq', Finset.sum_filter]
  simp [ComplexEmbedding.conjugate_coe_eq]

theorem baseC_of : BaseC := by
  intro p _ D ha hm t₀ ht ρ hs gb hst
  have hsub : Subsingleton (Fin D.a) := by rw [ha]; infer_instance
  let i₀ : Fin D.a := ⟨0, by omega⟩
  let b : Base D ℂ :=
    { unit := fun k hk => by
        refine isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 fun h => ?_)
        subst h
        exact (Fact.out : p.Prime).one_lt.ne' (Nat.coprime_zero_left p |>.1 hk)
      ρ := gb.ρ
      ρ_root := gb.ρ_root
      t := gb.t
      t_ω := gb.t_ω
      comax := fun i j hij => absurd (hsub.elim i j) hij
      apart := fun i j hij => absurd (hsub.elim i j) hij }
  refine ⟨b, rfl, fun i => (RingHom.id_comp _).symm, ?_⟩
  intro c
  have hti : b.t i₀ c = t₀ (c : D.F) := by
    have := hst.2 i₀ c
    rw [ht i₀] at this
    exact this
  have hb : b.ρ = D.ρc := hst.1
  have h₀ : t₀ (D.ω : D.F) = D.ρc := by rw [← ht i₀]; exact D.tau_ω i₀
  rw [hs.tr c, type_sum D t₀ h₀ hs.pos c, hm, Fintype.sum_subsingleton _ i₀, Fintype.sum_subsingleton _ i₀]
  simp [hti, hb]

end UpperTheory.Gal.W2
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.coordEx_of :
    UpperTheory.Gal.W2.PlaceEx → UpperTheory.Gal.W2.AdOfWit → UpperTheory.Gal.W2.PlaceLoc → UpperTheory.Gal.W2.PlacePer → UpperTheory.Gal.W2.CoordEx := by
  intro hEx hAd hLoc hPer p _ D G L ha hm v hv t₀ ht₀ ρ hρ PD RD N hN hNp D' t P hC hP
  obtain ⟨q, j, hj⟩ := hEx p D G L ha hm v hv t₀ ht₀ ρ hρ N D' t hC ⟨P, hP⟩
  obtain ⟨⟨f, nu, rfl, h1, h2⟩, hH⟩ := hC
  have hW : IsWit D' f nu := by
    refine ⟨h1, fun n hn hnp => ?_⟩
    obtain ⟨a1, a2, a3, a4, a5⟩ := h2 n hn hnp
    refine ⟨a1, a2, a3, a4, fun a a' => ?_⟩
    have e : D.plat.EF a a' = 2 * D.EF a a' := by
      show ((2 : ℤ) • D.EF) a a' = _
      simp [LinearMap.smul_apply]
    have := a5 a a'
    rw [e] at this
    exact this
  obtain ⟨h₁, hR⟩ := hAd p D G L (Quot.out q) D' j hj f nu hW
  obtain ⟨M, hM, hs, hML⟩ := hLoc p D G L _ D' j hj hH
  obtain ⟨hp, rfl⟩ := (PD (Quot.out q)).onto M hM hs
  obtain ⟨Q, hQ, hQP⟩ := (hPer p D G L _ ρ D' j hj).1 P hP
  obtain ⟨z, hz⟩ := (RD (Quot.out q)).line Q hQ
  exact ⟨q, ((h₁, hp), z), j, hj, hR N hN hNp, hML, Q, hQ, hQP, hz⟩
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.coordOcc_of :
    UpperTheory.Gal.W2.WitOfAd → UpperTheory.Gal.W2.PlacePer → UpperTheory.Gal.W2.CoordOcc := by
  intro hW hP p _ D G L _ _ v _ t₀ _ ρ _ PD RD N hN hNp B a
  obtain ⟨D', t, j, hcls, hpl, hco, hloc⟩ :=
    hW p D G L B N hN hNp a.1.1 ((PD B).lat a.1.2) ((PD B).isLat _) ((PD B).perf _)
  obtain ⟨Q, hQ, hrel⟩ := (RD B).per a.2
  have hev : Even (Module.finrank ℚ D.F) := by
    rw [← NumberField.InfinitePlace.card_add_two_mul_card_eq_rank]
    simp [NumberField.IsTotallyComplex.nrRealPlaces_eq_zero]
  have hg : 2 * D.g = Module.finrank ℤ D.La := by
    obtain ⟨k, hk⟩ := hev
    rw [D.rankLa, Datum.g, hk, ← two_mul, mul_left_comm, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  exact ⟨D', t, Q.comp j, j, hcls, (hP p D G L B.β ρ D' j hpl).2 Q hQ hg, hpl, hco, hloc, Q, hQ,
    fun u => rfl, hrel⟩
end
