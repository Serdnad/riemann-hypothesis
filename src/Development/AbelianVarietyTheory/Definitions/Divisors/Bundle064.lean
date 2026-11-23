module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
public import Formalism.SharpRestriction.Divisibility.Bundle002
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle004
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle027
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle026

@[expose] public section

section

set_option autoImplicit false


noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop
open scoped ENNReal

namespace GlobalTheory.CovHt

def cost {K : Type} [Field K] [NumberField K] (e : HeightOneSpectrum (𝓞 K) →₀ ℝ) (t : (K →+* ℂ) → ℝ) : ℝ :=
  ((e.sum fun la a => a * Real.log (Ideal.absNorm la.asIdeal : ℝ)) + ∑ σ, t σ) / (Module.finrank ℚ K : ℝ)

section Generic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) {D : D7}
  (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r)

def depthOn (Z : Comp Xo c) (G : WTZ E) (v : Rul Xo c → EReal) : EReal := ⨅ w ∈ latOn U Z G, v (w : Rul Xo c)

def smallL (Z : Comp Xo c) (G : WTZ E) (τ : ℕ) (t : ℝ) : Set (cuspOn U Z (τ • G)) :=
  {f | (∀ la, ∀ v ∈ (recVals Xo c).1 la, (τ : EReal) * depthOn U Z G v ≤ v (f : Rul Xo c)) ∧
    ∀ σ, GoodEmb c σ → ∀ y : FPt (U σ).X, (⟨y.1, y.2.1⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z →
      ENNReal.ofReal (homN (U σ) x (τ • G) f ⟨y.1, y.2.1⟩) ^ 2 ≤
        ENNReal.ofReal (Real.exp (2 * τ * t)) * bergOn (U σ) (V σ) (dict σ) Z G y ^ τ}

def volL (a : ℕ) (Z : Comp Xo c) (G : WTZ E) (t : ℝ) : ℝ≥0∞ :=
  countVol (dimFlag Dw) (Module.finrank ℚ c.F) a fun τ => (smallL U x V dict Z G τ t).encard

def FinBd (Z : Comp Xo c) (G : WTZ E) (a : ℕ) (θ : Rul Xo c) (e : HeightOneSpectrum (𝓞 c.F) →₀ ℝ) : Prop :=
  ∀ la, ∀ v ∈ (recVals Xo c).1 la, (∃ w ∈ latOn U Z G, v (w : Rul Xo c) ≠ ⊤) →
    (a : EReal) * depthOn U Z G v ≤ v θ + ((a * e la : ℝ) : EReal)

def NoBase (Z : Comp Xo c) (G : WTZ E) : Prop :=
  ∀ la, ∀ v ∈ (recVals Xo c).1 la, ∀ G' : WTZ E, ∀ f ∈ cuspOn U Z G', v f ≠ ⊤ → ∃ w ∈ latOn U Z G, v (w : Rul Xo c) ≠ ⊤

def InfBd (Z : Comp Xo c) (G G₀ : WTZ E) (a : ℕ) (θ : Rul Xo c) (t : (c.F →+* ℂ) → ℝ) : Prop :=
  (∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) ∧
  ∀ σ, GoodEmb c σ → ∀ y : FPt (U σ).X, (⟨y.1, y.2.1⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z →
    ENNReal.ofReal (homN (U σ) x G₀ θ ⟨y.1, y.2.1⟩) ^ 2 ≤
      ENNReal.ofReal (Real.exp (2 * a * t σ)) * bergOn (U σ) (V σ) (dict σ) Z G y ^ a

def Carries (Z : Comp Xo c) (u u' : AllWt.Weight Dw) (θ : Rul Xo c) : Prop :=
  θ ∈ secZ Xo c (exOf Dw ((8 : ℤ) • (u - u')) 0) ∧ genVal Z θ ≠ 0 ∧
    ∀ (k : ℕ), ∀ f ∈ cuspOn U Z ((8 * k) • wtOf Dw u' 0), θ ^ k * f ∈ cuspOn U Z ((8 * k) • wtOf Dw u 0)

def Mult (Z : Comp Xo c) (u u' : AllWt.Weight Dw) (cc : ℝ) : Prop :=
  NoBase U Z (wtOf Dw u 0) ∧ ∃ (θ : Rul Xo c) (e : HeightOneSpectrum (𝓞 c.F) →₀ ℝ) (t : (c.F →+* ℂ) → ℝ),
    Carries U Z u u' θ ∧ FinBd U Z (wtOf Dw u 0) 8 θ e ∧
    InfBd U x V dict Z (wtOf Dw u 0) (wtOf Dw ((8 : ℤ) • (u - u')) 0) 8 θ t ∧ cost e t ≤ cc

def l1 (u : AllWt.Weight Dw) : ℝ := ∑ τ, ∑ i, |(u τ i : ℝ)|


variable (E) in
def htEx (p : ℕ) : ℝ := 1 / ((p : ℝ) - 1) + 40 * ((padicValNat p (discr E).natAbs : ℝ) / (Module.finrank ℚ E : ℝ))


variable (Xo c) in
def HTCmp : Prop := ∀ (p : ℕ) (la : HeightOneSpectrum (𝓞 c.F)), p.Prime → ((p : ℕ) : 𝓞 c.F) ∈ la.asIdeal →
  ∀ v ∈ (recVals Xo c).1 la, ∃ w ∈ (htVals Xo c).1 la, ∀ (u : AllWt.Weight Dw), ∀ f ∈ secZ Xo c (exOf Dw u 0),
    w f ≤ v f + (((vLa la (p : c.F) : ℝ) * htEx E p * l1 u : ℝ) : EReal)


variable (l) in
def htCost (B : ℝ) : ℝ := ∑ᶠ p ∈ htPrimes l B, htEx E p * Real.log p

def WtGap (u : AllWt.Weight Dw) (g : ℝ) : Prop :=
  0 < g ∧ (∀ τ, StrictAnti (u τ)) ∧ ∀ τ (a b : Fin (Dw.p + Dw.q)), Dw.p ≤ (a : ℕ) → a ≠ b → g ≤ |(u τ a : ℝ) - u τ b|

def bndB (u : AllWt.Weight Dw) (g : ℝ) : ℝ :=
  4 * (Fintype.card (Psi H) : ℝ) * ((Dw.p + Dw.q : ℕ) : ℝ) ^ 2 * (1 + (⨆ k : Psi H × Fin (Dw.p + Dw.q), |(u k.1 k.2 : ℝ)|) / g)

def errX (s : ℝ) (u : AllWt.Weight Dw) (g : ℝ) : ℝ :=
  (Real.log (bndB u g) + s) * l1 u + (Dw.q : ℝ) * ∑ τ, ((⨆ i, (u τ i : ℝ)) - ⨅ i, (u τ i : ℝ))

def MeanGe (u : AllWt.Weight Dw) (B X : ℝ) : Prop :=
  ∃ sl : Comp Xo c → ℝ, (∀ Z, (sl Z : EReal) ≤ compVolSlope U x 8 (mixVals Xo c B) Z u) ∧
    -X ≤ (∑ᶠ Z, sl Z) / (Nat.card (Comp Xo c) : ℝ)

def MeanAll (s C : ℝ) : Prop := ∀ (u : AllWt.Weight Dw) (g : ℝ), WtGap u g → MeanGe U x u (bndB u g) (C * errX s u g)

end Generic

def ell (D : D7) : ℝ := Real.log D.host.rdE + |dlogL D 1|

section One

open MvPolynomial Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs

variable {D : D7} (Y : ShimX D.what₂.Tau)

def DeRhamMinusHodgeTateGoodPrimesAt : Prop := ∀ (Sx : Finset ℕ) (R : ℝ) (p : ℕ),
  p.Prime → p ≠ 2 → UnramE D p → p ∉ Y.lev → ∀ (τ : D.what₂.Tau) (k : ℕ), 1 ≤ k →
  ∀ (m : ℕ), m + k = dimFl D.what₂.Tau Y.N + 1 → ∀ Q : MvPolynomial (Vm D.what₂.Tau Y.N) ℝ,
    Q.IsWeightedHomogeneous (wt D.what₂.Tau Y.N) m →
    Y.arMix Sx R p ((tagDR D.what₂.Tau _ (C ((Nat.factorial k : ℝ)⁻¹) * pk D _ τ k) -
          tagHT D.what₂.Tau _ (C ((Nat.factorial k : ℝ)⁻¹) * pk D _ τ k)) * Q) =
      Real.log p * ((∑' n : ℕ, ((p : ℝ) ^ k)⁻¹ ^ (n + 1) *
          Y.chern (chLie Y.j (k - 1) (frobEmb D p (n + 1) (Sum.inl τ)) * collapse D _ Q)) -
        Y.chern (chLie Y.j (k - 1) (Sum.inl τ) * collapse D _ Q) / ((p : ℝ) - 1))

def DeRhamHodgeTateDifferenceKilledAt : Prop := ∀ (Sx : Finset ℕ) (R : ℝ) (p : ℕ), p.Prime →
  ∀ (τ : D.what₂.Tau) (k : ℕ), 1 ≤ k → ∀ Q : MvPolynomial (Rt D.what₂.Tau Y.N) ℝ,
    Y.arMix Sx R p (tagHT D.what₂.Tau _ (pk D _ τ k) * (tagDR D.what₂.Tau _ Q - tagHT D.what₂.Tau _ Q)) = 0

end One



section Obj

open GlobalTheory.Mean4 GlobalTheory.Mean4O Formalism.BasicNotions.DV


structure HypothesesH : Prop where
  sieg : GlobalTheory.Published.SiegelToroidalIntegral
  fan : GlobalTheory.Published.ToroidalChartsForFan
  charts : GlobalTheory.Published.ToroidalCharts
  deg : GlobalTheory.Published.ArDegree

end Obj

end GlobalTheory.CovHt

end
end

section

noncomputable section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan

namespace GlobalTheory.Poinc

structure FPre {O : Type} [CommRing O] (bar : O → O) (q p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [IsLocalRing A] where

  Y : Type

  ev : Y → A →+* PadicAlgCl p
  ev_le : ∀ y h, ‖ev y h‖ ≤ 1
  ev_lt : ∀ y, ∀ h ∈ maximalIdeal A, ‖ev y h‖ < 1

  X : Y → Type
  [add : ∀ y, AddCommGroup (X y)]
  [mod : ∀ y, Module O (X y)]
  [fin : ∀ y, Module.Finite O (X y)]
  [proj : ∀ y, Module.Projective O (X y)]
  [freeZ : ∀ y, Module.Free ℤ (X y)]
  [finZ : ∀ y, Module.Finite ℤ (X y)]
  rank_le : ∀ y, Module.finrank O (X y) ≤ q

  β : ∀ y, LinearMap.BilinForm ℤ (X y)
  bal : ∀ y, β y ∈ balForms bar (X y)
  pos : ∀ y x, x ≠ 0 → 0 < β y x x

  sc : Y → ℝ
  sc_pos : ∀ y, 0 < sc y

attribute [instance] FPre.add FPre.mod FPre.fin FPre.proj FPre.freeZ FPre.finZ

namespace FPre

variable {O : Type} [CommRing O] {bar : O → O} {q p : ℕ} [Fact p.Prime] {A : Type} [CommRing A] [IsLocalRing A]
  (Φ : FPre bar q p A) {s : ℕ} (W : Matrix (Fin s) (Fin s) ℤ)

def abelian₂ : Prop :=
  ∃ C : ℝ, ∀ y x, x ≠ 0 → ∃ h ∈ maximalIdeal A, Real.exp (-(C * (Φ.sc y * Φ.β y x x))) ≤ ‖Φ.ev y h‖

def IsTerms {Q : Type} (t : ∀ y, (Fin s → Φ.X y) → Q → PadicAlgCl p) : Prop :=
  (∀ y μ c, ‖t y μ c‖ ≤ Real.exp (-(Φ.sc y * qW W (Φ.β y) μ))) ∧
    ∀ y μ, ∃ c, ‖t y μ c‖ = Real.exp (-(Φ.sc y * qW W (Φ.β y) μ))

def OrbitSums (N₁ N : ℕ) (y₀ : Φ.Y) (k : ∀ y, Φ.X y₀ →ₗ[ℤ] Φ.X y) {Q : Type}
    (t : ∀ y, (Fin s → Φ.X y) → Q → PadicAlgCl p) : Prop :=
  ∀ (m : ℕ) (a : Fin m × Fin s → Φ.X y₀) (c : Fin m → Q) (e : ℕ), ∃ f : A, ∀ y,
    ∃ h ∈ maximalIdeal A, ∀ ε : ℝ, 0 < ε → ∃ S : Finset (Fin m × Fin s → Φ.X y), (↑S : Set _) ⊆ orbit O N₁ N (k y) a ∧
      (∀ μ ∈ orbit O N₁ N (k y) a, μ ∉ S → Real.exp (-(Φ.sc y * ∑ i, (qW W (Φ.β y) (fun u => μ (i, u)) : ℝ))) < ε) ∧
      ‖Φ.ev y f - ∑ μ ∈ S, ∏ i, t y (fun u => μ (i, u)) (c i)‖ ≤ max ε (‖Φ.ev y h‖ ^ e)

def Four (N₁ : ℕ) : Prop :=
  ∀ (y₀ : Φ.Y) (N₀ : ℕ), ∃ N, N₀ ≤ N ∧ N₁ ∣ N ∧ ∃ (k : ∀ y, Φ.X y₀ →ₗ[ℤ] Φ.X y) (Q : Type)
    (t : ∀ y, (Fin s → Φ.X y) → Q → PadicAlgCl p), k y₀ = LinearMap.id ∧ (∀ y, IsUnimodMod O N (k y)) ∧ Φ.IsTerms W t ∧
      Φ.OrbitSums W N₁ N y₀ k t

def Approx (φ : InvFun O) (d : ℕ) : Prop :=
  ∀ (y₀ : Φ.Y) (e : ℕ), ∃ f : A, ‖Φ.ev y₀ f‖ = Real.exp (-(Φ.sc y₀ * (d * φ.evalZ (Φ.β y₀)))) ∧
    ∀ y, ‖Φ.ev y f‖ ≤ Real.exp (-(Φ.sc y * (d * φ.evalZ (Φ.β y)))) ∨ ∃ h ∈ maximalIdeal A, ‖Φ.ev y f‖ ≤ ‖Φ.ev y h‖ ^ e

def ClassSums (N₁ N : ℕ) (y₀ : Φ.Y) (k : ∀ y, Φ.X y₀ →ₗ[ℤ] Φ.X y) {Q : Type}
    (t : ∀ y, (Fin s → Φ.X y) → Q → PadicAlgCl p) (B : Type) [CommRing B] [Algebra A B] (𝔷 : Ideal B) : Prop :=
  ∃ (ev' : Φ.Y → B →+* PadicAlgCl p) (f : (Fin s → Φ.X y₀) → Q → B),
    (∀ y a, ev' y (algebraMap A B a) = Φ.ev y a) ∧ (∀ y b, ‖ev' y b‖ ≤ 1) ∧ (∀ y, ∀ b ∈ 𝔷, ‖ev' y b‖ < 1) ∧
    (∀ c c' κ, (∀ u, CongMod N (c u) (c' u)) → f c κ = f c' κ) ∧
    (∀ y c κ (ε : ℝ), 0 < ε → ∃ S₀ : Finset (Fin s → Φ.X y), ∀ S : Finset (Fin s → Φ.X y),
      (∀ μ ∈ S, ∀ u, CongMod N (μ u) (k y (c u))) → (∀ μ ∈ S₀, (∀ u, CongMod N (μ u) (k y (c u))) → μ ∈ S) →
        ‖ev' y (f c κ) - ∑ μ ∈ S, t y μ κ‖ ≤ ε) ∧
    ∀ σ : B ≃ₐ[A] B, 𝔷.comap σ = 𝔷 → ∃ γ : Φ.X y₀ →ₗ[ℤ] Φ.X y₀, (∀ (c : O) x, CongMod N (γ (c • x)) (c • γ x)) ∧
      (N : ℤ) ∣ LinearMap.det γ - 1 ∧ (∀ x, CongMod N₁ (γ x) x) ∧ ∀ c κ, σ (f c κ) = f (fun u => γ (c u)) κ

end FPre

end GlobalTheory.Poinc
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ}

structure Trait (F : SFam g n ζ) where

  V : Type
  [ring : CommRing V]
  [dom : IsDomain V]
  [dvr : IsDiscreteValuationRing V]
  [char : CharZero V]
  complete : IsAdicComplete (maximalIdeal V) V

  ϖ : V
  irr : Irreducible ϖ

  y : Sp (FractionRing V) ⟶ F.X

  G : Over (Sp V)
  [grp : GrpObj G]
  [comm : IsCommMonObj G]
  semi : IsSemiAbelian G

  D : DegData V (maximalIdeal V)

  A : PolAV (Sp (FractionRing V))

  U : Unif (maximalIdeal V) D A G

  α : A.A.left ⟶ F.univ.A.left

  α₂ : (G2 A.A).left ⟶ (G2 F.univ.A).left
  cart : IsGrpPullback A.A F.univ.A y α
  sq : IsSquare α α₂
  lb : LBIso (abelian₂ A.A A.L) (F.univ.P.pull α₂)

  β : LinearMap.BilinForm ℤ D.toPre.X
  symm : ∀ a b, β a b = β b a
  mono : IsMonomial D.toPre ![ϖ] ![β]

attribute [instance] Trait.ring Trait.dom Trait.dvr Trait.char Trait.grp Trait.comm

def ValOn (F : SFam g n ζ) {S : Scheme.{0}} (j : F.X ⟶ S) (φ : InvFun ℤ) (J : S.IdealSheafData) (d : ℕ) : Prop :=
  ∀ (T : Trait F) (ξ : Sp T.V ⟶ S), jK T.V ≫ ξ = T.y ≫ j →
    ∃ a : ℕ, (a : ℝ) = d * φ.evalZ T.β ∧ idlAlong J ξ = Ideal.span {T.ϖ ^ a}

def SharpOver (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ) {T : Scheme.{0}} (P : PolAV T) (u : T ⟶ F.X) : Prop :=
  ∃ c : SiegPre g n ζ (u ≫ F.s), SiegPB c F.univ u ∧ ∃ pr : Fin 8 → (P.A ⟶ c.A), (∀ a, IsMonHom (pr a)) ∧
    (∀ (T' : Over T) (y : Fin 8 → (T' ⟶ c.A)), ∃! x : T' ⟶ P.A, ∀ a, x ≫ pr a = y a) ∧
    LBIso P.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2))

def ThetaInt (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ) {Z : Scheme.{0}} (i : F.X ⟶ Z) : Prop :=
  ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real)
    (u : Sp S.R ⟶ F.X), SharpOver F W ρ.P u → (∀ w, (spMap S.R.val.toRingHom ≫ u) w ∈ genericPoints F.X) →
    ∀ (M : RatModel o' Ω) (π : M.Z ⟶ Z), IsNormalScheme M.Z → M.pt ≫ π = spMap S.R.val.toRingHom ≫ u ≫ i →
      M.HasDiv S.th

def IsNormBl {S Z : Scheme.{0}} (π : S ⟶ Z) (J : Z.IdealSheafData) : Prop :=
  IsNormalScheme S ∧ ∃ (S₀ : Scheme.{0}) (π₀ : S₀ ⟶ Z) (ν : S ⟶ S₀) (U : S₀.Opens), FinalTheorems.Blowup π₀ J ∧ ν ≫ π₀ = π ∧
    IsFinite ν ∧ Dense (U : Set S₀) ∧ Dense (ν ⁻¹' U : Set S) ∧ IsIso (ν ∣_ U)

def IsThetaCompact (F : SFam g n (zetaAway n)) {Z : Scheme.{0}} (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) : Prop :=
  IsProjOver z ∧ IsNormalScheme Z ∧ IsOpenImmersion i ∧ i ≫ z = F.s ∧ Dense (Set.range i) ∧
    ∃ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W ∧ ThetaInt F W i

def IdealSt : Prop :=
  ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n))
    (i : F.X ⟶ Z), IsThetaCompact F z i → ∀ φ : InvFun ℤ, IsPolFan id g φ →
      ∃ (d : ℕ) (J : Z.IdealSheafData), 1 ≤ d ∧ (∀ x ∈ J.support, x ∉ Set.range i) ∧ ValOn F i φ J d

def PoinSt : Prop :=
  ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n))
    (i : F.X ⟶ Z), IsThetaCompact F z i → ∀ OZ : LB Z, OZ.IsLB → IsAmpleLB OZ → ∀ φ : InvFun ℤ, IsPolFan id g φ →
      ∃ (d : ℕ) (J : Z.IdealSheafData) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) (BD : EffCartierData S),
        1 ≤ d ∧ (∀ x ∈ J.support, x ∉ Set.range i) ∧ ValOn F i φ J d ∧ IsNormBl π J ∧ IsProjOver (π ≫ z) ∧
        IsOpenImmersion j ∧ Dense (Set.range j) ∧ j ≫ π = i ∧ π ⁻¹' Set.range i = Set.range j ∧
        BD.idealSheaf = J.comap π ∧ ValOn F j φ BD.idealSheaf d ∧
        ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → IsAmpleLB (CechPic.tens (lbPow (OZ.pull π) k) (CechPic.dual BD.lb))

end GlobalTheory.Poinc
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.KeyEven

def KeyOn {R K : Type} [CommRing R] [CommRing K] (f : R →+* K) (x : KeyIn K) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (L : RigLB G)
    (σ : L.L.Sec) (y : Fin x.P.g → (epsR R ⟶ G)) : Prop :=
  ∃ (φ : x.P.A.left ⟶ G.left) (he : eSec x.P.A ≫ φ = spMap f ≫ eSec G) (ψ : LB.Iso x.P.L (L.L.pull φ))
    (F : DualNumber R →+* DualNumber K),
    IsGrpPullback x.P.A G (spMap f) φ ∧ ψ.IsGen ∧
    LB.Gen.Maps (LB.linCombIso ψ (K := PUnit) (fun _ => eSec x.P.A) (fun _ => 1)) x.rig
      (rigPullOf φ (spMap f) he L.L L.rig) ∧
    (∀ (j : (L.L.pull φ).ι) (i : x.P.L.ι) (h : (L.L.pull φ).U j ⊓ x.P.L.U i ≤ φ ⁻¹ᵁ L.L.U (j PUnit.unit)),
      (φ.appLE _ _ h).hom (σ.f (j PUnit.unit)) =
        (show Γ(x.P.A.left, (L.L.pull φ).U j ⊓ x.P.L.U i) from (ψ.s (j, i)).val) * resG _ inf_le_right (x.th.f i)) ∧
    (∀ a, F (algebraMap R _ a) = algebraMap K _ (f a)) ∧ F DualNumber.eps = DualNumber.eps ∧
    ∀ i, (x.v i).left ≫ φ = spMap F ≫ (y i).left

def HasUnif {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G]
    (L : LB G.left) : Prop :=
  ∃ (D : DegData V (IsLocalRing.maximalIdeal V)) (A : PolAV (Sp (FractionRing V)))
    (U : Unif (IsLocalRing.maximalIdeal V) D A G), LBIso U.LG.L L

def UnifAlong {S : Scheme.{0}} (G : Over S) [GrpObj G] (L : LB G.left) : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
    IsAdicComplete (IsLocalRing.maximalIdeal V) V → Finite (IsLocalRing.ResidueField V) →
    ∀ ξ : Sp V ⟶ S, (ξ ⁻¹' abLocus G).Nonempty → ∀ [IsCommMonObj ((Over.pullback ξ).obj G)],
      HasUnif ((Over.pullback ξ).obj G) (L.pull (pullback.fst G.hom ξ))

def PolOnAb {S : Scheme.{0}} (G : Over S) [GrpObj G] (L : LB G.left) : Prop :=
  ∀ W : S.Opens, (W : Set S) ⊆ abLocus G →
    letI : (Over.pullback W.ι).Monoidal := (Over.instBraidedPullback (f := W.ι)).toMonoidal
    letI : GrpObj ((Over.pullback W.ι).obj G) := Functor.grpObjObj (F := Over.pullback W.ι)
    RelAmple ((Over.pullback W.ι).obj G) (L.pull (pullback.fst G.hom W.ι)) ∧
    KTriv ((Over.pullback W.ι).obj G) (L.pull (pullback.fst G.hom W.ι))

def NzFib {S : Scheme.{0}} {G : Over S} {L : LB G.left} (σ : L.Sec) : Prop :=
  ∀ s : S, ∃ z : G.left, G.hom z = s ∧ z ∈ nonzeroLocus σ

def KeyTrait (κ : GlobalTheory.KeyCl.Rule) : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
    IsAdicComplete (IsLocalRing.maximalIdeal V) V → Finite (IsLocalRing.ResidueField V) →
    ∀ (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (σ : L.L.Sec) (x : KeyIn (FractionRing V))
      (y : Fin x.P.g → (epsR V ⟶ G)), IsSemiAbelian G → HasUnif G L.L → IsLieBasis y → NzFib σ →
      KeyOn (algebraMap V (FractionRing V)) x G L σ y →
      ∃ u : Vˣ, (κ (FractionRing V) x : FractionRing V) = algebraMap V (FractionRing V) u

def KeyTraitU (κ : GlobalTheory.KeyCl.Rule) : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
    IsAdicComplete (IsLocalRing.maximalIdeal V) V → Finite (IsLocalRing.ResidueField V) →
    ∀ (D : DegData V (IsLocalRing.maximalIdeal V)) (x : KeyIn (FractionRing V)) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G],
    IsSemiAbelian G → ∀ (U : Unif (IsLocalRing.maximalIdeal V) D x.P G) (w₀ : GlobalTheory.UT.W0 U.toUnifPre),
    GlobalTheory.UT.NormW U.toUnifPre w₀ x.rig → ∀ y : Fin x.P.g → (epsR V ⟶ G), IsLieBasis y →
    (∀ i, GlobalTheory.IsVecOver (algebraMap V (FractionRing V)) (U.gen.inv.left ≫ pullback.fst G.hom (jK V)) (y i) (x.v i)) →
    ∀ σ : U.LG.L.Sec, NzFib σ →
      GlobalTheory.Cartier.SecMaps w₀ (GlobalTheory.Cartier.secPull x.th U.gen.hom.left) (GlobalTheory.Cartier.secPull σ (pullback.fst G.hom (jK V))) →
      ∃ u : Vˣ, (κ (FractionRing V) x : FractionRing V) = algebraMap V (FractionRing V) u

def KeyLoc (κ : GlobalTheory.KeyCl.Rule) : Prop :=
  ∀ (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CharZero A] [Algebra.FiniteType ℤ A]
    (G : Over (Sp A)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (σ : L.L.Sec) (x : KeyIn (FractionRing A))
    (y : Fin x.P.g → (epsR A ⟶ G)), IsSemiAbelian G → SmoothOfRelativeDimension x.P.g G.hom → IsOpen (abLocus G) →
    L.IsSymmetric → PolOnAb G L.L → UnifAlong G L.L → IsLieBasis y → NzFib σ →
    KeyOn (algebraMap A (FractionRing A)) x G L σ y →
    ∃ u : Aˣ, (κ (FractionRing A) x : FractionRing A) = algebraMap A (FractionRing A) u

def KeyGlob : Prop :=
  ∀ (S : Scheme.{0}) (s : S ⟶ Sp ℤ) (G : Over S) [GrpObj G] [IsCommMonObj G] (g : ℕ) (L : RigLB G) (δ : LB S)
    (σ : (CechPic.tens L.L (δ.pull G.hom)).Sec), 1 ≤ g → IsIntegral S → Geo.Tor.IsNormalScheme S → LocallyOfFiniteType s →
    CharZero Γ(S, ⊤) → IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → (abLocus G).Nonempty → IsOpen (abLocus G) →
    L.IsSymmetric → δ.IsLB → PolOnAb G L.L → UnifAlong G L.L → NzFib σ →
    LBIso (lbPow δ 8) (lbPow (GlobalTheory.SiegelTor.hodge G g) 4)

end GlobalTheory.KeyEven

end
end
