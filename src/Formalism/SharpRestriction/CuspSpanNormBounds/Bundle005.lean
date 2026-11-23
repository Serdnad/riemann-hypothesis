module

public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle004
public import Formalism.LocalRingCardinality.DataParams₂
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.PlaceDegreeData

open MeasureTheory NumberField Matrix Finset IsDedekindDomain
open scoped InnerProductSpace ComplexOrder
open Formalism.MainNotions.S

def qOf {n : ℕ} (ε : Fin n → Bool) : ℕ := (univ.filter fun a => ε a = false).card

def pOf {n : ℕ} (ε : Fin n → Bool) : ℕ := (univ.filter fun a => ε a = true).card

def decBound {n : ℕ} (q : ℕ) (h : ℝ) (X : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  Real.exp (-(h / 8) * min (Formalism.REAL.hs X) (Real.sqrt (Formalism.REAL.hs X) / Real.sqrt (2 * (q : ℝ))))

def fdegAll (I : AutInst) {H : InfinitePlace I.F → Type} [∀ v, NormedAddCommGroup (H v)]
    [∀ v, InnerProductSpace ℂ (H v)] (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v))
    (w : ∀ v, H v) : ℝ :=
  ∏ v, fdegOf (Formalism.REAL.muG (I.ε v)) (σ v) (w v)

def HidaSetting (I : AutInst) (n₀ : ℕ) (A b : ℝ) (lam : InfinitePlace I.F → Fin I.n → ℝ)
    (μf : Measure I.Gf) (g g₀ : ℕ) (e : I.Gf → ℂ) : Prop :=
  n₀ ≤ I.n ∧ (∃ p q : ℕ, (∀ v, I.pAt v = p ∧ I.qAt v = q) ∧ q ^ 2 ≤ I.n) ∧ 2 ≤ b ∧
    Real.log (Real.log I.rd) ≤ I.n ∧ (∀ v, Formalism.QuantumDeterminants.IsHCParam (lam v)) ∧ (∀ v a, |lam v a| ≤ b ^ 2) ∧
    I.IsAdmIdem μf g g₀ e ∧ 1 ≤ g ∧ (g : ℝ) ≤ b ^ A ∧ g₀.Prime ∧ 4 * I.n < g₀ ∧ SplitsCompl I.E g₀

def q0At (I : AutInst) (v : InfinitePlace I.F) : ℕ := min (I.pAt v) (I.qAt v)

section HC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end HC

def CountData (I : AutInst) {H : InfinitePlace I.F → Type} [∀ v, NormedAddCommGroup (H v)]
    [∀ v, InnerProductSpace ℂ (H v)] (lam : InfinitePlace I.F → Fin I.n → ℝ)
    (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)) (w : ∀ v, H v)
    {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] (σs : I.Ginf → (Hs →L[ℂ] Hs))
    (tens : (∀ v, H v) → Hs) (μf : Measure I.Gf) [SigmaFinite μf] (fund : Set I.GA)
    (R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund)) (e : I.Gf → ℂ)
    (Re : I.L2 μf fund →L[ℂ] I.L2 μf fund) : Prop :=
  (∀ v, IsDS (I.ε v) (lam v) (σ v)) ∧ (∀ v, IsLowUnit (I.ε v) (lam v) (σ v) (w v)) ∧
    I.IsHilbTensor σ σs tens ∧ μf.IsHaarMeasure ∧ I.IsFundDom (I.muA μf) fund ∧
    I.IsRightReg μf fund R ∧ I.IsRConvF μf fund R e Re

def phA {G : Type*} [Group G] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (d : ℝ)
    (σ : G →* (H →L[ℂ] H)) (w : H) : G → ℂ :=
  fun g => (d : ℂ) * star ⟪w, σ g w⟫_ℂ

def IsOpIntA {G : Type*} [Group G] [MeasurableSpace G] (μ : Measure G) {Hp : Type*} [NormedAddCommGroup Hp]
    [InnerProductSpace ℂ Hp] (π : G →* (Hp →L[ℂ] Hp)) (φ : G → ℂ) (P : Hp →L[ℂ] Hp) : Prop :=
  Integrable φ μ ∧ ∀ x y : Hp, ⟪x, P y⟫_ℂ = ∫ g, φ g * ⟪x, π g y⟫_ℂ ∂μ

def PointsLemma (_D : Formalism.BasicNotions.D7) (n₀ : ℕ) (A C c cb : ℝ) : Prop :=
  ∀ (I : AutInst) (b : ℝ) (lam : InfinitePlace I.F → Fin I.n → ℝ) (g g₀ : ℕ) (e : I.Gf → ℂ)
    (H : InfinitePlace I.F → Type) [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
    [∀ v, CompleteSpace (H v)] (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)) (w : ∀ v, H v)
    (Hs : Type) [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] [CompleteSpace Hs]
    (σs : I.Ginf → (Hs →L[ℂ] Hs)) (tens : (∀ v, H v) → Hs) (μf : Measure I.Gf) [SigmaFinite μf]
    (fund : Set I.GA) (R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund))
    (Re : I.L2 μf fund →L[ℂ] I.L2 μf fund) (h : ℝ),
    HidaSetting I n₀ A b lam μf g g₀ e → CountData I lam σ w σs tens μf fund R e Re →
    (∀ v, Formalism.QuantumDeterminants.GapAtLeast (I.ε v) (lam v) h) →
    C * (I.n : ℝ) ^ 19 * (I.f : ℝ) ^ 5 * Real.log (b * I.rd) ≤ h →
    Real.log (I.f : ℝ) ≤ Real.sqrt (I.n : ℝ) →
    Real.log (Real.log b) ≤ cb * (I.n : ℝ) * (I.f : ℝ) * Real.log (I.n : ℝ) →
    |(I.Dcount σs μf fund R Re : ℝ) - I.Dstar (fdegAll I σ w) μf fund e| ≤
      Real.exp (-c * (I.n : ℝ) * (I.f : ℝ) * Real.log (I.n : ℝ)) * I.Dstar (fdegAll I σ w) μf fund e

def RowsTie (D : Formalism.BasicNotions.D7) (X : RowsAut) : Prop :=
  (∃ pl : InfinitePlace X.I.F ≃ D.what₂.Tau, AutTie D X pl) ∧ (∀ v, Formalism.QuantumDeterminants.IsHCParam (X.lam v)) ∧
    (SplitsCompl D.host.E (D.host.g 0) → SplitsCompl X.I.E X.g₀)

end Formalism.MainNotions.PlaceDegreeData
end
end

section

noncomputable section

namespace Formalism.MainNotions.S

open Formalism.BasicNotions NumberField IsDedekindDomain

variable (D : D7)

def vOne (τ : D.what₂.Tau) (l : ℕ) : ℝ :=
  if h : 1 ≤ l ∧ l ≤ D.R.k - 1 then ((D.hc τ).v ⟨l - 1, by omega⟩ : ℝ) else 0

def bOne (τ : D.what₂.Tau) (j : ℕ) : ℝ :=
  if h : 1 ≤ j ∧ j ≤ D.R.m then ((D.hc τ).b ⟨j - 1, by omega⟩ : ℝ) else 0

def uS (u : D.what₂.Word) (τ : D.what₂.Tau) : Fin D.R.k → ℝ := fun i => ((D.hcW u τ).u i : ℝ)

def uOne (u : D.what₂.Word) (τ : D.what₂.Tau) (i : ℕ) : ℝ :=
  if h : 1 ≤ i ∧ i ≤ D.R.k then uS D u τ ⟨i - 1, by omega⟩ else 0

def IsTop (τ : D.what₂.Tau) : Prop :=
  ∃ t : D.host.TT, (D.eTau τ : D.R.GG) = D.R.tau1 t

def bTop (τ : D.what₂.Tau) : ℝ := -uOne D D.u₀ τ D.R.k

def gg : ℝ := (D.host.g 0 : ℝ) * D.host.g 1

def typedPl : Set (HeightOneSpectrum (𝓞 D.host.F)) :=
  {p | ((D.host.g 0 : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal ∨ ((D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal}

abbrev SplitsE (p : ℕ) : Prop := SplitsCompl D.host.E p

def VV (τ : D.what₂.Tau) : ℝ := D.dsig τ * ∏ i ∈ Finset.range D.R.r, (i.factorial : ℝ)

def Tcrit (u : D.what₂.Word) (τ : D.what₂.Tau) : ℝ :=
  (D.host.ka ^ (-(((D.R.m : ℝ) - 1) * D.R.k + (D.R.m : ℝ) * ((D.R.m : ℝ) - 1) / 2)) *
    D.host.rdE ^ (-(((D.R.m : ℝ) - 1) / 2)) *
    gg D ^ ((D.R.k : ℝ) * D.R.m + (D.R.m : ℝ) * ((D.R.m : ℝ) - 1) / 2) *
    VV D τ / vand (uS D u τ)) ^ ((1 : ℝ) / D.R.k)

def Tr (u : D.what₂.Word) : ℝ := ((D.mem u).A.T : ℝ)

def tV (u u' : D.what₂.Word) (τ : D.what₂.Tau) : ℝ :=
  Real.sqrt (Tcrit D u τ * Tcrit D u' τ / (Tr D u * Tr D u'))


open Classical in
def aEff (u : D.what₂.Word) (τ : D.what₂.Tau) : ℝ :=
  if IsTop D τ then uOne D u τ 1 * bTop D τ / ((D.R.k : ℝ) * D.s.Del) else uOne D u τ 1 - vOne D τ 1

def gaG : ℝ :=
  ∏ᶠ p ∈ typedPl D, ∏ i ∈ Finset.Icc 1 D.R.k, ((Ideal.absNorm p.asIdeal : ℝ) ^ i - 1)


open Classical in
def genScal (u u' : D.what₂.Word) : ℝ :=
  (∏ᶠ p ∈ typedPl D, (1 + 3 / (Ideal.absNorm p.asIdeal : ℝ))) * gaG D *
    (∑' P : D.s.Pair u u',
      if Formalism.MainNotions.S.scalarP D.s P ∧
          D.s.Gterm (D.s.pfst P) ≠ 0 ∧ D.s.Gterm (D.s.psnd P) ≠ 0
      then D.s.pval P else 0).re

def IsSat {u u' : D.what₂.Word} (Φ : Set (D.s.Term u u')) : Prop :=
  Φ = famG D.s ∨ Φ = famNG D.s ∨ Φ = {t | D.s.Gterm t = 0 ∧ ¬ D.s.isId t} ∨
    Φ = {t | D.s.relevant t ∧ D.s.Gterm t = 0 ∧ ¬ D.s.isId t}

def StandingNumericalData (C0 : ℝ) : Prop :=
  let k : ℝ := D.R.k
  let Del : ℝ := D.s.Del
  (∀ τ l, 1 ≤ l → l ≤ D.R.k - 1 → 0 ≤ vOne D τ l ∧ vOne D τ l ≤ 4 * k * Del) ∧
  (∀ u (l : ℕ), 1 ≤ l → l ≤ D.R.k - 2 →
    (∀ τ, uOne D u τ (l + 1) = vOne D τ l - 1 / 2) ∨ (∀ τ, uOne D u τ (l + 1) = vOne D τ l - 1 / 2 - Del)) ∧
  (∀ u τ, 4 * k * Del ≤ uOne D u τ 1 - vOne D τ 1) ∧
  (∀ u τ, ¬ IsTop D τ → uOne D u τ 1 - vOne D τ 1 ≤ 8 * k * Del) ∧
  (∀ u τ, ¬ IsTop D τ → uOne D u τ D.R.k = vOne D τ (D.R.k - 1) - 1 / 2) ∧
  (∀ τ, IsTop D τ → 3 ≤ bOne D τ 1 - bTop D τ ∧ bOne D τ 1 / 2 ≤ bTop D τ) ∧
  (∀ u τ, InterlaceS (show D.R.k ≤ D.R.r by have := D.R.two_le_m; unfold Formalism.BasicNotions.Ranks.r; omega)
    (uS D u τ) (lamS D.R (D.hc τ))) ∧
  (∀ u u', u ≠ u' → ∀ τ, uS D u τ ≠ uS D u' τ) ∧
  (∀ u, SplitsE D (D.mem u).A.T ∧
    (D.mem u).A.T % (D.host.g 0 * D.host.g 1) ^ 2 = 1 % (D.host.g 0 * D.host.g 1) ^ 2) ∧
  (∀ u, (D.mem u).A.GamP ^ (-2 : ℤ) * D.what₂.Dstar / C0 ≤ (D.duS u : ℝ) ∧
    (D.duS u : ℝ) ≤ (D.mem u).A.GamP ^ (-2 : ℤ) * D.what₂.Dstar * C0) ∧
  SplitsE D (D.host.g 0) ∧ SplitsE D (D.host.g 1) ∧

  NumberField.discr D.host.E = NumberField.discr D.host.F ^ 2 ∧
  (∀ u, (D.mem u).A.T ≠ D.host.g 0 ∧ (D.mem u).A.T ≠ D.host.g 1)

def StandingHypotheses (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT : ℝ) : Prop :=
  let k : ℝ := D.R.k
  let m : ℝ := D.R.m
  let f : ℝ := D.R.f
  let n : ℝ := D.R.r
  let r : ℝ := D.R.rS
  let L : ℝ := large₂.sc.L
  let b : ℝ := large₂.sc.b
  let Del : ℝ := D.s.Del
  let g1 : ℝ := D.host.g 0
  let g2 : ℝ := D.host.g 1
  8 * large₂.CGam ≤ C' ∧ C' * m ^ 5 * f * L ≤ k ∧
  D.R.m ^ 4 ≤ D.R.f ∧ D.R.f ≤ D.R.k ∧
  Real.log f ≤ Real.sqrt r ∧
  Cl * L ≤ f * Real.log k ∧
  Cl * (m ^ 2 * L) ≤ k ∧
  (∀ τ j, 1 ≤ j → j ≤ D.R.m → Cl * (m * k * Del) ≤ bOne D τ j) ∧
  Cl * (m * Real.log D.host.v) ≤ k ∧
  Cl * (m ^ 3 * L * Real.log D.host.rdE) ≤ k * Real.log k ^ 2 ∧
  Real.log D.host.rdE ≤ L / Cl ∧
  (k * b) ^ 8 ≤ g1 ∧ g1 ≤ b ^ Cg ∧ (k * b) ^ 8 ≤ g2 ∧ g2 ≤ b ^ Cg ∧
  (∀ τ j, 1 ≤ j → j ≤ D.R.m → max (k ^ Cl) (b ^ cb) ≤ bOne D τ j ∧ bOne D τ j ≤ b ^ (2 : ℝ)) ∧
  (∀ τ, bOne D τ D.R.m ≤ 2 * bOne D τ 1) ∧
  (∀ u τ, uOne D u τ 1 ≤ b ^ Cu) ∧
  1 ≤ D.host.v ∧
  (k * f * L) ^ Cl ≤ Del ∧
  (∀ τ j, 1 ≤ j → j + 1 ≤ D.R.m → Cl * n ^ 19 * f ^ 5 * L ≤ bOne D τ (j + 1) - bOne D τ j) ∧
  (∀ τ (i : Fin D.R.r) (h : i.1 + 1 < D.R.r),
    Cl * k * m ^ 4 + n * m ^ 10 < lamS D.R (D.hc τ) i - lamS D.R (D.hc τ) ⟨i.1 + 1, h⟩) ∧
  (∀ u, b ^ (cT * m) ≤ Tr D u ∧ Tr D u ≤ b ^ (CT * m)) ∧
  Cl ≤ m ∧ 0 < Cl

open scoped nonZeroDivisors

def eSum (Ce : ℝ) : ℝ :=
  Ce * ∑' p : HeightOneSpectrum (𝓞 D.host.F),
    (Ideal.absNorm p.asIdeal : ℝ) ^ (-((D.R.k : ℝ) - 2 * D.R.rS - 3))

def ddE : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E :=
  ((Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F)) :
    Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)

def gE : D.host.E := ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E)

def IsLatGLOB (L : LatticeDataWithDual D) : Prop :=
  ∀ i s : ℕ,
    L.aaV i s = ddE D ^ (-((2 * ((D.R.rS : ℤ) + 1) - i - (i + s - 1)) + 1)) *
      (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (gE D))⁻¹ ∧
    L.aaP i s = ddE D ^ (-(2 * ((D.R.rS : ℤ) + 1) - i - (i + s - 1))) *
      (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (gE D))⁻¹ ∧
    L.ρ i s = rhoReal D i s

def IsLocA (u u' : D.what₂.Word) (x : D.what₂.Tau → LocalDataRealPlace D) : Prop :=
  ∀ τ, (x τ).lam = lamSH D.R (D.hc τ) ∧ (x τ).u = uS D u τ ∧ (x τ).u' = uS D u' τ

def NA : ℝ := 4 * 5 * ((D.R.rS : ℝ) + 1)

def ThA (CA : ℝ) (u u' : D.what₂.Word) (x : D.what₂.Tau → LocalDataRealPlace D) (L : LatticeDataWithDual D) : ℝ :=
  ThS D CA CA (NA D) (Tr D u) (Tr D u') (gE D) x L

def IsLocC (u u' : D.what₂.Word) (l : ℕ) (x : D.what₂.Tau → LocalDataRealPlace D) : Prop :=
  IsLocA D u u' x ∧ ∀ τ, (x τ).a = 5 / 2 - vOne D τ l ∧ (x τ).b = (D.s.Del : ℝ) / 2 - vOne D τ l ∧
    (x τ).a1 = 5 / 2 - vOne D τ l ∧ (x τ).b1 = NA D ^ 3 - vOne D τ l

end Formalism.MainNotions.S
end
end

section

open Matrix MeasureTheory NumberField Filter Topology

noncomputable section

namespace Formalism.MainNotions.S.LocalFrameAxioms

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

def LocMatch (D : D7) (T T' : ℝ) (x : LocalDataRealPlace D) (B : LocBessel D.R.k D.R.rS) : Prop :=
  B.lam = x.lam ∧ B.u = x.u ∧ B.u' = x.u' ∧ Tz D.R.k D.R.rS B.z = T ∧ Tz D.R.k D.R.rS B.z' = T' ∧
    B.ε = epsSH D.R

def FrameAx (D : D7) (δ : D.host.E) (L : LatticeDataWithDual D) (B : D.what₂.Tau → LocBessel D.R.k D.R.rS) : Prop :=
  ∃ ϱ : ℝ, IsFrameScale D L ϱ ∧ ∀ v, (B v).c = cPsi D δ v / (ϱ : ℂ)

def PsiAx (D : D7) (δ : D.host.E) : Prop :=
  δ ≠ 0 ∧ ((∀ v, (plEmb D v δ).re = 0) ∨ ∀ v, (plEmb D v δ).im = 0)

theorem k_le_nS (D : D7) : D.R.k ≤ 2 * D.R.rS + D.R.k + 1 := by omega

def Nlet (D : D7) (Kst : ℕ) : ℝ := 4 * (Kst : ℝ) * ((D.R.rS : ℝ) + 1)

section Arith

open scoped ComplexOrder

variable (D : D7)

def InProd (Sg : ℕ → ℕ → Finset D.host.E) : ℕ → List (D.host.E × ℕ) → Prop
  | _, [] => True
  | a, (t, s) :: bs => t ∈ Sg (a + 1) s ∧ InProd Sg (a + s) bs

def headsOf (Sg : ℕ → ℕ → Finset D.host.E) (j : ℕ) : Set (Point D.host.E j) := {h | InProd D Sg 0 h.1}

def PSDKOn {α : Type*} (S : Set α) (K : α → α → ℂ) : Prop :=
  ∀ (X : Finset α) (a : α → ℂ), (∀ p ∈ X, p ∈ S) → 0 ≤ ∑ p ∈ X, ∑ q ∈ X, star (a p) * K p q * a q

def KLEOn {α : Type*} (S : Set α) (K L : α → α → ℂ) : Prop := PSDKOn S (fun p q => L p q - K p q)

def ArithAxF (L : LatticeDataWithDual D) (Kd : KernelData D) : Prop :=
  (∀ p q, Kd.K 0 p q = 1) ∧
  (∀ i, i ≤ D.R.rS + 1 → PSDK (Kd.K i)) ∧
  (∀ i, 1 ≤ i → i ≤ D.R.rS + 1 → 0 ≤ Kd.e i ∧ Kd.e i ≤ 1) ∧

  (∀ (j s : ℕ) (hs : 1 ≤ s), j + s ≤ D.R.rS + 1 → ∀ (h h' : Point D.host.E j) (t t' : D.host.E)
      (ht : t ≠ 0) (ht' : t' ≠ 0),
      Kd.K (j + s) (ptSnoc D h t ht s hs) (ptSnoc D h' t' ht' s hs) ≠ 0 →
        (if j + s = D.R.rS + 1 ∧ s = 1 then t = t' else t⁻¹ - t'⁻¹ ∈ L.La' (j + 1) s)) ∧

  ∀ Sg : ℕ → ℕ → Finset D.host.E,
    ∃ Th : (j s : ℕ) → D.host.E → Point D.host.E j → Point D.host.E j → ℂ,
    ∀ (j s : ℕ) (hs : 1 ≤ s), j + s ≤ D.R.rS + 1 →
      (∀ (t : D.host.E) (ht : t ≠ 0), t ∈ Sg (j + 1) s →
        KLEOn (headsOf D Sg j)
          (fun h h' : Point D.host.E j => Kd.K (j + s) (ptSnoc D h t ht s hs) (ptSnoc D h' t ht s hs)) (Th j s t)) ∧
      (∀ t, ∀ l ∈ L.La (j + 1) s, ∀ h ∈ headsOf D Sg j, ∀ h' ∈ headsOf D Sg j, Th j s (t + l) h h' = Th j s t h h') ∧
      (∀ t, PSDKOn (headsOf D Sg j) (Th j s t)) ∧
      (∀ X : Finset D.host.E, (∀ t ∈ X, ∀ t' ∈ X, t - t' ∈ L.La (j + 1) s → t = t') →
        KLEOn (headsOf D Sg j) (fun h h' => ∑ t ∈ X, Th j s t h h')
          (fun h h' => (1 + (Kd.e (j + s) : ℂ)) * Kd.K j h h'))

variable {D}

end Arith

end Formalism.MainNotions.S.LocalFrameAxioms

end
end
