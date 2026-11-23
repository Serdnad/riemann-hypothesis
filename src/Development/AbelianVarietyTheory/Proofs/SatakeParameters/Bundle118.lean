module

public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle004
public import Formalism.LocalToGlobal.Columns.DecorationStabilizerTrivialUnipotent
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.FourierColumnIndicator
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle010
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle011
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.JetSumTable
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.BadPrimesPeriodBound
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle013
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle002
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle110
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle080
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionToCpAlgebraMap
public import Mathlib.RingTheory.MvPowerSeries.Rename
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle111
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle112
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.NeutralLocalFields.Bundle001
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle025

@[expose] public section

section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.WeightedChainData

noncomputable section

namespace GlobalTheory.KFormsCmp

section Cong

variable {E V : Type} [Field E] [AddCommGroup V] [Module E V]

end Cong

section Red

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)}






end Red

section Primes

variable {X : Fields} {Pr : Primes X} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}

theorem notMem_of_QE (hs : IsSel X sel) (mu : Tup X.F X.E X.K S) {P : HeightOneSpectrum (𝓞 X.E)}
    (hP : P ∈ QE sel (mu : Chr X.F X.E X.K)) {p : ℕ} (hp : p.Prime) (hS : p ∈ S) : (p : 𝓞 X.E) ∉ P.asIdeal := by
  classical
  intro hm
  unfold QE at hP
  split_ifs at hP with hf
  swap
  · simp at hP
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hP
  have hv' : v ∈ Qprime (mu : Chr X.F X.E X.K) := (Set.Finite.mem_toFinset hf).1 hv
  have hg : GoodPl X.E S v := by
    by_contra hn
    have := (Subgroup.mem_inf.1 mu.2).2
    exact hv' (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 this v) hn)
  apply hg.2.2
  have h1 : (p : 𝓞 X.F) ∈ v.asIdeal := by
    rw [← hs v, Ideal.mem_under]
    simpa using hm
  have h2 : ((p : ℕ) : 𝓞 X.F ⧸ v.asIdeal) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk v.asIdeal)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 h1
  have h3 := (ringChar.spec _ p).1 h2
  have h4 : ringChar (𝓞 X.F ⧸ v.asIdeal) = p :=
    ((Nat.dvd_prime hp).1 h3).resolve_left CharP.ringChar_ne_one
  show ringChar (𝓞 X.F ⧸ v.asIdeal) ∈ S
  rwa [h4]

theorem g_mem_of_vGs (hP : Pr.Ok) {w : HeightOneSpectrum (𝓞 X.E)} (hw : w ∈ Pr.vGs) :
    ∃ k, (Pr.g k : 𝓞 X.E) ∈ w.asIdeal := by
  classical
  rcases Finset.mem_union.1 hw with h | h
  · exact ⟨0, hP.g_mem h⟩
  · exact ⟨1, hP.g_mem h⟩

theorem disj (hP : Pr.Ok) (hs : IsSel X sel) (mu : Tup X.F X.E X.K S) (hg : ∀ k, Pr.g k ∈ S)
    {P : HeightOneSpectrum (𝓞 X.E)} (hQ : P ∈ QE sel (mu : Chr X.F X.E X.K)) : P ∉ Pr.vGs := fun hw => by
  obtain ⟨k, hk⟩ := g_mem_of_vGs hP hw
  exact notMem_of_QE hs mu hQ (hP.g_prime k) (hg k) hk

end Primes

section Top

variable {E : Type} [Field E] {a n : ℕ}

end Top

section Levels

variable {D : D7} {u : D.what₂.Word} {μ : D.what₂.Tup} (T : ChainData D u μ)



variable {T}

end Levels

section Points

variable {D : D7} {u : D.what₂.Word} {μ : D.what₂.Tup} (T : ChainData D u μ)

abbrev APt (i : ℕ) : Type := AmbientLatticeAvoidance.Pt (R := D.R) T.sel T.xi T.L T.w i


variable {T}

end Points

section Moves

variable {D : D7} {u : D.what₂.Word} {μ : D.what₂.Tup} (T : ChainData D u μ)
  (abelian₂ : HeightOneSpectrum (𝓞 T.X.E) → Submodule (𝓞 T.X.E) (Sp T.X.E (AmbientLatticeAvoidance.rkTop D.R)))
  (dep : HeightOneSpectrum (𝓞 T.X.E) → ℕ)

variable {T abelian₂ dep}

end Moves

section Classes

variable {D : D7} {u : D.what₂.Word} {μ : D.what₂.Tup} {T : ChainData D u μ}
  {abelian₂ : HeightOneSpectrum (𝓞 T.X.E) → Submodule (𝓞 T.X.E) (Sp T.X.E (AmbientLatticeAvoidance.rkTop D.R))}
  {dep : HeightOneSpectrum (𝓞 T.X.E) → ℕ}


variable {rep : ∀ i, (D.chTw u μ).cls i → APt T i}


end Classes

section Kernels

variable {D : D7} {u : D.what₂.Word} {μ : D.what₂.Tup} {T : ChainData D u μ}
  {rep : ∀ i, (D.chTw u μ).cls i → APt T i}




variable {abelian₂ : HeightOneSpectrum (𝓞 T.X.E) → Submodule (𝓞 T.X.E) (Sp T.X.E (AmbientLatticeAvoidance.rkTop D.R))}
  {dep : HeightOneSpectrum (𝓞 T.X.E) → ℕ}

end Kernels

end GlobalTheory.KFormsCmp
end
end

section

noncomputable section

namespace GlobalTheory.ColPeriod

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker
open _root_.Formalism.L2.Col (AutY ChGlob ChIdx ChPt Chars Fields Frs HomE IsMu0 IsSdLat IsSel Jat LocCst Primes
  PsiAt QE RowPt Sall Sp UF Wts XiAt cAof cBof cOf homAt lamYat muAt mulLat qOf qValC rowSG stabL stdLat tilQ ybSet)
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recWts recSeam HostTie AnTie badS)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierColumnIndicator (FnModAt FnMod facTop)
open GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance (DegOneUnram)
open GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation (StdOver IsFrames)
open GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable (jetSum RatIdx)
open GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint (WtCompat InDeg HAt LatWithBasis)

section Notions

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] {a b : ℕ}

def AwayAt (P : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 K)) (B : ℕ) (N : Submodule (𝓞 E) (Sp E a))
    (N' : Submodule (𝓞 E) (Sp E b)) (Φ : HomE E a b → K) : Prop :=
  (∀ x, w.valuation K (Φ x) ≤ 1) ∧ ∀ x z, z ∈ homAt {P} N N' → Φ (x + ((qOf P : E) ^ B) • z) = Φ x


open Classical in
def DatumAt (Sg S : Finset (HeightOneSpectrum (𝓞 E))) (g c : ℕ) (w : HeightOneSpectrum (𝓞 K)) (N : Submodule (𝓞 E) (Sp E a))
    (N' : Submodule (𝓞 E) (Sp E b)) (Ξ : HomE E a b → K) : Prop :=
  (∀ x, w.valuation K (Ξ x) ≤ 1) ∧ (∀ x, Ξ x ≠ 0 → x ∈ homAt Sg N N') ∧
    ∀ x z, z ∈ mulLat g (homAt Sg N N') → z ∈ mulLat c (homAt (S \ Sg) N N') → Ξ (x + z) = Ξ x

end Notions

def JetLossAt {X : Fields} (Pr : Primes X) (R : Ranks) (A : Amb X)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) : Prop :=
  ∀ (i : Fin 2) (w : HeightOneSpectrum (𝓞 X.K)), ((Pr.g i : ℕ) : 𝓞 X.K) ∈ w.asIdeal →
  ∀ (u : Pr.Word) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)), cst.Ok →
  ∀ (j b : ℕ), j < R.m → b = R.N (j + 1) →
  ∀ (N : Submodule (𝓞 X.E) (Sp X.E (R.N j))) (N' : Submodule (𝓞 X.E) (Sp X.E b)),
    IsSdLat N → IsSdLat N' → StdOver (Pr.g i) N → StdOver (Pr.g i) N' →
  ∀ Ξ : HomE X.E (R.N j) b → X.K, DatumAt (Pr.vG i) (Sall sel mu u) (Pr.g i) (cBof sel mu cst u) w N N' Ξ →
  ∀ e : DVar X.Tau (R.N j) b →₀ ℕ, e.degree + 1 < Pr.g i →
    e ∈ RatIdx A (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N N' Ξ →
    w.valuation X.K ((Pr.g i : X.K) ^ (X.f * R.N j * b) *
      (e.prod fun k n => X.emb k.1 (star ((Pr.piG i : 𝓞 X.E) : X.E)) ^ n) *
      jetSum A (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N N' Ξ e) ≤ 1

def LevelPrimes : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ)
    (mu : Tup X.F X.E X.K S), X.Ok → Pr.Ok → IsSel X sel →
    ∀ P : rowSG Pr sel mu, DegOneUnram P.1 ∧ (P.1 ∉ Pr.vGs → qOf P.1 ∉ S)

def HeckeUnit : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (m : ℕ) (Ch : Chars X Pr m) (σ₀ : X.K →+* ℂ) (e : X.Tau → ℚ) (j : Fin m)
    (χ : Formalism.L2.Host.HChar X.E), X.Ok → Pr.Ok → IsMu0 Ch σ₀ e j χ →
    ∀ (p : ℕ) (w : HeightOneSpectrum (𝓞 X.K)) (P : HeightOneSpectrum (𝓞 X.E)), p.Prime → (p : 𝓞 X.K) ∈ w.asIdeal →
      (p : 𝓞 X.E) ∉ P.asIdeal → ∀ (x : X.Eˣ) (k : X.K), σ₀ k = ((χ.locK P x : ℂˣ) : ℂ) → w.valuation X.K k = 1

def TwistUnit : Prop :=
  ∀ (F E K : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Field K] [NumberField K] (S : Set ℕ)
    (mu : Tup F E K S) (P : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 K)),
    w.valuation K ((unifVal (mu : Chr F E K) P : Kˣ) : K) = 1 ∧ w.valuation K ((qValC (mu : Chr F E K) P : Kˣ) : K) = 1

def ScalarUnit : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ)
    (e : Fin R.m → X.Tau → ℚ) (eta : Formalism.L2.Host.HChar X.E),
    X.Ok → Pr.Ok → IsSel X sel → (∀ i, Pr.g i ∈ S) → Ch.Tied G.σ₀ e G.mu0 eta → L.Ok Ch sel mu cst G m2 →
    ∀ (i : Fin 2) (w : HeightOneSpectrum (𝓞 X.K)), ((Pr.g i : ℕ) : 𝓞 X.K) ∈ w.asIdeal → ∀ j, j < R.m →
      (∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vG i → w.valuation X.K (cst.muq (j + 1) P) = 1) ∧
      ∀ (n : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E n)) (fr : Frs X.E n (rowSG Pr sel mu)),
        IsSdLat N → StdOver (Pr.g i) N → IsFrames N fr →
        w.valuation X.K (muInvDet sel (rowSG Pr sel mu) (mUof Ch mu j) (muAt Ch sel mu cst j) N fr) = 1

def EntryAtG : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ),
    L.Ok Ch sel mu cst G m2 → ∀ i, i < m2 → ∀ (al : L.β i) (be : L.β (i + 1)) (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs →
      DegOneUnram P.1 → FnMod P.1 (XiAt Ch sel mu cst i P (L.h i al P) (L.h (i + 1) be P))

def VolumeAtQ : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (sharp : Bool) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) (h : AutY X R j)
    (w : HeightOneSpectrum (𝓞 X.K)), P ∉ Pr.vGs → DegOneUnram P → ((qOf P : ℕ) : 𝓞 X.K) ∉ w.asIdeal →
    w.valuation X.K (_root_.Formalism.L2.Col.Loc.volN X.K (_root_.Formalism.L2.Col.Loc.Cbe (Jat (Pr := Pr) sharp j P) h)
      (_root_.Formalism.L2.Col.Loc.N1 X.E (R.N j) (cOf R j) ⊓ stabL X.E _ (lamYat (Pr := Pr) (R := R) j P)))⁻¹ ≤ 1

def EntryAtQ : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ),
    L.Ok Ch sel mu cst G m2 → ∀ (P : rowSG Pr sel mu) (w : HeightOneSpectrum (𝓞 X.K)), P.1 ∉ Pr.vGs → DegOneUnram P.1 →
      ((qOf P.1 : ℕ) : 𝓞 X.K) ∉ w.asIdeal → (∀ j, j < R.m → w.valuation X.K (cst.muq (j + 1) P) = 1) →
      (∀ i, i < m2 → ∀ (al : L.β i) (be : L.β (i + 1)),
        AwayAt P.1 w cst.B (stdLat X.E _) (stdLat X.E _) (XiAt Ch sel mu cst i P (L.h i al P) (L.h (i + 1) be P))) ∧
      ∀ (al : L.β m2) (y : Sp X.E (R.N (m2 + 1))),
        AwayAt P.1 w cst.B (stdLat X.E _) (stdLat X.E _) fun x => PsiAt Ch sel mu cst m2 P (L.h m2 al P) x y

def TopAtQ : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ)
    (u : Pr.Word), Pr.Ok → IsSel X sel → Pr.T u ∈ S →
    L.Ok Ch sel mu cst G m2 → ∀ (P : rowSG Pr sel mu) (w : HeightOneSpectrum (𝓞 X.K)), P.1 ∉ Pr.vGs → DegOneUnram P.1 →
      ((qOf P.1 : ℕ) : 𝓞 X.K) ∉ w.asIdeal →
      ∀ (p : ChPt (R := R) sel mu u (m2 + 1)) (d : RowPt Pr R sel mu), ∀ Y ∈ ybSet sel mu cst p.deco.1.N,
        AwayAt P.1 w cst.B p.deco.1.N (tilQ sel mu u d).1.N (facTop Ch sel mu cst m2 p Y d P)

def JetOpIntegral : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (ι : Type) [Fintype ι] (a b : ℕ) (hab : a < b)
    (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (s s' : ι → ℤ) (n : ι → ℕ), WtCompat hab lam lam' s s' n →
    ∀ (M : ι → Submodule (𝓞 K) (Fin a → K)) (MW : ι → Submodule (𝓞 K) (Fin b → K)),
      LatWithBasis w M 1 → LatWithBasis w MW 1 →
      ∀ (c : K) (J : (DVar ι a b →₀ ℕ) → K), (∀ m, InDeg lam s' m → w.valuation K (c * J m) ≤ 1) →
        ∀ F ∈ HAt w lam M, c • jetOp lam lam' J n F ∈ HAt w lam' MW

def NabLeDel : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n)
    (M : ι → Submodule (𝓞 K) (Fin n → K)), (∀ τ, Submodule.IsFullLattice K (M τ)) →
    ∀ (p : ℕ) (w : HeightOneSpectrum (𝓞 K)), p.Prime → (p : 𝓞 K) ∈ w.asIdeal → (∀ τ, (lam τ).spread < p) →
      localization₂ w.asIdeal (nabK lam M) ≤ localization₂ w.asIdeal (delK lam M)

open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.ColPeriod.N_lt_succ (R : _root_.Formalism.BasicNotions.Ranks) (j : ℕ) : R.N j < R.N (j + 1) := by
  unfold _root_.Formalism.BasicNotions.Ranks.N
  simp

def ChainWeights : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R) (u : Pr.Word) (j : ℕ), j < R.m →
    ∃ s s' : X.Tau → ℤ, WtCompat (N_lt_succ R j) (W.lamTrue u j) (W.lamTrue u (j + 1)) s s' (nuLast W u j) ∧
      ∀ (τ : X.Tau) (a : Fin (R.N j)), (W.lamTrue u j τ).w a + s' τ = (W.nuW u (j + 1) τ).w a

def PartitionSize : Prop :=
  ∀ (D : D7) (EX : ErrX D) (u : D.what₂.Word) (j : ℕ), j < D.R.m → ∀ τ : D.what₂.Tau,
    nuAbs D u (j + 1) τ = ((∑ a, ((recWts EX).nuW u (j + 1) τ).w a : ℤ) : ℝ)

def StdMove : Prop :=
  ∀ (X : Fields) (Pr : Primes X), Pr.Ok → ∀ (i : Fin 2) (n : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E n)), IsSdLat N →
    ∃ γ : UF X.E n, StdOver (Pr.g i) (gmap γ.1 N)

end GlobalTheory.ColPeriod
end
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.AboveL

theorem restricts_of_isFrobSS : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : Formalism.ConjugateSelfDual.IsPlaceOver A v) (h' : Formalism.ConjugateSelfDual.IsPlaceOver A v') (X Y : Type) [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X] [AddCommGroup Y] [Module ℂ Y] [FiniteDimensional ℂ Y] (ρ : Representation ℂ (Weil h) X) (N : Module.End ℂ X) (a : WDRep h X) (ρ' : Representation ℂ (Weil h') Y) (N' : Module.End ℂ Y) (b : WDRep h' Y), IsSmooth ρ → IsSmooth ρ' → IsFrobSS ⇑ρ N a → IsFrobSS ⇑ρ' N' b → ∀ e : X ≃ₗ[ℂ] Y, (∀ (σ : Weil h) (σ' : Weil h'), (∀ z : Ω, (σ : Formalism.ConjugateSelfDual.G K Ω) z = (σ' : Formalism.ConjugateSelfDual.G L Ω) z) → ∀ x, e (ρ σ x) = ρ' σ' (e x)) → (∀ x, e (N x) = N' (e x)) → Restricts (WD.mk a) (WD.mk b) := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ _ A v v' h h' X Y _ _ _ _ _ _ ρ N a ρ' N' b _ _ ha hb e hρ hN
  let f := (Module.finBasis ℂ X).equivFun
  let a₁ := a.transport f
  let b₀ := ResEx.resRep h h' a₁
  let g : Y ≃ₗ[ℂ] (Fin (Module.finrank ℂ X) → ℂ) := e.symm.trans f
  let ρ'' : Weil h' → Module.End ℂ (Fin (Module.finrank ℂ X) → ℂ) :=
    fun σ' => f.conjAlgEquiv ℂ (ρ (ResEx.resW h h' σ'))
  let N'' := f.conjAlgEquiv ℂ N
  have hss : IsFrobSS ρ'' N'' b₀ := by
    refine ⟨?_, fun σ' => ?_⟩
    · show f.conjAlgEquiv ℂ a.N = _
      rw [ha.1]
    · show Commute (f.conjAlgEquiv ℂ (a.ρ (ResEx.resW h h' σ'))) _ ∧ IsNilpotent (_ - f.conjAlgEquiv ℂ (a.ρ (ResEx.resW h h' σ')))
      refine ⟨(ha.2 (ResEx.resW h h' σ')).1.map (f.conjAlgEquiv ℂ), ?_⟩
      have := (ha.2 (ResEx.resW h h' σ')).2.map (f.conjAlgEquiv ℂ)
      rwa [map_sub] at this
  have hiso : b.Iso b₀ := by
    refine IsFrobSS.iso hb hss g (fun σ' y => ?_) (fun y => ?_)
    · have h1 := hρ (ResEx.resW h h' σ') σ' (fun _ => rfl) (e.symm y)
      rw [LinearEquiv.apply_symm_apply] at h1
      show f (e.symm (ρ' σ' y)) = f.conjAlgEquiv ℂ (ρ (ResEx.resW h h' σ')) (f (e.symm y))
      rw [← h1]
      simp
    · have h1 := hN (e.symm y)
      rw [LinearEquiv.apply_symm_apply] at h1
      show f (e.symm (N' y)) = f.conjAlgEquiv ℂ N (f (e.symm y))
      rw [← h1]
      simp
  refine ⟨_, a₁, b₀, WD.sound (a.iso_transport f).symm, (WD.sound hiso).symm, rfl, fun σ σ' hs => ?_⟩
  show a₁.ρ (ResEx.resW h h' σ') = a₁.ρ σ
  congr 1
  exact Subtype.ext (AlgEquiv.ext fun z => (hs z).symm)

end GlobalTheory.AboveL
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU GlobalTheory.OnePlace Classical

noncomputable section
namespace GlobalTheory.OnePlace.Letters

theorem constantCoeff_jetLogG (p : ℕ) [Fact p.Prime] (n' : ℕ) {β : Type} (v : ZMod n' × β) :
    MvPowerSeries.constantCoeff (jetLogG p n' v) = 0 := by
  show jetLogG p n' v 0 = 0
  unfold jetLogG
  refine Finset.sum_eq_zero fun e _ => ?_
  rw [if_neg]
  intro h
  have h2 := congrArg (fun m : ZMod n' × β →₀ ℕ => m (v.1 - 2 * (e : ZMod n'), v.2)) h
  simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.single_eq_same] at h2
  exact (pow_ne_zero e (pow_ne_zero 2 (Fact.out : p.Prime).ne_zero)) h2.symm

def posEquiv (n r0 r1 : ℕ) [NeZero n] : Zidx n r0 r1 ≃ ZMod n × Fin r0 × Fin r1 where
  toFun z := (((z.1 : ℕ) : ZMod n), z.2)
  invFun v := (toFin v.1, v.2)
  left_inv z := by
    ext <;> simp [toFin, ZMod.val_natCast, Nat.mod_eq_of_lt z.1.2]
  right_inv v := by
    ext <;> simp [toFin, ZMod.natCast_zmod_val]

theorem coeff_inLetters {n r0 r1 : ℕ} [NeZero n] {R : Type} [Semiring R] (f : MvPowerSeries (Zidx n r0 r1) R)
    (m : ZMod n × Fin r0 × Fin r1 →₀ ℕ) :
    MvPowerSeries.coeff m (inLetters f) = MvPowerSeries.coeff (Finsupp.mapDomain (posEquiv n r0 r1).symm m) f := rfl

theorem inLetters_eq_rename {n r0 r1 : ℕ} [NeZero n] {R : Type} [CommRing R] (f : MvPowerSeries (Zidx n r0 r1) R) :
    inLetters f = MvPowerSeries.rename (posEquiv n r0 r1) f := by
  ext m
  have hm : m = Finsupp.mapDomain (posEquiv n r0 r1) (Finsupp.mapDomain (posEquiv n r0 r1).symm m) := by
    rw [← Finsupp.mapDomain_comp, Equiv.self_comp_symm, Finsupp.mapDomain_id]
  have h1 := MvPowerSeries.coeff_embDomain_rename (posEquiv n r0 r1).toEmbedding f
    (Finsupp.mapDomain (posEquiv n r0 r1).symm m)
  rw [Finsupp.embDomain_eq_mapDomain] at h1
  rw [coeff_inLetters]
  conv_rhs => rw [hm]
  exact h1.symm

theorem map_inLetters {n r0 r1 : ℕ} [NeZero n] {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)
    (f : MvPowerSeries (Zidx n r0 r1) R) :
    MvPowerSeries.map φ (inLetters f) = inLetters (MvPowerSeries.map φ f) := by
  ext m
  rw [MvPowerSeries.coeff_map, coeff_inLetters, coeff_inLetters, MvPowerSeries.coeff_map]

theorem subst_inLetters_jetLogG {p : ℕ} [Fact p.Prime] {n' r0 r1 : ℕ} [NeZero n'] (F : MvPowerSeries (Zidx n' r0 r1) (FormalGroupSystem.K0 p)) :
    (∀ z, MvPowerSeries.constantCoeff (jetZ p n' r0 r1 z) = 0) ∧
    MvPowerSeries.subst (fun v : ZMod n' × Fin r0 × Fin r1 => MvPowerSeries.C (1 : ℂ_[p]) * jetLogG p n' v)
      (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (inLetters F)) =
    MvPowerSeries.subst (jetZ p n' r0 r1) (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) F) := by
  refine ⟨fun z => constantCoeff_jetLogG p n' _, ?_⟩
  have ha : MvPowerSeries.HasSubst
      (fun v : ZMod n' × Fin r0 × Fin r1 => MvPowerSeries.C (1 : ℂ_[p]) * jetLogG p n' v) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun v => by
      rw [map_mul, constantCoeff_jetLogG, mul_zero]
  rw [map_inLetters, inLetters_eq_rename, MvPowerSeries.rename_eq_subst,
    MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.HasSubst.X_comp _) ha]
  congr 1
  funext z
  rw [Function.comp_apply, MvPowerSeries.subst_X ha, map_one, one_mul]
  rfl

end GlobalTheory.OnePlace.Letters
end
end

section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.twistedDualSizeWord_letter_eq_pageWord : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ ψ : D.R.GG), Roomy L C → ∀ a : ZMod (orderOf ψ), (((recWord L j ε (letter τ ψ)).sz a : ℕ) : ℤ) = (pageWord L j ε τ ψ).sz a ∧ (recWord L j ε (letter τ ψ)).Mi a = (pageWord L j ε τ ψ).Mi a ∧ (recWord L j ε (letter τ ψ)).hi a = (pageWord L j ε τ ψ).hi a ∧ (ThickN (bHat L) (etaHat L) (recWord L j ε (letter τ ψ)).sz a ↔ (pageWord L j ε τ ψ).thick a) := by
  first | exact @GlobalTheory.HTW.Rec.recWord_letter_eq_pageWord | exact GlobalTheory.HTW.Rec.recWord_letter_eq_pageWord | (intros; apply GlobalTheory.HTW.Rec.recWord_letter_eq_pageWord <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ThetaGL GlobalTheory.TameIwahori ValuativeRel

theorem _root_.GlobalTheory.T.parahoricVector_twoBlockProduct_exists_perm_ne_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (χ : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (σ₁ : Representation ℂ (GL (Fin r) k) V) (σ₂ : Representation ℂ (GL (Fin t) k) W) (f : _), f ≠ 0 → IsParahoricVec χ (prod₂ σ₁ σ₂) f → ∃ w : Equiv.Perm (Fin (r + t)), f.1.1 (GlobalTheory.Parabolic.permGL k w) ≠ 0 := by
  first | exact @GlobalTheory.ParahoricPerm.exists_perm_ne_zero | exact GlobalTheory.ParahoricPerm.exists_perm_ne_zero | (intros; apply GlobalTheory.ParahoricPerm.exists_perm_ne_zero <;> assumption)
end

section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.mem_integralGLAtPrime_of_congruent_one_mod_pow : ∀ {E : Type} [Field E] [NumberField E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (d : ℕ) (g : Formalism.L2.Col.Sp E n ≃ₗ[E] Formalism.L2.Col.Sp E n),
  (∀ a b, Formalism.L2.Col.IntAt P (((Formalism.L2.Col.qOf P : E) ^ d)⁻¹ * (LinearMap.toMatrix' g.toLinearMap a b - (1 : Matrix (Fin n) (Fin n) E) a b))) →
  (∀ a b, Formalism.L2.Col.IntAt P (((Formalism.L2.Col.qOf P : E) ^ d)⁻¹ * (LinearMap.toMatrix' g.symm.toLinearMap a b - (1 : Matrix (Fin n) (Fin n) E) a b))) →
  g ∈ Formalism.L2.Col.GLint E n P ∧ ∀ w ∈ Formalism.L2.Col.stdAt E n P, ((Formalism.L2.Col.qOf P : E) ^ d)⁻¹ • (g w - w) ∈ Formalism.L2.Col.stdAt E n P := by
  first | exact @GlobalTheory.Proof.mem_integralGLAtPrime_of_congruent_one_mod_pow.glint_of_cong | exact GlobalTheory.Proof.mem_integralGLAtPrime_of_congruent_one_mod_pow.glint_of_cong | (intros; apply GlobalTheory.Proof.mem_integralGLAtPrime_of_congruent_one_mod_pow.glint_of_cong <;> assumption)
end
