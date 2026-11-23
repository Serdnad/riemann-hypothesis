module

public import Formalism.LocalToGlobal.Divisibility.DivisionHeightBoundStatement
public import Formalism.LocalToGlobal.KernelLattices.Bundle003
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.KerEntHyp
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.AlgebraicTheory.StatementA
public import Formalism.LocalToGlobal.AlgebraicTheory.StatementKer
import Formalism.LocalToGlobal.ExponentGrids.EntryG
public import Formalism.QuotientMetricDivisors.Bundle004

@[expose] public section

section

noncomputable section
open scoped BigOperators ComplexConjugate
open NumberField IsDedekindDomain MvPolynomial

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Th1.H
open Formalism.L2.AlgTh (KerStd SplitS)
open Formalism.DivisionValues (vw)

section Cf

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {a b : ℕ}



end Cf

section AtG

variable {X : Fields} (A : Amb X) {p : ℕ} [Fact p.Prime] {a b : ℕ}

end AtG

section Lat

variable {K : Type} [Field K] [NumberField K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]

end Lat

section AtRec

open Formalism.DivisionValues (PlOver)

def StdOver {E : Type} [Field E] [NumberField E] {n : ℕ} (g : ℕ) (Lat : Submodule (𝓞 E) (Sp E n)) : Prop :=
  ∀ P : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal → localization₂ P.asIdeal Lat = stdAt E n P

end AtRec

section Hyp

variable {X : Fields} (A : Amb X) {p : ℕ} [Fact p.Prime] {a b : ℕ}

end Hyp

section Rec

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {Sg : Set ℕ}
  (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  (A : Amb X) {p : ℕ} [Fact p.Prime]

end Rec

section Paths

open Module NumberField IsDedekindDomain

open Formalism.L2.Col Formalism.L2.DIV

section Generic

variable {K : Type} [Field K] [NumberField K] [StarRing K]

variable (Q : KerChain K)

def Nd (j : ℕ) : Type := (Q.F j).Cl × (Q.F j).ιV

def famRep (j : ℕ) (c : (Q.F j).Cl) : (Q.F j).D c.1 := ((Q.F j).mem c.1).outSec.rep c.2

structure ChBas where

  B : ∀ j (c : (Q.F j).Cl), Basis (Q.F j).ιV K (Q.F j).V

  BS : Q.S.Cl → Basis Q.S.ιV K Q.S.V

variable {Q} (Bb : ChBas Q)

def crd (j : ℕ) (ν : Nd Q j) : (Q.F j).Forms →ₗ[K] K :=
  (Bb.B j ν.1).coord ν.2 ∘ₗ (LinearMap.proj (famRep Q j ν.1)) ∘ₗ ((Q.F j).mem ν.1.1).EqFun.subtype ∘ₗ LinearMap.proj ν.1.1



structure LastDat (S₁ : GSD K) (Bsp : Type) [AddCommGroup Bsp] [Module K Bsp] where

  Cl : Type
  [finCl : Fintype Cl]

  pt : Cl → S₁.D

  wt : Cl → ℕ

  V₂ : Type
  [addV : AddCommGroup V₂]
  [modV : Module K V₂]

  ι₂ : Type
  [finι : Fintype ι₂]

  β : S₁.V →ₗ[K] V₂ →ₗ[K] K

  ev : Cl → Bsp →ₗ[K] V₂

  B1 : Cl → Basis S₁.ιV K S₁.V

  B2 : Cl → Basis ι₂ K V₂

attribute [instance] LastDat.finCl LastDat.addV LastDat.modV LastDat.finι

variable {Bsp : Type} [AddCommGroup Bsp] [Module K Bsp]

variable (T : LastDat Q.S₁ Bsp)


variable {l : ℕ} [Fact l.Prime] {J : Type} [Fintype J] {Asp : Type} [AddCommGroup Asp] [Module K Asp]

def RowInt (w : HeightOneSpectrum (𝓞 K)) (NB : Set Bsp) : Prop :=
  ∀ c k, ∀ F ∈ NB, (T.B2 c).coord k (T.ev c F) = 0 ∨ 0 ≤ Formalism.DivisionValues.vw w ((T.B2 c).coord k (T.ev c F))

end Generic

section Transport

variable {K : Type} [Field K] [NumberField K] [StarRing K]

structure ChGood (Q : KerChain K) where

  s : ∀ j b, ((Q.F j).mem b).Sec

  sS : Q.S.Sec

  B : ∀ j, (Q.F j).Cl → Basis (Q.F j).ιV K (Q.F j).V

  BS : Q.S.Cl → Basis Q.S.ιV K Q.S.V

variable {Q : KerChain K} (G : ChGood Q)

variable {Bsp : Type} [AddCommGroup Bsp] [Module K Bsp] {J : Type}

end Transport

section Place

open Formalism.L2.Indef Formalism.L2.AtG.EntryG Formalism.L2.AlgTh

variable {X : Fields}

end Place

section Record

open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.AtG.EntryG Formalism.L2.AlgTh

variable {X : Fields} {Pr : Primes X} {Rk : Ranks} {W : Wts X Pr.Word Rk} {Ch : Chars X Pr Rk.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {Sg : Set ℕ}

abbrev recQ {mu : Tup X.F X.E X.K Sg} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr Rk (QE sel (mu : Chr X.F X.E X.K))}
    {P : LevFam X.E X.K Rk.r Pr.vGs} {u : Pr.Word} {m2 : ℕ} {b : L.β (m2 + 1)} {hY : YbHyp (R := Rk) sel mu cst L u m2 b} (Am : Amb X)
    (hK : KerEquivC W Ch sel mu cst L Am u m2 b hY P) (hF : ∀ j, (chF W sel mu L u j).Ok) (hE : (evGSD W Ch sel mu P u).Ok) : KerChain X.K :=
  KerChain.ofCol W Ch sel mu cst L (chKerC W Ch sel mu cst L Am u m2 b hY P hK) hF hE

section Entries

variable {mu : Tup X.F X.E X.K Sg} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr Rk (QE sel (mu : Chr X.F X.E X.K))}
  {P : LevFam X.E X.K Rk.r Pr.vGs} {u : Pr.Word} {m2 : ℕ} {b : L.β (m2 + 1)} {hY : YbHyp (R := Rk) sel mu cst L u m2 b} {Am : Amb X}
  {hK : KerEquivC W Ch sel mu cst L Am u m2 b hY P} {hF : ∀ j, (chF W sel mu L u j).Ok} {hE : (evGSD W Ch sel mu P u).Ok}
  (Bb : ChBas (recQ Am hK hF hE))

end Entries

section Steps

variable {mu : Tup X.F X.E X.K Sg} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr Rk (QE sel (mu : Chr X.F X.E X.K))}
  {P : LevFam X.E X.K Rk.r Pr.vGs} {u : Pr.Word} {m2 : ℕ} {b : L.β (m2 + 1)} {hY : YbHyp (R := Rk) sel mu cst L u m2 b} {Am : Amb X}
  {hK : KerEquivC W Ch sel mu cst L Am u m2 b hY P} {hF : ∀ j, (chF W sel mu L u j).Ok} {hE : (evGSD W Ch sel mu P u).Ok}
  {g : ℕ} [Fact g.Prime] {J : Type}

end Steps

end Record

end Paths

end Formalism.L2.Ker
end
end

section

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Mem

variable {D : D7} {u : D.what₂.Word}

end Mem

section Comparison₂

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}

def KerEntTied.MemSideU {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) : Prop :=
  ∀ u, IsMemAt (t.memObj u) (ex.errX.piT u)

end Comparison₂

end Formalism.L2.Ker
end
end

section

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Th1.H Formalism.MainNotions

def opDeg {ι : Type} {a : ℕ} (lam : ι → DomWeight a) (n : ι → ℕ) (τ : ι) : ℕ := ∑ r, ((lam τ).natW r + n τ)

def stepDeg {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (u : Pr.Word) (i : ℕ) : X.Tau → ℕ := opDeg (W.lamTrue u i) (nuLast W u i)

def StepDegIs : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R) (u : Pr.Word) (i : ℕ), i < R.m → ∀ τ : X.Tau,
    ((stepDeg W u i τ : ℕ) : ℤ) = ∑ r, (W.nuW u (i + 1) τ).w r

section Deg

variable {X : Fields} (A : Amb X) (a b : ℕ) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ) (dg : X.Tau → ℕ)

def Amb.JetAddDeg : Prop :=
  ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (c c' : ℕ) (x : HomE X.E a b), 0 < c → 0 < c' →
    InRange Sall D (c * c') N N' x → ∀ m, (∀ τ, degAt m τ = dg τ) → A.jetK Sall N N' c x m =
      latSum (mulLat c (homAt Sall N N')) (mulLat (c * c') (homAt Sall N N')) fun y => A.jetK Sall N N' (c * c') (x + y) m

def Amb.AnaStepD : Prop :=
  A.LaHyp a b Sall ∧ A.ESmooth a b ∧ A.JetsRatDeg a b Sall D dg

end Deg

section Inst

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))
  (A : Amb X) (u : Pr.Word) (m2 : ℕ)

def ThHypD : Prop :=
  (∀ i, i ≤ m2 → A.AnaStepD (R.N i) (R.N (i + 1)) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u) (stepDeg W u i)) ∧
  A.AnaStepD (R.N (m2 + 1)) (R.N R.m) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u) (stepDeg W u (m2 + 1)) ∧
  (∀ i, i ≤ m2 → ThEquivP ((chThT W Ch sel mu cst A u m2).th i) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u)
      (colValF W sel mu u i).rho (colValF W sel mu u (i + 1)).rho) ∧
  ThEquivP (chThT W Ch sel mu cst A u m2).top (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u)
      (colValF W sel mu u (m2 + 1)).rho (colVal W u R.m (Pr.vT u) (rowSG Pr sel mu)).rho

end Inst

section InstN

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (G : ChGlob X R.m)
  {D : D7} (s : Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (u : Pr.Word) (m2 : ℕ)

end InstN

section FieldDeg

variable {X : Fields} (A : Amb X) (a b : ℕ) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ) (dg : X.Tau → ℕ)

end FieldDeg

section Tied

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}

end Tied

section Reps

variable {X : Fields} (A : Amb X) (a b : ℕ) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ) (dg : X.Tau → ℕ)

end Reps

section TiedRep

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}

end TiedRep

end Formalism.L2.Ker
end
end

section

open NumberField Formalism.BasicNotions Classical

noncomputable section

namespace Formalism.L2.Ker

open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.G

variable {D : D7}

def SamePr {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (τ τ' : D.what₂.Tau) : Prop :=
  ∀ x : 𝓞 D.host.E, ‖tauEmb D lam τ (x : D.host.E)‖ < 1 ↔ ‖tauEmb D lam τ' (x : D.host.E)‖ < 1

def ConjPr {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (τ τ' : D.what₂.Tau) : Prop :=
  ∀ x : 𝓞 D.host.E, ‖tauEmb D lam τ (x : D.host.E)‖ < 1 ↔ ‖tauEmb D lam τ' (D.host.conj (x : D.host.E))‖ < 1

def dualM {N : ℕ} (M : Matrix (Fin N) (Fin N) D.host.E) : Matrix (Fin N) (Fin N) D.host.E :=
  ((M.map D.host.conj).transpose)⁻¹

def AdPl (D : D7) (w : D.what₂.places.Pl) : Prop :=
  D.host.cls (D.what₂.places.resChar w) = PrimeClass.inertClass ∨ D.host.cls (D.what₂.places.resChar w) = PrimeClass.signal ∨
    D.host.cls (D.what₂.places.resChar w) = PrimeClass.ramD

abbrev SysFam (D : D7) (u : D.what₂.Word) (μ : D.what₂.Tup) : Type :=
  ∀ i, (D.chTw u μ).cls i → D.what₂.Tau → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E

def AdaptedEnt (P : Examples₂.EntPl D) (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)) (B : PlaceMatrixFamily D) (Dx : DivX D) : Prop :=
  ∀ w : D.what₂.places.Pl, AdPl D w → ∀ u μ, LevFree Dx u μ w →
    ∃ Pm : ∀ i, (D.chTw u μ).cls i → D.what₂.Tau → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E,
      (∀ i, i ≤ D.R.m → ∀ c τ, GL3Columns.BasR D (P.lam w) τ ((O u μ).lat i c).1 ((Pm i c τ).map (tauEmb D (P.lam w) τ))) ∧
      (∀ i, i ≤ D.R.m → ∀ c τ τ', SamePr (P.lam w) τ τ' → Pm i c τ' = Pm i c τ) ∧
      (∀ i, i ≤ D.R.m → ∀ c τ τ', ConjPr (P.lam w) τ τ' → Pm i c τ' = dualM (Pm i c τ)) ∧
      (∀ i, i ≤ D.R.m → ∀ c τ, B u μ w i c τ =
        (lamC (P.lam w) ((O u μ).dgen τ))⁻¹ ^ i • (Pm i c τ).map (tauEmb D (P.lam w) τ))

def adCoef {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {N N' : ℕ} (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E)
    (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E) (k : D.what₂.Tau × Fin N' × Fin N) (j : (Bool × HH D) × Fin N × Fin N') : ℂ_[p] :=
  if tauPl D j.1 = k.1 then
    ((P' k.1).map (tauEmb D lam k.1)) k.2.1 j.2.2 * ((P k.1).map (tauEmb D lam k.1))⁻¹ j.2.1 k.2.2
  else 0

def AdaptedTh {Dx : DivX D} {Tw : TwForms D} (E : KerEnt D Dx Tw) (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)) : Prop :=
  ∀ w : D.what₂.places.Pl, AdPl D w → ∀ u μ, LevFree Dx u μ w → ∃ Pm : SysFam D u μ,
    (∀ i, i ≤ D.R.m → ∀ c τ, GL3Columns.BasR D (E.lam w) τ ((O u μ).lat i c).1 ((Pm i c τ).map (tauEmb D (E.lam w) τ))) ∧
    (∀ i, i ≤ D.R.m → ∀ c τ τ', SamePr (E.lam w) τ τ' → Pm i c τ' = Pm i c τ) ∧
    (∀ i, i ≤ D.R.m → ∀ c τ τ', ConjPr (E.lam w) τ τ' → Pm i c τ' = dualM (Pm i c τ)) ∧
    ∀ i, i < D.R.m → ∀ c c', E.Th u μ w i c c' =
      atLin (adCoef (E.lam w) (Pm i c) (Pm (i + 1) c')) (fun j => MvPowerSeries.X j) (pSer D (E.lam w) ((O u μ).Th i c c'))

def DgenUnitAd (P : Examples₂.EntPl D) (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)) : Prop :=
  ∀ w : D.what₂.places.Pl, AdPl D w → ∀ u μ τ, ‖lamC (P.lam w) ((O u μ).dgen τ)‖ = 1

def KerEntTied.Adapted {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}
    {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) : Prop :=
  AdaptedTh t.ent t.O

end Formalism.L2.Ker

end
end
