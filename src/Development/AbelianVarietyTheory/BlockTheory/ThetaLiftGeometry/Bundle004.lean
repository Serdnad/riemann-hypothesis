module

public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
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

@[expose] public section

section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.AmbientLatticeAvoidance

def reix (E : Type) [Field E] (n n' : ℕ) : Sp E n →ₗ[E] Sp E n' := LinearMap.pi fun l : Fin n' => atNL E n l.1

section Concrete

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

abbrev rkTop (R : Ranks) : ℕ := (R.N R.m - 1) + 0



open Classical in
def lamTop (sharp : Bool) (P : HeightOneSpectrum (𝓞 X.E)) (h : HomE X.E (rkTop R) (rkTop R)) : X.K :=
  if P ∈ Pr.vGs then
    (if sharp then LocE.lamGBS (qOf P) (psi0P Ch P) (chiP Ch P) R.k R.r R.t R.m (R.N R.m - 1) 0 h
      else LocE.lamGB (qOf P) (psi0P Ch P) (chiP Ch P) R.k R.r R.t R.m (R.N R.m - 1) 0 h)
  else LocE.lamQB (resChar (mu : Chr X.F X.E X.K) P) R.r (R.N R.m - 1) h



abbrev Pt (u : Pr.Word) (i : ℕ) : Type := ChPt (R := R) sel mu u i × Option (L.β i) × Set (Sp X.E (R.N i))

variable (abelian₂ : HeightOneSpectrum (𝓞 X.E) → Submodule (𝓞 X.E) (Sp X.E (rkTop R))) (dep : HeightOneSpectrum (𝓞 X.E) → ℕ)

end Concrete

section Global

variable {D : D7} {X : Fields} (s : Seam D X)

def ambE (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (e : TaylorLogMetric.FamE D) (dgen : D.what₂.Tau → ℂ) : Amb X where
  σ₀ := s.σ₀
  δ := δ
  d := D.host.d
  sc := (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹
  AA := Submodule.span (𝓞 X.E)
    {r | ∃ c ∈ cc, ∃ t ∈ D.host.AA0, r = s.iE.symm ((((c : 𝓞 D.host.K) : D.host.K) : D.host.E) * t)}
  cD τ := dgen (s.iT τ)
  e a b N N' z := e a b (s.lat N) (s.lat N') fun τ => z (s.iT.symm τ)
  chiF a b N N' := Base.chiFac χ a b (s.lat N) (s.lat N')


end Global

section Chain

variable {D : D7} {X : Fields} (s : Seam D X) {Pr : Primes X} (Ch : Chars X Pr D.R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr D.R (QE sel (mu : Chr X.F X.E X.K)))
  (abelian₂ : HeightOneSpectrum (𝓞 X.E) → Submodule (𝓞 X.E) (Sp X.E (rkTop D.R))) (dep : HeightOneSpectrum (𝓞 X.E) → ℕ)
  {u : D.what₂.Word} (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (v : Pr.Word)
  (rep : ∀ i, C.cls i → Pt sel mu L v i)
  (frm : ∀ i, C.Y i → D.what₂.Tau → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) ℂ)

end Chain

end GlobalTheory.IndefiniteRowSideFullHecke.AmbientLatticeAvoidance
end
end

section

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.WeightedChainData

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker

section Frames

variable (D : D7) {N : ℕ} {Y : Type} (frm : Y → D.what₂.Tau → Matrix (Fin N) (Fin N) ℂ)

end Frames

structure ChainData (D : D7) (u : D.what₂.Word) (μ : D.what₂.Tup) where
  X : Fields
  s : Seam D X
  Pr : Primes X

  w : Pr.Word
  Ch : Chars X Pr D.R.m

  sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)
  S : Set ℕ

  xi : Tup X.F X.E X.K S
  cst : LocCst X (rowSG Pr sel xi)
  L : ChIdx X Pr D.R (QE sel (xi : Chr X.F X.E X.K))
  G : ChGlob X D.R.m
  δ : ℂ
  B : Base D D.host.ccK δ
  idl : D.Dt ⧸ D.UO → TaylorLogMetric.IdE D
  O : GL3Theta.LiftObj D (D.chTw u μ)

  lamTop : rowSG Pr sel xi → Submodule (𝓞 X.E) (Sp X.E (D.R.N D.R.m - 1 + 0))

  depth : rowSG Pr sel xi → ℕ

  rep : ∀ i, (D.chTw u μ).cls i →
    Option (L.β i) × DecoF X.E (D.R.N i) (Pr.vT w) ∅ (rowSG Pr sel xi) × Set (Sp X.E (D.R.N i))

namespace ChainData

variable {D : D7} {u : D.what₂.Word} {μ : D.what₂.Tup} (T : ChainData D u μ)





end ChainData

end GlobalTheory.IndefiniteRowSideFullHecke.WeightedChainData
end
end

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ColumnAvoidanceConditions

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV

@[reducible] def fieldsOf (D : D7) : Fields where
  F := D.host.F
  E := D.host.E
  K := D.what₂.LL
  starE := D.host.cmStar
  Tau := D.what₂.Tau
  deTau := Classical.decEq _
  emb τ := D.embE.comp (D.host.sigmaOf (D.eTau τ : D.R.GG) : D.host.E →+* D.host.E)

@[reducible] def primesOf (D : D7) (EX : ErrX D) : Primes (fieldsOf D) where
  cond := D.host.QS * D.host.q * D.host.d
  g := D.host.g
  piG := EX.piG
  Word := D.what₂.Word
  ftWord := D.wordFin
  deWord := Classical.decEq _
  T u := (D.mem u).A.T
  piT := EX.piT

def seamOf (D : D7) : Seam D (fieldsOf D) where
  iE := RingEquiv.refl _
  iT := Equiv.refl _
  σ₀ := D.what₂.embLL

section Ties

variable (D : D7) (Dx : DivX D) (EX : ErrX D) (Ch : Chars (fieldsOf D) (primesOf D EX) D.R.m)
  (m0 : Fin D.R.m → Formalism.L2.Host.HChar D.host.E)
  (sel : HeightOneSpectrum (𝓞 (fieldsOf D).F) → HeightOneSpectrum (𝓞 (fieldsOf D).E))

variable {S : Set ℕ} (ξ : Tup (fieldsOf D).F (fieldsOf D).E (fieldsOf D).K S)

end Ties

def Bound (D : D7) (L : SizeData₂ D) (EX : ErrX D) (C1 : ℝ) (i : Fin 2) (w : LiftErrorLocal.Pl D) (u : D.what₂.Word) (μ : D.what₂.Tup) : Prop :=
  ∀ φ ∈ DV.MramL D u, ∀ F ∈ (D.what₂.Mtilde μ).carrier,
    ∃ y : D.what₂.LL, D.what₂.embLL y = D.what₂.perCol u μ (D.jN u φ) F ∧
      (y = 0 ∨ -(∑ j ∈ LiftErrorLocal.lifts D, vNN EX i u j w) - C1 * LiftErrorLocal.errC D L ≤ LiftErrorLocal.vG D w y)

end GlobalTheory.IndefiniteRowSideFullHecke.ColumnAvoidanceConditions

end
end
