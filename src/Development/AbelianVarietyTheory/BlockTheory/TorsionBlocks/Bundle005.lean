module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
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

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary

section Param

variable {R : Ranks}

def run (P : HCParam R) (j : Fin R.m) : Multiset ℚ :=
  (Multiset.range R.t).map fun k : ℕ => -P.e j + ((R.t : ℚ) + 1) / 2 - ((k : ℚ) + 1)

def param (P : HCParam R) (j : Fin R.m) : Multiset ℚ :=
  (Finset.univ : Finset (Fin (R.k - 1))).val.map P.v +
    (Finset.univ : Finset (Fin R.m)).val.map (fun i => -P.b i) + run P j

def sgnOf (ep b : Bool) : ℚ := if ep = b then 1 else -1

end Param

variable (D : D7)

def liftIdx (i : D.nd.Loc) : Fin D.R.m :=
  ⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩

def embOver (ρ : D.what₂.Tau) (b : Bool) : D.host.E →+* ℂ :=
  if b then
    (D.host.emb ((D.eTau ρ : D.R.Psi) : D.R.GG)).comp (D.host.conj : D.host.E →+* D.host.E)
  else D.host.emb ((D.eTau ρ : D.R.Psi) : D.R.GG)

def PP (i : D.nd.Loc) (ρ : D.what₂.Tau) : Multiset ℚ := param (D.hc ρ) (liftIdx D i)

section Local

variable (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

end Local

def chiGL (i : D.nd.Loc) (c : ℕ) : GE D.nd →* GL (Fin 1) (D.nd.O i) :=
  (Units.map (Matrix.scalar (Fin 1) : D.nd.O i →+* Matrix (Fin 1) (Fin 1) (D.nd.O i)).toMonoidHom).comp
    (D.nd.chi i c)

def WeightParam : Prop :=
  ∀ (i : D.nd.Loc) (ρ : D.what₂.Tau),
    D.naut.infWt i (embOver D ρ false) = (PP D i ρ).map (fun p => ((p - 1 / 2 : ℚ) : ℂ)) ∧
    D.naut.infWt i (embOver D ρ true) = (PP D i ρ).map (fun p => ((-(p - 1 / 2) : ℚ) : ℂ))

def BlockCharParam : Prop :=
  ∀ (i : D.nd.Loc) (ρ : D.what₂.Tau),
    D.naut.infG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) (embOver D ρ false) =
      {((-(D.hc ρ).e (liftIdx D i) - 1 / 2 : ℚ) : ℂ)} ∧
    D.naut.infG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) (embOver D ρ true) =
      {(((D.hc ρ).e (liftIdx D i) + 1 / 2 : ℚ) : ℂ)}

end GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary

end
end

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TwistedTriples

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

variable (D : D7)

abbrev Trip (a : D.nd.Loc) : Type := D.ntw.Sig (D.ntw.twOf a)

def rhoTrip (a : D.nd.Loc) (s : Trip D a) : GE D.nd →* GL (Fin D.R.r) (D.nd.O a) :=
  mapRep (D.ntw.twist₂ a) (D.ntw.rhoS (D.ntw.twOf a) s)

def chiTrip (a : D.nd.Loc) (s : Trip D a) : GE D.nd →* (D.nd.O a)ˣ :=
  (Units.map (D.ntw.twist₂ a).toMonoidHom).comp
    (D.ntw.chi1 (D.ntw.twOf a) (D.ntw.jS (D.ntw.twOf a) s) (D.ntw.side (D.ntw.twOf a) s))

def tTrip (a : D.nd.Loc) (s : Trip D a) : GE D.nd →* Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O a) :=
  twistM ((Units.coeHom _).comp (rhoTrip D a s)) (chiTrip D a s)⁻¹

def badS (a : D.nd.Loc) : Set (HeightOneSpectrum (𝓞 D.host.E)) :=
  {v | ((∃ k, v ∈ placesOver D.host.E (D.host.g k)) ∨ v ∈ D.ntw.pD (D.ntw.twOf a)) ∧
    v ∉ placesOver D.host.E (D.nd.l a)}

def selT (a : D.nd.Loc) (s : Trip D a) (ψ : GE D.nd →* (D.nd.O a)ˣ) :
    Submodule (D.nd.O a) (H1 (WKG (twistM (tTrip D a s) ψ⁻¹))) :=
  Br.selG D.nd.plOm (D.nd.l a) (D.loc (D.nd.l a)) (D.nbr a) (badS D a ∪ ↑(D.nd.Q a))
    (twistM (tTrip D a s) ψ⁻¹)

def IsGoodRow (a : D.nd.Loc) (σ : D.what₂.FT) : Prop :=
  D.what₂.isot (D.nd.j a) σ ≠ ⊥ ∧ D.nd.goodRow σ

def IsRhoOfRow (a : D.nd.Loc) (σ : D.what₂.FT) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O a)) : Prop :=
  IsSSRep (mapRep (algebraMap (D.nd.O a) (Kf D.nd a)) ρ) ∧
  ∀ᶠ w in Filter.cofinite, IsSplitPl D.host w →
    ∀ (B : ValuationSubring D.nd.Om) (g : GE D.nd), IsPlaceOver (F := D.host.E) B w →
      IsFrob (F := D.host.E) B (normV w) g →
      ((ρ g : GL (Fin D.R.r) (D.nd.O a)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O a)).charpoly.map
          (iotaO D.nd D.naut a) =
        galPol D.naut (D.naut.lpTw (D.naut.lpChar (D.naut.locW a σ w) (D.naut.locG D.naut.etaTinv w))
          ((1 - (D.R.nV : ℝ)) / 2))

def IsTripleOf (a : D.nd.Loc) (σ : D.what₂.FT) (s : Trip D a) : Prop :=
  D.ntw.jS (D.ntw.twOf a) s = D.nd.j a ∧ D.ntw.side (D.ntw.twOf a) s = D.ntw.twSide a ∧
    IsRhoOfRow D a σ (rhoTrip D a s)

def TripAll : Prop :=
  ∀ (a : D.nd.Loc) (σ : D.what₂.FT), IsGoodRow D a σ → ∃ s : Trip D a, IsTripleOf D a σ s

def ind2 (l : ℕ) : ℚ := if l = 2 then 1 else 0

def epsL (l : ℕ) : ℚ := ((l : ℚ) ^ 2)⁻¹

theorem badS_eq (a : D.nd.Loc) : badS D a = ↑(D.nd.S a) := by
  ext v
  have h := D.ntw.pD_eq (D.ntw.twOf a)
  rw [D.ntw.twOf_l a] at h
  have h' : v ∈ D.ntw.pD (D.ntw.twOf a) ↔
      v ∈ placesOver D.host.E (if D.nd.l a = D.host.pde then D.host.pde' else D.host.pde) := by
    rw [← h]; rfl
  simp only [badS, Set.mem_setOf_eq, Finset.mem_coe, D.nd.S_def, h', Fin.exists_fin_two, or_assoc]

end GlobalTheory.IndefiniteRowSideFullHecke.TwistedTriples

end
end
