module

public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.Bundle001
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

section

noncomputable section

namespace GlobalTheory.TwU

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

def XiTop {u : Pr.Word} (m2 : ℕ) (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1))))
    (d : DecoSet (E := X.E) (n := R.N R.m) (ST := Pr.vT u) (SG := rowSG Pr sel mu)) (fr : Frs X.E (R.N R.m) (rowSG Pr sel mu))
    (x : HomE X.E (R.N (m2 + 1)) (R.N R.m)) : X.K :=
  phiT X.K p.deco.1 d.1 x *
    ∏ P : rowSG Pr sel mu,
      PhiTop Ch mu cst.sharp m2 P.1 (prXp X.E R ∘ₗ (fr P).symm.toLinearMap ∘ₗ x ∘ₗ (frsF sel mu p P).toLinearMap ∘ₗ
          LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) *
        ftY sel mu cst P (atNL X.E (R.N R.m) (R.N R.m - 1) ∘ₗ (fr P).symm.toLinearMap ∘ₗ x ∘ₗ (frsF sel mu p P).toLinearMap)
          ((frsF sel mu p P).symm (repY Y))

end GlobalTheory.TwU

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual beMean)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog lgN)

namespace GlobalTheory.KerStd

def BeData (l d : ℕ) [Fact l.Prime] [NeZero d] (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (F be0 : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l))
    (om oms : Fin (d / 2) → MaximalUnramifiedExtension l) (ζ : MaximalUnramifiedExtension l) : Prop :=
  UnrOK (MaximalUnramifiedExtension l) l σ ∧ IsLawOfLog l F ∧ F1 F be0 ∧ F2 l σ be0 ∧ OwOK d σ om oms ∧ TrDual d σ om oms ∧
    IsPrimitiveRoot ζ (l ^ d - 1)

def beOf (l d : ℕ) [Fact l.Prime] [NeZero d] (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (be0 : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l))
    (om oms : Fin (d / 2) → MaximalUnramifiedExtension l) (ζ : MaximalUnramifiedExtension l) : MvPowerSeries (ZMod d) ℂ_[l] :=
  MvPowerSeries.map (MaximalUnramifiedExtension l).subtype (beMean (d := d) l σ be0 om oms ζ)

def BeStd (l d : ℕ) [Fact l.Prime] [NeZero d] (be : MvPowerSeries (ZMod d) ℂ_[l]) : Prop :=
  ∃ (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (F be0 : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l)) (om oms : Fin (d / 2) → MaximalUnramifiedExtension l) (ζ : MaximalUnramifiedExtension l),
    BeData l d σ F be0 om oms ζ ∧ be = beOf l d σ be0 om oms ζ

def BeFam (D : D7) (ep : ∀ w : D.what₂.places.Pl, ℂ_[D.what₂.places.resChar w])
    (be : ∀ w : D.what₂.places.Pl, OrbitPlaces.Pl D →
      MvPowerSeries (ZMod (nP D (D.what₂.places.resChar w))) ℂ_[D.what₂.places.resChar w]) : Prop :=
  ∀ w : D.what₂.places.Pl,
    ((IsResidueClassZero D (D.what₂.places.resChar w) ∧ HEv D (D.what₂.places.resChar w)) ∨ IsSg D (D.what₂.places.resChar w)) →
    ‖ep w‖ = 1 ∧ ∀ r, BeStd (D.what₂.places.resChar w) (nP D (D.what₂.places.resChar w)) (be w r)

def linEv (D : D7) (p : ℕ) [Fact p.Prime] {N0 N1 : ℕ} (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (c : MaximalUnramifiedExtension p) (r : OrbitPlaces.Pl D) (a : Fin N0) (b : Fin N1) :
    MvPowerSeries (OrbitPlaces.Pl D × Fin N0 × Fin N1) ℂ_[p] :=
  ∑ s : ZMod (nP D p), if s.val % 2 = 0 then
    MvPowerSeries.C ((σ^[s.val] c : MaximalUnramifiedExtension p) : ℂ_[p]) * MvPowerSeries.X (OrbitPlaces.orbMap D p r s, a, b) else 0

def linOd (D : D7) (p : ℕ) [Fact p.Prime] {N0 N1 : ℕ} (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (c : MaximalUnramifiedExtension p) (r : OrbitPlaces.Pl D) (a : Fin N0) (b : Fin N1) :
    MvPowerSeries (OrbitPlaces.Pl D × Fin N0 × Fin N1) ℂ_[p] :=
  ∑ s : ZMod (nP D p), if s.val % 2 = 0 then 0 else
    MvPowerSeries.C ((σ^[s.val] c : MaximalUnramifiedExtension p) : ℂ_[p]) * MvPowerSeries.X (OrbitPlaces.orbMap D p r s, a, b)

def hypZ (D : D7) (p : ℕ) [Fact p.Prime] {N0 N1 : ℕ} (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p)
    (R : Finset (OrbitPlaces.Pl D)) {n : Type} (f f' : (R × Fin (nP D p / 2)) × Fin N0 × Fin N1 → n → MaximalUnramifiedExtension p) (i : n) :
    MvPowerSeries (OrbitPlaces.Pl D × Fin N0 × Fin N1) ℂ_[p] :=
  ∑ e : (R × Fin (nP D p / 2)) × Fin N0 × Fin N1,
    (MvPowerSeries.C (f e i : ℂ_[p]) * linEv D p σ (oms e.1.2) e.1.1 e.2.1 e.2.2 +
      MvPowerSeries.C (f' e i : ℂ_[p]) * linOd D p σ (om e.1.2) e.1.1 e.2.1 e.2.2)

def alLoc (Lc : product_zeroth_first_parts.Loc) (s : ZMod Lc.d) : ℕ := if s ∈ Lc.TT then (Lc.nu s).rowLen 0 - (Lc.nu s).rowLen 1 else 0

def gainA (Lc : product_zeroth_first_parts.Loc) : ℝ :=
  (∑ s ∈ Lc.TT, ∑' e : ℕ,
    if Odd e ∧ ¬ (e < Lc.d ∧ s + (e : ZMod Lc.d) ∈ Lc.TT) then
      max ((alLoc Lc s : ℝ) / (Lc.l : ℝ) ^ e - (Lc.cap (s + (e : ZMod Lc.d)) : ℝ)) 0 else 0) -
  ((∑ s : ZMod Lc.d, ((Lc.N1 : ℝ) * lgN Lc.l (alLoc Lc s) + (Lc.N0 : ℝ) * Lc.N1 * lgN Lc.l (Lc.size s - alLoc Lc s))) +
    ∑ s ∈ Lc.TT, ((lgN Lc.l (alLoc Lc s) : ℝ)) ^ 2)

end GlobalTheory.KerStd
end
end
