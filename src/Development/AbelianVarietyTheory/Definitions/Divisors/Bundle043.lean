module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AbsPowOneNotIsAlgRat
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle026
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec
open scoped TensorProduct

namespace GlobalTheory.ResW

def blkE {r s N : ℕ} (h : r + s = N) : Fin r ⊕ Fin s ≃ Fin N := finSumFinEquiv.trans (finCongr h)

def blkM (R : Type) [CommRing R] {r s N : ℕ} (h : r + s = N) :
    Matrix (Fin r) (Fin r) R × Matrix (Fin s) (Fin s) R →* Matrix (Fin N) (Fin N) R where
  toFun p := Matrix.reindex (blkE h) (blkE h) (Matrix.fromBlocks p.1 0 0 p.2)
  map_one' := by simp [Matrix.fromBlocks_one]
  map_mul' p q := by
    simp only [Prod.fst_mul, Prod.snd_mul, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp

def blk {R : Type} [CommRing R] {r s N : ℕ} (h : r + s = N) : GL (Fin r) R × GL (Fin s) R →* GL (Fin N) R :=
  (Units.map (blkM R h)).comp MulEquiv.prodUnits.symm.toMonoidHom

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N r s m a : ℕ}


variable (E) in
def nu (t : ℝ) : HChar E := GlobalTheory.HeckeGal.Model.absPow E t





section Passive

variable {M : Type} [AddCommGroup M] [Module ℂ M]

end Passive


variable (E) in
abbrev Letter : Type := Σ a : ℕ, CuspSub E a

def wsize (u : List (Letter E)) : ℕ := (u.map (·.1)).sum

noncomputable def Vec : List (Letter E) → Type
  | [] => PUnit
  | x :: u => x.2.V × Vec u


variable (E N) in
def zc : Module.End ℂ (Sm E N) := lie E N fun i j => if i = j then 1 else 0

def cex (x : Letter E) : ℂ := Classical.epsilon fun c : ℂ => ∀ φ ∈ x.2.V, zc E x.1 φ = c • φ

def rexp (x : Letter E) : ℝ := (cex x).re / (x.1 * Module.finrank ℚ E)

def tw (x : Letter E) (t : ℝ) : Letter E := ⟨x.1, x.2.twist (nu E t)⟩

def SatVec (φ : Sm E N) (B : HeightOneSpectrum (𝓞 E) → Multiset ℂˣ) : Prop :=
  ∀ᶠ v in Filter.cofinite, GlobalTheory.LFun.IsSatVecGL v ((finRep E N).comp (locGL E N v)) φ (B v)

def SatFam (V : Submodule ℂ (Sm E N)) (B : HeightOneSpectrum (𝓞 E) → Multiset ℂˣ) : Prop := ∀ φ ∈ V, φ ≠ 0 → SatVec φ B


end GlobalTheory.ResW

end
end

section

open NumberField Matrix IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
  Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT GlobalTheory.WeilParts
open scoped TensorProduct Classical

namespace GlobalTheory.AdTh

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

structure IsPair (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle)
    (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) : Prop where
  weil : IsWeilDatumO ψ V W χV χW om
  inf : IsInfFam θ
  std : V.gram = 1
  even : Even V.rank
  sigV : V.SigOK
  sigW : W.SigOK
  expV : ∀ τ, ∃ a : ℤ, HasInfExp D χV τ a
  expW : ∀ τ, ∃ b : ℤ, HasInfExp D χW τ ((b : ℚ) + (W.rank : ℚ) / 2)
  unr : ∀ v ε, NonSplitAt D v ε → UnramAt ε χV ∧ UnramAt ε χW
  eta : ∃ η, IsEtaTilde D η

def MarkAd {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} (l : Level H) (W : HSp D) {r : ℕ} (hr : W.rank = r)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) (h : GA D W) (mk : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)) : Prop :=
  ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 D.host.E) Dw.La), ∃ w ∈ latGHat W h,
    finVec W (mk a ∘ Fin.cast hr) - (finHom W h).1.mulVec (finVec W (ι a)) = (l.M : ℕ) • w

def hatC {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} (l : Level H)
    {n : ℕ} (φ : (Fin n → LevQc Dw l) → ℂ) (q : Fin n → LevQ Dw l) : ℂ :=
  ∑ᶠ x : Fin n → LevQc Dw l, φ x * Complex.exp (2 * Real.pi * Complex.I / (l.M : ℂ)) ^
    pairL (l := l) (fun b => qRep (x b)) (fun b => levRep (q b))

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}

def SerOf (O : OMDat C R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : (R.MW i (sg0 D A)).Vec)
    (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ) (ph : ℂ) : Prop :=
  (∀ k, ‖cc k‖ = 1) ∧ ‖ph‖ = 1 ∧
    ∀ (t : Tp) (h : O.Cl' t → GA D (Vc D i)) (J' : Subgroup (Bridge.Gf (Vc D i))),
      RepsR R i (tup t) h (O.bad t) J' (O.Lh t) (O.gam t) (O.vol t) →
      ∀ (y : (R.HV i (tup t)).H) (x : O.Cl' t → VsV D i O.c'.F), Place R i (tup t) h O.c0' y x →
      ∀ f ∈ sec (C.Q.Xo ((i : ℕ) + 1)) O.c' (wtA κ) (Vc D i).rank,
        IsThClsD (C.Q.Xo ((i : ℕ) + 1)) O.c' (O.dδ t) (O.w t) (O.La t) (O.Nc t) (O.gam t) (O.vol t) (O.ep t) O.io x f →
        ∀ g : GA D (Wc D i), ph * R.thF i (tup t) y v₀ g =
          cc (O.dict g).1 * (lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * O.mu g *
            rdU (unfBC O.hle (C.U ((i : ℕ) + 1)) (inC O.c')) f (O.dict g).1 (O.dict g).2

end

end GlobalTheory.AdTh
end
