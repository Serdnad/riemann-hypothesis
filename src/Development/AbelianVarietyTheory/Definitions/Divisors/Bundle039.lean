module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle201
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.ChartGlue GlobalTheory.HermFrame GlobalTheory.GoodMetric

namespace GlobalTheory.GoodTop

variable {n : ℕ} {r : Type} [Fintype r] [DecidableEq r]

abbrev EndValuedForm11Coeffs (n : ℕ) (r : Type) : Type := Fin n → Fin n → Matrix r r ℂ

def mixTop (K : Fin n → EndValuedForm11Coeffs n r) : ℂ :=
  (n.factorial : ℂ)⁻¹ * ∑ p : Fin n → r, ∑ π : Equiv.Perm (Fin n), ∑ u : Equiv.Perm (Fin n),
    ((Equiv.Perm.sign π : ℤ) : ℂ) * ((Equiv.Perm.sign u : ℤ) : ℂ) *
      (Matrix.of fun i b => K i (u i) b (p i) (p (π i))).det

def intersection_update_fsHerm_neg_one {α : Type} (K₁ L K₀ : α) (j : Fin n) : Fin n → α :=
  fun i => if i < j then K₁ else if i = j then L else K₀

def curvAt (G : V n → Matrix r r ℂ) (v : V n) : EndValuedForm11Coeffs n r :=
  fun a b => curv G v (coordVec a) (coordVec b)

def cutForm (ρ : V n → ℝ) (G₀ G₁ : V n → Matrix r r ℂ) (v : V n) : EndValuedForm11Coeffs n r :=
  fun a b => dbar (fun x => (ρ x : ℂ)) v (coordVec b) • (conn G₁ v (coordVec a) - conn G₀ v (coordVec a))

def corrC (ρ : V n → ℝ) (G₀ G₁ : V n → Matrix r r ℂ) (v : V n) : ℂ :=
  ∑ j : Fin n, mixTop (intersection_update_fsHerm_neg_one (curvAt G₁ v) (cutForm ρ G₀ G₁ v) (curvAt G₀ v) j)

def corrTop (ρ : V n → ℝ) (G₀ G₁ : V n → Matrix r r ℂ) (v : V n) : ℝ := (Real.pi ^ n)⁻¹ * (corrC ρ G₀ G₁ v).re

def offHyp (S : Finset (Fin n)) (U : Set (V n)) : Set (V n) := {v | v ∈ U ∧ ∀ a ∈ S, v a ≠ 0}

section Glue

variable {Y : Type} [TopologicalSpace Y] [MeasurableSpace Y] {κ : Type}

def HasInt (e : κ → OpenPartialHomeomorph Y (V n)) (d : κ → Y → ℝ) (S : Set Y) (t : ℝ) : Prop :=
  (∀ ε : ℤˣ, glueMeas e (fun i y => ENNReal.ofReal ((ε : ℤ) * d i y)) S ≠ ⊤) ∧
    (glueMeas e fun i y => ENNReal.ofReal (((1 : ℤˣ) : ℤ) * d i y)).real S -
      (glueMeas e fun i y => ENNReal.ofReal (((-1 : ℤˣ) : ℤ) * d i y)).real S = t

structure IsTopForm (e : κ → OpenPartialHomeomorph Y (V n)) (d : κ → Y → ℝ) (S : Set Y) : Prop where
  trans : ∀ i j y, y ∈ S → y ∈ (e i).source → y ∈ (e j).source → d i y = ‖transDet (e i) (e j) y‖ ^ 2 * d j y
  meas : ∀ i, AEMeasurable (fun v => d i ((e i).symm v)) (volume.restrict ((e i).target ∩ (e i).symm ⁻¹' S))

end Glue

section Var

open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle

variable {F : Type} [Field F] {X : Var F} {σ : F →+* ℂ} {m : ℕ}

def topDens (E : Fr (ratOf X) (fun _ : Unit => m) 0)
    (H : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ)
    (c : AlgChart X.str σ X.dim) (y : CxPts X.str σ) : ℝ :=
  chernTop (MvPolynomial.X ((), X.dim)) (fun v => H (E.nonempty (under y)).choose (c.e.symm v)) (c.e y)

def corrDens (E : Fr (ratOf X) (fun _ : Unit => m) 0)
    (H₀ H : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ) (ρ : CxPts X.str σ → ℝ)
    (c : AlgChart X.str σ X.dim) (y : CxPts X.str σ) : ℝ :=
  corrTop (fun v => ρ (c.e.symm v)) (fun v => H₀ (E.nonempty (under y)).choose (c.e.symm v) ())
    (fun v => H (E.nonempty (under y)).choose (c.e.symm v) ()) (c.e y)

structure GoodPatch (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens)
    (H : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ)
    (e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)) (S : Finset (Fin X.dim)) (A : Mat (fun _ : Unit => m) X.Fn)
    (W : Set (CxPts X.str σ)) (c : ℝ) : Prop where
  holo : IsHoloChart e
  isOpen : IsOpen W
  sub : W ⊆ e.source
  frame : ∀ z ∈ W, A ∈ E.S (under z)
  small : ∀ z ∈ W, ∀ a ∈ S, ‖e z a‖ ≤ 1 / 2
  mem : ∀ z ∈ W, z ∈ ptsIn X.str σ O ↔ ∀ a ∈ S, e z a ≠ 0
  form : ∀ z ∈ W, z ∈ ptsIn X.str σ O → ∀ a i j,
    ‖conn (fun v => H A (e.symm v) ()) (e z) (coordVec a) i j‖ * poinWt S (e z) a ≤ c
  dbar : ∀ z ∈ W, z ∈ ptsIn X.str σ O → ∀ a b i j,
    ‖curv (fun v => H A (e.symm v) ()) (e z) (coordVec a) (coordVec b) i j‖ * (poinWt S (e z) a * poinWt S (e z) b) ≤ c

theorem hasChernIntegral_iff (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens)
    (H : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ) (t : ℝ) :
    HasChernIntegral E O H (MvPolynomial.X ((), X.dim)) t ↔
      HasInt (fun c : AlgChart X.str σ X.dim => c.e) (topDens E H) (ptsIn X.str σ O) t := Iff.rfl

end Var

end GlobalTheory.GoodTop
end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace ContDiff Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDictModel

open GlobalTheory.HolDict

section Local

open ReciprocityTheory.ChartRestriction.G.FD

variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

end Local

section Adelic

variable {D : D7}

theorem fix_iff (τ : D.host.E →+* ℂ) :
    τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD ↔ ∃ ρ, τ = tauE D ρ := by
  obtain ⟨g, rfl⟩ := (factEmb D.R D.host).1.2 τ
  have h1 : D.host.galE (D.host.sigmaOf g) = g :=
    (D.host.gal).apply_symm_apply g
  refine Iff.trans ?_ (Formalism.L2.Geo.exists_tauEmb_iff D g).symm
  conv_rhs => rw [← h1]
  refine Iff.trans ?_ (D.host.galE_mem_Psi_iff _).symm
  exact ⟨fun h => D.host.φ₀.injective h, fun h => congrArg D.host.φ₀ h⟩

end Adelic

section Dict

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.Member

variable {D : D7}


end Dict

section Forms

variable {D : D7}


end Forms

end GlobalTheory.HolDictModel
end
end
