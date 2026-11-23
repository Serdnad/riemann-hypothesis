module

public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle004
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle003
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle042
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle014
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle034
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle098
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle003
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FrameNormRestrictedDensity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle001

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.adelicUnitary_action_at_real_place : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → (∀ (V : HSp D) (k : GA D V) (τ : D.what₂.Tau), infMat D.sp.cm.sig V.gram (θ τ) k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) ∧ ∀ (V W : HSp D) (k : GA D V) (k' : GA D W) (x : WA V W), (∀ τ, wAt θ V W τ (actHom V W k k' x) = actC V W (infMat D.sp.cm.sig V.gram (θ τ) k) (infMat D.sp.cm.sig W.gram (θ τ) k') (wAt θ V W τ x)) ∧ (IsRealW V W x → IsRealW V W (actHom V W k k' x)) := by
  first | exact @GlobalTheory.FockCompare.RealAction.real_action | exact GlobalTheory.FockCompare.RealAction.real_action | (intros; apply GlobalTheory.FockCompare.RealAction.real_action <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_real_point_unitary_with_components : ∀ (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), Chart θ σ → ∀ (V : HSp D) (g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ τ, g τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) → ∃ k ∈ GinfC V, ∀ τ, infMat D.sp.cm.sig V.gram (θ τ) k = g τ := by
  first | exact @GlobalTheory.FockCompare.LiftUnitary.lift_unitary | exact GlobalTheory.FockCompare.LiftUnitary.lift_unitary | (intros; apply GlobalTheory.FockCompare.LiftUnitary.lift_unitary <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LowerBoundCompare

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0 GlobalTheory.IndefiniteRowSideFullHecke.FrameNormRestrictedDensity

variable {D : D7} {T : Core D}

theorem conjEmb_invol {E : Type} [Field E] (τ : E →+* ℂ) : conjEmb (conjEmb τ) = τ := by
  ext x
  simp [conjEmb]

theorem wtA_conj_tau (Q : Par D) (hp : Q.PinHost) {j : ℕ} (w : WeightFamilies.Wt D j) (t : D.what₂.Tau) (i : ℕ) :
    wtA w (conjEmb (DV.tauEmb D t), i) = ext0 (w.aM t) i := by
  classical
  have h1 : ∀ t', conjEmb (DV.tauEmb D t) ≠ DV.tauEmb D t' := fun t' h =>
    GlobalTheory.LeafCompare.tauEmb_ne_conj Q hp t' t h.symm
  unfold wtA
  rw [Finset.sum_eq_single t]
  · simp [h1]
  · intro t' _ ht'
    have : conjEmb (DV.tauEmb D t) ≠ conjEmb (DV.tauEmb D t') := fun h =>
      ht' (GlobalTheory.LeafCompare.tauEmb_inj (by
        rw [← conjEmb_invol (DV.tauEmb D t'), ← h, conjEmb_invol]))
    simp [h1, this]
  · simp

theorem wt_ext (Q : Par D) (hp : Q.PinHost) {j : ℕ} {w w' : WeightFamilies.Wt D j} (hA : wtA w = wtA w') (hn : w.n = w'.n) :
    w = w' := by
  have hP : w.aP = w'.aP := by
    funext t i
    have := congrFun hA (DV.tauEmb D t, i.1)
    rw [GlobalTheory.LeafCompare.wtA_tau Q hp, GlobalTheory.LeafCompare.wtA_tau Q hp] at this
    simpa [ext0, i.2] using this
  have hM : w.aM = w'.aM := by
    funext t i
    have := congrFun hA (conjEmb (DV.tauEmb D t), i.1)
    rw [wtA_conj_tau Q hp, wtA_conj_tau Q hp] at this
    simpa [ext0, i.2] using this
  cases w
  cases w'
  simp only at hP hM hn
  subst hP hM hn
  rfl

theorem wtA_wsmul_apply {j : ℕ} (k : ℕ) (w : WeightFamilies.Wt D j) (x : (D.host.E →+* ℂ) × ℕ) :
    wtA (WeightAlgebra.wsmul k w) x = k * wtA w x := by
  have h0 : ∀ {p : ℕ} (f : Fin p → ℕ) (i : ℕ), ext0 (fun s => k * f s) i = k * ext0 f i := by
    intro p f i
    unfold ext0
    split_ifs <;> simp
  simp only [wtA, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  have h1 : ext0 ((WeightAlgebra.wsmul k w).aP t) x.2 = k * ext0 (w.aP t) x.2 := h0 _ _
  have h2 : ext0 ((WeightAlgebra.wsmul k w).aM t) x.2 = k * ext0 (w.aM t) x.2 := h0 _ _
  rw [h1, h2]
  split_ifs <;> simp [mul_add]

theorem eq_wsmul_iff (h : LawsCore T) {j : ℕ} (ka wL : WeightFamilies.Wt D j) (n : ℕ) :
    wtZ (wtA ka) ka.n = n • wtZ (wtA wL) wL.n ↔ ka = WeightAlgebra.wsmul n wL := by
  constructor
  · intro H
    refine wt_ext T.Q h.pins.1 (funext fun x => ?_) ?_
    · have : (wtA ka x : ℤ) = n • (wtA wL x : ℤ) := congrFun (congrArg Prod.fst H) x
      rw [nsmul_eq_mul] at this
      rw [wtA_wsmul_apply]
      exact_mod_cast this
    · have : (ka.n : ℤ) = n • (wL.n : ℤ) := congrArg Prod.snd H
      rw [nsmul_eq_mul] at this
      show ka.n = n * wL.n
      exact_mod_cast this
  · rintro rfl
    refine Prod.ext (funext fun x => ?_) ?_
    · simp only [wtZ, Prod.smul_fst, Pi.smul_apply, nsmul_eq_mul, wtA_wsmul_apply]
      push_cast
      rfl
    · simp only [wtZ, Prod.smul_snd, nsmul_eq_mul]
      show ((n * wL.n : ℕ) : ℤ) = _
      push_cast
      rfl

section Density

variable (h : LawsCore T) (j : ℕ) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (fn : FrameNorms T j) (yP : GenericFrames T j)
  (ka : WeightFamilies.Wt D j)

end Density

section Separate

variable {j : ℕ}

end Separate

end GlobalTheory.LowerBoundCompare
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct

namespace GlobalTheory.SmoothForms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def BddDen (V : HSp D) (d : ℕ) (g : GA D V) : Prop :=
  ∀ i j, d • finMat D.sp.cm.sig V.gram g i j ∈ intAE D ∧ d • finMat D.sp.cm.sig V.gram g⁻¹ i j ∈ intAE D

def DenomBound (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) : Prop :=
  ∃ (C : ℝ) (M : ℕ), ∀ g : GA D V, ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ C * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V g : ℝ) ^ M ∧
    ∀ i : Fin V.rank, (Pi.single i (d : D.host.E) : Fin V.rank → D.host.E) ∈ Formalism.L2.Pj.latG V g

def RealPoints (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) : Prop :=
  (∀ τ, (gramAt D V τ)ᴴ = gramAt D V τ ∧ IsUnit (gramAt D V τ).det) ∧
  (∀ u : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, u τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) →
    ∃ g ∈ GinfC V, ∀ τ, infMat D.sp.cm.sig V.gram (θ τ) g = u τ) ∧
  (∀ g ∈ GinfC V, ∀ g' ∈ GinfC V,
    (∀ τ, infMat D.sp.cm.sig V.gram (θ τ) g = infMat D.sp.cm.sig V.gram (θ τ) g') → g = g') ∧
  (∀ g g' τ, infMat D.sp.cm.sig V.gram (θ τ) (g * g') =
    infMat D.sp.cm.sig V.gram (θ τ) g * infMat D.sp.cm.sig V.gram (θ τ) g') ∧
  (∀ k ∈ GfC V, ∀ τ, infMat D.sp.cm.sig V.gram (θ τ) k = 1) ∧
  (∀ a ∈ GinfC V, ∀ k ∈ GfC V, a * k = k * a) ∧
  (∀ g : GA D V, ∃ k ∈ GfC V, ∃ a ∈ GinfC V, g = k * a) ∧
  ∀ (g : GA D V), ∀ a ∈ GinfC V, finMat D.sp.cm.sig V.gram (g * a) = finMat D.sp.cm.sig V.gram g

end GlobalTheory.SmoothForms

end
end
