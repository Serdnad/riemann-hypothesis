module

public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle004
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle003
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.WeilIdempotents
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CoordDnApply
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle035
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle036
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.frame_basis_matrix_orthogonal_properties : ∀ (D : D7) (V : HSp D), (∀ Q : Matrix (Fin V.rank) (Fin V.rank) D.host.E, IsUnit Q.det → ∃ b : Module.Basis (Fin V.rank) D.host.E V.V, Q = V.frame.toMatrix b) ∧ ∀ b : Module.Basis (Fin V.rank) D.host.E V.V, IsUnit (V.frame.toMatrix b).det ∧ (∀ i j, (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (V.frame.toMatrix b) * V.gram * V.frame.toMatrix b) i j = V.hT (b i) (b j)) ∧ ((∀ i j, i ≠ j → V.hT (b i) (b j) = 0) → ∀ τ : D.what₂.Tau, (∀ i, (tauE D τ (V.hT (b i) (b i))).re ≠ 0) ∧ ((V.frame.toMatrix b).map (tauE D τ))ᴴ * gramAt D V τ * (V.frame.toMatrix b).map (tauE D τ) = Matrix.diagonal (fun i => (((tauE D τ (V.hT (b i) (b i))).re : ℝ) : ℂ)) ∧ ∀ s : Module.End D.host.E V.V, (∀ i, s (b i) = if 0 < (tauE D τ (V.hT (b i) (b i))).re then b i else -b i) → thAt V τ s * (V.frame.toMatrix b).map (tauE D τ) = (V.frame.toMatrix b).map (tauE D τ) * Matrix.diagonal (fun i => if 0 < (tauE D τ (V.hT (b i) (b i))).re then (1 : ℂ) else -1)) := by
  first | exact @GlobalTheory.FockBasisMatrix.basis_matrix | exact GlobalTheory.FockBasisMatrix.basis_matrix | (intros; apply GlobalTheory.FockBasisMatrix.basis_matrix <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.symplectic_val_tau_compat : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V W : HSp D) (τ : D.what₂.Tau) (x y : WA V W), valTau θ τ (sympl V W x y) = symplC V W τ (wAt θ V W τ x) (wAt θ V W τ y) := by
  first | exact @GlobalTheory.FockCompare.SymplVal.valTau_sympl | exact GlobalTheory.FockCompare.SymplVal.valTau_sympl | (intros; apply GlobalTheory.FockCompare.SymplVal.valTau_sympl <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

namespace GlobalTheory.DualPairCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

open GlobalTheory.IndefiniteRowSideFullHecke

section Gen
variable {M N : Type} [AddCommGroup M] [TopologicalSpace M] [AddCommGroup N] [TopologicalSpace N]

def SmoothAlong (Z : M → Prop) (f : M → ℂ) : Prop :=
  ∀ (k : ℕ) (L : (Fin k → ℝ) →+ M), Continuous L → (∀ t, Z (L t)) → ∀ w, ContDiff ℝ ∞ fun t => f (w + L t)

theorem gen_smooth_iff {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] (Z : M → Prop)
    (r : P →+ M) (hr : Continuous r) (hZ : ∀ p, Z (r p)) (co : M →+ P) (hc : Continuous co)
    (h3 : ∀ z, Z z → r (co z) = z) (f : M → ℂ) :
    SmoothAlong Z f ↔ ∀ w, ContDiff ℝ ∞ fun p => f (w + r p) := by
  constructor
  · intro h w
    let e : P ≃L[ℝ] (Fin (Module.finrank ℝ P) → ℝ) := ContinuousLinearEquiv.ofFinrankEq (by simp)
    have := (h _ (r.comp e.symm.toLinearEquiv.toLinearMap.toAddMonoidHom) (hr.comp e.symm.continuous)
      (fun t => hZ _) w).comp e.contDiff
    convert this using 2 with p
    exact congrArg (fun q => f (w + r q)) (e.symm_apply_apply p).symm
  · intro h k L hL h0 w
    have := (h w).comp ((co.comp L).toRealLinearMap (hc.comp hL)).contDiff
    convert this using 2 with t
    exact congrArg (fun q => f (w + q)) (h3 _ (h0 t)).symm


end Gen

def realMat (D : D7) (m n : ℕ) :
    (Fin m → Fin n → (InfinitePlace D.host.F → ℝ) × (InfinitePlace D.host.F → ℝ)) →+ Matrix (Fin m) (Fin n) (AE D) :=
  AddMonoidHom.mk' (fun p => Matrix.of fun i j => HeisenbergWeilMatrices.realPt D (p i j)) fun p q =>
    Matrix.ext fun i j => (realPtHom D).map_add (p i j) (q i j)

theorem continuous_realMat (D : D7) (m n : ℕ) : Continuous (realMat D m n) :=
  continuous_pi fun i => continuous_pi fun j =>
    (continuous_realPt D).comp ((continuous_apply j).comp (continuous_apply i))

theorem exists_coMat (D : D7) (m n : ℕ) : ∃ co : Matrix (Fin m) (Fin n) (AE D) →+
    (Fin m → Fin n → (InfinitePlace D.host.F → ℝ) × (InfinitePlace D.host.F → ℝ)), Continuous co ∧
    (∀ z, (z - realMat D m n (co z)).map (infPart D) = 0) ∧ ∀ z, z.map (finPart D) = 0 → realMat D m n (co z) = z := by
  obtain ⟨co, h1, h2, h3⟩ := exists_co D
  exact ⟨AddMonoidHom.mk' (fun z i j => co (z i j)) fun z w => funext₂ fun i j => co.map_add _ _,
    continuous_pi fun i => continuous_pi fun j => h1.comp ((continuous_apply j).comp (continuous_apply i)),
    fun z => Matrix.ext fun i j => h2 (z i j),
    fun z hz => Matrix.ext fun i j => h3 (z i j) (congrFun₂ hz i j)⟩

theorem smoothAlong_iff {m n : ℕ} (f : Matrix (Fin m) (Fin n) (AE D) → ℂ) :
    SmoothAlong (fun z => z.map (finPart D) = 0) f ↔ ∀ w, ContDiff ℝ ∞ fun p => f (w + realMat D m n p) := by
  obtain ⟨co, c1, -, c3⟩ := exists_coMat D m n
  exact gen_smooth_iff (fun z : Matrix (Fin m) (Fin n) (AE D) => z.map (finPart D) = 0) (realMat D m n) (continuous_realMat D m n)
    (fun p => Matrix.ext fun i j => finPart_realPt D (p i j)) co c1 c3 f

theorem continuous_cA (D : D7) : Continuous (cA D) :=
  IsModuleTopology.continuous_of_linearMap
    (Algebra.TensorProduct.map (AlgHom.id (AF D.host.F) (AF D.host.F)) D.sp.cm.sig).toLinearMap

end GlobalTheory.DualPairCompare

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.continuous_of_heisenberg_level_and_smooth : ∀ (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), Chart θ σ → ∀ (ψ : AddChar (AF D.host.F) ℂ), Continuous ψ → ∀ (V W : HSp D) (f : WA V W → ℂ), (∃ U : AddSubgroup (WA V W), IsOpen (U : Set (WA V W)) ∧ ∀ u ∈ U, u.map (infPart D) = 0 → Heisenberg₂ ψ V W u f = f) → Sm (iotaW σ V W) f → Continuous f := by
  first | exact @GlobalTheory.FockCompare.ThetaCont.continuous_of_level_of_smooth | exact GlobalTheory.FockCompare.ThetaCont.continuous_of_level_of_smooth | (intros; apply GlobalTheory.FockCompare.ThetaCont.continuous_of_level_of_smooth <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.heisenbergDirectionalDeriv_formula_and_smooth : ∀ (G R : Type) [AddCommGroup G] [NormedAddCommGroup R] [NormedSpace ℝ R] [FiniteDimensional ℝ R] (ι : R →+ G) (π : G →+ R) (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ), (∀ x, π (ι x) = x) → ∀ (f : G → ℂ), Sm ι f → ∀ u : R, (∀ w, hD ι π om u f w = -(Real.pi * Complex.I) * (om (π w) u : ℝ) * f w + fderiv ℝ (fun x : R => f (w + ι x)) 0 u) ∧ Sm ι (hD ι π om u f) := by
  first | exact @GlobalTheory.FockCompare.hD_formula_smooth | exact GlobalTheory.FockCompare.hD_formula_smooth | (intros; apply GlobalTheory.FockCompare.hD_formula_smooth <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.hermitianMajorant_isCartanInvolution_and_commute_iff : ∀ (n p q : ℕ), p + q = n → ∀ (A : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ) (G t : Matrix (Fin n) (Fin n) ℂ), G.det ≠ 0 → Aᴴ * Formalism.UG.Jpq p q * A = G → Formalism.UG.Jpq p q * A = A * t → IsCart G t ∧ ∀ g : Matrix (Fin n) (Fin n) ℂ, (∃ b : Mat p q, IsKC b ∧ b * A = A * g) ↔ Commute g t := by
  first | exact @GlobalTheory.FockCompare.CartanRel.cartan_rel | exact GlobalTheory.FockCompare.CartanRel.cartan_rel | (intros; apply GlobalTheory.FockCompare.CartanRel.cartan_rel <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.smooth_iff_realCoordinates_and_real_lines : ∀ (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), Chart θ σ → ∀ (V W : HSp D), (∀ f : WA V W → ℂ, (∀ (k : ℕ) (L : (Fin k → ℝ) →+ WA V W), Continuous L → (∀ t, (L t).map (finPart D) = 0) → ∀ w, ContDiff ℝ ∞ fun t => f (w + L t)) ↔ Sm (iotaW σ V W) f) ∧ (∀ L : ℝ →+ WA V W, IsRealDir V W L → ∀ t : ℝ, L t = iotaW σ V W (t • piW θ V W (L 1))) ∧ ∀ u : RW V W, ∃ L : ℝ →+ WA V W, IsRealDir V W L ∧ ∀ t : ℝ, L t = iotaW σ V W (t • u) := by
  first | exact @GlobalTheory.FockCompare.smooth_iff_sm_and_real_lines | exact GlobalTheory.FockCompare.smooth_iff_sm_and_real_lines | (intros; apply GlobalTheory.FockCompare.smooth_iff_sm_and_real_lines <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_heisenberg_derivative_linear_operators : ∀ (G R : Type) [AddCommGroup G] [NormedAddCommGroup R] [NormedSpace ℝ R] [FiniteDimensional ℝ R] (ι : R →+ G) (π : G →+ R) (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ), (∀ x, π (ι x) = x) → (∀ (f : G → ℂ), Sm ι f → ∀ (u : R) (w : G), hD ι π om u f w = -(Real.pi * Complex.I) * (om (π w) u : ℝ) * f w + fderiv ℝ (fun x : R => f (w + ι x)) 0 u) → ∀ (M : Submodule ℂ (G → ℂ)), (∀ f ∈ M, Sm ι f) → (∀ u, ∀ f ∈ M, hD ι π om u f ∈ M) → ∃ Dop : R → Module.End ℂ M, (∀ u (f : M), ((Dop u f : M) : G → ℂ) = hD ι π om u f) ∧ (∀ u v, Dop (u + v) = Dop u + Dop v) ∧ ∀ (c : ℝ) u, Dop (c • u) = (c : ℂ) • Dop u := by
  first | exact @GlobalTheory.FockCompare.exists_heisenberg_operators | exact GlobalTheory.FockCompare.exists_heisenberg_operators | (intros; apply GlobalTheory.FockCompare.exists_heisenberg_operators <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isKilledByOperatorProducts_succ_creation_apply : ∀ (I M : Type) [AddCommGroup M] [Module ℂ M] (a : I → Module.End ℂ M) (c : Module.End ℂ M), (∀ i, ∃ β : ℂ, a i * c - c * a i = β • (1 : Module.End ℂ M)) → ∀ (N : ℕ) (m : M), Killed a N m → Killed a (N + 1) (c m) := by
  first | exact @GlobalTheory.FockCompare.WeylCreate.killed_create | exact GlobalTheory.FockCompare.WeylCreate.killed_create | (intros; apply GlobalTheory.FockCompare.WeylCreate.killed_create <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.mem_of_isKilledByOperatorProducts_vacuum_creation : ∀ (I M : Type) [AddCommGroup M] [Module ℂ M] (a c : I → Module.End ℂ M) (n : ℕ) (e : Fin n → I) (lam : ℂ), lam ≠ 0 → (∀ i, a i * (∑ k, c (e k) * a (e k)) = ((∑ k, c (e k) * a (e k)) + lam • (1 : Module.End ℂ M)) * a i) → ∀ P : Submodule ℂ M, (∀ m, (∀ i, a i m = 0) → m ∈ P) → (∀ i, ∀ m ∈ P, c i m ∈ P) → ∀ (N : ℕ) (m : M), Killed a N m → m ∈ P := by
  first | exact @GlobalTheory.FockCompare.WeylInduct.mem_of_killed | exact GlobalTheory.FockCompare.WeylInduct.mem_of_killed | (intros; apply GlobalTheory.FockCompare.WeylInduct.mem_of_killed <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.norm_thetaFunction_periodic_real_variables : ∀ (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), Chart θ σ → ∀ (ψ : AddChar (AF D.host.F) ℂ), (∀ x, ‖ψ x‖ = 1) → (∀ U : AddSubgroup (AF D.host.F), IsOpen (U : Set (AF D.host.F)) → ∃ N : ℕ, 0 < N ∧ pairA D.host.F 0 (N : Af D.host.F) ∈ U) → ∀ (V W : HSp D) (f : WA V W → ℂ), IsThetaFun ψ V W f → ∀ γ : Matrix (Fin V.rank) (Fin W.rank) D.host.E, ∃ N : ℕ, 0 < N ∧ ∀ w, ‖f (w + iotaW σ V W ((N : ℝ) • piW θ V W (ratW V W γ)))‖ = ‖f w‖ := by
  first | exact @GlobalTheory.FockCompare.ThetaPeriod.norm_periodic | exact GlobalTheory.FockCompare.ThetaPeriod.norm_periodic | (intros; apply GlobalTheory.FockCompare.ThetaPeriod.norm_periodic <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.span_realProjection_rationalPoints_eq_top : ∀ (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), Chart θ σ → ∀ (V W : HSp D), Submodule.span ℝ (Set.range fun γ : Matrix (Fin V.rank) (Fin W.rank) D.host.E => piW θ V W (ratW V W γ)) = ⊤ := by
  first | exact @GlobalTheory.FockCompare.span_piW_ratW_eq_top | exact GlobalTheory.FockCompare.span_piW_ratW_eq_top | (intros; apply GlobalTheory.FockCompare.span_piW_ratW_eq_top <;> assumption)
end
