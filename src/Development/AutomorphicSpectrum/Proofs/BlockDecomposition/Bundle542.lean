module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle492
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle493
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle516
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle513
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle515
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle499
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle517
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle518
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle500
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle519
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle520
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
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLoc

@[expose] public section

section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG

theorem _root_.GlobalTheory.T.invariant_intertwines_dual : ∀ {n : ℕ} (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)) (Kf : Fin n → Fin n → Module.End ℂ V), IsDerivK σ Kf → ∀ (E : KMod n) (G : Fin n → Fin n → Module.End ℂ (E.V →L[ℂ] ℂ)), IsDualFam E G → ∀ t ∈ invA σ E, ∀ a b ξ, t (G a b ξ) = Kf a b (t ξ) := by
  first | exact @GlobalTheory.CompanionTheory.RealCountG.Intertw.intertwines | exact GlobalTheory.CompanionTheory.RealCountG.Intertw.intertwines | (intros; apply GlobalTheory.CompanionTheory.RealCountG.Intertw.intertwines <;> assumption)
end

section

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.right_derivative_lower_block_at_one : ∀ (n : ℕ) (lev : Fin n → ℕ) (f h : GlobalTheory.CompanionTheory.ModelS.SmF n), f ∈ GlobalTheory.CompanionTheory.ModelS.Eqv lev f.1 → f.1 1 = 1 → h ∈ GlobalTheory.CompanionTheory.ModelS.Eqv lev f.1 → ∀ X : Mat n, (∀ a b, lev a < lev b → X a b = 0) → (GlobalTheory.CompanionTheory.ModelS.DR X h).1 1 = (GlobalTheory.CompanionTheory.ModelS.DR X f).1 1 * h.1 1 := by
  first | exact @GlobalTheory.CompanionTheory.ModelS.DR_one_of_eqv | exact GlobalTheory.CompanionTheory.ModelS.DR_one_of_eqv | (intros; apply GlobalTheory.CompanionTheory.ModelS.DR_one_of_eqv <;> assumption)
end

section

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.right_derivative_real_lie_hom : ∀ (n : ℕ), (∀ X Y : Mat n, GlobalTheory.CompanionTheory.ModelS.DR (X + Y) = GlobalTheory.CompanionTheory.ModelS.DR X + GlobalTheory.CompanionTheory.ModelS.DR Y) ∧ (∀ (r : ℝ) (X : Mat n), GlobalTheory.CompanionTheory.ModelS.DR ((r : ℂ) • X) = (r : ℂ) • GlobalTheory.CompanionTheory.ModelS.DR X) ∧ (∀ X Y : Mat n, GlobalTheory.CompanionTheory.ModelS.DR (X * Y - Y * X) = GlobalTheory.CompanionTheory.ModelS.DR X * GlobalTheory.CompanionTheory.ModelS.DR Y - GlobalTheory.CompanionTheory.ModelS.DR Y * GlobalTheory.CompanionTheory.ModelS.DR X) := by
  first | exact @GlobalTheory.CompanionTheory.ModelS.LieAct.DR_lie | exact GlobalTheory.CompanionTheory.ModelS.LieAct.DR_lie | (intros; apply GlobalTheory.CompanionTheory.ModelS.LieAct.DR_lie <;> assumption)
end

section

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.k_action_skew_adjoint_l2 : ∀ (n : ℕ) [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)] [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)] (κ : Measure (Matrix.unitaryGroup (Fin n) ℂ)) [IsFiniteMeasure κ], (∀ u : Mat n → ℂ, ContDiffOn ℝ ∞ u (GLs n) → ∀ X : Mat n, Xᴴ = -X → ∫ k : Matrix.unitaryGroup (Fin n) ℂ, Rd X u k.1 ∂κ = 0) → ∀ (a b : Fin n) (x y : GlobalTheory.CompanionTheory.ModelS.SmF n), GlobalTheory.CompanionTheory.ModelS.ipK κ (GlobalTheory.CompanionTheory.ModelS.Kf a b x) y = GlobalTheory.CompanionTheory.ModelS.ipK κ x (GlobalTheory.CompanionTheory.ModelS.Kf b a y) := by
  first | exact @GlobalTheory.CompanionTheory.ModelS.ipK_Kf_transpose | exact GlobalTheory.CompanionTheory.ModelS.ipK_Kf_transpose | (intros; apply GlobalTheory.CompanionTheory.ModelS.ipK_Kf_transpose <;> assumption)
end

section

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.l2_inner_product_hermitian_form : ∀ (n : ℕ) [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)] [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)] (κ : Measure (Matrix.unitaryGroup (Fin n) ℂ)) [IsFiniteMeasure κ] [κ.IsOpenPosMeasure], (∀ x y : GlobalTheory.CompanionTheory.ModelS.SmF n, conj (GlobalTheory.CompanionTheory.ModelS.ipK κ y x) = GlobalTheory.CompanionTheory.ModelS.ipK κ x y) ∧ (∀ x : GlobalTheory.CompanionTheory.ModelS.SmF n, 0 ≤ (GlobalTheory.CompanionTheory.ModelS.ipK κ x x).re) ∧ (∀ x y z : GlobalTheory.CompanionTheory.ModelS.SmF n, GlobalTheory.CompanionTheory.ModelS.ipK κ (x + y) z = GlobalTheory.CompanionTheory.ModelS.ipK κ x z + GlobalTheory.CompanionTheory.ModelS.ipK κ y z) ∧ (∀ (c : ℂ) (x y : GlobalTheory.CompanionTheory.ModelS.SmF n), GlobalTheory.CompanionTheory.ModelS.ipK κ (c • x) y = conj c * GlobalTheory.CompanionTheory.ModelS.ipK κ x y) ∧ ∀ x : GlobalTheory.CompanionTheory.ModelS.SmF n, GlobalTheory.CompanionTheory.ModelS.ipK κ x x = 0 → ∀ k : Matrix.unitaryGroup (Fin n) ℂ, x.1 k.1 = 0 :=
  @GlobalTheory.CompanionTheory.ModelS.L2InnerProduct.ipK_form
end

section

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.iwasawa_parabolic_unitary : ∀ (n : ℕ) (lev : Fin n → ℕ), Monotone lev → ∀ g ∈ GLs n, ∃ p ∈ GlobalTheory.CompanionTheory.ModelS.Pb lev, ∃ k : Matrix.unitaryGroup (Fin n) ℂ, g = p * k.1 := by
  first | exact @GlobalTheory.CompanionTheory.ModelS.exists_Pb_mul_unitary | exact GlobalTheory.CompanionTheory.ModelS.exists_Pb_mul_unitary | (intros; apply GlobalTheory.CompanionTheory.ModelS.exists_Pb_mul_unitary <;> assumption)
end

section

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.right_derivative_preserves_equivariant : ∀ (n : ℕ) (lev : Fin n → ℕ) (φ : Mat n → ℂ) (X : Mat n) (h : GlobalTheory.CompanionTheory.ModelS.SmF n), h ∈ GlobalTheory.CompanionTheory.ModelS.Eqv lev φ → GlobalTheory.CompanionTheory.ModelS.DR X h ∈ GlobalTheory.CompanionTheory.ModelS.Eqv lev φ := by
  first | exact @GlobalTheory.CompanionTheory.ModelS.DR_mem_Eqv | exact GlobalTheory.CompanionTheory.ModelS.DR_mem_Eqv | (intros; apply GlobalTheory.CompanionTheory.ModelS.DR_mem_Eqv <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.CompanionTheory.WSum
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.archimedean_multiplier_temperate : ∀ (D : D7) (r : ℕ) (θ : InfFam D), IsInfFam θ → ∀ (α : D.host.F) (V : HSp D) (a : HermE D r), ∃ q : (D.what₂.Tau → Fin V.rank → Fin r → ℂ) → ℂ, q.HasTemperateGrowth ∧ ∀ y, ((multM θ α V a y : ℝ) : ℂ) = q (fun τ i j => compAt θ τ y i j) := by
  first | exact @GlobalTheory.CompanionTheory.WSum.multM_tempered | exact GlobalTheory.CompanionTheory.WSum.multM_tempered | (intros; apply GlobalTheory.CompanionTheory.WSum.multM_tempered <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.CompanionTheory.WSum
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.character_along_one_parameter_path : ∀ (D : D7) (ψ ψ₀ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ₀ (-1) → ∀ α : D.host.F, (∀ x, ψ x = ψ₀ (algebraMap D.host.F (AF D.host.F) α * x)) → ∀ (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ → ∀ (t : AE D) (s : ℝ), ψ (halfTr (rs σ s * t)) = Complex.exp (2 * Real.pi * Complex.I * ((s * lam θ α t : ℝ) : ℂ)) := by
  first | exact @GlobalTheory.CompanionTheory.WSum.psi_halfTr_rs | exact GlobalTheory.CompanionTheory.WSum.psi_halfTr_rs | (intros; apply GlobalTheory.CompanionTheory.WSum.psi_halfTr_rs <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.CompanionTheory.WSum
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.injective_pairing_finite_family : ∀ (D : D7) (r : ℕ) (θ : InfFam D), IsInfFam θ → ∀ α : D.host.F, α ≠ 0 → ∃ (d : ℕ) (a : Fin d → HermE D r), Function.Injective (fun (β : HermE D r) (k : Fin d) => pairF θ α (a k) β) := by
  first | exact @GlobalTheory.CompanionTheory.WSum.Sep.exists_separating | exact GlobalTheory.CompanionTheory.WSum.Sep.exists_separating | (intros; apply GlobalTheory.CompanionTheory.WSum.Sep.exists_separating <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.RgEis GlobalTheory.CompanionTheory.SiegelFrame

theorem _root_.GlobalTheory.T.parabolic_iff_frame_parabolic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (Y : Spc F E n), ∀ (χ : Chr F E) (ε : ℤˣ) (b : GL (Fin n ⊕ Fin n) E) (hb : b.1ᵀ * dbl Y.J * b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) (t₀ : GL (Fin n) E), b.1.toCols₁ = diagCols (Fin n) * t₀.1 → ∀ x : G2 σ Y, (∃ t, IsPar x t) ↔ frameEquiv χ ε b hb x ∈ (adCM σ χ).uQ ε (Set.univ : Set (Fin n)) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelFrame.ParStab.exists_isPar_iff_mem_uQ | exact GlobalTheory.CompanionTheory.SiegelFrame.ParStab.exists_isPar_iff_mem_uQ | (intros; apply GlobalTheory.CompanionTheory.SiegelFrame.ParStab.exists_isPar_iff_mem_uQ <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.RgEis GlobalTheory.CompanionTheory.SiegelFrame

theorem _root_.GlobalTheory.T.block_det_parabolic_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (Y : Spc F E n), ∀ (χ : Chr F E) (ε : ℤˣ) (b : GL (Fin n ⊕ Fin n) E) (hb : b.1ᵀ * dbl Y.J * b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) (t₀ : GL (Fin n) E), b.1.toCols₁ = diagCols (Fin n) * t₀.1 → ∀ (p : G2 σ Y) (t : GL (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), IsPar p t → bdet (Sum.inl '' (Set.univ : Set (Fin n))) (frameEquiv χ ε b hb p).1 = Matrix.GeneralLinearGroup.det t := by
  first | exact @GlobalTheory.CompanionTheory.SiegelFrameDet.bdet_frameEquiv | exact GlobalTheory.CompanionTheory.SiegelFrameDet.bdet_frameEquiv | (intros; apply GlobalTheory.CompanionTheory.SiegelFrameDet.bdet_frameEquiv <;> assumption)
end
