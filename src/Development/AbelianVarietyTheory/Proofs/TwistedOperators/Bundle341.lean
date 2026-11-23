module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1545
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle140
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle078
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle073
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle229
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle277
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle320
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle184
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle323
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle223
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle271
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle324
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle287
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

noncomputable section

namespace GlobalTheory.SquareComm.ThetaLeft

theorem isThetaFunO_of_mem_algF {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1))
    (hθ : IsInfFam θ) {M X : HSp D} (A : Fr M) (B : Fr X) {Φ : WO M X → ℂ} (hΦ : Φ ∈ algF ψ θ false A B) :
    IsThetaFunO ψ M X Φ := by
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, P, hf, rfl⟩ := hx
    exact GlobalTheory.GalLift.Vec.theta_pureTensorO hψ hθ _ _ _ _ hf.1 P
  | zero => exact GlobalTheory.OrientedHeis.theta_zero
  | add x y _ _ hx hy => exact GlobalTheory.OrientedHeis.theta_add hx hy
  | smul c x _ hx => exact GlobalTheory.OrientedHeis.theta_smul c hx

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (M X : HSp D) (A : Fr M) (B : Fr X)
    (χ χ' : (AE D)ˣ →* Circle) (ω : WRep M X), IsWeil ψ false M X χ χ' ω → ∀ Φ ∈ algF ψ θ false A B, ∀ γ ∈ GQ M,
    ∀ (g : GA D M) (h : GA D X), thetaKO ω (γ * g) h Φ = thetaKO ω g h Φ := by
  intro D ψ θ hθ M X A B χ χ' ω hω Φ hΦ γ hγ g h
  have hω' : IsWeilDatumO ψ M X χ χ' ω := hω
  have hth : IsThetaFunO ψ M X Φ := isThetaFunO_of_mem_algF hω'.std hθ A B hΦ
  unfold thetaKO
  have e : (γ * g, h) = (γ, (1 : GA D X)) * (g, h) := by simp
  rw [e, map_mul, Module.End.mul_apply]
  exact hω'.om_aut _ hγ _ (Subgroup.one_mem _) _ (hω'.om_pres _ _ hth)

end GlobalTheory.SquareComm.ThetaLeft
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.SquareComm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace CompanionTheory.Member.BlockMatrixNorms

theorem sq_le {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) (x : n → ℂ) :
    ∑ i, ‖(M *ᵥ x) i‖ ^ 2 ≤ ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) M‖ ^ 2 * ∑ i, ‖x i‖ ^ 2 := by
  have h := (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) M).le_opNorm (WithLp.toLp 2 x)
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at h2
  exact h2

theorem opNorm_blk {m n ι : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]
    (e : m ⊕ n ≃ ι) (x : Matrix m m ℂ) (y : Matrix n n ℂ) :
    ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (GlobalTheory.Doubling.blkMat e x y)‖₊ ≤
      max ‖Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ) x‖₊ ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) y‖₊ := by
  rw [← NNReal.coe_le_coe, NNReal.coe_max, coe_nnnorm, coe_nnnorm, coe_nnnorm]
  set a := ‖Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ) x‖ with ha
  set b := ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) y‖ with hb
  have ha0 : 0 ≤ a := norm_nonneg _
  have hb0 : 0 ≤ b := norm_nonneg _
  have hm : 0 ≤ max a b := le_max_of_le_left ha0
  refine ContinuousLinearMap.opNorm_le_bound _ hm fun w => ?_
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hm (norm_nonneg _)) two_ne_zero).1 ?_
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  have h1 := sq_le x (fun i => w.ofLp (e (.inl i)))
  have h2 := sq_le y (fun i => w.ofLp (e (.inr i)))
  have e1 : ∀ i, (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (GlobalTheory.Doubling.blkMat e x y) w).ofLp (e (.inl i)) =
      (x *ᵥ fun i => w.ofLp (e (.inl i))) i := by
    intro i
    show (GlobalTheory.Doubling.blkMat e x y *ᵥ w.ofLp) (e (.inl i)) = _
    simp [Matrix.mulVec, dotProduct, ← e.sum_comp, GlobalTheory.Doubling.blkMat]
  have e2 : ∀ i, (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (GlobalTheory.Doubling.blkMat e x y) w).ofLp (e (.inr i)) =
      (y *ᵥ fun i => w.ofLp (e (.inr i))) i := by
    intro i
    show (GlobalTheory.Doubling.blkMat e x y *ᵥ w.ofLp) (e (.inr i)) = _
    simp [Matrix.mulVec, dotProduct, ← e.sum_comp, GlobalTheory.Doubling.blkMat]
  rw [← e.sum_comp, ← e.sum_comp (fun i => ‖w.ofLp i‖ ^ 2), Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [e1, e2]
  have s1 : 0 ≤ ∑ i, ‖w.ofLp (e (.inl i))‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  have s2 : 0 ≤ ∑ i, ‖w.ofLp (e (.inr i))‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  have p1 : a ^ 2 ≤ (max a b) ^ 2 := pow_le_pow_left₀ ha0 (le_max_left _ _) 2
  have p2 : b ^ 2 ≤ (max a b) ^ 2 := pow_le_pow_left₀ hb0 (le_max_right _ _) 2
  rw [mul_add]
  exact add_le_add (h1.trans (mul_le_mul_of_nonneg_right p1 s1)) (h2.trans (mul_le_mul_of_nonneg_right p2 s2))

theorem key {c c' a a' b b' : NNReal} (h : c ≤ max a b) (h' : c' ≤ max a' b') :
    max 1 (max c c') ≤ max 1 (max a a') * max 1 (max b b') := by
  have hA : 1 ≤ max 1 (max a a') := le_max_left _ _
  have hB : 1 ≤ max 1 (max b b') := le_max_left _ _
  have l1 : max 1 (max a a') ≤ max 1 (max a a') * max 1 (max b b') := le_mul_of_one_le_right' hB
  have l2 : max 1 (max b b') ≤ max 1 (max a a') * max 1 (max b b') := le_mul_of_one_le_left' hA
  refine max_le (hA.trans l1) (max_le (h.trans (max_le ?_ ?_)) (h'.trans (max_le ?_ ?_)))
  · exact (le_max_of_le_right (le_max_left _ _)).trans l1
  · exact (le_max_of_le_right (le_max_left _ _)).trans l2
  · exact (le_max_of_le_right (le_max_right _ _)).trans l1
  · exact (le_max_of_le_right (le_max_right _ _)).trans l2

theorem sup_blk {A m n ι κ : Type} [CommRing A] [Fintype m] [Fintype n] [Fintype ι] [Fintype κ]
    (e : m ⊕ n ≃ ι) (φ : A → κ → NNReal) (hφ : ∀ k, φ 0 k = 0) (x : Matrix m m A) (y : Matrix n n A) :
    (Finset.univ.sup fun p : ι × ι × κ => φ (GlobalTheory.Doubling.blkMat e x y p.1 p.2.1) p.2.2) ≤
      max (Finset.univ.sup fun p : m × m × κ => φ (x p.1 p.2.1) p.2.2)
        (Finset.univ.sup fun p : n × n × κ => φ (y p.1 p.2.1) p.2.2) := by
  refine Finset.sup_le ?_
  rintro ⟨i, j, k⟩ -
  obtain ⟨i, rfl⟩ := e.surjective i
  obtain ⟨j, rfl⟩ := e.surjective j
  simp only [GlobalTheory.Doubling.blkMat, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases i with i | i <;> rcases j with j | j
  · exact le_max_of_le_left (Finset.le_sup (f := fun p : m × m × κ => φ (x p.1 p.2.1) p.2.2) (Finset.mem_univ (i, j, k)))
  · simp [hφ]
  · simp [hφ]
  · exact le_max_of_le_right (Finset.le_sup (f := fun p : n × n × κ => φ (y p.1 p.2.1) p.2.2) (Finset.mem_univ (i, j, k)))

variable {D : D7}

theorem finMat_blk (V V₁ : HSp D) (g : GA D V) (g₁ : GA D V₁) :
    finMat D.sp.cm.sig (hsum V V₁).gram (blk V V₁ (g, g₁)) =
      GlobalTheory.Doubling.blkMat finSumFinEquiv (finMat D.sp.cm.sig V.gram g) (finMat D.sp.cm.sig V₁.gram g₁) :=
  blkMat_map finSumFinEquiv _ (map_zero _) (Formalism.L2.Theta.mt V g) (Formalism.L2.Theta.mt V₁ g₁)

theorem infMat_blk (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (V V₁ : HSp D) (g : GA D V) (g₁ : GA D V₁) :
    infMat D.sp.cm.sig (hsum V V₁).gram θ (blk V V₁ (g, g₁)) =
      GlobalTheory.Doubling.blkMat finSumFinEquiv (infMat D.sp.cm.sig V.gram θ g) (infMat D.sp.cm.sig V₁.gram θ g₁) := by
  have h := blkMat_map finSumFinEquiv
    (fun z => θ (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) z)) (by simp only [map_zero])
    (Formalism.L2.Theta.mt V g) (Formalism.L2.Theta.mt V₁ g₁)
  exact h

theorem infNorm_blk (θ : InfFam D) (V V₁ : HSp D) (τ : D.what₂.Tau) (g : GA D V) (g₁ : GA D V₁) :
    GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.infNorm θ (hsum V V₁) τ (blk V V₁ (g, g₁)) ≤
      max (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.infNorm θ V τ g) (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.infNorm θ V₁ τ g₁) := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.infNorm
  rw [infMat_blk]
  exact opNorm_blk _ _ _

theorem finNorm_blk (V V₁ : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (g : GA D V) (g₁ : GA D V₁) :
    GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finNorm (hsum V V₁) v (blk V V₁ (g, g₁)) ≤
      max (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finNorm V v g) (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finNorm V₁ v g₁) := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finNorm
  rw [finMat_blk]
  refine sup_blk finSumFinEquiv (fun z k => ‖evalV D.host.F v (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D z k)‖₊) (fun k => ?_) _ _
  have hz : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D 0 k = 0 := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord
    rw [map_zero]; rfl
  show ‖evalV D.host.F v (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D 0 k)‖₊ = 0
  rw [hz, map_zero, nnnorm_zero]

theorem blk_inv (V V₁ : HSp D) (g : GA D V) (g₁ : GA D V₁) :
    (blk V V₁ (g, g₁))⁻¹ = blk V V₁ (g⁻¹, g₁⁻¹) := (map_inv (blk V V₁) (g, g₁)).symm

end CompanionTheory.Member.BlockMatrixNorms

theorem CompanionTheory.Member.unitaryAdelicHeight_blockDiagonal_le_mul : ∀ (D : D7) (θ : InfFam D) (V V₁ : HSp D) (g : GA D V) (g₁ : GA D V₁), GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ (hsum V V₁) (blk V V₁ (g, g₁)) ≤ GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V g * GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V₁ g₁ := by
  intro D θ V V₁ g g₁
  have f0 := GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finHt_mulSupport_finite (hsum V V₁) (blk V V₁ (g, g₁))
  have f1 := GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finHt_mulSupport_finite V g
  have f2 := GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finHt_mulSupport_finite V₁ g₁
  unfold GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height
  rw [mul_mul_mul_comm, ← Finset.prod_mul_distrib, ← finprod_mul_distrib f1 f2]
  refine mul_le_mul' (Finset.prod_le_prod' fun τ _ => ?_) ?_
  · unfold GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.infHt
    rw [CompanionTheory.Member.BlockMatrixNorms.blk_inv]
    exact CompanionTheory.Member.BlockMatrixNorms.key (CompanionTheory.Member.BlockMatrixNorms.infNorm_blk _ _ _ _ _ _)
      (CompanionTheory.Member.BlockMatrixNorms.infNorm_blk _ _ _ _ _ _)
  · refine finprod_le_finprod' f0 ((f1.union f2).subset (Function.mulSupport_mul _ _)) fun v => ?_
    show GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finHt _ _ _ ≤ GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finHt _ _ _ * GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finHt _ _ _
    unfold GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finHt
    rw [CompanionTheory.Member.BlockMatrixNorms.blk_inv]
    exact CompanionTheory.Member.BlockMatrixNorms.key (CompanionTheory.Member.BlockMatrixNorms.finNorm_blk _ _ _ _ _)
      (CompanionTheory.Member.BlockMatrixNorms.finNorm_blk _ _ _ _ _)

end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.SquareComm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem _root_.GlobalTheory.Adopt.unitaryAdelicHeight_orthogonalSum_embedding_le_mul : ∀ (D : D7) (θ : InfFam D) (V V₁ : HSp D) (g : GA D V) (g₁ : GA D V₁), GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ (hsum V V₁) (blk V V₁ (g, g₁)) ≤ GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V g * GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V₁ g₁ := by
  first | exact @CompanionTheory.Member.unitaryAdelicHeight_blockDiagonal_le_mul | exact CompanionTheory.Member.unitaryAdelicHeight_blockDiagonal_le_mul | (intros; apply CompanionTheory.Member.unitaryAdelicHeight_blockDiagonal_le_mul <;> assumption)

end
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MixedTermIntegral

variable {D : D7}

def infLift {m n : ℕ} (x : Matrix (Fin m) (Fin n) D.host.E) : Mx D m n :=
  x.map fun e => (pairA D.host.F 1 0 : AF D.host.F) ⊗ₜ[D.host.F] e

theorem map_incA_eq {m n : ℕ} (x : Matrix (Fin m) (Fin n) D.host.E) :
    x.map (incA D) = finLift x + infLift x := by
  ext a b
  simp only [Matrix.map_apply, Matrix.add_apply, finLift, infLift]
  rw [← TensorProduct.add_tmul]
  have : (pairA D.host.F 0 1 + pairA D.host.F 1 0 : AF D.host.F) = 1 := by
    refine Prod.ext ?_ ?_
    · exact zero_add _
    · exact add_zero _
  rw [this]
  rfl

theorem infLift_finPart {m n : ℕ} (x : Matrix (Fin m) (Fin n) D.host.E) :
    (infLift x).map (finPart D) = 0 := by
  ext a b
  simp only [Matrix.map_apply, infLift, Matrix.zero_apply]
  show (sndA D.host.F (pairA D.host.F 1 0)) ⊗ₜ[D.host.F] x a b = 0
  have : sndA D.host.F (pairA D.host.F 1 0) = 0 := rfl
  rw [this, TensorProduct.zero_tmul]

theorem compAt_infLift {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) {m n : ℕ}
    (x : Matrix (Fin m) (Fin n) D.host.E) : compAt θ τ (infLift x) = x.map (tauE D τ) := by
  ext a b
  simp only [compAt, Matrix.map_apply, infLift]
  have : infPart D ((pairA D.host.F 1 0 : AF D.host.F) ⊗ₜ[D.host.F] x a b) =
      (1 : Ainf D.host.F) ⊗ₜ[D.host.F] x a b := rfl
  rw [this]
  exact (hθ τ).1 _

theorem sum_two_re_tauE (D : D7) (e : D.host.E) :
    ∑ τ, 2 * (tauE D τ e).re = ((Algebra.trace ℚ D.host.E e : ℚ) : ℝ) := by
  classical
  have hc : ∀ σ : D.host.E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ :=
    fun σ => star_star σ
  have hi := GlobalTheory.StdRat.tauE_injective D
  have hcm := GlobalTheory.StdRat.tauE_cm D
  have hb : Function.Bijective (Sum.elim (tauE D) fun t => ComplexEmbedding.conjugate (tauE D t)) := by
    constructor
    · rintro (a | a) (b | b) h <;> simp only [Sum.elim_inl, Sum.elim_inr] at h
      · rw [hi h]
      · exact absurd ⟨a, h⟩ ((hcm (tauE D b)).1 ⟨b, rfl⟩)
      · exact absurd ⟨b, h.symm⟩ ((hcm (tauE D a)).1 ⟨a, rfl⟩)
      · have := congrArg ComplexEmbedding.conjugate h
        rw [hc, hc] at this
        rw [hi this]
    · intro σ
      by_cases h : ∃ t, tauE D t = ComplexEmbedding.conjugate σ
      · obtain ⟨t, ht⟩ := h
        exact ⟨Sum.inr t, by simp only [Sum.elim_inr]; rw [ht, hc]⟩
      · obtain ⟨t, ht⟩ := (hcm σ).2 h
        exact ⟨Sum.inl t, ht⟩
  have h1 : ((Algebra.trace ℚ D.host.E e : ℚ) : ℂ) = ∑ σ : D.host.E →+* ℂ, σ e := by
    have := trace_eq_sum_embeddings (K := ℚ) (L := D.host.E) ℂ (x := e)
    rw [eq_ratCast] at this
    rw [this]
    exact (Fintype.sum_equiv (RingHom.equivRatAlgHom D.host.E ℂ) _ _ fun _ => rfl).symm
  have h4 := hb.sum_comp fun σ : D.host.E →+* ℂ => σ e
  rw [Fintype.sum_sum_type, ← h1] at h4
  simp only [Sum.elim_inl, Sum.elim_inr] at h4
  have h5 := congrArg Complex.re h4
  simp only [ComplexEmbedding.conjugate_coe_eq, Complex.add_re, Complex.re_sum, Complex.conj_re,
    Complex.ratCast_re] at h5
  rw [← h5, Finset.sum_congr rfl fun τ _ => two_mul _, Finset.sum_add_distrib]

theorem phase_add (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) {r : ℕ}
    (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (y : Matrix (Fin W.rank) (Fin r) D.host.E)
    (κ κ' : Mx D W.rank r) :
    phase ψ V W C C' y (κ + κ') = phase ψ V W C C' y κ * phase ψ V W C C' y κ' := by
  have h : isoPart V W C (κ + κ') = isoPart V W C κ + isoPart V W C κ' := Matrix.add_mul _ _ _
  unfold phase
  rw [h, (GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_alt D V W).2.1, AddChar.map_add_eq_mul]

theorem isoPart_rat (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (y : Matrix (Fin W.rank) (Fin r) D.host.E) :
    isoPart V W C (y.map (incA D)) = ratW W V (y * (adj D C * V.gram)) := by
  show HMul.hMul (y.map (incA D)) ((adj D C * V.gram).map (incA D)) = (y * (adj D C * V.gram)).map (incA D)
  simp only [Matrix.map_mul]

theorem phase_rat (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (V W : HSp D) {r : ℕ}
    (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (y x : Matrix (Fin W.rank) (Fin r) D.host.E) :
    phase ψ V W C C' y (x.map (incA D)) = 1 := by
  unfold phase
  rw [isoPart_rat, isoPart_rat]
  obtain ⟨a, ha⟩ := GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_rat D V W (y * (adj D C' * V.gram)) (x * (adj D C * V.gram))
  rw [ha]
  exact hψ.2.2.1 a

theorem trace_tau (τ : D.what₂.Tau) {m n : ℕ} (q : Matrix (Fin m) (Fin n) D.host.E)
    (x : Matrix (Fin n) (Fin m) D.host.E) :
    Matrix.trace (q.map (tauE D τ) * x.map (tauE D τ)) = tauE D τ (Matrix.trace (q * x)) := by
  rw [← Matrix.map_mul (f := tauE D τ)]

  simp only [Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]

theorem ratPair_nat_smul (W : HSp D) {r : ℕ} (y x : Matrix (Fin W.rank) (Fin r) D.host.E) (N : ℕ) :
    ((Algebra.trace ℚ D.host.E (Matrix.trace (pairQ W y * ((N : D.host.E) • x))) : ℚ) : ℝ) =
      (N : ℝ) * ratPair W y x := by
  have h : Matrix.trace (pairQ W y * ((N : D.host.E) • x)) = N • Matrix.trace (pairQ W y * x) := by
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, nsmul_eq_mul]
  rw [h, map_nsmul, nsmul_eq_mul, ratPair]
  push_cast
  rfl

theorem integral : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → adj D C * V.gram * C' = 1 → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∃ e : ℕ, ∀ U : AddSubgroup (WO V W), IsOpen (U : Set (WO V W)) → ∃ M : ℕ, 0 < M ∧ ∀ (g : GA D V) (h : GA D W), ∃ N : ℕ, 0 < N ∧ (N : ℝ) ≤ M * (GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h) ^ e ∧ ∀ F : WO V W → ℂ, IsThetaFunO ψ V W F → (∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ V W (actO V W g h u) F = F) → ∀ y : Matrix (Fin W.rank) (Fin r) D.host.E, term ψ V V' W C C' B μ 𝓨 F y ≠ 0 → ∀ x : Matrix (Fin W.rank) (Fin r) D.host.E, (∀ a b, IsIntegral ℤ (x a b)) → ∃ c : ℤ, (N : ℝ) * ratPair W y x = c := by
  intro D V V' W r C C' B hs hCC ψ hψ θ hθ μ 𝓨 hY
  obtain ⟨e, he⟩ := GlobalTheory.T.openSubgroup_translate_height_bound D V W r (adj D C * V.gram)
  refine ⟨e, fun U hU => ?_⟩
  obtain ⟨M, hM, hMN⟩ := he U hU
  refine ⟨M, hM, fun g h => ?_⟩
  obtain ⟨N, hN, hNle, hx⟩ := hMN g h
  refine ⟨N, hN, hNle, fun F hF hinv y hy x hxi => ?_⟩
  obtain ⟨u, huU, hufin, hact⟩ := hx x hxi
  have h1 : heisO ψ V W (isoPart V W C (finLift ((N : D.host.E) • x))) F = F := by
    have := hinv u huU hufin
    rw [hact] at this
    exact this
  have h2 := GlobalTheory.T.mixedModelTerm_heisenbergIsotropic_character D V V' W r C C' B hs ψ hψ μ 𝓨 hY F hF y (finLift ((N : D.host.E) • x))
  rw [h1] at h2
  have hph : phase ψ V W C C' y (finLift ((N : D.host.E) • x)) = 1 :=
    mul_right_cancel₀ hy (by rw [one_mul]; exact h2.symm)
  have hinf : phase ψ V W C C' y (infLift ((N : D.host.E) • x)) = 1 := by
    have := phase_rat ψ hψ.1 V W C C' y ((N : D.host.E) • x)
    rw [map_incA_eq, phase_add, hph, one_mul] at this
    exact this
  rw [GlobalTheory.T.mixedModelHeisenbergPhase_eq_cexp_realPoints D V W r C C' hCC ψ hψ θ hθ y _ (infLift_finPart _)] at hinf
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 hinf
  have hsum : (∑ τ, 2 * (Matrix.trace ((pairQ W y).map (tauE D τ) *
      compAt θ τ (infLift ((N : D.host.E) • x)))).re : ℝ) = (N : ℝ) * ratPair W y x := by
    rw [← ratPair_nat_smul, ← sum_two_re_tauE]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [compAt_infLift hθ, trace_tau]
  rw [hsum] at hn
  refine ⟨n, ?_⟩
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have h3 : (((N : ℝ) * ratPair W y x : ℝ) : ℂ) = ((n : ℝ) : ℂ) := by
    apply mul_left_cancel₀ hpi
    rw [hn]
    push_cast
    ring
  exact_mod_cast h3

end GlobalTheory.MixedTermIntegral

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open Matrix

theorem _root_.GlobalTheory.T.idempotentCut_mem_latticeStabilizer_of_productLevel : ∀ {D : D7} {n : ℕ} (β : GL (Fin n) (Lev.EAf D)) (P : Finset (Pl D.host.E))
    {n' : P → ℕ} (h : ∀ w, n' w = n) (K : ∀ w : P, Subgroup (GL (Fin (n' w)) (Kw w.1))) (x : GL (Fin n) (Lev.EAf D)),
    x ∈ prodLev β P h K → ∀ (b : Lev.EAf D) (hb : b * b = b),
    (∀ w : Pl D.host.E, (∃ PP ∈ P, w.under (𝓞 D.host.F) = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → GlobalTheory.StdFrames.cpt (D := D) w b = 0) →
    GlobalTheory.UnitaryIdemCut.cutGL b hb x ∈ St β := by
  first | exact @GlobalTheory.CutProdLev.cutGL_mem_St_of_mem_prodLev | exact GlobalTheory.CutProdLev.cutGL_mem_St_of_mem_prodLev | (intros; apply GlobalTheory.CutProdLev.cutGL_mem_St_of_mem_prodLev <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GridJoin

variable {D : D7}

theorem exists_isVac_true_of_agree {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {N₁ N₀ : GlobalTheory.Grid.Node D} {V₁ V₀ : HSp D}
    {Λ₁ : Submodule (𝓞 D.host.E) (Fin V₁.rank → D.host.E)} {Λ₀ : Submodule (𝓞 D.host.E) (Fin V₀.rank → D.host.E)}
    {c₁ : D.what₂.Tau → Matrix (Fin V₁.rank) (Fin V₁.rank) ℂ} {c₀ : D.what₂.Tau → Matrix (Fin V₀.rank) (Fin V₀.rank) ℂ}
    (h₁ : N₁.V = V₁) (hΛ₁ : HEq N₁.Λ Λ₁) (hc₁ : HEq (Formalism.IndefR.Links.cart N₁.M) c₁)
    (h₀ : N₀.V = V₀) (hΛ₀ : HEq N₀.Λ Λ₀) (hc₀ : HEq (Formalism.IndefR.Links.cart N₀.M) c₀)
    {f : WO (negSp V₁) V₀ → ℂ} (hf : IsVacO ψ θ (negSp V₁) V₀ (fun τ => -c₁ τ) c₀ (Λ₁ : Set _) (Λ₀ : Set _) f) :
    ∃ f' : WO N₁.V N₀.V → ℂ, GlobalTheory.Grid.IsVac ψ θ true N₁ N₀ f' := by
  subst h₁ h₀
  obtain rfl := eq_of_heq hΛ₁
  obtain rfl := eq_of_heq hΛ₀
  obtain rfl := eq_of_heq hc₁
  obtain rfl := eq_of_heq hc₀
  exact ⟨f, hf⟩

end GlobalTheory.GridJoin

theorem GlobalTheory.GridJoin.exists_isVac_down : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ i, i < D.R.m → ∃ f : WO (G.P (i + 1)).V (G.P i).V → ℂ, GlobalTheory.Grid.IsVac R.ψ R.θ true (G.P (i + 1)) (G.P i) f := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc _ _ _ F hR _ G' W hW G _ _ hsp _ i hi
  obtain ⟨f, hf⟩ := GlobalTheory.FunObj.exists_isVac W hR.lev (p := .core i) (show (GlobalTheory.ChiGrid.Node.core (i + 1)).InRange D.R.m from (by show i + 1 ≤ D.R.m; omega))
  have a₁ := hsp.core (i + 1) (by omega)
  have a₀ := hsp.core i (by omega)
  unfold GlobalTheory.ChiGrid.GridData.Weil.IsVac at hf
  rw [hW.ψ, hW.θ] at hf
  exact GlobalTheory.GridJoin.exists_isVac_true_of_agree a₁.sp a₁.lat a₁.cart a₀.sp a₀.lat a₀.cart hf

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead


theorem _root_.GlobalTheory.T.exists_frame_reduction_eq_flagBasis_otherInstance : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → ∃ β : GL (Fin (Yc D 0).rank) (EAf D), IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) ∧ ∀ PP ∈ R.Pg, RedIs β PP (flagAt X h PP) := by
  exact @GlobalTheory.SeeConjRead.exists_frame_redIs
end
