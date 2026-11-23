module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle008
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle654
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle686
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle490
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle443
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle608
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle690
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle431
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BigCellCosetsHermitianParam
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.RegularClassTraces.RegClassFin
public import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelImpliesRegularClassFinite
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle500
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle060
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SubsingletonIrrClZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle397
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle383
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle048
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle080
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle067
import GroundTheory.LocalFields.PadicLogSeries
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle459
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle430
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
import Development.AbelianVarietyTheory.Definitions.Foundations.InnerEqZeroOfNotUEquiv

@[expose] public section

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.SegNcjm

theorem exists_perm_of_map_eq {α : Type*} {l : ℕ} {x y : Fin l → α}
    (h : Finset.univ.val.map y = Finset.univ.val.map x) : ∃ e : Equiv.Perm (Fin l), ∀ a, y a = x (e a) :=
  _root_.UpperTheory.Reformulated.B.Yhb6.main h

theorem exists_perm_one_le_jm : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {l N : ℕ} (x : Fin l → IrrGL (k := k))
    (hx : ∑ a, (x a).1 = N) (hxc : ∀ a, (x a).IsCusp) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π) (hi : π.IsIrreducible)
    (h : IsSubquotient π (prodIrr x hx)),
    ∃ (e : Equiv.Perm (Fin l)) (he : ∑ a, (x (e a)).1 = N), 1 ≤ jm (fun a => x (e a)) he π := by
  intro k _ _ _ _ hA l N x hx hxc V _ _ π hs hi h
  obtain ⟨c, y, hy, hyc, φ, hφ⟩ := GlobalTheory.T.support_subscheme_embedding k N V π hs hi
  have h1 : HasSupport π (Finset.univ.val.map x) := hasSupport_of_isSubquotient hi hxc h
  have h2 : HasSupport π (Finset.univ.val.map y) := hasSupport_of_isSubquotient hi hyc (.of_injective φ hφ)
  have hm := GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique GlobalTheory.CompanionTheory.GeoLink.geometricLemma
    GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness h2 h1
  have hcl : c = l := by simpa using congrArg Multiset.card hm
  subst hcl
  obtain ⟨e, he⟩ := exists_perm_of_map_eq hm
  obtain rfl : y = fun a => x (e a) := funext he
  refine ⟨e, hy, GlobalTheory.CompanionTheory.FrobJm.one_le_jm hA _ hy π hs φ ?_⟩
  have : Nontrivial V := GlobalTheory.SmGL.nontrivial_of_irreducible hi
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  exact ⟨v, fun h0 => hv (hφ (h0.trans (map_zero φ).symm))⟩

end GlobalTheory.CompanionTheory.SegNcjm
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis

namespace GlobalTheory.CompanionTheory.ZUnf

section RowReduce

variable {K : Type} [Field K] {n ρ p : ℕ}

theorem exists_rowReduce_firstCols (hn : ρ + p = n) (C : Matrix (Fin n) (Fin n) K)
    (h : LinearMap.ker (C.mulVecLin ∘ₗ zinc hn) = ⊥) :
    ∃ T : Matrix (Fin n) (Fin n) K, IsUnit T.det ∧ ∀ u, (T * C).mulVec (zinc hn u) = -(zinc hn u) := by
  have hz : Function.Injective (zinc (K := K) hn) := by
    intro u v huv
    funext j
    have := congrFun huv ((finSumFinEquiv.trans (finCongr hn)) (Sum.inl j))
    simpa [zinc] using this
  set f : (Fin ρ → K) →ₗ[K] (Fin n → K) := C.mulVecLin ∘ₗ zinc hn with hfdef
  set g : (Fin ρ → K) →ₗ[K] (Fin n → K) := -(zinc hn) with hgdef
  have hf : Function.Injective f := LinearMap.ker_eq_bot.mp h
  have hg : Function.Injective g := by
    intro u v huv
    apply hz
    simpa [hgdef] using huv
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl (LinearMap.range f)
  obtain ⟨W', hW'⟩ := Submodule.exists_isCompl (LinearMap.range g)
  have hfin : Module.finrank K W = Module.finrank K W' := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hW
    have h2 := Submodule.finrank_add_eq_of_isCompl hW'
    rw [LinearMap.finrank_range_of_inj hf] at h1
    rw [LinearMap.finrank_range_of_inj hg] at h2
    omega
  let ψ : W ≃ₗ[K] W' := LinearEquiv.ofFinrankEq W W' hfin
  let φ : LinearMap.range f ≃ₗ[K] LinearMap.range g :=
    (LinearEquiv.ofInjective f hf).symm.trans (LinearEquiv.ofInjective g hg)
  let A : (Fin n → K) ≃ₗ[K] (Fin n → K) :=
    (Submodule.prodEquivOfIsCompl _ _ hW).symm.trans
      ((φ.prodCongr ψ).trans (Submodule.prodEquivOfIsCompl _ _ hW'))
  have hA : ∀ u, A (f u) = g u := by
    intro u
    have h0 : (Submodule.prodEquivOfIsCompl _ _ hW).symm (f u) =
        ((⟨f u, LinearMap.mem_range_self f u⟩ : LinearMap.range f), (0 : W)) :=
      Submodule.prodEquivOfIsCompl_symm_apply_left _ _ hW ⟨f u, LinearMap.mem_range_self f u⟩
    have h1 : φ ⟨f u, LinearMap.mem_range_self f u⟩ = ⟨g u, LinearMap.mem_range_self g u⟩ := by
      have : (LinearEquiv.ofInjective f hf).symm ⟨f u, LinearMap.mem_range_self f u⟩ = u :=
        (LinearEquiv.ofInjective f hf).symm_apply_apply u
      simp only [φ, LinearEquiv.trans_apply, this]
      rfl
    simp only [A, LinearEquiv.trans_apply, h0, LinearEquiv.prodCongr_apply, h1, ψ.map_zero]
    simp
  refine ⟨LinearMap.toMatrix' A.toLinearMap, ?_, ?_⟩
  · refine Matrix.isUnit_det_of_left_inverse (B := LinearMap.toMatrix' A.symm.toLinearMap) ?_
    rw [← LinearMap.toMatrix'_comp]
    simp
  · intro u
    rw [← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec]
    exact hA u

theorem exists_bl_firstCols (hn : ρ + p = n) (N : Matrix (Fin n) (Fin n) K)
    (h : ∀ u, N.mulVec (zinc hn u) = -(zinc hn u)) :
    ∃ (X : Matrix (Fin ρ) (Fin p) K) (c' : Matrix (Fin p) (Fin p) K), N = bl hn (-1) X 0 c' := by
  classical
  set e := finSumFinEquiv.trans (finCongr hn) with he
  refine ⟨(N.submatrix e e).toBlocks₁₂, (N.submatrix e e).toBlocks₂₂, ?_⟩
  have hcol : ∀ (i : Fin n) (j : Fin ρ), N i (e (Sum.inl j)) = -(zinc hn (Pi.single j 1) i) := by
    intro i j
    have h1 := congrFun (h (Pi.single j 1)) i
    have h2 : zinc hn (Pi.single j (1 : K)) = Pi.single (e (Sum.inl j)) 1 := by
      funext k
      obtain ⟨k, rfl⟩ := e.surjective k
      rcases k with k | k
      · simp [zinc, he, Pi.single_apply]
      · have hne : e (Sum.inr k) ≠ e (Sum.inl j) := fun hh => by simpa using e.injective hh
        rw [Pi.single_eq_of_ne hne]
        simp [zinc, he]
    rw [h2, Matrix.mulVec_single_one] at h1
    rw [h2]
    simpa using h1
  ext i j
  obtain ⟨i, rfl⟩ := e.surjective i
  obtain ⟨j, rfl⟩ := e.surjective j
  rcases i with i | i <;> rcases j with j | j
  · simp [bl, ← he, hcol, zinc, Matrix.one_apply, Pi.single_apply]
  · simp [bl, ← he, Matrix.toBlocks₁₂]
  · simp [bl, ← he, hcol, zinc]
  · simp [bl, ← he, Matrix.toBlocks₂₂]

theorem exists_bl_blocks (hn : ρ + p = n) (N : Matrix (Fin n) (Fin n) K) :
    ∃ (a : Matrix (Fin ρ) (Fin ρ) K) (b : Matrix (Fin ρ) (Fin p) K) (c : Matrix (Fin p) (Fin ρ) K)
      (d : Matrix (Fin p) (Fin p) K), N = bl hn a b c d := by
  set e := finSumFinEquiv.trans (finCongr hn) with he
  refine ⟨(N.submatrix e e).toBlocks₁₁, (N.submatrix e e).toBlocks₁₂, (N.submatrix e e).toBlocks₂₁,
    (N.submatrix e e).toBlocks₂₂, ?_⟩
  unfold bl
  rw [Matrix.fromBlocks_toBlocks]
  ext i j
  simp [← he]

end RowReduce

theorem rowReduce_lowerC : ∀ {K : Type} [Field K] (σ : K →+* K), (∀ x, σ (σ x) = x) → ∀ {n ρ p : ℕ} (hn : ρ + p = n) (x : Matrix (Fin (n + n)) (Fin (n + n)) K),
    IsUnit x.det → IsUnitary σ (blk4 0 1 (-1) 0) x → LinearMap.ker ((lowerC x).mulVecLin ∘ₗ zinc hn) = ⊥ →
    ∃ (T₀ : Matrix (Fin n) (Fin n) K) (a₁ b₁ Z : Matrix (Fin ρ) (Fin ρ) K) (a₂ b₂ X Y : Matrix (Fin ρ) (Fin p) K)
      (a₃ b₃ W : Matrix (Fin p) (Fin ρ) K) (a₄ b₄ c' d' : Matrix (Fin p) (Fin p) K),
      IsUnitary σ (blk4 0 1 (-1) 0) (blk4 (bl hn a₁ a₂ a₃ a₄) (bl hn b₁ b₂ b₃ b₄) (bl hn (-1) X 0 c') (bl hn Z Y W d')) ∧
      IsUnit (blk4 (bl hn a₁ a₂ a₃ a₄) (bl hn b₁ b₂ b₃ b₄) (bl hn (-1) X 0 c') (bl hn Z Y W d')).det ∧
      lowerC x = T₀ * bl hn (-1) X 0 c' ∧ GlobalTheory.CompanionTheory.RatPtsUnn.blkD x = T₀ * bl hn Z Y W d' := by
  intro K _ σ hσ n ρ p hn x hdet hU hker
  obtain ⟨T, hT, hTC⟩ := exists_rowReduce_firstCols hn (lowerC x) hker
  obtain ⟨X, c', hN⟩ := exists_bl_firstCols hn (T * lowerC x) hTC
  obtain ⟨a, b, hx⟩ := GlobalTheory.CompanionTheory.SwUnf.BigCell.exists_blockMatrixTwoByTwoFin_eq x
  have hTi : T⁻¹ * T = 1 := Matrix.nonsing_inv_mul T hT
  have hiT : T * T⁻¹ = 1 := Matrix.mul_nonsing_inv T hT
  have hcc : ∀ M : Matrix (Fin n) (Fin n) K, cT σ (cT σ M) = M := by
    intro M
    ext i j
    simp [cT, hσ]
  have hcTi : cT σ T * cT σ T⁻¹ = 1 := by
    rw [← GlobalTheory.CompanionTheory.SwUnf.BigCell.cT_mul_sq, hTi, GlobalTheory.CompanionTheory.SwUnf.BigCell.cT_one_sq]
  have hcTi' : cT σ T⁻¹ * cT σ T = 1 := by
    rw [← GlobalTheory.CompanionTheory.SwUnf.BigCell.cT_mul_sq, hiT, GlobalTheory.CompanionTheory.SwUnf.BigCell.cT_one_sq]
  set m : Matrix (Fin (n + n)) (Fin (n + n)) K := blk4 (cT σ T⁻¹) 0 0 T with hm
  have hmU : cT σ m * blk4 0 1 (-1) 0 * m = blk4 0 1 (-1) 0 := by
    rw [hm, GlobalTheory.CompanionTheory.SwUnf.BigCell.cT_blk4, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul, hcc]
    have hc0 : cT σ (0 : Matrix (Fin n) (Fin n) K) = 0 := by
      ext i j
      simp [cT]
    simp [hTi, hcTi, hc0]
  have hmdet : IsUnit m.det := by
    refine Matrix.isUnit_det_of_left_inverse (B := blk4 (cT σ T) 0 0 T⁻¹) ?_
    rw [hm, submatrix_fromBlocks_mul]
    simp [hTi, hcTi, GlobalTheory.CompanionTheory.SwUnf.BigCell.block_identity_eq_one]
  have hmx : m * x = blk4 (cT σ T⁻¹ * a) (cT σ T⁻¹ * b) (T * lowerC x) (T * GlobalTheory.CompanionTheory.RatPtsUnn.blkD x) := by
    conv_lhs => rw [hx, hm, submatrix_fromBlocks_mul]
    simp
  obtain ⟨a₁, a₂, a₃, a₄, ha⟩ := exists_bl_blocks hn (cT σ T⁻¹ * a)
  obtain ⟨b₁, b₂, b₃, b₄, hb⟩ := exists_bl_blocks hn (cT σ T⁻¹ * b)
  obtain ⟨Z, Y, W, d', hd⟩ := exists_bl_blocks hn (T * GlobalTheory.CompanionTheory.RatPtsUnn.blkD x)
  have hfin : blk4 (bl hn a₁ a₂ a₃ a₄) (bl hn b₁ b₂ b₃ b₄) (bl hn (-1) X 0 c') (bl hn Z Y W d') = m * x := by
    rw [hmx, ha, hb, hN, hd]
  refine ⟨T⁻¹, a₁, b₁, Z, a₂, b₂, X, Y, a₃, b₃, W, a₄, b₄, c', d', ?_, ?_, ?_, ?_⟩
  · rw [hfin]
    unfold IsUnitary at hU ⊢
    have hc : cT σ (m * x) = cT σ x * cT σ m := by
      unfold cT
      rw [Matrix.map_mul, Matrix.transpose_mul]
    rw [hc]
    calc cT σ x * cT σ m * blk4 0 1 (-1) 0 * (m * x)
        = cT σ x * (cT σ m * blk4 0 1 (-1) 0 * m) * x := by simp only [Matrix.mul_assoc]
      _ = blk4 0 1 (-1) 0 := by rw [hmU, hU]
  · rw [hfin, Matrix.det_mul]
    exact hmdet.mul hdet
  · rw [← hN, ← Matrix.mul_assoc, hTi, Matrix.one_mul]
  · rw [← hd, ← Matrix.mul_assoc, hTi, Matrix.one_mul]
end GlobalTheory.CompanionTheory.ZUnf
end
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis

namespace GlobalTheory.CompanionTheory.ZUnf.LowerRows

variable {K : Type} [Field K] {n ρ p : ℕ}

theorem block_matrix_mul {m : ℕ} (a b c d a' b' c' d' : Matrix (Fin m) (Fin m) K) :
    blk4 a b c d * blk4 a' b' c' d' =
      blk4 (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  simp only [blk4]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem blockMatrix_mul_blockMatrix (hn : ρ + p = n) (a a' : Matrix (Fin ρ) (Fin ρ) K) (b b' : Matrix (Fin ρ) (Fin p) K)
    (c c' : Matrix (Fin p) (Fin ρ) K) (d d' : Matrix (Fin p) (Fin p) K) :
    bl hn a b c d * bl hn a' b' c' d' =
      bl hn (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  simp only [bl]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem blockMatrix_add (hn : ρ + p = n) (a a' : Matrix (Fin ρ) (Fin ρ) K) (b b' : Matrix (Fin ρ) (Fin p) K)
    (c c' : Matrix (Fin p) (Fin ρ) K) (d d' : Matrix (Fin p) (Fin p) K) :
    bl hn a b c d + bl hn a' b' c' d' = bl hn (a + a') (b + b') (c + c') (d + d') := by
  simp only [bl]
  rw [← Matrix.fromBlocks_add]
  rfl

theorem lowerRight_block_matrix {m : ℕ} (a b c d : Matrix (Fin m) (Fin m) K) :
    GlobalTheory.CompanionTheory.RatPtsUnn.blkD (blk4 a b c d) = d := by
  ext i j
  simp only [GlobalTheory.CompanionTheory.RatPtsUnn.blkD, blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Matrix.fromBlocks_apply₂₂]

theorem lower_rows_word (σ : K →+* K) (hn : ρ + p = n) (a b c d : Matrix (Fin p) (Fin p) K)
    (ζ : Matrix (Fin ρ) (Fin ρ) K) (η : Matrix (Fin ρ) (Fin p) K) :
    lowerC (wM hn * nM hn ζ * sM hn σ η * eM hn a b c d) = rowC hn η a c ∧
    GlobalTheory.CompanionTheory.RatPtsUnn.blkD (wM hn * nM hn ζ * sM hn σ η * eM hn a b c d) = rowD hn σ ζ η b d := by
  simp only [wM, nM, sM, eM, rowC, rowD, block_matrix_mul, BigCell.lowerLeft_block, lowerRight_block_matrix, blockMatrix_mul_blockMatrix,
    blockMatrix_add, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.mul_neg, Matrix.neg_mul, neg_zero, and_self]

theorem lower_rows : ∀ {K : Type} [Field K] (σ : K →+* K), (∀ x, σ (σ x) = x) → ∀ {n ρ p : ℕ} (hn : ρ + p = n) (a b c d : Matrix (Fin p) (Fin p) K) (ζ : Matrix (Fin ρ) (Fin ρ) K) (η : Matrix (Fin ρ) (Fin p) K),
    lowerC (wM hn * nM hn ζ * sM hn σ η * eM hn a b c d) = rowC hn η a c ∧
    GlobalTheory.CompanionTheory.RatPtsUnn.blkD (wM hn * nM hn ζ * sM hn σ η * eM hn a b c d) = rowD hn σ ζ η b d := by
  intro K _ σ _ n ρ p hn a b c d ζ η
  exact lower_rows_word σ hn a b c d ζ η

end GlobalTheory.CompanionTheory.ZUnf.LowerRows
end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.hermitian_euler_product_standard : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ n : ℕ, 0 < n → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ db : Measure (HermR (AF F) σ n), SdHerm F E σ (AF F) ψ n db → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdInf laminf → (∀ v, GlobalTheory.CompanionTheory.SW.IsStdV v (lam v)) → ∃ S₁ : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)), ∀ S, S₁ ⊆ S → ∃ (ρ : ℕ → HermR (Ainf F) σ n → ℝ) (U : ℕ → ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Set (HermR (Fv F v) σ n)), (∀ k, Continuous (ρ k) ∧ HasCompactSupport (ρ k) ∧ (∀ y, 0 ≤ ρ k y) ∧ 0 < ∫ y, ρ k y ∂(GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n)) ∧ Filter.Tendsto (fun k => tsupport (ρ k)) Filter.atTop (nhds (0 : HermR (Ainf F) σ n)).smallSets ∧ (∀ k v, IsCompact (U k v) ∧ IsOpen (U k v) ∧ (0 : HermR (Fv F v) σ n) ∈ U k v) ∧ (∀ v, Filter.Tendsto (fun k => U k v) Filter.atTop (nhds (0 : HermR (Fv F v) σ n)).smallSets) ∧ (∀ k v, 0 < (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b (lam v) n (U k v)).toReal) ∧ (∀ k, Integrable (GlobalTheory.CompanionTheory.SiegelND.Coef.fouH σ ψ db (GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k))) db ∧ ∀ z, ∫ y, GlobalTheory.CompanionTheory.SiegelND.Coef.fouH σ ψ db (GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k)) y * ψ (pairHerm (AF F) σ n y z) ∂db = GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k) (-z)) ∧ (∀ k, ∫ y, GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k) y ∂db = ((∫ y, ρ k y ∂(GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n) : ℝ) : ℂ) * ∏ v ∈ S, ((GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b (lam v) n (U k v)).toReal : ℂ)) ∧ (∀ k y, ‖GlobalTheory.CompanionTheory.SiegelND.Coef.fouH σ ψ db (GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k)) y‖ ≤ ‖∫ y, GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k) y ∂db‖) ∧ ∀ y, Filter.Tendsto (fun k => GlobalTheory.CompanionTheory.SiegelND.Coef.fouH σ ψ db (GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k)) y / ∫ y, GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k) y ∂db) Filter.atTop (nhds ((GlobalTheory.CompanionTheory.SiegelND.Coef.intH σ b n S).indicator (fun _ => (1 : ℂ)) (GlobalTheory.CompanionTheory.SiegelND.Coef.hermFin σ y))) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Coef.TestDeg.exists_test_approx | exact GlobalTheory.CompanionTheory.SiegelND.Coef.TestDeg.exists_test_approx | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Coef.TestDeg.exists_test_approx <;> assumption)
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf

theorem _root_.GlobalTheory.T.big_cell_cosets_hermitian_param : ∀ {D : D7} {n : ℕ} {w : G D n}, mat w = blk4 0 1 (-1) 0 → ∀ {nb : hermA D n → G D n}, IsNMap nb → ∃ e : ratHerm D n → Cosets (P D n) (GF D n), Function.Injective e ∧ (∀ q, cosetCell q = ⊥ ↔ q ∈ Set.range e) ∧ ∀ f : G D n → ℂ, LeftInv (P D n ⊓ GF D n) f → ∀ (l : ratHerm D n) (y : G D n), term (P D n) (GF D n) f y (e l) = f (w * nb l.1 * y) := by
  first | exact @GlobalTheory.CompanionTheory.SwUnf.BigCell.bigCell | exact GlobalTheory.CompanionTheory.SwUnf.BigCell.bigCell | (intros; apply GlobalTheory.CompanionTheory.SwUnf.BigCell.bigCell <;> assumption)
end
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

theorem _root_.GlobalTheory.T.siegel_implies_regular_class_finite : PositivityTheory.ThKR.SiegelCore → MainStatements.RegularCuspidalTrace.RegClassFin := by
  first | exact @GlobalTheory.CompanionTheory.CFin.regClassFin | exact GlobalTheory.CompanionTheory.CFin.regClassFin | (intros; apply GlobalTheory.CompanionTheory.CFin.regClassFin <;> assumption)
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.FineProdCell

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_class_of_degree (n : ℕ) (t : IrrGL (k := k)) (h : t.1 = n) :
    ∃ u : IrrCl (GL (Fin n) k), (⟨n, u⟩ : IrrGL (k := k)) = t := by
  subst h
  exact ⟨t.2, rfl⟩

theorem subsingleton_irrCl_of_eq_zero (n : ℕ) (h : n = 0) : Subsingleton (IrrCl (GL (Fin n) k)) := by
  subst h
  exact GlobalTheory.SmGL.SegModel.subsingleton_irrCl_zero

theorem class_eq_of_sigma_eq (t : IrrGL (k := k)) (z : IrrCl (GL (Fin t.1) k))
    (h : (⟨t.1, z⟩ : IrrGL (k := k)) = t) : z = t.2 :=
  eq_of_heq (Sigma.ext_iff.1 h).2



theorem jhMult_cell_colour : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {h : ℕ} (x : Fin h → IrrGL (k := k)) (W : List (IrrGL (k := k))) (b : Fin h → Fin W.length → ℕ) (hrow : ∀ i, ∑ j, b i j = (x i).1) (hcol : ∀ j, ∑ i, b i j = (W.get j).1) (c : Fin W.length → Fin h), (∀ i j, b i j = if c j = i then (W.get j).1 else 0) → jhMult (piTensor fun j => (W.get j).rep) (cellFunctor (c := fun i j => Fin (b i j)) (fun i => stdBlocks (b i) (hrow i)) (fun j => stdBlocks (fun i => b i j) (hcol j)) (piTensor fun i => (x i).rep)) = ∏ i, jmL (sub W c i) (x i).rep := by
  intro k _ _ _ _ h x W b hrow hcol c hb
  have hBZ := GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness
  have hC : CellSemisimplification k := (GlobalTheory.CompanionTheory.GeoLink.geometricLemma k).2
  obtain ⟨T, hT0, hT⟩ := hC (Fin h) (Fin W.length) (fun i => Fin (x i).1) (fun j => Fin (W.get j).1)
    (fun i j => Fin (b i j)) (fun i => stdBlocks (b i) (hrow i))
    (fun j => stdBlocks (fun i => b i j) (hcol j)) (fun i => (x i).2.rep.V) (fun i => (x i).rep)
    (fun i => (x i).2.rep.smooth) (fun i => (x i).2.rep.hasFiniteLength)
  have hirr : (piTensor fun j => (W.get j).rep).IsIrreducible :=
    GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible hBZ k _ _ fun j => (W.get j).2.rep
  let τ : IrrRep (Levi k fun j => Fin (W.get j).1) :=
    ⟨_, piTensor fun j => (W.get j).rep, isSmooth_piTensor fun j => (W.get j).2.rep.smooth, hirr⟩
  refine (hT τ).trans ?_
  have hzero : ∀ i j, c j ≠ i → b i j = 0 := fun i j hij => by rw [hb, if_neg hij]

  have hcolumn : ∀ (s : ∀ i j, IrrCl (GL (Fin (b i j)) k)) (j : Fin W.length),
      ∃ z : IrrCl (GL (Fin (W.get j).1) k), (⟨_, z⟩ : IrrGL (k := k)) = ⟨b (c j) j, s (c j) j⟩ ∧
        Nonempty ((multiProd (stdBlocks (fun i => b i j) (hcol j))
          fun i => (s i j).rep.ρ).Equiv z.rep.ρ) := fun s j =>
    GlobalTheory.T.product_single_nonzero_factor_equiv (fun i => (⟨b i j, s i j⟩ : IrrGL (k := k))) (hcol j) (c j)
      fun i hi => hzero i j (Ne.symm hi)

  have hex : ∀ i j, ∃ u : IrrCl (GL (Fin (b i j)) k),
      c j = i → (⟨b i j, u⟩ : IrrGL (k := k)) = W.get j := by
    intro i j
    by_cases hij : c j = i
    · obtain ⟨u, hu⟩ := exists_class_of_degree (b i j) (W.get j) (by rw [hb, if_pos hij])
      exact ⟨u, fun _ => hu⟩
    · exact ⟨(IrrRep.det (Fin (b i j)) 1 isSmoothChar_one).cl, fun h' => absurd h' hij⟩
  choose s₀ hs₀ using hex
  have hfirst : ∀ i, jhMult (piTensor fun j => (s₀ i j).rep.ρ)
      (_root_.GlobalTheory.SmGL.jac (stdBlocks (b i) (hrow i)) (x i).rep) = jmL (sub W c i) (x i).rep := fun i =>
    GlobalTheory.T.jacquet_multiplicity_sublist_padding W c i (fun j => (⟨b i j, s₀ i j⟩ : IrrGL (k := k))) (fun j hj => hs₀ i j hj)
      (fun j hj => hzero i j hj) (hrow i) (x i).rep
  rw [Finset.sum_eq_single s₀]
  · choose z hz e using hcolumn s₀
    have hzW : ∀ j, z j = (W.get j).2 := fun j =>
      class_eq_of_sigma_eq _ _ ((hz j).trans (hs₀ (c j) j rfl))
    have hsecond : jhMult τ.ρ (piTensor fun j =>
        multiProd (stdBlocks (fun i => b i j) (hcol j)) fun i => (s₀ i j).rep.ρ) = 1 := by
      have a : (piTensor fun j => multiProd (stdBlocks (fun i => b i j) (hcol j))
          fun i => (s₀ i j).rep.ρ).Equiv (piTensor fun j => (W.get j).rep) :=
        LocGL.piTensorEquiv fun j => (e j).some.trans (by rw [hzW j]; exact .refl _)
      exact (jhMult_congr_right _ a).trans (jhMult_self hirr)
    rw [hsecond, mul_one]
    exact Finset.prod_congr rfl fun i _ => hfirst i
  · intro s _ hs
    refine mul_eq_zero_of_right _ ?_
    choose z hz e using hcolumn s
    have a : (piTensor fun j => multiProd (stdBlocks (fun i => b i j) (hcol j))
        fun i => (s i j).rep.ρ).Equiv (piTensor fun j => (z j).rep.ρ) :=
      LocGL.piTensorEquiv fun j => (e j).some
    refine (jhMult_congr_right _ a).trans ?_
    by_contra hne
    obtain ⟨φ⟩ := (jhMult_ne_zero_iff.1 hne).nonempty_equiv hirr
      (GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible hBZ k _ _ fun j => (z j).rep)
    have hcl : ∀ j, (W.get j).2 = z j := fun j => by
      have := GlobalTheory.T.tensor_product_determines_factor_classes _ (fun j => GL (Fin (W.get j).1) k) (fun j => (W.get j).2.rep)
        (fun j => (z j).rep) ⟨φ.symm⟩ j
      rwa [IrrCl.cl_rep, IrrCl.cl_rep] at this
    refine hs (funext fun i => funext fun j => ?_)
    by_cases hij : c j = i
    · subst hij
      have h1 : (⟨b (c j) j, s (c j) j⟩ : IrrGL (k := k)) = ⟨b (c j) j, s₀ (c j) j⟩ := by
        rw [hs₀ (c j) j rfl, ← hz j, ← hcl j]
      exact eq_of_heq (Sigma.mk.inj_iff.1 h1).2
    · haveI := subsingleton_irrCl_of_eq_zero (k := k) (b i j) (hzero i j hij)
      exact Subsingleton.elim _ _
  · intro hs
    obtain ⟨i, hi⟩ := hT0 s₀ hs
    exact mul_eq_zero_of_left (Finset.prod_eq_zero (Finset.mem_univ i) hi) _

end GlobalTheory.CompanionTheory.FineProdCell
end
end
