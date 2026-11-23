module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1781
public import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1606
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1611
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1773
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1562
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinSubstLinSubst
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegrandIntegrable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle910
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1782
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1783
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import ReciprocityTheory.SemistableReduction.AeBlockSphereEvalNeZero
import ReciprocityTheory.SemistableReduction.Bundle014
import ReciprocityTheory.SemistableReduction.RestBlockSubstIsMultiHomogeneous
import ReciprocityTheory.SemistableReduction.Bundle027
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle002
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory ValuativeRel
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV

noncomputable section
namespace GlobalTheory.FunObj.FlatDep
open GlobalTheory.RootEx

variable {k : Type} [Field k]

theorem stepPt_add {n n' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
    (x₀ a₀ : Matrix n n' k) (u : StepVar n c n' → k) :
    stepPt (x₀ + a₀) u = stepPt x₀ u + fromBlocks a₀ 0 0 0 := by
  ext r s
  rcases r with r | r <;> rcases s with s | s <;> (simp [stepPt, basePt]; try abel)

variable {G : Grid k}

theorem colVar_add (x a : ColArgs G) (u : Vars G) (j : Fin (G.m - 1)) (r : Fin (topRank G (j + 1))) :
    colVar (x + a) u j r = colVar x u j r := by
  simp [colVar, stepPt_add]

theorem rowVar_add (x a : ColArgs G) (u : Vars G) (j : ℕ) (s : Fin (topRank G j)) :
    rowVar (x + a) u j s = rowVar x u j s + if j < G.m - 1 then 0 else a j (topLast G (j + 1)) s := by
  unfold rowVar
  split_ifs with h
  · simp [stepPt_add]
  · simp

theorem ch_add {n n' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
    (x₀ a₀ : Matrix n n' k) (u : StepVar n c n' → k) : ch (stepPt (x₀ + a₀) u) = ch (stepPt x₀ u) := by
  simp [ch, stepPt_add]

theorem phase_add (x a : ColArgs G) (u : Vars G) : phase (x + a) u = phase x u +
    ∑ j : Fin (G.m - 1), if Even (G.m - 2 - j) then ∑ r, (if (j : ℕ) + 1 < G.m - 1 then 0 else
      a (j + 1) (topLast G (j + 1 + 1)) r) * colVar x u j r else 0 := by
  unfold phase
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Pi.add_apply, ch_add]
  by_cases hE : Even (G.m - 2 - (j : ℕ))
  · simp only [if_pos hE, rowVar_add, colVar_add, add_mul, Finset.sum_add_distrib, add_assoc]
  · simp only [if_neg hE, add_zero]

section Loc
variable [ValuativeRel k] (hs : 1 ≤ G.s)

omit [ValuativeRel k] in
theorem mem_opp_theta {j : ℕ} (hj : j < G.m) : Edge.theta G.m j ∈ oppositePath G.m := by
  simp [oppositePath]; omega

omit [ValuativeRel k] in
theorem mem_opp {b : Edge} (hb : b ∈ oppositePath G.m) :
    (∃ i, i < G.m ∧ b = .ex i G.m) ∨ ∃ j, j < G.m ∧ b = .theta G.m j := by
  simp only [oppositePath, List.mem_append, List.mem_map, List.mem_range, List.mem_reverse] at hb
  rcases hb with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
  · exact .inl ⟨i, hi, rfl⟩
  · exact .inr ⟨j, hj, rfl⟩

omit [ValuativeRel k] in
theorem downMap_congr {x x' : ColArgs G} (hx : ∀ j, j < G.m → x j = x' j) (u : Vars G) {j : ℕ} (hj : j < G.m) :
    downMap hs x u j = downMap hs x' u j := by
  unfold downMap; rw [hx j hj]

omit [ValuativeRel k] in
theorem fill_congr {x x' : ColArgs G} {y y' : RowArgs G} (hx : ∀ j, j < G.m → x j = x' j)
    (hy : ∀ i, i < G.m → y i = y' i) (u : Vars G) {b : Edge} (hb : b ∈ oppositePath G.m) :
    fill hs x y u b = fill hs x' y' u b := by
  rcases mem_opp hb with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
  · rw [fill_ex, fill_ex, hy i hi]
  · rw [fill_theta, fill_theta, downMap_congr hs hx u hj]

omit [ValuativeRel k] in
theorem phase_congr {x x' : ColArgs G} (hx : ∀ j, j < G.m → x j = x' j) (u : Vars G) :
    phase x u = phase x' u := by
  unfold phase colVar rowVar
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 := hx j (by have := j.2; omega)
  have h2 := hx (j + 1) (by have := j.2; omega)
  rw [h1, h2]

theorem fromBlocks_le {n n' m m' : Type*} {A : Matrix n n' k} {t : ValueGroupWithZero k}
    (hA : ∀ r s, valuation k (A r s) ≤ t) (r : n ⊕ m) (s : n' ⊕ m') :
    valuation k (fromBlocks A 0 0 (0 : Matrix m m' k) r s) ≤ t := by
  rcases r with r | r <;> rcases s with s | s <;> simp [hA]

theorem fill_sub_le {x a : ColArgs G} {y b : RowArgs G} {t : ValueGroupWithZero k}
    (ha : ∀ j, j < G.m → ∀ r s, valuation k (a j r s) ≤ t) (hb : ∀ i, i < G.m → ∀ r s, valuation k (b i r s) ≤ t)
    (u : Vars G) {c : Edge} (hc : c ∈ oppositePath G.m) (r : Fin (G.rank c.tgt)) (s : Fin (G.rank c.src)) :
    valuation k ((fill hs (x + a) (y + b) u - fill hs x y u) c r s) ≤ t := by
  rcases mem_opp hc with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
  · simp only [Pi.sub_apply, fill_ex, Matrix.sub_apply, transpose_apply, Pi.add_apply, Matrix.add_apply,
      add_sub_cancel_left]
    exact hb i hi s r
  · simp only [Pi.sub_apply, fill_theta, Matrix.sub_apply, transpose_apply]
    unfold downMap
    split_ifs with h h'
    · simp only [reindex_apply, submatrix_apply, Pi.add_apply, stepPt_add, Matrix.add_apply, add_sub_cancel_left]
      exact fromBlocks_le (ha j hj) _ _
    · simp only [submatrix_apply, Pi.add_apply, Matrix.add_apply, add_sub_cancel_left]
      exact ha j hj _ _
    · simp

omit [ValuativeRel k] in
theorem exists_colVar_eq (x : ColArgs G) (y : RowArgs G) (u : Vars G) (j : Fin (G.m - 1))
    (r : Fin (topRank G (j + 1))) : ∃ p q, colVar x u j r = fill hs x y u (.theta G.m j) p q := by
  refine ⟨frame (a := topRank G j) (c := G.m - 2 - j + 1) (b := G.rank (G.m, j)) (by have := topRank_add hs j; have := j.2; omega)
      (.inr ⟨(G.m - 2 - j) / 2, by omega⟩),
    frame (a := topRank G (j + 1)) (c := G.m - 2 - j) (b := G.rank (G.m, j + 1)) (by have := topRank_add hs (j + 1); have := j.2; omega) (.inl r), ?_⟩
  rw [fill_theta, transpose_apply, downMap, dite_eq_left j.2]
  simp only [reindex_apply, submatrix_apply, Equiv.symm_apply_apply, colVar, Fin.eta]

end Loc
end GlobalTheory.FunObj.FlatDep

open GlobalTheory.FunObj.FlatDep in
theorem GlobalTheory.FunObj.FlatDep.flatTensor_dep_and_per : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (G : Grid k) (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k) (ϖ : kˣ) (e : ℕ) (T : G.Args → ℂ) (keep : Bool) (g : G.VertexGroup), IsUnif ϖ → HasConductor ψ 1 → G.IsTensor ϖ e (oppositePath G.m) T → (∀ (x x' : ColArgs G) (y y' : RowArgs G), (∀ j, j < G.m → x j = x' j) → (∀ i, i < G.m → y i = y' i) → flatTensor hs ψ ν (moved G keep g T) x y = flatTensor hs ψ ν (moved G keep g T) x' y') ∧ ∃ n : ℕ, ∀ (x a : ColArgs G) (y b : RowArgs G), (∀ j, j < G.m → ∀ r s, valuation k (a j r s) ≤ valuation k ((ϖ ^ n : kˣ) : k)) → (∀ i, i < G.m → ∀ r s, valuation k (b i r s) ≤ valuation k ((ϖ ^ n : kˣ) : k)) → flatTensor hs ψ ν (moved G keep g T) (x + a) (y + b) = flatTensor hs ψ ν (moved G keep g T) x y := by
  intro k _ _ _ _ _ _ G hs ψ ν ϖ e T keep g hϖ hψ hT
  obtain ⟨n, hA, hB⟩ := GlobalTheory.T.gridMovedTensor_bounded_support_locallyConstant G ϖ e T keep g hϖ hT
  refine ⟨fun x x' y y' hx hy => ?_, n, fun x a y b ha hb => ?_⟩
  · unfold flatTensor
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [flatIntegrand]
    rw [phase_congr hx u]
    have hTe : T (G.moveArgs .one g (fill hs x y u)) = T (G.moveArgs .one g (fill hs x' y' u)) :=
      hT.1 fun c hc => by simp only [Grid.moveArgs, fill_congr hs hx hy u hc]
    simp only [moved, Grid.pathAct, hTe]
  · unfold flatTensor
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [flatIntegrand]
    have hS : moved G keep g T (fill hs (x + a) (y + b) u) = moved G keep g T (fill hs x y u) := by
      have h := hB (fill hs x y u) (fill hs (x + a) (y + b) u - fill hs x y u)
        fun c hc r s => fill_sub_le hs ha hb u hc r s
      rwa [add_sub_cancel] at h
    rw [hS]
    by_cases h0 : moved G keep g T (fill hs x y u) = 0
    · simp [h0]
    have hbd := hA _ h0
    have hD : ∀ (j : Fin (G.m - 1)) r, valuation k ((if (j : ℕ) + 1 < G.m - 1 then 0 else
        a (j + 1) (topLast G (j + 1 + 1)) r) * colVar x u j r) ≤ 1 := by
      intro j r
      have := j.2
      split_ifs with h
      · simp
      · obtain ⟨p, q, hpq⟩ := exists_colVar_eq hs x y u j r
        rw [map_mul, hpq]
        calc _ ≤ valuation k ((ϖ ^ n : kˣ) : k) * valuation k (((ϖ ^ n)⁻¹ : kˣ) : k) :=
              mul_le_mul' (ha _ (by omega) _ _) (hbd _ (mem_opp_theta (by omega)) _ _)
          _ = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    have hsum : valuation k (-(∑ j : Fin (G.m - 1), if Even (G.m - 2 - j) then ∑ r, (if (j : ℕ) + 1 < G.m - 1 then 0
        else a (j + 1) (topLast G (j + 1 + 1)) r) * colVar x u j r else 0)) ≤ valuation k ((1 : kˣ) : k) := by
      rw [Valuation.map_neg, Units.val_one, map_one]
      refine (valuation k).map_sum_le fun j _ => ?_
      by_cases hE : Even (G.m - 2 - (j : ℕ))
      · rw [if_pos hE]; exact (valuation k).map_sum_le fun r _ => hD j r
      · rw [if_neg hE, map_zero]; exact zero_le'
    rw [phase_add, neg_add, AddChar.map_add_eq_mul, (hψ 1).2 le_rfl _ hsum, mul_one]
end
end

section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace GlobalTheory.HSShort.DetTop

theorem exists_rightInv {F : Type} [Field F] {N n : ℕ} (w : Matrix (Fin N) (Fin n) F)
    (hw : Submodule.span F (Set.range w.col) = ⊤) : ∃ w' : Matrix (Fin n) (Fin N) F, w * w' = 1 := by
  have hr : LinearMap.range w.mulVecLin = ⊤ := by
    rw [Matrix.range_mulVecLin]; exact hw
  obtain ⟨g', hg'⟩ := w.mulVecLin.exists_rightInverse_of_surjective hr
  refine ⟨LinearMap.toMatrix' g', ?_⟩
  have := congrArg LinearMap.toMatrix' hg'
  rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id] at this
  have e : LinearMap.toMatrix' w.mulVecLin = w := LinearMap.toMatrix'_toLin' w
  rwa [e] at this

theorem linSubst_det {F : Type} [Field F] {B N n d : ℕ} (w : Matrix (Fin N) (Fin n) F)
    (P : Matrix (Fin d) (Fin d) (MvPolynomial (Fin B × Fin N) F)) :
    linSubst w P.det = (P.map (linSubst w)).det := by
  have := RingHom.map_det (aeval (fun p : Fin B × Fin N => ∑ k, C (w p.2 k) * X (p.1, k)) :
    MvPolynomial (Fin B × Fin N) F →ₐ[F] MvPolynomial (Fin B × Fin n) F).toRingHom P
  exact this

end GlobalTheory.HSShort.DetTop

namespace GlobalTheory.HSShort.DetTop

theorem arch {F V : Type} [Field F] [AddCommGroup V] [Module F V] (nm : HermFam F V) {d : ℕ}
    (b : Module.Basis (Fin d) F V) {B N : ℕ} (hN : 0 < N) (σ : F →+* ℂ) (A : Matrix (Fin N) (Fin N) ℂ)
    (hA : A.det ≠ 0) (P : Matrix (Fin d) (Fin d) (MvPolynomial (Fin B × Fin N) F)) (a : Fin B → ℕ)
    (Bd : Fin d → ℝ) (hP : P.det ≠ 0) (hhom : IsMultiHomogeneous a P.det) (hBd : ∀ k, 0 < Bd k)
    (hbd : ∀ k (u : Fin B × Fin N → ℂ), (∀ i, frameNorm A (fun j => u (i, j)) = 1) →
      cnrm nm σ (fun i => eval₂ σ u (P i k)) b ≤ Bd k) :
    blockSphereMean B N (linSubst A (map σ P.det)) ≤
      ∑ k, Real.log (Bd k) - Real.log (nm.gram σ b).det.re / 2 := by
  haveI := blockSphereMeasure_isProbability (B := B) hN
  have hmap0 : map σ P.det ≠ 0 := fun h =>
    hP (MvPolynomial.map_injective σ σ.injective (by rw [h, map_zero]))
  have hf0 : linSubst A (map σ P.det) ≠ 0 :=
    GlobalTheory.HeightUnique.linSubst_ne_zero (Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.2 hA)) hmap0
  have hfm : IsMultiHomogeneous a (linSubst A (map σ P.det)) :=
    GlobalTheory.HeightUnique.linSubst_homog A (isMultiHomogeneous_map_ring a _ hhom σ)
  have hint := Closed.sphereLogIntegrable B N a _ hf0 hfm
  have hae := ae_blockSphere_eval_ne_zero B N a _ hf0 hfm
  have hpt : ∀ z : BlockSphere B N, eval (blockPoint z) (linSubst A (map σ P.det)) ≠ 0 →
      Real.log ‖eval (blockPoint z) (linSubst A (map σ P.det))‖ ≤
        ∑ k, Real.log (Bd k) - Real.log (nm.gram σ b).det.re / 2 := by
    intro z hz
    set u : Fin B × Fin N → ℂ := fun q => A.mulVec (fun k => blockPoint z (q.1, k)) q.2 with hu
    have hunit : ∀ i, frameNorm A (fun j => u (i, j)) = 1 := fun i => by
      show frameNorm A (A.mulVec (fun k => blockPoint z (i, k))) = 1
      rw [GlobalTheory.MaxPoint.frameNorm_mulVec hA]
      have hz := (z i).2
      rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq] at hz
      simpa [blockPoint, spherePoint] using hz
    have hev : eval (blockPoint z) (linSubst A (map σ P.det)) = (Matrix.of fun i k => eval₂ σ u (P i k)).det := by
      rw [GlobalTheory.MaxPoint.eval_linSubst, MvPolynomial.eval_map]
      have := RingHom.map_det (eval₂Hom σ u) P
      rw [coe_eval₂Hom] at this
      rw [this]; rfl
    rw [hev] at hz ⊢
    obtain ⟨hG, hH⟩ := GlobalTheory.T.hadamard_ineq_complex_combinations_basis F V nm d b σ (Matrix.of fun i k => eval₂ σ u (P i k))
    have hprod : ∏ k, cnrm nm σ (fun i => (Matrix.of fun i k => eval₂ σ u (P i k)) i k) b ≤ ∏ k, Bd k :=
      Finset.prod_le_prod₀ (fun k _ => Real.sqrt_nonneg _) (fun k _ => hbd k u hunit)
    have hpos : 0 < ‖(Matrix.of fun i k => eval₂ σ u (P i k)).det‖ := norm_pos_iff.2 hz
    have hsq : 0 < Real.sqrt (nm.gram σ b).det.re := Real.sqrt_pos.2 hG
    have hle := Real.log_le_log (mul_pos hpos hsq) (hH.trans hprod)
    rw [Real.log_mul hpos.ne' hsq.ne', Real.log_prod (fun k _ => (hBd k).ne'), Real.log_sqrt hG.le] at hle
    linarith
  unfold blockSphereMean
  calc ∫ z, Real.log ‖eval (blockPoint z) (linSubst A (map σ P.det))‖ ∂(blockSphereProb B N)
      ≤ ∫ _z, (∑ k, Real.log (Bd k) - Real.log (nm.gram σ b).det.re / 2) ∂(blockSphereProb B N) :=
        integral_mono_ae hint (integrable_const _) (by
          filter_upwards [hae] with z hz
          exact hpt z hz)
    _ = _ := by simp

end GlobalTheory.HSShort.DetTop

theorem GlobalTheory.HSShort.deg_ge_ht_det : ∀ (F V : Type) [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] (nm : HermFam F V) (M : Submodule (𝓞 F) V) (d : ℕ) (b : Module.Basis (Fin d) F V), IsFull M → ∀ (B N n : ℕ) (w : Matrix (Fin N) (Fin n) F) (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) (Λ : ℝ), Lat w A Λ → ∀ (P : Matrix (Fin d) (Fin d) (MvPolynomial (Fin B × Fin N) F)) (a : Fin B → ℕ) (Bd : Fin d → ℝ), P.det ≠ 0 → IsMultiHomogeneous a P.det → (∀ k, 0 < Bd k) → (∀ k m, ∑ i, AddMonoidAlgebra.coeff (linSubst w (P i k)) m • b i ∈ M) → (∀ k σ (u : Fin B × Fin N → ℂ), (∀ i, frameNorm (A σ) (fun j => u (i, j)) = 1) → cnrm nm σ (fun i => eval₂ σ u (P i k)) b ≤ Bd k) → ht w A P.det - ∑ k, Real.log (Bd k) ≤ deg nm M := by
  intro F V _ _ _ _ _ _ nm M d b hM B N n w A Λ hL P a Bd hP hhom hBd hcoef hbd
  obtain ⟨w', hw'⟩ := GlobalTheory.HSShort.DetTop.exists_rightInv w hL.spans
  have hdet := GlobalTheory.HSShort.DetTop.linSubst_det w P
  have hg0 : linSubst w P.det ≠ 0 := GlobalTheory.HeightUnique.linSubst_ne_zero hw' hP
  have hcg : ∀ m, AddMonoidAlgebra.coeff (linSubst w P.det) m ∈
      Submodule.span (𝓞 F) {y | ∃ v : Fin d → V, (∀ i, v i ∈ M) ∧ y = b.det v} := by
    rw [hdet]
    exact GlobalTheory.T.coeff_det_mem_span_det_integral_polynomial_vectors F V M d b _ (P.map (linSubst w)) (fun k m => by simpa using hcoef k m)
  have hfin := GlobalTheory.T.finiteHeight_sub_mean_le_degree_fullLattice_detIdeal F V nm M d b hM _ _ hg0 hcg
  have harch : ∀ σ, blockSphereMean B N (linSubst (A σ) (map σ P.det)) ≤
      ∑ k, Real.log (Bd k) - Real.log (nm.gram σ b).det.re / 2 := fun σ =>
    GlobalTheory.HSShort.DetTop.arch nm b hL.pos σ (A σ) (hL.det σ) P a Bd hP hhom hBd (fun k u hu => hbd k σ u hu)
  have hr : (0 : ℝ) < Module.finrank ℚ F := by exact_mod_cast Module.finrank_pos
  have hcard : (Fintype.card (F →+* ℂ) : ℝ) = Module.finrank ℚ F := by
    exact_mod_cast NumberField.Embeddings.card F ℂ
  have hht : ht w A P.det = finPart (linSubst w P.det) +
      mean F (fun σ => blockSphereMean B N (linSubst (A σ) (map σ P.det))) := by
    simp only [ht, formHeight, finPart, mean, Nat.cast_zero, mul_zero, zero_mul, zero_div, add_zero]
    rw [add_div]
  have hmean : mean F (fun σ => blockSphereMean B N (linSubst (A σ) (map σ P.det))) ≤
      ∑ k, Real.log (Bd k) - mean F (fun σ => Real.log (nm.gram σ b).det.re) / 2 := by
    unfold mean
    calc (∑ σ, blockSphereMean B N (linSubst (A σ) (map σ P.det))) / (Module.finrank ℚ F : ℝ)
        ≤ (∑ σ : F →+* ℂ, (∑ k, Real.log (Bd k) - Real.log (nm.gram σ b).det.re / 2)) / (Module.finrank ℚ F : ℝ) :=
          div_le_div_of_nonneg_right (Finset.sum_le_sum fun σ _ => harch σ) hr.le
      _ = _ := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard, ← Finset.sum_div]
          field_simp
  rw [hht]
  linarith
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.FunObj.ProdOpen

open Filter Topology

variable {D : D7}

theorem mem_GLint_of_entries {L : Type} [Field L] {n : ℕ} (O : Subring L) (g : GL (Fin n) L)
    (h1 : ∀ i j, g.1 i j ∈ O) (h2 : ∀ i j, g⁻¹.1 i j ∈ O) : g ∈ Formalism.UG.GLint (Fin n) O := by
  have hi : Function.Injective fun A : Matrix (Fin n) (Fin n) O => A.map O.subtype :=
    Matrix.map_injective Subtype.val_injective
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, hi ?_, hi ?_⟩, Units.ext rfl⟩
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.mul_inv
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.inv_mul

theorem inBasis_apply {n n' : ℕ} (h : n' = n) (β x : GL (Fin n) (Lev.EAf D)) (w : Pl D.host.E) (i j : Fin n') :
    (inBasis h β w x).1 i j = cpt w ((β⁻¹ * x * β).1 (finCongr h i) (finCongr h j)) := rfl

theorem inBasis_mem_KO {n : ℕ} (β x : GL (Fin n) (Lev.EAf D)) (hx : x ∈ St β) (w : Pl D.host.E) :
    inBasis rfl β w x ∈ KO (Kw w) (Fin n) := by
  obtain ⟨y, rfl⟩ := hx
  rw [GlobalTheory.SmGL.SphCompletion.KO_completion w n]
  have hm : ∀ z : GL (Fin n) (Lev.EAf D), z ∈ ({Formalism.L2.DIV.intGL _ _ n y, (Formalism.L2.DIV.intGL _ _ n y)⁻¹} : Set _) →
      ∀ a b, cpt w (z.1 a b) ∈ Formalism.UG.Ov D.host.E w := by
    intro z hz a b
    refine (mem_OA_iff _).1 ?_ w
    rcases hz with rfl | rfl
    · exact (y.1 a b).2
    · rw [← map_inv]; exact ((y⁻¹).1 a b).2
  have e1 : β⁻¹ * Formalism.L2.DIV.frGL β y * β = Formalism.L2.DIV.intGL _ _ n y := by
    simp only [Formalism.L2.DIV.frGL, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, MulAut.conj_apply]
    group
  have e2 : β⁻¹ * (Formalism.L2.DIV.frGL β y)⁻¹ * β = (Formalism.L2.DIV.intGL _ _ n y)⁻¹ := by
    rw [← e1]; group
  refine mem_GLint_of_entries _ _ (fun i j => ?_) (fun i j => ?_)
  · rw [inBasis_apply, e1]; exact hm _ (Or.inl rfl) _ _
  · rw [← map_inv, inBasis_apply, e2]; exact hm _ (Or.inr rfl) _ _

theorem tendsto_inBasis_val (V : HSp D) {n' : ℕ} (h : n' = V.rank) (β : GL (Fin V.rank) (Lev.EAf D)) (w : Pl D.host.E) :
    Tendsto (fun κ : GA D V => ((inBasis h β w (Lev.finE V κ)).1 : Matrix (Fin n') (Fin n') (Kw w))) (𝓝 1) (𝓝 1) := by
  obtain ⟨π, hπ, -⟩ := GlobalTheory.Mass.existsUnique_isFinProj D.sp.cm.sig V.gram
  have hf : Continuous (finHom V) := (continuous_subtype_val.comp hπ.continuous).congr fun κ => hπ κ
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => Metric.tendsto_nhds.2 fun ε hε => ?_
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε (GlobalTheory.LocalData.norm_resChar_lt_one w)
  have hN : Formalism.MainNotions.S.Loc.resChar w ^ k ≠ 0 := pow_ne_zero _ (GlobalTheory.LocalData.resChar_prime w).ne_zero
  filter_upwards [eventually_cong_mat β hN hf (map_one _)] with κ ⟨z, hz, e⟩
  change (β⁻¹ * Lev.finE V κ * β).1 - 1 = _ at e
  have e2 := congr_fun (congr_fun e (finCongr h i)) (finCongr h j)
  rw [Matrix.sub_apply, Matrix.smul_apply, sub_eq_iff_eq_add] at e2
  have e3 : cpt w ((1 : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) (finCongr h i) (finCongr h j)) =
      (1 : Matrix (Fin n') (Fin n') (Kw w)) i j := by
    simp only [Matrix.one_apply, (finCongr h).injective.eq_iff]
    split_ifs <;> simp
  have hz1 : ‖cpt w (z (finCongr h i) (finCongr h j))‖ ≤ 1 :=
    Valued.toNormedField.norm_le_one_iff.2 ((mem_OA_iff _).1 (hz _ _) w)
  rw [dist_eq_norm, inBasis_apply, e2, map_add (f := _), e3, add_sub_cancel_right, map_nsmul, nsmul_eq_mul, norm_mul,
    Nat.cast_pow, norm_pow]
  calc ‖((Formalism.MainNotions.S.Loc.resChar w : ℕ) : Kw w)‖ ^ k * ‖cpt w (z (finCongr h i) (finCongr h j))‖
      ≤ ‖((Formalism.MainNotions.S.Loc.resChar w : ℕ) : Kw w)‖ ^ k * 1 := by gcongr
    _ < ε := by rwa [mul_one]

theorem tendsto_inBasis (V : HSp D) {n' : ℕ} (h : n' = V.rank) (β : GL (Fin V.rank) (Lev.EAf D)) (w : Pl D.host.E) :
    Tendsto (fun κ : GA D V => inBasis h β w (Lev.finE V κ)) (𝓝 1) (𝓝 1) := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  rw [Units.isInducing_embedProduct.tendsto_nhds_iff]
  have hinv : Tendsto (fun κ : GA D V => κ⁻¹) (𝓝 1) (𝓝 1) := by
    simpa using (continuous_inv.tendsto (1 : GA D V))
  have h2 : Tendsto (fun κ : GA D V => ((inBasis h β w (Lev.finE V κ))⁻¹).1) (𝓝 1) (𝓝 1) := by
    have := (tendsto_inBasis_val V h β w).comp hinv
    refine this.congr fun κ => ?_
    simp only [Function.comp_apply, map_inv]
  have h3 := (tendsto_inBasis_val V h β w).prodMk_nhds (MulOpposite.continuous_op.tendsto _ |>.comp h2)
  convert h3 using 2
  · ext <;> simp [Units.embedProduct]
  · rw [map_one]; rfl

theorem isOpen_comap_prodLev : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (P : Finset (Pl D.host.E)) {n' : P → ℕ}
    (h : ∀ w, n' w = V.rank) (K : ∀ w : P, Subgroup (GL (Fin (n' w)) (Kw w.1))),
    (∀ w, IsOpen (K w : Set (GL (Fin (n' w)) (Kw w.1)))) →
      IsOpen (((prodLev β P h K).comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V)) := by
  intro D V β P n' h K hK
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  have hP : ∀ w : P, ∀ᶠ κ in 𝓝 (1 : GA D V), inBasis (h w) β w (Lev.finE V κ) ∈ K w := fun w =>
    tendsto_inBasis V (h w) β w.1 ((hK w).mem_nhds (one_mem _))
  filter_upwards [GlobalTheory.ThetaIntegrand.eventually_princ V β ∅, Filter.eventually_all.2 hP] with κ hh h3
  exact Subgroup.mem_inf.2 ⟨Subgroup.mem_iInf.2 h3,
    Subgroup.mem_iInf.2 fun w' => Subgroup.mem_iInf.2 fun _ => inBasis_mem_KO β _ hh.2.1 w'⟩

end GlobalTheory.FunObj.ProdOpen
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem _root_.GlobalTheory.T.subsingleton_Ht_two_of_isDedekindDomain_of_isAlgClosed : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ i : ℤ, Subsingleton (Ht q (sp B) 2 i) := by
  first | (exact @GlobalTheory.EtC.smoothAffineCurve_tateTwistCohomology_two_subsingleton) | (exact GlobalTheory.EtC.smoothAffineCurve_tateTwistCohomology_two_subsingleton) | (intros; apply GlobalTheory.EtC.smoothAffineCurve_tateTwistCohomology_two_subsingleton <;> assumption)
end

section

open GlobalTheory.PsCo.Pc1

theorem _root_.GlobalTheory.T.maximalCompact_pseudoCoefficientData : StKData := by
  first | exact @GlobalTheory.PsCo.Pc1.maximalCompact_pseudoCoefficientData' | exact GlobalTheory.PsCo.Pc1.maximalCompact_pseudoCoefficientData' | (intros; apply GlobalTheory.PsCo.Pc1.maximalCompact_pseudoCoefficientData' <;> assumption)
end

section

namespace GlobalTheory.PsCo.Pc3

theorem uFin : UFin := GlobalTheory.T.uniformFiniteness_of_reproducingPolynomial_averaging GlobalTheory.T.exists_reproducingPolynomial_valueAtOne_maxCompact GlobalTheory.T.exists_finiteDim_stable_polyAverages_weights

end GlobalTheory.PsCo.Pc3
end
