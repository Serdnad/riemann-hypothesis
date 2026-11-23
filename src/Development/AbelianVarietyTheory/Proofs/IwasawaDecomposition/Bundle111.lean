module

public import Formalism.AlgebraicWeights.InertDatumExists
public import Formalism.AlgebraicWeights.IsAlgWeight
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle035
public import Formalism.LocalToGlobal.Columns.GenericUnipotentCharacter
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.Columns.StdLatUnimodular
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle101
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import ReciprocityTheory.Automorphisms.Bundle001
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle047
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Bundle001
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle092

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial Formalism.UG GlobalTheory.SatInd

noncomputable section

open TensorProduct

namespace GlobalTheory.InertUmax

theorem tensor_decomp {K M N : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (b : Module.Basis (Fin 2) K M) (z : M ⊗[K] N) :
    ∃ a c : N, z = b 0 ⊗ₜ[K] a + b 1 ⊗ₜ[K] c := by
  have h := TensorProduct.equivFinsuppOfBasisLeft_symm_apply b
    (TensorProduct.equivFinsuppOfBasisLeft b z)
  rw [LinearEquiv.symm_apply_apply, Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two] at h
  exact ⟨_, _, h⟩

theorem tensor_decomp_zero {K M N : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (b : Module.Basis (Fin 2) K M) (a c : N)
    (h : b 0 ⊗ₜ[K] a + b 1 ⊗ₜ[K] c = 0) : a = 0 ∧ c = 0 := by
  have h' := congrArg (TensorProduct.equivFinsuppOfBasisLeft b) h
  have h0 := DFunLike.congr_fun h' 0
  have h1 := DFunLike.congr_fun h' 1
  simp [map_add (f := _), TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply] at h0 h1
  exact ⟨h0, h1⟩

variable (L : Type) [Field L] [NumberField L] [IsCMField L]

omit [IsCMField L] in
theorem compAt_tmul (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (x : L) (a : AFplus L) :
    compAt L v (x ⊗ₜ[maximalRealSubfield L] a) = x ⊗ₜ[maximalRealSubfield L] (a v) := by
  simp [ReciprocityTheory.Aut.compAt, Algebra.TensorProduct.map_tmul]
  rfl

theorem eq_zero_of_compAt (z : AL L) (hz : ∀ v, compAt L v z = 0) : z = 0 := by
  let b : Module.Basis (Fin 2) (maximalRealSubfield L) L := Module.finBasisOfFinrankEq _ _
    (Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield L) L)
  obtain ⟨A, B, hAB⟩ := tensor_decomp b z
  have hoff : ∀ w, A w = 0 ∧ B w = 0 := by
    intro w
    have h := hz w
    rw [hAB, map_add (f := _), compAt_tmul, compAt_tmul] at h
    exact tensor_decomp_zero b _ _ h
  have hA : A = 0 := by
    apply DFunLike.ext; intro w; exact (hoff w).1
  have hB : B = 0 := by
    apply DFunLike.ext; intro w; exact (hoff w).2
  rw [hAB, hA, hB]; simp


open Classical in
def sgl (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (r : v.adicCompletion (maximalRealSubfield L)) : AFplus L :=
  ⟨Pi.single (M := fun w : HeightOneSpectrum (𝓞 (maximalRealSubfield L)) =>
      w.adicCompletion (maximalRealSubfield L)) v r, by
    refine Filter.mem_of_superset (Set.finite_singleton v).compl_mem_cofinite ?_
    intro w hw
    have hw' : w ≠ v := hw
    simp only [Set.mem_setOf_eq, Pi.single_eq_of_ne hw']
    exact zero_mem _⟩

omit [IsCMField L] in
theorem sgl_same (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (r : v.adicCompletion (maximalRealSubfield L)) : sgl L v r v = r := by
  classical
  exact Pi.single_eq_same (M := fun w : HeightOneSpectrum (𝓞 (maximalRealSubfield L)) =>
      w.adicCompletion (maximalRealSubfield L)) v r

omit [IsCMField L] in
theorem sgl_ne (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (r : v.adicCompletion (maximalRealSubfield L)) {w} (hw : w ≠ v) : sgl L v r w = 0 := by
  classical
  exact Pi.single_eq_of_ne (M := fun w : HeightOneSpectrum (𝓞 (maximalRealSubfield L)) =>
      w.adicCompletion (maximalRealSubfield L)) hw r

omit [IsCMField L] in
theorem one_tmul_sgl_mem (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (r : v.adicCompletion (maximalRealSubfield L))
    (hr : r ∈ v.adicCompletionIntegers (maximalRealSubfield L)) :
    ((1 : L) ⊗ₜ[maximalRealSubfield L] sgl L v r : AL L) ∈ ALint L := by
  refine Subring.subset_closure (Or.inr ⟨sgl L v r, fun w => ?_, rfl⟩)
  rcases eq_or_ne w v with rfl | hw
  · rw [sgl_same]; exact hr
  · rw [sgl_ne L v r hw]; exact zero_mem _


omit [IsCMField L] in
theorem exists_lift (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (y : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L))
    (hy : y ∈ tensInt (F := maximalRealSubfield L) (v.adicCompletion (maximalRealSubfield L))
      (intOE L) (Formalism.UG.Ov (maximalRealSubfield L) v)) :
    ∃ Y ∈ ALint L, compAt L v Y = y := by
  have key : tensInt (F := maximalRealSubfield L) (v.adicCompletion (maximalRealSubfield L))
      (intOE L) (Formalism.UG.Ov (maximalRealSubfield L) v) ≤ (ALint L).map (compAt L v) := by
    rw [tensInt, Subring.closure_le]
    rintro _ (⟨⟨_, s, rfl⟩, rfl⟩ | ⟨r, rfl⟩)
    · refine ⟨(s : L) ⊗ₜ[maximalRealSubfield L] (1 : AFplus L),
        Subring.subset_closure (Or.inl ⟨s, rfl⟩), ?_⟩
      rw [compAt_tmul]; rfl
    · refine ⟨_, one_tmul_sgl_mem L v r r.2, ?_⟩
      rw [compAt_tmul, sgl_same]
  exact key hy

theorem mem_ALint_of_supported (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (x : AL L)
    (hoff : ∀ w, w ≠ v → compAt L w x = 0)
    (hv : compAt L v x ∈ tensInt (F := maximalRealSubfield L)
      (v.adicCompletion (maximalRealSubfield L)) (intOE L) (Formalism.UG.Ov (maximalRealSubfield L) v)) :
    x ∈ ALint L := by
  obtain ⟨Y, hY, hYv⟩ := exists_lift L v _ hv
  have h : x - Y * ((1 : L) ⊗ₜ[maximalRealSubfield L] sgl L v 1) = 0 := by
    apply eq_zero_of_compAt
    intro w
    rw [map_sub, map_mul, compAt_tmul]
    rcases eq_or_ne w v with rfl | hw
    · rw [sgl_same, hYv, ← Algebra.TensorProduct.one_def, mul_one, sub_self]
    · rw [sgl_ne L v 1 hw, hoff w hw, tmul_zero, mul_zero, sub_self]
  rw [sub_eq_zero.1 h]
  exact Subring.mul_mem _ hY (one_tmul_sgl_mem L v 1 (one_mem _))

theorem entries_mem_of_range {K : Type} [Field K] (S : Subring K) {n : ℕ} (P : GL (Fin n) K)
    (hP : P ∈ (Formalism.UG.bc (n := Fin n) S.subtype).range) (i j : Fin n) :
    (P : Matrix (Fin n) (Fin n) K) i j ∈ S := by
  obtain ⟨Q, rfl⟩ := hP
  exact ((Q : Matrix (Fin n) (Fin n) S) i j).2

theorem mem_Umax_of_trivOutside_of_loc_integral : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (z : GAf L n), TrivOutside {v} z → (∀ i j, ((Dv.loc z : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) i j ∈ intL (w.adicCompletion L)) → z ∈ Umax L n := by
  intro L _ _ _ n v w Dv z hz hint i j
  have hP := entries_mem_of_range _ _ Dv.Pint
  have hP' := entries_mem_of_range _ _ (inv_mem Dv.Pint)
  have hg : Formalism.UG.bc (n := Fin n)
      (Dv.e : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) →+* w.adicCompletion L)
      (Matrix.GeneralLinearGroup.map (compAt L v) (z : GL (Fin n) (AL L))) =
      Dv.P * Dv.loc z * Dv.P⁻¹ := by
    unfold InertDatum.loc
    group
  have he : Dv.e (compAt L v ((z.1 : Matrix (Fin n) (Fin n) (AL L)) i j)) ∈
      intL (w.adicCompletion L) := by
    have h1 : Dv.e (compAt L v ((z.1 : Matrix (Fin n) (Fin n) (AL L)) i j)) =
        ((Dv.P * Dv.loc z * Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) :
          Matrix (Fin n) (Fin n) (w.adicCompletion L)) i j := by
      rw [← hg]; rfl
    rw [h1]
    simp only [Units.val_mul, Matrix.mul_apply]
    exact Subring.sum_mem _ fun k _ => Subring.mul_mem _
      (Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hP i l) (hint l k)) (hP' k j)
  have hv := (Dv.integ _).2 he
  have hone : ∀ {R : Type} [CommRing R] (S : Subring R), (1 : Matrix (Fin n) (Fin n) R) i j ∈ S := by
    intro R _ S
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hc : ∀ u, compAt L u ((1 : Matrix (Fin n) (Fin n) (AL L)) i j) =
      (1 : Matrix (Fin n) (Fin n) _) i j := by
    intro u
    simp only [Matrix.one_apply]
    split_ifs <;> simp
  have hd : (z.1 : Matrix (Fin n) (Fin n) (AL L)) i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈
      ALint L := by
    apply mem_ALint_of_supported L v
    · intro u hu
      have h := congrFun (congrFun (hz u hu) i) j
      rw [map_sub, hc, ← h, Matrix.map_apply, sub_self]
    · rw [map_sub, hc]
      exact Subring.sub_mem _ hv (hone _)
  have := Subring.add_mem _ hd (hone (ALint L))
  rwa [sub_add_cancel] at this

end GlobalTheory.InertUmax
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TSetFinLoc

open GlobalTheory.TSetFin

theorem finite_image_tSet_loc : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L)
    (ϖ : s.v.adicCompletion (maximalRealSubfield L)), IsUnif L s.v ϖ → ∀ J : Subgroup (GAf L n),
    (∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ κ ∈ Umax L n)) → ∀ k : ℕ,
    ((fun x : GAf L n => (x : GAf L n ⧸ J)) '' tSet L n s ϖ k).Finite := by
  intro L _ _ _ n s ϖ hϖ J hJ k
  classical
  obtain ⟨c, hc⟩ := approx_class s.v
  haveI : Finite (𝓞 (maximalRealSubfield L) ⧸ s.v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ s.v.ne_bot
  let κ : GAf L n → (Fin n → Fin n → 𝓞 (maximalRealSubfield L) ⧸ s.v.asIdeal) := fun x =>
    if h : x ∈ tSet L n s ϖ k then
      fun i j => c (((h.2.choose : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) :
        Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j)
    else 0
  have key : ∀ x ∈ tSet L n s ϖ k, ∀ x' ∈ tSet L n s ϖ k, κ x = κ x' →
      (x : GAf L n ⧸ J) = x' := by
    intro x hx x' hx' hκ
    simp only [κ, dif_pos hx, dif_pos hx'] at hκ
    obtain ⟨ha, b, hb, hg⟩ := hx.2.choose_spec
    obtain ⟨ha', b', hb', hg'⟩ := hx'.2.choose_spec
    set a := hx.2.choose
    set a' := hx'.2.choose
    have ia := glint_int ha
    have ia' := glint_int ha'
    have ib := glint_int hb
    have ib' := glint_int hb'
    have hcl : ∀ i j, Valued.v ((a : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j -
        (a' : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j) < 1 := fun i j =>
      hc _ _ (ia.1 i j) (ia'.1 i j) (congrFun (congrFun hκ i) j)
    have hcl' : ∀ i j, Valued.v ((a' : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j -
        (a : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j) < 1 := fun i j => by
      rw [← Valuation.map_neg, neg_sub]; exact hcl i j
    have hunif : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
    have h1 := local_int s.v ϖ k hunif a a' b b' _ _ ia'.1 ia.2 ib.2 ib'.1 hcl hg hg'
    have h2 := local_int s.v ϖ k hunif a' a b' b _ _ ia.1 ia'.2 ib'.2 ib.1 hcl' hg' hg
    rw [QuotientGroup.eq]
    have htriv : TrivOutside {s.v} (x⁻¹ * x') := triv_mul (triv_inv hx.1) hx'.1
    refine (hJ _ htriv).2 ?_
    exact mem_Umax_of_loc s _ htriv (fun i j => by
      rw [map_mul, map_inv]; exact h1 i j) (fun i j => by
      rw [mul_inv_rev, inv_inv, map_mul, map_inv]; exact h2 i j)
  let g : GAf L n ⧸ J → (Fin n → Fin n → 𝓞 (maximalRealSubfield L) ⧸ s.v.asIdeal) := fun q =>
    if h : ∃ x ∈ tSet L n s ϖ k, (x : GAf L n ⧸ J) = q then κ h.choose else 0
  refine Set.Finite.of_finite_image (f := g) (Set.toFinite _) ?_
  rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩ hgg
  have h : ∃ y ∈ tSet L n s ϖ k, (y : GAf L n ⧸ J) = x := ⟨x, hx, rfl⟩
  have h' : ∃ y ∈ tSet L n s ϖ k, (y : GAf L n ⧸ J) = x' := ⟨x', hx', rfl⟩
  simp only [g, dif_pos h, dif_pos h'] at hgg
  show (x : GAf L n ⧸ J) = x'
  rw [← h.choose_spec.2, ← h'.choose_spec.2]
  exact key _ h.choose_spec.1 _ h'.choose_spec.1 hgg

end GlobalTheory.TSetFinLoc

end
end

section

open NumberField IsDedekindDomain

namespace GlobalTheory

theorem blkOf_eq_coarse {n r t : ℕ} (hn : n = r + t) :
    (Formalism.L2.DIV.blkOf r t : Fin n → ℕ) = fun a => Formalism.L2.Col.coarse r [t] a.val := by
  funext a
  have ha := a.isLt
  by_cases h : a.val < r
  · rw [Formalism.L2.Col.coarse_of_lt h]; simp [Formalism.L2.DIV.blkOf, h]
  · rw [Formalism.L2.Col.coarse_of_le (Nat.not_lt.mp h)]
    have h2 : a.val - r < t := by omega
    simp [Formalism.L2.DIV.blkOf, h, Formalism.L2.Col.blkIdx, h2, Nat.div_eq_of_lt h2]

theorem twoBlocks_eq_coarse_of_add {n r t : ℕ} (hn : n = r + t) :
    (Formalism.L2.DIV.blk2 r : Fin n → ℕ) = fun a => Formalism.L2.Col.coarse r [t] a.val := by
  funext a
  have ha := a.isLt
  by_cases h : a.val < r
  · rw [Formalism.L2.Col.coarse_of_lt h]; simp [Formalism.L2.DIV.blk2, h]
  · rw [Formalism.L2.Col.coarse_of_le (Nat.not_lt.mp h)]
    have h2 : a.val - r < t := by omega
    simp [Formalism.L2.DIV.blk2, h, Formalism.L2.Col.blkIdx, h2]

theorem lowerBlockDet_coarse_partition_eq_blockDet_upperTri {κ : Type} [CommRing κ] {n r t : ℕ} (g : GL (Fin n) κ)
    (hg : g ∈ Formalism.L2.Col.blockUT n κ r [t]) :
    Formalism.L2.DIV.dBlk (fun a : Fin n => Formalism.L2.Col.coarse r [t] a.val) 1 g =
      Formalism.L2.Col.blkDet n κ (Formalism.L2.Col.coarse r [t]) 1 ⟨g, hg⟩ := by
  have hg' : g ∈ Formalism.L2.DIV.blockTri (fun a : Fin n => Formalism.L2.Col.coarse r [t] a.val) := hg
  apply Units.ext
  rw [Formalism.L2.DIV.diag_block_det_val 1 hg', Formalism.L2.Col.blkDet_val]
  rfl

theorem secondBlockDet_eq_blockDet_of_sum_partitions : ∀ {κ : Type} [CommRing κ] {n r t : ℕ}, n = r + t → ∀ (g : GL (Fin n) κ) (hg : g ∈ Formalism.L2.Col.blockUT n κ r [t]),
    Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf r t) 1 g = Formalism.L2.Col.blkDet n κ (Formalism.L2.Col.coarse r [t]) 1 ⟨g, hg⟩ ∧
      Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blk2 r) 1 g = Formalism.L2.Col.blkDet n κ (Formalism.L2.Col.coarse r [t]) 1 ⟨g, hg⟩ := by
  intro κ _ n r t hn g hg
  refine ⟨?_, ?_⟩
  · rw [blkOf_eq_coarse hn]; exact lowerBlockDet_coarse_partition_eq_blockDet_upperTri g hg
  · rw [twoBlocks_eq_coarse_of_add hn]; exact lowerBlockDet_coarse_partition_eq_blockDet_upperTri g hg

end GlobalTheory
end

section

open NumberField IsDedekindDomain

namespace GlobalTheory

theorem topBlock_eq_one_iff_mem_colHK : ∀ {κ : Type} [CommRing κ] {n r t : ℕ}, n = r + t → ∀ (hr : r ≤ n) (g : GL (Fin n) κ),
    g ∈ Formalism.L2.Col.blockUT n κ r [t] → (Formalism.L2.DIV.upperLeftBlock hr g = 1 ↔ g ∈ Formalism.L2.Col.HK n κ r [t]) := by
  intro κ _ n r t _ hr g hg
  have hb : g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 (n := n) r) := by
    refine Formalism.L2.DIV.mem_blockTri.2 fun i j hij => ?_
    have hji : j.val < r ∧ ¬ i.val < r := by
      unfold Formalism.L2.DIV.blk2 at hij
      by_cases hj : j.val < r <;> by_cases hi : i.val < r <;> simp [hj, hi] at hij ⊢
    refine hg (show Formalism.L2.Col.coarse r [t] j.val < Formalism.L2.Col.coarse r [t] i.val from ?_)
    rw [Formalism.L2.Col.coarse_of_lt hji.1, Formalism.L2.Col.coarse_of_le (Nat.not_lt.mp hji.2)]
    exact Nat.succ_pos _
  rw [Formalism.L2.Col.mem_HK, Units.ext_iff, Formalism.L2.DIV.upper_block_val_submatrix hr hb, Units.val_one]
  constructor
  · intro h
    refine ⟨hg, fun i j hi hj => ?_⟩
    have h1 := congrFun (congrFun h ⟨i.val, hi⟩) ⟨j.val, hj⟩
    simp only [Matrix.submatrix_apply, Matrix.one_apply, Fin.mk.injEq] at h1
    rw [Matrix.one_apply]
    simp only [Fin.ext_iff]
    exact h1
  · rintro ⟨-, h⟩
    ext i j
    rw [Matrix.submatrix_apply, h _ _ i.2 j.2]
    simp [Matrix.one_apply]

end GlobalTheory
end

section

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Formalism.L2.Col GlobalTheory.InertExchange
open Classical

theorem _root_.GlobalTheory.T.exists_prime_pow_smul_le_of_localizations_eq_away : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (A B : Submodule (𝓞 E) (Sp E n)), Submodule.IsLattice E A → Submodule.IsLattice E B → (∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → localization₂ Q.asIdeal A = localization₂ Q.asIdeal B) → ∃ k : ℕ, P.asIdeal ^ k • A ≤ B ∧ P.asIdeal ^ k • B ≤ A := by
  first | exact @GlobalTheory.InertExchange.exists_pow_smul_le_of_locP_eq | exact GlobalTheory.InertExchange.exists_pow_smul_le_of_locP_eq | (intros; apply GlobalTheory.InertExchange.exists_pow_smul_le_of_locP_eq <;> assumption)
end

section

noncomputable section

open NumberField ReciprocityTheory.Aut Formalism.BasicNotions

namespace GlobalTheory.AlgWtF

section Rat

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem includeL_injective : Function.Injective (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L) := by
  haveI : Nontrivial (AFplus L) := Formalism.L2.GlobalTheoryTheory.Br.finiteAdeleRing_nontrivial
  exact Algebra.TensorProduct.includeLeft_injective (S := L) (RingHom.injective _)

abbrev incGL : GL (Fin n) L →* GL (Fin n) (AL L) :=
  Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L)

theorem incGL_injective : Function.Injective (incGL (L := L) (n := n)) := by
  intro a b h
  apply Units.ext
  ext i j
  apply includeL_injective (L := L)
  have := congrArg (fun g : GL (Fin n) (AL L) => (g : Matrix (Fin n) (Fin n) (AL L)) i j) h
  simpa using this

theorem mem_incGL (γ : GQ L n) : ((γ : GA L n) : GL (Fin n) (AL L)) ∈ (GQ0 L n).map incGL :=
  Subgroup.mem_subgroupOf.1 γ.2

def ratFun (γ : GQ L n) : GL (Fin n) L := (Subgroup.mem_map.1 (mem_incGL γ)).choose

theorem ratFun_mem (γ : GQ L n) : ratFun γ ∈ GQ0 L n := (Subgroup.mem_map.1 (mem_incGL γ)).choose_spec.1

theorem incGL_ratFun (γ : GQ L n) :
    incGL (L := L) (n := n) (ratFun γ) = ((γ : GA L n) : GL (Fin n) (AL L)) :=
  (Subgroup.mem_map.1 (mem_incGL γ)).choose_spec.2

def ratHom : GQ L n →* GL (Fin n) L where
  toFun := ratFun
  map_one' := incGL_injective (by rw [incGL_ratFun, map_one]; rfl)
  map_mul' γ δ := incGL_injective (by rw [map_mul, incGL_ratFun, incGL_ratFun, incGL_ratFun]; rfl)

theorem ratHom_mem (γ : GQ L n) : ratHom (L := L) (n := n) γ ∈ GQ0 L n := ratFun_mem γ

theorem ratHom_eq_of_match (γ : GQ L n) (γ₀ : GL (Fin n) L)
    (h : (((γ : GA L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      (γ₀ : Matrix (Fin n) (Fin n) L).map (Algebra.TensorProduct.includeLeftRingHom)) :
    γ₀ = ratHom (L := L) (n := n) γ := by
  apply incGL_injective
  rw [show ratHom (L := L) (n := n) γ = ratFun γ from rfl, incGL_ratFun]
  exact (Units.ext h).symm

end Rat

section Rep

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {ι : Type} [Fintype ι] {K : Type} [Field K]

instance finVV (lam : ι → DomWeight n) : FiniteDimensional K (Formalism.L2.DIV.VV K lam) :=
  Module.Finite.of_basis (Formalism.L2.DIV.bVV K lam)

instance finDualVV (lam : ι → DomWeight n) : FiniteDimensional K (Module.Dual K (Formalism.L2.DIV.VV K lam)) := inferInstance

def embGLF (emb : ι → L →+* K) : GL (Fin n) L →* (ι → GL (Fin n) K) :=
  MonoidHom.pi fun τ => Matrix.GeneralLinearGroup.map (emb τ)

def tenRepF (emb : ι → L →+* K) (lam : ι → DomWeight n) :
    Representation K (GQ L n) (Formalism.L2.DIV.VV K lam) :=
  (Formalism.L2.DIV.rhoK lam).comp ((embGLF emb).comp ratHom)

def wtRepF (emb : ι → L →+* K) (lam : ι → DomWeight n) :
    Representation K (GQ L n) (Module.Dual K (Formalism.L2.DIV.VV K lam)) :=
  (tenRepF emb lam).dual

def CMDist (emb : ι → L →+* K) : Prop :=
  Function.Injective emb ∧ ∀ τ τ', emb τ ≠ (emb τ').comp (IsCMField.complexConj L : L →+* L)

end Rep

end GlobalTheory.AlgWtF
end
end
