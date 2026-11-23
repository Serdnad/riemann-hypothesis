module

public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.MajorantInvolutionDiagonalForm
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Statements
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle010
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle075
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle015
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle014
import GroundTheory.AutomorphicForms.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix
open scoped ComplexOrder

theorem majorant_cauchySchwarz {ι : Type*} [Fintype ι] [DecidableEq ι] {H P : Matrix ι ι ℂ}
    (hM : IsMajorantOf H P) (a b : ι → ℂ) :
    ‖star a ⬝ᵥ (H *ᵥ b)‖ ≤
      Real.sqrt (star a ⬝ᵥ (P *ᵥ a)).re * Real.sqrt (star b ⬝ᵥ (P *ᵥ b)).re := by
  have key := majorant_mul_inv_mul hM
  obtain ⟨hP, hH, hdet, hPHP⟩ := hM
  have hPdet : IsUnit P.det := isUnit_iff_ne_zero.mpr (ne_of_gt hP.det_pos)
  set c := P⁻¹ *ᵥ (H *ᵥ b) with hc
  have h1 : P *ᵥ c = H *ᵥ b := by
    rw [hc, mulVec_mulVec, Matrix.mul_nonsing_inv _ hPdet, one_mulVec]
  have hPinv : (P⁻¹)ᴴ = P⁻¹ := by rw [conjTranspose_nonsing_inv, hP.1.eq]
  have h2 : star c ⬝ᵥ (P *ᵥ c) = star b ⬝ᵥ (P *ᵥ b) := by
    rw [h1, hc, star_mulVec, star_mulVec, hPinv, hH.eq, vecMul_vecMul, ← dotProduct_mulVec,
      mulVec_mulVec, key]
  let _ := P.toSeminormedAddCommGroup hP.posSemidef
  let _ := P.toInnerProductSpace hP.posSemidef
  have cs := inner_mul_inner_self_le (𝕜 := ℂ) a c
  have e1 : (inner ℂ a c : ℂ) = star a ⬝ᵥ (H *ᵥ b) := by
    change (P *ᵥ c) ⬝ᵥ star a = _
    rw [dotProduct_comm, h1]
  have e2 : (inner ℂ c a : ℂ) = star (star a ⬝ᵥ (H *ᵥ b)) := by
    rw [← e1]; exact (inner_conj_symm (𝕜 := ℂ) c a).symm
  have e3 : (inner ℂ a a : ℂ) = star a ⬝ᵥ (P *ᵥ a) := by
    change (P *ᵥ a) ⬝ᵥ star a = _
    rw [dotProduct_comm]
  have e4 : (inner ℂ c c : ℂ) = star b ⬝ᵥ (P *ᵥ b) := by
    change (P *ᵥ c) ⬝ᵥ star c = _
    rw [dotProduct_comm, h2]
  rw [e1, e2, e3, e4, norm_star] at cs
  simp only [RCLike.re_to_complex] at cs
  have ha : 0 ≤ (star a ⬝ᵥ (P *ᵥ a)).re := hP.posSemidef.re_dotProduct_nonneg a
  have hb : 0 ≤ (star b ⬝ᵥ (P *ᵥ b)).re := hP.posSemidef.re_dotProduct_nonneg b
  rw [← Real.sqrt_mul ha]
  exact Real.le_sqrt_of_sq_le (by nlinarith)

section Places

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem Majorant.isMajorantOf {h : HermitianForm F E W} {v : Basis ι E W} (M : Majorant h v)
    (w : InfinitePlace E) : IsMajorantOf (gramAt h v w) (M.P w) :=
  ⟨M.posDef w, (GramAtData.proof h v w).1, (GramAtData.proof h v w).2, M.siegel w⟩


omit [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem Majorant.sqrt_le_len {h : HermitianForm F E W} {v : Basis ι E W} (M : Majorant h v)
    (y : InfinitePlace E → ι → ℂ) (w : InfinitePlace E) :
    Real.sqrt (star (y w) ⬝ᵥ (M.P w *ᵥ y w)).re ≤ M.len y := by
  unfold Majorant.len
  exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun w => (star (y w) ⬝ᵥ (M.P w *ᵥ y w)).re)
    (fun u _ => LenSq.re_nonneg (M.posDef u) (y u)) (Finset.mem_univ w))

theorem LenCauchySchwarz.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    LenCauchySchwarz.Statement h v := by
  intro M g x y w
  rw [HermAtPlace.proof h v w x y, ← ArchInvariant.proof h v g (vecAt v x) (vecAt v y) w]
  refine (majorant_cauchySchwarz (M.isMajorantOf w) _ _).trans ?_
  exact mul_le_mul (M.sqrt_le_len _ w) (M.sqrt_le_len _ w) (Real.sqrt_nonneg _)
    ((Real.sqrt_nonneg _).trans (M.sqrt_le_len _ w))

end Places

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped Pointwise ComplexOrder ENNReal

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem vecAt_unitary (h : HermitianForm F E W) (v : Basis ι E W) (γ : h.unitaryGroup) (x : W)
    (w : InfinitePlace E) :
    vecAt v ((γ : W ≃ₗ[E] W) x) w =
      (((archEmbed h v γ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ
        vecAt v x w := by
  have h1 : (((archEmbed h v γ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) =
      (LinearMap.toMatrix v v ((γ : W ≃ₗ[E] W) : W →ₗ[E] W)).map w.embedding := by
    rw [← unitaryGroupEquivMatrix_apply]
    rfl
  have h2 := LinearMap.toMatrix_mulVec_repr v v ((γ : W ≃ₗ[E] W) : W →ₗ[E] W) x
  rw [LinearEquiv.coe_coe] at h2
  rw [h1]
  ext i
  simp only [vecAt]
  rw [← h2, RingHom.map_mulVec]
  rfl

theorem invApply_archEmbed_mul (h : HermitianForm F E W) (v : Basis ι E W) (γ : h.unitaryGroup)
    (g : archUnitary h v) (x : W) :
    invApply (archEmbed h v γ * g) (vecAt v ((γ : W ≃ₗ[E] W) x)) = invApply g (vecAt v x) := by
  funext w
  simp only [invApply, vecAt_unitary, Subgroup.coe_mul, Subgroup.coe_inv, Pi.mul_apply, Pi.inv_apply,
    Matrix.mulVec_mulVec]
  rw [_root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]

theorem MahlerCompactness.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (hB : BoundedGenerators.Statement h v) (hCS : LenCauchySchwarz.Statement h v)
    (hG : GramDetermines.Statement h) (hK : BoundedInverseCompact.Statement h v) :
    MahlerCompactness.Statement h v := by
  intro M D t ht
  obtain ⟨n, C, hC⟩ := hB M D t ht

  let P : Set (AddSubgroup W × (Fin n → W)) := {p | IsDIntegral h D p.1 ∧
    AddSubgroup.closure (Set.range p.2) = p.1 ∧
      ∃ g : archUnitary h v, ∀ a, M.len (invApply g (vecAt v (p.2 a))) ≤ C}
  let gr : (Fin n → W) → Matrix (Fin n) (Fin n) E := fun e a b => h.toSesq (e a) (e b)
  let T : Set (Matrix (Fin n) (Fin n) E) := (fun p => gr p.2) '' P
  have hT : T.Finite := by
    refine (Set.Finite.pi (t := fun _ : Fin n => Set.pi Set.univ fun _ : Fin n =>
      {x : E | IsIntegral ℤ x ∧ ∀ φ : E →+* ℂ, ‖φ x‖ ≤ C * C})
      fun _ => Set.Finite.pi fun _ => Embeddings.finite_of_norm_le E ℂ (C * C)).subset ?_
    rintro _ ⟨p, ⟨hD, hcl, g, hg⟩, rfl⟩
    intro a _ b _
    have hmem : ∀ c, p.2 c ∈ p.1 := fun c => hcl ▸ AddSubgroup.subset_closure ⟨c, rfl⟩
    refine Set.mem_ofPred.2 ⟨(mem_integralClosure_iff ℤ E).1 (hD.integral _ (hmem a) _ (hmem b)), fun φ => ?_⟩
    have h1 := hCS M g (p.2 a) (p.2 b) (InfinitePlace.mk φ)
    rw [InfinitePlace.norm_embedding_eq, InfinitePlace.apply] at h1
    exact h1.trans (mul_le_mul (hg a) (hg b) (Real.sqrt_nonneg _) ((Real.sqrt_nonneg _).trans (hg a)))
  have hrep : ∀ H ∈ T, ∃ p ∈ P, gr p.2 = H := fun H ⟨p, hp, hH⟩ => ⟨p, hp, hH⟩
  choose! rep hrepP hrepG using hrep
  let Kset : (Fin n → W) → Set (archUnitary h v) :=
    fun e => {g | ∀ a, M.len (invApply g (vecAt v (e a))) ≤ C}
  refine ⟨(fun H => (rep H).1) '' T, hT.image _, ⋃ H ∈ T, Kset (rep H).2,
    hT.isCompact_biUnion fun H hH => hK M n (rep H).2 ?_ C, ?_⟩
  · obtain ⟨hD, hcl, -⟩ := hrepP H hH
    have hsp := hD.isLattice.span_eq_top
    rw [← hcl] at hsp
    rw [eq_top_iff, ← hsp]
    refine Submodule.span_le.2 fun x hx => ?_
    exact (AddSubgroup.closure_le (Submodule.span E (Set.range (rep H).2)).toAddSubgroup).2
      Submodule.subset_span hx
  · intro La g hLa hmin
    obtain ⟨e, he, heC⟩ := hC La g hLa hmin
    have hH : gr e ∈ T := ⟨(La, e), ⟨hLa, he, g, heC⟩, rfl⟩
    obtain ⟨hD', hcl', -⟩ := hrepP _ hH
    have hgr := hrepG _ hH
    obtain ⟨γ, hγ⟩ := hG n e (rep (gr e)).2 (he ▸ hLa.isLattice) (hcl' ▸ hD'.isLattice)
      fun a b => (congrFun (congrFun hgr a) b).symm
    refine ⟨γ, ⟨gr e, hH, ?_⟩, Set.mem_biUnion hH fun a => ?_⟩
    · show (rep (gr e)).1 = γ • La
      rw [← hcl', ← he, Subgroup.smul_def, AddSubgroup.pointwise_smul_def]
      erw [AddMonoidHom.map_closure]
      rw [← Set.range_comp]
      exact congrArg (fun s => AddSubgroup.closure (Set.range s)) (funext fun a => (hγ a).symm)
    · show M.len (invApply (archEmbed h v γ * g) (vecAt v ((rep (gr e)).2 a))) ≤ C
      rw [← hγ a, invApply_archEmbed_mul]
      exact heC a

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology

noncomputable section

namespace ComplementArchCocompact

section Lattice

variable {E : Type*} [Field E] [NumberField E] {W : Type*} [AddCommGroup W] [Module E W]

theorem exists_zsmul_mem {La : AddSubgroup W} (hL : IsLattice E La) (x : W) :
    ∃ d : ℤ, d ≠ 0 ∧ d • x ∈ La :=
  _root_.UpperTheory.Reformulated.B.ExistsZsmulMem.exists_zsmul_mem hL x

end Lattice

end ComplementArchCocompact

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace ComplementArchCocompact

def formAt (h : HermitianForm F E W) (v : Basis ι E W) (w : InfinitePlace E) (u : ι → ℂ) :
    (ι → ℂ) →ₗ[ℂ] ℂ where
  toFun z := star u ⬝ᵥ (gramAt h v w *ᵥ z)
  map_add' x y := by simp [Matrix.mulVec_add, dotProduct_add]
  map_smul' c x := by simp [Matrix.mulVec_smul, dotProduct_smul]

def projAt (h : HermitianForm F E W) (v : Basis ι E W) (x₀ w₀ : W) :
    (InfinitePlace E → ι → ℂ) →ₗ[ℂ] (InfinitePlace E → ι → ℂ) :=
  LinearMap.pi fun w => (LinearMap.id - (formAt h v w (vecAt v w₀ w)).smulRight (vecAt v x₀ w) -
    (formAt h v w (vecAt v x₀ w)).smulRight (vecAt v w₀ w)) ∘ₗ LinearMap.proj w

omit [NumberField F] [NumberField E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] [DecidableEq ι] in
theorem projAt_apply (h : HermitianForm F E W) (v : Basis ι E W) (x₀ w₀ : W)
    (Y : InfinitePlace E → ι → ℂ) (w : InfinitePlace E) :
    projAt h v x₀ w₀ Y w = Y w - (star (vecAt v w₀ w) ⬝ᵥ (gramAt h v w *ᵥ Y w)) • vecAt v x₀ w -
      (star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ Y w)) • vecAt v w₀ w := rfl

omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Fintype ι] [DecidableEq ι] in
theorem vecAt_smul_apply (v : Basis ι E W) (a : E) (x : W) (w : InfinitePlace E) :
    vecAt v (a • x) w = w.embedding a • vecAt v x w := by
  funext i; simp [vecAt]

theorem projAt_vecAt (h : HermitianForm F E W) (v : Basis ι E W) {x₀ w₀ : W}
    (hp : IsHyperbolicPair h x₀ w₀) (e : W) :
    projAt h v x₀ w₀ (vecAt v e) = vecAt v (ComplementExtension.proj hp e : W) := by
  funext w
  rw [projAt_apply, ← HermAtPlace.proof h v w w₀, ← HermAtPlace.proof h v w x₀,
    ComplementExtension.proj_apply]
  simp only [← vecAtHom_apply, map_sub, Pi.sub_apply]
  simp only [vecAtHom_apply, vecAt_smul_apply]

end ComplementArchCocompact


open ComplementArchCocompact in
theorem ComplementArchCocompact.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    ComplementArchCocompact.Statement h v := by
  classical
  intro La x₀ w₀ m hLa hp hm
  obtain ⟨hli, hdim⟩ := CoordEmbedBasis.proof E ι
  let b₀ := Pi.basis fun _ : ι => integralBasis E
  let Bs := basisOfLinearIndependentOfCardEqFinrank' _ hli
    (by rw [hdim, finrank_eq_card_basis b₀])
  let e : _ → W := fun k => v.equivFun.symm (b₀ k)
  have hBe : ∀ k, Bs k = vecAt v (e k) := by
    intro k
    rw [coe_basisOfLinearIndependentOfCardEqFinrank']
    funext w i
    rw [vecAt, coordEmbed_apply, ← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  let p : _ → W := fun k => (ComplementExtension.proj hp (e k) : W)
  choose d hd hdL using fun k => exists_zsmul_mem hLa (p k)
  let f : _ → W := fun k => m • d k • p k
  let D : _ → ℝ := fun k => (m : ℝ) * d k
  have hD : ∀ k, D k ≠ 0 := fun k =>
    mul_ne_zero (by exact_mod_cast hm.ne') (by exact_mod_cast hd k)
  have hf : ∀ k, vecAt v (f k) = D k • vecAt v (p k) := by
    intro k
    simp only [f, D, ← vecAtHom_apply, map_nsmul, map_zsmul]
    rw [mul_smul, Nat.cast_smul_eq_nsmul, Int.cast_smul_eq_zsmul]
  refine ⟨(fun t : _ → ℝ => ∑ k, t k • vecAt v (f k)) '' Set.Icc 0 1,
    isCompact_Icc.image (continuous_finsetSum _ fun k _ =>
      (continuous_apply k).smul continuous_const), fun Y hY => ?_⟩
  have hPY : projAt h v x₀ w₀ Y = Y := by
    funext w
    rw [projAt_apply, (hY w).1, (hY w).2, zero_smul, zero_smul, sub_zero, sub_zero]
  set s : _ → ℝ := fun k => Bs.repr Y k * (D k)⁻¹ with hs
  have hYs : Y = ∑ k, s k • vecAt v (f k) := by
    calc Y = (projAt h v x₀ w₀).restrictScalars ℝ (∑ k, Bs.repr Y k • Bs k) := by
          rw [Bs.sum_repr]; exact hPY.symm
      _ = ∑ k, Bs.repr Y k • vecAt v (p k) := by

          simp only [map_sum, map_smul, LinearMap.restrictScalars_apply, hBe]
          exact Finset.sum_congr rfl fun k _ => by rw [projAt_vecAt]
      _ = _ := Finset.sum_congr rfl fun k _ => by
          rw [hf, smul_smul, hs, mul_assoc, inv_mul_cancel₀ (hD k), mul_one]
  refine ⟨∑ k, ⌊s k⌋ • f k, ?_, ⟨∑ k, ⌊s k⌋ • d k • p k, ?_, ?_⟩,
    ⟨fun k => Int.fract (s k), ⟨fun k => Int.fract_nonneg _, fun k => (Int.fract_lt_one _).le⟩, ?_⟩⟩
  · exact Submodule.sum_mem _ fun k _ =>
      zsmul_mem (nsmul_mem (zsmul_mem (ComplementExtension.proj hp (e k)).2 _) _) _
  · exact La.sum_mem fun k _ => La.zsmul_mem (hdL k) _
  · rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun k _ => smul_comm _ _ _
  · show ∑ k, Int.fract (s k) • vecAt v (f k) = Y - vecAt v (∑ k, ⌊s k⌋ • f k)
    conv_rhs => rw [hYs]

    rw [← vecAtHom_apply, map_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul, vecAtHom_apply, ← Int.cast_smul_eq_zsmul ℝ, ← sub_smul, Int.self_sub_floor]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory IsDedekindDomain
open scoped Pointwise ComplexOrder ENNReal NumberField.AdeleRing

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def AdelicLatticeDictionary.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∃ (K : Subgroup (unitaryPoints F E (gram h.toSesq v) (FiniteAdeleRing (𝓞 F) F))) (D : ℕ)
    (L : unitaryPoints F E (gram h.toSesq v) (FiniteAdeleRing (𝓞 F) F) → AddSubgroup W),
    IsCompact (K : Set (unitaryPoints F E (gram h.toSesq v) (FiniteAdeleRing (𝓞 F) F))) ∧
    IsOpen (K : Set (unitaryPoints F E (gram h.toSesq v) (FiniteAdeleRing (𝓞 F) F))) ∧
    (∀ g, IsDIntegral h D (L g)) ∧
    (∀ (γ : h.unitaryGroup) g, L ((adeleSplit h v (hermitianDiagonal h v γ)).2 * g) = γ • L g) ∧
    ∀ g g', L g = L g' ↔ g⁻¹ * g' ∈ K

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]


omit [IsTotallyReal F] in
theorem ShortestVectorIndex.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (h₁ : LineIndexCoeffs.Statement (E := E) W) (h₂ : LineCoeffsFG.Statement (E := E) W)
    (h₃ : WeightedLenSmul.Statement h v) (h₄ : WeightPos.Statement h v)
    (h₅ : WeightedIndexBound.Statement E) : ShortestVectorIndex.Statement h v := by
  intro M r ha D La g x hD hx hx0 hmin
  set c : InfinitePlace E → ℝ := fun w =>
    (star (invApply g (vecAt v x) w) ⬝ᵥ (M.P w *ᵥ invApply g (vecAt v x) w)).re with hc
  have hcpos : ∀ w, 0 < c w := h₄ M g x hx0
  have hdeg : finrank ℚ E = 2 * finrank ℚ F := by
    rw [← Module.finrank_mul_finrank ℚ F E, Algebra.IsQuadraticExtension.finrank_eq_two F E,
      mul_comm]

  have hlen : ∀ a : E, M.len (invApply g (vecAt v (a • x))) ^ 2 =
      ∑ w, c w * ‖w.embedding a‖ ^ 2 := by
    intro a
    rw [h₃ M g x a]
    exact Finset.sum_congr rfl fun w _ => mul_comm _ _
  have hlen1 : M.len (invApply g (vecAt v x)) ^ 2 = ∑ w, c w := by
    have := hlen 1
    simpa using this
  have hsub : intSubgroup E ≤ lineCoeffs La x := by
    rintro _ ⟨a, rfl⟩
    exact hD.isLattice.smul_mem a x hx
  have hfg : (lineCoeffs La x).FG := h₂ La x hD.isLattice.fg hx0
  have hmin' : ∀ a ∈ lineCoeffs La x, a ≠ 0 →
      ∑ w, c w ≤ ∑ w, c w * ‖w.embedding a‖ ^ 2 := by
    intro a haA ha0
    have hax : a • x ∈ La := haA
    have hax0 : a • x ≠ 0 := smul_ne_zero ha0 hx0
    have hle := hmin (a • x) hax hax0
    rw [← hlen1, ← hlen a]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hle 2
  obtain ⟨a, hali, habs⟩ := ha
  have ha' : ∃ b : Fin (finrank ℚ E) → 𝓞 E, LinearIndependent ℚ (fun i => (b i : E)) ∧
      ∀ i (σ : E →+* ℂ), ‖σ (b i)‖ ≤ r :=
    ⟨a ∘ Fin.cast hdeg, hali.comp _ (Fin.cast_injective hdeg), fun i σ => habs _ σ⟩
  have key := h₅ c hcpos (lineCoeffs La x) hsub hfg hmin' r ha'
  rw [h₁ La x hx0]
  rw [hdeg] at key
  push_cast at key
  exact key

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem ShortVectorIsotropic.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (h₁ : HermAtPlace.Statement h v) (h₂ : GramAtData.Statement h v)
    (h₃ : ArchInvariant.Statement h v) (h₄ : MajorantBound.Statement ι)
    (h₅ : LenSq.Statement h v) (h₆ : IntegerSmallAtPlaces.Statement E) :
    ShortVectorIsotropic.Statement h v := by
  intro M D La g x hLa hx hlen
  apply h₆ _ (hLa.integral x hx x hx)
  intro w
  set y := vecAt v x
  set z := invApply g y
  have hP : IsMajorantOf (gramAt h v w) (M.P w) :=
    ⟨M.posDef w, (h₂ w).1, (h₂ w).2, M.siegel w⟩
  obtain ⟨hnn, hsq⟩ := h₅ M z
  have hlen0 : 0 ≤ M.len z := Real.sqrt_nonneg _
  have hsq1 : M.len z ^ 2 < 1 := by nlinarith
  have hterm : (star (z w) ⬝ᵥ (M.P w *ᵥ z w)).re ≤ M.len z ^ 2 := by
    rw [hsq]
    exact Finset.single_le_sum (f := fun w' => (star (z w') ⬝ᵥ (M.P w' *ᵥ z w')).re)
      (fun w' _ => hnn w') (Finset.mem_univ w)
  have hform : w.embedding (h.toSesq x x) = star (z w) ⬝ᵥ (gramAt h v w *ᵥ z w) := by
    rw [h₁ w x x, h₃ g y y w]
  rw [← InfinitePlace.norm_embedding_eq, hform]
  exact lt_of_le_of_lt ((h₄ _ _ hP (z w)).trans hterm) hsq1

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end
