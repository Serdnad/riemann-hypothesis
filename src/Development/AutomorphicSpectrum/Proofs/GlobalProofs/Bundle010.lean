module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import Mathlib.MeasureTheory.Group.Measure
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle004
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle001
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Formalism.UnipotentAdelicQuotients.Bundle001
public import GroundTheory.AutomorphicForms.RealGroupsLie
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle054
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle101
public import GroundTheory.ProfiniteCohomology.Bundle005
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle008
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConormalFiniteProjectiveOfSmooth
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle005
public import GroundTheory.AutomorphicForms.MeasuresGL
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle007
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.Bundle001
public import ReciprocityTheory.GaloisValuations.Global
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.Valuation.LocalSubring
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Formalism.ConjugateSelfDual.Bundle001
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel

namespace GlobalTheory.CompanionTheory.QL.HaarGL

theorem exists_haar_unimodular : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ n : ℕ, (∃ κ : Measure (GL (Fin n) F), κ.IsMulLeftInvariant ∧ κ (GLint O n : Set (GL (Fin n) F)) = 1) ∧ ∀ μ : Measure (GL (Fin n) F), μ.IsHaarMeasure → μ.IsMulRightInvariant ∧ μ.IsInvInvariant := by
  intro F _ _ _ _ O ϖ nrm q hLF n
  obtain ⟨hKo, hKc, hlc, _hsc, ht2, -, -⟩ := GlobalTheory.T.generalLinear_integral_compact_open hLF n
  haveI := hlc
  haveI := ht2
  haveI : BorelSpace (GL (Fin n) F) := GlobalTheory.CompanionTheory.QL.instBorelGL n
  refine ⟨?_, fun μ hμ => ?_⟩
  · let μ₀ : Measure (GL (Fin n) F) := Measure.haar
    have hpos : μ₀ (GLint O n : Set (GL (Fin n) F)) ≠ 0 :=
      hKo.measure_ne_zero μ₀ ⟨1, (GLint O n).one_mem⟩
    have hfin : μ₀ (GLint O n : Set (GL (Fin n) F)) ≠ ⊤ := hKc.measure_lt_top.ne
    refine ⟨(μ₀ (GLint O n : Set (GL (Fin n) F)))⁻¹ • μ₀, inferInstance, ?_⟩
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hpos hfin]
  · haveI := hμ
    exact ⟨GroundTheory.Automorphic.Measures.isMulRightInvariant_GL F n μ,
      ⟨GroundTheory.Automorphic.Measures.inv_eq_self_GL F n μ⟩⟩

end GlobalTheory.CompanionTheory.QL.HaarGL
end

section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

namespace GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

theorem locPrincipal_locally_const {k A : Type} [Field k] [CommRing A] [IsDomain A] (φ : k →+* A) (I : Ideal A)
    (hφ : φ.Smooth) (hI : ((Ideal.Quotient.mk I).comp φ).Smooth) (p : PrimeSpectrum A)
    (hp : I ≤ p.asIdeal) :
    ∃ s, s ∉ p.asIdeal ∧ ∀ q : PrimeSpectrum A, s ∉ q.asIdeal → I ≤ q.asIdeal →
      (LocPrincipal I q.asIdeal ↔ LocPrincipal I p.asIdeal) := by
  obtain ⟨hfin, hproj⟩ := GlobalTheory.T.conormal_finite_projective_of_smooth φ I hφ hI
  have hnoeth : IsNoetherianRing A := by
    algebraize [φ]
    have : Algebra.FiniteType k A := inferInstance
    exact Algebra.FiniteType.isNoetherianRing k A
  have := Module.finitePresentation_of_projective (A ⧸ I) I.Cotangent
  have hsurj : Function.Surjective (Ideal.Quotient.mk I) := Ideal.Quotient.mk_surjective
  have hce := PrimeSpectrum.isClosedEmbedding_comap_of_surjective (A ⧸ I) (Ideal.Quotient.mk I) hsurj
  have hrange : ∀ q : PrimeSpectrum A, I ≤ q.asIdeal →
      ∃ Q : PrimeSpectrum (A ⧸ I), PrimeSpectrum.comap (Ideal.Quotient.mk I) Q = q := by
    intro q hq
    have : q ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) := by
      rw [_root_.range_comap_of_surjective _ _ hsurj, Ideal.mk_ker]
      exact hq
    exact this
  obtain ⟨P0, hP0⟩ := hrange p hp
  have hlc : IsLocallyConstant (Module.rankAtStalk (R := A ⧸ I) I.Cotangent) :=
    Module.isLocallyConstant_rankAtStalk
  have hO := hlc.isOpen_fiber (Module.rankAtStalk (R := A ⧸ I) I.Cotangent P0)
  obtain ⟨W, hW, hWO⟩ := hce.isInducing.isOpen_iff.1 hO
  have hpW : p ∈ W := by
    have : P0 ∈ PrimeSpectrum.comap (Ideal.Quotient.mk I) ⁻¹' W := by rw [hWO]; rfl
    rwa [Set.mem_preimage, hP0] at this
  obtain ⟨_, ⟨s, rfl⟩, hps, hsW⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hpW hW
  refine ⟨s, hps, fun q hs hq => ?_⟩
  obtain ⟨Q, hQ⟩ := hrange q hq
  have hQO : Module.rankAtStalk (R := A ⧸ I) I.Cotangent Q = Module.rankAtStalk (R := A ⧸ I) I.Cotangent P0 := by
    have : Q ∈ PrimeSpectrum.comap (Ideal.Quotient.mk I) ⁻¹' W := by
      rw [Set.mem_preimage, hQ]; exact hsW hs
    rw [hWO] at this
    exact this
  have e : ∀ R : PrimeSpectrum (A ⧸ I), LocPrincipal I (PrimeSpectrum.comap (Ideal.Quotient.mk I) R).asIdeal ↔ Module.rankAtStalk (R := A ⧸ I) I.Cotangent R = 1 :=
    fun R => ⟨GlobalTheory.T.conormal_rank_one_of_locally_principal I R, GlobalTheory.T.locally_principal_of_conormal_rank_one I R⟩
  rw [← hQ, ← hP0, e, e, hQO]

theorem fromSpec_mem_basicOpen_iff {X : Scheme.{0}} (U : X.affineOpens) (q : PrimeSpectrum Γ(X, U.1))
    (f : Γ(X, U.1)) : U.2.fromSpec q ∈ X.basicOpen f ↔ f ∉ q.asIdeal := by
  have := U.2.fromSpec_preimage_basicOpen f
  have h2 : q ∈ U.2.fromSpec ⁻¹ᵁ X.basicOpen f ↔ q ∈ PrimeSpectrum.basicOpen f := by
    rw [this]; rfl
  exact h2

theorem isClosed_of_locally_iff {T : Type*} [TopologicalSpace T] {C : Set T} (hC : IsClosed C)
    (P : T → Prop) (h : ∀ x ∈ C, ∃ V : Set T, IsOpen V ∧ x ∈ V ∧ ∀ y ∈ V, y ∈ C → (P y ↔ P x)) :
    IsClosed {x | x ∈ C ∧ P x} := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  by_cases hxC : x ∈ C
  · obtain ⟨V, hV, hxV, hy⟩ := h x hxC
    refine ⟨V, fun y hyV hyS => hx ⟨hxC, (hy y hyV hyS.1).1 hyS.2⟩, hV, hxV⟩
  · exact ⟨Cᶜ, fun y hy hyS => hy hyS.1, hC.isOpen_compl, hxC⟩

theorem isClosed_cartAt : ∀ {k : Type} [Field k] {X : Scheme.{0}} (g : X ⟶ Sp k) (Z : X.IdealSheafData), Smooth g → IsIntegral X → Smooth (Z.subschemeι ≫ g) → IsClosed {x : X | x ∈ Z.support ∧ CartAt Z x} ∧ IsClosed {x : X | x ∈ Z.support ∧ ¬ CartAt Z x} := by
  intro k _ X g Z hg hX hZ
  have key : ∀ x ∈ (Z.support : Set X), ∃ V : Set X, IsOpen V ∧ x ∈ V ∧
      ∀ y ∈ V, y ∈ (Z.support : Set X) → (CartAt Z y ↔ CartAt Z x) := by
    intro x hx
    obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
    let U' : X.affineOpens := ⟨U, hU⟩
    have hne : Nonempty U := ⟨⟨x, hxU⟩⟩
    have hdom : IsDomain Γ(X, U'.1) := inferInstanceAs (IsDomain Γ(X, U))
    obtain ⟨φ, hφ, hI⟩ := GlobalTheory.T.exists_smooth_affine_presentation_pair g Z U' hg hZ
    have hrange : ∀ y ∈ U, ∃ q, U'.2.fromSpec q = y := by
      intro y hy
      have : y ∈ Set.range U'.2.fromSpec := by rw [U'.2.range_fromSpec]; exact hy
      exact this
    have hIq : ∀ q : PrimeSpectrum Γ(X, U'.1), U'.2.fromSpec q ∈ (Z.support : Set X) →
        Z.ideal U' ≤ q.asIdeal := by
      intro q hq f hf
      by_contra hfq
      have hb := (fromSpec_mem_basicOpen_iff U' q f).2 hfq
      have hmem : U'.2.fromSpec q ∈ (Z.support : Set X) ∩ (U'.1 : Set X) :=
        ⟨hq, X.basicOpen_le f hb⟩
      rw [Z.coe_support_inter U'] at hmem
      exact (Scheme.mem_zeroLocus_iff _ _ _).1 hmem.1 f hf hb
    obtain ⟨q0, rfl⟩ := hrange x hxU
    obtain ⟨s, hs, h⟩ := locPrincipal_locally_const φ (Z.ideal U') hφ hI q0 (hIq q0 hx)
    refine ⟨X.basicOpen s, (X.basicOpen s).isOpen, (fromSpec_mem_basicOpen_iff U' q0 s).2 hs, ?_⟩
    intro y hy hyZ
    obtain ⟨q, rfl⟩ := hrange y (X.basicOpen_le s hy)
    have := h q ((fromSpec_mem_basicOpen_iff U' q s).1 hy) (hIq q hyZ)
    exact ⟨fun hc => GlobalTheory.T.cartier_at_of_locally_principal Z U' q0 (this.1 (GlobalTheory.T.locally_principal_of_cartier_at Z U' q hc)),
      fun hc => GlobalTheory.T.cartier_at_of_locally_principal Z U' q (this.2 (GlobalTheory.T.locally_principal_of_cartier_at Z U' q0 hc))⟩
  have hC : IsClosed (Z.support : Set X) := Z.support.isClosed
  refine ⟨isClosed_of_locally_iff hC _ key, isClosed_of_locally_iff hC _ fun x hx => ?_⟩
  obtain ⟨V, hV, hxV, hy⟩ := key x hx
  exact ⟨V, hV, hxV, fun y hyV hyC => not_congr (hy y hyV hyC)⟩

end GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
end

section

set_option maxSynthPendingDepth 1
open scoped Manifold ContDiff Topology
open MeasureTheory Set GroundTheory.Automorphic
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace GlobalTheory.CompanionTheory.ClosedSubgroupUnits

open Matrix

variable {n : Type} [Fintype n] [DecidableEq n] {m : ℕ}

def blk (e : n ⊕ n ≃ Fin m) : Matrix n n ℂ × Matrix n n ℂ →+* Matrix (Fin m) (Fin m) ℂ where
  toFun p := Matrix.reindex e e (Matrix.fromBlocks p.1 0 0 p.2)
  map_one' := by simp
  map_mul' p q := by
    simp [Matrix.fromBlocks_multiply, Matrix.submatrix_mul_equiv]
  map_zero' := by simp
  map_add' p q := by
    have h : Matrix.fromBlocks (p + q).1 0 0 (p + q).2 =
        Matrix.fromBlocks p.1 0 0 p.2 + Matrix.fromBlocks q.1 0 0 q.2 := by
      simp [Matrix.fromBlocks_add]
    rw [h]
    rfl

theorem blk_apply (e : n ⊕ n ≃ Fin m) (a b : Matrix n n ℂ) :
    blk e (a, b) = Matrix.reindex e e (Matrix.fromBlocks a 0 0 b) := rfl

def unblk (e : n ⊕ n ≃ Fin m) (g : Matrix (Fin m) (Fin m) ℂ) : Matrix n n ℂ × Matrix n n ℂ :=
  ((Matrix.reindex e.symm e.symm g).toBlocks₁₁, (Matrix.reindex e.symm e.symm g).toBlocks₂₂)

theorem unblk_blk (e : n ⊕ n ≃ Fin m) (p : Matrix n n ℂ × Matrix n n ℂ) :
    unblk e (blk e p) = p := by
  ext i j <;> simp [unblk, blk, Matrix.toBlocks₁₁, Matrix.toBlocks₂₂]

theorem continuous_blk (e : n ⊕ n ≃ Fin m) : Continuous (blk e) := by
  refine continuous_matrix fun i j => ?_
  change Continuous fun p : Matrix n n ℂ × Matrix n n ℂ =>
    Matrix.fromBlocks p.1 0 0 p.2 (e.symm i) (e.symm j)
  rcases e.symm i with a | a <;> rcases e.symm j with b | b <;> simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
  · exact (continuous_apply_apply a b).comp continuous_fst
  · exact continuous_const
  · exact continuous_const
  · exact (continuous_apply_apply a b).comp continuous_snd

theorem continuous_unblk (e : n ⊕ n ≃ Fin m) : Continuous (unblk e) := by
  refine Continuous.prodMk (continuous_matrix fun i j => ?_) (continuous_matrix fun i j => ?_)
  · exact continuous_apply_apply _ _
  · exact continuous_apply_apply _ _

theorem isClosedEmbedding_blk (e : n ⊕ n ≃ Fin m) : Topology.IsClosedEmbedding (blk e) :=
  Function.LeftInverse.isClosedEmbedding (f := unblk e) (unblk_blk e) (continuous_unblk e)
    (continuous_blk e)

theorem exp_blk (e : n ⊕ n ≃ Fin m) (a b : Matrix n n ℂ) :
    NormedSpace.exp (blk e (a, b)) = blk e (NormedSpace.exp a, NormedSpace.exp b) := by
  letI : NormedAlgebra ℚ (Matrix n n ℂ) := NormedAlgebra.restrictScalars ℚ ℝ (Matrix n n ℂ)
  rw [← NormedSpace.map_exp (blk e) (continuous_blk e) (a, b)]
  congr 1
  exact Prod.ext (Prod.fst_exp _) (Prod.snd_exp _)

def jHom (e : n ⊕ n ≃ Fin m) : (Matrix n n ℂ)ˣ →* Matrix (Fin m) (Fin m) ℂ where
  toFun u := blk e ((u : Matrix n n ℂ), (((u⁻¹ : (Matrix n n ℂ)ˣ) : Matrix n n ℂ))ᵀ)
  map_one' := by
    have h : blk e ((1 : Matrix n n ℂ), (1 : Matrix n n ℂ)) = 1 := map_one (blk e)
    simpa using h
  map_mul' u v := by
    rw [← map_mul]
    simp [Matrix.transpose_mul]

theorem jHom_apply (e : n ⊕ n ≃ Fin m) (u : (Matrix n n ℂ)ˣ) :
    jHom e u = blk e ((u : Matrix n n ℂ), (((u⁻¹ : (Matrix n n ℂ)ˣ) : Matrix n n ℂ))ᵀ) := rfl

theorem isClosedEmbedding_jHom (e : n ⊕ n ≃ Fin m) : Topology.IsClosedEmbedding (jHom e) := by
  have h1 : Topology.IsClosedEmbedding
      (fun p : Matrix n n ℂ × (Matrix n n ℂ)ᵐᵒᵖ => (p.1, (MulOpposite.unop p.2)ᵀ)) :=
    Function.LeftInverse.isClosedEmbedding
      (f := fun p : Matrix n n ℂ × Matrix n n ℂ => (p.1, MulOpposite.op p.2ᵀ))
      (fun p => by simp)
      (continuous_fst.prodMk (MulOpposite.continuous_op.comp continuous_snd.matrix_transpose))
      (continuous_fst.prodMk
        ((MulOpposite.continuous_unop.comp continuous_snd).matrix_transpose))
  exact (isClosedEmbedding_blk e).comp (h1.comp Units.isClosedEmbedding_embedProduct)

def dLin (e : n ⊕ n ≃ Fin m) : Matrix n n ℂ →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ where
  toFun X := blk e (X, -Xᵀ)
  map_add' X Y := by
    rw [← map_add (f := _)]
    simp [Matrix.transpose_add, add_comm]
  map_smul' r X := by
    ext i j
    simp only [blk_apply, Matrix.reindex_apply, Matrix.submatrix_apply, RingHom.id_apply,
      Matrix.smul_apply]
    rcases e.symm i with a | a <;> rcases e.symm j with b | b <;> simp

theorem dLin_apply (e : n ⊕ n ≃ Fin m) (X : Matrix n n ℂ) : dLin e X = blk e (X, -Xᵀ) := rfl

theorem continuous_dLin (e : n ⊕ n ≃ Fin m) : Continuous (dLin e) :=
  (continuous_blk e).comp (continuous_id.prodMk continuous_id.matrix_transpose.neg)

theorem exp_dLin (e : n ⊕ n ≃ Fin m) (X : Matrix n n ℂ) :
    NormedSpace.exp (dLin e X) = jHom e (expUnit ℝ (Matrix n n ℂ) X) := by
  rw [dLin_apply, exp_blk, jHom_apply, coe_expUnit, coe_expUnit_inv, ← Matrix.transpose_neg,
    Matrix.exp_transpose]

theorem isClosedMatrixGroup_image (e : n ⊕ n ≃ Fin m) (H : Subgroup (Matrix n n ℂ)ˣ)
    (hH : IsClosed (H : Set (Matrix n n ℂ)ˣ)) :
    SmoothVectors.IsClosedMatrixGroup (jHom e '' (H : Set (Matrix n n ℂ)ˣ)) := by
  refine ⟨(isClosedEmbedding_jHom e).isClosedMap _ hH, ⟨1, H.one_mem, map_one _⟩, ?_, ?_⟩
  · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    exact ⟨u * v, H.mul_mem hu hv, map_mul _ _ _⟩
  · rintro _ ⟨u, hu, rfl⟩
    refine ⟨jHom e u⁻¹, ⟨u⁻¹, H.inv_mem hu, rfl⟩, ?_, ?_⟩
    · rw [← map_mul, inv_mul_cancel, map_one]
    · rw [← map_mul, mul_inv_cancel, map_one]

theorem exists_isExpLieAlgebra {n : Type} [Fintype n] [DecidableEq n]
    (H : Subgroup (Matrix n n ℂ)ˣ) (hH : IsClosed (H : Set (Matrix n n ℂ)ˣ)) :
    ∃ 𝔤 : Submodule ℝ (Matrix n n ℂ), IsExpLieAlgebra H 𝔤 := by
  let e : n ⊕ n ≃ Fin (Fintype.card (n ⊕ n)) := Fintype.equivFin _
  have hJ := isClosedMatrixGroup_image e H hH
  obtain ⟨S, hS⟩ := GlobalTheory.CompanionTheory.MatrixLie.exists_submodule_eq_lieAlg _ _ hJ
  have hsm : ∀ (t : ℝ) (Z : Matrix (Fin (Fintype.card (n ⊕ n))) (Fin (Fintype.card (n ⊕ n))) ℂ),
      (t : ℂ) • Z = t • Z := by
    intro t Z
    ext a b
    simp
  have hS' : ∀ X, X ∈ S ↔ ∀ t : ℝ, NormedSpace.exp (t • X) ∈ jHom e '' (H : Set (Matrix n n ℂ)ˣ) := by
    intro X
    have h2 : X ∈ S ↔ X ∈ SmoothVectors.lieAlg (jHom e '' (H : Set (Matrix n n ℂ)ˣ)) := by
      rw [← hS]
      exact Iff.rfl
    rw [h2]
    refine forall_congr' fun t => ?_
    rw [hsm]
  have hinj := (isClosedEmbedding_jHom e).injective
  have hmem : ∀ X, NormedSpace.exp (dLin e X) ∈ jHom e '' (H : Set (Matrix n n ℂ)ˣ) →
      expUnit ℝ (Matrix n n ℂ) X ∈ H := by
    intro X hX
    rw [exp_dLin] at hX
    obtain ⟨u, hu, hue⟩ := hX
    rwa [← hinj hue]
  refine ⟨S.comap (dLin e), fun X hX => hmem X ?_, ?_⟩
  · simpa using (hS' _).1 hX 1
  · set 𝔢 := expPartialHomeomorph ℝ (Matrix n n ℂ) with h𝔢
    set 𝔣 := expPartialHomeomorph ℝ
      (Matrix (Fin (Fintype.card (n ⊕ n))) (Fin (Fintype.card (n ⊕ n))) ℂ) with h𝔣
    have hev := GlobalTheory.CompanionTheory.ClosedSubgroup.eventually_exp_of_mem hJ.1 hJ.2.1 hJ.2.2.1 hJ.2.2.2 hS'
      (𝔣.open_source.mem_nhds (zero_mem_expPartialHomeomorph_source ℝ _))
    obtain ⟨V, hV, hVo, h1V⟩ := eventually_nhds_iff.1 hev
    have hcD := continuous_dLin e
    have hcE : Continuous fun X => NormedSpace.exp (dLin e X) :=
      (contDiff_exp ℝ _ (n := 0)).continuous.comp hcD
    refine ⟨𝔢.source ∩ (dLin e ⁻¹' 𝔣.source ∩ (fun X => NormedSpace.exp (dLin e X)) ⁻¹' V),
      𝔢.open_source.inter ((𝔣.open_source.preimage hcD).inter (hVo.preimage hcE)),
      ⟨zero_mem_expPartialHomeomorph_source ℝ _, ?_, ?_⟩, Set.inter_subset_left, ?_⟩
    · simpa using zero_mem_expPartialHomeomorph_source ℝ
        (Matrix (Fin (Fintype.card (n ⊕ n))) (Fin (Fintype.card (n ⊕ n))) ℂ)
    · simpa using h1V
    · rintro X ⟨-, hXs, hXV⟩ hXH
      obtain ⟨Y, hYS, hYs, hYe⟩ := hV _ hXV ⟨_, hXH, (exp_dLin e X).symm⟩
      have hDY : dLin e X = Y := 𝔣.injOn hXs hYs hYe.symm
      change dLin e X ∈ S
      rwa [hDY]

end GlobalTheory.CompanionTheory.ClosedSubgroupUnits
end
end

section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual

theorem _root_.GlobalTheory.T.finite_H1_of_finite_crossed_homs : ∀ (k G : Type) [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (A : Rep.{0} k G) [IsDiscreteRep A], {f : G → A.V | IsLocallyConstant f ∧ ∀ g h : G, f (g * h) = f g + A.ρ g (f h)}.Finite → Finite (cohomology A 1) := by
  first | exact @GlobalTheory.CompanionTheory.Glob.finite_cohomology_one_of_finite_cocycles | exact GlobalTheory.CompanionTheory.Glob.finite_cohomology_one_of_finite_cocycles | (intros; apply GlobalTheory.CompanionTheory.Glob.finite_cohomology_one_of_finite_cocycles <;> assumption)
end

section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual

namespace GlobalTheory.CompanionTheory.GlobalFiniteness

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]


omit [NumberField F] [Algebra F Ω] [Field F] in
theorem mem_of_isIntegral_int (A : ValuationSubring Ω) {y : Ω} (hy : IsIntegral ℤ y) : y ∈ A := by
  have h1 : IsIntegral A y := hy.tower_top
  obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).mp h1
  rw [← hz]
  exact z.2

noncomputable def intToVal (A : ValuationSubring Ω) (M : IntermediateField F Ω) : 𝓞 M →+* A :=
  ((algebraMap M Ω).comp (algebraMap (𝓞 M) M)).codRestrict A fun z =>
    mem_of_isIntegral_int A ((RingOfIntegers.isIntegral_coe z).map (IsScalarTower.toAlgHom ℤ M Ω))

noncomputable def cutPrime (A : ValuationSubring Ω) (M : IntermediateField F Ω) : Ideal (𝓞 M) :=
  (IsLocalRing.maximalIdeal A).comap (intToVal A M)

instance (A : ValuationSubring Ω) (M : IntermediateField F Ω) : (cutPrime A M).IsPrime :=
  Ideal.comap_isPrime _ _

theorem mem_cutPrime_iff (A : ValuationSubring Ω) (M : IntermediateField F Ω) (z : 𝓞 M) :
    z ∈ cutPrime A M ↔ A.valuation ((z : M) : Ω) < 1 := by
  rw [cutPrime, Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff]
  rfl

theorem cutPrime_liesOver {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)}
    (hA : IsPlaceOver A v) (M : IntermediateField F Ω) : (cutPrime A M).LiesOver v.asIdeal := by
  constructor
  ext x
  rw [Ideal.under_def, Ideal.mem_comap, mem_cutPrime_iff, ← hA x]
  rfl

theorem inertia_apply_eq [IsGalois F Ω] {S : Set (HeightOneSpectrum (𝓞 F))}
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) {A : ValuationSubring Ω} (hA : IsPlaceOver A v)
    {σ : G F Ω} (hσ : σ ∈ Inertia (F := F) A) {x : Ω} (hx : x ∈ maxUnramifiedOutside F Ω S) :
    σ x = x := by
  classical
  haveI hM : IsGalois F (maxUnramifiedOutside F Ω S) := isGalois_maxUnramifiedOutside S
  haveI : FiniteDimensional F (IntermediateField.adjoin F ({x} : Set Ω)) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  set E : IntermediateField F Ω := IntermediateField.normalClosure F (IntermediateField.adjoin F ({x} : Set Ω)) Ω with hE
  haveI : FiniteDimensional F E := normalClosure.is_finiteDimensional F (IntermediateField.adjoin F ({x} : Set Ω)) Ω
  haveI : Normal F E := normalClosure.normal F (IntermediateField.adjoin F ({x} : Set Ω)) Ω
  haveI : Algebra.IsSeparable F E := Algebra.IsSeparable.of_algHom F Ω E.val
  haveI : IsGalois F E := ⟨⟩
  have hxE : x ∈ E := IntermediateField.le_normalClosure (IntermediateField.adjoin F ({x} : Set Ω)) (IntermediateField.mem_adjoin_simple_self F x)
  have hEM : E ≤ maxUnramifiedOutside F Ω S := by
    rw [hE, IntermediateField.normalClosure_le_iff_of_normal]
    exact IntermediateField.adjoin_simple_le_iff.2 hx
  have hEun : IsUnramifiedOutside S E := (isUnramifiedOutside_iff_le_maxUnramifiedOutside S).2 hEM
  haveI hPl : (cutPrime A E).LiesOver v.asIdeal := cutPrime_liesOver hA E
  haveI : NumberField E := NumberField.of_module_finite F E
  haveI : Module.Finite (𝓞 F) (𝓞 E) := Module.Finite.of_restrictScalars_finite ℤ (𝓞 F) (𝓞 E)
  haveI : Algebra.FiniteType (𝓞 F) (𝓞 E) := Algebra.FiniteType.of_restrictScalars_finiteType ℤ (𝓞 F) (𝓞 E)
  haveI : IsGaloisGroup Gal(E/F) (𝓞 F) (𝓞 E) := IsGaloisGroup.of_isFractionRing (G := Gal(E/F)) (A := 𝓞 F) (B := 𝓞 E) (K := F) (L := E)
  have he : (cutPrime A E).ramificationIdx (𝓞 F) = 1 :=
    Algebra.IsUnramifiedIn.ramificationIdx_eq_one (hEun v hv) hPl
  have hcard : Nat.card ((cutPrime A E).inertia Gal(E/F)) = 1 := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(E/F)) v.asIdeal (cutPrime A E),
      Ideal.ramificationIdxIn_eq_ramificationIdx (G := Gal(E/F)) v.asIdeal (cutPrime A E), he]
  set σ' : Gal(E/F) := σ.restrictNormal E with hσ'
  have hmem : σ' ∈ (cutPrime A E).inertia Gal(E/F) := by
    intro z
    show σ' • z - z ∈ cutPrime A E
    rw [mem_cutPrime_iff]
    obtain ⟨-, hσ2⟩ := hσ
    have hy : ((z : E) : Ω) ∈ A :=
      mem_of_isIntegral_int A ((RingOfIntegers.isIntegral_coe z).map (IsScalarTower.toAlgHom ℤ E Ω))
    have hc : (((σ' • z - z : 𝓞 E) : E) : Ω) = σ ((z : E) : Ω) - ((z : E) : Ω) := by
      have h1 := AlgEquiv.restrictNormal_commutes σ E (z : E)
      simp only [IntermediateField.algebraMap_apply] at h1
      rw [← h1, hσ']
      rfl
    rw [hc]
    exact hσ2 _ (A.valuation_le_one ⟨_, hy⟩)
  have hσ'1 : σ' = 1 := by
    haveI hsub : Subsingleton ((cutPrime A E).inertia Gal(E/F)) := (Nat.card_eq_one_iff_unique.1 hcard).1
    have := Subsingleton.elim (⟨σ', hmem⟩ : (cutPrime A E).inertia Gal(E/F)) ⟨1, Subgroup.one_mem _⟩
    exact congrArg Subtype.val this
  have h1 := AlgEquiv.restrictNormal_commutes σ E ⟨x, hxE⟩
  rw [← hσ', hσ'1] at h1
  exact h1.symm

theorem NS_le_fixingSubgroup : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (S : Set (HeightOneSpectrum (𝓞 F))),
    NS Ω S ≤ (maxUnramifiedOutside F Ω S).fixingSubgroup := by
  intro F Ω _ _ _ _ _ S
  haveI : IsGalois F Ω := ⟨⟩
  haveI hM : IsGalois F (maxUnramifiedOutside F Ω S) := isGalois_maxUnramifiedOutside S
  haveI : (maxUnramifiedOutside F Ω S).fixingSubgroup.Normal :=
    (InfiniteGalois.normal_iff_isGalois _).2 hM
  have hsub : (⋃ v ∈ Sᶜ, ⋃ A ∈ {A : ValuationSubring Ω | IsPlaceOver A v}, Inertia (F := F) A) ⊆
      ((maxUnramifiedOutside F Ω S).fixingSubgroup : Set (G F Ω)) := by
    intro σ hσ
    simp only [Set.mem_iUnion] at hσ
    obtain ⟨v, hv, A, hA, hσA⟩ := hσ
    show σ ∈ (maxUnramifiedOutside F Ω S).fixingSubgroup
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact inertia_apply_eq hv hA hσA hx
  show (Subgroup.normalClosure _).topologicalClosure ≤ _
  exact Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal hsub)
    (InfiniteGalois.fixingSubgroup_isClosed _)

end GlobalTheory.CompanionTheory.GlobalFiniteness
end
