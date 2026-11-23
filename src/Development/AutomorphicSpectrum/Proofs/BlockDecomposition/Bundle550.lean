module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1623
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1673
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1678
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1664
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1681
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.Bundle001
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle413
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcN.F2
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open scoped Pointwise

namespace GlobalTheory.CompanionTheory.GL3BlockMatrixLocal

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem blk_zero_eq {a b n : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w) :
    blk h w m 0 = CtLevel.dgM h w m := by
  ext1
  rw [CtLevel.blk_val, CtLevel.dgM_val, CtLevel.dgMat, Matrix.mul_zero]

theorem continuous_dgM {a b n : ℕ} (h : a + b = n) (w : Pl E) :
    Continuous (CtLevel.dgM h w : GLw a w × GLw b w → GLw n w) := by
  have e : (CtLevel.dgM h w : GLw a w × GLw b w → GLw n w) = fun k =>
      ((CtLevel.dgM h w).comp (MonoidHom.inl (GLw a w) (GLw b w))) k.1 *
        ((CtLevel.dgM h w).comp (MonoidHom.inr (GLw a w) (GLw b w))) k.2 := by
    funext k
    simp only [MonoidHom.comp_apply, MonoidHom.inl_apply, MonoidHom.inr_apply, ← map_mul]
    simp
  rw [e]
  exact ((CtLevel.continuous_dgM_inl h w).comp continuous_fst).mul
    ((CtLevel.continuous_dgM_inr h w).comp continuous_snd)

theorem dgM_entries {a b n : ℕ} (h : a + b = n) (w : Pl E) (k : GLw a w × GLw b w) :
    (∀ i j, (CtLevel.dgM h w k).val (CtLevel.blkEq h (Sum.inl i)) (CtLevel.blkEq h (Sum.inl j)) = k.1.val i j) ∧
      ∀ i j, (CtLevel.dgM h w k).val (CtLevel.blkEq h (Sum.inr i)) (CtLevel.blkEq h (Sum.inr j)) = k.2.val i j := by
  constructor <;> intro i j <;>
    rw [CtLevel.dgM_val, CtLevel.dgMat, reindex_apply, submatrix_apply, Equiv.symm_apply_apply,
      Equiv.symm_apply_apply] <;> simp

theorem blocks_mem_KGL {a b n : ℕ} (h : a + b = n) (w : Pl E) (k : GLw a w × GLw b w)
    (hk : CtLevel.dgM h w k ∈ GlobalTheory.LFun.KGL w (n := n)) : k.1 ∈ GlobalTheory.LFun.KGL w (n := a) ∧ k.2 ∈ GlobalTheory.LFun.KGL w (n := b) := by
  obtain ⟨h1, h2⟩ := GlobalTheory.AdelicU.mem_GLint_iff.1 hk
  rw [← map_inv] at h2
  refine ⟨GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩,
    GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩⟩
  · have := h1 (CtLevel.blkEq h (Sum.inl i)) (CtLevel.blkEq h (Sum.inl j))
    rwa [(dgM_entries h w k).1] at this
  · have := h2 (CtLevel.blkEq h (Sum.inl i)) (CtLevel.blkEq h (Sum.inl j))
    rwa [(dgM_entries h w k⁻¹).1] at this
  · have := h1 (CtLevel.blkEq h (Sum.inr i)) (CtLevel.blkEq h (Sum.inr j))
    rwa [(dgM_entries h w k).2] at this
  · have := h2 (CtLevel.blkEq h (Sum.inr i)) (CtLevel.blkEq h (Sum.inr j))
    rwa [(dgM_entries h w k⁻¹).2] at this

theorem constant_term_bi_invariant {a b n : ℕ} (h : a + b = n) (w : Pl E) (K' : Subgroup (GLw n w))
    (hKK : K' ≤ GlobalTheory.LFun.KGL w (n := n)) (hN : ∀ k ∈ GlobalTheory.LFun.KGL w (n := n), ∀ k' ∈ K', k * k' * k⁻¹ ∈ K')
    (f : GLw n w → ℂ) (hf : ∀ k₁ ∈ K', ∀ k₂ ∈ K', ∀ g, f (k₁ * g * k₂) = f g)
    (x y : GLw n w) (hx : x ∈ GlobalTheory.LFun.KGL w (n := n)) (hy : y ∈ GlobalTheory.LFun.KGL w (n := n))
    (k₁ k₂ : GLw a w × GLw b w) (hk₁ : k₁ ∈ leviOf h w K') (hk₂ : k₂ ∈ leviOf h w K')
    (m : GLw a w × GLw b w) : phi3 h w f x y (k₁ * m * k₂) = phi3 h w f x y m := by
  have hd₁ : CtLevel.dgM h w k₁ ∈ K' := by
    have : blk h w k₁ 0 ∈ K' := hk₁
    rwa [blk_zero_eq] at this
  have hd₂ : CtLevel.dgM h w k₂ ∈ K' := by
    have : blk h w k₂ 0 ∈ K' := hk₂
    rwa [blk_zero_eq] at this
  obtain ⟨h11, h12⟩ := blocks_mem_KGL h w k₁ (hKK hd₁)
  obtain ⟨h21, h22⟩ := blocks_mem_KGL h w k₂ (hKK hd₂)
  have hab : absHalf w ((k₁ * m * k₂).1.val.det ^ b / (k₁ * m * k₂).2.val.det ^ a) =
      absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) := by
    rw [(absHalf_blockDet_KGL_invariant E a b w (k₁ * m) k₂ h21 h22).2]
    exact (absHalf_blockDet_KGL_invariant E a b w m k₁ h11 h12).1
  have e : (fun X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) =>
      f (x⁻¹ * blk h w (k₁ * m * k₂) (Multiplicative.toAdd X) * y)) =
      fun X => (fun Y : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) =>
        f (x⁻¹ * blk h w m (Multiplicative.toAdd Y) * y))
        (Multiplicative.ofAdd (k₂.1.val * Multiplicative.toAdd X * (k₂.2⁻¹).val)) := by
    funext X
    rw [(CtLevel.blk_mul_dgM E a b n h w (k₁ * m) k₂ _).2, (CtLevel.blk_mul_dgM E a b n h w m k₁ _).1]
    have hc₁ : x⁻¹ * CtLevel.dgM h w k₁ * x ∈ K' := by
      simpa using hN x⁻¹ (inv_mem hx) _ hd₁
    have hc₂ : y⁻¹ * CtLevel.dgM h w k₂ * y ∈ K' := by
      simpa using hN y⁻¹ (inv_mem hy) _ hd₂
    have e2 : x⁻¹ * (CtLevel.dgM h w k₁ * blk h w m (k₂.1.val * Multiplicative.toAdd X * (k₂.2⁻¹).val) *
        CtLevel.dgM h w k₂) * y =
        (x⁻¹ * CtLevel.dgM h w k₁ * x) *
          (x⁻¹ * blk h w m (k₂.1.val * Multiplicative.toAdd X * (k₂.2⁻¹).val) * y) *
          (y⁻¹ * CtLevel.dgM h w k₂ * y) := by group
    rw [e2, hf _ hc₁ _ hc₂]
    rfl
  unfold phi3
  rw [hab, e, HintInv.hint_intMat_mul_mul E a b w (fun Y => f (x⁻¹ * blk h w m (Multiplicative.toAdd Y) * y))
    k₂.1 k₂.2⁻¹ h21 (inv_mem h22)]

theorem constant_term_support {a b n : ℕ} (h : a + b = n) (w : Pl E) (f : GLw n w → ℂ) (x y : GLw n w)
    (m : GLw a w × GLw b w) (hm : phi3 h w f x y m ≠ 0) :
    ∃ X, blk h w m X ∈ ({x} : Set (GLw n w)) * tsupport f * {y⁻¹} := by
  obtain ⟨X, hX⟩ := CtLevel.exists_ne_zero_of_hint_ne_zero _ _ (right_ne_zero_of_mul hm)
  refine ⟨Multiplicative.toAdd X, ?_⟩
  have e : blk h w m (Multiplicative.toAdd X) =
      x * (x⁻¹ * blk h w m (Multiplicative.toAdd X) * y) * y⁻¹ := by group
  rw [e]
  exact Set.mul_mem_mul (Set.mul_mem_mul rfl (subset_tsupport _ hX)) rfl

theorem constant_term_compact_support {a b n : ℕ} (h : a + b = n) (w : Pl E) (f : GLw n w → ℂ)
    (hf : HasCompactSupport f) (x y : GLw n w) : HasCompactSupport (phi3 h w f x y) := by
  set C : Set (GLw n w) := ({x} : Set (GLw n w)) * tsupport f * {y⁻¹} with hCdef
  have hC : IsCompact C := (isCompact_singleton.mul hf).mul isCompact_singleton
  let ψ : GLw n w → ((Matrix (Fin a) (Fin a) (w.adicCompletion E) × (Matrix (Fin a) (Fin a) (w.adicCompletion E))ᵐᵒᵖ) ×
      (Matrix (Fin b) (Fin b) (w.adicCompletion E) × (Matrix (Fin b) (Fin b) (w.adicCompletion E))ᵐᵒᵖ)) :=
    fun g => ((CtLevel.blkTL h g.val, MulOpposite.op (CtLevel.blkTL h (g⁻¹).val)),
      (CtLevel.blkBR h g.val, MulOpposite.op (CtLevel.blkBR h (g⁻¹).val)))
  have hψ : Continuous ψ := by
    refine ((((CtLevel.continuous_blkTL h).comp Units.continuous_val).prodMk
      (MulOpposite.continuous_op.comp ((CtLevel.continuous_blkTL h).comp Units.continuous_coe_inv))).prodMk
      (((CtLevel.continuous_blkBR h).comp Units.continuous_val).prodMk
      (MulOpposite.continuous_op.comp ((CtLevel.continuous_blkBR h).comp Units.continuous_coe_inv))))
  let ι : GLw a w × GLw b w → _ := Prod.map (Units.embedProduct (Matrix (Fin a) (Fin a) (w.adicCompletion E)))
    (Units.embedProduct (Matrix (Fin b) (Fin b) (w.adicCompletion E)))
  have hι : Topology.IsClosedEmbedding ι :=
    Units.isClosedEmbedding_embedProduct.prodMap Units.isClosedEmbedding_embedProduct
  have hιψ : ∀ m X, ι m = ψ (blk h w m X) := by
    intro m X
    simp only [ι, ψ, Prod.map, Units.embedProduct_apply, CtLevel.blk_inv, CtLevel.blkTL_blk, CtLevel.blkBR_blk,
      Prod.fst_inv, Prod.snd_inv]
  have hT : IsCompact (ψ '' C) := hC.image hψ
  refine HasCompactSupport.intro' (hι.isCompact_preimage hT) (hT.isClosed.preimage hι.continuous) ?_
  intro m hm
  by_contra hne
  obtain ⟨X, hX⟩ := constant_term_support h w f x y m hne
  exact hm ⟨blk h w m X, hX, (hιψ m X).symm⟩

theorem constant_term_locally_constant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (K' : Subgroup (GLw n w)), IsOpen (K' : Set (GLw n w)) → K' ≤ GlobalTheory.LFun.KGL w (n := n) → (∀ k ∈ GlobalTheory.LFun.KGL w (n := n), ∀ k' ∈ K', k * k' * k⁻¹ ∈ K') → ∀ X : Finset (GLw n w), (∀ x ∈ X, x ∈ GlobalTheory.LFun.KGL w (n := n)) → (∀ k ∈ GlobalTheory.LFun.KGL w (n := n), ∃! x ∈ X, x⁻¹ * k ∈ K') → ∀ f : GLw n w → ℂ, IsHk K' f → ∀ x ∈ X, ∀ y ∈ X, IsLocallyConstant (phi3 h w f x y) ∧ HasCompactSupport (phi3 h w f x y) ∧ ∀ k₁ ∈ leviOf h w K', ∀ k₂ ∈ leviOf h w K', ∀ m, phi3 h w f x y (k₁ * m * k₂) = phi3 h w f x y m := by
  intro E _ _ _ n a b h w K' hKo hKK hN X hXK _ f hf x hx y hy
  have hbi := constant_term_bi_invariant h w K' hKK hN f hf.2.2.2 x y (hXK x hx) (hXK y hy)
  refine ⟨?_, constant_term_compact_support h w f hf.2.2.1 x y, fun k₁ h₁ k₂ h₂ m => hbi k₁ k₂ h₁ h₂ m⟩
  have hL : IsOpen (leviOf h w K') := by
    have e : leviOf h w K' = (CtLevel.dgM h w) ⁻¹' (K' : Set (GLw n w)) := by
      ext m
      simp only [leviOf, Set.mem_setOf_eq, Set.mem_preimage, blk_zero_eq, SetLike.mem_coe]
    rw [e]
    exact hKo.preimage (continuous_dgM h w)
  have h1 : (1 : GLw a w × GLw b w) ∈ leviOf h w K' := by
    show blk h w 1 0 ∈ K'
    rw [blk_zero_eq, map_one]
    exact K'.one_mem
  rw [IsLocallyConstant.iff_exists_open]
  intro m
  refine ⟨(fun m' => m⁻¹ * m') ⁻¹' leviOf h w K', hL.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · simpa using h1
  · intro m' hm'
    have := hbi 1 (m⁻¹ * m') h1 hm' m
    simpa [mul_assoc] using this

end GlobalTheory.CompanionTheory.GL3BlockMatrixLocal
end
end

section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.BCT PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.G8

noncomputable section

namespace GlobalTheory.CompanionTheory.LocalThetaTopology

theorem locallyCompact_units {M : Type} [Ring M] [TopologicalSpace M] [IsTopologicalRing M] [T2Space M]
    [LocallyCompactSpace M] : LocallyCompactSpace Mˣ :=
  Units.isClosedEmbedding_embedProduct.locallyCompactSpace

theorem secondCountable_units {M : Type} [Monoid M] [TopologicalSpace M] [SecondCountableTopology M] :
    SecondCountableTopology Mˣ := by
  haveI : SecondCountableTopology Mᵐᵒᵖ := (MulOpposite.opHomeomorph (M := M)).symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

theorem t2Space_units {M : Type} [Monoid M] [TopologicalSpace M] [T2Space M] : T2Space Mˣ :=
  Units.isEmbedding_embedProduct.t2Space

theorem top_GL {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R]
    [SecondCountableTopology R] (n : ℕ) :
    LocallyCompactSpace (GL (Fin n) R) ∧ SecondCountableTopology (GL (Fin n) R) ∧ T2Space (GL (Fin n) R) := by
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) R) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → R))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) R) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → R))
  haveI : T2Space (Matrix (Fin n) (Fin n) R) := inferInstanceAs (T2Space (Fin n → Fin n → R))
  exact ⟨locallyCompact_units, secondCountable_units, t2Space_units⟩

theorem continuous_thetaR {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (σ : A →+* A)
    (hσ : Continuous σ) (n : ℕ) : Continuous (thetaR σ n) :=
  Units.continuous_iff.2 ⟨(Units.continuous_coe_inv.matrix_map hσ).matrix_transpose,
    (Units.continuous_val.matrix_map hσ).matrix_transpose⟩

theorem countable_numberField (E : Type) [Field E] [NumberField E] : Countable E := by
  let b := Module.finBasis ℚ E
  exact Function.Injective.countable b.equivFun.injective

theorem countable_GL (E : Type) [Field E] [NumberField E] (n : ℕ) : Countable (GL (Fin n) E) := by
  haveI := countable_numberField E
  haveI : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))
  exact Function.Injective.countable (f := fun g : GL (Fin n) E => (g : Matrix (Fin n) (Fin n) E)) fun _ _ h => Units.ext h

theorem continuous_thF (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) : Continuous (thF E n) := by
  have h : (thF E n : GL (Fin n) (Af E) → GL (Fin n) (Af E)) = fun g =>
      PhiU n (Af E) * thetaR (conjFin (IsCMField.complexConj E).toRingEquiv) n g * (PhiU n (Af E))⁻¹ :=
    funext fun g => thetaGL_eq n (Af E) _ g
  rw [h]
  exact (continuous_const.mul (continuous_thetaR _ (continuous_conjFin _) n)).mul continuous_const

theorem topo : Topo := by
  intro E _ _ _ n
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele E
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField E
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele E
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField E
  obtain ⟨c1, c2, -⟩ := top_GL (R := ℂ) n
  exact ⟨top_GL n, top_GL n, ⟨c1, c2⟩, countable_GL E n, continuous_thF E n,
    continuous_thetaR _ Complex.continuous_conj n⟩

end GlobalTheory.CompanionTheory.LocalThetaTopology
end
end

section

open Matrix Polynomial
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.Tf.Loc (twConj)

noncomputable section

namespace GlobalTheory.CompanionTheory.EllipticTwist

theorem exists_eigenbasis {n : ℕ} (N : Matrix (Fin n) (Fin n) ℂ) (hs : N.charpoly.Separable) :
    ∃ (h : GL (Fin n) ℂ) (γ : Fin n → ℂ), Function.Injective γ ∧ (∀ i, N.charpoly.IsRoot (γ i)) ∧
      N * h.val = h.val * diagonal γ := by
  have hne : N.charpoly ≠ 0 := (Matrix.charpoly_monic N).ne_zero
  have hcard : N.charpoly.roots.toFinset.card = n := by
    rw [Multiset.toFinset_card_of_nodup (nodup_roots hs), splits_iff_card_roots.1 (IsAlgClosed.splits _),
      charpoly_natDegree_eq_dim, Fintype.card_fin]
  let e := Finset.equivFinOfCardEq hcard
  let γ : Fin n → ℂ := fun i => (e.symm i).1
  have hinj : Function.Injective γ := fun i j hij => e.symm.injective (Subtype.ext hij)
  have hroot : ∀ i, N.charpoly.IsRoot (γ i) := fun i =>
    (mem_roots hne).1 (Multiset.mem_toFinset.1 (e.symm i).2)
  have hev : ∀ i, ∃ v : Fin n → ℂ, v ≠ 0 ∧ (scalar (Fin n) (γ i) - N) *ᵥ v = 0 := fun i =>
    exists_mulVec_eq_zero_iff.2 (by rw [← eval_charpoly]; exact hroot i)
  choose v hv0 hv using hev
  have hNv : ∀ i, N *ᵥ v i = γ i • v i := fun i => by
    have h1 := hv i
    rw [sub_mulVec, sub_eq_zero] at h1
    rw [← h1]
    ext k
    simp [scalar_apply, mulVec_diagonal]
  have hli : LinearIndependent ℂ v :=
    Module.End.eigenvectors_linearIndependent' (Matrix.toLin' N) γ hinj v
      (fun i => Module.End.hasEigenvector_iff.2
        ⟨Module.End.mem_eigenspace_iff.2 (by simpa using hNv i), hv0 i⟩)
  have hu : IsUnit (Matrix.of v)ᵀ := linearIndependent_cols_iff_isUnit.1 hli
  obtain ⟨h, hh⟩ := hu
  refine ⟨h, γ, hinj, hroot, ?_⟩
  have hh' : h.val = (Matrix.of v)ᵀ := hh
  rw [hh']
  ext i j
  have h2 := congrFun (hNv j) i
  rw [mul_diagonal]
  simpa [Matrix.mul_apply, mulVec, dotProduct, mul_comm] using h2

variable {n : ℕ}

theorem theta_val (g : GL (Fin n) ℂ) :
    (thetaR (starRingEnd ℂ) n g).val = (g⁻¹).valᴴ := by
  ext i j
  simp [thetaR_val, conjTranspose_apply]

theorem theta_inv_val (g : GL (Fin n) ℂ) :
    ((thetaR (starRingEnd ℂ) n g)⁻¹).val = g.valᴴ := by
  rw [← map_inv, theta_val, inv_inv]

theorem theta_theta (g : GL (Fin n) ℂ) :
    thetaR (starRingEnd ℂ) n (thetaR (starRingEnd ℂ) n g) = g :=
  Units.ext (by rw [theta_val, theta_inv_val, conjTranspose_conjTranspose])

theorem offDiag_eq_zero (D : Matrix (Fin n) (Fin n) ℂ) (γ : Fin n → ℂ) (hγ : ∀ i, ‖γ i‖ = 1)
    (hinj : Function.Injective γ) (hD : D = diagonal γ * Dᴴ) {i j : Fin n} (hij : i ≠ j) : D i j = 0 := by
  have h2 : Dᴴ = D * diagonal (star γ) := by
    conv_lhs => rw [hD]
    rw [conjTranspose_mul, conjTranspose_conjTranspose, diagonal_conjTranspose]
  have h3 : D i j = γ i * (D i j * star (γ j)) := by
    conv_lhs => rw [hD, h2]
    rw [diagonal_mul, mul_diagonal]
    rfl
  by_contra hne
  have h4 : γ i * star (γ j) = 1 := by
    apply mul_left_cancel₀ hne
    linear_combination -h3
  have h5 : star (γ j) * γ j = 1 := by
    have := Complex.conj_mul' (γ j)
    rw [hγ j] at this
    simpa using this
  apply hij
  apply hinj
  linear_combination -γ i * h5 + γ j * h4

theorem ellDiag : EllDiag := by
  intro n d hd
  obtain ⟨hs, hn⟩ := hd
  obtain ⟨h, γ, hinj, hroot, hN⟩ := exists_eigenbasis _ hs
  have hγ : ∀ i, ‖γ i‖ = 1 := fun i => hn _ (hroot i)
  set θ := thetaR (starRingEnd ℂ) n with hθ
  let d₁ : GL (Fin n) ℂ := twConj θ h d
  have hnorm : (d₁ * θ d₁).val = diagonal γ := by
    have h1 : d₁ * θ d₁ = h⁻¹ * (d * θ d) * h := by
      simp [d₁, twConj, map_mul, map_inv, hθ, theta_theta, mul_assoc]
    rw [h1, Units.val_mul, Units.val_mul, mul_assoc, hN, ← mul_assoc, ← Units.val_mul]
    simp
  have hD : d₁.val = diagonal γ * d₁.valᴴ := by
    rw [← hnorm, ← theta_inv_val, ← Units.val_mul]
    simp [hθ]
  let b : Fin n → ℂ := fun i => d₁.val i i
  have hdiag : d₁.val = diagonal b := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [b]
    · rw [offDiag_eq_zero _ γ hγ hinj hD hij, diagonal_apply_ne _ hij]
  have hb0 : ∀ i, b i ≠ 0 := by
    intro i hi
    have h0 : d₁.val.det = 0 := by
      rw [hdiag, det_diagonal]
      exact Finset.prod_eq_zero (Finset.mem_univ i) hi
    have h1 := (Matrix.isUnit_iff_isUnit_det _).1 d₁.isUnit
    rw [h0] at h1
    exact not_isUnit_zero h1
  have hbγ : ∀ i, b i = γ i * (starRingEnd ℂ) (b i) := by
    intro i
    have h1 := congrFun (congrFun hD i) i
    rw [diagonal_mul] at h1
    simpa [conjTranspose_apply] using h1
  let s : Fin n → ℂ := fun i => ((Real.sqrt ‖b i‖ : ℝ) : ℂ)
  have hnb : ∀ i, 0 < ‖b i‖ := fun i => norm_pos_iff.2 (hb0 i)
  have hs0 : ∀ i, s i ≠ 0 := fun i =>
    Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (hnb i)).ne'
  have hss : ∀ i, s i * s i = (‖b i‖ : ℂ) := fun i => by
    simp only [s]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hnb i).le]
  let t : GL (Fin n) ℂ := ⟨diagonal s, diagonal fun i => (s i)⁻¹,
    by rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; ext i; exact mul_inv_cancel₀ (hs0 i),
    by rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; ext i; exact inv_mul_cancel₀ (hs0 i)⟩
  have htinv : (t⁻¹).val = diagonal fun i => (s i)⁻¹ := rfl
  have htθ : (θ t).val = diagonal fun i => (s i)⁻¹ := by
    rw [hθ, theta_val, htinv, diagonal_conjTranspose]
    congr 1
    ext i
    simp [s]
  let z : Fin n → ℂ := fun i => b i / (‖b i‖ : ℂ)
  have hz2 : ∀ i, z i ^ 2 = γ i := by
    intro i
    have hne : (‖b i‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hnb i).ne'
    have h1 := Complex.mul_conj' (b i)
    simp only [z]
    rw [div_pow, div_eq_iff (pow_ne_zero 2 hne), ← h1]
    conv_lhs => rw [sq]; enter [1]; rw [hbγ i]
    ring
  refine ⟨(h * t)⁻¹, twConj θ t d₁, z, ?_, ?_, ?_, ?_⟩
  · change (t⁻¹ * d₁ * θ t).val = _
    rw [Units.val_mul, Units.val_mul, htinv, hdiag, htθ, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    ext i
    have := hss i
    have h0 := hs0 i
    simp only [z]
    rw [← this]
    field_simp
  · intro i
    simp only [z]
    rw [norm_div, Complex.norm_real, norm_norm, div_self (hnb i).ne']
  · intro i j hij
    apply hinj
    have := hz2 i
    have := hz2 j
    simp only at hij
    rw [← hz2 i, ← hz2 j, hij]
  · simp [twConj, d₁, map_mul, map_inv, mul_assoc]

end GlobalTheory.CompanionTheory.EllipticTwist

end
end

section

open PositivityTheory.Rg.BcB.G8

open MeasureTheory

namespace GlobalTheory.CompanionTheory.HaarProd

theorem haarSplit : HaarSplit := by
  intro G A B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ _ α _ e
  have : (μ.map e).IsHaarMeasure := e.isHaarMeasure_map μ
  let β₀ : Measure B := Measure.haar
  have hc := Measure.isMulLeftInvariant_eq_smul (μ.map e) (α.prod β₀)
  have hpos := Measure.haarScalarFactor_pos_of_isHaarMeasure (μ.map e) (α.prod β₀)
  refine ⟨Measure.haarScalarFactor (μ.map e) (α.prod β₀) • β₀, ?_, ?_⟩
  · exact Measure.IsHaarMeasure.nnreal_smul _ hpos.ne'
  · rw [Measure.prod_smul_right]
    exact hc

end GlobalTheory.CompanionTheory.HaarProd
end

section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.QuotNorm

theorem count_isInvInvariant {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
    [MeasurableSingletonClass G] (H : Subgroup G) : (Measure.count : Measure H).IsInvInvariant := by
  have hinv : MeasurableInv H := ⟨(measurable_subtype_coe.inv).subtype_mk⟩
  refine ⟨?_⟩
  ext s hs
  rw [Measure.inv_apply, Measure.count_apply hs, Measure.count_apply hs.inv, ← Set.image_inv_eq_inv]
  exact congrArg ((↑) : ℕ∞ → ℝ≥0∞) (inv_injective.encard_image s)

theorem qIndep : PositivityTheory.Rg.BcB.G8.QIndep := by
  intro G _ _ _ _ _ μ _ _ H _ F ρ hF hFH hρ
  have := count_isInvInvariant H
  exact quotIntegral_eq (μG := μ) hF hFH hρ

end GlobalTheory.CompanionTheory.QuotNorm
end
end
