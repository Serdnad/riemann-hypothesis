module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1623
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1235
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle084
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle369
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1641
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.IwRed

open GlobalTheory.LeviDesc GlobalTheory.TwOrbConj

theorem avg_const {H : Type} [Group H] (c : ℂ) : avg (fun _ : H => c) = c := by
  have hR : rStab (fun _ : H => c) = ⊤ := by
    ext k; simp [mem_rStab]
  unfold avg
  simp only
  rw [hR, Subgroup.index_top]
  haveI : Unique (H ⧸ (⊤ : Subgroup H)) :=
    ⟨⟨QuotientGroup.mk 1⟩, fun a => QuotientGroup.induction_on a fun x => QuotientGroup.eq.2 (Subgroup.mem_top _)⟩
  rw [finsum_unique]
  simp

variable {G : Type} [Group G]

theorem avg_cavg (K P : Subgroup G) (δ : G) (hδ : δ ∈ P) (f : G → ℂ) (p : P) :
    avg (fun k : K.subgroupOf P => cavg K f (((p * k)⁻¹ * ⟨δ, hδ⟩ * (p * k) : P) : G)) =
      avg (fun k : K => f (((p : G) * k)⁻¹ * δ * ((p : G) * k))) := by
  have h : ∀ k : K.subgroupOf P, cavg K f (((p * k)⁻¹ * ⟨δ, hδ⟩ * (p * k) : P) : G) =
      avg (fun k : K => f (((p : G) * k)⁻¹ * δ * ((p : G) * k))) := by
    intro k
    have hk : ((k : P) : G) ∈ K := k.2
    unfold cavg
    rw [← avg_left (fun k' : K => f (((p : G) * k')⁻¹ * δ * ((p : G) * k'))) ⟨_, hk⟩]
    congr 1
    funext k'
    congr 1
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv, _root_.mul_inv_rev]
    group
  simp_rw [h]
  exact avg_const _

theorem mem_twCent_sub (P : Subgroup G) (δ : G) (hδ : δ ∈ P) (x : P) :
    x ∈ twCent (MonoidHom.id P) ⟨δ, hδ⟩ ↔ (x : G) ∈ twCent (MonoidHom.id G) δ := by
  rw [mem_twCent, mem_twCent, Subtype.ext_iff]
  simp

theorem inf_eq_comap (K P : Subgroup G) (δ : G) (hδ : δ ∈ P) (p : P) :
    twCent (MonoidHom.id P) ⟨δ, hδ⟩ ⊓ (K.subgroupOf P).map (MulAut.conj p).toMonoidHom =
      (twCent (MonoidHom.id G) δ ⊓ K.map (MulAut.conj (p : G)).toMonoidHom).comap P.subtype := by
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_comap, Subgroup.mem_map_equiv, mem_twCent_sub, MulAut.conj_symm_apply,
    Subgroup.mem_subgroupOf, Subgroup.coe_subtype, Subgroup.coe_mul, InvMemClass.coe_inv]

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem cptPart_map_sub (P : Subgroup G) (hP : IsClosed (P : Set G)) (δ : G) (hδ : δ ∈ P)
    (hT : twCent (MonoidHom.id G) δ ≤ P) :
    (cptPart (twCent (MonoidHom.id P) ⟨δ, hδ⟩)).map P.subtype = cptPart (twCent (MonoidHom.id G) δ) := by
  unfold cptPart
  rw [MonoidHom.map_closure]
  congr 1
  have hc : ∀ x : P, IsCompact (closure (Subgroup.zpowers x : Set P)) ↔
      IsCompact (closure (Subgroup.zpowers (x : G) : Set G)) := by
    intro x
    rw [(hP.isClosedEmbedding_subtypeVal).isInducing.isCompact_iff,
      ← (hP.isClosedEmbedding_subtypeVal).closure_image_eq]
    have : (Subtype.val '' (Subgroup.zpowers x : Set P)) = (Subgroup.zpowers (x : G) : Set G) := by
      rw [← Subgroup.coe_subtype, ← Subgroup.coe_map, MonoidHom.map_zpowers]
    first
      | (convert Iff.rfl using 3; exact this.symm)
      | (convert Iff.rfl using 3; exact this)
      | exact this ▸ Iff.rfl
  ext y
  constructor
  · rintro ⟨x, ⟨hx, hx'⟩, rfl⟩
    exact ⟨(mem_twCent_sub P δ hδ x).1 hx, (hc x).1 hx'⟩
  · rintro ⟨hy, hy'⟩
    exact ⟨⟨y, hT hy⟩, ⟨(mem_twCent_sub P δ hδ _).2 hy, (hc _).2 hy'⟩, rfl⟩

end GlobalTheory.IwRed

namespace GlobalTheory.IwRed

open GlobalTheory.LeviDesc GlobalTheory.TwOrbConj

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem relIndex_sub (K P : Subgroup G) (hP : IsClosed (P : Set G)) (δ : G) (hδ : δ ∈ P)
    (hT : twCent (MonoidHom.id G) δ ≤ P) (p : P) :
    (twCent (MonoidHom.id P) ⟨δ, hδ⟩ ⊓ (K.subgroupOf P).map (MulAut.conj p).toMonoidHom).relIndex
        (cptPart (twCent (MonoidHom.id P) ⟨δ, hδ⟩)) =
      (twCent (MonoidHom.id G) δ ⊓ K.map (MulAut.conj (p : G)).toMonoidHom).relIndex
        (cptPart (twCent (MonoidHom.id G) δ)) := by
  rw [inf_eq_comap, Subgroup.relIndex_comap, cptPart_map_sub P hP δ hδ hT]

theorem summand_sub (K P : Subgroup G) (hP : IsClosed (P : Set G)) (δ : G) (hδ : δ ∈ P)
    (hT : twCent (MonoidHom.id G) δ ≤ P) (f : G → ℂ) (p : P) :
    summand (MonoidHom.id P) (K.subgroupOf P) ⟨δ, hδ⟩ (fun x : P => cavg K f (x : G)) p =
      summand (MonoidHom.id G) K δ f p := by
  unfold summand
  rw [relIndex_sub K P hP δ hδ hT p]
  congr 1
  simpa using avg_cavg K P δ hδ f p

def dcMap (K P : Subgroup G) (δ : G) (hδ : δ ∈ P) :
    DoubleCoset.Quotient (twCent (MonoidHom.id P) ⟨δ, hδ⟩ : Set P) (K.subgroupOf P : Set P) →
      DoubleCoset.Quotient (twCent (MonoidHom.id G) δ : Set G) (K : Set G) :=
  fun q => DoubleCoset.mk _ K ((Quotient.out q : P) : G)

theorem dcMap_bij (K P : Subgroup G) (δ : G) (hδ : δ ∈ P) (hT : twCent (MonoidHom.id G) δ ≤ P)
    (hPK : ∀ g : G, ∃ p ∈ P, ∃ k ∈ K, g = p * k) : Function.Bijective (dcMap K P δ hδ) := by
  constructor
  · intro q₁ q₂ h
    obtain ⟨t, ht, k, hk, he⟩ := (@DoubleCoset.eq _ _ _ _ _ _).1 h
    have htP : t ∈ P := hT ht
    have hkP : k ∈ P := by
      have : k = ((Quotient.out q₁ : P) : G)⁻¹ * t⁻¹ * ((Quotient.out q₂ : P) : G) := by rw [he]; group
      rw [this]
      exact P.mul_mem (P.mul_mem (P.inv_mem (Quotient.out q₁).2) (P.inv_mem htP)) (Quotient.out q₂).2
    rw [← DoubleCoset.out_eq' q₁, ← DoubleCoset.out_eq' q₂, DoubleCoset.eq]
    refine ⟨⟨t, htP⟩, (mem_twCent_sub P δ hδ _).2 ht, ⟨k, hkP⟩, (Subgroup.mem_subgroupOf).2 hk, ?_⟩
    exact Subtype.ext (by simpa using he)
  · intro q
    obtain ⟨p, hp, k, hk, hg⟩ := hPK (Quotient.out q)
    refine ⟨DoubleCoset.mk _ _ (⟨p, hp⟩ : P), ?_⟩
    obtain ⟨t, ht, k', hk', he⟩ := (@DoubleCoset.eq _ _ _ _ _ _).1
      (DoubleCoset.out_eq' (DoubleCoset.mk _ _ (⟨p, hp⟩ : P))).symm
    rw [← DoubleCoset.out_eq' q]
    show DoubleCoset.mk _ K _ = _
    rw [DoubleCoset.eq]
    refine ⟨(t : G)⁻¹, (twCent (MonoidHom.id G) δ).inv_mem ((mem_twCent_sub P δ hδ t).1 ht), ((k' : P) : G)⁻¹ * k,
      K.mul_mem (K.inv_mem ((Subgroup.mem_subgroupOf).1 hk')) hk, ?_⟩
    rw [hg]
    have he' := congrArg (fun x : P => (x : G)) he
    simp only [Subgroup.coe_mul] at he'
    rw [he']
    group

theorem twOrb_sub : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K P : Subgroup G),
    IsOpen (K : Set G) → IsCompact (K : Set G) → IsClosed (P : Set G) → (∀ g : G, ∃ p ∈ P, ∃ k ∈ K, g = p * k) →
    ∀ (δ : G) (hδ : δ ∈ P), twCent (MonoidHom.id G) δ ≤ P → ∀ f : G → ℂ,
    (∃ K' : Subgroup G, IsOpen (K' : Set G) ∧ IsHecke K' f) →
    twOrb (MonoidHom.id G) K δ f = twOrb (MonoidHom.id P) (K.subgroupOf P) ⟨δ, hδ⟩ (fun p => GlobalTheory.LeviDesc.cavg K f (p : G)) := by
  intro G _ _ _ K P _ _ hP hPK δ hδ hT f _
  rw [twOrb_eq, twOrb_eq]
  rw [← finsum_comp_equiv (Equiv.ofBijective _ (dcMap_bij K P δ hδ hT hPK))]
  refine finsum_congr fun q => ?_
  rw [summand_sub K P hP δ hδ hT f]
  show summand _ K δ f (Quotient.out (DoubleCoset.mk _ K ((Quotient.out q : P) : G))) = _
  obtain ⟨t, ht, k, hk, he⟩ := (@DoubleCoset.eq _ _ _ _ _ _).1
    (DoubleCoset.out_eq' (DoubleCoset.mk _ K ((Quotient.out q : P) : G))).symm
  rw [he, summand_rep _ K δ f _ ht hk]

end GlobalTheory.IwRed
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.CtLevel

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_ne_zero_of_hint_ne_zero {H : Type} [Group H] (K : Subgroup H) (u : H → ℂ) (hu : hint K u ≠ 0) :
    ∃ x, u x ≠ 0 := by
  by_contra hc
  push_neg at hc
  exact hu (by simp [hint, hc])

theorem exists_ne_zero_of_avg_ne_zero {H : Type} [Group H] (u : H → ℂ) (hu : avg u ≠ 0) : ∃ x, u x ≠ 0 := by
  by_contra hc
  push_neg at hc
  exact hu (by simp [avg, hc])

theorem blk_inv {n a b : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    (blk h w m X)⁻¹ = blk h w m⁻¹ (-(m.1.val * X * (m.2⁻¹).val)) := by
  refine inv_eq_of_mul_eq_one_right (Units.ext ?_)
  rw [Units.val_mul, blk_val, blk_val, Units.val_one, reindex_apply, reindex_apply, submatrix_mul_equiv,
    fromBlocks_multiply]
  have e1 : m.1.val * (m.1⁻¹).val = 1 := Units.mul_inv _
  have e2 : m.2.val * (m.2⁻¹).val = 1 := Units.mul_inv _
  simp only [Prod.fst_inv, Prod.snd_inv, Matrix.mul_zero, add_zero, Matrix.zero_mul, zero_add]
  rw [e1, e2, ← Matrix.mul_assoc, e1, Matrix.one_mul, Matrix.mul_assoc m.1.val, add_comm]
  simp [fromBlocks_one]
  exact submatrix_one_equiv (blkEq h).symm

end GlobalTheory.BCT.CtLevel

open scoped Pointwise

namespace GlobalTheory.BCT.CtLevel

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def blkTL {R : Type} {a b n : ℕ} (h : a + b = n) (g : Matrix (Fin n) (Fin n) R) : Matrix (Fin a) (Fin a) R :=
  (reindex (blkEq h).symm (blkEq h).symm g).toBlocks₁₁

def blkBR {R : Type} {a b n : ℕ} (h : a + b = n) (g : Matrix (Fin n) (Fin n) R) : Matrix (Fin b) (Fin b) R :=
  (reindex (blkEq h).symm (blkEq h).symm g).toBlocks₂₂

theorem blkTL_blk {n a b : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) : blkTL h (blk h w m X).val = m.1.val := by
  rw [blkTL, blk_val, ← reindex_symm, Equiv.symm_apply_apply, toBlocks_fromBlocks₁₁]

theorem blkBR_blk {n a b : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) : blkBR h (blk h w m X).val = m.2.val := by
  rw [blkBR, blk_val, ← reindex_symm, Equiv.symm_apply_apply, toBlocks_fromBlocks₂₂]

theorem continuous_blkTL {R : Type} [TopologicalSpace R] {a b n : ℕ} (h : a + b = n) :
    Continuous (blkTL (R := R) h) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [blkTL, toBlocks₁₁, reindex_apply, submatrix_apply, of_apply]
  exact (continuous_apply _).comp (continuous_apply _)

theorem continuous_blkBR {R : Type} [TopologicalSpace R] {a b n : ℕ} (h : a + b = n) :
    Continuous (blkBR (R := R) h) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [blkBR, toBlocks₂₂, reindex_apply, submatrix_apply, of_apply]
  exact (continuous_apply _).comp (continuous_apply _)

theorem hasCompactSupport_ctMu_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b n : ℕ) (h : a + b = n) (w : Pl E)
    (μ : (w.adicCompletion E)ˣ →* ℂˣ) (f : UL n w → ℂ), IsSplitAt w → HasCompactSupport f →
    HasCompactSupport (ctMu h w μ f) := by
  intro E _ _ _ a b n h w μ f hw hf
  have hUL : ∀ y : GLw n w, y ∈ UL n w := fun y => by rw [UL, if_pos hw]; trivial
  set S : Set (GLw n w) := Subtype.val '' tsupport f with hSdef
  have hS : IsCompact S := hf.image continuous_subtype_val
  have hK := (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).2
  set C : Set (GLw n w) := (GlobalTheory.LFun.KGL w (n := n) : Set (GLw n w)) * S * (GlobalTheory.LFun.KGL w (n := n) : Set (GLw n w)) with hCdef
  have hC : IsCompact C := (hK.mul hS).mul hK
  have hmem : ∀ m, ctMu h w μ f m ≠ 0 → ∃ X, blk h w m X ∈ C := by
    intro m hm
    have h1 := right_ne_zero_of_mul (right_ne_zero_of_mul hm)
    obtain ⟨X, hX⟩ := exists_ne_zero_of_hint_ne_zero _ _ h1
    obtain ⟨k, hk⟩ := exists_ne_zero_of_avg_ne_zero _ hX
    refine ⟨Multiplicative.toAdd X, ?_⟩
    set y := (k : GLw n w)⁻¹ * blk h w m (Multiplicative.toAdd X) * k with hy
    have hyS : y ∈ S := by
      refine ⟨⟨y, hUL y⟩, subset_tsupport _ ?_, rfl⟩
      have : toSub (UL n w) y = ⟨y, hUL y⟩ := by rw [toSub, dite_eq_left (hUL y)]
      simpa [this] using hk
    have e : blk h w m (Multiplicative.toAdd X) = (k : GLw n w) * y * (k : GLw n w)⁻¹ := by
      rw [hy]; group
    rw [e]
    exact Set.mul_mem_mul (Set.mul_mem_mul k.2 hyS) (inv_mem k.2)
  let ψ : GLw n w → ((Matrix (Fin a) (Fin a) (w.adicCompletion E) × (Matrix (Fin a) (Fin a) (w.adicCompletion E))ᵐᵒᵖ) ×
      (Matrix (Fin b) (Fin b) (w.adicCompletion E) × (Matrix (Fin b) (Fin b) (w.adicCompletion E))ᵐᵒᵖ)) :=
    fun g => ((blkTL h g.val, MulOpposite.op (blkTL h (g⁻¹).val)), (blkBR h g.val, MulOpposite.op (blkBR h (g⁻¹).val)))
  have hψ : Continuous ψ := by
    refine ((((continuous_blkTL h).comp Units.continuous_val).prodMk
      (MulOpposite.continuous_op.comp ((continuous_blkTL h).comp Units.continuous_coe_inv))).prodMk
      (((continuous_blkBR h).comp Units.continuous_val).prodMk
      (MulOpposite.continuous_op.comp ((continuous_blkBR h).comp Units.continuous_coe_inv))))
  let ι : GLw a w × GLw b w → _ := Prod.map (Units.embedProduct (Matrix (Fin a) (Fin a) (w.adicCompletion E)))
    (Units.embedProduct (Matrix (Fin b) (Fin b) (w.adicCompletion E)))
  have hι : Topology.IsClosedEmbedding ι :=
    Units.isClosedEmbedding_embedProduct.prodMap Units.isClosedEmbedding_embedProduct
  have hιψ : ∀ m X, ι m = ψ (blk h w m X) := by
    intro m X
    simp only [ι, ψ, Prod.map, Units.embedProduct_apply, blk_inv, blkTL_blk, blkBR_blk, Prod.fst_inv, Prod.snd_inv]
  have hT : IsCompact (ψ '' C) := hC.image hψ
  refine HasCompactSupport.intro' (hι.isCompact_preimage hT) (hT.isClosed.preimage hι.continuous) ?_
  intro m hm
  by_contra hne
  obtain ⟨X, hX⟩ := hmem m hne
  exact hm ⟨blk h w m X, hX, (hιψ m X).symm⟩

end GlobalTheory.BCT.CtLevel
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.CtLevel

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem continuous_dgM_inl {a b n : ℕ} (h : a + b = n) (w : Pl E) :
    Continuous ((dgM h w).comp (MonoidHom.inl (GLw a w) (GLw b w))) := by
  rw [Units.continuous_iff]
  constructor
  · change Continuous fun x : GLw a w => dgMat h x.val (1 : GLw b w).val
    exact (Continuous.matrix_fromBlocks Units.continuous_val continuous_const continuous_const
      continuous_const).matrix_reindex _ _
  · have : (fun x : GLw a w => (((dgM h w).comp (MonoidHom.inl (GLw a w) (GLw b w))) x)⁻¹.val) =
        fun x => dgMat h (x⁻¹).val ((1 : GLw b w)⁻¹).val := by
      funext x
      rw [← map_inv]
      rfl
    rw [this]
    exact (Continuous.matrix_fromBlocks Units.continuous_coe_inv continuous_const continuous_const
      continuous_const).matrix_reindex _ _

theorem continuous_dgM_inr {a b n : ℕ} (h : a + b = n) (w : Pl E) :
    Continuous ((dgM h w).comp (MonoidHom.inr (GLw a w) (GLw b w))) := by
  rw [Units.continuous_iff]
  constructor
  · change Continuous fun x : GLw b w => dgMat h (1 : GLw a w).val x.val
    exact (Continuous.matrix_fromBlocks continuous_const continuous_const continuous_const
      Units.continuous_val).matrix_reindex _ _
  · have : (fun x : GLw b w => (((dgM h w).comp (MonoidHom.inr (GLw a w) (GLw b w))) x)⁻¹.val) =
        fun x => dgMat h ((1 : GLw a w)⁻¹).val (x⁻¹).val := by
      funext x
      rw [← map_inv]
      rfl
    rw [this]
    exact (Continuous.matrix_fromBlocks continuous_const continuous_const continuous_const
      Units.continuous_coe_inv).matrix_reindex _ _

theorem continuous_det_GLw (m : ℕ) (w : Pl E) :
    Continuous (GeneralLinearGroup.det : GLw m w → (w.adicCompletion E)ˣ) := by
  rw [Units.continuous_iff]
  constructor
  · change Continuous fun x : GLw m w => (x.val).det
    exact Units.continuous_val.matrix_det
  · have : (fun x : GLw m w => ((GeneralLinearGroup.det x)⁻¹ : (w.adicCompletion E)ˣ).val) =
        fun x => ((x⁻¹).val).det := by
      funext x
      rw [← map_inv]
      rfl
    rw [this]
    exact Units.continuous_coe_inv.matrix_det

theorem isOpen_detKer (m : ℕ) (w : Pl E) (μ : (w.adicCompletion E)ˣ →* ℂˣ) (hμ : IsOpen {x | μ x = 1}) :
    IsOpen ((μ.ker.comap GeneralLinearGroup.det : Subgroup (GLw m w)) : Set (GLw m w)) :=
  hμ.preimage (continuous_det_GLw m w)

theorem thL_split (m : ℕ) (w : Pl E) (hw : IsSplitAt w) : thL m w = MonoidHom.id _ := by
  rw [thL, if_pos hw]

end GlobalTheory.BCT.CtLevel

theorem GlobalTheory.BCT.CtLevel.isLevel_lev_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b n : ℕ) (h : a + b = n) (w : Pl E)
    (N : Subgroup (GLw n w)) (μ : (w.adicCompletion E)ˣ →* ℂˣ), IsSplitAt w → IsOpen (N : Set (GLw n w)) →
    IsOpen {x | μ x = 1} →
    IsLevel (thL a w) (GlobalTheory.LFun.KGL w (n := a)) (lev₁ h w N μ) ∧ IsLevel (thL b w) (GlobalTheory.LFun.KGL w (n := b)) (lev₂ h w N μ) := by
  intro E _ _ _ a b n h w N μ hw hN hμ
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · exact (((GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).1.inter
      (hN.preimage (continuous_dgM_inl h w))).inter (isOpen_detKer a w μ hμ))
  · exact inf_le_left.trans inf_le_left
  · intro k hk
    rw [thL_split a w hw]
    exact hk
  · exact (((GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).1.inter
      (hN.preimage (continuous_dgM_inr h w))).inter (isOpen_detKer b w μ hμ))
  · exact inf_le_left.trans inf_le_left
  · intro k hk
    rw [thL_split b w hw]
    exact hk
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LeviDesc

theorem sign_sq_eq_one_of_pow {k : Type} [Field k] (n : ℕ) : ((-1 : k) ^ n) ^ 2 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]

theorem det_adL_sq_mul_det_pow : ∀ (k : Type) [Field k] (a b : ℕ) (A : GL (Fin a) k)
    (B : Matrix (Fin b) (Fin b) k),
    LinearMap.det (GlobalTheory.LeviDesc.adL A B) ^ 2 * A.val.det ^ (2 * b)
      = resultant A.val.charpoly B.charpoly ^ 2 := by
  intro k _ a b A B
  let e : Matrix (Fin a) (Fin b) k ≃ₗ[k] ((Fin b → k) →ₗ[k] (Fin a → k)) := Matrix.toLin'
  let F : ((Fin b → k) →ₗ[k] (Fin a → k)) →ₗ[k] ((Fin b → k) →ₗ[k] (Fin a → k)) :=
    LinearMap.llcomp k (Fin b → k) (Fin a → k) (Fin a → k) (Matrix.toLin' A.val)
  let G : ((Fin b → k) →ₗ[k] (Fin a → k)) →ₗ[k] ((Fin b → k) →ₗ[k] (Fin a → k)) :=
    LinearMap.lcomp k (Fin a → k) (Matrix.toLin' B)
  have hcomp : F ∘ₗ ((e : _ →ₗ[k] _) ∘ₗ GlobalTheory.LeviDesc.adL A B ∘ₗ (e.symm : _ →ₗ[k] _)) = F - G := by
    apply LinearMap.ext
    intro ψ
    obtain ⟨X, rfl⟩ := e.surjective ψ
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      LinearMap.sub_apply, F, G, e, LinearMap.llcomp_apply, LinearMap.lcomp_apply,
      GlobalTheory.LeviDesc.adL, LinearMap.coe_mk, AddHom.coe_mk]
    change Matrix.toLin' A.val ∘ₗ Matrix.toLin' (X - (A⁻¹ : GL (Fin a) k).val * X * B)
      = Matrix.toLin' A.val ∘ₗ Matrix.toLin' X - Matrix.toLin' X ∘ₗ Matrix.toLin' B
    rw [← Matrix.toLin'_mul, ← Matrix.toLin'_mul, ← Matrix.toLin'_mul, ← map_sub]
    congr 1
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.one_mul]
  have h1 := congrArg LinearMap.det hcomp
  rw [LinearMap.det_comp, LinearMap.det_conj, GlobalTheory.DetAdResultant.det_ad_eq_resultant,
    Matrix.charpoly_toLin', Matrix.charpoly_toLin'] at h1
  have hz : (0 : (Fin b → k) →ₗ[k] (Fin b → k)).charpoly = X ^ b := by
    rw [← (Matrix.toLin' : Matrix (Fin b) (Fin b) k ≃ₗ[k] _).map_zero, Matrix.charpoly_toLin',
      Matrix.charpoly_zero, Fintype.card_fin]
  have hF0 : F - LinearMap.lcomp k (Fin a → k) (0 : (Fin b → k) →ₗ[k] (Fin b → k)) = F := by
    apply LinearMap.ext
    intro ψ
    apply LinearMap.ext
    intro v
    simp [F]
  have h0 : LinearMap.det F = (-1) ^ (a * b) * A.val.charpoly.coeff 0 ^ b := by
    have h := GlobalTheory.DetAdResultant.det_ad_eq_resultant k (Fin a → k) (Fin b → k) (Matrix.toLin' A.val) 0
    rw [hF0, Matrix.charpoly_toLin', hz] at h
    rw [h, natDegree_X_pow, resultant_X_pow_right _ _ _ le_rfl, Matrix.charpoly_natDegree_eq_dim,
      Fintype.card_fin]
  rw [← h1, h0, pow_mul, Matrix.det_eq_sign_charpoly_coeff, Fintype.card_fin, mul_pow ((-1 : k) ^ a),
    sign_sq_eq_one_of_pow, one_mul]
  have hs := sign_sq_eq_one_of_pow (k := k) (a * b)
  linear_combination (-(LinearMap.det (GlobalTheory.LeviDesc.adL A B) ^ 2 * (A.val.charpoly.coeff 0 ^ b) ^ 2)) * hs

end GlobalTheory.LeviDesc
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF


theorem _root_.GlobalTheory.T.unitaryAdelicPoint_eq_real_mul_finite_both_orders : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (p : GAF σ J), ∃ a ∈ GlobalTheory.WeilPartsF.GinfCF σ J, ∃ k ∈ GlobalTheory.WeilPartsF.GfCF σ J, p = a * k ∧ p = k * a := by
  first | exact @GlobalTheory.WeilPartsF.exists_real_finite_mul | exact GlobalTheory.WeilPartsF.exists_real_finite_mul | (intros; apply GlobalTheory.WeilPartsF.exists_real_finite_mul <;> assumption)
end
