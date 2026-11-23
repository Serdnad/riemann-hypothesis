module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1623
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import GroundTheory.AutomorphicForms.GLnLocal
public import GroundTheory.AutomorphicForms.Iwasawa
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1624
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1622
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle404
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1640
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.UniformSpace.Uniformizable
import Std.Tactic.BVDecide.Normalize.BitVec
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LeviDesc.UnipMean

section Generic

variable {G : Type} [Group G]

def core (K K' : Subgroup G) : Subgroup G where
  carrier := {c | ∀ k ∈ K, k⁻¹ * c * k ∈ K'}
  one_mem' := by intro k _; simp
  mul_mem' := by
    intro a b ha hb k hk
    have : k⁻¹ * (a * b) * k = (k⁻¹ * a * k) * (k⁻¹ * b * k) := by group
    rw [this]; exact K'.mul_mem (ha k hk) (hb k hk)
  inv_mem' := by
    intro a ha k hk
    have : k⁻¹ * a⁻¹ * k = (k⁻¹ * a * k)⁻¹ := by group
    rw [this]; exact K'.inv_mem (ha k hk)

theorem isOpen_core [TopologicalSpace G] [IsTopologicalGroup G] (K K' : Subgroup G) (hK : IsCompact (K : Set G))
    (hK' : IsOpen (K' : Set G)) : IsOpen (core K K' : Set G) := by
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  have h := hK.eventually_forall_of_forall_eventually (x₀ := (1 : G)) (P := fun c k => k⁻¹ * c * k ∈ K') ?_
  · exact h
  intro k _
  have hc : Continuous fun p : G × G => p.2⁻¹ * p.1 * p.2 := by fun_prop
  have h1 : (fun p : G × G => p.2⁻¹ * p.1 * p.2) (1, k) ∈ (K' : Set G) := by simp [K'.one_mem]
  exact hc.continuousAt.preimage_mem_nhds (hK'.mem_nhds h1)

theorem cavg_mul_core (K K' : Subgroup G) (f : G → ℂ) (hf : ∀ k ∈ K', ∀ x, f (x * k) = f x) (x c : G)
    (hc : c ∈ core K K') : cavg K f (x * c) = cavg K f x := by
  unfold cavg
  congr 1
  funext k
  have := hf _ (hc k k.2) ((k : G)⁻¹ * x * k)
  rw [← this]
  congr 1
  group

theorem exists_of_cavg_ne_zero (K : Subgroup G) (f : G → ℂ) (x : G) (h : cavg K f x ≠ 0) :
    ∃ k ∈ K, f (k⁻¹ * x * k) ≠ 0 := by
  by_contra hn
  push_neg at hn
  apply h
  unfold cavg avg
  have : (fun k : K => f ((k : G)⁻¹ * x * k)) = fun _ => 0 := funext fun k => hn k k.2
  rw [this]
  simp

end Generic

section Block

variable {E : Type} [Field E] [NumberField E] {n a b : ℕ} (h : a + b = n) (w : Pl E)

theorem isUnit_blkMat (m : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    IsUnit (Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
      (Matrix.fromBlocks m.1.val (m.1.val * X) 0 m.2.val)) := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]
  exact ((Matrix.isUnit_iff_isUnit_det _).1 m.1.isUnit).mul ((Matrix.isUnit_iff_isUnit_det _).1 m.2.isUnit)

theorem blk_val (m : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    (blk h w m X).val = Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
      (Matrix.fromBlocks m.1.val (m.1.val * X) 0 m.2.val) := by
  unfold blk
  simp only
  rw [dite_eq_left (isUnit_blkMat h w m X)]
  rfl

theorem blk_add (m : GLw a w × GLw b w) (x y : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    blk h w m (x + y) = blk h w m x * blk h w 1 y := by
  ext1
  rw [Units.val_mul, blk_val, blk_val, blk_val]
  simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, Prod.fst_one,
    Prod.snd_one, Units.val_one, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero,
    zero_add, Matrix.mul_add]
  congr 2
  exact add_comm _ _

theorem blk_one_zero : blk h w (1 : GLw a w × GLw b w) 0 = 1 := by
  ext1
  rw [blk_val]
  simp only [Prod.fst_one, Prod.snd_one, Units.val_one, Matrix.mul_zero, Matrix.fromBlocks_one, Units.val_one]
  exact Matrix.submatrix_one_equiv _

theorem blk_one_neg (y : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    (blk h w 1 y)⁻¹ = blk h w 1 (-y) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← blk_add, add_neg_cancel, blk_one_zero]

theorem continuous_blk_one : Continuous fun y : Matrix (Fin a) (Fin b) (w.adicCompletion E) => blk h w 1 y := by
  have hv : Continuous fun y : Matrix (Fin a) (Fin b) (w.adicCompletion E) => (blk h w 1 y).val := by
    simp only [blk_val, Prod.fst_one, Prod.snd_one, Units.val_one, Matrix.one_mul]
    exact (continuous_const.matrix_fromBlocks continuous_id continuous_const continuous_const).matrix_reindex _ _
  refine Units.continuous_iff.2 ⟨hv, ?_⟩
  simp only [blk_one_neg]
  exact hv.comp continuous_neg

def corner (m : GLw a w × GLw b w) (g : GLw n w) : Matrix (Fin a) (Fin b) (w.adicCompletion E) :=
  (m.1⁻¹).val * (Matrix.reindex (finSumFinEquiv.trans (finCongr h)).symm (finSumFinEquiv.trans (finCongr h)).symm
    g.val).toBlocks₁₂

theorem corner_blk (m : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    corner h w m (blk h w m X) = X := by
  rw [corner, blk_val, ← Matrix.reindex_symm, Equiv.symm_apply_apply, Matrix.toBlocks_fromBlocks₁₂,
    ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]

theorem continuous_corner (m : GLw a w × GLw b w) : Continuous (corner h w m) := by
  unfold corner
  refine continuous_const.matrix_mul ?_
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Matrix.toBlocks₁₂, Matrix.of_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  exact (Units.continuous_val.matrix_elem _ _)

end Block

theorem cavg_blk_locConst_compactSupport : ∀ (E : Type) [Field E] [NumberField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (f : GLw n w → ℂ), (∃ K' : Subgroup (GLw n w), IsOpen (K' : Set (GLw n w)) ∧ IsHecke K' f) → ∀ m : GLw a w × GLw b w, (∃ U : AddSubgroup (Matrix (Fin a) (Fin b) (w.adicCompletion E)), IsOpen (U : Set (Matrix (Fin a) (Fin b) (w.adicCompletion E))) ∧ ∀ x, ∀ y ∈ U, GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w (n := n)) f (blk h w m (x + y)) = GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w (n := n)) f (blk h w m x)) ∧ HasCompactSupport (fun X => GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w (n := n)) f (blk h w m X)) := by
  intro E _ _ n a b h w f ⟨K', hK'o, hf⟩ m
  obtain ⟨_, hKc⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n
  have hCo : IsOpen (core (GlobalTheory.LFun.KGL w (n := n)) K' : Set (GLw n w)) := isOpen_core _ _ hKc hK'o
  let U : AddSubgroup (Matrix (Fin a) (Fin b) (w.adicCompletion E)) :=
    { carrier := {y | blk h w 1 y ∈ core (GlobalTheory.LFun.KGL w (n := n)) K'}
      zero_mem' := by
        simp only [Set.mem_setOf_eq, blk_one_zero]
        exact Subgroup.one_mem _
      add_mem' := by
        intro x y hx hy
        simp only [Set.mem_setOf_eq] at *
        rw [blk_add]
        exact Subgroup.mul_mem _ hx hy
      neg_mem' := by
        intro x hx
        simp only [Set.mem_setOf_eq] at *
        rw [← blk_one_neg]
        exact Subgroup.inv_mem _ hx }
  refine ⟨⟨U, hCo.preimage (continuous_blk_one h w), fun x y hy => ?_⟩, ?_⟩
  · rw [blk_add]
    exact cavg_mul_core _ _ f (fun k hk x => (hf.2 k hk x).2) _ _ hy
  · let S : Set (GLw n w) := (fun p : GLw n w × GLw n w × GLw n w => p.1 * p.2.1 * p.2.2) ''
      ((GlobalTheory.LFun.KGL w (n := n) : Set (GLw n w)) ×ˢ (tsupport f ×ˢ (GlobalTheory.LFun.KGL w (n := n) : Set (GLw n w))))
    have hS : IsCompact S := (hKc.prod (hf.1.isCompact.prod hKc)).image (by fun_prop)
    refine HasCompactSupport.intro (hS.image (continuous_corner h w m)) fun X hX => ?_
    by_contra hne
    obtain ⟨k, hk, hfk⟩ := exists_of_cavg_ne_zero _ f _ hne
    refine hX ⟨blk h w m X, ⟨(k, k⁻¹ * blk h w m X * k, k⁻¹),
      ⟨hk, subset_tsupport _ hfk, Subgroup.inv_mem _ hk⟩, by group⟩, corner_blk h w m X⟩

end GlobalTheory.LeviDesc.UnipMean
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LeviDesc

open ValuativeRel

theorem mem_integer_iff_mem_Ov {E : Type} [Field E] [NumberField E] (w : Pl E) (x : w.adicCompletion E) :
    x ∈ 𝒪[w.adicCompletion E] ↔ x ∈ Ov E w := by
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation _)
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))).le_one_iff_le_one

theorem integralGL_le_KGL {E : Type} [Field E] [NumberField E] (w : Pl E) (n : ℕ) :
    GroundTheory.Automorphic.GLnLocal.integralGL (w.adicCompletion E) n ≤ GlobalTheory.LFun.KGL w (n := n) := by
  intro g hg
  obtain ⟨h1, h2⟩ := (GroundTheory.Automorphic.GLnLocal.mem_integralGL_iff _ n).1 hg
  let A : Matrix (Fin n) (Fin n) (Ov E w) :=
    Matrix.of fun i j => ⟨g i j, (mem_integer_iff_mem_Ov w _).1 (h1 i j)⟩
  let B : Matrix (Fin n) (Fin n) (Ov E w) :=
    Matrix.of fun i j => ⟨(g⁻¹ : GL (Fin n) (w.adicCompletion E)) i j, (mem_integer_iff_mem_Ov w _).1 (h2 i j)⟩
  have hinj : Function.Injective (RingHom.mapMatrix (m := Fin n) (Ov E w).subtype) :=
    fun M N h => Matrix.ext fun i j => Subtype.ext (congrFun (congrFun h i) j)
  have hA : RingHom.mapMatrix (Ov E w).subtype A = (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := rfl
  have hB : RingHom.mapMatrix (Ov E w).subtype B =
      ((g⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := rfl
  have hAB : A * B = 1 := hinj (by rw [map_mul, map_one, hA, hB, Units.mul_inv])
  have hBA : B * A = 1 := hinj (by rw [map_mul, map_one, hA, hB, Units.inv_mul])
  exact ⟨⟨A, B, hAB, hBA⟩, Units.ext hA⟩

theorem exists_parabolic_mul_maximalCompact : ∀ (E : Type) [Field E] [NumberField E] (a n : ℕ) (w : Pl E) (g : GLw n w),
    ∃ p ∈ GlobalTheory.LeviDesc.parP a n w, ∃ k ∈ GlobalTheory.LFun.KGL w (n := n), g = p * k := by
  intro E _ _ a n w g
  have hβ : Monotone fun i : Fin n => decide (a ≤ (i : ℕ)) := by
    intro i j hij
    by_cases h : a ≤ (i : ℕ)
    · have : a ≤ (j : ℕ) := h.trans (Fin.le_iff_val_le_val.1 hij)
      simp [h, this]
    · simp [h]
  obtain ⟨p, hp, k, hk, rfl⟩ :=
    GroundTheory.Automorphic.Iwasawa.exists_blockUpper_mul_integralGL (w.adicCompletion E) n hβ g
  exact ⟨p, hp, k, integralGL_le_KGL w n hk, rfl⟩

end GlobalTheory.LeviDesc
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.BCT.TrKer.HopStab

theorem toSub_mul_right {G : Type} [Group G] (H : Subgroup G) (K : Subgroup H) (u : H → ℂ)
    (hu : ∀ k ∈ K, ∀ x, u (x * k) = u x) (y : G) (k : H) (hk : k ∈ K) :
    u (toSub H (y * k)) = u (toSub H y) := by
  unfold toSub
  by_cases hy : y ∈ H
  · have h2 : y * (k : G) ∈ H := H.mul_mem hy k.2
    rw [dite_eq_left h2, dite_eq_left hy]
    exact hu k hk ⟨y, hy⟩
  · have h2 : y * (k : G) ∉ H := fun h => hy (by simpa using H.mul_mem h (H.inv_mem k.2))
    rw [dite_eq_right h2, dite_eq_right hy]

theorem toSub_mul_left {G : Type} [Group G] (H : Subgroup G) (K : Subgroup H) (u : H → ℂ)
    (hu : ∀ k ∈ K, ∀ x, u (k * x) = u x) (y : G) (k : H) (hk : k ∈ K) :
    u (toSub H (k * y)) = u (toSub H y) := by
  unfold toSub
  by_cases hy : y ∈ H
  · have h2 : (k : G) * y ∈ H := H.mul_mem k.2 hy
    rw [dite_eq_left h2, dite_eq_left hy]
    exact hu k hk ⟨y, hy⟩
  · have h2 : (k : G) * y ∉ H := fun h => hy (by simpa using H.mul_mem (H.inv_mem k.2) h)
    rw [dite_eq_right h2, dite_eq_right hy]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem mem_loc {S : Set (Pl E)} {K' : ∀ w : Pl E, Subgroup (UL n w)} {k : finU (E := E) (n := n)} (hk : k ∈ globLev S K')
    {w : Pl E} (hw : w ∈ S) : ∃ k' : UL n w, k' ∈ K' w ∧ (k' : GLw n w) = cLoc w k.1 := by
  unfold globLev at hk
  have := (Subgroup.mem_iInf.1 hk w)
  have := Subgroup.mem_iInf.1 this hw
  simpa using this

theorem globFn_mul_right {S : Set (Pl E)} {K' : ∀ w : Pl E, Subgroup (UL n w)} {f : ∀ w : Pl E, UL n w → ℂ}
    (hf : ∀ w, IsHecke (K' w) (f w)) {k : finU (E := E) (n := n)} (hk : k ∈ globLev S K') (x : finU (E := E) (n := n)) :
    globFn S f (x * k) = globFn S f x := by
  unfold globFn
  refine finprod_mem_congr rfl fun w hw => ?_
  obtain ⟨k', hk', he⟩ := mem_loc hk hw
  rw [Subgroup.coe_mul, map_mul, ← he]
  exact toSub_mul_right _ (K' w) (f w) (fun k hk x => ((hf w).2 k hk x).2) _ k' hk'

theorem globFn_mul_left {S : Set (Pl E)} {K' : ∀ w : Pl E, Subgroup (UL n w)} {f : ∀ w : Pl E, UL n w → ℂ}
    (hf : ∀ w, IsHecke (K' w) (f w)) {k : finU (E := E) (n := n)} (hk : k ∈ globLev S K') (x : finU (E := E) (n := n)) :
    globFn S f (k * x) = globFn S f x := by
  unfold globFn
  refine finprod_mem_congr rfl fun w hw => ?_
  obtain ⟨k', hk', he⟩ := mem_loc hk hw
  rw [Subgroup.coe_mul, map_mul, ← he]
  exact toSub_mul_left _ (K' w) (f w) (fun k hk x => ((hf w).2 k hk x).1) _ k' hk'

end GlobalTheory.BCT.TrKer.HopStab

namespace GlobalTheory.BCT.TrKer.HopStab
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem hopM_apply {S : Set (Pl E)} {lam : InfinitePlace E → DomWeight n} {K' : ∀ w : Pl E, Subgroup (UL n w)}
    (f : ∀ w : Pl E, UL n w → ℂ) (F : finU (E := E) (n := n) → Module.Dual ℂ (Wsp lam))
    (hfin : (Function.support fun q : finU (E := E) (n := n) ⧸ globLev S K' =>
      globFn S f q.out • (rightReg ℂ (finU (E := E) (n := n)) (Module.Dual ℂ (Wsp lam)) q.out ∘ₗ LinearMap.id)).Finite)
    (x : finU (E := E) (n := n)) :
    hopM S lam K' f F x = (((globLev S K').relIndex (globLev S (KL n)) : ℕ) : ℂ)⁻¹ •
      ∑ᶠ q : finU (E := E) (n := n) ⧸ globLev S K', globFn S f q.out • F (x * q.out) := by
  have hsub : (Function.support fun q : finU (E := E) (n := n) ⧸ globLev S K' => globFn S f q.out • F (x * q.out)) ⊆
      (hfin.toFinset : Set _) := by
    intro q hq
    simp only [Set.Finite.coe_toFinset, Function.mem_support] at hq ⊢
    intro h0
    apply hq
    have := congrArg (fun L : (finU (E := E) (n := n) → Module.Dual ℂ (Wsp lam)) →ₗ[ℂ] (finU (E := E) (n := n) → Module.Dual ℂ (Wsp lam)) => L F x) h0
    simpa [rightReg, LinearMap.funLeft] using this
  unfold hopM levOp
  rw [finsum_eq_sum _ hfin, finsum_eq_sum_of_support_subset _ hsub]
  simp [rightReg, LinearMap.funLeft, Finset.sum_apply, LinearMap.sum_apply]

end GlobalTheory.BCT.TrKer.HopStab

namespace GlobalTheory.BCT.TrKer.HopStab

theorem hopM_mem_vecM : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E))
    (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)),
    IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ,
    IsTest (KL n) K' f → ∀ F ∈ vecM S lam K', hopM S lam K' f F ∈ vecM S lam K' := by
  intro E _ _ _ n S lam K' _ f hf F hF
  by_cases hfin : (Function.support fun q : finU (E := E) (n := n) ⧸ globLev S K' =>
      globFn S f q.out • (rightReg ℂ (finU (E := E) (n := n)) (Module.Dual ℂ (Wsp lam)) q.out ∘ₗ LinearMap.id)).Finite
  swap
  · have h0 : hopM S lam K' f = 0 := by
      unfold hopM levOp
      rw [finsum_of_infinite_support hfin, smul_zero]
    rw [h0]
    exact (vecM S lam K').zero_mem
  have hsupp : ∀ y : finU (E := E) (n := n), (Function.support fun q : finU (E := E) (n := n) ⧸ globLev S K' =>
      globFn S f q.out • F (y * q.out)).Finite := by
    intro y
    refine hfin.subset fun q hq => ?_
    simp only [Function.mem_support] at hq ⊢
    intro h0
    apply hq
    have := congrArg (fun L : (finU (E := E) (n := n) → Module.Dual ℂ (Wsp lam)) →ₗ[ℂ] (finU (E := E) (n := n) → Module.Dual ℂ (Wsp lam)) => L F y) h0
    simpa [rightReg, LinearMap.funLeft] using this
  refine ⟨fun γ x => ?_, fun k hk x => ?_⟩
  · rw [hopM_apply f F hfin, hopM_apply f F hfin, map_smul, map_finsum _ (hsupp x)]
    congr 1
    refine finsum_congr fun q => ?_
    rw [mul_assoc, hF.1 γ, map_smul]
  · rw [hopM_apply f F hfin, hopM_apply f F hfin]
    congr 1
    symm
    rw [← finsum_comp_equiv (MulAction.toPerm k : Equiv.Perm (finU (E := E) (n := n) ⧸ globLev S K'))]
    refine finsum_congr fun q => ?_
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (globLev S K') (k * q.out)
    have hq : (MulAction.toPerm k : Equiv.Perm (finU (E := E) (n := n) ⧸ globLev S K')) q =
        ((k * q.out : finU (E := E) (n := n)) : finU (E := E) (n := n) ⧸ globLev S K') := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    rw [hq, hh, globFn_mul_right hf.1 h.2, globFn_mul_left hf.1 hk, ← mul_assoc, ← mul_assoc, hF.2 h h.2]

end GlobalTheory.BCT.TrKer.HopStab
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.TraceBlocks

section Generic

variable {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]

def eqvM (ι : H →* G) (ρ : Representation ℂ H V) (K : Subgroup G) : Submodule ℂ (G → V) where
  carrier := {φ | (∀ h x, φ (ι h * x) = ρ h (φ x)) ∧ ∀ k ∈ K, ∀ x, φ (x * k) = φ x}
  add_mem' := by
    intro a b ha hb
    refine ⟨fun h x => ?_, fun k hk x => ?_⟩
    · simp only [Pi.add_apply, ha.1 h x, hb.1 h x, map_add (f := _)]
    · simp only [Pi.add_apply, ha.2 k hk x, hb.2 k hk x]
  zero_mem' := ⟨fun _ _ => by simp, fun _ _ _ => rfl⟩
  smul_mem' := by
    intro c a ha
    refine ⟨fun h x => ?_, fun k hk x => ?_⟩
    · simp only [Pi.smul_apply, ha.1 h x, map_smul]
    · simp only [Pi.smul_apply, ha.2 k hk x]

def stabCard (ι : H →* G) (K : Subgroup G) (x : G) : ℕ :=
  Nat.card (ι.range ⊓ K.map (MulAut.conj x).toMonoidHom : Subgroup G)

def secM (ι : H →* G) (ρ : Representation ℂ H V) (K : Subgroup G) (x : G) : V →ₗ[ℂ] (G → V) where
  toFun v y := ((stabCard ι K x : ℂ))⁻¹ • (∑ᶠ h : H, if (ι h * x)⁻¹ * y ∈ K then ρ h else 0) v
  map_add' a b := by
    funext y
    simp only [map_add (f := _), smul_add, Pi.add_apply]
  map_smul' c a := by
    funext y
    simp only [map_smul, Pi.smul_apply, RingHom.id_apply, smul_comm c]

end Generic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def finPtHom : UE E n →* finU (E := E) (n := n) where
  toFun := finPt
  map_one' := by
    apply Subtype.ext
    rw [FinPtLoc.finPt_eq]
    apply Subtype.ext
    simp
  map_mul' a b := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, FinPtLoc.finPt_eq, FinPtLoc.finPt_eq, FinPtLoc.finPt_eq]
    apply Subtype.ext
    exact (congrArg (finGL E n) (map_mul (ratF E n) a.1 b.1)).trans (map_mul _ _ _)

theorem finPtHom_apply (γ : UE E n) : finPtHom γ = finPt γ := rfl

theorem wAt_mul (lam : InfinitePlace E → DomWeight n) (a b : UE E n) :
    GlobalTheory.BCT.TrKer.wAt lam (a * b) = GlobalTheory.BCT.TrKer.wAt lam a ∘ₗ GlobalTheory.BCT.TrKer.wAt lam b := by
  unfold GlobalTheory.BCT.TrKer.wAt
  rw [← PiTensorProduct.map_comp]
  refine congrArg PiTensorProduct.map (funext fun v => ?_)
  change GlobalTheory.Branching.sqRep ℂ n (lam v) (GeneralLinearGroup.map v.embedding (a.1 * b.1)) = _
  rw [map_mul, map_mul, Module.End.mul_eq_comp]

theorem wAt_one (lam : InfinitePlace E → DomWeight n) : GlobalTheory.BCT.TrKer.wAt lam 1 = LinearMap.id := by
  unfold GlobalTheory.BCT.TrKer.wAt
  simp only [OneMemClass.coe_one, map_one]
  exact PiTensorProduct.map_id

def wDual (lam : InfinitePlace E → DomWeight n) : Representation ℂ (UE E n) (Module.Dual ℂ (GlobalTheory.BCT.TrKer.Wsp lam)) where
  toFun γ := (GlobalTheory.BCT.TrKer.wAt lam γ⁻¹).dualMap
  map_one' := by
    rw [inv_one, wAt_one]
    rfl
  map_mul' a b := by
    rw [_root_.mul_inv_rev, wAt_mul, ← LinearMap.dualMap_comp_dualMap]
    rfl

end GlobalTheory.BCT.TraceBlocks
end
end

section

open scoped Matrix

theorem _root_.GlobalTheory.T.full_rank_coinvariant_induced_iso : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n d : ℕ) (ν : kˣ →* ℂˣ), n ≤ d → GlobalTheory.SmGL.IsSmoothChar ν →
    ∃ Z : (Matrix (Fin n) (Fin d) k → ℂ) →ₗ[ℂ] (GL (Fin d) k → ℂ),
      (∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, Z Ψ ∈ GlobalTheory.FullRankCoinv.indSp k n d ν) ∧
      (∀ f ∈ GlobalTheory.FullRankCoinv.indSp k n d ν, ∃ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, Z Ψ = f) ∧
      (∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, Z Ψ = 0 → Ψ ∈ GlobalTheory.FullRankCoinv.augRk n d ν) ∧
      ∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, ∀ h₀ : GL (Fin d) k,
        Z (fun Y => Ψ (Y * h₀.1)) = fun h => Z Ψ (h * h₀) := by
  first | exact @GlobalTheory.FullRankCoinv.fibre_coinvariants | exact GlobalTheory.FullRankCoinv.fibre_coinvariants | (intros; apply GlobalTheory.FullRankCoinv.fibre_coinvariants <;> assumption)
end
