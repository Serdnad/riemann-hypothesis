module

import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle005
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle001
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MinorOrderedEntries
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle006
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
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
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.TensorProduct.Free
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Mathlib.Analysis.Calculus.ContDiff.Comp

@[expose] public section

section

namespace GlobalTheory

theorem multiplicative_hasDerivAt_zero : ∀ (lam : ℝ → ℂ), lam 0 = 1 →
    (∀ s t, lam (s + t) = lam s * lam t) → ContinuousAt lam 0 → ∃ c : ℂ, HasDerivAt lam c 0 := by
  apply GlobalTheory.exists_hasDerivAt_zero_of_map_add_mul <;> assumption

end GlobalTheory
end

section

noncomputable section

open scoped TensorProduct
open Module

namespace GlobalTheory.SemilinearExt

open GlobalTheory.IndefiniteRowSideFullHecke.SemilinearExtensionBases

section

variable {O K K'' : Type} [CommRing O] [Field K] [Algebra O K] [IsFractionRing O K]
  [Field K''] [Algebra O K''] [Algebra K K''] [IsScalarTower O K K'']
  {Fm : Type} [AddCommGroup Fm] [Module K Fm] [Module O Fm] [IsScalarTower O K Fm]

theorem algebraMap_tmul (c : K) (m : Fm) :
    algebraMap K K'' c ⊗ₜ[O] m = (1 : K'') ⊗ₜ[O] (c • m) := by
  obtain ⟨⟨a, b⟩, hc⟩ := IsLocalization.mk'_surjective (nonZeroDivisors O) c
  dsimp only at hc
  subst hc
  have hb : algebraMap O K (b : O) ≠ 0 := (IsLocalization.map_units K b).ne_zero
  set m₀ : Fm := (algebraMap O K (b : O))⁻¹ • m with hm₀
  have h1 : (b : O) • m₀ = m := by
    rw [← algebraMap_smul K (b : O) m₀, hm₀, smul_smul, mul_inv_cancel₀ hb, one_smul]
  have h2 : IsLocalization.mk' K a b • m = (a : O) • m₀ := by
    rw [← algebraMap_smul K a m₀, hm₀, smul_smul, ← div_eq_mul_inv, IsFractionRing.mk'_eq_div]
  have h3 : (b : O) • algebraMap K K'' (IsLocalization.mk' K a b) = (a : O) • (1 : K'') := by
    rw [Algebra.smul_def, Algebra.smul_def, mul_one, IsScalarTower.algebraMap_apply O K K'' (b : O),
      IsScalarTower.algebraMap_apply O K K'' a, ← map_mul, IsLocalization.mk'_spec']
  calc algebraMap K K'' (IsLocalization.mk' K a b) ⊗ₜ[O] m
      = algebraMap K K'' (IsLocalization.mk' K a b) ⊗ₜ[O] ((b : O) • m₀) := by rw [h1]
    _ = ((b : O) • algebraMap K K'' (IsLocalization.mk' K a b)) ⊗ₜ[O] m₀ :=
        (TensorProduct.smul_tmul _ _ _).symm
    _ = ((a : O) • (1 : K'')) ⊗ₜ[O] m₀ := by rw [h3]
    _ = (1 : K'') ⊗ₜ[O] ((a : O) • m₀) := TensorProduct.smul_tmul _ _ _
    _ = (1 : K'') ⊗ₜ[O] (IsLocalization.mk' K a b • m) := by rw [h2]

theorem exists_basis_tensor {ι : Type} (b : Basis ι K Fm) :
    ∃ c : Basis ι K'' (K'' ⊗[O] Fm), ∀ i, c i = (1 : K'') ⊗ₜ[O] b i := by
  have : TensorProduct.CompatibleSMul O K K'' Fm := ⟨fun c x m => by
    rw [Algebra.smul_def, mul_comm, ← smul_eq_mul x, ← TensorProduct.smul_tmul', algebraMap_tmul,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one]⟩
  refine ⟨(Algebra.TensorProduct.basis K'' b).map (TensorProduct.equivOfCompatibleSMul O K K'' K'' Fm),
    fun i => ?_⟩
  rw [Basis.map_apply, Algebra.TensorProduct.basis_apply]
  rfl

end

def extOfBasis {L L' V V' : Type} [Field L] [Field L'] [AddCommGroup V] [Module L V] [AddCommGroup V'] [Module L' V']
    (σ : L →+* L') {n : ℕ} (B : Basis (Fin n) L V) (w : Fin n → V') : V →ₛₗ[σ] V' where
  toFun x := ∑ k, σ (B.repr x k) • w k
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a x := by simp [mul_smul, Finset.smul_sum]

theorem extOfBasis_basis {L L' V V' : Type} [Field L] [Field L'] [AddCommGroup V] [Module L V] [AddCommGroup V']
    [Module L' V'] (σ : L →+* L') {n : ℕ} (B : Basis (Fin n) L V) (w : Fin n → V') (k : Fin n) :
    extOfBasis σ B w (B k) = w k := by
  show ∑ j, σ (B.repr (B k) j) • w j = w k
  rw [B.repr_self, Finset.sum_eq_single k]
  · simp
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finset.mem_univ k) h

theorem carries_of_basis {L L' V V' : Type} [Field L] [Field L'] [AddCommGroup V] [Module L V] [AddCommGroup V']
    [Module L' V'] {σ : L →+* L'} (e : V →ₛₗ[σ] V') {n : ℕ} (B : Basis (Fin n) L V) (C : Basis (Fin n) L' V')
    (h : ∀ k, e (B k) = C k) {ι : Type} (b : Basis ι L V) : ∃ c : Basis ι L' V', ∀ i, c i = e (b i) := by
  classical
  have : Module.Finite L V := Module.Finite.of_basis B
  have : Module.Finite L' V' := Module.Finite.of_basis C
  have : Finite ι := Module.Finite.finite_basis b
  haveI : Fintype ι := Fintype.ofFinite ι
  have hspan : ⊤ ≤ Submodule.span L' (Set.range fun i => e (b i)) := by
    rw [← C.span_eq, Submodule.span_le]
    rintro _ ⟨k, rfl⟩

    rw [← h k, ← b.sum_repr (B k), map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hcard : Fintype.card ι = finrank L' V' := by
    rw [finrank_eq_card_basis C, ← finrank_eq_card_basis B, finrank_eq_card_basis b]
  exact ⟨basisOfTopLeSpanOfCardEqFinrank _ hspan hcard, fun i => by simp⟩

theorem semilinearExtension : SemilinearExtension := by
  intro Ks LL WL _ _ _ _ _ _ _ WK hForm O K K'' _ _ _ _ _ _ _ _ _ _ emb hemb Fm _ _ _ _ eF
  obtain ⟨n, bv, -, hKs, hspanK, hLL, hspanL⟩ := hForm
  let B : Basis (Fin n) LL WL := Basis.mk hLL hspanL.ge
  have hB : ∀ k, B k = bv k := fun k => Basis.mk_apply _ _ _
  let BK : Basis (Fin n) Ks WK := (Basis.span hKs).map (LinearEquiv.ofEq _ _ hspanK)
  have hBK : ∀ k, (BK k : WL) = bv k := fun k => by simp [BK, Basis.span_apply]
  let bF : Basis (Fin n) K Fm := (Algebra.TensorProduct.basis K BK).map eF.symm
  obtain ⟨c, hc⟩ := exists_basis_tensor (O := O) (K'' := K'') bF
  have hck : ∀ k, c k = (1 : K'') ⊗ₜ[O] eF.symm ((1 : K) ⊗ₜ[Ks] BK k) := fun k => by
    rw [hc, Basis.map_apply, Algebra.TensorProduct.basis_apply]
  have hscal : ∀ (a : Ks) (m : Fm),
      emb (algebraMap Ks LL a) ⊗ₜ[O] m = (1 : K'') ⊗ₜ[O] (algebraMap Ks K a • m) := by
    intro a m
    rw [← RingHom.comp_apply emb (algebraMap Ks LL) a, hemb, RingHom.comp_apply, algebraMap_tmul]
  have hf : ∀ e : WL →ₛₗ[emb] K'' ⊗[O] Fm,
      (∀ k, e (bv k) = (1 : K'') ⊗ₜ[O] eF.symm ((1 : K) ⊗ₜ[Ks] BK k)) →
      ∀ f : WK, e f = (1 : K'') ⊗ₜ[O] eF.symm ((1 : K) ⊗ₜ[Ks] f) := by
    intro e he f
    have hterm : ∀ (r : Ks) (j : Fin n),
        e (r • bv j) = (1 : K'') ⊗ₜ[O] eF.symm ((1 : K) ⊗ₜ[Ks] (r • BK j)) := by
      intro r j
      rw [← algebraMap_smul LL r (bv j), map_smulₛₗ, he, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
        hscal, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one, Algebra.algebraMap_eq_smul_one,
        TensorProduct.smul_tmul]
    have hsum : (f : WL) = ∑ j, BK.repr f j • bv j := by
      conv_lhs => rw [← BK.sum_repr f]
      simp only [Submodule.coe_sum, Submodule.coe_smul, hBK]

    rw [hsum, map_sum]
    simp_rw [hterm]

    rw [← TensorProduct.tmul_sum, ← map_sum eF.symm, ← TensorProduct.tmul_sum, BK.sum_repr]
  have hext : ∀ e : WL →ₛₗ[emb] K'' ⊗[O] Fm,
      (∀ k, e (bv k) = (1 : K'') ⊗ₜ[O] eF.symm ((1 : K) ⊗ₜ[Ks] BK k)) → IsExt O emb eF e := by
    intro e he ι _ a f

    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smulₛₗ, hf e he, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hval : ∀ e : WL →ₛₗ[emb] K'' ⊗[O] Fm, IsExt O emb eF e →
      ∀ k, e (bv k) = (1 : K'') ⊗ₜ[O] eF.symm ((1 : K) ⊗ₜ[Ks] BK k) := by
    intro e he k
    rw [← hBK]
    exact he.apply_coe (BK k)
  let e₀ : WL →ₛₗ[emb] K'' ⊗[O] Fm :=
    extOfBasis emb B fun k => (1 : K'') ⊗ₜ[O] eF.symm ((1 : K) ⊗ₜ[Ks] BK k)
  have he₀ : ∀ k, e₀ (bv k) = (1 : K'') ⊗ₜ[O] eF.symm ((1 : K) ⊗ₜ[Ks] BK k) := fun k => by
    rw [← hB]
    exact extOfBasis_basis emb B _ k
  refine ⟨⟨e₀, hext e₀ he₀, fun e' he' => B.ext fun k => ?_⟩, fun e he => ?_, fun a m => ?_⟩
  · rw [hB, hval e' he' k, he₀ k]
  · exact fun ι b => carries_of_basis e B c (fun k => by rw [hB, hval e he k, hck k]) b
  · exact hscal a m

end GlobalTheory.SemilinearExt
end
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries

namespace GlobalTheory.StrictInterlace

inductive Alt : ℚ → List ℚ → List ℚ → ℚ → Prop
  | nil (x : ℚ) : Alt x [] [] x
  | cons {x s b y : ℚ} {sm bg : List ℚ} : x > s → s > b → Alt b sm bg y → Alt x (s :: sm) (b :: bg) y

theorem Alt.append {x y z : ℚ} {s b s' b' : List ℚ} (h : Alt x s b y) (h' : Alt y s' b' z) :
    Alt x (s ++ s') (b ++ b') z := by
  induction h with
  | nil x => simpa using h'
  | cons h1 h2 _ ih => exact Alt.cons h1 h2 (ih h')

theorem Alt.interlace {x y : ℚ} {s b : List ℚ} (h : Alt x s b y) : Interlace (x :: b) s := by
  induction h with
  | nil x => exact ⟨rfl, fun i h => absurd h (by simp)⟩
  | cons h1 h2 _ ih =>
    refine ⟨by simpa using ih.1, fun i h h' => ?_⟩
    cases i with
    | zero => exact ⟨h1, h2⟩
    | succ i => exact ih.2 i (by simpa using h) (by simpa using h')

def Above (x : ℚ) (L : List ℚ) : Prop := ∀ z : ℤ, (z : ℚ) ∈ L → x > z

theorem alt_flatMap {ι : Type} (f g h : ι → List ℚ)
    (seg : ∀ i x L, (f i ++ L).Pairwise (· > ·) → Above x (f i ++ L) → ∃ y, Alt x (g i) (h i) y ∧ Above y L)
    (l : List ι) (L : List ℚ) : ∀ x, (l.flatMap f ++ L).Pairwise (· > ·) → Above x (l.flatMap f ++ L) →
      ∃ y, Alt x (l.flatMap g) (l.flatMap h) y ∧ Above y L := by
  induction l with
  | nil => intro x _ hx; exact ⟨x, Alt.nil x, by simpa using hx⟩
  | cons i l ih =>
    intro x hp hx
    rw [List.flatMap_cons, List.append_assoc] at hp hx
    obtain ⟨y, h1, h2⟩ := seg i x _ hp hx
    obtain ⟨z, h3, h4⟩ := ih y (List.pairwise_append.1 hp).2.1 h2
    exact ⟨z, by simpa only [List.flatMap_cons] using h1.append h3, h4⟩

theorem block_succ (c : ℚ) (n : ℕ) : block c (n + 1) = (c + n / 2) :: block (c - 1 / 2) n := by
  simp only [block, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  · push_cast; ring
  · refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp]
    push_cast; ring

theorem mem_block (c : ℚ) {n i : ℕ} (hi : i < n) {x : ℚ} (hx : x = c + ((n : ℚ) - 1) / 2 - i) : x ∈ block c n :=
  List.mem_map.2 ⟨i, List.mem_range.2 hi, hx.symm⟩

theorem alt_block_upper (n : ℕ) (a : ℚ) : ∀ c x : ℚ, x > c + n / 2 → c - n / 2 > a →
    Alt x (block c (n + 1)) (block c n ++ [a]) a := by
  induction n with
  | zero =>
    intro c x h1 h2
    rw [block_succ]
    exact Alt.cons h1 (by simpa using h2) (Alt.nil a)
  | succ n ih =>
    intro c x h1 h2
    rw [block_succ c (n + 1), block_succ c n]
    push_cast at h1 h2 ⊢
    exact Alt.cons h1 (by linarith) (ih _ _ (by linarith) (by linarith))

theorem alt_block_lower (n : ℕ) : ∀ c : ℚ, Alt (c + n / 2) (block c n) (block (c - 1 / 2) n) (c - n / 2) := by
  induction n with
  | zero => intro c; simpa [block] using Alt.nil c
  | succ n ih =>
    intro c
    rw [block_succ c n, block_succ (c - 1 / 2) n]
    have e : c - ((n + 1 : ℕ) : ℚ) / 2 = c - 1 / 2 - n / 2 := by push_cast; ring
    rw [e]
    refine Alt.cons ?_ (by linarith) (ih _)
    push_cast; linarith

theorem seg_upper (c : ℤ) (a : ℚ) {s : ℕ} (hs : Odd s) (x : ℚ) (L : List ℚ)
    (hp : (block c s ++ [a] ++ L).Pairwise (· > ·)) (hx : Above x (block c s ++ [a] ++ L)) :
    ∃ y, Alt x (block c s) (block c (s - 1) ++ [a]) y ∧ Above y L := by
  obtain ⟨r, rfl⟩ := hs
  obtain ⟨h1, -, h2⟩ := List.pairwise_append.1 hp
  refine ⟨a, alt_block_upper (2 * r) a c x ?_ ?_, fun z hz => h2 a (by simp) _ hz⟩
  · have := hx (c + r) (List.mem_append_left _ (List.mem_append_left _
      (mem_block (i := 0) _ (by omega) (by push_cast; ring))))
    push_cast at this ⊢; linarith
  · exact (List.pairwise_append.1 h1).2.2 _ (mem_block (i := 2 * r) _ (by omega) (by push_cast; ring)) a (by simp)

theorem seg_middle (v : ℤ) (u : ℚ) (x : ℚ) (L : List ℚ)
    (hp : ([(v : ℚ), u] ++ L).Pairwise (· > ·)) (hx : Above x ([(v : ℚ), u] ++ L)) :
    ∃ y, Alt x [(v : ℚ)] [u] y ∧ Above y L := by
  obtain ⟨h1, -, h2⟩ := List.pairwise_append.1 hp
  exact ⟨u, Alt.cons (hx v (by simp)) (by simpa using h1) (Alt.nil u), fun z hz => h2 u (by simp) _ hz⟩

theorem seg_lower (b e : ℤ) {t : ℕ} (ht : Odd t) (x : ℚ) (L : List ℚ)
    (hp : (((-b : ℚ) :: block (-e) t) ++ L).Pairwise (· > ·)) (hx : Above x (((-b : ℚ) :: block (-e) t) ++ L)) :
    ∃ y, Alt x ((-b : ℚ) :: block (-e) t) (block (-e) (t + 1)) y ∧ Above y L := by
  obtain ⟨r, rfl⟩ := ht
  obtain ⟨h1, -, h2⟩ := List.pairwise_append.1 hp
  rw [block_succ (-e) (2 * r + 1)]
  refine ⟨_, Alt.cons ?_ ?_ (alt_block_lower _ _), fun z hz => ?_⟩
  · have := hx (-b) (by simp)
    exact_mod_cast this
  · have h3 : (-b : ℚ) > ((-e + r : ℤ) : ℚ) :=
      (List.pairwise_cons.1 h1).1 _ (mem_block (i := 0) _ (by omega) (by push_cast; ring))
    have h4 : -e + r < -b := by exact_mod_cast h3
    have h5 : ((-e + r + 1 : ℤ) : ℚ) ≤ ((-b : ℤ) : ℚ) := by exact_mod_cast h4
    push_cast at h5 ⊢; linarith
  · have h3 : ((-e - r : ℤ) : ℚ) > z :=
      h2 _ (List.mem_cons_of_mem _ (mem_block (i := 2 * r) _ (by omega) (by push_cast; ring))) _ hz
    have h4 : z < -e - r := by exact_mod_cast h3
    have h5 : ((z + 1 : ℤ) : ℚ) ≤ ((-e - r : ℤ) : ℚ) := by exact_mod_cast h4
    push_cast at h5 ⊢; linarith

theorem interlace_big_small (S : Sizes) (Q : Entries S) (hQ : Q.Good) : Interlace Q.bigPar Q.smallPar := by
  have ho := hQ.order
  rw [Entries.orderList, List.cons_append, List.cons_append, List.append_assoc] at ho
  obtain ⟨h0, ho⟩ := List.pairwise_cons.1 ho
  obtain ⟨y1, a1, b1⟩ := alt_flatMap _ _ _ (fun i => seg_upper (Q.c i) (Q.a i.succ) S.s_odd) _ _ (Q.a 0) ho
    (fun z hz => h0 _ hz)
  have ho2 := (List.pairwise_append.1 ho).2.1
  obtain ⟨y2, a2, b2⟩ := alt_flatMap _ _ _ (fun i => seg_middle (Q.v i) (Q.u i)) _ _ y1 ho2 b1
  have ho3 := (List.pairwise_append.1 ho2).2.1
  obtain ⟨y3, a3, -⟩ := alt_flatMap _ _ _ (fun i => seg_lower (Q.b i) (Q.e i) S.t_odd) (List.finRange S.m) [] y2
    (by simpa only [List.append_nil] using ho3) (by simpa only [List.append_nil] using b2)
  have := (a1.append (a2.append a3)).interlace
  simpa only [Entries.bigPar, Entries.psiPar, Entries.smallPar, Entries.basePar, List.cons_append, List.append_assoc,
    List.map_eq_flatMap] using this

end GlobalTheory.StrictInterlace
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.RowReal

variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : Sizes} (P : ι → Entries S)

def omLiftOfMultilinear
    (Φ : MultilinearMap (RingHom.id ℂ) (fun j : Fin S.m => Pol ι (S.nR j.castSucc) (S.nR j.succ))
      (MultilinearMap (RingHom.id ℂ) (fun i : Fin S.m => Pol ι (S.nC i.castSucc) (S.nC i.succ))
        (weylSub (S.nR (0 : Fin (S.m + 1))) (psiWt P) →ₗ[ℂ]
          Module.Dual ℂ (weylSub (S.nC (0 : Fin (S.m + 1))) (baseWt P)) →ₗ[ℂ] ℂ))) : OM P →ₗ[ℂ] ℂ :=
  TensorProduct.lift
    ((TensorProduct.uncurry (RingHom.id ℂ) _ _ ℂ).comp
      (((LinearMap.llcomp ℂ _ _ _ (TensorProduct.uncurry (RingHom.id ℂ) _ _ ℂ)).comp
        PiTensorProduct.lift.toLinearMap).comp (PiTensorProduct.lift Φ)))

theorem omLiftOfMultilinear_tprod
    (Φ : MultilinearMap (RingHom.id ℂ) (fun j : Fin S.m => Pol ι (S.nR j.castSucc) (S.nR j.succ))
      (MultilinearMap (RingHom.id ℂ) (fun i : Fin S.m => Pol ι (S.nC i.castSucc) (S.nC i.succ))
        (weylSub (S.nR (0 : Fin (S.m + 1))) (psiWt P) →ₗ[ℂ]
          Module.Dual ℂ (weylSub (S.nC (0 : Fin (S.m + 1))) (baseWt P)) →ₗ[ℂ] ℂ))) (x y v φ) :
    omLiftOfMultilinear P Φ (PiTensorProduct.tprod ℂ x ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ y ⊗ₜ[ℂ] (v ⊗ₜ[ℂ] φ))) =
      Φ x y v φ := by
  simp only [omLiftOfMultilinear, TensorProduct.lift.tmul, LinearMap.comp_apply, TensorProduct.uncurry_apply,
    LinearMap.llcomp_apply, LinearEquiv.coe_coe, PiTensorProduct.lift.tprod]

theorem invFun_of_multilinear : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {S : Sizes} (P : ι → Entries S)
    (Φ : MultilinearMap (RingHom.id ℂ) (fun j : Fin S.m => Pol ι (S.nR j.castSucc) (S.nR j.succ))
      (MultilinearMap (RingHom.id ℂ) (fun i : Fin S.m => Pol ι (S.nC i.castSucc) (S.nC i.succ))
        (weylSub (S.nR (0 : Fin (S.m + 1))) (psiWt P) →ₗ[ℂ]
          Module.Dual ℂ (weylSub (S.nC (0 : Fin (S.m + 1))) (baseWt P)) →ₗ[ℂ] ℂ)))
    (hΦ : ∀ g x y v φ, Φ (fun j => rowFock P j g (x j)) (fun i => colFock P i g (y i)) (psiRep P g v)
      ((baseRep P).dual g φ) = Φ x y v φ), ∃ l ∈ invFun (omRep P), ∀ x y v φ,
      l (PiTensorProduct.tprod ℂ x ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ y ⊗ₜ[ℂ] (v ⊗ₜ[ℂ] φ))) = Φ x y v φ := by
  intro ι _ _ S P Φ hΦ
  refine ⟨omLiftOfMultilinear P Φ, ?_, omLiftOfMultilinear_tprod P Φ⟩
  intro g z
  have key : (omLiftOfMultilinear P Φ).comp (omRep P g) = omLiftOfMultilinear P Φ := by
    ext x y v φ
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, TensorProduct.AlgebraTensorModule.curry_apply,
      TensorProduct.curry_apply, LinearMap.restrictScalars_apply]
    rw [omRep, Representation.tprod_apply, TensorProduct.map_tmul, Representation.tprod_apply,
      TensorProduct.map_tmul, Representation.tprod_apply, TensorProduct.map_tmul]
    simp only [piTprod, MonoidHom.comp_apply, PiTensorProduct.mapMonoidHom_apply, PiTensorProduct.map_tprod,
      Pi.monoidHom_apply, omLiftOfMultilinear_tprod]
    exact hΦ g x y v φ
  exact LinearMap.congr_fun key z

end GlobalTheory.RowReal

end
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology

noncomputable section
namespace GlobalTheory.SBExtend

variable {X : Type} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [TotallyDisconnectedSpace X]


open Matrix Topology in
variable {X : Type} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [TotallyDisconnectedSpace X] in
theorem _root_.GlobalTheory.SBExtend.exists_isCompact_isClopen_between {K W : Set X} (hK : IsCompact K)
    (hW : IsOpen W) (hKW : K ⊆ W) : ∃ V : Set X, IsCompact V ∧ IsClopen V ∧ K ⊆ V ∧ V ⊆ W := by
  have hB := loc_compact_Haus_tot_disc_of_zero_dim (X := X)
  have h : ∀ x ∈ K, ∃ U : Set X, (IsClopen U ∧ IsCompact U) ∧ x ∈ U ∧ U ⊆ W := by
    intro x hx
    obtain ⟨C, hCx, hCW, hC⟩ := local_compact_nhds (hW.mem_nhds (hKW hx))
    obtain ⟨U, hU, hxU, hUC⟩ :=
      hB.exists_subset_of_mem_open (mem_interior_iff_mem_nhds.2 hCx) isOpen_interior
    exact ⟨U, ⟨hU, hC.of_isClosed_subset hU.isClosed (hUC.trans interior_subset)⟩, hxU,
      (hUC.trans interior_subset).trans hCW⟩
  choose U hU hxU hUW using h
  obtain ⟨t, ht⟩ := hK.elim_nhds_subcover' U fun x hx => (hU x hx).1.isOpen.mem_nhds (hxU x hx)
  exact ⟨⋃ x ∈ t, U x x.2, t.isCompact_biUnion fun x _ => (hU x x.2).2,
    isClopen_biUnion_finset fun x _ => (hU x x.2).1, ht, Set.iUnion₂_subset fun x _ => hUW x x.2⟩


open Matrix Topology in
variable {X : Type} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [TotallyDisconnectedSpace X] in
omit [LocallyCompactSpace X] [TotallyDisconnectedSpace X] in
theorem _root_.GlobalTheory.SBExtend.indicator_mem_SB {V : Set X} (hc : IsCompact V)
    (hV : IsClopen V) : (V.indicator fun _ => (1 : ℂ)) ∈ _root_.GlobalTheory.SplitWeil.SB X := by
  show IsLocallyConstant _ ∧ HasCompactSupport _
  refine ⟨fun s => ?_, HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩
  rcases Set.indicator_const_preimage V s (1 : ℂ) with h | h | h | h <;> rw [h]
  exacts [isOpen_univ, hV.isOpen, hV.compl.isOpen, isOpen_empty]

end GlobalTheory.SBExtend
end
end

section

open MeasureTheory

namespace GlobalTheory.FockFamily

theorem contDiff_blockB_blockD {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (J : ℝ → (V × V) →ₗ[ℝ] (V × V)) (hJ : ∀ w, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => J t w) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => GlobalTheory.FockFamily.blockB (J t)) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => GlobalTheory.FockFamily.blockD (J t)) := by
  constructor
  · rw [contDiff_clm_apply_iff]
    intro q
    simpa only [blockB_apply] using (hJ (0, q)).fst
  · rw [contDiff_clm_apply_iff]
    intro q
    simpa only [blockD_apply] using (hJ (0, q)).snd

end GlobalTheory.FockFamily
end
