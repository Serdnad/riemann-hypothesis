module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle001
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle002
public import Mathlib.CategoryTheory.Category.Basic
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open scoped NNReal
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity Classical

noncomputable section
namespace GlobalTheory.HerbrandBridge

variable {C : Type} [Field C]

def toAddVal (w : Valuation C ℝ≥0) (ℓ : C) (h0 : 0 < w ℓ) (h1 : w ℓ < 1) :
    AddValuation C (WithTop ℝ) :=
  AddValuation.of
    (fun x => if x = 0 then ⊤ else ((Real.log (w x : ℝ) / Real.log (w ℓ : ℝ) : ℝ) : WithTop ℝ))
    (by simp) (by simp)
    (by
      have hL : Real.log (w ℓ : ℝ) < 0 :=
        Real.log_neg (by exact_mod_cast h0) (by exact_mod_cast h1)
      have key : ∀ x z : C, z ≠ 0 → w z ≤ w x →
          Real.log (w x : ℝ) / Real.log (w ℓ : ℝ) ≤ Real.log (w z : ℝ) / Real.log (w ℓ : ℝ) := by
        intro x z hz hle
        apply div_le_div_of_nonpos_of_le hL.le
        apply Real.log_le_log
        · have := (Valuation.ne_zero_iff w).2 hz
          exact_mod_cast pos_iff_ne_zero.2 this
        · exact_mod_cast hle
      intro x y
      by_cases hxy : x + y = 0
      · simp [hxy]
      by_cases hx : x = 0
      · subst hx; simp
      by_cases hy : y = 0
      · subst hy; simp
      simp only [hx, hy, hxy, if_false]
      rcases le_max_iff.1 (w.map_add x y) with h | h
      · exact min_le_of_left_le (WithTop.coe_le_coe.2 (key x _ hxy h))
      · exact min_le_of_right_le (WithTop.coe_le_coe.2 (key y _ hxy h)))
    (by
      intro x y
      by_cases hx : x = 0
      · subst hx; simp
      by_cases hy : y = 0
      · subst hy; simp
      have hx' : (0 : ℝ) < w x := by
        have := (Valuation.ne_zero_iff w).2 hx; exact_mod_cast pos_iff_ne_zero.2 this
      have hy' : (0 : ℝ) < w y := by
        have := (Valuation.ne_zero_iff w).2 hy; exact_mod_cast pos_iff_ne_zero.2 this
      simp only [mul_eq_zero, hx, hy, or_self, if_false, map_mul, NNReal.coe_mul]
      rw [Real.log_mul hx'.ne' hy'.ne', add_div]
      rfl)

theorem toAddVal_apply (w : Valuation C ℝ≥0) (ℓ : C) (h0 : 0 < w ℓ) (h1 : w ℓ < 1) (x : C) :
    toAddVal w ℓ h0 h1 x =
      if x = 0 then ⊤ else ((Real.log (w x : ℝ) / Real.log (w ℓ : ℝ) : ℝ) : WithTop ℝ) := rfl

theorem mem_addValuationIntegerRing_normalized_iff (w : Valuation C ℝ≥0) (ℓ : C) (h0 : 0 < w ℓ) (h1 : w ℓ < 1) (x : C) :
    x ∈ Int0 (toAddVal w ℓ h0 h1) ↔ x ∈ w.valuationSubring := by
  rw [mem_addValuationIntegerRing_iff, toAddVal_apply, Valuation.mem_valuationSubring_iff]
  by_cases hx : x = 0
  · simp [hx]
  have hL : Real.log (w ℓ : ℝ) < 0 :=
    Real.log_neg (by exact_mod_cast h0) (by exact_mod_cast h1)
  have hx' : (0 : ℝ) < w x := by
    have := (Valuation.ne_zero_iff w).2 hx; exact_mod_cast pos_iff_ne_zero.2 this
  simp only [hx, if_false]
  rw [← WithTop.coe_zero, WithTop.coe_le_coe, div_nonneg_iff]
  constructor
  · rintro (⟨-, h⟩ | ⟨h, -⟩)
    · exact absurd h (not_le.2 hL)
    · have := (Real.log_nonpos_iff hx'.le).1 h
      exact_mod_cast this
  · intro h
    right
    exact ⟨Real.log_nonpos hx'.le (by exact_mod_cast h), hL.le⟩

theorem toAddVal_of_ne (w : Valuation C ℝ≥0) (ℓ : C) (h0 : 0 < w ℓ) (h1 : w ℓ < 1) {x : C}
    (hx : x ≠ 0) : toAddVal w ℓ h0 h1 x = ((GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.addVal w ℓ x : ℝ) : WithTop ℝ) := by
  rw [toAddVal_apply, if_neg hx]; rfl

variable {S : Type} [Fintype S] [DecidableEq S]

def liftA {w : Valuation C ℝ≥0} {v : AddValuation C (WithTop ℝ)}
    (hv : ∀ x, x ∈ Int0 v ↔ x ∈ w.valuationSubring) (a : S → w.valuationSubring) : S → Int0 v :=
  fun s => ⟨a s, (hv _).2 (a s).2⟩

def evalVec {v : AddValuation C (WithTop ℝ)} (a : S → Int0 v) (N : ℕ) (x : Fin N → RS a) :
    S → Fin N → C :=
  fun s i => ((ev a s (x i) : Int0 v) : C)

def filPre {w : Valuation C ℝ≥0} {v : AddValuation C (WithTop ℝ)} (a : S → Int0 v) {N : ℕ}
    (F : Submodule w.valuationSubring (S → Fin N → C)) : Submodule (RS a) (Fin N → RS a) :=
  Submodule.span (RS a) {x | evalVec a N x ∈ F}

end GlobalTheory.HerbrandBridge

namespace GlobalTheory.HerbrandBridge
open GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference (freeLattice unif IsFiltration filSpace eigenSub eigenQuot lie quotMap addVal
  DetRel IsLatticeBasis HasVal)

variable {C : Type} [Field C] {S : Type} [Fintype S] [DecidableEq S]

theorem evalVec_smul {v : AddValuation C (WithTop ℝ)} (a : S → Int0 v) (N : ℕ) (c : Int0 v)
    (x : Fin N → RS a) : evalVec a N (c • x) = fun s i => (c : C) * evalVec a N x s i := by
  funext s i
  simp only [evalVec, Pi.smul_apply, map_smul, smul_eq_mul, Subring.coe_mul]

theorem evalVec_add {v : AddValuation C (WithTop ℝ)} (a : S → Int0 v) (N : ℕ)
    (x y : Fin N → RS a) : evalVec a N (x + y) = evalVec a N x + evalVec a N y := by
  funext s i
  simp only [evalVec, Pi.add_apply, map_add (f := _), Subring.coe_add]

theorem evalVec_sub {v : AddValuation C (WithTop ℝ)} (a : S → Int0 v) (N : ℕ)
    (x y : Fin N → RS a) : evalVec a N (x - y) = evalVec a N x - evalVec a N y := by
  funext s i
  simp only [evalVec, Pi.sub_apply, map_sub]; rfl

theorem comp_coe {v : AddValuation C (WithTop ℝ)} (a : S → Int0 v) (N : ℕ) (s : S)
    (x : Fin N → RS a) : (fun i => ((comp a N s x i : Int0 v) : C)) = evalVec a N x s := rfl

end GlobalTheory.HerbrandBridge
end
end

section

open scoped NNReal

namespace GlobalTheory.EigenSubFree

open GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference Polynomial

theorem prod_X_sub_C_dvd {O ι : Type} [CommRing O] [IsDomain O] (T : Finset ι)
    (c : ι → O) (hc : Set.InjOn c (↑T : Set ι)) (f : Polynomial O)
    (hf : ∀ j ∈ T, f.eval (c j) = 0) :
    (∏ i ∈ T, (X - C (c i))) ∣ f := by
  by_cases h0 : f = 0
  · simp [h0]
  have hnd : (T.val.map c).Nodup :=
    Multiset.Nodup.map_on (fun x hx y hy h => hc hx hy h) T.nodup
  have hle : T.val.map c ≤ f.roots := by
    rw [Multiset.le_iff_subset hnd]
    intro b hb
    obtain ⟨j, hj, rfl⟩ := Multiset.mem_map.1 hb
    exact (Polynomial.mem_roots h0).2 (hf j hj)
  have := (Multiset.prod_X_sub_C_dvd_iff_le_roots h0 _).2 hle
  rwa [Multiset.map_map] at this

variable {C : Type} [Field C] {w : Valuation C ℝ≥0} {S : Type}

theorem mem_eigenQuot_freeLattice (a : S → w.valuationSubring) (r : ℕ) (τ : S) (u : Fin r → C) :
    u ∈ eigenQuot (W := fun _ => Fin r → C) (freeLattice a r) τ ↔
      ∀ i, u i ∈ w.valuationSubring := by
  constructor
  · rintro ⟨x, hx, rfl⟩ i
    obtain ⟨f, hf⟩ := hx i
    simp only [LinearMap.proj_apply]
    rw [hf τ]
    exact Subtype.prop _
  · intro hu
    exact ⟨fun _ => u, fun i => ⟨Polynomial.C ⟨u i, hu i⟩, fun s => by simp⟩, rfl⟩

theorem mem_eigenSub_freeLattice [DecidableEq S] (a : S → w.valuationSubring) (r : ℕ) (τ : S)
    (v : Fin r → C) :
    v ∈ eigenSub (W := fun _ => Fin r → C) (freeLattice a r) τ ↔
      ∀ i, ∃ f : Polynomial w.valuationSubring,
        (∀ s, s ≠ τ → f.eval (a s) = 0) ∧ ((f.eval (a τ) : w.valuationSubring) : C) = v i := by
  show (LinearMap.single w.valuationSubring (fun _ : S => Fin r → C) τ v) ∈ freeLattice a r ↔ _
  constructor
  · intro h i
    obtain ⟨f, hf⟩ := h i
    refine ⟨f, fun s hs => ?_, ?_⟩
    · have := hf s
      simp [hs] at this
      exact_mod_cast this.symm
    · have := hf τ
      simp at this
      exact this.symm
  · intro h i
    obtain ⟨f, h0, h1⟩ := h i
    refine ⟨f, fun s => ?_⟩
    by_cases hs : s = τ
    · subst hs; simp [h1]
    · simp [hs, h0 s hs]

theorem eigenSub_freeLattice [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (r : ℕ)
    (τ : S) (ha : Function.Injective a) :
    eigenSub (W := fun _ => Fin r → C) (freeLattice a r) τ =
      flatLattice (r := r) a τ (diffGen a τ) := by
  ext v
  rw [mem_eigenSub_freeLattice]
  unfold flatLattice
  rw [Submodule.mem_map]
  constructor
  · intro h
    have key : ∀ i, ∃ g : w.valuationSubring, (diffGen a τ : C) * g = v i := by
      intro i
      obtain ⟨f, h0, h1⟩ := h i
      obtain ⟨q, hq⟩ := prod_X_sub_C_dvd (Finset.univ.erase τ) a
        (fun x _ y _ e => ha e) f (fun j hj => h0 j (Finset.ne_of_mem_erase hj))
      refine ⟨q.eval (a τ), ?_⟩
      rw [← h1, hq, eval_mul, eval_prod]
      simp [diffGen]
    choose g hg using key
    refine ⟨fun i => (g i : C), (mem_eigenQuot_freeLattice a r τ _).2 fun i => (g i).2, ?_⟩
    funext i
    simp [Algebra.smul_def, hg i]
  · rintro ⟨u, hu, rfl⟩ i
    have hu' := (mem_eigenQuot_freeLattice a r τ u).1 hu
    refine ⟨Polynomial.C (⟨u i, hu' i⟩ : w.valuationSubring) *
      ∏ s ∈ Finset.univ.erase τ, (X - Polynomial.C (a s)), fun s hs => ?_, ?_⟩
    · rw [eval_mul, eval_prod]
      rw [Finset.prod_eq_zero (i := s) (Finset.mem_erase.2 ⟨hs, Finset.mem_univ _⟩) (by simp)]
      simp
    · rw [eval_mul, eval_prod]
      simp [diffGen, Algebra.smul_def, mul_comm]

theorem main : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (S : Type) [Fintype S] [DecidableEq S]
    (a : S → w.valuationSubring) (r : ℕ) (τ : S), Function.Injective a →
    GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub (W := fun _ => Fin r → C) (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a r) τ =
      GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.flatLattice (r := r) a τ (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.diffGen a τ) :=
  fun _ _ _ _ _ _ a r τ ha => eigenSub_freeLattice a r τ ha

end GlobalTheory.EigenSubFree
end

section

open NumberField Complex
open scoped nonZeroDivisors
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization

noncomputable section

namespace GlobalTheory.LatExpSum

theorem trace_eq_sum_emb (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (x : F) :
    ((Algebra.trace ℚ F x : ℚ) : ℝ) = ∑ τ : Emb F, τ x := by
  have h := trace_eq_sum_embeddings (K := ℚ) (E := ℂ) (x := x)
  rw [← Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ) (fun f => f x) (fun φ => φ x)
    (fun _ => by simp [RingHom.equivRatAlgHom_apply])] at h
  rw [eq_ratCast] at h
  have h2 : ∑ φ : F →+* ℂ, φ x = ∑ τ : Emb F, ((τ x : ℝ) : ℂ) := by
    refine (Fintype.sum_bijective (fun τ : Emb F => (ofRealHom.comp τ : F →+* ℂ)) ⟨?_, ?_⟩ _ _ (fun _ => rfl)).symm
    · intro τ τ' hτ
      ext y
      have := DFunLike.congr_fun hτ y
      simpa using this
    · intro φ
      have hr : ComplexEmbedding.IsReal φ := IsTotallyReal.complexEmbedding_isReal φ
      exact ⟨hr.embedding, by ext y; simp⟩
  rw [h2, ← ofReal_sum] at h
  exact_mod_cast h

theorem summable_pi_prod {ι : Type} [Fintype ι] {f : ι → ℤ → ℝ} (h0 : ∀ i x, 0 ≤ f i x)
    (hf : ∀ i, Summable (f i)) : Summable fun n : ι → ℤ => ∏ i, f i (n i) := by
  classical
  refine summable_of_sum_le (c := ∏ i, ∑' x, f i x)
    (fun n => Finset.prod_nonneg fun i _ => h0 i _) fun s => ?_
  calc ∑ n ∈ s, ∏ i, f i (n i)
      ≤ ∑ n ∈ Fintype.piFinset fun i => s.image (· i), ∏ i, f i (n i) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun n hn => Fintype.mem_piFinset.mpr fun i => Finset.mem_image_of_mem _ hn)
          fun n _ _ => Finset.prod_nonneg fun i _ => h0 i _
    _ = ∏ i, ∑ x ∈ s.image (· i), f i x := (Finset.prod_univ_sum _ _).symm
    _ ≤ _ := Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun x _ => h0 i x)
        fun i _ => (hf i).sum_le_tsum _ fun x _ => h0 i x

theorem summable_exp_neg_abs {ε : ℝ} (hε : 0 < ε) : Summable fun n : ℤ => Real.exp (-ε * |(n : ℝ)|) := by
  have hg : Summable fun n : ℕ => Real.exp (-ε) ^ n :=
    summable_geometric_of_lt_one (Real.exp_pos _).le (Real.exp_lt_one_iff.mpr (by linarith))
  apply Summable.of_nat_of_neg
  · refine hg.congr fun n => ?_
    rw [← Real.exp_nat_mul]; push_cast; rw [abs_of_nonneg (by positivity)]; ring_nf
  · refine hg.congr fun n => ?_
    rw [← Real.exp_nat_mul]; push_cast; rw [abs_neg, abs_of_nonneg (by positivity)]; ring_nf

end GlobalTheory.LatExpSum

namespace GlobalTheory.LatExpSum

theorem repr_eq_trace (F : Type) [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ F) (y : F) (i : ι) :
    b.repr y i = Algebra.trace ℚ F ((Algebra.traceForm ℚ F).dualBasis (traceForm_nondegenerate ℚ F) b i * y) := by
  rw [← Algebra.traceForm_apply]
  symm
  calc _ = (Algebra.traceForm ℚ F) ((Algebra.traceForm ℚ F).dualBasis (traceForm_nondegenerate ℚ F) b i) (∑ j, b.repr y j • b j) := by rw [b.sum_repr]
    _ = ∑ j, b.repr y j * (Algebra.traceForm ℚ F) ((Algebra.traceForm ℚ F).dualBasis (traceForm_nondegenerate ℚ F) b i) (b j) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, smul_eq_mul]
    _ = b.repr y i := by simp [LinearMap.BilinForm.apply_dualBasis_left]
end GlobalTheory.LatExpSum

namespace GlobalTheory.LatExpSum

theorem summable_exp_neg_trace : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (L : FractionalIdeal (𝓞 F)⁰ F) (δ : ℝ), 0 < δ → Summable (fun x : {x : F // x ∈ L ∧ ∀ τ : Emb F, 0 < τ x} => Real.exp (-δ * ∑ τ : Emb F, τ x.1)) := by
  intro F _ _ _ L δ hδ
  classical
  obtain ⟨a, ha, hint⟩ := L.isFractional
  have hz : ∀ x : {x : F // x ∈ L ∧ ∀ τ : Emb F, 0 < τ x}, ∃ w : 𝓞 F,
      algebraMap (𝓞 F) F w = algebraMap (𝓞 F) F a * x.1 := fun x => by
    obtain ⟨w, hw⟩ := hint x.1 x.2.1
    exact ⟨w, by rw [hw, Algebra.smul_def]⟩
  choose z hz using hz
  let b := integralBasis F
  let d := (Algebra.traceForm ℚ F).dualBasis (traceForm_nondegenerate ℚ F) b
  have hrepr : ∀ (y : F) i, b.repr y i = Algebra.trace ℚ F (d i * y) := fun y i => repr_eq_trace F b y i
  let c : {x : F // x ∈ L ∧ ∀ τ : Emb F, 0 < τ x} → Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℤ :=
    fun x => (RingOfIntegers.basis F).repr (z x)
  have hc : ∀ x i, ((c x i : ℚ)) = Algebra.trace ℚ F ((d i * algebraMap (𝓞 F) F a) * x.1) := by
    intro x i
    have := integralBasis_repr_apply (K := F) (z x) i
    rw [hz x] at this
    rw [mul_assoc, ← hrepr]
    rw [this, eq_intCast]
  let Mi : Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℝ := fun i => ∑ τ : Emb F, |τ (d i * algebraMap (𝓞 F) F a)|
  have hMi : ∀ i, 0 ≤ Mi i := fun i => Finset.sum_nonneg fun τ _ => abs_nonneg _
  let M : ℝ := ∑ i, Mi i + 1
  have hM : 0 < M := by
    have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => hMi i
    show 0 < ∑ i, Mi i + 1
    linarith
  have hbound : ∀ x, ∑ i, |(c x i : ℝ)| ≤ M * ∑ τ : Emb F, τ x.1 := by
    intro x
    have hT : 0 ≤ ∑ τ : Emb F, τ x.1 := Finset.sum_nonneg fun τ _ => (x.2.2 τ).le
    have h1 : ∀ i, |(c x i : ℝ)| ≤ Mi i * ∑ τ : Emb F, τ x.1 := by
      intro i
      have e : (c x i : ℝ) = ∑ τ : Emb F, τ (d i * algebraMap (𝓞 F) F a) * τ x.1 := by
        have h := congrArg (fun q : ℚ => (q : ℝ)) (hc x i)
        simp only [Rat.cast_intCast] at h
        rw [h, trace_eq_sum_emb]
        simp only [map_mul]
      rw [e]
      calc |∑ τ : Emb F, τ (d i * algebraMap (𝓞 F) F a) * τ x.1|
          ≤ ∑ τ : Emb F, |τ (d i * algebraMap (𝓞 F) F a) * τ x.1| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ τ : Emb F, |τ (d i * algebraMap (𝓞 F) F a)| * τ x.1 := by
          refine Finset.sum_congr rfl fun τ _ => ?_
          rw [abs_mul, abs_of_pos (x.2.2 τ)]
        _ ≤ ∑ τ : Emb F, |τ (d i * algebraMap (𝓞 F) F a)| * ∑ σ : Emb F, σ x.1 :=
          Finset.sum_le_sum fun τ _ => mul_le_mul_of_nonneg_left
            (Finset.single_le_sum (f := fun σ : Emb F => σ x.1) (fun σ _ => (x.2.2 σ).le) (Finset.mem_univ τ)) (abs_nonneg _)
        _ = Mi i * ∑ τ : Emb F, τ x.1 := by rw [Finset.sum_mul]
    calc ∑ i, |(c x i : ℝ)| ≤ ∑ i, Mi i * ∑ τ : Emb F, τ x.1 := Finset.sum_le_sum fun i _ => h1 i
      _ = (∑ i, Mi i) * ∑ τ : Emb F, τ x.1 := by rw [Finset.sum_mul]
      _ ≤ M * ∑ τ : Emb F, τ x.1 := mul_le_mul_of_nonneg_right (by simp [M]) hT
  have ha0 : algebraMap (𝓞 F) F a ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) F)).2 (nonZeroDivisors.ne_zero ha)
  have hinj : Function.Injective c := by
    intro x y hxy
    have h1 : z x = z y := (RingOfIntegers.basis F).repr.injective (Finsupp.ext fun i => congrFun hxy i)
    have h2 : algebraMap (𝓞 F) F a * x.1 = algebraMap (𝓞 F) F a * y.1 := by rw [← hz, ← hz, h1]
    exact Subtype.ext (mul_left_cancel₀ ha0 h2)
  have hε : 0 < δ / M := div_pos hδ hM
  have hg : Summable fun n : Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℤ => ∏ i, Real.exp (-(δ / M) * |(n i : ℝ)|) :=
    summable_pi_prod (f := fun _ x => Real.exp (-(δ / M) * |(x : ℝ)|)) (fun _ _ => (Real.exp_pos _).le) fun _ => summable_exp_neg_abs hε
  refine (hg.comp_injective hinj).of_nonneg_of_le (fun _ => (Real.exp_pos _).le) fun x => ?_
  simp only [Function.comp_apply]
  rw [← Real.exp_sum, Real.exp_le_exp, ← Finset.mul_sum]
  have h3 : δ / M * ∑ i, |(c x i : ℝ)| ≤ δ * ∑ τ : Emb F, τ x.1 := by
    calc δ / M * ∑ i, |(c x i : ℝ)| ≤ δ / M * (M * ∑ τ : Emb F, τ x.1) := mul_le_mul_of_nonneg_left (hbound x) hε.le
      _ = δ * ∑ τ : Emb F, τ x.1 := by field_simp
  linarith

end GlobalTheory.LatExpSum
end
end

section

noncomputable section

open NumberField Complex MeasureTheory
open scoped nonZeroDivisors ContDiff

namespace GlobalTheory.HeckeTwo

open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization

variable {F : Type} [Field F] [NumberField F]

def NZ (I : FractionalIdeal (𝓞 F)⁰ F) : Type := {b : F // b ∈ I ∧ b ≠ 0}

def unitRel (I : FractionalIdeal (𝓞 F)⁰ F) : Setoid (NZ I) where
  r p q := ∃ ε : (𝓞 F)ˣ, q.1 = ((ε : 𝓞 F) : F) * p.1
  iseqv :=
    { refl := fun _ => ⟨1, by simp⟩
      symm := fun {p q} ⟨ε, h⟩ => ⟨ε⁻¹, by rw [h, ← mul_assoc, unit_inv_mul, one_mul]⟩
      trans := fun {p q r} ⟨ε, h⟩ ⟨ε', h'⟩ => ⟨ε' * ε, by rw [h', h, ← mul_assoc]; simp⟩ }

def phi (σ w : ℂ) : ℂ := w⁻¹ ^ 2 * ((‖w‖ : ℝ) : ℂ) ^ (-2 * σ)

def hTrans (σ : ℂ) (ν y : ℝ) : ℂ :=
  ∫ t : ℝ, phi σ ((t : ℂ) + (y : ℂ) * I) * Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ)))

def cConst (σ : ℂ) : ℂ := hTrans σ 0 1


variable (F) in
def kFac (σ : ℂ) : ℂ :=
  ∏ _τ : Emb F, ((2 * (Real.pi : ℂ) * I)⁻¹ ^ 2 * ((2 * Real.pi : ℝ) : ℂ) ^ (-2 * σ))

def fTerm (σ : ℂ) (z : Emb F → ℂ) (b ν : F) : ℂ :=
  ∏ τ : Emb F, (Complex.exp (2 * (Real.pi : ℂ) * I * ((τ ν * τ b * (z τ).re : ℝ) : ℂ)) *
    hTrans σ (τ ν) (τ b * (z τ).im))

def aPart (𝔞 : Frac F) (σ : ℂ) : ℂ :=
  ∑' c : Quotient (unitRel (latM 𝔞)), eisTerm 2 σ 0 (c.out.1, 0)

def bOne (𝔞 𝔟 : Frac F) (σ : ℂ) (z : Emb F → ℂ) : ℂ :=
  ∑' c : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)),
    ∑' ν : NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F), fTerm σ z c.out.1 ν.1

def bZero (Zb : ℂ → ℂ) (𝔞 𝔟 : Frac F) (σ : ℂ) (z : Emb F → ℂ) : ℂ :=
  if σ = 0 then 0 else
    kFac (F := F) σ * ((omegaFactor (F := F) 𝔞) : ℂ) * (((nrm (F := F) 𝔟) : ℝ) : ℂ) ^ (-1 - 2 * σ) * Zb (1 + 2 * σ) *
      ∏ τ : Emb F, (cConst σ * (((z τ).im : ℝ) : ℂ) ^ (-1 - 2 * σ))

def gFun (Zb : ℂ → ℂ) (𝔞 𝔟 : Frac F) (σ : ℂ) (z : Emb F → ℂ) : ℂ :=
  aPart 𝔞 σ + bZero Zb 𝔞 𝔟 σ z + kFac (F := F) σ * ((omegaFactor (F := F) 𝔞) : ℂ) * bOne 𝔞 𝔟 σ z

def IsGood (P : ℂ → (Emb F → ℂ) → ℂ) : Prop :=
  (∀ σ ∈ halfPlane, ContDiffOn ℝ ∞ (P σ) (upperHalf F)) ∧
  (∀ w : List (Emb F × Bool), ∀ z ∈ upperHalf F, DifferentiableOn ℂ (fun σ => wirtWord w (P σ) z) halfPlane)

theorem kFac_differentiable : Differentiable ℂ (kFac (F := F)) := by
  intro σ
  unfold kFac
  rw [show (fun σ : ℂ => ∏ _τ : Emb F, ((2 * (Real.pi : ℂ) * I)⁻¹ ^ 2 * ((2 * Real.pi : ℝ) : ℂ) ^ (-2 * σ))) =
      fun σ => ((2 * (Real.pi : ℂ) * I)⁻¹ ^ 2 * ((2 * Real.pi : ℝ) : ℂ) ^ (-2 * σ)) ^ Fintype.card (Emb F) from
    funext fun σ => Finset.prod_const _]
  refine DifferentiableAt.pow (DifferentiableAt.const_mul ?_ _) _
  refine DifferentiableAt.const_cpow (differentiableAt_id.const_mul _) (Or.inl ?_)
  exact_mod_cast (mul_pos two_pos Real.pi_pos).ne'

end GlobalTheory.HeckeTwo
end
end
