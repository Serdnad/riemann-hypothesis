module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle027
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle028
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle032
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle023
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
public import Mathlib.RingTheory.Ideal.Quotient.Index
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Lemma
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
public import Mathlib.MeasureTheory.Measure.Haar.Unique
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

section

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch

theorem blkM_castSucc_castSucc {n : ℕ} (b : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → ℂ) (d : ℝ)
    (i j : Fin n) : blkM b u d i.castSucc j.castSucc = b i j := by
  have h : ∀ k : Fin n, finSumFinEquiv.symm k.castSucc = (Sum.inl k : Fin n ⊕ Fin 1) :=
    fun k => finSumFinEquiv_symm_apply_castAdd k
  simp [blkM, Matrix.reindex_apply, Matrix.submatrix_apply, h]

theorem blkM_castSucc_last {n : ℕ} (b : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → ℂ) (d : ℝ)
    (i : Fin n) : blkM b u d i.castSucc (Fin.last n) = u i := by
  have h : ∀ k : Fin n, finSumFinEquiv.symm k.castSucc = (Sum.inl k : Fin n ⊕ Fin 1) :=
    fun k => finSumFinEquiv_symm_apply_castAdd k
  simp [blkM, Matrix.reindex_apply, Matrix.submatrix_apply, h, finSumFinEquiv_symm_last]

theorem blkM_last_last {n : ℕ} (b : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → ℂ) (d : ℝ) :
    blkM b u d (Fin.last n) (Fin.last n) = d := by
  simp [blkM, Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_last]

theorem blkM_last_castSucc {n : ℕ} (b : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → ℂ) (d : ℝ)
    (j : Fin n) : blkM b u d (Fin.last n) j.castSucc = star (u j) := by
  have h : ∀ k : Fin n, finSumFinEquiv.symm k.castSucc = (Sum.inl k : Fin n ⊕ Fin 1) :=
    fun k => finSumFinEquiv_symm_apply_castAdd k
  simp [blkM, Matrix.reindex_apply, Matrix.submatrix_apply, h, finSumFinEquiv_symm_last]

theorem blkM_add {n : ℕ} (b b' : Matrix (Fin n) (Fin n) ℂ) (u u' : Fin n → ℂ) (d d' : ℝ) :
    blkM (b + b') (u + u') (d + d') = blkM b u d + blkM b' u' d' := by
  ext i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp [blkM_last_last]
    | cast j => simp [blkM_last_castSucc]
  | cast i =>
    induction j using Fin.lastCases with
    | last => simp [blkM_castSucc_last]
    | cast j => simp [blkM_castSucc_castSucc]

def upperLeftHermBlock {n : ℕ} (b : hermC (n + 1)) : hermC n :=
  ⟨(b : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ).submatrix Fin.castSucc Fin.castSucc,
    mem_hermC.2 ((mem_hermC.1 b.2).submatrix _)⟩

def blkEquiv (n : ℕ) : (hermC n × (Fin n → ℂ) × ℝ) ≃+ hermC (n + 1) where
  toFun x := blk x.1 x.2.1 x.2.2
  invFun b := (upperLeftHermBlock b, fun i => (b : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) i.castSucc (Fin.last n),
    ((b : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (Fin.last n) (Fin.last n)).re)
  left_inv x := by
    obtain ⟨b, u, d⟩ := x
    refine Prod.ext (Subtype.ext ?_) (Prod.ext ?_ ?_)
    · ext i j
      simp [upperLeftHermBlock, blk, blkM_castSucc_castSucc]
    · ext i
      simp [blk, blkM_castSucc_last]
    · simp [blk, blkM_last_last]
  right_inv b := by
    have hb := mem_hermC.1 b.2
    apply Subtype.ext
    ext i j
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last =>
        simp only [blk, blkM_last_last]
        have := hb.apply (Fin.last n) (Fin.last n)
        exact (Complex.conj_eq_iff_real.1 this).choose_spec ▸ by simp
      | cast j =>
        simp only [blk, blkM_last_castSucc]
        exact hb.apply _ _
    | cast i =>
      induction j using Fin.lastCases with
      | last => simp [blk, blkM_castSucc_last]
      | cast j => simp [blk, blkM_castSucc_castSucc, upperLeftHermBlock]
  map_add' x y := by
    apply Subtype.ext
    simp [blk, blkM_add]

theorem continuous_blkEquiv (n : ℕ) : Continuous (blkEquiv n) := by
  refine Continuous.subtype_mk (f := fun x : hermC n × (Fin n → ℂ) × ℝ =>
    blkM (x.1 : Matrix (Fin n) (Fin n) ℂ) x.2.1 x.2.2) ?_ _
  exact continuous_blkM.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

theorem continuous_blkEquiv_symm (n : ℕ) : Continuous (blkEquiv n).symm := by
  have h : ∀ i j : Fin (n + 1), Continuous fun b : hermC (n + 1) =>
      (b : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) i j := fun i j =>
    (continuous_apply_apply i j).comp continuous_subtype_val
  refine Continuous.prodMk ?_ (Continuous.prodMk ?_ ?_)
  · refine Continuous.subtype_mk (continuous_matrix fun i j => ?_) _
    exact h _ _
  · exact continuous_pi fun i => h _ _
  · exact Complex.continuous_re.comp (h _ _)

theorem haar_blocks (n : ℕ) (ν : Measure (hermC (n + 1))) (ν' : Measure (hermC n))
    (hν : ν.IsAddHaarMeasure) (hν' : ν'.IsAddHaarMeasure) :
    ∃ c : ENNReal, c ≠ ⊤ ∧ ∀ F : hermC (n + 1) → ENNReal, Measurable F →
      ∫⁻ b, F b ∂ν = c * ∫⁻ b', ∫⁻ u : Fin n → ℂ, ∫⁻ d : ℝ, F (blk b' u d) ∂volume ∂volume ∂ν' := by
  haveI := hν
  haveI := hν'
  haveI : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have hp : (ν'.prod ((volume : Measure (Fin n → ℂ)).prod (volume : Measure ℝ))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  have hm : (Measure.map (blkEquiv n)
      (ν'.prod ((volume : Measure (Fin n → ℂ)).prod (volume : Measure ℝ)))).IsAddHaarMeasure :=
    (blkEquiv n).isAddHaarMeasure_map _ (continuous_blkEquiv n) (continuous_blkEquiv_symm n)
  have he : Measurable (blkEquiv n) := (continuous_blkEquiv n).measurable
  refine ⟨(Measure.addHaarScalarFactor ν (Measure.map (blkEquiv n)
      (ν'.prod ((volume : Measure (Fin n → ℂ)).prod (volume : Measure ℝ)))) : ENNReal),
    ENNReal.coe_ne_top, fun F hF => ?_⟩
  conv_lhs => rw [Measure.isAddLeftInvariant_eq_smul ν (Measure.map (blkEquiv n)
      (ν'.prod ((volume : Measure (Fin n → ℂ)).prod (volume : Measure ℝ))))]
  rw [lintegral_smul_measure, lintegral_map hF he, lintegral_prod (fun a => F (blkEquiv n a)) (hF.comp he).aemeasurable]
  simp only [ENNReal.smul_def, smul_eq_mul]
  congr 1
  refine lintegral_congr fun b' => ?_
  rw [lintegral_prod]
  · rfl
  · exact ((hF.comp he).comp measurable_prodMk_left).aemeasurable

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
end
end

section

@[expose] public section

noncomputable section

open Matrix

namespace GlobalTheory.CompanionTheory.Jp.Iw

section Ops

variable {O L ι : Type} [CommRing O] [Field L] [Algebra O L] [Fintype ι] [DecidableEq ι]

def admitted (O : Type) [CommRing O] [Algebra O L] (T : Finset ι) (k : GL ι L) : Prop :=
  (∃ κ : GL ι O, Matrix.GeneralLinearGroup.map (algebraMap O L) κ = k) ∧
    ∀ v : ι → L, (∀ i ∈ T, v i = 0) → v ᵥ* k.1 = v

lemma admitted.one (T : Finset ι) : admitted O T (1 : GL ι L) :=
  ⟨⟨1, map_one _⟩, fun v _ => by simp⟩

lemma admitted.mul {T : Finset ι} {k k' : GL ι L} (h : admitted O T k) (h' : admitted O T k') : admitted O T (k * k') := by
  obtain ⟨⟨κ, rfl⟩, f⟩ := h
  obtain ⟨⟨κ', rfl⟩, f'⟩ := h'
  refine ⟨⟨κ * κ', map_mul _ _ _⟩, fun v hv => ?_⟩
  rw [Units.val_mul, ← Matrix.vecMul_vecMul, f v hv, f' v hv]

lemma exists_transv {T : Finset ι} {i j : ι} (hi : i ∈ T) (hij : i ≠ j) (c : O) :
    ∃ k : GL ι L, admitted O T k ∧
      ∀ z : ι → L, z ᵥ* k.1 = z + Pi.single j (z i * algebraMap O L c) := by
  let κ : GL ι O := ⟨transvection i j c, transvection i j (-c),
    by simp [transvection_mul_transvection_same, hij], by simp [transvection_mul_transvection_same, hij]⟩
  have key : ∀ z : ι → L, z ᵥ* (Matrix.GeneralLinearGroup.map (algebraMap O L) κ).1 =
      z + Pi.single j (z i * algebraMap O L c) := by
    intro z
    have e : (Matrix.GeneralLinearGroup.map (algebraMap O L) κ).1 =
        1 + Matrix.single i j (algebraMap O L c) := by
      ext a b
      simp [κ, transvection, Matrix.one_apply, Matrix.single_apply, apply_ite (algebraMap O L)]
    rw [e, Matrix.vecMul_add, Matrix.vecMul_one]
    congr 1
    ext l
    by_cases h : l = j
    · subst h
      simp [Matrix.vecMul, dotProduct, Matrix.single_apply]
    · simp [Matrix.vecMul, dotProduct, Matrix.single_apply, h, Ne.symm h]
  exact ⟨_, ⟨⟨κ, rfl⟩, fun v hv => by rw [key, hv i hi]; simp⟩, key⟩

lemma exists_mul_or [IsDomain O] [ValuationRing O] [IsFractionRing O L] (a b : L) :
    (∃ c : O, b = algebraMap O L c * a) ∨ ∃ c : O, a = algebraMap O L c * b := by
  by_cases ha : a = 0
  · exact Or.inr ⟨0, by simp [ha]⟩
  by_cases hb : b = 0
  · exact Or.inl ⟨0, by simp [hb]⟩
  rcases ValuationRing.isInteger_or_isInteger O (b / a) with ⟨c, hc⟩ | ⟨c, hc⟩
  · refine Or.inl ⟨c, ?_⟩
    have hc' : algebraMap O L c = b / a := hc
    rw [hc']; field_simp
  · refine Or.inr ⟨c, ?_⟩
    have hc' : algebraMap O L c = (b / a)⁻¹ := hc
    rw [hc']; field_simp

lemma exists_clear [IsDomain O] [ValuationRing O] [IsFractionRing O L] {T : Finset ι} {j p : ι}
    (hj : j ∈ T) (hp : p ∈ T) (hjp : j ≠ p) (z : ι → L) :
    ∃ k : GL ι L, admitted O T k ∧ (z ᵥ* k.1) j = 0 ∧ ∀ l, l ≠ j → l ≠ p → (z ᵥ* k.1) l = z l := by
  rcases exists_mul_or (O := O) (z j) (z p) with ⟨c, hc⟩ | ⟨c, hc⟩
  · obtain ⟨k₁, a₁, h₁⟩ := exists_transv (O := O) (L := L) hj hjp (1 - c)
    obtain ⟨k₂, a₂, h₂⟩ := exists_transv (O := O) (L := L) hp hjp.symm (-1)
    refine ⟨k₁ * k₂, a₁.mul a₂, ?_, fun l hl hl' => ?_⟩
    · rw [Units.val_mul, ← Matrix.vecMul_vecMul, h₂, h₁]
      simp [Pi.single_apply, hjp, hjp.symm, hc]
      ring
    · rw [Units.val_mul, ← Matrix.vecMul_vecMul, h₂, h₁]
      simp [Pi.single_apply, hl, hl']
  · obtain ⟨k, a, h⟩ := exists_transv (O := O) (L := L) hp hjp.symm (-c)
    refine ⟨k, a, ?_, fun l hl _ => ?_⟩
    · rw [h]
      simp [hc]
      ring
    · rw [h]
      simp [Pi.single_apply, hl]

lemma exists_clear_set [IsDomain O] [ValuationRing O] [IsFractionRing O L] {T : Finset ι} {p : ι}
    (hp : p ∈ T) (z : ι → L) (s : Finset ι) (hs : s ⊆ T) (hps : p ∉ s) :
    ∃ k : GL ι L, admitted O T k ∧ ∀ l ∈ s, (z ᵥ* k.1) l = 0 := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, admitted.one T, by simp⟩
  | insert a s ha ih =>
    obtain ⟨k, hk, h⟩ := ih ((Finset.subset_insert a s).trans hs)
      (fun hh => hps (Finset.mem_insert_of_mem hh))
    have hap : a ≠ p := fun e => hps (e ▸ Finset.mem_insert_self a s)
    obtain ⟨k', hk', h0, h1⟩ := exists_clear (O := O) (hs (Finset.mem_insert_self a s)) hp hap (z ᵥ* k.1)
    refine ⟨k * k', hk.mul hk', fun l hl => ?_⟩
    rw [Units.val_mul, ← Matrix.vecMul_vecMul]
    rcases Finset.mem_insert.1 hl with rfl | hl
    · exact h0
    · rw [h1 l (fun e => ha (e ▸ hl)) (fun e => hps (e ▸ Finset.mem_insert_of_mem hl))]
      exact h l hl

lemma exists_rows [IsDomain O] [ValuationRing O] [IsFractionRing O L] {ρ : Type} [DecidableEq ρ]
    (f : ρ → ι) (hf : Function.Injective f) (g : Matrix ι ι L) (S : Finset ρ) :
    ∃ κ : GL ι O, ∀ i ∈ S, ∀ c ∉ S.image f,
      (g * (Matrix.GeneralLinearGroup.map (algebraMap O L) κ).1) (f i) c = 0 := by
  induction S using Finset.induction_on with
  | empty => exact ⟨1, by simp⟩
  | insert a S ha ih =>
    obtain ⟨κ, h⟩ := ih
    have hpT : f a ∈ (S.image f)ᶜ := by
      simp only [Finset.mem_compl, Finset.mem_image, not_exists, not_and]
      exact fun x hx e => ha (hf e ▸ hx)
    obtain ⟨k, ⟨⟨κ', rfl⟩, fix⟩, hk⟩ := exists_clear_set (O := O) hpT
      ((g * (Matrix.GeneralLinearGroup.map (algebraMap O L) κ).1) (f a)) (((S.image f)ᶜ).erase (f a))
      (Finset.erase_subset _ _) (Finset.notMem_erase _ _)
    refine ⟨κ * κ', fun i hi c hc => ?_⟩
    have row : ∀ r, (g * (Matrix.GeneralLinearGroup.map (algebraMap O L) (κ * κ')).1) r =
        (g * (Matrix.GeneralLinearGroup.map (algebraMap O L) κ).1) r ᵥ*
          (Matrix.GeneralLinearGroup.map (algebraMap O L) κ').1 := by
      intro r
      rw [map_mul, Units.val_mul, ← Matrix.mul_assoc, Matrix.mul_apply_eq_vecMul]
    have hcS : c ∉ S.image f := fun e => hc (by
      rw [Finset.image_insert]; exact Finset.mem_insert_of_mem e)
    have hca : c ≠ f a := fun e => hc (by
      rw [Finset.image_insert, e]; exact Finset.mem_insert_self _ _)
    rw [row]
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact hk c (Finset.mem_erase.2 ⟨hca, Finset.mem_compl.2 hcS⟩)
    · rw [fix _ (fun l hl => h i hi l (Finset.mem_compl.1 hl))]
      exact h i hi c hcS

end Ops

theorem jpIw : JpIw := by
  intro O L _ _ _ _ _ _ n g
  obtain ⟨κ, h⟩ := exists_rows (O := O) (L := L) (ι := Ix n) (Sum.inr : Fin n → Ix n)
    Sum.inr_injective g.1 Finset.univ
  set k : GL (Ix n) L := inL κ with hk
  set G : Matrix (Ix n) (Ix n) L := (g * k).1 with hG
  have hC : G.toBlocks₂₁ = 0 := by
    ext i j
    exact h i (Finset.mem_univ _) (Sum.inl j) (by simp)
  have hGb : G = fromBlocks G.toBlocks₁₁ G.toBlocks₁₂ 0 G.toBlocks₂₂ := by
    rw [← hC, Matrix.fromBlocks_toBlocks]
  have hdet : G.toBlocks₁₁.det * G.toBlocks₂₂.det ≠ 0 := by
    rw [← Matrix.det_fromBlocks_zero₂₁ G.toBlocks₁₁ G.toBlocks₁₂ G.toBlocks₂₂, ← hGb]
    exact (Matrix.isUnits_det_units (g * k)).ne_zero
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ (left_ne_zero_of_mul hdet),
    Matrix.GeneralLinearGroup.mkOfDetNeZero _ (right_ne_zero_of_mul hdet), G.toBlocks₁₂, κ⁻¹, ?_⟩
  have hp : pM (Matrix.GeneralLinearGroup.mkOfDetNeZero _ (left_ne_zero_of_mul hdet))
      (Matrix.GeneralLinearGroup.mkOfDetNeZero _ (right_ne_zero_of_mul hdet)) G.toBlocks₁₂ = g * k := by
    apply Units.ext
    exact hGb.symm
  rw [hp, map_inv, ← hk, mul_inv_cancel_right]

end GlobalTheory.CompanionTheory.Jp.Iw

end
end

section

noncomputable section

open Matrix MeasureTheory

namespace GlobalTheory.CompanionTheory.Jp.Unif

theorem integral_coset {X G : Type*} [Group X] [MeasurableSpace X] [MeasurableMul X] (ν : Measure X)
    [IsProbabilityMeasure ν] [ν.IsMulLeftInvariant] [Group G] (N : Subgroup G) [Finite (G ⧸ N)] (ρ : X →* G)
    (hρ : Function.Surjective ρ) (hN : MeasurableSet (ρ ⁻¹' (N : Set G))) (c : G ⧸ N → ℂ) :
    ∫ x, c (QuotientGroup.mk (ρ x)) ∂ν = (ν.real (ρ ⁻¹' (N : Set G)) : ℂ) * ∑ᶠ u, c u := by
  classical
  letI := Fintype.ofFinite (G ⧸ N)
  have hS : ∀ u : G ⧸ N, ∃ y : X, {x | (QuotientGroup.mk (ρ x) : G ⧸ N) = u} =
      (fun x => y * x) ⁻¹' (ρ ⁻¹' (N : Set G)) := by
    intro u
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective u
    obtain ⟨y, hy⟩ := hρ g⁻¹
    refine ⟨y, ?_⟩
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe, map_mul, hy]
    rw [eq_comm, QuotientGroup.eq]
  choose y hy using hS
  have hmeas : ∀ u : G ⧸ N, MeasurableSet {x | (QuotientGroup.mk (ρ x) : G ⧸ N) = u} := by
    intro u
    rw [hy u]
    exact hN.preimage (measurable_const_mul (y u))
  have hmeasure : ∀ u : G ⧸ N,
      ν.real {x | (QuotientGroup.mk (ρ x) : G ⧸ N) = u} = ν.real (ρ ⁻¹' (N : Set G)) := by
    intro u
    rw [hy u]
    show (ν _).toReal = (ν _).toReal
    rw [measure_preimage_mul]
  have hdecomp : (fun x => c (QuotientGroup.mk (ρ x))) = fun x =>
      ∑ u, Set.indicator {x | (QuotientGroup.mk (ρ x) : G ⧸ N) = u} (fun _ => c u) x := by
    funext x
    rw [Finset.sum_eq_single (QuotientGroup.mk (ρ x) : G ⧸ N)]
    · exact (Set.indicator_of_mem (show x ∈ {x' : X | (QuotientGroup.mk (ρ x') : G ⧸ N) =
        QuotientGroup.mk (ρ x)} from rfl) (fun _ => c (QuotientGroup.mk (ρ x)))).symm
    · intro u _ hu
      exact Set.indicator_of_notMem (by intro h; exact hu (Eq.symm h)) _
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [finsum_eq_sum_of_fintype, hdecomp, integral_finsetSum]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [integral_indicator_const _ (hmeas u), hmeasure u, Complex.real_smul]
  · intro u _
    exact (integrable_const (c u)).indicator (hmeas u)

theorem integral_level {X G : Type*} [Group X] [MeasurableSpace X] [MeasurableMul X] (ν : Measure X)
    [IsProbabilityMeasure ν] [ν.IsMulLeftInvariant] [Group G] (N : Subgroup G) [Finite (G ⧸ N)] (ρ : X →* G)
    (hρ : Function.Surjective ρ) (hN : MeasurableSet (ρ ⁻¹' (N : Set G))) (φ : G → ℂ)
    (hφ : ∀ κ, ∀ γ ∈ N, φ (κ * γ) = φ κ) :
    ∫ x, φ (ρ x) ∂ν = (Nat.card (G ⧸ N) : ℂ)⁻¹ * ∑ᶠ u : G ⧸ N, φ (Quotient.out u) := by
  classical
  letI := Fintype.ofFinite (G ⧸ N)
  have hone : ∫ _x, (1 : ℂ) ∂ν = 1 := by simp
  have hsum : ∑ᶠ _u : G ⧸ N, (1 : ℂ) = (Nat.card (G ⧸ N) : ℂ) := by
    rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card,
      nsmul_eq_mul, mul_one]
  have h1 : ∫ _x, (1 : ℂ) ∂ν = (ν.real (ρ ⁻¹' (N : Set G)) : ℂ) * ∑ᶠ _u : G ⧸ N, (1 : ℂ) :=
    GlobalTheory.CompanionTheory.Jp.Unif.integral_coset ν N ρ hρ hN (fun _ => 1)
  rw [hone, hsum] at h1
  have hA : (ν.real (ρ ⁻¹' (N : Set G)) : ℂ) = (Nat.card (G ⧸ N) : ℂ)⁻¹ :=
    eq_inv_of_mul_eq_one_left h1.symm
  calc ∫ x, φ (ρ x) ∂ν = ∫ x, φ (Quotient.out (QuotientGroup.mk (ρ x) : G ⧸ N)) ∂ν := by
        congr 1
        funext x
        obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul N (ρ x)
        rw [hh, hφ _ _ h.2]
    _ = (ν.real (ρ ⁻¹' (N : Set G)) : ℂ) * ∑ᶠ u : G ⧸ N, φ (Quotient.out u) :=
        GlobalTheory.CompanionTheory.Jp.Unif.integral_coset ν N ρ hρ hN (fun u => φ (Quotient.out u))
    _ = (Nat.card (G ⧸ N) : ℂ)⁻¹ * ∑ᶠ u : G ⧸ N, φ (Quotient.out u) := by rw [hA]

theorem finite_quot_sq {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Fintype (IsLocalRing.ResidueField O)] {ϖ : O} (hϖ : Irreducible ϖ) : Finite (O ⧸ Ideal.span {ϖ ^ 2}) := by
  have hm : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  have : Finite (O ⧸ IsLocalRing.maximalIdeal O) := Finite.of_fintype (IsLocalRing.ResidueField O)
  rw [← Ideal.span_singleton_pow, ← hm]
  exact Ideal.finite_quotient_pow (IsNoetherian.noetherian _) 2

theorem finite_quotient_level_square_congruence {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Fintype (IsLocalRing.ResidueField O)] (n : ℕ) {ϖ : O} (hϖ : Irreducible ϖ) :
    Finite (GL (Ix n) O ⧸ Gam2 (n := n) ϖ) := by
  haveI := GlobalTheory.CompanionTheory.Jp.Unif.finite_quot_sq hϖ
  haveI : Finite (Matrix (GlobalTheory.CompanionTheory.Jp.Ix n) (GlobalTheory.CompanionTheory.Jp.Ix n) (O ⧸ Ideal.span {ϖ ^ 2})) :=
    inferInstanceAs (Finite (GlobalTheory.CompanionTheory.Jp.Ix n → GlobalTheory.CompanionTheory.Jp.Ix n → O ⧸ Ideal.span {ϖ ^ 2}))
  haveI : Finite (GL (GlobalTheory.CompanionTheory.Jp.Ix n) (O ⧸ Ideal.span {ϖ ^ 2})) :=
    Finite.of_injective (fun g : GL (GlobalTheory.CompanionTheory.Jp.Ix n) (O ⧸ Ideal.span {ϖ ^ 2}) =>
      (g : Matrix (GlobalTheory.CompanionTheory.Jp.Ix n) (GlobalTheory.CompanionTheory.Jp.Ix n) (O ⧸ Ideal.span {ϖ ^ 2})))
      (fun _ _ h => Units.ext h)
  exact Finite.of_injective _ (QuotientGroup.kerLift_injective
    (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (Ideal.span {ϖ ^ 2})) :
      GL (GlobalTheory.CompanionTheory.Jp.Ix n) O →* GL (GlobalTheory.CompanionTheory.Jp.Ix n) (O ⧸ Ideal.span {ϖ ^ 2})))

theorem jpUnif : JpUnif := by
  intro O _ _ _ _ n ϖ hϖ X _ _ _ ν _ _ ρ hρ hN φ hφ
  haveI := finite_quotient_level_square_congruence n hϖ
  exact integral_level ν (Gam2 (n := n) ϖ) ρ hρ hN φ hφ

end GlobalTheory.CompanionTheory.Jp.Unif

end
end

section

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens

namespace GlobalTheory.CompanionTheory.UnrDens

theorem card_hermitian_resAlg (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ)
    (hE : ResAlg E τ q ε) (n : ℕ) :
    Nat.card {H : Matrix (Fin n) (Fin n) E // cT τ H = H} = q ^ (n ^ 2) := by
  have hq : q ≠ 0 := by have := hE.one_lt; omega
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hE.card]; exact pow_ne_zero 2 hq)
  obtain ⟨u, hu, -⟩ := hE.basis
  have key := GlobalTheory.GramCount.card_hermitian_dvd_sq τ hE.inv u hu 1 (map_one τ) n
  have hiff : ∀ H : Matrix (Fin n) (Fin n) E,
      cT τ H = H ↔ ((∀ a b, τ (H b a) = H a b) ∧ ∀ a b, (1 : E) ∣ H a b) := by
    intro H
    constructor
    · intro h
      refine ⟨fun a b => ?_, fun a b => one_dvd _⟩
      have := congrFun (congrFun h a) b
      simpa [cT] using this
    · rintro ⟨h, -⟩
      ext a b
      simpa [cT] using h a b
  have e1 : Nat.card {H : Matrix (Fin n) (Fin n) E // cT τ H = H}
      = Nat.card {H : Matrix (Fin n) (Fin n) E //
          (∀ a b, τ (H b a) = H a b) ∧ ∀ a b, (1 : E) ∣ H a b} :=
    Nat.card_congr (Equiv.subtypeEquivRight hiff)
  have e2 : Nat.card {x : E // (1 : E) ∣ x} = q ^ 2 := by
    rw [← hE.card]
    exact Nat.card_congr (Equiv.subtypeUnivEquiv fun x => one_dvd x)
  rw [e2] at key
  have hsq : (q ^ (n ^ 2)) ^ 2 = (q ^ 2) ^ (n * n) := by
    rw [← pow_mul, ← pow_mul]
    congr 1
    ring
  rw [e1]
  exact Nat.pow_left_injective (by norm_num) (key.trans hsq.symm)

end GlobalTheory.CompanionTheory.UnrDens
end
