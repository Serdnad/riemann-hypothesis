module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1997
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1918
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

@[expose] public section

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
open Formalism.UG (cT)
open Matrix

noncomputable section

namespace GlobalTheory.FlagRad

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]


omit [NumberField E] in
theorem mulVec_initCols_mem {n r : ℕ} (X : Matrix (Fin n) (Fin r) E) (m : Fin r) (A : Set (Fin r))
    (a : Fin (m.val + 1) → AF F ⊗[F] E) (ha : ∀ l, a l ≠ 0 → Fin.castLE m.2 l ∈ A) :
    adMat F (GlobalTheory.StdPar.initCols X m) *ᵥ a ∈ GlobalTheory.StdPar.colSpan F X A := by
  rw [Matrix.mulVec_eq_sum]
  refine sum_mem fun l _ => ?_
  by_cases h : a l = 0
  · simp [h]
  · rw [op_smul_eq_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ha l h, rfl⟩)

theorem exists_of_card_lt {r : ℕ} (S : Finset (Fin r)) {a b : ℕ}
    (h : (S.filter fun k => k.val < a).card < (S.filter fun k => k.val < b).card) :
    ∃ k ∈ S, a ≤ k.val ∧ k.val < b := by
  by_contra hc
  push_neg at hc
  refine absurd h (not_lt.2 (Finset.card_le_card fun k hk => ?_))
  simp only [Finset.mem_filter] at hk ⊢
  exact ⟨hk.1, not_le.1 fun h' => absurd hk.2 (not_lt.2 (hc k hk.1 h'))⟩


open GlobalTheory.StdPar in
theorem unipFlag_le_unip (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J) (r : ℕ)
    (X Y : Matrix (Fin n) (Fin r) E) (hW : IsWittFrame σ J X Y) (S : Finset (Fin r)) (m : Fin r) (hmS : m ∈ S)
    (hm : ∀ k ∈ S, k ≤ m) :
    GlobalTheory.UAut.unipFlag σ J (GlobalTheory.StdPar.initCols X m) (fun i => (S.filter fun k => k.val < i.val).card) ≤
      GlobalTheory.StdPar.unip σ J X S := by
  set C := initCols X m with hCdef
  set d : Fin (m.val + 1) → ℕ := fun i => (S.filter fun k => k.val < i.val).card with hd
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.SiegelSet.sigma_sigma h
  have hC : IsIsoCols σ J C := isIsoCols_of_isWittFrame hW hσ hJ m.2
  have memS : ∀ g ∈ unipFlag σ J C d, g ∈ unipSet σ J C d := fun g hg => (mem_unipFlag hJ hσ hC d).1 hg

  have stab : ∀ g ∈ unipSet σ J C d, ∀ A : Set (Fin r), (∀ i ∈ A, i.val ≤ m.val) →
      (∀ l l' : Fin (m.val + 1), Fin.castLE m.2 l ∈ A → d l' < d l → Fin.castLE m.2 l' ∈ A) →
      ∀ y ∈ colSpan F X A, (matHom _ σ J g).1 *ᵥ y ∈ colSpan F X A := by
    intro g hg A hA1 hA2 y hy
    have hle : colSpan F X A ≤ (colSpan F X A).comap (matHom _ σ J g).1.mulVecLin := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨i, hi, rfl⟩
      obtain ⟨a, ha0, ha⟩ := hg.1 ⟨i.val, Nat.lt_succ_of_le (hA1 i hi)⟩
      have ha' : ((matHom _ σ J g).1 - 1) *ᵥ (adMat F X)ᵀ i = adMat F C *ᵥ a := ha
      have e : (matHom _ σ J g).1 *ᵥ (adMat F X)ᵀ i = (adMat F X)ᵀ i + ((matHom _ σ J g).1 - 1) *ᵥ (adMat F X)ᵀ i := by
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, add_sub_cancel]
      show (matHom _ σ J g).1 *ᵥ (adMat F X)ᵀ i ∈ colSpan F X A
      rw [e, ha']
      refine add_mem (Submodule.subset_span ⟨i, hi, rfl⟩) (GlobalTheory.FlagRad.mulVec_initCols_mem X m A a fun l' hl' => ?_)
      exact hA2 ⟨i.val, Nat.lt_succ_of_le (hA1 i hi)⟩ l' hi (not_le.1 fun h' => hl' (ha0 l' h'))
    exact hle hy
  have inv_app : ∀ (g : GAd σ J) y, (matHom _ σ J g⁻¹).1 *ᵥ (matHom _ σ J g).1 *ᵥ y = y := fun g y => by
    rw [mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, one_mulVec]
  intro g hg
  have hg1 := memS g hg
  have hg2 := memS g⁻¹ (inv_mem hg)
  have iffPart : ∀ A : Set (Fin r), (∀ i ∈ A, i.val ≤ m.val) →
      (∀ l l' : Fin (m.val + 1), Fin.castLE m.2 l ∈ A → d l' < d l → Fin.castLE m.2 l' ∈ A) →
      ∀ y, y ∈ colSpan F X A ↔ (matHom _ σ J g).1 *ᵥ y ∈ colSpan F X A := fun A hA1 hA2 y =>
    ⟨stab g hg1 A hA1 hA2 y, fun hy => by
      have := stab g⁻¹ hg2 A hA1 hA2 _ hy
      rwa [inv_app] at this⟩
  have e1 : {i | ∃ k ∈ S, i ≤ k} = {i | i ≤ m} :=
    Set.ext fun i => ⟨fun ⟨k, hk, hik⟩ => hik.trans (hm k hk), fun hi => ⟨m, hmS, hi⟩⟩
  have hB1 : ∀ i ∈ {i : Fin r | i ≤ m}, i.val ≤ m.val := fun i hi => hi
  have hB2 : ∀ l l' : Fin (m.val + 1), Fin.castLE m.2 l ∈ {i : Fin r | i ≤ m} → d l' < d l →
      Fin.castLE m.2 l' ∈ {i : Fin r | i ≤ m} := fun l l' _ _ => Nat.le_of_lt_succ l'.2
  have sub_app : ∀ y, (matHom _ σ J g).1 *ᵥ y - y = ((matHom _ σ J g).1 - 1) *ᵥ y := fun y => by
    simp [Matrix.sub_mulVec]
  refine ⟨Subgroup.mem_iInf.2 fun j => ⟨iffPart _ ?_ ?_, fun y hy => ?_⟩, ?_⟩
  · rintro i ⟨k, hk, hik, -⟩
    exact hik.trans (hm k hk)
  · rintro l l' ⟨k, hk, hlk, hkj⟩ hdl
    obtain ⟨k', hk', h1, h2⟩ := GlobalTheory.FlagRad.exists_of_card_lt S hdl
    refine ⟨k', hk', h1, ?_⟩
    rw [Fin.le_def] at hlk
    rw [Fin.lt_def] at hkj ⊢
    simp only [Fin.coe_castLE] at hlk
    omega
  ·
    have hle : colSpan F X {j} ≤ (colSpan F X {i | ∃ k ∈ S, i ≤ k ∧ k < j}).comap
        ((matHom _ σ J g).1 - 1).mulVecLin := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨i, hi', rfl⟩
      have hij : i = j := hi'
      simp only [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply]
      by_cases hi : i.val ≤ m.val
      · obtain ⟨a, ha0, ha⟩ := hg1.1 ⟨i.val, Nat.lt_succ_of_le hi⟩
        have e : ((matHom _ σ J g).1 - 1) *ᵥ (adMat F X)ᵀ i = adMat F C *ᵥ a := ha
        rw [e]
        refine GlobalTheory.FlagRad.mulVec_initCols_mem X m _ a fun l' hl' => ?_
        obtain ⟨k, hk, h1, h2⟩ := GlobalTheory.FlagRad.exists_of_card_lt S (not_le.1 fun h' => hl' (ha0 l' h'))
        refine ⟨k, hk, h1, ?_⟩
        rw [Fin.lt_def, ← hij]
        exact h2
      · have hx : (cT (σ : E →+* E) C * J) *ᵥ (fun k => X k i) = 0 :=
          funext fun l => congrFun (congrFun hW.xx (l.castLE m.2)) i
        obtain ⟨a, ha⟩ := hg1.2 _ hx
        have e : ((matHom _ σ J g).1 - 1) *ᵥ (adMat F X)ᵀ i = adMat F C *ᵥ a := ha
        rw [e]
        refine GlobalTheory.FlagRad.mulVec_initCols_mem X m _ a fun l' _ => ⟨m, hmS, Nat.le_of_lt_succ l'.2, ?_⟩
        rw [Fin.lt_def, ← hij]
        omega
    rw [sub_app]
    exact hle hy
  · rw [e1]
    refine ⟨iffPart _ hB1 hB2, fun y hy => ?_⟩
    set T := cT (σ : E →+* E) (initCols X m) * J
    have hT : T * initCols Y m = 1 := Matrix.ext fun i j =>
      (congrFun (congrFun hW.xy (i.castLE m.2)) (j.castLE m.2)).trans (by simp [Matrix.one_apply])
    have hQ : T * (1 - initCols Y m * T) = 0 := by
      rw [Matrix.mul_sub, ← Matrix.mul_assoc, hT, Matrix.one_mul, Matrix.mul_one, sub_self]
    have hy' : y = adMat F (1 - initCols Y m * T) *ᵥ y := by
      rw [adMat, Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_mul, sub_mulVec,
        one_mulVec, ← mulVec_mulVec, mem_colPerp_iff.1 hy, mulVec_zero, sub_zero]
    have : (matHom _ σ J g).1 *ᵥ y - y = ((matHom _ σ J g).1 - 1).mulVecLin y := by simp [sub_mulVec]

    rw [this, hy', mulVec_eq_sum, map_sum]
    refine sum_mem fun j _ => ?_
    rw [op_smul_eq_smul, map_smul]
    obtain ⟨a, ha⟩ := hg1.2 (fun i => (1 - initCols Y m * T : Matrix (Fin n) (Fin n) E) i j)
      (funext fun i => congrFun (congrFun hQ i) j)
    exact Submodule.smul_mem _ _ (mem_colSpan_iff.2 ⟨a, ha.symm⟩)

end GlobalTheory.FlagRad
end
end

section

open scoped TensorProduct NNReal ENNReal Matrix ComplexConjugate
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.StdPar
open GlobalTheory.Doubling (absE)
open GlobalTheory.EisMidHt (adVec)
open Matrix

noncomputable section

namespace GlobalTheory.FlagNorm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}

omit [NumberField E] in
theorem mulVec_inv (g : GAd σ J) (y : Fin n → AF F ⊗[F] E) :
    (matHom _ σ J g).1 *ᵥ (matHom _ σ J g⁻¹).1 *ᵥ y = y := by
  rw [mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, one_mulVec]

omit [NumberField E] in
theorem inv_mulVec (g : GAd σ J) (y : Fin n → AF F ⊗[F] E) :
    (matHom _ σ J g⁻¹).1 *ᵥ (matHom _ σ J g).1 *ᵥ y = y := by
  rw [mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, one_mulVec]

omit [NumberField E] in
theorem keep_inv {g : GAd σ J} {A : Submodule (AF F ⊗[F] E) (Fin n → AF F ⊗[F] E)}
    (hA : ∀ y, y ∈ A ↔ (matHom _ σ J g).1 *ᵥ y ∈ A) (y : Fin n → AF F ⊗[F] E) :
    y ∈ A ↔ (matHom _ σ J g⁻¹).1 *ᵥ y ∈ A := by
  rw [hA ((matHom _ σ J g⁻¹).1 *ᵥ y), mulVec_inv]

omit [NumberField E] in
theorem conj_mulVec (m u : GAd σ J) (y : Fin n → AF F ⊗[F] E) :
    (matHom _ σ J (m * u * m⁻¹)).1 *ᵥ y =
      (matHom _ σ J m).1 *ᵥ (matHom _ σ J u).1 *ᵥ (matHom _ σ J m⁻¹).1 *ᵥ y := by
  rw [map_mul, map_mul, Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec]

omit [NumberField E] in
theorem conj_sub (m u : GAd σ J) (y : Fin n → AF F ⊗[F] E) :
    (matHom _ σ J (m * u * m⁻¹)).1 *ᵥ y - y =
      (matHom _ σ J m).1 *ᵥ ((matHom _ σ J u).1 *ᵥ (matHom _ σ J m⁻¹).1 *ᵥ y - (matHom _ σ J m⁻¹).1 *ᵥ y) := by
  rw [conj_mulVec, mulVec_sub, mulVec_inv]

omit [NumberField E] in
theorem keep_conj {m u : GAd σ J} {A : Submodule (AF F ⊗[F] E) (Fin n → AF F ⊗[F] E)}
    (hm : ∀ y, y ∈ A ↔ (matHom _ σ J m).1 *ᵥ y ∈ A) (hu : ∀ y, y ∈ A ↔ (matHom _ σ J u).1 *ᵥ y ∈ A)
    (y : Fin n → AF F ⊗[F] E) : y ∈ A ↔ (matHom _ σ J (m * u * m⁻¹)).1 *ᵥ y ∈ A := by
  rw [conj_mulVec]
  exact (keep_inv hm y).trans ((hu _).trans (hm _))

theorem perp_inv {X : Matrix (Fin n) (Fin r) E} {k : Fin r} {g : GAd σ J}
    (hg : ∀ y, y ∈ colSpan F X {i | i ≤ k} ↔ (matHom _ σ J g).1 *ᵥ y ∈ colSpan F X {i | i ≤ k})
    {y : Fin n → AF F ⊗[F] E} (hy : y ∈ colPerp σ J X {i | i ≤ k}) :
    (matHom _ σ J g⁻¹).1 *ᵥ y ∈ colPerp σ J X {i | i ≤ k} := by
  have hcol : ∀ i : Fin (k.val + 1), (matHom _ σ J g).1 *ᵥ (fun l => adMat F (initCols X k) l i) ∈
      colSpan F X {i | i ≤ k} := fun i =>
    (hg _).1 (Submodule.subset_span ⟨i.castLE k.2, Nat.le_of_lt_succ i.2, rfl⟩)
  choose a ha using fun i => mem_colSpan_iff.1 (hcol i)
  have hB : (matHom _ σ J g).1 * adMat F (initCols X k) = adMat F (initCols X k) * Matrix.of (fun l i => a i l) :=
    Matrix.ext fun l i => (congrFun (ha i) l).symm
  have hF := GlobalTheory.UAut.form_mul_of_mul_cols hB
  rw [mem_colPerp_iff] at hy ⊢
  rw [mulVec_mulVec, hF, ← mulVec_mulVec, hy, mulVec_zero]

end GlobalTheory.FlagNorm


open GlobalTheory.FlagNorm in
theorem GlobalTheory.FlagNorm.conj_mem_unip : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
    ∀ (T : Finset (Fin r)) (m : GAd σ J),
      (∀ k ∈ T, ∀ y, y ∈ colSpan F X {i | i ≤ k} ↔ (matHom _ σ J m).1 *ᵥ y ∈ colSpan F X {i | i ≤ k}) →
      ∀ u ∈ unip σ J X T, m * u * m⁻¹ ∈ unip σ J X T := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW T m hm u hu
  by_cases hT : T = ∅
  · subst hT
    rw [unip_empty, Subgroup.mem_bot] at hu ⊢
    simp [hu]
  have hne := Finset.nonempty_iff_ne_empty.2 hT
  have hkMT : T.max' hne ∈ T := T.max'_mem _
  have eB : {i | ∃ k ∈ T, i ≤ k} = {i | i ≤ T.max' hne} :=
    Set.ext fun i => ⟨fun ⟨k, hk, hik⟩ => hik.trans (T.le_max' k hk), fun hi => ⟨_, hkMT, hi⟩⟩

  have keepSub : ∀ T' : Finset (Fin r), T' ⊆ T → ∀ y, y ∈ colSpan F X {i | ∃ k ∈ T', i ≤ k} ↔
      (matHom _ σ J m).1 *ᵥ y ∈ colSpan F X {i | ∃ k ∈ T', i ≤ k} := by
    intro T' hT' y
    by_cases h0 : T' = ∅
    · subst h0
      have e : {i : Fin r | ∃ k ∈ (∅ : Finset (Fin r)), i ≤ k} = ∅ := by simp
      rw [e, colSpan, Set.image_empty, Submodule.span_empty, Submodule.mem_bot, Submodule.mem_bot]
      exact ⟨fun hy => by rw [hy, mulVec_zero], fun hy => by rw [← inv_mulVec m y, hy, mulVec_zero]⟩
    · have hne' := Finset.nonempty_iff_ne_empty.2 h0
      have e : {i | ∃ k ∈ T', i ≤ k} = {i | i ≤ T'.max' hne'} :=
        Set.ext fun i => ⟨fun ⟨k, hk, hik⟩ => hik.trans (T'.le_max' k hk), fun hi => ⟨_, T'.max'_mem _, hi⟩⟩
      rw [e]
      exact hm _ (hT' (T'.max'_mem _)) y
  have eA : ∀ j : Fin r, {i | ∃ k ∈ T, i ≤ k ∧ k < j} = {i | ∃ k ∈ T.filter (· < j), i ≤ k} := fun j =>
    Set.ext fun i => ⟨fun ⟨k, hk, h1, h2⟩ => ⟨k, Finset.mem_filter.2 ⟨hk, h2⟩, h1⟩,
      fun ⟨k, hk, h1⟩ => ⟨k, (Finset.mem_filter.1 hk).1, h1, (Finset.mem_filter.1 hk).2⟩⟩
  have keepA : ∀ j : Fin r, ∀ y, y ∈ colSpan F X {i | ∃ k ∈ T, i ≤ k ∧ k < j} ↔
      (matHom _ σ J m).1 *ᵥ y ∈ colSpan F X {i | ∃ k ∈ T, i ≤ k ∧ k < j} := fun j => by
    rw [eA j]
    exact keepSub _ (Finset.filter_subset _ _)
  have keepB := keepSub T subset_rfl
  rw [eB] at keepB
  have hu1 : ∀ j, u ∈ trivOn σ J (colSpan F X {i | ∃ k ∈ T, i ≤ k ∧ k < j}) (colSpan F X {j}) :=
    fun j => Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hu).1 j
  have hu2 : u ∈ trivOn σ J (colSpan F X {i | i ≤ T.max' hne}) (colPerp σ J X {i | i ≤ T.max' hne}) := by
    have := (Subgroup.mem_inf.1 hu).2
    rw [eB] at this
    exact this
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_iInf.2 fun j => ⟨keep_conj (keepA j) (hu1 j).1, fun y hy => ?_⟩, ?_⟩
  ·
    unfold colSpan at hy
    rw [Set.image_singleton, Submodule.mem_span_singleton] at hy
    obtain ⟨a, rfl⟩ := hy
    rw [mulVec_smul, ← smul_sub]
    refine Submodule.smul_mem _ a ?_
    rw [conj_sub]
    refine (keepA j _).1 ?_
    set z := (matHom _ σ J m⁻¹).1 *ᵥ (adMat F X)ᵀ j
    by_cases hex : ∃ k ∈ T, j ≤ k
    · have hne2 : (T.filter (j ≤ ·)).Nonempty := let ⟨k, hk, hjk⟩ := hex; ⟨k, Finset.mem_filter.2 ⟨hk, hjk⟩⟩
      set k0 := (T.filter (j ≤ ·)).min' hne2
      have hk0 := Finset.mem_filter.1 ((T.filter (j ≤ ·)).min'_mem hne2)
      have hmin : ∀ k ∈ T, j ≤ k → k0 ≤ k := fun k hk hjk => (T.filter (j ≤ ·)).min'_le k (Finset.mem_filter.2 ⟨hk, hjk⟩)
      have hz : z ∈ colSpan F X {i | i ≤ k0} :=
        (keep_inv (hm k0 hk0.1) _).1 (Submodule.subset_span ⟨j, hk0.2, rfl⟩)
      have hle : colSpan F X {i | i ≤ k0} ≤
          (colSpan F X {i | ∃ k ∈ T, i ≤ k ∧ k < j}).comap ((matHom _ σ J u).1 - 1).mulVecLin := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨i, hi, rfl⟩
        have h1 := (hu1 i).2 _ (Submodule.subset_span ⟨i, Set.mem_singleton i, rfl⟩)
        have hsub : {l | ∃ k ∈ T, l ≤ k ∧ k < i} ⊆ {l | ∃ k ∈ T, l ≤ k ∧ k < j} := by
          rintro l ⟨k', hk', hlk', hk'i⟩
          refine ⟨k', hk', hlk', not_le.1 fun hjk' => ?_⟩
          exact absurd (hmin k' hk' hjk') (not_le.2 (lt_of_lt_of_le hk'i hi))
        have h2 := Submodule.span_mono (R := AF F ⊗[F] E) (Set.image_mono (f := fun i => (adMat F X)ᵀ i) hsub) h1
        change _ ∈ colSpan F X _ at h2
        simpa [sub_mulVec] using h2
      simpa [sub_mulVec] using hle hz
    · push_neg at hex
      have eAj : {i | ∃ k ∈ T, i ≤ k ∧ k < j} = {i | i ≤ T.max' hne} := by
        rw [← eB]
        exact Set.ext fun i => ⟨fun ⟨k, hk, h1, _⟩ => ⟨k, hk, h1⟩, fun ⟨k, hk, h1⟩ => ⟨k, hk, h1, hex k hk⟩⟩
      rw [eAj]
      have hxj : (adMat F X)ᵀ j ∈ colPerp σ J X {i | i ≤ T.max' hne} := by
        refine mem_colPerp_iff.2 (funext fun i => ?_)
        exact (RingHom.map_mulVec (inclR (F := F) (AF F)) _ (Xᵀ j) i).symm.trans
          ((congrArg _ (congrFun (congrFun hW.xx (i.castLE (T.max' hne).2)) j)).trans (map_zero _))
      exact hu2.2 z (perp_inv (hm _ hkMT) hxj)
  · rw [eB]
    refine ⟨keep_conj keepB hu2.1, fun y hy => ?_⟩
    rw [conj_sub]
    exact (keepB _).1 (hu2.2 _ (perp_inv (hm _ hkMT) hy))
end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
namespace GlobalTheory.StdParFlag

open Matrix

theorem unip_le_parFlag : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
      ∀ (S T : Finset (Fin r)) (m : Fin r), T ⊆ S → m ∈ T → (∀ k ∈ T, k ≤ m) →
        GlobalTheory.StdPar.unip σ J X S ≤ GlobalTheory.UAut.parFlag σ J (GlobalTheory.StdPar.initCols X m) (fun i => (T.filter fun k => k.val < i.val).card) := by
  intro F E _ _ _ _ _ σ _ n J _ r X Y _ S T m _ _ _
  classical
  have key : ∀ p ∈ GlobalTheory.StdPar.unip σ J X S, ∃ B : Matrix (Fin (m.val + 1)) (Fin (m.val + 1)) (AF F ⊗[F] E),
      B.BlockTriangular (fun i => (T.filter fun k => k.val < i.val).card) ∧
      (matHom _ σ J p).1 * adMat F (GlobalTheory.StdPar.initCols X m) = adMat F (GlobalTheory.StdPar.initCols X m) * B := by
    intro p hp
    have span_lemma : ∀ (i : Fin (m.val + 1)) (I : Set (Fin r)), (∀ l ∈ I, l.val < i.val) →
        ∀ y ∈ GlobalTheory.StdPar.colSpan F X I, ∃ a : Fin (m.val + 1) → AF F ⊗[F] E, (∀ j, i.val ≤ j.val → a j = 0) ∧
          adMat F (GlobalTheory.StdPar.initCols X m) *ᵥ a = y := by
      intro i I hI y hy
      induction hy using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨l, hl, rfl⟩ := hx
        have hl' : l.val < m.val + 1 := by have := hI l hl; have := i.2; omega
        refine ⟨Pi.single ⟨l.val, hl'⟩ 1, fun j hj => Pi.single_eq_of_ne (fun e => ?_) _, ?_⟩
        · have := hI l hl; rw [e] at hj; simp at hj; omega
        · rw [mulVec_single_one]; rfl
      | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨a, ha, rfl⟩ := hx
        obtain ⟨b, hb, rfl⟩ := hy
        exact ⟨a + b, fun j hj => by simp [ha j hj, hb j hj], by rw [mulVec_add]⟩
      | smul c x _ hx =>
        obtain ⟨a, ha, rfl⟩ := hx
        exact ⟨c • a, fun j hj => by simp [ha j hj], by rw [mulVec_smul]⟩
    have hcol : ∀ i : Fin (m.val + 1), ∃ a : Fin (m.val + 1) → AF F ⊗[F] E, (∀ j, (fun k : Fin (m.val + 1) => k.val) i ≤ (fun k : Fin (m.val + 1) => k.val) j → a j = 0) ∧
        ((matHom _ σ J p).1 - 1) *ᵥ (fun k => inclR (F := F) (AF F) (GlobalTheory.StdPar.initCols X m k i)) =
          adMat F (GlobalTheory.StdPar.initCols X m) *ᵥ a := by
      intro i
      have h := (Subgroup.mem_iInf.1 hp.1 (Fin.castLE m.2 i)).2 _ (Submodule.subset_span ⟨_, rfl, rfl⟩)
      have hv : (fun k => inclR (F := F) (AF F) (GlobalTheory.StdPar.initCols X m k i)) = (adMat F X)ᵀ (Fin.castLE m.2 i) := rfl
      rw [hv, sub_mulVec, one_mulVec]
      obtain ⟨a, ha, e⟩ := span_lemma i _ (fun l hl => by
        obtain ⟨k, _, hlk, hki⟩ := hl
        have := Fin.lt_def.1 (lt_of_le_of_lt hlk hki)
        simpa using this) _ h
      exact ⟨a, ha, e.symm⟩
    obtain ⟨A, hA, e⟩ := lower_iff.1 hcol
    refine ⟨1 + A, fun l j hlt => ?_, ?_⟩
    · have hjl : j.val ≤ l.val := by
        by_contra hc
        refine absurd hlt (not_lt.2 (Finset.card_le_card fun k hk => ?_))
        simp only [Finset.mem_filter] at hk ⊢
        exact ⟨hk.1, by omega⟩
      have hne : l ≠ j := fun h => by subst h; exact lt_irrefl _ hlt
      rw [Matrix.add_apply, Matrix.one_apply_ne hne, hA l j hjl, add_zero]
    · rw [Matrix.mul_add, Matrix.mul_one, ← e, Matrix.sub_mul, Matrix.one_mul, add_sub_cancel]
  intro p hp
  exact ⟨key p hp, key p⁻¹ (inv_mem hp)⟩

end GlobalTheory.StdParFlag
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
open Matrix

namespace GlobalTheory.StdPar

theorem unip_le_unipFlag_initCols : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
      ∀ (S : Finset (Fin r)) (m : Fin r), m ∈ S → (∀ k ∈ S, k ≤ m) →
        GlobalTheory.StdPar.unip σ J X S ≤ GlobalTheory.UAut.unipFlag σ J (GlobalTheory.StdPar.initCols X m) (fun i => (S.filter fun k => k.val < i.val).card) := by
  intro F E _ _ _ _ _ σ _ n J _ r X Y _ S m hm hS g hg
  have e1 : {i | ∃ k ∈ S, i ≤ k} = {i | i ≤ m} :=
    Set.ext fun i => ⟨fun ⟨k, hk, h⟩ => h.trans (hS k hk), fun h => ⟨m, hm, h⟩⟩
  apply Subgroup.subset_closure
  refine ⟨fun i => ?_, fun x hx => ?_⟩
  · have key : ∀ y ∈ colSpan F X {l | ∃ k ∈ S, l ≤ k ∧ k < i.castLE m.2},
        ∃ a : Fin (m.val + 1) → AF F ⊗[F] E, (∀ j : Fin (m.val + 1), (S.filter fun k => k.val < i.val).card ≤
          (S.filter fun k => k.val < j.val).card → a j = 0) ∧ y = adMat F (initCols X m) *ᵥ a := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨l, ⟨k, hk, hlk, hki⟩, rfl⟩ := hy
        have hl : l.val < m.val + 1 := Nat.lt_succ_of_le (hlk.trans (hS k hk))
        refine ⟨Pi.single ⟨l.val, hl⟩ 1, fun j hj => ?_, ?_⟩
        · refine Pi.single_eq_of_ne ?_ _
          rintro rfl
          refine absurd hj (not_le.2 (Finset.card_lt_card ⟨fun t ht => ?_, fun h => ?_⟩))
          · rw [Finset.mem_filter] at ht ⊢
            exact ⟨ht.1, lt_trans (lt_of_lt_of_le ht.2 hlk) hki⟩
          · have := (Finset.mem_filter.1 (h (Finset.mem_filter.2 ⟨hk, hki⟩))).2
            exact absurd this (not_lt.2 hlk)
        · rw [mulVec_single_one]
          rfl
      | zero => exact ⟨0, fun _ _ => rfl, (mulVec_zero _).symm⟩
      | add y z _ _ hy hz =>
        obtain ⟨a, ha, rfl⟩ := hy
        obtain ⟨b, hb, rfl⟩ := hz
        exact ⟨a + b, fun j hj => by rw [Pi.add_apply, ha j hj, hb j hj, add_zero], (mulVec_add _ _ _).symm⟩
      | smul c y _ hy =>
        obtain ⟨a, ha, rfl⟩ := hy
        exact ⟨c • a, fun j hj => by rw [Pi.smul_apply, ha j hj, smul_zero], (mulVec_smul _ _ _).symm⟩
    have := (Subgroup.mem_iInf.1 hg.1 (i.castLE m.2)).2 _ (Submodule.subset_span ⟨_, rfl, rfl⟩)
    obtain ⟨a, ha, e⟩ := key _ this
    refine ⟨a, ha, ?_⟩
    rw [sub_mulVec, one_mulVec]
    exact e
  · have := hg.2.2 (fun i => inclR (F := F) (AF F) (x i)) (by
      rw [e1, mem_colPerp_iff]
      funext i
      exact (RingHom.map_mulVec (inclR (F := F) (AF F)) _ x i).symm.trans (by rw [hx]; exact map_zero _))
    rw [e1, mem_colSpan_iff] at this
    exact this.imp fun a ha => by rw [sub_mulVec, one_mulVec, ha]

end GlobalTheory.StdPar
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.kernelOfLineBundle_finiteFlat_subgroupScheme : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left), L.IsLB → Out.RelAmple A L → ∃ (H : Over (Sp R)) (_ : GrpObj H) (i : H ⟶ A), IsMonHom i ∧ Mono i ∧ IsFinite H.hom ∧ Flat H.hom ∧ ∀ (T : Over (Sp R)) (x : T ⟶ A), GlobalTheory.MemKL A L x ↔ ∃ z : T ⟶ H, z ≫ i = x := by
  first | exact @GlobalTheory.kernel_finiteFlat_subgroup | exact GlobalTheory.kernel_finiteFlat_subgroup | (intros; apply GlobalTheory.kernel_finiteFlat_subgroup <;> assumption)
end
