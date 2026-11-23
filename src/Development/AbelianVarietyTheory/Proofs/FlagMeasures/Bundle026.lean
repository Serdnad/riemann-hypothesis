module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle001
import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Cint
public import Mathlib.Analysis.Complex.Norm
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle014
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Group.Measure
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle018
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Basic.Complex.BigOperators

@[expose] public section

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.Sloc.CloseConj

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem cT_mul (L : LocE F E) {n : ℕ} (A B : Matrix (Fin n) (Fin n) E) :
    cT L (A * B) = cT L B * cT L A := by
  ext i j

  simp only [cT, Matrix.mul_apply, map_sum, map_mul]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem cT_one (L : LocE F E) {n : ℕ} : cT L (1 : Matrix (Fin n) (Fin n) E) = 1 := by
  ext i j
  simp only [cT, Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

theorem cT_sub (L : LocE F E) {n : ℕ} (A B : Matrix (Fin n) (Fin n) E) :
    cT L (A - B) = cT L A - cT L B := by
  ext i j
  simp [cT, map_sub]

theorem cj_mem (L : LocE F E) {x : E} (hx : x ∈ L.O) : L.cj x ∈ L.O := by
  rw [L.O_def] at hx ⊢
  exact hx.map (L.cj.toAlgHom.restrictScalars 𝒪[F])

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) (n : ℕ) (Z Zi M Mi M' : Matrix (Fin n) (Fin n) E) (t e : E), t ∈ L.O → L.cj t = t → Zi * Z = 1 → (∀ i j, e * Z i j ∈ L.O) → (∀ i j, e * Zi i j ∈ L.O) → Mi * M = 1 → M * Mi = 1 → (∀ i j, ∃ o ∈ L.O, (Mi - 1) i j = t * o) → cT L M * Z * M' = Z → ∀ i j, ∃ o ∈ L.O, e * e * (M' - 1) i j = t * o := by
  intro F _ _ _ E _ _ _ L n Z Zi M Mi M' t e ht htc hZiZ heZ heZi hMiM hMMi hclose hM'
  have hc : cT L Mi * cT L M = 1 := by rw [← cT_mul, hMMi, cT_one]
  have hM'eq : M' = Zi * cT L Mi * Z := by
    calc M' = Zi * (cT L Mi * cT L M) * Z * M' := by rw [hc, Matrix.mul_one, hZiZ, Matrix.one_mul]
      _ = Zi * cT L Mi * (cT L M * Z * M') := by simp only [Matrix.mul_assoc]
      _ = Zi * cT L Mi * Z := by rw [hM']
  have hsub : M' - 1 = Zi * cT L (Mi - 1) * Z := by
    rw [hM'eq, cT_sub, cT_one, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hZiZ]
  choose o ho hoe using hclose
  intro i j
  refine ⟨∑ l, ∑ k, (e * Zi i k) * L.cj (o l k) * (e * Z l j), ?_, ?_⟩
  · refine Subring.sum_mem _ fun l _ => Subring.sum_mem _ fun k _ => ?_
    exact Subring.mul_mem _ (Subring.mul_mem _ (heZi i k) (cj_mem L (ho l k))) (heZ l j)
  · rw [hsub]
    simp only [Matrix.mul_apply, cT, hoe, map_mul, htc, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
    ring

end GlobalTheory.Sloc.CloseConj
end

section

noncomputable section

open NumberField Matrix GlobalTheory.SgAlg
open scoped nonZeroDivisors

namespace GlobalTheory.SgGlob.Iota

variable {E : Type} [Field E] [NumberField E]
variable {σ : E →+* E} {n m r : ℕ} {J : Matrix (Fin n) (Fin n) E} {Jb : Matrix (Fin m) (Fin m) E}

open NumberField Matrix in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] in
private theorem one_le_inv_differentIdeal :
    (1 : FractionalIdeal (𝓞 E)⁰ E) ≤ (↑(differentIdeal ℤ (𝓞 E)))⁻¹ := by
  have h := FractionalIdeal.inv_anti_mono (K := E)
    (I := (↑(differentIdeal ℤ (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E)) (J := 1)
    (by simp [differentIdeal_ne_bot]) FractionalIdeal.coeIdeal_le_one
  simpa using h


open NumberField Matrix in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] in
theorem _root_.GlobalTheory.SgGlob.Iota.one_mem_dInv (j : ℕ) : (1 : E) ∈ _root_.GlobalTheory.SgGlob.dInv E j := by
  unfold _root_.GlobalTheory.SgGlob.dInv
  have hpow : (1 : FractionalIdeal (𝓞 E)⁰ E) ≤ (↑(differentIdeal ℤ (𝓞 E)))⁻¹ ^ j := by
    simpa using pow_le_pow_left' (one_le_inv_differentIdeal (E := E)) j
  exact hpow (FractionalIdeal.one_mem_one _)

section Pair

variable {g : ℕ} {Λ : Submodule (𝓞 E) (Fin n → E)} {P P' : Matrix (Fin n) (Fin (r + 1)) E}

end Pair

section Gram

end Gram

end GlobalTheory.SgGlob.Iota
end
end

section

noncomputable section

open NumberField Matrix GlobalTheory.SgAlg
open scoped nonZeroDivisors

namespace GlobalTheory.SgGlob.Inhab

variable {E : Type} [Field E] [NumberField E]

abbrev Int' (E : Type) [Field E] : Subring E := (algebraMap (𝓞 E) E).range

omit [NumberField E] in
theorem mem_int_iff (x : E) : x ∈ Int' E ↔ IsIntegral ℤ x :=
  ⟨fun ⟨y, hy⟩ => hy ▸ y.isIntegral_coe, fun h => ⟨⟨x, h⟩, rfl⟩⟩

omit [NumberField E] in
theorem map_mem_int (σ : E →+* E) {x : E} (h : x ∈ Int' E) : σ x ∈ Int' E := by
  rw [mem_int_iff] at h ⊢
  exact h.map σ.toIntAlgHom

omit [NumberField E] in
theorem smul_eq (c : 𝓞 E) (x : E) : c • x = algebraMap (𝓞 E) E c * x := Algebra.smul_def c x

theorem mem_dInv_zero (x : E) : x ∈ dInv E 0 ↔ x ∈ Int' E := by
  simp only [dInv, pow_zero, FractionalIdeal.mem_one_iff]
  rfl

def std (E : Type) [Field E] : Submodule (𝓞 E) (Fin 2 → E) :=
  Submodule.span (𝓞 E) {![0, 1], ![1, 1]}

omit [NumberField E] in
theorem mem_std (v : Fin 2 → E) : v ∈ std E ↔ v 0 ∈ Int' E ∧ v 1 ∈ Int' E := by
  rw [std, Submodule.mem_span_pair]
  constructor
  · rintro ⟨a, b, rfl⟩
    constructor
    · exact ⟨b, by simp [smul_eq]⟩
    · exact ⟨a + b, by simp [smul_eq]⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨b - a, a, ?_⟩
    ext i
    fin_cases i <;> simp [smul_eq, ← ha, ← hb]

omit [NumberField E] in
theorem form_two (σ : E →+* E) (v w : Fin 2 → E) :
    form σ !![1, 0; 0, -1] v w = σ (w 0) * v 0 - σ (w 1) * v 1 := by
  simp [form, dotProduct, Matrix.mulVec, Fin.sum_univ_two, sub_eq_add_neg]

theorem selfDual_std (σ : E →+* E) : SelfDual σ !![1, 0; 0, -1] (std E) := by
  refine ⟨Submodule.fg_span (Set.toFinite _), fun v => ⟨fun hv w hw => ?_, fun h => ?_⟩⟩
  · rw [mem_std] at hv hw
    rw [form_two]
    exact sub_mem (mul_mem (map_mem_int σ hw.1) hv.1) (mul_mem (map_mem_int σ hw.2) hv.2)
  · have h0 := h ![1, 0] ((mem_std _).2 ⟨one_mem _, zero_mem _⟩)
    have h1 := h ![0, -1] ((mem_std _).2 ⟨zero_mem _, neg_mem (one_mem _)⟩)
    rw [form_two] at h0 h1
    exact (mem_std v).2 ⟨by simpa using h0, by simpa using h1⟩

theorem frameLat_zero {n : ℕ} (P : Matrix (Fin n) (Fin (0 + 1)) E) :
    frameLat P = Submodule.span (𝓞 E) {fun i => P i 0} := by
  apply le_antisymm
  · rw [frameLat, Submodule.span_le]
    rintro v ⟨b, a, ha, rfl⟩
    obtain rfl : b = 0 := Subsingleton.elim (α := Fin 1) _ _
    obtain ⟨c, rfl⟩ := (mem_dInv_zero a).1 ha
    exact Submodule.mem_span_singleton.2 ⟨c, by ext i; simp [smul_eq]⟩
  · rw [Submodule.span_le]
    rintro v rfl
    exact Submodule.subset_span ⟨0, 1, (mem_dInv_zero 1).2 (one_mem _), by simp⟩

theorem pairLat_std {g : ℕ} (hg : g ≠ 0) :
    pairLat (r := 0) g (!![0; 1] : Matrix (Fin 2) (Fin (0 + 1)) E) !![(g : E); 1 + g] = std E := by
  have hg' : (g : E) ≠ 0 := Nat.cast_ne_zero.2 hg
  rw [pairLat, frameLat_zero, frameLat_zero, std, Submodule.span_insert]
  congr 3
  · ext i; fin_cases i <;> simp
  · ext i; fin_cases i <;> simp [hg']

theorem mem_genConf_zero (σ : E →+* E) {g : ℕ} (hg : g ≠ 0) :
    ((std E, !![0; 1], !![(g : E); 1 + g]) : Tri E 2 0) ∈
      GenConf σ !![1, 0; 0, -1] 1 (1 + 2 * g) g !![-1 - (g : E)] := by
  refine ⟨selfDual_std σ, ⟨⟨⟨!![0, 1], ?_⟩, ?_⟩, ⟨⟨!![-1, 1], ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · ext i j; fin_cases i; fin_cases j; simp [Matrix.mul_apply]
  · ext i j; fin_cases i; fin_cases j; simp [pairM, cT, TF, Matrix.mul_apply]
  · ext i j; fin_cases i; fin_cases j; simp [Matrix.mul_apply]
  · ext i j; fin_cases i; fin_cases j; simp [pairM, cT, TF, Matrix.mul_apply]; ring
  · ext i j; fin_cases i; fin_cases j; simp [pairM, cT, Matrix.mul_apply]; ring
  · dsimp only
    rw [pairLat_std hg]
    exact ⟨le_rfl, fun v hv _ => hv⟩

omit [NumberField E] in
theorem gq_zero (σ : E →+* E) (g : ℕ) :
    Gq (r := 0) σ 1 (1 + 2 * g) !![-1 - (g : E)] = (g : E) ^ 2 := by
  simp [Gq, GlobalTheory.SgAlg.lead] <;> ring

end GlobalTheory.SgGlob.Inhab
end
end

section

open GlobalTheory.IdxInt
open scoped Pointwise Classical

namespace GlobalTheory.IdxInt

open scoped Pointwise Classical in
variable {W : Type} [AddCommGroup W] in
private lemma eq_of_mem_finset_of_mk_eq {A B : AddSubgroup W} {R : Finset W}
    (hRA : ∀ w ∈ R, w ∈ A) (hR : ∀ w ∈ A, ∃! x, x ∈ R ∧ w - x ∈ B)
    {x y : W} (hx : x ∈ R) (hy : y ∈ R) (h : (x : W ⧸ B) = y) : x = y := by
  have hxy : -x + y ∈ B := QuotientAddGroup.eq.mp h
  obtain ⟨z, _, hz⟩ := hR y (hRA y hy)
  have h1 := hz y ⟨hy, by simp⟩
  have h2 := hz x ⟨hx, by rwa [sub_eq_neg_add]⟩
  exact h2.trans h1.symm

open scoped Pointwise Classical in
variable {W : Type} [AddCommGroup W] in
private lemma exists_mem_finset_mk_eq_of_mem {A B : AddSubgroup W} {R : Finset W}
    (hR : ∀ w ∈ A, ∃! x, x ∈ R ∧ w - x ∈ B) {w : W} (hw : w ∈ A) :
    ∃ x ∈ R, (x : W ⧸ B) = w := by
  obtain ⟨x, ⟨hx, hwx⟩, _⟩ := hR w hw
  refine ⟨x, hx, QuotientAddGroup.eq.mpr ?_⟩
  rw [← sub_eq_neg_add]
  exact hwx

open scoped Pointwise Classical in
variable {W : Type} [AddCommGroup W] in
private lemma apply_eq_of_quotient_mk_eq_of_invariant {B : AddSubgroup W} {φ : W → ℂ}
    (hinv : ∀ w, ∀ b ∈ B, φ (w + b) = φ w) {u v : W} (h : (u : W ⧸ B) = v) : φ u = φ v := by
  have hb : -u + v ∈ B := QuotientAddGroup.eq.mp h
  have := hinv u (-u + v) hb
  rwa [add_neg_cancel_left, eq_comm] at this


open scoped Pointwise Classical in
variable {W : Type} [AddCommGroup W] in
theorem _root_.GlobalTheory.IdxInt.cint_eq_mean_reps {W : Type} [AddCommGroup W]
    (A B : AddSubgroup W) (φ : W → ℂ) (R : Finset W)
    (hBA : B ≤ A) (hinv : ∀ w, ∀ b ∈ B, φ (w + b) = φ w) (hsupp : ∀ w, w ∉ A → φ w = 0)
    (hRA : ∀ w ∈ R, w ∈ A) (hR : ∀ w ∈ A, ∃! x, x ∈ R ∧ w - x ∈ B) :
    _root_.GlobalTheory.IdxInt.Fine A φ B ∧ (R.card : ℕ) = B.relIndex A ∧
      _root_.GlobalTheory.IdxInt.cint A φ = (∑ w ∈ R, φ w) / (R.card : ℂ) := by
  have hmemA : ∀ w, φ w ≠ 0 → w ∈ A := fun w hw => by
    by_contra h
    exact hw (hsupp w h)
  have hcard : (R.card : ℕ) = B.relIndex A := by
    let f : R → A ⧸ B.addSubgroupOf A := fun x => ((⟨x.1, hRA x.1 x.2⟩ : A) : A ⧸ B.addSubgroupOf A)
    have hf : Function.Bijective f := by
      constructor
      · rintro ⟨x, hx⟩ ⟨y, hy⟩ h
        have h' : -(⟨x, hRA x hx⟩ : A) + ⟨y, hRA y hy⟩ ∈ B.addSubgroupOf A :=
          QuotientAddGroup.eq.mp h
        rw [AddSubgroup.mem_addSubgroupOf] at h'
        have h'' : -x + y ∈ B := by simpa using h'
        exact Subtype.ext (eq_of_mem_finset_of_mk_eq hRA hR hx hy (QuotientAddGroup.eq.mpr h''))
      · intro c
        induction c using QuotientAddGroup.induction_on with
        | H a =>
          obtain ⟨x, ⟨hx, hax⟩, _⟩ := hR a.1 a.2
          refine ⟨⟨x, hx⟩, QuotientAddGroup.eq.mpr ?_⟩
          rw [AddSubgroup.mem_addSubgroupOf]
          have : -x + a.1 ∈ B := by rwa [← sub_eq_neg_add]
          simpa using this
    rw [AddSubgroup.relIndex, AddSubgroup.index, ← Nat.card_congr (Equiv.ofBijective f hf),
      Nat.card_eq_fintype_card, Fintype.card_coe]
  have hne : R.card ≠ 0 := by
    obtain ⟨x, ⟨hx, _⟩, _⟩ := hR 0 A.zero_mem
    exact Finset.card_ne_zero_of_mem hx
  have hfine : _root_.GlobalTheory.IdxInt.Fine A φ B := by
    unfold _root_.GlobalTheory.IdxInt.Fine
    refine ⟨hBA, hcard ▸ hne, fun w b hb => hinv w b hb, ?_⟩
    refine (R.finite_toSet.image (QuotientAddGroup.mk : W → W ⧸ B)).subset ?_
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨x, hx, hxw⟩ := exists_mem_finset_mk_eq_of_mem hR (hmemA w hw)
    exact ⟨x, hx, hxw⟩
  refine ⟨hfine, hcard, ?_⟩
  have hsum : ∑ᶠ c : W ⧸ B, φ (Quotient.out c) = ∑ w ∈ R, φ w := by
    rw [finsum_eq_sum_of_support_subset (s := R.image (QuotientAddGroup.mk : W → W ⧸ B)) _ ?_]
    · rw [Finset.sum_image (fun x hx y hy h => eq_of_mem_finset_of_mk_eq hRA hR hx hy h)]
      exact Finset.sum_congr rfl fun x _ => apply_eq_of_quotient_mk_eq_of_invariant hinv (QuotientAddGroup.out_eq' _)
    · intro c hc
      obtain ⟨x, hx, hxc⟩ := exists_mem_finset_mk_eq_of_mem hR (hmemA _ hc)
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
      exact ⟨x, hx, hxc.trans (QuotientAddGroup.out_eq' c)⟩
  rw [_root_.GlobalTheory.IdxInt.cint_eq_of_fine A B φ hfine, hsum, ← hcard]

end GlobalTheory.IdxInt
end

section

open GlobalTheory.IdxInt
open scoped Pointwise Classical

namespace GlobalTheory.IdxInt.Lin

variable {W : Type} [AddCommGroup W]

open scoped Pointwise Classical in
open Function in
private lemma quotientEquivProdOfLE_mk_fst {W : Type} [AddCommGroup W] {C B : AddSubgroup W}
    (h : C ≤ B) (w : W) : ((AddSubgroup.quotientEquivProdOfLE h) (w : W ⧸ C)).1 = (w : W ⧸ B) :=
  rfl

open scoped Pointwise Classical in
open Function in
private lemma Fine_of_le_of_relIndex_ne_zero {W : Type} [AddCommGroup W] {A B C : AddSubgroup W} {φ : W → ℂ}
    (hB : _root_.GlobalTheory.IdxInt.Fine A φ B) (hCB : C ≤ B) (hC : C.relIndex A ≠ 0) :
    _root_.GlobalTheory.IdxInt.Fine A φ C := by
  obtain ⟨hBA, -, hinv, hsupp⟩ := hB
  have hidx : C.relIndex B ≠ 0 := by
    rw [← AddSubgroup.relIndex_mul_relIndex C B A hCB hBA] at hC
    exact left_ne_zero_of_mul hC
  have hfin : Finite (B ⧸ C.addSubgroupOf B) := Nat.finite_of_card_ne_zero hidx
  refine ⟨hCB.trans hBA, hC, fun w b hb => hinv w b (hCB hb), ?_⟩
  let e := AddSubgroup.quotientEquivProdOfLE hCB
  refine ((hsupp.prod (Set.finite_univ (α := B ⧸ C.addSubgroupOf B))).preimage
    e.injective.injOn).subset ?_
  rintro _ ⟨w, hw, rfl⟩
  simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true]
  rw [quotientEquivProdOfLE_mk_fst]
  exact ⟨w, hw, rfl⟩

open scoped Pointwise Classical in
variable {W : Type} [AddCommGroup W] in
private lemma exists_fine_fine_of_nice_nice {W : Type} [AddCommGroup W] {A : AddSubgroup W} {φ ψ : W → ℂ}
    (hφ : _root_.GlobalTheory.IdxInt.Nice A φ) (hψ : _root_.GlobalTheory.IdxInt.Nice A ψ) :
    ∃ C, _root_.GlobalTheory.IdxInt.Fine A φ C ∧ _root_.GlobalTheory.IdxInt.Fine A ψ C := by
  obtain ⟨B, hB⟩ := hφ
  obtain ⟨B', hB'⟩ := hψ
  have hidx : (B ⊓ B').relIndex A ≠ 0 := AddSubgroup.relIndex_inf_ne_zero hB.2.1 hB'.2.1
  exact ⟨B ⊓ B', Fine_of_le_of_relIndex_ne_zero hB inf_le_left hidx, Fine_of_le_of_relIndex_ne_zero hB' inf_le_right hidx⟩

open scoped Pointwise Classical in
variable {W : Type} [AddCommGroup W] in
private lemma Fine_add {W : Type} [AddCommGroup W] {A C : AddSubgroup W} {φ ψ : W → ℂ}
    (hφ : _root_.GlobalTheory.IdxInt.Fine A φ C) (hψ : _root_.GlobalTheory.IdxInt.Fine A ψ C) :
    _root_.GlobalTheory.IdxInt.Fine A (φ + ψ) C := by
  refine ⟨hφ.1, hφ.2.1, fun w b hb => by simp only [Pi.add_apply, hφ.2.2.1 w b hb, hψ.2.2.1 w b hb], ?_⟩
  refine (hφ.2.2.2.union hψ.2.2.2).subset ?_
  rintro _ ⟨w, hw, rfl⟩
  rcases Function.support_add φ ψ hw with h | h
  · exact Or.inl ⟨w, h, rfl⟩
  · exact Or.inr ⟨w, h, rfl⟩

open scoped Pointwise Classical in
open Function in
private lemma finite_support_quotient_out_of_finite_image {W : Type} [AddCommGroup W] {B : AddSubgroup W} (φ : W → ℂ)
    (hφ : ((fun w : W => (w : W ⧸ B)) '' support φ).Finite) :
    (support fun c : W ⧸ B => φ (Quotient.out c)).Finite := by
  refine hφ.subset fun c hc => ⟨Quotient.out c, hc, QuotientAddGroup.out_eq' c⟩


open scoped Pointwise Classical in
variable {W : Type} [AddCommGroup W] in
theorem _root_.GlobalTheory.IdxInt.Lin.main : ∀ {W : Type} [AddCommGroup W] (A : AddSubgroup W), (∀ φ ψ : W → ℂ, _root_.GlobalTheory.IdxInt.Nice A φ → _root_.GlobalTheory.IdxInt.Nice A ψ → _root_.GlobalTheory.IdxInt.Nice A (φ + ψ) ∧ _root_.GlobalTheory.IdxInt.cint A (φ + ψ) = _root_.GlobalTheory.IdxInt.cint A φ + _root_.GlobalTheory.IdxInt.cint A ψ ∧ ((∀ w, ‖φ w‖ ≤ (ψ w).re) → ‖_root_.GlobalTheory.IdxInt.cint A φ‖ ≤ (_root_.GlobalTheory.IdxInt.cint A ψ).re)) ∧ (∀ (c : ℂ) (φ : W → ℂ), _root_.GlobalTheory.IdxInt.Nice A φ → _root_.GlobalTheory.IdxInt.Nice A (fun w => c * φ w) ∧ _root_.GlobalTheory.IdxInt.cint A (fun w => c * φ w) = c * _root_.GlobalTheory.IdxInt.cint A φ) ∧ (∀ P : W → Prop, 0 ≤ (_root_.GlobalTheory.IdxInt.cint A (_root_.GlobalTheory.IdxInt.ind P)).re ∧ (_root_.GlobalTheory.IdxInt.cint A (_root_.GlobalTheory.IdxInt.ind P)).im = 0) ∧ ∀ (ι : Type) (s : Finset ι) (φ : ι → W → ℂ), (∀ i ∈ s, _root_.GlobalTheory.IdxInt.Nice A (φ i)) → _root_.GlobalTheory.IdxInt.Nice A (fun w => ∑ i ∈ s, φ i w) ∧ _root_.GlobalTheory.IdxInt.cint A (fun w => ∑ i ∈ s, φ i w) = ∑ i ∈ s, _root_.GlobalTheory.IdxInt.cint A (φ i) := by
  intro W _ A
  have hadd : ∀ φ ψ : W → ℂ, _root_.GlobalTheory.IdxInt.Nice A φ → _root_.GlobalTheory.IdxInt.Nice A ψ → _root_.GlobalTheory.IdxInt.Nice A (φ + ψ) ∧ _root_.GlobalTheory.IdxInt.cint A (φ + ψ) = _root_.GlobalTheory.IdxInt.cint A φ + _root_.GlobalTheory.IdxInt.cint A ψ ∧ ((∀ w, ‖φ w‖ ≤ (ψ w).re) → ‖_root_.GlobalTheory.IdxInt.cint A φ‖ ≤ (_root_.GlobalTheory.IdxInt.cint A ψ).re) := by
    intro φ ψ hφ hψ
    obtain ⟨C, hφC, hψC⟩ := exists_fine_fine_of_nice_nice hφ hψ
    have hsum := Fine_add hφC hψC
    have hfφ := finite_support_quotient_out_of_finite_image φ hφC.2.2.2
    have hfψ := finite_support_quotient_out_of_finite_image ψ hψC.2.2.2
    refine ⟨⟨C, hsum⟩, ?_, fun hle => ?_⟩
    · rw [_root_.GlobalTheory.IdxInt.cint_eq_of_fine A C _ hsum, _root_.GlobalTheory.IdxInt.cint_eq_of_fine A C _ hφC,
        _root_.GlobalTheory.IdxInt.cint_eq_of_fine A C _ hψC, ← add_div]
      simp only [Pi.add_apply]
      rw [finsum_add_distrib hfφ hfψ]
    · rw [_root_.GlobalTheory.IdxInt.cint_eq_of_fine A C _ hφC, _root_.GlobalTheory.IdxInt.cint_eq_of_fine A C _ hψC,
        finsum_eq_sum_of_support_subset (s := (hfφ.union hfψ).toFinset) _ (by simp),
        finsum_eq_sum_of_support_subset (s := (hfφ.union hfψ).toFinset) _ (by simp),
        norm_div, Complex.norm_natCast, Complex.div_natCast_re, Complex.re_sum]
      gcongr
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hle _)
  refine ⟨hadd, ?_, ?_, ?_⟩
  · intro c φ hφ
    obtain ⟨B, hB⟩ := hφ
    have hc : _root_.GlobalTheory.IdxInt.Fine A (fun w => c * φ w) B :=
      ⟨hB.1, hB.2.1, fun w b hb => by simp only [hB.2.2.1 w b hb],
        hB.2.2.2.subset (Set.image_mono (Function.support_mul_subset_right _ _))⟩
    refine ⟨⟨B, hc⟩, ?_⟩
    rw [_root_.GlobalTheory.IdxInt.cint_eq_of_fine A B _ hc, _root_.GlobalTheory.IdxInt.cint_eq_of_fine A B _ hB,
      ← mul_finsum, mul_div_assoc]
  · intro P
    by_cases h : _root_.GlobalTheory.IdxInt.Nice A (_root_.GlobalTheory.IdxInt.ind P)
    · obtain ⟨B, hB⟩ := h
      rw [_root_.GlobalTheory.IdxInt.cint_eq_of_fine A B _ hB,
        finsum_eq_sum _ (finite_support_quotient_out_of_finite_image _ hB.2.2.2), Complex.div_natCast_re, Complex.div_natCast_im,
        Complex.re_sum, Complex.im_sum]
      refine ⟨div_nonneg (Finset.sum_nonneg fun i _ => ?_) (Nat.cast_nonneg _), ?_⟩
      · unfold _root_.GlobalTheory.IdxInt.ind
        split_ifs <;> simp
      · rw [Finset.sum_eq_zero fun i _ => ?_, zero_div]
        unfold _root_.GlobalTheory.IdxInt.ind
        split_ifs <;> simp
    · unfold _root_.GlobalTheory.IdxInt.cint
      rw [dite_eq_right h]
      simp
  · intro ι s φ hs
    induction s using Finset.induction_on with
    | empty =>
      have h0 : _root_.GlobalTheory.IdxInt.Fine A (fun _ : W => (0 : ℂ)) A :=
        ⟨le_rfl, by simp [AddSubgroup.relIndex_self], fun _ _ _ => rfl, by simp⟩
      simp only [Finset.sum_empty]
      refine ⟨⟨A, h0⟩, ?_⟩
      rw [_root_.GlobalTheory.IdxInt.cint_eq_of_fine A A _ h0]
      simp
    | insert i s hi ih =>
      have hi' := hs i (Finset.mem_insert_self i s)
      have ih' := ih fun j hj => hs j (Finset.mem_insert_of_mem hj)
      simp only [Finset.sum_insert hi]
      obtain ⟨hn, he, -⟩ := hadd (φ i) (fun w => ∑ j ∈ s, φ j w) hi' ih'.1
      exact ⟨hn, he.trans (by rw [ih'.2])⟩

end GlobalTheory.IdxInt.Lin
end

section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

theorem _root_.GlobalTheory.T.upperDensity_bounds_almost_homogeneous_measure : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (l ν : Measure V) [l.IsAddHaarMeasure] [IsFiniteMeasure ν] (c : ℝ≥0∞), c ≠ ⊤ → Tendsto (fun r : ℝ => ν (Metric.ball 0 r) / l (Metric.ball 0 r)) (𝓝[>] 0) (𝓝 c) → ∀ ε η : ℝ, 0 < ε → ε < 1 → (∀ x : V, ‖x‖ < η → ∀ᶠ r in 𝓝[>] (0:ℝ), ν (Metric.ball x ((1 - ε) * r)) ≤ ν (Metric.ball 0 r) ∧ ν (Metric.ball 0 r) ≤ ν (Metric.ball x ((1 + ε) * r))) → ∀ x : V, ‖x‖ < η → ENNReal.ofReal ((1 + ε)⁻¹ ^ Module.finrank ℝ V) * c ≤ GlobalTheory.HaarDensChart.upperDens l ν x ∧ GlobalTheory.HaarDensChart.upperDens l ν x ≤ ENNReal.ofReal (((1 + ε) / (1 - ε)) ^ Module.finrank ℝ V) * c := by
  first | exact @GlobalTheory.upperDens_bounds_of_almost_homogeneous | exact GlobalTheory.upperDens_bounds_of_almost_homogeneous | (intros; apply GlobalTheory.upperDens_bounds_of_almost_homogeneous <;> assumption)
end
