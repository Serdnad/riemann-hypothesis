module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle605
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle606
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.DiscPrism

variable {l : ℕ} [hl : Fact l.Prime]

theorem breuilKisinDatum_radius_pow_degree_eq_inv {K : FinExt l} (bk : BK K) : bk.ρ₀ ^ bk.Ep.natDegree = (l : ℝ≥0)⁻¹ := by
  have he : (bk.Ep.natDegree : ℝ) ≠ 0 := Nat.cast_ne_zero.2 bk.deg_pos.ne'
  unfold BK.ρ₀
  rw [← NNReal.rpow_natCast, ← NNReal.rpow_mul, neg_mul, one_div, inv_mul_cancel₀ he, NNReal.rpow_neg_one]

theorem breuilKisinDatum_radius_le_one {K : FinExt l} (bk : BK K) : bk.ρ₀ ≤ 1 := by
  unfold BK.ρ₀
  exact NNReal.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hl.out.one_lt.le)
    (neg_nonpos.2 (by positivity))

theorem breuilKisinDatum_radius_pos {K : FinExt l} (bk : BK K) : 0 < bk.ρ₀ := by
  unfold BK.ρ₀
  exact NNReal.rpow_pos (by exact_mod_cast hl.out.pos)

theorem inv_le_rho {K : FinExt l} (bk : BK K) {ρ : ℝ≥0} (h : bk.ρ₀ ≤ ρ) : (l : ℝ≥0)⁻¹ ≤ ρ := by
  rw [← breuilKisinDatum_radius_pow_degree_eq_inv]
  exact (pow_le_of_le_one (by positivity) (breuilKisinDatum_radius_le_one bk) bk.deg_pos.ne').trans h

theorem E_eq {K : FinExt l} (bk : BK K) : ∃ q : bk.S, bk.E = X ^ bk.Ep.natDegree + (l : bk.S) * q := by
  have hm : bk.Ep - Polynomial.X ^ bk.Ep.natDegree ∈ (Ideal.span {(l : Wq l bk.a)}).map Polynomial.C := by
    rw [Ideal.mem_map_C_iff]
    intro n
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow]
    rcases lt_trichotomy n bk.Ep.natDegree with hn | hn | hn
    · rw [if_neg hn.ne, sub_zero]
      exact Ideal.mem_span_singleton.2 (bk.dvd_coeff n hn)
    · subst hn
      rw [if_pos rfl, bk.monic.coeff_natDegree, sub_self]; exact zero_mem _
    · rw [if_neg hn.ne', Polynomial.coeff_eq_zero_of_natDegree_lt hn, sub_zero]; exact zero_mem _
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton] at hm
  obtain ⟨q, hq⟩ := hm
  refine ⟨(q : bk.S), ?_⟩
  have h1 : bk.Ep = Polynomial.X ^ bk.Ep.natDegree + Polynomial.C (l : Wq l bk.a) * q := by
    rw [← hq]; ring
  have h2 : (bk.Ep : bk.S) =
      ((Polynomial.X ^ bk.Ep.natDegree + Polynomial.C (l : Wq l bk.a) * q : Polynomial (Wq l bk.a)) : bk.S) :=
    congrArg _ h1
  show (bk.Ep : bk.S) = _
  rw [h2, Polynomial.coe_add, Polynomial.coe_pow, Polynomial.coe_X, Polynomial.coe_mul, Polynomial.coe_C, map_natCast]

theorem gauge_mono_le {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0) (a b : ℕ) {r : ℝ} (hr : 0 < r)
    (h : (ρ : ℝ) ^ b ≤ r * (l : ℝ) ^ a) :
    ‖algebraMap A (PreDisc l u ρ) ((l : A) ^ a * u ^ b)‖ ≤ r :=
  gauge_le l u ρ hr (Submodule.subset_span ⟨a, b, 0, by simpa using h, by simp⟩)

end GlobalTheory.BSP.DiscPrism

namespace GlobalTheory.BSP.DiscPrism

variable {l : ℕ} [hl : Fact l.Prime]

theorem norm_toDisc_hf_le {K : FinExt l} (bk : BK K) (B : Obj l ↥(OL K)) (f g : Hom bk.prism B) (ρ : ℝ≥0)
    (h0 : bk.ρ₀ ≤ ρ) (h1 : ρ ≤ 1) : ‖toDisc l (BK.hf f X) ρ (BK.hf g X)‖ ≤ ρ := by
  have hρ : (0 : ℝ) < ρ := NNReal.coe_pos.2 ((breuilKisinDatum_radius_pos bk).trans_le h0)
  have hρ1 : (ρ : ℝ) ≤ 1 := by exact_mod_cast h1
  have hl0 : (0 : ℝ) < l := Nat.cast_pos.2 hl.out.pos
  have hlρ : (1 : ℝ) ≤ ρ * l := by
    have h := inv_le_rho bk h0
    have h' : ((l : ℝ))⁻¹ ≤ ρ := by exact_mod_cast h
    rw [inv_le_iff_one_le_mul₀ hl0] at h'
    linarith [mul_comm (l : ℝ) ρ]
  set u := BK.hf f X with hu
  let am := algebraMap B.A (PreDisc l u ρ)
  have um : ∀ x y : PreDisc l u ρ, ‖x + y‖ ≤ max ‖x‖ ‖y‖ := gauge_add_le_max l u ρ
  have hX : ‖am u‖ ≤ ρ := by
    simpa using gauge_mono_le (l := l) u ρ 0 1 hρ (by simp)
  have hE : ‖am (BK.hf f bk.E)‖ ≤ ρ := by
    obtain ⟨q, hq⟩ := E_eq bk
    have e1 : BK.hf f bk.E = u ^ bk.Ep.natDegree + (l : B.A) ^ 1 * u ^ 0 * BK.hf f q := by
      rw [hq, map_add (f := _), map_pow, map_mul, map_natCast, hu]; ring
    rw [e1, map_add (f := _), map_mul]
    refine (um _ _).trans (max_le ?_ ?_)
    · have := gauge_mono_le (l := l) u ρ 0 bk.Ep.natDegree hρ
        (by simpa using pow_le_of_le_one hρ.le hρ1 bk.deg_pos.ne')
      simpa using this
    · refine (norm_mul_le _ _).trans ?_
      have h2 := gauge_mono_le (l := l) u ρ 1 0 hρ (by simpa using hlρ)
      have h3 := norm_algebraMap_le (l := l) (u := u) (ρ := ρ) (BK.hf f q)
      calc _ ≤ (ρ : ℝ) * 1 := mul_le_mul h2 h3 (norm_nonneg _) hρ.le
        _ = ρ := mul_one _
  have hmem : BK.hf g X - BK.hf f X ∈ B.I := by
    have hs : Ideal.Quotient.mk bk.prism.I (X : bk.S) = bk.prism.str (bk.str.symm (Ideal.Quotient.mk _ X)) :=
      (bk.str.apply_symm_apply _).symm
    exact Ideal.Quotient.eq.1 ((g.f_str _ _ hs).trans (f.f_str _ _ hs).symm)
  have hI : B.I = Ideal.span {BK.hf f bk.E} := by
    rw [← GlobalTheory.T.prism_hom_map_ideal_eq l ↥(OL K) bk.prism B f]
    show (Ideal.span {bk.E}).map (BK.hf f) = _
    rw [Ideal.map_span, Set.image_singleton]
  rw [hI, Ideal.mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  have e2 : BK.hf g X = u + BK.hf f bk.E * c := by rw [← hc, hu]; ring
  show ‖ofPre l u ρ (am (BK.hf g X))‖ ≤ ρ
  rw [norm_ofPre, ← norm_preDisc, e2, map_add (f := _), map_mul]
  refine (um _ _).trans (max_le hX ?_)
  refine (norm_mul_le _ _).trans ?_
  calc _ ≤ (ρ : ℝ) * 1 := mul_le_mul hE (norm_algebraMap_le _) (norm_nonneg _) hρ.le
    _ = ρ := mul_one _

theorem disc_map_exists : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), ∀ (B : Obj l ↥(OL K))
    (f g : Hom bk.prism B) (ρ : ℝ≥0), bk.ρ₀ ≤ ρ → ρ ≤ 1 →
    ∃ F : bk.DS ρ →+* Disc l (BK.hf f X) ρ, IsDiscMap (l := _) (u := _) (ρ := _) (BK.hf g) F := by
  intro l _ K bk B f g ρ h0 h1
  exact ⟨Disc.map (BK.hf g) (norm_toDisc_hf_le bk B f g ρ h0 h1), isDiscMap_map _ _⟩

end GlobalTheory.BSP.DiscPrism
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.IdealSubMembership

theorem padicInt_ringHom_ext {l : ℕ} [Fact l.Prime] {A : Type} [CommRing A] {J : Ideal A}
    (hlJ : (l : A) ∈ J) [IsHausdorff J A] (φ ψ : ℤ_[l] →+* A) : φ = ψ := by
  ext c
  rw [← sub_eq_zero]
  refine IsHausdorff.haus' (I := J) _ fun n => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.1 (PadicInt.appr_spec n c)
  have h1 : c = ((c.appr n : ℕ) : ℤ_[l]) + (l : ℤ_[l]) ^ n * d := by rw [← hd]; ring
  have e : φ c - ψ c = (l : A) ^ n * (φ d - ψ d) := by
    rw [h1]
    simp only [map_add (f := _), map_mul, map_pow, map_natCast]
    ring
  rw [e]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hlJ n)

theorem eq_of_pow_eq_self {A : Type} [CommRing A] {J : Ideal A} (hJ : J ≤ (⊥ : Ideal A).jacobson) {q : ℕ}
    (hq : (q : A) ∈ J) {x y : A} (hx : x ^ q = x) (hy : y ^ q = y) (hxy : x - y ∈ J) : x = y := by
  set S := ∑ i ∈ Finset.range q, x ^ i * y ^ (q - 1 - i) with hS
  have hS1 : S * (x - y) = x - y := by
    rw [hS, geom_sum₂_mul, hx, hy]
  have hSJ : S ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have hxy' : Ideal.Quotient.mk J y = Ideal.Quotient.mk J x := (Ideal.Quotient.eq.2 hxy).symm
    have hq' : (q : A ⧸ J) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk J), Ideal.Quotient.eq_zero_iff_mem]; exact hq

    rw [hS, map_sum]
    simp only [map_mul, map_pow, hxy']
    rcases Nat.eq_zero_or_pos q with h0 | hpos
    · subst h0; simp
    have : ∀ i ∈ Finset.range q, (Ideal.Quotient.mk J x) ^ i * (Ideal.Quotient.mk J x) ^ (q - 1 - i) =
        (Ideal.Quotient.mk J x) ^ (q - 1) := fun i hi => by
      rw [← pow_add]; congr 1; have := Finset.mem_range.1 hi; omega
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul, hq', zero_mul]
  have hu : IsUnit (S * (-1) + 1) := (Ideal.mem_jacobson_bot.1 (hJ hSJ)) (-1)
  have h2 : (S * (-1) + 1) * (x - y) = 0 := by linear_combination -hS1
  rw [← sub_eq_zero]
  exact (hu.mul_right_eq_zero).1 h2

variable {l : ℕ} [hl : Fact l.Prime]

theorem sub_mem_I {K : FinExt l} (bk : BK K) {B : Obj l ↥(OL K)} (f g : Hom bk.prism B) (x : bk.S) :
    BK.hf f x - BK.hf g x ∈ B.I := by
  have h : Ideal.Quotient.mk bk.prism.I x = bk.prism.str (bk.str.symm (Ideal.Quotient.mk _ x)) :=
    (bk.str.apply_symm_apply _).symm
  rw [← Ideal.Quotient.eq]
  exact (f.f_str _ x h).trans (g.f_str _ x h).symm

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K)) (f g : Hom bk.prism B),
    (∀ w, BK.hf f (PowerSeries.C w) = BK.hf g (PowerSeries.C w)) ∧ BK.hf f X - BK.hf g X ∈ B.I ∧
      B.I = Ideal.span {BK.hf f bk.E} := by
  intro l _ K bk B f g
  haveI := B.complete
  have hlJ : (l : B.A) ∈ Ideal.span {(l : B.A)} ⊔ B.I := Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
  refine ⟨fun w => ?_, sub_mem_I bk f g X, ?_⟩
  · let φ1 : Wq l bk.a →+* B.A := (BK.hf f).comp C
    let φ2 : Wq l bk.a →+* B.A := (BK.hf g).comp C
    have hz := padicInt_ringHom_ext hlJ (φ1.comp (algebraMap ℤ_[l] (Wq l bk.a)))
      (φ2.comp (algebraMap ℤ_[l] (Wq l bk.a)))
    have ht : ∀ z : Fq l bk.a, φ1 (WittVector.teichmuller l z) = φ2 (WittVector.teichmuller l z) := by
      intro z
      have hq : ((l ^ bk.a : ℕ) : B.A) ∈ Ideal.span {(l : B.A)} ⊔ B.I := by
        rw [Nat.cast_pow]; exact Ideal.pow_mem_of_mem _ hlJ _ (Nat.pos_of_ne_zero (NeZero.ne bk.a))
      have hp : WittVector.teichmuller l z ^ (l ^ bk.a) = WittVector.teichmuller l z := by
        rw [← map_pow, Fq.pow_card]
      refine eq_of_pow_eq_self (IsAdicComplete.le_jacobson_bot _) hq ?_ ?_
        (Ideal.mem_sup_right (sub_mem_I bk f g _))
      · rw [← map_pow, hp]
      · rw [← map_pow, hp]
    have hw : w ∈ Submodule.span ℤ_[l] (Set.range (WittVector.teichmuller l : Fq l bk.a → Wq l bk.a)) := by
      rw [span_teich]; exact Submodule.mem_top
    change φ1 w = φ2 w
    induction hw using Submodule.span_induction with
    | mem x hx => obtain ⟨z, rfl⟩ := hx; exact ht z
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
    | smul c x _ hx =>
      rw [Algebra.smul_def, map_mul, map_mul, hx]
      exact congrArg (· * φ2 x) (RingHom.congr_fun hz c)
  · rw [← GlobalTheory.T.prism_hom_map_ideal_eq l _ bk.prism B f]
    change Ideal.map f.f (Ideal.span ({bk.E} : Set bk.prism.A)) = _
    rw [Ideal.map_span]
    exact congrArg Ideal.span (Set.image_singleton (f := f.f) (a := bk.E))

end GlobalTheory.BSP.IdealSubMembership
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.ImageTower

variable {S A : Type} [CommRing S] [CommRing A] (e : S →+* A) (p : ℕ) {d : ℕ} {d' : ℕ → ℕ}
  (R : ∀ n, Matrix (Fin d) (Fin (d' n)) A)

def Img (n m : ℕ) : Set (Fin d → A) :=
  {w | ∃ s : Fin (d' m) → S, ∀ i, (p : A) ^ n ∣ (w - R m *ᵥ fun j => e (s j)) i}

variable {e p R}

theorem mem_of_dvd {n m : ℕ} {w x : Fin d → A} (hw : w ∈ Img e p R n m)
    (h : ∀ i, (p : A) ^ n ∣ (x - w) i) : x ∈ Img e p R n m := by
  obtain ⟨s, hs⟩ := hw
  refine ⟨s, fun i => ?_⟩
  have : (x - R m *ᵥ fun j => e (s j)) i = (x - w) i + (w - R m *ᵥ fun j => e (s j)) i := by
    simp only [Pi.sub_apply]; ring
  rw [this]; exact dvd_add (h i) (hs i)

theorem add_mem {n m : ℕ} {w x : Fin d → A} (hw : w ∈ Img e p R n m) (hx : x ∈ Img e p R n m) :
    w + x ∈ Img e p R n m := by
  obtain ⟨s, hs⟩ := hw
  obtain ⟨t, ht⟩ := hx
  refine ⟨s + t, fun i => ?_⟩
  have he : (fun j => e ((s + t) j)) = (fun j => e (s j)) + fun j => e (t j) := by
    funext j; simp
  rw [he, mulVec_add]
  have : (w + x - ((R m *ᵥ fun j => e (s j)) + R m *ᵥ fun j => e (t j))) i =
      (w - R m *ᵥ fun j => e (s j)) i + (x - R m *ᵥ fun j => e (t j)) i := by
    simp only [Pi.sub_apply, Pi.add_apply]; ring
  rw [this]; exact dvd_add (hs i) (ht i)

theorem image_mem (n m : ℕ) (s : Fin (d' m) → S) : (R m *ᵥ fun j => e (s j)) ∈ Img e p R n m :=
  ⟨s, fun i => by simp⟩

theorem dvd_mulVec' {κ ι : Type} [Fintype ι] {q : A} (D : Matrix κ ι A) (h : ∀ i j, q ∣ D i j)
    (v : ι → A) (i : κ) : q ∣ (D *ᵥ v) i := by
  simp only [mulVec, dotProduct]
  exact Finset.dvd_sum fun j _ => dvd_mul_of_dvd_left (h i j) _

theorem img_succ_sub (Y : ∀ n, Matrix (Fin (d' n)) (Fin (d' (n + 1))) S)
    (h1 : ∀ n i j, (p : A) ^ n ∣ (R n * (Y n).map e - R (n + 1)) i j) {n m : ℕ} (hnm : n ≤ m) :
    Img e p R n (m + 1) ⊆ Img e p R n m := by
  rintro w ⟨s, hs⟩
  refine ⟨Y m *ᵥ s, fun i => ?_⟩
  have he : (fun j => e ((Y m *ᵥ s) j)) = (Y m).map e *ᵥ fun j => e (s j) := by
    funext j; exact RingHom.map_mulVec e (Y m) s j
  rw [he, mulVec_mulVec]
  have : (w - (R m * (Y m).map e) *ᵥ fun j => e (s j)) i =
      (w - R (m + 1) *ᵥ fun j => e (s j)) i -
        ((R m * (Y m).map e - R (m + 1)) *ᵥ fun j => e (s j)) i := by
    simp only [sub_mulVec, Pi.sub_apply]; ring
  rw [this]
  exact dvd_sub (hs i) ((pow_dvd_pow _ hnm).trans (dvd_mulVec' _ (h1 m) _ i))

theorem img_anti (Y : ∀ n, Matrix (Fin (d' n)) (Fin (d' (n + 1))) S)
    (h1 : ∀ n i j, (p : A) ^ n ∣ (R n * (Y n).map e - R (n + 1)) i j) {n m m' : ℕ} (hnm : n ≤ m)
    (hm : m ≤ m') : Img e p R n m' ⊆ Img e p R n m := by
  induction m', hm using Nat.le_induction with
  | base => exact le_rfl
  | succ k hk ih => exact (img_succ_sub Y h1 (hnm.trans hk)).trans ih

theorem img_mod {k n m : ℕ} (hkn : k ≤ n) : Img e p R n m ⊆ Img e p R k m := by
  rintro w ⟨s, hs⟩; exact ⟨s, fun i => (pow_dvd_pow _ hkn).trans (hs i)⟩

theorem img_stable (u : S) (Y : ∀ n, Matrix (Fin (d' n)) (Fin (d' (n + 1))) S)
    (h1 : ∀ n i j, (p : A) ^ n ∣ (R n * (Y n).map e - R (n + 1)) i j)
    (n c : ℕ) [Finite (S ⧸ (Ideal.span {(p : S) ^ n} ⊔ Ideal.span {u ^ c}))]
    (hc : ∀ m, n ≤ m → ∀ s : Fin (d' n) → S, ∃ s' : Fin (d' m) → S, ∀ i,
      (p : A) ^ n ∣ ((R n *ᵥ fun j => e (u ^ c * s j)) - R m *ᵥ fun j => e (s' j)) i) :
    ∃ m₀, n ≤ m₀ ∧ ∀ m, m₀ ≤ m → Img e p R n m = Img e p R n m₀ := by
  let J : Ideal S := Ideal.span {(p : S) ^ n} ⊔ Ideal.span {u ^ c}
  let T : ℕ → Set (Fin (d' n) → S ⧸ J) := fun m =>
    {q | ∃ s : Fin (d' n) → S, (fun j => Ideal.Quotient.mk J (s j)) = q ∧
      (R n *ᵥ fun j => e (s j)) ∈ Img e p R n m}
  have key : ∀ m m', n ≤ m → n ≤ m' → T m ⊆ T m' → Img e p R n m ⊆ Img e p R n m' := by
    intro m m' hm hm' hT w hw
    obtain ⟨s, hs⟩ := img_anti Y h1 le_rfl hm hw
    have hRs : (R n *ᵥ fun j => e (s j)) ∈ Img e p R n m :=
      mem_of_dvd hw fun i => dvd_sub_comm.1 (hs i)
    obtain ⟨s', hq, hs'⟩ := hT ⟨s, rfl, hRs⟩
    have hj : ∀ j, ∃ a b : S, s j = s' j + (p : S) ^ n * a + u ^ c * b := by
      intro j
      have hqj : Ideal.Quotient.mk J (s' j) = Ideal.Quotient.mk J (s j) := congrFun hq j
      have hmem : s' j - s j ∈ J := Ideal.Quotient.eq.1 hqj
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hmem
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.1 hy
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.1 hz
      exact ⟨-a, -b, by linear_combination hyz⟩
    choose a b hab using hj
    obtain ⟨t, ht⟩ := hc m' hm' b
    have hsum : ((R n *ᵥ fun j => e (s' j)) + R n *ᵥ fun j => e (u ^ c * b j)) ∈ Img e p R n m' :=
      add_mem hs' (mem_of_dvd (image_mem n m' t) ht)
    have hRs' : (R n *ᵥ fun j => e (s j)) ∈ Img e p R n m' := by
      refine mem_of_dvd hsum fun i => ?_
      have hv : (fun j => e (s j)) = (fun j => e (s' j)) + (p : A) ^ n • (fun j => e (a j)) +
          fun j => e (u ^ c * b j) := by
        funext j; rw [hab j]; simp
      rw [hv, mulVec_add, mulVec_add, mulVec_smul]
      have : ((R n *ᵥ fun j => e (s' j)) + (p : A) ^ n • (R n *ᵥ fun j => e (a j)) +
          (R n *ᵥ fun j => e (u ^ c * b j)) - ((R n *ᵥ fun j => e (s' j)) +
            R n *ᵥ fun j => e (u ^ c * b j))) i = (p : A) ^ n * (R n *ᵥ fun j => e (a j)) i := by
        simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
      rw [this]; exact dvd_mul_right _ _
    exact mem_of_dvd hRs' hs
  have hanti : Antitone fun k => T (n + k) := by
    rintro k k' hkk q ⟨s, rfl, hs⟩
    exact ⟨s, rfl, img_anti Y h1 (Nat.le_add_right n k) (by omega) hs⟩
  obtain ⟨k₀, hk₀⟩ := WellFoundedLT.antitone_chain_condition hanti
  refine ⟨n + k₀, by omega, fun m hm => le_antisymm (img_anti Y h1 (by omega) hm) ?_⟩
  have hTe : T (n + k₀) = T m := by
    have := hk₀ (m - n) (by omega)
    rwa [Nat.add_sub_cancel' (by omega : n ≤ m)] at this
  exact key _ _ (by omega) (by omega) hTe.le

theorem ml (u : S) (Y : ∀ n, Matrix (Fin (d' n)) (Fin (d' (n + 1))) S)
    (h1 : ∀ n i j, (p : A) ^ n ∣ (R n * (Y n).map e - R (n + 1)) i j)
    (hfin : ∀ n c, Finite (S ⧸ (Ideal.span {(p : S) ^ n} ⊔ Ideal.span {u ^ c})))
    [IsAdicComplete (Ideal.span {(p : A)}) A]
    (h2 : ∀ n, ∃ c : ℕ, ∀ m, n ≤ m → ∀ s : Fin (d' n) → S, ∃ s' : Fin (d' m) → S, ∀ i,
      (p : A) ^ n ∣ ((R n *ᵥ fun j => e (u ^ c * s j)) - R m *ᵥ fun j => e (s' j)) i) :
    ∀ n, ∃ m, n ≤ m ∧ ∀ s : Fin (d' m) → S, ∃ v : Fin d → A,
      (∀ i, (p : A) ^ n ∣ (v - R m *ᵥ fun j => e (s j)) i) ∧
      ∀ k, ∃ s' : Fin (d' k) → S, ∀ i, (p : A) ^ k ∣ (v - R k *ᵥ fun j => e (s' j)) i := by
  have hst : ∀ n, ∃ m₀, n ≤ m₀ ∧ ∀ m, m₀ ≤ m → Img e p R n m = Img e p R n m₀ := fun n => by
    obtain ⟨c, hc⟩ := h2 n
    haveI := hfin n c
    exact img_stable u Y h1 n c hc
  choose m₀ hnm₀ hm₀ using hst
  have lift : ∀ n x, x ∈ Img e p R n (m₀ n) →
      ∃ y, y ∈ Img e p R (n + 1) (m₀ (n + 1)) ∧ ∀ i, (p : A) ^ n ∣ (y - x) i := by
    intro n x hx
    rw [← hm₀ n (max (m₀ n) (m₀ (n + 1))) (le_max_left _ _)] at hx
    obtain ⟨s, hs⟩ := hx
    refine ⟨_, ?_, fun i => dvd_sub_comm.1 (hs i)⟩
    rw [← hm₀ (n + 1) (max (m₀ n) (m₀ (n + 1))) (le_max_right _ _)]
    exact image_mem _ _ s
  choose! L hL hLd using lift
  intro n
  refine ⟨m₀ n, hnm₀ n, fun s => ?_⟩
  set x₀ := R (m₀ n) *ᵥ fun j => e (s j) with hx₀def
  have hx₀ : x₀ ∈ Img e p R n (m₀ n) := image_mem _ _ s
  let w : ℕ → Fin d → A := fun k => Nat.rec x₀ (fun k y => L (n + k) y) k
  have hw0 : w 0 = x₀ := rfl
  have hws : ∀ k, w (k + 1) = L (n + k) (w k) := fun _ => rfl
  have hmem : ∀ k, w k ∈ Img e p R (n + k) (m₀ (n + k)) := by
    intro k; induction k with
    | zero => exact hx₀
    | succ k ih => rw [hws]; exact hL _ _ ih
  have htel : ∀ k j i, (p : A) ^ (n + k) ∣ (w (k + j) - w k) i := by
    intro k j; induction j with
    | zero => intro i; simp
    | succ j ih =>
      intro i
      have : (w (k + (j + 1)) - w k) i = (w (k + j + 1) - w (k + j)) i + (w (k + j) - w k) i := by
        rw [← add_assoc]; simp only [Pi.sub_apply]; ring
      rw [this, hws]
      exact dvd_add ((pow_dvd_pow _ (by omega)).trans (hLd _ _ (hmem _) i)) (ih i)
  have hcau : ∀ i, ∃ v : A, ∀ k, (p : A) ^ k ∣ w k i - v := by
    intro i
    obtain ⟨v, hv⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete (Ideal.span {(p : A)}) A) (f := fun k => w k i) (by
      intro a b hab
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hab
      have h' : (p : A) ^ a ∣ w (a + j) i - w a i := (pow_dvd_pow _ (by omega)).trans (htel a j i)
      exact dvd_sub_comm.1 h')
    refine ⟨v, fun k => ?_⟩
    have := hv k
    rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton] at this
  choose V hV using hcau
  refine ⟨V, fun i => ?_, fun k => ?_⟩
  · have h1' := htel 0 n i
    rw [Nat.add_zero, Nat.zero_add, hw0] at h1'
    have : (V - x₀) i = (V i - w n i) + (w n - x₀) i := by simp only [Pi.sub_apply]; ring
    rw [this]; exact dvd_add (dvd_sub_comm.1 (hV i n)) h1'
  · have hk : w k ∈ Img e p R k k :=
      img_anti Y h1 le_rfl (le_trans (by omega) (hnm₀ (n + k))) (img_mod (by omega) (hmem k))
    exact mem_of_dvd hk fun i => dvd_sub_comm.1 (hV i k)

end GlobalTheory.ImageTower

theorem GlobalTheory.ImageTower.perfectRing_Cb' (l : ℕ) [Fact l.Prime] : PerfectRing (Cb l) l := by
  refine PerfectRing.ofSurjective _ _ fun x => ?_
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := OCb l) x
  obtain ⟨a, rfl⟩ := (bijective_frobenius (OCb l) l).2 a
  obtain ⟨b, rfl⟩ := (bijective_frobenius (OCb l) l).2 b
  exact ⟨algebraMap _ _ a / algebraMap _ _ b, by simp [frobenius_def]⟩

theorem GlobalTheory.BKLim.mittagLeffler_image : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (d' : ℕ → ℕ) (R : ∀ n, Matrix (Fin d) (Fin (d' n)) (WCb l)) (Y : ∀ n, Matrix (Fin (d' n)) (Fin (d' (n + 1))) (bk.S)), (∀ n i j, (l : WCb l) ^ n ∣ (R n * (Y n).map bk.evW - R (n + 1)) i j) → (∀ n, ∃ c : ℕ, ∀ m, n ≤ m → ∀ s : Fin (d' n) → bk.S, ∃ s' : Fin (d' m) → bk.S, ∀ i, (l : WCb l) ^ n ∣ ((R n *ᵥ fun j => bk.evW (X ^ c * s j)) - R m *ᵥ fun j => bk.evW (s' j)) i) → ∀ n, ∃ m, n ≤ m ∧ ∀ s : Fin (d' m) → bk.S, ∃ v : Fin d → WCb l, (∀ i, (l : WCb l) ^ n ∣ (v - R m *ᵥ fun j => bk.evW (s j)) i) ∧ ∀ k, ∃ s' : Fin (d' k) → bk.S, ∀ i, (l : WCb l) ^ k ∣ (v - R k *ᵥ fun j => bk.evW (s' j)) i := by
  intro l _ K bk d d' R Y h1 h2
  haveI : PerfectRing (Cb l) l := GlobalTheory.ImageTower.perfectRing_Cb' l
  haveI : IsAdicComplete (Ideal.span {(l : WCb l)}) (WCb l) := WittVector.isAdicCompleteIdealSpanP
  exact GlobalTheory.ImageTower.ml (e := bk.evW) (p := l) (R := R) X Y h1 (fun n c => GlobalTheory.T.finite_breuilKisin_quotient_prime_pow_X_pow l K bk n c) h2
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.breuilKisin_OE_mod_prime_laurent_field : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), (∀ y : Cb l, y ∈ bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l)) ↔ ∃ (m : ℕ) (s : bk.S), algebraMap (OCb l) (Cb l) bk.flat ^ m * y = algebraMap (OCb l) (Cb l) ((bk.ev s).coeff 0)) ∧ (∀ s : bk.S, bk.evW s ∈ bk.OE) ∧ IsUnit (bk.evW X) ∧ (∀ w : WCb l, bk.evW X * w ∈ bk.OE → w ∈ bk.OE) ∧ ∀ y ∈ bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l)), y⁻¹ ∈ bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l)) := by
  first | exact @GlobalTheory.BSP.oe_mod_l | exact GlobalTheory.BSP.oe_mod_l | (intros; apply GlobalTheory.BSP.oe_mod_l <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim.AinfRetraction

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), ∃ c : Ainf l →+ bk.S, (∀ (s : bk.S) (a : Ainf l), c (bk.ev s * a) = s * c a) ∧ c 1 = 1 := by
  intro l _ K bk
  obtain ⟨ι, ⟨TB⟩⟩ := GlobalTheory.BSP.AinfTopBasis.main l K bk
  refine ⟨TB.c TB.i₀, TB.c_mul TB.i₀, ?_⟩
  rw [← TB.b_i₀]
  exact TB.c_self TB.i₀

end GlobalTheory.BKLim.AinfRetraction
end
