module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle572
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsSumMonomialAdd
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle557
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem polyDelta_supported_linear_mod (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (i : ℕ) :
    ∀ s ∈ MvPolynomial.supported A (Set.Iic i), (polyDelta D).δ s ∈ MvPolynomial.supported A (Set.Iic (i + 1)) ∧
      ∃ a ∈ MvPolynomial.supported A (Set.Iic i), ∃ b ∈ MvPolynomial.supported A (Set.Iic i),
        (polyDelta D).δ s - (a * MvPolynomial.X (i + 1) + b) ∈ Ideal.span {(l : MvPolynomial ℕ A)} := by
  intro s hs
  have hX : ∀ (U : Set ℕ) (j : ℕ), j ∈ U → (MvPolynomial.X j : MvPolynomial ℕ A) ∈ MvPolynomial.supported A U :=
    fun U j hj => by
      rw [MvPolynomial.supported_eq_adjoin_X]; exact Algebra.subset_adjoin ⟨j, hj, rfl⟩
  have hC : ∀ (U : Subalgebra A (MvPolynomial ℕ A)) (a : A), MvPolynomial.C a ∈ U :=
    fun U a => U.algebraMap_mem a
  set S := MvPolynomial.supported A (Set.Iic i) with hS
  set T := MvPolynomial.supported A (Set.Iic (i + 1)) with hT
  have hST : S ≤ T := MvPolynomial.supported_mono (Set.Iic_subset_Iic.2 (Nat.le_succ i))
  have hcc : ∀ x y, x ∈ S → y ∈ S → cc l x y ∈ S := by
    intro x y hx hy
    unfold cc
    refine Subalgebra.sum_mem _ fun k _ => ?_
    refine Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ _) (Subalgebra.pow_mem _ hx _))
      (Subalgebra.pow_mem _ hy _)
  have hS' : S = Algebra.adjoin A (MvPolynomial.X '' Set.Iic i) := MvPolynomial.supported_eq_adjoin_X _
  rw [hS'] at hs
  induction hs using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := hx
    have hj' : j ≤ i := Set.mem_Iic.1 hj
    rw [polyDelta_X]
    refine ⟨hX _ _ (Set.mem_Iic.2 (by omega)), ?_⟩
    rcases Nat.lt_or_ge j i with h | h
    · refine ⟨0, Subalgebra.zero_mem _, MvPolynomial.X (j + 1), hX _ _ (Set.mem_Iic.2 (by omega)), ?_⟩
      simp
    · have : j = i := le_antisymm hj' h
      subst this
      refine ⟨1, Subalgebra.one_mem _, 0, Subalgebra.zero_mem _, ?_⟩
      simp
  | algebraMap a =>
    rw [MvPolynomial.algebraMap_eq, polyDelta_C]
    refine ⟨hC _ _, 0, Subalgebra.zero_mem _, MvPolynomial.C (D.δ a), hC _ _, ?_⟩
    simp
  | add x y hx hy ihx ihy =>
    rw [← hS'] at hx hy
    obtain ⟨hx1, a1, ha1, b1, hb1, hx2⟩ := ihx
    obtain ⟨hy1, a2, ha2, b2, hb2, hy2⟩ := ihy
    have hd : (polyDelta D).δ (x + y) = (polyDelta D).δ x + (polyDelta D).δ y - cc l x y := (polyDelta D).δ_add x y
    rw [hd]
    refine ⟨T.sub_mem (T.add_mem hx1 hy1) (hST (hcc x y hx hy)), a1 + a2, S.add_mem ha1 ha2,
      b1 + b2 - cc l x y, S.sub_mem (S.add_mem hb1 hb2) (hcc x y hx hy), ?_⟩
    have := Ideal.add_mem _ hx2 hy2
    convert this using 1
    ring
  | mul x y hx hy ihx ihy =>
    rw [← hS'] at hx hy
    obtain ⟨hx1, a1, ha1, b1, hb1, hx2⟩ := ihx
    obtain ⟨hy1, a2, ha2, b2, hb2, hy2⟩ := ihy
    have hd : (polyDelta D).δ (x * y) = x ^ l * (polyDelta D).δ y + y ^ l * (polyDelta D).δ x +
        (l : MvPolynomial ℕ A) * (polyDelta D).δ x * (polyDelta D).δ y := (polyDelta D).δ_mul x y
    rw [hd]
    refine ⟨T.add_mem (T.add_mem (T.mul_mem (T.pow_mem (hST hx) _) hy1) (T.mul_mem (T.pow_mem (hST hy) _) hx1))
        (T.mul_mem (T.mul_mem (T.natCast_mem _) hx1) hy1),
      x ^ l * a2 + y ^ l * a1, S.add_mem (S.mul_mem (S.pow_mem hx _) ha2) (S.mul_mem (S.pow_mem hy _) ha1),
      x ^ l * b2 + y ^ l * b1, S.add_mem (S.mul_mem (S.pow_mem hx _) hb2) (S.mul_mem (S.pow_mem hy _) hb1), ?_⟩
    have h3 : (l : MvPolynomial ℕ A) * (polyDelta D).δ x * (polyDelta D).δ y ∈
        Ideal.span {(l : MvPolynomial ℕ A)} :=
      Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
    have := Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ (x ^ l) hy2) (Ideal.mul_mem_left _ (y ^ l) hx2)) h3
    convert this using 1
    ring

end GlobalTheory.BSP
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem GlobalTheory.BSP.delta_quot_span : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (s : Set A), (∀ x ∈ s, D.δ x ∈ Ideal.span s) → ∃ D' : Delta l (A ⧸ Ideal.span s), IsδMap D D' (Ideal.Quotient.mk (Ideal.span s)) := by
  intro l _ A _ D s hs
  let N := Ideal.span s
  let g : A →+* W2 l (A ⧸ N) := (W2.map (Ideal.Quotient.mk N)).comp (deltaSectionToWittLengthTwo D)
  have hg : ∀ a ∈ N, g a = 0 := by
    intro a ha
    have hle : N ≤ RingHom.ker g := by
      refine Ideal.span_le.2 fun x hx => ?_
      rw [SetLike.mem_coe, RingHom.mem_ker]
      refine W2.ext ?_ ?_
      · exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span hx)
      · exact Ideal.Quotient.eq_zero_iff_mem.2 (hs x hx)
    exact hle ha
  let sec : A ⧸ N →+* W2 l (A ⧸ N) := Ideal.Quotient.lift N g hg
  have hsec : ∀ a, (sec a).fst = a := by
    intro a
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    rfl
  exact ⟨deltaStructureOfWittLengthTwoSection sec hsec, fun a => rfl⟩
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem pow_mul_eq_zero_of_invertible {A : Type} [CommRing A] (I : Ideal A) (hI : Module.Invertible A ↥I)
    (f c : A) (h : ∀ x ∈ I, ∃ k : ℕ, f ^ k * (c * x) = 0) : ∃ K : ℕ, f ^ K * c = 0 := by
  classical
  have hfg : I.FG := Module.Finite.iff_fg.1 inferInstance
  obtain ⟨S, hS⟩ := hfg
  let k : A → ℕ := fun x => if hx : x ∈ I then (h x hx).choose else 0
  have hk : ∀ x ∈ I, f ^ k x * (c * x) = 0 := fun x hx => by
    simp only [k, dif_pos hx]; exact (h x hx).choose_spec
  refine ⟨S.sup k, ?_⟩
  have hle : I ≤ LinearMap.ker (LinearMap.mulLeft A (f ^ S.sup k * c)) := by
    rw [← hS, Submodule.span_le]
    intro x hx
    have hxI : x ∈ I := hS ▸ Submodule.subset_span hx
    have hkx : k x ≤ S.sup k := Finset.le_sup (f := k) hx
    rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.mulLeft_apply]
    obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hkx
    rw [hj, pow_add]
    linear_combination (f ^ j) * hk x hxI
  apply eq_of_smul_eq_smul (α := ↥I)
  intro y
  have := hle y.2
  rw [LinearMap.mem_ker, LinearMap.mulLeft_apply] at this
  ext
  simp [this]

theorem locAway_span_nzd_bdd (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B : Obj l R) (f d : B.A)
    (hG : GenAway B f d) (M : Submonoid B.A) (hf : f ∈ M) :
    B.I.map (algebraMap B.A (Localization M)) = Ideal.span {algebraMap B.A (Localization M) d} ∧
    algebraMap B.A (Localization M) d ∈ nonZeroDivisors (Localization M) ∧
    ∃ N : ℕ, ∀ (x : Localization M) (m : ℕ), (l : Localization M) ^ m * x ∈
      Ideal.span {algebraMap B.A (Localization M) d} →
      (l : Localization M) ^ N * x ∈ Ideal.span {algebraMap B.A (Localization M) d} := by
  set φ := algebraMap B.A (Localization M) with hφ
  have hu : IsUnit (φ f) := IsLocalization.map_units (Localization M) (⟨f, hf⟩ : M)
  have h1 : B.I.map φ = Ideal.span {φ d} := by
    refine le_antisymm ?_ ?_
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      obtain ⟨k, hk⟩ := hG.2 x hx
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hk
      rw [Ideal.mem_comap, ← Ideal.unit_mul_mem_iff_mem _ (hu.pow k), ← map_pow, ← map_mul, ← hc, map_mul]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.mem_map_of_mem _ hG.1
  refine ⟨h1, ?_, ?_⟩
  · rw [mem_nonZeroDivisors_iff_right]
    intro x hx
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective M x
    rw [mul_comm, hφ, IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_zero_iff] at hx
    obtain ⟨t, ht⟩ := hx
    obtain ⟨K, hK⟩ := pow_mul_eq_zero_of_invertible B.I B.inv f ((t : B.A) * a) (fun x hx => by
      obtain ⟨k, hk⟩ := hG.2 x hx
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hk
      exact ⟨k, by linear_combination c * ht - (t : B.A) * a * hc⟩)
    rw [IsLocalization.mk'_eq_zero_iff]
    exact ⟨⟨f ^ K * t, M.mul_mem (M.pow_mem hf K) t.2⟩, by simp only; linear_combination hK⟩
  · obtain ⟨n, hn⟩ := B.bdd
    refine ⟨n, fun x m hx => ?_⟩
    rw [← h1] at hx ⊢
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective M x
    have e : ∀ j : ℕ, (l : Localization M) ^ j * IsLocalization.mk' (Localization M) a s =
        IsLocalization.mk' (Localization M) ((l : B.A) ^ j * a) s := fun j => by
      rw [← IsLocalization.mul_mk'_eq_mk'_of_mul, map_pow, map_natCast]
    rw [e, IsLocalization.mk'_mem_map_algebraMap_iff] at hx ⊢
    obtain ⟨s', hs', hI⟩ := hx
    refine ⟨s', hs', ?_⟩
    have h0 : (l : B.A ⧸ B.I) ^ m * Ideal.Quotient.mk B.I (s' * a) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk B.I), ← map_pow, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      convert hI using 1; ring
    have h2 := hn _ ⟨m, h0⟩
    rw [← map_natCast (Ideal.Quotient.mk B.I), ← map_pow, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at h2
    convert h2 using 1; ring

end GlobalTheory.BSP
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem ringHom_eq_of_isCompl (L : Type) [CommRing L] (Q : Type) [CommRing Q] (C : Type) [CommRing C]
    (i : L →+* Q) (J : Ideal L) (JC : Ideal C) (hc : IsCompl i J) (hH : IsHausdorff JC C)
    (h h' : Q →+* C) (hJ : J.map (h.comp i) ≤ JC) (he : h.comp i = h'.comp i) : h = h' := by
  have mem : ∀ (g : Q →+* C), J.map (g.comp i) ≤ JC → ∀ (n : ℕ) (y : Q), y ∈ (J ^ n).map i → g y ∈ JC ^ n := by
    intro g hg n y hy
    have h1 : g y ∈ ((J ^ n).map i).map g := Ideal.mem_map_of_mem g hy
    rw [Ideal.map_map, Ideal.map_pow] at h1
    exact Ideal.pow_right_mono hg n h1
  have hJ' : J.map (h'.comp i) ≤ JC := by rwa [← he]
  ext x
  rw [← sub_eq_zero]
  apply hH.haus
  intro n
  obtain ⟨a, ha⟩ := hc.surj x n
  have e1 : h x - h' x = h (x - i a) - h' (x - i a) := by
    have : h (i a) = h' (i a) := RingHom.congr_fun he a
    simp only [map_sub, this]; ring
  rw [SModEq.zero, e1, smul_eq_mul, Ideal.mul_top]
  exact Ideal.sub_mem _ (mem h hJ n _ ha) (mem h' hJ' n _ ha)

end GlobalTheory.BSP
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.ComplLD

theorem smodEq_iff {Q : Type} [CommRing Q] (I : Ideal Q) (n : ℕ) (x y : Q) :
    x ≡ y [SMOD (I ^ n • ⊤ : Submodule Q Q)] ↔ x - y ∈ I ^ n := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]

theorem eq_zero_of_mem {Q : Type} [CommRing Q] (I : Ideal Q) [IsHausdorff I Q] (x : Q)
    (h : ∀ n, x ∈ I ^ n) : x = 0 :=
  IsHausdorff.haus' x fun n => (smodEq_iff I n x 0).2 (by simpa using h n)

theorem exists_lim {Q : Type} [CommRing Q] (I : Ideal Q) [IsPrecomplete I Q] (f : ℕ → Q)
    (h : ∀ m n, m ≤ n → f n - f m ∈ I ^ m) : ∃ z, ∀ n, f n - z ∈ I ^ n := by
  obtain ⟨z, hz⟩ := IsPrecomplete.prec' (I := I) f fun {m n} hmn =>
    (smodEq_iff I m _ _).2 (by rw [show f m - f n = -(f n - f m) by ring]; exact neg_mem (h m n hmn))
  exact ⟨z, fun n => (smodEq_iff I n _ _).1 (hz n)⟩

theorem regular_and_torsion_bounded : ∀ (l : ℕ) [Fact l.Prime] (L : Type) [CommRing L] (Q : Type) [CommRing Q] (i : L →+* Q) (d : L) (N : ℕ), d ∈ nonZeroDivisors L → (∀ (x : L) (m : ℕ), (l : L) ^ m * x ∈ Ideal.span {d} → (l : L) ^ N * x ∈ Ideal.span {d}) → IsCompl i (Ideal.span {(l : L)} ⊔ Ideal.span {d}) → i d ∈ nonZeroDivisors Q ∧ ∀ (x : Q) (m : ℕ), (l : Q) ^ m * x ∈ Ideal.span {i d} → (l : Q) ^ N * x ∈ Ideal.span {i d} := by
  intro l _ L _ Q _ i d N hd hbd hc
  set J : Ideal L := Ideal.span {(l : L)} ⊔ Ideal.span {d} with hJ
  set I : Ideal Q := J.map i with hI
  haveI : IsAdicComplete I Q := hc.complete
  have hpow : ∀ n, (J ^ n).map i = I ^ n := fun n => Ideal.map_pow _ _ _
  have surj : ∀ (x : Q) n, ∃ a, x - i a ∈ I ^ n := fun x n => by
    obtain ⟨a, ha⟩ := hc.surj x n; exact ⟨a, by rwa [← hpow]⟩
  have ker : ∀ a n, i a ∈ I ^ n → a ∈ J ^ n := fun a n h => hc.ker a n (by rwa [hpow])
  have strict : ∀ n z, i d * z ∈ I ^ (2 * (n + N + 1)) → z ∈ I ^ n := by
    intro n z hz
    obtain ⟨a, ha⟩ := surj z (2 * (n + N + 1))
    have h1 : i (d * a) ∈ I ^ (2 * (n + N + 1)) := by
      have e : i (d * a) = i d * z - i d * (z - i a) := by rw [map_mul]; ring
      rw [e]; exact sub_mem hz (Ideal.mul_mem_left _ _ ha)
    have h2 := GlobalTheory.T.mem_pow_of_mul_mem_pow_bounded_torsion l L d N hd hbd n a (ker _ _ h1)
    have h3 : i a ∈ I ^ n := by rw [← hpow]; exact Ideal.mem_map_of_mem i h2
    have h4 : z - i a ∈ I ^ n := Ideal.pow_le_pow_right (by omega) ha
    simpa using add_mem h4 h3
  have reg : i d ∈ nonZeroDivisors Q := by
    rw [mem_nonZeroDivisors_iff]
    exact ⟨fun z hz => eq_zero_of_mem I z fun n => strict n z (by rw [hz]; exact zero_mem _),
      fun z hz => eq_zero_of_mem I z fun n => strict n z (by rw [mul_comm (i d) z, hz]; exact zero_mem _)⟩
  have closed : ∀ x, (∀ n, ∃ z, x - i d * z ∈ I ^ n) → x ∈ Ideal.span {i d} := by
    intro x hx
    choose z hz using fun n => hx (2 * (n + N + 1))
    obtain ⟨w, hw⟩ := exists_lim I z fun m n hmn => strict m _ (by
      have e : i d * (z n - z m) = (x - i d * z m) - (x - i d * z n) := by ring
      rw [e]; exact sub_mem (hz m) (Ideal.pow_le_pow_right (by omega) (hz n)))
    have h0 : x - i d * w = 0 := eq_zero_of_mem I _ fun n => by
      have e : x - i d * w = (x - i d * z n) + i d * (z n - w) := by ring
      rw [e]; exact add_mem (Ideal.pow_le_pow_right (by omega) (hz n)) (Ideal.mul_mem_left _ _ (hw n))
    exact Ideal.mem_span_singleton'.2 ⟨w, by rw [mul_comm]; exact (sub_eq_zero.1 h0).symm⟩
  refine ⟨reg, fun x m hx => closed _ fun n => ?_⟩
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hx
  obtain ⟨a, ha⟩ := surj x (m + n + 1)
  obtain ⟨b, hb⟩ := surj y (m + n + 1)
  have h1 : i ((l : L) ^ m * a - d * b) ∈ I ^ (m + n + 1) := by
    have e : i ((l : L) ^ m * a - d * b) = -((l : Q) ^ m * (x - i a)) + i d * (y - i b) := by
      rw [map_sub, map_mul, map_mul, map_pow, map_natCast]; linear_combination (-1 : Q) * hy
    rw [e]; exact add_mem (neg_mem (Ideal.mul_mem_left _ _ ha)) (Ideal.mul_mem_left _ _ hb)
  have h2 : (l : L) ^ m * a - d * b ∈ Ideal.span {(l : L) ^ (m + n)} ⊔ Ideal.span {d} := by
    have hle : J ^ (m + n + 1) ≤ Ideal.span {(l : L)} ^ (m + n) ⊔ Ideal.span {d} ^ 1 :=
      Ideal.sup_pow_add_le_pow_sup_pow
    simpa [Ideal.span_singleton_pow] using hle (ker _ _ h1)
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 h2
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hu
  obtain ⟨e, rfl⟩ := Ideal.mem_span_singleton'.1 hv
  have h3 : (l : L) ^ m * (a - (l : L) ^ n * c) ∈ Ideal.span {d} :=
    Ideal.mem_span_singleton'.2 ⟨b + e, by linear_combination huv⟩
  obtain ⟨f, hf⟩ := Ideal.mem_span_singleton'.1 (hbd _ _ h3)
  refine ⟨i f, ?_⟩
  have hf' := congrArg i hf
  simp only [map_mul, map_pow, map_natCast, map_sub] at hf'
  have e : (l : Q) ^ N * x - i d * i f = (l : Q) ^ N * (x - i a) + i ((l : L) ^ (N + n) * c) := by
    rw [map_mul, map_pow, map_natCast]; linear_combination (-1 : Q) * hf'
  rw [e]
  refine add_mem (Ideal.pow_le_pow_right (by omega) (Ideal.mul_mem_left _ _ ha)) ?_
  rw [← hpow]
  refine Ideal.mem_map_of_mem i (Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right (by omega : n ≤ N + n)
    (Ideal.pow_mem_pow (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)) (N + n))))

end GlobalTheory.BSP.ComplLD
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal Matrix

namespace GlobalTheory.BKReal

theorem coeff_iterate_derivative_descFactorial (K : Type) [NormedField K] (p : ℕ) (f : K⟦X⟧) (m : ℕ) :
    coeff m (d⁄dX^[p] f) = ((m + p).descFactorial p : K) * coeff (m + p) f := by
  rw [PowerSeries.coeff_iterate_derivative, Nat.add_descFactorial_eq_ascFactorial]

theorem descN_eq_X_pow_mul_iterate_derivative :
    ∀ (K : Type) [NormedField K] (p : ℕ) (f : K⟦X⟧), descN K p f = X ^ p * d⁄dX^[p] f := by
  intro K _ p f
  ext n
  rw [coeff_descN, coeff_X_pow_mul']
  split_ifs with h
  · rw [coeff_iterate_derivative_descFactorial, Nat.sub_add_cancel h]
  · rw [Nat.descFactorial_of_lt (by omega), Nat.cast_zero, zero_mul]

end GlobalTheory.BKReal
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries GlobalTheory.BK GlobalTheory.BKReal
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKReal

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]

theorem N_sub_smul_mem_A {c : K} (hc : ‖c‖ ≤ 1) {g : K⟦X⟧} (hg : g ∈ A O K) :
    N K g - c • g ∈ A O K := fun n => by
  rw [map_sub, coeff_N, coeff_smul, smul_eq_mul, ← sub_mul, norm_mul]
  rw [sub_eq_add_neg]
  refine mul_le_one₀ ?_ (norm_nonneg _) (hg n)
  refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
  rw [norm_neg]
  exact
    max_le (IsUltrametricDist.norm_natCast_le_one K n) hc

theorem exists_N_sub_smul_E_pow_mul (l e : ℕ) {c : K} (hc : ‖c‖ ≤ 1) {g : K⟦X⟧} (hg : g ∈ A O K)
    (j : ℕ) : ∃ g' ∈ A O K,
      N K (E K l e ^ j * g) - c • (E K l e ^ j * g) = E K l e ^ (j - 1) * g' := by
  cases j with
  | zero => exact ⟨_, N_sub_smul_mem_A hc hg, by simp⟩
  | succ j =>
    refine ⟨((j + 1 : ℕ) : K⟦X⟧) * ((e : K⟦X⟧) * X ^ e) * g + E K l e * (N K g - c • g),
      (A O K).add_mem ((A O K).mul_mem ((A O K).mul_mem (natCast_mem _ _)
        ((A O K).mul_mem (natCast_mem _ _) ((A O K).pow_mem HasU.X_mem e))) hg)
        ((A O K).mul_mem (E_mem l e _) (N_sub_smul_mem_A hc hg)), ?_⟩
    rw [Derivation.leibniz, Derivation.leibniz_pow, N_E, Nat.add_sub_cancel]
    simp only [smul_eq_mul, nsmul_eq_mul, smul_eq_C_mul]
    push_cast
    ring

theorem exists_aeval_comp_E_pow_mul (l e i : ℕ) : ∀ (m : ℕ) {g : K⟦X⟧}, g ∈ A O K →
    ∃ g' ∈ A O K, Polynomial.aeval (N K).toLinearMap
      ((descPochhammer K i).comp (Polynomial.X - 1)) (E K l e ^ m * g) = E K l e ^ (m - i) * g' := by
  induction i with
  | zero => intro m g hg; exact ⟨g, hg, by simp⟩
  | succ i ih =>
    intro m g hg
    obtain ⟨g₁, hg₁, h₁⟩ := exists_N_sub_smul_E_pow_mul (O := O) l e (c := ((i + 1 : ℕ) : K))
      (IsUltrametricDist.norm_natCast_le_one K _) hg m
    obtain ⟨g₂, hg₂, h₂⟩ := ih (m - 1) hg₁
    refine ⟨g₂, hg₂, ?_⟩
    have h₃ : ∀ x : K⟦X⟧, Polynomial.aeval (N K).toLinearMap
        ((Polynomial.X - (i : Polynomial K)).comp (Polynomial.X - 1)) x = N K x - ((i + 1 : ℕ) : K) • x := by
      intro x
      rw [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.natCast_comp, map_sub, map_sub,
        Polynomial.aeval_X, map_natCast, map_one, LinearMap.sub_apply, LinearMap.sub_apply,
        Module.End.natCast_apply, Module.End.one_apply, Derivation.coeFn_coe]
      push_cast
      rw [add_smul, one_smul, Nat.cast_smul_eq_nsmul]
      abel
    rw [descPochhammer_succ_right, Polynomial.mul_comp, map_mul (Polynomial.aeval _), Module.End.mul_apply, h₃, h₁, h₂,
      Nat.sub_sub, add_comm 1 i]

theorem exists_l_pow_mul_descN_eq_E_pow_mul : ∀ (l e : ℕ) (O K : Type) [CommRing O] [NormedField K]
    [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (f h : K⟦X⟧) (k m : ℕ), h ∈ A O K →
    (l : K⟦X⟧) ^ k * N K f = E K l e ^ m * h → ∀ i : ℕ, 1 ≤ i →
    ∃ h' ∈ A O K, (l : K⟦X⟧) ^ k * descN K i f = E K l e ^ (m + 1 - i) * h' := by
  intro l e O K _ _ _ _ _ f h k m hh hf i hi
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le' hi
  obtain ⟨h', hh', h₁⟩ := exists_aeval_comp_E_pow_mul (O := O) l e i m hh
  refine ⟨h', hh', ?_⟩
  have hl : (l : K⟦X⟧) ^ k = C ((l : K) ^ k) := by simp
  rw [Nat.add_sub_add_right, ← h₁, ← hf, descN, descPochhammer_succ_left, mul_comm (Polynomial.X : Polynomial K), map_mul (Polynomial.aeval _),
    Polynomial.aeval_X, Module.End.mul_apply, hl, ← smul_eq_C_mul, ← smul_eq_C_mul, map_smul]
  rfl

end GlobalTheory.BKReal
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem delta_add_sub_mem_pow : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A)
    (J : Ideal A), (l : A) ∈ J → ∀ (n : ℕ) (x : A), ∀ y ∈ J ^ (n + 1), D.δ (x + y) - D.δ x ∈ J ^ n := by
  intro l _ A _ D J hl n x y hy
  have hy' : y ∈ J ^ n := Ideal.pow_le_pow_right (Nat.le_succ n) hy
  have hδ : D.δ y ∈ J ^ n := GlobalTheory.T.delta_mem_ideal_pow_of_mem_pow_succ l A D J hl n y hy
  rw [D.δ_add x y]
  have e : D.δ x + D.δ y - ∑ k ∈ Finset.Ioo 0 l, ((l.choose k / l : ℕ) : A) * x ^ k * y ^ (l - k) - D.δ x
      = D.δ y - ∑ k ∈ Finset.Ioo 0 l, ((l.choose k / l : ℕ) : A) * x ^ k * y ^ (l - k) := by ring
  rw [e]
  refine Ideal.sub_mem _ hδ (Ideal.sum_mem _ fun k hk => ?_)
  have hk' : 0 < l - k := Nat.sub_pos_of_lt (Finset.mem_Ioo.1 hk).2
  have : y ^ (l - k) ∈ J ^ n := by
    obtain ⟨m, hm⟩ : ∃ m, l - k = m + 1 := ⟨l - k - 1, by omega⟩
    rw [hm, pow_succ]
    exact Ideal.mul_mem_left _ _ hy'
  exact Ideal.mul_mem_left _ _ this

end GlobalTheory.BSP
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.galois_action_extends_to_ainf_disc_rings : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), (∀ g : GQ l, bk.ev X ∣ Per.σA g (bk.ev X)) ∧ ∀ (ρ : ℝ≥0), 0 < ρ → ∀ g : GQ l, ∃ G : bk.DA ρ →+* bk.DA ρ, IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA g) G := by
  first | exact @GlobalTheory.BSP.galois_discMap | exact GlobalTheory.BSP.galois_discMap | (intros; apply GlobalTheory.BSP.galois_discMap <;> assumption)
end
