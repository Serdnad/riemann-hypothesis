module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle025
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimOfIsUnitDet
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle027
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMemFractionalIdealPrimitiveLocalGeneratorA
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Cint

@[expose] public section

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.Frames

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem stab_span_of_integral {L : LocE F E} {r k : ℕ} (S : Frames L r k) (h : S.GLV)
    (g : Fin (r + 1) → S.V) (s si : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hs : ∀ i j, s i j ∈ L.O) (hsi : ∀ i j, si i j ∈ L.O) (hm : s * si = 1)
    (hg : ∀ j, h (g j) = ∑ i, s i j • g i) :
    h ∈ MulAction.stabilizer S.GLV (Submodule.span L.O (Set.range g)) := by
  rw [MulAction.mem_stabilizer_iff]
  set N := Submodule.span L.O (Set.range g) with hN
  have mem : ∀ (c : Matrix (Fin (r + 1)) (Fin (r + 1)) E), (∀ i j, c i j ∈ L.O) →
      ∀ j, ∑ i, c i j • g i ∈ N := by
    intro c hc j
    refine Submodule.sum_mem _ fun i _ => ?_
    have : c i j • g i = (⟨c i j, hc i j⟩ : L.O) • g i := rfl
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  apply le_antisymm
  · rw [Submodule.pointwise_smul_def, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    show h (g j) ∈ N
    rw [hg j]
    exact mem s hs j
  · rw [hN, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have key : g j = h (∑ i, si i j • g i) := by

      rw [map_sum]
      simp_rw [map_smul, hg, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_smul]
      have : ∀ x, ∑ i, si i j * s x i = (s * si) x j := fun x => by
        rw [Matrix.mul_apply]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
      simp_rw [this, hm, Matrix.one_apply, ite_smul, one_smul, zero_smul]
      simp
    rw [key]
    exact Submodule.smul_mem_pointwise_smul _ h _ (mem si hsi j)

theorem mem_K0_of_integral : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) (r k : ℕ) (S : Frames L r k) (h : S.GLV) (s si s' si' : Matrix (Fin (r + 1)) (Fin (r + 1)) E), h ∈ S.St → (∀ i j, s i j ∈ L.O) → (∀ i j, si i j ∈ L.O) → s * si = 1 → (∀ i j, s' i j ∈ L.O) → (∀ i j, si' i j ∈ L.O) → s' * si' = 1 → (∀ j, h (S.f j) = ∑ i, s i j • S.f i) → (∀ j, h (S.f' j) = ∑ i, s' i j • S.f' i) → h ∈ S.K0 := by
  intro F _ _ _ E _ _ _ L r k S h s si s' si' hSt hs hsi hm hs' hsi' hm' hg hg'
  unfold Frames.K0
  exact ⟨⟨hSt, S.stab_span_of_integral h S.f s si hs hsi hm hg⟩,
    S.stab_span_of_integral h S.f' s' si' hs' hsi' hm' hg'⟩

end GlobalTheory.HL.Frames
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.EichlerUnip
open GlobalTheory.HL.Eichler

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem spanTo_mono (g : Fin (r + 1) → S.V) {a b : ℕ} (h : a ≤ b) : S.spanTo g a ≤ S.spanTo g b :=
  Submodule.span_mono (Set.image_mono fun _ hi => lt_of_lt_of_le hi h)

theorem mem_spanTo (g : Fin (r + 1) → S.V) {a : ℕ} (i : Fin (r + 1)) (h : (i : ℕ) < a) :
    g i ∈ S.spanTo g a := Submodule.subset_span ⟨i, h, rfl⟩

theorem hf_spanTo (g : Fin (r + 1) → S.V) {a : ℕ} (y : S.V)
    (h : ∀ i : Fin (r + 1), (i : ℕ) < a → hf L S.Hm (g i) y = 0) {x : S.V} (hx : x ∈ S.spanTo g a) :
    hf L S.Hm x y = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨i, hi, rfl⟩ := hx; exact h i hi
  | zero => simp [hf]
  | add a b _ _ ha hb => rw [hf_add_l, ha, hb, add_zero]
  | smul c a _ ha => rw [hf_smul_l, ha, mul_zero]

theorem hf_symm0 {x y : S.V} (h : hf L S.Hm x y = 0) : hf L S.Hm y x = 0 := by
  rw [← hf_cj L S.herm.1, h, map_zero]

theorem mem_unipOn {N : ℕ} {A B : Submodule E (Fin N → E)} (hBA : B ≤ A)
    (n : (Fin N → E) ≃ₗ[E] (Fin N → E)) (h1 : ∀ v ∈ A, n v - v ∈ B) (h2 : ∀ v ∈ A, n⁻¹ v - v ∈ B) :
    n ∈ unipOn A B := by
  refine ⟨fun v => ⟨fun hv => ?_, fun hv => ?_⟩, h1⟩
  · have h3 := A.add_mem (hBA (h2 _ hv)) hv
    have h4 : n⁻¹ (n v) = v := n.symm_apply_apply v
    rw [h4] at h3
    simpa using h3
  · simpa using A.add_mem (hBA (h1 _ hv)) hv

end

theorem eichler_mem_unip : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (g : Fin (r + 1) → S.V) (gs : Fin r → S.V), (g = S.f ∧ gs = S.es) ∨ (g = S.f' ∧ gs = S.es') → ∀ (j : Fin r) (x u : S.V) (s : E), x ∈ S.spanTo g (j + 1) → u ∈ perp L S.Hm (S.spanTo g (j + 1)) → s + L.cj s = S.h u u → ∃ n ∈ S.Nof g, (∀ v, n v = eich L S.Hm x u s v) ∧ (∀ v, n⁻¹ v = eich L S.Hm x (-u) (L.cj s) v) ∧ (∀ v ∈ S.spanTo g (j + 1), n v = v) ∧ ∀ m ∈ S.Nof g, S.psiOf g gs n = L.psi0 (algebraMap F E S.th⁻¹ * (S.h x (gs j) * S.h (m (g j.succ)) u)) := by
  intro F _ _ _ _ _ E _ _ _ L r k S g gs hg j x u s hx hu hs
  have hgram : ∀ a b : Fin (r + 1), (b : ℕ) < r → hf L S.Hm (g a) (g b) = 0 := by
    intro a b hb
    have hb' : b ≠ Fin.last r := fun h => by simp [h] at hb
    rcases hg with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · rw [S.gram]; simp [hb']
    · rw [S.gram']; simp [hb']
  have hdual : ∀ a i, hf L S.Hm (g a) (gs i) = if a = i.castSucc then 1 else 0 := by
    intro a i
    rcases hg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact S.dual a i
    · exact S.dual' a i
  have hjr : (j : ℕ) + 1 ≤ r := j.2
  have hgX : ∀ a, ∀ y ∈ S.spanTo g r, hf L S.Hm (g a) y = 0 := fun a y hy =>
    hf_symm0 S (hf_spanTo S g _ (fun i hi => hf_symm0 S (hgram a i hi)) hy)
  have hXX : ∀ {c : ℕ}, ∀ v ∈ S.spanTo g c, v ∈ perp L S.Hm (S.spanTo g r) := fun v hv y hy =>
    hf_spanTo S g y (fun i _ => hgX i y hy) hv
  have hxr : x ∈ S.spanTo g r := spanTo_mono S g hjr hx
  have hE : ∀ (u : S.V) (s : E), ∀ v ∈ perp L S.Hm (S.spanTo g r),
      eich L S.Hm x u s v - v = hf L S.Hm v u • x := by
    intro u s v hv
    simp only [eich, hv x hxr]
    module
  have hfl : ∀ u ∈ perp L S.Hm (S.spanTo g (j + 1)), ∀ (s : E) (i : ℕ), ∀ v ∈ S.spanTo g (i + 1),
      eich L S.Hm x u s v - v ∈ S.spanTo g i := by
    intro u hu s i v hv
    rw [hE u s v (hXX v hv)]
    rcases le_or_gt i j with h | h
    · rw [hf_symm0 S (hu v (spanTo_mono S g (by omega) hv)), zero_smul]
      exact Submodule.zero_mem _
    · exact Submodule.smul_mem _ _ (spanTo_mono S g h hx)
  obtain ⟨n, hn, h1, h2⟩ := eichler_isometry L S.Hm S.herm x u s (hXX x hx x hxr) (hu x hx) hs
  refine ⟨n, ⟨⟨hn, ?_⟩, ?_⟩, h1, h2, ?_, ?_⟩
  · refine Subgroup.mem_iInf.2 fun i => ?_
    refine mem_unipOn (spanTo_mono S g (by omega)) n (fun v hv => ?_) (fun v hv => ?_)
    · rw [h1]; exact hfl u hu s i v hv
    · rw [h2]; exact hfl _ (Submodule.neg_mem _ hu) _ i v hv
  · refine mem_unipOn (fun v hv => hXX v hv) n (fun v hv => ?_) (fun v hv => ?_)
    · rw [h1, hE _ _ v hv]; exact Submodule.smul_mem _ _ hxr
    · rw [h2, hE _ _ v hv]; exact Submodule.smul_mem _ _ hxr
  · intro v hv
    have := hE u s v (hXX v hv)
    rw [hf_symm0 S (hu v hv), zero_smul, sub_eq_zero] at this
    rw [h1, this]
  · rintro m ⟨⟨-, hm1⟩, hm2⟩
    replace hm1 := Subgroup.mem_iInf.1 hm1
    have hm : m (g j.succ) - g j.succ ∈ S.spanTo g (j + 1) := by
      rcases hjr.lt_or_eq with h | h
      · exact (hm1 ⟨j + 1, h⟩).2 _ (mem_spanTo S g _ (by simp))
      · have := hm2.2 (g j.succ) (hgX _)
        exact spanTo_mono S g h.ge this
    have hmu : hf L S.Hm (m (g j.succ)) u = hf L S.Hm (g j.succ) u := by
      have := hf_symm0 S (hu _ hm)
      rwa [hf_sub_l, sub_eq_zero] at this
    have hc : ∀ i : Fin r, S.coef g gs n i = hf L S.Hm x (gs i) * hf L S.Hm (g i.succ) u := by
      intro i
      have h3 := hE u s (g i.succ) (hgX _)
      rw [sub_eq_iff_eq_add, ← h1] at h3
      have h4 : i.succ ≠ i.castSucc := (Fin.castSucc_lt_succ).ne'
      simp only [Frames.coef, Frames.h]
      rw [h3, hf_add_l, hf_smul_l, hdual, if_neg h4]
      ring
    have hsum : ∑ i, S.coef g gs n i = S.h x (gs j) * S.h (m (g j.succ)) u := by
      simp only [Frames.h]
      rw [Finset.sum_eq_single j, hc, hmu]
      · intro i _ hij
        rw [hc]
        rcases lt_or_gt_of_ne hij with h | h
        · have h' : (i : ℕ) < j := h
          rw [hf_symm0 S (hu _ (mem_spanTo S g i.succ (by simp; omega))), mul_zero]
        · have h' : (j : ℕ) < i := h
          rw [hf_spanTo S g (gs i) (fun a ha => ?_) hx, zero_mul]
          rw [hdual, if_neg]
          rintro rfl
          simp at ha
          omega
      · simp
    simp only [Frames.psiOf, hsum]

end GlobalTheory.HL.EichlerUnip
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.EichlerLocal

open GlobalTheory.HL.Eichler

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E}

theorem smul_mem' {Λ : Submodule L.O (Fin n → E)} {a : E} (ha : a ∈ L.O) {v : Fin n → E}
    (hv : v ∈ Λ) : a • v ∈ Λ := Λ.smul_mem (⟨a, ha⟩ : L.O) hv

theorem mem_of_close (hH : IsHerm L Hm) {Λ : Submodule L.O (Fin n → E)} (hΛ : IsSD L Hm Λ)
    {p : E} (hp : p ∈ L.O) (hpc : L.cj p = p) {x u a b : Fin n → E} {s t : E}
    (hx : hf L Hm x x = 0) (hu : hf L Hm u x = 0) (hs : s + L.cj s = hf L Hm u u)
    (hxΛ : p • x ∈ Λ) (huΛ : u ∈ Λ) (hsO : s ∈ L.O) (ha : a ∈ Λ) (hb : b ∈ Λ) (ht : t ∈ L.O)
    {v : Fin n → E} (hv : eich L Hm x u s v ∈ Λ) :
    eich L Hm (x + p ^ 4 • a) (u + p ^ 4 • b) (s + p ^ 4 * t) v ∈ Λ := by
  have hint : ∀ {y z}, y ∈ Λ → z ∈ Λ → hf L Hm y z ∈ L.O := fun hy hz => (hΛ.2 _).2 hz _ hy
  have hV : p ^ 2 • v ∈ Λ := by
    rw [← eich_inv L hH x u s hx hu hs v]
    generalize eich L Hm x u s v = w at hv
    have e : p ^ 2 • eich L Hm x (-u) (L.cj s) w = p ^ 2 • w - (p * hf L Hm w u) • (p • x)
        + (p * hf L Hm w (p • x)) • u - (hf L Hm w (p • x) * L.cj s) • (p • x) := by
      simp only [eich, hf_neg_r, hf_smul_r, hpc]
      module
    rw [e]
    exact Λ.sub_mem (Λ.add_mem (Λ.sub_mem (smul_mem' L (L.O.pow_mem hp 2) hv)
      (smul_mem' L (L.O.mul_mem hp (hint hv huΛ)) hxΛ))
      (smul_mem' L (L.O.mul_mem hp (hint hv hxΛ)) huΛ))
      (smul_mem' L (L.O.mul_mem (hint hv hxΛ) (GlobalTheory.UnramOrder.cj_mem L hsO)) hxΛ)
  have hu1 : u + p ^ 4 • b ∈ Λ := Λ.add_mem huΛ (smul_mem' L (L.O.pow_mem hp 4) hb)
  have hx1 : p • x + p ^ 5 • a ∈ Λ := Λ.add_mem hxΛ (smul_mem' L (L.O.pow_mem hp 5) ha)
  have hs1 : s + p ^ 4 * t ∈ L.O := L.O.add_mem hsO (L.O.mul_mem (L.O.pow_mem hp 4) ht)
  have e : eich L Hm (x + p ^ 4 • a) (u + p ^ 4 • b) (s + p ^ 4 * t) v = eich L Hm x u s v
      + (p * hf L Hm (p ^ 2 • v) b) • (p • x) + (p ^ 2 * hf L Hm (p ^ 2 • v) (u + p ^ 4 • b)) • a
      - (p * hf L Hm (p ^ 2 • v) (p • x)) • b - (p ^ 2 * hf L Hm (p ^ 2 • v) a) • (u + p ^ 4 • b)
      - (p * hf L Hm (p ^ 2 • v) a * (s + p ^ 4 * t)) • (p • x + p ^ 5 • a)
      - (hf L Hm (p ^ 2 • v) (p • x) * t) • (p • x + p ^ 5 • a)
      - (p * hf L Hm (p ^ 2 • v) (p • x) * s) • a := by
    simp only [eich, hf_add_r, hf_smul_r, hf_smul_l, map_pow, hpc]
    module
  rw [e]
  have hp2 := L.O.pow_mem hp 2
  exact Λ.sub_mem (Λ.sub_mem (Λ.sub_mem (Λ.sub_mem (Λ.sub_mem (Λ.add_mem (Λ.add_mem hv
    (smul_mem' L (L.O.mul_mem hp (hint hV hb)) hxΛ))
    (smul_mem' L (L.O.mul_mem hp2 (hint hV hu1)) ha))
    (smul_mem' L (L.O.mul_mem hp (hint hV hxΛ)) hb))
    (smul_mem' L (L.O.mul_mem hp2 (hint hV ha)) hu1))
    (smul_mem' L (L.O.mul_mem (L.O.mul_mem hp (hint hV ha)) hs1) hx1))
    (smul_mem' L (L.O.mul_mem (hint hV hxΛ) ht) hx1))
    (smul_mem' L (L.O.mul_mem (L.O.mul_mem hp (hint hV hxΛ)) hsO) ha)

end

theorem moved_locally_constant : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ Λ : Submodule L.O S.V, IsSD L S.Hm Λ → ∀ c : ℕ, ∃ N : ℕ, ∀ (x x₁ u u₁ : S.V) (s s₁ : E), S.h x x = 0 → S.h u x = 0 → s + L.cj s = S.h u u → S.h x₁ x₁ = 0 → S.h u₁ x₁ = 0 → s₁ + L.cj s₁ = S.h u₁ u₁ → algebraMap F E ((S.ϖ : F) ^ c) • x ∈ Λ → u ∈ Λ → s ∈ L.O → (∃ y ∈ Λ, x₁ - x = algebraMap F E ((S.ϖ : F) ^ N) • y) → (∃ y ∈ Λ, u₁ - u = algebraMap F E ((S.ϖ : F) ^ N) • y) → (∃ y ∈ L.O, s₁ - s = algebraMap F E ((S.ϖ : F) ^ N) * y) → S.moved Λ x₁ u₁ s₁ = S.moved Λ x u s := by
  intro F _ _ _ _ _ E _ _ _ L r k S Λ hΛ c
  refine ⟨c * 4, ?_⟩
  rintro x x₁ u u₁ s s₁ hx hu hs hx₁ hu₁ hs₁ hxΛ huΛ hsO ⟨a, ha, ea⟩ ⟨b, hb, eb⟩ ⟨t, ht, et⟩
  rw [pow_mul, map_pow] at ea eb et
  have hp : algebraMap F E ((S.ϖ : F) ^ c) ∈ L.O :=
    (GlobalTheory.UnramOrder.algebraMap_mem_iff L _).2 (Subring.pow_mem _ S.ϖ.2 c)
  have hpc : L.cj (algebraMap F E ((S.ϖ : F) ^ c)) = algebraMap F E ((S.ϖ : F) ^ c) :=
    L.cj.commutes _
  generalize algebraMap F E ((S.ϖ : F) ^ c) = p at *
  obtain rfl : x₁ = x + p ^ 4 • a := by rw [← ea]; abel
  obtain rfl : u₁ = u + p ^ 4 • b := by rw [← eb]; abel
  obtain rfl : s₁ = s + p ^ 4 * t := by rw [← et]; ring
  ext v
  constructor
  · intro hv
    have h := mem_of_close L S.herm.1 hΛ hp hpc hx₁ hu₁ hs₁
      (by
        rw [smul_add]
        exact Λ.add_mem hxΛ (smul_mem' L hp (smul_mem' L (L.O.pow_mem hp 4) ha)))
      (Λ.add_mem huΛ (smul_mem' L (L.O.pow_mem hp 4) hb))
      (L.O.add_mem hsO (L.O.mul_mem (L.O.pow_mem hp 4) ht))
      (Λ.neg_mem ha) (Λ.neg_mem hb) (L.O.neg_mem ht) hv
    simp only [smul_neg, mul_neg, add_neg_cancel_right] at h
    exact h
  · intro hv
    exact mem_of_close L S.herm.1 hΛ hp hpc hx hu hs hxΛ huΛ hsO ha hb ht hv

end GlobalTheory.HL.EichlerLocal
end

section

open GlobalTheory.GramCount
open scoped Classical

namespace GlobalTheory.GramCount

variable {B : Type} [CommRing B] [Fintype B]

theorem quad_sum_char_pi (χ : AddChar B ℂ) (hχ : χ.IsPrimitive) {m : ℕ} (w : Fin m → B) :
    ∑ s : Fin m → B, χ (∑ i, s i * w i) =
      if w = 0 then (Fintype.card B : ℂ) ^ m else 0 := by
  have h1 : ∀ s : Fin m → B, χ (∑ i, s i * w i) = ∏ i, χ (s i * w i) := by
    intro s
    induction (Finset.univ : Finset (Fin m)) using Finset.induction_on with
    | empty => simp
    | insert a S ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]
  simp only [h1]
  have h2 := Finset.prod_univ_sum (fun _ : Fin m => (Finset.univ : Finset B))
    (fun i b => χ (b * w i))
  rw [Fintype.piFinset_univ] at h2
  rw [← h2]
  simp only [AddChar.sum_mulShift _ hχ]
  split_ifs with hw
  · simp [hw]
  · obtain ⟨i, hi⟩ := Function.ne_iff.1 hw
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [show w i ≠ 0 from hi])


omit [Fintype B] in
theorem quad_char_skew (c : B →+* B) (hc : ∀ u, c (c u) = u) {ω : B} (hω : IsUnit (ω - c ω))
    (χ : AddChar B ℂ) (hχc : ∀ u, χ (c u) = χ u) {a w : B} (ha : c a = -a) (hw : c w = w) :
    χ (a * w) = 1 := by
  obtain ⟨θ, e, hθ, -, -⟩ := exists_trace_one c hc hω
  have h1 : a * w = θ * (a * w) + c (θ * (-(a * w))) := by
    simp only [map_mul, map_neg, ha, hw]
    linear_combination (-(a * w)) * hθ
  rw [h1, AddChar.map_add_eq_mul, hχc, ← AddChar.map_add_eq_mul]
  simp

theorem quad_count {B : Type} [CommRing B] [Fintype B] (c : B →+* B) (hc : ∀ u, c (c u) = u)
    (ω : B) (hω : IsUnit (ω - c ω)) (hf : ∀ t, c t = t → t ≠ 0 → IsUnit t) (q : ℕ) (hq : 2 ≤ q)
    (hB : Fintype.card B = q ^ 2) (χ : AddChar B ℂ) (hχ : χ.IsPrimitive)
    (hχc : ∀ u, χ (c u) = χ u) (k n : ℕ) (hkn : 2 * k + 1 ≤ 2 * n) (x : Fin k → Fin n → B)
    (hx : Prim c x) (g : Fin k → B) (t : B) (ht : c t = t) :
    |(Set.ncard {y : Fin n → B | (∀ i, ip c y (x i) = g i) ∧ ip c y y = t} : ℝ)
      - (q : ℝ) ^ (2 * n - (2 * k + 1))| ≤ (q : ℝ) ^ n := by
  set N := Set.ncard {y : Fin n → B | (∀ i, ip c y (x i) = g i) ∧ ip c y y = t} with hN
  let F : B × (Fin k → B) → ℂ := fun z => ∑ y : Fin n → B,
    χ (z.1 * (ip c y y - t)) * χ (∑ i, z.2 i * (ip c y (x i) - g i))
  let G : B × (Fin k → B) → ℂ := fun z =>
    if c z.1 = -z.1 ∧ z.2 = 0 then (q : ℂ) ^ (2 * n) else 0
  have hF : ∑ z, F z = (N : ℂ) * (q : ℂ) ^ (2 * k + 2) := by
    simp only [F]
    rw [Finset.sum_comm]
    have h1 : ∀ y : Fin n → B, ∑ z : B × (Fin k → B),
        χ (z.1 * (ip c y y - t)) * χ (∑ i, z.2 i * (ip c y (x i) - g i)) =
        if (∀ i, ip c y (x i) = g i) ∧ ip c y y = t then (q : ℂ) ^ (2 * k + 2) else 0 := by
      intro y
      rw [Fintype.sum_prod_type]
      simp only
      rw [← Finset.sum_mul_sum, AddChar.sum_mulShift _ hχ,
        quad_sum_char_pi χ hχ (fun i => ip c y (x i) - g i)]
      have h2 : ((fun i => ip c y (x i) - g i) = 0) ↔ ∀ i, ip c y (x i) = g i := by
        simp [funext_iff, sub_eq_zero]
      simp only [h2, sub_eq_zero, hB]
      by_cases h3 : (∀ i, ip c y (x i) = g i) <;> by_cases h4 : ip c y y = t <;> simp [h3, h4]
      ring
    simp only [h1]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hN, ← Set.ncard_coe_finset]
    congr 3
    ext y
    simp
  have hG : ∑ z, G z = (q : ℂ) ^ (2 * n + 1) := by
    have h1 := (card_fixed_sq c hc hω (M := B) c.toAddMonoidHom hc
      (fun a u => by simp)).2
    rw [Nat.card_eq_fintype_card (α := B), hB] at h1
    have h2 := (Nat.pow_left_injective two_ne_zero) h1
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype] at h2
    simp only [G]
    rw [Fintype.sum_prod_type]
    have h3 : ∀ a : B, (∑ s : Fin k → B,
        if c a = -a ∧ s = 0 then (q : ℂ) ^ (2 * n) else 0) =
        if c a = -a then (q : ℂ) ^ (2 * n) else 0 := by
      intro a
      by_cases h : c a = -a <;> simp [h]
    simp only [h3]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have h4 : (Finset.univ.filter fun a : B => c a = -a).card = q := by
      rw [← h2]; congr 1
    rw [h4]; ring
  have hFG : ∀ z, ‖F z - G z‖ ≤ (q : ℝ) ^ n := by
    rintro ⟨a, s⟩
    have hv : ∀ y : Fin n → B, ∑ i, s i * (ip c y (x i) - g i) =
        ip c y (∑ i, c (s i) • x i) - ∑ i, s i * g i := by
      intro y
      simp [ip_sum_right, ip_smul_right, hc, mul_sub, Finset.sum_sub_distrib]
    by_cases ha : c a = -a
    · have h0 : F (a, s) = G (a, s) := by
        have h1 : ∀ y : Fin n → B, χ (a * (ip c y y - t)) = 1 := fun y =>
          quad_char_skew c hc hω χ hχc ha (by rw [map_sub, cj_ip c hc, ht])
        simp only [F, G, h1, one_mul, ha, true_and]
        split_ifs with hs
        · simp [hs, hB, ← pow_mul]
        · simp only [hv]
          simp only [sub_eq_add_neg, AddChar.map_add_eq_mul]
          rw [← Finset.sum_mul]
          have h2 := quad_sum_char_pi χ hχ (fun j => c ((∑ i, c (s i) • x i) j))
          rw [if_neg] at h2
          · simp only [ip]
            rw [h2, zero_mul]
          · intro h3
            apply hs
            have h4 : ∑ i, c (s i) • x i = 0 := by
              funext j
              have := congrArg c (congrFun h3 j)
              simpa only [hc, Pi.zero_apply, map_zero] using this
            have h5 := hx.eq_zero c (fun i => c (s i)) h4
            funext i
            have := congrArg c (congrFun h5 i)
            simpa only [hc, Pi.zero_apply, map_zero] using this
      rw [h0, sub_self, norm_zero]
      positivity
    · have hu : IsUnit (a + c a) := hf _ (by rw [map_add (f := _), hc, add_comm])
        (fun h => ha (by linear_combination h))
      have h1 := GlobalTheory.T.norm_gauss_sum_hermitian_form_linear_le c hc q hq hB χ hχ hχc n a hu (∑ i, c (s i) • x i)
      have h2 : F (a, s) = χ (-(a * t + ∑ i, s i * g i)) *
          ∑ y : Fin n → B, χ (a * ip c y y + ip c y (∑ i, c (s i) • x i)) := by
        simp only [F, hv, Finset.mul_sum, ← AddChar.map_add_eq_mul]
        refine Finset.sum_congr rfl fun y _ => ?_
        congr 1
        ring
      have h3 : G (a, s) = 0 := by simp [G, ha]
      rw [h3, sub_zero, h2, norm_mul, AddChar.norm_apply, one_mul]
      exact h1
  have hS : ‖∑ z, F z - ∑ z, G z‖ ≤ (q : ℝ) ^ (2 * k + 2) * (q : ℝ) ^ n := by
    rw [← Finset.sum_sub_distrib]
    refine (norm_sum_le_of_le _ fun z _ => hFG z).trans (le_of_eq ?_)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fun,
      Fintype.card_fin, hB, nsmul_eq_mul]
    push_cast
    ring
  have hE : (q : ℂ) ^ (2 * n + 1) = (q : ℂ) ^ (2 * n - (2 * k + 1)) * (q : ℂ) ^ (2 * k + 2) := by
    rw [← pow_add]; congr 1; omega
  rw [hF, hG, hE, ← sub_mul, norm_mul] at hS
  have hq' : (0 : ℝ) < (q : ℝ) ^ (2 * k + 2) := by
    have : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
    positivity
  have h5 : ‖(q : ℂ) ^ (2 * k + 2)‖ = (q : ℝ) ^ (2 * k + 2) := by simp
  have h6 : ‖(N : ℂ) - (q : ℂ) ^ (2 * n - (2 * k + 1))‖ =
      |(N : ℝ) - (q : ℝ) ^ (2 * n - (2 * k + 1))| := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real]
    push_cast
    rfl
  rw [h5, h6, mul_comm] at hS
  exact le_of_mul_le_mul_left hS hq'

end GlobalTheory.GramCount
end

section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.exists_mem_fractionalIdeal_primitive_local_generator' : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Module.finrank F E = 2 → ∀ (c : FractionalIdeal (nonZeroDivisors (𝓞 E)) E), c ≠ 0 → ∀ N : 𝓞 E, N ≠ 0 → ∃ a : E, a ∈ c ∧ (∀ Q : Ideal (𝓞 E), Q.IsMaximal → N ∈ Q → a ∉ (Q : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c) ∧ ∀ p : Ideal (𝓞 F), p.IsMaximal → a ∉ ((Ideal.map (algebraMap (𝓞 F) (𝓞 E)) p : Ideal (𝓞 E)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c := by
  first | exact @GlobalTheory.exists_mem_fractionalIdeal_primitive_local_generator | exact GlobalTheory.exists_mem_fractionalIdeal_primitive_local_generator | (intros; apply GlobalTheory.exists_mem_fractionalIdeal_primitive_local_generator <;> assumption)
end
