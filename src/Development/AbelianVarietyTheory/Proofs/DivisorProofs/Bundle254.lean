module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain Matrix GlobalTheory.AdLat GlobalTheory.UCls ReciprocityTheory.ChartRestriction.G.FD
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.LocGlob

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem ratM_mulVec_tmul (γ : Matrix (Fin n) (Fin n) E) (a : FiniteAdeleRing (𝓞 F) F) (x : Fin n → E) :
    ratM F γ *ᵥ (fun i => a ⊗ₜ[F] x i) = fun i => a ⊗ₜ[F] (γ *ᵥ x) i := by
  ext i
  simp only [mulVec, dotProduct, ratM, Matrix.map_apply]
  rw [TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem ratM_mulVec_fv (γ : Matrix (Fin n) (Fin n) E) (x : Fin n → E) :
    ratM F γ *ᵥ fv F x = fv F (γ *ᵥ x) :=
  ratM_mulVec_tmul γ 1 x

theorem ratM_mul (γ δ : Matrix (Fin n) (Fin n) E) : ratM F (γ * δ) = ratM F γ * ratM F δ := by
  have h : ∀ ε : Matrix (Fin n) (Fin n) E,
      ratM F ε = (Algebra.TensorProduct.includeRight : E →ₐ[F] RA F E).toRingHom.mapMatrix ε := by
    intro ε; ext i j; simp [ratM]
  rw [h, h, h, map_mul]

theorem ratM_one : ratM F (1 : Matrix (Fin n) (Fin n) E) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [ratM, Matrix.one_apply, h, Algebra.TensorProduct.one_def]

theorem fv_sub (x y : Fin n → E) : fv F (x - y) = fv F x - fv F y := by
  ext i; simp [fv, TensorProduct.tmul_sub]

theorem fv_nsmul (M : ℕ) (x : Fin n → E) : fv F (M • x) = M • fv F x := by
  ext i
  simp only [fv, Pi.smul_apply]
  exact map_nsmul (TensorProduct.mk F (FiniteAdeleRing (𝓞 F) F) E 1) M (x i)

theorem nsmul_cancel {V : Type} [AddCommGroup V] [Module F V] {M : ℕ} (hM : 1 ≤ M) {u w : V}
    (h : M • u = M • w) : u = w := by
  have h0 : (M : F) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  rw [← Nat.cast_smul_eq_nsmul F, ← Nat.cast_smul_eq_nsmul F] at h
  simpa [h0] using congrArg (fun z => (M : F)⁻¹ • z) h

theorem stab_cong_iff_hat (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (M : ℕ) (β : GL (Fin n) E) (hM : 1 ≤ M)
    (hrat : ∀ v, fv F v ∈ hat F (Λ : Set (Fin n → E)) ↔ v ∈ Λ) :
    ((∀ x, x ∈ Λ ↔ (β : Matrix (Fin n) (Fin n) E) *ᵥ x ∈ Λ) ∧
        ∀ x ∈ Λ, ∃ y ∈ Λ, (β : Matrix (Fin n) (Fin n) E) *ᵥ x - x = M • y) ↔
      ((∀ x ∈ hat F (Λ : Set (Fin n → E)), ∃ y ∈ hat F (Λ : Set (Fin n → E)),
          ratM F (β : Matrix (Fin n) (Fin n) E) *ᵥ x - x = M • y) ∧
        ∀ x ∈ hat F (Λ : Set (Fin n → E)), ∃ y ∈ hat F (Λ : Set (Fin n → E)),
          ratM F (β : Matrix (Fin n) (Fin n) E) *ᵥ y = x) := by
  set B : Matrix (Fin n) (Fin n) E := (β : Matrix (Fin n) (Fin n) E) with hB
  set C : Matrix (Fin n) (Fin n) E := ((β⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) with hC
  have hBC : B * C = 1 := Units.mul_inv β
  have hCB : C * B = 1 := Units.inv_mul β
  have hRBC : ∀ z, ratM F B *ᵥ (ratM F C *ᵥ z) = z := by
    intro z; rw [mulVec_mulVec, ← ratM_mul, hBC, ratM_one, one_mulVec]
  have hRCB : ∀ z, ratM F C *ᵥ (ratM F B *ᵥ z) = z := by
    intro z; rw [mulVec_mulVec, ← ratM_mul, hCB, ratM_one, one_mulVec]
  have gen : ∀ (a : FiniteAdeleRing (𝓞 F) F), (∀ v, a v ∈ v.adicCompletionIntegers F) → ∀ x ∈ Λ,
      (fun i => a ⊗ₜ[F] x i) ∈ hat F (Λ : Set (Fin n → E)) :=
    fun a ha x hx => AddSubgroup.subset_closure ⟨a, ha, x, hx, rfl⟩
  constructor
  · rintro ⟨hstab, hcong⟩
    refine ⟨fun z hz => ?_, fun z hz => ⟨ratM F C *ᵥ z, ?_, hRBC z⟩⟩
    · induction hz using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨a, ha, x, hx, rfl⟩ := hz
        obtain ⟨y, hy, hxy⟩ := hcong x hx
        refine ⟨fun i => a ⊗ₜ[F] y i, gen a ha y hy, ?_⟩
        rw [ratM_mulVec_tmul]
        ext i
        have := congrFun hxy i
        simp only [Pi.sub_apply, Pi.smul_apply] at this ⊢
        rw [← TensorProduct.tmul_sub, this]
        exact map_nsmul (TensorProduct.mk F (FiniteAdeleRing (𝓞 F) F) E a) M (y i)
      | zero => exact ⟨0, zero_mem _, by simp⟩
      | add z w _ _ h1 h2 =>
        obtain ⟨y1, hy1, e1⟩ := h1
        obtain ⟨y2, hy2, e2⟩ := h2
        refine ⟨y1 + y2, add_mem hy1 hy2, ?_⟩
        rw [mulVec_add, smul_add, ← e1, ← e2]; abel
      | neg z _ h =>
        obtain ⟨y, hy, e⟩ := h
        refine ⟨-y, neg_mem hy, ?_⟩
        rw [mulVec_neg, smul_neg, ← e]; abel
    · induction hz using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨a, ha, x, hx, rfl⟩ := hz
        rw [ratM_mulVec_tmul]
        refine gen a ha _ ((hstab _).2 ?_)
        rw [mulVec_mulVec, hBC, one_mulVec]; exact hx
      | zero => simp
      | add z w _ _ h1 h2 => rw [mulVec_add]; exact add_mem h1 h2
      | neg z _ h => rw [mulVec_neg]; exact neg_mem h
  · rintro ⟨hcong, hsurj⟩
    have himg : ∀ x ∈ Λ, B *ᵥ x ∈ Λ := by
      intro x hx
      obtain ⟨y, hy, e⟩ := hcong _ ((hrat x).2 hx)
      rw [← hrat, ← ratM_mulVec_fv, sub_eq_iff_eq_add.mp e]
      exact add_mem (nsmul_mem hy M) ((hrat x).2 hx)
    refine ⟨fun x => ⟨himg x, fun hx => ?_⟩, fun x hx => ?_⟩
    · obtain ⟨y, hy, e⟩ := hsurj _ ((hrat _).2 hx)
      rw [← ratM_mulVec_fv] at e
      have hyx : y = fv F x := by
        have := congrArg (fun z => ratM F C *ᵥ z) e
        simpa only [hRCB] using this
      rw [← hrat, ← hyx]; exact hy
    · obtain ⟨y, hy, e⟩ := hcong _ ((hrat x).2 hx)
      have hM0 : (M : E) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
      set w : Fin n → E := (M : E)⁻¹ • (B *ᵥ x - x) with hw
      have hMw : M • w = B *ᵥ x - x := by
        rw [hw, ← Nat.cast_smul_eq_nsmul E, smul_inv_smul₀ hM0]
      have hfw : fv F w = y := by
        apply nsmul_cancel (F := F) hM
        rw [← fv_nsmul, hMw, fv_sub, ← ratM_mulVec_fv, e]
      exact ⟨w, (hrat w).1 (hfw ▸ hy), hMw.symm⟩

end GlobalTheory.LocGlob
end
end

section

open GlobalTheory GlobalTheory.DI

set_option autoImplicit false

namespace GlobalTheory.DI

section CupDelta

variable {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E]

theorem sum_alt_filter_lt_le (F : Finset ι → E) (u : Finset ι) :
    ∑ j ∈ u, (-1 : ℤ) ^ (u.filter (· < j)).card • (F (u.filter (· < j)) + F (u.filter (· ≤ j))) =
      F ∅ - (-1 : ℤ) ^ u.card • F u := by
  induction u using Finset.induction_on_max with
  | empty => simp
  | insert m u hm ih =>
    have hmu : m ∉ u := fun h => lt_irrefl m (hm m h)
    rw [Finset.sum_insert hmu]
    rw [Finset.sum_congr rfl (g := fun j => (-1 : ℤ) ^ (u.filter (· < j)).card •
        (F (u.filter (· < j)) + F (u.filter (· ≤ j)))) (fun j hj => by
      rw [Finset.filter_insert, if_neg (not_lt.2 (hm j hj).le), Finset.filter_insert,
        if_neg (not_le.2 (hm j hj))]), ih]
    have e1 : (insert m u).filter (· < m) = u := by
      ext x; simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hx, hxm⟩
        · exact absurd hxm (lt_irrefl _)
        · exact hx
      · intro hx; exact ⟨Or.inr hx, hm x hx⟩
    have e2 : (insert m u).filter (· ≤ m) = insert m u := by
      ext x; simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · exact fun h => h.1
      · rintro (rfl | hx)
        · exact ⟨Or.inl rfl, le_rfl⟩
        · exact ⟨Or.inr hx, (hm x hx).le⟩
    rw [e1, e2, Finset.card_insert_of_notMem hmu, pow_succ, smul_add, mul_neg_one, neg_smul]
    abel

theorem delta_cup_eq : ∀ {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E]
    (Φ : E →+ (Finset ι → E)) (c : Finset ι → E), (∀ x, Φ x ∅ = 0) → c ∅ = 0 → ∀ u,
    delta (cup Φ c) u = cup Φ (delta c) u + ∑ j ∈ u, (-1 : ℤ) ^ (u.filter (· < j)).card •
      delta (Φ (c (u.filter (· ≤ j)))) (u.filter (j ≤ ·)) := by
  intro ι _ E _ Φ c hΦ hc u

  have sL : ∀ {i j : ι}, i < j → cubeSign u i = cubeSign (u.filter (· ≤ j)) i := by
    intro i j hij
    have : (u.filter (· ≤ j)).filter (· < i) = u.filter (· < i) := by
      ext x; simp only [Finset.mem_filter]; grind
    unfold cubeSign; rw [this]
  have sR : ∀ {i j : ι}, j < i → cubeSign u i =
      (-1 : ℤ) ^ (u.filter (· < j)).card * cubeSign (u.filter (j ≤ ·)) i := by
    intro i j hji
    have hd : Disjoint (u.filter (· < j)) ((u.filter (j ≤ ·)).filter (· < i)) := by
      rw [Finset.disjoint_left]; intro x h1 h2
      simp only [Finset.mem_filter] at h1 h2
      exact absurd h1.2 (not_lt.2 h2.1.2)
    have : u.filter (· < i) = u.filter (· < j) ∪ (u.filter (j ≤ ·)).filter (· < i) := by
      ext x; simp only [Finset.mem_filter, Finset.mem_union]; grind
    unfold cubeSign; rw [← pow_add, ← Finset.card_union_of_disjoint hd, this]

  have hL : delta (cup Φ c) u = ∑ j ∈ u, ∑ i ∈ u.erase j,
      cubeSign u i • Φ (c ((u.erase i).filter (· ≤ j))) ((u.erase i).filter (j ≤ ·)) := by
    simp only [delta, cup, Finset.smul_sum]
    exact Finset.sum_comm' (fun i j => by simp only [Finset.mem_erase]; tauto)

  have key : ∀ j ∈ u, Φ (delta c (u.filter (· ≤ j))) (u.filter (j ≤ ·)) +
      (-1 : ℤ) ^ (u.filter (· < j)).card • delta (Φ (c (u.filter (· ≤ j)))) (u.filter (j ≤ ·)) =
      ∑ i ∈ u.erase j,
        cubeSign u i • Φ (c ((u.erase i).filter (· ≤ j))) ((u.erase i).filter (j ≤ ·)) +
      (-1 : ℤ) ^ (u.filter (· < j)).card • (Φ (c (u.filter (· < j))) (u.filter (j ≤ ·)) +
        Φ (c (u.filter (· ≤ j))) (u.filter (j < ·))) := by
    intro j hj
    have eL : (u.erase j).filter (· < j) = u.filter (· < j) := by
      ext x; simp only [Finset.mem_filter, Finset.mem_erase]; grind
    have eG : (u.erase j).filter (fun x => ¬ x < j) = u.filter (j < ·) := by
      ext x; simp only [Finset.mem_filter, Finset.mem_erase]; grind
    have eLeL : (u.filter (· ≤ j)).filter (· < j) = u.filter (· < j) := by
      ext x; simp only [Finset.mem_filter]; grind
    have eLeJ : (u.filter (· ≤ j)).filter (fun x => ¬ x < j) = {j} := by
      ext x; simp only [Finset.mem_filter, Finset.mem_singleton]; grind
    have eGeG : (u.filter (j ≤ ·)).filter (j < ·) = u.filter (j < ·) := by
      ext x; simp only [Finset.mem_filter]; grind
    have eGeJ : (u.filter (j ≤ ·)).filter (fun x => ¬ j < x) = {j} := by
      ext x; simp only [Finset.mem_filter, Finset.mem_singleton]; grind
    have eLeE : (u.filter (· ≤ j)).erase j = u.filter (· < j) := by
      ext x; simp only [Finset.mem_filter, Finset.mem_erase]; grind
    have eGeE : (u.filter (j ≤ ·)).erase j = u.filter (j < ·) := by
      ext x; simp only [Finset.mem_filter, Finset.mem_erase]; grind

    rw [← Finset.sum_filter_add_sum_filter_not (u.erase j) (· < j), eL, eG]

    have h1 : Φ (delta c (u.filter (· ≤ j))) (u.filter (j ≤ ·)) =
        ∑ i ∈ u.filter (· < j), cubeSign (u.filter (· ≤ j)) i •
          Φ (c ((u.filter (· ≤ j)).erase i)) (u.filter (j ≤ ·)) +
        (-1 : ℤ) ^ (u.filter (· < j)).card • Φ (c (u.filter (· < j))) (u.filter (j ≤ ·)) := by

      simp only [delta, map_sum, map_zsmul, Finset.sum_apply, Pi.smul_apply]
      rw [← Finset.sum_filter_add_sum_filter_not (u.filter (· ≤ j)) (· < j), eLeL, eLeJ,
        Finset.sum_singleton, eLeE]
      congr 2
      unfold cubeSign; rw [eLeL]

    have h2 : delta (Φ (c (u.filter (· ≤ j)))) (u.filter (j ≤ ·)) =
        ∑ i ∈ u.filter (j < ·), cubeSign (u.filter (j ≤ ·)) i •
          Φ (c (u.filter (· ≤ j))) ((u.filter (j ≤ ·)).erase i) +
        Φ (c (u.filter (· ≤ j))) (u.filter (j < ·)) := by
      simp only [delta]
      rw [← Finset.sum_filter_add_sum_filter_not (u.filter (j ≤ ·)) (j < ·), eGeG, eGeJ,
        Finset.sum_singleton, eGeE, cubeSign_eq_one_of_forall_le (by simp), one_smul]
    rw [h1, h2, smul_add, Finset.smul_sum]
    have hA : ∑ i ∈ u.filter (· < j), cubeSign u i •
          Φ (c ((u.erase i).filter (· ≤ j))) ((u.erase i).filter (j ≤ ·)) =
        ∑ i ∈ u.filter (· < j), cubeSign (u.filter (· ≤ j)) i •
          Φ (c ((u.filter (· ≤ j)).erase i)) (u.filter (j ≤ ·)) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hij : i < j := (Finset.mem_filter.1 hi).2
      rw [sL hij, Finset.filter_erase, Finset.filter_erase,
        Finset.erase_eq_of_notMem (s := u.filter (j ≤ ·)) (by simp [hij])]
    have hB : ∑ i ∈ u.filter (j < ·), cubeSign u i •
          Φ (c ((u.erase i).filter (· ≤ j))) ((u.erase i).filter (j ≤ ·)) =
        ∑ i ∈ u.filter (j < ·), (-1 : ℤ) ^ (u.filter (· < j)).card •
          cubeSign (u.filter (j ≤ ·)) i • Φ (c (u.filter (· ≤ j))) ((u.filter (j ≤ ·)).erase i) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hji : j < i := (Finset.mem_filter.1 hi).2
      rw [sR hji, Finset.filter_erase, Finset.filter_erase,
        Finset.erase_eq_of_notMem (s := u.filter (· ≤ j)) (by simp [hji]), mul_smul]
    rw [hA, hB]
    simp only [smul_add]
    abel

  have tele := sum_alt_filter_lt_le (fun s => Φ (c s) (u \ s)) u
  simp only [Finset.sdiff_self, hΦ, Finset.sdiff_empty, hc, map_zero, Pi.zero_apply, smul_zero,
    sub_zero] at tele
  have hT : ∑ j ∈ u, (-1 : ℤ) ^ (u.filter (· < j)).card • (Φ (c (u.filter (· < j))) (u.filter (j ≤ ·)) +
      Φ (c (u.filter (· ≤ j))) (u.filter (j < ·))) = 0 := by
    rw [← tele]
    refine Finset.sum_congr rfl fun j _ => ?_
    have a1 : u \ u.filter (· < j) = u.filter (j ≤ ·) := by
      ext x; simp only [Finset.mem_sdiff, Finset.mem_filter]; grind
    have a2 : u \ u.filter (· ≤ j) = u.filter (j < ·) := by
      ext x; simp only [Finset.mem_sdiff, Finset.mem_filter]; grind
    rw [a1, a2]
  rw [hL]
  show _ = ∑ j ∈ u, Φ (delta c (u.filter (· ≤ j))) (u.filter (j ≤ ·)) + _
  rw [← Finset.sum_add_distrib, Finset.sum_congr rfl key, Finset.sum_add_distrib, hT, add_zero]

end CupDelta

end GlobalTheory.DI
end

section

set_option autoImplicit false

namespace GlobalTheory.DI

variable {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E]

theorem delta_add (c c' : Finset ι → E) : delta (c + c') = delta c + delta c' := by
  funext t
  simp only [delta, Pi.add_apply, smul_add, Finset.sum_add_distrib]

theorem delta_sub (c c' : Finset ι → E) : delta (c - c') = delta c - delta c' := by
  funext t
  simp only [delta, Pi.sub_apply, smul_sub, Finset.sum_sub_distrib]

theorem delta_delta (c : Finset ι → E) : delta (delta c) = 0 := by
  funext t
  let f : ι × ι → E := fun q =>
    (cubeSign t q.1 * cubeSign (t.erase q.1) q.2) • c ((t.erase q.1).erase q.2)
  have h1 : delta (delta c) t = ∑ q ∈ t.offDiag, f q := by
    show ∑ i ∈ t, cubeSign t i • delta c (t.erase i) = _
    rw [Finset.sum_finset_product t.offDiag t (fun i => t.erase i)
      (fun q => by simp only [Finset.mem_offDiag, Finset.mem_erase]; tauto)]
    refine Finset.sum_congr rfl fun i _ => ?_
    show cubeSign t i • ∑ j ∈ t.erase i, cubeSign (t.erase i) j • c ((t.erase i).erase j) = _
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [f, smul_smul]
  rw [h1, Pi.zero_apply]
  refine Finset.sum_involution (fun q _ => q.swap) (fun q hq => ?_) (fun q hq _ h => ?_)
    (fun q hq => ?_) (fun q _ => rfl)
  · rw [Finset.mem_offDiag] at hq
    simp only [f, Prod.fst_swap, Prod.snd_swap]
    rw [cubeSign_mul_erase hq.1 hq.2.1 hq.2.2, Finset.erase_right_comm (a := q.1) (b := q.2),
      neg_smul, neg_add_cancel]
  · rw [Finset.mem_offDiag] at hq
    exact hq.2.2 (congrArg Prod.snd h)
  · rw [Finset.mem_offDiag] at hq ⊢
    exact ⟨hq.2.1, hq.1, hq.2.2.symm⟩

theorem Dtot_add (d : E →+ E) (c c' : Finset ι → E) : Dtot d (c + c') = Dtot d c + Dtot d c' := by
  funext t
  simp only [Dtot, delta_add, Pi.add_apply, map_add (f := _), smul_add]
  abel

theorem Dtot_sub (d : E →+ E) (c c' : Finset ι → E) : Dtot d (c - c') = Dtot d c - Dtot d c' := by
  funext t
  simp only [Dtot, delta_sub, Pi.sub_apply, map_sub, smul_sub]
  abel

theorem Dtot_Dtot (d : E →+ E) (hd : ∀ x, d (d x) = 0) (c : Finset ι → E) :
    Dtot d (Dtot d c) = 0 := by
  funext t
  have hDt : ∀ s, Dtot d c s = delta c s + (-1 : ℤ) ^ s.card • d (c s) := fun s => rfl
  have e1 : delta (Dtot d c) t = delta (delta c) t +
      ∑ i ∈ t, cubeSign t i • ((-1 : ℤ) ^ (t.erase i).card • d (c (t.erase i))) := by
    show ∑ i ∈ t, cubeSign t i • Dtot d c (t.erase i) = delta (delta c) t + _
    simp only [hDt, smul_add, Finset.sum_add_distrib]
    rfl
  have e2 : d (delta c t) = ∑ i ∈ t, cubeSign t i • d (c (t.erase i)) := by
    show d (∑ i ∈ t, cubeSign t i • c (t.erase i)) = _

    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => map_zsmul d _ _
  show delta (Dtot d c) t + (-1 : ℤ) ^ t.card • d (Dtot d c t) = 0
  rw [e1, delta_delta, hDt, map_add (f := _), map_zsmul, hd, smul_zero, add_zero, e2, Finset.smul_sum,
    Pi.zero_apply, zero_add, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hc : (-1 : ℤ) ^ (t.erase i).card = -(-1 : ℤ) ^ t.card := by
    rw [← Finset.card_erase_add_one hi, pow_succ]; ring
  rw [hc, neg_smul, smul_neg, smul_comm, neg_add_cancel]

theorem delta_Dtot_props : ∀ {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E] (d : E →+ E),
    (∀ c c' : Finset ι → E, delta (c + c') = delta c + delta c') ∧
    (∀ c c' : Finset ι → E, delta (c - c') = delta c - delta c') ∧
    (∀ c c' : Finset ι → E, Dtot d (c + c') = Dtot d c + Dtot d c') ∧
    (∀ c c' : Finset ι → E, Dtot d (c - c') = Dtot d c - Dtot d c') ∧
    (∀ c : Finset ι → E, delta (delta c) = 0) ∧
    ((∀ x, d (d x) = 0) → ∀ c : Finset ι → E, Dtot d (Dtot d c) = 0) :=
  fun d => ⟨delta_add, delta_sub, Dtot_add d, Dtot_sub d, delta_delta, fun hd => Dtot_Dtot d hd⟩

end GlobalTheory.DI
end

section

set_option autoImplicit false

namespace GlobalTheory.DI

section
variable {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V]

theorem forms_gen_mem {B : Set K} {L : Set V} {q : ℕ} {b : K} (hb : b ∈ B) (v : Fin q → V)
    (hv : ∀ k, v k ∈ L) : b • ExteriorAlgebra.ιMulti K q v ∈ forms B L q :=
  AddSubgroup.subset_closure ⟨b, hb, v, hv, rfl⟩

theorem forms_le_comap_of_gen {B B' : Set K} {L L' : Set V} {q q' : ℕ}
    (φ : ExteriorAlgebra K V →+ ExteriorAlgebra K V)
    (h : ∀ b ∈ B, ∀ v : Fin q → V, (∀ k, v k ∈ L) →
      φ (b • ExteriorAlgebra.ιMulti K q v) ∈ forms B' L' q') :
    forms B L q ≤ (forms B' L' q').comap φ := by
  show AddSubgroup.closure _ ≤ _
  rw [AddSubgroup.closure_le]
  rintro x ⟨b, hb, v, hv, rfl⟩
  exact h b hb v hv

theorem ι_mul_ιMulti_eq (u : V) {q : ℕ} (w : Fin q → V) :
    ExteriorAlgebra.ι K u * ExteriorAlgebra.ιMulti K q w =
      ExteriorAlgebra.ιMulti K (q + 1) (Fin.cons u w) := by
  rw [ExteriorAlgebra.ιMulti_succ_apply]
  rfl

theorem ιMulti_one_eq (u : Fin 1 → V) : ExteriorAlgebra.ιMulti K 1 u = ExteriorAlgebra.ι K (u 0) := by
  rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, mul_one]

theorem forms_mul_smul_mono (A : Subring K) (L : Set V) :
    (1 : ExteriorAlgebra K V) ∈ forms (A : Set K) L 0 ∧
    (∀ q x y, x ∈ forms (A : Set K) L 1 → y ∈ forms (A : Set K) L q →
      x * y ∈ forms (A : Set K) L (q + 1)) ∧
    (∀ q (c : K) y, c ∈ A → y ∈ forms (A : Set K) L q → c • y ∈ forms (A : Set K) L q) ∧
    (∀ (B : Set K) q (c : K) y, y ∈ forms B L q → c • y ∈ forms ((fun b => c * b) '' B) L q) ∧
    ∀ (B B' : Set K) (L' : Set V) q, B ⊆ B' → L ⊆ L' → forms B L q ≤ forms B' L' q := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h := forms_gen_mem (B := (A : Set K)) (L := L) A.one_mem (Fin.elim0 : Fin 0 → V)
      (fun k => k.elim0)
    simpa using h
  · intro q x y hx hy

    have key : ∀ a ∈ (A : Set K), ∀ u : Fin 1 → V, (∀ k, u k ∈ L) →
        a • ExteriorAlgebra.ιMulti K 1 u * y ∈ forms (A : Set K) L (q + 1) := by
      intro a ha u hu
      have := forms_le_comap_of_gen (B := (A : Set K)) (L := L) (B' := (A : Set K)) (L' := L)
        (q := q) (q' := q + 1) (AddMonoidHom.mulLeft (a • ExteriorAlgebra.ιMulti K 1 u)) ?_ hy
      · exact this
      intro b hb w hw
      show a • ExteriorAlgebra.ιMulti K 1 u * (b • ExteriorAlgebra.ιMulti K q w) ∈ _
      rw [smul_mul_smul_comm, ιMulti_one_eq, ι_mul_ιMulti_eq]
      refine forms_gen_mem (A.mul_mem ha hb) _ ?_
      intro k
      refine Fin.cases ?_ (fun k => ?_) k
      · simpa using hu 0
      · simpa using hw k
    exact forms_le_comap_of_gen (B' := (A : Set K)) (L' := L) (q' := q + 1)
      (AddMonoidHom.mulRight y) (fun a ha u hu => key a ha u hu) hx
  · intro q c y hc hy
    refine forms_le_comap_of_gen (B' := (A : Set K)) (L' := L) (q' := q)
      (DistribSMul.toAddMonoidHom _ c) ?_ hy
    intro b hb v hv
    show c • b • ExteriorAlgebra.ιMulti K q v ∈ _
    rw [smul_smul]
    exact forms_gen_mem (A.mul_mem hc hb) v hv
  · intro B q c y hy
    refine forms_le_comap_of_gen (B' := (fun b => c * b) '' B) (L' := L) (q' := q)
      (DistribSMul.toAddMonoidHom _ c) ?_ hy
    intro b hb v hv
    show c • b • ExteriorAlgebra.ιMulti K q v ∈ _
    rw [smul_smul]
    exact forms_gen_mem (B := (fun b => c * b) '' B) (Set.mem_image_of_mem _ hb) v hv
  · intro B B' L' q hB hL
    refine (forms_le_comap_of_gen (B' := B') (L' := L') (q' := q) (AddMonoidHom.id _) ?_)
    intro b hb v hv
    exact forms_gen_mem (hB hb) v (fun k => hL (hv k))

end

end GlobalTheory.DI
end
