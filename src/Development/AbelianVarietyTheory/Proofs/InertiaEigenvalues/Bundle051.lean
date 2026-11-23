module

public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.RingTheory.WittVector.Frobenius
public import Mathlib.RingTheory.WittVector.Teichmuller
public import Mathlib.RingTheory.WittVector.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
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
public import Mathlib.RingTheory.WittVector.Identities
public import Mathlib.RingTheory.WittVector.InitTail
import Mathlib.RingTheory.WittVector.Complete
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Topology.Order.Basic

@[expose] public section

section

open scoped PowerSeries Pointwise

namespace GlobalTheory

namespace WittIntegrality

open WittVector

variable {C : Type} [Field C] (A : ValuationSubring C)

lemma mem_of_pow_mem {c : C} {k : ℕ} (hk : 1 ≤ k) (h : c ^ k ∈ A) : c ∈ A := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rcases A.mem_or_inv_mem c with hc | hc
  · exact hc
  · by_cases h0 : c = 0
    · rw [h0]; exact A.zero_mem
    · have e : c = c ^ (m + 1) * c⁻¹ ^ m := by
        rw [pow_succ', mul_assoc, ← mul_pow, mul_inv_cancel₀ h0, one_pow, mul_one]
      rw [e]; exact mul_mem h (pow_mem hc _)

variable (p : ℕ) [hp : Fact p.Prime]

noncomputable def S : Subring (WittVector p C) := (WittVector.map (p := p) A.subtype).range

variable {p}

lemma mem_S (x : WittVector p C) : x ∈ S A p ↔ ∀ k, x.coeff k ∈ A := by
  constructor
  · rintro ⟨y, rfl⟩ k
    rw [WittVector.map_coeff]
    exact (y.coeff k).2
  · intro h
    refine ⟨WittVector.mk p fun k => ⟨x.coeff k, h k⟩, ?_⟩
    ext k
    rw [WittVector.map_coeff]
    rfl

lemma teich_mem {c : C} (hc : c ∈ A) : teichmuller p c ∈ S A p := by
  rw [mem_S]
  intro k
  cases k with
  | zero => rwa [teichmuller_coeff_zero]
  | succ k => rw [teichmuller_coeff_pos p c _ (Nat.succ_pos k)]; exact A.zero_mem

variable [CharP C p]

lemma frob_mem {x : WittVector p C} (hx : x ∈ S A p) : frobenius x ∈ S A p := by
  rw [mem_S] at hx ⊢
  intro k
  rw [coeff_frobenius_charP]
  exact pow_mem (hx k) _

lemma mem_of_mul_p_mem {x : WittVector p C} (hx : x * (p : WittVector p C) ∈ S A p) :
    x ∈ S A p := by
  rw [mem_S] at hx ⊢
  intro k
  have := hx (k + 1)
  rw [mul_charP_coeff_succ] at this
  exact mem_of_pow_mem A hp.out.one_lt.le this

variable [PerfectRing C p]

noncomputable def tail (x : WittVector p C) : WittVector p C :=
  WittVector.mk p fun k => (frobeniusEquiv C p).symm (x.coeff (k + 1))

lemma tail_coeff (x : WittVector p C) (k : ℕ) : x.coeff (k + 1) = (tail x).coeff k ^ p := by
  simp only [tail, WittVector.coeff_mk, frobeniusEquiv_symm_pow_p]

lemma decomp (x : WittVector p C) : x = teichmuller p (x.coeff 0) + tail x * p := by
  ext k
  rw [coeff_add_of_disjoint]
  · cases k with
    | zero => rw [teichmuller_coeff_zero, mul_charP_coeff_zero, add_zero]
    | succ k =>
      rw [teichmuller_coeff_pos p _ _ (Nat.succ_pos k), mul_charP_coeff_succ, zero_add, tail_coeff]
  · intro k
    cases k with
    | zero => exact Or.inr (mul_charP_coeff_zero _)
    | succ k => exact Or.inl (teichmuller_coeff_pos p _ _ (Nat.succ_pos k))

lemma key0 {n : Type} [Fintype n] (Y Z B : Matrix n n (WittVector p C))
    (hY : ∀ i j, Y i j ∈ S A p) (hB : ∀ i j, B i j ∈ S A p)
    (h : ∀ i j, frobenius (Z i j) = ∑ a, Y i a * Z a j + B i j) :
    ∀ i j, (Z i j).coeff 0 ∈ A := by
  classical
  have he : ∀ i j, (Z i j).coeff 0 ^ p =
      ∑ a, (Y i a).coeff 0 * (Z a j).coeff 0 + (B i j).coeff 0 := by
    intro i j
    have := congrArg (WittVector.constantCoeff (p := p) (R := C)) (h i j)

    simp only [map_add (f := _), map_sum, map_mul, WittVector.constantCoeff_apply,
    coeff_frobenius_charP] at this
    exact this
  by_contra hne
  push_neg at hne
  obtain ⟨i0, j0, hij⟩ := hne
  obtain ⟨⟨i1, j1⟩, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (n × n))
    (fun q => A.valuation ((Z q.1 q.2).coeff 0)) ⟨(i0, j0), Finset.mem_univ _⟩
  set z1 := (Z i1 j1).coeff 0 with hz1
  have h1 : 1 < A.valuation z1 := by
    have a := hmax (i0, j0) (Finset.mem_univ _)
    have b : ¬ A.valuation ((Z i0 j0).coeff 0) ≤ 1 := by rwa [A.valuation_le_one_iff]
    exact lt_of_lt_of_le (not_le.mp b) a
  have hz1A : z1 ∉ A := by
    rw [← A.valuation_le_one_iff]; exact not_le.mpr h1
  have hz0 : z1 ≠ 0 := fun e => hz1A (e ▸ A.zero_mem)
  have hle : A.valuation (z1 ^ p) ≤ A.valuation z1 := by
    rw [hz1, he i1 j1]
    refine Valuation.map_add_le _ ?_ ?_
    · refine Valuation.map_sum_le _ fun a _ => ?_
      rw [map_mul]
      calc A.valuation ((Y i1 a).coeff 0) * A.valuation ((Z a j1).coeff 0)
          ≤ 1 * A.valuation ((Z a j1).coeff 0) :=
            by gcongr; exact (A.valuation_le_one_iff _).2 ((mem_S A _).1 (hY i1 a) 0)
        _ ≤ A.valuation z1 := by rw [one_mul]; exact hmax (a, j1) (Finset.mem_univ _)
    · exact ((A.valuation_le_one_iff _).2 ((mem_S A _).1 (hB i1 j1) 0)).trans h1.le
  have hpm : z1 ^ (p - 1) ∈ A := by
    rw [← A.valuation_le_one_iff]
    have e : z1 ^ (p - 1) = z1 ^ p * z1⁻¹ := by
      obtain ⟨m, hm⟩ : ∃ m, p = m + 1 := ⟨p - 1, by have := hp.out.one_lt; omega⟩
      rw [hm, Nat.add_sub_cancel, pow_succ, mul_assoc, mul_inv_cancel₀ hz0, mul_one]
    rw [e, map_mul]
    calc A.valuation (z1 ^ p) * A.valuation z1⁻¹ ≤ A.valuation z1 * A.valuation z1⁻¹ :=
          by gcongr
      _ = 1 := by rw [← map_mul, mul_inv_cancel₀ hz0, map_one]
  exact hz1A (mem_of_pow_mem A (by have := hp.out.two_le; omega) hpm)

lemma key {n : Type} [Fintype n] (Y : Matrix n n (WittVector p C)) (hY : ∀ i j, Y i j ∈ S A p) :
    ∀ (k : ℕ) (Z B : Matrix n n (WittVector p C)), (∀ i j, B i j ∈ S A p) →
    (∀ i j, frobenius (Z i j) = ∑ a, Y i a * Z a j + B i j) →
    ∀ i j, (Z i j).coeff k ∈ A := by
  intro k
  induction k with
  | zero => exact fun Z B hB h => key0 A Y Z B hY hB h
  | succ k ih =>
    intro Z B hB h
    have h0 := key0 A Y Z B hY hB h
    let U : Matrix n n (WittVector p C) := fun i j => tail (Z i j)
    let D : Matrix n n (WittVector p C) :=
      fun i j => frobenius (U i j) - ∑ a, Y i a * U a j
    have hD : ∀ i j, D i j * p = ∑ a, Y i a * teichmuller p ((Z a j).coeff 0) + B i j
        - frobenius (teichmuller p ((Z i j).coeff 0)) := by
      intro i j
      have e1 : frobenius (Z i j) = frobenius (teichmuller p ((Z i j).coeff 0))
          + frobenius (U i j) * p := by
        conv_lhs => rw [decomp (Z i j)]
        rw [map_add (f := _), map_mul, map_natCast]
      have e2 : ∑ a, Y i a * Z a j = ∑ a, Y i a * teichmuller p ((Z a j).coeff 0)
          + (∑ a, Y i a * U a j) * p := by
        rw [Finset.sum_mul, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        conv_lhs => rw [decomp (Z a j)]
        ring
      have e4 := h i j
      rw [e1, e2] at e4
      simp only [D]
      linear_combination e4
    have hDm : ∀ i j, D i j ∈ S A p := by
      intro i j
      refine mem_of_mul_p_mem A ?_
      rw [hD]
      exact Subring.sub_mem _ (Subring.add_mem _ (Subring.sum_mem _ fun a _ =>
        Subring.mul_mem _ (hY i a) (teich_mem A (h0 a j))) (hB i j))
        (frob_mem A (teich_mem A (h0 i j)))
    have hU := ih U D hDm (fun i j => by simp only [D]; ring)
    intro i j
    rw [tail_coeff]
    exact pow_mem (hU i j) _

end WittIntegrality

open WittIntegrality in
theorem witt_matrix_coeff_mem_of_frobenius : ∀ (p : ℕ) [Fact p.Prime] {C : Type} [Field C] [CharP C p] [PerfectRing C p] (A : ValuationSubring C) {n : Type} [Fintype n] (Z : Matrix n n (WittVector p C)) (Y : Matrix n n (WittVector p A)), (Z.map WittVector.frobenius = Y.map (WittVector.map A.subtype) * Z ∨ Z.map WittVector.frobenius = Z * Y.map (WittVector.map A.subtype)) → ∀ i j m, (Z i j).coeff m ∈ A := by
  intro p _ C _ _ _ A n _ Z Y h i j m
  rcases h with h | h
  · refine key A (Y.map (WittVector.map A.subtype)) (fun i j => ⟨Y i j, rfl⟩) m Z 0
      (fun _ _ => Subring.zero_mem _) ?_ i j
    intro i j
    have := congrFun (congrFun h i) j
    rw [Matrix.map_apply, Matrix.mul_apply] at this
    rw [this, Matrix.zero_apply, add_zero]
  · refine key A (Y.map (WittVector.map A.subtype)).transpose (fun i j => ⟨Y j i, rfl⟩) m
      Z.transpose 0 (fun _ _ => Subring.zero_mem _) ?_ j i
    intro i j
    have := congrFun (congrFun h j) i
    rw [Matrix.map_apply, Matrix.mul_apply] at this
    rw [Matrix.transpose_apply, this, Matrix.zero_apply, add_zero]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _

end GlobalTheory
end

section

namespace GlobalTheory.Cyc.FontW

def Dv (l r : ℕ) (M : Type*) [AddCommGroup M] : AddSubgroup M :=
  (nsmulAddMonoidHom (l ^ r) : M →+ M).range

theorem mem_Dv {l r : ℕ} {M : Type*} [AddCommGroup M] {x : M} :
    x ∈ Dv l r M ↔ ∃ y, l ^ r • y = x := Iff.rfl

theorem Dv_map {l r : ℕ} {M M' F : Type*} [AddCommGroup M] [AddCommGroup M'] [FunLike F M M']
    [AddMonoidHomClass F M M'] (f : F) {x : M} (hx : x ∈ Dv l r M) : f x ∈ Dv l r M' := by
  obtain ⟨y, rfl⟩ := mem_Dv.1 hx
  exact mem_Dv.2 ⟨f y, (map_nsmul f _ _).symm⟩

theorem Dv_smul {l r : ℕ} {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M] (a : A) {x : M}
    (hx : x ∈ Dv l r M) : a • x ∈ Dv l r M := by
  obtain ⟨y, rfl⟩ := mem_Dv.1 hx
  exact mem_Dv.2 ⟨a • y, smul_comm _ _ _⟩

def Cpl (l : ℕ) (M : Type*) [AddCommGroup M] : Prop :=
  (∀ x : M, (∀ r, x ∈ Dv l r M) → x = 0) ∧
    ∀ f : ℕ → M, (∀ r, f (r + 1) - f r ∈ Dv l r M) → ∃ L, ∀ r, L - f r ∈ Dv l r M

theorem Cpl.equiv {l : ℕ} {M M' : Type*} [AddCommGroup M] [AddCommGroup M'] (e : M ≃+ M')
    (h : Cpl l M') : Cpl l M := by
  refine ⟨fun x hx => ?_, fun f hf => ?_⟩
  · exact e.injective (by rw [map_zero]; exact h.1 _ fun r => Dv_map e (hx r))
  · obtain ⟨L, hL⟩ := h.2 (fun r => e (f r)) fun r => by
      rw [← map_sub]; exact Dv_map e (hf r)
    refine ⟨e.symm L, fun r => ?_⟩
    have := Dv_map e.symm (hL r)
    rwa [map_sub, e.symm_apply_apply] at this

theorem Cpl.pi {l : ℕ} {M : Type*} [AddCommGroup M] (ι : Type*) (h : Cpl l M) : Cpl l (ι → M) := by
  refine ⟨fun x hx => funext fun i => ?_, fun f hf => ?_⟩
  · exact h.1 _ fun r => Dv_map (Pi.evalAddMonoidHom (fun _ : ι => M) i) (hx r)
  · choose L hL using fun i => h.2 (fun r => f r i) fun r =>
      Dv_map (Pi.evalAddMonoidHom (fun _ : ι => M) i) (hf r)
    refine ⟨L, fun r => ?_⟩
    choose y hy using fun i => mem_Dv.1 (hL i r)
    exact mem_Dv.2 ⟨y, funext hy⟩

theorem Cpl.tensor_left {l : ℕ} {R P M : Type*} [CommRing R] [AddCommGroup P] [Module R P]
    [Module.Free R P] [Module.Finite R P] [AddCommGroup M] [Module R M] (h : Cpl l M) :
    Cpl l (TensorProduct R P M) := by
  classical
  let b := Module.Free.chooseBasis R P
  exact Cpl.equiv ((TensorProduct.equivFinsuppOfBasisLeft b).toAddEquiv.trans
    Finsupp.addEquivFunOnFinite) (h.pi _)

theorem Cpl.tensor_right {l : ℕ} {R P M : Type*} [CommRing R] [AddCommGroup P] [Module R P]
    [Module.Free R P] [Module.Finite R P] [AddCommGroup M] [Module R M] (h : Cpl l M) :
    Cpl l (TensorProduct R M P) :=
  Cpl.equiv (TensorProduct.comm R M P).toAddEquiv h.tensor_left

theorem cpl_witt (p : ℕ) [Fact p.Prime] (k : Type*) [CommRing k] [CharP k p] [PerfectRing k p] :
    Cpl p (WittVector p k) := by
  have key : ∀ (r : ℕ) (x : WittVector p k), x ∈ Dv p r (WittVector p k) ↔
      x ∈ ((Ideal.span {(p : WittVector p k)}) ^ r • ⊤ : Submodule (WittVector p k) (WittVector p k)) := by
    intro r x
    rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton', mem_Dv]
    simp [mul_comm]
  refine ⟨fun x hx => ?_, fun f hf => ?_⟩
  · exact IsHausdorff.haus (I := Ideal.span {(p : WittVector p k)}) inferInstance x fun n =>
      SModEq.zero.2 ((key n x).1 (hx n))
  · obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := Ideal.span {(p : WittVector p k)}) inferInstance
      (f := f) ((AdicCompletion.isAdicCauchy_iff _ _ f).2 fun n => by
        rw [SModEq.sub_mem, ← key, ← neg_sub]; exact neg_mem (hf n))
    refine ⟨L, fun r => ?_⟩
    have := hL r
    rw [SModEq.sub_mem, ← key] at this
    rw [← neg_sub]; exact neg_mem this

theorem sum_translate {G X : Type*} [Group G] [AddCommMonoid X] (N : Subgroup G) (S : Finset G)
    (hS : ∀ h, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ N) (f : G → X) (hf : ∀ g, ∀ n ∈ N, f (g * n) = f g) (σ : G) :
    ∑ s ∈ S, f (σ * s) = ∑ s ∈ S, f s := by
  choose π hπ huniq using hS
  refine Finset.sum_nbij' (fun s => π (σ * s)) (fun t => π (σ⁻¹ * t)) (fun s _ => (hπ _).1)
    (fun s _ => (hπ _).1) (fun s hs => ?_) (fun t ht => ?_) (fun s _ => ?_)
  · refine (huniq _ s ⟨hs, ?_⟩).symm
    have := N.inv_mem (hπ (σ * s)).2
    simpa [mul_assoc] using this
  · refine (huniq _ t ⟨ht, ?_⟩).symm
    have := N.inv_mem (hπ (σ⁻¹ * t)).2
    simpa [mul_assoc] using this
  · have := hf (π (σ * s)) _ (hπ (σ * s)).2
    rw [← this]; simp

section Avg

variable {G A M : Type*} [Group G] [CommRing A] [AddCommGroup M] [Module A M] (l : ℕ)
  (𝓕 : Filter G) (a : G → A → A) (ρ : G → M →+ M)

theorem avg_step (amul : ∀ g h β, a (g * h) β = a g (a h β))
    (ρmul : ∀ g h x, ρ (g * h) x = ρ g (ρ h x))
    (semi : ∀ g β x, ρ g (β • x) = a g β • ρ g x)
    (htr : ∀ W ∈ 𝓕, ∃ N : Subgroup G, N.Normal ∧ (N : Set G) ∈ 𝓕 ∧ (N : Set G) ⊆ W ∧
      ∃ S : Finset G, (∀ h, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ N) ∧
        ∃ β, (∀ n ∈ N, a n β = β) ∧ ∑ s ∈ S, a s β = 1)
    (c : G → M) (hc : ∀ g h, c (g * h) = c g + ρ g (c h))
    (hcont : ∀ r, {g | c g ∈ Dv l r M} ∈ 𝓕) (k : ℕ) (hk : ∀ g, c g ∈ Dv l k M) :
    ∃ b ∈ Dv l k M, (∀ r, {g | c g - (ρ g b - b) ∈ Dv l r M} ∈ 𝓕) ∧
      ∀ g, c g - (ρ g b - b) ∈ Dv l (k + 1) M := by
  obtain ⟨N, hN, hNF, hNW, S, hS, β, hβ, hsum⟩ := htr _ (hcont (k + 1))
  have hβ' : ∀ g, ∀ n ∈ N, a (g * n) β = a g β := fun g n hn => by rw [amul, hβ n hn]
  have hρ : ∀ σ, ρ σ (∑ s ∈ S, a s β • c s) = ∑ s ∈ S, a (σ * s) β • ρ σ (c s) := by
    intro σ

    rw [map_sum]
    exact Finset.sum_congr rfl fun s _ => by rw [semi, amul]
  refine ⟨-∑ s ∈ S, a s β • c s, neg_mem (sum_mem fun s _ => Dv_smul _ (hk s)), fun r => ?_,
    fun σ => ?_⟩
  · obtain ⟨N', hN', hNF', hNW', -⟩ := htr _ (hcont r)
    filter_upwards [hNF, hNF'] with n hn hn'
    refine sub_mem (hNW' hn') ?_
    rw [map_neg, hρ, neg_sub_neg, ← Finset.sum_sub_distrib]
    refine sum_mem fun s _ => ?_
    have h1 : n * s = s * (s⁻¹ * n * s) := by group
    have h2 : a (n * s) β = a s β := by
      rw [h1]; exact hβ' _ _ (by simpa using hN.conj_mem n hn s⁻¹)
    rw [h2, ← smul_sub]
    refine Dv_smul _ ?_
    have h3 : c s - ρ n (c s) = c n - ρ s (c (s⁻¹ * n * s)) := by
      have h4 := hc n s
      rw [h1, hc] at h4
      rw [sub_eq_sub_iff_add_eq_add, h4]
    rw [h3]
    exact sub_mem (hNW' hn') (Dv_map _ (hNW' (by simpa using hN'.conj_mem n hn' s⁻¹)))
  · have h1 : ∑ s ∈ S, a (σ * s) β = 1 := by
      rw [sum_translate N S hS (fun g => a g β) hβ' σ, hsum]
    have h2 : c σ - (ρ σ (-∑ s ∈ S, a s β • c s) - -∑ s ∈ S, a s β • c s) =
        ∑ s ∈ S, a (σ * s) β • c (σ * s) - ∑ s ∈ S, a s β • c s := by
      rw [map_neg, hρ]
      simp only [hc, smul_add, Finset.sum_add_distrib, ← Finset.sum_smul, h1, one_smul]
      abel
    rw [h2, ← QuotientAddGroup.eq_iff_sub_mem]
    have h3 := sum_translate N S hS
      (fun g => QuotientAddGroup.mk' (Dv l (k + 1) M) (a g β • c g)) (fun g n hn => by
        rw [hβ' g n hn]
        refine QuotientAddGroup.eq_iff_sub_mem.2 ?_
        rw [hc, smul_add, add_sub_cancel_left]
        exact Dv_smul _ (Dv_map _ (hNW hn))) σ

    rw [← map_sum, ← map_sum] at h3
    exact h3

theorem avg_cob (hM : Cpl l M) (amul : ∀ g h β, a (g * h) β = a g (a h β))
    (ρmul : ∀ g h x, ρ (g * h) x = ρ g (ρ h x))
    (semi : ∀ g β x, ρ g (β • x) = a g β • ρ g x)
    (htr : ∀ W ∈ 𝓕, ∃ N : Subgroup G, N.Normal ∧ (N : Set G) ∈ 𝓕 ∧ (N : Set G) ⊆ W ∧
      ∃ S : Finset G, (∀ h, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ N) ∧
        ∃ β, (∀ n ∈ N, a n β = β) ∧ ∑ s ∈ S, a s β = 1)
    (c : G → M) (hc : ∀ g h, c (g * h) = c g + ρ g (c h))
    (hcont : ∀ r, {g | c g ∈ Dv l r M} ∈ 𝓕) : ∃ b, ∀ g, c g = ρ g b - b := by
  let P : ℕ → M → Prop := fun k b => (∀ r, {g | c g - (ρ g b - b) ∈ Dv l r M} ∈ 𝓕) ∧
      ∀ g, c g - (ρ g b - b) ∈ Dv l k M
  have h0 : P 0 0 := ⟨by simpa using hcont, fun g => mem_Dv.2 ⟨_, by rw [pow_zero, one_smul]⟩⟩
  have hstep : ∀ k b, P k b → ∃ b', P (k + 1) b' ∧ b' - b ∈ Dv l k M := by
    intro k b hb
    obtain ⟨d, hd, h1, h2⟩ := avg_step l 𝓕 a ρ amul ρmul semi htr (fun g => c g - (ρ g b - b))
      (fun g h => by simp only [hc, ρmul, map_sub]; abel) hb.1 k hb.2
    have e : ∀ g, c g - (ρ g (b + d) - (b + d)) = c g - (ρ g b - b) - (ρ g d - d) := fun g => by
      rw [map_add (f := _)]; abel
    refine ⟨b + d, ⟨?_, ?_⟩, by simpa using hd⟩
    · simpa only [e] using h1
    · simpa only [e] using h2
  choose nx hnx using hstep
  let f : (k : ℕ) → {b // P k b} := fun k =>
    Nat.rec ⟨0, h0⟩ (fun k b => ⟨nx k b.1 b.2, (hnx k b.1 b.2).1⟩) k
  obtain ⟨L, hL⟩ := hM.2 (fun k => (f k).1) fun k => (hnx k (f k).1 (f k).2).2
  refine ⟨L, fun g => sub_eq_zero.1 (hM.1 _ fun r => ?_)⟩
  have e : c g - (ρ g L - L) = (c g - (ρ g (f r).1 - (f r).1)) - (ρ g (L - (f r).1) - (L - (f r).1)) := by
    rw [map_sub]; abel
  rw [e]
  exact sub_mem ((f r).2.2 g) (sub_mem (Dv_map _ (hL r)) (hL r))

end Avg

end GlobalTheory.Cyc.FontW
end

section

open Polynomial

namespace GlobalTheory

theorem window_around_last_max : ∀ (β : ℤ → ℝ) (c : ℝ) (h : ℕ), 0 < c → (∀ k, 0 ≤ β k) → (∃ k, β k ≠ 0) → Filter.Tendsto β Filter.cofinite (nhds 0) → ∃ (D E M : ℕ), h ≤ D ∧ M + h ≤ E ∧ 0 < β ((M + h : ℕ) - D) ∧ (∀ k, β k ≤ β ((M + h : ℕ) - D)) ∧ (∀ k, ((M + h : ℕ) : ℤ) - D < k → β k < β ((M + h : ℕ) - D)) ∧ ∀ k : ℤ, (k < -(D : ℤ) ∨ (E : ℤ) - D < k) → β k ≤ c * β ((M + h : ℕ) - D) := by
  intro β c h hc hβ0 hne hlim
  have hfin : ∀ ε : ℝ, 0 < ε → {k | ε ≤ β k}.Finite := by
    intro ε hε
    have h1 : ∀ᶠ k in Filter.cofinite, β k < ε := hlim.eventually (gt_mem_nhds hε)
    rw [Filter.eventually_cofinite] at h1
    simpa [not_lt] using h1
  obtain ⟨k₀, hk₀⟩ := hne
  have hpos : 0 < β k₀ := lt_of_le_of_ne (hβ0 k₀) (Ne.symm hk₀)
  set T := (hfin _ hpos).toFinset with hT
  have hk₀T : k₀ ∈ T := by simp [T]
  obtain ⟨m, hmT, hm⟩ := T.exists_max_image β ⟨k₀, hk₀T⟩
  have hmax : ∀ k, β k ≤ β m := by
    intro k
    by_cases hk : β k₀ ≤ β k
    · exact hm k (by simp [T, hk])
    · push_neg at hk
      have : β k₀ ≤ β m := hm k₀ hk₀T
      linarith
  set U := T.filter (fun k => β k = β m) with hU
  have hmU : m ∈ U := Finset.mem_filter.2 ⟨hmT, rfl⟩
  set N := U.max' ⟨m, hmU⟩ with hNdef
  have hNU : N ∈ U := U.max'_mem _
  have hN : β N = β m := (Finset.mem_filter.1 hNU).2
  have hk₀m : β k₀ ≤ β m := hm k₀ hk₀T
  have hNlast : ∀ k, N < k → β k < β N := by
    intro k hk
    rcases lt_or_eq_of_le (hmax k) with h1 | h1
    · rw [hN]; exact h1
    · exfalso
      have hkU : k ∈ U := by
        refine Finset.mem_filter.2 ⟨?_, h1⟩
        simp [T]; linarith
      have := U.le_max' k hkU
      omega
  have hc₀ : 0 < β N := by rw [hN]; linarith
  have hcpos : 0 < c * β N := mul_pos hc hc₀
  set F := (hfin _ hcpos).toFinset with hF
  set B : ℕ := (F.image (fun k => k.natAbs)).sup id ⊔ N.natAbs with hB
  have hNB : N.natAbs ≤ B := le_sup_right
  have hFB : ∀ k, c * β N ≤ β k → k.natAbs ≤ B := by
    intro k hk
    have hkF : k ∈ F := by simp [F, hk]
    have : k.natAbs ≤ (F.image (fun k => k.natAbs)).sup id :=
      Finset.le_sup (f := id) (Finset.mem_image_of_mem _ hkF)
    exact le_trans this le_sup_left
  refine ⟨B + h, B + h + B, (N + B).toNat, ?_⟩
  have hx : ((((N + (B : ℤ)).toNat + h : ℕ)) : ℤ) - ((B + h : ℕ) : ℤ) = N := by omega
  rw [hx]
  refine ⟨by omega, by omega, hc₀, fun k => hN ▸ hmax k, fun k hk => hNlast k hk, ?_⟩
  intro k hk
  by_contra hlt
  push_neg at hlt
  have := hFB k hlt.le
  omega

end GlobalTheory
end
