module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle001
public import Mathlib.Data.Nat.Prime.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle018
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle020
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.Interleave
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.WedgeSub
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelL2RowsColumns
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.PosDef
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
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Algebra.CharP.Lemmas
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.Order.Chebyshev

@[expose] public section

section

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.PerfectRing

theorem pf_facts : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A], Pf p A →
    (∃ F : A ≃+* A, ∀ x, F x = x ^ p) ∧ (∀ (x : A) (n : ℕ), x ^ n = 0 → x = 0) ∧
    (∀ (k : ℕ) (x : A), ∃ y, y ^ p ^ k = x) ∧ (∀ (k : ℕ) (x y : A), x ^ p ^ k = y ^ p ^ k → x = y) ∧
    ∀ r : ℕ → A, IsRt p r → (∀ k, ∃ c, r k = c * r (k + 1) * r (k + 1)) ∧ (∀ k, r k ^ p ^ k = r 0) ∧
      ∀ (N : ℕ) (x : A), r 0 ^ N * x = 0 → ∀ k, r k * x = 0 := by
  intro p _ A _ h
  have hp : p.Prime := Fact.out
  have hadd : ∀ x y : A, (x + y) ^ p = x ^ p + y ^ p := by
    intro x y
    obtain ⟨c, hc⟩ := exists_add_pow_prime_eq hp x y
    rw [hc, h.char]
    simp
  let F : A →+* A :=
    { toFun := fun x => x ^ p
      map_one' := one_pow p
      map_mul' := fun x y => mul_pow x y p
      map_zero' := zero_pow hp.ne_zero
      map_add' := hadd }
  have hk : ∀ k : ℕ, Function.Bijective fun x : A => x ^ p ^ k := by
    intro k
    induction k with
    | zero =>
      simp only [pow_zero, pow_one]
      exact Function.bijective_id
    | succ k ih =>
      have : (fun x : A => x ^ p ^ (k + 1)) = (fun x : A => x ^ p) ∘ (fun x : A => x ^ p ^ k) := by
        funext x
        simp only [Function.comp_apply]
        rw [pow_succ, pow_mul]
      rw [this]
      exact h.bij.comp ih
  have hinj : ∀ (k : ℕ) (x y : A), x ^ p ^ k = y ^ p ^ k → x = y := fun k x y e => (hk k).1 e
  have hred : ∀ (x : A) (n : ℕ), x ^ n = 0 → x = 0 := by
    intro x n e
    apply hinj n
    have hlt : n < p ^ n := Nat.lt_pow_self hp.one_lt
    rw [pow_eq_zero_of_le hlt.le e, zero_pow (pow_ne_zero n hp.ne_zero)]
  refine ⟨⟨RingEquiv.ofBijective F h.bij, fun x => rfl⟩, hred, fun k x => (hk k).2 x, hinj, ?_⟩
  intro r hr
  have hroot : ∀ k, r k ^ p ^ k = r 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', pow_mul, hr k, ih]
  refine ⟨?_, hroot, ?_⟩
  · intro k
    refine ⟨r (k + 1) ^ (p - 2), ?_⟩
    have h2 : p = (p - 2) + 1 + 1 := by have := hp.two_le; omega
    conv_lhs => rw [← hr k, h2]
    rw [pow_succ, pow_succ]
  · intro N x e k
    apply hred _ (p ^ k * N + 1)
    calc (r k * x) ^ (p ^ k * N + 1)
        = r k ^ (p ^ k * N + 1) * x ^ (p ^ k * N + 1) := mul_pow _ _ _
      _ = r k * x ^ (p ^ k * N) * (r 0 ^ N * x) := by
          rw [pow_succ (r k), pow_mul, hroot k, pow_succ x]
          ring
      _ = 0 := by rw [e, mul_zero]

end GlobalTheory.CompanionTheory.PerfectRing
end

section

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.PerfClos

theorem exists_PQ : ∀ (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] (I : Ideal S), (p : S) = 0 →
    ∃ (T : Type) (_ : CommRing T) (i : S →+* T), PQ p i I := by
  intro p hpf S _ I hp
  obtain ⟨T, inst, i, hc, hb, hpow, hker⟩ := exists_perfect_radical p S I hp
  refine ⟨T, inst, i, ⟨⟨hc, hb⟩, hpow, fun x => ?_⟩⟩
  rw [hker x]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, Ideal.pow_mem_of_pow_mem I hn ?_⟩
    exact (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le
  · rintro ⟨k, hk⟩
    exact ⟨p ^ k, hk⟩

end GlobalTheory.CompanionTheory.PerfClos
end

section

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.CovCmp

theorem one_tmul_mem_range_iff {A : Type} [CommRing A] (B' : Type) [CommRing B'] [Algebra A B']
    {K₁ K₀ : Type} [AddCommGroup K₁] [Module A K₁] [AddCommGroup K₀] [Module A K₀]
    (d : K₁ →ₗ[A] K₀) (z : K₀) :
    ((1 : B') ⊗ₜ[A] z) ∈ LinearMap.range (d.lTensor B') ↔
      (1 : B') ⊗ₜ[A] ((LinearMap.range d).mkQ z) = 0 := by
  have hex := lTensor_exact B' (LinearMap.exact_map_mkQ_range d)
    (Submodule.mkQ_surjective (LinearMap.range d))
  have := hex ((1 : B') ⊗ₜ[A] z)
  rw [LinearMap.lTensor_tmul] at this
  exact this.symm

theorem cov_of_solv : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (r : ℕ → A), (∀ (m n : ℕ) (a : Fin m → Fin n → A) (c : Fin m → A), Solv B a c → ∃ (B₁ : Type) (_ : CommRing B₁) (_ : Algebra A B₁), Cov p r B₁ ∧ Solv B₁ a c) → Cov p r B := by
  intro p _ A _ B _ _ r h K₁ K₀ _ _ _ _ h₁ h₀ d hd z hz k
  have hB := (one_tmul_mem_range_iff B d z).mp hz
  obtain ⟨m, n, a, c, hs, hall⟩ := GlobalTheory.CompanionTheory.EqCrit.exists_system B ((LinearMap.range d).mkQ z) hB
  obtain ⟨B₁, i₁, i₂, hc, hs₁⟩ := h m n a c hs
  have h0 := hall B₁ hs₁
  exact hc K₁ K₀ h₁ h₀ d hd z ((one_tmul_mem_range_iff B₁ d z).mpr h0) k

end GlobalTheory.CompanionTheory.CovCmp
end

section

open Zc.Comb

universe u

namespace GlobalTheory.CompanionTheory.Comb

theorem interleave_perm_append {T : Type u} {u v w : List T} (h : Interleave u v w) :
    w.Perm (u ++ v) := by
  induction h with
  | nil => exact List.Perm.refl _
  | left _ ih => exact ih.cons _
  | right _ ih => exact (ih.cons _).trans List.perm_middle.symm

theorem shuffle_perm_flatten {T : Type u} (us : List (List T)) (w : List T)
    (h : Shuffle us w) : w.Perm us.flatten := by
  induction h with
  | nil => exact List.Perm.refl _
  | cons _ hi ih =>
    rw [List.flatten_cons]
    exact (interleave_perm_append hi).trans (ih.append_left _)

end GlobalTheory.CompanionTheory.Comb
end

section

open Zc.Comb

universe u

namespace GlobalTheory.CompanionTheory.SegOrder

variable {T : Type u}

theorem exists_last_start (s : T → T) (hs : ∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t)
    (m : Multiset (ASeg T)) (hm : m ≠ 0) :
    ∃ a ∈ m, ∀ b ∈ m, ¬ ∃ j : ℕ, 0 < j ∧ b.start = s^[j] a.start := by
  have irr : ∀ a : ASeg T, ¬ ∃ j : ℕ, 0 < j ∧ a.start = s^[j] a.start := by
    rintro a ⟨j, hj, h⟩
    exact hs a.start j hj h.symm
  induction m using Multiset.induction_on with
  | empty => exact absurd rfl hm
  | cons x m ih =>
    by_cases hm' : m = 0
    · subst hm'
      refine ⟨x, Multiset.mem_cons_self x 0, ?_⟩
      intro b hb
      have hbx : b = x := by simpa using hb
      subst hbx
      exact irr b
    · obtain ⟨a, ham, hmax⟩ := ih hm'
      by_cases hax : ∃ j : ℕ, 0 < j ∧ x.start = s^[j] a.start
      · obtain ⟨j, hj, hxa⟩ := hax
        refine ⟨x, Multiset.mem_cons_self x m, ?_⟩
        intro b hb
        rcases Multiset.mem_cons.mp hb with rfl | hbm
        · exact irr b
        · rintro ⟨i, hi, hbx⟩
          refine hmax b hbm ⟨i + j, by omega, ?_⟩
          rw [hbx, hxa, Function.iterate_add_apply]
      · refine ⟨a, Multiset.mem_cons_of_mem ham, ?_⟩
        intro b hb
        rcases Multiset.mem_cons.mp hb with rfl | hbm
        · exact hax
        · exact hmax b hbm

theorem exists_ordered_form : ∀ {T : Type u} (s : T → T), Function.Injective s →
    (∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t) →
    ∀ m : Multiset (ASeg T), ∃ L : List (ASeg T), (L : Multiset (ASeg T)) = m ∧ AOrdered s L := by
  classical
  intro T s _ hs m
  induction hn : Multiset.card m generalizing m with
  | zero =>
    refine ⟨[], ?_, List.Pairwise.nil⟩
    simpa using (Multiset.card_eq_zero.mp hn).symm
  | succ n ih =>
    have hm : m ≠ 0 := by
      rintro rfl
      simp at hn
    obtain ⟨a, ham, hmax⟩ := exists_last_start s hs m hm
    have hcard : Multiset.card (m.erase a) = n := by
      rw [Multiset.card_erase_of_mem ham, hn]
      rfl
    obtain ⟨L, hL, hord⟩ := ih (m.erase a) hcard
    refine ⟨a :: L, ?_, ?_⟩
    · rw [← Multiset.cons_coe, hL]
      exact Multiset.cons_erase ham
    · refine List.pairwise_cons.mpr ⟨?_, hord⟩
      intro b hb hprec
      have hbm : b ∈ m := by
        have : b ∈ (L : Multiset (ASeg T)) := by simpa using hb
        rw [hL] at this
        exact Multiset.mem_of_mem_erase this
      exact hmax b hbm hprec.2

end GlobalTheory.CompanionTheory.SegOrder
end

section

noncomputable section

open Matrix PositivityTheory.Rg.BcB.D1
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.GramWedge

theorem star_dotProduct_self {α : Type} [Fintype α] (w : α → ℂ) :
    star w ⬝ᵥ w = ((∑ i, ‖w i‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  simpa using Complex.conj_mul' (w i)

theorem norm_entry_le_sz {ι ι' : Type} [Fintype ι] [Fintype ι'] (g : Matrix ι' ι ℂ) (a : ι') (b : ι) :
    ‖g a b‖ ≤ sz g :=
  le_ciSup (f := fun p : ι' × ι => ‖g p.1 p.2‖) (Set.finite_range _).bddAbove (a, b)

theorem sum_norm_mulVec_sq_le {ι ι' : Type} [Fintype ι] [Fintype ι'] (g : Matrix ι' ι ℂ) (v : ι → ℂ) :
    ∑ a, ‖(g *ᵥ v) a‖ ^ 2 ≤
      (Fintype.card ι * Fintype.card ι' : ℝ) * sz g ^ 2 * ∑ b, ‖v b‖ ^ 2 := by
  have row : ∀ a, ‖(g *ᵥ v) a‖ ^ 2 ≤ (Fintype.card ι : ℝ) * sz g ^ 2 * ∑ b, ‖v b‖ ^ 2 := by
    intro a
    have h1 : ‖(g *ᵥ v) a‖ ≤ sz g * ∑ b, ‖v b‖ := by
      rw [Finset.mul_sum]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (norm_entry_le_sz g a b) (norm_nonneg _)
    have h2 : (∑ b, ‖v b‖) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ b, ‖v b‖ ^ 2 := by
      simpa using sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι)) (f := fun b => ‖v b‖)
    calc ‖(g *ᵥ v) a‖ ^ 2 ≤ (sz g * ∑ b, ‖v b‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = sz g ^ 2 * (∑ b, ‖v b‖) ^ 2 := mul_pow _ _ _
      _ ≤ sz g ^ 2 * ((Fintype.card ι : ℝ) * ∑ b, ‖v b‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
      _ = _ := by ring
  calc ∑ a, ‖(g *ᵥ v) a‖ ^ 2
      ≤ ∑ _a : ι', (Fintype.card ι : ℝ) * sz g ^ 2 * ∑ b, ‖v b‖ ^ 2 := Finset.sum_le_sum fun a _ => row a
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

theorem posSemidef_smul_gram_sub {ι ι' κ : Type} [Fintype ι] [Fintype ι'] [Fintype κ] [DecidableEq κ]
    (g : Matrix ι' ι ℂ) (A : Matrix ι κ ℂ) :
    (((((Fintype.card ι * Fintype.card ι' : ℝ) * sz g ^ 2 : ℝ) : ℂ) • (Aᴴ * A)) -
      (g * A)ᴴ * (g * A)).PosSemidef := by
  set c : ℝ := (Fintype.card ι * Fintype.card ι' : ℝ) * sz g ^ 2 with hc
  have hG : (Aᴴ * A).IsHermitian := isHermitian_conjTranspose_mul_self A
  have hH : ((g * A)ᴴ * (g * A)).IsHermitian := isHermitian_conjTranspose_mul_self _
  refine PosSemidef.of_dotProduct_mulVec_nonneg
    ((hG.smul (show star (c : ℂ) = c from Complex.conj_ofReal c)).sub hH) fun x => ?_
  have e : ∀ {α : Type} [Fintype α] (B : Matrix α κ ℂ),
      star x ⬝ᵥ ((Bᴴ * B) *ᵥ x) = star (B *ᵥ x) ⬝ᵥ (B *ᵥ x) := by
    intro α _ B
    rw [← mulVec_mulVec, star_mulVec, dotProduct_mulVec]
  have e1 := e A
  have e2 : star x ⬝ᵥ (((g * A)ᴴ * (g * A)) *ᵥ x) = star (g *ᵥ (A *ᵥ x)) ⬝ᵥ (g *ᵥ (A *ᵥ x)) := by
    rw [e (g * A), mulVec_mulVec]
  rw [sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul, e1, e2, star_dotProduct_self,
    star_dotProduct_self, smul_eq_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sub]
  exact Complex.zero_le_real.2 (sub_nonneg.2 (sum_norm_mulVec_sq_le g (A *ᵥ x)))

theorem gram_mul_det {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℂ) (s : Matrix κ κ ℂ) :
    ((A * s)ᴴ * (A * s)).det = ((‖s.det‖ ^ 2 : ℝ) : ℂ) * (Aᴴ * A).det := by
  have h : star s.det * s.det = ((‖s.det‖ ^ 2 : ℝ) : ℂ) := by
    simpa using Complex.conj_mul' s.det
  rw [conjTranspose_mul, show sᴴ * Aᴴ * (A * s) = sᴴ * (Aᴴ * A) * s by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc],
    det_mul, det_mul, det_conjTranspose, ← h]
  ring

theorem mulI_of_detMono : DetMono → MulI := by
  intro hm ι ι' κ _ _ _ _ A
  refine ⟨fun g => ?_, fun s => ?_, fun s => ?_⟩
  · have h := hm κ _ _ (posSemidef_conjTranspose_mul_self (g * A)) (posSemidef_smul_gram_sub g A)
    rw [det_smul, ← Complex.ofReal_pow, Complex.re_ofReal_mul] at h
    exact h
  · simp only [nI]
    rw [gram_mul_det, Complex.re_ofReal_mul, mul_comm]
  · have h := gram_mul_det (1 : Matrix κ κ ℂ) s
    simp only [Matrix.one_mul, conjTranspose_one, Matrix.mul_one, det_one, mul_one] at h
    simp only [nI]
    rw [h, Complex.ofReal_re]

end GlobalTheory.CompanionTheory.GramWedge

end
end

section

open Matrix PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.Wedge


open ComplexOrder in
theorem pairI_of_detMono : DetMono → PairI := by
  open scoped ComplexOrder in
  intro hD ι κ _ _ _ U W
  have hG : (Uᴴ * U).PosSemidef := posSemidef_conjTranspose_mul_self U
  have hH : (Wᴴ * W).PosSemidef := posSemidef_conjTranspose_mul_self W
  have hHn : 0 ≤ ((Wᴴ * W).det).re := (Complex.le_def.1 hH.det_nonneg).1
  have hGn : 0 ≤ ((Uᴴ * U).det).re := (Complex.le_def.1 hG.det_nonneg).1
  have hGim : ((Uᴴ * U).det).im = 0 := ((Complex.le_def.1 hG.det_nonneg).2).symm
  unfold nI
  by_cases hdet : (Uᴴ * U).det = 0
  ·
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    have hUv : U *ᵥ v = 0 := by
      have := (Matrix.conjTranspose_mul_self_mulVec_eq_zero U v).1 hv
      exact this
    have hM : ((Uᴴ * W)ᴴ) *ᵥ v = 0 := by
      rw [conjTranspose_mul, conjTranspose_conjTranspose, ← Matrix.mulVec_mulVec, hUv,
        Matrix.mulVec_zero]
    have hd : ((Uᴴ * W)ᴴ).det = 0 := Matrix.exists_mulVec_eq_zero_iff.1 ⟨v, hv0, hM⟩
    have hd' : (Uᴴ * W).det = 0 := by
      rw [det_conjTranspose] at hd
      simpa using hd
    rw [hd', norm_zero]
    have : ((Uᴴ * U).det).re * ((Wᴴ * W).det).re ≥ 0 := mul_nonneg hGn hHn
    simpa using this
  · set G := Uᴴ * U with hGdef
    set M := Uᴴ * W with hMdef
    have hu : IsUnit G.det := isUnit_iff_ne_zero.2 hdet
    have hGi : G * G⁻¹ = 1 := mul_nonsing_inv _ hu
    have hiG : G⁻¹ * G = 1 := nonsing_inv_mul _ hu
    have hGh : Gᴴ = G := hG.isHermitian
    have hih : (G⁻¹)ᴴ = G⁻¹ := by rw [conjTranspose_nonsing_inv, hGh]
    have hMh : Mᴴ = Wᴴ * U := by
      rw [hMdef, conjTranspose_mul, conjTranspose_conjTranspose]
    set T := G⁻¹ * M with hT
    have hTh : Tᴴ = Mᴴ * G⁻¹ := by rw [hT, conjTranspose_mul, hih]
    have hGT : G * T = M := by rw [hT, ← Matrix.mul_assoc, hGi, Matrix.one_mul]
    have hX : (Tᴴ * G * T).PosSemidef := hG.conjTranspose_mul_mul_same T
    have hXe : Tᴴ * G * T = Mᴴ * T := by
      rw [Matrix.mul_assoc, hGT, hTh, Matrix.mul_assoc, ← hT]
    have hXp : (Mᴴ * T).PosSemidef := hXe ▸ hX
    have e1 : Wᴴ * (U * T) = Mᴴ * T := by rw [hMh, Matrix.mul_assoc]
    have e2 : Tᴴ * Uᴴ * W = Mᴴ * T := by
      rw [Matrix.mul_assoc, ← hMdef, hTh, Matrix.mul_assoc, ← hT]
    have e3 : Tᴴ * Uᴴ * (U * T) = Mᴴ * T := by
      rw [← hXe, hGdef]
      simp only [Matrix.mul_assoc]

    have hZ : (W - U * T)ᴴ * (W - U * T) = Wᴴ * W - Mᴴ * T := by
      rw [conjTranspose_sub, conjTranspose_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
        e1, e2, e3]
      abel
    have hmono : ((Mᴴ * T).det).re ≤ ((Wᴴ * W).det).re :=
      hD κ _ _ hXp (hZ ▸ posSemidef_conjTranspose_mul_self (W - U * T))
    have hiGd : (G⁻¹).det * G.det = 1 := by rw [← det_mul, hiG, det_one]
    have hdX : (Mᴴ * T).det * G.det = ((‖M.det‖ ^ 2 : ℝ) : ℂ) := by
      have hc : (starRingEnd ℂ) M.det * M.det = ((‖M.det‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.conj_mul']
        push_cast
        rfl
      rw [det_mul, hT, det_mul, det_conjTranspose, ← hc, Complex.star_def]
      linear_combination ((starRingEnd ℂ) M.det * M.det) * hiGd
    have hre : ((Mᴴ * T).det).re * G.det.re = ‖M.det‖ ^ 2 := by
      have := congrArg Complex.re hdX
      rw [Complex.mul_re, hGim, mul_zero, sub_zero, Complex.ofReal_re] at this
      exact this
    rw [← hre, mul_comm]
    exact mul_le_mul_of_nonneg_left hmono hGn

end GlobalTheory.CompanionTheory.Wedge
end

section

open MeasureTheory
open scoped ENNReal Pointwise
open PositivityTheory.Rg.BcB.E1

namespace GlobalTheory.CompanionTheory.KerSquare

theorem memLp_column (hK : KerBasic) (hC : CntBasic) (hS : ColSq) (X : Ctx) (φ : X.G → ℂ)
    (hφ : Tst φ) (y : X.G) : MemLp (fun x => ker X.Γ φ x y) 2 X.ν := by
  have hcont : Continuous fun x => ker X.Γ φ x y :=
    (hK X φ hφ).2.1.comp (continuous_id.prodMk continuous_const)
  obtain ⟨B, hB⟩ := hφ.1.bounded_above_of_compact_support hφ.2
  have hΩ : IsCompact (tsupport φ) := hφ.2
  have hbound := hS X φ B (tsupport φ) hφ hB hΩ (subset_tsupport φ) y
  have hμ : X.μ (tsupport φ)⁻¹ ≠ ⊤ := hΩ.inv.measure_lt_top.ne
  have hcnt : cnt X.Γ ((tsupport φ)⁻¹ * tsupport φ) y ≠ ⊤ :=
    (hC X).1 _ (hΩ.inv.mul hΩ) y
  have hfin : ENNReal.ofReal B ^ 2 * X.μ (tsupport φ)⁻¹ *
      cnt X.Γ ((tsupport φ)⁻¹ * tsupport φ) y < ⊤ :=
    ENNReal.mul_lt_top
      (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) hμ.lt_top) hcnt.lt_top
  rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top
    (by norm_num) (by norm_num) hcont.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat]
  exact hbound.trans_lt hfin

theorem memLp_row (hK : KerBasic) (hC : CntBasic) (hS : ColSq) (X : Ctx) (φ : X.G → ℂ)
    (hφ : Tst φ) (x : X.G) : MemLp (fun y => ker X.Γ φ x y) 2 X.ν := by
  obtain ⟨-, hcont, -, hadj, hconj, -⟩ := hK X φ hφ
  have hc : Continuous fun y => ker X.Γ φ x y :=
    hcont.comp (continuous_const.prodMk continuous_id)
  refine (memLp_column hK hC hS X (adj φ) hadj x).of_le hc.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  rw [hconj y x, RCLike.norm_conj]

theorem kernel_rows_columns_square_integrable : KerBasic → CntBasic → ColSq → KernelL2RowsColumns := fun hK hC hS X φ hφ =>
  ⟨memLp_column hK hC hS X φ hφ, memLp_row hK hC hS X φ hφ⟩

end GlobalTheory.CompanionTheory.KerSquare
end
