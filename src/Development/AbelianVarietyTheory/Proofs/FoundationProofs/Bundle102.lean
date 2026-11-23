module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle069
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle034
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumEqZeroAddUnits
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle023
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle070
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle026
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle072
public import Mathlib.NumberTheory.ModularForms.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle067
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle068
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle063
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
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

@[expose] public section

section

open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

open Classical in
open scoped BigOperators in
private lemma submodule_toAddSubgroup_inf {R X : Type} [CommRing R] [AddCommGroup X] [Module R X]
    (A B : Submodule R X) : (A ⊓ B).toAddSubgroup = A.toAddSubgroup ⊓ B.toAddSubgroup := by
  ext; simp


open Classical in
open scoped BigOperators in
theorem _root_.GlobalTheory.FinWeil.sumOp_comp_of_adj_of_inf_eq : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, _root_.GlobalTheory.FinWeil.IsHeis σ w γ W → ∀ lam : ℕ →* ℂ, _root_.GlobalTheory.FinWeil.GoodNorm σ lam → ∀ (A B C : Submodule R X), _root_.GlobalTheory.FinWeil.SelfDual γ A → _root_.GlobalTheory.FinWeil.SelfDual γ B → _root_.GlobalTheory.FinWeil.SelfDual γ C → _root_.GlobalTheory.FinWeil.Adj A B → _root_.GlobalTheory.FinWeil.idx A C ≠ 0 → A ⊓ C = B ⊓ C → ∀ v, _root_.GlobalTheory.FinWeil.Fixes W A v → _root_.GlobalTheory.FinWeil.sumOp W B C (_root_.GlobalTheory.FinWeil.sumOp W A B v) = lam (_root_.GlobalTheory.FinWeil.idx A B) • _root_.GlobalTheory.FinWeil.sumOp W A C v := by
  intro R X M _ _ _ _ _ σ w γ W hW lam hlam A B C hA hB hC hAdj hAC hinf v hv
  have hA' : ∀ y, y ∈ A ↔ ∀ a ∈ A, γ y a = 1 := hA
  have hB' : ∀ y, y ∈ B ↔ ∀ b ∈ B, γ y b = 1 := hB
  have hC' : ∀ y, y ∈ C ↔ ∀ c ∈ C, γ y c = 1 := hC
  have hv' : ∀ a ∈ A, W a v = v := hv
  have hlam' : (∀ n : ℕ, n ≠ 0 → lam n ≠ 0) ∧ ∀ P : Ideal R, P.IsMaximal → Finite (R ⧸ P) →
      lam (Nat.card (R ⧸ P)) ^ 2 = (Nat.card (R ⧸ P) : ℂ) ∧ ((∀ r ∈ P, σ r ∈ P) →
        lam (Nat.card (R ⧸ P)) = -(Real.sqrt (Nat.card (R ⧸ P)) : ℂ) ∧ ∃ r, σ r - r ∉ P) := hlam
  obtain ⟨x, hx, P, hP, hfin, hxP, hBle⟩ : ∃ x ∈ B, ∃ P : Ideal R, P.IsMaximal ∧ Finite (R ⧸ P) ∧
      (∀ r : R, r • x ∈ A ↔ r ∈ P) ∧ B ≤ (A ⊓ B) ⊔ Submodule.span R {x} := hAdj
  obtain ⟨hAB, -, hrep, -, -⟩ :=
    _root_.GlobalTheory.FinWeil.adjacent_selfDual_simple hW A B hA hB x hx P hP hfin hxP hBle
  haveI := Fintype.ofFinite (R ⧸ P)
  have hN : Nat.card (R ⧸ P) ≠ 0 := Nat.card_pos.ne'
  have hu : _root_.GlobalTheory.FinWeil.sumOp W A B v = ∑ q : R ⧸ P, W (Quotient.out q • x) v :=
    (_root_.GlobalTheory.FinWeil.sumOp_eq_sum_transversal hW A B hB v hv (R ⧸ P) (fun q => Quotient.out q • x)
      (fun q => B.smul_mem _ hx) hrep).1
  have huB : _root_.GlobalTheory.FinWeil.Fixes W B (_root_.GlobalTheory.FinWeil.sumOp W A B v) :=
    ((_root_.GlobalTheory.FinWeil.sumOp_transversal hW A B hB).2.1 (hAB ▸ hN)).2.1 v hv
  obtain ⟨n, f, hfC, hfrep⟩ := _root_.GlobalTheory.FinWeil.exists_transversal_of_idx_ne_zero A C hAC
  have hfrepB : ∀ c ∈ C, ∃! i, c - f i ∈ B := by
    intro c hc
    have key : ∀ i, c - f i ∈ A ↔ c - f i ∈ B := fun i => by
      have hm : c - f i ∈ C := C.sub_mem hc (hfC i)
      constructor
      · intro h
        have h' : c - f i ∈ A ⊓ C := Submodule.mem_inf.2 ⟨h, hm⟩
        rw [hinf] at h'
        exact (Submodule.mem_inf.1 h').1
      · intro h
        have h' : c - f i ∈ B ⊓ C := Submodule.mem_inf.2 ⟨h, hm⟩
        rw [← hinf] at h'
        exact (Submodule.mem_inf.1 h').1
    simpa only [key] using hfrep c hc
  have hBC := (_root_.GlobalTheory.FinWeil.sumOp_eq_sum_transversal hW B C hC _ huB (Fin n) f hfC hfrepB).1
  have hACsum := (_root_.GlobalTheory.FinWeil.sumOp_eq_sum_transversal hW A C hC v hv (Fin n) f hfC hfrep).1
  have hSfix : ∀ c ∈ C, W c (_root_.GlobalTheory.FinWeil.sumOp W A C v) = _root_.GlobalTheory.FinWeil.sumOp W A C v :=
    ((_root_.GlobalTheory.FinWeil.sumOp_transversal hW A C hC).2.1 hAC).2.1 v hv

  have hmemE : ∀ y, y ∈ (A ⊓ C).toAddSubgroup ↔ y ∈ A ∧ y ∈ C := fun y => by
    simp only [Submodule.mem_toAddSubgroup, Submodule.mem_inf]
  have hEC : (A ⊓ C).toAddSubgroup.relIndex C.toAddSubgroup ≠ 0 := by
    rw [submodule_toAddSubgroup_inf, AddSubgroup.inf_relIndex_right]
    exact hAC
  have hEA := (_root_.GlobalTheory.FinWeil.perfect_pairing_quotients hW (A ⊓ C).toAddSubgroup A.toAddSubgroup
    (A ⊓ C).toAddSubgroup C.toAddSubgroup
    (fun a ha => by
      simp only [Submodule.mem_toAddSubgroup] at ha
      rw [hmemE, hC' a]
      exact ⟨fun h => h.2, fun h => ⟨ha, h⟩⟩)
    (fun t ht => by
      simp only [Submodule.mem_toAddSubgroup] at ht
      rw [hmemE, hA' t]
      exact ⟨fun h a ha => hW.swap_eq_one (h.1 a ha),
        fun h => ⟨fun a ha => hW.swap_eq_one (h a ha), ht⟩⟩)
    hEC).1
  have hdual := (_root_.GlobalTheory.FinWeil.perfect_pairing_quotients hW (A ⊓ C).toAddSubgroup C.toAddSubgroup
    (A ⊓ C).toAddSubgroup A.toAddSubgroup
    (fun c hc => by
      simp only [Submodule.mem_toAddSubgroup] at hc
      rw [hmemE, hA' c]
      exact ⟨fun h => h.1, fun h => ⟨h, hc⟩⟩)
    (fun t ht => by
      simp only [Submodule.mem_toAddSubgroup] at ht
      rw [hmemE, hC' t]
      exact ⟨fun h c hc => hW.swap_eq_one (h.2 c hc),
        fun h => ⟨ht, fun c hc => hW.swap_eq_one (h c hc)⟩⟩)
    (hEA ▸ hEC)).2.1

  obtain ⟨a, ha, hxa⟩ := hdual x (fun c _ hcE => by
    have hcBC : c ∈ B ⊓ C := by
      rw [← hinf]
      exact Submodule.mem_inf.2 ((hmemE c).1 hcE)
    exact hW.iso hB (Submodule.mem_inf.1 hcBC).1 hx)
  simp only [Submodule.mem_toAddSubgroup] at ha
  have hc₀ : x - a ∈ C := by
    rw [hC']
    intro c hc
    apply hW.swap_eq_one
    rw [sub_eq_add_neg, hW.add_right, hW.neg_right, hxa c hc,
      mul_inv_cancel₀ (hW.ne_zero c a)]
  obtain ⟨c₀, hc₀C, hxac⟩ : ∃ c₀ ∈ C, x = a + c₀ := ⟨x - a, hc₀, by abel⟩

  obtain ⟨χ, hχ⟩ : ∃ χ : R → ℂ, ∀ t, χ t = γ a (t • c₀) := ⟨fun t => γ a (t • c₀), fun _ => rfl⟩
  have hχne : ∀ t, χ t ≠ 0 := fun t => by rw [hχ]; exact hW.ne_zero _ _
  have hχadd : ∀ s t, χ (s + t) = χ s * χ t := fun s t => by
    rw [hχ, hχ, hχ, add_smul, hW.add_right]
  have hχ0 : χ 0 = 1 := by rw [hχ, zero_smul]; exact hW.zero_right a
  have hχx : ∀ t, χ t = γ a (t • x) := fun t => by
    rw [hχ, hxac, smul_add, hW.add_right,
      hW.iso hA ha (A.smul_mem t ha), one_mul]
  have hχP : ∀ r ∈ P, χ r = 1 := fun r hr => by
    rw [hχx]
    exact hW.iso hA ha ((hxP r).2 hr)
  have hχσ : ∀ t, χ (σ t) = χ t := fun t => by
    have h1 : γ (t • a) c₀ * γ (t • c₀) a = 1 := by
      have h0 := hW.iso hB (B.smul_mem t hx) hx
      rw [hxac, smul_add, hW.add_left, hW.add_right,
        hW.add_right,
        hW.iso hA (A.smul_mem t ha) ha,
        hW.iso hC (C.smul_mem t hc₀C) hc₀C] at h0
      simpa only [one_mul, mul_one] using h0
    rw [hW.swap a (t • c₀), ← hχ] at h1
    rw [hχ, ← hW.adj t a c₀]
    exact (mul_inv_eq_one₀ (hχne t)).1 h1
  have hχnt : ∃ t, χ t ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    have haB : a ∈ B := by
      rw [hB']
      intro b hb
      obtain ⟨d, hd, y, hy, rfl⟩ := Submodule.mem_sup.1 (hBle hb)
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hy
      rw [hW.add_right,
        hW.iso hA ha (Submodule.mem_inf.1 hd).1, ← hχx,
        hcon, one_mul]
    have hc₀A : c₀ ∈ A := by
      have h1 : c₀ ∈ B ⊓ C := by
        refine Submodule.mem_inf.2 ⟨?_, hc₀C⟩
        have h2 := B.sub_mem hx haB
        rwa [hxac, add_sub_cancel_left] at h2
      rw [← hinf] at h1
      exact (Submodule.mem_inf.1 h1).1
    have h3 : (1 : R) • x ∈ A := by
      rw [one_smul, hxac]
      exact A.add_mem ha hc₀A
    exact hP.ne_top ((Ideal.eq_top_iff_one P).2 ((hxP 1).1 h3))
  have hσP : ∀ r ∈ P, σ r ∈ P := by
    intro r hr
    by_contra hσr
    obtain ⟨s, i, hi, hsi⟩ := hP.exists_inv hσr
    obtain ⟨t, ht⟩ := hχnt
    apply ht
    have h1 : t = t * i + σ (r * σ (t * s)) := by
      rw [map_mul, hW.sg_sg]
      linear_combination (-t) * hsi
    rw [h1, hχadd, hχP _ (P.mul_mem_left t hi), hχσ, hχP _ (P.mul_mem_right _ hr), one_mul]

  have hterm : ∀ s : R, W (s • x) v = χ (w * s * σ s) • W (s • c₀) v := fun s => by
    have hcomp := hW.comp (s • c₀) (s • a) v
    rw [hv' _ (A.smul_mem s ha), ← smul_add, add_comm c₀ a, ← hxac] at hcomp
    have e : γ (w • s • c₀) (s • a) = (χ (w * s * σ s))⁻¹ := by
      rw [hW.swap (s • a) (w • s • c₀), hW.adj s a,
        smul_smul, smul_smul, hχ, show σ s * w * s = w * s * σ s by ring]
    rw [hcomp, e, smul_smul, mul_inv_cancel₀ (hχne _), one_smul]

  have hshift : ∀ c ∈ C, ∑ i, W (f i) (W c v) = _root_.GlobalTheory.FinWeil.sumOp W A C v := by
    intro c hc
    have h1 : ∀ i, W (f i) (W c v) = W c (W (f i) v) := fun i => by
      rw [hW.comm,
        hW.iso hC (hfC i) hc, one_smul]

    rw [Finset.sum_congr rfl (fun i _ => h1 i), ← map_sum, ← hACsum]
    exact hSfix c hc
  have hstep : ∀ i, W (f i) (∑ q : R ⧸ P, W (Quotient.out q • x) v) =
      ∑ q : R ⧸ P, χ (w * Quotient.out q * σ (Quotient.out q)) •
        W (f i) (W (Quotient.out q • c₀) v) := fun i => by

    rw [map_sum]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [hterm, map_smul]
  have hstep' : ∀ q : R ⧸ P, ∑ i, χ (w * Quotient.out q * σ (Quotient.out q)) •
      W (f i) (W (Quotient.out q • c₀) v) =
        χ (w * Quotient.out q * σ (Quotient.out q)) • _root_.GlobalTheory.FinWeil.sumOp W A C v :=
    fun q => by rw [← Finset.smul_sum, hshift _ (C.smul_mem _ hc₀C)]
  rw [hBC, hu, Finset.sum_congr rfl (fun i _ => hstep i), Finset.sum_comm,
    Finset.sum_congr rfl (fun q _ => hstep' q), ← Finset.sum_smul]
  congr 1
  rw [← finsum_eq_sum_of_fintype,
    _root_.GlobalTheory.NormFormGauss.gauss_quotient σ w hW.sg_sg hW.w_add P hP hfin hσP
      ((hlam'.2 P hP hfin).2 hσP).2 χ hχadd hχ0 hχP hχσ hχnt,
    hAB, ((hlam'.2 P hP hfin).2 hσP).1]

end GlobalTheory.FinWeil
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.KZ.ES

theorem toGQ_mul_pos' (m m' : Matrix (Fin 2) (Fin 2) ℤ) (h : 0 < m.det) (h' : 0 < m'.det) :
    toGQ (m * m') = toGQ m * toGQ m' := by
  have hmm : 0 < (m * m').det := by rw [Matrix.det_mul]; exact mul_pos h h'
  unfold toGQ
  rw [dite_eq_left hmm, dite_eq_left h, dite_eq_left h']
  apply Subtype.ext
  apply Units.ext
  simp only [Matrix.GeneralLinearGroup.mkOfDetNeZero, Units.val_mul] at *
  exact Matrix.map_mul (f := Int.castRingHom ℚ)

theorem sl_trans_of_lev {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (M : ℕ) (f : X.K)
    (hf : Lev X M f) (t : ℕ) : X.sl (toGQ !![1, ((t * M : ℕ) : ℤ); 0, 1]) f = f := by
  let γ : SL(2, ℤ) := ⟨!![1, ((t * M : ℕ) : ℤ); 0, 1], by simp [Matrix.det_fin_two]⟩
  have hγ : γ ∈ CongruenceSubgroup.Gamma M := by
    rw [CongruenceSubgroup.Gamma_mem]
    simp [γ]
  have e : toGQ !![1, ((t * M : ℕ) : ℤ); 0, 1] = ofSL γ := Betti.toGQ_sl γ
  rw [e]; exact hf γ hγ

theorem Nq_eq_of_dvd : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    ∀ (M M' q : ℕ) (f : X.K), 0 < q → M ∣ M' → Nat.Coprime q M' → Lev X M f → Nq X M q f = Nq X M' q f := by
  intro Ω _ _ _ ε X M M' q f hq hdvd hcop hlev
  obtain ⟨e, rfl⟩ := hdvd
  have hqe : Nat.Coprime q e := Nat.Coprime.coprime_dvd_right (dvd_mul_left e M) hcop
  set g : ℕ → X.K := fun i => X.sl (toGQ !![1, ((i : ℤ) * (M : ℤ)); 0, (q : ℤ)]) f with hg
  have step : ∀ j : ℕ, X.sl (toGQ !![1, ((j : ℤ) * ((M * e : ℕ) : ℤ)); 0, (q : ℤ)]) f = g (j * e % q) := by
    intro j
    have hm : !![1, ((j : ℤ) * ((M * e : ℕ) : ℤ)); 0, (q : ℤ)] =
        !![1, (((j * e / q) * M : ℕ) : ℤ); 0, 1] * !![1, (((j * e % q : ℕ) : ℤ) * (M : ℤ)); 0, (q : ℤ)] := by
      have hd := Nat.mod_add_div (j * e) q
      generalize j * e % q = a at hd ⊢
      generalize j * e / q = b at hd ⊢
      have hdz : (a : ℤ) + (q : ℤ) * (b : ℤ) = (j : ℤ) * (e : ℤ) := by exact_mod_cast hd
      ext i k; fin_cases i <;> fin_cases k <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination (M : ℤ) * hdz.symm
    have h1 : (0 : ℤ) < (!![1, (((j * e / q) * M : ℕ) : ℤ); 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).det := by
      simp [Matrix.det_fin_two]
    have h2 : (0 : ℤ) < (!![1, (((j * e % q : ℕ) : ℤ) * (M : ℤ)); 0, (q : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ).det := by
      simp [Matrix.det_fin_two]; exact_mod_cast hq
    rw [hm, toGQ_mul_pos' _ _ h1 h2, X.sl_mul, sl_trans_of_lev X M f hlev]
  have hinj : Set.InjOn (fun j => j * e % q) (Finset.range q : Set ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    have h' : a * e ≡ b * e [MOD q] := hab
    have := Nat.ModEq.cancel_right_of_coprime (by simpa [Nat.gcd_comm] using hqe) h'
    simpa [Nat.ModEq, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using this
  have himg : (Finset.range q).image (fun j => j * e % q) = Finset.range q := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_image, Finset.mem_range] at hx ⊢
      obtain ⟨j, _, rfl⟩ := hx
      exact Nat.mod_lt _ hq
    · rw [Finset.card_image_of_injOn hinj]
  unfold Nq
  simp_rw [step]
  show ∏ j ∈ Finset.range q, g j = _
  rw [← Finset.prod_image (f := g) hinj, himg]

end GlobalTheory.KZ.ES
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

theorem _root_.GlobalTheory.T.exists_level_mul_pow_of_invariant_mod_pow : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), ∀ (l n M e : ℕ), l.Prime → 0 < M → ∀ f : X.Kˣ, Lev X (M ^ e) f → (∀ γ ∈ CongruenceSubgroup.Gamma M, ∃ g : X.Kˣ, X.sl (ofSL γ) (f : X.K) = f * (g : X.K) ^ (l ^ n)) → ∃ (k : ℕ) (h : X.Kˣ), Lev X (M * l ^ k) ((f : X.K) * (h : X.K) ^ (l ^ n)) := by
  first | exact @GlobalTheory.KZ.ES.exists_lev_mul_pow_of_invariant_mod_pow | exact GlobalTheory.KZ.ES.exists_lev_mul_pow_of_invariant_mod_pow | (intros; apply GlobalTheory.KZ.ES.exists_lev_mul_pow_of_invariant_mod_pow <;> assumption)
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

theorem _root_.GlobalTheory.T.kronecker_congruence_frobenius_diag : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), ∀ (q : ℕ), q.Prime → ∀ (V : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω), FrobV V q s → ∀ a : X.K, IntC X V a → SmallC X V (X.sl (toGQ !![(q : ℤ), 0; 0, 1]) a - (X.gal s.symm a) ^ q) := by
  first | exact @GlobalTheory.KZ.ES.kron_frob_diag | exact GlobalTheory.KZ.ES.kron_frob_diag | (intros; apply GlobalTheory.KZ.ES.kron_frob_diag <;> assumption)
end

section

open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold

theorem _root_.GlobalTheory.T.isCuspidalAtAllCuspsSL2_slash_intMatrix : ∀ (k : ℤ) (M : Matrix (Fin 2) (Fin 2) ℤ) (G : ℍ → ℂ), 0 < M.det → CuspAll k G → CuspAll k (G ∣[k] toGL M) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.cuspAll_slash_toGL | exact GlobalTheory.HeckeFamilyMatrices.cuspAll_slash_toGL | (intros; apply GlobalTheory.HeckeFamilyMatrices.cuspAll_slash_toGL <;> assumption)
end

section

open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold

theorem _root_.GlobalTheory.T.nebentypus_slash_intDiagTwoMatrix_levelRaise : ∀ (N l : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (B : ℍ → ℂ), 0 < l → ChiInv k N N χ B → ChiInv k N (N * l) χ (B ∣[k] toGL (dg l 1)) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.chiInv_slash_dg | exact GlobalTheory.HeckeFamilyMatrices.chiInv_slash_dg | (intros; apply GlobalTheory.HeckeFamilyMatrices.chiInv_slash_dg <;> assumption)
end

section

open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold

theorem _root_.GlobalTheory.T.nebentypus_slash_oldformLevelRaisingMatrix : ∀ (N l : ℕ) (k : ℤ) (a b : ℤ), (l : ℤ) * b - N * a = 1 → ∀ (χ : DirichletCharacter ℂ N) (G : ℍ → ℂ), 0 < l → ChiInv k N (N * l) χ G → ChiInv k N (N * l) χ (G ∣[k] toGL (wOld N l a b)) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.chiInv_slash_wOld | exact GlobalTheory.HeckeFamilyMatrices.chiInv_slash_wOld | (intros; apply GlobalTheory.HeckeFamilyMatrices.chiInv_slash_wOld <;> assumption)
end

section

open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold

theorem _root_.GlobalTheory.T.oldformLevelRaising_slash_slash_nebentypus : ∀ (N l : ℕ) (k : ℤ) (a b : ℤ), (l : ℤ) * b - N * a = 1 → ∀ (χ : DirichletCharacter ℂ N) (G : ℍ → ℂ), 0 < l → ChiInv k N (N * l) χ G → (G ∣[k] toGL (wOld N l a b)) ∣[k] toGL (wOld N l a b) = ((l : ℂ) ^ (k - 2) * χ (b : ZMod N)) • G := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.wOld_slash_slash | exact GlobalTheory.HeckeFamilyMatrices.wOld_slash_slash | (intros; apply GlobalTheory.HeckeFamilyMatrices.wOld_slash_slash <;> assumption)
end

section

open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold

theorem _root_.GlobalTheory.T.oldformTraceToGammaOne_eq_heckeUl_levelRaising : ∀ (N l : ℕ) (k : ℤ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1) (G : ℍ → ℂ), 0 < l → trOld k N l a b h G = G + ((l : ℂ) ^ (2 - k)) • UlF k l (G ∣[k] toGL (wOld N l a b)) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.trOld_eq | exact GlobalTheory.HeckeFamilyMatrices.trOld_eq | (intros; apply GlobalTheory.HeckeFamilyMatrices.trOld_eq <;> assumption)
end

section

open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold

theorem _root_.GlobalTheory.T.cuspForm_isCuspidalAtAllCuspsSL2 : ∀ (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (k : ℤ) (f : CuspForm Γ k), CuspAll k f := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.cuspForm_cuspAll | exact GlobalTheory.HeckeFamilyMatrices.cuspForm_cuspAll | (intros; apply GlobalTheory.HeckeFamilyMatrices.cuspForm_cuspAll <;> assumption)
end

section

open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold

theorem _root_.GlobalTheory.T.exists_cuspForm_gammaOne_of_nebentypus_cuspidal : ∀ (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (G : ℍ → ℂ), 0 < N → CuspAll k G → ChiInv k N N χ G → ∃ f : CuspForm (Gamma1 N) k, ⇑f = G := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.cuspForm_of_chiInv | exact GlobalTheory.HeckeFamilyMatrices.cuspForm_of_chiInv | (intros; apply GlobalTheory.HeckeFamilyMatrices.cuspForm_of_chiInv <;> assumption)
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

noncomputable section

namespace GlobalTheory.KZ


open scoped MatrixGroups TensorProduct in
open Matrix in
theorem _root_.GlobalTheory.KZ.gamma_le_of_dvd {M M' : ℕ} (h : M ∣ M') :
    CongruenceSubgroup.Gamma M' ≤ CongruenceSubgroup.Gamma M := by
  intro γ hγ
  rw [CongruenceSubgroup.Gamma_mem] at hγ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hγ
  have e : ∀ z : ℤ, (z : ZMod M) = ZMod.castHom h (ZMod M) (z : ZMod M') := fun z =>
    (map_intCast _ z).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e, h1, map_one]
  · rw [e, h2, map_zero]
  · rw [e, h3, map_zero]
  · rw [e, h4, map_one]

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem Tower.lev_mono (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] {M M' : ℕ} (h : M ∣ M') :
    X.Lev l M ≤ X.Lev l M' := by
  apply Submodule.span_mono
  rintro x ⟨f, hf, rfl⟩
  exact ⟨f, fun γ hγ => hf γ (gamma_le_of_dvd h hγ), rfl⟩

theorem Tower.exists_lev (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (y : X.Kl l) :
    ∃ M : ℕ, 0 < M ∧ y ∈ X.Lev l M := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨1, one_pos, Submodule.zero_mem _⟩
  | tmul a f =>
    obtain ⟨M, hM, hf⟩ := X.level (Additive.toMul f : X.Kˣ)
    refine ⟨M, hM, ?_⟩
    have hmem : (1 : ℤ_[l]) ⊗ₜ[ℤ] f ∈ X.Lev l M :=
      Submodule.subset_span ⟨Additive.toMul f, fun γ hγ => hf γ hγ, rfl⟩
    have e : a ⊗ₜ[ℤ] f = a • ((1 : ℤ_[l]) ⊗ₜ[ℤ] f) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [e]
    exact Submodule.smul_mem _ a hmem
  | add y z hy hz =>
    obtain ⟨M, hM, hy⟩ := hy
    obtain ⟨M', hM', hz⟩ := hz
    refine ⟨M * M', Nat.mul_pos hM hM', Submodule.add_mem _ ?_ ?_⟩
    · exact X.lev_mono l (dvd_mul_right M M') hy
    · exact X.lev_mono l (dvd_mul_left M' M) hz

theorem Tower.exists_lev_family : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ)
    [Fact l.Prime] (K : ℕ) {ι : Type} [Fintype ι] (y : ι → X.Kl l), 0 < K →
    ∃ M : ℕ, 0 < M ∧ K ∣ M ∧ ∀ i, y i ∈ X.Lev l M := by
  intro Ω _ _ ε X l _ K ι _ y hK
  choose L hL hy using fun i => X.exists_lev l (y i)
  refine ⟨K * ∏ i, L i, Nat.mul_pos hK (Finset.prod_pos fun i _ => hL i), dvd_mul_right _ _, fun i => ?_⟩
  refine X.lev_mono l ?_ (hy i)
  exact Dvd.dvd.mul_left (Finset.dvd_prod_of_mem L (Finset.mem_univ i)) K

end GlobalTheory.KZ
end
end
