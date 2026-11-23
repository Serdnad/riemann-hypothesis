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
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm

@[expose] public section

section

set_option autoImplicit false

open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI

theorem divided_frob_logForm : ∀ {K Kt : Type} [Field K] [CommRing Kt] (p : ℕ) [Fact p.Prime] [CharP K p] (π : Kt →+* K) {ι : Type} (F : ι → Kt →+* Kt) (f : ι → Ω[K⁄ℤ] →+ Ω[K⁄ℤ]) (h : ι → ι → Ω[K⁄ℤ] →+ K) (s : Finset ι) (A : Subring K) (g : K), (∀ i, IsF p π (F i) (f i)) → (∀ i j, IsH p π (F i) (F j) (h i j)) → LogLift p π F s (A : Set K) g → (∀ i ∈ s, ∃ w ∈ A, g ≠ 0 → f i (g⁻¹ • KaehlerDifferential.D ℤ K g) = g⁻¹ • KaehlerDifferential.D ℤ K g + KaehlerDifferential.D ℤ K w) ∧ ∀ i ∈ s, ∀ j ∈ s, h i j (g⁻¹ • KaehlerDifferential.D ℤ K g) ∈ A := by
  intro K Kt _ _ p hp _ π ι F f h s A g hF hH hL
  obtain ⟨z, hz, hw⟩ := hL
  have hp0 : p ≠ 0 := hp.out.ne_zero
  have hDp : KaehlerDifferential.D ℤ K (g ^ p) = 0 := by
    rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero, zero_smul]
  have e2 : ∀ hg : g ≠ 0, g⁻¹ ^ p * g ^ p = 1 := fun hg => by
    rw [← mul_pow, inv_mul_cancel₀ hg, one_pow]
  refine ⟨fun i hi => ?_, fun i hi j hj => ?_⟩
  · obtain ⟨w, hwA, hFw⟩ := hw i hi
    refine ⟨π w, hwA, fun hg => ?_⟩
    have key := (hF i).2 z (z ^ p * w) (by rw [hFw]; ring)
    rw [map_mul, map_pow, hz] at key
    have e1 : g⁻¹ ^ p * g ^ (p - 1) = g⁻¹ := by
      obtain ⟨n, hn⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
      rw [hn, Nat.add_sub_cancel, pow_succ, mul_comm (g⁻¹ ^ n), mul_assoc, ← mul_pow, inv_mul_cancel₀ hg,
        one_pow, mul_one]
    rw [(hF i).1, key, Derivation.leibniz, hDp, smul_zero, add_zero, smul_add, smul_smul, smul_smul, e1,
      e2 hg, one_smul]
  · obtain ⟨wi, hwiA, hFi⟩ := hw i hi
    obtain ⟨wj, hwjA, hFj⟩ := hw j hj
    have key := (hH i j).2 z (z ^ p * (wj - wi)) (by rw [hFj, hFi]; ring)
    rw [map_mul, map_pow, map_sub, hz] at key
    rw [(hH i j).1, key]
    by_cases hg : g = 0
    · subst hg
      simp [hp0]
    · rw [← mul_assoc, e2 hg, one_mul]
      exact A.sub_mem hwjA hwiA

end GlobalTheory.DI
end

section

open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI

theorem _root_.GlobalTheory.DI.inTot_delta_Dtot : ∀ {ι : Type} [LinearOrder ι] {E : Type}
    [AddCommGroup E] (d : E →+ E)
    (T : ℕ → Finset ι → AddSubgroup E), (∀ q s t, s.Nonempty → s ⊆ t → T q s ≤ T q t) →
    ∀ m c, _root_.GlobalTheory.DI.InTot T m c → _root_.GlobalTheory.DI.InTot T (m + 1)
        (_root_.GlobalTheory.DI.delta c) ∧
      ((∀ q s x, x ∈ T q s → d x ∈ T (q + 1) s) →
        _root_.GlobalTheory.DI.InTot T (m + 1) (_root_.GlobalTheory.DI.Dtot d c)) := by
  intro ι _ E _ d T hmono m c hc
  unfold _root_.GlobalTheory.DI.InTot at hc
  obtain ⟨h0, hmem, hzero⟩ := hc
  have hδ0 : _root_.GlobalTheory.DI.delta c ∅ = 0 := by
    unfold _root_.GlobalTheory.DI.delta; simp
  have hδmem : ∀ (q : ℕ) (t : Finset ι), q + t.card = m + 1 →
      _root_.GlobalTheory.DI.delta c t ∈ T q t := by
    intro q t hqt
    unfold _root_.GlobalTheory.DI.delta
    refine AddSubgroup.sum_mem _ fun i hi => AddSubgroup.zsmul_mem _ ?_ _
    have hcard : (t.erase i).card = t.card - 1 := Finset.card_erase_of_mem hi
    have hpos : 0 < t.card := Finset.card_pos.mpr ⟨i, hi⟩
    have hq : q + (t.erase i).card = m := by omega
    rcases (t.erase i).eq_empty_or_nonempty with he | hne
    · rw [he, h0]; exact zero_mem _
    · exact hmono q _ _ hne (Finset.erase_subset i t) (hmem q _ hq)
  have hδz : ∀ t : Finset ι, m + 1 < t.card → _root_.GlobalTheory.DI.delta c t = 0 := by
    intro t ht
    unfold _root_.GlobalTheory.DI.delta
    refine Finset.sum_eq_zero fun i hi => ?_
    have hcard : (t.erase i).card = t.card - 1 := Finset.card_erase_of_mem hi
    rw [hzero _ (by omega), smul_zero]
  refine ⟨⟨hδ0, hδmem, hδz⟩, fun hd => ⟨?_, ?_, ?_⟩⟩
  · unfold _root_.GlobalTheory.DI.Dtot; simp [hδ0, h0]
  · intro q t hqt
    unfold _root_.GlobalTheory.DI.Dtot
    refine add_mem (hδmem q t hqt) (AddSubgroup.zsmul_mem _ ?_ _)
    rcases q with _ | q
    · rw [hzero t (by omega), map_zero]; exact zero_mem _
    · exact hd q t _ (hmem q t (by omega))
  · intro t ht
    unfold _root_.GlobalTheory.DI.Dtot
    rw [hδz t ht, hzero t (by omega), map_zero, smul_zero, add_zero]

end GlobalTheory.DI
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

noncomputable section

namespace GlobalTheory.Shin.BlockPar

variable {F : Type} [Field F] {a b : ℕ}

def sm (M : Matrix (Fin (a + b)) (Fin (a + b)) F) : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) F :=
  M.submatrix finSumFinEquiv finSumFinEquiv

theorem tl_eq (M : Matrix (Fin (a + b)) (Fin (a + b)) F) : tl a M = (sm M).toBlocks₁₁ := by
  ext i j
  have hi : (i : ℕ) < a + b := by omega
  have hj : (j : ℕ) < a + b := by omega
  simp only [tl, ent, hi, hj, and_self, dif_pos, sm, Matrix.toBlocks₁₁, Matrix.of_apply,
    Matrix.submatrix_apply, finSumFinEquiv_apply_left]
  rfl

theorem br_eq (M : Matrix (Fin (a + b)) (Fin (a + b)) F) : br a b M = (sm M).toBlocks₂₂ := by
  ext i j
  have hi : a + (i : ℕ) < a + b := by omega
  have hj : a + (j : ℕ) < a + b := by omega
  simp only [br, ent, hi, hj, and_self, dif_pos, sm, Matrix.toBlocks₂₂, Matrix.of_apply,
    Matrix.submatrix_apply, finSumFinEquiv_apply_right]
  rfl

theorem inPar_iff (x : GL (Fin (a + b)) F) :
    InPar a x ↔ (sm (x : Matrix (Fin (a + b)) (Fin (a + b)) F)).toBlocks₂₁ = 0 := by
  constructor
  · intro h
    ext i j
    simp only [sm, Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.submatrix_apply, finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right, Matrix.zero_apply]
    apply h <;> simp
  · intro h i j hj hi
    obtain ⟨i', rfl⟩ : ∃ i' : Fin b, Fin.natAdd a i' = i :=
      ⟨⟨i - a, by omega⟩, Fin.ext (by simp; omega)⟩
    obtain ⟨j', rfl⟩ : ∃ j' : Fin a, Fin.castAdd b j' = j := ⟨⟨j, hj⟩, rfl⟩
    have := congrFun (congrFun h i') j'
    simpa [sm, Matrix.toBlocks₂₁] using this

theorem sm_eq {M : Matrix (Fin (a + b)) (Fin (a + b)) F} (h : (sm M).toBlocks₂₁ = 0) :
    sm M = Matrix.fromBlocks (tl a M) (sm M).toBlocks₁₂ 0 (br a b M) := by
  rw [tl_eq, br_eq, ← h, Matrix.fromBlocks_toBlocks]

theorem sm_mul (M N : Matrix (Fin (a + b)) (Fin (a + b)) F) : sm (M * N) = sm M * sm N :=
  (Matrix.submatrix_mul_equiv M N _ _ _).symm

theorem mul_blocks {M N : Matrix (Fin (a + b)) (Fin (a + b)) F} (hM : (sm M).toBlocks₂₁ = 0)
    (hN : (sm N).toBlocks₂₁ = 0) :
    (sm (M * N)).toBlocks₂₁ = 0 ∧ tl a (M * N) = tl a M * tl a N ∧ br a b (M * N) = br a b M * br a b N := by
  have e : sm (M * N) = Matrix.fromBlocks (tl a M * tl a N)
      (tl a M * (sm N).toBlocks₁₂ + (sm M).toBlocks₁₂ * br a b N) 0 (br a b M * br a b N) := by
    rw [sm_mul, sm_eq hM, sm_eq hN, Matrix.fromBlocks_multiply]
    simp
  refine ⟨by rw [e, Matrix.toBlocks_fromBlocks₂₁], ?_, ?_⟩
  · rw [tl_eq (M * N), e, Matrix.toBlocks_fromBlocks₁₁]
  · rw [br_eq (M * N), e, Matrix.toBlocks_fromBlocks₂₂]

theorem det_eq {M : Matrix (Fin (a + b)) (Fin (a + b)) F} (h : (sm M).toBlocks₂₁ = 0) :
    M.det = (tl a M).det * (br a b M).det := by
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv M]
  change (sm M).det = _
  rw [sm_eq h, Matrix.det_fromBlocks_zero₂₁]

theorem charpoly_eq {M : Matrix (Fin (a + b)) (Fin (a + b)) F} (h : (sm M).toBlocks₂₁ = 0) :
    M.charpoly = (tl a M).charpoly * (br a b M).charpoly := by
  rw [← Matrix.charpoly_reindex finSumFinEquiv.symm M]
  have : Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm M = sm M := by
    rw [Matrix.reindex_apply, Equiv.symm_symm]; rfl
  rw [this, sm_eq h, Matrix.charpoly_fromBlocks_zero₂₁]

theorem toG_val {m : ℕ} {M : Matrix (Fin m) (Fin m) F} (h : IsUnit M) : ((toG M : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = M := by
  unfold toG; rw [dif_pos h]; rfl

theorem units_of_par (x : GL (Fin (a + b)) F) (h : InPar a x) :
    IsUnit (tl a (x : Matrix (Fin (a + b)) (Fin (a + b)) F)) ∧ IsUnit (br a b (x : Matrix (Fin (a + b)) (Fin (a + b)) F)) := by
  have hu : IsUnit (x : Matrix (Fin (a + b)) (Fin (a + b)) F).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 x.isUnit
  rw [det_eq ((inPar_iff x).1 h)] at hu
  exact ⟨(Matrix.isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_left hu),
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_right hu)⟩

theorem inPar_inv (x : GL (Fin (a + b)) F) (h : InPar a x) : InPar a x⁻¹ := by
  let β : Fin (a + b) → Bool := fun i => decide (a ≤ (i : ℕ))
  have hb : (x : Matrix (Fin (a + b)) (Fin (a + b)) F).BlockTriangular β := by
    intro i j hij
    rw [Bool.lt_iff] at hij
    simp only [β, decide_eq_false_iff_not, decide_eq_true_eq, not_le] at hij
    exact h i j hij.1 hij.2
  haveI := x.invertible
  have hb' := Matrix.blockTriangular_inv_of_blockTriangular hb
  intro i j hj hi
  rw [Matrix.coe_units_inv]
  exact hb' (by rw [Bool.lt_iff]; simp [β]; omega)

theorem block_par : ∀ (F : Type) [Field F] (a b n : ℕ), n = a + b → ∃ (H : Subgroup (GL (Fin n) F)) (π : H →* GL (Fin a) F × GL (Fin b) F), (∀ x, x ∈ H ↔ InPar a x) ∧ Function.Surjective π ∧ (∀ p : H, π p = (tlG a p.1, brG a b p.1)) ∧ (∀ p : H, ((π p).1 : Matrix (Fin a) (Fin a) F) = tl a (p.1 : Matrix (Fin n) (Fin n) F) ∧ ((π p).2 : Matrix (Fin b) (Fin b) F) = br a b (p.1 : Matrix (Fin n) (Fin n) F)) ∧ ∀ p : H, Matrix.charpoly (p.1 : Matrix (Fin n) (Fin n) F) = Matrix.charpoly ((π p).1 : Matrix (Fin a) (Fin a) F) * Matrix.charpoly ((π p).2 : Matrix (Fin b) (Fin b) F) := by
  intro F _ a b n hn
  subst hn
  let H : Subgroup (GL (Fin (a + b)) F) :=
    { carrier := {x | InPar a x}
      one_mem' := by
        intro i j hj hi
        rw [Units.val_one, Matrix.one_apply_ne]
        intro e; subst e; omega
      mul_mem' := by
        intro x y hx hy
        exact (inPar_iff _).2 (mul_blocks ((inPar_iff x).1 hx) ((inPar_iff y).1 hy)).1
      inv_mem' := fun {x} hx => inPar_inv x hx }
  have hH : ∀ x, x ∈ H ↔ InPar a x := fun _ => Iff.rfl
  have hpar : ∀ p : H, (sm ((p.1 : GL (Fin (a + b)) F) : Matrix (Fin (a + b)) (Fin (a + b)) F)).toBlocks₂₁ = 0 :=
    fun p => (inPar_iff _).1 p.2
  have hval : ∀ p : H, ((tlG a p.1 : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) = tl a (p.1 : Matrix (Fin (a + b)) (Fin (a + b)) F) ∧
      ((brG a b p.1 : GL (Fin b) F) : Matrix (Fin b) (Fin b) F) = br a b (p.1 : Matrix (Fin (a + b)) (Fin (a + b)) F) :=
    fun p => ⟨toG_val (units_of_par _ p.2).1, toG_val (units_of_par _ p.2).2⟩
  let π : H →* GL (Fin a) F × GL (Fin b) F :=
    MonoidHom.mk' (fun p => (tlG a p.1, brG a b p.1)) (by
      intro p q
      have hm := mul_blocks (hpar p) (hpar q)
      refine Prod.ext (Units.ext ?_) (Units.ext ?_)
      · change ((tlG a (p * q).1 : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) = ((tlG a p.1 : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) * ((tlG a q.1 : GL (Fin a) F) : Matrix (Fin a) (Fin a) F)
        rw [(hval (p * q)).1, (hval p).1, (hval q).1]
        exact hm.2.1
      · change ((brG a b (p * q).1 : GL (Fin b) F) : Matrix (Fin b) (Fin b) F) = ((brG a b p.1 : GL (Fin b) F) : Matrix (Fin b) (Fin b) F) * ((brG a b q.1 : GL (Fin b) F) : Matrix (Fin b) (Fin b) F)
        rw [(hval (p * q)).2, (hval p).2, (hval q).2]
        exact hm.2.2)
  have hπ : ∀ p : H, π p = (tlG a p.1, brG a b p.1) := fun _ => rfl
  refine ⟨H, π, hH, ?_, hπ, fun p => hval p, fun p => ?_⟩
  · rintro ⟨u, v⟩
    let M : Matrix (Fin (a + b)) (Fin (a + b)) F :=
      (Matrix.fromBlocks (u : Matrix (Fin a) (Fin a) F) 0 0 (v : Matrix (Fin b) (Fin b) F)).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm
    have hsm : sm M = Matrix.fromBlocks (u : Matrix (Fin a) (Fin a) F) 0 0 (v : Matrix (Fin b) (Fin b) F) := by
      simp only [sm, M, Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id]
    have h21 : (sm M).toBlocks₂₁ = 0 := by rw [hsm, Matrix.toBlocks_fromBlocks₂₁]
    have htl : tl a M = u := by rw [tl_eq, hsm, Matrix.toBlocks_fromBlocks₁₁]
    have hbr : br a b M = v := by rw [br_eq, hsm, Matrix.toBlocks_fromBlocks₂₂]
    have hu : IsUnit M := by
      rw [Matrix.isUnit_iff_isUnit_det, det_eq h21, htl, hbr]
      exact ((Matrix.isUnit_iff_isUnit_det _).1 u.isUnit).mul ((Matrix.isUnit_iff_isUnit_det _).1 v.isUnit)
    have hmem : hu.unit ∈ H := by
      rw [hH, inPar_iff]
      exact h21
    refine ⟨⟨hu.unit, hmem⟩, ?_⟩
    have hv := hval ⟨hu.unit, hmem⟩
    simp only [IsUnit.unit_spec] at hv
    rw [hπ]
    refine Prod.ext (Units.ext ?_) (Units.ext ?_)
    · exact hv.1.trans htl
    · exact hv.2.trans hbr
  · rw [hπ, (hval p).1, (hval p).2]
    exact charpoly_eq (hpar p)

end GlobalTheory.Shin.BlockPar
end
end

section

noncomputable section

namespace GlobalTheory.Shin.HcUnit

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

variable {F : Type} [Field F]

theorem toG_val {n : ℕ} (x : GL (Fin n) F) : toG (x : Matrix (Fin n) (Fin n) F) = x := by
  unfold toG
  rw [dite_eq_left x.isUnit]
  exact Units.ext (IsUnit.unit_spec _)

theorem brG_zero {a : ℕ} (x : GL (Fin a) F) : brG 0 a x = x := by
  have h : br 0 a (x : Matrix (Fin a) (Fin a) F) = x := by
    ext i j
    simp [br, ent]
  unfold brG
  rw [h, toG_val]

theorem tlG_self {a : ℕ} (x : GL (Fin a) F) : tlG a x = x := by
  have h : tl a (x : Matrix (Fin a) (Fin a) F) = x := by
    ext i j
    simp [tl, ent]
  unfold tlG
  rw [h, toG_val]

theorem inPar_zero {n : ℕ} (x : GL (Fin n) F) : InPar 0 x :=
  fun _ _ hj _ => absurd hj (Nat.not_lt_zero _)

theorem inPar_self {a : ℕ} (x : GL (Fin a) F) : InPar a x :=
  fun i _ _ hi => absurd i.isLt (not_lt.mpr hi)

theorem gal_id {n : ℕ} (y : GL (Fin n) F) : gal (RingHom.id F) n y = y := by
  ext i j
  simp [gal]

theorem mean_class {G : Type} [Group G] [Finite G] {χ : G → ℂ} (h : IsCl χ) (x : G) :
    (Nat.card G : ℂ)⁻¹ * ∑ᶠ y : G, χ (y⁻¹ * x * y) = χ x := by
  have hc : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have h' : ∀ y : G, χ (y⁻¹ * x * y) = χ x := fun y => h x y
  have := Fintype.ofFinite G
  rw [finsum_congr h', finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

private theorem card_infinitePlace_eq_f {G : Type} {p : G → Prop} (h : ∀ x, p x) :
    Nat.card {x // p x} = Nat.card G :=
  Nat.card_congr (Equiv.subtypeUnivEquiv h)

theorem main : ∀ (F : Type) [Field F] [Finite F], ∀ (a : ℕ) (α : GL (Fin a) F → ℂ), IsCl α →
    hc 0 a (fun _ => 1) α a = α ∧ hc a 0 α (fun _ => 1) a = α := by
  intro F _ _ a α hα
  refine ⟨funext fun x => ?_, funext fun x => ?_⟩
  · simp only [hc, hcTw]
    rw [card_infinitePlace_eq_f inPar_zero]
    simp only [gal_id, inPar_zero, ↓reduceIte, brG_zero, one_mul]
    exact mean_class hα x
  · simp only [hc, hcTw]
    rw [card_infinitePlace_eq_f inPar_self]
    simp only [gal_id, inPar_self, ↓reduceIte, tlG_self, mul_one]
    exact mean_class hα x

end GlobalTheory.Shin.HcUnit

end
end

section

open GlobalTheory GlobalTheory.DI

set_option autoImplicit false

namespace GlobalTheory.DI.PhiLead
variable {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι]

theorem prodL_single (f : ι → V →+ V) (h : ι → ι → V →+ K) (j : ι) (vs : List V) :
    prodL f h vs {j} = ((-1 : ℤ) ^ vs.length) • (vs.map (fun v => ExteriorAlgebra.ι K (f j v))).prod := by
  induction vs with
  | nil => simp [prodL, oneC]
  | cons v vs ih =>
    have e : prodL f h (v :: vs) = Lop f h v (prodL f h vs) := rfl
    rw [e]
    simp only [Lop, Finset.singleton_nonempty, dite_true, Finset.min'_singleton, Finset.erase_singleton,
      Finset.not_nonempty_empty, dite_false, add_zero, Finset.card_singleton, ih, List.length_cons,
      List.map_cons, List.prod_cons, pow_succ]
    rw [mul_smul_comm, smul_smul]
    ring_nf

theorem alt_single (f : ι → V →+ V) (h : ι → ι → V →+ K) (a : ℕ) (v : Fin a → V) (j : ι) :
    alt f h a v {j} = ((-1 : ℤ) ^ a * (a.factorial : ℤ)) • ExteriorAlgebra.ιMulti K a (fun k => f j (v k)) := by
  have key : ∀ σ : Equiv.Perm (Fin a), prodL f h (List.ofFn (v ∘ σ)) {j} =
      ((-1 : ℤ) ^ a * ((Equiv.Perm.sign σ : ℤˣ) : ℤ)) • ExteriorAlgebra.ιMulti K a (fun k => f j (v k)) := by
    intro σ
    rw [prodL_single, List.length_ofFn, List.map_ofFn]
    have h1 : (List.ofFn ((fun v => ExteriorAlgebra.ι K (f j v)) ∘ v ∘ σ)).prod =
        ExteriorAlgebra.ιMulti K a ((fun k => f j (v k)) ∘ σ) := by
      rw [ExteriorAlgebra.ιMulti_apply]; rfl
    rw [h1, AlternatingMap.map_perm, mul_smul]
    simp [Units.smul_def]
  simp only [alt, Finset.sum_apply, Pi.smul_apply, key, smul_smul]
  rw [← Finset.sum_smul]
  congr 1
  have hs : ∀ σ : Equiv.Perm (Fin a), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) * ((-1 : ℤ) ^ a * ((Equiv.Perm.sign σ : ℤˣ) : ℤ)) = (-1 : ℤ) ^ a := by
    intro σ
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hσ | hσ <;> simp [hσ]
  simp only [hs, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  push_cast; ring

theorem gamma_iMulti (p : ℕ) (g : V →+ V) (γ : ExteriorAlgebra K V →+* ExteriorAlgebra K V)
    (hγ : IsGamma p g γ) (a : ℕ) (v : Fin a → V) :
    γ (ExteriorAlgebra.ιMulti K a v) = ExteriorAlgebra.ιMulti K a (fun k => g (v k)) := by
  rw [ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
  congr 1
  exact List.ofFn_inj.mpr (funext fun k => hγ.2 (v k))

theorem leading_term : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι] (p : ℕ) (f : ι → V →+ V) (h : ι → ι → V →+ K), (∀ (a : ℕ) (v : Fin a → V) (j : ι), alt f h a v {j} = ((-1 : ℤ) ^ a * (a.factorial : ℤ)) • ExteriorAlgebra.ιMulti K a (fun k => f j (v k))) ∧ ∀ (Φ : ExteriorAlgebra K V →+ (Finset ι → ExteriorAlgebra K V)) (j : ι) (γ : ExteriorAlgebra K V →+* ExteriorAlgebra K V), IsPhi p f h Φ → IsGamma p (f j) γ → ∀ a, ∀ x ∈ forms (Set.univ : Set K) (Set.univ : Set V) a, Φ x {j} = ((-1 : ℤ) ^ a * (a.factorial : ℤ)) • γ x := by
  intro K _ V _ _ ι _ p f h
  refine ⟨fun a v j => alt_single f h a v j, ?_⟩
  intro Φ j γ hΦ hγ a x hx
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨b, -, v, -, rfl⟩ := hx
    have hg : γ (b • ExteriorAlgebra.ιMulti K a v) = b ^ p • ExteriorAlgebra.ιMulti K a (fun k => f j (v k)) := by
      rw [Algebra.smul_def, map_mul, hγ.1, gamma_iMulti p (f j) γ hγ, ← Algebra.smul_def]
    rw [hΦ, Pi.smul_apply, alt_single, hg, smul_comm]
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy, smul_add]
  | neg x _ hx => simp [hx, smul_neg]
end GlobalTheory.DI.PhiLead
end

section

open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI

theorem prodL_eq_zero_of_card {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type}
    [LinearOrder ι] (f : ι → V →+ V) (h : ι → ι → V →+ K) (vs : List V) (t : Finset ι)
    (ht : vs.length + 1 < t.card) : prodL f h vs t = 0 := by
  induction vs generalizing t with
  | nil =>
    simp only [prodL, List.foldr_nil, oneC]
    simp only [List.length_nil] at ht
    rw [if_neg (by omega)]
  | cons v vs ih =>
    change Lop f h v (prodL f h vs) t = 0
    simp only [List.length_cons] at ht
    unfold Lop
    split_ifs with h1 h2
    · have e1 := ih t (by omega)
      have e2 := ih (t.erase (t.min' h1))
        (by rw [Finset.card_erase_of_mem (Finset.min'_mem _ _)]; omega)
      rw [e1, e2, mul_zero, smul_zero, smul_zero, add_zero]
    · have e1 := ih t (by omega)
      rw [e1, mul_zero, smul_zero, add_zero]
    · rfl

theorem alt_and_phi_vanish_above_degree : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι] (p : ℕ) (f : ι → V →+ V) (h : ι → ι → V →+ K), (∀ (a : ℕ) (v : Fin a → V) (t : Finset ι), a + 1 < t.card → alt f h a v t = 0) ∧ ∀ (Φ : ExteriorAlgebra K V →+ (Finset ι → ExteriorAlgebra K V)), IsPhi p f h Φ → ∀ a, ∀ x ∈ forms (Set.univ : Set K) (Set.univ : Set V) a, ∀ t : Finset ι, a + 1 < t.card → Φ x t = 0 := by
  intro K _ V _ _ ι _ p f h
  have halt : ∀ (a : ℕ) (v : Fin a → V) (t : Finset ι), a + 1 < t.card → alt f h a v t = 0 := by
    intro a v t ht
    simp only [alt, Finset.sum_apply, Pi.smul_apply]
    apply Finset.sum_eq_zero
    intro σ _
    rw [prodL_eq_zero_of_card f h _ t (by simpa using ht), smul_zero]
  refine ⟨halt, ?_⟩
  intro Φ hΦ a x hx t ht
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨b, -, v, -, rfl⟩ := hx
    rw [hΦ, Pi.smul_apply, halt a v t ht, smul_zero]
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | neg x _ hx => simp [hx]

end GlobalTheory.DI
end
