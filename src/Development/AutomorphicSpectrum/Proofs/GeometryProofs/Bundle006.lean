module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.NumberTheory.NumberField.Basic
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
public import Mathlib.GroupTheory.CosetCover
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

namespace GlobalTheory.CompanionTheory.LuFields

open Matrix

theorem entries_mem_of_eq_mul {K L : Type} [Field K] [Field L] [Algebra K L] {n : ℕ}
    (F : IntermediateField K L) (C v w : Matrix (Fin n) (Fin n) L) (hC : ∀ i k, C i k ∈ F)
    (hv1 : ∀ k, v k k = 1) (hv0 : ∀ l k, l < k → v l k = 0)
    (hw0 : ∀ l k, k < l → w l k = 0) (hwd : ∀ k, w k k ≠ 0) (h : C = v * w) :
    (∀ i k, v i k ∈ F) ∧ (∀ i k, w i k ∈ F) := by
  have hC' : ∀ i k, ∑ l, v i l * w l k ∈ F := fun i k => by
    have := hC i k
    rwa [h, Matrix.mul_apply] at this
  have key : ∀ m : ℕ, ∀ i k : Fin n, ((i : ℕ) < m ∨ (k : ℕ) < m) → v i k ∈ F ∧ w i k ∈ F := by
    intro m
    induction m with
    | zero => intro i k hik; exact absurd hik (by omega)
    | succ m ih =>
      have hw : ∀ i k : Fin n, (i : ℕ) = m → i ≤ k → w i k ∈ F := by
        intro i k hi hik
        have hsum := hC' i k
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), hv1, one_mul] at hsum
        have hrest : ∑ l ∈ Finset.univ.erase i, v i l * w l k ∈ F := by
          refine sum_mem fun l hl => ?_
          rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hl) with hlt | hgt
          · have hl' : (l : ℕ) < m := by have := Fin.lt_def.1 hlt; omega
            exact F.mul_mem (ih i l (Or.inr hl')).1 (ih l k (Or.inl hl')).2
          · rw [hv0 i l hgt, zero_mul]
            exact F.zero_mem
        simpa using F.sub_mem hsum hrest
      have hv : ∀ i k : Fin n, (k : ℕ) = m → k < i → v i k ∈ F := by
        intro i k hk hki
        have hwk : w k k ∈ F := hw k k hk le_rfl
        have hsum := hC' i k
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)] at hsum
        have hrest : ∑ l ∈ Finset.univ.erase k, v i l * w l k ∈ F := by
          refine sum_mem fun l hl => ?_
          rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hl) with hlt | hgt
          · have hl' : (l : ℕ) < m := by have := Fin.lt_def.1 hlt; omega
            exact F.mul_mem (ih i l (Or.inr hl')).1 (ih l k (Or.inl hl')).2
          · rw [hw0 l k hgt, mul_zero]
            exact F.zero_mem
        have h1 : v i k * w k k ∈ F := by simpa using F.sub_mem hsum hrest
        have h2 := F.mul_mem h1 (F.inv_mem hwk)
        rwa [mul_assoc, mul_inv_cancel₀ (hwd k), mul_one] at h2
      intro i k hik
      by_cases h' : (i : ℕ) < m ∨ (k : ℕ) < m
      · exact ih i k h'
      · push_neg at h'
        rcases le_or_gt i k with hle | hlt
        · have hi : (i : ℕ) = m := by have := Fin.le_def.1 hle; omega
          refine ⟨?_, hw i k hi hle⟩
          rcases eq_or_lt_of_le hle with heq | hlt'
          · rw [heq, hv1]
            exact F.one_mem
          · rw [hv0 i k hlt']
            exact F.zero_mem
        · have hk : (k : ℕ) = m := by have := Fin.lt_def.1 hlt; omega
          refine ⟨hv i k hk hlt, ?_⟩
          rw [hw0 i k hlt]
          exact F.zero_mem
  exact ⟨fun i k => (key (i + 1) i k (Or.inl (Nat.lt_succ_self _))).1,
    fun i k => (key (i + 1) i k (Or.inl (Nat.lt_succ_self _))).2⟩

theorem adjoin_entries_eq (K L : Type) [Field K] [Field L] [Algebra K L] (n : ℕ)
    (A : Matrix (Fin n) (Fin n) K) (u v w : Matrix (Fin n) (Fin n) L) (hA : A.det ≠ 0)
    (hu1 : ∀ k, u k k = 1) (hu0 : ∀ l k, l < k → u l k = 0)
    (hv1 : ∀ k, v k k = 1) (hv0 : ∀ l k, l < k → v l k = 0)
    (hw0 : ∀ l k, k < l → w l k = 0) (hwd : ∀ k, w k k ≠ 0)
    (h : A.map (algebraMap K L) * u = v * w) :
    IntermediateField.adjoin K (Set.range fun p : Fin n × Fin n => u p.1 p.2) =
      IntermediateField.adjoin K (Set.range fun p : Fin n × Fin n => v p.1 p.2) := by
  have hwT : w.BlockTriangular id := by
    intro l k hkl
    exact hw0 l k hkl
  have hdetw : w.det ≠ 0 := by
    rw [Matrix.det_of_upperTriangular hwT]
    exact Finset.prod_ne_zero_iff.2 fun k _ => hwd k
  have := Matrix.invertibleOfIsUnitDet w (isUnit_iff_ne_zero.2 hdetw)
  have hwiT : w⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hwT
  have hwwi : w * w⁻¹ = 1 := Matrix.mul_nonsing_inv w (isUnit_iff_ne_zero.2 hdetw)
  have hwid : ∀ k, w⁻¹ k k ≠ 0 := by
    intro k hk
    have e := congrFun (congrFun hwwi k) k
    rw [Matrix.mul_apply, Finset.sum_eq_single k, hk, mul_zero, Matrix.one_apply_eq] at e
    · exact zero_ne_one e
    · intro l _ hlk
      rcases lt_or_gt_of_ne hlk with hlt | hgt
      · rw [hw0 k l hlt, zero_mul]
      · rw [hwiT hgt, mul_zero]
    · intro hk'
      exact absurd (Finset.mem_univ k) hk'
  have hBA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.2 hA)
  have hBAm : A⁻¹.map (algebraMap K L) * A.map (algebraMap K L) = 1 := by
    rw [← Matrix.map_mul, hBA, Matrix.map_one _ (map_zero _) (map_one _)]
  have hC' : A⁻¹.map (algebraMap K L) * v = u * w⁻¹ := by
    have hu : u = A⁻¹.map (algebraMap K L) * v * w := by
      rw [Matrix.mul_assoc, ← h, ← Matrix.mul_assoc, hBAm, Matrix.one_mul]
    rw [hu, Matrix.mul_assoc, hwwi, Matrix.mul_one]
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨p, rfl⟩
    have hC : ∀ i k, (A⁻¹.map (algebraMap K L) * v) i k ∈
        IntermediateField.adjoin K (Set.range fun p : Fin n × Fin n => v p.1 p.2) := by
      intro i k
      rw [Matrix.mul_apply]
      refine sum_mem fun l _ => IntermediateField.mul_mem _ ?_ ?_
      · rw [Matrix.map_apply]
        exact IntermediateField.algebraMap_mem _ _
      · exact IntermediateField.subset_adjoin K _ ⟨(l, k), rfl⟩
    exact (entries_mem_of_eq_mul _ _ u w⁻¹ hC hu1 hu0 (fun l k hkl => hwiT hkl) hwid hC').1 p.1 p.2
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨p, rfl⟩
    have hC : ∀ i k, (A.map (algebraMap K L) * u) i k ∈
        IntermediateField.adjoin K (Set.range fun p : Fin n × Fin n => u p.1 p.2) := by
      intro i k
      rw [Matrix.mul_apply]
      refine sum_mem fun l _ => IntermediateField.mul_mem _ ?_ ?_
      · rw [Matrix.map_apply]
        exact IntermediateField.algebraMap_mem _ _
      · exact IntermediateField.subset_adjoin K _ ⟨(l, k), rfl⟩
    exact (entries_mem_of_eq_mul _ _ v w hC hv1 hv0 hw0 hwd h).1 p.1 p.2

end GlobalTheory.CompanionTheory.LuFields
end

section

open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.HopfFrob

theorem exists_algHom_ne_zero_of_not_isNilpotent
    {k : Type} [Field k] [IsAlgClosed k] {A : Type} [CommRing A] [Algebra k A]
    [Module.Finite k A] {f : A} (hf : ¬ IsNilpotent f) :
    ∃ x : A →ₐ[k] k, x f ≠ 0 := by
  haveI : IsArtinianRing A := isArtinian_of_tower k inferInstance
  rw [← mem_nilradical, nilradical_eq_sInf, Ideal.mem_sInf] at hf
  push_neg at hf
  obtain ⟨P, hP, hfP⟩ := hf
  haveI : P.IsPrime := hP
  haveI : P.IsMaximal := IsArtinianRing.isMaximal_of_isPrime P
  letI : Field (A ⧸ P) := Ideal.Quotient.field P
  have hbij : Function.Bijective (algebraMap k (A ⧸ P)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : k ≃ₐ[k] (A ⧸ P) := AlgEquiv.ofBijective (Algebra.ofId k (A ⧸ P)) hbij
  refine ⟨(e.symm : (A ⧸ P) →ₐ[k] k).comp (Ideal.Quotient.mkₐ k P), ?_⟩
  intro h
  apply hfP
  have h' : e.symm (Ideal.Quotient.mk P f) = 0 := h
  have h2 : Ideal.Quotient.mk P f = 0 := by
    simpa using h'
  exact Ideal.Quotient.eq_zero_iff_mem.mp h2

theorem exists_pow_eq_zero_of_isNilpotent
    {A : Type} [CommRing A] {p : ℕ} (hp : 2 ≤ p) {S : Set A}
    (hS : ∀ f ∈ S, f ^ p ∈ S) {f : A} (hfS : f ∈ S) (hf0 : f ≠ 0) (hf : IsNilpotent f) :
    ∃ g ∈ S, g ≠ 0 ∧ g ^ p = 0 := by
  classical
  obtain ⟨n, hn⟩ := hf
  have hex : ∃ m : ℕ, f ^ (p ^ m) = 0 :=
    ⟨n, pow_eq_zero_of_le (Nat.lt_pow_self (by omega)).le hn⟩
  have hspec := Nat.find_spec hex
  have hpos : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0] at hspec
    simp at hspec
    exact hf0 hspec
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hpos
  have hmem : ∀ j : ℕ, f ^ (p ^ j) ∈ S := by
    intro j
    induction j with
    | zero => simpa using hfS
    | succ j ih =>
      have := hS _ ih
      rwa [← pow_mul, ← pow_succ] at this
  refine ⟨f ^ (p ^ m), hmem m, Nat.find_min hex (m := m) (by omega), ?_⟩
  rw [← pow_mul, ← pow_succ]
  rw [hm] at hspec
  exact hspec

theorem exists_frobenius_fixed_or_killed :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A] (V : Submodule k A),
    V ≠ ⊥ → (∀ f ∈ V, f ^ p ∈ V) → ∃ f ∈ V, f ≠ 0 ∧ (f ^ p = 0 ∨ f ^ p = f) := by
  intro k _ _ p _ _ A _ _ _ V hV hVp
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  obtain ⟨f₀, hf₀V, hf₀⟩ := (Submodule.ne_bot_iff V).mp hV
  have key : ∀ n : ℕ, ∀ f ∈ V, f ≠ 0 →
      Module.finrank k (LinearMap.range (LinearMap.mulLeft k f)) = n →
      ∃ f ∈ V, f ≠ 0 ∧ (f ^ p = 0 ∨ f ^ p = f) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro f hfV hf0 hn
      by_cases hnil : IsNilpotent f
      · obtain ⟨g, hg, hg0, hgp⟩ := exists_pow_eq_zero_of_isNilpotent (S := (V : Set A)) hp
          (fun a ha => hVp a ha) hfV hf0 hnil
        exact ⟨g, hg, hg0, Or.inl hgp⟩
      obtain ⟨x, hx⟩ := exists_algHom_ne_zero_of_not_isNilpotent (k := k) hnil
      set c : k := (x f)⁻¹ with hc
      set f' : A := c • f with hf'
      have hf'V : f' ∈ V := V.smul_mem c hfV
      have hxf' : x f' = 1 := by
        simp [hf', hc, hx]
      have hf'0 : f' ≠ 0 := by
        intro h
        rw [h] at hxf'
        simp at hxf'
      set g : A := f' ^ p - f' with hg
      have hgV : g ∈ V := V.sub_mem (hVp _ hf'V) hf'V
      by_cases hg0 : g = 0
      · exact ⟨f', hf'V, hf'0, Or.inr (sub_eq_zero.mp hg0)⟩
      have hxg : x g = 0 := by
        simp [hg, hxf']
      obtain ⟨q, hq⟩ : ∃ q : A, g = f * q := by
        obtain ⟨r, hr⟩ : ∃ r, p = r + 1 := ⟨p - 1, by omega⟩
        refine ⟨c • (f' ^ r - 1), ?_⟩
        calc g = f' * (f' ^ r - 1) := by rw [hg, hr]; ring
          _ = f * (c • (f' ^ r - 1)) := by rw [mul_smul_comm, hf', smul_mul_assoc]
      have hlt : LinearMap.range (LinearMap.mulLeft k g) <
          LinearMap.range (LinearMap.mulLeft k f) := by
        refine lt_of_le_of_ne ?_ ?_
        · rintro _ ⟨a, rfl⟩
          exact ⟨q * a, by simp [hq, mul_assoc]⟩
        · intro heq
          have hmem : f ∈ LinearMap.range (LinearMap.mulLeft k g) := by
            rw [heq]
            exact ⟨1, by simp⟩
          obtain ⟨a, ha⟩ := hmem
          apply hx
          have : g * a = f := by simpa using ha
          rw [← this, map_mul, hxg, zero_mul]
      have hrank := Submodule.finrank_lt_finrank_of_lt hlt
      exact ih _ (hn ▸ hrank) g hgV hg0 rfl
  exact key _ f₀ hf₀V hf₀ rfl

end GlobalTheory.CompanionTheory.HopfFrob
end

section

open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.FiniteAlgebraUnit

theorem exists_isUnit_mem_of_forall_point :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (R : Type) [CommRing R] [Algebra k R] [Module.Finite k R]
    (U : Submodule k R), (∀ x : R →ₐ[k] k, ∃ t ∈ U, x t ≠ 0) → ∃ w ∈ U, IsUnit w := by
  intro k _ _ R _ _ _ U hU
  haveI : IsArtinianRing R := IsArtinianRing.of_finite k R
  haveI : Infinite k := IsAlgClosed.instInfinite

  have hpt : ∀ m : Ideal R, m.IsMaximal → ∃ x : R →ₐ[k] k, ∀ r ∈ m, x r = 0 := by
    intro m hm
    letI : Field (R ⧸ m) := Ideal.Quotient.field m
    haveI : Module.Finite k (R ⧸ m) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ k m).toLinearMap
        (Ideal.Quotient.mkₐ_surjective k m)
    let e : k ≃ₐ[k] (R ⧸ m) :=
      AlgEquiv.ofBijective (Algebra.ofId k (R ⧸ m))
        IsAlgClosed.algebraMap_bijective_of_isIntegral
    refine ⟨(e.symm : (R ⧸ m) →ₐ[k] k).comp (Ideal.Quotient.mkₐ k m), fun r hr => ?_⟩
    have h0 : Ideal.Quotient.mkₐ k m r = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hr
    change e.symm (Ideal.Quotient.mkₐ k m r) = 0
    rw [h0, map_zero]

  let f : Ideal R → Submodule k U := fun m => (m.restrictScalars k).comap U.subtype
  have hfin : (f '' {m : Ideal R | m.IsMaximal}).Finite :=
    (IsArtinianRing.setOfPred_isMaximal_finite R).image f
  let s : Finset (Submodule k U) := hfin.toFinset
  have htop : (⊤ : Submodule k U) ∉ s := by
    intro h
    obtain ⟨m, hm, hfm⟩ := (Set.Finite.mem_toFinset hfin).mp h
    obtain ⟨x, hx⟩ := hpt m hm
    obtain ⟨t, htU, ht⟩ := hU x
    have : (⟨t, htU⟩ : U) ∈ f m := by rw [hfm]; trivial
    exact ht (hx t this)
  have hne := Subspace.biUnion_ne_univ_of_top_notMem (k := k) (s := s) htop
  obtain ⟨w, hw⟩ : ∃ w : U, w ∉ ⋃ p ∈ s, (p : Set U) := by
    by_contra hcon
    push_neg at hcon
    exact hne (Set.eq_univ_of_forall hcon)
  refine ⟨w, w.2, ?_⟩
  by_contra hnu
  obtain ⟨m, hm, hwm⟩ := exists_max_ideal_of_mem_nonunits (show (w : R) ∈ nonunits R from hnu)
  apply hw
  simp only [Set.mem_iUnion]
  exact ⟨f m, (Set.Finite.mem_toFinset hfin).mpr ⟨m, hm, rfl⟩, hwm⟩

end GlobalTheory.CompanionTheory.FiniteAlgebraUnit
end

section

namespace GlobalTheory.CompanionTheory.WedgeSpan

theorem span_of_wedge_proportional (Ω V : Type) [Field Ω] [AddCommGroup V] [Module Ω V] (n : ℕ)
    (b e : Fin n → V) (t : Ω) (he : LinearIndependent Ω e) (ht : t ≠ 0)
    (hbe : exteriorPower.ιMulti Ω n b = t • exteriorPower.ιMulti Ω n e) (i : Fin n) :
    b i ∈ Submodule.span Ω (Set.range e) := by
  classical
  by_contra hx
  have hv : LinearIndependent Ω (Fin.cons (b i) e : Fin (n + 1) → V) :=
    linearIndependent_finCons.2 ⟨he, hx⟩
  have hbe' : ExteriorAlgebra.ιMulti Ω n b = t • ExteriorAlgebra.ιMulti Ω n e := by
    have := congrArg Subtype.val hbe
    simpa using this
  have htb : Matrix.vecTail (Fin.cons (b i) b : Fin (n + 1) → V) = b :=
    by funext k; simp [Matrix.vecTail]
  have hte : Matrix.vecTail (Fin.cons (b i) e : Fin (n + 1) → V) = e :=
    by funext k; simp [Matrix.vecTail]
  have h0 : ExteriorAlgebra.ιMulti Ω (n + 1) (Fin.cons (b i) b : Fin (n + 1) → V) = 0 :=
    (ExteriorAlgebra.ιMulti Ω (n + 1)).map_eq_zero_of_eq _ (i := 0) (j := i.succ)
      (by simp) (Fin.succ_ne_zero i).symm
  rw [ExteriorAlgebra.ιMulti_succ_apply, htb, hbe', mul_smul_comm, smul_eq_zero] at h0
  have h1 : ExteriorAlgebra.ιMulti Ω (n + 1) (Fin.cons (b i) e : Fin (n + 1) → V) = 0 := by
    rw [ExteriorAlgebra.ιMulti_succ_apply, hte]
    rcases h0 with h | h
    · exact absurd h ht
    · simpa using h
  have hfam := exteriorPower.ιMulti_family_linearIndependent_field (n := n + 1) hv
  apply hfam.ne_zero (Set.powersetCard.ofFinEmbEquiv (RelEmbedding.refl _))
  rw [exteriorPower.ιMulti_family, Equiv.symm_apply_apply]
  exact Subtype.ext h1

end GlobalTheory.CompanionTheory.WedgeSpan
end

section

namespace GlobalTheory.CompanionTheory.Ggeo.FrameDet

open scoped BigOperators

private theorem det_mem_of_forall_mem' {Ω : Type} [CommRing Ω] (R : Subring Ω) {n : ℕ}
    (P : Matrix (Fin n) (Fin n) Ω) (hP : ∀ i j, P i j ∈ R) : P.det ∈ R := by
  have h : P = R.subtype.mapMatrix (Matrix.of fun i j => (⟨P i j, hP i j⟩ : R)) := by
    ext i j
    rfl
  rw [h, ← RingHom.map_det]
  exact (Matrix.det (Matrix.of fun i j => (⟨P i j, hP i j⟩ : R))).2

theorem matrix_eq_of_linearIndependent {Ω M : Type} [Field Ω] [AddCommGroup M] [Module Ω M]
    {n : ℕ} {w : Fin n → M} (hw : LinearIndependent Ω w)
    {C D : Matrix (Fin n) (Fin n) Ω}
    (h : ∀ i, ∑ j, C i j • w j = ∑ j, D i j • w j) : C = D := by
  ext i j
  have h' : ∑ k, (C i k - D i k) • w k = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, h i, sub_self]
  exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hw (fun k => C i k - D i k) h' j)

theorem sum_smul_sum_smul {Ω M : Type} [Field Ω] [AddCommGroup M] [Module Ω M]
    {n : ℕ} (w : Fin n → M) (C D : Matrix (Fin n) (Fin n) Ω) (i : Fin n) :
    ∑ j, C i j • ∑ k, D j k • w k = ∑ k, (C * D) i k • w k := by
  simp only [Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  exact Finset.sum_comm

theorem det_eq_unit_mul : ∀ (Ω M : Type) [Field Ω] [AddCommGroup M] [Module Ω M] (R : Subring Ω) (n : ℕ) (u : Fin n → M) (A B : Matrix (Fin n) (Fin n) Ω), LinearIndependent Ω u → LinearIndependent Ω (fun i => ∑ j, A i j • u j) → LinearIndependent Ω (fun i => ∑ j, B i j • u j) → Submodule.span R (Set.range fun i => ∑ j, A i j • u j) = Submodule.span R (Set.range fun i => ∑ j, B i j • u j) → ∃ c : Ω, c ∈ R ∧ c⁻¹ ∈ R ∧ c ≠ 0 ∧ B.det = c * A.det := by
  intro Ω M _ _ _ R n u A B hu ha _ hspan
  have key : ∀ a b : Fin n → M, Submodule.span R (Set.range b) ≤ Submodule.span R (Set.range a) →
      ∃ P : Matrix (Fin n) (Fin n) Ω, (∀ i j, P i j ∈ R) ∧ ∀ i, b i = ∑ j, P i j • a j := by
    intro a b hle
    have hex : ∀ i, ∃ c : Fin n → R, ∑ j, c j • a j = b i := fun i =>
      (Submodule.mem_span_range_iff_exists_fun R).mp (hle (Submodule.subset_span ⟨i, rfl⟩))
    choose c hc using hex
    refine ⟨Matrix.of fun i j => (c i j : Ω), fun i j => (c i j).2, fun i => ?_⟩
    rw [← hc i]
    exact Finset.sum_congr rfl fun j _ => Subring.smul_def _ _
  obtain ⟨P, hPR, hP⟩ := key (fun i => ∑ j, A i j • u j) (fun i => ∑ j, B i j • u j) hspan.ge
  obtain ⟨Q, hQR, hQ⟩ := key (fun i => ∑ j, B i j • u j) (fun i => ∑ j, A i j • u j) hspan.le
  have hP' : ∀ i, ∑ j, B i j • u j = ∑ j, P i j • ∑ k, A j k • u k := hP
  have hQ' : ∀ i, ∑ j, A i j • u j = ∑ j, Q i j • ∑ k, B j k • u k := hQ
  have hBPA : B = P * A := GlobalTheory.CompanionTheory.Ggeo.FrameDet.matrix_eq_of_linearIndependent hu fun i =>
    (hP' i).trans (GlobalTheory.CompanionTheory.Ggeo.FrameDet.sum_smul_sum_smul u P A i)
  have hQP : Q * P = 1 := by
    apply GlobalTheory.CompanionTheory.Ggeo.FrameDet.matrix_eq_of_linearIndependent ha
    intro i
    calc ∑ j, (Q * P) i j • ∑ k, A j k • u k
        = ∑ j, Q i j • ∑ k, P j k • ∑ l, A k l • u l :=
          (GlobalTheory.CompanionTheory.Ggeo.FrameDet.sum_smul_sum_smul (fun k => ∑ l, A k l • u l) Q P i).symm
      _ = ∑ j, Q i j • ∑ k, B j k • u k := Finset.sum_congr rfl fun j _ => by rw [hP' j]
      _ = ∑ k, A i k • u k := (hQ' i).symm
      _ = ∑ j, (1 : Matrix (Fin n) (Fin n) Ω) i j • ∑ k, A j k • u k := by
          simp [Matrix.one_apply]
  have hdet : P.det * Q.det = 1 := by
    rw [mul_comm, ← Matrix.det_mul, hQP, Matrix.det_one]
  refine ⟨P.det, det_mem_of_forall_mem' R P hPR, ?_, left_ne_zero_of_mul_eq_one hdet, ?_⟩
  · rw [inv_eq_of_mul_eq_one_right hdet]
    exact det_mem_of_forall_mem' R Q hQR
  · rw [hBPA, Matrix.det_mul]

end GlobalTheory.CompanionTheory.Ggeo.FrameDet
end

section

open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.CompanionTheory.Ggeo

private theorem map_aeval_int' {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (a : A)
    (q : Polynomial ℤ) : f (Polynomial.aeval a q) = Polynomial.aeval (f a) q := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂,
    RingHom.ext_int (f.comp (algebraMap ℤ A)) (algebraMap ℤ B)]

theorem unit_of_local_hom_charZero_nf : ∀ (O F L K : Type) [CommRing O] [Field F] [NumberField F] [CommRing L] [Field K] [CharZero K] (β : O →+* F) (θ : O →+* L) (ρ : L →+* K), IsLocalHom ρ → (∀ a, β a = 0 → θ a = 0) → ∀ b, β b ≠ 0 → IsUnit (θ b) := by
  intro O F L K _ _ _ _ _ _ β θ ρ hρ hker b hb
  have halg : IsAlgebraic ℤ (β b) :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ F).mpr (Algebra.IsAlgebraic.isAlgebraic (β b))
  obtain ⟨q, hq0, hq⟩ :=
    halg.exists_nonzero_coeff_and_aeval_eq_zero (mem_nonZeroDivisors_of_ne_zero hb)
  have h1 : β (Polynomial.aeval b q) = 0 := by rw [map_aeval_int', hq]
  have h2 : ρ (θ (Polynomial.aeval b q)) = 0 := by rw [hker _ h1, map_zero]
  rw [map_aeval_int', map_aeval_int'] at h2
  have h3 : ρ (θ b) ≠ 0 := by
    intro h0
    rw [h0, ← Polynomial.coeff_zero_eq_aeval_zero'] at h2
    exact hq0 (by simpa using h2)
  exact hρ.map_nonunit _ (isUnit_iff_ne_zero.mpr h3)

end GlobalTheory.CompanionTheory.Ggeo
end
