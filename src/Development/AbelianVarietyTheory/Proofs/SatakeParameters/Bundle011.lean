module

public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.LinearIndependentWave
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle108
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle002
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsStableGraphOfEqualAnnihilators
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.RingTheory.Flat.Basic

@[expose] public section

section

noncomputable section

namespace GlobalTheory.FourierSpan

variable {G : Type} [AddCommGroup G]

def annihIn (χ : G → G → ℂ) (hχ : GlobalTheory.PlaceModel.IsBichar χ) (Yh L : AddSubgroup G) : AddSubgroup G where
  carrier := {y | y ∈ Yh ∧ ∀ x ∈ L, χ x y = 1}
  add_mem' := fun {a b} ha hb => ⟨Yh.add_mem ha.1 hb.1, fun x hx => by rw [hχ.right, ha.2 x hx, hb.2 x hx, one_mul]⟩
  zero_mem' := ⟨Yh.zero_mem, fun x _ => hχ.zero_right x⟩
  neg_mem' := fun {a} ha => ⟨Yh.neg_mem ha.1, fun x hx => by
    have e : χ x (-a) * χ x a = 1 := by rw [← hχ.right, neg_add_cancel, hχ.zero_right]
    rwa [ha.2 x hx, mul_one] at e⟩

theorem bichar_pow_left {χ : G → G → ℂ} (hχ : GlobalTheory.PlaceModel.IsBichar χ) (k : ℕ) (x y : G) :
    χ (k • x) y = χ x y ^ k := by
  induction k with
  | zero => simp [hχ.zero_left]
  | succ k ih => rw [succ_nsmul, hχ.left, ih, pow_succ]

theorem mem_span_translates_of_fixed {G V : Type} [AddCommGroup G] [AddCommGroup V] [Module ℂ V]
    (χ : G → G → ℂ) (hχ : GlobalTheory.PlaceModel.IsBichar χ) (ρ : G → V →ₗ[ℂ] V) (X Yh L L' K : AddSubgroup G)
    (hLL' : L ≤ L') (hL'X : L' ≤ X) (hKY : K ≤ Yh) (ρ0 : ∀ v, ρ 0 v = v)
    (ρX : ∀ x ∈ X, ∀ x' ∈ X, ∀ v, ρ x (ρ x' v) = ρ (x + x') v)
    (ρY : ∀ y ∈ Yh, ∀ y' ∈ Yh, ∀ v, ρ y (ρ y' v) = ρ (y + y') v)
    (ρXY : ∀ x ∈ X, ∀ y ∈ Yh, ∀ v, ρ x (ρ y v) = χ x y • ρ y (ρ x v))
    (hR : ∃ R : Finset G, ∀ t ∈ L', ∃ r ∈ R, t - r ∈ L)
    (hLK : ∀ x ∈ L', ∀ y ∈ K, χ x y = 1)
    (hsep : ∀ y ∈ Yh, (∀ x ∈ L', χ x y = 1) → y ∈ K)
    (W : Submodule ℂ V) (hWX : ∀ v ∈ W, ∀ x ∈ X, ρ x v ∈ W) (hWY : ∀ v ∈ W, ∀ y ∈ Yh, ρ y v ∈ W)
    (f : V) (hfW : f ∈ W) (hfL : ∀ x ∈ L, ρ x f = f) (hfK : ∀ y ∈ K, ρ y f = f) :
    f ∈ Submodule.span ℂ {v | ∃ r ∈ X, ∃ g ∈ W, (∀ x ∈ L, ρ x g = g) ∧
      (∀ y ∈ Yh, (∀ x ∈ L, χ x y = 1) → ρ y g = g) ∧ v = ρ r g} := by
  classical
  obtain ⟨R, hR⟩ := hR
  have negR : ∀ x y, χ x (-y) * χ x y = 1 := fun x y => by rw [← hχ.right, neg_add_cancel, hχ.zero_right]
  set P := annihIn χ hχ Yh L with hPdef
  have memP : ∀ y, y ∈ P ↔ y ∈ Yh ∧ ∀ x ∈ L, χ x y = 1 := fun y => Iff.rfl
  have hPY : ∀ y ∈ P, y ∈ Yh := fun y hy => ((memP y).1 hy).1
  have hKP : K ≤ P := fun y hy => (memP y).2 ⟨hKY hy, fun x hx => hLK x (hLL' hx) y hy⟩

  have wdQ : ∀ y ∈ P, ∀ u v : L', (QuotientAddGroup.mk u : L' ⧸ L.addSubgroupOf L') = QuotientAddGroup.mk v →
      χ u y = χ v y := by
    intro y hy u v huv
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at huv
    have e : (v : G) = u + ((-u + v : L') : G) := by simp
    rw [e, hχ.left, ((memP y).1 hy).2 _ huv, mul_one]
  have wdQ' : ∀ h : V, (∀ k ∈ K, ρ k h = h) → ∀ u v : P,
      (QuotientAddGroup.mk u : P ⧸ K.addSubgroupOf P) = QuotientAddGroup.mk v → ρ u h = ρ v h := by
    intro h hh u v huv
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at huv
    have e : (v : G) = u + ((-u + v : P) : G) := by simp
    rw [e, ← ρY _ (hPY _ u.2) _ (hKY huv), hh _ huv]

  have finQ : Finite (L' ⧸ L.addSubgroupOf L') := by
    let φ : R → L' ⧸ L.addSubgroupOf L' := fun r =>
      if h : (r : G) ∈ L' then QuotientAddGroup.mk ⟨r, h⟩ else 0
    refine Finite.of_surjective φ ?_
    intro q
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨r, hr, htr⟩ := hR t t.2
    have hrL' : r ∈ L' := by
      have := L'.sub_mem t.2 (hLL' htr)
      simpa using this
    refine ⟨⟨r, hr⟩, ?_⟩
    simp only [φ, dif_pos hrL']
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_add, AddSubgroup.coe_neg]
    convert htr using 1
    simp only
    abel
  letI : Fintype (L' ⧸ L.addSubgroupOf L') := Fintype.ofFinite _
  set n := Fintype.card (L' ⧸ L.addSubgroupOf L') with hn_def
  have hn : 0 < n := Fintype.card_pos
  have powQ : ∀ y ∈ P, ∀ u : L', χ u y ^ n = 1 := by
    intro y hy u
    have hnu : ((n • u : L') : G) ∈ L := by
      have h0 : n • (QuotientAddGroup.mk u : L' ⧸ L.addSubgroupOf L') = 0 := card_nsmul_eq_zero
      rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at h0
      exact h0
    rw [← bichar_pow_left hχ, ← AddSubgroup.coe_nsmul]
    exact ((memP y).1 hy).2 _ hnu

  have finS : ({z : ℂ | z ^ n = 1} : Set ℂ).Finite :=
    (Polynomial.nthRoots n (1 : ℂ)).toFinset.finite_toSet.subset fun z hz => by
      simp only [Finset.mem_coe, Multiset.mem_toFinset]
      exact (Polynomial.mem_nthRoots hn).2 hz
  haveI := finS.to_subtype
  have finQ' : Finite (P ⧸ K.addSubgroupOf P) := by
    let Φ : (P ⧸ K.addSubgroupOf P) → ((L' ⧸ L.addSubgroupOf L') → ({z : ℂ | z ^ n = 1} : Set ℂ)) :=
      fun q' q => ⟨χ (q.out : L') (q'.out : P), powQ _ (q'.out).2 _⟩
    refine Finite.of_injective Φ ?_
    intro a b hab
    rw [← QuotientAddGroup.out_eq' a, ← QuotientAddGroup.out_eq' b, QuotientAddGroup.eq,
      AddSubgroup.mem_addSubgroupOf]
    refine hsep _ (hPY _ (-a.out + b.out : P).2) fun x hx => ?_
    have e := congrArg Subtype.val (congrFun hab (QuotientAddGroup.mk ⟨x, hx⟩))
    simp only [Φ] at e
    have ea := wdQ _ (a.out).2 ((QuotientAddGroup.mk ⟨x, hx⟩ : L' ⧸ L.addSubgroupOf L').out) ⟨x, hx⟩
      (QuotientAddGroup.out_eq' _)
    have eb := wdQ _ (b.out).2 ((QuotientAddGroup.mk ⟨x, hx⟩ : L' ⧸ L.addSubgroupOf L').out) ⟨x, hx⟩
      (QuotientAddGroup.out_eq' _)
    rw [ea, eb] at e
    rw [AddSubgroup.coe_add, AddSubgroup.coe_neg, hχ.right, ← e]
    exact negR _ _
  letI : Fintype (P ⧸ K.addSubgroupOf P) := Fintype.ofFinite _

  have hKh : ∀ r ∈ L', ∀ k ∈ K, ρ k (ρ (-r) f) = ρ (-r) f := by
    intro r hr k hk
    have := ρXY (-r) (X.neg_mem (hL'X hr)) k (hKY hk) f
    rw [hfK k hk, hLK _ (L'.neg_mem hr) k hk, one_smul] at this
    exact this.symm
  let g : (L' ⧸ L.addSubgroupOf L') → V := fun q =>
    ∑ q' : P ⧸ K.addSubgroupOf P, ρ ((q'.out : P) : G) (ρ (-((q.out : L') : G)) f)
  have gW : ∀ q, g q ∈ W := fun q => Submodule.sum_mem _ fun q' _ =>
    hWY _ (hWX f hfW _ (X.neg_mem (hL'X (q.out).2))) _ (hPY _ (q'.out).2)
  have gL : ∀ q, ∀ x ∈ L, ρ x (g q) = g q := by
    intro q x hx

    simp only [g, map_sum]
    refine Finset.sum_congr rfl fun q' _ => ?_
    have hxX : x ∈ X := hL'X (hLL' hx)
    have hrX : -((q.out : L') : G) ∈ X := X.neg_mem (hL'X (q.out).2)
    rw [ρXY x hxX _ (hPY _ (q'.out).2), ((memP _).1 (q'.out).2).2 x hx, one_smul, ρX x hxX _ hrX, add_comm,
      ← ρX _ hrX _ hxX, hfL x hx]
  have gP : ∀ q, ∀ y ∈ Yh, (∀ x ∈ L, χ x y = 1) → ρ y (g q) = g q := by
    intro q y hy hyL
    have hyP : y ∈ P := (memP y).2 ⟨hy, hyL⟩

    simp only [g, map_sum]
    refine Eq.trans ?_ (Equiv.sum_comp (Equiv.addRight (QuotientAddGroup.mk ⟨y, hyP⟩ : P ⧸ K.addSubgroupOf P))
      (fun q' : P ⧸ K.addSubgroupOf P => ρ ((q'.out : P) : G) (ρ (-((q.out : L') : G)) f)))
    refine Finset.sum_congr rfl fun q' _ => ?_
    simp only [Equiv.coe_addRight]
    rw [ρY y hy _ (hPY _ (q'.out).2), ← wdQ' _ (hKh _ (q.out).2) (q'.out + ⟨y, hyP⟩) _ ?_]
    · rw [AddSubgroup.coe_add, add_comm]
    · rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq', QuotientAddGroup.out_eq']
  have key : ∑ q : L' ⧸ L.addSubgroupOf L', ρ ((q.out : L') : G) (g q) = (n : ℂ) • f := by
    have step : ∀ q : L' ⧸ L.addSubgroupOf L', ∀ q' : P ⧸ K.addSubgroupOf P,
        ρ ((q.out : L') : G) (ρ ((q'.out : P) : G) (ρ (-((q.out : L') : G)) f)) =
          χ ((q.out : L') : G) ((q'.out : P) : G) • ρ ((q'.out : P) : G) f := by
      intro q q'
      have hrX := hL'X (q.out).2
      rw [ρXY _ hrX _ (hPY _ (q'.out).2), ρX _ hrX _ (X.neg_mem hrX), add_neg_cancel, ρ0]

    simp only [g, map_sum, step]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul]
    rw [Finset.sum_eq_single (0 : P ⧸ K.addSubgroupOf P)]
    · have h0K : (((0 : P ⧸ K.addSubgroupOf P).out : P) : G) ∈ K := by
        have := QuotientAddGroup.out_eq' (0 : P ⧸ K.addSubgroupOf P)
        rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at this
        exact this
      have h1 : ∀ q : L' ⧸ L.addSubgroupOf L',
          χ ((q.out : L') : G) (((0 : P ⧸ K.addSubgroupOf P).out : P) : G) = 1 :=
        fun q => hLK _ (q.out).2 _ h0K
      rw [hfK _ h0K]
      simp only [h1, Finset.sum_const, Finset.card_univ, ← hn_def, nsmul_eq_mul, mul_one]
    · intro q' _ hq'
      have hnK : ((q'.out : P) : G) ∉ K := by
        intro hK
        apply hq'
        rw [← QuotientAddGroup.out_eq' q', QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
        exact hK
      obtain ⟨x, hx, hxy⟩ : ∃ x ∈ L', χ x ((q'.out : P) : G) ≠ 1 := by
        by_contra hc
        push_neg at hc
        exact hnK (hsep _ (hPY _ (q'.out).2) hc)
      have hyP := (q'.out).2
      have shift : ∀ q : L' ⧸ L.addSubgroupOf L',
          χ (((q + (QuotientAddGroup.mk (⟨x, hx⟩ : L') : L' ⧸ L.addSubgroupOf L')).out : L') : G) ((q'.out : P) : G) =
            χ ((q.out : L') : G) ((q'.out : P) : G) * χ x ((q'.out : P) : G) := by
        intro q
        rw [← wdQ _ hyP (q.out + (⟨x, hx⟩ : L')) _ ?_, AddSubgroup.coe_add, hχ.left]
        rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq', QuotientAddGroup.out_eq']
      have hS2 := Equiv.sum_comp (Equiv.addRight (QuotientAddGroup.mk ⟨x, hx⟩ : L' ⧸ L.addSubgroupOf L'))
        (fun q : L' ⧸ L.addSubgroupOf L' => χ ((q.out : L') : G) ((q'.out : P) : G))
      simp only [Equiv.coe_addRight, shift, ← Finset.sum_mul] at hS2
      have hsum : ∑ q : L' ⧸ L.addSubgroupOf L', χ ((q.out : L') : G) ((q'.out : P) : G) = 0 := by
        have h3 : (∑ q : L' ⧸ L.addSubgroupOf L', χ ((q.out : L') : G) ((q'.out : P) : G)) *
            (χ x ((q'.out : P) : G) - 1) = 0 := by
          rw [mul_sub, hS2, mul_one, sub_self]
        exact (mul_eq_zero.1 h3).resolve_right (sub_ne_zero.2 hxy)
      rw [hsum, zero_smul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hf : f = (n : ℂ)⁻¹ • ∑ q : L' ⧸ L.addSubgroupOf L', ρ ((q.out : L') : G) (g q) := by
    rw [key, smul_smul, inv_mul_cancel₀ hn0, one_smul]
  rw [hf]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun q _ => Submodule.subset_span ?_)
  exact ⟨_, hL'X (q.out).2, g q, gW q, gL q, gP q, rfl⟩
end GlobalTheory.FourierSpan
end
end

section

open NumberField GlobalTheory.LKInvGood
open scoped TensorProduct

namespace GlobalTheory.LocIso

theorem tensor_padicInt_equiv_locOrder : ∀ (O : Type) [Ring O] [Module.Free ℤ O] [Module.Finite ℤ O] (ℓ : ℕ) [Fact ℓ.Prime], ∃ ι : O ⊗[ℤ] ℤ_[ℓ] ≃+* locOrder ℓ (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := O)).toRingHom.range, ∀ o : O, (ι (o ⊗ₜ[ℤ] 1) : ℚ_[ℓ] ⊗[ℚ] (ℚ ⊗[ℤ] O)) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] o) := by
  intro O _ _ _ ℓ _
  let g1 : O →ₐ[ℤ] ℚ_[ℓ] ⊗[ℚ] (ℚ ⊗[ℤ] O) :=
    ((Algebra.TensorProduct.includeRight : (ℚ ⊗[ℤ] O) →ₐ[ℚ] ℚ_[ℓ] ⊗[ℚ] (ℚ ⊗[ℤ] O)).toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := O)).toRingHom).toIntAlgHom
  let g2 : ℤ_[ℓ] →ₐ[ℤ] ℚ_[ℓ] ⊗[ℚ] (ℚ ⊗[ℤ] O) :=
    ((Algebra.TensorProduct.includeLeftRingHom (R := ℚ) (A := ℚ_[ℓ]) (B := ℚ ⊗[ℤ] O)).comp
      PadicInt.Coe.ringHom).toIntAlgHom
  have hg1 : ∀ x, g1 x = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] x) := fun _ => rfl
  have hg2 : ∀ y : ℤ_[ℓ], g2 y = (y : ℚ_[ℓ]) ⊗ₜ[ℚ] (1 : ℚ ⊗[ℤ] O) := fun _ => rfl
  have hg : ∀ x y, Commute (g1 x) (g2 y) := by
    intro x y
    simp only [hg1, hg2, Commute, SemiconjBy, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  let f := Algebra.TensorProduct.lift g1 g2 hg
  have hf : ∀ (o : O) (a : ℤ_[ℓ]), f (o ⊗ₜ a) = (a : ℚ_[ℓ]) ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] o) := by
    intro o a
    simp only [f, Algebra.TensorProduct.lift_tmul, hg1, hg2, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  have hinj : Function.Injective f := by
    have hl : Function.Injective (LinearMap.lTensor O (PadicInt.Coe.ringHom (p := ℓ)).toIntAlgHom.toLinearMap) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ (fun a b h => Subtype.ext h)
    have heq : (f : O ⊗[ℤ] ℤ_[ℓ] → ℚ_[ℓ] ⊗[ℚ] (ℚ ⊗[ℤ] O)) =
        (TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ ℚ ℚ_[ℓ] ℚ_[ℓ] O).symm ∘
          (TensorProduct.comm ℤ O ℚ_[ℓ]) ∘
          (LinearMap.lTensor O (PadicInt.Coe.ringHom (p := ℓ)).toIntAlgHom.toLinearMap) := by
      funext x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul o a =>
        simp only [Function.comp_apply, LinearMap.lTensor_tmul, TensorProduct.comm_tmul,
          TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul, hf]
        rfl
      | add x y hx hy =>
        simp only [Function.comp_apply, map_add (f := _)] at hx hy ⊢
        rw [hx, hy]
    rw [heq]
    exact (LinearEquiv.injective _).comp ((LinearEquiv.injective _).comp hl)
  have hmem : ∀ x, f x ∈ locOrder ℓ (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := O)).toRingHom.range := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul o a =>
      rw [hf]
      have h1 : (a : ℚ_[ℓ]) ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] o) =
          algebraMap ℤ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] (ℚ ⊗[ℤ] O)) a * ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] o)) := by
        rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        rfl
      rw [h1]
      refine Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ a) (Algebra.subset_adjoin ?_)
      exact ⟨(1 : ℚ) ⊗ₜ[ℤ] o, ⟨o, rfl⟩, rfl⟩
    | add x y hx hy => rw [map_add (f := _)]; exact Subalgebra.add_mem _ hx hy
  let g : O ⊗[ℤ] ℤ_[ℓ] →+* locOrder ℓ (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := O)).toRingHom.range :=
    (f.toRingHom).codRestrict _ hmem
  have hsurj : Function.Surjective g := by
    rintro ⟨y, hy⟩
    have hy' : y ∈ (locOrder ℓ (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := O)).toRingHom.range).toSubring := hy
    rw [locOrder, Algebra.adjoin_eq_ring_closure] at hy'
    have hle : Subring.closure (Set.range (algebraMap ℤ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] (ℚ ⊗[ℤ] O))) ∪
        ((fun b => (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] b) '' ((Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := O)).toRingHom.range : Set (ℚ ⊗[ℤ] O)))) ≤ f.toRingHom.range := by
      rw [Subring.closure_le]
      rintro _ (⟨a, rfl⟩ | ⟨_, ⟨o, rfl⟩, rfl⟩)
      · refine ⟨(1 : O) ⊗ₜ a, ?_⟩
        change f _ = _
        rw [hf, Algebra.TensorProduct.algebraMap_apply]
        rfl
      · refine ⟨o ⊗ₜ (1 : ℤ_[ℓ]), ?_⟩
        change f _ = _
        rw [hf]
        simp
    obtain ⟨x, hx⟩ := hle hy'
    exact ⟨x, Subtype.ext hx⟩
  refine ⟨RingEquiv.ofBijective g ⟨fun x y h => hinj (congrArg Subtype.val h), hsurj⟩, fun o => ?_⟩
  change f (o ⊗ₜ 1) = _
  rw [hf]
  simp

end GlobalTheory.LocIso
end

section

open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.EtC.Tr

theorem diagComplHom_isFinite_etale : ∀ {Z X : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [Etale f],
    IsFinite (GlobalTheory.EtC.Tr.diagComplHom f) ∧ Etale (GlobalTheory.EtC.Tr.diagComplHom f) := by
  intro Z X f _ _
  have hopen : IsOpen (Set.range (pullback.diagonal f)) :=
    (pullback.diagonal f).isOpenEmbedding.isOpen_range
  have hcl : IsClosedImmersion (diagCompl f).ι :=
    IsClosedImmersion.of_isPreimmersion _ (by
      rw [Scheme.Opens.range_ι]
      exact hopen.isClosed_compl)
  unfold diagComplHom
  exact ⟨inferInstance, inferInstance⟩

end GlobalTheory.EtC.Tr
end

section

open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.EtC.Tr

theorem fibrePointsLE_diagComplHom {Z X : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [Etale f] (n : ℕ)
    (h : FibrePointsLE f (n + 1)) : FibrePointsLE (diagComplHom f) n := by
  intro K _ y s hs hinj
  set t : Fin (n + 1) → (Spec (CommRingCat.of K) ⟶ Z) := fun j => s j ≫ (diagCompl f).ι ≫ pullback.fst f f
    with ht
  have hsnd : ∀ j, s j ≫ (diagCompl f).ι ≫ pullback.snd f f = y := fun j => by
    simpa [diagComplHom] using hs j
  have htf : ∀ j, t j ≫ f = y ≫ f := fun j => by
    simp only [ht, Category.assoc, pullback.condition]
    rw [← hsnd j]
    simp only [Category.assoc]
  have hne : ∀ j, t j ≠ y := by
    intro j hj
    have heq : s j ≫ (diagCompl f).ι = y ≫ pullback.diagonal f := by
      apply pullback.hom_ext
      · simp [← hj, ht]
      · simp [hsnd j]
    obtain ⟨x⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstance
    have h1 : (s j ≫ (diagCompl f).ι).base x ∈ diagCompl f := by
      rw [← SetLike.mem_coe, ← Scheme.Opens.range_ι]
      exact ⟨_, rfl⟩
    rw [heq] at h1
    exact h1 ⟨_, rfl⟩
  apply h K (y ≫ f) (Fin.cons y t)
  · intro j
    cases j using Fin.cases with
    | zero => simp
    | succ j => simpa using htf j
  · intro i j hij
    cases i using Fin.cases <;> cases j using Fin.cases
    · rfl
    · simp only [Fin.cons_zero, Fin.cons_succ] at hij; exact absurd hij.symm (hne _)
    · simp only [Fin.cons_zero, Fin.cons_succ] at hij; exact absurd hij (hne _)
    · rename_i i j
      simp only [Fin.cons_succ] at hij
      congr 1
      apply hinj
      rw [← cancel_mono (diagCompl f).ι]
      apply pullback.hom_ext
      · simpa [ht] using hij
      · simp [hsnd i, hsnd j]

end GlobalTheory.EtC.Tr
end

section

open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.EtC.Tr

theorem ringHom_count_bound {A B : Type} [CommRing A] [CommRing B] (g : A →+* B)
    (hg : g.Finite) : ∃ n : ℕ, ∀ (K : Type) [Field K] (ψ : A →+* K) (φ : Fin (n + 1) → (B →+* K)),
      (∀ j, (φ j).comp g = ψ) → ¬ Function.Injective φ := by
  letI := g.toAlgebra
  have hfin : Module.Finite A B := hg
  obtain ⟨S, hS⟩ := hfin.fg_top
  refine ⟨S.card, fun K _ ψ φ hφ hinj => ?_⟩
  let L : (Fin (S.card + 1) → K) →ₗ[K] (S → K) :=
    { toFun := fun c s => ∑ j, c j * φ j (s : B)
      map_add' := by intro c d; funext s; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by intro a c; funext s; simp [Finset.mul_sum, mul_assoc] }
  have hker : LinearMap.ker L ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by simp)
  obtain ⟨c, hc, hc0⟩ := (Submodule.ne_bot_iff _).1 hker
  have hcS : ∀ s ∈ S, ∑ j, c j * φ j s = 0 := by
    intro s hs
    have := congrFun (LinearMap.mem_ker.1 hc) ⟨s, hs⟩
    simpa [L] using this
  have hall : ∀ b : B, ∑ j, c j * φ j b = 0 := by
    intro b
    have hb : b ∈ Submodule.span A (S : Set B) := hS ▸ Submodule.mem_top
    induction hb using Submodule.span_induction with
    | mem x hx => exact hcS x hx
    | zero => simp
    | add x y _ _ hx hy => simp [mul_add, Finset.sum_add_distrib, hx, hy]
    | smul a x _ hx =>
      have e : ∀ j, φ j (a • x) = ψ a * φ j x := by
        intro j
        rw [Algebra.smul_def, map_mul, ← hφ j]
        rfl
      simp only [e]
      calc ∑ j, c j * (ψ a * φ j x) = ψ a * ∑ j, c j * φ j x := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
        _ = 0 := by rw [hx, mul_zero]
  have hli := (linearIndependent_monoidHom B K).comp (fun j => (φ j : B →* K))
    (fun i j h => hinj (RingHom.ext fun b => DFunLike.congr_fun h b))
  have := (Fintype.linearIndependent_iff.1 hli) c (by
    funext b
    simpa [Finset.sum_apply, smul_eq_mul] using hall b)
  exact hc0 (funext this)

theorem finite_fibrePointsLE_of_isAffine : ∀ {Z X : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [IsAffine X],
    ∃ n, GlobalTheory.EtC.Tr.FibrePointsLE f n := by
  intro Z X f _ _
  haveI := isAffine_of_isAffineHom f
  obtain ⟨n, hn⟩ := ringHom_count_bound f.appTop.hom f.finite_appTop
  refine ⟨n, fun K _ y s hs hinj => ?_⟩
  refine hn K (y.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom
    (fun j => ((s j).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom) (fun j => ?_) ?_
  · rw [← hs j, Scheme.Hom.comp_appTop, Category.assoc]
    simp only [CommRingCat.hom_comp]
  · intro i j h
    apply hinj
    apply ext_of_isAffine
    exact (cancel_mono (Scheme.ΓSpecIso (CommRingCat.of K)).hom).1 (CommRingCat.hom_ext h)

end GlobalTheory.EtC.Tr
end

section


theorem _root_.GlobalTheory.T.exists_stable_graph_of_equal_annihilators : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ι : Type) (C : ι → Subalgebra ℂ (Module.End ℂ V)) (U₁ U₂ : Submodule ℂ V), FiniteDimensional ℂ U₁ → U₁ ≠ ⊥ → U₂ ≠ ⊥ → (∀ v, ∀ c ∈ C v, ∀ x ∈ U₁, c x ∈ U₁) → (∀ v, ∀ c ∈ C v, ∀ x ∈ U₂, c x ∈ U₂) → (∀ v w, v ≠ w → ∀ c ∈ C v, ∀ d ∈ C w, (∀ x ∈ U₁, c (d x) = d (c x)) ∧ (∀ x ∈ U₂, c (d x) = d (c x))) → (∀ v, ∀ c ∈ C v, (∀ x ∈ U₁, c x = 0) ↔ (∀ x ∈ U₂, c x = 0)) → (∀ Y ≤ U₁, (∀ v, ∀ c ∈ C v, ∀ x ∈ Y, c x ∈ Y) → Y = ⊥ ∨ Y = U₁) → (∀ Y ≤ U₂, (∀ v, ∀ c ∈ C v, ∀ x ∈ Y, c x ∈ Y) → Y = ⊥ ∨ Y = U₂) → ∃ X : Submodule ℂ (V × V), X ≠ ⊥ ∧ (∀ z ∈ X, z.1 ∈ U₁ ∧ z.2 ∈ U₂) ∧ (∀ v, ∀ c ∈ C v, ∀ z ∈ X, (c z.1, c z.2) ∈ X) ∧ (∀ u, ((0 : V), u) ∈ X → u = 0) ∧ (∀ u, (u, (0 : V)) ∈ X → u = 0) := by
  first | exact @GlobalTheory.CommDet.stable_graph | exact GlobalTheory.CommDet.stable_graph | (intros; apply GlobalTheory.CommDet.stable_graph <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_representing_of_comp_idempotent_of_nondegenerate : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ), (∀ φ, (∀ ψ, B φ ψ = 0) → φ = 0) → (∀ ψ, (∀ φ, B φ ψ = 0) → ψ = 0) → ∀ (P P' : Module.End ℂ V), P ∘ₗ P = P → FiniteDimensional ℂ (LinearMap.range P) → (∀ φ ψ, B (P φ) ψ = B φ (P' ψ)) → ∀ f : V →ₗ[ℂ] ℂ, f ∘ₗ P = f → ∃ ψ, ∀ φ, B φ ψ = f φ := by
  first | exact @GlobalTheory.functional_fixed_by_idempotent_represented | exact GlobalTheory.functional_fixed_by_idempotent_represented | (intros; apply GlobalTheory.functional_fixed_by_idempotent_represented <;> assumption)
end
