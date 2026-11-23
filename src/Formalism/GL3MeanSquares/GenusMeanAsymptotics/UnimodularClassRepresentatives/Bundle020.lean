module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExtPPowLeSpanSup
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NormRepCountPowSuccInert
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle005
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensityRatio
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AlgebraMapConjO
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle010
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle007
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.StarAlgebraMap
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
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Ideal.Norm.RelNorm
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds

open NormLifting

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

abbrev AQ (K : Type) {F : Type} [Field K] [Field F] [Algebra F K] (𝔭 : Ideal (𝓞 F)) (k : ℕ) : Type :=
  𝓞 K ⧸ extP K 𝔭 ^ k

def sg (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) (k : ℕ) : AQ K 𝔭 k →+* AQ K 𝔭 k :=
  conjQ (extP K 𝔭 ^ k) (idealPowerSpanBounds.conjO_mem_pow hF 𝔭 k)

theorem sg_mk (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : 𝓞 K) :
    sg hF 𝔭 k (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (conjO K a) := conjQ_mk _ _ a

theorem sg_sg (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : AQ K 𝔭 k) :
    sg hF 𝔭 k (sg hF 𝔭 k a) = a := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [sg_mk, sg_mk, conjO_conjO]

def InQ (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : AQ K 𝔭 k) : Prop :=
  ∃ z ∈ extP K 𝔭, Ideal.Quotient.mk (extP K 𝔭 ^ k) z = a

theorem inQ_mk (𝔭 : Ideal (𝓞 F)) {k : ℕ} (hk : 1 ≤ k) (y : 𝓞 K) :
    InQ 𝔭 k (Ideal.Quotient.mk (extP K 𝔭 ^ k) y) ↔ y ∈ extP K 𝔭 := by
  unfold InQ
  constructor
  · rintro ⟨z, hz, hzy⟩
    have hd : z - y ∈ extP K 𝔭 ^ k := Ideal.Quotient.eq.mp hzy
    have hd' : z - y ∈ extP K 𝔭 := Ideal.pow_le_self (by omega) hd
    have hy := sub_mem hz hd'
    simpa using hy
  · intro hy
    exact ⟨y, hy, rfl⟩

def cnt (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) (k M : ℕ) (n : 𝓞 K) : ℕ :=
  Nat.card {x : Fin M → AQ K 𝔭 k // ∑ i, sg hF 𝔭 k (x i) * x i = Ideal.Quotient.mk _ n}

def cntP (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) (k M : ℕ) (n : 𝓞 K) : ℕ :=
  Nat.card {x : Fin M → AQ K 𝔭 k // (¬ ∀ i, InQ 𝔭 k (x i)) ∧
    ∑ i, sg hF 𝔭 k (x i) * x i = Ideal.Quotient.mk _ n}

def cntI (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) (k M : ℕ) (n : 𝓞 K) : ℕ :=
  Nat.card {x : Fin M → AQ K 𝔭 k // (∀ i, InQ 𝔭 k (x i)) ∧
    ∑ i, sg hF 𝔭 k (x i) * x i = Ideal.Quotient.mk _ n}

theorem cnt_eq_normRepCount (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) (k M : ℕ) (n : 𝓞 K) :
    cnt hF 𝔭 k M n = normRepCount K (extP K 𝔭 ^ k) M n :=
  (normRepCount_eq _ (idealPowerSpanBounds.conjO_mem_pow hF 𝔭 k) M n).symm

theorem finite_AQ {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) : Finite (AQ K 𝔭 k) :=
  Ideal.finiteQuotientOfFreeOfNeBot _ (pow_ne_zero _ (idealPowerSpanBounds.map_ne_bot_of_isMaximal h𝔭))

theorem absNorm_extP (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) :
    Ideal.absNorm (extP K 𝔭) = Ideal.absNorm 𝔭 ^ 2 := by
  unfold extP
  rw [Ideal.absNorm_algebraMap, ← MeanB.finrank_eq_two hK hF]
  congr 1
  exact (IsFractionRing.finrank_eq (𝓞 F) F (𝓞 K) K).symm

theorem card_AQ (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) (k : ℕ) :
    Nat.card (AQ K 𝔭 k) = Ideal.absNorm 𝔭 ^ (2 * k) := by
  rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, map_pow, absNorm_extP hK hF, ← pow_mul]

theorem card_split {X : Type*} [Finite X] (p r : X → Prop) :
    Nat.card {x // r x} = Nat.card {x // ¬ p x ∧ r x} + Nat.card {x // p x ∧ r x} := by
  classical
  haveI := Fintype.ofFinite X
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    tauto
  · rw [Finset.disjoint_filter]
    intro x _ h1 h2
    exact h1.1 h2.1

theorem cnt_eq_add (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k M : ℕ) (n : 𝓞 K) :
    cnt hF 𝔭 k M n = cntP hF 𝔭 k M n + cntI hF 𝔭 k M n := by
  haveI := finite_AQ (K := K) h𝔭 k
  unfold cnt cntP cntI
  exact card_split (fun x : Fin M → AQ K 𝔭 k => ∀ i, InQ 𝔭 k (x i)) _

theorem exists_tr_one (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {a : 𝓞 K} (ha : a ∉ extP K 𝔭) (N : ℕ) :
    ∃ b : 𝓞 K, conjO K a * b + conjO K b * a - 1 ∈ extP K 𝔭 ^ N := by
  obtain ⟨θ, hθ⟩ := idealPowerSpanBounds.exists_theta hK hF h𝔭
  have h1 : ∃ b : 𝓞 K, conjO K a * b + conjO K b * a ∉ extP K 𝔭 := by
    by_contra hcon
    push Not at hcon
    have e1 := hcon 1
    have e2 := hcon θ
    apply ha
    have e3 : (θ - conjO K θ) * a ∈ extP K 𝔭 ^ 1 := by
      rw [pow_one]
      have := (extP K 𝔭).sub_mem ((extP K 𝔭).mul_mem_left θ e1) e2
      have e : θ * (conjO K a * 1 + conjO K 1 * a) - (conjO K a * θ + conjO K θ * a) =
          (θ - conjO K θ) * a := by rw [map_one]; ring
      rwa [e] at this
    have := idealPowerSpanBounds.mem_of_unit_mul_mem hθ e3
    rwa [pow_one] at this
  obtain ⟨b, hb⟩ := h1
  obtain ⟨c, hc⟩ := idealPowerSpanBounds.exists_tr hF (conjO K a * b)
  rw [map_mul, conjO_conjO, mul_comm a] at hc
  have hc𝔭 : c ∉ 𝔭 := by
    intro h
    apply hb
    rw [← hc]
    exact Ideal.mem_map_of_mem _ h
  obtain ⟨u, hu⟩ := MeanA.exists_mul_sub_one_mem_pow h𝔭 hc𝔭 N
  refine ⟨(algebraMap (𝓞 F) (𝓞 K)) u * b, ?_⟩
  have e : conjO K a * ((algebraMap (𝓞 F) (𝓞 K)) u * b) + conjO K ((algebraMap (𝓞 F) (𝓞 K)) u * b) * a - 1 = (algebraMap (𝓞 F) (𝓞 K)) (u * c - 1) := by
    rw [map_mul (conjO K), idealPowerSpanBounds.conjO_map hF, map_sub, map_mul, map_one, hc]
    ring
  rw [e, idealPowerSpanBounds.mem_pow_iff]
  exact hu

theorem cntP_succ (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {k M : ℕ} (hk : 1 ≤ k) (hM : 1 ≤ M) {n : 𝓞 K} (hn : conjO K n = n) :
    cntP hF 𝔭 (k + 1) M n = Ideal.absNorm 𝔭 ^ (2 * M - 1) * cntP hF 𝔭 k M n := by
  have hle : extP K 𝔭 ^ (k + 1) ≤ extP K 𝔭 ^ k := Ideal.pow_le_pow_right (Nat.le_succ k)
  have := finite_AQ (K := K) h𝔭 (k + 1)
  obtain ⟨θ, hθ⟩ := idealPowerSpanBounds.exists_theta hK hF h𝔭
  obtain ⟨e, he⟩ := idealPowerSpanBounds.exists_inv_theta hθ (k + 1)
  have hIn : ∀ a : AQ K 𝔭 (k + 1), InQ 𝔭 k (Ideal.Quotient.factor hle a) ↔ InQ 𝔭 (k + 1) a := by
    intro a
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Ideal.Quotient.factor_mk, inQ_mk 𝔭 hk, inQ_mk 𝔭 (by omega)]
  have h := SecondPropositionFree.card_lift_pred (σ := sg hF 𝔭 (k + 1)) (τ := sg hF 𝔭 k)
    (π := Ideal.Quotient.factor hle) (Ideal.Quotient.factor_surjective hle)
    (by
      intro a
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [sg_mk, Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk, sg_mk])
    (sg_sg hF 𝔭 (k + 1))
    (by
      intro a b ha hb
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
      rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at ha hb
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      have h2 : a * b ∈ extP K 𝔭 ^ (k + k) := by rw [pow_add]; exact Ideal.mul_mem_mul ha hb
      exact Ideal.pow_le_pow_right (by omega) h2)
    (θ := Ideal.Quotient.mk _ θ) (e := Ideal.Quotient.mk _ e)
    (by
      rw [sg_mk, ← map_sub, ← map_mul, ← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]
      exact he)
    (n := Ideal.Quotient.mk _ n) (by rw [sg_mk, hn]) (Ideal.absNorm 𝔭)
    (by rw [card_AQ hK hF, card_AQ hK hF]; ring) M hM
    (fun x => ¬ ∀ i, InQ 𝔭 k (x i))
    (by
      intro y hy w hw
      push Not at hy
      obtain ⟨i₀, hi₀⟩ := hy
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (y i₀)
      rw [← ha, Ideal.Quotient.factor_mk, inQ_mk 𝔭 hk] at hi₀
      obtain ⟨b, hb⟩ := exists_tr_one hK hF h𝔭 hi₀ (k + 1)
      refine SecondPropositionFree.mem_range_linPart _ y i₀ (b := Ideal.Quotient.mk _ b) ?_ hw
      rw [← ha, sg_mk, sg_mk, ← map_mul, ← map_mul, ← map_add (f := _), ← map_one (Ideal.Quotient.mk _),
        Ideal.Quotient.eq]
      exact hb)
  rw [Ideal.Quotient.factor_mk] at h
  unfold cntP
  rw [← h]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by simp only [hIn])

theorem cntP_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (j : ℕ) {M : ℕ} (hM : 1 ≤ M) {n : 𝓞 K} (hn : conjO K n = n) :
    cntP hF 𝔭 (j + 1) M n = Ideal.absNorm 𝔭 ^ ((2 * M - 1) * j) * cntP hF 𝔭 1 M n := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [cntP_succ hK hF h𝔭 (by omega) hM hn, ih, ← mul_assoc, ← pow_add]
    congr 2
    ring

end Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
end
end

section

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BallB

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

structure IsStep (P : Ideal (𝓞 K)) (A B : Submodule (𝓞 K) V) (y : V) : Prop where
  le : A ≤ B
  mem : y ∈ B
  notMem : y ∉ A
  smul : ∀ π ∈ P, π • y ∈ A
  gen : ∀ x ∈ B, ∃ c : 𝓞 K, x - c • y ∈ A

def col (I : Ideal (𝓞 K)) (z : 𝓞 K) : Ideal (𝓞 K) where
  carrier := {c | c * z ∈ I}
  add_mem' := fun {a c} ha hc => by
    change (a + c) * z ∈ I
    rw [add_mul]; exact I.add_mem ha hc
  zero_mem' := by change (0 : 𝓞 K) * z ∈ I; rw [zero_mul]; exact I.zero_mem
  smul_mem' := fun c a ha => by
    change (c • a) * z ∈ I
    rw [smul_eq_mul, mul_assoc]; exact I.mul_mem_left c ha

omit [StarRing K] in
theorem mem_col {I : Ideal (𝓞 K)} {z c : 𝓞 K} : c ∈ col I z ↔ c * z ∈ I := Iff.rfl

omit [StarRing K] in
theorem mem_of_col_eq_top {I : Ideal (𝓞 K)} {z : 𝓞 K} (h : col I z = ⊤) : z ∈ I := by
  have h1 : (1 : 𝓞 K) ∈ col I z := by
    rw [h]; exact Submodule.mem_top
  simpa using (mem_col.1 h1)

namespace IsStep

variable {P : Ideal (𝓞 K)} {A B : Submodule (𝓞 K) V} {y : V}

omit [StarRing K] [Module K V] [IsScalarTower (𝓞 K) K V] in
theorem mem_of_smul_mem (S : IsStep P A B y) (hP : P.IsMaximal) {c : 𝓞 K} (hc : c • y ∈ A) :
    c ∈ P := by
  by_contra hcP
  obtain ⟨r, π, hπ, hrc⟩ := hP.exists_inv hcP
  apply S.notMem
  have e : y = r • (c • y) + π • y := by
    rw [smul_smul, ← add_smul, hrc, one_smul]
  rw [e]
  exact A.add_mem (A.smul_mem r hc) (S.smul π hπ)

omit [StarRing K] [Module K V] [IsScalarTower (𝓞 K) K V] in
theorem change (S : IsStep P A B y) (hP : P.IsMaximal) {x₀ : V} (hx : x₀ ∈ B) (hn : x₀ ∉ A) :
    IsStep P A B x₀ := by
  obtain ⟨c, hc⟩ := S.gen x₀ hx
  have hcP : c ∉ P := by
    intro hcP
    apply hn
    have h0 := A.add_mem hc (S.smul c hcP)
    simpa using h0
  obtain ⟨r, π, hπ, hrc⟩ := hP.exists_inv hcP
  refine ⟨S.le, hx, hn, ?_, ?_⟩
  · intro p hp
    have h1 : p • x₀ = p • (x₀ - c • y) + c • (p • y) := by
      rw [smul_sub, smul_comm p c y, sub_add_cancel]
    rw [h1]
    exact A.add_mem (A.smul_mem p hc) (A.smul_mem c (S.smul p hp))
  · intro x hxB
    obtain ⟨d, hd⟩ := S.gen x hxB
    refine ⟨d * r, ?_⟩
    have key : d • y = (d * r * c) • y + (d * π) • y := by
      rw [← add_smul, show d * r * c + d * π = d * (r * c + π) by ring, hrc, mul_one]
    have h2 : x - (d * r) • x₀ = (x - d • y) - (d * r) • (x₀ - c • y) + d • (π • y) := by
      rw [smul_sub, smul_smul (d * r) c y, smul_smul d π y, key]
      abel
    rw [h2]
    exact A.add_mem (A.sub_mem hd (A.smul_mem _ hc)) (A.smul_mem d (S.smul π hπ))

end IsStep

omit [NumberField K] [StarRing K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem det_add_smul {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι K V) (x : ι → V)
    (e : ι → K) (i₀ : ι) (he : e i₀ = 0) : b.det (fun k => x k + e k • x i₀) = b.det x := by
  rw [Basis.det_apply, Basis.det_apply, ← Matrix.det_transpose,
    ← Matrix.det_transpose (b.toMatrix x)]
  refine Matrix.det_eq_of_forall_row_eq_smul_add_const (fun k => e k) i₀ he ?_
  intro i j
  simp [Matrix.transpose_apply, Basis.toMatrix_apply, map_add (f := _), map_smul]

theorem conjO_mem_conjIdeal {P : Ideal (𝓞 K)} {π : 𝓞 K} (hπ : π ∈ P) :
    conjO K π ∈ Formalism.HermitianLatticesTheory.conjIdeal (K := K) P := by
  apply Ideal.subset_span
  exact ⟨π, hπ, by first | rfl | simp [conjO]⟩

theorem term_mem {P I : Ideal (𝓞 K)} {p₁ p₂ z : 𝓞 K} (h₁ : p₁ ∈ P) (h₂ : p₂ ∈ P) (hz : z ∈ I) :
    conjO K p₁ * p₂ * z ∈ P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P * I := by
  have h3 := Ideal.mul_mem_mul (Ideal.mul_mem_mul h₂ (conjO_mem_conjIdeal h₁)) hz
  rwa [mul_comm p₂ (conjO K p₁)] at h3

theorem step_ge (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K} {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) {A B : Submodule (𝓞 K) V} {y : V} (S : IsStep P A B y)
    (hB : Formalism.HermitianLatticesTheory.IsIntegralLat h B) (b : Basis (Fin (finrank K V)) K V) :
    P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P * discrIdeal h B ≤ discrIdeal h A := by
  have hA : Formalism.HermitianLatticesTheory.IsIntegralLat h A := fun x hx w hw => hB x (S.le hx) w (S.le hw)
  have key : ∀ π ∈ P, ∀ ρ ∈ Formalism.HermitianLatticesTheory.conjIdeal (K := K) P, ∀ z ∈ discrIdeal h B,
      π * ρ * z ∈ discrIdeal h A := by
    intro π hπ ρ hρ
    rw [conjIdeal_eq_comap, Ideal.mem_comap] at hρ
    suffices hle : discrIdeal h B ≤ Submodule.comap (LinearMap.mulLeft (𝓞 K) (π * ρ))
        (discrIdeal h A) from fun z hz => hle hz
    refine discrIdeal_le b fun x hx z hz => ?_
    change π * ρ * z ∈ discrIdeal h A
    by_cases hall : ∀ i, x i ∈ A
    · exact Ideal.mul_mem_left _ _ (mem_discrIdeal b hall hz)
    · push Not at hall
      obtain ⟨i₀, hi₀⟩ := hall
      have S' := S.change hP (hx i₀) hi₀
      choose c hc using fun k => S'.gen (x k) (hx k)
      let e : Fin (finrank K V) → K := fun k => if k = i₀ then 0 else - algebraMap (𝓞 K) K (c k)
      let x' : Fin (finrank K V) → V := fun k => x k + e k • x i₀
      have hdet : b.det x' = b.det x := det_add_smul b x e i₀ (by simp [e])
      have hx'0 : x' i₀ = x i₀ := by simp [x', e]
      have hx' : ∀ k, k ≠ i₀ → x' k ∈ A := by
        intro k hk
        have : x' k = x k - c k • x i₀ := by
          simp only [x', e, if_neg hk, neg_smul, algebraMap_smul]
          abel
        rw [this]; exact hc k
      have hup : ∀ a : 𝓞 K, b.det (Function.update x' i₀ (a • x i₀)) =
          algebraMap (𝓞 K) K a * b.det x := by
        intro a
        rw [← algebraMap_smul K a (x i₀), AlternatingMap.map_update_smul, ← hx'0,
          Function.update_eq_self, hdet, smul_eq_mul]
      refine mixed_mem hK hA b hx' (S'.smul _ hρ) (S'.smul _ hπ) ?_
      rw [hup, hup, map_mul, map_mul, hz, algebraMap_conjO, star_mul', star_star]
      ring
  rw [Ideal.mul_le]
  intro r hr z hz
  induction hr using Submodule.mul_induction_on' with
  | mem_mul_mem π hπ ρ hρ => exact key π hπ ρ hρ z hz
  | add a _ c _ ha hc => rw [add_mul]; exact Ideal.add_mem _ ha hc

end Formalism.HermitianLattices.Ext.L3.BallB
end
end
