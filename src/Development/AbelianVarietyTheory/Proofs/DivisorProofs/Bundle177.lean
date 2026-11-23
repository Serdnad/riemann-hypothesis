module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle008
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FinrankOfIsStandardSmoothOfRelativeDimension
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.LatticeRep

variable {R X M Γ : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] [Group Γ]

def Transl (W : X → M →ₗ[ℂ] M) (A : Submodule R X) : Set M := {m | ∃ x v, Fixes W A v ∧ m = W x v}

def IsLatSystem (σ : R →+* R) (w : R) (γ : X → X → ℂ) (W : X → M →ₗ[ℂ] M) (lam : ℕ →* ℂ) (A : Submodule R X)
    (ρ : Γ →* Module.End R X) : Prop :=
  IsHeis σ w γ W ∧ GoodNorm σ lam ∧ SelfDual γ A ∧ Submodule.span ℂ (Transl W A) = ⊤ ∧
    (∀ g x y, γ (ρ g x) (ρ g y) = γ x y) ∧ ∀ g, idx A (A.map (ρ g)) ≠ 0

def IsLatRep (W : X → M →ₗ[ℂ] M) (lam : ℕ →* ℂ) (A : Submodule R X) (ρ : Γ →* Module.End R X)
    (Om : Γ →* Module.End ℂ M) : Prop :=
  (∀ g x v, Om g (W x v) = W (ρ g x) (Om g v)) ∧ ∀ g v, Fixes W A v → Om g v = normOp lam W A (A.map (ρ g)) v

variable {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} {lam : ℕ →* ℂ} {A : Submodule R X}
  {ρ : Γ →* Module.End R X} {Om : Γ →* Module.End ℂ M}

open Classical in
open scoped BigOperators in
variable {R X M Γ : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] [Group Γ] in
variable {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} {lam : ℕ →* ℂ} {A : Submodule R X}
  {ρ : Γ →* Module.End R X} {Om : Γ →* Module.End ℂ M} in
theorem _root_.GlobalTheory.LatticeRep.transl_induction (hs : Submodule.span ℂ (_root_.GlobalTheory.LatticeRep.Transl W A) = ⊤) {p : M → Prop}
    (mem : ∀ x v, _root_.GlobalTheory.FinWeil.Fixes W A v → p (W x v)) (zero : p 0) (add : ∀ a b, p a → p b → p (a + b))
    (smul : ∀ (c : ℂ) a, p a → p (c • a)) (m : M) : p m := by
  have hm : m ∈ Submodule.span ℂ (_root_.GlobalTheory.LatticeRep.Transl W A) := by
    rw [hs]; exact Submodule.mem_top
  induction hm using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, v, hv, rfl⟩ := hy
    exact mem x v hv
  | zero => exact zero
  | add a b _ _ ha hb => exact add a b ha hb
  | smul c a _ ha => exact smul c a ha

open Classical in
open scoped BigOperators in
variable {R X M Γ : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] [Group Γ] in
variable {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} {lam : ℕ →* ℂ} {A : Submodule R X}
  {ρ : Γ →* Module.End R X} {Om : Γ →* Module.End ℂ M} in
private theorem sumOp_eq_self_of_le {B : Submodule R X} (hBA : B ≤ A) {v : M}
    (hv : _root_.GlobalTheory.FinWeil.Fixes W A v) : _root_.GlobalTheory.FinWeil.sumOp W A B v = v := by
  unfold _root_.GlobalTheory.FinWeil.sumOp
  have hz : ∀ q : B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup, q = 0 := by
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H b => exact (QuotientAddGroup.eq_zero_iff b).mpr (hBA b.2)
  rw [finsum_eq_single _ 0 (fun q hq => absurd (hz q) hq)]
  exact hv _ (hBA (Quotient.out (0 : B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup)).2)


open Classical in
open scoped BigOperators in
variable {R X M Γ : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] [Group Γ] in
variable {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} {lam : ℕ →* ℂ} {A : Submodule R X}
  {ρ : Γ →* Module.End R X} {Om : Γ →* Module.End ℂ M} in
theorem _root_.GlobalTheory.LatticeRep.IsLatRep.fix_of_map_le (h : _root_.GlobalTheory.LatticeRep.IsLatSystem σ w γ W lam A ρ) (hO : _root_.GlobalTheory.LatticeRep.IsLatRep W lam A ρ Om) {g : Γ}
    (hg : A.map (ρ g) ≤ A) {v : M} (hv : _root_.GlobalTheory.FinWeil.Fixes W A v) : Om g v = v := by
  rw [hO.2 g v hv]
  unfold _root_.GlobalTheory.FinWeil.normOp _root_.GlobalTheory.FinWeil.idx
  have hidx : A.toAddSubgroup.relIndex (A.map (ρ g)).toAddSubgroup = 1 :=
    AddSubgroup.relIndex_eq_one.mpr hg
  rw [hidx, map_one, inv_one, one_smul]
  exact sumOp_eq_self_of_le hg hv

open Classical in
open scoped BigOperators in
variable {R X M Γ : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] [Group Γ] in
variable {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} {lam : ℕ →* ℂ} {A : Submodule R X}
  {ρ : Γ →* Module.End R X} {Om : Γ →* Module.End ℂ M} in
private theorem map_sumOp_of_commute {B : Submodule R X} (φ : M →ₗ[ℂ] M)
    (h : _root_.GlobalTheory.FinWeil.idx A B ≠ 0) (hφ : ∀ x m, φ (W x m) = W x (φ m)) (v : M) :
    φ (_root_.GlobalTheory.FinWeil.sumOp W A B v) = _root_.GlobalTheory.FinWeil.sumOp W A B (φ v) := by
  unfold _root_.GlobalTheory.FinWeil.idx at h
  have : Finite (B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup) :=
    AddSubgroup.index_ne_zero_iff_finite.mp h
  unfold _root_.GlobalTheory.FinWeil.sumOp
  rw [map_finsum φ (Set.toFinite _)]
  simp only [hφ]


open Classical in
open scoped BigOperators in
variable {R X M Γ : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] [Group Γ] in
variable {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} {lam : ℕ →* ℂ} {A : Submodule R X}
  {ρ : Γ →* Module.End R X} {Om : Γ →* Module.End ℂ M} in
theorem _root_.GlobalTheory.LatticeRep.IsLatRep.comm (h : _root_.GlobalTheory.LatticeRep.IsLatSystem σ w γ W lam A ρ) (hO : _root_.GlobalTheory.LatticeRep.IsLatRep W lam A ρ Om) (φ : M →ₗ[ℂ] M)
    (hφ : ∀ x m, φ (W x m) = W x (φ m)) (g : Γ) (m : M) : Om g (φ m) = φ (Om g m) := by
  refine _root_.GlobalTheory.LatticeRep.transl_induction (p := fun m => Om g (φ m) = φ (Om g m))
    h.2.2.2.1 (fun x v hv => ?_) ?_
    (fun a b ha hb => ?_) (fun c a ha => ?_) m
  · have hφv : _root_.GlobalTheory.FinWeil.Fixes W A (φ v) := fun a ha => by rw [← hφ, hv a ha]
    rw [hφ, hO.1, hO.1, hO.2 g _ hφv, hO.2 g _ hv, hφ]
    congr 1
    unfold _root_.GlobalTheory.FinWeil.normOp
    rw [map_smul, map_sumOp_of_commute φ (h.2.2.2.2.2 g) hφ]
  · simp
  · simp only [map_add (f := _), ha, hb]
  · simp only [map_smul, ha]

end GlobalTheory.LatticeRep

end
end

section

namespace GlobalTheory.PowerIdealSurjectivity

variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A]

lemma exists_span_sub_mem_sq (ε : A →ₐ[O] O) {d : ℕ} (x : Fin d → A) (hx : ∀ i, ε (x i) = 0)
    (hs : Submodule.span O (Set.range fun i ↦ GlobalTheory.AugCot.d ε (x i)) = ⊤) {c : A}
    (hc : c ∈ RingHom.ker ε) :
    ∃ m ∈ Submodule.span O (Set.range x), m ∈ RingHom.ker ε ∧ c - m ∈ RingHom.ker ε ^ 2 := by
  classical

  let J : Submodule O A := (RingHom.ker ε ^ 2).restrictScalars O
  let D : A →ₗ[O] A ⧸ J := J.mkQ ∘ₗ (LinearMap.id - (Algebra.linearMap O A) ∘ₗ ε.toLinearMap)
  have hDa : ∀ a, D a = Submodule.Quotient.mk (a - algebraMap O A (ε a)) := fun a => rfl
  have hmemI : ∀ a, a - algebraMap O A (ε a) ∈ RingHom.ker ε := fun a =>
    RingHom.mem_ker.mpr (show ε (a - algebraMap O A (ε a)) = 0 by simp)
  have hD : ∀ a b : A, D (a * b) = ε a • D b + ε b • D a := by
    intro a b
    rw [hDa, hDa, hDa, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul,
      ← Submodule.Quotient.mk_add, Submodule.Quotient.eq, Submodule.restrictScalars_mem]
    have key : a * b - algebraMap O A (ε (a * b)) -
        (ε a • (b - algebraMap O A (ε b)) + ε b • (a - algebraMap O A (ε a))) =
        (a - algebraMap O A (ε a)) * (b - algebraMap O A (ε b)) := by
      rw [map_mul, Algebra.smul_def, Algebra.smul_def, map_mul]
      ring
    rw [key, pow_two]
    exact Ideal.mul_mem_mul (hmemI a) (hmemI b)
  have hdc : GlobalTheory.AugCot.d ε c ∈ Submodule.span O (Set.range fun i => GlobalTheory.AugCot.d ε (x i)) := by
    rw [hs]
    exact Submodule.mem_top
  obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun O).mp hdc
  have hε0 : ε (∑ i, r i • x i) = 0 := by simp [map_sum, hx]
  refine ⟨∑ i, r i • x i,
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩),
    RingHom.mem_ker.mpr hε0, ?_⟩
  have hdm : GlobalTheory.AugCot.d ε (∑ i, r i • x i) = GlobalTheory.AugCot.d ε c := by

    rw [← hr, map_sum]
    simp only [map_smul]
  have h := congrArg (GlobalTheory.AugCot.lift ε D hD) hdm
  rw [GlobalTheory.AugCot.lift_d, GlobalTheory.AugCot.lift_d, hDa, hDa, Submodule.Quotient.eq,
    Submodule.restrictScalars_mem] at h
  have hεc : ε c = 0 := RingHom.mem_ker.mp hc
  rw [hε0, hεc, map_zero, sub_zero, sub_zero] at h
  rw [← neg_sub]
  exact (RingHom.ker ε ^ 2).neg_mem h

lemma exists_sub_mem_pow (B : Subalgebra O A) (I : Ideal A)
    (h0 : ∀ a, ∃ b ∈ B, a - b ∈ I) (h1 : ∀ c ∈ I, ∃ m ∈ B, m ∈ I ∧ c - m ∈ I ^ 2) (n : ℕ) (a : A) :
    ∃ b ∈ B, a - b ∈ I ^ (n + 1) := by

  have step : ∀ k : ℕ, ∀ c ∈ I ^ (k + 1), ∃ m ∈ B, m ∈ I ^ (k + 1) ∧ c - m ∈ I ^ (k + 2) := by
    intro k
    induction k with
    | zero =>
      intro c hc
      rw [zero_add, pow_one] at hc
      obtain ⟨m, hmB, hmI, hcm⟩ := h1 c hc
      exact ⟨m, hmB, by rwa [zero_add, pow_one], hcm⟩
    | succ k ih =>
      intro c hc
      have hc' : c ∈ I ^ (k + 1) * I := by rw [← pow_succ]; exact hc
      refine Submodule.mul_induction_on
        (C := fun c => ∃ m ∈ B, m ∈ I ^ (k + 1 + 1) ∧ c - m ∈ I ^ (k + 1 + 2)) hc' ?_ ?_
      · intro y hy z hz
        obtain ⟨my, hmyB, hmyI, hy'⟩ := ih y hy
        obtain ⟨mz, hmzB, hmzI, hz'⟩ := h1 z hz
        refine ⟨my * mz, B.mul_mem hmyB hmzB, ?_, ?_⟩
        · rw [pow_succ]
          exact Ideal.mul_mem_mul hmyI hmzI
        · have e : y * z - my * mz = y * (z - mz) + (y - my) * mz := by ring
          rw [e]
          refine Ideal.add_mem _ ?_ ?_
          · have := Ideal.mul_mem_mul hy hz'
            rwa [← pow_add] at this
          · have := Ideal.mul_mem_mul hy' hmzI
            rwa [← pow_succ] at this
      · rintro y z ⟨my, hmyB, hmyI, hy'⟩ ⟨mz, hmzB, hmzI, hz'⟩
        refine ⟨my + mz, B.add_mem hmyB hmzB, Ideal.add_mem _ hmyI hmzI, ?_⟩
        have e : y + z - (my + mz) = (y - my) + (z - mz) := by ring
        rw [e]
        exact Ideal.add_mem _ hy' hz'
  induction n with
  | zero =>
    obtain ⟨b, hb, hab⟩ := h0 a
    exact ⟨b, hb, by rwa [zero_add, pow_one]⟩
  | succ n ih =>
    obtain ⟨b, hb, hab⟩ := ih
    obtain ⟨m, hmB, -, hm⟩ := step n (a - b) hab
    refine ⟨b + m, B.add_mem hb hmB, ?_⟩
    have e : a - (b + m) = a - b - m := by ring
    rw [e]
    exact hm

theorem aeval_surjective (O A : Type) [CommRing O] [IsLocalRing O] [CommRing A] [Algebra O A]
    [Module.Finite O A] [IsLocalRing A] (q : O) (hq : q ∈ IsLocalRing.maximalIdeal O)
    (ε : A →ₐ[O] O) (d : ℕ) (x : Fin d → A) (hx : ∀ i, ε (x i) = 0)
    (hN : ∀ i, ∃ N : ℕ, algebraMap O A q ∣ x i ^ N)
    (hs : Submodule.span O (Set.range fun i ↦ GlobalTheory.AugCot.d ε (x i)) = ⊤) :
    Function.Surjective (MvPolynomial.aeval x : MvPolynomial (Fin d) O → A) := by
  classical
  let B : Subalgebra O A := Algebra.adjoin O (Set.range x)
  have h0 : ∀ a, ∃ b ∈ B, a - b ∈ RingHom.ker ε := fun a =>
    ⟨algebraMap O A (ε a), B.algebraMap_mem _,
      RingHom.mem_ker.mpr (show ε (a - algebraMap O A (ε a)) = 0 by simp)⟩
  have h1 : ∀ c ∈ RingHom.ker ε, ∃ m ∈ B, m ∈ RingHom.ker ε ∧ c - m ∈ RingHom.ker ε ^ 2 := by
    intro c hc
    obtain ⟨m, hm, hmI, hcm⟩ := exists_span_sub_mem_sq ε x hx hs hc
    exact ⟨m, Algebra.span_le_adjoin O _ hm, hmI, hcm⟩

  let φ : A →ₗ[O] A := LinearMap.id - (Algebra.linearMap O A) ∘ₗ ε.toLinearMap
  have hφ : ∀ a, φ a = a - algebraMap O A (ε a) := fun a => rfl
  have hfg : (RingHom.ker ε).FG := by
    apply Submodule.FG.of_restrictScalars O
    have heq : (RingHom.ker ε).restrictScalars O = LinearMap.range φ := by
      ext c
      rw [Submodule.restrictScalars_mem, LinearMap.mem_range]
      constructor
      · intro hc
        refine ⟨c, ?_⟩
        rw [hφ, show ε c = 0 from RingHom.mem_ker.mp hc, map_zero, sub_zero]
      · rintro ⟨a, rfl⟩
        rw [hφ]
        exact RingHom.mem_ker.mpr (show ε (a - algebraMap O A (ε a)) = 0 by simp)
    rw [heq, ← Submodule.map_top]
    exact (Module.Finite.fg_top (R := O) (M := A)).map φ

  have hker_ne : RingHom.ker ε ≠ ⊤ := RingHom.ker_ne_top ε
  have hle_span : RingHom.ker ε ≤ Ideal.span (Set.range x) := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := RingHom.ker ε) hfg ?_ ?_
    · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
      exact IsLocalRing.le_maximalIdeal hker_ne
    · intro c hc
      obtain ⟨m, hm, -, hcm⟩ := exists_span_sub_mem_sq ε x hx hs hc
      have hm' : m ∈ Ideal.span (Set.range x) := Submodule.span_le_restrictScalars O A _ hm
      rw [pow_two, ← smul_eq_mul] at hcm
      rw [show c = m + (c - m) by ring]
      exact Submodule.add_mem_sup hm' hcm

  have hrad : Ideal.span (Set.range x) ≤ (Ideal.span {algebraMap O A q}).radical := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨N, hNi⟩ := hN i
    exact ⟨N, Ideal.mem_span_singleton.mpr hNi⟩
  have hfgx : (Ideal.span (Set.range x)).FG :=
    ⟨Finset.univ.image x, by rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]⟩
  obtain ⟨K, hK⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad hfgx

  have htop : (⊤ : Submodule O A) ≤ Subalgebra.toSubmodule B := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := IsLocalRing.maximalIdeal O)
      Module.Finite.fg_top ?_ ?_
    · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    · intro a _
      obtain ⟨b, hb, hab⟩ := exists_sub_mem_pow B (RingHom.ker ε) h0 h1 K a
      have h2 : a - b ∈ Ideal.span (Set.range x) ^ K :=
        Ideal.pow_right_mono hle_span K (Ideal.pow_le_pow_right (Nat.le_succ K) hab)
      obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp (hK h2)
      have h3 : a - b ∈ IsLocalRing.maximalIdeal O • (⊤ : Submodule O A) := by
        rw [← hy, mul_comm, ← Algebra.smul_def]
        exact Submodule.smul_mem_smul hq Submodule.mem_top
      rw [show a = b + (a - b) by ring]
      exact Submodule.add_mem_sup hb h3
  intro a
  have ha : a ∈ B := htop Submodule.mem_top
  rw [show B = (MvPolynomial.aeval x).range from Algebra.adjoin_range_eq_range_aeval O x] at ha
  obtain ⟨p, hp⟩ := ha
  exact ⟨p, hp⟩

end GlobalTheory.PowerIdealSurjectivity
end

section

open scoped Matrix
open MeasureTheory GlobalTheory.RealWeil

namespace GlobalTheory

theorem quad_eq_sum_symplDual (l κ : Type) [Fintype l] [DecidableEq l] [Fintype κ]
    (X : Matrix (l ⊕ l) (l ⊕ l) ℝ) (u v : κ → (l ⊕ l → ℝ))
    (h : ∀ w, ∑ i, sympl (v i) w • u i = w) :
    quad X = (4 * Real.pi * Complex.I : ℂ)⁻¹ • ∑ i, (1 / 2 : ℂ) •
      (dRho (X *ᵥ u i) * dRho (v i) + dRho (v i) * dRho (X *ᵥ u i)) := by
  have hJ : ∀ (x : l ⊕ l → ℝ) (b : l ⊕ l), sympl x (Matrix.J l ℝ *ᵥ Pi.single b 1) = x b := by
    intro x b
    rcases b with b | b <;>
      simp [sympl, pPart, qPart, PiLp.inner_apply, Matrix.J, Matrix.mulVec, dotProduct, Pi.single_apply,
        Matrix.one_apply]
  have hcol : ∀ b, ∑ i, v i b • u i = Matrix.J l ℝ *ᵥ Pi.single b 1 := by
    intro b
    have := h (Matrix.J l ℝ *ᵥ Pi.single b 1)
    simp only [hJ] at this
    exact this
  have hcoef : ∀ a b, ∑ i, (X *ᵥ u i) a * v i b = (X * Matrix.J l ℝ) a b := by
    intro a b
    have := congrArg (fun w => (X *ᵥ w) a) (hcol b)
    simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.mulVec_mulVec] at this
    have e : ((X * Matrix.J l ℝ) *ᵥ Pi.single b 1) a = (X * Matrix.J l ℝ) a b := by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [← e, ← this]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hT : ∀ i, dRho (X *ᵥ u i) * dRho (v i) + dRho (v i) * dRho (X *ᵥ u i) =
      ∑ a, ∑ b, (((X *ᵥ u i) a * v i b : ℝ) : ℂ) •
        (dRho (Pi.single a 1) * dRho (Pi.single b 1) + dRho (Pi.single b 1) * dRho (Pi.single a 1)) := by
    intro i
    rw [dRho_eq_sum (X *ᵥ u i), dRho_eq_sum (v i)]
    simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm]
    conv_lhs => arg 1; rw [Finset.sum_comm]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    push_cast
    module
  rw [quad]
  congr 1
  simp_rw [hT, ← hcoef, Finset.sum_div, Complex.ofReal_sum, Finset.sum_smul, Finset.smul_sum]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul]
  congr 1
  push_cast
  ring

end GlobalTheory
end

section

open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap

namespace GlobalTheory

theorem one_add_pow_le_two_pow_mul (a : ℝ) (ha : 0 ≤ a) (N : ℕ) :
    (1 + a) ^ N ≤ 2 ^ N * (1 + a ^ N) := by
  rcases le_total a 1 with h | h
  · calc (1 + a) ^ N ≤ 2 ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
      _ ≤ 2 ^ N * (1 + a ^ N) := by
        have : 0 ≤ a ^ N := pow_nonneg ha N
        nlinarith [pow_pos (two_pos : (0:ℝ) < 2) N]
  · calc (1 + a) ^ N ≤ (2 * a) ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
      _ = 2 ^ N * a ^ N := mul_pow _ _ _
      _ ≤ 2 ^ N * (1 + a ^ N) := by
        gcongr
        linarith

theorem one_add_norm_le_mul_of_add {E : Type*} [NormedAddCommGroup E] (x p : E) :
    1 + ‖p‖ ≤ (1 + ‖x + p‖) * (1 + ‖x‖) := by
  have h : ‖p‖ ≤ ‖x + p‖ + ‖x‖ := by
    have := norm_sub_le (x + p) x
    simpa using this
  nlinarith [norm_nonneg (x + p), norm_nonneg x, mul_nonneg (norm_nonneg (x + p)) (norm_nonneg x)]

theorem matrixCoeff_pPart_decay : ∀ (n : ℕ) (g g' : Sch (Fin n)) (N : ℕ), ∃ C : ℝ,
    ∀ w : Fin n ⊕ Fin n → ℝ,
      ‖∫ x, rhoFun w ⇑g x * starRingEnd ℂ (g' x)‖ * (1 + ‖pPart w‖) ^ N ≤ C := by
  intro n g g' N
  set A : ℝ := 2 ^ (N, 0).1 * (Finset.Iic (N, 0)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) g with hA
  have hg : ∀ y, (1 + ‖y‖) ^ N * ‖g y‖ ≤ A := fun y => by
    have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (N, 0)) (k := N) (n := 0)
      le_rfl le_rfl g y
    rwa [norm_iteratedFDeriv_zero] at this
  set h : EuclideanSpace ℝ (Fin n) → ℝ := fun x => (1 + ‖x‖) ^ N * ‖g' x‖ with hh
  have hint : Integrable h := by
    have i1 := (g'.integrable_pow_mul volume 0).add (g'.integrable_pow_mul volume N)
    refine (i1.const_mul (2 ^ N)).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact ((continuous_const.add continuous_norm).pow N |>.mul g'.continuous.norm).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (by positivity)]
      simp only [hh, pow_zero, one_mul]
      calc (1 + ‖x‖) ^ N * ‖g' x‖ ≤ (2 ^ N * (1 + ‖x‖ ^ N)) * ‖g' x‖ :=
            mul_le_mul_of_nonneg_right (one_add_pow_le_two_pow_mul _ (norm_nonneg _) N) (norm_nonneg _)
        _ = 2 ^ N * (‖g' x‖ + ‖x‖ ^ N * ‖g' x‖) := by ring
  refine ⟨A * ∫ x, h x, fun w => ?_⟩
  set c : ℝ := (1 + ‖pPart w‖) ^ N with hc
  have hc0 : 0 ≤ c := by positivity
  have hpt : ∀ x, ‖rhoFun w ⇑g x * starRingEnd ℂ (g' x)‖ * c ≤ A * h x := fun x => by
    have e : ‖rhoFun w ⇑g x * starRingEnd ℂ (g' x)‖ = ‖g (x + pPart w)‖ * ‖g' x‖ := by
      simp [rhoFun, norm_phase]
    rw [e, hc]
    have hp := pow_le_pow_left₀ (by positivity) (one_add_norm_le_mul_of_add x (pPart w)) N
    rw [mul_pow] at hp
    calc ‖g (x + pPart w)‖ * ‖g' x‖ * (1 + ‖pPart w‖) ^ N
        ≤ ‖g (x + pPart w)‖ * ‖g' x‖ * ((1 + ‖x + pPart w‖) ^ N * (1 + ‖x‖) ^ N) :=
          mul_le_mul_of_nonneg_left hp (by positivity)
      _ = ((1 + ‖x + pPart w‖) ^ N * ‖g (x + pPart w)‖) * h x := by simp only [hh]; ring
      _ ≤ A * h x := mul_le_mul_of_nonneg_right (hg _) (by positivity)
  calc ‖∫ x, rhoFun w ⇑g x * starRingEnd ℂ (g' x)‖ * c
      ≤ (∫ x, ‖rhoFun w ⇑g x * starRingEnd ℂ (g' x)‖) * c :=
        mul_le_mul_of_nonneg_right (norm_integral_le_integral_norm _) hc0
    _ = ∫ x, ‖rhoFun w ⇑g x * starRingEnd ℂ (g' x)‖ * c := (integral_mul_const _ _).symm
    _ ≤ ∫ x, A * h x :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity)
          (hint.const_mul A) (Filter.Eventually.of_forall hpt)
    _ = A * ∫ x, h x := integral_const_mul _ _

end GlobalTheory
end

section

open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap

namespace GlobalTheory.RealWeil

theorem continuous_matrixCoeff_rhoFun : ∀ (n : ℕ) (g g' : Sch (Fin n)),
    Continuous (fun w : Fin n ⊕ Fin n → ℝ => ∫ x, rhoFun w ⇑g x * starRingEnd ℂ (g' x)) := by
  intro n g g'
  have hp : Continuous (fun w : Fin n ⊕ Fin n → ℝ => pPart w) := by
    unfold pPart; fun_prop
  have hq : Continuous (fun w : Fin n ⊕ Fin n → ℝ => qPart w) := by
    unfold qPart; fun_prop
  refine continuous_of_dominated (bound := fun x => SchwartzMap.seminorm ℂ 0 0 g * ‖g' x‖) ?_ ?_ ?_ ?_
  · intro w
    exact (((continuous_phase w).mul (g.continuous.comp (continuous_id.add continuous_const))).mul
      (continuous_star.comp g'.continuous)).aestronglyMeasurable
  · intro w
    refine Filter.Eventually.of_forall fun x => ?_
    simp only [rhoFun, norm_mul, norm_phase, one_mul, RCLike.norm_conj]
    exact mul_le_mul_of_nonneg_right (SchwartzMap.norm_le_seminorm ℂ g _) (norm_nonneg _)
  · exact (SchwartzMap.integrable g').norm.const_mul _
  · refine Filter.Eventually.of_forall fun x => ?_
    simp only [rhoFun, phase]
    fun_prop

end GlobalTheory.RealWeil
end
