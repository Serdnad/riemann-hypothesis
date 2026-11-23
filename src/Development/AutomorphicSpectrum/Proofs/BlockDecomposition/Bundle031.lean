module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle017
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.Topology.Instances.Matrix
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle018
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.PsiApply
public import Mathlib.GroupTheory.GroupAction.Ring
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
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.Ideal.Quotient.Basic
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MeasureTheory Topology Filter GlobalTheory.CompanionTheory.NullFr
open scoped NNReal ENNReal Matrix

namespace GlobalTheory.CompanionTheory.NullFr.Coeff

variable {A : Type} [CommRing A]

theorem mul_eq_zero_of_mem {f : A} (hf : f * f = f) {x : A}
    (hx : x ∈ Ideal.span ({1 - f} : Set A)) : f * x = 0 := by
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hx
  linear_combination (-y) * hf

theorem mem_of_mul_eq_zero {f x : A} (hx : f * x = 0) :
    x ∈ Ideal.span ({1 - f} : Set A) :=
  Ideal.mem_span_singleton'.2 ⟨x, by linear_combination (-1 : A) * hx⟩

theorem isMaximal_span {f : A} (hf : IsFieldIdem f) :
    (Ideal.span ({1 - f} : Set A)).IsMaximal := by
  refine Ideal.isMaximal_iff.2 ⟨fun h => hf.ne ?_, fun J x hJ hx hxJ => ?_⟩
  · simpa using mul_eq_zero_of_mem hf.idem h
  · have hne : f * x ≠ 0 := fun h => hx (mem_of_mul_eq_zero h)
    obtain ⟨y, hy⟩ := hf.inv x hne
    have h1 : (1 - f) ∈ J := hJ (Ideal.subset_span rfl)
    have h2 : x * (f * y) ∈ J := J.mul_mem_right _ hxJ
    have : (1 : A) = (1 - f) + x * (f * y) := by linear_combination (-1 : A) * hy
    rw [this]
    exact J.add_mem h1 h2

theorem alt_of_field {K : Type} [Field K] (π : A →+* K) (hs : Function.Surjective π) {f : A}
    (hf : f * f = f) (h1 : π f = 1) (h0 : ∀ x, π x = 0 → f * x = 0) {a t : ℕ} (v : Fx A a t) :
    (∃ M : Fx A t a, f • (M * v) = f • (1 : Fx A t t)) ∨
      ∃ (i : Fin t) (c : Fin t → A), c i = 0 ∧ (∀ k, f * c k = c k) ∧
        ∀ p, f * v p i = ∑ k, c k * v p k := by
  classical
  set w : Matrix (Fin a) (Fin t) K := v.map π with hw
  by_cases hli : LinearIndependent K w.col
  · left
    have hinj : Function.Injective w.mulVecLin := Matrix.mulVec_injective_iff.2 hli
    obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective w.mulVecLin
      (LinearMap.ker_eq_bot.2 hinj)
    set N : Matrix (Fin t) (Fin a) K := LinearMap.toMatrix' g with hN
    have hNw : N * w = 1 := by
      have : LinearMap.toMatrix' (g ∘ₗ w.mulVecLin) = N * w := by
        rw [LinearMap.toMatrix'_comp, hN]
        congr 1
        rw [← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']
      rw [← this, hg, LinearMap.toMatrix'_id]
    choose l hl using hs
    refine ⟨Matrix.of fun p q => l (N p q), ?_⟩
    have hmap : ((Matrix.of fun p q => l (N p q) : Fx A t a) * v).map π = 1 := by
      rw [Matrix.map_mul, ← hNw]
      congr 1
      ext p q
      simp [hl]
    ext p q
    have hpq := congrFun (congrFun hmap p) q
    have hz : π (((Matrix.of fun p q => l (N p q) : Fx A t a) * v) p q - (1 : Fx A t t) p q) = 0 := by
      rw [map_sub, sub_eq_zero]
      have hpq' : π (((Matrix.of fun p q => l (N p q) : Fx A t a) * v) p q) = (1 : Matrix (Fin t) (Fin t) K) p q := hpq
      rw [hpq']
      by_cases h : p = q
      · subst h
        rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]
      · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h, map_zero]
    have := h0 _ hz
    simp only [Matrix.smul_apply, smul_eq_mul]
    linear_combination this
  · right
    obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.1 hli
    set b : Fin t → K := fun k => if k = i then 0 else -(g k / g i) with hb
    choose l hl using hs
    refine ⟨i, fun k => f * l (b k), ?_, fun k => ?_, fun p => ?_⟩
    · have : π (l (b i)) = 0 := by simp [hl, hb]
      exact h0 _ this
    · rw [← mul_assoc, hf]
    · have hrow : ∑ k, g k * w p k = 0 := by
        have := congrFun hg p
        simpa [Matrix.col_apply, Finset.sum_apply] using this
      have hz : π (v p i - ∑ k, l (b k) * v p k) = 0 := by
        have hw' : ∀ k, π (v p k) = w p k := fun k => rfl

        rw [map_sub, map_sum]
        simp only [map_mul, hl, hw']
        have hsum : ∑ k, b k * w p k = w p i := by
          have hsplit : ∀ k, b k * w p k = -(g i)⁻¹ * (g k * w p k) +
              (if k = i then w p i else 0) := by
            intro k
            by_cases h : k = i
            · subst h
              simp only [hb, if_true]
              field_simp
              ring
            · simp only [hb, if_neg h]
              field_simp
              ring
          rw [Finset.sum_congr rfl fun k _ => hsplit k, Finset.sum_add_distrib,
            ← Finset.mul_sum, hrow]
          simp
        rw [hsum, sub_self]
      have := h0 _ hz
      rw [mul_sub, Finset.mul_sum, sub_eq_zero] at this
      rw [this]
      exact Finset.sum_congr rfl fun k _ => by ring

theorem exists_dependent_column {A : Type} [CommRing A] {ι : Type} [Fintype ι] (e : A) (f : ι → A)
    (hd : IsFieldDec e f) {a t : ℕ} (v : Fx A a t)
    (hv : ¬ ∃ M : Fx A t a, M * v = e • (1 : Fx A t t)) :
    ∃ (j : ι) (i : Fin t) (c : Fin t → A), c i = 0 ∧ (∀ k, f j * c k = c k) ∧
      ∀ p, f j * v p i = ∑ k, c k * v p k := by
  classical
  have key : ∀ j, (∃ M : Fx A t a, f j • (M * v) = f j • (1 : Fx A t t)) ∨
      ∃ (i : Fin t) (c : Fin t → A), c i = 0 ∧ (∀ k, f j * c k = c k) ∧
        ∀ p, f j * v p i = ∑ k, c k * v p k := by
    intro j
    have hj := hd.field j
    haveI := isMaximal_span hj
    letI : Field (A ⧸ Ideal.span ({1 - f j} : Set A)) := Ideal.Quotient.field _
    refine alt_of_field (Ideal.Quotient.mk (Ideal.span ({1 - f j} : Set A)))
      Ideal.Quotient.mk_surjective hj.idem ?_ ?_ v
    · rw [← map_one (Ideal.Quotient.mk (Ideal.span ({1 - f j} : Set A)))]
      refine Ideal.Quotient.eq.2 ?_
      have : f j - 1 = (-1 : A) * (1 - f j) := by ring
      rw [this]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
    · intro x hx
      exact mul_eq_zero_of_mem hj.idem (Ideal.Quotient.eq_zero_iff_mem.1 hx)
  by_contra hno
  have hall : ∀ j, ∃ M : Fx A t a, f j • (M * v) = f j • (1 : Fx A t t) := fun j =>
    (key j).resolve_right fun ⟨i, c, h⟩ => hno ⟨j, i, c, h⟩
  choose M hM using hall
  refine hv ⟨∑ j, f j • M j, ?_⟩
  rw [Matrix.sum_mul, ← hd.sum, Finset.sum_smul]
  exact Finset.sum_congr rfl fun j _ => by rw [Matrix.smul_mul, hM j]

end GlobalTheory.CompanionTheory.NullFr.Coeff
end

section

open MeasureTheory Topology Filter GlobalTheory.CompanionTheory.NullFr
open scoped NNReal ENNReal Matrix

namespace GlobalTheory.CompanionTheory.NullFr

theorem entries_isCompact {A : Type} [TopologicalSpace A] {m n : ℕ} {C : Set A} (hC : IsCompact C) :
    IsCompact {M : Matrix (Fin m) (Fin n) A | ∀ p q, M p q ∈ C} := by
  have h : IsCompact (Set.pi Set.univ (fun _ : Fin m => Set.pi Set.univ (fun _ : Fin n => C))) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hC
  have e : {M : Matrix (Fin m) (Fin n) A | ∀ p q, M p q ∈ C} =
      Set.pi Set.univ (fun _ : Fin m => Set.pi Set.univ (fun _ : Fin n => C)) := by
    ext M
    exact ⟨fun h p _ q _ => h p q, fun h p q => h p (Set.mem_univ p) q (Set.mem_univ q)⟩
  rw [e]
  exact h

theorem exists_compact_comb {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (n : ℕ)
    {C₁ C₂ C₃ : Set A} (h₁ : IsCompact C₁) (h₂ : IsCompact C₂) (h₃ : IsCompact C₃) :
    ∃ D : Set A, IsCompact D ∧ ∀ (x : A) (b d : Fin n → A), x ∈ C₁ → (∀ k, b k ∈ C₂) → (∀ k, d k ∈ C₃) →
      x + ∑ k, b k * d k ∈ D := by
  have hK : IsCompact (C₁ ×ˢ ((Set.pi Set.univ (fun _ : Fin n => C₂)) ×ˢ
      (Set.pi Set.univ (fun _ : Fin n => C₃)))) :=
    h₁.prod ((isCompact_univ_pi fun _ => h₂).prod (isCompact_univ_pi fun _ => h₃))
  have hc : Continuous (fun w : A × (Fin n → A) × (Fin n → A) => w.1 + ∑ k, w.2.1 k * w.2.2 k) := by
    fun_prop
  refine ⟨_, hK.image hc, fun x b d hx hb hd => ⟨(x, b, d), ⟨hx, ?_, ?_⟩, rfl⟩⟩
  · exact fun k _ => hb k
  · exact fun k _ => hd k

theorem piece_measure_lt_top : ∀ {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] {a r t : ℕ}
    [MeasurableSpace (Fx A a r)] [MeasurableSpace (Fx A a t)] (e f : A) (P : Fx A a r → Fx A r a) (i : Fin t) (C : Set A)
    (_ : IsCompact C) (_ : (0 : A) ∈ C) (ν : Measure (Fx A a r × Fx A a t)) (_ : IsFiniteMeasureOnCompacts ν), ν (Piece e f P i C) < ∞ := by
  intro A _ _ _ a r t _ _ e f P i C hC h0 ν _
  obtain ⟨D₃, hD₃, h₃⟩ := exists_compact_comb (A := A) t hC hC hC
  have hS : IsCompact ((fun w : A × A => w.1 + w.2) '' (C ×ˢ C)) :=
    (hC.prod hC).image continuous_add
  obtain ⟨D, hD, hDm⟩ := exists_compact_comb (A := A) r (hC.union hD₃) hC hS
  refine lt_of_le_of_lt (measure_mono ?_)
    (((entries_isCompact (m := a) (n := r) hC).prod (entries_isCompact (m := a) (n := t) hD)).measure_lt_top)
  rintro z ⟨-, hz, hy, hv, hvi, c, hci, hc, hcv⟩
  refine ⟨hz, fun p k => ?_⟩
  have hyk : ∀ l, yc P z l k ∈ (fun w : A × A => w.1 + w.2) '' (C ×ˢ C) := fun l =>
    ⟨(f * yc P z l k, (1 - f) * yc P z l k), ⟨(hy l k).1, (hy l k).2⟩, by simp only; ring⟩
  have hvk : vc P z p k ∈ C ∪ D₃ := by
    by_cases hk : k = i
    · subst hk
      right
      have hmem := h₃ ((1 - f) * vc P z p k) c (fun j => if j = k then 0 else vc P z p j) (hvi p)
        (fun j => (hc j).2) (fun j => by
          by_cases hj : j = k
          · simpa [hj] using h0
          · simpa [hj] using hv p j hj)
      have hsum : ∑ j, c j * (if j = k then 0 else vc P z p j) = f * vc P z p k := by
        rw [hcv p]
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hj : j = k
        · subst hj
          simp [hci]
        · simp [hj]
      rw [hsum] at hmem
      have hE : (1 - f) * vc P z p k + f * vc P z p k = vc P z p k := by ring
      rwa [hE] at hmem
    · exact Or.inl (hv p k hk)
  have hE : z.2 p k = vc P z p k + ∑ l, z.1 p l * yc P z l k := by
    simp [vc, Matrix.sub_apply, Matrix.mul_apply]
  rw [hE]
  exact hDm _ _ _ hvk (fun l => hz p l) hyk

end GlobalTheory.CompanionTheory.NullFr
end

section

open MeasureTheory Topology
open scoped ENNReal NNReal Matrix Pointwise

namespace GlobalTheory.CompanionTheory.SplitExtLat

theorem aedisjoint_smul_image_prod : ∀ (P G₁ : Type) [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [LocallyCompactSpace P] [SecondCountableTopology P] [T2Space P] [MeasurableSpace P] [BorelSpace P] [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁] (ι : G₁ →* P) (π : P →* G₁) (hι : Continuous ι) (hπ : Continuous π) (hπι : ∀ u, π (ι u) = u) (Γ : Subgroup P) (Γ₁ : Subgroup G₁) [Countable Γ₁], (∀ γ ∈ Γ, π γ ∈ Γ₁) → ∀ (ν : Measure π.ker) [ν.IsHaarMeasure] (μ₁ : Measure G₁) [μ₁.IsHaarMeasure] (D : Set π.ker) (𝓕₁ : Set G₁), (∀ x : π.ker, ∃! g : Γ.subgroupOf π.ker, g • x ∈ D) → IsFundamentalDomain Γ₁ 𝓕₁ μ₁ → ∀ γ : Γ, γ ≠ 1 → AEDisjoint (Measure.map (GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι) (ν.prod μ₁)) (γ • (GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι '' (D ×ˢ 𝓕₁))) (GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι '' (D ×ˢ 𝓕₁)) := by
  intro P G₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ι π hι hπ hπι Γ Γ₁ _ hΓ ν _ μ₁ _ D 𝓕₁ hD h𝓕 γ hγ
  have hker : ∀ z : π.ker, π (z : P) = 1 := fun z => MonoidHom.mem_ker.1 z.2
  have hfa : ∀ z : π.ker × G₁, GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι z = (z.1 : P) * ι z.2 :=
    GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo_apply ι π hι hπ hπι
  set f := GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι with hf
  have hπx : ∀ z : π.ker × G₁, π (f z) = z.2 := by
    intro z
    rw [hfa, map_mul, hker, one_mul, hπι]
  let g : Γ₁ := ⟨π γ, hΓ γ γ.2⟩
  have hsub : γ • (f '' (D ×ˢ 𝓕₁)) ∩ f '' (D ×ˢ 𝓕₁) ⊆ π ⁻¹' (g • 𝓕₁ ∩ 𝓕₁) := by
    rintro x ⟨⟨y, ⟨z, ⟨-, hz⟩, rfl⟩, rfl⟩, ⟨z', ⟨-, hz'⟩, hzx⟩⟩
    dsimp only at hzx ⊢
    have hγπ : π (γ • f z) = π γ * z.2 := by
      rw [Subgroup.smul_def, smul_eq_mul, map_mul, hπx]
    refine ⟨⟨z.2, hz, ?_⟩, ?_⟩
    · dsimp only
      rw [hγπ, Subgroup.smul_def, smul_eq_mul]
    · rw [← hzx, hπx]
      exact hz'
  by_cases hg : g = 1
  · have hγk : (γ : P) ∈ π.ker := MonoidHom.mem_ker.2 (congrArg Subtype.val hg)
    suffices hempty : γ • (f '' (D ×ˢ 𝓕₁)) ∩ f '' (D ×ˢ 𝓕₁) = ∅ by
      show Measure.map f (ν.prod μ₁) _ = 0
      rw [hempty, measure_empty]
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨⟨y, ⟨z, ⟨hz1, hz2⟩, rfl⟩, rfl⟩, ⟨z', ⟨hz1', hz2'⟩, hzx⟩⟩
    dsimp only at hzx
    have h2 : z'.2 = z.2 := by
      have := congrArg π hzx
      rw [hπx, Subgroup.smul_def, smul_eq_mul, map_mul, hπx, MonoidHom.mem_ker.1 hγk, one_mul] at this
      exact this
    have h1 : (z'.1 : P) = (γ : P) * z.1 := by
      have := hzx
      rw [hfa, Subgroup.smul_def, smul_eq_mul, hfa, h2, ← mul_assoc] at this
      exact mul_right_cancel this
    let γk : Γ.subgroupOf π.ker := ⟨⟨γ, hγk⟩, Subgroup.mem_subgroupOf.2 γ.2⟩
    obtain ⟨g₀, -, huniq⟩ := hD z.1
    have e1 : (1 : Γ.subgroupOf π.ker) = g₀ := huniq 1 (by show (1 : Γ.subgroupOf π.ker) • z.1 ∈ D; rw [one_smul]; exact hz1)
    have e2 : γk = g₀ := huniq γk (by
      show γk • z.1 ∈ D
      have : γk • z.1 = z'.1 := Subtype.ext (by rw [Subgroup.smul_def, smul_eq_mul, Subgroup.coe_mul]; exact h1.symm)
      rw [this]
      exact hz1')
    apply hγ
    have := congrArg (fun t : Γ.subgroupOf π.ker => ((t : π.ker) : P)) (e2.trans e1.symm)
    exact Subtype.ext this
  · have hN : μ₁ (g • 𝓕₁ ∩ 𝓕₁) = 0 := by
      have := h𝓕.aedisjoint hg
      simp only [Function.onFun, one_smul] at this
      exact this
    have hpre : f ⁻¹' (π ⁻¹' (g • 𝓕₁ ∩ 𝓕₁)) = Set.univ ×ˢ (g • 𝓕₁ ∩ 𝓕₁) := by
      ext z
      simp only [Set.mem_preimage, hπx, Set.mem_prod, Set.mem_univ, true_and]
    have hmap : Measure.map f (ν.prod μ₁) (π ⁻¹' (g • 𝓕₁ ∩ 𝓕₁)) = 0 := by
      rw [show Measure.map f (ν.prod μ₁) (π ⁻¹' (g • 𝓕₁ ∩ 𝓕₁)) = (ν.prod μ₁) (f ⁻¹' (π ⁻¹' (g • 𝓕₁ ∩ 𝓕₁))) from
        f.toMeasurableEquiv.map_apply _, hpre, Measure.prod_prod, hN, mul_zero]
    exact measure_mono_null hsub hmap

end GlobalTheory.CompanionTheory.SplitExtLat
end

section

open MeasureTheory Topology
open scoped ENNReal NNReal Matrix Pointwise

namespace GlobalTheory.CompanionTheory.SplitExtLat

theorem ae_exists_smul_mem_image_prod :
    ∀ (P G₁ : Type) [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [LocallyCompactSpace P] [SecondCountableTopology P] [T2Space P] [MeasurableSpace P] [BorelSpace P] [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁] (ι : G₁ →* P) (π : P →* G₁) (hι : Continuous ι) (hπ : Continuous π) (hπι : ∀ u, π (ι u) = u) (Γ : Subgroup P) (Γ₁ : Subgroup G₁) [Countable Γ₁], (∀ u ∈ Γ₁, ι u ∈ Γ) → ∀ (ν : Measure π.ker) [ν.IsHaarMeasure] (μ₁ : Measure G₁) [μ₁.IsHaarMeasure] (D : Set π.ker) (𝓕₁ : Set G₁), (∀ x : π.ker, ∃! g : Γ.subgroupOf π.ker, g • x ∈ D) → IsFundamentalDomain Γ₁ 𝓕₁ μ₁ → ∀ᵐ p ∂(Measure.map (GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι) (ν.prod μ₁)), ∃ γ : Γ, γ • p ∈ (GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι '' (D ×ˢ 𝓕₁)) := by
  intro P G₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ι π hι hπ hπι Γ Γ₁ _ hΓ ν _ μ₁ _ D 𝓕₁ hD h𝓕
  rw [(GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι).measurableEmbedding.ae_map_iff]
  have hcov : ∀ᵐ z ∂(ν.prod μ₁), ∃ γ₁ : Γ₁, γ₁ • z.2 ∈ 𝓕₁ :=
    Measure.quasiMeasurePreserving_snd.ae h𝓕.ae_covers
  filter_upwards [hcov] with z hz
  obtain ⟨m, u⟩ := z
  obtain ⟨γ₁, hγ₁⟩ := hz
  obtain ⟨δ, hδ, -⟩ := hD (GlobalTheory.CompanionTheory.SplitExtLat.kerPart ι π hπι (ι γ₁) *
    MulAut.conjNormal (ι (π (ι γ₁))) m)
  have hδΓ : ((δ : π.ker) : P) ∈ Γ := Subgroup.mem_subgroupOf.mp δ.2
  refine ⟨⟨((δ : π.ker) : P) * ι γ₁, Γ.mul_mem hδΓ (hΓ γ₁ γ₁.2)⟩,
    ⟨(δ • (GlobalTheory.CompanionTheory.SplitExtLat.kerPart ι π hπι (ι γ₁) * MulAut.conjNormal (ι (π (ι γ₁))) m),
      γ₁ • u), ⟨hδ, hγ₁⟩, ?_⟩⟩
  simp only [GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo_apply, Subgroup.smul_def, smul_eq_mul,
    Subgroup.coe_mul]
  rw [mul_assoc (((δ : π.ker) : P)) (ι (γ₁ : G₁)), GlobalTheory.CompanionTheory.SplitExtLat.mul_split ι π hπι (ι γ₁) m u,
    hπι, Subgroup.coe_mul, mul_assoc]

end GlobalTheory.CompanionTheory.SplitExtLat
end

section

open MeasureTheory Topology
open scoped ENNReal NNReal Matrix Pointwise

namespace GlobalTheory.CompanionTheory.SplitExtLat

theorem isHaarMeasure_map_splitHomeo :
    ∀ (P G₁ : Type) [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [LocallyCompactSpace P] [SecondCountableTopology P] [T2Space P] [MeasurableSpace P] [BorelSpace P] [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁] (ι : G₁ →* P) (π : P →* G₁) (hι : Continuous ι) (hπ : Continuous π) (hπι : ∀ u, π (ι u) = u) (ν : Measure π.ker) [ν.IsHaarMeasure] (μ₁ : Measure G₁) [μ₁.IsHaarMeasure], (∀ u, Measure.map (fun m : π.ker => MulAut.conjNormal (ι u) m) ν = ν) → (Measure.map (GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι) (ν.prod μ₁)).IsHaarMeasure := by
  intro P G₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ι π hι hπ hπι ν _ μ₁ _ hconj
  have hclosed : IsClosed (π.ker : Set P) := by
    have hk : (π.ker : Set P) = π ⁻¹' {1} := by
      ext p
      simp
    rw [hk]
    exact isClosed_singleton.preimage hπ
  have : LocallyCompactSpace π.ker := hclosed.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology π.ker :=
    TopologicalSpace.Subtype.secondCountableTopology (π.ker : Set P)
  have : SigmaCompactSpace π.ker := inferInstance
  have : SigmaFinite ν := inferInstance
  set Φ := splitHomeo ι π hι hπ hπι with hΦdef
  have hΦm : Measurable Φ := Φ.continuous.measurable
  have hinv : (Measure.map Φ (ν.prod μ₁)).IsMulLeftInvariant := by
    refine ⟨fun g => ?_⟩
    set k₀ := kerPart ι π hπι g
    have hcm : Measurable (fun m : π.ker => MulAut.conjNormal (ι (π g)) m) :=
      ((continuous_conj ι π hι).comp (Continuous.prodMk_right (π g))).measurable
    have hfm : Measurable (fun m : π.ker => k₀ * MulAut.conjNormal (ι (π g)) m) :=
      (measurable_const_mul k₀).comp hcm
    have hhm : Measurable (fun u : G₁ => π g * u) := measurable_const_mul _
    have e1 : Measure.map (fun m : π.ker => k₀ * MulAut.conjNormal (ι (π g)) m) ν = ν := by
      have hsplit : (fun m : π.ker => k₀ * MulAut.conjNormal (ι (π g)) m) =
          (fun x => k₀ * x) ∘ (fun m : π.ker => MulAut.conjNormal (ι (π g)) m) := rfl
      rw [hsplit, ← Measure.map_map (measurable_const_mul k₀) hcm, hconj, map_mul_left_eq_self]
    have e2 : Measure.map (fun u : G₁ => π g * u) μ₁ = μ₁ := map_mul_left_eq_self μ₁ _
    have hcomp : (fun x => g * x) ∘ Φ =
        Φ ∘ Prod.map (fun m : π.ker => k₀ * MulAut.conjNormal (ι (π g)) m) (fun u : G₁ => π g * u) := by
      funext z
      simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, hΦdef, splitHomeo_apply]
      exact mul_split ι π hπι g z.1 z.2
    rw [Measure.map_map (measurable_const_mul g) hΦm, hcomp, ← Measure.map_map hΦm (hfm.prodMap hhm),
      ← Measure.map_prod_map ν μ₁ hfm hhm, e1, e2]
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : P)
  have hKm : MeasurableSet K := hK.measurableSet
  refine Measure.isHaarMeasure_of_isCompact_nonempty_interior _ K hK ⟨1, mem_interior_iff_mem_nhds.mpr hK1⟩ ?_ ?_
  · rw [Measure.map_apply hΦm hKm]
    have hopen : IsOpen (Φ ⁻¹' interior K) := isOpen_interior.preimage Φ.continuous
    have hne : (Φ ⁻¹' interior K).Nonempty := by
      obtain ⟨z, hz⟩ := Φ.surjective 1
      refine ⟨z, ?_⟩
      show Φ z ∈ interior K
      rw [hz]
      exact mem_interior_iff_mem_nhds.mpr hK1
    exact ((hopen.measure_pos _ hne).trans_le (measure_mono (Set.preimage_mono interior_subset))).ne'
  · rw [Measure.map_apply hΦm hKm]
    exact (Φ.isCompact_preimage.mpr hK).measure_lt_top.ne

end GlobalTheory.CompanionTheory.SplitExtLat
end

section

open MeasureTheory Topology
open scoped ENNReal NNReal Matrix Pointwise

namespace GlobalTheory.CompanionTheory.SplitExtLat

theorem setLIntegral_splitHomeo_image_prod
    (P G₁ : Type) [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [LocallyCompactSpace P]
    [SecondCountableTopology P] [T2Space P] [MeasurableSpace P] [BorelSpace P]
    [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁]
    [SecondCountableTopology G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁]
    (ι : G₁ →* P) (π : P →* G₁) (hι : Continuous ι) (hπ : Continuous π)
    (hπι : ∀ u, π (ι u) = u) (ν : Measure π.ker) [ν.IsHaarMeasure]
    (μ₁ : Measure G₁) [μ₁.IsHaarMeasure] (D : Set π.ker) (𝓕₁ : Set G₁) :
    MeasurableSet D → NullMeasurableSet 𝓕₁ μ₁ →
      NullMeasurableSet (GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι '' (D ×ˢ 𝓕₁))
        (Measure.map (GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι) (ν.prod μ₁)) ∧
      ∀ f : P → ℝ≥0∞, Measurable f →
        ∫⁻ p in (GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι '' (D ×ˢ 𝓕₁)), f p
            ∂(Measure.map (GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι) (ν.prod μ₁)) =
          ∫⁻ u in 𝓕₁, ∫⁻ m in D, f ((m : P) * ι u) ∂ν ∂μ₁ := by
  intro hD h𝓕
  have hker : IsClosed ((π.ker : Set P)) := by
    rw [MonoidHom.coe_ker]
    exact isClosed_singleton.preimage hπ
  have hsc : SecondCountableTopology π.ker :=
    TopologicalSpace.Subtype.secondCountableTopology (π.ker : Set P)
  have hlc : LocallyCompactSpace π.ker := hker.locallyCompactSpace
  have hσc : SigmaCompactSpace π.ker := sigmaCompactSpace_of_locallyCompact_secondCountable
  have hνσ : SigmaFinite ν := Measure.IsHaarMeasure.sigmaFinite ν
  set e := GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι with he
  have hemb : MeasurableEmbedding e := e.measurableEmbedding
  refine ⟨?_, ?_⟩
  · rw [e.image_eq_preimage_symm]
    exact (hD.nullMeasurableSet.prod h𝓕).preimage
      (MeasurableEquiv.quasiMeasurePreserving_symm (ν.prod μ₁) e.toMeasurableEquiv)
  · intro f hf
    rw [hemb.restrict_map, Set.preimage_image_eq _ e.injective, hemb.lintegral_map,
      ← Measure.prod_restrict, lintegral_prod_symm']
    · rfl
    · exact hf.comp hemb.measurable

end GlobalTheory.CompanionTheory.SplitExtLat
end

section

open TensorProduct CrystallineSemistableComparison.Pb.Psi

namespace GlobalTheory.CompanionTheory.FrobPsi

theorem T_ksmul : ∀ {W A C₀ : Type} [CommRing W] [CommRing A] [CommRing C₀] [Algebra W A] {K₀ : Type} [Field K₀] [Algebra W K₀] {L : Type 1} [AddCommGroup L] [Module W L] (c : A →+* C₀) (k : K₀ →+* C₀) (hk : ∀ w : W, k (algebraMap W K₀ w) = c (algebraMap W A w)), ∀ (x : K₀) (f : Module.Dual K₀ (K₀ ⊗[W] L)) (z : A ⊗[W] L), T c k hk (x • f) z = k x * T c k hk f z := by
  intro W A C₀ _ _ _ _ K₀ _ _ L _ _ c k hk x f z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a y =>
    rw [T_tmul, T_tmul, LinearMap.smul_apply, smul_eq_mul, map_mul]
    ring
  | add z z' hz hz' => rw [map_add (f := _), map_add (f := _), hz, hz', mul_add]

end GlobalTheory.CompanionTheory.FrobPsi
end
