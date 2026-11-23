module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Data.Finset.Defs
public import Mathlib.Algebra.Module.LinearMap.Star
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Linter.Style
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Data.Finset.Image
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.Algebra.MvPolynomial.Funext

@[expose] public section

section

namespace GlobalTheory

theorem isolate_abstract : ∀ (X : Type) [AddCommGroup X] (Γ G : AddSubgroup X) (V : Type) [AddCommGroup V] [Module ℂ V] (T : X → V →ₗ[ℂ] V) (W : Set V) (β : X → X → ℂ) (a : X → ℂ) (χ : X → X → ℂ), Γ ≤ G → (∀ v, T 0 v = v) → (∀ x y v, T x (T y v) = β x y • T (x + y) v) → (∀ x y, β x y ≠ 0) → (∀ γ ∈ Γ, a γ ≠ 0 ∧ ∀ v ∈ W, T γ v = a γ • v) → (∀ γ ∈ Γ, ∀ x v, T γ (T x v) = χ x γ • T x (T γ v)) → (∀ x, ∀ γ ∈ Γ, ∀ γ' ∈ Γ, χ (x + γ') γ = χ x γ) → (∀ x ∈ G, ∀ y ∈ G, x - y ∉ Γ → ∃ γ ∈ Γ, χ x γ ≠ χ y γ) → ∀ (J : Finset X) (c : X → ℂ), (∀ x ∈ J, x ∈ G) → (∀ v ∈ W, ∑ x ∈ J, c x • T x v = 0) ∨ ∃ κ : X →₀ ℂ, (∀ y ∈ κ.support, y ∈ G) ∧ ∀ v ∈ W, ∑ y ∈ κ.support, κ y • T y (∑ x ∈ J, c x • T x v) = v := by
  intro X _ Γ G V _ _ T W β a χ hΓG hT0 hTT hβ ha hχ hχc hsep J c hJ
  classical
  obtain ⟨A, hA⟩ : ∃ A : Submodule ℂ (V →ₗ[ℂ] V), A = Submodule.span ℂ (T '' (G : Set X)) := ⟨_, rfl⟩
  have hTA : ∀ y ∈ G, T y ∈ A := fun y hy => hA ▸ Submodule.subset_span ⟨y, hy, rfl⟩
  have hmulT : ∀ y ∈ G, ∀ g ∈ A, T y * g ∈ A := by
    intro y hy g hg
    rw [hA] at hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨z, hz, rfl⟩ := hg
      have e : T y * T z = β y z • T (y + z) := by ext v; simp [hTT]
      rw [e]; exact A.smul_mem _ (hTA _ (G.add_mem hy hz))
    | zero => simp
    | add f g _ _ hf hg => rw [mul_add]; exact A.add_mem hf hg
    | smul r f _ hf => rw [mul_smul_comm]; exact A.smul_mem r hf
  have hmul : ∀ f ∈ A, ∀ g ∈ A, f * g ∈ A := by
    intro f hf g hg
    rw [hA] at hf
    induction hf using Submodule.span_induction with
    | mem f hf => obtain ⟨y, hy, rfl⟩ := hf; exact hmulT y hy g hg
    | zero => simp
    | add f f' _ _ h h' => rw [add_mul]; exact A.add_mem h h'
    | smul r f _ h => rw [smul_mul_assoc]; exact A.smul_mem r h
  have hone : (1 : V →ₗ[ℂ] V) ∈ A := by
    have e : (1 : V →ₗ[ℂ] V) = T 0 := by ext v; simp [hT0]
    rw [e]; exact hTA 0 G.zero_mem
  have hκ : ∀ L ∈ A, ∃ κ : X →₀ ℂ, (∀ y ∈ κ.support, y ∈ G) ∧ ∀ u, ∑ y ∈ κ.support, κ y • T y u = L u := by
    intro L hL
    rw [hA, Finsupp.mem_span_image_iff_linearCombination] at hL
    obtain ⟨l, hl, rfl⟩ := hL
    refine ⟨l, fun y hy => (Finsupp.mem_supported _ _).1 hl hy, fun u => ?_⟩
    simp [Finsupp.linearCombination_apply, Finsupp.sum, LinearMap.sum_apply]
  have hshift : ∀ x0 x, x - x0 ∈ Γ → ∀ v ∈ W, T x v = ((β x0 (x - x0))⁻¹ * a (x - x0)) • T x0 v := by
    intro x0 x h v hv
    have h1 := hTT x0 (x - x0) v
    have e : x0 + (x - x0) = x := by abel
    rw [(ha _ h).2 v hv, map_smul, e] at h1
    rw [mul_smul, h1, smul_smul, inv_mul_cancel₀ (hβ _ _), one_smul]
  have hcls : ∀ x0 (c : X → ℂ), ∀ v ∈ W, ∑ x ∈ J, (if x - x0 ∈ Γ then c x else 0) • T x v
      = (∑ x ∈ J, if x - x0 ∈ Γ then c x * ((β x0 (x - x0))⁻¹ * a (x - x0)) else 0) • T x0 v := by
    intro x0 c v hv
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs with h
    · rw [mul_smul, ← hshift x0 x h v hv]
    · simp
  have hQ : ∀ γ ∈ Γ, ∀ k : ℂ, ∀ c : X → ℂ, ∀ v ∈ W,
      ((a γ)⁻¹ • T γ - k • (1 : V →ₗ[ℂ] V)) (∑ x ∈ J, c x • T x v) = ∑ x ∈ J, (c x * (χ x γ - k)) • T x v := by
    intro γ hγ k c v hv
    have hb : ∀ x, T γ (T x v) = (χ x γ * a γ) • T x v := by
      intro x; rw [hχ γ hγ x v, (ha γ hγ).2 v hv, map_smul, smul_smul]

    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sum, map_smul, hb,
    Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [smul_smul, ← sub_smul]
    congr 1
    have := (ha γ hγ).1
    field_simp
  have hQA : ∀ γ ∈ Γ, ∀ k : ℂ, ((a γ)⁻¹ • T γ - k • (1 : V →ₗ[ℂ] V)) ∈ A := fun γ hγ k =>
    A.sub_mem (A.smul_mem _ (hTA γ (hΓG hγ))) (A.smul_mem _ hone)
  have hproj : ∀ x0 ∈ G, ∀ n : ℕ, ∀ c : X → ℂ, (J.filter (fun x => c x ≠ 0 ∧ x - x0 ∉ Γ)).card = n →
      ∃ L ∈ A, ∃ s : ℂ, s ≠ 0 ∧ ∀ v ∈ W,
        L (∑ x ∈ J, c x • T x v) = s • ∑ x ∈ J, (if x - x0 ∈ Γ then c x else 0) • T x v := by
    intro x0 hx0 n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro c hn
    by_cases hS : ∃ x1 ∈ J, c x1 ≠ 0 ∧ x1 - x0 ∉ Γ
    · obtain ⟨x1, hx1J, hcx1, hx1⟩ := hS
      obtain ⟨γ, hγ, hne⟩ := hsep x1 (hJ x1 hx1J) x0 hx0 hx1
      obtain ⟨c', hc'⟩ : ∃ c' : X → ℂ, c' = fun x => c x * (χ x γ - χ x1 γ) := ⟨_, rfl⟩
      have hsub : J.filter (fun x => c' x ≠ 0 ∧ x - x0 ∉ Γ) ⊂ J.filter (fun x => c x ≠ 0 ∧ x - x0 ∉ Γ) := by
        rw [Finset.ssubset_iff_of_subset]
        · refine ⟨x1, by simp [hx1J, hcx1, hx1], ?_⟩
          simp [hc']
        · intro x hx
          simp only [Finset.mem_filter] at hx ⊢
          exact ⟨hx.1, fun h => hx.2.1 (by simp [hc', h]), hx.2.2⟩
      obtain ⟨L', hL', s', hs', hL'eq⟩ := ih _ (hn ▸ Finset.card_lt_card hsub) c' rfl
      refine ⟨L' * ((a γ)⁻¹ • T γ - χ x1 γ • (1 : V →ₗ[ℂ] V)), hmul _ hL' _ (hQA γ hγ _),
        s' * (χ x0 γ - χ x1 γ), mul_ne_zero hs' (sub_ne_zero.2 (Ne.symm hne)), fun v hv => ?_⟩
      rw [Module.End.mul_apply, hQ γ hγ _ c v hv,
        show (∑ x ∈ J, (c x * (χ x γ - χ x1 γ)) • T x v) = ∑ x ∈ J, c' x • T x v by rw [hc'],
        hL'eq v hv, mul_smul]
      congr 1
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      split_ifs with h
      · have hχx : χ x γ = χ x0 γ := by simpa using hχc x0 γ hγ (x - x0) h
        simp only [hc', smul_smul, hχx, mul_comm]
      · simp
    · push_neg at hS
      refine ⟨1, hone, 1, one_ne_zero, fun v hv => ?_⟩
      rw [Module.End.one_apply, one_smul]
      refine Finset.sum_congr rfl fun x hx => ?_
      split_ifs with h
      · rfl
      · by_cases hc : c x = 0
        · simp [hc]
        · exact absurd (hS x hx hc) h
  have main : ∀ n : ℕ, ∀ c : X → ℂ, (J.filter (fun x => c x ≠ 0)).card = n →
      (∀ v ∈ W, ∑ x ∈ J, c x • T x v = 0) ∨ ∃ L ∈ A, ∀ v ∈ W, L (∑ x ∈ J, c x • T x v) = v := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro c hn
    by_cases hS : ∃ x0 ∈ J, c x0 ≠ 0
    · obtain ⟨x0, hx0J, hcx0⟩ := hS
      have hx0 := hJ x0 hx0J
      obtain ⟨d, hd⟩ : ∃ d : ℂ, d = ∑ x ∈ J, if x - x0 ∈ Γ then c x * ((β x0 (x - x0))⁻¹ * a (x - x0)) else 0 :=
        ⟨_, rfl⟩
      by_cases hd0 : d = 0
      · obtain ⟨c'', hc''⟩ : ∃ c'' : X → ℂ, c'' = fun x => if x - x0 ∈ Γ then 0 else c x := ⟨_, rfl⟩
        have hsub : J.filter (fun x => c'' x ≠ 0) ⊂ J.filter (fun x => c x ≠ 0) := by
          rw [Finset.ssubset_iff_of_subset]
          · refine ⟨x0, by simp [hx0J, hcx0], ?_⟩
            simp [hc'']
          · intro x hx
            simp only [Finset.mem_filter] at hx ⊢
            refine ⟨hx.1, fun h => hx.2 ?_⟩
            simp [hc'', h]
        have heq : ∀ v ∈ W, ∑ x ∈ J, c x • T x v = ∑ x ∈ J, c'' x • T x v := by
          intro v hv
          have h1 := hcls x0 c v hv
          rw [← hd, hd0, zero_smul] at h1
          calc ∑ x ∈ J, c x • T x v
              = ∑ x ∈ J, ((if x - x0 ∈ Γ then c x else 0) • T x v + c'' x • T x v) :=
                Finset.sum_congr rfl fun x _ => by simp only [hc'']; split_ifs <;> simp
            _ = ∑ x ∈ J, c'' x • T x v := by rw [Finset.sum_add_distrib, h1, zero_add]
        rcases ih _ (hn ▸ Finset.card_lt_card hsub) c'' rfl with h | ⟨L, hL, hLeq⟩
        · exact Or.inl fun v hv => by rw [heq v hv]; exact h v hv
        · exact Or.inr ⟨L, hL, fun v hv => by rw [heq v hv]; exact hLeq v hv⟩
      · obtain ⟨L, hL, s, hs, hLeq⟩ := hproj x0 hx0 _ c rfl
        refine Or.inr ⟨(((s * d) * β (-x0) x0)⁻¹ • T (-x0)) * L,
          hmul _ (A.smul_mem _ (hTA _ (G.neg_mem hx0))) _ hL, fun v hv => ?_⟩
        rw [Module.End.mul_apply, LinearMap.smul_apply, hLeq v hv, hcls x0 c v hv, ← hd, map_smul, map_smul,
          hTT, neg_add_cancel, hT0, smul_smul, smul_smul, smul_smul]
        have hβ' := hβ (-x0) x0
        have e : ((s * d) * β (-x0) x0)⁻¹ * s * d * β (-x0) x0 = 1 := by
          field_simp
        rw [e, one_smul]
    · push_neg at hS
      exact Or.inl fun v _ => Finset.sum_eq_zero fun x hx => by simp [hS x hx]
  rcases main _ c rfl with h | ⟨L, hL, hLeq⟩
  · exact Or.inl h
  · obtain ⟨κ, hκG, hκeq⟩ := hκ L hL
    exact Or.inr ⟨κ, hκG, fun v hv => by rw [hκeq, hLeq v hv]⟩

end GlobalTheory
end

section

namespace GlobalTheory.DoubleCosetIndicator

def dc {G : Type} [Group G] (R K : Subgroup G) (t : G) : Set G :=
  {x : G | ∃ r ∈ R, ∃ κ ∈ K, x = r * t * κ}

theorem dc_subset {G : Type} [Group G] (R K : Subgroup G) {s t x : G}
    (hs : x ∈ dc R K s) (ht : x ∈ dc R K t) : dc R K s ⊆ dc R K t := by
  rintro y ⟨a, ha, b, hb, rfl⟩
  obtain ⟨r, hr, κ, hκ, hx⟩ := hs
  obtain ⟨r', hr', κ', hκ', hx'⟩ := ht
  have hrs : r * s * κ = r' * t * κ' := hx.symm.trans hx'
  have hs' : s = r⁻¹ * r' * t * κ' * κ⁻¹ := by
    calc s = r⁻¹ * (r * s * κ) * κ⁻¹ := by group
      _ = r⁻¹ * (r' * t * κ') * κ⁻¹ := by rw [hrs]
      _ = r⁻¹ * r' * t * κ' * κ⁻¹ := by group
  refine ⟨a * r⁻¹ * r', R.mul_mem (R.mul_mem ha (R.inv_mem hr)) hr', κ' * κ⁻¹ * b,
    K.mul_mem (K.mul_mem hκ' (K.inv_mem hκ)) hb, ?_⟩
  rw [hs']
  group

theorem exists_eq_sum_indicator {G : Type} [Group G] {M : Type} [AddCommMonoid M]
    (R K : Subgroup G) (T : Finset G) (φ : G → M)
    (hR : ∀ r ∈ R, ∀ x : G, φ (r * x) = φ x) (hK : ∀ κ ∈ K, ∀ x : G, φ (x * κ) = φ x)
    (hT : ∀ x : G, φ x ≠ 0 → ∃ t ∈ T, x ∈ dc R K t) :
    ∃ c : G → M, (∀ t : G, c t = 0 ∨ c t = φ t) ∧
      ∀ x : G, φ x = ∑ t ∈ T, Set.indicator (dc R K t) (fun _ => c t) x := by
  classical

  let S : G → Finset G := fun t => T.filter (fun t' => dc R K t' = dc R K t)
  let rep : G → G := fun t => if h : (S t).Nonempty then h.choose else t
  let c : G → M := fun t => if t ∈ T ∧ rep t = t then φ t else 0
  have hdc_eq : ∀ {s t x : G}, x ∈ dc R K s → x ∈ dc R K t → dc R K s = dc R K t := fun hs ht =>
    Set.Subset.antisymm (dc_subset R K hs ht) (dc_subset R K ht hs)
  have hinv : ∀ {s x : G}, x ∈ dc R K s → φ x = φ s := by
    rintro s x ⟨r, hr, κ, hκ, rfl⟩
    rw [hK κ hκ, hR r hr]
  refine ⟨c, fun t => ?_, fun x => ?_⟩
  · simp only [c]
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl
  by_cases hx : ∃ t ∈ T, x ∈ dc R K t
  · obtain ⟨t0, ht0, hxt0⟩ := hx
    have hS : (S t0).Nonempty := ⟨t0, Finset.mem_filter.mpr ⟨ht0, rfl⟩⟩
    obtain ⟨ht1T, ht1dc⟩ := Finset.mem_filter.mp hS.choose_spec
    have hrep : ∀ t, dc R K t = dc R K t0 → rep t = hS.choose := by
      intro t ht
      have hSt : S t = S t0 := by simp only [S, ht]
      simp only [rep, hSt, dif_pos hS]
    have hxt1 : x ∈ dc R K hS.choose := by rw [ht1dc]; exact hxt0
    rw [Finset.sum_eq_single hS.choose]
    · have hc1 : c hS.choose = φ hS.choose := by
        simp only [c]
        rw [if_pos ⟨ht1T, hrep _ ht1dc⟩]
      rw [Set.indicator_of_mem hxt1, hc1, hinv hxt1]
    · intro t _ hne
      by_cases hxt : x ∈ dc R K t
      · have hc0 : c t = 0 := by
          simp only [c]
          rw [if_neg]
          rintro ⟨-, h⟩
          exact hne (h.symm.trans (hrep t (hdc_eq hxt hxt0)))
        rw [Set.indicator_of_mem hxt, hc0]
      · rw [Set.indicator_of_notMem hxt]
    · intro h
      exact absurd ht1T h
  · push_neg at hx
    have hφ : φ x = 0 := by
      by_contra h
      obtain ⟨t, ht, hxt⟩ := hT x h
      exact hx t ht hxt
    rw [hφ]
    symm
    exact Finset.sum_eq_zero fun t ht => Set.indicator_of_notMem (hx t ht) _

theorem main : (let d1 : {G : Type} → [inst : Group G] → Subgroup G → Subgroup G → G → Set G := @(fun {G : Type} [Group G] (R K : Subgroup G) (t : G) ↦ {x : G | ∃ r ∈ R, ∃ κ ∈ K, x = r * t * κ}); ∀ {G : Type} [inst : Group G] {M : Type} [inst_1 : AddCommMonoid M] (R K : Subgroup G) (T : Finset G) (φ : G → M), (∀ r ∈ R, ∀ (x : G), φ (r * x) = φ x) → (∀ κ ∈ K, ∀ (x : G), φ (x * κ) = φ x) → (∀ (x : G), φ x ≠ (0 : M) → ∃ t ∈ T, x ∈ d1 R K t) → ∃ (c : G → M), (∀ (t : G), c t = (0 : M) ∨ c t = φ t) ∧ ∀ (x : G), φ x = ∑ t ∈ T, Set.indicator (d1 R K t) (fun (x : G) ↦ c t) x) := by
  intro d1 G _ M _ R K T φ hR hK hT
  exact exists_eq_sum_indicator R K T φ hR hK hT

end GlobalTheory.DoubleCosetIndicator
end

section

namespace GlobalTheory

theorem addSubgroup_finite_quot_of_commensurable : ∀ (V : Type) [AddCommGroup V] (A L : AddSubgroup V) (N M : ℕ), 0 < N → 0 < M → (∀ v : V, N • v = 0 → v = 0) → (∀ a ∈ A, N • a ∈ L) → (∀ l ∈ L, M • l ∈ A) → (∀ j : ℕ, 0 < j → ∃ R : Finset V, ∀ u ∈ L, ∃ r ∈ R, ∃ v ∈ L, u = r + j • v) → ∀ k : ℕ, 0 < k → ∃ R : Finset V, ∀ u ∈ A, ∃ r ∈ R, ∃ v ∈ A, u = r + k • v := by
  classical
  intro V _ A L N M hN hM htf hAL hLA hfin k hk
  obtain ⟨R₀, hR₀⟩ := hfin (k * N * M) (by positivity)
  let P : V → Prop := fun r₀ => ∃ a ∈ A, ∃ w ∈ L, N • a = r₀ + (k * N * M) • w
  let f : V → V := fun r₀ => if h : P r₀ then h.choose else 0
  refine ⟨R₀.image f, ?_⟩
  intro u hu
  obtain ⟨r₀, hr₀, v, hv, huv⟩ := hR₀ (N • u) (hAL u hu)
  have hP : P r₀ := ⟨u, hu, v, hv, huv⟩
  have hf : f r₀ = hP.choose := dif_pos hP
  obtain ⟨haA, w, hwL, haw⟩ := hP.choose_spec
  refine ⟨f r₀, Finset.mem_image_of_mem f hr₀, M • (v - w), hLA _ (L.sub_mem hv hwL), ?_⟩
  rw [hf]
  have key : N • (u - (hP.choose + k • M • (v - w))) = 0 := by
    have e : N • k • M • (v - w) = (k * N * M) • (v - w) := by
      rw [smul_smul, smul_smul]
      congr 1
      ring
    rw [smul_sub, smul_add, huv, haw, e, smul_sub]
    abel
  exact sub_eq_zero.mp (htf _ key)

end GlobalTheory
end

section

open scoped ComplexConjugate

namespace GlobalTheory

theorem hermitian_adjoint_exists_unique :
    ∀ (A C : Type) [AddCommGroup A] [Module ℂ A] [AddCommGroup C] [Module ℂ C] [FiniteDimensional ℂ C]
      (ipA : A →ₗ[ℂ] A →ₗ⋆[ℂ] ℂ) (ip : C →ₗ[ℂ] C →ₗ⋆[ℂ] ℂ),
      (∀ x y, ip x y = conj (ip y x)) → (∀ x, x ≠ 0 → 0 < (ip x x).re) →
      ∀ (io : C →ₗ[ℂ] A) (u : A), ∃! x : C, ∀ y, ip y x = ipA (io y) u := by
  intro A C _ _ _ _ _ ipA ip _hsym hpos io u

  let g : C →ₗ[ℝ] (C →ₗ[ℂ] ℂ) :=
    { toFun := fun x => ip.flip x
      map_add' := fun x y => by simp
      map_smul' := fun r x => by
        ext y
        have h1 : (r • x : C) = (r : ℂ) • x := rfl
        have h2 : (r • ip.flip x : C →ₗ[ℂ] ℂ) y = (r : ℂ) * ip y x := by
          show ((r : ℂ) • ip.flip x) y = _
          simp
        simp only [RingHom.id_apply]
        rw [h2, h1, LinearMap.map_smulₛₗ]
        simp [Complex.conj_ofReal] }
  have hg : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    by_contra hne
    have h0 : ip x x = 0 := by
      have := LinearMap.congr_fun hx x
      simpa [g] using this
    have := hpos x hne
    rw [h0] at this
    simp at this
  have hrank : Module.finrank ℝ C = Module.finrank ℝ (C →ₗ[ℂ] ℂ) := by
    rw [finrank_real_of_complex, finrank_real_of_complex, Module.finrank_linearMap, Module.finrank_self, mul_one]
  have hs : Function.Surjective g := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mp hg
  obtain ⟨x, hx⟩ := hs ((ipA.flip u).comp io)
  refine ⟨x, fun y => ?_, fun x' hx' => ?_⟩
  · have := LinearMap.congr_fun hx y
    simpa [g] using this
  · apply hg
    ext y
    have hy := LinearMap.congr_fun hx y
    simp only [g, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.flip_apply] at hy ⊢
    rw [hx' y, hy]
    rfl

end GlobalTheory
end

section

namespace GlobalTheory

open MvPolynomial Matrix

noncomputable def hermGenericMatrix {κ : Type} [Field κ] (n : ℕ) (e : κ) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) κ) :=
  Matrix.of fun i j => X (i, j) + X (j, i) + C e * (X (i, j) - X (j, i))

theorem hermGenericMatrix_map_eval {κ : Type} [Field κ] (n : ℕ) (e : κ)
    (u : Fin n × Fin n → κ) :
    (hermGenericMatrix n e).map (MvPolynomial.eval u) =
      Matrix.of fun i j => u (i, j) + u (j, i) + e * (u (i, j) - u (j, i)) := by
  ext i j
  simp [hermGenericMatrix]

theorem hermGenericMatrix_onto {κ : Type} [Field κ] [CharZero κ] (n : ℕ) (e : κ) (he : e ≠ 0)
    (y : Matrix (Fin n) (Fin n) κ) :
    ∃ u : Fin n × Fin n → κ, (hermGenericMatrix n e).map (MvPolynomial.eval u) = y := by
  refine ⟨fun p => (y p.1 p.2 + y p.2 p.1) / 4 + (y p.1 p.2 - y p.2 p.1) / (4 * e), ?_⟩
  rw [hermGenericMatrix_map_eval]
  ext i j
  simp only [Matrix.of_apply]
  field_simp
  ring

theorem eval_det_affine_matrix {κ ι : Type} [Field κ] {n : ℕ} (c d : Matrix (Fin n) (Fin n) κ)
    (G : Matrix (Fin n) (Fin n) (MvPolynomial ι κ)) (u : ι → κ) :
    MvPolynomial.eval u (c.map C * G + d.map C).det =
      (c * G.map (MvPolynomial.eval u) + d).det := by
  rw [RingHom.map_det, map_add (f := _), map_mul]
  congr 1
  ext i j
  simp [Matrix.mul_apply]

theorem exists_hermitian_det_ne_zero_two :
    ∀ (E κ : Type) [Field E] [CharZero E] [Field κ] (σ : E →+* E) (φ : E →+* κ) (δ : E), δ ≠ 0 → σ δ = -δ → ∀ (n : ℕ) (c d y c' d' y' : Matrix (Fin n) (Fin n) κ), (c * y + d).det ≠ 0 → (c' * y' + d').det ≠ 0 → ∃ x : Matrix (Fin n) (Fin n) E, x.map σ = x.transpose ∧ (c * x.map φ + d).det ≠ 0 ∧ (c' * x.transpose.map φ + d').det ≠ 0 := by
  intro E κ _ _ _ σ φ δ hδ hσ n c d y c' d' y' h h'
  haveI : CharZero κ := (RingHom.charZero_iff φ.injective).mp inferInstance
  have he : φ δ ≠ 0 := (map_ne_zero φ).mpr hδ
  set G := hermGenericMatrix n (φ δ) with hG
  have h1 : (c.map C * G + d.map C).det ≠ 0 := by
    obtain ⟨u, hu⟩ := hermGenericMatrix_onto n (φ δ) he y
    intro h0
    have := eval_det_affine_matrix c d G u
    rw [h0, map_zero, hG, hu] at this
    exact h this.symm
  have h2 : (c'.map C * Gᵀ + d'.map C).det ≠ 0 := by
    obtain ⟨u, hu⟩ := hermGenericMatrix_onto n (φ δ) he y'ᵀ
    intro h0
    have := eval_det_affine_matrix c' d' Gᵀ u
    rw [h0, map_zero, Matrix.transpose_map, hG, hu, Matrix.transpose_transpose] at this
    exact h' this.symm
  have h12 := mul_ne_zero h1 h2
  have key : ∃ m : Fin n × Fin n → ℕ, MvPolynomial.eval (fun p => (m p : κ))
      ((c.map C * G + d.map C).det * (c'.map C * Gᵀ + d'.map C).det) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply h12
    apply MvPolynomial.funext_set (fun _ => Set.range (Nat.cast : ℕ → κ))
      (fun _ => Set.infinite_range_of_injective Nat.cast_injective)
    intro x hx
    have hx' : ∀ p, ∃ m : ℕ, (m : κ) = x p := fun p => hx p (Set.mem_univ p)
    choose m hm using hx'
    have : x = fun p => (m p : κ) := funext fun p => (hm p).symm
    rw [this, map_zero]
    exact hcon m
  obtain ⟨m, hm⟩ := key
  rw [map_mul, eval_det_affine_matrix, eval_det_affine_matrix, Matrix.transpose_map, hG,
    hermGenericMatrix_map_eval] at hm
  let x : Matrix (Fin n) (Fin n) E := Matrix.of fun i j =>
    (m (i, j) : E) + (m (j, i) : E) + δ * ((m (i, j) : E) - (m (j, i) : E))
  have hx : x.map φ = Matrix.of fun i j =>
      (m (i, j) : κ) + (m (j, i) : κ) + φ δ * ((m (i, j) : κ) - (m (j, i) : κ)) := by
    ext i j
    simp [x]
  refine ⟨x, ?_, ?_, ?_⟩
  · ext i j
    simp only [x, Matrix.map_apply, Matrix.of_apply, Matrix.transpose_apply, map_add (f := _), map_mul,
      map_sub, map_natCast, hσ]
    ring
  · rw [hx]; exact left_ne_zero_of_mul hm
  · rw [Matrix.transpose_map, hx]; exact right_ne_zero_of_mul hm

end GlobalTheory
end
