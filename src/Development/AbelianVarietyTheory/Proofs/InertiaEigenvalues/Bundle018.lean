module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Matrix.Mul
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
import Mathlib.RingTheory.Henselian
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
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Analysis.Normed.Group.Ultra

@[expose] public section

section

namespace GlobalTheory

private theorem cur_decomposition_of_maximal_minor {K : Type} [Field K] {d r : ℕ} (e : Matrix (Fin d) (Fin d) K)
    (τ σ : Fin r → Fin d) (hA : (e.submatrix τ σ).det ≠ 0)
    (hmax : ∀ τ' σ' : Fin (r + 1) → Fin d, (e.submatrix τ' σ').det = 0) :
    e.submatrix id σ * (e.submatrix τ σ)⁻¹ * e.submatrix τ id = e := by
  ext i j
  set A := e.submatrix τ σ with hAdef
  let B : Matrix (Fin r) (Fin 1) K := Matrix.of fun k _ => e (τ k) j
  let C : Matrix (Fin 1) (Fin r) K := Matrix.of fun _ l => e i (σ l)
  let D : Matrix (Fin 1) (Fin 1) K := Matrix.of fun _ _ => e i j
  have hM : Matrix.fromBlocks A B C D =
      e.submatrix (Sum.elim τ fun _ => i) (Sum.elim σ fun _ => j) := by
    ext (a | a) (b | b) <;> rfl
  have h0 : (Matrix.fromBlocks A B C D).det = 0 := by
    rw [hM, ← Matrix.det_reindex_self finSumFinEquiv, Matrix.reindex_apply,
      Matrix.submatrix_submatrix]
    exact hmax _ _
  have : Invertible A := A.invertibleOfIsUnitDet (isUnit_iff_ne_zero.mpr hA)
  rw [Matrix.det_fromBlocks₁₁, Matrix.det_fin_one, Matrix.invOf_eq_nonsing_inv] at h0
  have h1 := (mul_eq_zero.mp h0).resolve_left hA
  rw [Matrix.sub_apply, sub_eq_zero] at h1
  have h2 : (C * A⁻¹ * B) 0 0 = (e.submatrix id σ * A⁻¹ * e.submatrix τ id) i j := rfl
  rw [← h2, ← h1]
  rfl

private theorem inv_mul_submatrix_apply_eq_det_ratio {K : Type} [Field K] {d r : ℕ}
    (e : Matrix (Fin d) (Fin d) K) (τ σ : Fin r → Fin d) (k : Fin r) (j : Fin d) :
    ((e.submatrix τ σ)⁻¹ * e.submatrix τ id) k j =
      (e.submatrix τ σ).det⁻¹ * (e.submatrix τ (Function.update σ k j)).det := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
  congr 1
  change (Matrix.mulVec (e.submatrix τ σ).adjugate fun l => e (τ l) j) k = _
  rw [← Matrix.cramer_eq_adjugate_mulVec, Matrix.cramer_apply]
  congr 1
  ext a c
  by_cases h : c = k
  · subst h; simp
  · simp [h]

theorem exists_integral_factor_of_idempotent {K : Type} [Field K] (O : ValuationSubring K) (d : ℕ)
    (e : Matrix (Fin d) (Fin d) K) (he : e * e = e) :
    ∃ (r : ℕ) (R : Matrix (Fin r) (Fin d) K) (S : Matrix (Fin d) (Fin r) K),
      (∀ i j, R i j ∈ O) ∧ (∀ i j, S i j ∈ O) ∧ R * S = 1 ∧ R * e = R ∧ e * S * R = e := by
  classical
  let P : ℕ → Prop := fun k => ∃ τ σ : Fin k → Fin d, (e.submatrix τ σ).det ≠ 0
  set r := Nat.findGreatest P d with hr
  have hPr : P r := Nat.findGreatest_spec (m := 0) (Nat.zero_le _) ⟨Fin.elim0, Fin.elim0, by simp⟩
  have hnot : ∀ τ σ : Fin (r + 1) → Fin d, (e.submatrix τ σ).det = 0 := by
    intro τ σ
    by_contra hne
    by_cases hle : r + 1 ≤ d
    · exact Nat.findGreatest_is_greatest (Nat.lt_succ_self r) hle ⟨τ, σ, hne⟩
    · obtain ⟨a, b, hab, hτ⟩ := Fintype.exists_ne_map_eq_of_card_lt τ (by simp; omega)
      exact hne (Matrix.det_zero_of_row_eq hab (by funext c; simp [hτ]))
  let v := O.valuation
  obtain ⟨τ0, σ0, h0⟩ := hPr
  obtain ⟨p, -, hp⟩ := Finset.exists_max_image Finset.univ
    (fun p : (Fin r → Fin d) × (Fin r → Fin d) => v (e.submatrix p.1 p.2).det)
    ⟨(τ0, σ0), Finset.mem_univ _⟩
  obtain ⟨τ, σ⟩ := p
  have hA : (e.submatrix τ σ).det ≠ 0 := by
    intro hz
    have hle := hp (τ0, σ0) (Finset.mem_univ _)
    simp only [hz, map_zero] at hle
    exact h0 ((Valuation.zero_iff _).mp (le_antisymm hle zero_le))
  have hv : v (e.submatrix τ σ).det ≠ 0 := (Valuation.ne_zero_iff _).mpr hA
  let S : Matrix (Fin d) (Fin r) K := Matrix.of fun i k => if i = σ k then 1 else 0
  have hS : ∀ {m : Type} [Fintype m] (M : Matrix m (Fin d) K), M * S = M.submatrix id σ := by
    intro m _ M
    ext a k
    simp [S, Matrix.mul_apply]
  refine ⟨r, (e.submatrix τ σ)⁻¹ * e.submatrix τ id, S, ?_, ?_, ?_, ?_, ?_⟩
  · intro k j
    rw [inv_mul_submatrix_apply_eq_det_ratio, ← O.valuation_le_one_iff, map_mul, map_inv₀]
    have hle := hp (τ, Function.update σ k j) (Finset.mem_univ _)
    calc (v (e.submatrix τ σ).det)⁻¹ * v (e.submatrix τ (Function.update σ k j)).det
        ≤ (v (e.submatrix τ σ).det)⁻¹ * v (e.submatrix τ σ).det := mul_le_mul_right hle _
      _ = 1 := inv_mul_cancel₀ hv
  · intro i k
    simp only [S, Matrix.of_apply]
    split_ifs
    · exact O.one_mem
    · exact O.zero_mem
  · rw [Matrix.mul_assoc, hS]
    exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hA)
  · rw [Matrix.mul_assoc]
    congr 1
    ext a c
    change (e * e) (τ a) c = e (τ a) c
    rw [he]
  · rw [hS, ← Matrix.mul_assoc]
    exact cur_decomposition_of_maximal_minor e τ σ hA hnot

theorem exists_integral_factor_of_idempotent_subfield (C : Type) [NormedField C]
    [IsUltrametricDist C] (F : Subfield C) (d : ℕ) (e : Matrix (Fin d) (Fin d) C)
    (hF : ∀ i j, e i j ∈ F) (he : e * e = e) :
    ∃ (r : ℕ) (R : Matrix (Fin r) (Fin d) C) (S : Matrix (Fin d) (Fin r) C),
      (∀ i j, R i j ∈ F ∧ ‖R i j‖ ≤ 1) ∧ (∀ i j, S i j ∈ F ∧ ‖S i j‖ ≤ 1) ∧
        R * S = 1 ∧ R * e = R ∧ e * S * R = e := by
  obtain ⟨e', rfl⟩ : ∃ e' : Matrix (Fin d) (Fin d) F, e'.map F.subtype = e :=
    ⟨Matrix.of fun i j => ⟨e i j, hF i j⟩, by ext; rfl⟩
  let O : ValuationSubring F :=
    { carrier := {x | ‖(x : C)‖ ≤ 1}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, Subfield.coe_mul, norm_mul] at *
        calc ‖(a : C)‖ * ‖(b : C)‖ ≤ 1 * 1 := mul_le_mul ha hb (norm_nonneg _) zero_le_one
          _ = 1 := one_mul 1
      one_mem' := by simp
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, Subfield.coe_add] at *
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
      zero_mem' := by simp
      neg_mem' := fun {a} ha => by simpa using ha
      mem_or_inv_mem' := fun x => by
        rcases le_or_gt ‖(x : C)‖ 1 with h | h
        · exact Or.inl h
        · right
          change ‖((x⁻¹ : F) : C)‖ ≤ 1
          rw [Subfield.coe_inv, norm_inv]
          exact inv_le_one_of_one_le₀ h.le }
  have hinj : Function.Injective (F.subtype : F → C) := Subtype.val_injective
  have he' : e' * e' = e' := Matrix.map_injective hinj (by
    change (e' * e').map F.subtype = e'.map F.subtype
    rw [Matrix.map_mul, he])
  obtain ⟨r, R, S, hR, hS, hRS, hRe, heSR⟩ := exists_integral_factor_of_idempotent O d e' he'
  refine ⟨r, R.map F.subtype, S.map F.subtype, fun i j => ⟨(R i j).2, hR i j⟩,
    fun i j => ⟨(S i j).2, hS i j⟩, ?_, ?_, ?_⟩
  · rw [← Matrix.map_mul, hRS, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [← Matrix.map_mul, hRe]
  · rw [← Matrix.map_mul, ← Matrix.map_mul, heSR]

end GlobalTheory
end

section

universe u_1 u_2

namespace GlobalTheory.PermutationExistence

theorem exists_perm {G : Type u_1} {C : Type u_2} [Group G] [AddCommMonoid C]
    (H V : Subgroup G) (S : Finset G) (hS : ∀ s ∈ S, s ∈ H)
    (hT : ∀ h ∈ H, ∃! s : G, s ∈ S ∧ s⁻¹ * h ∈ V) (h : G) (hh : h ∈ H) :
    ∃ σ : G → G, (∀ s ∈ S, σ s ∈ S ∧ (σ s)⁻¹ * (h * s) ∈ V) ∧
      ∀ f : G → C, ∑ s ∈ S, f (σ s) = ∑ s ∈ S, f s := by
  classical
  have key : ∀ s ∈ S, ∃ s' : G, s' ∈ S ∧ s'⁻¹ * (h * s) ∈ V := fun s hs =>
    (hT (h * s) (H.mul_mem hh (hS s hs))).exists
  choose! σ hσS hσV using key
  refine ⟨σ, fun s hs => ⟨hσS s hs, hσV s hs⟩, fun f => ?_⟩

  have hinj : Set.InjOn σ S := by
    intro s₁ hs₁ s₂ hs₂ heq
    have h1 := hσV s₁ hs₁
    rw [heq] at h1
    have h12 : s₁⁻¹ * s₂ ∈ V := by
      have e : ((σ s₂)⁻¹ * (h * s₁))⁻¹ * ((σ s₂)⁻¹ * (h * s₂)) = s₁⁻¹ * s₂ := by group
      rw [← e]
      exact V.mul_mem (V.inv_mem h1) (hσV s₂ hs₂)
    obtain ⟨u, _, hu⟩ := hT s₂ (hS s₂ hs₂)
    have e1 : s₁ = u := hu s₁ ⟨hs₁, h12⟩
    have e2 : s₂ = u := hu s₂ ⟨hs₂, by rw [inv_mul_cancel]; exact V.one_mem⟩
    rw [e1, e2]
  have himg : S.image σ = S := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
      exact hσS s hs
    · rw [Finset.card_image_of_injOn hinj]
  calc ∑ s ∈ S, f (σ s) = ∑ x ∈ S.image σ, f x := (Finset.sum_image hinj).symm
    _ = ∑ s ∈ S, f s := by rw [himg]

theorem main {G : Type u_1} {C : Type u_2} [Group G] [NormedField C] [IsUltrametricDist C]
    (act : G →* C ≃+* C) (hn : ∀ (g : G) (y : C), ‖act g y‖ = ‖y‖)
    (H V : Subgroup G) (S : Finset G) (hS : ∀ s ∈ S, s ∈ H)
    (hT : ∀ h ∈ H, ∃! s : G, s ∈ S ∧ s⁻¹ * h ∈ V) (a b : C) (hb : ‖b‖ ≤ (1 : ℝ))
    (hV : ∀ g ∈ V, act g b = b) (ha : ∑ s ∈ S, act s b = a) (c : G → C)
    (hc : ∀ g ∈ H, ∀ h ∈ H, c (g * h) = c g + act g (c h)) (t ε : ℝ) (ht : (0 : ℝ) ≤ t)
    (hε : (0 : ℝ) ≤ ε) (hct : ∀ g ∈ H, ‖c g‖ ≤ t) (hcε : ∀ g ∈ H, g ∈ V → ‖c g‖ ≤ ε) :
    ∃ x : C, ‖x‖ ≤ t ∧ ∀ h ∈ H, ‖a * c h - (act h x - x)‖ ≤ ε := by
  classical
  refine ⟨-∑ s ∈ S, act s b * c s, ?_, ?_⟩
  · rw [norm_neg]
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg ht
    intro s hs
    rw [norm_mul, hn]
    calc ‖b‖ * ‖c s‖ ≤ 1 * t := mul_le_mul hb (hct s (hS s hs)) (norm_nonneg _) zero_le_one
      _ = t := one_mul t
  · intro h hh
    obtain ⟨σ, hσ, hsum⟩ := exists_perm (C := C) H V S hS hT h hh
    have hmul : ∀ (g k : G) (y : C), act (g * k) y = act g (act k y) := by
      intro g k y
      rw [map_mul]
      rfl

    have hterm : ∀ s ∈ S, act h (act s b * c s) = act (σ s) b * c (σ s)
        + act (σ s) (b * c ((σ s)⁻¹ * (h * s))) - act (σ s) b * c h := by
      intro s hs
      have hsH := hS s hs
      have hσH := hS (σ s) (hσ s hs).1
      have hvV := (hσ s hs).2
      have hhs : h * s = σ s * ((σ s)⁻¹ * (h * s)) := (mul_inv_cancel_left _ _).symm
      have hvH : (σ s)⁻¹ * (h * s) ∈ H := H.mul_mem (H.inv_mem hσH) (H.mul_mem hh hsH)
      have h1 : act h (act s b) = act (σ s) b := by
        rw [← hmul, hhs, hmul, hV _ hvV]
      have h2 : act h (c s) = c (σ s) + act (σ s) (c ((σ s)⁻¹ * (h * s))) - c h := by
        have e1 := hc h hh s hsH
        have e2 := hc (σ s) hσH _ hvH
        rw [← hhs] at e2
        linear_combination e2 - e1
      rw [map_mul, h1, h2, map_mul (act (σ s)) b (c ((σ s)⁻¹ * (h * s)))]
      ring
    have hsumA : ∑ s ∈ S, act (σ s) b = a := by
      rw [← ha]
      exact hsum (fun g => act g b)
    have hsumT : ∑ s ∈ S, act (σ s) b * c (σ s) = ∑ s ∈ S, act s b * c s :=
      hsum (fun g => act g b * c g)
    have hact : act h (-∑ s ∈ S, act s b * c s) = -(∑ s ∈ S, act s b * c s
        + ∑ s ∈ S, act (σ s) (b * c ((σ s)⁻¹ * (h * s))) - a * c h) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_neg, map_sum, Finset.sum_congr rfl hterm, Finset.sum_sub_distrib,
        Finset.sum_add_distrib, hsumT, ← Finset.sum_mul, hsumA]
    rw [hact]
    have hE : a * c h - (-(∑ s ∈ S, act s b * c s
        + ∑ s ∈ S, act (σ s) (b * c ((σ s)⁻¹ * (h * s))) - a * c h)
        - -∑ s ∈ S, act s b * c s) = ∑ s ∈ S, act (σ s) (b * c ((σ s)⁻¹ * (h * s))) := by
      ring
    rw [hE]
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hε
    intro s hs
    rw [hn, norm_mul]
    have hvH : (σ s)⁻¹ * (h * s) ∈ H :=
      H.mul_mem (H.inv_mem (hS _ (hσ s hs).1)) (H.mul_mem hh (hS s hs))
    calc ‖b‖ * ‖c ((σ s)⁻¹ * (h * s))‖ ≤ 1 * ε :=
          mul_le_mul hb (hcε _ hvH (hσ s hs).2) (norm_nonneg _) zero_le_one
      _ = ε := one_mul ε

end GlobalTheory.PermutationExistence
end

section

universe u_1

namespace GlobalTheory.PowerEqOneClose

theorem norm_pow_sub_one_le {K : Type u_1} [NormedField K] [IsUltrametricDist K] (u : K)
    (hu : ‖u‖ ≤ 1) (n : ℕ) : ‖u ^ n - 1‖ ≤ ‖u - 1‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : u ^ (n + 1) - 1 = (u ^ n - 1) * u + (u - 1) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ le_rfl)
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) hu).trans ih

theorem norm_geom_sum_sub_le {K : Type u_1} [NormedField K] [IsUltrametricDist K] (u : K)
    (hu : ‖u‖ ≤ 1) (n : ℕ) : ‖(∑ i ∈ Finset.range n, u ^ i) - (n : K)‖ ≤ ‖u - 1‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : (∑ i ∈ Finset.range (n + 1), u ^ i) - ((n + 1 : ℕ) : K)
        = ((∑ i ∈ Finset.range n, u ^ i) - (n : K)) + (u ^ n - 1) := by
      rw [Finset.sum_range_succ]; push_cast; ring
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le ih (norm_pow_sub_one_le u hu n))

theorem eq_one_of_pow_eq_one {K : Type u_1} [NormedField K] [IsUltrametricDist K] (m : ℕ)
    (hm : ‖(m : K)‖ = (1 : ℝ)) (u : K) (hu : u ^ m = (1 : K)) (h : ‖u - (1 : K)‖ < (1 : ℝ)) :
    u = (1 : K) := by
  have hu1 : ‖u‖ ≤ 1 := by
    have e : u = (u - 1) + 1 := by ring
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h.le norm_one.le)
  have hs := norm_geom_sum_sub_le u hu1 m
  have hg : (∑ i ∈ Finset.range m, u ^ i) * (u - 1) = 0 := by
    rw [geom_sum_mul, hu, sub_self]
  rcases mul_eq_zero.mp hg with h0 | h0
  · rw [h0, zero_sub, norm_neg, hm] at hs
    exact absurd h (not_lt.mpr hs)
  · exact sub_eq_zero.mp h0

end GlobalTheory.PowerEqOneClose
end

section

namespace GlobalTheory.PowerDifferenceNormInertiaEigenvalues

universe u_1

theorem norm_pow_sub_pow_le {C : Type u_1} [NormedField C] [IsUltrametricDist C] {x y : C}
    (hx : ‖x‖ ≤ (1 : ℝ)) (hy : ‖y‖ ≤ (1 : ℝ)) (n : ℕ) : ‖x ^ n - y ^ n‖ ≤ ‖x - y‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : x ^ (n + 1) - y ^ (n + 1) = x * (x ^ n - y ^ n) + y ^ n * (x - y) := by ring
    rw [h]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) hx).trans ih
    · rw [norm_mul, norm_pow]
      exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hy)

end GlobalTheory.PowerDifferenceNormInertiaEigenvalues
end

section

namespace GlobalTheory.UnitNormPowerSubOne

theorem norm_eq_one {C : Type} [NormedField C] [IsUltrametricDist C] (u : C)
    (h : ‖u - 1‖ < 1) : ‖u‖ = 1 := by
  apply le_antisymm
  · have h1 := IsUltrametricDist.norm_add_le_max (u - 1) (1 : C)
    rw [sub_add_cancel, norm_one] at h1
    exact h1.trans (max_le h.le le_rfl)
  · have h1 := IsUltrametricDist.norm_add_le_max u (-(u - 1))
    have e : u + -(u - 1) = 1 := by ring
    rw [e, norm_one, norm_neg] at h1
    rcases le_max_iff.mp h1 with h2 | h2
    · exact h2
    · exact absurd h (not_lt.mpr h2)

theorem norm_pow_sub_one_le {C : Type} [NormedField C] [IsUltrametricDist C] (u : C)
    (h : ‖u - 1‖ < 1) (n : ℕ) : ‖u ^ n - 1‖ ≤ ‖u - 1‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 := IsUltrametricDist.norm_add_le_max (u ^ n * (u - 1)) (u ^ n - 1)
    have e : u ^ n * (u - 1) + (u ^ n - 1) = u ^ (n + 1) - 1 := by ring
    rw [e, norm_mul, norm_pow, norm_eq_one u h, one_pow, one_mul] at h1
    exact h1.trans (max_le le_rfl ih)

theorem norm_zpow_sub_one_le {C : Type} [NormedField C] [IsUltrametricDist C] (u : C)
    (h : ‖u - 1‖ < 1) (i : ℤ) : ‖u ^ i - 1‖ ≤ ‖u - 1‖ := by
  have hn := norm_eq_one u h
  have hu : u ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hn
    exact zero_ne_one hn
  rcases Int.eq_nat_or_neg i with ⟨n, rfl | rfl⟩
  · rw [zpow_natCast]
    exact norm_pow_sub_one_le u h n
  · have hp : u ^ n ≠ 0 := pow_ne_zero n hu
    have e : u ^ (-(n : ℤ)) - 1 = -((u ^ n)⁻¹ * (u ^ n - 1)) := by
      rw [zpow_neg, zpow_natCast, mul_sub, inv_mul_cancel₀ hp, mul_one, neg_sub]
    rw [e, norm_neg, norm_mul, norm_inv, norm_pow, hn, one_pow, inv_one, one_mul]
    exact norm_pow_sub_one_le u h n

end GlobalTheory.UnitNormPowerSubOne
end

section

open Polynomial

namespace GlobalTheory

theorem additive_poly_taylor_coeff_sub_norm_le :
    ∀ (l : ℕ) [Fact l.Prime] (E : ℕ) (a : ℕ → ℂ_[l]) (W : ℂ_[l]), (∀ k, k ≤ E → ‖a k‖ ≤ 1) → ‖W‖ ≤ 1 →
      ∀ j : ℕ, 1 ≤ j → ‖(Polynomial.taylor W (∑ k ∈ Finset.range (E + 1), Polynomial.monomial (l ^ k) (a k) : Polynomial ℂ_[l])).coeff j - (∑ k ∈ Finset.range (E + 1), Polynomial.monomial (l ^ k) (a k) : Polynomial ℂ_[l]).coeff j‖ ≤ ‖(l : ℂ_[l])‖ := by
  intro l hl E a W ha hW j hj
  have hp : l.Prime := hl.out

  rw [map_sum, Polynomial.finsetSum_coeff, Polynomial.finsetSum_coeff, ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun k hk => ?_
  have hak : ‖a k‖ ≤ 1 := ha k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
  rw [Polynomial.taylor_monomial, ← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coeff_C_mul,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_add_C_pow, Polynomial.coeff_X_pow]
  rcases lt_trichotomy j (l ^ k) with h | h | h
  · have hne : j ≠ l ^ k := h.ne
    simp only [hne, if_false, mul_zero, sub_zero]
    obtain ⟨m, hm⟩ : l ∣ (l ^ k).choose j := hp.dvd_choose_pow (by omega) h.ne
    rw [hm, Nat.cast_mul, norm_mul, norm_mul, norm_mul]
    have h1 : ‖W ^ (l ^ k - j)‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hW
    have h2 : ‖(m : ℂ_[l])‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ m
    calc ‖a k‖ * (‖W ^ (l ^ k - j)‖ * (‖(l : ℂ_[l])‖ * ‖(m : ℂ_[l])‖))
        ≤ 1 * (1 * (‖(l : ℂ_[l])‖ * 1)) := by gcongr
      _ = ‖(l : ℂ_[l])‖ := by ring
  · subst h
    simp
  · have hne : j ≠ l ^ k := h.ne'
    simp only [hne, if_false, mul_zero, sub_zero, Nat.choose_eq_zero_of_lt h, Nat.cast_zero]
    simp

end GlobalTheory
end

section

namespace GlobalTheory.SingleStatement

theorem main : ∀ {p : ℕ} [inst : Fact (Nat.Prime p)] {ι : Type} (s : Finset ι) (g : ι → ℂ_[p]) {r : ℝ},
    (0 : ℝ) ≤ r → (∀ k ∈ s, ‖g k‖ ≤ r) → ‖∑ k ∈ s, g k‖ ≤ r := by
  intro p _ ι s g r hr hg
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hr
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have h1 : ‖g a‖ ≤ r := hg a (Finset.mem_insert_self a s)
    have h2 : ‖∑ k ∈ s, g k‖ ≤ r := ih (fun k hk => hg k (Finset.mem_insert_of_mem hk))
    exact (PadicComplex.isNonarchimedean p (g a) (∑ k ∈ s, g k)).trans (max_le h1 h2)

end GlobalTheory.SingleStatement
end

section

namespace GlobalTheory.TriangularDiagonal

theorem mul_diag_of_triangular :
    ∀ {p : ℕ} {κ : Fin p → ℤ}, Function.Injective κ → ∀ {M N : Matrix (Fin p) (Fin p) ℂ},
      (∀ (a b : Fin p), κ a < κ b → M a b = (0 : ℂ)) →
      (∀ (a b : Fin p), κ a < κ b → N a b = (0 : ℂ)) →
      ∀ (i : Fin p), (M * N) i i = M i i * N i i := by
  intro p κ hκ M N hM hN i
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i ?_ ?_
  · intro k _ hk
    rcases lt_trichotomy (κ i) (κ k) with h | h | h
    · rw [hM i k h, zero_mul]
    · exact absurd (hκ h).symm hk
    · rw [hN k i h, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

end GlobalTheory.TriangularDiagonal
end
