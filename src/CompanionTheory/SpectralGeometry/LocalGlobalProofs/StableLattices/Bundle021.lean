module

public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
public import Formalism.RealPlaceAnalysis.Bundle005
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

section

open Finset Equiv

noncomputable section

namespace GlobalTheory.CompanionTheory.CapelliBlocks

open Formalism.REAL CompanionTheory.D.DSIC

theorem qminor_equiv {A : Type} [Ring A] [Algebra ℂ A] {m n : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E)
    (τ : Fin m ≃ Fin n) (u : ℂ) : qminor E τ τ u = qdet E u := by
  obtain rfl : m = n := Fin.equiv_iff_eq.mp ⟨τ⟩
  have hr := qSkewRow A m m E id (τ : Fin m → Fin m) τ u
  have hc := qSkewCol A m m E hE id id τ u
  simp only [Function.id_comp] at hr hc
  rw [hr, hc, ← mul_assoc, ← Int.cast_mul, qdet]
  have : ((Perm.sign τ : ℤˣ) : ℤ) * (Perm.sign τ : ℤˣ) = 1 := by
    rw [← Units.val_mul, Int.units_mul_self, Units.val_one]
  rw [this, Int.cast_one, one_mul]

theorem qminor_sum {A : Type} [Ring A] [Algebra ℂ A] {n q p : ℕ} (E : Fin n → Fin n → A)
    (r : Fin q ⊕ Fin p → Fin n) (u : ℂ) :
    qminor E (r ∘ finSumFinEquiv.symm) (r ∘ finSumFinEquiv.symm) u =
      ∑ σ : Perm (Fin q ⊕ Fin p), ((Perm.sign σ : ℤ) : A) *
        ((List.ofFn fun k : Fin q => Tm E (u - (k : ℂ)) (r (σ (Sum.inl k))) (r (Sum.inl k))).prod *
         (List.ofFn fun k : Fin p => Tm E (u - (q : ℂ) - (k : ℂ)) (r (σ (Sum.inr k))) (r (Sum.inr k))).prod) := by
  rw [qminor, ← (finSumFinEquiv (m := q) (n := p)).permCongr.sum_comp]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Perm.sign_permCongr, List.ofFn_add, List.prod_append]
  congr 4
  · funext k
    have : (Fin.castLE (Nat.le_add_right q p) k) = Fin.castAdd p k := rfl
    simp [this]
  · funext k
    simp [sub_sub]

theorem prod_mem {V : Type} [AddCommGroup V] [Module ℂ V] (P : Submodule ℂ V) :
    ∀ l : List (Module.End ℂ V), (∀ T ∈ l, ∀ v ∈ P, T v ∈ P) → (∃ T ∈ l, ∀ v, T v ∈ P) → ∀ v, l.prod v ∈ P := by
  intro l
  induction l with
  | nil =>
    intro _ h _
    simp at h
  | cons T l ih =>
    intro h1 h2 v
    rw [List.prod_cons, Module.End.mul_apply]
    obtain ⟨S, hS, hS'⟩ := h2
    rcases List.mem_cons.mp hS with rfl | hS
    · exact hS' _
    · exact h1 T List.mem_cons_self _
        (ih (fun T hT => h1 T (List.mem_cons_of_mem _ hT)) ⟨S, hS, hS'⟩ v)

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

def pplus (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) : Submodule ℂ V where
  carrier := {v | ∃ w : NC ε → V, v = ∑ i : NC ε, E i.1.1 i.1.2 (w i)}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨w, rfl⟩ ⟨w', rfl⟩
    exact ⟨w + w', by simp [Finset.sum_add_distrib]⟩
  smul_mem' := by
    rintro c _ ⟨w, rfl⟩
    exact ⟨c • w, by simp [Finset.smul_sum]⟩

theorem mem_pplus (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) {a b : Fin n}
    (ha : ε a = true) (hb : ε b = false) (v : V) : E a b v ∈ pplus ε E := by
  classical
  refine ⟨Pi.single (⟨(a, b), ha, hb⟩ : NC ε) v, ?_⟩
  rw [Finset.sum_eq_single (⟨(a, b), ha, hb⟩ : NC ε)]
  · simp
  · intro i _ hi
    simp [Pi.single_eq_of_ne hi]
  · simp

theorem stab_pplus (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) {c d : Fin n}
    (hc : ε c = false) (hd : ε d = false) : ∀ v ∈ pplus ε E, E c d v ∈ pplus ε E := by
  rintro _ ⟨w, rfl⟩

  rw [map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨⟨a, b⟩, ha, hb⟩ := i
  dsimp only at ha hb ⊢
  generalize w _ = x
  have h := LinearMap.congr_fun (hE c d a b) x
  have hda : d ≠ a := by rintro rfl; simp [ha] at hd
  rw [if_neg hda, zero_sub, LinearMap.sub_apply, sub_eq_iff_eq_add, LinearMap.neg_apply,
    Module.End.mul_apply, Module.End.mul_apply] at h
  rw [h]
  refine Submodule.add_mem _ (Submodule.neg_mem _ ?_) (mem_pplus ε E ha hb _)
  split_ifs
  · exact mem_pplus ε E ha hd _
  · simp

theorem Tm_mem (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) {a b : Fin n}
    (ha : ε a = true) (hb : ε b = false) (u : ℂ) (v : V) : Tm E u a b v ∈ pplus ε E := by
  have hab : a ≠ b := by rintro rfl; simp [ha] at hb
  rw [Tm, if_neg hab, zero_add]
  exact mem_pplus ε E ha hb v

theorem Tm_stab (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) (a : Fin n) {b : Fin n}
    (hb : ε b = false) (u : ℂ) : ∀ v ∈ pplus ε E, Tm E u a b v ∈ pplus ε E := by
  intro v hv
  cases ha : ε a
  · rw [Tm, LinearMap.add_apply]
    refine Submodule.add_mem _ ?_ (stab_pplus ε E hE ha hb v hv)
    split_ifs
    · rw [Module.algebraMap_end_apply]
      exact Submodule.smul_mem _ _ hv
    · simp
  · exact Tm_mem ε E ha hb u v

theorem block_mem (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) {q p : ℕ}
    (r : Fin q ⊕ Fin p → Fin n) (hl : ∀ k, ε (r (Sum.inl k)) = false) (hr : ∀ k, ε (r (Sum.inr k)) = true)
    (u : ℂ) (v : V) :
    qminor E (r ∘ finSumFinEquiv.symm) (r ∘ finSumFinEquiv.symm) u v -
      (qminor E (r ∘ Sum.inl) (r ∘ Sum.inl) u * qminor E (r ∘ Sum.inr) (r ∘ Sum.inr) (u - (q : ℂ))) v ∈
        pplus ε E := by
  classical
  rw [qminor_sum]
  set f : Perm (Fin q ⊕ Fin p) → Module.End ℂ V := fun σ => ((Perm.sign σ : ℤ) : Module.End ℂ V) *
        ((List.ofFn fun k : Fin q => Tm E (u - (k : ℂ)) (r (σ (Sum.inl k))) (r (Sum.inl k))).prod *
         (List.ofFn fun k : Fin p => Tm E (u - (q : ℂ) - (k : ℂ)) (r (σ (Sum.inr k))) (r (Sum.inr k))).prod)
    with hf
  set s : Finset (Perm (Fin q ⊕ Fin p)) :=
    univ.image fun σ : Perm (Fin q) × Perm (Fin p) => Perm.sumCongrHom _ _ σ with hs
  have h1 : qminor E (r ∘ Sum.inl) (r ∘ Sum.inl) u * qminor E (r ∘ Sum.inr) (r ∘ Sum.inr) (u - (q : ℂ)) =
      ∑ σ ∈ s, f σ := by
    rw [hs, Finset.sum_image (fun x _ y _ h => Perm.sumCongrHom_injective h), qminor, qminor,
      Finset.sum_mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => ?_
    simp only [hf, Perm.sumCongrHom_apply, Perm.sign_sumCongr, Units.val_mul, Int.cast_mul,
      Perm.sumCongr_apply, Sum.map_inl, Sum.map_inr, Function.comp_apply, mul_assoc]
    congr 1
    rw [← mul_assoc, ← (Int.cast_commute _ _).eq, mul_assoc]
  rw [h1, ← Finset.sum_add_sum_compl s, LinearMap.add_apply, add_sub_cancel_left, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun σ hσ => ?_
  have h2 : ∃ k j, σ (Sum.inl k) = Sum.inr j := by
    by_contra hcon
    push Not at hcon
    apply Finset.mem_compl.mp hσ
    have : σ ∈ (Perm.sumCongrHom (Fin q) (Fin p)).range := by
      apply Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl
      rintro _ ⟨k, rfl⟩
      cases h : σ (Sum.inl k) with
      | inl j => exact ⟨j, rfl⟩
      | inr j => exact absurd h (hcon k j)
    obtain ⟨τ, hτ⟩ := this
    exact Finset.mem_image.mpr ⟨τ, Finset.mem_univ _, hτ⟩
  obtain ⟨k, j, hkj⟩ := h2
  simp only [hf, Module.End.mul_apply, Module.End.intCast_apply]
  refine Submodule.smul_of_tower_mem _ _ (prod_mem _ _ ?_ ?_ _)
  · intro T hT
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hT
    exact Tm_stab ε E hE _ (hl i) _
  · refine ⟨_, List.mem_ofFn.mpr ⟨k, rfl⟩, fun v => Tm_mem ε E ?_ (hl k) _ v⟩
    rw [hkj]
    exact hr j

theorem blk_val (ε : Fin n → Bool) (s : Bool) (k : Fin (nb ε s)) : ε (blk ε s k) = s := by
  have := Finset.orderEmbOfFin_mem (univ.filter fun a => ε a = s) rfl k
  exact (Finset.mem_filter.mp this).2

theorem blk_bijective (ε : Fin n → Bool) : Function.Bijective (Sum.elim (blk ε false) (blk ε true)) := by
  have hinj : ∀ s, Function.Injective (blk ε s) := fun s =>
    ((univ.filter fun a => ε a = s).orderEmbOfFin rfl).injective
  have hsur : ∀ a, ∃ k, blk ε (ε a) k = a := fun a => by
    have : a ∈ Set.range ((univ.filter fun b => ε b = ε a).orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]
      simp
    exact this
  constructor
  · refine Function.Injective.sumElim (hinj false) (hinj true) fun a b h => ?_
    have h1 := blk_val ε false a
    rw [h, blk_val ε true b] at h1
    exact absurd h1 (by simp)
  · intro a
    have h := hsur a
    cases ha : ε a
    · rw [ha] at h
      obtain ⟨k, hk⟩ := h
      exact ⟨Sum.inl k, hk⟩
    · rw [ha] at h
      obtain ⟨k, hk⟩ := h
      exact ⟨Sum.inr k, hk⟩

theorem co0 : CompanionTheory.D.DSIC.CapelliDeterminantBlockProduct := by
  intro n ε V _ _ E hE u v
  have h := block_mem ε E hE (Sum.elim (blk ε false) (blk ε true)) (blk_val ε false) (blk_val ε true) u v
  have h2 := qminor_equiv E hE (finSumFinEquiv.symm.trans (Equiv.ofBijective _ (blk_bijective ε))) u
  rw [← h2]
  exact h

end GlobalTheory.CompanionTheory.CapelliBlocks
end
end

section

open Matrix Finset Filter Topology Set

noncomputable section

namespace GlobalTheory.CompanionTheory.DSStabLink

open PI.UpqRep CompanionTheory.D.DSIC

theorem flow_mem {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (W : Submodule ℂ H)
    [FiniteDimensional ℂ W] (T : ℝ → (H →L[ℂ] H)) (h0 : ∀ v, T 0 v = v)
    (hadd : ∀ s t v, T (s + t) v = T s (T t v)) (hiso : ∀ t v, ‖T t v‖ = ‖v‖)
    (hder : ∀ w ∈ W, ∃ z ∈ W, HasDerivAt (fun t => T t w) z 0) (u : H) (hu : u ∈ W) :
    T 1 u ∈ W := by
  set Q : H →L[ℂ] H := Wᗮ.starProjection with hQ
  have hQW : ∀ w ∈ W, Q w = 0 := fun w hw => Submodule.starProjection_orthogonal_apply_eq_zero hw
  have hQs : ∀ x, x - Q x ∈ W := fun x => by
    have := Submodule.sub_starProjection_mem_orthogonal (K := Wᗮ) x
    rwa [Submodule.orthogonal_orthogonal] at this
  have hQn : ∀ x, ‖Q x‖ ≤ ‖x‖ := fun x => Submodule.norm_starProjection_apply_le _ x
  have hcont : Continuous fun t => T t u := by
    rw [continuous_iff_continuousAt]
    intro t
    obtain ⟨z, -, hz⟩ := hder u hu
    have h1 : ContinuousAt (fun s : ℝ => T (s - t) u) t := by
      have h2 : ContinuousAt (fun s : ℝ => s - t) t := by fun_prop
      exact ContinuousAt.comp_of_eq (g := fun t => T t u) hz.continuousAt h2 (by simp)
    have h3 : ContinuousAt (fun s : ℝ => T t (T (s - t) u)) t :=
      (T t).continuous.continuousAt.comp h1
    convert h3 using 2 with s
    rw [← hadd]; simp
  have key : ∀ ⦃x⦄, x ∈ Icc (0 : ℝ) 1 → ‖Q (T x u)‖ ≤ 0 := by
    refine image_le_of_liminf_slope_right_le_deriv_boundary (f := fun t => ‖Q (T t u)‖)
      (B := fun _ => 0) (B' := fun _ => 0) ?_ ?_ continuousOn_const
      (fun x _ => hasDerivWithinAt_const _ _ _) ?_
    · exact ((Q.continuous.comp hcont).norm).continuousOn
    · simp [h0, hQW u hu]
    · intro x _ r hr
      set w := T x u - Q (T x u) with hw
      obtain ⟨z, hzW, hz⟩ := hder w (hQs _)
      have hg : HasDerivAt (fun t => Q (T t w)) 0 0 := by
        have := (Q.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hz
        simpa [hQW z hzW, Function.comp_def] using this
      have hg2 : HasDerivAt (fun s : ℝ => Q (T (s - x) w)) 0 x := by
        have h2 : HasDerivAt (fun s : ℝ => s - x) 1 x := (hasDerivAt_id x).sub_const x
        have := HasDerivAt.scomp_of_eq (g₁ := fun t => Q (T t w)) x hg h2 (by simp)
        simpa [Function.comp_def] using this
      have hsl := (hasDerivAt_iff_tendsto_slope.1 hg2).norm
      rw [norm_zero] at hsl
      have hev : ∀ᶠ s in 𝓝[>] x, ‖slope (fun s : ℝ => Q (T (s - x) w)) x s‖ < r :=
        (hsl.eventually (gt_mem_nhds hr)).filter_mono (nhdsWithin_mono _ fun s hs => ne_of_gt hs)
      refine (hev.and self_mem_nhdsWithin).frequently.mono ?_
      rintro s ⟨hs, hsx⟩
      have hpos : 0 < s - x := sub_pos.2 hsx
      refine lt_of_le_of_lt ?_ hs
      rw [slope_def_field, slope_def_module, norm_smul, sub_self, h0, hQW w (hQs _), sub_zero,
        Real.norm_eq_abs, abs_of_pos (inv_pos.2 hpos), div_eq_inv_mul]
      refine mul_le_mul_of_nonneg_left ?_ (inv_pos.2 hpos).le
      have e : Q (T s u) = Q (T (s - x) w) + Q (T (s - x) (Q (T x u))) := by
        rw [← map_add (f := _), ← map_add (f := _), hw, sub_add_cancel, ← hadd, sub_add_cancel]
      have e2 : ‖Q (T (s - x) (Q (T x u)))‖ ≤ ‖Q (T x u)‖ := (hQn _).trans (hiso _ _).le
      have e3 := norm_add_le (Q (T (s - x) w)) (Q (T (s - x) (Q (T x u))))
      rw [← e] at e3
      linarith
  have h1 := norm_le_zero_iff.1 (key (x := 1) ⟨zero_le_one, le_rfl⟩)
  simpa [h1] using hQs (T 1 u)

theorem deriv_mem {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (W : Submodule ℂ H)
    [FiniteDimensional ℂ W] (c : ℝ → H) (z : H) (hc : ∀ t, c t ∈ W) (hz : HasDerivAt c z 0) :
    z ∈ W := by
  set Q : H →L[ℂ] H := Wᗮ.starProjection with hQ
  have hQW : ∀ w ∈ W, Q w = 0 := fun w hw => Submodule.starProjection_orthogonal_apply_eq_zero hw
  have hQs : ∀ x, x - Q x ∈ W := fun x => by
    have := Submodule.sub_starProjection_mem_orthogonal (K := Wᗮ) x
    rwa [Submodule.orthogonal_orthogonal] at this
  have h1 : HasDerivAt (fun t => Q (c t)) (Q z) 0 :=
    (Q.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hz
  have h2 : (fun t => Q (c t)) = fun _ => 0 := funext fun t => hQW _ (hc t)
  rw [h2] at h1
  have h3 : Q z = 0 := h1.unique (hasDerivAt_const _ _)
  simpa [h3] using hQs z

variable {n : ℕ}

theorem inK_iff (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) :
    inK ε X ↔ (∀ c d, ε c ≠ ε d → X c d = 0) ∧ ∀ c d, star (X d c) = -X c d := by
  unfold inK inG Jm
  simp only [← Matrix.ext_iff, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.conjTranspose_apply, Matrix.zero_apply]
  constructor
  · rintro ⟨h1, h2⟩
    have h3 : ∀ c d, ε c ≠ ε d → X c d = 0 := by
      intro c d h
      have := h2 c d
      cases hc : ε c <;> cases hd : ε d <;> simp [hc, hd] at h this <;>
        first | linear_combination this / 2 | linear_combination -this / 2
    refine ⟨h3, fun c d => ?_⟩
    have := h1 c d
    by_cases h : ε c = ε d
    · cases hc : ε c <;> cases hd : ε d <;> simp [hc, hd] at h this ⊢ <;>
        first | linear_combination this | linear_combination -this
    · simp [h3 c d h, h3 d c (Ne.symm h)]
  · rintro ⟨h1, h2⟩
    constructor
    · intro c d
      by_cases h : ε c = ε d
      · rw [h2, h]; ring
      · simp [h1 c d h, h1 d c (Ne.symm h)]
    · intro c d
      by_cases h : ε c = ε d
      · rw [h]; ring
      · simp [h1 c d h]

theorem inK_smul (ε : Fin n → Bool) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (t : ℝ) :
    inK ε ((t : ℂ) • X) := by
  rw [inK_iff] at hX ⊢
  refine ⟨fun c d h => by simp [hX.1 c d h], fun c d => ?_⟩
  have := hX.2 c d
  simp only [Matrix.smul_apply, smul_eq_mul, star_mul', this]
  simp

theorem exp_mem_K (ε : Fin n → Bool) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ Kset ε :=
  (Formalism.REAL.maximal_compact_facts n ε).2.2.2.1 _ (inK_smul ε hX t)

theorem exp_mem_UJ (ε : Fin n → Bool) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ UJset ε :=
  Formalism.REAL.exp_indefinite_unitary_holds n ε X hX t

theorem stabLink : KExp → StabLink := by
  intro hK n ε H _ _ σ S E hσ hS U hU
  constructor
  · intro hst g hg v hv
    obtain ⟨X, hX, rfl⟩ := hK n ε g hg
    have := flow_mem (U.map S.subtype) (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)))
      ?_ ?_ ?_ ?_ v hv
    · simpa using this
    · intro v
      simp [hσ.1.1]
    · intro s t v
      have hc : Commute ((s : ℂ) • X) ((t : ℂ) • X) := ((Commute.refl X).smul_left _).smul_right _
      simp only [Complex.ofReal_add, add_smul]
      rw [Matrix.exp_add_of_commute _ _ hc,
        hσ.1.2 _ (exp_mem_UJ ε hX.1 s) _ (exp_mem_UJ ε hX.1 t)]
      rfl
    · intro t v
      exact hσ.2.1 _ (exp_mem_UJ ε hX.1 t) v
    · rintro _ ⟨w, hw, rfl⟩
      refine ⟨_, ?_, hS.real X hX.1 w⟩
      refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
      by_cases h : ε a = ε b
      · exact Submodule.smul_mem _ _ ⟨_, hst a b h w hw, rfl⟩
      · simp [((inK_iff ε X).1 hX).1 a b h]
  · intro hst a b hab v hv
    have hL : ∀ X, inK ε X → ∑ c, ∑ d, X c d • (E c d v : H) ∈ U.map S.subtype := fun X hX =>
      deriv_mem _ _ _ (fun t => hst _ (exp_mem_K ε hX t) _ ⟨v, hv, rfl⟩) (hS.real X hX.1 v)
    have hs : ∀ (p q : Fin n) (z : ℂ),
        ∑ c, ∑ d, (Matrix.single p q z) c d • (E c d v : H) = z • (E p q v : H) := by
      intro p q z
      simp [Matrix.single_apply, ite_and]
    have hoff : ∀ (p q : Fin n) (z : ℂ), ε p = ε q → ∀ c d, ε c ≠ ε d →
        Matrix.single p q z c d = 0 := by
      intro p q z h c d hcd
      rw [Matrix.single_apply, if_neg]
      rintro ⟨rfl, rfl⟩
      exact hcd h
    have hZ : ∀ z : ℂ, z • (E a b v : H) - star z • (E b a v : H) ∈ U.map S.subtype := by
      intro z
      have hin : inK ε (Matrix.single a b z - Matrix.single b a (star z)) := by
        rw [inK_iff]
        refine ⟨fun c d h => by simp [hoff a b z hab c d h, hoff b a _ hab.symm c d h], fun c d => ?_⟩
        simp only [Matrix.sub_apply, Matrix.single_apply, star_sub, apply_ite star, star_star,
          star_zero, neg_sub, and_comm]
      have := hL _ hin
      simpa only [Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib, hs] using this
    have h1 := hZ 1
    have h2 := hZ Complex.I
    have h3 := Submodule.add_mem _ (Submodule.smul_mem _ (1 / 2 : ℂ) h1)
      (Submodule.smul_mem _ (-Complex.I / 2 : ℂ) h2)
    have e : (1 / 2 : ℂ) • ((1 : ℂ) • (E a b v : H) - star (1 : ℂ) • (E b a v : H)) +
        (-Complex.I / 2 : ℂ) • (Complex.I • (E a b v : H) - star Complex.I • (E b a v : H)) =
        (E a b v : H) := by
      simp only [star_one, Complex.star_def, Complex.conj_I]
      match_scalars
      · linear_combination (-1 / 2 : ℂ) * Complex.I_mul_I
      · linear_combination (-1 / 2 : ℂ) * Complex.I_mul_I
    rw [e] at h3
    obtain ⟨y, hy, hye⟩ := h3
    have : y = E a b v := Subtype.ext hye
    exact this ▸ hy

end GlobalTheory.CompanionTheory.DSStabLink
end
end
