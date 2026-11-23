module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.Int.ConditionallyCompleteOrder
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Notation
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Block
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
public import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Insert
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Data.Matrix.Basis

@[expose] public section

section

noncomputable def UpperTheory.Reformulated.B.CardinalityOfBand.band :
    (m : Nat) → Nat → Nat → Fin m → Bool :=
    fun (m a b : Nat) (i : Fin m) ↦
      @Decidable.decide (And (@LE.le Nat instLENat a (@Fin.val m i)) (@LT.lt Nat instLTNat (@Fin.val m i) b))
        (@instDecidableAnd (@LE.le Nat instLENat a (@Fin.val m i)) (@LT.lt Nat instLTNat (@Fin.val m i) b)
          (a.decLe (@Fin.val m i)) ((@Fin.val m i).decLt b))

theorem UpperTheory.Reformulated.B.CardinalityOfBand.card_band :
    ∀ (m a b : Nat),
      @LE.le Nat instLENat b m →
        @Eq Nat (@Finset.card (Fin m) {i : Fin m | @Eq Bool (UpperTheory.Reformulated.B.CardinalityOfBand.band m a b i) Bool.true})
          (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) b a) := by
  intro m a b hb
  rw [← Nat.card_Ico a b, ← Finset.card_map Fin.valEmbedding]
  congr 1
  ext x
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
    Finset.mem_Ico, UpperTheory.Reformulated.B.CardinalityOfBand.band, decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact hi
  · intro hx
    exact ⟨⟨x, lt_of_lt_of_le hx.2 hb⟩, hx, rfl⟩
end

section

noncomputable def UpperTheory.Reformulated.B.Qk46.colH :
    {n : Nat} → (Fin n → Int) → Int → Nat :=
    fun {n : Nat} (mu : Fin n → Int) (c : Int) ↦ @Finset.card (Fin n) {m : Fin n | @LE.le Int Int.instLEInt c (mu m)}

theorem UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH :
    ∀ {r : Nat} {μ : Fin r → Int},
      @Antitone (Fin r) Int (@PartialOrder.toPreorder (Fin r) (@Fin.instPartialOrder r))
          (@PartialOrder.toPreorder Int
            (@ConditionallyCompletePartialOrderSup.toPartialOrder Int
              (@ConditionallyCompletePartialOrder.toConditionallyCompletePartialOrderSup Int
                (@ConditionallyCompleteLattice.toConditionallyCompletePartialOrder Int
                  (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice Int
                    Int.instConditionallyCompleteLinearOrder)))))
          μ →
        ∀ (c : Int) (m : Fin r),
          Iff (@LE.le Int Int.instLEInt c (μ m)) (@LT.lt Nat instLTNat (@Fin.val r m) (@UpperTheory.Reformulated.B.Qk46.colH r μ c)) := by
  intro r μ h c m
  unfold UpperTheory.Reformulated.B.Qk46.colH
  exact (Tuple.lt_card_ge_iff_apply_ge_of_antitone h).symm
end

section

theorem UpperTheory.Reformulated.B.Rc5.exists_reps :
    ∀ {α : Type} (r : α → α → Prop),
    (∀ (a b : α), r a b → r b a) →
      (∀ (a b c : α), r a b → r b c → r a c) →
        ∀ (t : Finset α), ∃ C ⊆ t, (∀ a ∈ C, ∀ b ∈ C, r a b → a = b) ∧ ∀ x ∈ t, x ∈ C ∨ ∃ c ∈ C, r x c := by
  intro α r hs _ t
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨∅, Finset.Subset.refl _, by simp, by simp⟩
  | insert y s _ ih =>
    obtain ⟨C, hC, h1, h2⟩ := ih
    by_cases h : ∃ c ∈ C, r y c
    · refine ⟨C, hC.trans (Finset.subset_insert _ _), h1, ?_⟩
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact Or.inr h
      · exact h2 x hx
    · refine ⟨insert y C, Finset.insert_subset_insert _ hC, ?_, ?_⟩
      · intro a ha b hb hab
        rcases Finset.mem_insert.1 ha with ha | ha
        · rcases Finset.mem_insert.1 hb with hb | hb
          · rw [ha, hb]
          · exact absurd ⟨b, hb, ha ▸ hab⟩ h
        · rcases Finset.mem_insert.1 hb with hb | hb
          · exact absurd ⟨a, ha, hb ▸ hs a b hab⟩ h
          · exact h1 a ha b hb hab
      · intro x hx
        rcases Finset.mem_insert.1 hx with hx | hx
        · exact Or.inl (Finset.mem_insert.2 (Or.inl hx))
        · rcases h2 x hx with h3 | ⟨c, hc, h3⟩
          · exact Or.inl (Finset.mem_insert_of_mem h3)
          · exact Or.inr ⟨c, Finset.mem_insert_of_mem hc, h3⟩
end

section

theorem UpperTheory.Reformulated.B.Qh68.reps.{u_1} :
    ∀ {α : Type u_1} (r : α → α → Prop),
    Equivalence r → ∀ (A : Finset α), ∃ T ⊆ A, (∀ t ∈ T, ∀ t' ∈ T, r t t' → t = t') ∧ ∀ a ∈ A, ∃ t ∈ T, r a t := by
  intro α r hr A
  classical
  induction A using Finset.induction_on with
  | empty => exact ⟨∅, Finset.Subset.refl _, by simp, by simp⟩
  | insert a s _ ih =>
    obtain ⟨T, hTs, hinj, hcov⟩ := ih
    by_cases h : ∃ t ∈ T, r a t
    · refine ⟨T, hTs.trans (Finset.subset_insert a s), hinj, ?_⟩
      intro b hb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact h
      · exact hcov b hb
    · refine ⟨insert a T, Finset.insert_subset_insert a hTs, ?_, ?_⟩
      · intro t ht t' ht' htt
        rcases Finset.mem_insert.mp ht with h1 | h1
        · rcases Finset.mem_insert.mp ht' with h2 | h2
          · rw [h1, h2]
          · exact absurd ⟨t', h2, h1 ▸ htt⟩ h
        · rcases Finset.mem_insert.mp ht' with h2 | h2
          · exact absurd ⟨t, h1, h2 ▸ hr.symm htt⟩ h
          · exact hinj t h1 t' h2 htt
      · intro b hb
        rcases Finset.mem_insert.mp hb with h1 | h1
        · exact ⟨b, Finset.mem_insert.mpr (Or.inl h1), hr.refl b⟩
        · obtain ⟨t, ht, hbt⟩ := hcov b h1
          exact ⟨t, Finset.mem_insert_of_mem ht, hbt⟩
end

section

theorem UpperTheory.Reformulated.B.Qm7.exists_common_multiple.{u_2} :
    ∀ {ι : Type u_2} (s : Finset ι)
    (P : ι → ℕ → Prop),
    (∀ (i : ι) (a b : ℕ), P i a → a ∣ b → P i b) →
      (∀ i ∈ s, ∃ (a : ℕ), (0 : ℕ) < a ∧ P i a) → ∃ (d : ℕ), (0 : ℕ) < d ∧ ∀ i ∈ s, P i d := by
  intro ι s P hP h
  choose! a ha using h
  exact ⟨∏ i ∈ s, a i, Finset.prod_pos fun i hi => (ha i hi).1,
    fun i hi => hP i _ _ (ha i hi).2 (Finset.dvd_prod_of_mem a hi)⟩
end

section

theorem UpperTheory.Reformulated.B.Qf39.ev_decomp :
    ∀ {O σ : Type} [inst : CommRing O] [inst_1 : Fintype σ]
    (f : MvPowerSeries σ O),
    ∃ (h : σ → MvPowerSeries σ O),
      f =
          (MvPowerSeries.C : O → MvPowerSeries σ O) ((MvPowerSeries.constantCoeff : MvPowerSeries σ O → O) f) +
            ∑ i : σ, MvPowerSeries.X i * h i ∧
        ∀ (i : σ),
          (MvPowerSeries.constantCoeff : MvPowerSeries σ O → O) (h i) =
            (MvPowerSeries.coeff fun₀ | i => (1 : ℕ) : MvPowerSeries σ O → O) f := by
  intro O σ _ _ f
  classical
  have key : ∀ m : σ →₀ ℕ, ∃ o : Option σ,
      (m ≠ 0 → ∃ j, o = some j) ∧ ∀ j, o = some j → m j ≠ 0 := by
    intro m
    by_cases hm : m = 0
    · exact ⟨none, fun h => (h hm).elim, fun j hj => by cases hj⟩
    · obtain ⟨j, hj⟩ := Finsupp.ne_iff.1 hm
      refine ⟨some j, fun _ => ⟨j, rfl⟩, fun k hk => ?_⟩
      cases hk
      simpa using hj
  choose c hc₁ hc₂ using key
  let h : σ → MvPowerSeries σ O := fun i m =>
    if c (m + Finsupp.single i 1) = some i then
      MvPowerSeries.coeff (m + Finsupp.single i 1) f else 0
  have hh : ∀ i m, MvPowerSeries.coeff m (h i) =
      if c (m + Finsupp.single i 1) = some i then
        MvPowerSeries.coeff (m + Finsupp.single i 1) f else 0 := fun _ _ => rfl
  have hX : ∀ i m, MvPowerSeries.coeff m (MvPowerSeries.X i * h i) =
      if c m = some i then MvPowerSeries.coeff m f else 0 := by
    intro i m
    rw [MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul, one_mul]
    by_cases hle : Finsupp.single i 1 ≤ m
    · rw [if_pos hle, hh, tsub_add_cancel_of_le hle]
    · rw [if_neg hle, if_neg]
      intro hi
      exact hle (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 (hc₂ m i hi)))
  refine ⟨h, ?_, fun i => ?_⟩
  · ext m

    rw [map_add (f := _), map_sum, MvPowerSeries.coeff_C]
    simp only [hX]
    by_cases hm : m = 0
    · subst hm
      have : ∀ i, ¬ c 0 = some i := fun i hi => hc₂ 0 i hi rfl
      simp [this]
    · obtain ⟨j, hj⟩ := hc₁ m hm
      simp [hm, hj]
  · have hne : (Finsupp.single i 1 : σ →₀ ℕ) ≠ 0 := by simp
    obtain ⟨j, hj⟩ := hc₁ _ hne
    have hji : j = i := by
      by_contra hji
      exact hc₂ _ j hj (Finsupp.single_eq_of_ne hji)
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hh, zero_add, if_pos (hji ▸ hj)]
end

section

namespace DegreeOneCoeffSubstitution
open MvPowerSeries Finsupp

private lemma deg_one {σ : Type} [DecidableEq σ] (d : σ →₀ ℕ) (h : d.degree = 1) :
    ∃ s, d = Finsupp.single s 1 := by
  have hd : d ≠ 0 := by rintro rfl; simp at h
  obtain ⟨s, hs⟩ := Finsupp.support_nonempty_iff.mpr hd
  refine ⟨s, ?_⟩
  have hsum : d s + ∑ i ∈ d.support.erase s, d i = 1 := by
    rw [Finset.add_sum_erase _ _ hs, ← degree_apply, h]
  have hs0 : d s ≠ 0 := Finsupp.mem_support_iff.mp hs
  have hds : d s = 1 := by omega
  have hrest : ∑ i ∈ d.support.erase s, d i = 0 := by omega
  rw [Finset.sum_eq_zero_iff] at hrest
  ext i
  by_cases his : i = s
  · subst his; simp [hds]
  · rw [Finsupp.single_apply, if_neg (Ne.symm his)]
    by_cases hi : i ∈ d.support
    · exact hrest i (Finset.mem_erase.mpr ⟨his, hi⟩)
    · exact Finsupp.notMem_support_iff.mp hi

end DegreeOneCoeffSubstitution

open MvPowerSeries Finsupp in
theorem UpperTheory.Reformulated.B.LinearTermOfSubstitution.main :
    ∀ {S : Type}
    [inst : CommRing S] {σ τ : Type} [inst_1 : Fintype σ] [DecidableEq σ] [DecidableEq τ] (a : σ → MvPowerSeries τ S),
    (∀ (s : σ), (MvPowerSeries.constantCoeff : MvPowerSeries τ S → S) (a s) = (0 : S)) →
      ∀ (f : MvPowerSeries σ S) (t : τ),
        (MvPowerSeries.coeff fun₀ | t => (1 : ℕ) : MvPowerSeries τ S → S) (MvPowerSeries.subst a f) =
          ∑ s : σ,
            (MvPowerSeries.coeff fun₀ | s => (1 : ℕ) : MvPowerSeries σ S → S) f *
              (MvPowerSeries.coeff fun₀ | t => (1 : ℕ) : MvPowerSeries τ S → S) (a s) := by
  intro S _ σ τ _ _ _ a ha f t
  have hS : HasSubst a := hasSubst_of_constantCoeff_zero ha
  rw [coeff_subst hS]
  have key : ∀ d : σ →₀ ℕ, d ∉ Finset.univ.image (fun s => Finsupp.single s 1) →
      coeff (Finsupp.single t 1) (d.prod fun s e => a s ^ e) = 0 := by
    intro d hd
    by_cases h0 : d = 0
    · subst h0
      simp [coeff_one]
    have h1 : d.degree ≠ 1 := by
      intro h
      obtain ⟨s, rfl⟩ := DegreeOneCoeffSubstitution.deg_one d h
      exact hd (by simp)
    have h2 : 2 ≤ d.degree := by
      have : d.degree ≠ 0 := fun h => h0 ((degree_eq_zero_iff d).mp h)
      omega
    unfold Finsupp.prod
    apply coeff_of_lt_order
    rw [Finsupp.degree_single]
    refine lt_of_lt_of_le ?_ (le_order_prod _ _)
    calc ((1 : ℕ) : ℕ∞) < 2 := by norm_num
      _ ≤ ((d.degree : ℕ) : ℕ∞) := by exact_mod_cast h2
      _ = ∑ i ∈ d.support, ((d i : ℕ) : ℕ∞) := by rw [degree_apply]; push_cast; rfl
      _ ≤ ∑ i ∈ d.support, (a i ^ d i).order :=
          Finset.sum_le_sum fun i _ => le_order_pow_of_constantCoeff_eq_zero _ (ha i)
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.univ.image (fun s => Finsupp.single s 1)) ?_]
  · rw [Finset.sum_image (fun x _ y _ h => Finsupp.single_left_injective one_ne_zero h)]
    apply Finset.sum_congr rfl
    intro s _
    simp [Finsupp.prod_single_index, smul_eq_mul]
  · intro d hd
    by_contra h
    apply hd
    simp only
    rw [key d (by simpa using h), smul_zero]
end

section

namespace UpperTheory.Reformulated.B.Qi38

noncomputable def Irr : {R : Type} →
  [inst : CommRing R] →
    {H : Type} →
      [inst_1 : Group H] → {n : Type} → [inst_2 : Fintype n] → [inst_3 : DecidableEq n] → (H →* Matrix n n R) → Prop :=
  fun {R} [CommRing R] {H} [Group H] {n} [Fintype n] [DecidableEq n] r => Submodule.span R (Set.range ⇑r) = ⊤

@[reducible] noncomputable def modFun : {O M ι : Type} →
  [inst : CommRing O] → [inst_1 : AddCommGroup M] → [Module O M] → Module O (ι → M) :=
  fun {O M ι} [CommRing O] [AddCommGroup M] [Module O M] => Pi.Function.module ι O M

attribute [local instance] modFun

noncomputable def mapRep : {R R' : Type} →
  [inst : CommRing R] →
    [inst_1 : CommRing R'] →
      {H : Type} →
        [inst_2 : Group H] →
          {n : Type} →
            [inst_3 : Fintype n] → [inst_4 : DecidableEq n] → (R →+* R') → (H →* Matrix n n R) → H →* Matrix n n R' :=
  fun {R R'} [CommRing R] [CommRing R'] {H} [Group H] {n} [Fintype n] [DecidableEq n] f r => f.mapMatrix.toMonoidHom.comp r

private theorem aux {Γ E E' : Type} [Field E] [Field E'] (f : E →+* E') {n : Nat}
    (r : Γ → Matrix (Fin n) (Fin n) E) (hr : Submodule.span E (Set.range r) = ⊤)
    (N : Submodule E' (Fin n → E'))
    (hN : ∀ g v, v ∈ N → ((r g).map f).mulVec v ∈ N) : N = ⊥ ∨ N = ⊤ := by
  have key : ∀ A : Matrix (Fin n) (Fin n) E, ∀ v ∈ N, (A.map f).mulVec v ∈ N := by
    intro A v hv
    have hA : A ∈ Submodule.span E (Set.range r) := by rw [hr]; exact Submodule.mem_top
    induction hA using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact hN g v hv
    | zero =>
      rw [Matrix.map_zero _ (map_zero f), Matrix.zero_mulVec]
      exact N.zero_mem
    | add x y _ _ hx hy =>
      rw [Matrix.map_add _ (map_add f), Matrix.add_mulVec]
      exact N.add_mem hx hy
    | smul a x _ hx =>
      have h : (a • x).map f = f a • x.map f := by
        ext i j
        simp
      rw [h, Matrix.smul_mulVec]
      exact N.smul_mem _ hx
  refine or_iff_not_imp_left.2 fun hne => ?_
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff N).1 hne
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hv0
  have hj' : v j ≠ 0 := hj
  rw [eq_top_iff]
  intro w _
  rw [← Finset.univ_sum_single w]
  refine N.sum_mem fun i _ => ?_
  have h1 := N.smul_mem (w i * (v j)⁻¹) (key (Matrix.single i j 1) v hv)
  have h2 : (w i * (v j)⁻¹) • ((Matrix.single i j (1 : E)).map f).mulVec v = Pi.single i (w i) := by
    rw [Matrix.map_single, map_one, Matrix.single_mulVec]
    ext k
    by_cases hk : k = i
    · subst hk
      simp [hj']
    · simp [hk]
  rwa [h2] at h1

theorem irr_map : ∀ {Γ E E' : Type} [inst : Group Γ] [inst_1 : Field E]
  [inst_2 : Field E'] (f : E →+* E') {n : ℕ} (r : Γ →* Matrix (Fin n) (Fin n) E),
  Irr r →
    ∀ (N : Submodule E' (Fin n → E')),
      (∀ (g : Γ), ∀ v ∈ N, ((mapRep f r) g).mulVec v ∈ N) → N = ⊥ ∨ N = ⊤ := by
  intro Γ E E' _ _ _ f n r hr N hN
  exact aux f (fun g => r g) hr N hN

end UpperTheory.Reformulated.B.Qi38
end

section

noncomputable def UpperTheory.Reformulated.B.BlockFourMatrices.blk4 :
    {R : Type} →
      {n : ℕ} →
        Matrix (Fin n) (Fin n) R →
          Matrix (Fin n) (Fin n) R →
            Matrix (Fin n) (Fin n) R → Matrix (Fin n) (Fin n) R → Matrix (Fin (n + n)) (Fin (n + n)) R :=
    fun {R : Type} {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) R) ↦
      (Matrix.fromBlocks a b c d).submatrix (⇑finSumFinEquiv.symm : Fin (n + n) → Fin n ⊕ Fin n)
        (⇑finSumFinEquiv.symm : Fin (n + n) → Fin n ⊕ Fin n)

theorem UpperTheory.Reformulated.B.BlockFourMatrices.main :
    ∀ {R S : Type} {m : ℕ} (f : R → S) (a b c d : Matrix (Fin m) (Fin m) R),
      (UpperTheory.Reformulated.B.BlockFourMatrices.blk4 a b c d).map f = UpperTheory.Reformulated.B.BlockFourMatrices.blk4 (a.map f) (b.map f) (c.map f) (d.map f) := by
  intro R S m f a b c d
  unfold UpperTheory.Reformulated.B.BlockFourMatrices.blk4
  rw [← Matrix.submatrix_map, Matrix.fromBlocks_map]
end

section

theorem UpperTheory.Reformulated.B.UpperTriangularThreeDiagonalOfMul.diag_mul :
    ∀ {R : Type} [inst : CommRing R]
    (X Y : Matrix (Fin (3 : ℕ)) (Fin (3 : ℕ)) R),
    (∀ (i j : Fin (3 : ℕ)), j < i → X i j = (0 : R)) →
      (∀ (i j : Fin (3 : ℕ)), j < i → Y i j = (0 : R)) → ∀ (a : Fin (3 : ℕ)), (X * Y) a a = X a a * Y a a := by
  intro R _ X Y hX hY a
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single a (fun b _ hb => ?_) (fun h => absurd (Finset.mem_univ a) h)
  rcases lt_or_gt_of_ne hb with h | h
  · rw [hX a b h, zero_mul]
  · rw [hY b a h, mul_zero]
end

section

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qk42.M4 :
    Type → Type :=
    fun (R : Type) ↦ Matrix (Fin (4 : ℕ)) (Fin (4 : ℕ)) R

noncomputable def UpperTheory.Reformulated.B.Qk42.FGe :
    {R : Type} → [CommRing R] → (Fin (4 : ℕ) → ℤ) → ℤ → UpperTheory.Reformulated.B.Qk42.M4 R → Prop :=
    fun {R : Type} [CommRing R] (m : Fin (4 : ℕ) → ℤ) (p : ℤ) (X : UpperTheory.Reformulated.B.Qk42.M4 R) ↦
      ∀ (i j : Fin (4 : ℕ)), m i - m j < p → X i j = (0 : R)

theorem UpperTheory.Reformulated.B.Qk42.mul :
    ∀ {R : Type} [inst : CommRing R] {m : Fin (4 : ℕ) → ℤ} {p q : ℤ} {A B : UpperTheory.Reformulated.B.Qk42.M4 R},
      UpperTheory.Reformulated.B.Qk42.FGe m p A → UpperTheory.Reformulated.B.Qk42.FGe m q B → UpperTheory.Reformulated.B.Qk42.FGe m (p + q) (A * B) := by
  intro R _ m p q A B hA hB i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : m i - m k < p
  · rw [hA i k hk, zero_mul]
  · rw [hB k j (by omega), mul_zero]
end

section

namespace UpperTheory.Reformulated.B.S8

theorem diag_mul {R : Type} [CommRing R] {n : ℕ} (X Y : Matrix (Fin n) (Fin n) R) (hX : ∀ i j, j < i → X i j = 0)
    (hY : ∀ i j, j < i → Y i j = 0) (a : Fin n) : (X * Y) a a = X a a * Y a a := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single_of_mem a (Finset.mem_univ a) ?_
  intro b _ hb
  rcases lt_or_gt_of_ne hb with h | h
  · rw [hX a b h, zero_mul]
  · rw [hY b a h, mul_zero]

end UpperTheory.Reformulated.B.S8
end
