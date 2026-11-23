module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle003
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.GroupTheory.Schreier
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
public import Mathlib.GroupTheory.Finiteness

@[expose] public section

section

open MvPolynomial Equiv UpperTheory.V.AlgebraTools.Hk

private theorem swap_lt {n : ℕ} {a c : Fin n} (h : a.val + 1 = c.val) {x y : Fin n} (hxy : x < y)
    (hne : ¬ (x = a ∧ y = c)) : swap a c x < swap a c y := by
  have key : ∀ z : Fin n, (swap a c z).val = if z.val = a.val then c.val else if z.val = c.val then a.val else z.val := by
    intro z
    rw [swap_apply_def]
    by_cases h1 : z = a
    · subst h1
      simp
    · by_cases h2 : z = c
      · subst h2
        have h1' : z.val ≠ a.val := fun e => h1 (Fin.ext e)
        simp [h1, h1']
      · have h1' : z.val ≠ a.val := fun e => h1 (Fin.ext e)
        have h2' : z.val ≠ c.val := fun e => h2 (Fin.ext e)
        simp [h1, h2, h1', h2']
  rw [Fin.lt_def, key, key]
  rw [Fin.lt_def] at hxy
  have hne' : ¬ (x.val = a.val ∧ y.val = c.val) := fun e => hne ⟨Fin.ext e.1, Fin.ext e.2⟩
  split_ifs <;> omega

private theorem mem_invSet {n : ℕ} (w : Perm (Fin n)) (p : Fin n × Fin n) :
    p ∈ invSet w ↔ p.1 < p.2 ∧ w⁻¹ p.2 < w⁻¹ p.1 := by
  simp [invSet, pairs]

private theorem eq_one_of_strictMono {n : ℕ} (w : Perm (Fin n)) (h : StrictMono w) : w = 1 := by
  exact Equiv.ext fun x => congrFun h.eq_id x

private theorem invSet_rev (n : ℕ) : invSet (Fin.revPerm : Perm (Fin n)) = pairs n := by
  ext ⟨x, y⟩
  rw [mem_invSet]
  have hinv : ∀ z : Fin n, (Fin.revPerm : Perm (Fin n))⁻¹ z = z.rev := by
    intro z
    rw [Perm.inv_eq_iff_eq, Fin.revPerm_apply, Fin.rev_rev]
  simp only [hinv, Fin.rev_lt_rev]
  simp only [pairs, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => h.1, fun h => ⟨h, h⟩⟩

theorem UpperTheory.V.AlgebraTools.hkInv :
    ∀ n : ℕ, (∀ (a c : Fin n), a.val + 1 = c.val → ∀ w : Perm (Fin n), w⁻¹ a < w⁻¹ c →
        invSet (swap a c * w) = insert (a, c) ((invSet w).image fun p => (swap a c p.1, swap a c p.2)) ∧
        (a, c) ∉ (invSet w).image (fun p => (swap a c p.1, swap a c p.2)) ∧ invN (swap a c * w) = invN w + 1) ∧
      (∀ w : Perm (Fin n), w ≠ 1 → ∃ a c : Fin n, a.val + 1 = c.val ∧ w⁻¹ c < w⁻¹ a) ∧
      invSet (1 : Perm (Fin n)) = ∅ ∧ invSet (Fin.revPerm : Perm (Fin n)) = pairs n ∧
      (∀ w : Perm (Fin n), w ≠ Fin.revPerm → invN w < invN (Fin.revPerm : Perm (Fin n))) := by
  intro n
  refine ⟨?_, ?_, ?_, invSet_rev n, ?_⟩
  · intro a c hac w hw
    have hlt : a < c := by
      rw [Fin.lt_def]
      omega
    have hff : ∀ p : Fin n × Fin n, (swap a c (swap a c p.1), swap a c (swap a c p.2)) = p := by
      intro p
      simp
    have hmemimg : ∀ q : Fin n × Fin n, q ∈ (invSet w).image (fun p => (swap a c p.1, swap a c p.2)) ↔
        (swap a c q.1, swap a c q.2) ∈ invSet w := by
      intro q
      rw [Finset.mem_image]
      constructor
      · rintro ⟨p, hp, rfl⟩
        rwa [hff]
      · intro hq
        exact ⟨_, hq, hff q⟩
    have hnot : (a, c) ∉ (invSet w).image (fun p => (swap a c p.1, swap a c p.2)) := by
      rw [hmemimg, mem_invSet]
      simp only [swap_apply_left, swap_apply_right]
      exact fun h => absurd h.1 (lt_asymm hlt)
    have heq : invSet (swap a c * w) = insert (a, c) ((invSet w).image (fun p => (swap a c p.1, swap a c p.2))) := by
      ext ⟨x, y⟩
      rw [Finset.mem_insert, hmemimg, mem_invSet, mem_invSet]
      simp only [mul_inv_rev, swap_inv, Perm.mul_apply, Prod.mk.injEq]
      by_cases hp : x = a ∧ y = c
      · obtain ⟨rfl, rfl⟩ := hp
        simp only [swap_apply_left, swap_apply_right]
        exact ⟨fun _ => Or.inl (by simp), fun _ => ⟨hlt, hw⟩⟩
      · constructor
        · rintro ⟨hxy, hA⟩
          exact Or.inr ⟨swap_lt hac hxy hp, hA⟩
        · rintro (h | ⟨hs, hA⟩)
          · exact absurd h hp
          · refine ⟨?_, hA⟩
            rcases lt_trichotomy x y with h | h | h
            · exact h
            · subst h
              exact absurd hs (lt_irrefl _)
            · by_cases hq : y = a ∧ x = c
              · obtain ⟨rfl, rfl⟩ := hq
                simp only [swap_apply_left, swap_apply_right] at hA
                exact absurd hA (lt_asymm hw)
              · exact absurd (swap_lt hac h hq) (lt_asymm hs)
    refine ⟨heq, hnot, ?_⟩
    unfold invN
    rw [heq, Finset.card_insert_of_notMem hnot, Finset.card_image_of_injective]
    intro p q hpq
    have := congrArg (fun r : Fin n × Fin n => (swap a c r.1, swap a c r.2)) hpq
    simp only [hff] at this
    exact this
  · intro w hw
    by_contra hcon
    push_neg at hcon
    apply hw
    have hadj : ∀ a c : Fin n, a.val + 1 = c.val → w⁻¹ a < w⁻¹ c := by
      intro a c h
      refine lt_of_le_of_ne (hcon a c h) ?_
      intro h'
      have := w⁻¹.injective h'
      rw [this] at h
      omega
    have key : ∀ k : ℕ, ∀ i j : Fin n, j.val = i.val + k + 1 → w⁻¹ i < w⁻¹ j := by
      intro k
      induction k with
      | zero =>
        intro i j h
        exact hadj i j (by omega)
      | succ k ih =>
        intro i j h
        have hj := j.isLt
        have hm : i.val + k + 1 < n := by omega
        exact lt_trans (ih i ⟨i.val + k + 1, hm⟩ rfl) (hadj _ _ (by show i.val + k + 1 + 1 = j.val; omega))
    have hsm : StrictMono ⇑(w⁻¹) := by
      intro i j hij
      rw [Fin.lt_def] at hij
      exact key (j.val - i.val - 1) i j (by omega)
    exact inv_eq_one.mp (eq_one_of_strictMono _ hsm)
  · apply Finset.eq_empty_of_forall_notMem
    intro p hp
    rw [mem_invSet] at hp
    simp only [inv_one, Perm.one_apply] at hp
    exact lt_asymm hp.1 hp.2
  · intro w hw
    unfold invN
    rw [invSet_rev]
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨Finset.filter_subset _ _, ?_⟩
    intro hset
    apply hw
    have hall : ∀ i j : Fin n, i < j → w⁻¹ j < w⁻¹ i := by
      intro i j hij
      have hm : (i, j) ∈ invSet w := by
        rw [hset]
        simp [pairs, hij]
      exact ((mem_invSet w _).mp hm).2
    have hsm : StrictMono ⇑(w⁻¹ * (Fin.revPerm : Perm (Fin n))) := by
      intro i j hij
      simp only [Perm.mul_apply, Fin.revPerm_apply]
      exact hall _ _ (Fin.rev_lt_rev.mpr hij)
    have h1 := eq_one_of_strictMono _ hsm
    rw [mul_eq_one_iff_eq_inv] at h1
    exact inv_inj.mp h1
end

section

open MvPolynomial Equiv UpperTheory.V.AlgebraTools.Hk

private theorem finset_prod_dvd_of_prime_of_dvd_imp_eq {M ι : Type} [CommRing M] (f : ι → M) (y : M) (s : Finset ι)
    (hp : ∀ a ∈ s, Prime (f a)) (hn : ∀ a ∈ s, ∀ b ∈ s, f a ∣ f b → a = b) (hd : ∀ a ∈ s, f a ∣ y) :
    ∏ a ∈ s, f a ∣ y :=
  _root_.UpperTheory.Reformulated.B.Qi3.finset_prod_dvd_of_prime_of_dvd_imp_eq f y s hp hn hd

private def sb {n : ℕ} (i j : Fin n) : Fin n → Fin n := fun k => if k = j then i else k

private theorem dvd_sub_sb {R : Type} [CommRing R] {n : ℕ} (i j : Fin n) (y : MvPolynomial (Fin n) R) :
    (X j - X i : MvPolynomial (Fin n) R) ∣ y - rename (sb i j) y := by
  induction y using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    have := dvd_add hp hq
    rw [map_add (f := _)]
    convert this using 1
    ring
  | mul_X p k hp =>
    have hk : (X j - X i : MvPolynomial (Fin n) R) ∣ X k - X (sb i j k) := by
      unfold sb
      split_ifs with h
      · rw [h]
      · simp
    have := dvd_add (hp.mul_right (X k)) (hk.mul_left (rename (sb i j) p))
    rw [map_mul, rename_X]
    convert this using 1
    ring

private theorem dvd_iff_sb {R : Type} [CommRing R] {n : ℕ} (i j : Fin n) (y : MvPolynomial (Fin n) R) :
    (X j - X i : MvPolynomial (Fin n) R) ∣ y ↔ rename (sb i j) y = 0 := by
  constructor
  · rintro ⟨c, rfl⟩
    have : sb i j j = sb i j i := by simp [sb]
    rw [map_mul, map_sub, rename_X, rename_X, this, sub_self, zero_mul]
  · intro h
    have := dvd_sub_sb i j y
    rwa [h, sub_zero] at this

private theorem prime_sb {R : Type} [CommRing R] [IsDomain R] {n : ℕ} {i j : Fin n} (h : i ≠ j) :
    Prime (X j - X i : MvPolynomial (Fin n) R) := by
  refine ⟨fun e => h.symm (X_injective (sub_eq_zero.1 e)), fun hu => ?_, fun a b hab => ?_⟩
  · have := (dvd_iff_sb i j (1 : MvPolynomial (Fin n) R)).1 hu.dvd
    simp at this
  · rw [dvd_iff_sb, map_mul, mul_eq_zero] at hab
    rwa [dvd_iff_sb, dvd_iff_sb]

private theorem alt_sb {R : Type} [CommRing R] {n : ℕ} {i j : Fin n} (h : i ≠ j) (x : MvPolynomial (Fin n) R) :
    rename (sb i j) (alt x) = 0 := by
  have hs : ∀ k, sb i j (swap i j k) = sb i j k := by
    intro k
    by_cases h1 : k = i
    · subst h1; simp [sb]
    · by_cases h2 : k = j
      · subst h2; simp [sb]
      · rw [swap_apply_of_ne_of_ne h1 h2]

  rw [alt, map_sum]
  refine Finset.sum_involution (fun w _ => swap i j * w) (fun w _ => ?_) (fun w _ _ e => ?_)
    (fun w _ => Finset.mem_univ _) (fun w _ => ?_)
  · have e : sb i j ∘ (swap i j * w : Perm (Fin n)) = sb i j ∘ w := funext fun k => hs _
    rw [Units.smul_def, Units.smul_def, map_zsmul, map_zsmul, rename_rename, rename_rename, e, Perm.sign_mul,
      Perm.sign_swap h]
    simp
  · have := mul_eq_right.1 e
    exact h (swap_eq_one_iff.1 this)
  · simp [← mul_assoc]

theorem UpperTheory.V.AlgebraTools.hkDdSpec :
    ∀ (R : Type) [CommRing R] [IsDomain R] (n : ℕ) (x : MvPolynomial (Fin n) R), De R n * dd x = alt x := by
  intro R _ _ n x
  have hlt : ∀ p ∈ pairs n, p.1 < p.2 := fun p hp => by simpa [pairs] using hp
  have hd : De R n ∣ alt x := by
    refine finset_prod_dvd_of_prime_of_dvd_imp_eq _ _ _ (fun p hp => prime_sb (hlt p hp).ne) (fun p hp q hq hpq => ?_)
      (fun p hp => (dvd_iff_sb _ _ _).2 (alt_sb (hlt p hp).ne x))
    rw [dvd_iff_sb, map_sub, rename_X, rename_X, sub_eq_zero] at hpq
    have e := X_injective hpq
    have h1 := hlt p hp
    have h2 := hlt q hq
    unfold sb at e
    split_ifs at e with a b b
    · exact absurd (b.trans a.symm) h2.ne
    · exact Prod.ext e a.symm
    · rw [e, b] at h2
      exact absurd h1 h2.not_gt
    · exact absurd e h2.ne'
  obtain ⟨y, hy⟩ := hd
  have h : ∃ y, De R n * y = alt x := ⟨y, hy.symm⟩
  rw [dd, dite_eq_left h]
  exact h.choose_spec
end

section

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

open ProfiniteGrp ProfiniteGrp.ProfiniteCompletion CategoryTheory in
theorem UpperTheory.V.AlgebraTools.exists_free_profinite :
    ∀ r : ℕ, ∃ (P : Type) (_ : Group P) (_ : TopologicalSpace P) (_ : IsTopologicalGroup P) (_ : CompactSpace P)
      (_ : TotallyDisconnectedSpace P) (x : Fin r → P), TopGen (Set.range x) ∧
        ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (y : Fin r → G), ∃ f : P →* G, Continuous f ∧ ∀ i, f (x i) = y i := by
  intro r
  let F : GrpCat.{0} := GrpCat.of (FreeGroup (Fin r))
  let P : ProfiniteGrp.{0} := completion F
  let η : FreeGroup (Fin r) →* P := (eta F).hom
  refine ⟨P, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    fun i => η (FreeGroup.of i), ?_, ?_⟩
  · unfold TopGen
    have hr : Set.range (fun i => η (FreeGroup.of i)) = η '' Set.range FreeGroup.of := by
      rw [← Set.range_comp]
      rfl
    rw [hr, ← MonoidHom.map_closure, FreeGroup.closure_range_of, ← MonoidHom.range_eq_map,
      MonoidHom.coe_range]
    exact denseRange (G := F)
  · intro G _ _ _ _ _ y
    let Q : ProfiniteGrp.{0} := ProfiniteGrp.of G
    let f0 : F ⟶ GrpCat.of Q := GrpCat.ofHom (FreeGroup.lift y)
    let L : P ⟶ Q := lift f0
    refine ⟨L.hom.toMonoidHom, L.hom.continuous, ?_⟩
    intro i
    have h : ((eta F) ≫ (forget₂ ProfiniteGrp GrpCat).map L).hom (FreeGroup.of i) =
        f0.hom (FreeGroup.of i) := by
      rw [lift_eta]
    exact h.trans FreeGroup.lift_apply_of
end

section

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.TopFG.subgroup_quot :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G], TopFG G →
      (∀ H : Subgroup G, IsOpen (H : Set G) → TopFG H) ∧
      (∀ (Z : Type) [Group Z] [TopologicalSpace Z] (f : G →* Z), Continuous f → Function.Surjective f → TopFG Z) := by
  intro G _ _ _ _ hG
  obtain ⟨s, hs, hden⟩ := hG
  refine ⟨?_, ?_⟩
  · intro H hH
    haveI : Finite (G ⧸ H) := H.quotient_finite_of_isOpen hH
    haveI : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    set D := Subgroup.closure s with hD
    haveI : Finite s := hs
    haveI : Group.FG D := inferInstance
    haveI : (H.subgroupOf D).FiniteIndex := inferInstance
    have hfg : Group.FG (H.subgroupOf D) := inferInstance
    obtain ⟨t, ht, htf⟩ := Group.fg_iff.mp hfg
    let φ : H.subgroupOf D →* H :=
      (D.subtype.comp (H.subgroupOf D).subtype).codRestrict H (fun x => x.2)
    refine ⟨φ '' t, htf.image _, ?_⟩
    unfold TopGen
    rw [← MonoidHom.map_closure, ht, ← MonoidHom.range_eq_map]
    rw [dense_iff_inter_open]
    intro U hU hUne
    have hVo : IsOpen ((Subtype.val : H → G) '' U) := hH.isOpenMap_subtype_val U hU
    obtain ⟨x, ⟨y, hyU, rfl⟩, hxD⟩ := hden.inter_open_nonempty _ hVo (hUne.image _)
    refine ⟨y, hyU, ⟨⟨y.1, hxD⟩, y.2⟩, ?_⟩
    rfl
  · intro Z _ _ f hf hsurj
    refine ⟨f '' s, hs.image _, ?_⟩
    unfold TopGen at hden ⊢
    rw [← MonoidHom.map_closure, Subgroup.coe_map]
    exact hsurj.denseRange.dense_image hf hden
end

section

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

private theorem pq_iff (l : ℕ) (G : Type) [Group G] (N : Subgroup G) [N.Normal] :
    IsPGroup l (G ⧸ N) ↔ ∀ g : G, ∃ k : ℕ, g ^ l ^ k ∈ N := by
  refine ⟨fun h g => ?_, fun h x => ?_⟩
  · obtain ⟨k, hk⟩ := h (g : G ⧸ N)
    exact ⟨k, by rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk⟩
  · obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨k, hk⟩ := h g
    exact ⟨k, by rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]⟩

private theorem res_map (l : ℕ) (G : Type) [Group G] [TopologicalSpace G] (f : G →* G)
    (hf : Continuous f) {x : G} (hx : x ∈ proLRes l G) : f x ∈ proLRes l G := by
  rw [mem_proLRes] at hx ⊢
  intro N hN
  let M : OpenNormalSubgroup G :=
    { toSubgroup := (N.toOpenSubgroup : Subgroup G).comap f
      isOpen' := N.toOpenSubgroup.isOpen.preimage hf
      isNormal' := Subgroup.Normal.comap inferInstance f }
  have hM : IsPGroup l (G ⧸ (M.toOpenSubgroup : Subgroup G)) := by
    rw [pq_iff] at hN ⊢
    intro g
    obtain ⟨k, hk⟩ := hN (f g)
    exact ⟨k, by simpa [M, map_pow] using hk⟩
  have := hx M hM
  simpa [M] using this

private theorem res_pow (l : ℕ) (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] (K : Subgroup G) (hK : IsOpen (K : Set G)) (h : proLRes l G ≤ K) (g : G) :
    ∃ k : ℕ, g ^ l ^ k ∈ K := by
  classical
  let ι := {N : OpenNormalSubgroup G // IsPGroup l (G ⧸ (N.toOpenSubgroup : Subgroup G))}
  let t : ι → Set G := fun i => ((i.1.toOpenSubgroup : Subgroup G) : Set G)
  have ht : ∀ i, IsClosed (t i) := fun i => i.1.toOpenSubgroup.isClosed
  have hs : IsCompact ((K : Set G)ᶜ) := (hK.isClosed_compl).isCompact
  have hdisjoint : Disjoint (K : Set G)ᶜ (⋂ i, t i) := by
    simp only [Set.disjoint_left, Set.mem_compl_iff, Set.mem_iInter]
    intro y hy hall
    apply hy
    apply h
    rw [mem_proLRes]
    intro N hN
    exact hall ⟨N, hN⟩
  obtain ⟨u, hu⟩ := hs.elim_finite_subfamily_closed t ht hdisjoint
  have hk : ∀ i : ι, ∃ k : ℕ, g ^ l ^ k ∈ (i.1.toOpenSubgroup : Subgroup G) := fun i =>
    (pq_iff l G _).mp i.2 g
  choose kf hkf using hk
  refine ⟨∑ i ∈ u, kf i, ?_⟩
  by_contra hg
  apply Set.disjoint_left.mp hu hg
  simp only [Set.mem_iInter]
  intro i hi
  have hle : kf i ≤ ∑ j ∈ u, kf j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi
  have heq : l ^ (∑ j ∈ u, kf j) = l ^ kf i * l ^ (∑ j ∈ u, kf j - kf i) := by
    rw [← pow_add, Nat.add_sub_cancel' hle]
  show g ^ l ^ (∑ j ∈ u, kf j) ∈ ((i.1.toOpenSubgroup : Subgroup G) : Set G)
  rw [heq, pow_mul]
  exact Subgroup.pow_mem _ (hkf i) _

theorem UpperTheory.V.AlgebraTools.proLResOf_normal :
    ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (H : Subgroup G) [H.Normal], IsClosed (H : Set G) →
      (proLResOf l H).Normal ∧ IsClosed (proLResOf l H : Set G) ∧ proLResOf l H ≤ H ∧
      ∀ (O : OpenNormalSubgroup G), proLResOf l H ≤ O.toSubgroup → ∀ h ∈ H, ∃ k : ℕ, h ^ l ^ k ∈ O.toSubgroup := by
  intro l _ G _ _ _ _ _ H _ hH
  have : CompactSpace H := isCompact_iff_compactSpace.mp hH.isCompact
  refine ⟨?_, ?_, ?_, ?_⟩
  · constructor
    intro x hx g
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    let c : H →* H := (MulAut.conjNormal g).toMonoidHom
    have hc : Continuous c := by
      apply Continuous.subtype_mk
      exact (continuous_const.mul continuous_subtype_val).mul continuous_const
    have := res_map l H c hc hy
    refine Subgroup.mem_map.mpr ⟨c y, this, ?_⟩
    simp [c, MulAut.conjNormal_apply]
  · unfold proLResOf
    rw [Subgroup.coe_map, Subgroup.coe_subtype]
    exact hH.isClosedEmbedding_subtypeVal.isClosedMap _ (isClosed_proLRes l H)
  · exact Subgroup.map_subtype_le _
  · intro O hO h hh
    have hle : proLRes l H ≤ (O.toOpenSubgroup : Subgroup G).comap H.subtype :=
      Subgroup.map_le_iff_le_comap.mp hO
    have hopen : IsOpen (((O.toOpenSubgroup : Subgroup G).comap H.subtype : Subgroup H) : Set H) :=
      O.toOpenSubgroup.isOpen.preimage continuous_subtype_val
    obtain ⟨k, hk⟩ := res_pow l H _ hopen hle ⟨h, hh⟩
    exact ⟨k, hk⟩
end
