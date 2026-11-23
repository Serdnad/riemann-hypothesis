module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Data.Rat.Defs
public import Mathlib.GroupTheory.Index
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Star.Basic
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

section

open scoped InnerProductSpace BigOperators

namespace GlobalTheory

theorem finprod_components_of_rightInvariant_mul :
    ∀ (Γ : Type) [Group Γ] (K : Subgroup Γ) (ι : Type) (c : ι → Γ →* Γ) (a : Γ → ℂ),
      (∀ g, g ∈ K ↔ ∀ v, c v g ∈ K) → (∀ g, {v | c v g ∉ K}.Finite) →
      (∀ v g, c v (c v g) = c v g) → (∀ v w g, v ≠ w → c w (c v g) = 1) →
      (∀ g k, k ∈ K → a (g * k) = a g) → a 1 = 1 →
      (∀ v g h, c v g = 1 → c v h = h → a (g * h) = a g * a h) →
      ∀ g, a g = ∏ᶠ v, a (c v g) := by
  intro Γ _ K ι c a hK hfin hidem horth hinv ha1 hmul
  classical

  have haK : ∀ k, k ∈ K → a k = 1 := by
    intro k hk
    have := hinv 1 k hk
    rw [one_mul] at this
    rw [this, ha1]
  have key : ∀ (s : Finset ι) (g : Γ), {v | c v g ∉ K} ⊆ (s : Set ι) →
      a g = ∏ v ∈ s, a (c v g) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro g hg
      have hgK : g ∈ K := (hK g).2 (fun v => by
        by_contra h
        simpa using hg h)
      simp [haK g hgK]
    | @insert v s hv ih =>
      intro g hg
      set g' := g * (c v g)⁻¹ with hg'
      have hcv : c v g' = 1 := by
        rw [hg', map_mul, map_inv, hidem, mul_inv_cancel]
      have hcw : ∀ w, w ≠ v → c w g' = c w g := by
        intro w hw
        rw [hg', map_mul, map_inv, horth v w g (Ne.symm hw), inv_one, mul_one]
      have hsupp : {w | c w g' ∉ K} ⊆ (s : Set ι) := by
        intro w hw
        simp only [Set.mem_setOf_eq] at hw
        by_cases hwv : w = v
        · subst hwv
          exact absurd (hcv ▸ K.one_mem) hw
        · rw [hcw w hwv] at hw
          have := hg hw
          simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at this
          exact this.resolve_left hwv
      have ih' := ih g' hsupp
      have hprod : ∏ w ∈ s, a (c w g') = ∏ w ∈ s, a (c w g) := by
        apply Finset.prod_congr rfl
        intro w hw
        rw [hcw w (fun h => hv (h ▸ hw))]
      have hsplit : g = g' * c v g := by
        rw [hg', inv_mul_cancel_right]
      have hag : a g = a g' * a (c v g) := by
        conv_lhs => rw [hsplit]
        exact hmul v g' (c v g) hcv (hidem v g)
      rw [hag, ih', hprod, Finset.prod_insert hv, mul_comm]
  intro g
  have hsub : Function.mulSupport (fun v => a (c v g)) ⊆ ((hfin g).toFinset : Set ι) := by
    intro w hw
    simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    intro hwK
    exact hw (haK _ hwK)
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub]
  exact key _ g (by simp)

end GlobalTheory
end

section

open Polynomial

namespace GlobalTheory.OrbitCounting

theorem stabilizer_smul_eq {G X : Type} [CommGroup G] [MulAction G X] (g : G) (x : X) :
    MulAction.stabilizer G (g • x) = MulAction.stabilizer G x := by
  ext h
  simp only [MulAction.mem_stabilizer_iff]
  rw [← mul_smul, mul_comm, mul_smul, smul_left_cancel_iff]

theorem ncard_fibre_inter_orbit {G X Y : Type} [CommGroup G] [MulAction G X] [MulAction G Y]
    (π : X → Y) (hπ : ∀ (g : G) (x : X), π (g • x) = g • π x) (x0 : X) :
    {x | π x = π x0 ∧ x ∈ MulAction.orbit G x0}.ncard =
      (MulAction.stabilizer G x0).relIndex (MulAction.stabilizer G (π x0)) := by
  have hset : {x | π x = π x0 ∧ x ∈ MulAction.orbit G x0} =
      MulAction.orbit (MulAction.stabilizer G (π x0)) x0 := by
    ext x; constructor
    · rintro ⟨hx, g, rfl⟩
      refine ⟨⟨g, ?_⟩, rfl⟩
      rw [MulAction.mem_stabilizer_iff, ← hπ]; exact hx
    · rintro ⟨⟨g, hg⟩, rfl⟩
      refine ⟨?_, ⟨g, rfl⟩⟩
      show π (g • x0) = π x0
      rw [hπ]; exact hg
  rw [hset, Subgroup.relIndex, ← MulAction.index_stabilizer]
  congr 1

theorem counting_principle : ∀ (G X Y : Type) [CommGroup G] [MulAction G X] [MulAction G Y] (Gc : Subgroup G) (π : X → Y), (∀ (g : G) (x : X), π (g • x) = g • π x) → (∀ y, (π ⁻¹' {y}).Finite) → (∀ y : Y, MulAction.stabilizer G y ≤ Gc ∧ (MulAction.stabilizer G y).relIndex Gc ≠ 0) → Finite (MulAction.orbitRel.Quotient G Y) → ∀ w : Y → ℚ, (∀ (g : G) (y : Y), w (g • y) = w y) → ∑ᶠ o : MulAction.orbitRel.Quotient G X, w (π (Quotient.out o)) * ((MulAction.stabilizer G (Quotient.out o)).relIndex Gc : ℚ) = ∑ᶠ o : MulAction.orbitRel.Quotient G Y, w (Quotient.out o) * ((π ⁻¹' {(Quotient.out o)}).ncard : ℚ) * ((MulAction.stabilizer G (Quotient.out o)).relIndex Gc : ℚ) := by
  intro G X Y _ _ _ Gc π hπ hfin hstab hY w hw
  classical
  have hmem : ∀ a b : X, a ∈ MulAction.orbit G b → π a ∈ MulAction.orbit G (π b) := by
    rintro a b ⟨g, rfl⟩; exact ⟨g, (hπ g b).symm⟩
  let q : MulAction.orbitRel.Quotient G X → MulAction.orbitRel.Quotient G Y :=
    Quotient.map π (fun a b h => MulAction.orbitRel_apply.2 (hmem a b (MulAction.orbitRel_apply.1 h)))
  have hq : ∀ x : X, q (Quotient.mk _ x) = Quotient.mk _ (π x) := fun x => rfl

  have hrep : ∀ (oX : MulAction.orbitRel.Quotient G X) (y : Y), q oX = Quotient.mk _ y →
      ∃ x0, π x0 = y ∧ Quotient.mk _ x0 = oX := by
    intro oX y h
    have h1 : q oX = Quotient.mk _ (π (Quotient.out oX)) := by
      rw [← hq, Quotient.out_eq]
    rw [h1] at h
    have h2 : y ∈ MulAction.orbit G (π (Quotient.out oX)) :=
      MulAction.orbitRel_apply.1 (Quotient.exact h.symm)
    obtain ⟨g, hg⟩ := h2
    refine ⟨g • Quotient.out oX, by rw [hπ]; exact hg, ?_⟩
    rw [← Quotient.out_eq oX]
    exact Quotient.sound (MulAction.orbitRel_apply.2 ⟨g, by rw [Quotient.out_eq]⟩)

  let F : X → ℚ := fun x => w (π x) * ((MulAction.stabilizer G x).relIndex Gc : ℚ)
  let H : Y → ℚ := fun y => w y * ((π ⁻¹' {y}).ncard : ℚ) * ((MulAction.stabilizer G y).relIndex Gc : ℚ)
  have hF : ∀ x x' : X, x' ∈ MulAction.orbit G x → F x' = F x := by
    rintro x x' ⟨g, rfl⟩
    simp only [F, hπ, hw, stabilizer_smul_eq]

  haveI : ∀ oY : MulAction.orbitRel.Quotient G Y, Finite ↥(π ⁻¹' {Quotient.out oY}) :=
    fun oY => (hfin _).to_subtype
  haveI hXf : Finite (MulAction.orbitRel.Quotient G X) := by
    refine Finite.of_surjective
      (fun p : (Σ oY : MulAction.orbitRel.Quotient G Y, ↥(π ⁻¹' {Quotient.out oY})) =>
        (Quotient.mk _ (p.2 : X) : MulAction.orbitRel.Quotient G X)) ?_
    intro oX
    obtain ⟨x0, hx0, hx0'⟩ := hrep oX (Quotient.out (q oX)) (Quotient.out_eq _).symm
    exact ⟨⟨q oX, ⟨x0, hx0⟩⟩, hx0'⟩
  haveI := Fintype.ofFinite (MulAction.orbitRel.Quotient G X)
  haveI := Fintype.ofFinite (MulAction.orbitRel.Quotient G Y)
  have hL : ∀ oX : MulAction.orbitRel.Quotient G X,
      w (π (Quotient.out oX)) * ((MulAction.stabilizer G (Quotient.out oX)).relIndex Gc : ℚ) = F (Quotient.out oX) := fun _ => rfl
  have hR : ∀ oY : MulAction.orbitRel.Quotient G Y,
      w (Quotient.out oY) * ((π ⁻¹' {(Quotient.out oY)}).ncard : ℚ) * ((MulAction.stabilizer G (Quotient.out oY)).relIndex Gc : ℚ) = H (Quotient.out oY) := fun _ => rfl
  simp only [hL, hR]
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, ← Finset.sum_fiberwise Finset.univ q]
  refine Finset.sum_congr rfl (fun oY _ => ?_)
  set y := Quotient.out oY with hy
  have hyo : Quotient.mk _ y = oY := Quotient.out_eq oY
  set S := (hfin y).toFinset with hS
  have hcard : (π ⁻¹' {y}).ncard = S.card := Set.ncard_eq_toFinset_card _ (hfin y)
  have hmaps : (S : Set X).MapsTo (fun x => (Quotient.mk _ x : MulAction.orbitRel.Quotient G X))
      (Finset.univ.filter (fun oX => q oX = oY) : Finset _) := by
    intro x hx
    simp only [hS, Set.Finite.coe_toFinset, Set.mem_preimage, Set.mem_singleton_iff] at hx
    simp [hq, hx, hyo]
  have hsum := Finset.card_eq_sum_card_fiberwise hmaps
  show _ = w y * ((π ⁻¹' {y}).ncard : ℚ) * ((MulAction.stabilizer G y).relIndex Gc : ℚ)
  rw [hcard, hsum]
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun oX hoX => ?_)
  have hqo : q oX = Quotient.mk _ y := by
    rw [hyo]; simpa using hoX
  obtain ⟨x0, hx0, hx0'⟩ := hrep oX y hqo
  have hout : Quotient.out oX ∈ MulAction.orbit G x0 := by
    apply MulAction.orbitRel_apply.1
    apply Quotient.exact
    rw [Quotient.out_eq, hx0']
  rw [hF x0 _ hout]
  have hfilt : ((S.filter (fun x => (Quotient.mk _ x : MulAction.orbitRel.Quotient G X) = oX) : Finset X) : Set X)
      = {x | π x = π x0 ∧ x ∈ MulAction.orbit G x0} := by
    ext x
    simp only [hS, Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_preimage,
      Set.mem_singleton_iff, Set.mem_setOf_eq, hx0]
    rw [← hx0']
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, MulAction.orbitRel_apply.1 (Quotient.exact h2)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, Quotient.sound (MulAction.orbitRel_apply.2 h2)⟩
  rw [← Set.ncard_coe_finset, hfilt, ncard_fibre_inter_orbit π hπ x0]
  have hle1 : MulAction.stabilizer G x0 ≤ MulAction.stabilizer G (π x0) := by
    intro g hg
    rw [MulAction.mem_stabilizer_iff] at hg ⊢
    rw [← hπ, hg]
  rw [hx0] at hle1
  have hle2 : MulAction.stabilizer G y ≤ Gc := (hstab y).1
  have hmul := Subgroup.relIndex_mul_relIndex _ _ _ hle1 hle2
  simp only [F, hx0]
  rw [← hmul]
  push_cast
  ring

end GlobalTheory.OrbitCounting
end

section

namespace GlobalTheory

theorem finsupp_vanishing_on_equiv_compl_prod :
    ∀ {I : Type} (S : Finset I) (n : ℕ),
    ∃ e : {l : I →₀ (Fin n → ℤ) // ∀ v ∈ S, l v = 0} ≃ ({i : I // i ∉ S} →₀ (Fin n → ℤ)),
      ∀ (M : Type) [CommMonoid M] (r : I → (Fin n → ℤ) → M), (∀ i, r i 0 = 1) →
        ∀ l, (e l).prod (fun i v => r i.1 v) = l.1.prod r := by
  intro I S n
  classical
  refine ⟨{
    toFun := fun l => l.1.subtypeDomain (· ∉ S)
    invFun := fun l' => ⟨l'.embDomain (Function.Embedding.subtype _), by
      intro v hv
      apply Finsupp.embDomain_notin_range
      rintro ⟨i, rfl⟩
      exact i.2 hv⟩
    left_inv := by
      rintro ⟨l, hl⟩
      apply Subtype.ext
      refine Finsupp.ext fun v => ?_
      by_cases hv : v ∈ S
      · show Finsupp.embDomain _ _ v = l v
        rw [Finsupp.embDomain_notin_range, hl v hv]
        rintro ⟨i, rfl⟩
        exact i.2 hv
      · show Finsupp.embDomain _ _ v = l v
        have := Finsupp.embDomain_apply_self (Function.Embedding.subtype (· ∉ S))
          (l.subtypeDomain (· ∉ S)) ⟨v, hv⟩
        simpa using this
    right_inv := by
      intro l'
      refine Finsupp.ext fun i => ?_
      rw [Finsupp.subtypeDomain_apply]
      exact Finsupp.embDomain_apply_self (Function.Embedding.subtype (· ∉ S)) l' i }, ?_⟩
  intro M _ r _ l
  obtain ⟨l, hl⟩ := l
  show (l.subtypeDomain (· ∉ S)).prod (fun i v => r i.1 v) = l.prod r
  apply Finsupp.prod_subtypeDomain_index
  intro x hx hxS
  exact (Finsupp.mem_support_iff.mp hx) (hl x hxS)

end GlobalTheory
end

section

namespace GlobalTheory.EigenvectorOfSum

theorem eigenvector_mem_of_sum_mem {L Y I α : Type} [Field L] [AddCommGroup Y] [Module L Y]
    (T : I → Y →ₗ[L] Y) (χ : α → I → L) (hχ : Function.Injective χ) (U : Submodule L Y)
    (hU : ∀ (g : I), ∀ y ∈ U, (T g : Y → Y) y ∈ U) (S : Finset α) (y : α → Y)
    (hy : ∀ a ∈ S, ∀ (g : I), (T g : Y → Y) (y a) = χ a g • y a)
    (hs : ∑ a ∈ S, y a ∈ U) : ∀ a ∈ S, y a ∈ U := by
  classical
  induction S using Finset.strongInduction generalizing y with
  | H S ih =>
  intro a ha
  by_cases hex : ∃ b ∈ S, b ≠ a
  · obtain ⟨b, hb, hba⟩ := hex
    obtain ⟨g, hg⟩ : ∃ g, χ a g ≠ χ b g := by
      by_contra hcon
      simp only [ne_eq, not_exists, not_not] at hcon
      exact hba (hχ (funext hcon)).symm
    set y' : α → Y := fun c => (χ c g - χ b g) • y c with hyq
    have hy' : ∀ c ∈ S.erase b, ∀ g', (T g' : Y → Y) (y' c) = χ c g' • y' c := by
      intro c hc g'
      rw [hyq, map_smul, hy c (Finset.mem_of_mem_erase hc) g', smul_comm]
    have hs' : ∑ c ∈ S.erase b, y' c ∈ U := by
      have h1 : (T g : Y → Y) (∑ c ∈ S, y c) - χ b g • ∑ c ∈ S, y c ∈ U :=
        U.sub_mem (hU g _ hs) (U.smul_mem _ hs)
      have h2 : (T g : Y → Y) (∑ c ∈ S, y c) - χ b g • ∑ c ∈ S, y c = ∑ c ∈ S.erase b, y' c := by

        rw [map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_erase_add _ _ hb]
        have hb0 : (T g : Y → Y) (y b) - χ b g • y b = 0 := by rw [hy b hb g, sub_self]
        rw [hb0, add_zero]
        refine Finset.sum_congr rfl fun c hc => ?_
        rw [hyq]
        dsimp only
        rw [sub_smul, hy c (Finset.mem_of_mem_erase hc) g]
      rwa [h2] at h1
    have hmem := ih (S.erase b) (Finset.erase_ssubset hb) y' hy' hs' a
      (Finset.mem_erase.2 ⟨hba.symm, ha⟩)
    have hne : χ a g - χ b g ≠ 0 := sub_ne_zero.2 hg
    have h3 := U.smul_mem (χ a g - χ b g)⁻¹ hmem
    rwa [hyq, smul_smul, inv_mul_cancel₀ hne, one_smul] at h3
  · simp only [ne_eq, not_exists, not_and, not_not] at hex
    have hS : S = {a} := Finset.eq_singleton_iff_unique_mem.2 ⟨ha, hex⟩
    subst hS
    simpa using hs

end GlobalTheory.EigenvectorOfSum
end

section

universe u_1 u_2

namespace GlobalTheory.TranslateSum

theorem sum_translate_eq {G : Type u_1} {M : Type u_2} [Group G] [AddCommMonoid M]
    (H V : Subgroup G) (S : Finset G) (hS : ∀ s ∈ S, s ∈ H)
    (huniq : ∀ h ∈ H, ∃! s : G, s ∈ S ∧ s⁻¹ * h ∈ V) (f : G → M)
    (hf : ∀ (g v : G), v ∈ H → v ∈ V → f (g * v) = f g) :
    ∀ h ∈ H, ∑ s ∈ S, f (h * s) = ∑ s ∈ S, f s := by
  intro h hh
  have hex : ∀ s ∈ S, ∃ t : G, t ∈ S ∧ t⁻¹ * (h * s) ∈ V := fun s hs =>
    (huniq (h * s) (H.mul_mem hh (hS s hs))).exists
  choose φ hφS hφV using hex
  refine Finset.sum_bij φ hφS ?_ ?_ ?_
  · intro s hs t ht hst
    have h1 : s⁻¹ * t ∈ V := by
      have := V.mul_mem (V.inv_mem (hφV s hs)) (hφV t ht)
      rw [hst] at this
      have e : ((φ t ht)⁻¹ * (h * s))⁻¹ * ((φ t ht)⁻¹ * (h * t)) = s⁻¹ * t := by group
      rwa [e] at this
    have h2 : t⁻¹ * t ∈ V := by
      rw [inv_mul_cancel]; exact V.one_mem
    exact (huniq t (hS t ht)).unique ⟨hs, h1⟩ ⟨ht, h2⟩
  · intro u hu
    obtain ⟨s, hs, hsV⟩ := (huniq (h⁻¹ * u) (H.mul_mem (H.inv_mem hh) (hS u hu))).exists
    refine ⟨s, hs, ?_⟩
    have h1 : u⁻¹ * (h * s) ∈ V := by
      have := V.inv_mem hsV
      have e : (s⁻¹ * (h⁻¹ * u))⁻¹ = u⁻¹ * (h * s) := by group
      rwa [e] at this
    exact (huniq (h * s) (H.mul_mem hh (hS s hs))).unique ⟨hφS s hs, hφV s hs⟩ ⟨hu, h1⟩
  · intro s hs
    have hm : (φ s hs)⁻¹ * (h * s) ∈ H :=
      H.mul_mem (H.inv_mem (hS _ (hφS s hs))) (H.mul_mem hh (hS s hs))
    have := hf (φ s hs) _ hm (hφV s hs)
    rwa [mul_inv_cancel_left] at this

end GlobalTheory.TranslateSum
end

section

theorem GlobalTheory.cauchy_product_dvd_pow : ∀ {R : Type} [CommRing R] (x : R) (α β : ℕ → R) (A B : R), (∀ r : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀, x ^ r ∣ A - ∑ p ∈ Finset.range n, α p) → (∀ r : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀, x ^ r ∣ B - ∑ q ∈ Finset.range n, β q) → ∀ r : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀, x ^ r ∣ A * B - ∑ k ∈ Finset.range n, ∑ p ∈ Finset.range (k + 1), α p * β (k - p) := by
  intro R _ x α β A B hA hB r
  obtain ⟨NA, hNA⟩ := hA r
  obtain ⟨NB, hNB⟩ := hB r
  have hα : ∀ p ≥ NA, x ^ r ∣ α p := by
    intro p hp
    have h1 := hNA p hp
    have h2 := hNA (p + 1) (by omega)
    have e : α p = (A - ∑ i ∈ Finset.range p, α i) - (A - ∑ i ∈ Finset.range (p + 1), α i) := by
      rw [Finset.sum_range_succ]; ring
    rw [e]; exact dvd_sub h1 h2
  refine ⟨NA + NB, fun n hn => ?_⟩
  have key : ∑ k ∈ Finset.range n, ∑ p ∈ Finset.range (k + 1), α p * β (k - p)
      = ∑ p ∈ Finset.range n, α p * ∑ q ∈ Finset.range (n - p), β q := by
    rw [Finset.sum_range_diag_flip n (fun p q => α p * β q)]
    simp only [Finset.mul_sum]
  have hsplit : A * B - ∑ k ∈ Finset.range n, ∑ p ∈ Finset.range (k + 1), α p * β (k - p)
      = (A - ∑ p ∈ Finset.range n, α p) * B
        + ∑ p ∈ Finset.range n, α p * (B - ∑ q ∈ Finset.range (n - p), β q) := by
    rw [key, Finset.sum_congr rfl (fun p _ => mul_sub (α p) B _), Finset.sum_sub_distrib,
      ← Finset.sum_mul]
    ring
  rw [hsplit]
  refine dvd_add (dvd_mul_of_dvd_left (hNA n (by omega)) _) (Finset.dvd_sum fun p _ => ?_)
  by_cases hp' : NA ≤ p
  · exact dvd_mul_of_dvd_left (hα p hp') _
  · exact dvd_mul_of_dvd_right (hNB _ (by omega)) _
end

section

namespace GlobalTheory

theorem eq_of_nodup_sum_multiset_of_eq (ι : Type) [Fintype ι] [DecidableEq ι]
    (B : ι → Multiset ℂ) (h : (∑ i, B i).Nodup) (i j : ι) (hi : B i ≠ 0) (hij : B i = B j) :
    i = j := by
  by_contra hne
  have hle : B i + B j ≤ ∑ k, B k := by
    rw [← Finset.sum_pair hne]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have hnd : (B i + B j).Nodup := Multiset.nodup_of_le hle h
  rw [← hij] at hnd
  obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hi
  exact Multiset.disjoint_left.1 (Multiset.nodup_add.1 hnd).2.2 ha ha

end GlobalTheory
end

section

namespace GlobalTheory.UltrametricSum

theorem ultra_sum_le {R : Type} [inst : CommRing R] (a : R → ℝ) (h0 : a (0 : R) = (0 : ℝ))
    (hadd : ∀ (x y : R), a (x + y) ≤ Max.max (a x) (a y)) {ι : Type} (s : Finset ι) (f : ι → R)
    (c : ℝ) (hc : (0 : ℝ) ≤ c) (h : ∀ i ∈ s, a (f i) ≤ c) : a (∑ i ∈ s, f i) ≤ c := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, h0]; exact hc
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact (hadd _ _).trans (max_le (h j (Finset.mem_insert_self _ _))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))

end GlobalTheory.UltrametricSum
end

section

universe u_1

namespace GlobalTheory.AddMulInvMembership

theorem add_mul_inv_mem :
    (let d1 : {K : Type u_1} → [inst : Field K] → Subring K → K → K → Prop :=
      @(fun {K : Type u_1} [Field K] (S : Subring K) (π a : K) ↦ a * π⁻¹ ∈ S);
    ∀ {K : Type u_1} [inst : Field K] [StarRing K] {S : Subring K} {π a b : K},
      d1 S π a → d1 S π b → d1 S π (a + b)) := by
  intro d1 K _ _ S π a b ha hb
  show (a + b) * π⁻¹ ∈ S
  rw [add_mul]
  exact S.add_mem ha hb

end GlobalTheory.AddMulInvMembership
end
