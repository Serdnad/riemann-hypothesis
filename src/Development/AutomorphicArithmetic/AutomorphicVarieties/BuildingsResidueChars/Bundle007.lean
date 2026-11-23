module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.FibAbs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.GqIndex
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.EvenVal
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.LevelTwoFiniteIndex

@[expose] public section

section

open MulAction

private theorem conj_memS {G : Type} [Group G] {S : Subgroup G} (hc : ∀ a b : G, a * b * a⁻¹ * b⁻¹ ∈ S)
    {s : G} (hs : s ∈ S) (a : G) : a * s * a⁻¹ ∈ S := by
  have h : a * s * a⁻¹ = (a * s * a⁻¹ * s⁻¹) * s := by group
  rw [h]
  exact S.mul_mem (hc a s) hs

private theorem mem_orb {G : Type} [Group G] (S U : Subgroup G) (x : G) (y : G ⧸ U) :
    y ∈ orbit S (x : G ⧸ U) ↔ ∃ s ∈ S, y = ((s * x : G) : G ⧸ U) := by
  constructor
  · rintro ⟨⟨s, hs⟩, rfl⟩
    exact ⟨s, hs, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨⟨s, hs⟩, rfl⟩

private theorem sup_act {G : Type} [Group G] {S U : Subgroup G} (hc : ∀ a b : G, a * b * a⁻¹ * b⁻¹ ∈ S)
    {g : G} (hg : g ∈ S ⊔ U) (x : G) {y : G ⧸ U} (hy : y ∈ orbit S (x : G ⧸ U)) :
    g • y ∈ orbit S (x : G ⧸ U) := by
  haveI : S.Normal := ⟨fun n hn a => conj_memS hc hn a⟩
  rw [← SetLike.mem_coe, Subgroup.normal_mul, Set.mem_mul] at hg
  obtain ⟨s, hs, u, hu, rfl⟩ := hg
  obtain ⟨s₀, hs₀, rfl⟩ := (mem_orb S U x y).1 hy
  refine (mem_orb S U x _).2 ⟨s * (u * s₀ * x * u⁻¹ * x⁻¹), S.mul_mem hs ?_, ?_⟩
  · convert S.mul_mem (conj_memS hc hs₀ u) (hc u x) using 1
    group
  · rw [MulAction.Quotient.smul_mk, QuotientGroup.eq, smul_eq_mul]
    convert U.inv_mem hu using 1
    group

private theorem phi_out {G : Type} [Group G] (U : Subgroup G) (Φ : G → ℂ) (hΦu : ∀ u ∈ U, ∀ g, Φ (g * u) = Φ g) (g : G) :
    Φ ((g : G ⧸ U).out) = Φ g := by
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U g
  rw [hu, hΦu _ u.2]

theorem UpperTheory.orbitalFiber_sum_over_fibers :
    UpperTheory.V.Z.Sym.Glob.Fib.SumFib := by
  intro Γ G I _ _ _ ι S U' Γ₀ x Φ hc hN hΦl hΦu hT hdisj hcov
  classical
  let Γ' : Subgroup Γ := Subgroup.comap ι (S ⊔ U')
  letI A : MulAction Γ (G ⧸ U') := MulAction.compHom _ ι
  letI B : MulAction Γ' (G ⧸ U') := MulAction.compHom _ (ι.comp Γ'.subtype)
  let k : G ⧸ U' → ℂ := fun y => Φ y.out
  let ki : I → G ⧸ U' → ℂ := fun i => (orbit S (x i : G ⧸ U')).indicator k
  have hsmul : ∀ (h : Γ) (g : G), h • (g : G ⧸ U') = ((ι h * g : G) : G ⧸ U') := fun h g => rfl
  have hk : ∀ g : G, k g = Φ g := phi_out U' Φ hΦu
  have hkinv : ∀ (h : Γ) (y : G ⧸ U'), k (h • y) = k y := by
    intro h y
    refine QuotientGroup.induction_on y fun g => ?_
    rw [hsmul, hk, hk, hΦl]
  have hki_mem : ∀ i y, ki i y ≠ 0 → y ∈ orbit S (x i : G ⧸ U') :=
    fun i y h => Set.mem_of_indicator_ne_zero h
  have hD := @UpperTheory.orbitalFiber_decomposition Γ (G ⧸ U') I _ A Γ₀ k (fun _ => Γ') (fun _ => G ⧸ U')
    (fun _ => inferInstance) (fun _ => B) (fun _ => Γ'.subtype) (fun _ => id) ki hN hkinv
    ?_ (fun _ _ _ => rfl) (fun _ => Function.injective_id) ?_ ?_ ?_ ?_
  · show UpperTheory.V.Z.Sym.gq Γ₀ k = ∑ i, UpperTheory.V.Z.Sym.gq (Γ₀.subgroupOf Γ') (ki i)
    rw [hD, finsum_eq_sum_of_fintype]
    rfl
  · obtain ⟨T, hT⟩ := hT
    refine ⟨T.image (fun g : G => (g : G ⧸ U')), fun y => ?_⟩
    refine QuotientGroup.induction_on y fun g _ => ?_
    obtain ⟨γ, s, hs, u, hu, rfl⟩ := hT g
    refine ⟨γ, (s : G ⧸ U'), Finset.mem_image_of_mem _ hs, ?_⟩
    rw [hsmul, QuotientGroup.eq]
    convert U'.inv_mem hu using 1
    group
  · intro i h y
    have hh : ι h ∈ S ⊔ U' := h.2
    have e : h • y = (ι h) • y := rfl
    have hmem : h • y ∈ orbit S (x i : G ⧸ U') ↔ y ∈ orbit S (x i : G ⧸ U') := by
      rw [e]
      constructor
      · intro hy'
        simpa using sup_act hc (Subgroup.inv_mem _ hh) (x i) hy'
      · intro hy
        exact sup_act hc hh (x i) hy
    show Set.indicator _ k (h • y) = Set.indicator _ k y
    by_cases hy : y ∈ orbit S (x i : G ⧸ U')
    · rw [Set.indicator_apply, Set.indicator_apply, if_pos (hmem.2 hy), if_pos hy]
      exact hkinv (h : Γ) y
    · rw [Set.indicator_apply, Set.indicator_apply, if_neg (mt hmem.1 hy), if_neg hy]
  · intro i y h
    exact (Set.indicator_of_mem (hki_mem i y h) k).symm
  · intro z
    refine QuotientGroup.induction_on z fun g hz => ?_
    obtain ⟨i, γ, s, hs, u, hu, rfl⟩ := hcov g
    have hy : ((s * x i : G) : G ⧸ U') ∈ orbit S (x i : G ⧸ U') := (mem_orb S U' _ _).2 ⟨s, hs, rfl⟩
    have hval : k ((s * x i : G) : G ⧸ U') = k ((ι γ * s * x i * u : G) : G ⧸ U') := by
      rw [hk, hk, hΦu _ hu, mul_assoc (ι γ) s, hΦl]
    refine ⟨i, ((s * x i : G) : G ⧸ U'), γ, ?_, ?_⟩
    · rw [show ki i _ = k _ from Set.indicator_of_mem hy k, hval]
      exact hz
    · show _ = γ • ((s * x i : G) : G ⧸ U')
      rw [hsmul, QuotientGroup.eq]
      convert U'.inv_mem hu using 1
      group
  · intro i j y y' h hy hy' he
    obtain ⟨s, hs, rfl⟩ := (mem_orb S U' _ _).1 (hki_mem i y hy)
    obtain ⟨s', hs', rfl⟩ := (mem_orb S U' _ _).1 (hki_mem j y' hy')
    change ((ι h * (s * x i) : G) : G ⧸ U') = ((s' * x j : G) : G ⧸ U') at he
    rw [QuotientGroup.eq] at he
    obtain ⟨u, hu_mem, hu_eq⟩ : ∃ u ∈ U', (ι h * (s * x i))⁻¹ * (s' * x j) = u := ⟨_, he, rfl⟩
    have hxj : x j = ι h * ((ι h)⁻¹ * s'⁻¹ * ι h * s) * x i * u := by
      rw [← hu_eq]
      group
    have e2 : ι h = s' * x j * u⁻¹ * (x i)⁻¹ * s⁻¹ := by
      rw [← hu_eq]
      group
    have hmid : (ι h)⁻¹ * s'⁻¹ * ι h * s ∈ S :=
      S.mul_mem (by simpa using conj_memS hc (S.inv_mem hs') (ι h)⁻¹) hs
    have key : ∀ X : G, s' * X * u⁻¹ * X⁻¹ * s⁻¹ ∈ S ⊔ U' := by
      intro X
      have e3 : s' * X * u⁻¹ * X⁻¹ * s⁻¹ = s' * (X * u⁻¹ * X⁻¹ * u⁻¹⁻¹) * u⁻¹ * s⁻¹ := by group
      rw [e3]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hs')
        (Subgroup.mem_sup_left (hc _ _))) (Subgroup.mem_sup_right (U'.inv_mem hu_mem)))
        (Subgroup.mem_sup_left (S.inv_mem hs))
    have hij := hdisj i j h _ hmid u hu_mem hxj
    subst hij
    refine ⟨rfl, ⟨h, ?_⟩, rfl⟩
    show ι h ∈ S ⊔ U'
    rw [e2]
    exact key _
end

section

open MulAction

theorem UpperTheory.orbitalFiber_pushforward :
    UpperTheory.V.Z.Sym.Glob.Fib.Push := by
  intro H X' X _ _ _ H₀ q k hN hq hH₀ hk hT hfin hidx
  classical
  let F : orbitRel.Quotient H X → Set X' := fun i => {y | q y = Quotient.out i}
  letI act : ∀ i : orbitRel.Quotient H X, MulAction (stabilizer H (Quotient.out i)) (F i) := fun i =>
    { smul := fun h y => ⟨(h : H) • (y : X'), by
          show q ((h : H) • (y : X')) = Quotient.out i
          rw [hq, show q (y : X') = Quotient.out i from y.2]
          exact mem_stabilizer_iff.mp h.2⟩
      one_smul := fun y => Subtype.ext (one_smul H (y : X'))
      mul_smul := fun a b y => Subtype.ext (mul_smul (a : H) (b : H) (y : X')) }
  have hD := UpperTheory.orbitalFiber_decomposition H X' (orbitRel.Quotient H X) H₀ k
    (fun i => stabilizer H (Quotient.out i)) (fun i => F i)
    (fun i => (stabilizer H (Quotient.out i)).subtype) (fun i y => (y : X'))
    (fun i y => k (y : X')) hN hk hT
    (fun i h y => rfl) (fun i => Subtype.val_injective)
    (fun i h y => hk (h : H) (y : X')) (fun i y _ => rfl) ?cover ?disj
  case cover =>
    intro x hx
    obtain ⟨g, hg⟩ := orbitRel_apply.mp (Quotient.mk_out (s := orbitRel H X) (q x))
    refine ⟨Quotient.mk _ (q x), ⟨g • x, ?_⟩, g⁻¹, ?_, ?_⟩
    · show q (g • x) = _
      rw [hq]; exact hg
    · show k (g • x) ≠ 0
      rw [hk]; exact hx
    · show x = g⁻¹ • g • x
      rw [inv_smul_smul]
  case disj =>
    intro i j y y' h _ _ he
    have hqe : h • Quotient.out i = Quotient.out j := by
      have h1 : q (h • (y : X')) = q (y' : X') := congrArg q he
      rw [hq, show q (y : X') = Quotient.out i from y.2,
        show q (y' : X') = Quotient.out j from y'.2] at h1
      exact h1
    have hij : i = j := by
      rw [← Quotient.out_eq i, ← Quotient.out_eq j]
      exact (Quotient.sound (orbitRel_apply.mpr ⟨h, hqe⟩)).symm
    subst hij
    refine ⟨rfl, ?_⟩
    rw [Subgroup.range_subtype]
    exact mem_stabilizer_iff.mpr hqe
  rw [hD]
  conv_rhs => unfold UpperTheory.V.Z.Sym.gq
  refine finsum_congr (fun i => ?_)
  beta_reduce
  by_cases hz : ∃ y : X', q y = Quotient.out i ∧ k y ≠ 0
  · obtain ⟨y₀, hy₀, hk₀⟩ := hz
    have hind : (Subgroup.comap (stabilizer H (Quotient.out i)).subtype H₀).index ≠ 0 := by
      have := hidx y₀ hk₀
      rw [hy₀] at this
      exact this
    rw [UpperTheory.orbitalFiber_pushforward_eq_zero _ (F i) _ _ hind
      (fun z hz y => Subtype.ext (hH₀ (z : H) (Subgroup.mem_comap.mp hz) (y : X')))
      (fun h y => hk (h : H) (y : X'))
      (((hfin (Quotient.out i)).preimage Subtype.val_injective.injOn).subset
        (fun y hy => ⟨y.2, hy⟩))]
    rw [finsum_set_coe_eq_finsum_mem (f := k) (F i)]
    rfl
  · push_neg at hz
    have h0 : (∑ᶠ (y : X') (_ : q y = Quotient.out i), k y) = 0 := by
      apply finsum_eq_zero_of_forall_eq_zero
      intro y
      rw [finsum_eq_if]
      split_ifs with hy
      · exact hz y hy
      · rfl
    rw [h0, zero_div]
    unfold UpperTheory.V.Z.Sym.gq
    apply finsum_eq_zero_of_forall_eq_zero
    intro o
    beta_reduce
    rw [hz _ (Quotient.out o).2, zero_div]
end

section

open MulAction in
theorem UpperTheory.orbitalFiber_single :
    UpperTheory.V.Z.Sym.Glob.Fib.OneFib := by
  intro Γ G _ _ ι S U' Γ₁ Γ₀ x Φ hcomm hΓS hN htriv hΦl hΦr hTex hst hrel hcard
  classical
  haveI hSn : S.Normal := ⟨fun n hn g => by
    convert S.mul_mem (hcomm g n) hn using 1
    group⟩
  set C := Subgroup.comap ι (S ⊔ U') with hC
  set f := (orbit ↥S (x : G ⧸ U')).indicator fun y => Φ (Quotient.out y) with hf
  have hΓC : Γ₁ ≤ C := fun a ha =>
    Subgroup.mem_comap.mpr ((le_sup_left : S ≤ S ⊔ U') (Subgroup.mem_comap.mp (hΓS ha)))
  let j : C →* G := ι.comp C.subtype
  let φ : Γ₁ →* C := Subgroup.inclusion hΓC
  have hclos : ∀ g ∈ S ⊔ U', ∀ y ∈ orbit ↥S (x : G ⧸ U'), g • y ∈ orbit ↥S (x : G ⧸ U') := by
    intro g hg y hy
    obtain ⟨s, hs, u, hu, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hg
    obtain ⟨⟨s', hs'⟩, rfl⟩ := hy
    refine ⟨⟨s * (u * (s' * x) * u⁻¹ * (s' * x)⁻¹) * s', S.mul_mem (S.mul_mem hs (hcomm _ _)) hs'⟩, ?_⟩
    show ((s * (u * (s' * x) * u⁻¹ * (s' * x)⁻¹) * s' * x : G) : G ⧸ U') = ((s * u * (s' * x) : G) : G ⧸ U')
    rw [QuotientGroup.eq]
    have he : (s * (u * (s' * x) * u⁻¹ * (s' * x)⁻¹) * s' * x)⁻¹ * (s * u * (s' * x)) = u := by group
    rw [he]
    exact hu
  have hinv : ∀ (h : C) (y : G ⧸ U'), f (j h • y) = f y := by
    intro h y
    have hg : ι h.1 ∈ S ⊔ U' := h.2
    change f (ι h.1 • y) = f y
    by_cases hy : y ∈ orbit ↥S (x : G ⧸ U')
    · have hy' := hclos _ hg y hy
      rw [hf, Set.indicator_of_mem hy', Set.indicator_of_mem hy]
      obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U' (ι h.1 * Quotient.out y)
      have hyy : ι h.1 • y = ((ι h.1 * Quotient.out y : G) : G ⧸ U') := by
        conv_lhs => rw [← QuotientGroup.out_eq' y]
        rfl
      rw [hyy, hu, hΦr _ u.2, hΦl]
    · have hy' : ι h.1 • y ∉ orbit ↥S (x : G ⧸ U') := fun hm => hy (by
        have := hclos _ (inv_mem hg) _ hm
        rwa [inv_smul_smul] at this)
      rw [hf, Set.indicator_apply, if_neg hy', Set.indicator_apply, if_neg hy]
  have hfin : ∃ T' : Finset (G ⧸ U'), ∀ y, f y ≠ 0 → ∃ h : C, ∃ x' ∈ T', y = j h • x' := by
    obtain ⟨T, hT⟩ := hTex
    refine ⟨T.image (QuotientGroup.mk : G → G ⧸ U'), ?_⟩
    intro y hy
    obtain ⟨⟨s, hs⟩, rfl⟩ := Set.mem_of_indicator_ne_zero hy
    obtain ⟨h, hh, t, ht, u, hu, he⟩ := hT s hs
    refine ⟨⟨h, hΓC hh⟩, (t : G ⧸ U'), Finset.mem_image_of_mem QuotientGroup.mk ht, ?_⟩
    show ((s * x : G) : G ⧸ U') = ((ι h * t : G) : G ⧸ U')
    rw [he, QuotientGroup.eq]
    rw [show (ι h * t * u)⁻¹ * (ι h * t) = u⁻¹ by group]
    exact inv_mem hu
  have hsup : φ.range ⊔ Γ₀.subgroupOf C = (Γ₁ ⊔ Γ₀).subgroupOf C := by
    ext z
    rw [Subgroup.mem_sup_of_normal_right, Subgroup.mem_subgroupOf, Subgroup.mem_sup_of_normal_right]
    constructor
    · rintro ⟨a, ⟨a', rfl⟩, b, hb, rfl⟩
      exact ⟨a'.1, a'.2, b.1, Subgroup.mem_subgroupOf.mp hb, rfl⟩
    · rintro ⟨a, ha, b, hb, hab⟩
      have hbC : b ∈ C := by
        have hb' : b = a⁻¹ * (z : Γ) := by rw [← hab]; group
        rw [hb']
        exact C.mul_mem (C.inv_mem (hΓC ha)) z.2
      exact ⟨φ ⟨a, ha⟩, ⟨⟨a, ha⟩, rfl⟩, ⟨b, hbC⟩, Subgroup.mem_subgroupOf.mpr hb, Subtype.ext hab⟩
  have hidx : (φ.range ⊔ Γ₀.subgroupOf C).index = (Γ₁ ⊔ Γ₀).relIndex C := by
    rw [hsup]
    rfl
  have key := UpperTheory.V.Z.Sym.Tf.gqIndex Γ₁ C G φ j (Γ₀.subgroupOf C) U' f
    inferInstance (fun z hz y => htriv z.1 (Subgroup.mem_subgroupOf.mp hz) y)
    (by rw [hidx]; exact hrel) hinv hfin
    (fun y _ => by
      rw [← Subgroup.comap_comap]
      exact Subgroup.relIndex_comap_ne_zero _ (hst y))
  have e1 : UpperTheory.V.Z.Sym.gqOn (ι.comp Γ₁.subtype) (Γ₀.subgroupOf Γ₁) U' f =
      UpperTheory.V.Z.Sym.gqOn (j.comp φ) (Subgroup.comap φ (Γ₀.subgroupOf C)) U' f := rfl
  have hb : UpperTheory.V.Z.Sym.gqOn (ι.comp Γ₁.subtype) (Γ₀.subgroupOf Γ₁) U' f =
      ↑(Nat.card ↥(Γ₀.subgroupOf Γ₁)) * UpperTheory.V.Z.Sym.gqOn (ι.comp Γ₁.subtype) ⊥ U' f := by
    letI := MulAction.compHom (G ⧸ U') (ι.comp Γ₁.subtype)
    exact (UpperTheory.orbitalFiber_of_bot Γ₁ (G ⧸ U') (Γ₀.subgroupOf Γ₁) f).2 hcard
      (fun z hz y => htriv z.1 (Subgroup.mem_subgroupOf.mp hz) y)
  rw [← hb, e1, key, hidx]
end

section

open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob Matrix

private theorem star_alg {K : Type} [Field K] {Δ : K} (x : K) :
    star (algebraMap K (Lsq K Δ) x) = algebraMap K (Lsq K Δ) x := by
  ext <;> simp

private theorem sigL_mul' {K : Type} [Field K] {Δ τ : K} (a b : EL Δ τ) :
    sigL (a * b) = sigL a * sigL b := by
  ext <;> simp [sigL, star_alg] <;> ring

private theorem sigL_one' {K : Type} [Field K] {Δ τ : K} : sigL (1 : EL Δ τ) = 1 := by
  apply QuadraticAlgebra.ext
  · exact star_one (Lsq K Δ)
  · exact star_zero (Lsq K Δ)

private theorem fixed_scalar {K : Type} [Field K] [CharZero K] {Δ τ : K} (r : EL Δ τ)
    (h1 : sigL r = r) (h2 : star r = r) : ∃ p : K, ∀ x : EL Δ τ, r * x = p • x := by
  have z : ∀ y : K, -y = y → y = 0 := fun y h => by
    have h' : (2 : K) * y = 0 := by linear_combination -h
    simpa using h'
  have e1 := congrArg (fun w : EL Δ τ => w.re.im) h1
  have e2 := congrArg (fun w : EL Δ τ => w.im.re) h2
  have e3 := congrArg (fun w : EL Δ τ => w.im.im) h2
  simp [sigL] at e1 e2 e3
  have hr : algebraMap K (EL Δ τ) r.re.re = r := by
    rw [show algebraMap K (EL Δ τ) r.re.re = ⟨⟨r.re.re, 0⟩, 0⟩ from rfl]
    ext <;> simp [z _ e1, z _ e2, z _ e3]
  refine ⟨r.re.re, fun x => ?_⟩
  calc r * x = algebraMap K (EL Δ τ) r.re.re * x := by rw [hr]
    _ = r.re.re • x := (Algebra.smul_def _ _).symm

theorem UpperTheory.hermitian_datum_unique_up_to_scalar :
    ∀ (K : Type) [Field K] [CharZero K] (Δ τ c c' : K) (d m m' : EL Δ τ), IsDat c d m → IsDat c' d m' → ∃ t : Kˣ, m' = (t : K) • m := by
  intro K _ _ Δ τ c c' d m m' hm hm'
  obtain ⟨u, hu⟩ := hm.m_unit
  set r : EL Δ τ := m' * ↑u⁻¹ with hrdef
  have hrm : r * m = m' := by
    rw [hrdef, ← hu, mul_assoc, Units.inv_mul, mul_one]
  have hsu : IsUnit (sigL m) := by
    refine IsUnit.of_mul_eq_one (sigL (↑u⁻¹ : EL Δ τ)) ?_
    rw [← sigL_mul', ← hu, Units.mul_inv, sigL_one']
  have hs : sigL r = r := by
    have e : sigL r * sigL m = r * sigL m := by
      rw [← sigL_mul', hrm, hm'.m_sig, hm.m_sig, ← mul_assoc, ← mul_assoc, hrm]
    exact hsu.mul_left_injective e
  have hsm : star m = sigL m := by
    conv_lhs => rw [← hm.m_star]
    exact star_star _
  have hsm' : star m' = sigL m' := by
    conv_lhs => rw [← hm'.m_star]
    exact star_star _
  have hst : star r = r := by
    have e : star r * sigL m = r * sigL m :=
      calc star r * sigL m = star r * star m := by rw [hsm]
        _ = star (r * m) := (star_mul' r m).symm
        _ = star m' := by rw [hrm]
        _ = sigL m' := hsm'
        _ = sigL r * sigL m := by rw [← sigL_mul', hrm]
        _ = r * sigL m := by rw [hs]
    exact hsu.mul_left_injective e
  obtain ⟨p, hp⟩ := fixed_scalar r hs hst
  have hm'p : m' = p • m := by rw [← hp, hrm]
  have hp0 : p ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hm'p
    exact hm'.m_unit.ne_zero hm'p
  exact ⟨Units.mk0 p hp0, hm'p⟩
end

section

open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob Matrix

private lemma star_mulVec_fin_three {L : Type} [CommRing L] [StarRing L] (N : Matrix (Fin 3) (Fin 3) L) (v : Fin 3 → L) :
    star (N *ᵥ v) = N.map star *ᵥ star v := by
  funext i
  have h := RingHom.map_mulVec (starRingEnd L) N v i
  exact h

theorem UpperTheory.semilinear_coords_eq_mulVec_star :
    ∀ (K : Type) [Field K] (Δ τ : K) (d : EL Δ τ) (A N : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) (e v : Fin 3 → Lsq K Δ),
        A * N.map star = N * A → A *ᵥ star e = e → A *ᵥ star v = d.re • v + d.im • (N *ᵥ v) →
        N *ᵥ (N *ᵥ v) = algebraMap K (Lsq K Δ) τ • (N *ᵥ v) - v → ∀ x : Sp Δ τ,
        (semi d x).1 • e + (semi d x).2.re • v + (semi d x).2.im • (N *ᵥ v) = A *ᵥ star (x.1 • e + x.2.re • v + x.2.im • (N *ᵥ v)) := by
  intro K _ Δ τ d A N e v hAN he hv hN x
  have hNv : A *ᵥ star (N *ᵥ v) = d.re • (N *ᵥ v) + d.im • (algebraMap K (Lsq K Δ) τ • (N *ᵥ v) - v) := by
    rw [star_mulVec_fin_three, Matrix.mulVec_mulVec, hAN, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_add,
      Matrix.mulVec_smul, Matrix.mulVec_smul, hN]
  have hs : star (x.1 • e + x.2.re • v + x.2.im • (N *ᵥ v)) =
      star x.1 • star e + star x.2.re • star v + star x.2.im • star (N *ᵥ v) := by
    funext i
    simp [mul_comm]
  rw [hs, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul, he, hv, hNv]
  funext i
  simp only [semi, sigL, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
  simp
  ring
end

section

open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob Matrix

private theorem vecMul_of_three {R : Type} [CommRing R] (a b c : R) (e v w : Fin 3 → R) :
    ![a, b, c] ᵥ* (Matrix.of ![e, v, w]) = a • e + b • v + c • w := by
  ext j
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three]

theorem UpperTheory.exists_linearEquiv_sp_of_isUnit_det_basis :
    ∀ (K : Type) [Field K] (Δ τ : K) (e v w : Fin 3 → Lsq K Δ), IsUnit (Matrix.of ![e, v, w]).det →
        ∃ P : Sp Δ τ ≃ₗ[Lsq K Δ] (Fin 3 → Lsq K Δ), ∀ x : Sp Δ τ, P x = x.1 • e + x.2.re • v + x.2.im • w := by
  intro K _ Δ τ e v w h
  set M : Matrix (Fin 3) (Fin 3) (Lsq K Δ) := Matrix.of ![e, v, w] with hM
  have h1 : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M h
  have h2 : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M h
  refine ⟨{ toFun := fun x => x.1 • e + x.2.re • v + x.2.im • w
            map_add' := ?_
            map_smul' := ?_
            invFun := fun y => ((y ᵥ* M⁻¹) 0, ⟨(y ᵥ* M⁻¹) 1, (y ᵥ* M⁻¹) 2⟩)
            left_inv := ?_
            right_inv := ?_ }, fun x => rfl⟩
  · intro x y
    simp only [Prod.fst_add, Prod.snd_add, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, add_smul]
    abel
  · intro r x
    simp [mul_smul, smul_add]
  · intro x
    have : (x.1 • e + x.2.re • v + x.2.im • w) ᵥ* M⁻¹ = ![x.1, x.2.re, x.2.im] := by
      rw [← vecMul_of_three, ← hM, Matrix.vecMul_vecMul, h1, Matrix.vecMul_one]
    simp only [this]
    ext <;> simp
  · intro y
    have : ((y ᵥ* M⁻¹) 0) • e + ((y ᵥ* M⁻¹) 1) • v + ((y ᵥ* M⁻¹) 2) • w = (y ᵥ* M⁻¹) ᵥ* M := by
      rw [hM, ← vecMul_of_three]
      congr 1
      funext i; fin_cases i <;> rfl
    simp only [this]
    rw [Matrix.vecMul_vecMul, h2, Matrix.vecMul_one]
end
