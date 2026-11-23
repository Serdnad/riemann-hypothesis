module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
public import Mathlib.RingTheory.Length
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle001
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle002
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.CocycleZeroMemInvariants
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.SelmerDuality.LengthExact
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
public import Mathlib.Data.ENat.BigOperators
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Separation.CompletelyRegular

@[expose] public section

section

open ReciprocityTheory.Gal UpperTheory.V.Base

private theorem relIndex_inf_dvd {G : Type} [Group G] (U' U D : Subgroup G) [U'.Normal] :
    (U' ⊓ D).relIndex (U ⊓ D) ∣ U'.relIndex U := by
  have e : (U' ⊓ D).relIndex (U ⊓ D) = U'.relIndex (U ⊓ D) := by
    unfold Subgroup.relIndex
    congr 1
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, x.2.2⟩⟩
  rw [e]
  have k : ∀ K : Subgroup G, U'.relIndex K = Nat.card (K.map (QuotientGroup.mk' U')) := fun K => by
    rw [← Subgroup.relIndex_ker, QuotientGroup.ker_mk']
  rw [k, k]
  exact Subgroup.card_dvd_of_le (Subgroup.map_mono inf_le_left)

private theorem eq_zero_of_nsmul {R N : Type} [CommRing R] [AddCommGroup N] [Module R N] {n : ℕ}
    (hn : IsUnit (n : R)) {x : N} (hx : n • x = 0) : x = 0 := by
  rw [← Nat.cast_smul_eq_nsmul R] at hx
  exact (hn.smul_eq_zero).1 hx

theorem UpperTheory.V.Base.selUnit :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M] [Module R M]
      [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M), ContAction ρ → ∀ (U' U : Subgroup G) [U'.Normal] (h : U' ≤ U), IsOpen (U'.subgroupOf U : Set U) →
      IsUnit (U'.relIndex U : R) → ∀ (𝒟 : Set (Subgroup G)) (h𝒟 : ConjStable 𝒟),
      Function.Injective (selRes ρ h 𝒟) ∧ LinearMap.range (selRes ρ h 𝒟) = selEig ρ U' h𝒟 U 1 := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ hρ U' U _ h hop hu 𝒟 h𝒟
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have h0 : resU ρ h x.1 = 0 := congrArg Subtype.val hx
    exact Subtype.ext (eq_zero_of_nsmul hu (kerResSmul R G M ρ U' U h x.1 h0))
  · ext y
    rw [selEig, eig_one]
    constructor
    · rintro ⟨x, rfl⟩ g
      exact Subtype.ext (restriction_mem_invariant_H1 ρ h x.1 g)
    · intro hy
      have hy' : y.1 ∈ invariantsUnderSubgroupH1 ρ U U' := fun g => congrArg Subtype.val (hy g)
      have h1 := corInv R G M ρ hρ U' U h hop y.1 hy'
      rw [← Nat.cast_smul_eq_nsmul R] at h1
      obtain ⟨v, hv⟩ := hu.exists_left_inv
      have h2 := Submodule.smul_mem _ v h1
      rw [smul_smul, hv, one_smul] at h2
      obtain ⟨x, hx⟩ := h2
      have hxs : x ∈ LocSel ρ U 𝒟 := by
        rw [mem_locSel]
        intro D hD
        have hu' : IsUnit (((U' ⊓ D).relIndex (U ⊓ D) : ℕ) : R) :=
          isUnit_of_dvd_unit (Nat.cast_dvd_cast (relIndex_inf_dvd U' U D)) hu
        refine eq_zero_of_nsmul hu' (kerResSmul R G M ρ _ _ (inf_le_inf_right D h) _ ?_)
        rw [resU_resU, ← resU_resU ρ inf_le_left h, hx]
        exact mem_locSel.1 y.2 D hD
      exact ⟨⟨x, hxs⟩, Subtype.ext hx⟩
end

section

open ReciprocityTheory.Gal UpperTheory.V.Base

private theorem length_addMonoidHom_le_of_card_eq {R A B C X : Type} [CommRing R] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C] [AddCommGroup X] [Module R X]
    (f : A →ₗ[R] X) (j : B →ₗ[R] X) (hj : Function.Injective j) (g : B →ₗ[R] C)
    (h : ∀ x, g x = 0 → j x ∈ LinearMap.range f) :
    Module.length R B ≤ Module.length R A + Module.length R C := by
  have hex : Function.Exact (LinearMap.ker g).subtype g.rangeRestrict := by
    intro x
    constructor
    · intro hx
      refine ⟨⟨x, ?_⟩, rfl⟩
      have := congrArg Subtype.val hx
      simpa [LinearMap.mem_ker] using this
    · rintro ⟨y, rfl⟩
      apply Subtype.ext
      simpa using y.2
  rw [Module.length_eq_add_of_exact (LinearMap.ker g).subtype g.rangeRestrict
    (Submodule.subtype_injective _) g.surjective_rangeRestrict hex]
  gcongr
  · let φ : LinearMap.ker g →ₗ[R] LinearMap.range f :=
      (j.comp (LinearMap.ker g).subtype).codRestrict (LinearMap.range f) (fun x => h x x.2)
    have hφ : Function.Injective φ := by
      intro a b hab
      apply Subtype.ext
      apply hj
      exact congrArg Subtype.val hab
    calc Module.length R (LinearMap.ker g) ≤ Module.length R (LinearMap.range f) :=
          Module.length_le_of_injective φ hφ
      _ ≤ Module.length R A := Module.length_le_of_surjective f.rangeRestrict f.surjective_rangeRestrict
  · exact Module.length_le_of_injective (LinearMap.range g).subtype (Submodule.subtype_injective _)

theorem UpperTheory.V.Base.selDown :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M] [Module R M]
      [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M) (U' U : Subgroup G) [U'.Normal] (h : U' ≤ U) (𝒟 : Set (Subgroup G)) (h𝒟 : ConjStable 𝒟) (ι : Type) [Fintype ι] (D : ι → Subgroup G), (∀ i, D i ∈ 𝒟) →
      (∀ D' ∈ 𝒟, U ⊓ D' ≤ U' ∨ ∃ i, ∃ u ∈ U, ∀ x ∈ U ⊓ D', u⁻¹ * x * u ∈ D i) →
      Module.length R (selEig ρ U' h𝒟 U 1) ≤ Module.length R (LocSel ρ U 𝒟) + ∑ i, Module.length R (LinearMap.ker (resU ρ (inf_le_inf_right (D i) h))) + Module.length R (resCoker ρ h) := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ U' U _ h 𝒟 h𝒟 ι _ D hD hcov
  have hinv : ∀ x : selEig ρ U' h𝒟 U 1,
      ((x : LocSel ρ U' 𝒟) : H1U ρ U') ∈ invariantsUnderSubgroupH1 ρ U U' := by
    intro x
    rw [Representation.mem_invariants]
    intro u
    have := (mem_eig.mp x.2) u
    simpa [selRep, Representation.subrepresentation] using congrArg Subtype.val this
  let j : selEig ρ U' h𝒟 U 1 →ₗ[R] H1U ρ U' :=
    (LocSel ρ U' 𝒟).subtype.comp (selEig ρ U' h𝒟 U 1).subtype
  let g : selEig ρ U' h𝒟 U 1 →ₗ[R] resCoker ρ h :=
    (Submodule.mkQ _).comp (LinearMap.codRestrict (invariantsUnderSubgroupH1 ρ U U') j hinv)
  let A := Submodule.comap (resU ρ h) (LocSel ρ U' 𝒟)
  have hj : Function.Injective j := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact hab
  have hker : ∀ x, g x = 0 → j x ∈ LinearMap.range ((resU ρ h).comp A.subtype) := by
    intro x hx
    have hx' := (Submodule.Quotient.mk_eq_zero _).mp hx
    obtain ⟨y, hy⟩ := hx'
    refine ⟨⟨y, ?_⟩, hy⟩
    show resU ρ h y ∈ LocSel ρ U' 𝒟
    rw [hy]
    exact (x : LocSel ρ U' 𝒟).2
  refine le_trans (length_addMonoidHom_le_of_card_eq ((resU ρ h).comp A.subtype) j hj g hker) ?_
  gcongr
  exact selLocal R G M ρ U' U h 𝒟 ι D hD hcov
end

section

open ReciprocityTheory.Gal UpperTheory.V.Base

theorem UpperTheory.V.Base.selBase :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M] [Module R M]
      [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M) (O M' : Type) [CommRing O] [Algebra R O] [IsLocalRing R] [IsLocalRing O] [IsLocalHom (algebraMap R O)] [Module.Free R O]
      [Module.Finite R O] [AddCommGroup M'] [Module O M'] [Module R M'] [IsScalarTower R O M'] [TopologicalSpace M']
      [IsTopologicalAddGroup M'] [ContinuousConstSMul O M'] [DiscreteTopology M'] (ρ' : Representation O G M') (j : M →ₗ[R] M'),
      IsBaseChange O j → (∀ g m, j (ρ g m) = ρ' g (j m)) → ∀ (U : Subgroup G) (𝒟 : Set (Subgroup G)),
      Module.length O (LocSel ρ' U 𝒟) = Module.length R (LocSel ρ U 𝒟) * Module.length O (O ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R O)) := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ O M' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ρ' j hb hj U 𝒟
  exact length_of_isBaseChange (isBaseChange_selMap ρ ρ' j hj U hb 𝒟)
end

section

open ReciprocityTheory.Gal UpperTheory.V.Base

private theorem len_le_pi {R Z M ι : Type} [CommRing R] [AddCommGroup Z] [Module R Z] [AddCommGroup M] [Module R M]
    [Fintype ι] (ev : Z →ₗ[R] (ι → M)) (hev : Function.Injective ev) (W : Submodule R Z) (H : ι → Submodule R M)
    (hW : ∀ z ∈ W, ∀ i, ev z i ∈ H i) : Module.length R W ≤ ∑ i, Module.length R (H i) := by
  rw [← Module.length_pi_of_fintype]
  let φ : W →ₗ[R] (∀ i, H i) := LinearMap.pi fun i =>
    LinearMap.codRestrict (H i) ((LinearMap.proj i).comp (ev.comp W.subtype)) fun z => hW z.1 z.2 i
  refine Module.length_le_of_injective φ fun x y hxy => ?_
  refine Subtype.ext (hev (funext fun i => ?_))
  exact congrArg Subtype.val (congrFun hxy i)

private theorem len_abs {R Z K M ι : Type} [CommRing R] [AddCommGroup Z] [Module R Z] [AddCommGroup M] [Module R M]
    [AddCommGroup K] [Module R K] [Fintype ι] (hM : ∀ m : M, Module.length R (Submodule.span R {m}) ≠ ⊤)
    (ev : Z →ₗ[R] (ι → M)) (hev : Function.Injective ev) (π : Z →ₗ[R] K) (hπ : Function.Surjective π) (a : R)
    (ha : ∀ z, π (a • z) = 0) (H : Submodule R M) (hH : ∀ m, a • m = 0 → m ∈ H) :
    Module.length R K ≤ Fintype.card ι * Module.length R H := by
  have hZ : ∀ z : Z, Module.length R (Submodule.span R {z}) ≠ ⊤ := by
    intro z
    refine ne_top_of_le_ne_top ?_ (len_le_pi ev hev _ (fun i => Submodule.span R {ev z i}) ?_)
    · exact ENat.sum_ne_top.2 fun i _ => hM _
    · intro w hw i
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hw
      rw [map_smul]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have h1 := lenCokerLe R Z hZ a
  have h2 := len_le_pi ev hev (LinearMap.ker (a • (LinearMap.id : Z →ₗ[R] Z))) (fun _ => H) (by
    intro z hz i
    apply hH
    have : a • z = 0 := hz
    have e := congrFun (congrArg ev this) i
    simpa using e)
  have h3 : Module.length R K ≤ Module.length R (Z ⧸ LinearMap.range (a • (LinearMap.id : Z →ₗ[R] Z))) := by
    refine Module.length_le_of_surjective (Submodule.liftQ _ π ?_) ?_
    · rintro _ ⟨z, rfl⟩
      exact ha z
    · intro k
      obtain ⟨z, rfl⟩ := hπ k
      exact ⟨Submodule.Quotient.mk z, rfl⟩
  refine h3.trans (h1.trans (h2.trans ?_))
  simp

theorem UpperTheory.V.Base.kerResAb :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M] [Module R M]
      [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M) [IsPrincipalIdealRing R], ContAction ρ → (∀ m : M, Module.length R (Submodule.span R {m}) ≠ ⊤) → (∀ g, ∃ c : R, ∀ m, ρ g m = c • m) →
      ∀ (U' U : Subgroup G) (h : U' ≤ U), (∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ U') → ∀ T : Finset G, (T : Set G) ⊆ U →
      U ≤ (Subgroup.closure (T : Set G) ⊔ U').topologicalClosure →
      Module.length R (LinearMap.ker (resU ρ h)) ≤ T.card * Module.length R (H0U ρ U) := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ _ hρ hM hc U' U h hab T hT hU
  choose c hc using hc
  have hρU : ContAction (ρ.comp U.subtype : Representation R U M) :=
    hρ.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  let Z0 : Submodule R (Z1U ρ U) :=
    { carrier := {z | ∀ u : U, u.1 ∈ U' → z.1 u = 0}
      zero_mem' := fun _ _ => rfl
      add_mem' := fun {x y} hx hy u hu => by
        show x.1 u + y.1 u = 0
        rw [hx u hu, hy u hu, add_zero]
      smul_mem' := fun r x hx u hu => by
        show r • x.1 u = 0
        rw [hx u hu, smul_zero] }
  have hcoc : ∀ (z : Z1U ρ U) (u v : U), z.1 (u * v) = z.1 u + ρ u (z.1 v) := fun z u v => z.2.2 u v
  let ev : Z0 →ₗ[R] (T → M) := LinearMap.pi fun t =>
    (LinearMap.proj (⟨t.1, hT t.2⟩ : U)).comp ((Z1U ρ U).subtype.comp Z0.subtype)
  have hev : Function.Injective ev := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro z hz
    have h1 : z.1.1 1 = 0 := z.2 1 U'.one_mem
    let K : Subgroup U :=
      { carrier := {u | z.1.1 u = 0}
        one_mem' := h1
        mul_mem' := fun {u v} hu hv => by
          have hu' : z.1.1 u = 0 := hu
          have hv' : z.1.1 v = 0 := hv
          show z.1.1 (u * v) = 0
          rw [hcoc, hu', hv', map_zero, add_zero]
        inv_mem' := fun {u} hu => by
          have hu' : z.1.1 u = 0 := hu
          have e := hcoc z.1 u⁻¹ u
          rw [inv_mul_cancel, h1, hu', map_zero, add_zero] at e
          exact e.symm }
    have hK : IsClosed (K : Set U) := isClosed_eq z.1.2.1 continuous_const
    have hle : Subgroup.closure (T : Set G) ⊔ U' ≤ K.map U.subtype := by
      refine sup_le ((Subgroup.closure_le _).2 fun t ht => ?_) fun u hu => ?_
      · exact ⟨⟨t, hT ht⟩, congrFun hz ⟨t, ht⟩, rfl⟩
      · exact ⟨⟨u, h hu⟩, z.2 _ hu, rfl⟩
    refine Subtype.ext (Subtype.ext (funext fun u => ?_))
    have : u ∈ closure (K : Set U) := by
      rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image]
      exact closure_mono hle (hU u.2)
    rw [hK.closure_eq] at this
    exact this
  let π : Z0 →ₗ[R] LinearMap.ker (resU ρ h) :=
    LinearMap.codRestrict _ ((Submodule.mkQ _).comp Z0.subtype) fun z =>
      (resU_mk_eq_zero ρ h z.1).2 ⟨0, fun u => by rw [z.2 _ u.2]; simp⟩
  have hπ : Function.Surjective π := by
    rintro ⟨x, hx⟩
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨m, hm⟩ := (resU_mk_eq_zero ρ h z).1 hx
    let b : Z1U ρ U := ⟨d0 _ m, coboundaries_le_cocycles _ hρU ⟨m, rfl⟩⟩
    refine ⟨⟨z - b, fun u hu => ?_⟩, Subtype.ext ?_⟩
    · show z.1 u - (ρ u m - m) = 0
      exact sub_eq_zero.2 (hm ⟨u.1, hu⟩)
    · refine (mk_eq_mk ρ U (z - b) z).2 ⟨-m, fun u => ?_⟩
      show z.1 u - (ρ u m - m) - z.1 u = _
      rw [map_neg]
      abel
  obtain ⟨a, ha⟩ := (IsPrincipalIdealRing.principal (Ideal.span (Set.range fun u : U => c u - 1))).principal
  have hkill : ∀ (u : U) (z : Z0), π ((c u - 1) • z) = 0 := by
    intro u z
    refine Subtype.ext ((Submodule.Quotient.mk_eq_zero _).2 ((mem_coboundaries1 _ _).2 ⟨z.1.1 u, fun g => ?_⟩))
    show (c u - 1) • z.1.1 g = ρ g (z.1.1 u) - z.1.1 u
    have e0 : u * g = (u * g * u⁻¹ * g⁻¹) * (g * u) := by group
    have e1 : ρ ((u * g * u⁻¹ * g⁻¹ : U) : G) = 1 := by
      have : ρ u * ρ g = ρ g * ρ u := by
        ext m
        simp only [Module.End.mul_apply, hc, smul_smul, mul_comm]
      have e : ((u * g * u⁻¹ * g⁻¹ : U) : G) = u * g * ((u : G)⁻¹ * (g : G)⁻¹) := by
        simp [mul_assoc]
      rw [e, map_mul, map_mul, this, ← map_mul, ← map_mul]
      simp
    have e2 : z.1.1 (u * g) = z.1.1 (g * u) := by
      rw [e0, hcoc, e1, z.2 _ (hab u u.2 g g.2)]
      simp
    rw [hcoc, hcoc, hc u] at e2
    rw [sub_smul, one_smul, eq_sub_of_add_eq' e2]
    abel
  have hamem : a ∈ Ideal.span (Set.range fun u : U => c u - 1) := by
    rw [ha]; exact Submodule.mem_span_singleton_self a
  have key := len_abs hM ev hev π hπ a (fun z => ?_) (H0U ρ U) (fun m hm => ?_)
  · simpa using key
  · refine Submodule.span_induction (p := fun r _ => π (r • z) = 0) ?_ ?_ ?_ ?_ hamem
    · rintro _ ⟨u, rfl⟩
      exact hkill u z
    · simp
    · intro x y _ _ hx hy
      rw [add_smul, map_add (f := _), hx, hy, add_zero]
    · intro r x _ hx
      rw [smul_assoc, map_smul, hx, smul_zero]
  · intro u
    have : c u - 1 ∈ Ideal.span (Set.range fun u : U => c u - 1) := Ideal.subset_span ⟨u, rfl⟩
    rw [ha] at this
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 this
    show ρ u m = m
    have e : (c u - 1) • m = 0 := by rw [← hr, smul_assoc, hm, smul_zero]
    rw [hc, ← sub_eq_zero]
    rw [sub_smul, one_smul] at e
    exact e
end

section

open ReciprocityTheory.Gal UpperTheory.V.Base

theorem UpperTheory.V.Base.kerResCyc :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M] [Module R M]
      [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M), ContAction ρ → ∀ (U' U : Subgroup G) (h : U' ≤ U) [(U'.subgroupOf U).Normal] (γ : G), γ ∈ U →
      U ≤ (Subgroup.zpowers γ ⊔ U').topologicalClosure →
      (Module.length R (H0U ρ U') ≠ ⊤ → Module.length R (LinearMap.ker (resU ρ h)) ≤ Module.length R (H0U ρ U)) ∧
      ((∀ m ∈ H0U ρ U', ∃ m' ∈ H0U ρ U', ρ γ m' - m' = m) → Function.Injective (resU ρ h)) := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ hρ U' U h _ γ hγ hcl
  have memU : ∀ (V : Subgroup G) (m : M), m ∈ H0U ρ V ↔ ∀ g ∈ V, ρ g m = m := by
    intro V m
    simp [H0U, H0, Representation.mem_invariants]
  have hinv : ∀ m ∈ H0U ρ U', ρ γ m ∈ H0U ρ U' := by
    intro m hm
    rw [memU] at hm ⊢
    intro u hu
    have hc := Subgroup.Normal.conj_mem (H := U'.subgroupOf U) ⟨u, h hu⟩
      (by simpa [Subgroup.mem_subgroupOf] using hu) (⟨γ, hγ⟩⁻¹)
    rw [Subgroup.mem_subgroupOf] at hc
    simp only [inv_inv, Subgroup.coe_mul, InvMemClass.coe_inv] at hc
    have e : ρ u (ρ γ m) = ρ γ (ρ (γ⁻¹ * u * γ) m) := by
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
      congr 2
      group
    rw [e, hm _ hc]
  let T : H0U ρ U' →ₗ[R] H0U ρ U' := LinearMap.codRestrict (H0U ρ U')
    ((ρ γ - LinearMap.id) ∘ₗ (H0U ρ U').subtype)
    (fun m => Submodule.sub_mem _ (hinv m m.2) m.2)
  have hT : ∀ m : H0U ρ U', ((T m : H0U ρ U') : M) = ρ γ m - m := fun m => rfl
  obtain ⟨φ, hφ⟩ := kerResGen1 R G M ρ hρ U' U h γ hγ hcl T hT
  refine ⟨fun hfin => ?_, fun hsurj => ?_⟩
  · have hfix : ∀ m : H0U ρ U', T m = 0 → (m : M) ∈ H0U ρ U := by
      intro m hm0
      have hγm : ρ γ m = m := by
        have := congrArg Subtype.val hm0
        rw [hT] at this
        exact sub_eq_zero.mp this
      let S : Subgroup G :=
        { carrier := {g | ρ g m = m}
          mul_mem' := by
            intro a b ha hb
            simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
            rw [hb, ha]
          one_mem' := by simp
          inv_mem' := by
            intro a ha
            simp only [Set.mem_setOf_eq] at *
            calc ρ a⁻¹ m = ρ a⁻¹ (ρ a m) := by rw [ha]
              _ = m := by rw [← Module.End.mul_apply, ← map_mul]; simp }
      have hScl : IsClosed (S : Set G) :=
        IsClosed.preimage (hρ.comp (Continuous.prodMk continuous_id continuous_const))
          (isClosed_singleton (x := (m : M)))
      have hle : Subgroup.zpowers γ ⊔ U' ≤ S :=
        sup_le (Subgroup.zpowers_le.mpr hγm) (fun u hu => (memU U' m).mp m.2 u hu)
      have hUS := hcl.trans (Subgroup.topologicalClosure_minimal _ hle hScl)
      exact (memU U m).mpr fun g hg => hUS hg
    let ι : LinearMap.ker T →ₗ[R] H0U ρ U := LinearMap.codRestrict (H0U ρ U)
      ((H0U ρ U').subtype ∘ₗ (LinearMap.ker T).subtype) (fun m => hfix m m.2)
    have hι : Function.Injective ι := by
      intro a b hab
      have e : ((ι a : H0U ρ U) : M) = ((ι b : H0U ρ U) : M) := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext e)
    calc Module.length R (LinearMap.ker (resU ρ h))
        ≤ Module.length R (H0U ρ U' ⧸ LinearMap.range T) := Module.length_le_of_injective φ hφ
      _ = Module.length R (LinearMap.ker T) :=
        (KStar.Selmer.length_ker_eq_length_coker T hfin).symm
      _ ≤ Module.length R (H0U ρ U) := Module.length_le_of_injective ι hι
  · have hq : ∀ x : H0U ρ U' ⧸ LinearMap.range T, x = 0 := by
      intro x
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [Submodule.Quotient.mk_eq_zero]
      obtain ⟨m', hm', he⟩ := hsurj y y.2
      exact ⟨⟨m', hm'⟩, Subtype.ext (by rw [hT]; exact he)⟩
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    have := @hφ ⟨x, hx⟩ 0 (by rw [hq (φ _), hq (φ 0)])
    rw [Submodule.mem_bot]
    exact congrArg Subtype.val this
end
