module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle029
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle042
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.RingTheory.Length
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open ReciprocityTheory.Gal UpperTheory.V.Base

private theorem exists_continuous_mulEquiv_of_map_embedding {G G' : Type} [Group G] [Group G'] [TopologicalSpace G]
    [TopologicalSpace G'] (φ : G' →* G) (hφ : Topology.IsEmbedding φ) (U' : Subgroup G')
    (U : Subgroup G) (h : U'.map φ = U) :
    ∃ e : U' ≃* U, (∀ u' : U', ((e u' : U) : G) = φ u') ∧ Continuous e ∧ Continuous e.symm := by
  have hmem : ∀ u' : U', φ u' ∈ U := fun u' => h ▸ Subgroup.mem_map_of_mem φ u'.2
  let f : U' →* U :=
    { toFun := fun u' => ⟨φ u', hmem u'⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp }
  have hinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply hφ.injective
    exact congrArg Subtype.val hab
  have hsurj : Function.Surjective f := by
    rintro ⟨g, hg⟩
    rw [← h] at hg
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hg
    exact ⟨⟨x, hx⟩, rfl⟩
  let e : U' ≃* U := MulEquiv.ofBijective f ⟨hinj, hsurj⟩
  have he : ∀ u' : U', ((e u' : U) : G) = φ u' := fun _ => rfl
  refine ⟨e, he, ?_, ?_⟩
  · change Continuous (fun u' : U' => (⟨φ u', hmem u'⟩ : U))
    exact (hφ.continuous.comp continuous_subtype_val).subtype_mk _
  · rw [Topology.IsEmbedding.subtypeVal.isInducing.continuous_iff, hφ.isInducing.continuous_iff]
    have hc : (⇑φ ∘ Subtype.val ∘ ⇑e.symm) = (Subtype.val : U → G) := by
      funext u
      have := he (e.symm u)
      rw [e.apply_symm_apply] at this
      exact this.symm
    rw [hc]
    exact continuous_subtype_val

theorem UpperTheory.V.Base.selTransport :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M] [Module R M]
      [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M) (G' : Type) [Group G'] [TopologicalSpace G'] (φ : G' →* G), Topology.IsEmbedding φ →
      ∀ (U' : Subgroup G') (U : Subgroup G), U'.map φ = U → ∀ 𝒟 : Set (Subgroup G),
      ∃ Φ : LocSel (ρ.comp φ : Representation R G' M) U' (Subgroup.comap φ '' 𝒟) ≃ₗ[R] LocSel ρ U 𝒟,
        ∀ (z' : Z1U (ρ.comp φ : Representation R G' M) U') (z : Z1U ρ U) hz', (∀ (u' : U') (u : U), φ u' = u → z.1 u = z'.1 u') →
          (Φ ⟨Submodule.Quotient.mk z', hz'⟩ : H1U ρ U) = Submodule.Quotient.mk z := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ G' _ _ φ hφ U' U hU 𝒟
  obtain ⟨e, he, hec, hesc⟩ := exists_continuous_mulEquiv_of_map_embedding φ hφ U' U hU
  have key : ∀ g : U, φ ((e.symm g : U') : G') = g := fun g => by
    rw [← he, e.apply_symm_apply]
  let A : Representation R U' M := (ρ.comp φ).comp U'.subtype
  let B : Representation R U M := ρ.comp U.subtype
  let F : H1 B →ₗ[R] H1 A :=
    pairH1DecompositionMap B A e.toMonoidHom hec LinearMap.id continuous_id (fun g m => by
      simp only [A, B, LinearMap.id_apply, MonoidHom.comp_apply, Subgroup.coe_subtype,
        MulEquiv.coe_toMonoidHom, he])
  let E : H1 A →ₗ[R] H1 B :=
    pairH1DecompositionMap A B e.symm.toMonoidHom hesc LinearMap.id continuous_id (fun g m => by
      simp only [A, B, LinearMap.id_apply, MonoidHom.comp_apply, Subgroup.coe_subtype,
        MulEquiv.coe_toMonoidHom, key])
  have hEF : E ∘ₗ F = LinearMap.id := by
    apply LinearMap.ext
    intro x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp only [E, F, LinearMap.comp_apply, pairH1DecompositionMap, Submodule.mapQ_apply, LinearMap.id_apply]
    congr 1
    apply Subtype.ext
    funext g
    simp [compatiblePairCocycles1]
  have hFE : F ∘ₗ E = LinearMap.id := by
    apply LinearMap.ext
    intro x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp only [E, F, LinearMap.comp_apply, pairH1DecompositionMap, Submodule.mapQ_apply, LinearMap.id_apply]
    congr 1
    apply Subtype.ext
    funext g
    simp [compatiblePairCocycles1]
  let L : H1 A ≃ₗ[R] H1 B := LinearEquiv.ofLinear E F hEF hFE
  have hmap : (LocSel (ρ.comp φ : Representation R G' M) U' (Subgroup.comap φ '' 𝒟)).map
      (L : H1 A →ₗ[R] H1 B) = LocSel ρ U 𝒟 := by
    ext x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [Submodule.mem_map_equiv]
    simp only [L, LinearEquiv.ofLinear_symm_apply, F, pairH1DecompositionMap, Submodule.mapQ_apply]
    rw [mk_mem_locSel, mk_mem_locSel]
    constructor
    · intro hyp D hD
      obtain ⟨m, hm⟩ := hyp _ ⟨D, hD, rfl⟩
      refine ⟨m, fun u hu => ?_⟩
      have h1 := hm (e.symm u) (by rw [Subgroup.mem_comap, key]; exact hu)
      simpa [compatiblePairCocycles1, key] using h1
    · rintro hyp D' ⟨D, hD, rfl⟩
      obtain ⟨m, hm⟩ := hyp D hD
      refine ⟨m, fun u' hu' => ?_⟩
      have h1 := hm (e u') (by rw [he]; exact hu')
      rw [he] at h1
      simpa [compatiblePairCocycles1, he] using h1
  refine ⟨L.ofSubmodules _ _ hmap, ?_⟩
  intro z' z hz' hzz
  rw [LinearEquiv.ofSubmodules_apply]
  simp only [L, LinearEquiv.ofLinear_apply, E, pairH1DecompositionMap, Submodule.mapQ_apply]
  congr 1
  apply Subtype.ext
  funext u
  simp only [compatiblePairCocycles1]
  exact (hzz (e.symm u) u (key u)).symm
end

section

open ReciprocityTheory.Gal UpperTheory.V.Base

theorem UpperTheory.V.Base.corInv :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M] [Module R M]
      [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M), ContAction ρ → ∀ (U' U : Subgroup G) [U'.Normal] (h : U' ≤ U), IsOpen (U'.subgroupOf U : Set U) →
      ∀ x ∈ invariantsUnderSubgroupH1 ρ U U', U'.relIndex U • x ∈ LinearMap.range (resU ρ h) := by
  classical
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ hρ U' U _ h hopen x hx
  by_cases hfin : U'.relIndex U = 0
  · rw [hfin, zero_smul]
    exact zero_mem _
  haveI : (U'.subgroupOf U).FiniteIndex := ⟨hfin⟩
  haveI : Fintype (U ⧸ U'.subgroupOf U) := Fintype.ofFinite _
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hinv : ∀ g : U, conjU ρ U' g (Submodule.Quotient.mk z) = Submodule.Quotient.mk z :=
    fun g => (Representation.mem_invariants _ _).mp hx g
  have hq : ∀ q : U ⧸ U'.subgroupOf U, ∃ m : M, ∀ u : U',
      ρ (q.out : G) (z.1 (conjHom U' (q.out : G) u)) - z.1 u = ρ u m - m := by
    intro q
    obtain ⟨z', hz1, hz2⟩ := conjU_mk ρ U' (q.out : G) z
    rw [hinv, mk_eq_mk] at hz1
    obtain ⟨m, hm⟩ := hz1
    refine ⟨-m, fun u => ?_⟩
    have e := hm u
    rw [hz2] at e
    rw [map_neg, neg_sub_neg, ← neg_sub ((ρ u) m) m, ← e]
    abel
  choose mq hmq using hq
  let f : U → M := fun g => if hg : (g : G) ∈ U' then z.1 ⟨g, hg⟩ else 0
  have hfc : ContinuousOn f (U'.subgroupOf U : Set U) := by
    rw [continuousOn_iff_continuous_restrict]
    refine (z.2.1.comp (Continuous.subtype_mk
      (continuous_subtype_val.comp continuous_subtype_val)
      (fun g : (U'.subgroupOf U : Set U) => Subgroup.mem_subgroupOf.mp g.2))).congr ?_
    intro g
    simp [f, dif_pos (Subgroup.mem_subgroupOf.mp g.2)]
  have hfcoc : ∀ g ∈ U'.subgroupOf U, ∀ k ∈ U'.subgroupOf U,
      f (g * k) = f g + (ρ.comp U.subtype) g (f k) := by
    intro g hg k hk
    rw [Subgroup.mem_subgroupOf] at hg hk
    have hgk : ((g * k : U) : G) ∈ U' := by
      rw [Subgroup.coe_mul]
      exact U'.mul_mem hg hk
    simp only [f, dif_pos hg, dif_pos hk, dif_pos hgk]
    exact z.2.2 ⟨g, hg⟩ ⟨k, hk⟩
  obtain ⟨F, hFc, hFcoc, ⟨x0, hx0⟩, -⟩ := GlobalTheory.exists_corestriction_cocycle R U M
    (ρ.comp U.subtype) (U'.subgroupOf U) hopen (fun _ => continuous_of_discreteTopology)
    (fun m => hρ.comp (Continuous.prodMk
      (continuous_subtype_val) continuous_const)) f hfc hfcoc
  let Fz : Z1U ρ U := ⟨F, hFc, hFcoc⟩
  refine ⟨Submodule.Quotient.mk Fz, ?_⟩
  obtain ⟨w, hw1, hw2⟩ := resU_mk ρ h Fz
  rw [hw1, ← Submodule.Quotient.mk_smul, mk_eq_mk]
  refine ⟨x0 + ∑ q, mq q, fun u => ?_⟩
  have hterm : ∀ q : U ⧸ U'.subgroupOf U,
      (ρ.comp U.subtype) q.out (f ((q.out)⁻¹ * ⟨(u : G), h u.2⟩ * q.out)) =
        z.1 u + (ρ u (mq q) - mq q) := by
    intro q
    rw [← hmq q u, add_sub_cancel]
    have hmem : (((q.out)⁻¹ * ⟨(u : G), h u.2⟩ * q.out : U) : G) ∈ U' := by
      have e := ‹U'.Normal›.conj_mem u u.2 ((q.out : G)⁻¹)
      simpa [mul_assoc] using e
    simp only [f, dif_pos hmem]
    rfl
  have hcard : Fintype.card (U ⧸ U'.subgroupOf U) = U'.relIndex U := by
    rw [Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]
  rw [hw2 u]
  show F ⟨(u : G), h u.2⟩ - _ = _
  rw [hx0 ⟨u, h u.2⟩ (Subgroup.mem_subgroupOf.mpr u.2), finsum_eq_sum_of_fintype,
    Finset.sum_congr rfl (fun q _ => hterm q), Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, hcard]

  simp only [Submodule.coe_smul, Pi.smul_apply, MonoidHom.comp_apply, Subgroup.coe_subtype,
  map_add, map_sum]
  rw [show ((U'.relIndex U • z : Z1U ρ U') : U' → M) u = U'.relIndex U • z.1 u from rfl]
  abel
end

section

open ReciprocityTheory.Gal UpperTheory.V.Base

private theorem aux {R Q M : Type} [CommRing R] [Group Q] [AddCommGroup M] [Module R M]
    (π : Representation R Q M) (H : Subgroup Q) (f : Q → M) (hf : ∀ g h, f (g * h) = f g + π g (f h))
    (h0 : ∀ u ∈ H, f u = 0) : ∃ m, ∀ g, H.index • f g = π g m - m :=
  _root_.UpperTheory.Reformulated.B.Qi36.aux π H f hf h0

theorem UpperTheory.V.Base.kerResSmul :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M] [Module R M]
      [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M) (U' U : Subgroup G) (h : U' ≤ U) (x : H1U ρ U), resU ρ h x = 0 → U'.relIndex U • x = 0 := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ U' U h x hx
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨m, hm⟩ := (resU_mk_eq_zero ρ h z).1 hx
  obtain ⟨s, hs⟩ := aux (ρ.comp U.subtype : Representation R U M) (U'.subgroupOf U)
    (fun u => z.1 u - (ρ u m - m))
    (fun g k => by
      have e : z.1 (g * k) = z.1 g + ρ g (z.1 k) := z.2.2 g k
      show z.1 (g * k) - (ρ ((g : G) * k) m - m) = z.1 g - (ρ g m - m) + ρ g (z.1 k - (ρ k m - m))
      rw [e, map_mul, Module.End.mul_apply, map_sub, map_sub]
      abel)
    (fun u hu => sub_eq_zero.2 (hm ⟨u.1, hu⟩))
  have e0 : U'.relIndex U • (Submodule.Quotient.mk z : H1U ρ U) = Submodule.Quotient.mk (U'.relIndex U • z) :=
    (map_nsmul (Submodule.mkQ _) _ z).symm
  rw [e0, Submodule.Quotient.mk_eq_zero]
  refine (mem_coboundaries1 _ _).2 ⟨s + U'.relIndex U • m, fun g => ?_⟩
  have e : U'.relIndex U • (z.1 g - (ρ g m - m)) = ρ g s - s := hs g
  show U'.relIndex U • z.1 g = ρ g (s + U'.relIndex U • m) - (s + U'.relIndex U • m)
  rw [smul_sub, smul_sub, sub_eq_iff_eq_add] at e
  rw [e, map_add (f := _), map_nsmul]
  abel
end

section

open ReciprocityTheory.Gal UpperTheory.V.Base

private theorem len_le_add {R A B C D : Type} [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] [AddCommGroup D] [Module R D] (g : A →ₗ[R] B) (j : A →ₗ[R] C) (k : C →ₗ[R] D)
    (hj : Function.Injective j) (hk : ∀ x, g x = 0 → k (j x) = 0) :
    Module.length R A ≤ Module.length R B + Module.length R (LinearMap.ker k) := by
  have h1 : Module.length R A = Module.length R (LinearMap.ker g) + Module.length R (LinearMap.range g) :=
    Module.length_eq_add_of_exact (LinearMap.ker g).subtype g.rangeRestrict (Submodule.injective_subtype _)
      g.surjective_rangeRestrict (by
        rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype])
  have h2 : Module.length R (LinearMap.range g) ≤ Module.length R B :=
    Module.length_le_of_injective (LinearMap.range g).subtype (Submodule.injective_subtype _)
  have h3 : Module.length R (LinearMap.ker g) ≤ Module.length R (LinearMap.ker k) :=
    Module.length_le_of_injective (j.restrict (p := LinearMap.ker g) (q := LinearMap.ker k) fun x hx => hk x hx)
      fun x y e => Subtype.ext (hj (congrArg Subtype.val e))
  rw [h1, add_comm]
  exact add_le_add h2 h3

private theorem len_sub {R A B C D : Type} [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] [AddCommGroup D] [Module R D] (g : A →ₗ[R] B) (j : A →ₗ[R] C) (k : C →ₗ[R] D)
    (hj : Function.Injective j) (hk : ∀ x, g x = 0 → k (j x) = 0) (P : Submodule R A) (Q : Submodule R B)
    (hPQ : ∀ x ∈ P, g x ∈ Q) :
    Module.length R P ≤ Module.length R Q + Module.length R (LinearMap.ker k) :=
  len_le_add (g.restrict hPQ) (j.comp P.subtype) k (hj.comp (Submodule.injective_subtype P))
    fun x hx => hk x.1 (congrArg Subtype.val hx)

theorem UpperTheory.V.Base.selUp :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M] [Module R M]
      [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M) (U' U : Subgroup G) (h : U' ≤ U) (𝒟 : Set (Subgroup G)) (h𝒟 : ConjStable 𝒟),
      Module.length R (LocSel ρ U 𝒟) ≤ Module.length R (LocSel ρ U' 𝒟) + Module.length R (LinearMap.ker (resU ρ h)) ∧
      (∀ [U'.Normal], Module.length R (LocSel ρ U 𝒟) ≤ Module.length R (selEig ρ U' h𝒟 U 1) + Module.length R (LinearMap.ker (resU ρ h))) ∧
      (∀ [U'.Normal] [U.Normal] (W : Subgroup G) (ψ : W →* Rˣ),
        Module.length R (selEig ρ U h𝒟 W ψ) ≤ Module.length R (selEig ρ U' h𝒟 W ψ) + Module.length R (LinearMap.ker (resU ρ h))) ∧
      ∀ [U'.Normal] [U.Normal] (g : G) (s : R), Module.length R (Module.End.eigenspace (selRep ρ U h𝒟 g) s) ≤
        Module.length R (Module.End.eigenspace (selRep ρ U' h𝒟 g) s) + Module.length R (LinearMap.ker (resU ρ h)) := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ U' U h 𝒟 h𝒟
  have hj := Submodule.injective_subtype (LocSel ρ U 𝒟)
  have hk : ∀ x, selRes ρ h 𝒟 x = 0 → resU ρ h ((LocSel ρ U 𝒟).subtype x) = 0 :=
    fun x hx => congrArg Subtype.val hx
  refine ⟨len_le_add (selRes ρ h 𝒟) _ _ hj hk, ?_, ?_, ?_⟩
  · intro _
    have hm : ∀ x, selRes ρ h 𝒟 x ∈ selEig ρ U' h𝒟 U 1 := fun x => by
      rw [selEig, eig_one]
      intro g
      exact Subtype.ext (restriction_mem_invariant_H1 ρ h x.1 g)
    exact len_le_add ((selRes ρ h 𝒟).codRestrict _ hm) _ _ hj fun x hx => hk x (congrArg Subtype.val hx)
  · intro _ _ W ψ
    refine len_sub (selRes ρ h 𝒟) _ _ hj hk _ _ fun x hx => ?_
    rw [mem_eig] at hx ⊢
    intro g
    have e : selRep ρ U h𝒟 g.1 x = ((ψ g : Rˣ) : R) • x := hx g
    show selRep ρ U' h𝒟 g.1 _ = _
    rw [← selRes_selRep, e, map_smul]
  · intro _ _ g s
    refine len_sub (selRes ρ h 𝒟) _ _ hj hk _ _ fun x hx => ?_
    rw [Module.End.mem_eigenspace_iff] at hx ⊢
    rw [← selRes_selRep, hx, map_smul]
end

section

open ReciprocityTheory.Gal UpperTheory.V.Base

private theorem length_le_of_ker_le {R A B : Type} [CommRing R] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] {C : Type} [AddCommGroup C] [Module R C] (f : A →ₗ[R] B)
    (g : LinearMap.ker f →ₗ[R] C) (hg : Function.Injective g) :
    Module.length R A ≤ Module.length R C + Module.length R B := by
  rw [Module.length_eq_add_of_exact (LinearMap.ker f).subtype f.rangeRestrict
    (Submodule.subtype_injective _) f.surjective_rangeRestrict
    (LinearMap.exact_iff.mpr (by rw [LinearMap.ker_rangeRestrict, Submodule.range_subtype]))]
  exact add_le_add (Module.length_le_of_injective g hg)
    (Module.length_le_of_injective (LinearMap.range f).subtype (Submodule.subtype_injective _))

theorem UpperTheory.V.Base.selLocal :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M] [Module R M]
      [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M) (U' U : Subgroup G) (h : U' ≤ U) (𝒟 : Set (Subgroup G)) (ι : Type) [Fintype ι] (D : ι → Subgroup G), (∀ i, D i ∈ 𝒟) →
      (∀ D' ∈ 𝒟, U ⊓ D' ≤ U' ∨ ∃ i, ∃ u ∈ U, ∀ x ∈ U ⊓ D', u⁻¹ * x * u ∈ D i) →
      Module.length R ((LocSel ρ U' 𝒟).comap (resU ρ h)) ≤ Module.length R (LocSel ρ U 𝒟) + ∑ i, Module.length R (LinearMap.ker (resU ρ (inf_le_inf_right (D i) h))) := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ U' U h 𝒟 ι _ D hD hcov
  set X := (LocSel ρ U' 𝒟).comap (resU ρ h) with hX
  have key0 : ∀ x ∈ X, ∀ D' ∈ 𝒟, resU ρ (le_trans inf_le_left h : U' ⊓ D' ≤ U) x = 0 := by
    intro x hx D' hD'
    have e := (mem_locSel.mp (Submodule.mem_comap.mp hx)) D' hD'
    rw [resU_resU] at e
    exact e
  have key : ∀ x ∈ X, ∀ D' ∈ 𝒟,
      resU ρ (inf_le_inf_right D' h) (resU ρ (inf_le_left : U ⊓ D' ≤ U) x) = 0 := by
    intro x hx D' hD'
    rw [resU_resU]
    exact key0 x hx D' hD'
  let f : X →ₗ[R] (∀ i, LinearMap.ker (resU ρ (inf_le_inf_right (D i) h))) :=
    LinearMap.pi fun i => LinearMap.codRestrict _
      ((resU ρ (inf_le_left : U ⊓ D i ≤ U)).comp X.subtype)
      (fun x => LinearMap.mem_ker.mpr (key x.1 x.2 (D i) (hD i)))
  have hmem : ∀ y ∈ LinearMap.ker f, ((y : H1U ρ U)) ∈ LocSel ρ U 𝒟 := by
    intro y hy
    have hy' : ∀ i, resU ρ (inf_le_left : U ⊓ D i ≤ U) (y : H1U ρ U) = 0 := by
      intro i
      simpa [f] using congrArg Subtype.val (congrFun (LinearMap.mem_ker.mp hy) i)
    rw [mem_locSel]
    intro D' hD'
    rcases hcov D' hD' with hle | ⟨i, u, hu, hconj⟩
    · have e := resU_resU ρ (le_inf hle inf_le_right : U ⊓ D' ≤ U' ⊓ D')
        (le_trans inf_le_left h) (y : H1U ρ U)
      rw [key0 _ y.2 D' hD', map_zero] at e
      exact e.symm
    · obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (y : H1U ρ U)
      have h0 := hy' i
      rw [← hz] at h0 ⊢
      rw [resU_mk_eq_zero] at h0 ⊢
      obtain ⟨m, hm⟩ := h0
      refine ⟨ρ u m - z.1 ⟨u, hu⟩, fun v => ?_⟩
      have hvU : (v : G) ∈ U := (Subgroup.mem_inf.mp v.2).1
      have hwD : u⁻¹ * (v : G) * u ∈ D i := hconj v v.2
      have hwU : u⁻¹ * (v : G) * u ∈ U := U.mul_mem (U.mul_mem (U.inv_mem hu) hvU) hu
      have e1 : z.1 ⟨u⁻¹ * (v : G) * u, hwU⟩ = ρ (u⁻¹ * (v : G) * u) m - m :=
        hm ⟨u⁻¹ * (v : G) * u, Subgroup.mem_inf.mpr ⟨hwU, hwD⟩⟩
      have hc := z.2.2
      have c1 := hc ⟨v, hvU⟩ ⟨u, hu⟩
      have c2 := hc ⟨u, hu⟩ ⟨u⁻¹ * (v : G) * u, hwU⟩
      have eq : (⟨v, hvU⟩ * ⟨u, hu⟩ : U) = ⟨u, hu⟩ * ⟨u⁻¹ * (v : G) * u, hwU⟩ :=
        Subtype.ext (by simp [mul_assoc])
      rw [eq, c2, e1] at c1
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype] at c1
      have hr : ρ u (ρ (u⁻¹ * (v : G) * u) m) = ρ v (ρ u m) := by
        rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
        congr 2
        group
      rw [map_sub, hr] at c1
      show z.1 ⟨v, hvU⟩ = _
      rw [eq_sub_of_add_eq c1.symm]
      simp only [map_sub]
      abel
  let g : LinearMap.ker f →ₗ[R] LocSel ρ U 𝒟 :=
    LinearMap.codRestrict _ (X.subtype.comp (LinearMap.ker f).subtype) (fun y => hmem y.1 y.2)
  have hg : Function.Injective g := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    have e := congrArg Subtype.val hab
    exact e
  have e := length_le_of_ker_le f g hg
  rwa [Module.length_pi_of_fintype] at e
end
