module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsIntegralRepDetectingInvariantSubspace
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.UOpSum
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
public import Mathlib.RepresentationTheory.Invariants
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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

@[expose] public section

section

open GlobalTheory.CuspRep

noncomputable section

namespace UpperTheory.V.Hi.TyLoc

private theorem avg {Q N : Type} [Group Q] [Fintype Q] [AddCommGroup N] [Module ℂ N] {d : ℕ}
    (ξ : Representation ℂ Q (Fin d → ℂ)) (π : Representation ℂ Q N) :
    (∃ f : (Fin d → ℂ) →ₗ[ℂ] N, f ≠ 0 ∧ ∀ k v, f (ξ k v) = π k (f v)) ↔
      ∃ i v n, ∑ g, ξ g⁻¹ v i • π g n ≠ 0 := by
  classical
  constructor
  · rintro ⟨f, hf, he⟩
    by_contra hc
    push Not at hc
    refine hf (LinearMap.ext fun v => ?_)
    have h1 : ∀ g, ∑ i, ξ g⁻¹ v i • π g (f (Pi.single i 1)) = f v := fun g => by
      have : ∑ i, ξ g⁻¹ v i • (Pi.single i 1 : Fin d → ℂ) = ξ g⁻¹ v := by
        ext j
        simp [Finset.sum_apply, Pi.single_apply]

      simp only [← map_smul, ← map_sum]
      rw [this, ← he, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    have h2 : ∑ g : Q, f v = 0 := by
      rw [← Finset.sum_congr rfl fun g _ => h1 g, Finset.sum_comm]
      exact Finset.sum_eq_zero fun i _ => hc i v _
    rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ] at h2
    exact (smul_eq_zero.1 h2).resolve_left (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
  · rintro ⟨i, v, n, h⟩
    refine ⟨∑ g, (LinearMap.toSpanSingleton ℂ N (π g n)) ∘ₗ (LinearMap.proj i) ∘ₗ ξ g⁻¹, fun h0 => h ?_, fun k v => ?_⟩
    · simpa using LinearMap.congr_fun h0 v
    · set_option synthInstance.maxHeartbeats 100000 in
        simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply,
          LinearMap.proj_apply, map_sum, map_smul]
      rw [← Equiv.sum_comp (Equiv.mulLeft k)]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [Equiv.coe_mulLeft, ← Module.End.mul_apply (ξ _), ← map_mul, mul_inv_rev, inv_mul_cancel_right, map_mul,
        Module.End.mul_apply]

private def Tw (_γ : ℂ ≃+* ℂ) (V : Type) : Type := V

private instance (γ : ℂ ≃+* ℂ) (V : Type) [h : AddCommGroup V] : AddCommGroup (Tw γ V) := h

private instance (γ : ℂ ≃+* ℂ) (V : Type) [AddCommGroup V] [Module ℂ V] : Module ℂ (Tw γ V) :=
  Module.compHom V γ.toRingHom

private theorem twist {G : Type} [Group G] [TopologicalSpace G] (γ : ℂ ≃+* ℂ) (σ' : SmIrr G) :
    ∃ (σ : SmIrr G) (f : σ.V ≃+ σ'.V), (∀ (z : ℂ) v, f (z • v) = γ z • f v) ∧ ∀ g v, f (σ.ρ g v) = σ'.ρ g (f v) := by
  let ρ : Representation ℂ G (Tw γ σ'.V) :=
    { toFun := fun g =>
        { toFun := fun v => σ'.ρ g v
          map_add' := fun x y => map_add (σ'.ρ g) x y
          map_smul' := fun z x => (σ'.ρ g).map_smul (γ z) x }
      map_one' := LinearMap.ext fun v => LinearMap.congr_fun (map_one σ'.ρ) v
      map_mul' := fun a b => LinearMap.ext fun v => LinearMap.congr_fun (map_mul σ'.ρ a b) v }
  obtain ⟨h0, h⟩ := (isIrreducible_iff _).1 σ'.irred
  refine ⟨⟨Tw γ σ'.V, ρ, σ'.smooth, (isIrreducible_iff _).2 ⟨h0, fun W hW => ?_⟩⟩, AddEquiv.refl _, fun _ _ => rfl,
    fun _ _ => rfl⟩
  let W' : Submodule ℂ σ'.V :=
    { carrier := W.carrier
      add_mem' := W.add_mem
      zero_mem' := W.zero_mem
      smul_mem' := fun z x hx => by
        have h1 : γ (γ.symm z) • x ∈ W.carrier := W.smul_mem (γ.symm z) hx
        rwa [γ.apply_symm_apply] at h1 }
  refine (h W' hW).imp (fun e => ?_) fun e => ?_
  · exact (Submodule.eq_bot_iff _).2 fun x hx => (Submodule.eq_bot_iff _).1 e x hx
  · exact Submodule.eq_top_iff'.2 fun x => Submodule.eq_top_iff'.1 e x

end UpperTheory.V.Hi.TyLoc

open UpperTheory.V.Hi.TyLoc in
theorem UpperTheory.V.Hi.typeLoc : ∀ (O : Type) [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Algebra O ℂ] [FaithfulSMul O ℂ] [Algebra.IsAlgebraic O ℂ] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsCompact (K : Set G) → ∀ (P : SmIrr G → Prop) (d : ℕ) (ξ : Representation ℂ K (Fin d → ℂ)), GlobalTheory.PRep.IsSmooth ξ → (∀ π : SmIrr G, (∃ f : (Fin d → ℂ) →ₗ[ℂ] π.V, f ≠ 0 ∧ ∀ k v, f (ξ k v) = π.ρ k (f v)) ↔ P π) → (∀ (γ : ℂ ≃ₐ[O] ℂ) (σ σ' : SmIrr G) (f : σ.V ≃+ σ'.V), (∀ (z : ℂ) v, f (z • v) = γ z • f v) → (∀ g v, f (σ.ρ g v) = σ'.ρ g (f v)) → P σ → P σ') → ∃ (m : ℕ) (τ : K →* GL (Fin m) O), IsOpen (τ.ker : Set K) ∧ ∀ π : SmIrr G, (∃ y : Fin m → π.V, y ≠ 0 ∧ ∀ (k : K) i, ∑ a, algebraMap O ℂ (τ k i a) • π.ρ k (y a) = y i) ↔ P π := by
  intro O _ _ _ _ _ _ G _ _ _ K hK P d ξ hξ hP hγ
  classical
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  let U : Subgroup K := MonoidHom.ker ξ
  have hU : IsOpen (U : Set K) := by
    have : (U : Set K) = ⋂ i : Fin d, {g | ξ g (Pi.single i 1) = Pi.single i 1} := by
      ext g
      simp only [U, SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, Set.mem_setOf_eq]
      refine ⟨fun h i => by rw [h]; rfl, fun h => (Pi.basisFun ℂ (Fin d)).ext fun i => by simpa using h i⟩
    rw [this]
    exact isOpen_iInter_of_finite fun i => hξ _
  haveI : Finite (K ⧸ U) := Subgroup.quotient_finite_of_isOpen U hU
  letI : Fintype (K ⧸ U) := Fintype.ofFinite _
  let R : ∀ π : SmIrr G, Representation ℂ K π.V := fun π => π.ρ.comp K.subtype
  let N : ∀ π : SmIrr G, Submodule ℂ π.V := fun π => Representation.invariants ((R π).comp U.subtype)
  let RQ : ∀ π : SmIrr G, Representation ℂ (K ⧸ U) (N π) := fun π => (R π).quotientToInvariants U
  have hRQ : ∀ π (k : K) (v : N π), (RQ π (k : K ⧸ U) v : π.V) = π.ρ k v := fun π k v => rfl
  let ξQ : Representation ℂ (K ⧸ U) (Fin d → ℂ) := QuotientGroup.lift U ξ le_rfl
  have hPQ : ∀ π, (∃ i v n, ∑ g, ξQ g⁻¹ v i • RQ π g n ≠ 0) ↔ P π := fun π => by
    rw [← avg, ← hP]
    constructor
    · rintro ⟨f, hf, he⟩
      refine ⟨(N π).subtype ∘ₗ f, fun h0 => hf (LinearMap.ext fun v => Subtype.ext (LinearMap.congr_fun h0 v)), fun k v => ?_⟩
      exact congrArg Subtype.val (he (k : K ⧸ U) v)
    · rintro ⟨f, hf, he⟩
      have hm : ∀ v, f v ∈ N π := fun v u => by
        have h1 : ξ u.1 = 1 := u.2
        have := he u.1 v
        rw [h1] at this
        exact this.symm
      refine ⟨f.codRestrict _ hm, fun h0 => hf (LinearMap.ext fun v => congrArg Subtype.val (LinearMap.congr_fun h0 v)),
        fun k v => ?_⟩
      obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective k
      exact Subtype.ext (he k v)
  let I : Submodule ℂ (K ⧸ U → ℂ) :=
    { carrier := {x | ∀ π, ¬ P π → ∀ v, ∑ g, x g • RQ π g v = 0}
      add_mem' := fun {a b} ha hb π hπ v => by
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, ha π hπ v, hb π hπ v, add_zero]
      zero_mem' := fun π _ v => by simp
      smul_mem' := fun z x hx π hπ v => by
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, hx π hπ v, smul_zero] }
  obtain ⟨m, τ, hτ⟩ := UpperTheory.exists_integral_rep_detecting_invariant_subspace O (K ⧸ U) I (fun g x hx π hπ v => by
      rw [← Equiv.sum_comp (Equiv.mulLeft g)]
      have := congrArg (RQ π g) (hx π hπ v)

      simp only [map_sum, map_smul, map_zero] at this
      simpa only [Equiv.coe_mulLeft, inv_mul_cancel_left, map_mul, Module.End.mul_apply] using this)
    (UpperTheory.le_span_integralValued_of_galoisStable O (K ⧸ U) I fun γ x hx π' hπ' v' => by
      obtain ⟨π, f, hf, he⟩ := twist γ.toRingEquiv π'
      have hv : f.symm v' ∈ N π := fun u => f.injective <| by
        refine (he _ _).trans ?_
        rw [f.apply_symm_apply]
        exact v'.2 u
      have h1 := congrArg (fun y : N π => f y) (hx π (fun h => hπ' (hγ γ π π' f hf he h)) ⟨_, hv⟩)

      simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, hf, Submodule.coe_zero, map_zero] at h1
      refine Subtype.ext ?_
      rw [Submodule.coe_sum, Submodule.coe_zero, ← h1]
      refine Finset.sum_congr rfl fun g _ => ?_
      obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective g
      rw [Submodule.coe_smul, hRQ, hRQ, he, f.apply_symm_apply]
      rfl)
  refine ⟨m, τ.comp (QuotientGroup.mk' U), Subgroup.isOpen_mono (fun u hu => ?_) hU, fun π => ?_⟩
  · rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff u).2 hu, map_one]
  have h2 : (∃ x ∈ I, ∃ v, ∑ g, x g • RQ π g v ≠ 0) ↔ P π := by
    refine ⟨fun ⟨x, hx, v, hv⟩ => by_contra fun h => hv (hx π h v), fun h => ?_⟩
    obtain ⟨i, v, n, hn⟩ := (hPQ π).2 h
    exact ⟨fun g => ξQ g⁻¹ v i, fun π' hπ' n' => by_contra fun h' => hπ' ((hPQ π').1 ⟨i, v, n', h'⟩), n, hn⟩
  rw [← h2, ← hτ]
  constructor
  · rintro ⟨y, hy, he⟩
    have hm : ∀ a, y a ∈ N π := fun a u => by
      have := he u.1 a
      rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff u.1).2 u.2, map_one] at this
      change π.ρ u.1 (y a) = y a
      simpa [Matrix.one_apply, apply_ite] using this
    refine ⟨fun a => ⟨y a, hm a⟩, fun h0 => hy (funext fun a => congrArg Subtype.val (congrFun h0 a)), fun g i => ?_⟩
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective g
    refine Subtype.ext ?_
    rw [Submodule.coe_sum]
    exact he k i
  · rintro ⟨F, hF, he⟩
    refine ⟨fun a => F a, fun h0 => hF (funext fun a => Subtype.ext (congrFun h0 a)), fun k i => ?_⟩
    have := congrArg Subtype.val (he (k : K ⧸ U) i)
    rw [Submodule.coe_sum] at this
    exact this
end
end

section

open IsLocalRing Matrix UpperTheory.V.Hi

private theorem relIndex_ne_zero_of_cover_ordinary_hecke_characters {G : Type} [Group G] (H K L : Subgroup G) (hHK : H ≤ K) (hLK : L ≤ K)
    (hcov : ∀ k ∈ K, ∃ l ∈ L, ∃ h ∈ H, k = l * h) (hfin : H.relIndex L ≠ 0) : H.relIndex K ≠ 0 := by
  haveI : (H.subgroupOf L).FiniteIndex := ⟨hfin⟩
  let f : L ⧸ H.subgroupOf L → K ⧸ H.subgroupOf K :=
    Quotient.map' (fun l => (⟨l, hLK l.2⟩ : K)) (by
      intro a b hab
      rw [QuotientGroup.leftRel_apply] at hab ⊢
      simpa [Subgroup.mem_subgroupOf] using hab)
  have hf : Function.Surjective f := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H k =>
      obtain ⟨l, hl, h, hh, e⟩ := hcov k k.2
      refine ⟨QuotientGroup.mk ⟨l, hl⟩, ?_⟩
      show QuotientGroup.mk _ = QuotientGroup.mk k
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simpa [e] using hh
  haveI := Finite.of_surjective f hf
  exact Subgroup.index_ne_zero_of_finite

private theorem iwahori_relIndex_ne_zero {G : Type} [Group G] (I : Iwa G) (c : ℕ) : (I.Iw c).relIndex (I.Iw 0) ≠ 0 := by
  have hNm : I.Nm c ≤ I.Iw c := le_sup_right
  have hT : I.T ≤ I.Iw c := le_trans le_sup_right le_sup_left
  have hN : I.N ≤ I.Iw c := le_trans le_sup_left le_sup_left
  refine relIndex_ne_zero_of_cover_ordinary_hecke_characters (I.Iw c) (I.Iw 0) (I.Nm 0) ?_ le_sup_right ?_ ?_
  · show I.N ⊔ I.T ⊔ I.Nm c ≤ I.N ⊔ I.T ⊔ I.Nm 0
    exact sup_le_sup_left (I.Nm_anti (Nat.zero_le c)) _
  · intro g hg
    obtain ⟨x, hx, t, ht, y, hy, e⟩ := ((iwMem G I 0 g⁻¹).1).1 (inv_mem hg)
    refine ⟨y⁻¹, inv_mem hy, t⁻¹ * x⁻¹, mul_mem (hT (inv_mem ht)) (hN (inv_mem hx)), ?_⟩
    rw [← inv_inv g, e]
    group
  · intro h0
    apply I.fin_Nm c
    have hd := Subgroup.relIndex_dvd_of_le_left (I.Nm 0) hNm
    rw [h0] at hd
    exact Nat.eq_zero_of_zero_dvd hd

private theorem iwahori_pro_unipotent_finite_index {G : Type} [Group G] (I : Iwa G) (c : ℕ) : (I.I1 c).relIndex (I.Iw 0) ≠ 0 := by
  have hTc : I.Tc c ≤ I.I1 c := le_trans le_sup_right le_sup_left
  have hN1 : I.N ≤ I.I1 c := le_trans le_sup_left le_sup_left
  have hNm1 : I.Nm c ≤ I.I1 c := le_sup_right
  have hT : I.T ≤ I.Iw c := le_trans le_sup_right le_sup_left
  have hle : I.I1 c ≤ I.Iw c := by
    show I.N ⊔ I.Tc c ⊔ I.Nm c ≤ I.N ⊔ I.T ⊔ I.Nm c
    exact sup_le_sup_right (sup_le_sup_left (I.Tc_le c) _) _
  have hle' : I.Iw c ≤ I.Iw 0 := by
    show I.N ⊔ I.T ⊔ I.Nm c ≤ I.N ⊔ I.T ⊔ I.Nm 0
    exact sup_le_sup_left (I.Nm_anti (Nat.zero_le c)) _
  have h1 : (I.I1 c).relIndex (I.Iw c) ≠ 0 := by
    refine relIndex_ne_zero_of_cover_ordinary_hecke_characters (I.I1 c) (I.Iw c) I.T hle hT ?_ ?_
    · intro g hg
      obtain ⟨x, hx, t, ht, y, hy, e⟩ := ((iwMem G I c g).1).1 hg
      have hx' : t⁻¹ * x * t ∈ I.N := by
        simpa using I.T_N t⁻¹ (inv_mem ht) x hx
      refine ⟨t, ht, t⁻¹ * x * t * y, mul_mem (hN1 hx') (hNm1 hy), ?_⟩
      rw [e]
      group
    · intro h0
      apply I.fin_Tc c
      have hd := Subgroup.relIndex_dvd_of_le_left I.T hTc
      rw [h0] at hd
      exact Nat.eq_zero_of_zero_dvd hd
  rw [← Subgroup.relIndex_mul_relIndex _ _ _ hle hle']
  exact mul_ne_zero h1 (iwahori_relIndex_ne_zero I c)

theorem UpperTheory.V.Hi.iwFin :
    ∀ (G : Type) [Group G] (I : Iwa G) (c : ℕ), (I.Iw c).relIndex (I.Iw 0) ≠ 0 ∧ (I.I1 c).relIndex (I.Iw 0) ≠ 0 := by
  intro G _ I c
  exact ⟨iwahori_relIndex_ne_zero I c, iwahori_pro_unipotent_finite_index I c⟩
end

section

open IsLocalRing Matrix UpperTheory.V.Hi

private theorem UpperTheory.V.Hi.uOpMul_mem {G : Type} [Group G] (I : Iwa G) (a x : G) :
    x ∈ I.Nconj a ↔ a⁻¹ * x * a ∈ I.N := by
  constructor
  · intro h
    obtain ⟨n, hn, e⟩ := Subgroup.mem_map.1 h
    have e2 : a * n * a⁻¹ = x := e
    have : a⁻¹ * x * a = n := by rw [← e2]; group
    rwa [this]
  · intro h
    refine Subgroup.mem_map.2 ⟨_, h, ?_⟩
    show a * (a⁻¹ * x * a) * a⁻¹ = x
    group

private theorem UpperTheory.V.Hi.uOpMul_sum {G : Type} [Group G] (I : Iwa G) {A M : Type} [CommRing A] [AddCommGroup M]
    [Module A M] (π : Representation A G M) {a : G} (ha : a ∈ I.P) {ι : Type} (s : Finset ι) (f : ι → G)
    (hf : ∀ i ∈ s, f i ∈ I.N) (hu : ∀ x ∈ I.N, ∃! i, i ∈ s ∧ a⁻¹ * ((f i)⁻¹ * x) * a ∈ I.N)
    {v : M} (hv : v ∈ fixd π I.N) : I.uOp π a v = ∑ i ∈ s, π (f i * a) v := by
  classical
  have inj : Set.InjOn f s := by
    intro i hi j hj e
    exact (hu (f j) (hf j hj)).unique ⟨hi, by rw [e]; simp⟩ ⟨hj, by simp⟩
  rw [((uOpSum G I A M π a ha).2 (s.image f) ?_ ?_).2 v hv, Finset.sum_image inj]
  · intro u h
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 h
    exact hf i hi
  · intro x hx
    obtain ⟨i, ⟨hi, h⟩, hun⟩ := hu x hx
    refine ⟨f i, ⟨Finset.mem_image_of_mem f hi, (uOpMul_mem I a _).2 h⟩, ?_⟩
    rintro u ⟨h1, h2⟩
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 h1
    rw [hun j ⟨hj, (uOpMul_mem I a _).1 h2⟩]

private theorem UpperTheory.V.Hi.uOpMul_ex {G : Type} [Group G] (I : Iwa G) {a : G} (ha : a ∈ I.P) :
    ∃ s : Finset G, (∀ u ∈ s, u ∈ I.N) ∧ ∀ x ∈ I.N, ∃! u, u ∈ s ∧ a⁻¹ * (u⁻¹ * x) * a ∈ I.N := by
  obtain ⟨s, h1, h2⟩ := (uOpSum G I ℤ ℤ (Representation.trivial ℤ G ℤ) a ha).1
  refine ⟨s, h1, fun x hx => ?_⟩
  simpa only [uOpMul_mem] using h2 x hx

theorem UpperTheory.V.Hi.uOpMul :
    ∀ (G : Type) [Group G] (I : Iwa G) (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (π : Representation A G M) (a b : G), a ∈ I.P → b ∈ I.P → ∀ v ∈ fixd π I.N, I.uOp π a v ∈ fixd π I.N ∧ I.uOp π a (I.uOp π b v) = I.uOp π (a * b) v ∧ I.uOp π 1 v = v ∧ (∀ t ∈ I.T, π t (I.uOp π a v) = I.uOp π a (π t v)) ∧ (a⁻¹ ∈ I.P → I.uOp π a v = π a v) := by
  intro G _ I A M _ _ _ π a b ha hb v hv
  have mul : ∀ (g h : G) (w : M), π g (π h w) = π (g * h) w := fun g h w => by
    rw [map_mul π g h, Module.End.mul_apply]
  have fix : ∀ c ∈ I.P, I.uOp π c v ∈ fixd π I.N := by
    intro c hc n hn
    obtain ⟨s, hs, hu⟩ := uOpMul_ex I hc
    have e1 := uOpMul_sum I π hc s id hs hu hv
    have e2 := uOpMul_sum I π hc s (fun u => n * u) (fun u h => mul_mem hn (hs u h)) (fun x hx => by
      have := hu (n⁻¹ * x) (mul_mem (inv_mem hn) hx)
      simpa only [_root_.mul_inv_rev, mul_assoc] using this) hv
    conv_lhs => rw [e1]

    rw [e2, map_sum]
    simp only [mul, id, mul_assoc]
  have unit : ∀ c ∈ I.P, c⁻¹ ∈ I.P → I.uOp π c v = π c v := by
    intro c hc hc'
    rw [uOpMul_sum I π hc ({1} : Finset G) id (by simp) ?_ hv]
    · simp
    · intro x hx
      refine ⟨1, ⟨by simp, by simpa using I.P_N _ hc' x hx⟩, fun y hy => by simpa using hy.1⟩
  refine ⟨fix a ha, ?_, ?_, ?_, unit a ha⟩
  · obtain ⟨s, hs, hu⟩ := uOpMul_ex I ha
    obtain ⟨r, hr, hw⟩ := uOpMul_ex I hb
    rw [uOpMul_sum I π ha s id hs hu (fix b hb), uOpMul_sum I π hb r id hr hw hv,
      uOpMul_sum I π (mul_mem ha hb) (s ×ˢ r) (fun p => p.1 * (a * p.2 * a⁻¹)) ?_ ?_ hv, Finset.sum_product]
    · refine Finset.sum_congr rfl fun u _ => ?_

      rw [map_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [mul]
      congr 2
      simp only [id]
      group
    · intro p hp
      rw [Finset.mem_product] at hp
      exact mul_mem (hs _ hp.1) (I.P_N a ha _ (hr _ hp.2))
    · intro x hx
      have e : ∀ u w : G, (a * b)⁻¹ * ((u * (a * w * a⁻¹))⁻¹ * x) * (a * b) =
          b⁻¹ * (w⁻¹ * (a⁻¹ * (u⁻¹ * x) * a)) * b := fun u w => by group
      obtain ⟨u, ⟨hus, hux⟩, hun⟩ := hu x hx
      obtain ⟨w, ⟨hwr, hwx⟩, hwn⟩ := hw _ hux
      refine ⟨(u, w), ⟨Finset.mem_product.2 ⟨hus, hwr⟩, by rw [e]; exact hwx⟩, ?_⟩
      rintro ⟨u', w'⟩ ⟨hp, h⟩
      rw [Finset.mem_product] at hp
      rw [e] at h
      have h1 : a⁻¹ * (u'⁻¹ * x) * a ∈ I.N := by
        have := mul_mem (hr _ hp.2) (I.P_N b hb _ h)
        convert this using 1
        group
      obtain rfl : u' = u := hun u' ⟨hp.1, h1⟩
      obtain rfl : w' = w := hwn w' ⟨hp.2, h⟩
      rfl
  · rw [unit 1 (one_mem _) (by simpa using one_mem I.P)]
    simp
  · intro t ht
    obtain ⟨s, hs, hu⟩ := uOpMul_ex I ha
    have hc : t * a = a * t := I.comm t (I.T_le ht) a (I.P_le a ha)
    have hN : ∀ x ∈ I.N, t⁻¹ * x * t ∈ I.N := fun x hx => by simpa using I.T_N _ (inv_mem ht) x hx
    have htv : π t v ∈ fixd π I.N := by
      intro n hn
      have : n * t = t * (t⁻¹ * n * t) := by group
      rw [mul, this, ← mul, hv _ (hN n hn)]

    rw [uOpMul_sum I π ha s id hs hu hv,
    uOpMul_sum I π ha s (fun u => t * u * t⁻¹) (fun u h => I.T_N t ht u (hs u h)) ?_ htv, map_sum]
    · refine Finset.sum_congr rfl fun u _ => ?_
      rw [mul, mul, mul_assoc _ a t, ← hc]
      congr 2
      simp only [id]
      group
    · intro x hx
      have e : ∀ u : G, a⁻¹ * ((t * u * t⁻¹)⁻¹ * x) * a = t * (a⁻¹ * (u⁻¹ * (t⁻¹ * x * t)) * a) * t⁻¹ := by
        intro u
        have h1 : a⁻¹ * t = t * a⁻¹ := (Commute.inv_left (show Commute a t from hc.symm)).eq
        have h2 : a = t * a * t⁻¹ := by rw [hc]; group
        calc a⁻¹ * ((t * u * t⁻¹)⁻¹ * x) * a = (a⁻¹ * t) * (u⁻¹ * t⁻¹ * x) * a := by group
          _ = (t * a⁻¹) * (u⁻¹ * t⁻¹ * x) * (t * a * t⁻¹) := by rw [h1, ← h2]
          _ = _ := by group
      have e' : ∀ y : G, t * y * t⁻¹ ∈ I.N ↔ y ∈ I.N := fun y =>
        ⟨fun h => by simpa [mul_assoc] using hN _ h, I.T_N t ht y⟩
      simpa only [e, e'] using hu _ (hN x hx)
end
