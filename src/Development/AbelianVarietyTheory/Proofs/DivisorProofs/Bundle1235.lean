module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

noncomputable section

namespace GlobalTheory.TwTrLevel

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem mem_fixed_iff (ρ : Representation ℂ G V) (H : Subgroup G) (v : V) :
    v ∈ fixed ρ H ↔ ∀ h ∈ H, ρ h v = v := by
  simp [fixed, GlobalTheory.PRep.eig]

theorem out_eq_of_inv {M : Type} (H : Subgroup G) (F : G → M) (hF : ∀ g, ∀ h ∈ H, F (g * h) = F g) (g : G) :
    F (QuotientGroup.mk g : G ⧸ H).out = F g := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
  rw [hh, hF g h h.2]

theorem finite_supp [TopologicalSpace G] [IsTopologicalGroup G] (H : Subgroup G) (hH : IsOpen (H : Set G))
    (f : G → ℂ) (hf : HasCompactSupport f) : {q : G ⧸ H | f q.out ≠ 0}.Finite := by
  haveI := QuotientGroup.discreteTopology hH
  have hc : IsCompact ((QuotientGroup.mk : G → G ⧸ H) '' tsupport f) :=
    hf.isCompact.image QuotientGroup.continuous_mk
  refine hc.finite_of_discrete.subset ?_
  intro q hq
  exact ⟨q.out, subset_tsupport f hq, QuotientGroup.out_eq' q⟩

theorem levOp_apply (ρ : Representation ℂ G V) (K H : Subgroup G) (f : G → ℂ) (A : V →ₗ[ℂ] V) (v : V)
    (hs : {q : G ⧸ H | f q.out ≠ 0}.Finite) :
    levOp ρ K H f A v = ((H.relIndex K : ℕ) : ℂ)⁻¹ • ∑ᶠ q : G ⧸ H, f q.out • ρ q.out (A v) := by
  unfold levOp
  rw [LinearMap.smul_apply]
  congr 1
  have := AddMonoidHom.map_finsum (LinearMap.applyₗ (R := ℂ) (M := V) (M₂ := V) v).toAddMonoidHom
    (f := fun q : G ⧸ H => f q.out • (ρ q.out ∘ₗ A)) (hs.subset ?_)
  · simpa using this
  · intro q hq
    simp only [Function.mem_support, ne_eq, Set.mem_setOf_eq] at hq ⊢
    intro h0
    exact hq (by rw [h0, zero_smul])

theorem A_mem_fixed (ρ : Representation ℂ G V) (θ : G →* G) (hθ : ∀ g, θ (θ g) = g) (A : V →ₗ[ℂ] V)
    (hA : ∀ g, A ∘ₗ ρ g = ρ (θ g) ∘ₗ A) (H : Subgroup G) (hH : ∀ k ∈ H, θ k ∈ H) (w : V)
    (hw : w ∈ fixed ρ H) : A w ∈ fixed ρ H := by
  rw [mem_fixed_iff] at hw ⊢
  intro k hk
  have h1 := LinearMap.congr_fun (hA (θ k)) w
  simp only [LinearMap.coe_comp, Function.comp_apply, hθ] at h1
  rw [← h1, hw _ (hH k hk)]

theorem levOp_mem_fixed [TopologicalSpace G] [IsTopologicalGroup G] (ρ : Representation ℂ G V) (θ : G →* G)
    (hθ : ∀ g, θ (θ g) = g) (A : V →ₗ[ℂ] V) (hA : ∀ g, A ∘ₗ ρ g = ρ (θ g) ∘ₗ A) (K H : Subgroup G)
    (hHo : IsOpen (H : Set G)) (hH : ∀ k ∈ H, θ k ∈ H) (f : G → ℂ) (hf : IsHecke H f) (v : V)
    (hv : v ∈ fixed ρ H) : levOp ρ K H f A v ∈ fixed ρ H := by
  have hs := finite_supp H hHo f hf.1
  have hu := A_mem_fixed ρ θ hθ A hA H hH v hv
  rw [mem_fixed_iff] at hu
  rw [levOp_apply ρ K H f A v hs, mem_fixed_iff]
  intro k hk
  set F : G → V := fun g => f g • ρ g (A v) with hFdef
  have hF : ∀ g, ∀ h ∈ H, F (g * h) = F g := by
    intro g h hh
    simp only [hFdef, (hf.2 h hh g).2, map_mul, Module.End.mul_apply, hu h hh]
  have hsupp : (Function.support fun q : G ⧸ H => F q.out).Finite := by
    refine hs.subset ?_
    intro q hq
    simp only [Function.mem_support, ne_eq, Set.mem_setOf_eq, hFdef] at hq ⊢
    intro h0
    exact hq (by rw [h0, zero_smul])
  rw [map_smul]
  congr 1
  change ρ k (∑ᶠ q : G ⧸ H, F q.out) = ∑ᶠ q : G ⧸ H, F q.out
  have hm := AddMonoidHom.map_finsum (ρ k).toAddMonoidHom hsupp
  simp only [LinearMap.toAddMonoidHom_coe] at hm
  rw [hm]
  have hk' : ∀ q : G ⧸ H, ρ k (F q.out) = F (k • q).out := by
    intro q
    have e1 : (k • q : G ⧸ H) = QuotientGroup.mk (k * q.out) := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    rw [e1, out_eq_of_inv H F hF]
    simp only [hFdef, map_smul, map_mul, Module.End.mul_apply, (hf.2 k hk q.out).1]
  simp_rw [hk']
  exact finsum_comp_equiv (MulAction.toPerm k : Equiv.Perm (G ⧸ H)) (f := fun q : G ⧸ H => F q.out)

def avgOp (ρ : Representation ℂ G V) (K' K'' : Subgroup G) : V →ₗ[ℂ] V :=
  ((K''.relIndex K' : ℕ) : ℂ)⁻¹ • ∑ᶠ j : K' ⧸ K''.subgroupOf K', ρ (j.out : G)

theorem finite_quot [TopologicalSpace G] [IsTopologicalGroup G] (K K' K'' : Subgroup G)
    (hK : IsCompact (K : Set G)) (h' : IsOpen (K' : Set G)) (h'' : IsOpen (K'' : Set G)) (hle : K' ≤ K) :
    Finite (K' ⧸ K''.subgroupOf K') := by
  have hc : IsCompact (K' : Set G) := hK.of_isClosed_subset (Subgroup.isClosed_of_isOpen K' h') hle
  haveI : CompactSpace K' := isCompact_iff_compactSpace.mp hc
  have ho : IsOpen ((K''.subgroupOf K' : Subgroup K') : Set K') := h''.preimage continuous_subtype_val
  haveI := QuotientGroup.discreteTopology ho
  exact finite_of_compact_of_discrete

theorem avgOp_apply (ρ : Representation ℂ G V) (K' K'' : Subgroup G) [Finite (K' ⧸ K''.subgroupOf K')] (u : V) :
    avgOp ρ K' K'' u = ((K''.relIndex K' : ℕ) : ℂ)⁻¹ • ∑ᶠ j : K' ⧸ K''.subgroupOf K', ρ (j.out : G) u := by
  unfold avgOp
  rw [LinearMap.smul_apply]
  congr 1
  have := AddMonoidHom.map_finsum (LinearMap.applyₗ (R := ℂ) (M := V) (M₂ := V) u).toAddMonoidHom
    (f := fun j : K' ⧸ K''.subgroupOf K' => ρ (j.out : G)) (Set.toFinite _)
  simpa using this

theorem levOp_le [TopologicalSpace G] [IsTopologicalGroup G] (ρ : Representation ℂ G V) (K K' K'' : Subgroup G)
    (hle : K'' ≤ K') (hK'K : K' ≤ K) [Finite (K' ⧸ K''.subgroupOf K')] (h'o : IsOpen (K' : Set G))
    (h''o : IsOpen (K'' : Set G)) (f : G → ℂ) (hf : IsHecke K' f) (u : V) (hu : u ∈ fixed ρ K'') :
    levOp ρ K K'' f LinearMap.id u = levOp ρ K K' f LinearMap.id (avgOp ρ K' K'' u) := by
  have hs' := finite_supp K' h'o f hf.1
  have hs'' := finite_supp K'' h''o f hf.1
  rw [mem_fixed_iff] at hu
  rw [levOp_apply ρ K K'' f _ u hs'', levOp_apply ρ K K' f _ _ hs', avgOp_apply]
  simp only [LinearMap.id_apply]
  set F : G → V := fun g => f g • ρ g u with hFdef
  have hF : ∀ g, ∀ h ∈ K'', F (g * h) = F g := by
    intro g h hh
    simp only [hFdef, (hf.2 h (hle hh) g).2, map_mul, Module.End.mul_apply, hu h hh]
  set e := Subgroup.quotientEquivProdOfLE hle with hedef
  have he : ∀ (q : G ⧸ K') (j : K' ⧸ K''.subgroupOf K'),
      F (e.symm (q, j)).out = f q.out • ρ q.out (ρ (j.out : G) u) := by
    intro q j
    have h1 : e.symm (q, j) = (QuotientGroup.mk (q.out * (j.out : G)) : G ⧸ K'') := by
      rw [hedef, Subgroup.quotientEquivProdOfLE_symm_apply]
      conv_lhs => rw [← QuotientGroup.out_eq' j]
      rfl
    rw [h1, out_eq_of_inv K'' F hF]
    simp only [hFdef, (hf.2 _ (j.out).2 q.out).2, map_mul, Module.End.mul_apply]
  set S : G ⧸ K' → V := fun q => ∑ᶠ j : K' ⧸ K''.subgroupOf K', f q.out • ρ q.out (ρ (j.out : G) u) with hSdef
  have hL : ∑ᶠ r : G ⧸ K'', F r.out = ∑ᶠ q, S q := by
    rw [← finsum_comp_equiv e.symm]
    rw [finsum_curry]
    · simp only [he, hSdef]
    · refine (hs'.prod (Set.finite_univ (α := K' ⧸ K''.subgroupOf K'))).subset ?_
      rintro ⟨q, j⟩ hp
      simp only [Function.mem_support, ne_eq, he] at hp
      simp only [Set.mem_prod, Set.mem_setOf_eq, Set.mem_univ, and_true]
      intro h0
      exact hp (by rw [h0, zero_smul])
  have hR : ∀ q : G ⧸ K', f q.out • ρ q.out (((K''.relIndex K' : ℕ) : ℂ)⁻¹ •
      ∑ᶠ j : K' ⧸ K''.subgroupOf K', ρ (j.out : G) u) = ((K''.relIndex K' : ℕ) : ℂ)⁻¹ • S q := by
    intro q
    have hm := AddMonoidHom.map_finsum (f q.out • ρ q.out).toAddMonoidHom
      (f := fun j : K' ⧸ K''.subgroupOf K' => ρ (j.out : G) u) (Set.toFinite _)
    simp only [LinearMap.toAddMonoidHom_coe, LinearMap.smul_apply] at hm
    rw [map_smul, smul_comm, hm]
  simp only [hR]
  rw [hL, ← smul_finsum, smul_smul, ← Subgroup.relIndex_mul_relIndex K'' K' K hle hK'K]
  congr 1
  push_cast
  rw [mul_inv, mul_comm]

theorem avgOp_mem (ρ : Representation ℂ G V) (K' K'' : Subgroup G) [Finite (K' ⧸ K''.subgroupOf K')] (u : V)
    (hu : u ∈ fixed ρ K'') : avgOp ρ K' K'' u ∈ fixed ρ K' := by
  rw [mem_fixed_iff] at hu
  rw [avgOp_apply, mem_fixed_iff]
  intro k hk
  set F : K' → V := fun x => ρ (x : G) u with hFdef
  have hF : ∀ x : K', ∀ h ∈ K''.subgroupOf K', F (x * h) = F x := by
    intro x h hh
    simp only [hFdef, Subgroup.coe_mul, map_mul, Module.End.mul_apply, hu _ (Subgroup.mem_subgroupOf.mp hh)]
  rw [map_smul]
  congr 1
  change ρ k (∑ᶠ j : K' ⧸ K''.subgroupOf K', F j.out) = ∑ᶠ j : K' ⧸ K''.subgroupOf K', F j.out
  have hm := AddMonoidHom.map_finsum (ρ k).toAddMonoidHom (f := fun j : K' ⧸ K''.subgroupOf K' => F j.out)
    (Set.toFinite _)
  simp only [LinearMap.toAddMonoidHom_coe] at hm
  rw [hm]
  have hk' : ∀ j : K' ⧸ K''.subgroupOf K', ρ k (F j.out) = F ((⟨k, hk⟩ : K') • j).out := by
    intro j
    have e1 : ((⟨k, hk⟩ : K') • j : K' ⧸ K''.subgroupOf K') = QuotientGroup.mk ((⟨k, hk⟩ : K') * j.out) := by
      conv_lhs => rw [← QuotientGroup.out_eq' j]
      rfl
    rw [e1, out_eq_of_inv _ F hF]
    simp only [hFdef, Subgroup.coe_mul, map_mul, Module.End.mul_apply]
  simp_rw [hk']
  exact finsum_comp_equiv (MulAction.toPerm (⟨k, hk⟩ : K') : Equiv.Perm (K' ⧸ K''.subgroupOf K'))
    (f := fun j : K' ⧸ K''.subgroupOf K' => F j.out)

theorem avgOp_fix (ρ : Representation ℂ G V) (K' K'' : Subgroup G) [Finite (K' ⧸ K''.subgroupOf K')] (u : V)
    (hu : u ∈ fixed ρ K') : avgOp ρ K' K'' u = u := by
  rw [mem_fixed_iff] at hu
  rw [avgOp_apply]
  have h1 : ∀ j : K' ⧸ K''.subgroupOf K', ρ (j.out : G) u = u := fun j => hu _ (j.out).2
  simp only [h1]
  haveI := Fintype.ofFinite (K' ⧸ K''.subgroupOf K')
  rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  have h2 : (K''.relIndex K' : ℕ) = Fintype.card (K' ⧸ K''.subgroupOf K') := by
    rw [Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]
  have h3 : (Fintype.card (K' ⧸ K''.subgroupOf K') : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := K' ⧸ K''.subgroupOf K')).ne'
  rw [h2, inv_mul_cancel₀ h3, one_smul]

end GlobalTheory.TwTrLevel
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

noncomputable section

namespace GlobalTheory.TwOrbConj

variable {G : Type} [Group G]

theorem mem_rStab {H : Type} [Group H] (u : H → ℂ) (k : H) : k ∈ GlobalTheory.BCT.rStab u ↔ ∀ x, u (x * k) = u x := Iff.rfl

theorem mem_twCent (θ : G →* G) (δ x : G) : x ∈ GlobalTheory.BCT.twCent θ δ ↔ x * δ = δ * θ x := Iff.rfl

theorem relIndex_map_equiv (φ : G ≃* G) (H L : Subgroup G) :
    (H.map φ.toMonoidHom).relIndex (L.map φ.toMonoidHom) = H.relIndex L := by
  first
  | (rw [Subgroup.map_equiv_eq_comap_symm, Subgroup.relIndex_comap, Subgroup.map_map]; simp)
  | exact Subgroup.relIndex_map_map_of_injective _ _ φ.injective
  | simp [Subgroup.relIndex]

theorem avg_left {H : Type} [Group H] (u : H → ℂ) (a : H) :
    GlobalTheory.BCT.avg (fun h => u (a * h)) = GlobalTheory.BCT.avg u := by
  have hR : GlobalTheory.BCT.rStab (fun h => u (a * h)) = GlobalTheory.BCT.rStab u := by
    ext k
    rw [mem_rStab, mem_rStab]
    constructor
    · intro h x
      simpa [mul_assoc] using h (a⁻¹ * x)
    · intro h x
      simpa [mul_assoc] using h (a * x)
  unfold GlobalTheory.BCT.avg
  rw [hR]
  congr 1
  have hc : ∀ q : H ⧸ GlobalTheory.BCT.rStab u, u (a * q.out) = u (a • q).out := by
    intro q
    obtain ⟨r, hr⟩ := QuotientGroup.mk_out_eq_mul (GlobalTheory.BCT.rStab u) (a * q.out)
    have hq : (a • q) = (QuotientGroup.mk (a * q.out) : H ⧸ GlobalTheory.BCT.rStab u) := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    rw [hq, hr]
    exact ((mem_rStab u r).1 r.2 (a * q.out)).symm
  simp_rw [hc]
  exact finsum_comp_equiv (f := fun q : H ⧸ GlobalTheory.BCT.rStab u => u q.out) (MulAction.toPerm a)

theorem map_conj_self (H : Subgroup G) {h : G} (hh : h ∈ H) :
    H.map (MulAut.conj h).toMonoidHom = H := by
  ext x
  rw [Subgroup.mem_map_equiv]
  simp only [MulAut.conj_symm_apply]
  constructor
  · intro hx
    have := H.mul_mem (H.mul_mem hh hx) (H.inv_mem hh)
    simpa [mul_assoc] using this
  · intro hx
    exact H.mul_mem (H.mul_mem (H.inv_mem hh) hx) hh

theorem map_conj_mul (L : Subgroup G) (a b : G) :
    L.map (MulAut.conj (a * b)).toMonoidHom = (L.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem twCent_conj (θ : G →* G) (δ g : G) :
    GlobalTheory.BCT.twCent θ (g⁻¹ * δ * θ g) = (GlobalTheory.BCT.twCent θ δ).map (MulAut.conj g⁻¹).toMonoidHom := by
  ext x
  rw [Subgroup.mem_map_equiv]
  have e : (MulAut.conj g⁻¹).symm x = g * x * g⁻¹ := by simp [MulAut.conj_symm_apply]
  rw [e, mem_twCent, mem_twCent, map_mul, map_mul, map_inv]
  constructor
  · intro h
    calc g * x * g⁻¹ * δ = g * (x * (g⁻¹ * δ * θ g)) * (θ g)⁻¹ := by group
      _ = g * (g⁻¹ * δ * θ g * θ x) * (θ g)⁻¹ := by rw [h]
      _ = δ * (θ g * θ x * (θ g)⁻¹) := by group
  · intro h
    calc x * (g⁻¹ * δ * θ g) = g⁻¹ * (g * x * g⁻¹ * δ) * θ g := by group
      _ = g⁻¹ * (δ * (θ g * θ x * (θ g)⁻¹)) * θ g := by rw [h]
      _ = g⁻¹ * δ * θ g * θ x := by group

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem cptPart_map (c : G) (T : Subgroup G) :
    GlobalTheory.BCT.cptPart (T.map (MulAut.conj c).toMonoidHom) = (GlobalTheory.BCT.cptPart T).map (MulAut.conj c).toMonoidHom := by
  unfold GlobalTheory.BCT.cptPart
  rw [MonoidHom.map_closure]
  congr 1
  let h : G ≃ₜ G := (Homeomorph.mulLeft c).trans (Homeomorph.mulRight c⁻¹)
  have hh : ∀ x, h x = (MulAut.conj c).toMonoidHom x := fun x => by
    simp [h, MulAut.conj_apply]
  have hz : ∀ t, (Subgroup.zpowers ((MulAut.conj c).toMonoidHom t) : Set G) = h '' (Subgroup.zpowers t : Set G) := by
    intro t
    rw [← MonoidHom.map_zpowers, Subgroup.coe_map]
    ext y
    simp only [Set.mem_image, hh]
  have hk : ∀ t, IsCompact (closure (Subgroup.zpowers ((MulAut.conj c).toMonoidHom t) : Set G)) ↔
      IsCompact (closure (Subgroup.zpowers t : Set G)) := by
    intro t
    rw [hz, ← Homeomorph.image_closure, Homeomorph.isCompact_image]
  ext x
  constructor
  · rintro ⟨⟨t, ht, rfl⟩, hc⟩
    exact ⟨t, ⟨ht, (hk t).1 hc⟩, rfl⟩
  · rintro ⟨t, ⟨ht, hc⟩, rfl⟩
    exact ⟨⟨t, ht, rfl⟩, (hk t).2 hc⟩

theorem relIndex_conj (c : G) (T T' L L' : Subgroup G) (hT : T' = T.map (MulAut.conj c).toMonoidHom)
    (hL : L' = L.map (MulAut.conj c).toMonoidHom) :
    (T' ⊓ L').relIndex (GlobalTheory.BCT.cptPart T') = (T ⊓ L).relIndex (GlobalTheory.BCT.cptPart T) := by
  subst hT hL
  rw [← Subgroup.map_inf_eq _ _ _ (MulAut.conj c).injective, cptPart_map, relIndex_map_equiv]

def summand (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ) (y : G) : ℂ :=
  (((GlobalTheory.BCT.twCent θ δ ⊓ K.map (MulAut.conj y).toMonoidHom).relIndex (GlobalTheory.BCT.cptPart (GlobalTheory.BCT.twCent θ δ)) : ℕ) : ℂ) *
    GlobalTheory.BCT.avg fun k : K => f ((y * k)⁻¹ * δ * θ (y * k))

theorem twOrb_eq (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ) :
    GlobalTheory.BCT.twOrb θ K δ f = ∑ᶠ q : DoubleCoset.Quotient (GlobalTheory.BCT.twCent θ δ : Set G) (K : Set G),
      summand θ K δ f (Quotient.out q) := rfl

theorem summand_rep (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ) (y : G) {t k : G}
    (ht : t ∈ GlobalTheory.BCT.twCent θ δ) (hk : k ∈ K) : summand θ K δ f (t * y * k) = summand θ K δ f y := by
  unfold summand
  congr 1
  · exact congrArg (fun n : ℕ => (n : ℂ)) (relIndex_conj t _ _ _ _ (map_conj_self _ ht).symm
      (by rw [map_conj_mul, map_conj_mul, map_conj_self K hk]))
  · have hd : t⁻¹ * δ * θ t = δ := by
      rw [mul_assoc, ← (mem_twCent θ δ t).1 ht, inv_mul_cancel_left]
    have hfun : (fun k' : K => f ((t * y * k * k')⁻¹ * δ * θ (t * y * k * k'))) =
        fun k' : K => (fun k'' : K => f ((y * k'')⁻¹ * δ * θ (y * k''))) (⟨k, hk⟩ * k') := by
      funext k'
      congr 1
      simp only [Subgroup.coe_mul]
      calc (t * y * k * ↑k')⁻¹ * δ * θ (t * y * k * ↑k')
          = (y * (k * ↑k'))⁻¹ * (t⁻¹ * δ * θ t) * θ (y * (k * ↑k')) := by
            simp only [map_mul, _root_.mul_inv_rev]; group
        _ = (y * (k * ↑k'))⁻¹ * δ * θ (y * (k * ↑k')) := by rw [hd]
    rw [hfun]
    exact avg_left (fun k'' : K => f ((y * k'')⁻¹ * δ * θ (y * k''))) ⟨k, hk⟩

theorem summand_twist (θ : G →* G) (K : Subgroup G) (δ g : G) (f : G → ℂ) (x : G) :
    summand θ K (g⁻¹ * δ * θ g) f x = summand θ K δ f (g * x) := by
  unfold summand
  congr 1
  · exact congrArg (fun n : ℕ => (n : ℂ)) (relIndex_conj g⁻¹ _ _ _ _ (twCent_conj θ δ g)
      (by rw [← map_conj_mul, inv_mul_cancel_left]))
  · congr 1
    funext k
    congr 1
    simp only [map_mul, _root_.mul_inv_rev]
    group

def dcEquiv (θ : G →* G) (K : Subgroup G) (δ g : G) :
    DoubleCoset.Quotient (GlobalTheory.BCT.twCent θ (g⁻¹ * δ * θ g) : Set G) (K : Set G) ≃
      DoubleCoset.Quotient (GlobalTheory.BCT.twCent θ δ : Set G) (K : Set G) where
  toFun q := DoubleCoset.mk (GlobalTheory.BCT.twCent θ δ) K (g * Quotient.out q)
  invFun q := DoubleCoset.mk (GlobalTheory.BCT.twCent θ (g⁻¹ * δ * θ g)) K (g⁻¹ * Quotient.out q)
  left_inv q := by
    obtain ⟨t, ht, k, hk, he⟩ :=
      DoubleCoset.mk_out_eq_mul (GlobalTheory.BCT.twCent θ δ) K (g * Quotient.out q)
    show DoubleCoset.mk _ K (g⁻¹ * Quotient.out (DoubleCoset.mk (GlobalTheory.BCT.twCent θ δ) K (g * Quotient.out q))) = q
    rw [he]
    conv_rhs => rw [← DoubleCoset.out_eq' (H := GlobalTheory.BCT.twCent θ (g⁻¹ * δ * θ g)) (K := K) q]
    rw [DoubleCoset.eq]
    refine ⟨g⁻¹ * t⁻¹ * g, ?_, k⁻¹, K.inv_mem hk, by group⟩
    rw [twCent_conj]
    exact ⟨t⁻¹, (GlobalTheory.BCT.twCent θ δ).inv_mem ht, by simp [MulAut.conj_apply]⟩
  right_inv q := by
    obtain ⟨t, ht, k, hk, he⟩ :=
      DoubleCoset.mk_out_eq_mul (GlobalTheory.BCT.twCent θ (g⁻¹ * δ * θ g)) K (g⁻¹ * Quotient.out q)
    show DoubleCoset.mk _ K (g * Quotient.out (DoubleCoset.mk (GlobalTheory.BCT.twCent θ (g⁻¹ * δ * θ g)) K
      (g⁻¹ * Quotient.out q))) = q
    rw [he]
    conv_rhs => rw [← DoubleCoset.out_eq' (H := GlobalTheory.BCT.twCent θ δ) (K := K) q]
    rw [DoubleCoset.eq]
    rw [twCent_conj] at ht
    obtain ⟨s, hs, rfl⟩ := ht
    refine ⟨s⁻¹, (GlobalTheory.BCT.twCent θ δ).inv_mem hs, k⁻¹, K.inv_mem hk, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

end GlobalTheory.TwOrbConj

namespace GlobalTheory.TwOrbConj

theorem twOrb_twConj : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (θ : G →* G) (K : Subgroup G)
    (δ g : G) (f : G → ℂ), (∀ x : G, (GlobalTheory.BCT.rStab fun k : K => f ((x * k)⁻¹ * δ * θ (x * k))).index ≠ 0) →
    GlobalTheory.BCT.twOrb θ K (g⁻¹ * δ * θ g) f = GlobalTheory.BCT.twOrb θ K δ f := by
  intro G _ _ _ θ K δ g f _
  rw [twOrb_eq, twOrb_eq]
  calc ∑ᶠ q, summand θ K (g⁻¹ * δ * θ g) f (Quotient.out q)
      = ∑ᶠ q, summand θ K δ f (Quotient.out (dcEquiv θ K δ g q)) := by
        refine finsum_congr fun q => ?_
        rw [summand_twist]
        obtain ⟨t, ht, k, hk, he⟩ :=
          DoubleCoset.mk_out_eq_mul (GlobalTheory.BCT.twCent θ δ) K (g * Quotient.out q)
        show _ = summand θ K δ f (Quotient.out (DoubleCoset.mk (GlobalTheory.BCT.twCent θ δ) K (g * Quotient.out q)))
        rw [he, summand_rep θ K δ f _ ht hk]
    _ = ∑ᶠ q, summand θ K δ f (Quotient.out q) :=
        finsum_comp_equiv (f := fun q : DoubleCoset.Quotient (GlobalTheory.BCT.twCent θ δ : Set G) (K : Set G) =>
          summand θ K δ f (Quotient.out q)) (dcEquiv θ K δ g)

end GlobalTheory.TwOrbConj
end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RStabFin

theorem rStab_conj_index_ne_zero : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K K' : Subgroup G)
    (f : G → ℂ) (δ : G), IsCompact (K : Set G) → IsOpen (K' : Set G) → K' ≤ K →
    (∀ k ∈ K', ∀ x, f (k * x) = f x ∧ f (x * k) = f x) → ∀ x : G,
    (rStab fun k : K => f ((x * k)⁻¹ * δ * (x * k))).index ≠ 0 := by
  intro G _ _ _ K K' f δ hK hK' _ hf x
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hopen : IsOpen ((K'.subgroupOf K : Subgroup K) : Set K) := hK'.preimage continuous_subtype_val
  have hfin : Finite (K ⧸ K'.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ hopen
  have h0 : (K'.subgroupOf K).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hle : K'.subgroupOf K ≤ rStab fun k : K => f ((x * k)⁻¹ * δ * (x * k)) := by
    intro k hk y
    have hk' : ((k : K) : G) ∈ K' := hk
    show f ((x * ((y * k : K) : G))⁻¹ * δ * (x * ((y * k : K) : G))) = f ((x * (y : G))⁻¹ * δ * (x * (y : G)))
    have e : (x * ((y * k : K) : G))⁻¹ * δ * (x * ((y * k : K) : G))
        = ((k : G))⁻¹ * ((x * (y : G))⁻¹ * δ * (x * (y : G)) * (k : G)) := by
      simp only [Subgroup.coe_mul, _root_.mul_inv_rev]; group
    rw [e, (hf _ (inv_mem hk') _).1, (hf _ hk' _).2]
  exact fun h => h0 (Nat.eq_zero_of_zero_dvd (h ▸ Subgroup.index_dvd_of_le hle))

end GlobalTheory.RStabFin
end
end
