module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1845
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import GroundTheory.LocalFields.PadicLogSeries
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1879
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1141
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1236
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
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

@[expose] public section

section

open UpperTheory.V.Z.Mult UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
open Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryBC GlobalTheory.LFun Formalism.UG Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.PRep

theorem UpperTheory.V.Z.Mult.lcLev :
    UpperTheory.V.Z.Mult.LcLev := by
  intro E _ _ _ n w hw f hf
  obtain ⟨K', hKo, hKle, hK⟩ := hf
  have hU : UL n w = ⊤ := if_pos hw
  have hcl : IsClosed ((UL n w : Subgroup (GLw n w)) : Set (GLw n w)) := by
    rw [hU]
    exact isClosed_univ
  refine ⟨K'.subgroupOf (UL n w), hKo.preimage continuous_subtype_val, ?_, ?_, ?_⟩
  · intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hKle (Subgroup.mem_subgroupOf.mp hx))
  · exact hK.1.comp_isClosedEmbedding hcl.isClosedEmbedding_subtypeVal
  · intro k hk x
    exact hK.2 k.1 (Subgroup.mem_subgroupOf.mp hk) x.1
end

section

open UpperTheory.V.Z.Mult UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

theorem UpperTheory.V.Z.Mult.offSec :
    UpperTheory.V.Z.Mult.OffSec := by
  intro E _ _ _ n S K' K'' h
  unfold GlobalTheory.BCT.globLev
  refine iInf_congr fun w => iInf_congr fun hw => ?_
  rw [h w hw]
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

namespace UpperTheory.V.Z.Mult

section Generic

variable {G V : Type} [Group G]

private abbrev ind (H : Subgroup G) : G → ℂ := (H : Set G).indicator 1

private theorem ind_mem {H : Subgroup G} {x : G} (hx : x ∈ H) : ind H x = 1 :=
  Set.indicator_of_mem (show x ∈ (H : Set G) from hx) _

private theorem ind_notMem {H : Subgroup G} {x : G} (hx : x ∉ H) : ind H x = 0 :=
  Set.indicator_of_notMem (show x ∉ (H : Set G) from hx) _

private theorem ind_mul_left (H : Subgroup G) {k : G} (hk : k ∈ H) (x : G) :
    ind H (k * x) = ind H x := by
  by_cases hx : x ∈ H
  · rw [ind_mem (H.mul_mem hk hx), ind_mem hx]
  · rw [ind_notMem (fun h => hx ((H.mul_mem_cancel_left hk).1 h)), ind_notMem hx]

private theorem ind_mul_right (H : Subgroup G) {k : G} (hk : k ∈ H) (x : G) :
    ind H (x * k) = ind H x := by
  by_cases hx : x ∈ H
  · rw [ind_mem (H.mul_mem hx hk), ind_mem hx]
  · rw [ind_notMem (fun h => hx ((H.mul_mem_cancel_right hk).1 h)), ind_notMem hx]

private theorem rStab_ind (H : Subgroup G) : rStab (ind H) = H := by
  ext k
  constructor
  · intro hk
    by_contra hn
    have h := hk 1
    rw [one_mul, ind_notMem hn, ind_mem H.one_mem] at h
    exact zero_ne_one h
  · intro hk x
    exact ind_mul_right H hk x

private theorem ind_inv (H : Subgroup G) : (fun y : G => ind H y⁻¹) = ind H := by
  funext y
  by_cases hy : y ∈ H
  · rw [ind_mem (H.inv_mem hy), ind_mem hy]
  · rw [ind_notMem (fun h => hy (by simpa using H.inv_mem h)), ind_notMem hy]

variable [AddCommGroup V] [Module ℂ V]

private theorem levOp_ind (ρ : Representation ℂ G V) (K H : Subgroup G) (x : V) (hx : x ∈ fixed ρ H) :
    levOp ρ K H (ind H) LinearMap.id x = ((H.relIndex K : ℕ) : ℂ)⁻¹ • x := by
  have hfx : ∀ h ∈ H, ρ h x = x := fun h hh => by simpa using hx ⟨h, hh⟩
  have hout : ∀ q : G ⧸ H, q.out ∈ H ↔ q = (QuotientGroup.mk 1 : G ⧸ H) := by
    intro q
    constructor
    · intro h
      have h2 : ((q.out : G) : G ⧸ H) = QuotientGroup.mk 1 :=
        QuotientGroup.eq.2 (by simpa using H.inv_mem h)
      rwa [QuotientGroup.out_eq'] at h2
    · rintro rfl
      obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H (1 : G)
      rw [hh]
      simpa using h.2
  unfold levOp
  rw [finsum_eq_single _ (QuotientGroup.mk 1 : G ⧸ H)]
  · rw [ind_mem ((hout _).2 rfl)]
    simp [hfx _ ((hout _).2 rfl)]
  · intro q hq
    rw [ind_notMem (fun h => hq ((hout q).1 h))]
    simp

private theorem trc_ind_ne (ρ : Representation ℂ G V) (K H : Subgroup G) (hle : H ≤ K) (hi : H.relIndex K ≠ 0)
    (hfd : FiniteDimensional ℂ (fixed ρ H)) (hne : fixed ρ H ≠ ⊥) : trc ρ K (ind H) ≠ 0 := by
  have hlev : K ⊓ rStab (ind H) ⊓ rStab (fun y : G => ind H y⁻¹) = H := by
    rw [ind_inv, rStab_ind, inf_assoc, inf_idem]
    exact inf_eq_right.2 hle
  unfold trc
  rw [hlev]
  have hc : ∀ v ∈ fixed ρ H, levOp ρ K H (ind H) LinearMap.id v ∈ fixed ρ H := by
    intro v hv
    rw [levOp_ind ρ K H v hv]
    exact Submodule.smul_mem _ _ hv
  have hr : (levOp ρ K H (ind H) LinearMap.id).restrict hc = ((H.relIndex K : ℕ) : ℂ)⁻¹ • LinearMap.id := by
    ext v
    simp [LinearMap.restrict_apply, levOp_ind ρ K H v v.2]
  unfold twTr
  rw [dite_eq_left hc, hr, map_smul, LinearMap.trace_id, smul_eq_mul]
  have hpos : Module.finrank ℂ (fixed ρ H) ≠ 0 := fun h0 => hne (Submodule.finrank_eq_zero.1 h0)
  exact mul_ne_zero (inv_ne_zero (by exact_mod_cast hi)) (by exact_mod_cast hpos)

private theorem fixed_map_ne (ρ : Representation ℂ G V) (U : Subgroup G) (K : Subgroup U)
    (h : fixed (ρ.comp U.subtype) K ≠ ⊥) : fixed ρ (K.map U.subtype) ≠ ⊥ := by
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 h
  refine (Submodule.ne_bot_iff _).2 ⟨x, ?_, hx0⟩
  rintro ⟨_, u, hu, rfl⟩
  simpa using hx ⟨u, hu⟩

variable [TopologicalSpace G] [IsTopologicalGroup G]

private theorem map_top_open (U : Subgroup G) (hU : U = ⊤) (K : Subgroup U) (ho : IsOpen (K : Set U)) :
    IsOpen ((K.map U.subtype : Subgroup G) : Set G) := by
  subst hU
  rw [Subgroup.coe_map]
  exact (IsOpen.isOpenMap_subtype_val (by simp)) _ ho

private theorem compact_of_map (U : Subgroup G) (K : Subgroup U)
    (hc : IsCompact ((K.map U.subtype : Subgroup G) : Set G)) : IsCompact (K : Set U) := by
  rw [Subgroup.coe_map] at hc
  exact Topology.IsInducing.subtypeVal.isCompact_iff.2 hc

end Generic

end UpperTheory.V.Z.Mult

theorem UpperTheory.V.Z.Mult.levInd :
    UpperTheory.V.Z.Mult.LevInd := by
  intro E _ _ _ n w hw K hKo hKle
  obtain ⟨ho, hc⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n
  have hU : UL n w = ⊤ := if_pos hw
  let H : Subgroup (GLw n w) := K.map (UL n w).subtype
  have hHo : IsOpen (H : Set (GLw n w)) := map_top_open _ hU K hKo
  have hle : H ≤ GlobalTheory.LFun.KGL w (n := n) := by
    rintro _ ⟨u, hu, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (hKle hu)
  have hHc : IsCompact (H : Set (GLw n w)) := hc.of_isClosed_subset (H.isClosed_of_isOpen hHo) hle
  have hKc : IsCompact (K : Set (UL n w)) := compact_of_map _ K hHc
  have hmem : ∀ x : UL n w, x.1 ∈ H ↔ x ∈ K := fun x => by
    constructor
    · rintro ⟨u, hu, hux⟩
      have : u = x := Subtype.ext hux
      exact this ▸ hu
    · exact fun hx => ⟨x, hx, rfl⟩
  have hi : H.relIndex (GlobalTheory.LFun.KGL w (n := n)) ≠ 0 := by
    haveI : CompactSpace (GlobalTheory.LFun.KGL w (n := n)) := isCompact_iff_compactSpace.1 hc
    haveI : Finite ((GlobalTheory.LFun.KGL w (n := n)) ⧸ H.subgroupOf (GlobalTheory.LFun.KGL w (n := n))) :=
      Subgroup.quotient_finite_of_isOpen _ (hHo.preimage continuous_subtype_val)
    exact (Subgroup.finiteIndex_of_finite_quotient (H := H.subgroupOf (GlobalTheory.LFun.KGL w (n := n)))).index_ne_zero
  refine ⟨ind H, ⟨H, hHo, hle, ?_, ?_⟩, ?_, ?_⟩
  · exact HasCompactSupport.intro' hHc (H.isClosed_of_isOpen hHo) fun x hx => ind_notMem hx
  · exact fun k hk x => ⟨ind_mul_left H hk x, ind_mul_right H hk x⟩
  · intro K₁ hK₁
    refine ⟨HasCompactSupport.intro' hKc (K.isClosed_of_isOpen hKo) fun x hx => ind_notMem fun h => hx ((hmem x).1 h), ?_⟩
    intro k hk x
    have hkH : k.1 ∈ H := (hmem k).2 (hK₁ hk)
    exact ⟨ind_mul_left H hkH x.1, ind_mul_right H hkH x.1⟩
  · intro τ hτ
    exact trc_ind_ne τ.ρ _ H hle hi (finiteDimensional_fixed_openSubgroup_GLw E n w τ H hHo) (fixed_map_ne τ.ρ _ K hτ)
end
end

section

open UpperTheory.V.Z.Mult UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun

private theorem trc_of_equiv {G V V' : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    {ρ : Representation ℂ G V} {ρ' : Representation ℂ G V'} (e : ρ.Equiv ρ') (K : Subgroup G) (f : G → ℂ) :
    trc ρ K f = trc ρ' K f := by
  have hid : e.toLinearEquiv.toLinearMap ∘ₗ LinearMap.id ∘ₗ e.toLinearEquiv.symm.toLinearMap = LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    exact e.toLinearEquiv.apply_symm_apply v
  have h := GlobalTheory.BCT.twTr_conj_equiv G V V' ρ ρ' e K (K ⊓ GlobalTheory.BCT.rStab f ⊓ GlobalTheory.BCT.rStab fun y => f y⁻¹) f LinearMap.id
  rw [hid] at h
  exact h.symm

section Split

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {w : Pl E}

private theorem mem_UL (hw : IsSplitAt w) (g : GLw n w) : g ∈ UL n w := by
  rw [UL, if_pos hw]
  trivial

private noncomputable def toUL (hw : IsSplitAt w) (τ : SmIrr (GLw n w)) : SmIrr (UL n w) where
  V := τ.V
  ρ := τ.ρ.comp (UL n w).subtype
  smooth v := (τ.smooth v).preimage continuous_subtype_val
  irred := by
    obtain ⟨h0, h⟩ := (GlobalTheory.CuspRep.isIrreducible_iff _).1 τ.irred
    exact (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨h0, fun W hW => h W fun g x hx => hW ⟨g, mem_UL hw g⟩ x hx⟩

private theorem isCompU_toUL (hw : IsSplitAt w) {σ : Submodule ℂ (UA E n → ℂ)} {τ : SmIrr (GLw n w)} (h : Cp σ w τ) :
    IsCompU σ w (toUL hw τ) := by
  obtain ⟨-, F, hF0, hFσ, hF⟩ := h
  refine ⟨{ toFun := fun x => ⟨cLoc w x.1, mem_UL hw _⟩
            map_one' := Subtype.ext (by simp)
            map_mul' := fun a b => Subtype.ext (by simp) }, fun _ => rfl, (toUL hw τ).irred, F, hF0, hFσ, fun x v => hF x v⟩

private noncomputable def equivOfUL (hw : IsSplitAt w) {τ τ' : SmIrr (GLw n w)} (e : (toUL hw τ).ρ.Equiv (toUL hw τ').ρ) : τ.ρ.Equiv τ'.ρ :=
  Representation.Equiv.mk e.toLinearEquiv fun g => e.isIntertwining' ⟨g, mem_UL hw g⟩

end Split

theorem UpperTheory.V.Z.Mult.cpUniq :
    UpperTheory.V.Z.Mult.CpUniq := by
  intro E _ _ _ hU n hn σ hσ w hw τ τ' h h'
  obtain ⟨e⟩ := (GlobalTheory.T.exists_unique_admissible_localComponent_definiteUnitary E hU n hn σ hσ w).2 (toUL hw τ) (toUL hw τ') (isCompU_toUL hw h) (isCompU_toUL hw h')
  have e' := equivOfUL hw e
  exact ⟨fun B hB => GlobalTheory.PrinSat.hasSatGL_of_equiv e'.symm hB, fun f => trc_of_equiv e' _ f⟩
end
