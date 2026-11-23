module

public import Formalism.LocalToGlobal.NumberFieldFamilies.NPartCNd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Module

namespace Formalism.L2.Fam.NPC.LatticeFinitenessFree

open Formalism.L2.Fam.NPC

theorem span_top_of_image {L : Type*} [Field L] (e : L →+* ℂ) {M V : Type*} [AddCommGroup M] [Module L M] [AddCommGroup V]
    [Module ℂ V] (jm : M →ₛₗ[e] V) {ι : Type*} (b : Module.Basis ι L M) (hb1 : LinearIndependent ℂ (fun k => jm (b k)))
    (hb2 : Submodule.span ℂ (Set.range fun k => jm (b k)) = ⊤) (S : Set M) (hS : Submodule.span ℂ (jm '' S) = ⊤) :
    Submodule.span L S = ⊤ := by
  by_contra hW
  obtain ⟨f, hf0, hfW⟩ := Submodule.exists_le_ker_of_lt_top (Submodule.span L S) (lt_top_iff_ne_top.2 hW)
  let bC : Module.Basis ι ℂ V := Module.Basis.mk hb1 (le_of_eq hb2.symm)
  let F : V →ₗ[ℂ] ℂ := bC.constr ℂ fun k => e (f (b k))
  have hFb : ∀ k, F (jm (b k)) = e (f (b k)) := fun k => by
    have h : jm (b k) = bC k := (Module.Basis.mk_apply hb1 (le_of_eq hb2.symm) k).symm
    rw [h, Module.Basis.constr_basis]
  have hFj : ∀ x, F (jm x) = e (f x) := by
    intro x
    have hx : x ∈ Submodule.span L (Set.range b) := b.span_eq ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy => obtain ⟨k, rfl⟩ := hy; exact hFb k
    | zero => simp
    | add y z _ _ hy hz => rw [map_add (f := _), map_add (f := _), hy, hz, map_add (f := _), map_add (f := _)]
    | smul c y _ hy => rw [LinearMap.map_smulₛₗ, map_smul, hy, map_smul, smul_eq_mul, smul_eq_mul, map_mul]
  have hF0 : F = 0 := by
    refine LinearMap.ext fun v => ?_
    have hv : v ∈ Submodule.span ℂ (jm '' S) := hS ▸ Submodule.mem_top
    induction hv using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, hx, rfl⟩ := hy
      rw [hFj, show f x = 0 from hfW (Submodule.subset_span hx), map_zero]; rfl
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul c x _ hx => simp [hx]
  apply hf0
  refine LinearMap.ext fun x => e.injective ?_
  rw [← hFj, hF0]
  simp

section Loc

variable {O : Type*} [CommRing O] [IsDomain O] {K : Type*} [Field K] [Algebra O K] [IsFractionRing O K]
  {P : Type*} [AddCommGroup P] [Module K P] [Module O P] [IsScalarTower O K P]

theorem isLocalized_of_span (N : Submodule O P) (hN : Submodule.span K (N : Set P) = ⊤) :
    IsLocalizedModule (nonZeroDivisors O) N.subtype := by
  have hK : ∀ s ∈ nonZeroDivisors O, algebraMap O K s ≠ 0 := fun s hs =>
    (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 (nonZeroDivisors.ne_zero hs)
  refine ⟨fun s => ?_, fun y => ?_, fun {a b} h => ⟨1, by simpa using Subtype.ext h⟩⟩
  · rw [Module.End.isUnit_iff]
    have hs := hK s s.2
    refine ⟨fun x y hxy => ?_, fun y => ⟨(algebraMap O K s)⁻¹ • y, ?_⟩⟩
    · have h1 : (algebraMap O K s) • x = (algebraMap O K s) • y := by
        simpa [algebraMap_smul] using hxy
      exact (smul_right_injective P hs) h1
    · show (s : O) • ((algebraMap O K s)⁻¹ • y) = y
      rw [← algebraMap_smul K (s : O), smul_smul, mul_inv_cancel₀ hs, one_smul]
  · have hy : y ∈ Submodule.span K (N : Set P) := hN ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem x hx => exact ⟨⟨⟨x, hx⟩, 1⟩, by simp⟩
    | zero => exact ⟨⟨0, 1⟩, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨⟨a, s⟩, ha⟩ := hx
      obtain ⟨⟨b, t⟩, hb⟩ := hy
      refine ⟨⟨(t : O) • a + (s : O) • b, s * t⟩, ?_⟩
      simp only [Submonoid.smul_def, Submodule.subtype_apply, Submodule.coe_add, Submodule.coe_smul] at ha hb ⊢
      rw [← ha, ← hb, Submonoid.coe_mul, smul_add, mul_smul, mul_smul, smul_comm (t : O) (s : O) x]
    | smul c x _ hx =>
      obtain ⟨⟨a, s⟩, ha⟩ := hx
      obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := O) c
      refine ⟨⟨n • a, ⟨d, hd⟩ * s⟩, ?_⟩
      simp only [Submonoid.smul_def, Submodule.subtype_apply, Submodule.coe_smul] at ha ⊢
      rw [← ha, Submonoid.coe_mul, mul_smul]
      change (d : O) • (s : O) • ((algebraMap O K n / algebraMap O K d) • x) = n • (s : O) • x
      rw [← algebraMap_smul K (d : O), ← algebraMap_smul K (s : O), ← algebraMap_smul K n, ← algebraMap_smul K (s : O) x,
        smul_smul, smul_smul, smul_smul]
      congr 1
      have hd0 : algebraMap O K d ≠ 0 := hK d hd
      field_simp

end Loc

theorem span_image_top {L : Type*} [Field L] {K : Type*} [Field K] (e : L →+* K) {M V : Type*} [AddCommGroup M] [Module L M]
    [AddCommGroup V] [Module K V] (jm : M →ₛₗ[e] V) {ι : Type*} (b : Module.Basis ι L M)
    (hb2 : Submodule.span K (Set.range fun k => jm (b k)) = ⊤) (S : Set M) (hS : Submodule.span L S = ⊤) :
    Submodule.span K (jm '' S) = ⊤ := by
  refine le_antisymm le_top (hb2 ▸ Submodule.span_le.2 ?_)
  rintro _ ⟨k, rfl⟩
  have key : ∀ x ∈ Submodule.span L S, jm x ∈ Submodule.span K (jm '' S) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ hx
  exact key _ (hS ▸ Submodule.mem_top)

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {B : LocBase0 H what₂}

theorem span_latL (i : LocT B) : Submodule.span what₂.LL (latL B i) = ⊤ := by
  have hb := what₂.jMt_basis (what₂.muTw (wOf B i)) (jOf B i) (Module.Free.chooseBasis what₂.LL _)
  refine span_top_of_image what₂.embLL (what₂.jMt (what₂.muTw (wOf B i)) (jOf B i)) _ hb.1 hb.2 _ ?_
  have h := (what₂.MtLat (what₂.muTw (wOf B i)) (jOf B i)).span_top
  refine le_antisymm le_top (h ▸ Submodule.span_mono fun v hv => ?_)
  obtain ⟨x, rfl⟩ := what₂.MtLat_sub _ _ v hv
  exact ⟨x, hv, rfl⟩



theorem span_mtSub (hC : PartCompl B) (i : LocT B) :
    Submodule.span (FractionRing (OOf B i)) ((MtSub B hC i : Submodule (OOf B i) (partOf B i)) : Set (partOf B i)) = ⊤ := by
  have hV := span_image_top (B.ec (jOf B i) (wOf B i)) (B.iV (jOf B i) (wOf B i)) (Module.Free.chooseBasis what₂.LL _)
    (B.iV_basis (jOf B i) (wOf B i) _).2 _ (span_latL i)
  refine le_antisymm le_top ?_
  rintro y -
  obtain ⟨x, rfl⟩ := Submodule.projectionOnto_surjective (hC i) y
  have hx : x ∈ Submodule.span (FractionRing (OOf B i)) (B.iV (jOf B i) (wOf B i) '' latL B i) := hV ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨u, hu, rfl⟩ := hz
    exact Submodule.subset_span (Submodule.subset_span ⟨u, hu, rfl⟩)
  | zero => simp
  | add a b _ _ ha hb => rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha



theorem mtLoc_holds (hC : PartCompl B) : MtLoc B hC := fun i => isLocalized_of_span _ (span_mtSub hC i)

end Formalism.L2.Fam.NPC.LatticeFinitenessFree
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Module

namespace Formalism.L2.Fam.NPC.LatticeFinitenessFree

open Formalism.L2.Fam.NPC



variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (B : LocBase0 H what₂)

theorem jMt_injective (μ : what₂.Tup) (j : ℕ) : Function.Injective (what₂.jMt μ j) := by
  set b := Module.Free.chooseBasis what₂.LL (what₂.MtL μ j)
  have hb := (what₂.jMt_basis μ j b).1
  have key : ∀ z, Finsupp.linearCombination ℂ (fun i => what₂.jMt μ j (b i))
      ((b.repr z).mapRange what₂.embLL (map_zero _)) = what₂.jMt μ j z := by
    intro z
    conv_rhs => rw [← b.linearCombination_repr z]
    rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index (by simp),
      map_finsuppSum]
    simp only [LinearMap.map_smulₛₗ]
  intro x y hxy
  have h1 : what₂.jMt μ j (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  rw [← key] at h1
  have h2 := (linearIndependent_iff.1 hb) _ h1
  have h3 : b.repr (x - y) = 0 := Finsupp.ext fun i => what₂.embLL.injective (by
    have := congrArg (fun f => f i) h2
    simpa using this)
  rw [← sub_eq_zero]
  exact b.repr.injective (h3.trans (map_zero _).symm)

theorem latL_finite (i : LocT B) : (latL B i).Finite := by
  classical
  refine Set.Finite.subset ((what₂.MtLat (what₂.muTw (wOf B i)) (jOf B i)).gen.finite_toSet.preimage
    ((jMt_injective (what₂.muTw (wOf B i)) (jOf B i)).injOn)) fun x hx => hx

variable {B}

instance noZero (i : LocT B) : NoZeroSMulDivisors (OOf B i) (B.V (jOf B i) (wOf B i)) := by
  refine ⟨fun {c x} h => ?_⟩
  have h1 : algebraMap (OOf B i) (FractionRing (OOf B i)) c • x = 0 := by rw [algebraMap_smul]; exact h
  rcases smul_eq_zero.1 h1 with h2 | h2
  · exact Or.inl ((map_eq_zero_iff _ (IsFractionRing.injective _ _)).1 h2)
  · exact Or.inr h2

theorem mtSub_fg (hC : PartCompl B) (i : LocT B) : (MtSub B hC i).FG := by
  classical
  refine ⟨((latL_finite B i).toFinset.image fun x => projOf B hC i (B.iV (jOf B i) (wOf B i) x)), ?_⟩
  unfold MtSub
  congr 1
  ext y
  simp

theorem mtSub_finite (hC : PartCompl B) (i : LocT B) : Module.Finite (OOf B i) (MtSub B hC i) :=
  Module.Finite.iff_fg.2 (mtSub_fg hC i)

theorem mtSub_free (hC : PartCompl B) (i : LocT B) : Module.Free (OOf B i) (MtSub B hC i) := by
  haveI := mtSub_finite hC i
  haveI : NoZeroSMulDivisors (OOf B i) (partOf B i) := by
    refine ⟨fun {c x} h => ?_⟩
    have h1 : c • (x : B.V (jOf B i) (wOf B i)) = 0 := by
      have := congrArg (fun z : partOf B i => (z : B.V (jOf B i) (wOf B i))) h
      simpa using this
    rcases smul_eq_zero.1 h1 with h2 | h2
    · exact Or.inl h2
    · exact Or.inr (Subtype.ext h2)
  exact Module.free_of_finite_type_torsion_free'

end Formalism.L2.Fam.NPC.LatticeFinitenessFree
end
end

section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Module Module.End Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace Formalism.L2.Fam.NPC




section Gen

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (B : LocBase0 H what₂)

theorem prMtC_lat (hC : PartCompl B) (hL : MtLoc B hC) (i : LocT B) (x : what₂.MtL (what₂.muTw (wOf B i)) (jOf B i))
    (hx : x ∈ latL B i) :
    prMtC B hC hL i x = TensorProduct.mk (OOf B i) (FractionRing (OOf B i)) (MtSub B hC i) 1
      ⟨projOf B hC i (B.iV (jOf B i) (wOf B i) x), Submodule.subset_span ⟨x, hx, rfl⟩⟩ := by
  apply (mtEquiv B hC hL i).injective
  have e1 : mtEquiv B hC hL i (prMtC B hC hL i x) = projOf B hC i (B.iV (jOf B i) (wOf B i) x) := by
    simp [prMtC]
  rw [e1, TensorProduct.mk_apply]
  unfold mtEquiv
  rw [IsBaseChange.equiv_tmul, one_smul]
  rfl

theorem prMtC_latSpan (hC : PartCompl B) (hL : MtLoc B hC) (i : LocT B) :
    Submodule.span (OOf B i) (prMtC B hC hL i '' latL B i) =
      LinearMap.range (TensorProduct.mk (OOf B i) (FractionRing (OOf B i)) (MtSub B hC i) 1) := by
  set G : Set (partOf B i) := (fun x => projOf B hC i (B.iV (jOf B i) (wOf B i) x)) '' latL B i with hG
  have e : prMtC B hC hL i '' latL B i =
      (TensorProduct.mk (OOf B i) (FractionRing (OOf B i)) (MtSub B hC i) 1) '' ((↑) ⁻¹' G : Set (MtSub B hC i)) := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨_, ⟨x, hx, rfl⟩, (prMtC_lat B hC hL i x hx).symm⟩
    · rintro ⟨m, ⟨x, hx, hmx⟩, rfl⟩
      refine ⟨x, hx, ?_⟩
      rw [prMtC_lat B hC hL i x hx]
      congr 1
      exact Subtype.ext hmx
  have htop : Submodule.span (OOf B i) ((↑) ⁻¹' G : Set (MtSub B hC i)) = ⊤ := Submodule.span_span_coe_preimage
  rw [e, Submodule.span_image, htop, Submodule.map_top]

theorem prMtC_span (hC : PartCompl B) (hL : MtLoc B hC) (i : LocT B) :
    Submodule.span (FractionRing (OOf B i)) (Set.range (prMtC B hC hL i)) = ⊤ := by
  let b := Module.Free.chooseBasis what₂.LL (what₂.MtL (what₂.muTw (wOf B i)) (jOf B i))
  have hb := (B.iV_basis (jOf B i) (wOf B i) b).2
  have h1 : Submodule.span (FractionRing (OOf B i)) (Set.range (B.iV (jOf B i) (wOf B i))) = ⊤ :=
    eq_top_iff.2 (hb ▸ Submodule.span_mono (Set.range_comp_subset_range b (B.iV (jOf B i) (wOf B i))))
  have h2 : Set.range (prMtC B hC hL i) =
      (mtEquiv B hC hL i).symm.toLinearMap '' (projOf B hC i '' Set.range (B.iV (jOf B i) (wOf B i))) := by
    ext z
    simp [prMtC]
  have h3 : LinearMap.range (projOf B hC i) = ⊤ := Submodule.linearProjOfIsCompl_range (hC i)
  rw [h2, Submodule.span_image, Submodule.span_image, h1, Submodule.map_top, h3, Submodule.map_top,
    LinearMap.range_eq_top.2 (mtEquiv B hC hL i).symm.surjective]

end Gen

end Formalism.L2.Fam.NPC
end
end
