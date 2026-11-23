module

public import Formalism.SharpRestriction.GrowthBounds.CovariantDegrees
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle003
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.BinomialPreservesDiagonalStable
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle006
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle014
import Formalism.SharpRestriction.GrowthBounds.RootWeights.LoweringWordWeightOrNMinus
import Formalism.SharpRestriction.GrowthBounds.RootWeights.MemWeightSpaceIffDiagonalEigen
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle011
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle013
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.EquivariantInjectiveOfCyclic
import Formalism.SharpRestriction.GrowthBounds.RootWeights.InvariantProjectionRangeTrivial
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle008
import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle004
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def ExtremalProjectorProperties {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (E : GLOps n K V) (L : ℕ) : Prop :=
  ∀ (c : Fin n) (u : V), u ∈ weightSp E 0 → (∀ a b : Fin n, a < c → b < c → E a b u = 0) →
    (∀ j, j < c → E j c (extremalProjector E c L u) = 0) ∧
    (∀ a b : Fin n, a < c → b < c → E a b (extremalProjector E c L u) = 0) ∧
    extremalProjector E c L u ∈ weightSp E 0 ∧
    ∃ w : Fin n → V, extremalProjector E c L u = u + ∑ i ∈ Finset.Iio c, E c i (w i)

theorem denominator_chain_bound (D : Formalism.BasicNotions.D7) (h2 : adm2 D) (p : ℕ) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CharZero (KK O)] (n : ℕ) (V : Type) [AddCommGroup V]
    [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V] [FiniteDimensional (KK O) V]
    (E : GLOps n (KK O) V) (hE : IsGLRep E) (M : Submodule O V)
    (Inv : Module.End (KK O) V) (hInv : IsInvProj E Inv) (L de : ℕ) (hA : ExtremalProjectorProperties E L)
    (hB : ∀ (c : Fin n) (y : V), y ∈ M → ((p : O) ^ (c.val * de)) • extremalProjector E c L y ∈ M)
    (x0 : V) (hx0 : x0 ∈ weightSp E 0) (hxM : x0 ∈ M) (c : ℕ) (hc : c ≤ n) :
    ∃ y, y ∈ weightSp E 0 ∧ (∀ a b : Fin n, a.val < c → b.val < c → E a b y = 0) ∧ Inv y = Inv x0 ∧
      ((p : O) ^ ((∑ i ∈ range c, i) * de)) • y ∈ M := by
  induction c with
  | zero =>
    refine ⟨x0, hx0, fun a b ha _ => absurd ha (Nat.not_lt_zero _), rfl, ?_⟩
    simpa using hxM
  | succ c ih =>
    obtain ⟨y, hy0, hyk, hyI, hyM⟩ := ih (Nat.le_of_succ_le hc)
    have hcn : c < n := hc
    obtain ⟨cf, hcf⟩ : ∃ cf : Fin n, cf.val = c := ⟨⟨c, hcn⟩, rfl⟩
    obtain ⟨hA1, hA2, hA3, w, hw⟩ := hA cf y hy0 (fun a b ha hb =>
      hyk a b (by have := Fin.lt_def.mp ha; omega) (by have := Fin.lt_def.mp hb; omega))
    refine ⟨extremalProjector E cf L y, hA3, ?_, ?_, ?_⟩
    · intro a b ha hb
      rcases Nat.lt_succ_iff_lt_or_eq.mp ha with ha' | ha' <;>
        rcases Nat.lt_succ_iff_lt_or_eq.mp hb with hb' | hb'
      · exact hA2 a b (Fin.lt_def.mpr (by omega)) (Fin.lt_def.mpr (by omega))
      · have hb2 : b = cf := Fin.ext (by omega)
        subst hb2
        exact hA1 a (Fin.lt_def.mpr (by omega))
      · have ha2 : a = cf := Fin.ext (by omega)
        subst ha2
        exact weight_zero_lowering_kills_raising hE hA3 b a (by rintro rfl; omega) (hA1 b (Fin.lt_def.mpr (by omega)))
      · have ha2 : a = cf := Fin.ext (by omega)
        have hb2 : b = cf := Fin.ext (by omega)
        rw [ha2, hb2]
        have h0 := hA3
        simp only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker] at h0
        simpa using h0 cf
    · set_option synthInstance.maxHeartbeats 100000 in
        rw [hw, map_add (f := _), map_sum]
      simp only [invariant_projection_kills_operator D h2 E hE Inv hInv, Finset.sum_const_zero, add_zero]
      exact hyI
    · have hM2 := hB cf _ hyM
      rw [LinearMap.map_smul_of_tower, smul_smul, ← pow_add] at hM2
      have he : (∑ i ∈ range (c + 1), i) * de = cf.val * de + (∑ i ∈ range c, i) * de := by
        rw [Finset.sum_range_succ, hcf]; ring
      rw [he]
      exact hM2

theorem invariant_projection_denominator_bound (D : Formalism.BasicNotions.D7) (h2 : adm2 D) (p : ℕ) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CharZero (KK O)] (n : ℕ) (V : Type) [AddCommGroup V]
    [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V] [FiniteDimensional (KK O) V]
    (E : GLOps n (KK O) V) (hE : IsGLRep E) (M : Submodule O V) (hM : UZStable (O := O) E M)
    (Inv : Module.End (KK O) V) (hInv : IsInvProj E Inv) (L de : ℕ) (hA : ExtremalProjectorProperties E L)
    (hB : ∀ (c : Fin n) (y : V), y ∈ M → ((p : O) ^ (c.val * de)) • extremalProjector E c L y ∈ M)
    (x : V) (hx : x ∈ M) : ((p : O) ^ (N0 n * de)) • Inv x ∈ M := by
  obtain ⟨Θ, hΘ1, hΘ2⟩ := weight_projections_integral_findim E
  obtain ⟨y, hy0, hyk, hyI, hyM⟩ := denominator_chain_bound D h2 p O n V E hE M Inv hInv L de hA hB (Θ 0 x)
    (weight_projection_mem_weightSpace E hE Θ hΘ2 0 x) (binomial_subring_preserves_lattice hM _ (hΘ1 0) x hx) n le_rfl
  have hInvy : Inv y = y := by
    by_cases hy : y = 0
    · rw [hy, map_zero]
    · apply hInv.1
      exact Submodule.subset_span ⟨1, one_mem _, y, ⟨hy, hy0, fun a b _ => hyk a b a.2 b.2⟩, rfl⟩
  rw [invariant_projection_through_zero_weight D h2 E hE Inv hInv Θ hΘ2 x, ← hyI, hInvy]
  rwa [Finset.sum_range_id] at hyM

end Formalism.MainNotions.G.GLWeightTheory
end
end

section

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem v2rep_Umon_stable (E : GLOps n K V) (W : Submodule K V) (hW : IsStableUnderOperators E W) (u : Module.End K V)
    (hu : u ∈ Umon E) : ∀ x ∈ W, u x ∈ W := by
  induction hu using Submonoid.closure_induction with
  | mem u hu => obtain ⟨⟨a, b⟩, rfl⟩ := hu; exact hW a b
  | one => intro x hx; exact hx
  | mul u v _ _ hu hv => intro x hx; exact hu _ (hv x hx)

theorem v2rep_isoIn_stable (E : GLOps n K V) (W : Submodule K V) (mu : Fin n → ℤ) :
    IsStableUnderOperators E (isotypicPartIn E W mu) := by
  intro a b x hx
  unfold isotypicPartIn at hx ⊢
  have h : Submodule.span K {x | ∃ u ∈ Umon E, ∃ v ∈ W, IsHWV E mu v ∧ x = u v} ≤
      (Submodule.span K {x | ∃ u ∈ Umon E, ∃ v ∈ W, IsHWV E mu v ∧ x = u v}).comap (E a b) := by
    rw [Submodule.span_le]
    rintro y ⟨u, hu, v, hv, hhw, rfl⟩
    exact Submodule.subset_span
      ⟨E a b * u, (Umon E).mul_mem (Submonoid.subset_closure ⟨(a, b), rfl⟩) hu, v, hv, hhw, rfl⟩
  exact h hx

theorem v2rep_iSup_stable (E : GLOps n K V) {ι : Sort*} (p : ι → Submodule K V) (hp : ∀ i, IsStableUnderOperators E (p i)) :
    IsStableUnderOperators E (⨆ i, p i) := by
  intro a b x hx
  exact Submodule.iSup_induction (motive := fun y => E a b y ∈ ⨆ i, p i) p hx
    (fun i y hy => Submodule.mem_iSup_of_mem i (hp i a b y hy))
    (by rw [map_zero]; exact zero_mem _)
    (fun y z hy hz => by rw [map_add]; exact add_mem hy hz)

def restrictToStableSubmodule (E : GLOps n K V) (W : Submodule K V) (hW : IsStableUnderOperators E W) : GLOps n K W :=
  fun a b => (E a b).restrict (hW a b)

theorem v2rep_res_apply (E : GLOps n K V) (W : Submodule K V) (hW : IsStableUnderOperators E W) (a b : Fin n) (x : W) :
    ((restrictToStableSubmodule E W hW a b x : W) : V) = E a b x := rfl

theorem v2rep_res_weightSp (E : GLOps n K V) (W : Submodule K V) (hW : IsStableUnderOperators E W) (mu : Fin n → ℤ) :
    weightSp (restrictToStableSubmodule E W hW) mu = (weightSp E mu).comap W.subtype := by
  ext x
  simp only [weightSp, Submodule.mem_comap, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, Submodule.subtype_apply]
  refine forall_congr' fun a => ?_
  rw [← Submodule.coe_eq_zero, Submodule.coe_sub, Submodule.coe_smul, v2rep_res_apply]
  simp

theorem v2rep_res_isGLRep [CharZero K] (E : GLOps n K V) (hR : SatisfiesGLRelations E) (W : Submodule K V)
    [FiniteDimensional K W] (hW : IsStableUnderOperators E W) (hw : W ≤ ⨆ ν, weightSp E ν) : IsGLRep (restrictToStableSubmodule E W hW) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b c d
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have h := v2rep_comm E hR a b c d (x : V)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, v2rep_res_apply]
    rw [h, add_sub_cancel_left]
    congr 1
    · split_ifs <;> simp [v2rep_res_apply]
    · split_ifs <;> simp [v2rep_res_apply]
  · intro x
    exact ⟨⊤, inferInstance, Submodule.mem_top, fun _ _ _ _ => Submodule.mem_top⟩
  · rw [eq_top_iff]
    intro y _
    have h1 := v2rep_graded E W (fun a => hW a a) y y.2 (hw y.2)
    have h2 : (⨆ ν, weightSp E ν ⊓ W) = (⨆ ν, weightSp (restrictToStableSubmodule E W hW) ν).map W.subtype := by
      rw [Submodule.map_iSup]
      refine iSup_congr fun ν => ?_
      rw [v2rep_res_weightSp, Submodule.map_comap_subtype, inf_comm]
    rw [h2] at h1
    obtain ⟨y', hy', hyy⟩ := Submodule.mem_map.1 h1
    have : y' = y := Subtype.ext hyy
    rwa [this] at hy'

theorem stable_subspace_complete_reducibility (D : Formalism.BasicNotions.D7) (h2 : adm2 D) : StableSubspaceCompleteReducibility := by
  intro K V _ _ _ _ n E hR W hfd hW hw
  have := hfd
  set W' : Submodule K V := ⨆ mu, isotypicPartIn E W mu with hW'
  have hW'st : IsStableUnderOperators E W' := v2rep_iSup_stable E _ fun mu => v2rep_isoIn_stable E W mu
  obtain ⟨P2, hcompl, hP2⟩ := h2 K W n (restrictToStableSubmodule E W hW) (v2rep_res_isGLRep E hR W hW hw)
    (W'.comap W.subtype) (fun a b x hx => hW'st a b x hx)
  have hbot : P2 = ⊥ := by
    by_contra hne
    let Z : Submodule K V := P2.map W.subtype
    have hZW : Z ≤ W := by
      rintro _ ⟨y, _, rfl⟩
      exact y.2
    have : FiniteDimensional K Z := Submodule.finiteDimensional_of_le hZW
    have hZst : IsStableUnderOperators E Z := by
      rintro a b _ ⟨y, hy, rfl⟩
      exact ⟨restrictToStableSubmodule E W hW a b y, hP2 a b y hy, rfl⟩
    have hZne : Z ≠ ⊥ := by
      intro h
      obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
      have h5 : (y : V) ∈ Z := ⟨y, hy, rfl⟩
      rw [h] at h5
      exact hy0 (Subtype.ext h5)
    obtain ⟨mu, v, hvZ, hhw⟩ := v2rep_exists_hwv E hR Z hZst (hZW.trans hw) hZne
    obtain ⟨y, hy, rfl⟩ := hvZ
    have h1 : (y : V) ∈ W' :=
      Submodule.mem_iSup_of_mem mu (Submodule.subset_span ⟨1, Submonoid.one_mem _, y, y.2, hhw, rfl⟩)
    have h3 : y ∈ (W'.comap W.subtype) ⊓ P2 := ⟨h1, hy⟩
    rw [hcompl.inf_eq_bot] at h3
    have h4 : y = 0 := h3
    exact hhw.1 (by rw [h4]; rfl)
  have htop : W'.comap W.subtype = ⊤ := by
    have := hcompl.sup_eq_top
    rwa [hbot, sup_bot_eq] at this
  intro x hx
  have : (⟨x, hx⟩ : W) ∈ W'.comap W.subtype := by rw [htop]; exact Submodule.mem_top
  exact this

end Formalism.MainNotions.G.GLWeightTheory
end
end

section

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem exists_equivariant_cyclic_to_hwv (D : Formalism.BasicNotions.D7) (h2 : adm2 D) {n : ℕ} {K V : Type} [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (E : GLOps n K V) (hE : IsGLRep E) (lam : Fin n → ℤ)
    (v0 v : V) (hv0 : IsHWV E lam v0) (hv : IsHWV E lam v) (hL : IsSubrepresentation E (cyclicSubmodule E v0)) :
    ∃ φ : cyclicSubmodule E v0 →ₗ[K] V, IsEquivariantMap (restrictRepresentation E _ hL) E φ ∧ φ ⟨v0, self_mem_cyclicSubmodule E v0⟩ = v := by
  have hP := prodRepresentation_isRep E E hE hE
  have hg : IsHWV (prodRepresentation E E) lam (v0, v) := by
    refine ⟨fun h => hv0.1 (congrArg Prod.fst h), (prod_mem_weightSpace_iff E E lam _).2 ⟨hv0.2.1, hv.2.1⟩, fun a b hab => ?_⟩
    rw [prodRepresentation_apply, hv0.2.2 a b hab, hv.2.2 a b hab]; rfl
  have hΓ := cyclicSubmodule_isSubrepresentation (prodRepresentation E E) (v0, v)
  have hEΓ := restrictRepresentation_isRep (prodRepresentation E E) hP _ hΓ
  have hg' := highest_vector_restrict (prodRepresentation E E) _ hΓ lam (v0, v) (self_mem_cyclicSubmodule _ _) hg
  have hcyc := cyclicSubmodule_restrict_eq_top (prodRepresentation E E) (v0, v) hΓ
  let F : cyclicSubmodule (prodRepresentation E E) (v0, v) →ₗ[K] V := (LinearMap.fst K V V) ∘ₗ (Submodule.subtype _)
  let S2 : cyclicSubmodule (prodRepresentation E E) (v0, v) →ₗ[K] V := (LinearMap.snd K V V) ∘ₗ (Submodule.subtype _)
  have hF : IsEquivariantMap (restrictRepresentation (prodRepresentation E E) _ hΓ) E F := fun a b x => rfl
  have hS : IsEquivariantMap (restrictRepresentation (prodRepresentation E E) _ hΓ) E S2 := fun a b x => rfl
  have hker := equivariant_injective_of_cyclic D h2 _ hEΓ E lam _ hg' hcyc F hF hv0.1
  have hinj : Function.Injective F := LinearMap.ker_eq_bot.1 hker
  have hrange : LinearMap.range F = cyclicSubmodule E v0 := by
    have := equivariant_map_cyclicSubmodule _ E F hF ⟨(v0, v), self_mem_cyclicSubmodule _ _⟩
    rw [hcyc, Submodule.map_top] at this
    exact this
  have hmem : ∀ z, F z ∈ cyclicSubmodule E v0 := fun z => by rw [← hrange]; exact ⟨z, rfl⟩
  let e : cyclicSubmodule (prodRepresentation E E) (v0, v) ≃ₗ[K] cyclicSubmodule E v0 :=
    LinearEquiv.ofBijective (F.codRestrict _ hmem)
      ⟨fun x y hxy => hinj (congrArg Subtype.val hxy), fun y => by
        have hy : (y : V) ∈ LinearMap.range F := by rw [hrange]; exact y.2
        obtain ⟨z, hz⟩ := hy
        exact ⟨z, Subtype.ext hz⟩⟩
  have he : ∀ z, ((e z : cyclicSubmodule E v0) : V) = F z := fun z => rfl
  refine ⟨S2 ∘ₗ e.symm.toLinearMap, fun a b y => ?_, ?_⟩
  · obtain ⟨z, rfl⟩ := e.surjective y
    have h1 : restrictRepresentation E _ hL a b (e z) = e (restrictRepresentation (prodRepresentation E E) _ hΓ a b z) := Subtype.ext rfl
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [h1, e.symm_apply_apply, e.symm_apply_apply]
    exact hS a b z
  · have h1 : (⟨v0, self_mem_cyclicSubmodule E v0⟩ : cyclicSubmodule E v0) = e ⟨(v0, v), self_mem_cyclicSubmodule _ _⟩ := Subtype.ext rfl
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [h1, e.symm_apply_apply]
    rfl

def trivialRepresentation (n : ℕ) (K : Type) [Field K] : GLOps n K K := fun _ _ => 0

theorem trivialRepresentation_isRep (n : ℕ) (K : Type) [Field K] : IsGLRep (trivialRepresentation n K) := by
  refine ⟨?_, fun x => ⟨⊤, inferInstance, trivial, fun _ _ _ _ => trivial⟩, ?_⟩
  · intro a b c d
    simp only [trivialRepresentation]
    split_ifs <;> simp
  · rw [eq_top_iff]
    intro x _
    exact Submodule.mem_iSup_of_mem 0 ((mem_weightSp_iff_diagonal_apply _ _ _).2 fun a => by simp [trivialRepresentation])

theorem trivialRep_invariant_projection (n : ℕ) (K : Type) [Field K] [CharZero K] : IsInvProj (trivialRepresentation n K) 1 := by
  refine ⟨fun x _ => rfl, fun mu hmu x hx => ?_⟩
  have hle : isoSub (trivialRepresentation n K) mu ≤ ⊥ := by
    refine Submodule.span_le.2 ?_
    rintro y ⟨u, _, v, hv, _⟩
    exfalso
    obtain ⟨i, hi⟩ : ∃ i, mu i ≠ 0 := by
      by_contra hcon
      exact hmu (funext fun i => by_contra fun h => hcon ⟨i, h⟩)
    have h1 := (mem_weightSp_iff_diagonal_apply _ mu v).1 hv.2.1 i
    simp only [trivialRepresentation, LinearMap.zero_apply] at h1
    rcases smul_eq_zero.1 h1.symm with h | h
    · exact hi (by exact_mod_cast h)
    · exact hv.1 h
  have := hle hx
  rw [Submodule.mem_bot] at this
  rw [this, map_zero]

theorem invariant_projection_equivariant (D : Formalism.BasicNotions.D7) (h2 : adm2 D) {n : ℕ} {K V V' : Type} [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
    (E : GLOps n K V) (E' : GLOps n K V') (hE : IsGLRep E) (hE' : IsGLRep E')
    (P : Module.End K (V →ₗ[K] V')) (hP : IsInvProj (homRepresentation E E') P) (g : V →ₗ[K] V') : IsEquivariantMap E E' (P g) := by
  intro a b x
  have h := congrArg (fun f : V →ₗ[K] V' => f x)
    (invariant_projection_kills_operators D h2 n K _ (homRepresentation E E') (homRepresentation_isRep E E' hE hE') P hP g a b)
  simp only [homRepresentation_apply, LinearMap.zero_apply] at h
  exact (sub_eq_zero.1 h).symm

theorem schur_invariant_projection_trace (D : Formalism.BasicNotions.D7) (h2 : adm2 D) {n : ℕ} {K L : Type} [Field K] [CharZero K]
    [AddCommGroup L] [Module K L] [FiniteDimensional K L] (EL : GLOps n K L) (hEL : IsGLRep EL) (lam : Fin n → ℤ)
    (v0 : L) (hv0 : IsHWV EL lam v0) (hcyc : cyclicSubmodule EL v0 = ⊤)
    (P0 : Module.End K (L →ₗ[K] L)) (hP0 : IsInvProj (homRepresentation EL EL) P0) (g : L →ₗ[K] L) :
    (Module.finrank K L : K) • P0 g = (LinearMap.trace K L g) • (LinearMap.id : L →ₗ[K] L) := by
  have hψ := invariant_projection_equivariant D h2 EL EL hEL hEL P0 hP0 g
  have hw : P0 g v0 ∈ weightSp EL lam := by
    rw [mem_weightSp_iff_diagonal_apply]
    intro a
    rw [← hψ, (mem_weightSp_iff_diagonal_apply EL lam v0).1 hv0.2.1 a, map_smul]
  obtain ⟨c, hc⟩ := cyclic_highest_weightSpace_line EL hEL lam v0 hv0 (P0 g v0) (by rw [hcyc]; trivial) hw
  have hid : P0 g = c • (LinearMap.id : L →ₗ[K] L) := by
    have hT : IsEquivariantMap EL EL (P0 g - c • (LinearMap.id : L →ₗ[K] L)) := by
      intro a b x
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, map_sub, map_smul]
      rw [hψ]
    have h0 : (P0 g - c • (LinearMap.id : L →ₗ[K] L)) v0 = 0 := by
      simp [hc]
    ext x
    have := equivariant_kills_cyclic_of_zero EL EL _ hT v0 h0 x (by rw [hcyc]; trivial)
    exact sub_eq_zero.1 this
  have htr : IsEquivariantMap (homRepresentation EL EL) (trivialRepresentation n K) (LinearMap.trace K L) := by
    intro a b f
    have : homRepresentation EL EL a b f = EL a b * f - f * EL a b := by
      ext x; simp
    rw [this, map_sub, LinearMap.trace_mul_comm, sub_self]
    rfl
  have h3 := equivariant_commutes_isotypic D h2 n K _ K (homRepresentation EL EL) (trivialRepresentation n K) (homRepresentation_isRep EL EL hEL hEL)
    (trivialRepresentation_isRep n K) (LinearMap.trace K L) htr P0 1 hP0 (trivialRep_invariant_projection n K) g
  rw [Module.End.one_apply, hid, map_smul, LinearMap.trace_id, smul_eq_mul] at h3
  rw [hid, smul_smul, ← h3, mul_comm]

end Formalism.MainNotions.G.GLWeightTheory
end
end
