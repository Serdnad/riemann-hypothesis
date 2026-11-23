module

public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle013
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle017
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Data.Fintype.Pi
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Eigenspace.Basic
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Measure.Haar.Basic

@[expose] public section

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.WordGrowth

variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
  {π : Representation ℂ G V} {J : Subgroup G}

theorem _root_.GlobalTheory.WordGrowth.exists_average
    {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V]
    [Module ℂ V] {π : Representation ℂ G V} {J : Subgroup G}
    (hπ : _root_.GlobalTheory.PRep.IsSmooth π) (hJ : IsCompact (↑J : Set G)) (u : V) :
          ∃ t ∈ _root_.GlobalTheory.PRep.fixed π J,
            ∀ (f : V →ₗ[ℂ] ℂ),
              (∀ j ∈ J, (f : V → ℂ) (((π : G → V →ₗ[ℂ] V) j : V → V) u) = (f : V → ℂ) u) →
                (f : V → ℂ) t = (f : V → ℂ) u := by

  have hK : IsOpen {g : G | π g u = u} := hπ u
  obtain ⟨F, hF⟩ := hJ.elim_finite_subcover
    (fun j : J => (fun g : G => (j : G)⁻¹ * g) ⁻¹' {g : G | π g u = u})
    (fun j => hK.preimage (continuous_const.mul continuous_id))
    (by
      intro g hg
      exact Set.mem_iUnion.2 ⟨⟨g, hg⟩, by simp⟩)
  have hfin : ((fun g : G => π g u) '' (J : Set G)).Finite := by
    apply (F.finite_toSet.image (fun j : J => π (j : G) u)).subset
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨j, hjF, hj⟩ := Set.mem_iUnion₂.1 (hF hg)
    refine ⟨j, hjF, ?_⟩
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hj
    show π j u = π g u
    calc π (j : G) u = π j (π ((j : G)⁻¹ * g) u) := by rw [hj]
      _ = π g u := by rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
  set O := hfin.toFinset with hO
  have hmem : ∀ v, v ∈ O ↔ ∃ g ∈ J, π g u = v := by
    intro v
    simp [O]
  have huO : u ∈ O := (hmem u).2 ⟨1, J.one_mem, by simp⟩
  have hcard : (O.card : ℂ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.2 ⟨u, huO⟩).ne'
  refine ⟨(O.card : ℂ)⁻¹ • ∑ v ∈ O, v, ?_, ?_⟩
  · simp only [_root_.GlobalTheory.PRep.fixed, _root_.GlobalTheory.PRep.eig]
    simp
    intro a ha
    congr 1
    apply Finset.sum_nbij' (fun v => π a v) (fun v => π a⁻¹ v)
    · intro v hv
      obtain ⟨g, hg, rfl⟩ := (hmem v).1 hv
      exact (hmem _).2 ⟨a * g, J.mul_mem ha hg, by rw [map_mul, Module.End.mul_apply]⟩
    · intro v hv
      obtain ⟨g, hg, rfl⟩ := (hmem v).1 hv
      exact (hmem _).2 ⟨a⁻¹ * g, J.mul_mem (J.inv_mem ha) hg, by rw [map_mul, Module.End.mul_apply]⟩
    · intro v _
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    · intro v _
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    · intro v _
      rfl
  · intro f hf

    rw [map_smul, map_sum, smul_eq_mul]
    rw [Finset.sum_congr rfl (g := fun _ => f u) ?_]
    · rw [Finset.sum_const, nsmul_eq_mul]
      field_simp
    · intro v hv
      obtain ⟨g, hg, rfl⟩ := (hmem v).1 hv
      exact hf g hg

end GlobalTheory.WordGrowth
end
end

section

namespace GlobalTheory.SchurAdmissibility

theorem schur_admissible (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K : Subgroup G) (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G))
    (N : Type) [AddCommGroup N] [Module ℂ N] (π : Representation ℂ G N)
    (hirr : Representation.IsIrreducible π) (hadm : GlobalTheory.PRep.IsAdmissible π)
    (φ : N →ₗ[ℂ] N) (hφ : ∀ (g : G) (x : N), φ (π g x) = π g (φ x)) :
    ∃ c : ℂ, φ = c • LinearMap.id := by
  by_cases hN : ∀ v : N, v = 0
  · exact ⟨0, LinearMap.ext fun v => by rw [hN (φ v)]; simp⟩
  push Not at hN
  obtain ⟨v, hv⟩ := hN
  let S : Subgroup G :=
    { carrier := {g : G | π g v = v}
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul, Module.End.mul_apply, hb, ha]
      one_mem' := by simp
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hSo : IsOpen (S : Set G) := hadm.1 v
  have hSc : IsClosed (S : Set G) := S.isClosed_of_isOpen hSo
  have hLo : IsOpen ((K ⊓ S : Subgroup G) : Set G) := by
    rw [Subgroup.coe_inf]; exact hKo.inter hSo
  have hLc : IsCompact ((K ⊓ S : Subgroup G) : Set G) := by
    rw [Subgroup.coe_inf]; exact hKc.inter_right hSc
  haveI hfd := hadm.2 (K ⊓ S) hLo hLc
  have hmem : ∀ w : N, w ∈ GlobalTheory.PRep.fixed π (K ⊓ S) ↔
      ∀ h : (K ⊓ S : Subgroup G), π (h : G) w = w := by
    intro w
    change (∀ h : (K ⊓ S : Subgroup G), π (h : G) w = _) ↔ _
    simp
  have hvm : v ∈ GlobalTheory.PRep.fixed π (K ⊓ S) := (hmem v).2 fun h => h.2.2
  haveI : Nontrivial (GlobalTheory.PRep.fixed π (K ⊓ S)) :=
    ⟨⟨⟨v, hvm⟩, 0, fun h => hv (congrArg Subtype.val h)⟩⟩
  have hres : ∀ w ∈ GlobalTheory.PRep.fixed π (K ⊓ S), φ w ∈ GlobalTheory.PRep.fixed π (K ⊓ S) := by
    intro w hw
    rw [hmem] at hw ⊢
    intro h
    rw [← hφ, hw h]
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (φ.restrict hres)
  obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
  have hw0 : (w : N) ≠ 0 := fun h => hw.2 (Subtype.ext h)
  have hw1 : φ w = c • (w : N) := congrArg Subtype.val hw.apply_eq_smul
  let U : Subrepresentation π :=
    { toSubmodule := Module.End.eigenspace φ c
      apply_mem_toSubmodule := by
        intro g x hx
        rw [Module.End.mem_eigenspace_iff] at hx ⊢
        rw [hφ, hx, map_smul] }
  refine ⟨c, ?_⟩
  rcases hirr.eq_bot_or_eq_top U with h | h
  · exfalso
    have h1 : (w : N) ∈ U.toSubmodule := Module.End.mem_eigenspace_iff.2 hw1
    rw [h] at h1
    exact hw0 h1
  · ext x
    have h1 : x ∈ U.toSubmodule := by
      rw [h]; trivial
    exact Module.End.mem_eigenspace_iff.1 h1

end GlobalTheory.SchurAdmissibility
end

section

open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Topology
open scoped ENNReal

namespace GlobalTheory.SmGL.DualAverage

theorem isLocallyConstant_orbit {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ G W} (hσ : IsSmooth σ) (u : W) :
    IsLocallyConstant fun g : G => σ g u := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun g => ?_
  have ho : IsOpen ((fun x => g⁻¹ * x) ⁻¹' {x : G | σ x u = u}) := (hσ u).preimage (by fun_prop)
  filter_upwards [ho.mem_nhds (by simp)] with x hx
  have hx' : σ (g⁻¹ * x) u = u := hx
  conv_rhs => rw [← hx']
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]

theorem exists_invariant_form (G W : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G W) (hσ : IsSmooth σ)
    (H : Subgroup G) (hH : IsCompact (H : Set G)) (l₀ : Module.Dual ℂ W) :
    ∃ l : Module.Dual ℂ W, (∀ h ∈ H, ∀ w, l (σ h w) = l w) ∧
      ∀ w, (∀ h ∈ H, σ h w = w) → l w = l₀ w := by
  have : CompactSpace H := isCompact_iff_compactSpace.1 hH
  borelize ↥H
  let η : Measure H := Measure.haar
  have hne : ((η.real Set.univ : ℝ) : ℂ) ≠ 0 := by
    have : η.real Set.univ ≠ 0 := by
      rw [Measure.real, ENNReal.toReal_ne_zero]
      exact ⟨(isOpen_univ.measure_pos η Set.univ_nonempty).ne', measure_ne_top _ _⟩
    exact_mod_cast this
  have hint : ∀ w, Integrable (fun h : H => l₀ (σ ((h : G)⁻¹) w)) η := by
    intro w
    have hc : Continuous fun h : H => l₀ (σ ((h : G)⁻¹) w) :=
      (((isLocallyConstant_orbit hσ w).comp_continuous
        (continuous_subtype_val.inv : Continuous fun h : H => (h : G)⁻¹)).comp l₀).continuous
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let a : Module.Dual ℂ W :=
    { toFun := fun w => ∫ h : H, l₀ (σ ((h : G)⁻¹) w) ∂η
      map_add' := fun v w => by
        simp only [map_add (f := _)]
        exact integral_add (hint v) (hint w)
      map_smul' := fun c w => by
        simp only [map_smul, RingHom.id_apply]
        exact integral_smul c _ }
  have ha : ∀ w, a w = ∫ h : H, l₀ (σ ((h : G)⁻¹) w) ∂η := fun _ => rfl
  refine ⟨((η.real Set.univ : ℝ) : ℂ)⁻¹ • a, fun h₀ hh₀ w => ?_, fun w hw => ?_⟩
  · rw [LinearMap.smul_apply, LinearMap.smul_apply, ha, ha,
      ← integral_mul_left_eq_self (μ := η) (fun h : H => l₀ (σ ((h : G)⁻¹) (σ h₀ w))) ⟨h₀, hh₀⟩]
    congr 2
    funext h
    rw [← Module.End.mul_apply, ← map_mul]
    simp
  · rw [LinearMap.smul_apply, ha]
    have : (fun h : H => l₀ (σ ((h : G)⁻¹) w)) = fun _ => l₀ w :=
      funext fun h => by rw [hw _ (inv_mem h.2)]
    rw [this, integral_const, Complex.real_smul, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

end GlobalTheory.SmGL.DualAverage
end

section

open scoped TensorProduct

namespace GlobalTheory.TensHead

open scoped TensorProduct in
private lemma piOp_tprod {ι : Type} [DecidableEq ι] {M : ι → Type}
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)] (i : ι) (g : Module.End ℂ (M i))
    (y : ∀ j, M j) :
    _root_.GlobalTheory.TensHead.piOp i g (PiTensorProduct.tprod ℂ y) =
      PiTensorProduct.tprod ℂ (Function.update y i (g (y i))) := by
  unfold _root_.GlobalTheory.TensHead.piOp
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext j
  by_cases h : j = i
  · subst h
    simp
  · simp [h]

open scoped TensorProduct in
lemma _root_.GlobalTheory.TensHead.piOp_tprod_update {ι : Type} [DecidableEq ι] {M : ι → Type}
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)] (i : ι) (g : Module.End ℂ (M i))
    (y : ∀ j, M j) (x : M i) :
    _root_.GlobalTheory.TensHead.piOp i g (PiTensorProduct.tprod ℂ (Function.update y i x)) =
      PiTensorProduct.tprod ℂ (Function.update y i (g x)) := by
  rw [piOp_tprod]
  simp

open scoped TensorProduct in
private lemma apply_tmul_mem_of_stab_left {ι : Type} [DecidableEq ι] {M₀ : Type} [AddCommGroup M₀]
    [Module ℂ M₀] {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    {Op₀ : Set (Module.End ℂ M₀)} {Op : ∀ i, Set (Module.End ℂ (M i))}
    {N : Submodule ℂ (M₀ ⊗[ℂ] (⨂[ℂ] i, M i))}
    (hN : _root_.GlobalTheory.TensHead.Stab
      (_root_.GlobalTheory.TensHead.tensOps Op₀ (_root_.GlobalTheory.TensHead.piOps Op)) N)
    {g : Module.End ℂ M₀} (hg : g ∈ Op₀) {a : M₀} {t : ⨂[ℂ] i, M i} (h : a ⊗ₜ[ℂ] t ∈ N) :
    g a ⊗ₜ[ℂ] t ∈ N := by
  have hmem : TensorProduct.map g LinearMap.id ∈
      _root_.GlobalTheory.TensHead.tensOps Op₀ (_root_.GlobalTheory.TensHead.piOps Op) := by
    unfold _root_.GlobalTheory.TensHead.tensOps
    exact Or.inl ⟨g, hg, rfl⟩
  unfold _root_.GlobalTheory.TensHead.Stab at hN
  simpa using hN _ hmem _ h

open scoped TensorProduct in
private lemma tmul_tprod_update_apply_mem_of_stab {ι : Type} [DecidableEq ι] {M₀ : Type} [AddCommGroup M₀]
    [Module ℂ M₀] {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    {Op₀ : Set (Module.End ℂ M₀)} {Op : ∀ i, Set (Module.End ℂ (M i))}
    {N : Submodule ℂ (M₀ ⊗[ℂ] (⨂[ℂ] i, M i))}
    (hN : _root_.GlobalTheory.TensHead.Stab
      (_root_.GlobalTheory.TensHead.tensOps Op₀ (_root_.GlobalTheory.TensHead.piOps Op)) N)
    (i : ι) {g : Module.End ℂ (M i)} (hg : g ∈ Op i) {a : M₀} {y : ∀ j, M j} {x : M i}
    (h : a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update y i x) ∈ N) :
    a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update y i (g x)) ∈ N := by
  have hmem : TensorProduct.map LinearMap.id (_root_.GlobalTheory.TensHead.piOp i g) ∈
      _root_.GlobalTheory.TensHead.tensOps Op₀ (_root_.GlobalTheory.TensHead.piOps Op) := by
    unfold _root_.GlobalTheory.TensHead.tensOps _root_.GlobalTheory.TensHead.piOps
    exact Or.inr ⟨_, ⟨i, g, hg, rfl⟩, rfl⟩
  unfold _root_.GlobalTheory.TensHead.Stab at hN
  have := hN _ hmem _ h
  rwa [TensorProduct.map_tmul, LinearMap.id_apply, _root_.GlobalTheory.TensHead.piOp_tprod_update] at this


open scoped TensorProduct in
theorem _root_.GlobalTheory.TensHead.eq_top_of_pure_generators :
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {M₀ : Type} [AddCommGroup M₀] [Module ℂ M₀]
    {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    (Op₀ : Set (Module.End ℂ M₀)) (Op : ∀ i, Set (Module.End ℂ (M i)))
    (Rel₀ : Submodule ℂ M₀) (Rel : ∀ i, Submodule ℂ (M i)) (F₀ : Finset M₀) (F : ∀ i, Finset (M i)),
    (∀ N : Submodule ℂ M₀, Rel₀ ≤ N → _root_.GlobalTheory.TensHead.Stab Op₀ N → (↑F₀ : Set M₀) ⊆ ↑N → N = ⊤) →
    (∀ i, ∀ N : Submodule ℂ (M i), Rel i ≤ N → _root_.GlobalTheory.TensHead.Stab (Op i) N →
      (↑(F i) : Set (M i)) ⊆ ↑N → N = ⊤) →
    ∀ N : Submodule ℂ (M₀ ⊗[ℂ] (⨂[ℂ] i, M i)),
      (∀ x ∈ Rel₀, ∀ y, x ⊗ₜ[ℂ] y ∈ N) →
      (∀ i, ∀ x ∈ Rel i, ∀ (x₀ : M₀) (y : ∀ j, M j),
        x₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update y i x) ∈ N) →
      _root_.GlobalTheory.TensHead.Stab (_root_.GlobalTheory.TensHead.tensOps Op₀ (_root_.GlobalTheory.TensHead.piOps Op)) N →
      (∀ x₀ ∈ F₀, ∀ y : ∀ i, M i, (∀ i, y i ∈ F i) → x₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ y ∈ N) →
      N = ⊤ := by
  intro ι _ _ M₀ _ _ M _ _ Op₀ Op Rel₀ Rel F₀ F h₀ hF N hRel₀ hRel hN hgen
  have key : ∀ s : Finset ι, ∀ y : ∀ j, M j, (∀ j, j ∉ s → y j ∈ F j) →
      ∀ a : M₀, a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ y ∈ N := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro y hy a
      have hT := h₀ (N.comap ((TensorProduct.mk ℂ M₀ (⨂[ℂ] i, M i)).flip
        (PiTensorProduct.tprod ℂ y))) ?_ ?_ ?_
      · have ha : a ∈ (⊤ : Submodule ℂ M₀) := trivial
        rw [← hT] at ha
        simpa using ha
      · intro x hx
        simpa using hRel₀ x hx _
      · unfold _root_.GlobalTheory.TensHead.Stab
        intro g hg x hx
        simp only [Submodule.mem_comap, LinearMap.flip_apply, TensorProduct.mk_apply] at hx ⊢
        exact apply_tmul_mem_of_stab_left hN hg hx
      · intro x hx
        simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.flip_apply,
          TensorProduct.mk_apply]
        exact hgen x hx y (fun j => hy j (by simp))
    | insert i s hi ih =>
      intro y hy a
      let S : Submodule ℂ (M i) := ⨅ (b : M₀)
        (z : {z : ∀ j, M j // ∀ j, j ∉ s → j ≠ i → z j ∈ F j}),
        N.comap ((TensorProduct.mk ℂ M₀ (⨂[ℂ] j, M j) b) ∘ₗ
          (PiTensorProduct.tprod ℂ).toLinearMap z.1 i)
      have hS : ∀ x, x ∈ S ↔ ∀ (b : M₀) (z : ∀ j, M j), (∀ j, j ∉ s → j ≠ i → z j ∈ F j) →
          b ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update z i x) ∈ N := by
        intro x
        simp only [S, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.comp_apply,
          MultilinearMap.toLinearMap_apply, TensorProduct.mk_apply, Subtype.forall]
      have hT := hF i S ?_ ?_ ?_
      · have hx : y i ∈ S := by
          rw [hT]
          trivial
        have := (hS _).1 hx a y (fun j hj hji => hy j (by simp [hji, hj]))
        simpa using this
      · intro x hx
        rw [hS]
        intro b z _
        exact hRel i x hx b z
      · unfold _root_.GlobalTheory.TensHead.Stab
        intro g hg x hx
        rw [hS] at hx ⊢
        intro b z hz
        exact tmul_tprod_update_apply_mem_of_stab hN i hg (hx b z hz)
      · intro x hx
        rw [SetLike.mem_coe, hS]
        intro b z hz
        apply ih
        intro j hj
        by_cases hji : j = i
        · subst hji
          simpa using hx
        · rw [Function.update_of_ne hji]
          exact hz j hj hji
  have hall : ∀ v, v ∈ N := by
    intro v
    induction v using TensorProduct.induction_on with
    | zero => exact N.zero_mem
    | tmul a t =>
      induction t using PiTensorProduct.induction_on with
      | smul_tprod r y =>
        rw [TensorProduct.tmul_smul]
        exact N.smul_mem r (key Finset.univ y (fun j hj => absurd (Finset.mem_univ j) hj) a)
      | add p q hp hq =>
        rw [TensorProduct.tmul_add]
        exact N.add_mem hp hq
    | add p q hp hq => exact N.add_mem hp hq
  exact eq_top_iff.2 fun v _ => hall v

end GlobalTheory.TensHead
end

section

open MeasureTheory Function
open scoped Pointwise

namespace GlobalTheory.UnfoldNormal

theorem ae_exists_pairGroup_smul_mem_shear : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H], ∀ (ν : Measure H) [ν.IsHaarMeasure] (Γ N : Subgroup H), Countable Γ → IsClosed (N : Set H) → ∀ (hN : ∀ γ ∈ Γ, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) (κ : Measure N) (𝓝 : Set N), κ.IsHaarMeasure → IsFundamentalDomain (Γ.subgroupOf N) 𝓝 κ → (∀ (γ : H) (hγ : γ ∈ Γ), κ.map (fun n : N => (⟨γ * n * γ⁻¹, hN γ hγ n n.2⟩ : N)) = κ) → ∀ 𝓕 : Set H, IsFundamentalDomain Γ 𝓕 ν → ∀ᵐ p ∂((κ.prod ν).map (GlobalTheory.UnfoldNormal.shear N)), ∃ g : GlobalTheory.UnfoldNormal.pairGroup Γ N hN, g • p ∈ GlobalTheory.UnfoldNormal.shear N '' (𝓝 ×ˢ 𝓕) := by
  intro H _ _ _ _ _ _ _ _ ν _ Γ N hΓ hNc hN κ 𝓝 hκ h𝓝 hconj 𝓕 h𝓕
  haveI : LocallyCompactSpace N := hNc.locallyCompactSpace
  haveI : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology (N : Set H)
  haveI : SigmaFinite κ := inferInstance
  have hgoodn : ∀ᵐ n : N ∂κ, ∀ v : Γ, ∃ δ : Γ.subgroupOf N,
      δ • (⟨(v : H) * n * (v : H)⁻¹, hN v v.2 n n.2⟩ : N) ∈ 𝓝 := by
    rw [ae_all_iff]
    intro v
    have hc : Continuous (fun n : N => (⟨(v : H) * n * (v : H)⁻¹, hN v v.2 n n.2⟩ : N)) :=
      Continuous.subtype_mk (by fun_prop) _
    have hmp : MeasurePreserving (fun n : N => (⟨(v : H) * n * (v : H)⁻¹, hN v v.2 n n.2⟩ : N)) κ κ :=
      ⟨hc.measurable, hconj v v.2⟩
    exact hmp.quasiMeasurePreserving.ae h𝓝.ae_covers
  have hboth : ∀ᵐ p ∂(κ.prod ν), (∀ v : Γ, ∃ δ : Γ.subgroupOf N,
      δ • (⟨(v : H) * p.1 * (v : H)⁻¹, hN v v.2 p.1 p.1.2⟩ : N) ∈ 𝓝) ∧
      ∃ v : Γ, v • p.2 ∈ 𝓕 :=
    (Measure.quasiMeasurePreserving_fst.ae hgoodn).and
      (Measure.quasiMeasurePreserving_snd.ae h𝓕.ae_covers)
  rw [(measurableEmbedding_shear hNc).ae_map_iff]
  filter_upwards [hboth] with p hp
  obtain ⟨n, h⟩ := p
  obtain ⟨hn, v, hv⟩ := hp
  obtain ⟨δ, hδ⟩ := hn v
  have hδN : ((δ : N) : H) ∈ N := (δ : N).2
  have hδΓ : ((δ : N) : H) ∈ Γ := δ.2
  refine ⟨⟨(((δ : N) : H) * v, (v : H)), Γ.mul_mem hδΓ v.2, v.2, ?_⟩, ?_⟩
  · simpa using hδN
  · refine ⟨(_, v • h), ⟨hδ, hv⟩, ?_⟩
    ext
    · simp [shear, Subgroup.smul_def, Submonoid.smul_def, mul_assoc]
    · simp [shear, Subgroup.smul_def, Submonoid.smul_def]

end GlobalTheory.UnfoldNormal
end

section


theorem _root_.GlobalTheory.T.sum_prod_update_regroup_of_update_eq : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type} {W : ι → Type}
    [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    {m : ι → ℕ} (k : ∀ i, Fin (m i) → X i) (ℓ : ∀ i, Fin (m i) → W i →ₗ[ℂ] ℂ) (i₀ : ι)
    (F F' : (∀ i, X i) → ℂ) (w w' : W i₀)
    (hone : ∀ J : (∀ i, Fin (m i)), ∑ j, ℓ i₀ j w' * F (Function.update (fun i => k i (J i)) i₀ (k i₀ j)) =
      ∑ j, ℓ i₀ j w * F' (Function.update (fun i => k i (J i)) i₀ (k i₀ j)))
    (v : ∀ i, W i), ∑ J : (∀ i, Fin (m i)), (∏ i, ℓ i (J i) (Function.update v i₀ w' i)) * F (fun i => k i (J i)) =
    ∑ J : (∀ i, Fin (m i)), (∏ i, ℓ i (J i) (Function.update v i₀ w i)) * F' (fun i => k i (J i)) := by
  first | exact @GlobalTheory.sum_prod_update_regroup | exact GlobalTheory.sum_prod_update_regroup | (intros; apply GlobalTheory.sum_prod_update_regroup <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_finset_eq_sum_smul_of_mem_submodule : ∀ {X : Type} (V : Submodule ℂ (X → ℂ)) (F : Finset (X → ℂ)), (∀ u ∈ F, u ∈ V) →
    ∃ (s : Finset X) (E : X → X → ℂ), (∀ x, E x ∈ V) ∧ ∀ u ∈ F, u = ∑ x ∈ s, u x • E x := by
  first | exact @GlobalTheory.finset_functions_recovered_from_values | exact GlobalTheory.finset_functions_recovered_from_values | (intros; apply GlobalTheory.finset_functions_recovered_from_values <;> assumption)
end
