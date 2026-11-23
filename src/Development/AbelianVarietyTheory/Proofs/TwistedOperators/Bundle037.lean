module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle027
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.LocallyConstant.Basic
import Aesop.Main
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Irreducible
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle017
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle028
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Topology.Instances.Matrix
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Tactic.TypeStar
public import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Extend
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Algebra.Order.Chebyshev
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower

@[expose] public section

section

open scoped InnerProductSpace
-- `MultilinearMap` now takes the scalar ring hom explicitly.  Preserve the
-- older `MultilinearMap R M N` spelling used by the statement in this file.
local notation "MultilinearMap " "ℂ " M:max N:max =>
  _root_.MultilinearMap (RingHom.id ℂ) M N

namespace GlobalTheory.DensityMultiPlace

private theorem multilinear_translates_zero_local : ∀ (ι : Type) [Fintype ι]
    (H : ι → Type) [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
    [∀ i, CompleteSpace (H i)] (G : ι → Type) [∀ i, Group (G i)]
    (π : ∀ i, G i →* (H i →L[ℂ] H i)) (hu : ∀ i g x, ‖π i g x‖ = ‖x‖)
    (hs : ∀ i, ∀ B : H i →L[ℂ] H i,
      (∀ g, B.comp (π i g) = (π i g).comp B) →
        ∃ c : ℂ, B = c • ContinuousLinearMap.id ℂ (H i))
    (Sm : ∀ i, Submodule ℂ (H i)) (hd : ∀ i, Dense (Sm i : Set (H i)))
    (hinv : ∀ i g, ∀ x ∈ Sm i, π i g x ∈ Sm i)
    (L : MultilinearMap ℂ (fun i => Sm i) ℂ) (C : ℝ)
    (hL : ∀ v, ‖L v‖ ≤ C * ∏ i, ‖(v i : H i)‖)
    (n : ℕ) (c : Fin n → ℂ) (v : Fin n → ∀ i, Sm i)
    (hv : ∀ g : ∀ i, G i,
      ∑ j, c j * L (fun i => ⟨π i (g i) (v j i), hinv i (g i) _ (v j i).2⟩) = 0)
    (φ : ∀ i, H i) (u : ∀ i, Sm i),
    (∑ j, c j * ∏ i, ⟪φ i, (v j i : H i)⟫_ℂ) * L u = 0 := by
  intro ι _ H _ _ _ G _ π hu hs Sm hd hinv L C hL n c v hv φ u
  classical
  let w : Fin n → (∀ i, G i) → ∀ i, Sm i :=
    fun j g i => ⟨π i (g i) (v j i), hinv i (g i) _ (v j i).2⟩
  have key : ∀ s : Finset ι, ∀ (g : ∀ i, G i) (u : ∀ i, Sm i),
      ∑ j, c j * (∏ i ∈ s, ⟪φ i, (v j i : H i)⟫_ℂ) * L (s.piecewise u (w j g)) = 0 := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro g u
      simpa [w] using hv g
    · intro a s ha ih g u
      have hnorm : ∀ (m : ∀ i, Sm i) (x : Sm a),
          ∏ i, ‖((Function.update m a x) i : H i)‖
            = (∏ i ∈ Finset.univ.erase a, ‖(m i : H i)‖) * ‖x‖ := by
        intro m x
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a), Function.update_self,
          mul_comm]
        congr 1
        · refine Finset.prod_congr rfl fun i hi => ?_
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
      have hbd : ∀ j (x : Sm a), ‖L.toLinearMap (s.piecewise u (w j g)) a x‖
          ≤ (C * ∏ i ∈ Finset.univ.erase a,
            ‖((s.piecewise u (w j g)) i : H i)‖) * ‖x‖ := by
        intro j x
        rw [MultilinearMap.toLinearMap_apply, mul_assoc, ← hnorm]
        exact hL _
      have hden : DenseRange (Sm a).subtypeL := (hd a).denseRange_val
      have hui : IsUniformInducing (Sm a).subtypeL :=
        isUniformEmbedding_subtype_val.isUniformInducing
      let Λ : Fin n → (H a →L[ℂ] ℂ) := fun j =>
        (c j * ∏ i ∈ s, ⟪φ i, (v j i : H i)⟫_ℂ) •
          ((L.toLinearMap (s.piecewise u (w j g)) a).mkContinuous _ (hbd j)).extend
            (Sm a).subtypeL
      have hΛ : ∀ j (x : Sm a), Λ j (x : H a) =
          (c j * ∏ i ∈ s, ⟪φ i, (v j i : H i)⟫_ℂ) *
            L (Function.update (s.piecewise u (w j g)) a x) := by
        intro j x
        have this := ContinuousLinearMap.extend_eq
          ((L.toLinearMap (s.piecewise u (w j g)) a).mkContinuous _ (hbd j)) hden hui x
        simp only [Λ, ContinuousLinearMap.smul_apply, smul_eq_mul]
        erw [this]
        rw [LinearMap.mkContinuous_apply, MultilinearMap.toLinearMap_apply]
      have hupd : ∀ j (k : G a), s.piecewise u (w j (Function.update g a k)) =
          Function.update (s.piecewise u (w j g)) a
            ⟨π a k (v j a), hinv a k _ (v j a).2⟩ := by
        intro j k
        funext i
        by_cases hia : i = a
        · subst hia
          simp [Finset.piecewise_eq_of_notMem _ _ _ ha, w]
        · rw [Function.update_of_ne hia]
          by_cases his : i ∈ s
          · simp [Finset.piecewise_eq_of_mem _ _ _ his]
          · simp [Finset.piecewise_eq_of_notMem _ _ _ his, w, Function.update_of_ne hia]
      have hG : ∀ k : G a, ∑ j, Λ j (π a k (v j a)) = 0 := by
        intro k
        have h1 := ih (Function.update g a k) u
        rw [← h1]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [show (π a k (v j a) : H a) =
          ((⟨π a k (v j a), hinv a k _ (v j a).2⟩ : Sm a) : H a) from rfl,
          hΛ, hupd, mul_assoc]
      have h2 := GlobalTheory.T.irreducibleUnitary_vector_density
        (H a) (G a) (π a) (hu a) (hs a) n (fun j => (v j a : H a)) Λ hG (φ a) (u a)
      rw [← h2]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hΛ, Finset.prod_insert ha, Finset.piecewise_insert]
      ring
  have h := key Finset.univ (fun _ => 1) u
  simp only [Finset.piecewise_univ] at h
  rw [Finset.sum_mul]
  rw [← h]

end GlobalTheory.DensityMultiPlace


theorem _root_.GlobalTheory.T.multilinear_zero_of_kills_translates_tensor : ∀ (ι : Type) [Fintype ι] (H : ι → Type) [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)] [∀ i, CompleteSpace (H i)] (G : ι → Type) [∀ i, Group (G i)] (π : ∀ i, G i →* (H i →L[ℂ] H i)), (∀ i g x, ‖π i g x‖ = ‖x‖) → (∀ i, ∀ B : H i →L[ℂ] H i, (∀ g, B.comp (π i g) = (π i g).comp B) → ∃ c : ℂ, B = c • ContinuousLinearMap.id ℂ (H i)) → ∀ (Sm : ∀ i, Submodule ℂ (H i)), (∀ i, Dense (Sm i : Set (H i))) → ∀ (hinv : ∀ i g, ∀ x ∈ Sm i, π i g x ∈ Sm i) (L : MultilinearMap ℂ (fun i => Sm i) ℂ) (C : ℝ), (∀ v, ‖L v‖ ≤ C * ∏ i, ‖(v i : H i)‖) → ∀ (n : ℕ) (c : Fin n → ℂ) (v : Fin n → ∀ i, Sm i), (∀ g : ∀ i, G i, ∑ j, c j * L (fun i => ⟨π i (g i) (v j i), hinv i (g i) _ (v j i).2⟩) = 0) → ∀ (φ : ∀ i, H i) (u : ∀ i, Sm i), (∑ j, c j * ∏ i, ⟪φ i, (v j i : H i)⟫_ℂ) * L u = 0 := by
  exact @GlobalTheory.DensityMultiPlace.multilinear_translates_zero_local
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

namespace GlobalTheory


open MeasureTheory ValuativeRel Matrix in
theorem _root_.GlobalTheory.exists_weakIntegral_of_isLocallyConstant_of_isCompact :
    ∀ (U : Type) [TopologicalSpace U] [T2Space U] [MeasurableSpace U] [OpensMeasurableSpace U] (m : Measure U) [IsFiniteMeasureOnCompacts m] (V : Type) [AddCommGroup V] [Module ℂ V] (T : U → V) (_ : IsLocallyConstant T) (K : Set U) (_ : IsCompact K) (_ : ∀ u, u ∉ K → T u = 0), ∃ w : V, ∀ l : V →ₗ[ℂ] ℂ, l w = ∫ u, l (T u) ∂m := by
  intro U _ _ _ _ m _ V _ _ T hT K hK hzero
  classical
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun v : V => T ⁻¹' {v})
    (fun v => hT.isOpen_fiber v) (fun u _ => Set.mem_iUnion.2 ⟨T u, rfl⟩)
  have hS : ∀ u, T u ∈ insert 0 t := by
    intro u
    by_cases hu : u ∈ K
    · have h := ht hu
      simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff] at h
      obtain ⟨v, hv, huv⟩ := h
      rw [huv]
      exact Finset.mem_insert_of_mem hv
    · rw [hzero u hu]
      exact Finset.mem_insert_self 0 t
  have hmeas : ∀ v, MeasurableSet (T ⁻¹' {v}) := fun v => (hT.isOpen_fiber v).measurableSet
  refine ⟨∑ v ∈ insert 0 t, ((m.real (T ⁻¹' {v}) : ℂ)) • v, fun l => ?_⟩
  have hpt : ∀ u, l (T u) = ∑ v ∈ insert 0 t, (T ⁻¹' {v}).indicator (fun _ => l v) u := by
    intro u
    rw [Finset.sum_eq_single_of_mem (T u) (hS u)]
    · simp
    · intro v _ hv
      exact Set.indicator_of_notMem
        (show u ∉ T ⁻¹' {v} from fun h => hv (Set.mem_singleton_iff.1 h).symm) (fun _ => l v)
  have hint : ∀ v ∈ insert 0 t, Integrable ((T ⁻¹' {v}).indicator fun _ => l v) m := by
    intro v _
    by_cases hv : v = 0
    · subst hv
      simp
    · have hsub : T ⁻¹' {v} ⊆ K := by
        intro u hu
        by_contra hK'
        exact hv (by rw [← Set.mem_singleton_iff.1 hu, hzero u hK'])
      have hfin : m (T ⁻¹' {v}) ≠ ⊤ := ((measure_mono hsub).trans_lt hK.measure_lt_top).ne
      exact (integrable_indicator_iff (hmeas v)).2 (integrableOn_const (C := l v) hfin)

  rw [integral_congr_ae (ae_of_all _ hpt), MeasureTheory.integral_finsetSum _ hint, map_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [integral_indicator_const _ (hmeas v), map_smul, smul_eq_mul, Complex.real_smul]

end GlobalTheory
end

section

open scoped TensorProduct

namespace GlobalTheory.OuterTensor

theorem nontrivial_of_isIrreducible {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (h : ρ.IsIrreducible) : Nontrivial V := by
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  have hne : (⊥ : Subrepresentation ρ) ≠ ⊤ := bot_ne_top
  exact hne (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))

theorem isIrreducible_outer_tprod :
    ∀ (G H V W : Type) [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ H W), ρ.IsIrreducible → σ.IsIrreducible → (Representation.tprod (ρ.comp (MonoidHom.fst G H)) (σ.comp (MonoidHom.snd G H)) : Representation ℂ (G × H) (V ⊗[ℂ] W)).IsIrreducible := by
  intro G H V W _ _ _ _ _ _ _ _ ρ σ hρ hσ
  have hV := nontrivial_of_isIrreducible ρ hρ
  have hW := nontrivial_of_isIrreducible σ hσ
  have sρ := GlobalTheory.ClassFin.span_range_eq_top_of_isIrreducible G V ρ hρ
  have sσ := GlobalTheory.ClassFin.span_range_eq_top_of_isIrreducible H W σ hσ
  have hVW : Nontrivial (V ⊗[ℂ] W) := by
    apply Module.nontrivial_of_finrank_pos (R := ℂ)
    rw [Module.finrank_tensorProduct]
    exact Nat.mul_pos Module.finrank_pos Module.finrank_pos
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun S => ?_ }
  · exact bot_ne_top (congrArg Subrepresentation.toSubmodule h : (⊥ : Submodule ℂ (V ⊗[ℂ] W)) = ⊤)
  have h1 : ∀ (g : G) (B : W →ₗ[ℂ] W), ∀ x ∈ S.toSubmodule,
      TensorProduct.map (ρ g) B x ∈ S.toSubmodule := by
    intro g B
    have hB : B ∈ Submodule.span ℂ (Set.range σ) := sσ ▸ Submodule.mem_top
    induction hB using Submodule.span_induction with
    | mem B hB =>
      obtain ⟨h, rfl⟩ := hB
      intro x hx
      exact S.apply_mem_toSubmodule (g, h) hx
    | zero => intro x _; simp
    | add B C _ _ hB hC =>
      intro x hx
      rw [TensorProduct.map_add_right, LinearMap.add_apply]
      exact add_mem (hB x hx) (hC x hx)
    | smul c B _ hB =>
      intro x hx
      rw [TensorProduct.map_smul_right, LinearMap.smul_apply]
      exact Submodule.smul_mem _ _ (hB x hx)
  have h2 : ∀ (A : V →ₗ[ℂ] V) (B : W →ₗ[ℂ] W), ∀ x ∈ S.toSubmodule,
      TensorProduct.map A B x ∈ S.toSubmodule := by
    intro A B
    have hA : A ∈ Submodule.span ℂ (Set.range ρ) := sρ ▸ Submodule.mem_top
    induction hA using Submodule.span_induction with
    | mem A hA =>
      obtain ⟨g, rfl⟩ := hA
      exact h1 g B
    | zero => intro x _; simp
    | add A C _ _ hA hC =>
      intro x hx
      rw [TensorProduct.map_add_left, LinearMap.add_apply]
      exact add_mem (hA x hx) (hC x hx)
    | smul c A _ hA =>
      intro x hx
      rw [TensorProduct.map_smul_left, LinearMap.smul_apply]
      exact Submodule.smul_mem _ _ (hA x hx)
  have h3 : ∀ (F : V ⊗[ℂ] W →ₗ[ℂ] V ⊗[ℂ] W), ∀ x ∈ S.toSubmodule, F x ∈ S.toSubmodule := by
    intro F
    obtain ⟨t, rfl⟩ := (homTensorHomEquiv ℂ V W V W).surjective F
    induction t using TensorProduct.induction_on with
    | zero => intro x _; simp
    | tmul A B =>
      intro x hx
      rw [homTensorHomEquiv_apply, TensorProduct.homTensorHomMap_apply]
      exact h2 A B x hx
    | add s t hs ht =>
      intro x hx
      rw [map_add (f := _), LinearMap.add_apply]
      exact add_mem (hs x hx) (ht x hx)
  by_cases hS : S.toSubmodule = ⊥
  · exact Or.inl (Subrepresentation.toSubmodule_injective hS)
  · right
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS
    apply Subrepresentation.toSubmodule_injective
    change S.toSubmodule = ⊤
    refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℂ hx0
    have := h3 (f.smulRight y) x hx
    simpa [hf] using this

end GlobalTheory.OuterTensor
end

section

open MeasureTheory

namespace GlobalTheory.PeriodicMean

theorem mean_factor_le : ∀ (g : ℕ) (Λ Λ' : AddSubgroup (Fin g → ℂ)) (Fd Fd' : Set (Fin g → ℂ)) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (u u' : (Fin g → ℂ) → ℝ) (p n : ℕ) (v : Fin n → (Fin g → ℂ)) (T : ℝ), Countable Λ → Countable Λ' → MeasureTheory.IsAddFundamentalDomain Λ Fd MeasureTheory.volume → MeasureTheory.IsAddFundamentalDomain Λ' Fd' MeasureTheory.volume → 0 < p → (∀ a ∈ Λ, h a ∈ Λ') → (∀ z, 0 ≤ u z) → (∀ z, 0 ≤ u' z) → (∀ a ∈ Λ, ∀ z, u (z + a) = u z) → (∀ a ∈ Λ', ∀ z, u' (z + a) = u' z) → (∫ z in Fd, u z ^ 2) / (MeasureTheory.volume Fd).toReal = 1 → (∫ z in Fd', u' z ^ 2) / (MeasureTheory.volume Fd').toReal = 1 → (∀ z, T * u' (h z) ≤ ∑ m, u ((p : ℂ) • z + v m)) → T ≤ n := by
  intro g Λ Λ' Fd Fd' h u u' p n v T hΛc hΛ'c hF hF' hp hh hu hu' hpu hpu' hm hm' hT

  have hV : 0 < (volume Fd).toReal := by
    rcases (ENNReal.toReal_nonneg (a := volume Fd)).lt_or_eq with h0 | h0
    · exact h0
    · rw [← h0, div_zero] at hm; exact absurd hm zero_ne_one
  have hVt : volume Fd ≠ ⊤ := fun h0 => by simp [h0] at hV

  have hA1 : IntegrableOn (fun z => u' (h z) ^ 2) Fd volume ∧
      (∫ z in Fd, u' (h z) ^ 2) / (volume Fd).toReal = 1 := by
    let Λ₁ : AddSubgroup (Fin g → ℂ) := Λ'.comap (h.toLinearMap.toAddMonoidHom)
    have hc : Countable Λ₁ := by
      have : Function.Injective (fun x : Λ₁ => (⟨h x, x.2⟩ : Λ')) := fun x y hxy =>
        Subtype.ext (h.injective (congrArg Subtype.val hxy))
      exact this.countable
    obtain ⟨hD, hmD⟩ := GlobalTheory.T.affine_change_fundamentalDomain_mean_periodic g Λ' Λ₁ Fd' h 0 (fun z => u' z ^ 2) hΛ'c (fun z => Iff.rfl) hF'
      (fun a ha z => by simp only [hpu' a ha z]) hm'
    exact GlobalTheory.T.mean_fundamentalDomain_eq_one_of_le g Λ Λ₁ Fd _ (fun z => u' (h z) ^ 2) hc (fun a ha => hh a ha) hF hD hVt
      (fun a ha z => by
        have : h (z + a) = h z + h a := map_add h z a
        rw [this, hpu' (h a) ha]) (by simpa using hmD)

  have hA2 : ∀ m, IntegrableOn (fun z => u ((p : ℂ) • z + v m) ^ 2) Fd volume ∧
      (∫ z in Fd, u ((p : ℂ) • z + v m) ^ 2) / (volume Fd).toReal = 1 := by
    intro m
    have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
    let L : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) := LinearEquiv.smulOfNeZero ℂ (Fin g → ℂ) (p : ℂ) hp0
    let Λ₁ : AddSubgroup (Fin g → ℂ) := Λ.comap (L.toLinearMap.toAddMonoidHom)
    have hc : Countable Λ₁ := by
      have : Function.Injective (fun x : Λ₁ => (⟨L x, x.2⟩ : Λ)) := fun x y hxy =>
        Subtype.ext (L.injective (congrArg Subtype.val hxy))
      exact this.countable
    obtain ⟨hD, hmD⟩ := GlobalTheory.T.affine_change_fundamentalDomain_mean_periodic g Λ Λ₁ Fd L (v m) (fun z => u z ^ 2) hΛc (fun z => Iff.rfl) hF
      (fun a ha z => by simp only [hpu a ha z]) hm
    refine GlobalTheory.T.mean_fundamentalDomain_eq_one_of_le g Λ Λ₁ Fd _ (fun z => u ((p : ℂ) • z + v m) ^ 2) hc ?_ hF hD hVt ?_ hmD
    · intro a ha
      change (p : ℂ) • a ∈ Λ
      have : (p : ℂ) • a = p • a := by rw [Nat.cast_smul_eq_nsmul]
      rw [this]; exact Λ.nsmul_mem ha p
    · intro a ha z
      have ha' : (p : ℂ) • a ∈ Λ := ha
      have : (p : ℂ) • (z + a) + v m = ((p : ℂ) • z + v m) + (p : ℂ) • a := by rw [smul_add]; abel
      simp only [this, hpu _ ha']
  obtain ⟨hI1, hM1⟩ := hA1
  have hE1 : ∫ z in Fd, u' (h z) ^ 2 = (volume Fd).toReal := by
    field_simp at hM1; linarith
  have hE2 : ∀ m, ∫ z in Fd, u ((p : ℂ) • z + v m) ^ 2 = (volume Fd).toReal := fun m => by
    have := (hA2 m).2; field_simp at this; linarith
  rcases le_or_gt T 0 with hT0 | hT0
  · exact hT0.trans (Nat.cast_nonneg n)

  have hpt : ∀ z, T ^ 2 * u' (h z) ^ 2 ≤ (n : ℝ) * ∑ m, u ((p : ℂ) • z + v m) ^ 2 := by
    intro z
    have h0 : 0 ≤ T * u' (h z) := mul_nonneg hT0.le (hu' _)
    calc T ^ 2 * u' (h z) ^ 2 = (T * u' (h z)) ^ 2 := by ring
      _ ≤ (∑ m, u ((p : ℂ) • z + v m)) ^ 2 := pow_le_pow_left₀ h0 (hT z) 2
      _ ≤ (Finset.univ : Finset (Fin n)).card * ∑ m, u ((p : ℂ) • z + v m) ^ 2 := sq_sum_le_card_mul_sum_sq
      _ = (n : ℝ) * ∑ m, u ((p : ℂ) • z + v m) ^ 2 := by simp
  have hint : ∫ z in Fd, T ^ 2 * u' (h z) ^ 2 ≤ ∫ z in Fd, (n : ℝ) * ∑ m, u ((p : ℂ) • z + v m) ^ 2 := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => by positivity) ?_
      (Filter.Eventually.of_forall hpt)
    exact (integrable_finsetSum _ fun m _ => (hA2 m).1).const_mul _
  rw [integral_const_mul, integral_const_mul, integral_finsetSum _ fun m _ => (hA2 m).1, hE1] at hint
  simp only [hE2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hint
  have hT2 : T ^ 2 ≤ (n : ℝ) ^ 2 := by nlinarith
  exact abs_le_of_sq_le_sq' hT2 (Nat.cast_nonneg n) |>.2 |> fun h => h

end GlobalTheory.PeriodicMean
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology

theorem _root_.GlobalTheory.T.exists_GL_mul_rightColumns_eq_zero_of_rank : ∀ (k m a b n : Type) [Field k] [Fintype m] [Fintype a] [Fintype b] [Fintype n] [DecidableEq n] (e : a ⊕ b ≃ n) (x : Matrix m n k), x.rank = Fintype.card a → ∃ g : GL n k, ∀ i j, (x * g.val) i (e (Sum.inr j)) = 0 := by
  first | exact @GlobalTheory.exists_gl_mul_cols_eq_zero_of_rank | exact GlobalTheory.exists_gl_mul_cols_eq_zero_of_rank | (intros; apply GlobalTheory.exists_gl_mul_cols_eq_zero_of_rank <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology

theorem _root_.GlobalTheory.T.leftColumns_mulVec_injective_of_rank_eq_card : ∀ (k m a b n : Type) [Field k] [Fintype m] [Fintype a] [Fintype b] [Fintype n] (e : a ⊕ b ≃ n) (x : Matrix m n k), x.rank = Fintype.card a → (∀ i j, x i (e (Sum.inr j)) = 0) → ∀ v : a → k, (x.submatrix id (fun i => e (Sum.inl i))) *ᵥ v = 0 → v = 0 := by
  first | exact @GlobalTheory.mulVec_firstCols_eq_zero_of_rank_eq_card | exact GlobalTheory.mulVec_firstCols_eq_zero_of_rank_eq_card | (intros; apply GlobalTheory.mulVec_firstCols_eq_zero_of_rank_eq_card <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

noncomputable section
namespace GlobalTheory.PairingOne

section Alg
variable {k : Type*} [Field k] {m : Type*} [Fintype m] [DecidableEq m]

end Alg

variable {k : Type*} [Field k] [ValuativeRel k] {m : Type*} [Fintype m] [DecidableEq m]

variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isCompact_bounded (t : ValueGroupWithZero k) :
    IsCompact {w : GL m k | (∀ a b, valuation k (w.val a b) ≤ t) ∧ ∀ a b, valuation k ((w⁻¹).val a b) ≤ t} := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hK : IsCompact {A : Matrix m m k | ∀ i j, valuation k (A i j) ≤ t} := by
    have h : IsCompact (Set.pi Set.univ fun _ : m => Set.pi Set.univ fun _ : m => {x : k | valuation k x ≤ t}) :=
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k t
    have e : {A : Matrix m m k | ∀ i j, valuation k (A i j) ≤ t} =
        (Set.pi Set.univ fun _ : m => Set.pi Set.univ fun _ : m => {x : k | valuation k x ≤ t}) :=
      Set.ext fun x => ⟨fun hx i _ j _ => hx i j, fun hx i j => hx i trivial j trivial⟩
    rw [e]; exact h
  have h := (Units.isClosedEmbedding_embedProduct (α := Matrix m m k)).isCompact_preimage
    (hK.prod (hK.image MulOpposite.continuous_op))
  convert h using 1
  ext g
  simp only [Set.mem_setOf_eq, Set.mem_preimage, Units.embedProduct_apply,
    Set.mem_prod, (MulOpposite.op_injective).mem_set_image]

end GlobalTheory.PairingOne
end
end
