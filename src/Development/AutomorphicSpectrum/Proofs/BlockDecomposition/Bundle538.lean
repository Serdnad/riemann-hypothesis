module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrreducibleSecondFactorOfIrreducibleProduct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1298
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle529
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle432
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1623
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle106
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle089
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PrimitiveVectorsContentDecomposition
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.GeneralLinearIntegers.AlgebraMapIntMemOint
public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.SquareIntegrableAtPlace.SqIntAt
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.IsSliceMap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle430

@[expose] public section

section

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.CompanionTheory.DegPrinSeries

theorem nontrivial_subrepresentation : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₁ → IsSmoothChar χ₂ → Nontrivial (Subrepresentation (parInd (two (stdSum (rfl : a + b = a + b))) ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom))) := by
  intro k _ _ _ _ a b χ₁ χ₂ hχ₁ hχ₂
  have hdetChar : ∀ (m : ℕ) (χ : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar χ →
      GlobalTheory.PRep.IsSmooth (GlobalTheory.SmGL.detRep (Fin m) χ) := by
    intro m χ hχ
    have hc : Continuous (Matrix.GeneralLinearGroup.det : GL (Fin m) k → kˣ) := by
      rw [Units.continuous_iff]
      constructor
      · have hval : (Units.val ∘ (Matrix.GeneralLinearGroup.det : GL (Fin m) k → kˣ)) =
            fun g : GL (Fin m) k => Matrix.det (g : Matrix (Fin m) (Fin m) k) := by
          funext g
          exact Matrix.GeneralLinearGroup.val_det_apply g
        rw [hval]
        exact Units.continuous_val.matrix_det
      · have hinv : (fun g : GL (Fin m) k => ((Matrix.GeneralLinearGroup.det g)⁻¹ : kˣ).val) =
            fun g => Matrix.det ((g⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) := by
          funext g
          rw [← map_inv, Matrix.GeneralLinearGroup.val_det_apply]
        rw [hinv]
        exact Units.continuous_coe_inv.matrix_det
    unfold GlobalTheory.SmGL.detRep
    rw [GlobalTheory.SmGL.isSmooth_ofChar_iff]
    unfold GlobalTheory.SmGL.IsSmoothChar at hχ ⊢
    exact hc.isOpen_preimage _ hχ
  have hsmooth := GlobalTheory.SmGL.isSmooth_comp
    (GlobalTheory.SmGL.isSmooth_extTensor (hdetChar a χ₁ hχ₁) (hdetChar b χ₂ hχ₂))
    (GlobalTheory.SmGL.leviTwo k (Fin a) (Fin b)).symm.toMonoidHom
    (by exact (continuous_apply Bool.false).prodMk (continuous_apply Bool.true))
  have hu : ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ)) ≠ 0 := by
    intro h0
    have := congrArg (TensorProduct.lid ℂ ℂ) h0
    simp at this
  obtain ⟨f, hf1, -⟩ := GlobalTheory.SmGL.ProdIrr.exists_indSp_apply_one
    (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum (rfl : a + b = a + b))) _
    hsmooth ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ))
  refine ⟨⟨⟨⊥, fun g ⦃v⦄ hv => ?_⟩, ⟨⊤, fun _ ⦃_⦄ _ => Submodule.mem_top⟩, fun hEq => ?_⟩⟩
  · rw [Submodule.mem_bot] at hv ⊢
    rw [hv, map_zero]
  · have hsub := congrArg Subrepresentation.toSubmodule hEq
    have hf : f = 0 := (Submodule.mem_bot ℂ).1 (Submodule.eq_top_iff'.1 hsub f)
    rw [hf] at hf1
    apply hu
    rw [← hf1]
    first
    | rfl
    | simp

end GlobalTheory.CompanionTheory.DegPrinSeries
end
end

section

open scoped Classical InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.AutomorphicL2Unitary GlobalTheory.SqIntGL
open scoped GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory.CompanionTheory.FinDiscOrth

theorem setIntegral_mul_conj_eq_inner : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (μ : Measure (GA E N)) [μ.IsHaarMeasure] (F : Set (GA E N)), IsFundamentalDomain (latticeGL E N) F μ → ∀ x y : Sm E N, x ∈ squareIntegrableSmoothSubmoduleGL μ → y ∈ squareIntegrableSmoothSubmoduleGL μ → ∫ g in F, x.1 g * (starRingEnd ℂ) (y.1 g) ∂μ = ⟪l2Map μ y, l2Map μ x⟫_ℂ := by
  intro E _ _ _ N μ _ F hF x y hx hy
  rw [l2Map_apply μ hx, l2Map_apply μ hy, MemL2Quotient.inner_toL2_eq_theta_pairing, pet_eq hF ((mem_l2Sub μ).1 hx).1 ((mem_l2Sub μ).1 hy).1]

end GlobalTheory.CompanionTheory.FinDiscOrth
end

section

open scoped Classical InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.AutomorphicL2Unitary GlobalTheory.SqIntGL
open scoped GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section

namespace GlobalTheory.CompanionTheory.FinDiscOrth

theorem rt_mem_l2Sub_and_inner_eq (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (μ : Measure (GA E N))
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (g : GA E N) (x y : Sm E N) (hx : x ∈ squareIntegrableSmoothSubmoduleGL μ) (hy : y ∈ squareIntegrableSmoothSubmoduleGL μ) :
    rt E N g x ∈ squareIntegrableSmoothSubmoduleGL μ ∧ ⟪l2Map μ (rt E N g x), l2Map μ (rt E N g y)⟫_ℂ = ⟪l2Map μ x, l2Map μ y⟫_ℂ := by
  have key : ∀ z : Sm E N, ∀ hz : z ∈ squareIntegrableSmoothSubmoduleGL μ, ∃ h' : rt E N g z ∈ squareIntegrableSmoothSubmoduleGL μ,
      l2Map μ (rt E N g z) = R (latticeGL E N) μ g (l2Map μ z) := by
    intro z hz
    have h' : rt E N g z ∈ squareIntegrableSmoothSubmoduleGL μ := ((mem_l2Sub μ).1 hz).mul_right g
    refine ⟨h', ?_⟩
    rw [l2Map_apply μ h', l2Map_apply μ hz, right_translate_toL2]
    rfl
  obtain ⟨hx', ex⟩ := key x hx
  obtain ⟨hy', ey⟩ := key y hy
  refine ⟨hx', ?_⟩
  let U : L2 (latticeGL E N) μ →ₗᵢ[ℂ] L2 (latticeGL E N) μ :=
    ⟨(R (latticeGL E N) μ g).toLinearMap, norm_R g⟩
  rw [ex, ey]
  exact U.inner_map_map _ _

end GlobalTheory.CompanionTheory.FinDiscOrth
end
end

section

open scoped Classical InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.AutomorphicL2Unitary GlobalTheory.SqIntGL
open scoped GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section

namespace GlobalTheory.CompanionTheory.FinDiscAvg

theorem exists_sum_fixed {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [AddCommGroup W] [Module ℂ W] (ρ : G →* Module.End ℂ W) (x : W) (ho : IsOpen {k | ρ k x = x}) :
    ∃ R : Finset G, R.Nonempty ∧ ∀ u, ρ u (∑ r ∈ R, ρ r x) = ∑ r ∈ R, ρ r x := by
  let K : Subgroup G :=
    { carrier := {k | ρ k x = x}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul, Module.End.mul_apply, hb, ha]
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        have h : ρ a⁻¹ (ρ a x) = x := by
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
        rwa [ha] at h }
  have hK : ∀ k, k ∈ K ↔ ρ k x = x := fun _ => Iff.rfl
  obtain ⟨R, hR, hc⟩ := GlobalTheory.compact_finite_leftCoset_reps G K ho Set.univ isCompact_univ
  have hc' : ∀ g : G, ∃ r ∈ R, r⁻¹ * g ∈ K := fun g => hc g (Set.mem_univ g)
  have hne : R.Nonempty := by
    obtain ⟨r, hr, -⟩ := hc' 1
    exact ⟨r, hr⟩
  refine ⟨R, hne, fun u => ?_⟩
  choose! σ hσR hσ using fun r : G => hc' (u * r)
  have hval : ∀ r, ρ (u * r) x = ρ (σ r) x := by
    intro r
    have h := (hK _).1 (hσ r)
    have e : u * r = σ r * ((σ r)⁻¹ * (u * r)) := by group
    rw [e, map_mul, Module.End.mul_apply, h]
  have hinj : Set.InjOn σ R := by
    intro r hr r' hr' e
    refine hR r hr r' hr' ?_
    have h1 := hσ r
    have h2 := hσ r'
    rw [show σ r = σ r' from e] at h1
    have := K.mul_mem (K.inv_mem h1) h2
    have e2 : ((σ r')⁻¹ * (u * r))⁻¹ * ((σ r')⁻¹ * (u * r')) = r⁻¹ * r' := by group
    rwa [e2] at this
  have himg : R.image σ = R := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro s hs
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hs
      exact hσR r
    · rw [Finset.card_image_of_injOn hinj]
  calc ρ u (∑ r ∈ R, ρ r x) = ∑ r ∈ R, ρ (σ r) x := by

        rw [map_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [← hval, map_mul, Module.End.mul_apply]
    _ = ∑ s ∈ R.image σ, ρ s x := (Finset.sum_image (f := fun s => ρ s x) hinj).symm
    _ = ∑ r ∈ R, ρ r x := by rw [himg]

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}
  (μ : Measure (GA E N)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]

theorem l2Map_right_translate (k : GL (Fin N) (Af E)) {a : Sm E N} (ha : a ∈ squareIntegrableSmoothSubmoduleGL μ) (hb : finRep E N k a ∈ squareIntegrableSmoothSubmoduleGL μ) :
    l2Map μ (finRep E N k a) = R (latticeGL E N) μ (finGL E N k) (l2Map μ a) := by
  rw [l2Map_apply μ ha, l2Map_apply μ hb, right_translate_toL2]
  rfl

theorem inner_R (g : GA E N) (u v : L2 (latticeGL E N) μ) :
    ⟪R (latticeGL E N) μ g u, R (latticeGL E N) μ g v⟫_ℂ = ⟪u, v⟫_ℂ := by
  let T : L2 (latticeGL E N) μ →ₗᵢ[ℂ] L2 (latticeGL E N) μ :=
    ⟨(R (latticeGL E N) μ g : L2 (latticeGL E N) μ →L[ℂ] L2 (latticeGL E N) μ).toLinearMap, norm_R g⟩
  exact T.inner_map_map u v

theorem exists_avg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (μ : Measure (GA E N)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (V : Submodule ℂ (Sm E N)), IsDiscrete V → ∀ L : Subgroup (GL (Fin N) (Af E)), IsCompact (L : Set (GL (Fin N) (Af E))) → ∀ x ∈ V, ∃ x' ∈ V, (∀ u ∈ L, finRep E N u x' = x') ∧ ∀ y : Sm E N, y ∈ squareIntegrableSmoothSubmoduleGL μ → (∀ u ∈ L, finRep E N u y = y) → ⟪l2Map μ x, l2Map μ y⟫_ℂ = ⟪l2Map μ x', l2Map μ y⟫_ℂ := by
  intro E _ _ _ N μ _ _ V hV L hL x hx
  haveI : CompactSpace L := isCompact_iff_compactSpace.1 hL
  let ρ : L →* Module.End ℂ (Sm E N) := (finRep E N).comp L.subtype
  have hρ : ∀ l : L, ρ l = finRep E N (l : GL (Fin N) (Af E)) := fun _ => rfl
  have ho : IsOpen {k : L | ρ k x = x} :=
    (hV.aut x hx).level.preimage continuous_subtype_val
  obtain ⟨S, hS, hfix⟩ := exists_sum_fixed ρ x ho
  have hn : ((S.card : ℂ)) ≠ 0 := Nat.cast_ne_zero.2 hS.card_pos.ne'
  have hmem : ∀ l : L, ρ l x ∈ V := fun l => hV.stable (.fin _) x hx
  refine ⟨(S.card : ℂ)⁻¹ • ∑ r ∈ S, ρ r x, V.smul_mem _ (V.sum_mem fun r _ => hmem r), ?_, ?_⟩
  · intro u hu
    rw [map_smul, ← hρ ⟨u, hu⟩ , hfix]
  · intro y hy hyL
    have hl2 : ∀ z ∈ V, z ∈ squareIntegrableSmoothSubmoduleGL μ := fun z hz => mem_l2Sub_of_isAutForm μ (hV.aut z hz) (hV.sqInt z hz)
    have hxl := hl2 x hx
    have key : ∀ r : L, ⟪l2Map μ (ρ r x), l2Map μ y⟫_ℂ = ⟪l2Map μ x, l2Map μ y⟫_ℂ := by
      intro r
      have e1 := l2Map_right_translate μ (r : GL (Fin N) (Af E)) hxl (hl2 _ (hmem r))
      have e2 := l2Map_right_translate μ (r : GL (Fin N) (Af E)) hy (by rw [hyL _ r.2]; exact hy)
      rw [hyL _ r.2] at e2
      rw [hρ, e1]
      conv_lhs => rw [e2]
      exact inner_R μ _ _ _

    rw [map_smul, map_sum, inner_smul_left, sum_inner, Finset.sum_congr rfl fun r _ => key r,
    Finset.sum_const, nsmul_eq_mul, map_inv₀, Complex.conj_natCast, inv_mul_cancel_left₀ hn]

end GlobalTheory.CompanionTheory.FinDiscAvg

end
end

section

open scoped Classical InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.AutomorphicL2Unitary GlobalTheory.SqIntGL
open scoped GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory.CompanionTheory.FinDiscOrth

theorem lie_skew_l2Map : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (μ : Measure (GA E N)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (X : Lie E N) (x y : Sm E N), Continuous x.1 → Continuous y.1 → Continuous (lie E N X x).1 → Continuous (lie E N X y).1 → x ∈ squareIntegrableSmoothSubmoduleGL μ → y ∈ squareIntegrableSmoothSubmoduleGL μ → lie E N X x ∈ squareIntegrableSmoothSubmoduleGL μ → lie E N X y ∈ squareIntegrableSmoothSubmoduleGL μ → ⟪l2Map μ x, l2Map μ (lie E N X y)⟫_ℂ = -⟪l2Map μ (lie E N X x), l2Map μ y⟫_ℂ := by
  intro E _ _ _ N μ _ _ X x y cx cy cXx cXy hx hy hXx hXy
  rw [l2Map_apply μ hx, l2Map_apply μ hy, l2Map_apply μ hXx, l2Map_apply μ hXy,
    GlobalTheory.CompanionTheory.LieSkew.lie_skew E N μ X x y ((mem_l2Sub μ).1 hx) ((mem_l2Sub μ).1 hy)
      ((mem_l2Sub μ).1 hXx) ((mem_l2Sub μ).1 hXy) cx cy cXx cXy, neg_neg]

end GlobalTheory.CompanionTheory.FinDiscOrth
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.UnipLevel

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem blk_one_inv {a b n : ℕ} (h : a + b = n) (w : Pl E) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    (blk h w 1 X)⁻¹ = blk h w 1 (-X) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [GlobalTheory.LeviFubini.blk_mul_blk]
  simpa using GlobalTheory.LeviFubini.blk_one_zero h w

theorem blk_one_corner {a b n : ℕ} (h : a + b = n) (w : Pl E) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E))
    (i : Fin a) (j : Fin b) :
    (blk h w 1 X).val (CtLevel.blkEq h (Sum.inl i)) (CtLevel.blkEq h (Sum.inr j)) = X i j := by
  rw [CtLevel.blk_val]
  simp

theorem continuous_blk_one_val {a b n : ℕ} (h : a + b = n) (w : Pl E) :
    Continuous fun X : Matrix (Fin a) (Fin b) (w.adicCompletion E) => (blk h w 1 X).val := by
  refine continuous_matrix fun i j => ?_
  obtain ⟨i, rfl⟩ := (CtLevel.blkEq h).surjective i
  obtain ⟨j, rfl⟩ := (CtLevel.blkEq h).surjective j
  simp only [CtLevel.blk_val, reindex_apply, submatrix_apply, Equiv.symm_apply_apply]
  rcases i with i | i <;> rcases j with j | j
  · simpa using continuous_const
  · simpa using continuous_id.matrix_elem i j
  · simpa using continuous_const
  · simpa using continuous_const

theorem continuous_blk_one {a b n : ℕ} (h : a + b = n) (w : Pl E) :
    Continuous fun X : Matrix (Fin a) (Fin b) (w.adicCompletion E) => blk h w 1 X := by
  refine Units.continuous_iff.2 ⟨continuous_blk_one_val h w, ?_⟩
  have e : (fun X : Matrix (Fin a) (Fin b) (w.adicCompletion E) => (((blk h w 1 X)⁻¹ : GLw n w)).val) =
      (fun X => (blk h w 1 X).val) ∘ fun X => -X := by
    funext X
    simp [blk_one_inv]
  exact e ▸ (continuous_blk_one_val h w).comp continuous_neg

def intSub (a b : ℕ) (w : Pl E) : Subgroup (Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E))) where
  carrier := {X | ∀ i j, Valued.v (Multiplicative.toAdd X i j) ≤ 1}
  one_mem' := fun i j => by simp
  mul_mem' := fun {X Y} hX hY i j => by
    simpa using (Valued.v.map_add _ _).trans (max_le (hX i j) (hY i j))
  inv_mem' := fun {X} hX i j => by simpa using hX i j

theorem intMat_eq_intSub (a b : ℕ) (w : Pl E) : intMat a b w = intSub a b w := by
  refine le_antisymm ((Subgroup.closure_le _).2 fun X hX => hX) fun X hX => Subgroup.subset_closure hX

theorem isCompact_intSub (a b : ℕ) (w : Pl E) :
    IsCompact (intSub a b w : Set (Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)))) := by
  have e : (intSub a b w : Set (Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)))) =
      Multiplicative.toAdd ⁻¹' (Set.pi Set.univ fun _ : Fin a => Set.pi Set.univ
        fun _ : Fin b => ((w.adicCompletionIntegers E : Set (w.adicCompletion E)))) := by
    ext X
    exact ⟨fun hX i _ j _ => hX i j, fun hX i j => hX i trivial j trivial⟩
  rw [e]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers w

theorem unip_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b n : ℕ) (h : a + b = n) (w : Pl E) (K' : Subgroup (GLw n w)), IsOpen (K' : Set (GLw n w)) → K' ≤ GlobalTheory.LFun.KGL w (n := n) → (K'.subgroupOf (GlobalTheory.LeviFubini.parB h w)).comap (GlobalTheory.LeviFubini.uN h w) ≤ intMat a b w ∧ ((K'.subgroupOf (GlobalTheory.LeviFubini.parB h w)).comap (GlobalTheory.LeviFubini.uN h w)).relIndex (intMat a b w) ≠ 0 := by
  intro E _ _ _ a b n h w K' hK' hKK
  have hmem : ∀ X, X ∈ (K'.subgroupOf (GlobalTheory.LeviFubini.parB h w)).comap (GlobalTheory.LeviFubini.uN h w) ↔
      blk h w 1 (Multiplicative.toAdd X) ∈ K' := fun X => Iff.rfl
  refine ⟨fun X hX => ?_, ?_⟩
  · rw [intMat_eq_intSub]
    intro i j
    obtain ⟨u, hu⟩ := hKK ((hmem X).1 hX)
    have h1 : Valued.v ((blk h w 1 (Multiplicative.toAdd X)).val (CtLevel.blkEq h (Sum.inl i))
        (CtLevel.blkEq h (Sum.inr j))) ≤ 1 := by
      rw [← hu]
      exact (u.val (CtLevel.blkEq h (Sum.inl i)) (CtLevel.blkEq h (Sum.inr j))).2
    rwa [blk_one_corner] at h1
  · have hopen : IsOpen (((K'.subgroupOf (GlobalTheory.LeviFubini.parB h w)).comap (GlobalTheory.LeviFubini.uN h w) :
        Subgroup _) : Set (Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)))) :=
      hK'.preimage ((continuous_blk_one h w).comp continuous_toAdd)
    rw [intMat_eq_intSub]
    haveI : CompactSpace (intSub a b w) := isCompact_iff_compactSpace.1 (isCompact_intSub a b w)
    haveI : Finite ((intSub a b w) ⧸ ((K'.subgroupOf (GlobalTheory.LeviFubini.parB h w)).comap (GlobalTheory.LeviFubini.uN h w)).subgroupOf (intSub a b w)) :=
      Subgroup.quotient_finite_of_isOpen _ (hopen.preimage continuous_subtype_val)
    exact Subgroup.index_ne_zero_of_finite

end GlobalTheory.CompanionTheory.UnipLevel
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.LeviInt

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem blk_entries_int {a b n : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (X : Matrix (Fin a) (Fin b) (w.adicCompletion E))
    (h1 : ∀ i j, (m.1.val i j) ∈ Ov E w) (h2 : ∀ i j, (m.2.val i j) ∈ Ov E w)
    (hX : ∀ i j, X i j ∈ Ov E w) (i j : Fin n) :
    ((blk h w m X : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j ∈ Ov E w := by
  rw [CtLevel.blk_val]
  obtain ⟨i', rfl⟩ := (CtLevel.blkEq h).surjective i
  obtain ⟨j', rfl⟩ := (CtLevel.blkEq h).surjective j
  rw [reindex_apply, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rcases i' with i' | i' <;> rcases j' with j' | j'
  · simpa using h1 i' j'
  · simp only [fromBlocks_apply₁₂, Matrix.mul_apply]
    exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (h1 _ _) (hX _ _)
  · simp
  · simpa using h2 i' j'

theorem blk_corner {a b n : ℕ} (h : a + b = n) (w : Pl E)
    (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) (i : Fin a) (j : Fin b) :
    ((blk h w 1 X : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E))
      (CtLevel.blkEq h (Sum.inl i)) (CtLevel.blkEq h (Sum.inr j)) = X i j := by
  rw [CtLevel.blk_val, reindex_apply, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  simp

theorem comap_uN_and_map_sM : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b n : ℕ) (h : a + b = n) (w : Pl E), ((GlobalTheory.LFun.KGL w (n := n)).subgroupOf (GlobalTheory.LeviFubini.parB h w)).comap (GlobalTheory.LeviFubini.uN h w) = intMat a b w ∧ ((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b))).map (GlobalTheory.LeviFubini.sM h w) ≤ (GlobalTheory.LFun.KGL w (n := n)).subgroupOf (GlobalTheory.LeviFubini.parB h w) := by
  intro E _ _ _ a b n h w
  have hinv : ∀ X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)),
      ((GlobalTheory.LeviFubini.uN h w X : GlobalTheory.LeviFubini.parB h w) : GLw n w)⁻¹ =
        blk h w 1 (Multiplicative.toAdd X⁻¹) := fun X => by
    rw [← GlobalTheory.LeviFubini.uN_val, map_inv, Subgroup.coe_inv]
  have hint : ∀ k : ℕ, ∀ i j : Fin k, ((1 : GLw k w).val i j) ∈ Ov E w := fun k i j => by
    rw [Units.val_one, Matrix.one_apply]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  refine ⟨le_antisymm (fun X hX => ?_) ?_, ?_⟩
  · rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, GlobalTheory.LeviFubini.uN_val] at hX
    refine Subgroup.subset_closure fun i j => ?_
    have h1 := (GlobalTheory.AdelicU.mem_GLint_iff.1 hX).1 (CtLevel.blkEq h (Sum.inl i)) (CtLevel.blkEq h (Sum.inr j))
    rw [blk_corner] at h1
    exact h1
  · refine (Subgroup.closure_le _).2 fun X hX => ?_
    have hX' : ∀ i j, Multiplicative.toAdd X i j ∈ Ov E w := hX
    rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    refine GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [GlobalTheory.LeviFubini.uN_val]
      exact blk_entries_int h w 1 _ (hint a) (hint b) hX' i j
    · rw [hinv]
      refine blk_entries_int h w 1 _ (hint a) (hint b) (fun i j => ?_) i j
      simpa using Subring.neg_mem _ (hX' i j)
  · rintro _ ⟨m, ⟨h1, h2⟩, rfl⟩
    obtain ⟨h11, h12⟩ := GlobalTheory.AdelicU.mem_GLint_iff.1 h1
    obtain ⟨h21, h22⟩ := GlobalTheory.AdelicU.mem_GLint_iff.1 h2
    rw [Subgroup.mem_subgroupOf]
    refine GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [GlobalTheory.LeviFubini.sM_val]
      exact blk_entries_int h w m 0 h11 h21 (fun _ _ => Subring.zero_mem _) i j
    · rw [← Subgroup.coe_inv, ← map_inv, GlobalTheory.LeviFubini.sM_val]
      exact blk_entries_int h w m⁻¹ 0 h12 h22 (fun _ _ => Subring.zero_mem _) i j

end GlobalTheory.CompanionTheory.LeviInt
end

section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.SpectralAccumulation.FD
open scoped GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section

namespace GlobalTheory.CompanionTheory.LatticeFD

theorem exists_measurable_isFundamentalDomain (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ)
    [MeasurableSpace (GA E N)] [BorelSpace (GA E N)] :
    ∃ 𝓕 : Set (GA E N), MeasurableSet 𝓕 ∧ ∀ μ : Measure (GA E N), IsFundamentalDomain (latticeGL E N) 𝓕 μ :=
  ⟨GlobalTheory.AutomorphicL2Unitary.stdDom (latticeGL E N), GlobalTheory.AutomorphicL2Unitary.measurableSet_stdDom _,
    fun μ => GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom _ μ⟩

end GlobalTheory.CompanionTheory.LatticeFD

end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypMass

theorem _root_.GlobalTheory.T.primitive_vectors_content_decomposition : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ (ι : Type) (c : ι → Fv F v ⊗[F] E) (w : ι → ℕ), IsContent σ b v c w → MeasurableSet (primV σ J b v) ∧ (∀ i, ∀ y ∈ primV σ J b v, scalT (c i) y ∈ latV b v) ∧ (∀ i j, ∀ y ∈ primV σ J b v, ∀ y' ∈ primV σ J b v, scalT (c i) y = scalT (c j) y' → i = j) ∧ (∀ y : Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E, LinearIndependent (Fv F v ⊗[F] E) y → gramR (Fv F v) σ (hypOne J) y = 0 → y ∈ latV b v → ∃ i, ∃ y₀ ∈ primV σ J b v, y = scalT (c i) y₀) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypMass.PrimDec.eventually_primV_decomposition | exact GlobalTheory.CompanionTheory.WeilSiegel.HypMass.PrimDec.eventually_primV_decomposition | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypMass.PrimDec.eventually_primV_decomposition <;> assumption)
end
