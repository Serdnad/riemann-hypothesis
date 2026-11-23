module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle211
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle209
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle217
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle303
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle302
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightedSupDriftOnOrthonormalFrames
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBoundOrthonormalFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle201
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle045
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle172
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle205
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle006
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelOfDualParameter
public import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1262
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1494
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicDiscreteSeriesLowestKTypeSmoothIrredu
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelaf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle014
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle007
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FlatSpaceComponents
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteReal.RecTie

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmVec

theorem exists_l2_lift {H : Type} [AddCommGroup H] [Module ℂ H] (D : Submodule ℂ H) {X : Type} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] (ν : Measure X) [IsFiniteMeasure ν] (a : H →ₗ[ℂ] (X → ℂ))
    (ha : ∀ w ∈ D, Continuous (a w) ∧ ∃ C : ℝ, ∀ x, ‖a w x‖ ≤ C) :
    ∃ A : H →ₗ[ℂ] Lp ℂ 2 ν, ∀ w ∈ D, (A w : X → ℂ) =ᵐ[ν] a w := by
  classical
  have hm : ∀ w : D, MemLp (a w) 2 ν := fun w => by
    obtain ⟨hc, C, hC⟩ := ha w w.2
    exact MemLp.of_bound hc.aestronglyMeasurable C (Filter.Eventually.of_forall hC)
  let f : D →ₗ[ℂ] Lp ℂ 2 ν :=
    { toFun := fun w => (hm w).toLp (a w)
      map_add' := fun w w' => by
        refine Lp.ext ?_
        filter_upwards [(hm (w + w')).coeFn_toLp, (hm w).coeFn_toLp, (hm w').coeFn_toLp,
          Lp.coeFn_add ((hm w).toLp (a w)) ((hm w').toLp (a w'))] with x h1 h2 h3 h4
        rw [h4, Pi.add_apply, h1, h2, h3, Submodule.coe_add, map_add (f := _), Pi.add_apply]
      map_smul' := fun c w => by
        refine Lp.ext ?_
        filter_upwards [(hm (c • w)).coeFn_toLp, (hm w).coeFn_toLp,
          Lp.coeFn_smul c ((hm w).toLp (a w))] with x h1 h2 h3
        rw [RingHom.id_apply, h3, Pi.smul_apply, h1, h2, Submodule.coe_smul, map_smul, Pi.smul_apply] }
  obtain ⟨g, hg⟩ := LinearMap.exists_extend f
  refine ⟨g, fun w hw => ?_⟩
  have hgw : g w = f ⟨w, hw⟩ := by rw [← hg]; rfl
  rw [hgw]
  exact (hm ⟨w, hw⟩).coeFn_toLp

theorem l2_inner_of_ae {X : Type} [MeasurableSpace X] {ν : Measure X} {f g : Lp ℂ 2 ν} {u v : X → ℂ}
    (hf : (f : X → ℂ) =ᵐ[ν] u) (hg : (g : X → ℂ) =ᵐ[ν] v) : ⟪f, g⟫_ℂ = ∫ x, star (u x) * v x ∂ν := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf, hg] with x hx hy
  rw [hx, hy, RCLike.inner_apply, mul_comm, starRingEnd_apply]

private lemma jm_sq_lemma {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  split_ifs <;> norm_num

private lemma jm_herm_lemma_2 {n : ℕ} (ε : Fin n → Bool) : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  by_cases h : ε i <;> simp [h]

private lemma jm_conjTranspose_jm_mem_and_inverse {n : ℕ} {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) :
    Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε ∈ UJset ε ∧ (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) * g = 1 ∧
      g * (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) = 1 := by
  have h : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := hg
  have jj : ∀ Y : Matrix (Fin n) (Fin n) ℂ, Formalism.REAL.Jm ε * (Formalism.REAL.Jm ε * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, jm_sq_lemma, Matrix.one_mul]
  have hl : (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) * g = 1 := by
    calc (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) * g = Formalism.REAL.Jm ε * (gᴴ * Formalism.REAL.Jm ε * g) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h, jm_sq_lemma]
  have hr : g * (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) = 1 := mul_eq_one_comm.mp hl
  refine ⟨?_, hl, hr⟩
  have hr' : g * (Formalism.REAL.Jm ε * (gᴴ * Formalism.REAL.Jm ε)) = 1 := by simpa only [Matrix.mul_assoc] using hr
  show (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε)ᴴ * Formalism.REAL.Jm ε * (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) = Formalism.REAL.Jm ε
  simp only [Matrix.conjTranspose_mul, jm_herm_lemma_2, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, jj]
  rw [hr', Matrix.mul_one]

theorem schurLemma_equivariant_pair_boundedFunctions : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → ∀ (X : Type) [TopologicalSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] (ν : Measure X) [IsFiniteMeasure ν] (act : Formalism.REAL.UJ ε → X → X), Continuous (Function.uncurry act) → ∀ (a a' : H →ₗ[ℂ] (X → ℂ)), (∀ w ∈ smSub G (trRep σ P), Continuous (a w) ∧ (∃ C : ℝ, ∀ x, ‖a w x‖ ≤ C) ∧ ∀ (g : Formalism.REAL.UJ ε) x, a (σ (umat g) w) x = a w (act g x)) → (∀ x, Sobolev₂ (lieG G) (trRep σ P) ((LinearMap.proj x).comp a)) → (∀ w ∈ smSub G (trRep σ P), Continuous (a' w) ∧ (∃ C : ℝ, ∀ x, ‖a' w x‖ ≤ C) ∧ ∀ (g : Formalism.REAL.UJ ε) x, a' (σ (umat g) w) x = a' w (act g x)) → (∀ x, Sobolev₂ (lieG G) (trRep σ P) ((LinearMap.proj x).comp a')) → (∀ g ∈ UJset ε, ∀ u ∈ smSub G (trRep σ P), ∀ w ∈ smSub G (trRep σ P), ∫ x, star (a (σ g u) x) * a (σ g w) x ∂ν = ∫ x, star (a u x) * a w x ∂ν) → (∀ g ∈ UJset ε, ∀ u ∈ smSub G (trRep σ P), ∀ w ∈ smSub G (trRep σ P), ∫ x, star (a' (σ g u) x) * a' (σ g w) x ∂ν = ∫ x, star (a' u x) * a' w x ∂ν) → (∀ g ∈ UJset ε, ∀ u ∈ smSub G (trRep σ P), ∀ w ∈ smSub G (trRep σ P), ∫ x, star (a (σ g u) x) * a' (σ g w) x ∂ν = ∫ x, star (a u x) * a' w x ∂ν) → ∃ c : ℂ, ∀ w ∈ smSub G (trRep σ P), ∀ w' ∈ smSub G (trRep σ P), ∫ x, star (a w x) * a' w' x ∂ν = c * ⟪w, w'⟫_ℂ := by
  intro n ε H _ _ _ σ P G hP hG hσ hirr X _ _ _ _ ν _ act hact a a' ha hsa ha' hsa' hI hI' hIx
  obtain ⟨A, hA⟩ := exists_l2_lift (smSub G (trRep σ P)) ν a (fun w hw => ⟨(ha w hw).1, (ha w hw).2.1⟩)
  obtain ⟨A', hA'⟩ := exists_l2_lift (smSub G (trRep σ P)) ν a' (fun w hw => ⟨(ha' w hw).1, (ha' w hw).2.1⟩)
  have hmem : ∀ g ∈ UJset ε, ∀ w ∈ smSub G (trRep σ P), σ g w ∈ smSub G (trRep σ P) :=
    fun g hg w hw => sigma_mem hP hG hσ hw hg
  have hAinv : ∀ g ∈ UJset ε, ∀ u ∈ smSub G (trRep σ P), ∀ w ∈ smSub G (trRep σ P),
      ⟪A (σ g u), A (σ g w)⟫_ℂ = ⟪A u, A w⟫_ℂ := by
    intro g hg u hu w hw
    rw [l2_inner_of_ae (hA _ (hmem g hg u hu)) (hA _ (hmem g hg w hw)), l2_inner_of_ae (hA u hu) (hA w hw)]
    exact hI g hg u hu w hw
  have hA'inv : ∀ g ∈ UJset ε, ∀ u ∈ smSub G (trRep σ P), ∀ w ∈ smSub G (trRep σ P),
      ⟪A' (σ g u), A' (σ g w)⟫_ℂ = ⟪A' u, A' w⟫_ℂ := by
    intro g hg u hu w hw
    rw [l2_inner_of_ae (hA' _ (hmem g hg u hu)) (hA' _ (hmem g hg w hw)), l2_inner_of_ae (hA' u hu) (hA' w hw)]
    exact hI' g hg u hu w hw
  have hxinv : ∀ g ∈ UJset ε, ∀ u ∈ smSub G (trRep σ P), ∀ w ∈ smSub G (trRep σ P),
      ⟪A (σ g u), A' (σ g w)⟫_ℂ = ⟪A u, A' w⟫_ℂ := by
    intro g hg u hu w hw
    rw [l2_inner_of_ae (hA _ (hmem g hg u hu)) (hA' _ (hmem g hg w hw)), l2_inner_of_ae (hA u hu) (hA' w hw)]
    exact hIx g hg u hu w hw
  have hcl := closable_of_smoothing n ε H σ P G hP hG hσ (Lp ℂ 2 ν) A hAinv
    (continuous_inner_l2_translate n ε H σ P G hP hG hσ X ν act hact a A ha hsa hA)
    (GlobalTheory.T.smooth_vectors_continuous_l2 n ε H σ P G hP hG hσ X ν act hact a A ha hsa hA)
    (GlobalTheory.T.smooth_vectors_inner_product n ε H σ P G hP hG hσ X ν act hact a A ha hsa hA)
  have hcl' := closable_of_smoothing n ε H σ P G hP hG hσ (Lp ℂ 2 ν) A' hA'inv
    (continuous_inner_l2_translate n ε H σ P G hP hG hσ X ν act hact a' A' ha' hsa' hA')
    (GlobalTheory.T.smooth_vectors_continuous_l2 n ε H σ P G hP hG hσ X ν act hact a' A' ha' hsa' hA')
    (GlobalTheory.T.smooth_vectors_inner_product n ε H σ P G hP hG hσ X ν act hact a' A' ha' hsa' hA')
  have hnorm : ∀ B : H →ₗ[ℂ] Lp ℂ 2 ν, (∀ g ∈ UJset ε, ∀ u ∈ smSub G (trRep σ P), ∀ w ∈ smSub G (trRep σ P),
      ⟪B (σ g u), B (σ g w)⟫_ℂ = ⟪B u, B w⟫_ℂ) →
      ∀ i : UJset ε, ∀ w ∈ smSub G (trRep σ P), ‖B (σ i.1 w)‖ = ‖B w‖ := by
    intro B hB i w hw
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ) (B w), hB i.1 i.2 w hw w hw]
  have hrep := hσ.1
  obtain ⟨c, hc⟩ := GlobalTheory.T.schur_inner_eq_pair_closable_normInvariant (UJset ε) H (Lp ℂ 2 ν) (fun i => σ i.1) (smSub G (trRep σ P))
    (fun i v => hσ.2.1 i.1 i.2 v)
    (fun i => by
      obtain ⟨hj, hl, hr⟩ := jm_conjTranspose_jm_mem_and_inverse i.2
      refine ⟨⟨_, hj⟩, fun v => ?_, fun v => ?_⟩
      · show σ _ (σ i.1 v) = v
        rw [← ContinuousLinearMap.comp_apply, ← hrep.2 _ hj _ i.2, hl, hrep.1,
          ContinuousLinearMap.one_apply]
      · show σ i.1 (σ _ v) = v
        rw [← ContinuousLinearMap.comp_apply, ← hrep.2 _ i.2 _ hj, hr, hrep.1,
          ContinuousLinearMap.one_apply])
    (fun S hS hS' => hirr S hS (fun g hg v hv => hS' ⟨g, hg⟩ v hv))
    (fun i v hv => hmem i.1 i.2 v hv)
    A A' (hnorm A hAinv) (hnorm A' hA'inv) (fun i w hw => hxinv i.1 i.2 w hw w hw) hcl hcl'
  exact ⟨c, fun w hw w' hw' => by rw [← l2_inner_of_ae (hA w hw) (hA' w' hw')]; exact hc w hw w' hw'⟩

end GlobalTheory.SmVec
end

section

namespace GlobalTheory.MixedSignature

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem compact_mod_stabiliser_of_minGe :
    (∀ (r : ℕ) (X : Data E r) (G : Matrix (Fin r) (Fin r) E) (p : X.Ψ → ℕ) (_ : G.det ≠ 0) {den : 𝓞 E} (_ : den ≠ 0) (_ : ∀ x ∈ X.Λ, ∀ y ∈ X.Λ, IsIntegral ℤ ((den : E) * herm G x y)) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ Uni X G fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → ∀ x0, Orth X G p x0 → ∀ ε : ℝ, 0 < ε → ∃ K : Set H, IsCompact K ∧ ∀ g : H, MinGe X ε (X.lmulC (fun τ => (((g : H) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) → ∃ u : H, (∃ γ : GL (Fin r) E, IsUStab G X.Λ γ ∧ ∀ τ : X.Ψ, ((((u : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1) ∧ ∃ k ∈ K, g = u * k) := by
  intro r X G p hG den hden hint H hH x0 hx0 ε hε
  obtain ⟨-, -, hfr⟩ := unitary_group_frames r X p H hH
  obtain ⟨horth, ι, hιc, -, hιg⟩ := hfr x0 hx0
  obtain ⟨R, hR⟩ := exists_bound_orthonormal_frame X G p hG hden hint ε hε
  obtain ⟨Γ, hΓ⟩ := exists_stabiliser_image_subgroup r X H hH
  refine ⟨ι '' {x : Frame X.Ψ r | Orth X G p x ∧ ∀ τ a b, ‖x τ a b‖ ≤ R},
    (isCompact_orth_bounded r X G p R).image_of_continuousOn
      (hιc.mono fun x hx => hx.1), fun g hg => ?_⟩
  obtain ⟨γ, hγ, hb⟩ := hR _ (horth g) hg
  obtain ⟨u, hu⟩ := exists_unitary_elem_of_isUStab r X H hH γ hγ
  have huΓ : u ∈ Γ := (hΓ u).2 ⟨γ, hγ, hu⟩
  refine ⟨u⁻¹, (hΓ _).1 (Γ.inv_mem huΓ), u * g, ⟨_, ⟨horth (u * g), ?_⟩, hιg (u * g)⟩,
    (inv_mul_cancel_left u g).symm⟩
  have key : X.lmulC (fun τ => (((u * g : H) : X.Ψ → GL (Fin r) ℂ) τ :
      Matrix (Fin r) (Fin r) ℂ)) x0 = lact γ (X.lmulC (fun τ =>
        (((g : H) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) := by
    funext τ
    change (((u : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ) *
        ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) * mat x0 τ =
      (γ : Matrix (Fin r) (Fin r) E).map τ.1 *
        (((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ) * mat x0 τ)
    rw [hu, Matrix.mul_assoc]
  rw [key]
  exact hb

theorem exists_finite_measure_cover : (∀ (r : ℕ) (X : Data E r) (G : Matrix (Fin r) (Fin r) E) (p : X.Ψ → ℕ) (_ : G.det ≠ 0) {den : 𝓞 E} (_ : den ≠ 0) (_ : ∀ x ∈ X.Λ, ∀ y ∈ X.Λ, IsIntegral ℤ ((den : E) * herm G x y)) (x0 : Frame X.Ψ r) (_ : Orth X G p x0) (_ : ∀ τ, p τ ≤ r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ Uni X G fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → ∀ [MeasurableSpace H] [BorelSpace H] (ν : Measure H) [ν.IsHaarMeasure], ∃ Ω : Set H, MeasurableSet Ω ∧ ν Ω < ⊤ ∧ ∀ g : H, ∃ γ : GL (Fin r) E, IsUStab G X.Λ γ ∧ ∃ w ∈ Ω, ∀ τ : X.Ψ, (((g : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * (((w : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) := by
  intro r X G p hG den hden hint x0 hx0 hple H hH _ _ ν _
  obtain ⟨Γ, hΓ⟩ := exists_stabiliser_image_subgroup r X H hH
  suffices hS : ∃ Ω : Set H, MeasurableSet Ω ∧ ν Ω < ⊤ ∧ ∀ g : H, ∃ γ ∈ Γ, ∃ w ∈ Ω, g = γ * w by
    obtain ⟨Ω, h1, h2, h3⟩ := hS
    refine ⟨Ω, h1, h2, fun g => ?_⟩
    obtain ⟨u, hu, w, hw, rfl⟩ := h3 g
    obtain ⟨γ, hγ, hγu⟩ := (hΓ u).1 hu
    refine ⟨γ, hγ, w, hw, fun τ => ?_⟩
    rw [← hγu τ]
    simp
  by_cases hp : ∀ τ, p τ = 0 ∨ p τ = r
  · have : CompactSpace H := compactSpace_unitary_of_definite r X H hH hp x0 hx0
    exact ⟨Set.univ, MeasurableSet.univ, isCompact_univ.measure_lt_top,
      fun g => ⟨1, Γ.one_mem, g, Set.mem_univ _, (one_mul g).symm⟩⟩
  · obtain ⟨τ0, hp⟩ := not_forall.1 hp
    have hp0 : 0 < p τ0 := Nat.pos_of_ne_zero fun h => hp (Or.inl h)
    have hpr : p τ0 < r := lt_of_le_of_ne (hple τ0) fun h => hp (Or.inr h)
    obtain ⟨hlc, hsc, -⟩ := unitary_group_frames r X p H hH
    obtain ⟨σ, _, _, h, f, c, b, hk, hf, hf0, hinv, hc0, hc1, hb, hdrift, hsub⟩ :=
      exists_drift_function r X G p hG τ0 H hH hp0 hpr x0 hx0
    obtain ⟨U, hU, hU1⟩ := gamDisc r X H hH
    refine GlobalTheory.exists_finite_measure_cover_of_drift_function H ν Γ σ h f c b
      ⟨U, hU, fun γ hγ => hU1 γ ((hΓ γ).1 hγ)⟩ hk hf hf0
      (fun γ hγ => hinv γ ((hΓ γ).1 hγ)) hc0 hc1 hb hdrift fun M => ?_
    obtain ⟨ε, hε, hM⟩ := hsub M
    obtain ⟨K, hK, hKc⟩ := compact_mod_stabiliser_of_minGe r X G p hG hden hint H hH x0 hx0 ε hε
    refine ⟨K, hK, fun g hg => ?_⟩
    obtain ⟨u, hu, k, hk, e⟩ := hKc g (hM g hg)
    exact ⟨u, (hΓ u).2 hu, k, hk, e⟩

end


open NumberField in
theorem exists_cmType_finite_measure_cover : (∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)), (∀ a b, ReciprocityTheory.ChartRestriction.G.FD.cc (G a b) = G b a) → G.det ≠ 0 → Λ.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → ∃ Ψ : Finset (E →+* ℂ), (∀ τ : E →+* ℂ, τ ∈ Ψ ↔ NumberField.ComplexEmbedding.conjugate τ ∉ Ψ) ∧ ∀ (H : Subgroup (Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ ∀ τ : Ψ, ∀ u w : Fin r → ℂ, ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 G (Matrix.mulVec (g τ : Matrix (Fin r) (Fin r) ℂ) u) (Matrix.mulVec (g τ : Matrix (Fin r) (Fin r) ℂ) w) = ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 G u w) → ∀ [MeasurableSpace H] [BorelSpace H] (ν : MeasureTheory.Measure H) [ν.IsHaarMeasure], ∃ Ω : Set H, MeasurableSet Ω ∧ ν Ω < ⊤ ∧ ∀ g : H, ∃ γ : GL (Fin r) E, ReciprocityTheory.ChartRestriction.G.FD.IsUStab G Λ γ ∧ ∃ w ∈ Ω, ∀ τ : Ψ, (((g : Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * (((w : Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) := by
  intro E _ _ _ r G Λ hh hG hfg hsp
  obtain ⟨X, rfl⟩ := GlobalTheory.Member.LatData.exists_data_lattice E r Λ hfg hsp
  obtain ⟨den, hden, hint⟩ := GlobalTheory.HermDen.exists_den E r G X.Λ hfg
  choose p hp P _ hP using fun τ : X.Ψ => GlobalTheory.HermSignature.exists_le_gram_eq_sgn E r G hh hG τ.1
  exact ⟨X.Ψ, X.cmType, exists_finite_measure_cover r X G p hG hden hint P hP hp⟩

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

theorem finite_covolume_real_points : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (L : Submodule (𝓞 E) (Fin M → E)), L.FG → Submodule.span E (L : Set (Fin M → E)) = ⊤ → ∀ ν : Measure (HA (Ainf F) σ J), ν.IsHaarMeasure → ∃ Ω : Set (HA (Ainf F) σ J), MeasurableSet Ω ∧ ν Ω < ⊤ ∧ ∀ g : HA (Ainf F) σ J, ∃ γ ∈ Formalism.UG.UJ (σ : E →+* E) J, (∀ x, x ∈ L ↔ (γ : Matrix (Fin M) (Fin M) E).mulVec x ∈ L) ∧ ∃ w ∈ Ω, HA.mat (Ainf F) σ J g = Formalism.UG.bc (inclR (F := F) (Ainf F)) γ * HA.mat (Ainf F) σ J w :=
  GlobalTheory.Mem.CovolTransport.finite_covolume_real_points exists_cmType_finite_measure_cover

end GlobalTheory.MixedSignature
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LowSmooth

open GlobalTheory.ConjDS GlobalTheory.ConjExt Formalism.MainNotions.S

variable {D : D7} {V : HSp D}

def glue {S : D.what₂.Tau → D.what₂.Tau → SPar} (N : ∀ τ, DSModel V (S τ)) : DSModel V fun τ => S τ τ where
  H τ := (N τ).H τ
  σ τ := (N τ).σ τ
  lam τ := (N τ).lam τ
  ε τ := (N τ).ε τ
  fr τ := (N τ).fr τ
  enum τ := (N τ).enum τ
  ds τ := (N τ).ds τ
  fr_unit τ := (N τ).fr_unit τ
  fr_gram τ := (N τ).fr_gram τ

theorem dualPar_dualPar (S : SPar) : dualPar (dualPar S) = S := by
  unfold dualPar
  ext x
  simp only [Finset.mem_image]
  exact ⟨fun ⟨_, ⟨y, hy, e⟩, e'⟩ => by subst e e'; simpa using hy,
    fun hx => ⟨(-x.1, x.2), ⟨x, hx, rfl⟩, by simp⟩⟩

theorem low_of_conj {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    (h : lowKSub ((conjModel M).ε τ) ((conjModel M).lam τ) ((conjModel M).σ τ) ≤ (conjModel M).sm τ) :
    lowKSub (M.ε τ) (M.lam τ) (M.σ τ) ≤ M.sm τ := by
  intro w hw
  let c : (conjModel M).H τ ≃ₗᵢ⋆[ℂ] M.H τ := cj (M.H τ)
  have h1 := h (lowKSub_transfer (ε := M.ε τ) (ε' := (conjModel M).ε τ) (σ' := (conjModel M).σ τ) (fun _ => rfl) c
    (fun _ _ => rfl) hw)
  have h2 : ∀ y ∈ (conjModel M).sm τ, c y ∈ M.sm τ := fun y hy => by
    induction hy using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span (smoothVec_map c (conj_rep M τ) hy)
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [LinearIsometryEquiv.map_smulₛₗ]; exact Submodule.smul_mem _ _ hx
  have h3 := h2 _ h1
  simpa using h3

theorem shape_at {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) (h : HCParam D.R) {p q : ℕ}
    (hn : V.rank = D.R.r) (hpq : p + q = V.rank)
    (hS : S τ = Formalism.L2.NTheta.holPar p q (Formalism.L2.NTheta.kapW h p q)) :
    Formalism.QuantumDeterminants.IsHCParam (M.lam τ) ∧ ∃ p ≤ V.rank, ∀ a, M.ε τ a = decide ((a : ℕ) < p) := by
  have key := GlobalTheory.HolDict.isEnum_holPar_kapW h hn hpq (hS ▸ M.enum τ)
  refine ⟨⟨(M.enum τ).1, fun a => ?_⟩, p, by omega, fun a => (key a).2⟩
  obtain ⟨z, hz⟩ := Formalism.L2.NTheta.lamAt_int h a
  obtain ⟨s, hs⟩ := Formalism.L2.NTheta.odd_r D.R
  refine ⟨z - s, ?_⟩
  have hr : ((V.rank : ℕ) : ℝ) = 2 * s + 1 := by rw [hn, hs]; push_cast; rfl
  rw [(key a).1, hz, hr]
  push_cast
  ring

theorem lowSm_MW : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ i σ, LowSm (R.MW i σ) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R i σ
  have key : ∀ τ, ∃ (S : D.what₂.Tau → SPar) (N : DSModel (Wc D i) S),
      (Formalism.QuantumDeterminants.IsHCParam (N.lam τ) ∧ ∃ p ≤ (Wc D i).rank, ∀ a, N.ε τ a = decide ((a : ℕ) < p)) ∧
      (lowKSub (N.ε τ) (N.lam τ) (N.σ τ) ≤ N.sm τ →
        lowKSub ((R.MW i σ).ε τ) ((R.MW i σ).lam τ) ((R.MW i σ).σ τ) ≤ (R.MW i σ).sm τ) := fun τ => by
    have hpq := GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.pW_add_qW (D := D) i τ
    by_cases hb : labE σ (lab σ τ) = tauE D τ
    · exact ⟨_, R.MW i σ, shape_at _ τ (D.hc (lab σ τ)) (rank_Wc i) hpq (if_pos hb), id⟩
    · refine ⟨_, conjModel (R.MW i σ), shape_at _ τ (D.hc (lab σ τ)) (rank_Wc i) hpq ?_, low_of_conj _ τ⟩
      unfold Links.parAt
      rw [if_neg hb, dualPar_dualPar]
      rfl
  choose S N hN hL using key
  exact fun τ => hL τ ((GlobalTheory.HolLowOnce.lowSm_and_lowIrr D _ _ (glue N) hN).1 τ)

end GlobalTheory.LowSmooth

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.StdFrames GlobalTheory.AdIsom GlobalTheory.IdemSupport

namespace GlobalTheory.ConjLt
variable {D : D7}

theorem lt_one_le_exp {x : WithZero (Multiplicative ℤ)} (h : x < 1) : x ≤ WithZero.exp (-1) := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact zero_le'
  · obtain ⟨n, rfl⟩ := WithZero.ne_zero_iff_exists.1 hx
    have : (n : WithZero (Multiplicative ℤ)) = WithZero.exp (Multiplicative.toAdd n) := rfl
    rw [this, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [this, WithZero.exp_le_exp]
    omega

theorem cpt_sg_lt_one (Q : Pl D.host.E) (z : EAf D) (h : Valued.v (cpt Q z) < 1) :
    Valued.v (cpt (cP Q) (sg D z)) < 1 := by
  obtain ⟨π, hπ⟩ := Q.intValuation_exists_uniformizer
  set p : D.host.E := (π : D.host.E) with hp
  have hvp : Valued.v (cpt Q (GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.inc D p)) = WithZero.exp (-1) := by
    rw [cpt_inc, Formalism.UG.P.levelaf_valued_algebraMap, hp, ← hπ]
    exact Q.valuation_of_algebraMap π
  have hp0 : p ≠ 0 := by
    rintro h0
    rw [h0, map_zero, map_zero, map_zero] at hvp
    exact WithZero.exp_ne_zero hvp.symm
  set a := z * GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.inc D p⁻¹ with ha
  have hza : z = a * GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.inc D p := by
    rw [ha, mul_assoc, ← map_mul, inv_mul_cancel₀ hp0, map_one, mul_one]
  have hva : Valued.v (cpt Q a) ≤ 1 := by
    have e1 : Valued.v (cpt Q a) * WithZero.exp (-1) = Valued.v (cpt Q z) := by
      rw [← hvp, ← Valuation.map_mul, ← map_mul, ← hza]
    have e2 := lt_one_le_exp h
    rw [← e1] at e2
    by_contra hc
    push_neg at hc
    have : WithZero.exp (-1) < Valued.v (cpt Q a) * WithZero.exp (-1) := by
      calc WithZero.exp (-1) = 1 * WithZero.exp (-1) := (one_mul _).symm
        _ < _ := mul_lt_mul_of_pos_right hc (WithZero.exp_pos)
    exact absurd e2 (not_le.2 this)
  have h1 := (cpt_cjA_le_iff Q a).2 hva
  have hs : sg D z = GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.cjA D a * GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.inc D (star p) := by
    rw [hza, map_mul]; rfl
  have h2 : Valued.v (cpt (cP Q) (GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.inc D (star p))) < 1 := by
    rw [cpt_inc, Formalism.UG.P.levelaf_valued_algebraMap]
    have e : star p = ((cO D π : 𝓞 D.host.E) : D.host.E) := rfl
    rw [e, (cP Q).valuation_lt_one_iff_mem, mem_cP, cO_cO, ← Q.intValuation_lt_one_iff_mem, hπ]
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  rw [hs, map_mul, Valuation.map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_left' h1) h2

theorem conj_sub_one {A : Type} [CommRing A] (σ : A →+* A) {n : ℕ} (β x : GL (Fin n) A)
    (R U' : Matrix (Fin n) (Fin n) A) (hX : Formalism.UG.cT σ x.val * R * x.val = R)
    (hU : U' * (Formalism.UG.cT σ β.val * R * β.val) = 1) :
    (β⁻¹ * x * β).val - 1 = U' * (Formalism.UG.cT σ (β⁻¹ * x⁻¹ * β).val - 1) * (Formalism.UG.cT σ β.val * R * β.val) := by
  set G := Formalism.UG.cT σ β.val * R * β.val with hG
  set Y := (β⁻¹ * x * β).val with hYdef
  set Yi := (β⁻¹ * x⁻¹ * β).val with hYidef
  have hYYi : Y * Yi = 1 := by
    rw [hYdef, hYidef, ← Units.val_mul]
    rw [show β⁻¹ * x * β * (β⁻¹ * x⁻¹ * β) = 1 by group, Units.val_one]
  have hY : Y = (β⁻¹).val * x.val * β.val := by rw [hYdef, Units.val_mul, Units.val_mul]
  have c1 : ∀ Z : Matrix (Fin n) (Fin n) A, Formalism.UG.cT σ (β⁻¹).val * (Formalism.UG.cT σ β.val * Z) = Z := by
    intro Z
    rw [← Matrix.mul_assoc, ← cT_mul', Units.mul_inv, cT_one', Matrix.one_mul]
  have c2 : ∀ Z : Matrix (Fin n) (Fin n) A, β.val * ((β⁻¹).val * Z) = Z := by
    intro Z
    rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  have hUY : Formalism.UG.cT σ Y * G * Y = G := by
    rw [hY, hG, cT_mul', cT_mul']
    simp only [Matrix.mul_assoc, c1, c2]
    rw [show Formalism.UG.cT σ x.val * (R * (x.val * β.val)) = (Formalism.UG.cT σ x.val * R * x.val) * β.val by
        simp only [Matrix.mul_assoc], hX]
  have hGY : G * Y = Formalism.UG.cT σ Yi * G := by
    have := congrArg (fun Z => Formalism.UG.cT σ Yi * Z) hUY
    rw [← this, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← cT_mul', hYYi, cT_one', Matrix.one_mul]
  have e1 : Y = U' * (G * Y) := by rw [← Matrix.mul_assoc, hU, Matrix.one_mul]
  calc Y - 1 = U' * (G * Y) - U' * G := by rw [← e1, hU]
    _ = U' * (Formalism.UG.cT σ Yi * G) - U' * G := by rw [hGY]
    _ = U' * (Formalism.UG.cT σ Yi - 1) * G := by
      rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.mul_assoc]

theorem frame_mat_sub_one_lt : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsSDFrame V β Λ N → ∀ (g : GA D V) (Q : Formalism.L2.DIV.Pl D.host.E), (∀ a b : Fin V.rank, Valued.v (GlobalTheory.StdFrames.cpt Q ((β⁻¹ * (finE V g)⁻¹ * β).val a b - (1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) a b)) < 1) → ∀ a b : Fin V.rank, Valued.v (GlobalTheory.StdFrames.cpt (GlobalTheory.IdemSupport.cP Q) ((β⁻¹ * finE V g * β).val a b - (1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) a b)) < 1 := by
  intro D V β Λ N hSD g Q h a b
  obtain ⟨hGi, U', hU'i, hU'⟩ := unimod_of_isSD hSD
  have hX : Formalism.UG.cT (sg D) (finE V g).val * GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices.ratM V.gram * (finE V g).val =
      GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices.ratM V.gram := GlobalTheory.LevSplit.finE_mem_UA V g
  have hYsub := conj_sub_one (sg D) β (finE V g) _ U' hX hU'
  have hM : ∀ i j, Valued.v (cpt (cP Q) ((Formalism.UG.cT (sg D) (β⁻¹ * (finE V g)⁻¹ * β).val - 1) i j)) < 1 := by
    intro i j
    have e : (Formalism.UG.cT (sg D) (β⁻¹ * (finE V g)⁻¹ * β).val - 1) i j =
        sg D ((β⁻¹ * (finE V g)⁻¹ * β).val j i - (1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) j i) := by
      simp only [Formalism.UG.cT, Matrix.sub_apply, Matrix.transpose_apply, Matrix.map_apply, map_sub, Matrix.one_apply]
      by_cases hij : i = j
      · subst hij; simp
      · rw [if_neg hij, if_neg (Ne.symm hij), map_zero]
    rw [e]
    exact cpt_sg_lt_one Q _ (h j i)
  have hint : ∀ x ∈ GlobalTheory.StdFrames.OA D, Valued.v (cpt (cP Q) x) ≤ 1 := fun x hx => (mem_OA x).1 hx (cP Q)

  rw [← Matrix.sub_apply, hYsub, Matrix.mul_apply, map_sum]
  refine Valuation.map_sum_lt' _ zero_lt_one fun j _ => ?_

  rw [map_mul, Valuation.map_mul, Matrix.mul_apply, map_sum]
  refine lt_of_le_of_lt (mul_le_of_le_one_right' (hint _ (hGi j b))) ?_
  refine Valuation.map_sum_lt' _ zero_lt_one fun i _ => ?_
  rw [map_mul, Valuation.map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint _ (hU'i a i))) (hM i j)

end GlobalTheory.ConjLt
end
