module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle013
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle577
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle495
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle017
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle594
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle452
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.OrthonormalBaseFrameNeg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1546
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle534
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle077
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingSecond
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle578
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle583
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LayerDdRBounds
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle580
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle126
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle581
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle579
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.finiteInertiaImpliesPotSemistable_proof : UnrStep := by
  first | exact @GlobalTheory.PMon.unrStep_holds | exact GlobalTheory.PMon.unrStep_holds | (intros; apply GlobalTheory.PMon.unrStep_holds <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.deRham_iff_framed_galois_representation : FrameEx := by
  first | exact @GlobalTheory.PMon.FrameEquiv.frameEx | exact GlobalTheory.PMon.FrameEquiv.frameEx | (intros; apply GlobalTheory.PMon.FrameEquiv.frameEx <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors

theorem _root_.GlobalTheory.T.idelicAbsDetPow_diagonalUniformizer_mul : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ)
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) (x : ℝ) (g : GA E n),
    GlobalTheory.RSJ.detPow E n x (GlobalTheory.CellDec.tl n ϖ l * g) =
      (∏ w ∈ l.support, (qV E w : ℝ) ^ (-x * ∑ i, (l w i : ℝ))) * GlobalTheory.RSJ.detPow E n x g := by
  first | exact @GlobalTheory.CellEvalDet.detPow_tl_mul | exact GlobalTheory.CellEvalDet.detPow_tl_mul | (intros; apply GlobalTheory.CellEvalDet.detPow_tl_mul <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.DesignUnconditional

theorem main : ∀ D : D7, GlobalTheory.CoefDuty.TakenAll D → Formalism.MainNotions.N.K.Rows.AllDesignConditions D :=
  GlobalTheory.T.designConditionAll_of_cheb_of_takenAll (GlobalTheory.Published.chebotarevDegreeOne_iff_cheb.mp GlobalTheory.Published.chebotarevDegreeOne')

end GlobalTheory.DesignUnconditional
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.CoverFrameArith

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem arch_rat {D : D7} (V : HSp D) {r : ℕ} (hr : V.rank = r) (ρ : GA D V) (hρ : ρ ∈ GQ V) :
    ∃ R : GL (Fin r) D.host.E, ∀ (τ : D.host.E →+* ℂ) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ),
      Formalism.MainNotions.StandardLattice.IsInfEmb τ θ → ∀ u : GA D V,
        Matrix.reindex (finCongr hr) (finCongr hr) (archM V θ (ρ * u)) =
          (R : Matrix (Fin r) (Fin r) D.host.E).map τ * Matrix.reindex (finCongr hr) (finCongr hr) (archM V θ u) := by
  subst hr
  obtain ⟨R, -, -, hRa⟩ := GlobalTheory.MarkCoset.rational_matrix V ρ hρ
  have hre : ∀ m : Matrix (Fin V.rank) (Fin V.rank) ℂ,
      Matrix.reindex (finCongr (rfl : V.rank = V.rank)) (finCongr rfl) m = m := fun m => by
    ext i j
    rfl
  refine ⟨R, fun τ θ hθ u => ?_⟩
  rw [hre, hre, archM, archM, map_mul, Units.val_mul, Matrix.map_mul, ← archM, hRa τ θ hθ]

theorem mulVec_add_nsmul {A : Type} [CommRing A] {n : ℕ} (m : Matrix (Fin n) (Fin n) A) (N : ℕ) (y y' : Fin n → A) :
    m *ᵥ (y + N • y') = m *ᵥ y + N • (m *ᵥ y') := by
  rw [Matrix.mulVec_add, Matrix.mulVec_smul]



theorem conj_move {D : D7} (V : HSp D) {r : ℕ} (hr : V.rank = r) (δa g₀ κ : GA D V) (hδ : δa ∈ GQ V) (N : ℕ)
    (hN : N ≠ 0) (hκ : ∀ z ∈ latHat V, ∃ y ∈ latHat V, (finHom V κ).1.mulVec z - z = N • y)
    (hκ' : ∀ z ∈ latHat V, ∃ y ∈ latHat V, (finHom V κ⁻¹).1.mulVec z - z = N • y)
    (he : finHom V (g₀⁻¹ * δa * g₀) = finHom V κ) (L : Submodule (𝓞 D.host.E) (Fin r → D.host.E))
    (hL : (L : Set (Fin r → D.host.E)) =
      (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast hr.symm) '' (latG V g₀ : Set _))
    (G : Matrix (Fin r) (Fin r) D.host.E) (hG : G = -(Matrix.reindex (finCongr hr) (finCongr hr) V.gram).transpose) :
    ∃ Δ : GL (Fin r) D.host.E,
      (∀ v w, herm G ((Δ : Matrix (Fin r) (Fin r) D.host.E) *ᵥ v) ((Δ : Matrix (Fin r) (Fin r) D.host.E) *ᵥ w) =
        herm G v w) ∧
      (∀ v, v ∈ L ↔ (Δ : Matrix (Fin r) (Fin r) D.host.E) *ᵥ v ∈ L) ∧
      (∀ v ∈ L, ∃ u ∈ L, (Δ : Matrix (Fin r) (Fin r) D.host.E) *ᵥ v = v + N • u) ∧
      ∀ (τ : D.host.E →+* ℂ) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ), Formalism.MainNotions.StandardLattice.IsInfEmb τ θ →
        ∀ u : GA D V, Matrix.reindex (finCongr hr) (finCongr hr) (archM V θ (δa * u)) =
          (Δ : Matrix (Fin r) (Fin r) D.host.E).map τ * Matrix.reindex (finCongr hr) (finCongr hr) (archM V θ u) := by
  subst hr
  have hgr : Matrix.reindex (finCongr (rfl : V.rank = V.rank)) (finCongr rfl) V.gram = V.gram := by
    ext i j
    rfl
  have hre : ∀ m : Matrix (Fin V.rank) (Fin V.rank) ℂ,
      Matrix.reindex (finCongr (rfl : V.rank = V.rank)) (finCongr rfl) m = m := fun m => by
    ext i j
    rfl
  rw [hgr] at hG
  obtain ⟨Δ, hΔu, hΔf, hΔa⟩ := GlobalTheory.MarkCoset.rational_matrix V δa hδ
  have hmem : ∀ v, v ∈ L ↔ finVec V v ∈ latGHat V g₀ := fun v => by
    rw [← (GlobalTheory.MarkCoset.latG_spec D V _).1, ← SetLike.mem_coe, hL]
    exact Set.ext_iff.1 (Set.image_id _) v
  have hfh : finHom V (δa * g₀ * κ⁻¹) = finHom V g₀ := by
    have e : δa * g₀ * κ⁻¹ = g₀ * (g₀⁻¹ * δa * g₀) * κ⁻¹ := by group
    rw [e, map_mul, map_mul, he, map_inv, mul_inv_cancel_right]
  have hLh : latGHat V (δa * g₀ * κ⁻¹) = latGHat V g₀ := by
    unfold latGHat gLat
    rw [hfh]
  obtain ⟨ht1, -⟩ := GlobalTheory.MarkCoset.transport (finHom V) (latGHat V) (fun g => (GlobalTheory.MarkCoset.latG_spec D V g).2) N
    δa g₀ κ⁻¹ (GlobalTheory.MarkCoset.level_latGHat V N κ⁻¹ hκ')
    (by rw [inv_inv]; exact GlobalTheory.MarkCoset.level_latGHat V N κ hκ)
  rw [hLh] at ht1
  refine ⟨Δ, fun v w => by rw [hG]; exact hΔu v w, fun v => by rw [hmem, hmem, ← hΔf]; exact ht1 _,
    fun v hv => ?_, fun τ θ hθ u => ?_⟩
  · obtain ⟨y, hy, hyz⟩ := ((GlobalTheory.MarkCoset.latG_spec D V g₀).2 _).1 ((hmem v).1 hv)
    obtain ⟨y', hy', ey⟩ := GlobalTheory.MarkCoset.level_latGHat V N κ hκ y hy
    have hc : (finHom V δa).1 *ᵥ ((finHom V g₀).1 *ᵥ y) = (finHom V g₀).1 *ᵥ ((finHom V κ).1 *ᵥ y) := by
      rw [← he, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul,
        show g₀ * (g₀⁻¹ * δa * g₀) = δa * g₀ by group]
    have hs : finVec V ((Δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v - v) =
        finVec V ((Δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v) - finVec V v := by
      funext i
      simp only [finVec, Pi.sub_apply, TensorProduct.tmul_sub]
    have key : finVec V ((Δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v - v) =
        N • ((finHom V g₀).1 *ᵥ y') := by
      rw [hs, ← hΔf, ← hyz, hc, ey, mulVec_add_nsmul, add_sub_cancel_left]
    obtain ⟨w, hw, e⟩ := GlobalTheory.MarkCoset.finVec_div V N hN _ _ key
    refine ⟨w, (hmem w).2 ?_, sub_eq_iff_eq_add'.1 e⟩
    rw [hw]
    exact ((GlobalTheory.MarkCoset.latG_spec D V g₀).2 _).2 ⟨y', hy', rfl⟩
  · rw [hre, hre, archM, archM, map_mul, Units.val_mul, Matrix.map_mul, ← archM, hΔa τ θ hθ]



theorem frame_move_arith : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ (h h₀ : GA D (T.V j σ)), (C.dict₂ h).1 = (C.dict₂ h₀).1 → ∀ γ₀ : GL (Fin D.R.r) D.host.E, (((T.U j σ).X (T.dict j σ h₀).1).Λ : Set (Fin D.R.r → D.host.E)) = (γ₀ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec '' ((C.U₂.X (C.dict₂ h₀).1).Λ : Set _) → (∀ v w, herm ((T.U j σ).X (T.dict j σ h₀).1).Gm ((γ₀ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((γ₀ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm (C.U₂.X (C.dict₂ h₀).1).Gm v w) → (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X (C.dict₂ h₀).1).Ψ) (h₁ : τ ∈ ((T.U j σ).X (T.dict j σ h₀).1).Ψ), mat (T.dict j σ h₀).2 ⟨τ, h₁⟩ = (γ₀ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat (C.dict₂ h₀).2 ⟨τ, h₂⟩) → ∃ δ ∈ ((T.U j σ).X (T.dict j σ h).1).Γ, ∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X (C.dict₂ h).1).Ψ) (h₁ : τ ∈ ((T.U j σ).X (T.dict j σ h).1).Ψ), mat (T.dict j σ h).2 ⟨τ, h₁⟩ = (δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * ((γ₀ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat (C.dict₂ h).2 ⟨τ, h₂⟩) := by
  intro D T hT j hj σ hσ C hC h h₀ hh γ₀ _ _ hfr0
  have hk : (T.dict j σ h).1 = (T.dict j σ h₀).1 :=
    GlobalTheory.CoverRead.CompIndep.comp_eq_of_cover D T hT j hj σ hσ C hC h h₀ hh
  obtain ⟨hr₁, g₁, e₁, F₁, ik₁, φ₁, th₁, hι, -, hth₁, -, hd₁⟩ := hT.adPin j hj σ hσ
  obtain ⟨⟨-, hMl, -, hIl, -⟩, -, -, hU₂, hdom, hr₂, g₂, e₂, F₂, ik₂, φ₂, th₂, -, hth₂, -, hd₂⟩ := hC
  obtain ⟨hr₀, hW₁⟩ := hT.modelW j hj σ hσ
  have hU₁ := hT.unf j hj σ hσ
  have hK := hT.levelK j hj σ hσ
  rw [← hT.pins.2.1.1] at hK
  obtain ⟨γ₁, hγ₁, hL₁, hm₁, hf₁⟩ := hd₁ h
  obtain ⟨γ₁', hγ₁', hL₁', hm₁', hf₁'⟩ := hd₁ h₀
  obtain ⟨γ₂, hγ₂, hL₂, hm₂, hf₂⟩ := hd₂ h
  obtain ⟨γ₂', hγ₂', hL₂', hm₂', hf₂'⟩ := hd₂ h₀

  obtain ⟨M₀, hM₀⟩ := arch_rat (T.V j σ) hr₁ (γ₁' * γ₂'⁻¹) (mul_mem hγ₁' (inv_mem hγ₂'))
  have hΨ : ∀ (g : GA D (T.V j σ)) τ, τ ∈ ((T.U j σ).X (T.dict j σ g).1).Ψ ↔ τ ∈ (C.U₂.X (C.dict₂ g).1).Ψ :=
    fun g τ => ((hU₁.2.1 _).2 τ).trans ((hU₂.2.1 _).2 τ).symm
  have hM0eq : (M₀ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) = γ₀ := by
    obtain ⟨τ, t₂⟩ : ∃ τ, τ ∈ (C.U₂.X (C.dict₂ h₀).1).Ψ := by
      by_cases h0 : D.host.φ₀ ∈ (C.U₂.X (C.dict₂ h₀).1).Ψ
      · exact ⟨_, h0⟩
      · exact ⟨_, not_not.1 (mt ((C.U₂.X (C.dict₂ h₀).1).cmType _).2 h0)⟩
    have t₁ := (hΨ h₀ τ).2 t₂
    have a₁ := hf₁' ⟨τ, t₁⟩
    have a₂ := hf₂' ⟨τ, t₂⟩
    rw [GlobalTheory.LettersCheck.isInfEmb_unique τ _ _ (hth₂ _ ⟨τ, t₂⟩) (hth₁ _ ⟨τ, t₁⟩)] at a₂
    have e : γ₁' * h₀ = γ₁' * γ₂'⁻¹ * (γ₂' * h₀) := by group
    rw [e, hM₀ τ _ (hth₁ _ ⟨τ, t₁⟩), Matrix.mul_assoc, ← a₂] at a₁
    have a₃ := (hfr0 τ t₂ t₁).symm.trans a₁
    have hu : IsUnit (mat (C.dict₂ h₀).2 ⟨τ, t₂⟩) :=
      (Matrix.isUnit_iff_isUnit_det _).2 (Ne.isUnit (hdom h₀ ⟨τ, t₂⟩).1)
    exact (Matrix.map_injective τ.injective (hu.mul_right_cancel a₃)).symm

  rw [← hk] at hL₁' hm₁'
  rw [← hh] at hL₂' hm₂'
  have hinj : ∀ hr : (T.V j σ).rank = D.R.r,
      Function.Injective (fun v : Fin (T.V j σ).rank → D.host.E => v ∘ Fin.cast hr.symm) := fun hr u v huv =>
    funext fun i => congrFun huv (Fin.cast hr i)
  have hLb : latG (T.V j σ) (γ₁' * h₀) = latG (T.V j σ) (γ₁ * h) :=
    SetLike.coe_injective ((hinj hr₁).image_injective (hL₁'.symm.trans hL₁))
  have hLc : latG (T.V j σ) (γ₂ * h) = latG (T.V j σ) (γ₂' * h₀) :=
    SetLike.coe_injective ((hinj hr₂).image_injective (hL₂.symm.trans hL₂'))

  obtain ⟨a₁, ha₁, k₁, hk₁, eak₁⟩ := (GlobalTheory.UnitarySplit.real_finite_split D (T.V j σ)).1 ((γ₁' * h₀)⁻¹ * (γ₁ * h))
  obtain ⟨a₂, ha₂, k₂, hk₂, eak₂⟩ := (GlobalTheory.UnitarySplit.real_finite_split D (T.V j σ)).1 ((γ₂ * h)⁻¹ * (γ₂' * h₀))
  have hk₁K : k₁ ∈ T.Kf j σ := by
    refine (hT.kfHalf j hj σ hσ k₁).2 ⟨hk₁, ?_⟩
    have hmA := hm₁'
    have hmB := hm₁
    rw [show (T.Q.l.M : ℕ) = T.Q.l.M * 1 from (mul_one _).symm] at hmA hmB
    exact GlobalTheory.CoverRead.CompIndep.congr_of_marked (T.V j σ) _ hι _ _ one_ne_zero _ _
      (fun b hb => by rwa [Nat.cast_one, one_mul]) (γ₁' * h₀) (γ₁ * h) k₁
      (by rw [eak₁, map_mul, show finHom (T.V j σ) a₁ = 1 from ha₁, one_mul]) hLb _ hmA hmB
  have hp : C.d.pd ≠ 0 := fun h0 => by
    have := C.d.l₂.three_le
    rw [hMl, h0] at this
    omega
  have hk₂K : k₂ ∈ T.Kf j σ := by
    refine (hT.kfHalf j hj σ hσ k₂).2 ⟨hk₂, ?_⟩
    have hmA := hm₂
    have hmB := hm₂'
    rw [hMl] at hmA hmB
    exact GlobalTheory.CoverRead.CompIndep.congr_of_marked (T.V j σ) _ hι _ _ hp _ _
      (GlobalTheory.CoverRead.CompIndep.ratio_mul_mem T.Q.l C.d.l₂ _ _ hMl hIl) (γ₂ * h) (γ₂' * h₀) k₂
      (by rw [eak₂, map_mul, show finHom (T.V j σ) a₂ = 1 from ha₂, one_mul]) hLc _ hmA hmB
  have hκK : k₁ * k₂ ∈ T.Kf j σ := mul_mem hk₁K hk₂K
  have he : finHom (T.V j σ) ((γ₁' * h₀)⁻¹ * (γ₁ * γ₂⁻¹ * γ₂' * γ₁'⁻¹) * (γ₁' * h₀)) =
      finHom (T.V j σ) (k₁ * k₂) := by
    have e : (γ₁' * h₀)⁻¹ * (γ₁ * γ₂⁻¹ * γ₂' * γ₁'⁻¹) * (γ₁' * h₀) =
        ((γ₁' * h₀)⁻¹ * (γ₁ * h)) * ((γ₂ * h)⁻¹ * (γ₂' * h₀)) := by group
    rw [e, map_mul, eak₁, eak₂, map_mul, map_mul, show finHom (T.V j σ) a₁ = 1 from ha₁,
      show finHom (T.V j σ) a₂ = 1 from ha₂, one_mul, one_mul, map_mul]
  have hM0' : T.Q.l.M ≠ 0 := by
    have := T.Q.l.three_le
    omega
  have hδa : γ₁ * γ₂⁻¹ * γ₂' * γ₁'⁻¹ ∈ GQ (T.V j σ) :=
    mul_mem (mul_mem (mul_mem hγ₁ (inv_mem hγ₂)) hγ₂') (inv_mem hγ₁')
  obtain ⟨Δ, hΔi, hΔl, hΔc, hΔa⟩ := conj_move (T.V j σ) hr₁ _ (γ₁' * h₀) (k₁ * k₂) hδa T.Q.l.M hM0'
    ((hK _).1 hκK).2 ((hK _).1 (inv_mem hκK)).2 he _ hL₁' _ (hW₁ (T.dict j σ h).1).1
  refine ⟨Δ, GlobalTheory.PrincCore.mem_group_of_congruent D T.toCore hT.toLawsM j hj σ hσ _ Δ ⟨hΔi, hΔl⟩ hΔc,
    fun τ t₂ t₁ => ?_⟩
  have a₁ := hf₁ ⟨τ, t₁⟩
  have a₂ := hf₂ ⟨τ, t₂⟩
  rw [GlobalTheory.LettersCheck.isInfEmb_unique τ _ _ (hth₂ _ ⟨τ, t₂⟩) (hth₁ _ ⟨τ, t₁⟩)] at a₂
  have e : γ₁ * h = (γ₁ * γ₂⁻¹ * γ₂' * γ₁'⁻¹) * ((γ₁' * γ₂'⁻¹) * (γ₂ * h)) := by group
  rw [a₁, e, hΔa τ _ (hth₁ _ ⟨τ, t₁⟩), hM₀ τ _ (hth₁ _ ⟨τ, t₁⟩), Matrix.mul_assoc, Matrix.mul_assoc, ← a₂, hM0eq]

end GlobalTheory.CoverFrameArith
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.isSemistable_latticeInMatrixAlgebraLayer : ∀ (l : ℕ) [Fact l.Prime] (K L₀ : FinExt l) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (a : ℕ) (Cl : Set (↥(GK K) →* GL (Fin a) (Om l))) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (Ly : Layer L₀ Cl ρ), ((∀ ρ₁ ∈ Cl, ∀ (L : FinExt l) (r' : ↥(GK K) →* GL (Fin a) ↥L.1) (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1)), L₀.1 ≤ L.1 → (∀ g v, R g v = (r' g).val *ᵥ v) → (∀ g i j, (((r' g).val i j : ↥L.1) : Om l) = (ρ₁ g).val i j) → IsSst P R) → IsSst P (qRep ρ)) ∧ ((∀ ρ₁ ∈ Cl, (∀ (L : FinExt l) (r' : ↥(GK K) →* GL (Fin a) ↥L.1) (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1)), L₀.1 ≤ L.1 → (∀ g v, R g v = (r' g).val *ᵥ v) → (∀ g i j, (((r' g).val i j : ↥L.1) : Om l) = (ρ₁ g).val i j) → IsCrys (P.PD K) R)) → IsCrys (P.PD K) (qRep ρ)) := by
  first | exact @GlobalTheory.LayerSst.main | exact GlobalTheory.LayerSst.main | (intros; apply GlobalTheory.LayerSst.main <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.layer_DdR_bounds_alt : ∀ (l : ℕ) [Fact l.Prime] (K L₀ : FinExt l) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (a : ℕ) (Cl : Set (↥(GK K) →* GL (Fin a) (Om l))) (J : (↥K.1 →ₐ[ℚ_[l]] Om l) → Multiset ℤ) (N : ℕ), (∀ (τ : ↥K.1 →ₐ[ℚ_[l]] Om l) (x : ↥K.1), τ x ∈ L₀.1) → (∀ τ, ∀ n ∈ J τ, |n| ≤ N) → ∀ (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (Ly : Layer L₀ Cl ρ), (∀ ρ₁ ∈ Cl, (∀ (L : FinExt l) (r' : ↥(GK K) →* GL (Fin a) ↥L.1) (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1)), L₀.1 ≤ L.1 → (∀ g v, R g v = (r' g).val *ᵥ v) → (∀ g i j, (((r' g).val i j : ↥L.1) : Om l) = (ρ₁ g).val i j) → IsSst P R ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥L.1) (n : ℤ), multV (P.PD K) R τ n = ((J (L.1.val.comp τ)).count n : ℤ))) → (DdR (P.PD K) (qRep ρ) ≤ FilV (P.PD K) (LL := ℚ_[l]) (V := Fin d → ℚ_[l]) (-(N : ℤ)) ∧ DdR (P.PD K) (qRep ρ) ⊓ FilV (P.PD K) (LL := ℚ_[l]) (V := Fin d → ℚ_[l]) ((N : ℤ) + 1) = ⊥) := by
  first | exact @GlobalTheory.LayerJumps.layer_DdR_bounds | exact GlobalTheory.LayerJumps.layer_DdR_bounds | (intros; apply GlobalTheory.LayerJumps.layer_DdR_bounds <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.InvRatio

theorem fixed_of_inv {A : Type} [CommRing A] {d : ℕ} (σ : A →+* A) (R Q Q' c : Matrix (Fin d) (Fin d) A)
    (hQu : IsUnit Q) (hc : Q * c = Q') (h1 : R * Q.map σ = Q) (h2 : R * Q'.map σ = Q') : c.map σ = c := by
  have e : Q'.map σ = Q.map σ * c.map σ := by rw [← hc, Matrix.map_mul]
  have : Q * c.map σ = Q * c := by
    rw [hc, ← h1, Matrix.mul_assoc, ← e, h2]
  exact hQu.mul_left_cancel this

end GlobalTheory.BKLim.InvRatio


open GlobalTheory.BKLim.InvRatio in
theorem GlobalTheory.BKLim.invMatrix_ratio : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l), C.InvdR → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (Q : Matrix (Fin d) (Fin d) (Per.BdR l)), IsUnit Q → (∀ g : ↥(GK K), (ρ g).map (Per.zD l) * Q.map (Per.σD (g : GQ l)) = Q) → ∀ H : Hodge C (bk.ev bk.E) (fun g => (ρ g).map (zOm l)) K, ∃ c c' : Matrix (Fin d) (Fin d) (Om l), (∀ i j, c i j ∈ K.1) ∧ (∀ i j, c' i j ∈ K.1) ∧ c * c' = 1 ∧ H.Q = Q * c.map C.oD := by
  intro l _ K bk C hI d ρ Q hQu hQ H
  obtain ⟨-, hinj, hF, -⟩ := BdRField.bdR_isField l
  obtain ⟨u, hu, -⟩ := AdaptedHodge.xi_unit_fil C (bk.ev bk.E) bk.span_ev
  set ι := algebraMap (Per.BdRp l) (Per.BdR l) with hι

  have hz : ∀ z : ℤ_[l], ι (C.o (zOm l z)) = Per.zD l z := by
    intro z
    simp only [zOm, RingHom.comp_apply, hι]
    exact (congrArg ι (C.o_sec.z z)).trans (GlobalTheory.RingIface.zD_eq_alg l z).symm
  have hHinv : ∀ g : ↥(GK K), (ρ g).map (Per.zD l) * H.Q.map (Per.σD (g : GQ l)) = H.Q := by
    intro g
    have h := H.inv g g.2
    have e : ((ρ g).map (zOm l)).map (ι.comp C.o) = (ρ g).map (Per.zD l) := by
      ext i j; simp [hz]
    rwa [e] at h

  set dg : Fin d → Per.BdR l := fun k => ((u⁻¹ ^ H.q : (Per.BdR l)ˣ) : Per.BdR l) * (u : Per.BdR l) ^ H.p k with hdg
  have hQH : H.Q = H.V.map ι * Matrix.diagonal dg := by
    ext i k
    rw [Matrix.mul_diagonal, Matrix.map_apply]
    have h := H.Q_eq i k
    rw [map_mul, map_pow, ← hι, ← hu] at h
    calc H.Q i k = ((u⁻¹ ^ H.q : (Per.BdR l)ˣ) : Per.BdR l) * ((u : Per.BdR l) ^ H.q * H.Q i k) := by
          rw [← mul_assoc, ← Units.val_pow_eq_pow_val, ← Units.val_mul, inv_pow, inv_mul_cancel, Units.val_one, one_mul]
      _ = ι (H.V i k) * dg k := by rw [h, hdg]; ring
  have hHu : IsUnit H.Q := by
    rw [hQH]
    refine IsUnit.mul ?_ ?_
    · exact H.unit.map (ι.mapMatrix)
    · rw [Matrix.isUnit_diagonal, Pi.isUnit_iff]
      intro k
      exact (Units.isUnit _).mul ((Units.isUnit u).pow _)

  obtain ⟨Qi, hQi⟩ : ∃ Qi, Q * Qi = 1 := ⟨_, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hQu)⟩
  obtain ⟨Hi, hHi⟩ : ∃ Hi, H.Q * Hi = 1 := ⟨_, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hHu)⟩
  set c₀ := Qi * H.Q with hc₀
  set c₀' := Hi * Q with hc₀'
  have e0 : Q * c₀ = H.Q := by rw [hc₀, ← Matrix.mul_assoc, hQi, Matrix.one_mul]
  have e0' : H.Q * c₀' = Q := by rw [hc₀', ← Matrix.mul_assoc, hHi, Matrix.one_mul]
  have fix0 : ∀ g ∈ GK K, ∀ i j, Per.σD g (c₀ i j) = c₀ i j := by
    intro g hg i j
    have := fixed_of_inv (Per.σD g) _ Q H.Q c₀ hQu e0 (hQ ⟨g, hg⟩) (hHinv ⟨g, hg⟩)
    exact congrFun (congrFun this i) j
  have fix0' : ∀ g ∈ GK K, ∀ i j, Per.σD g (c₀' i j) = c₀' i j := by
    intro g hg i j
    have := fixed_of_inv (Per.σD g) _ H.Q Q c₀' hHu e0' (hHinv ⟨g, hg⟩) (hQ ⟨g, hg⟩)
    exact congrFun (congrFun this i) j
  choose x hxK hx using fun i j => hI K (c₀ i j) (fun g hg => fix0 g hg i j)
  choose x' hxK' hx' using fun i j => hI K (c₀' i j) (fun g hg => fix0' g hg i j)
  haveI : Nontrivial (Per.BdR l) := hF.nontrivial
  have hoinj : Function.Injective C.oD := C.oD.injective
  have hm : (Matrix.of x).map C.oD = c₀ := by ext i j; simp [hx]
  have hm' : (Matrix.of x').map C.oD = c₀' := by ext i j; simp [hx']
  refine ⟨Matrix.of x, Matrix.of x', hxK, hxK', ?_, ?_⟩
  · have h1 : c₀ * c₀' = 1 := by
      rw [hc₀, hc₀', Matrix.mul_assoc, ← Matrix.mul_assoc H.Q, hHi, Matrix.one_mul]
      exact mul_eq_one_comm.1 hQi
    have h2 : (Matrix.of x * Matrix.of x').map C.oD = (1 : Matrix (Fin d) (Fin d) (Om l)).map C.oD := by
      rw [Matrix.map_mul, hm, hm', h1, Matrix.map_one _ (map_zero _) (map_one _)]
    ext i j
    exact hoinj (congrFun (congrFun h2 i) j)
  · rw [hm, e0]

end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.hodge_structure_of_adapted_invariant_family : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (ξ : Ainf l), Ideal.span {ξ} = RingHom.ker (Per.θ l) → ∀ (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (x : Fin d → Fin d → P.R.BdR) (h : Fin d → ℤ), (∀ j (g : ↥(GK K)), (ρ g).val.map (fun z : ℤ_[l] => algebraMap ℚ_[l] P.R.BdR (z : ℚ_[l])) *ᵥ (fun i => P.actQdR (g : GQ l) (x j i)) = x j) → (∀ j i, x j i ∈ (P.PD K).Fil (h j)) → (∀ y : Fin d → P.R.BdR, (∀ i, y i ∈ (P.PD K).Fil 0) → ∃ c : Fin d → P.R.BdR, (∀ j, c j ∈ (P.PD K).Fil (-h j)) ∧ y = ∑ j, c j • x j) → ∃ H : Hodge C ξ (fun g => (ρ g).val.map (zOm l)) K, ∀ i, (H.p i : ℤ) - H.q = h i := by
  first | (exact @GlobalTheory.BKLim.hodge_of_adapted) | (exact GlobalTheory.BKLim.hodge_of_adapted) | (intros; apply GlobalTheory.BKLim.hodge_of_adapted  <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.isHodgeTate_iff_diagonal_adapted_basis : ∀ (l : ℕ) [Fact l.Prime] (K K' : FinExt l) (C : Core l), C.InvdR → ∀ (ξ : Ainf l), Ideal.span {ξ} = RingHom.ker (Per.θ l) → ∀ (a : ℕ) (ρ : ↥(GK K) → Matrix (Fin a) (Fin a) (Om l)) (H : Hodge C ξ ρ K') (z : ℂ_[l]) (u : Matrix (Fin a) (Fin a) (ℂ_[l])), K.1 ≤ K'.1 → (u * H.V.map (Per.θD l) = H.V.map (Per.θD l) * Matrix.diagonal (fun i => z ^ ((H.p i : ℤ) - H.q)) ↔ IsHT C ξ ρ z u) := by
  first | exact @GlobalTheory.BKLim.isHT_iff_diag | exact GlobalTheory.BKLim.isHT_iff_diag | (intros; apply GlobalTheory.BKLim.isHT_iff_diag; all_goals assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.isStablePrismHom_comp : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B C D : Obj l R) (h : Hom B C) (h₂ : Hom C D), Stable h → Stable h₂ → Stable (h₂.comp h) := by
  first | exact @GlobalTheory.BSP.stable_comp | exact GlobalTheory.BSP.stable_comp | (intros; apply GlobalTheory.BSP.stable_comp <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.framedFCrystal_exists_coords_every_prism : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (M : FCrys l ↥(OL K)) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)), Framed S M e → ∀ B : Obj l ↥(OL K), ∃ V : Eval S B (M.M B), IsCoord e V := by
  first | exact @GlobalTheory.BSP.CoordEx.main | exact GlobalTheory.BSP.CoordEx.main | (intros; apply GlobalTheory.BSP.CoordEx.main <;> assumption)
end
