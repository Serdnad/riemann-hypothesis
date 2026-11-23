module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle499
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle442
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle622
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeStabilizerCompact
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle631
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle669
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle673
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittFrameReduceRank
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import GroundTheory.AutomorphicForms.AdelicUnitaryGroups
public import GroundTheory.AutomorphicForms.AnisotropicUnitaryRes
public import CompanionTheory.AutomorphicTheory.SiegelWeilFiniteness.Bridge
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductTransposeInverseDualReverse
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle675
import Development.WeilBound.ThetaLifts.FrameEstimates.LeHeightOfIsTorusElt
import Development.WeilBound.ThetaLifts.Reductions.SiegelAbs
import GroundTheory.AutomorphicForms.ReductionMahler
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle081
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm

@[expose] public section

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.CompanionTheory.WSum
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.integral_multiple_path_trivial_character : ∀ (D : D7) (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D) (hσ : GlobalTheory.FockCompare.Chart θ σ) (a : HermE D r) (φ : Mx D V.rank r → ℂ), φ ∈ schwartzA θ V.rank r → ∃ N : ℕ, 0 < N ∧ ∀ y, φ y ≠ 0 → ψ (halfTr (Matrix.trace (HMul.hMul (N • ((GlobalTheory.CompanionTheory.HermPoisson.ofHermE a).1 - path hσ a 1)).1 (inner V y y) : Mx D r r))) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.WSum.Level.level | exact GlobalTheory.CompanionTheory.WSum.Level.level | (intros; apply GlobalTheory.CompanionTheory.WSum.Level.level <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct

theorem _root_.GlobalTheory.T.lattice_stabilizer_compact : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}, IsCMExt F E σ → IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)) (Λ : Submodule (intLoc F E v) (Fin n → Fv F v ⊗[F] E)), IsLat (intLoc F E v) Λ → IsCompact (stabLat σ J Λ : Set (GLoc σ J v)) := by
  first | exact @GlobalTheory.CompanionTheory.KFin.CompactStab.isCompact_stabLat | exact GlobalTheory.CompanionTheory.KFin.CompactStab.isCompact_stabLat | (intros; apply GlobalTheory.CompanionTheory.KFin.CompactStab.isCompact_stabLat <;> assumption)
end

section

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

namespace GlobalTheory.CompanionTheory.RapidDecay

theorem torus_contracts_unipRad : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (Q : Set (GAd σ J)) (c : ℝ), IsCompact Q → 0 < c → ∀ s : Fin r, ∃ M : ℝ, 0 ≤ M ∧ ∀ m ∈ Q, m ∈ unipRad σ J (pre X s) → ∀ t ∈ cone r c, ∀ a, IsTorusElt σ J X Y t a → ∀ (w : InfinitePlace F) (τ : EmbOver E w) (i j : Fin n), ‖(archMat σ J τ (projArch σ J w (a⁻¹ * m * a)) - 1) i j‖ ≤ M / ratio t s := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW Q c hQ hc s
  obtain ⟨K, hK0, hK⟩ := GlobalTheory.T.cone_frame_weight_ratio_bound r c hc
  have hb : ∀ q : (Σ w : InfinitePlace F, EmbOver E w) × FrameIx r × FrameIx r × Fin n × Fin n, ∃ B : ℝ, ∀ g ∈ Q,
      ‖((frameIdem (σ : E →+* E) J X Y q.2.1).map q.1.2.1 * (archMat σ J q.1.2 (projArch σ J q.1.1 g) - 1) *
        (frameIdem (σ : E →+* E) J X Y q.2.2.1).map q.1.2.1) q.2.2.2.1 q.2.2.2.2‖ ≤ B := fun q => by
    have hcont : Continuous fun g : GAd σ J => archMat σ J q.1.2 (projArch σ J q.1.1 g) :=
      (GlobalTheory.Orb.continuous_archMat σ J q.1.2).comp (continuous_projArch σ J q.1.1)
    refine hQ.exists_bound_of_continuousOn (Continuous.continuousOn ?_)
    exact ((continuous_const.matrix_mul (hcont.sub continuous_const)).matrix_mul continuous_const).matrix_elem _ _
  choose B hB using hb
  set Bt : ℝ := ∑ q, |B q| with hBt
  have hBt0 : 0 ≤ Bt := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨(Fintype.card (FrameIx r) : ℝ) * ((Fintype.card (FrameIx r) : ℝ) * (K * Bt)), by positivity, ?_⟩
  intro m hm hmU t ht a ha w τ i j
  have hr : 0 < ratio t s := ratio_pos ht s
  have hd : ∀ α, 0 < frameWt t α := frameWt_pos ht.1
  set A := archMat σ J τ (projArch σ J w a) with hAdef
  set A' := archMat σ J τ (projArch σ J w a⁻¹) with hA'def
  set M₁ := archMat σ J τ (projArch σ J w m) - 1 with hM₁
  set P : FrameIx r → Matrix (Fin n) (Fin n) ℂ := fun α => (frameIdem (σ : E →+* E) J X Y α).map τ.1 with hPdef
  have hAA : A' * A = 1 := by
    rw [hAdef, hA'def, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one]
  have e2 : archMat σ J τ (projArch σ J w (a⁻¹ * m * a)) - 1 = A' * M₁ * A := by
    rw [map_mul, map_mul, map_mul, map_mul, ← hAdef, ← hA'def, hM₁, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hAA]
  have hP : ∑ α, P α = 1 := by
    have : ∑ α, P α = (τ.1.mapMatrix) (∑ α, frameIdem (σ : E →+* E) J X Y α) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]; rfl
    rw [this, sum_frameIdem, map_one]
  have hTor : ∀ β, A * P β = ((frameWt t β : ℝ) : ℂ) • P β := fun β =>
    GlobalTheory.T.torus_archimedean_frame_action F E σ h n J hJ r X Y hW t a ha ht.1 w τ β
  have hA : A = ∑ β, ((frameWt t β : ℝ) : ℂ) • P β := by
    calc A = A * ∑ β, P β := by rw [hP, Matrix.mul_one]
      _ = _ := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun β _ => hTor β
  have hTor' : ∀ α, A' * P α = ((frameWt t α : ℝ) : ℂ)⁻¹ • P α := fun α => by
    have hne : ((frameWt t α : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hd α).ne'
    rw [eq_inv_smul_iff₀ hne, ← Matrix.mul_smul, ← hTor α, ← Matrix.mul_assoc, hAA, Matrix.one_mul]
  have hA' : A' = ∑ α, ((frameWt t α : ℝ) : ℂ)⁻¹ • P α := by
    calc A' = A' * ∑ α, P α := by rw [hP, Matrix.mul_one]
      _ = _ := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun α _ => hTor' α
  have e3 : A' * M₁ * A = ∑ α, ∑ β, (((frameWt t α : ℝ) : ℂ)⁻¹ * ((frameWt t β : ℝ) : ℂ)) • (P α * M₁ * P β) := by
    conv_lhs => rw [hA', hA]
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [smul_mul_assoc, smul_mul_assoc, Matrix.mul_smul, smul_smul]
  have term : ∀ α β, ‖((((frameWt t α : ℝ) : ℂ)⁻¹ * ((frameWt t β : ℝ) : ℂ)) • (P α * M₁ * P β)) i j‖ ≤ K * Bt / ratio t s := fun α β => by
    by_cases hl : frameLev s α ≤ frameLev s β
    · have h0 : P α * M₁ * P β = 0 := GlobalTheory.T.unipotent_frame_level_triangular F E σ h n J hJ r X Y hW s m hmU w τ α β hl
      rw [h0, smul_zero]
      simpa using div_nonneg (mul_nonneg hK0 hBt0) hr.le
    · have h1 := hK s t ht α β (not_le.1 hl)
      have h2 : ‖(P α * M₁ * P β) i j‖ ≤ Bt :=
        ((hB (⟨w, τ⟩, α, β, i, j) m hm).trans (le_abs_self _)).trans
          (Finset.single_le_sum (f := fun q => |B q|) (fun _ _ => abs_nonneg _) (Finset.mem_univ _))
      have h3 : ‖((frameWt t α : ℝ) : ℂ)⁻¹ * ((frameWt t β : ℝ) : ℂ)‖ = frameWt t β / frameWt t α := by
        rw [norm_mul, norm_inv, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (hd α).le,
          Real.norm_of_nonneg (hd β).le, div_eq_inv_mul]
      rw [Matrix.smul_apply, norm_smul, h3]
      calc _ ≤ K / ratio t s * Bt := mul_le_mul h1 h2 (norm_nonneg _) (div_nonneg hK0 hr.le)
        _ = _ := by ring
  rw [e2, e3, Matrix.sum_apply]
  calc _ ≤ ∑ α : FrameIx r, ‖(∑ β, (((frameWt t α : ℝ) : ℂ)⁻¹ * ((frameWt t β : ℝ) : ℂ)) • (P α * M₁ * P β)) i j‖ := norm_sum_le _ _
    _ ≤ ∑ α : FrameIx r, ∑ β : FrameIx r, K * Bt / ratio t s := Finset.sum_le_sum fun α _ => by
        rw [Matrix.sum_apply]
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun β _ => term α β)
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

end GlobalTheory.CompanionTheory.RapidDecay

end
end

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.minimal_parabolic_scales_isotropic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsWittFrame σ J X Y → ∀ δ ∈ ratPts σ J, δ ∈ minPar σ J X → ∃ e : E, e ≠ 0 ∧ Sends σ J δ (e • Xᵀ 0) (Xᵀ 0) := by
  first | exact @GlobalTheory.CompanionTheory.RedCov.exists_sends_of_rat_mem_minPar | exact GlobalTheory.CompanionTheory.RedCov.exists_sends_of_rat_mem_minPar | (intros; apply GlobalTheory.CompanionTheory.RedCov.exists_sends_of_rat_mem_minPar <;> assumption)
end

section

set_option maxSynthPendingDepth 1

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.RedCov.Simple
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.RedCov.Simple

theorem exists_one_le_mul_hgt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (D : Set (GAd σ J)), IsCompact D → ∃ P : ℝ, 0 < P ∧ ∀ g ∈ D, ∀ v : Fin n → E, v ≠ 0 → 1 ≤ P * hgt σ J g v := by
  intro F E _ _ _ _ _ σ hCM n J D hD
  obtain ⟨-, -, h2, -⟩ := hCM
  haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  obtain ⟨P, hP, h⟩ := GroundTheory.Automorphic.Reduction.exists_adelicNorm_vecMul_le_mul
    (hD.image (Bridge.continuous_trG σ J).inv)
  refine ⟨P, hP, fun g hg v hv => ?_⟩
  have hc := Bridge.cvec_ne_zero (F := F) hv
  have e : GroundTheory.Automorphic.Reduction.ratVec (Bridge.cvec F v) ᵥ*
        (Bridge.trG σ J g).1 ᵥ* ((Bridge.trG σ J g)⁻¹).1 =
      GroundTheory.Automorphic.Reduction.ratVec (Bridge.cvec F v) := by
    rw [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]
  have h3 : GroundTheory.Automorphic.Reduction.adelicNorm (GroundTheory.Automorphic.Reduction.ratVec (Bridge.cvec F v) ᵥ*
        (Bridge.trG σ J g).1 ᵥ* ((Bridge.trG σ J g)⁻¹).1) ≤
      P * GroundTheory.Automorphic.Reduction.height (Bridge.trG σ J g) (Bridge.cvec F v) :=
    h _ ⟨g, hg, rfl⟩ _ (GroundTheory.Automorphic.Reduction.hasFiniteContent_height (Bridge.trG σ J g) hc)
  rw [e] at h3
  rw [Bridge.hgt_eq]
  exact (GroundTheory.Automorphic.Reduction.one_le_adelicNorm_ratVec hc).trans h3

end GlobalTheory.CompanionTheory.RedCov.Simple

end
end

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.exists_near_minimal_vector : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsWittFrame σ J X Y → ∀ g : GAd σ J, ∃ v, NearMin σ J g v := by
  first | exact @GlobalTheory.CompanionTheory.RedCov.exists_nearMin | exact GlobalTheory.CompanionTheory.RedCov.exists_nearMin | (intros; apply GlobalTheory.CompanionTheory.RedCov.exists_nearMin <;> assumption)
end

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.rational_unitary_sends_isotropic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsWittFrame σ J X Y → ∀ v : Fin n → E, v ≠ 0 → hE σ J v v = 0 → ∃ γ ∈ ratPts σ J, Sends σ J γ (Xᵀ 0) v := by
  first | exact @GlobalTheory.CompanionTheory.RedCov.exists_ratPts_sends_isotropic | exact GlobalTheory.CompanionTheory.RedCov.exists_ratPts_sends_isotropic | (intros; apply GlobalTheory.CompanionTheory.RedCov.exists_ratPts_sends_isotropic <;> assumption)
end

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.rational_unitary_witt_extension : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ γ ∈ ratPts σ J, ∀ w : Fin n → E, ∃ w' : Fin n → E, Sends σ J γ w w' ∧ hE σ J w' w' = hE σ J w w := by
  first | exact @GlobalTheory.CompanionTheory.RedCov.exists_sends_hE | exact GlobalTheory.CompanionTheory.RedCov.exists_sends_hE | (intros; apply GlobalTheory.CompanionTheory.RedCov.exists_sends_hE <;> assumption)
end

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.witt_frame_reduce_rank : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsWittFrame σ J X Y → ∃ (n' : ℕ) (J' : Matrix (Fin n') (Fin n') E) (X' Y' : Matrix (Fin n') (Fin r) E) (ι : GAd σ J' →* GAd σ J), IsHermND σ J' ∧ IsWittFrame σ J' X' Y' ∧ Continuous ι ∧ (∀ γ ∈ ratPts σ J', ι γ ∈ ratPts σ J) ∧ (∀ g', Sends σ J (ι g') (Xᵀ 0) (Xᵀ 0)) ∧ (∀ q ∈ minParOne σ J' X', ι q ∈ minParOne σ J X) ∧ ∀ a, IsTorus σ J X Y a → (∀ a', IsTorus σ J' X' Y' a' → ∀ s', ι (a' s') = a (Fin.cons 0 s')) ∧ (∀ (s₁ : ℝ) g', Commute (a (Fin.cons s₁ 0)) (ι g')) ∧ ∀ p ∈ minPar σ J X, ∃ g', ∃ q₀ ∈ minParOne σ J X, ∃ s₁ : ℝ, p = q₀ * a (Fin.cons s₁ 0) * ι g' ∧ ∀ h', (ι h')⁻¹ * q₀ * ι h' ∈ minParOne σ J X := by
  first | exact @GlobalTheory.CompanionTheory.RedCov.Levi.exists_levi | exact GlobalTheory.CompanionTheory.RedCov.Levi.exists_levi | (intros; apply GlobalTheory.CompanionTheory.RedCov.Levi.exists_levi <;> assumption)
end

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GroundTheory.Automorphic GroundTheory.Automorphic.Anisotropic
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal NumberField.AdeleRing
attribute [local instance] tensorTopology finite_of_isQuadraticExtension isModuleTopology_tensor isTopologicalRing_tensor

set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.RedCov.Mahler

open GlobalTheory.CompanionTheory.RedCov.Bridge

def pointsHomeo {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    GAd (conj F E).toAlgHom J ≃ₜ unitaryPoints F E J 𝔸[F] where
  toFun g := ⟨matHom _ _ J g, (SetLike.ext_iff.1 (CompanionTheory.SWFin.HR_eq J (AF F)) _).1 g.2⟩
  invFun u := ⟨u.1, (SetLike.ext_iff.1 (CompanionTheory.SWFin.HR_eq J (AF F)) _).2 u.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := Continuous.subtype_mk continuous_subtype_val _
  continuous_invFun := Continuous.subtype_mk continuous_subtype_val _

theorem exists_isCompact_of_le_hgt : (∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Algebra.IsQuadraticExtension F E] (n : ℕ) (H : Matrix (Fin n) (Fin n) E), IsUnit H.det → ∀ (Y : Set (unitaryPoints F E H 𝔸[F])) (ε : ℝ), 0 < ε → (∀ u ∈ Y, ∀ x : Fin (Fintype.card (Fin n × Fin (Module.finrank F E))) → F, x ≠ 0 → ε ≤ Reduction.height (trHom (ι := Fin n) (Module.finBasis F E) 𝔸[F] (u : GL (Fin n) (𝔸[F] ⊗[F] E))) x) → ∃ Ω : Set (unitaryPoints F E H 𝔸[F]), IsCompact Ω ∧ ∀ u ∈ Y, ∃ θ ∈ (unitaryDiagonal F H).range, θ⁻¹ * u ∈ Ω) → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ t : ℝ, 0 < t → ∃ C₀ : Set (GAd σ J), IsCompact C₀ ∧ ∀ g : GAd σ J, (∀ v : Fin n → E, v ≠ 0 → t ≤ hgt σ J g v) → ∃ γ ∈ ratPts σ J, γ⁻¹ * g ∈ C₀ := by
  intro hM F E _ _ _ _ _ σ hσ n J hJ t ht
  obtain ⟨hF, hE', h2, hc⟩ := hσ
  haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  obtain rfl : σ = (conj F E).toAlgHom := AlgHom.ext fun x =>
    τ.injective ((hc τ x).trans (GroundTheory.Heights₂.Heights.FiniteCovolume.embedding_conj τ x).symm)
  have hu : IsUnit J.det := isUnit_iff_ne_zero.2 hJ.2
  let e := pointsHomeo (F := F) (E := E) J
  obtain ⟨Ω, hΩ, hcov⟩ := hM F E n J hu
    (e '' {g | ∀ v : Fin n → E, v ≠ 0 → t ≤ hgt _ J g v}) t ht (by
      rintro _ ⟨g, hg, rfl⟩ x hx
      obtain ⟨v, rfl⟩ := cvec_surjective (F := F) (E := E) (n := n) x
      have hv : v ≠ 0 := by
        rintro rfl
        apply hx
        funext p
        simp [cvec]
      have := hg v hv
      rw [hgt_eq] at this
      exact this)
  refine ⟨e ⁻¹' Ω, e.isCompact_preimage.2 hΩ, fun g hg => ?_⟩
  obtain ⟨θ, hθ, hθΩ⟩ := hcov (e g) ⟨g, hg, rfl⟩
  rw [← CompanionTheory.SWFin.HFin_eq, Subgroup.mem_subgroupOf] at hθ
  refine ⟨e.symm θ, ?_, ?_⟩
  · exact Subgroup.mem_subgroupOf.2 hθ
  · exact hθΩ

end GlobalTheory.CompanionTheory.RedCov.Mahler
end
end

section

set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 1

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.RedCov.FirstLower

section Helpers

open PositivityTheory.ThKEst (rId)
open PositivityTheory.ThKEst.Sieg (rId_add rId_zero' rId_snd)
open GroundTheory.Automorphic.Anisotropic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def rIdele [IsTotallyReal F] (c : ℝ) : GroundTheory.Global.IdeleGroup F where
  val := rId F c
  inv := rId F (-c)
  val_inv := by rw [← rId_add, add_neg_cancel, rId_zero']
  inv_val := by rw [← rId_add, neg_add_cancel, rId_zero']

theorem ideleModule_rIdele [IsTotallyReal F] (c : ℝ) :
    (GroundTheory.Global.IdeleGroup.ideleModule F (rIdele c) : ℝ) = Real.exp ((Module.finrank ℚ F : ℝ) * c) := by
  have hm : ∀ w : InfinitePlace F, w.mult = 1 := fun w => by
    rw [InfinitePlace.mult, ite_eq_left (IsTotallyReal.isReal w)]
  have hinf : ∀ w : InfinitePlace F, ‖(rId F c).1 w‖ ^ w.mult = Real.exp c := fun w => by
    rw [hm, pow_one]
    exact norm_evInf_rId w c
  have hfin : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), ‖(rId F c).2 v‖ = 1 := fun v => by
    rw [rId_snd]
    exact norm_one
  have e : (GroundTheory.Global.IdeleGroup.ideleModule F (rIdele c) : ℝ) =
      (∏ w : InfinitePlace F, ‖(rId F c).1 w‖ ^ w.mult) *
        ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), ‖(rId F c).2 v‖ :=
    GroundTheory.Global.IdeleGroup.ideleModule_eq _
  rw [e, finprod_eq_one_of_forall_eq_one hfin, mul_one, Finset.prod_congr rfl fun w _ => hinf w,
    Finset.prod_const, Finset.card_univ, card_infinitePlace, ← Real.exp_nat_mul]

variable {n r : ℕ}

theorem mulVec_ratV_col {X : Matrix (Fin n) (Fin (r + 1)) E} {M : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)}
    {B : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)} (hB : B.BlockTriangular id)
    (h : M * adMat F X = adMat F X * B) : M *ᵥ ratV F (Xᵀ 0) = B 0 0 • ratV F (Xᵀ 0) := by
  funext i
  have h1 : (M *ᵥ ratV F (Xᵀ 0)) i = (M * adMat F X) i 0 := rfl
  rw [h1, h, Matrix.mul_apply, Finset.sum_eq_single 0]
  · simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_comm _ _
  · intro j _ hj
    rw [hB (show id (0 : Fin (r + 1)) < id j from Fin.pos_of_ne_zero hj), mul_zero]
  · simp

theorem ratV_smul (e : E) (w : Fin n → E) : ratV F (e • w) = inclR (F := F) (AF F) e • ratV F w := by
  funext i
  simp [ratV, map_mul]

theorem resVec_algebraMap_smul [Algebra.IsQuadraticExtension F E] (c : AF F) (ξ : Fin n → AF F ⊗[F] E) :
    resVec (ι := Fin n) (Module.finBasis F E) (AF F) (algebraMap (AF F) (AF F ⊗[F] E) c • ξ) =
      c • resVec (ι := Fin n) (Module.finBasis F E) (AF F) ξ := by
  have e : algebraMap (AF F) (AF F ⊗[F] E) c • ξ = c • ξ := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, ← Algebra.smul_def]
  rw [e]
  conv_lhs => rw [← ofResVec_resVec (Module.finBasis F E) (AF F) ξ, ← ofResVec_smul, resVec_ofResVec]

variable {σ : E →ₐ[F] E} {J : Matrix (Fin n) (Fin n) E} {X Y : Matrix (Fin n) (Fin (r + 1)) E}

theorem IsTorus.inv_eq {a : (Fin (r + 1) → ℝ) → GAd σ J} (ha : IsTorus σ J X Y a) (s : Fin (r + 1) → ℝ) :
    (a s)⁻¹ = a (-s) := by
  have h0 : a 0 = 1 := by
    have := ha.add 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  rw [inv_eq_iff_mul_eq_one, ← ha.add, add_neg_cancel, h0]

theorem torus_inv_mulVec {a : (Fin (r + 1) → ℝ) → GAd σ J} (ha : IsTorus σ J X Y a) {p : GAd σ J}
    (hp : p ∈ minPar σ J X) (s : Fin (r + 1) → ℝ) (e : E) :
    (matHom _ σ J (a s)⁻¹).1 *ᵥ ((matHom _ σ J p).1 *ᵥ ratV F (e • Xᵀ 0)) =
      algebraMap (AF F) (AF F ⊗[F] E) (rId F (-s 0)) • ((matHom _ σ J p).1 *ᵥ ratV F (e • Xᵀ 0)) := by
  obtain ⟨B, hB, hpB⟩ := hp
  have h1 := mulVec_ratV_col hB hpB
  have h2 := mulVec_ratV_col (Matrix.blockTriangular_diagonal _) (ha.onX (-s))
  rw [Matrix.diagonal_apply_eq] at h2
  rw [IsTorus.inv_eq ha, ratV_smul, Matrix.mulVec_smul, h1, Matrix.mulVec_smul, Matrix.mulVec_smul, h2]
  funext i
  simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem col_ne_zero (hW : IsWittFrame σ J X Y) : Xᵀ 0 ≠ 0 := by
  intro h0
  have h1 := congrFun (congrFun hW.xy 0) 0
  have hc : ∀ i, X i 0 = 0 := fun i => congrFun h0 i
  simp [cT, Matrix.mul_apply, hc] at h1

end Helpers


open GroundTheory.Automorphic GroundTheory.Automorphic.Anisotropic GlobalTheory.CompanionTheory.RedCov.Bridge in
theorem vecMul_trG_torus {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] {σ : E →ₐ[F] E} {n r : ℕ} {J : Matrix (Fin n) (Fin n) E}
    {X Y : Matrix (Fin n) (Fin (r + 1)) E} {a : (Fin (r + 1) → ℝ) → GAd σ J} (ha : IsTorus σ J X Y a)
    {ω : GAd σ J} (hω : ω⁻¹ ∈ minPar σ J X) (s : Fin (r + 1) → ℝ) (e : E) :
    (Reduction.ratVec (cvec F (e • Xᵀ 0)) ᵥ* (trG σ J ω).1) ᵥ* (trG σ J (a s)).1 =
      ((rIdele (-s 0) : GroundTheory.Global.IdeleGroup F) : AF F) •
        (Reduction.ratVec (cvec F (e • Xᵀ 0)) ᵥ* (trG σ J ω).1) := by
  have step : ∀ (g : GAd σ J) (ξ : Fin n → AF F ⊗[F] E),
      resVec (ι := Fin n) (Module.finBasis F E) (AF F) ξ ᵥ* (trG σ J g).1 =
        resVec (ι := Fin n) (Module.finBasis F E) (AF F) ((matHom _ σ J g⁻¹).1 *ᵥ ξ) := fun g ξ => by
    rw [trG, MonoidHom.comp_apply, map_inv]
    exact resVec_vecMul_trHom _ _ _ _
  rw [ratVec_cvec, step, step, torus_inv_mulVec ha hω, resVec_algebraMap_smul]
  rfl


open GroundTheory.Automorphic GlobalTheory.CompanionTheory.RedCov.Bridge in
theorem exp_le_hgt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsWittFrame σ J X Y → ∀ a, IsTorus σ J X Y a → ∀ (Ω C : Set (GAd σ J)), IsCompact Ω → Ω ⊆ minPar σ J X → IsCompact C → ∃ P : ℝ, 0 < P ∧ ∀ ω ∈ Ω, ∀ s : Fin (r + 1) → ℝ, ∀ κ ∈ C, ∀ e : E, e ≠ 0 → Real.exp (- ((Module.finrank ℚ F : ℝ) * s 0)) ≤ P * hgt σ J (ω * a s * κ) (e • Xᵀ 0) := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW a ha Ω C hΩ hΩP hC
  haveI : Algebra.IsQuadraticExtension F E := ⟨h.2.2.1⟩
  haveI : IsTotallyReal F := h.1
  have hcont : Continuous fun g : GAd σ J => (trG σ J g)⁻¹ := (continuous_trG σ J).inv
  obtain ⟨P₁, hP₁, hb₁⟩ := Reduction.exists_adelicNorm_vecMul_le_mul (hC.image hcont)
  obtain ⟨P₂, hP₂, hb₂⟩ := Reduction.exists_adelicNorm_vecMul_le_mul (hΩ.image hcont)
  refine ⟨P₁ * P₂, mul_pos hP₁ hP₂, fun ω hω s κ hκ e he => ?_⟩
  have hv : e • Xᵀ 0 ≠ 0 := smul_ne_zero he (col_ne_zero hW)
  have hc0 := cvec_ne_zero (F := F) hv
  set y₀ := Reduction.ratVec (cvec F (e • Xᵀ 0)) with hy₀
  have hf₀ : Reduction.HasFiniteContent y₀ := Reduction.hasFiniteContent_ratVec hc0
  set y₁ := y₀ ᵥ* (trG σ J ω).1 with hy₁
  have hf₁ : Reduction.HasFiniteContent y₁ := hf₀.vecMul (trG σ J ω)
  set u := rIdele (F := F) (-s 0) with hu
  have hkey : y₁ ᵥ* (trG σ J (a s)).1 = (u : AF F) • y₁ :=
    vecMul_trG_torus ha (inv_mem_minPar h hJ hW (hΩP hω)) s e
  have hg : hgt σ J (ω * a s * κ) (e • Xᵀ 0) = Reduction.adelicNorm (((u : AF F) • y₁) ᵥ* (trG σ J κ).1) := by
    rw [hgt_eq, Reduction.height, map_mul, map_mul, Units.val_mul, Units.val_mul, ← Matrix.vecMul_vecMul,
      ← Matrix.vecMul_vecMul, ← hy₀, ← hy₁, hkey]
  have hf₂ : Reduction.HasFiniteContent (((u : AF F) • y₁) ᵥ* (trG σ J κ).1) := (hf₁.smul u).vecMul (trG σ J κ)
  have hb3 : Reduction.adelicNorm ((u : AF F) • y₁) ≤ P₁ * hgt σ J (ω * a s * κ) (e • Xᵀ 0) := by
    have := hb₁ _ ⟨κ, hκ, rfl⟩ _ hf₂
    rwa [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one, ← hg] at this
  have hb4 : Reduction.adelicNorm y₀ ≤ P₂ * Reduction.adelicNorm y₁ := by
    have := hb₂ _ ⟨ω, hω, rfl⟩ _ hf₁
    rwa [hy₁, Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one] at this
  have h1 : 1 ≤ Reduction.adelicNorm y₀ := Reduction.one_le_adelicNorm_ratVec hc0
  have hsm : Reduction.adelicNorm ((u : AF F) • y₁) =
      Real.exp (- ((Module.finrank ℚ F : ℝ) * s 0)) * Reduction.adelicNorm y₁ := by
    rw [Reduction.adelicNorm_smul hf₁ u, hu, ideleModule_rIdele, mul_neg]
  have hexp := Real.exp_pos (- ((Module.finrank ℚ F : ℝ) * s 0))
  calc Real.exp (- ((Module.finrank ℚ F : ℝ) * s 0))
      ≤ Real.exp (- ((Module.finrank ℚ F : ℝ) * s 0)) * (P₂ * Reduction.adelicNorm y₁) :=
        le_mul_of_one_le_right hexp.le (h1.trans hb4)
    _ = P₂ * Reduction.adelicNorm ((u : AF F) • y₁) := by rw [hsm]; ring
    _ ≤ P₂ * (P₁ * hgt σ J (ω * a s * κ) (e • Xᵀ 0)) := mul_le_mul_of_nonneg_left hb3 hP₂.le
    _ = P₁ * P₂ * hgt σ J (ω * a s * κ) (e • Xᵀ 0) := by ring

end GlobalTheory.CompanionTheory.RedCov.FirstLower
end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL Zc.Cos GlobalTheory.CompanionTheory.ThetaProd

theorem _root_.GlobalTheory.T.jacquet_theta_reverse_blocks : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (hd' : ∑ a, d (Fin.rev a) = N)
    (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V),
    Nonempty ((_root_.GlobalTheory.SmGL.jac (stdBlocks d hd) (π.comp (thetaW k N))).Equiv
      ((_root_.GlobalTheory.SmGL.jac (stdBlocks (fun a => d (Fin.rev a)) hd') π).comp (thetaL d))) := by
  first | exact @GlobalTheory.CompanionTheory.JacTheta.nonempty_jac_comp_thetaW | exact GlobalTheory.CompanionTheory.JacTheta.nonempty_jac_comp_thetaW | (intros; apply GlobalTheory.CompanionTheory.JacTheta.nonempty_jac_comp_thetaW <;> assumption)
end
