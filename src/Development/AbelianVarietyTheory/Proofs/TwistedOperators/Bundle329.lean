module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle309
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle196
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactHaarRightInvariantInst
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoefIntegralEq
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle073
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Mathlib.LinearAlgebra.Matrix.Rank
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilRepresentationContinuous
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
public import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle312
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Normed.Module.HahnBanach
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Chain.IoLift

theorem it_eq_sum_kMean : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (pt : PolF D W.rank V.rank → WO V W → ℂ) (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M), IsItW θ M M' ω pt It → ∀ (τ : D.what₂.Tau) (n : ℕ) (c : Fin n → Formalism.REAL.KG (M'.ε τ) → ℂ) (φ : PolF D W.rank V.rank) (φs : Fin n → PolF D W.rank V.rank) (v : M'.Vec) (u : Fin n → M'.sm τ), (∀ i, Continuous (c i)) → (∀ k, ω (1, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.elt θ M' τ (Formalism.REAL.toMK k)) (pt φ) = pt (∑ i, c i k • φs i)) → (∀ i, (u i : M'.H τ) = kMean M' τ (c i) (v τ)) → It φ (PiTensorProduct.tprod ℂ v) = ∑ i, It (φs i) (PiTensorProduct.tprod ℂ (Function.update v τ (u i))) := by
  intro D V W S S' M M' θ ω pt It hIt τ n c φ φs v u hc hω hu
  have := (M'.ds τ).1
  have hU := (M'.ds τ).2.2.1
  rw [← sub_eq_zero]
  refine inclT_injective M ?_
  rw [map_zero]
  refine ellT_separates M _ fun w => ?_
  let l : Fin n → (M'.sm τ →ₗ[ℂ] ℂ) := fun i => ellT M w ∘ₗ inclT M ∘ₗ It (φs i) ∘ₗ
    (PiTensorProduct.tprod ℂ (s := fun ρ => M'.sm ρ)).toLinearMap v τ
  have hl : ∀ i x, l i x = ellT M w (inclT M (It (φs i) (PiTensorProduct.tprod ℂ (Function.update v τ x)))) :=
    fun _ _ => rfl
  have hb : ∀ i, ∃ C : ℝ, ∀ x, ‖l i x‖ ≤ C * ‖x‖ := fun i => by
    obtain ⟨C, hC⟩ := hIt.bdd (φs i) w
    refine ⟨C * ∏ ρ ∈ Finset.univ.erase τ, ‖(v ρ : M'.H ρ)‖, fun x => ?_⟩
    rw [hl]
    refine (hC _).trans (le_of_eq ?_)
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ τ), mul_assoc, Function.update_self]
    congr 2
    refine Finset.prod_congr rfl fun ρ hρ => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hρ)]
  choose L hL _ using fun i => exists_extension_norm_eq (M'.sm τ) ((l i).mkContinuousOfExistsBound (hb i))
  have hL' : ∀ i (x : M'.sm τ), L i x = l i x := hL
  have hk : ∀ k : Formalism.REAL.KG (M'.ε τ), Formalism.REAL.toMK k ∈ Formalism.MainNotions.S.UJset (M'.ε τ) :=
    fun k => (Formalism.REAL.maximal_compact_facts _ _).1 _ k.2
  have hcm : Continuous fun k : Formalism.REAL.KG (M'.ε τ) => Formalism.REAL.toMK k :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hx : Continuous fun k : Formalism.REAL.KG (M'.ε τ) => M'.σ τ (Formalism.REAL.toMK k) (v τ) :=
    (hU.2.2 _).comp_continuous hcm hk
  have hint : ∀ i, Integrable (fun k : Formalism.REAL.KG (M'.ε τ) => c i k • M'.σ τ (Formalism.REAL.toMK k) (v τ))
      (Formalism.REAL.muK (M'.ε τ)) := fun i =>
    integrableOn_univ.1 (((hc i).smul hx).continuousOn.integrableOn_compact isCompact_univ)
  have key : ∀ k : Formalism.REAL.KG (M'.ε τ), ∑ i, L i (c i k • M'.σ τ (Formalism.REAL.toMK k) (v τ)) =
      ellT M w (inclT M (It φ (PiTensorProduct.tprod ℂ v))) := fun k => by
    have hs : M'.σ τ (Formalism.REAL.toMK k) (v τ) ∈ M'.sm τ :=
      (GlobalTheory.SmVec.sm_eq M' τ).ge
        (GlobalTheory.SmVec.sigma_mem (M'.fr_unit τ) (M'.fr_gram τ) hU ((GlobalTheory.SmVec.sm_eq M' τ).le (v τ).2) (hk k))
    have hr : M'.rep τ ((M'.fr τ)⁻¹ * Formalism.REAL.toMK k * M'.fr τ) = M'.σ τ (Formalism.REAL.toMK k) :=
      GlobalTheory.SmVec.trRep_conj (σ := M'.σ τ) (M'.fr_unit τ) _
    have h1 := hIt.invK τ _ (GlobalTheory.SmVec.conj_mem_UH (M'.fr_unit τ) (M'.fr_gram τ) (hk k)) φ _
      (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ (Function.update v τ ⟨_, hs⟩)) (hω k).symm (by
        unfold inclT
        rw [PiTensorProduct.map_tprod, PiTensorProduct.map_tprod, actT_pure, hr]
        congr 1
        funext ρ
        by_cases h : ρ = τ
        · subst h; simp
        · simp [Function.update_of_ne h])

    rw [← h1, map_sum, LinearMap.sum_apply, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, map_smul, LinearMap.smul_apply, map_smul, map_smul, ← hl, ← hL']

  rw [map_sub, map_sub, map_sum, map_sum, sub_eq_zero]
  have h2 : ∀ i, ellT M w (inclT M (It (φs i) (PiTensorProduct.tprod ℂ (Function.update v τ (u i))))) =
      ∫ k, L i (c i k • M'.σ τ (Formalism.REAL.toMK k) (v τ)) ∂(Formalism.REAL.muK (M'.ε τ)) := fun i => by
    rw [← hl, ← hL', hu, kMean, (L i).integral_comp_comm (hint i)]
  simp only [h2]
  rw [← integral_finsetSum _ fun i _ => (L i).integrable_comp (hint i)]
  simp only [key]
  simp

end GlobalTheory.Chain.IoLift

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IsoMean

def cplx {D : D7} (V W : HSp D) {k : ℕ} (B : Fin k → Matrix (Fin W.rank) (Fin V.rank) D.host.E) (z : Mx D 1 k) :
    WO V W :=
  ∑ i, z 0 i • (B i).map (incA D)

section

variable {D : D7} (V W : HSp D) {k : ℕ} (B : Fin k → Matrix (Fin W.rank) (Fin V.rank) D.host.E)

theorem cplx_add (z z' : Mx D 1 k) : cplx V W B (z + z') = cplx V W B z + cplx V W B z' := by
  simp only [cplx, Matrix.add_apply, add_smul, Finset.sum_add_distrib]

theorem cplx_zero : cplx V W B 0 = 0 := by
  simp [cplx]

theorem continuous_cplx : Continuous (cplx V W B) := by
  unfold cplx
  refine continuous_finsetSum _ fun i _ => ?_
  exact (continuous_id.matrix_elem 0 i).smul continuous_const

theorem cplx_rat (c : Matrix (Fin 1) (Fin k) D.host.E) :
    cplx V W B (c.map (incA D)) = (∑ i, c 0 i • B i).map (incA D) := by
  ext p q

  simp [cplx, Matrix.sum_apply, map_sum, smul_eq_mul]

end

theorem symplO_eq_add {D : D7} (S T : HSp D) (x y : WO S T) : symplO S T x y = symplOH S T x y + symplOH S T x y := by
  have h2 : algebraMap D.host.F (AF D.host.F) (1 / 2) * 2 = 1 := by
    rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]
    norm_num
  unfold symplOH
  linear_combination (-symplO S T x y) * h2

theorem meanX_heisO_rat {D : D7} (V W : HSp D) {a b : ℕ} (P : Matrix (Fin W.rank) (Fin a) D.host.E)
    (Q : Matrix (Fin b) (Fin V.rank) D.host.E) (μ : Measure (Mx D a b)) (𝓨 : Set (Mx D a b))
    (ψ : AddChar (AF D.host.F) ℂ) (F : WO V W → ℂ) (hF : IsThetaFunO ψ V W F) (w : WO V W) (hw : w ∈ ratL W V)
    (hwX : ∀ y, symplO V W w (emb V W P Q y) = 0) (x : WO V W) (hx : ∀ y, symplO V W x (emb V W P Q y) = 0) :
    meanX V W P Q μ 𝓨 (heisO ψ V W w F) x = ψ (symplO V W x w) * meanX V W P Q μ 𝓨 F x := by
  obtain ⟨l1, l2, l3, -, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D V W
  have hH0 : ∀ x y, symplO V W x y = 0 → symplOH V W x y = 0 := fun x y e => by
    unfold symplOH; rw [e, mul_zero]
  have skew : ∀ x y, symplOH V W y x = -symplOH V W x y := fun x y => by
    have e := l3 (x + y)
    rw [l1, l2, l2, l3 x, l3 y] at e
    linear_combination e
  obtain ⟨γ, rfl⟩ := hw
  unfold meanX
  rw [← integral_const_mul]
  congr 1
  funext y
  have hq := hF.quasi γ (emb V W P Q y + x)
  have er : (((incA D).toAddMonoidHom.mapMatrix (m := Fin W.rank) (n := Fin V.rank)) γ) = ratW W V γ := rfl
  simp only [heisO]
  rw [er] at hwX ⊢
  rw [show emb V W P Q y + x + ratW W V γ = ratW W V γ + (emb V W P Q y + x) by abel, hq, ← mul_assoc,
    ← AddChar.map_add_eq_mul]
  congr 2
  rw [l1, l2, skew (ratW W V γ) (emb V W P Q y), hH0 _ _ (hwX y), skew (ratW W V γ) x, symplO_eq_add, skew (ratW W V γ) x]
  ring

theorem meanX_mul_star_rat {D : D7} (V W : HSp D) {a b : ℕ} (P : Matrix (Fin W.rank) (Fin a) D.host.E)
    (Q : Matrix (Fin b) (Fin V.rank) D.host.E) (μ : Measure (Mx D a b)) (𝓨 : Set (Mx D a b))
    (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (F F' : WO V W → ℂ) (hF : IsThetaFunO ψ V W F)
    (hF' : IsThetaFunO ψ V W F') (w : WO V W) (hw : w ∈ ratL W V)
    (hwX : ∀ y, symplO V W w (emb V W P Q y) = 0) (x : WO V W) :
    meanX V W P Q μ 𝓨 F (w + x) * star (meanX V W P Q μ 𝓨 F' (w + x)) =
      meanX V W P Q μ 𝓨 F x * star (meanX V W P Q μ 𝓨 F' x) := by
  obtain ⟨l1, l2, l3, -, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D V W
  have hH0 : ∀ x y, symplO V W x y = 0 → symplOH V W x y = 0 := fun x y e => by
    unfold symplOH; rw [e, mul_zero]
  obtain ⟨γ, rfl⟩ := hw
  have er : (((incA D).toAddMonoidHom.mapMatrix (m := Fin W.rank) (n := Fin V.rank)) γ) = ratW W V γ := rfl
  rw [er] at hwX ⊢
  have key : ∀ G : WO V W → ℂ, IsThetaFunO ψ V W G →
      meanX V W P Q μ 𝓨 G (ratW W V γ + x) = ψ (-(symplOH V W (ratW W V γ) x)) * meanX V W P Q μ 𝓨 G x := by
    intro G hG
    unfold meanX
    rw [← integral_const_mul]
    congr 1
    funext y
    rw [show emb V W P Q y + (ratW W V γ + x) = ratW W V γ + (emb V W P Q y + x) by abel, hG.quasi, l2,
      hH0 _ _ (hwX y), zero_add]
  rw [key F hF, key F' hF', star_mul]
  have hn : ψ (-(symplOH V W (ratW W V γ) x)) * star (ψ (-(symplOH V W (ratW W V γ) x))) = 1 := by
    have h1 := hψ.1.2.1 (-(symplOH V W (ratW W V γ) x))
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, h1]
    norm_num
  linear_combination (meanX V W P Q μ 𝓨 F x * star (meanX V W P Q μ 𝓨 F' x)) * hn

end GlobalTheory.IsoMean

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EntryTest

theorem exists_left_inv {K : Type} [Field K] {m n : ℕ} (P : Matrix (Fin m) (Fin n) K) (h : P.rank = n) :
    ∃ P' : Matrix (Fin n) (Fin m) K, P' * P = 1 := by
  have hker : LinearMap.ker P.mulVecLin = ⊥ := by
    have e := LinearMap.finrank_range_add_finrank_ker P.mulVecLin
    rw [Matrix.finrank_range_mulVecLin, h, Module.finrank_fin_fun] at e
    exact Submodule.finrank_eq_zero.1 (by omega)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective P.mulVecLin hker
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  rw [← LinearMap.toMatrix'_toLin' P, ← LinearMap.toMatrix'_comp]
  rw [show Matrix.toLin' P = P.mulVecLin from rfl, hg, LinearMap.toMatrix'_id]

theorem exists_right_inv {K : Type} [Field K] {m n : ℕ} (Q : Matrix (Fin m) (Fin n) K) (h : Q.rank = m) :
    ∃ Q' : Matrix (Fin n) (Fin m) K, Q * Q' = 1 := by
  have hrange : LinearMap.range Q.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Matrix.finrank_range_mulVecLin, h, Module.finrank_fin_fun]
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective Q.mulVecLin hrange
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  rw [← LinearMap.toMatrix'_toLin' Q, ← LinearMap.toMatrix'_comp]
  rw [show Matrix.toLin' Q = Q.mulVecLin from rfl, hg, LinearMap.toMatrix'_id]

variable {D : D7}

theorem hO_test (V W : HSp D) (N : Matrix (Fin V.rank) (Fin W.rank) D.host.E) (x : WO V W) :
    hO V W x ((Matrix.of fun c b => star ((V.gram * N * W.gram⁻¹) b c) :
      Matrix (Fin W.rank) (Fin V.rank) D.host.E).map (incA D)) = ∑ a, ∑ d, incA D (N a d) * x d a := by
  have h1 : V.gram⁻¹ * (V.gram * N * W.gram⁻¹) * W.gram = N := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (GlobalTheory.LatVac.gram_det_isUnit W), Matrix.mul_one,
      Matrix.nonsing_inv_mul_cancel_left _ _ (GlobalTheory.LatVac.gram_det_isUnit V)]
  have hc : ∀ b c, cA D (((Matrix.of fun c b => star ((V.gram * N * W.gram⁻¹) b c) :
      Matrix (Fin W.rank) (Fin V.rank) D.host.E).map (incA D)) c b) = incA D ((V.gram * N * W.gram⁻¹) b c) := by
    intro b c
    rw [Matrix.map_apply, GlobalTheory.DualPairCheck.cA_incA, Matrix.of_apply, star_star]
  unfold hO
  simp only [hc]
  generalize V.gram * N * W.gram⁻¹ = M at h1
  subst h1

  simp only [Matrix.mul_apply, map_sum, map_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun c _ => Finset.sum_comm).trans ?_
  rw [Finset.sum_comm]

theorem sum_emb_single (V W : HSp D) {a b : ℕ} (P : Matrix (Fin W.rank) (Fin a) D.host.E)
    (Q : Matrix (Fin b) (Fin V.rank) D.host.E) (N : Matrix (Fin V.rank) (Fin W.rank) D.host.E) (i : Fin a) (j : Fin b)
    (e : D.host.E) (hN : Q * N * P = Matrix.single j i e) (y : Mx D a b) :
    ∑ k, ∑ l, incA D (N k l) * GlobalTheory.IsoMean.emb V W P Q y l k = incA D e * y i j := by
  have h1 : ∑ k, ∑ l, incA D (N k l) * GlobalTheory.IsoMean.emb V W P Q y l k =
      (N.map (incA D) * GlobalTheory.IsoMean.emb V W P Q y).trace := by
    simp [Matrix.trace, Matrix.mul_apply]
  have h2 : N.map (incA D) * GlobalTheory.IsoMean.emb V W P Q y =
      N.map (incA D) * (P.map (incA D) * y) * Q.map (incA D) := by
    simp only [GlobalTheory.IsoMean.emb, Matrix.mul_assoc]
  rw [h1, h2, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.map_mul, ← Matrix.map_mul, hN]
  simp [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, ite_and]

theorem entry : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), P.rank = a → Q.rank = b → ∀ (i : Fin a) (j : Fin b) (c : D.host.E), ∃ m : Matrix (Fin W.rank) (Fin V.rank) D.host.E, ∀ (y : Mx D a b) (r : AF D.host.F), symplO V W (GlobalTheory.IsoMean.emb V W P Q y) (r • m.map (incA D)) = r * Algebra.trace (AF D.host.F) (AE D) (incA D c * y i j) := by
  intro D V W a b P Q hP hQ i j c
  obtain ⟨P', hP'⟩ := exists_left_inv P hP
  obtain ⟨Q', hQ'⟩ := exists_right_inv Q hQ
  set N := Q' * Matrix.single j i (D.host.xi0⁻¹ * c) * P' with hNdef
  have hN : Q * N * P = Matrix.single j i (D.host.xi0⁻¹ * c) := by
    rw [hNdef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQ', Matrix.one_mul, Matrix.mul_assoc, hP', Matrix.mul_one]
  refine ⟨Matrix.of fun q p => star ((V.gram * N * W.gram⁻¹) p q), fun y r => ?_⟩
  rw [← GlobalTheory.SplitScalar.symplOH_add_self, GlobalTheory.FinTranslate.symplOH_smul_right, ← mul_add,
    GlobalTheory.SplitScalar.symplOH_add_self]
  congr 1
  rw [symplO, hO_test, sum_emb_single V W P Q N i j _ hN y, ← mul_assoc, ← map_mul,
    mul_inv_cancel_left₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)]

end GlobalTheory.EntryTest
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

noncomputable section

namespace GlobalTheory.ThetaL2InnerProduct

open GlobalTheory.OrientedHeis GlobalTheory.Size Filter
open scoped Topology

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}

def thetaSpace (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) : Submodule ℂ (WO S T → ℂ) where
  carrier := {f | IsThetaFunO ψ S T f}
  add_mem' := GlobalTheory.OrientedHeis.theta_add
  zero_mem' := GlobalTheory.OrientedHeis.theta_zero
  smul_mem' := fun a _ hf => GlobalTheory.OrientedHeis.theta_smul a hf

theorem ipTh_eq (f f' : WO S T → ℂ) : ipTh μ 𝓕 f f' = GlobalTheory.Ker.ipO μ 𝓕 f f' := rfl

theorem bound_near (hω : IsWeilDatumO ψ S T χS χT ω) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (p₀ : GA D S × GA D T) : ∃ C : ℝ, ∀ᶠ p in 𝓝 p₀, ∀ w, ‖ω p f w‖ ≤ C := by
  obtain ⟨K, hK, hKγ⟩ := (GlobalTheory.AdelicMatrixLattice.lattice D T S).2.2.2.2.2
  have hcont : Continuous fun q : (GA D S × GA D T) × WO S T => ω q.1 f q.2 :=
    GlobalTheory.ThetaJointCont.continuous_om_oriented hω hf
  have hc0 : ContinuousOn (fun w : WO S T => ω p₀ f w) K :=
    (hcont.comp (by fun_prop : Continuous fun w : WO S T => (p₀, w))).continuousOn
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hc0
  refine ⟨M + 1, ?_⟩
  have hev : ∀ᶠ p in 𝓝 p₀, ∀ y ∈ K, ‖ω p f y‖ < M + 1 := by
    refine hK.eventually_forall_of_forall_eventually fun y hy => ?_
    have hlt : ‖ω p₀ f y‖ < M + 1 := lt_of_le_of_lt (hM y hy) (lt_add_one M)
    exact hcont.norm.continuousAt.eventually_lt continuousAt_const hlt
  filter_upwards [hev] with p hp w
  obtain ⟨γ, hγ, hγK⟩ := hKγ w
  rw [← theta_norm_periodic hω.std (hω.om_pres p f hf) γ hγ w]
  exact (hp _ hγK).le

theorem continuousOn_ip (hω : IsWeilDatumO ψ S T χS χT ω) (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratL T S) 𝓕 μ) {X : Type} [TopologicalSpace X] [FirstCountableTopology X]
    {γ : X → GA D S × GA D T} {U : Set X} (hγ : ContinuousOn γ U) {F E : WO S T → ℂ}
    (hF : IsThetaFunO ψ S T F) (hE : IsThetaFunO ψ S T E) :
    ContinuousOn (fun x => ipTh μ 𝓕 (ω (γ x) F) E) U := by
  intro x₀ hx₀
  obtain ⟨C, hC⟩ := bound_near hω hF (γ x₀)
  obtain ⟨CE, hCE⟩ := theta_bounded hω.std hE
  have hfin : μ 𝓕 ≠ ⊤ := (measure_dom hμ h𝓕).2
  have : IsFiniteMeasure (μ.restrict 𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hfin.lt_top⟩
  unfold ipTh
  refine continuousWithinAt_of_dominated (bound := fun _ => C * CE) ?_ ?_ (integrable_const _) ?_
  · refine Filter.Eventually.of_forall fun x => ?_
    exact (integrableOn_mul_conj hω.std hμ h𝓕 (hω.om_pres (γ x) F hF) hE).aestronglyMeasurable
  · have ht : Tendsto γ (𝓝[U] x₀) (𝓝 (γ x₀)) := hγ x₀ hx₀
    filter_upwards [ht.eventually hC] with x hx
    refine Filter.Eventually.of_forall fun w => ?_
    rw [norm_mul, norm_star]
    exact mul_le_mul (hx w) (hCE w) (norm_nonneg _) ((norm_nonneg _).trans (hx w))
  · refine Filter.Eventually.of_forall fun w => ?_
    exact ((hω.om_cont F hF w).continuousAt.comp_continuousWithinAt (hγ x₀ hx₀)).mul continuousWithinAt_const

theorem weaklyContinuous_unitaryAction_of_realUnitaryHom (hω : IsWeilDatumO ψ S T χS χT ω) (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratL T S) 𝓕 μ) {n : ℕ} {ι : Type} (G : Mn n) (γ : Mn n → GA D S × GA D T)
    (h1 : γ 1 = 1) (hmul : ∀ g ∈ Formalism.QuantumDeterminants.UH G, ∀ g' ∈ Formalism.QuantumDeterminants.UH G, γ (g * g') = γ g * γ g')
    (hc : ContinuousOn γ (Formalism.QuantumDeterminants.UH G)) (pt : MvPolynomial ι ℂ →ₗ[ℂ] (WO S T → ℂ))
    (hpt : ∀ P, IsThetaFunO ψ S T (pt P))
    (hd : ∀ X : Mn n, Xᴴ * G + G * X = 0 → ∀ P, ∃ F', DerAll ψ ω (fun t => γ (NormedSpace.exp (t • X))) (pt P) F') :
    L2UnitaryRepresentationData G (fun g F => ω (γ g) F) pt (ipTh μ 𝓕) (thetaSpace ψ S T) := {
  mem := hpt
  pt_lin := fun z P Q => by rw [map_add (f := _), map_smul]
  ip_lin := fun z F hF F' hF' E hE => by
    rw [ipTh_eq, ipTh_eq, ipTh_eq, ipO_add_left hω.std hμ h𝓕 ((thetaSpace ψ S T).smul_mem z hF) hF' hE,
      ipO_smul_left]
  ip_symm := fun F _ E _ => by rw [ipTh_eq, ipTh_eq, ipO_conj]
  ip_pos := fun F hF hne => by
    have htheta : IsThetaFunO ψ S T F := hF
    have hc : Continuous F := htheta.cont
    have h0 : GlobalTheory.Ker.ipO μ 𝓕 F F ≠ 0 := fun h => hne ((ipO_self_eq_zero_iff hω.std hμ h𝓕 hF).1 h)
    rw [ipO_self, sqNormIntegralFundamentalDomain_eq_l2Norm_sq μ 𝓕 hc] at h0
    rw [ipTh_eq, ipO_self, sqNormIntegralFundamentalDomain_eq_l2Norm_sq μ 𝓕 hc, Complex.ofReal_re]
    exact lt_of_le_of_ne (sq_nonneg _) (fun h => h0 (by rw [← h]; simp))
  stable := fun g _ F hF => hω.om_pres _ F hF
  lin := fun g _ z F _ F' _ => by simp only [map_add (f := _), map_smul]
  one := fun F _ => by
    show ω (γ 1) F = F
    rw [h1, map_one]
    rfl
  mul := fun g hg g' hg' F _ => by
    show ω (γ (g * g')) F = ω (γ g) (ω (γ g') F)
    rw [hmul g hg g' hg', map_mul]
    rfl
  unit := fun g _ F hF E hE => by
    show ipTh μ 𝓕 (ω (γ g) F) (ω (γ g) E) = ipTh μ 𝓕 F E
    rw [ipTh_eq, ipTh_eq, ipO_om hω hμ h𝓕 hF hE (γ g)]
  cont := fun F hF E hE => by
    have : FirstCountableTopology (Mn n) :=
      inferInstanceAs (FirstCountableTopology (Fin n → Fin n → ℂ))
    exact continuousOn_ip hω hμ h𝓕 hc hF hE
  der := fun X hX P P' hPP' E hE => by
    obtain ⟨F', hF'1, hF'2⟩ := hd X hX P
    have heq : F' = pt P' := by
      funext z
      have hz := hF'1 1 z
      simp only [one_mul, map_one, one_apply_eq_self] at hz
      exact hz.unique (hPP' z)
    have hder := hF'2 μ 𝓕 hμ h𝓕 E hE
    rw [heq] at hder
    exact hder }

theorem exists_l2_unitary_theta_of_fundamentalDomain : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (τ : D.what₂.Tau), IsInfFam θ → IsWeilDatumO ψ S T χS χT ω → ∀ (frS : Mn S.rank) (εS : Fin S.rank → Bool) (frT : Mn T.rank) (εT : Fin T.rank → Bool) (aS aT : ℚ) (pt : LPol T.rank S.rank →ₗ[ℂ] (WO S T → ℂ)), (∀ P, IsThetaFunO ψ S T (pt P)) → LieAt ψ θ τ ω εS frS εT frT aS aT pt → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∃ Θ, L2UnitaryRepresentationData (gramAt D S τ) (actSrc θ ω τ) pt (ipTh μ 𝓕) Θ ∧ L2UnitaryRepresentationData (gramAt D T τ) (actTgt θ ω τ) pt (ipTh μ 𝓕) Θ := by
  intro D ψ θ S T χS χT ω τ hθ hω frS εS frT εT aS aT pt hpt hL μ 𝓕 hμ h𝓕
  refine ⟨thetaSpace ψ S T, ?_, ?_⟩
  · have hcS := GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ S τ
    exact weaklyContinuous_unitaryAction_of_realUnitaryHom hω hμ h𝓕 (gramAt D S τ) (fun g => (atTau θ S τ g, (1 : GA D T)))
      (by rw [GlobalTheory.PointAtPlaceHom.atTau_one hθ S τ]; rfl)
      (fun g hg g' hg' => by
        rw [GlobalTheory.PointAtPlaceHom.atTau_mul hθ S τ hg hg', Prod.mk_mul_mk, one_mul])
      (by fun_prop) pt hpt (fun X hX P => ⟨_, hL.1 X hX P⟩)
  · have hcT := GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ T τ
    exact weaklyContinuous_unitaryAction_of_realUnitaryHom hω hμ h𝓕 (gramAt D T τ) (fun h => ((1 : GA D S), atTau θ T τ h))
      (by rw [GlobalTheory.PointAtPlaceHom.atTau_one hθ T τ]; rfl)
      (fun h hh h' hh' => by
        rw [GlobalTheory.PointAtPlaceHom.atTau_mul hθ T τ hh hh', Prod.mk_mul_mk, one_mul])
      (by fun_prop) pt hpt (fun Y hY P => ⟨_, hL.2 Y hY P⟩)

end GlobalTheory.ThetaL2InnerProduct

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rowLevelMatchAt_of_levelConjugation : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∀ (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (t : GA D (Yc D 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∃ (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1), (∀ kv, ((plg kv : R.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) ∧ (∀ g, D.what₂.embLL ((idemOf A.X).coeff g) = D.ntypes.e0.coeff ((R.eG.trans cG) g)) ∧ (∀ kv, R.C.P.Div kv.1 (plg kv).1) ∧ ∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) ((R.eG.trans cG) g kv)) → IdempotentRealFixed D → t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → IsFrame (finE (Yc D 0) t * R.βY 0) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → RowLevelMatchAt R F X h t := by
  first | exact @GlobalTheory.rowLevelMatchAt_of_conjLevel | exact GlobalTheory.rowLevelMatchAt_of_conjLevel | (intros; apply GlobalTheory.rowLevelMatchAt_of_conjLevel <;> assumption)
end
