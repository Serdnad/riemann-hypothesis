module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1284
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1286
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1287
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1288
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1289
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1292
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1290
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1319
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1291
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle704
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDecay
open scoped TensorProduct NNReal Matrix

noncomputable section

namespace GlobalTheory.WeilDirBound

open GlobalTheory.AdelicU

theorem norm_entry_le_opNorm {m : Type} [Fintype m] [DecidableEq m] (A : Matrix m m ℂ) (i k : m) :
    ‖A i k‖ ≤ (opNorm A : ℝ) := by
  have h1 : Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ) A (EuclideanSpace.single k 1) =
      WithLp.toLp 2 (A *ᵥ Pi.single k 1) := Matrix.toEuclideanCLM_toLp A _
  have h2 : (A *ᵥ Pi.single k (1 : ℂ)) i = A i k := by simp
  calc ‖A i k‖ = ‖(Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ) A (EuclideanSpace.single k 1)).ofLp i‖ := by
        rw [h1, ← h2]
    _ ≤ ‖Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ) A (EuclideanSpace.single k 1)‖ := PiLp.norm_apply_le _ _
    _ ≤ ‖Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ) A‖ * ‖EuclideanSpace.single k (1 : ℂ)‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ = (opNorm A : ℝ) := by simp [opNorm]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem norm_piInf_entry_le_heightGL {m : Type} [Fintype m] [DecidableEq m] (g : GL m (AF F ⊗[F] E))
    (w : InfinitePlace F) (τ : EmbOver E w) (i k : m) :
    ‖piInf τ ((g : Matrix m m (AF F ⊗[F] E)) i k)‖ ≤ (heightGL F g : ℝ) := by
  have e : piInf τ ((g : Matrix m m (AF F ⊗[F] E)) i k) =
      (((Formalism.UG.bc (compInf F E w) g : GL m (w.Completion ⊗[F] E)) : Matrix m m _).map (infEmb τ)) i k := rfl
  rw [e]
  refine (norm_entry_le_opNorm _ i k).trans ?_
  have h1 : opNorm (((Formalism.UG.bc (compInf F E w) g : GL m (w.Completion ⊗[F] E)) : Matrix m m _).map (infEmb τ))
      ≤ heightGL F g := by
    refine ((normInf_le_iff F w).1 le_rfl τ).trans ((le_htOf _ _).trans ?_)
    refine le_trans ?_ (le_mul_of_one_le_right' (one_le_finprod' fun _ => one_le_htOf _ _))
    exact Finset.single_le_prod' (f := fun w => htInf F w (Formalism.UG.bc (compInf F E w) g))
      (fun _ _ => one_le_htOf _ _) (Finset.mem_univ w)
  exact_mod_cast h1

end GlobalTheory.WeilDirBound

end

namespace GlobalTheory.WeilDirBound

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem norm_piInf_actAB_le (σ : E →ₐ[F] E) (n d : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (J' : Matrix (Fin d) (Fin d) E) (p : UA σ J × UA σ J')
    (x : Matrix (Fin n) (Fin d) (AE F E)) (B : ℝ) (hB : 0 ≤ B)
    (hx : ∀ (w : InfinitePlace F) (τ : EmbOver E w) k l, ‖piInf τ (x k l)‖ ≤ B) :
    ∀ (w : InfinitePlace F) (τ : EmbOver E w) i j,
      ‖piInf τ (actAB (cA σ) p x i j)‖ ≤ n * d * ((ht p.1 : ℝ) * ht p.2) * B := by
  intro w τ i j
  set g : GL (Fin n) (AF F ⊗[F] E) := (p.1 : GL (Fin n) (AF F ⊗[F] E)) with hg
  set h : GL (Fin d) (AF F ⊗[F] E) := (p.2 : GL (Fin d) (AF F ⊗[F] E)) with hh
  have hg1 : (ht p.1 : ℝ) = heightGL F g := rfl
  have hh1 : (ht p.2 : ℝ) = heightGL F h := rfl
  have e : actAB (cA σ) p x i j = ∑ l, ∑ k,
      (g : Matrix (Fin n) (Fin n) _) i k * x k l * (h : Matrix (Fin d) (Fin d) _) j l := by
    simp only [actAB, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    rfl
  have hG := fun k => norm_piInf_entry_le_heightGL g w τ i k
  have hH := fun l => norm_piInf_entry_le_heightGL h w τ j l
  have hG0 : (0 : ℝ) ≤ heightGL F g := NNReal.coe_nonneg _
  have hH0 : (0 : ℝ) ≤ heightGL F h := NNReal.coe_nonneg _
  rw [e, hg1, hh1]
  calc ‖piInf τ (∑ l, ∑ k, (g : Matrix (Fin n) (Fin n) _) i k * x k l * (h : Matrix (Fin d) (Fin d) _) j l)‖
      ≤ ∑ l : Fin d, ∑ k : Fin n, ((heightGL F g : ℝ) * heightGL F h * B) := by

        rw [map_sum]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)

        rw [map_sum]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
        rw [map_mul, map_mul, norm_mul, norm_mul]
        calc ‖piInf τ ((g : Matrix (Fin n) (Fin n) _) i k)‖ * ‖piInf τ (x k l)‖ *
              ‖piInf τ ((h : Matrix (Fin d) (Fin d) _) j l)‖
            ≤ (heightGL F g : ℝ) * B * heightGL F h :=
              mul_le_mul (mul_le_mul (hG k) (hx w τ k l) (norm_nonneg _) hG0) (hH l) (norm_nonneg _)
                (mul_nonneg hG0 hB)
          _ = (heightGL F g : ℝ) * heightGL F h * B := by ring
    _ = n * d * ((heightGL F g : ℝ) * heightGL F h) * B := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end GlobalTheory.WeilDirBound
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.MixedLagr
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.MixedLagrGram

theorem hTens_eq_trace {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
    {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α β E) :
    hTens c JA JB x y = Matrix.trace (xᵀ * JA * y.map c * JBᵀ) := by
  simp only [hTens, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  conv_rhs => enter [2, j, 2, l]; rw [Finset.sum_comm]
  conv_rhs => enter [2, j]; rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem hTens_restrict {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
    {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
    (JA : Matrix α α E) (JB : Matrix β β E) (JB₁ : Matrix γ γ E) (ι : Matrix β γ E)
    (h : ιᵀ * JB * ι.map c = JB₁) (z z' : Matrix α γ E) :
    hTens c JA JB (z * ιᵀ) (z' * ιᵀ) = hTens c JA JB₁ z z' := by
  rw [hTens_eq_trace, hTens_eq_trace, ← h, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.map_mul, Matrix.transpose_map]
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem incM_map_cA {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {m k : Type} (J : Matrix m k E) :
    (incM F J).map (cA σ) = incM F (J.map σ) := by
  ext i j
  simp [incM, cA, inclR]

theorem symp_restrict_gram : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n d d₁ : ℕ) (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E) (JW₁ : Matrix (Fin d₁) (Fin d₁) E)
    (ι : Matrix (Fin d) (Fin d₁) E), ιᵀ * JW * ι.map σ = JW₁ → ∀ z z' : Matrix (Fin n) (Fin d₁) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      symp (cA σ) (-1) (incM F JX) (incM F JW) (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F ι)ᵀ)
        (incM F (1 : Matrix (Fin n) (Fin n) E) * z' * (incM F ι)ᵀ) = symp (cA σ) (-1) (incM F JX) (incM F JW₁) z z' := by
  intro F E _ _ _ _ _ σ n d d₁ JX JW JW₁ ι h z z'
  have hA : (incM F ι)ᵀ * incM F JW * (incM F ι).map (cA σ) = incM F JW₁ := by
    rw [incM_map_cA, ← h]
    simp only [incM, Matrix.map_mul, Matrix.transpose_map]
  have h1 : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := by
    simp only [incM, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [h1, Matrix.one_mul, Matrix.one_mul]
  simp only [symp]
  rw [hTens_restrict _ _ _ _ _ hA]

end GlobalTheory.MixedLagrGram
end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnipMass

namespace GlobalTheory.RatUDiscreteSub

theorem discreteTopology_subgroupOf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (N : Subgroup (UA σ J)),
    DiscreteTopology ((ratU σ J).subgroupOf N) := by
  intro F E _ _ _ _ _ σ n J N
  haveI := GlobalTheory.RatUDiscrete.discreteTopology_ratU F E σ n J
  let φ : (ratU σ J).subgroupOf N → ratU σ J := fun x => ⟨x.1.1, Subgroup.mem_subgroupOf.1 x.2⟩
  have h2 : Topology.IsEmbedding (fun x : (ratU σ J).subgroupOf N => ((x : N) : UA σ J)) :=
    Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
  have hφ : Topology.IsEmbedding φ :=
    (Topology.IsEmbedding.of_comp_iff (Topology.IsEmbedding.subtypeVal (p := fun x : UA σ J => x ∈ ratU σ J))).1 h2
  exact hφ.discreteTopology

end GlobalTheory.RatUDiscreteSub
end

section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl


theorem _root_.GlobalTheory.T.norm_extensionAdeles_eq_one_of_mul_conj_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), z * cA σ z = 1 → Algebra.norm (AF F) z = 1 := by
  first | exact @GlobalTheory.NormOne.norm_eq_one | exact GlobalTheory.NormOne.norm_eq_one | (intros; apply GlobalTheory.NormOne.norm_eq_one <;> assumption)
end

section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

theorem _root_.GlobalTheory.T.realScalarArchimedeanAdele_smul_matrix_realPlace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {α β : Type}
    (τ : ∀ w : InfinitePlace F, EmbOver E w), IsCMExt F E σ →
    ∀ (u : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (r : ℝ) (w : InfinitePlace F),
      (realAd F r • u).map (piInf (τ w)) = (r : ℂ) • u.map (piInf (τ w)) := by
  first | exact @GlobalTheory.RealScalar.realAd_smul_map | exact GlobalTheory.RealScalar.realAd_smul_map | (intros; apply GlobalTheory.RealScalar.realAd_smul_map <;> assumption)
end

section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

theorem _root_.GlobalTheory.T.weil_operator_unitary_adelic_L2 : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (L : SInf F κ →ₗ[ℂ] SInf F κ) (Ω : Module.End ℂ ((κ → AF F) → ℂ)),
    (∀ (f : SInf F κ) (h : (κ → Af F) → ℂ), Ω (pureA F f h) = pureA F (L f) h) →
    (∀ ν : Measure (κ → mixedEmbedding.mixedSpace F), ν.IsAddHaarMeasure → ∀ f₁ f₂ : SInf F κ,
      ∫ x, star (L f₁ x) * L f₂ x ∂ν = ∫ x, star (f₁ x) * f₂ x ∂ν) →
    ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ φ ∈ schA F κ, ∫⁻ x, ‖Ω φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ := by
  first | exact @GlobalTheory.ArchimedeanL2.lintegral_arch_eq | exact GlobalTheory.ArchimedeanL2.lintegral_arch_eq | (intros; apply GlobalTheory.ArchimedeanL2.lintegral_arch_eq <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical

theorem _root_.GlobalTheory.T.adelicThetaSum_norm_le_polynomial_scale : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∃ (N₀ k : ℕ) (C : ℝ), ∀ (A : ℝ) (m : ℕ) (Ψ : (κ → AF F) → ℂ), 1 ≤ m →
    (∀ ξ : κ → F, ‖Ψ (fun i => algebraMap F (AF F) (ξ i))‖ * (1 + ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖) ^ N₀ ≤ A) →
    (∀ ξ : κ → F, Ψ (fun i => algebraMap F (AF F) (ξ i)) ≠ 0 → ∀ i, IsIntegral ℤ ((m : F) * ξ i)) →
    ‖thetaSum F Ψ‖ ≤ C * A * (m : ℝ) ^ k := by
  first | exact @GlobalTheory.LatScaleSum.thetaSum_norm_le_pow | exact GlobalTheory.LatScaleSum.thetaSum_norm_le_pow | (intros; apply GlobalTheory.LatScaleSum.thetaSum_norm_le_pow <;> assumption)
end

section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl


theorem _root_.GlobalTheory.T.archimedeanSchwartz_integral_mul_star_ne_zero : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (f : SInf F κ), f ≠ 0 →
    (∫ x : κ → mixedEmbedding.mixedSpace F, f x * star (f x)) ≠ 0 := by
  first | exact @GlobalTheory.L2InnerProductNonvanishing.integral_mul_star_ne_zero | exact GlobalTheory.L2InnerProductNonvanishing.integral_mul_star_ne_zero | (intros; apply GlobalTheory.L2InnerProductNonvanishing.integral_mul_star_ne_zero <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Matrix

theorem _root_.GlobalTheory.T.good_models_differ_by_symplectic_matrix : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (ψ : AddChar (AF F) ℂ) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M M₁ : Model σ X W), M.IsGood ψ → M₁.IsGood ψ → ∃ a : Matrix ((Fin n × Fin d) ⊕ (Fin n × Fin d)) ((Fin n × Fin d) ⊕ (Fin n × Fin d)) F, aᵀ * Matrix.fromBlocks 0 1 (-1) 0 * a = Matrix.fromBlocks 0 1 (-1) 0 ∧ ∀ u, M₁.co.e u = ((a.map (algebraMap F (AF F)) *ᵥ Sum.elim (M.co.e u).1 (M.co.e u).2) ∘ Sum.inl, (a.map (algebraMap F (AF F)) *ᵥ Sum.elim (M.co.e u).1 (M.co.e u).2) ∘ Sum.inr) := by
  first | exact @GlobalTheory.goodModel_coords_rat_symplectic | exact GlobalTheory.goodModel_coords_rat_symplectic | (intros; apply GlobalTheory.goodModel_coords_rat_symplectic <;> assumption)
end

section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

theorem _root_.GlobalTheory.T.heisenbergRho_split_archimedean_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (α β κ : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (ψ : AddChar (AF F) ℂ)
    (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ),
    ∀ w : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
    ∃ (u : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (H : ((κ → Af F) → ℂ) → (κ → Af F) → ℂ), At (evI F) u ∧
      ∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1) →
        ∀ (f f₁ : SInf F κ) (h : (κ → Af F) → ℂ),
          (∀ h' : (κ → Af F) → ℂ, d.rho ψ (actB (cA σ) g u) (pureA F f h') = pureA F f₁ h') →
            d.rho ψ (actB (cA σ) g w) (pureA F f h) = pureA F f₁ (H h) := by
  first | exact @GlobalTheory.HeisSplit.rho_split | exact GlobalTheory.HeisSplit.rho_split | (intros; apply GlobalTheory.HeisSplit.rho_split <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

theorem _root_.GlobalTheory.T.tensorCartanInvolution_invariant_and_positive : ∀ (n d : ℕ) (JX θX : Matrix (Fin n) (Fin n) ℂ) (JW θW : Matrix (Fin d) (Fin d) ℂ),
    (∀ i j, star (JX j i) = JX i j) → IsCartan JX θX → (∀ i j, star (JW j i) = -JW i j) → IsCartan (Complex.I • JW) θW →
    ∀ x y : Matrix (Fin n) (Fin d) ℂ,
      (∑ i, ∑ j, ∑ k, ∑ l, (Complex.I • (θX * x * θWᵀ)) i j * JX i k * JW j l * star ((Complex.I • (θX * y * θWᵀ)) k l)) =
        (∑ i, ∑ j, ∑ k, ∑ l, x i j * JX i k * JW j l * star (y k l)) ∧
      (x ≠ 0 → 0 < -(∑ i, ∑ j, ∑ k, ∑ l, x i j * JX i k * JW j l * star ((Complex.I • (θX * x * θWᵀ)) k l)).re) := by
  first | exact @GlobalTheory.CartanTensor.tensor_cartan_invariant_pos | exact GlobalTheory.CartanTensor.tensor_cartan_invariant_pos | (intros; apply GlobalTheory.CartanTensor.tensor_cartan_invariant_pos <;> assumption)
end

section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl


theorem _root_.GlobalTheory.T.heisenberg_derivative_on_schwartz_tensor_conj : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a₁ b₁ a₂ b₂ : κ → AF F)
    (f g₁ g₂ : SInf F κ) (f₀ h : SInf F (κ ⊕ κ)),
    (∀ y, g₁ y = fderiv ℝ f y (fun i => evI F (a₁ i)) - 2 * Real.pi * Complex.I *
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, y i * evI F (b₁ i)) : ℝ) * f y) →
    (∀ y, g₂ y = fderiv ℝ f y (fun i => evI F (a₂ i)) - 2 * Real.pi * Complex.I *
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, y i * evI F (b₂ i)) : ℝ) * f y) →
    (∀ x, h x = fderiv ℝ f₀ x (fun i => evI F (Sum.elim a₁ a₂ i)) - 2 * Real.pi * Complex.I *
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * evI F (Sum.elim b₁ (-b₂) i)) : ℝ) * f₀ x) →
    (∀ x, f₀ x = f (x ∘ Sum.inl) * star (f (x ∘ Sum.inr))) → ∀ x : κ ⊕ κ → mixedEmbedding.mixedSpace F,
    h x = g₁ (x ∘ Sum.inl) * star (f (x ∘ Sum.inr)) + f (x ∘ Sum.inl) * star (g₂ (x ∘ Sum.inr)) := by
  first | exact @GlobalTheory.heisenbergDeriv_tensor_conj | exact GlobalTheory.heisenbergDeriv_tensor_conj | (intros; apply GlobalTheory.heisenbergDeriv_tensor_conj <;> assumption)
end
