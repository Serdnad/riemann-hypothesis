module

public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle068
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IdealCharacterLSeriesContinuation
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle065
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.PicardGroup
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
import Formalism.LocalToGlobal.IndefiniteReal.SelfDualFullLattice

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatOpen

open GlobalTheory.LatVac Topology

theorem isOpen_of_nhds {G G' : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [AddCommGroup G'] (φ : G →+ G') (L : AddSubgroup G) (N : ℕ) (U : Set G) (hU : U ∈ 𝓝 0)
    (h : ∀ x ∈ U, ∃ l ∈ L, φ (x - N • l) = 0) : IsOpen {x : G | ∃ l ∈ L, φ (x - N • l) = 0} := by
  let H : AddSubgroup G :=
    { carrier := {x : G | ∃ l ∈ L, φ (x - N • l) = 0}
      zero_mem' := ⟨0, L.zero_mem, by simp⟩
      add_mem' := by
        rintro x y ⟨l, hl, e⟩ ⟨l', hl', e'⟩
        refine ⟨l + l', L.add_mem hl hl', ?_⟩
        rw [show x + y - N • (l + l') = (x - N • l) + (y - N • l') by rw [nsmul_add]; abel, map_add (f := _), e, e', add_zero]
      neg_mem' := by
        rintro x ⟨l, hl, e⟩
        refine ⟨-l, L.neg_mem hl, ?_⟩
        rw [show -x - N • (-l) = -(x - N • l) by rw [neg_nsmul]; abel, map_neg, e, neg_zero] }
  exact H.isOpen_of_mem_nhds (g := 0) (Filter.mem_of_superset hU h)

theorem isOpen_intAf (F : Type) [Field F] [NumberField F] : IsOpen (intAf F) :=
  RestrictedProduct.isOpen_forall_mem (A := fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    fun v => Valued.isOpen_valuationSubring _

theorem zero_mem_intAf (F : Type) [Field F] [NumberField F] : (0 : Af F) ∈ intAf F :=
  fun v => zero_mem (v.adicCompletionIntegers F)

variable {D : D7}

theorem finPart_eq_sum {ι : Type} [Fintype ι] (b : Module.Basis ι D.host.F D.host.E) (z : AE D) :
    finPart D z = ∑ k, sndA D.host.F ((Algebra.TensorProduct.basis (AF D.host.F) b).coord k z) ⊗ₜ[D.host.F] b k := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis (AF D.host.F) b).sum_repr z]

  rw [show ∀ y, finPart D y = (finPart D).toAddMonoidHom y from fun _ => rfl, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  show finPart D _ = _
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rfl

theorem nsmul_tmul_cancel {F A E : Type} [Field F] [CharZero F] [CommRing A] [Algebra F A] [AddCommGroup E] [Module F E]
    {N M : ℕ} (hN : 0 < N) (hM : 0 < M) (a : A) (e : E) :
    N • ((algebraMap F A ((N * M : ℕ) : F)⁻¹ * a) ⊗ₜ[F] (M • e)) = a ⊗ₜ[F] e := by
  have hN' : (N : F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hM' : (M : F) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  rw [← Algebra.smul_def, ← Nat.cast_smul_eq_nsmul F, ← Nat.cast_smul_eq_nsmul F, TensorProduct.tmul_smul,
    ← TensorProduct.smul_tmul', smul_smul, smul_smul, Nat.cast_mul, mul_inv_cancel₀ (mul_ne_zero hN' hM'), one_smul]

private theorem selfDual_isFullLattice {D : D7} : ∀ (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
    IsSelfDualC V Λ → Submodule.IsFullLattice D.host.E Λ := by
  intro V Λ hΛ
  exact Formalism.IndefR.Datum.IsSelfDualC.isFullLattice V Λ hΛ


theorem isOpen_nsmul_latO : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ N : ℕ, 0 < N → IsOpen {x : WO S T | ∃ l ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), (x - N • l).map (finPart D) = 0} := by
  intro D S T ΛS ΛT hS hT N hN
  classical
  let b := Module.finBasis D.host.F D.host.E
  let B := Algebra.TensorProduct.basis (AF D.host.F) b
  choose M hM hMl using fun p : Fin T.rank × Fin S.rank × Fin (Module.finrank D.host.F D.host.E) =>
    GlobalTheory.T.scaled_matrix_mem_rational_lattice D S T ΛS ΛT (selfDual_isFullLattice S ΛS hS) (selfDual_isFullLattice T ΛT hT) (Matrix.single p.1 p.2.1 (b p.2.2))
  let f : Fin T.rank × Fin S.rank × Fin (Module.finrank D.host.F D.host.E) → WO S T → Af D.host.F := fun p x =>
    algebraMap D.host.F (Af D.host.F) ((N * M p : ℕ) : D.host.F)⁻¹ * sndA D.host.F (B.coord p.2.2 (x p.1 p.2.1))
  have hf : ∀ p, Continuous (f p) := fun p => by
    have h1 : Continuous (B.coord p.2.2) := IsModuleTopology.continuous_of_linearMap _
    have h2 : Continuous (sndA D.host.F) := continuous_snd
    exact continuous_const.mul (h2.comp (h1.comp ((continuous_apply p.2.1).comp (continuous_apply p.1))))
  have hf0 : ∀ p, f p 0 = 0 := fun p => by
    show _ * sndA D.host.F (B.coord p.2.2 0) = 0
    rw [LinearMap.map_zero, map_zero, mul_zero]
  let φ : WO S T →+ Matrix (Fin T.rank) (Fin S.rank) (Af D.host.F ⊗[D.host.F] D.host.E) :=
    (finPart D).toAddMonoidHom.mapMatrix
  refine isOpen_of_nhds φ _ N (⋂ p, f p ⁻¹' intAf D.host.F) ?_ ?_
  · refine Filter.iInter_mem.2 fun p => ((isOpen_intAf _).preimage (hf p)).mem_nhds ?_
    show f p 0 ∈ intAf D.host.F
    rw [hf0]; exact zero_mem_intAf _
  · intro x hx
    refine ⟨∑ p, finTens (f p x) (M p • Matrix.single p.1 p.2.1 (b p.2.2)),
      AddSubgroup.sum_mem _ fun p _ => finTens_mem_latO (Set.mem_iInter.1 hx p) (hMl p), ?_⟩

    rw [AddMonoidHom.map_sub, AddMonoidHom.map_nsmul, sub_eq_zero, map_sum, ← Finset.sum_nsmul]
    ext i j
    rw [Matrix.sum_apply]
    have e : ∀ p : Fin T.rank × Fin S.rank × Fin (Module.finrank D.host.F D.host.E),
        (N • φ (finTens (f p x) (M p • Matrix.single p.1 p.2.1 (b p.2.2)))) i j =
        sndA D.host.F (B.coord p.2.2 (x p.1 p.2.1)) ⊗ₜ[D.host.F] (Matrix.single p.1 p.2.1 (b p.2.2) i j) :=
      fun p => nsmul_tmul_cancel hN (hM p) _ _
    rw [Finset.sum_congr rfl fun p _ => e p, Fintype.sum_prod_type, Finset.sum_eq_single i, Fintype.sum_prod_type,
      Finset.sum_eq_single j]
    · simp only [Matrix.single_apply_same]
      exact finPart_eq_sum b (x i j)
    · intro j' _ hj
      exact Finset.sum_eq_zero fun k _ => by
        rw [Matrix.single_apply_of_col_ne _ _ hj, TensorProduct.tmul_zero]
    · simp
    · intro i' _ hi
      exact Finset.sum_eq_zero fun k _ => by
        rw [Matrix.single_apply_of_row_ne hi, TensorProduct.tmul_zero]
    · simp

end GlobalTheory.LatOpen

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeisOrtho

open GlobalTheory.SplitScalar

theorem setIntegral_add_right {G E : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [NormedAddCommGroup E] [NormedSpace ℝ E] (Γ : AddSubgroup G) [Countable Γ]
    (μ : Measure G) [μ.IsAddHaarMeasure] (𝓕 : Set G) (h𝓕 : IsAddFundamentalDomain Γ 𝓕 μ) (h : G → E)
    (hp : ∀ γ ∈ Γ, ∀ w, h (γ + w) = h w) (u : G) : ∫ w in 𝓕, h (w + u) ∂μ = ∫ w in 𝓕, h w ∂μ := by
  have h1 : IsAddFundamentalDomain Γ (u +ᵥ 𝓕) μ := h𝓕.vadd_of_comm u
  rw [h𝓕.setIntegral_eq h1 (f := h) fun γ w => hp γ γ.2 w]
  have h2 := (measurePreserving_add_left μ u).setIntegral_image_emb (measurableEmbedding_addLeft u) h 𝓕
  simp only [add_comm _ u]
  exact h2.symm

theorem integral_norm_sq_sum {X ι : Type} [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν] (s : Finset ι)
    (g : ι → X → ℂ) (c : ι → ℂ) (C : ℝ) (hm : ∀ i, Measurable (g i)) (hC : ∀ i x, ‖g i x‖ ≤ C)
    (hc : ∀ i ∈ s, ‖c i‖ = 1) (h1 : ∀ i ∈ s, ∫ x, ‖g i x‖ ^ 2 ∂ν = 1)
    (h0 : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∫ x, g i x * (starRingEnd ℂ) (g j x) ∂ν = 0) :
    ∫ x, ‖(∑ i ∈ s, c i • g i) x‖ ^ 2 ∂ν = (s.card : ℝ) := by
  classical
  have hi : ∀ i j, Integrable (fun x => g i x * (starRingEnd ℂ) (g j x)) ν := fun i j => by
    refine Integrable.of_bound (((hm i).mul (Complex.continuous_conj.measurable.comp (hm j))).aestronglyMeasurable)
      (C * C) (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (hC i x) (hC j x) (norm_nonneg _) ((norm_nonneg _).trans (hC i x))
  have e : ∀ x, ((‖(∑ i ∈ s, c i • g i) x‖ ^ 2 : ℝ) : ℂ) =
      ∑ i ∈ s, ∑ j ∈ s, (c i * (starRingEnd ℂ) (c j)) * (g i x * (starRingEnd ℂ) (g j x)) := fun x => by

    rw [Complex.ofReal_pow, ← Complex.mul_conj', Finset.sum_apply, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    ring
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [e]
  rw [integral_finsetSum (f := fun i x => ∑ j ∈ s, c i * (starRingEnd ℂ) (c j) *
      (g i x * (starRingEnd ℂ) (g j x))) _
      (fun i _ => integrable_finsetSum _ fun j _ => (hi i j).const_mul _),
    Finset.card_eq_sum_ones]
  push_cast
  refine Finset.sum_congr rfl fun i hi' => ?_
  rw [integral_finsetSum (f := fun j x => c i * (starRingEnd ℂ) (c j) *
      (g i x * (starRingEnd ℂ) (g j x))) _ (fun j _ => (hi i j).const_mul _),
    Finset.sum_eq_single i]
  · rw [integral_const_mul, Complex.mul_conj', hc i hi']
    simp_rw [Complex.mul_conj', ← Complex.ofReal_pow]
    rw [integral_complex_ofReal, h1 i hi']
    simp
  · intro j hj hji
    rw [integral_const_mul, h0 i hi' j hj hji.symm, mul_zero]
  · exact fun h => absurd hi' h

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem heisO_quasi {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (u : WO S T) (γ : WO S T) (hγ : γ ∈ ratL T S)
    (w : WO S T) : heisO ψ S T u f (γ + w) = ψ (-(symplOH S T γ w)) * heisO ψ S T u f w := by
  obtain ⟨γ, rfl⟩ := hγ
  have h := hf.quasi γ (w + u)
  show ψ (symplOH S T (ratW T S γ + w) u) * f (ratW T S γ + w + u) =
    ψ (-(symplOH S T (ratW T S γ) w)) * (ψ (symplOH S T w u) * f (w + u))
  rw [add_assoc, h, ← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul,
    symplOH_add_left, symplOH_add_right]
  congr 2
  abel

theorem continuous_heisO (hψ : IsCharAF D.host.F ψ) {f : WO S T → ℂ} (hf : Continuous f) (u : WO S T) :
    Continuous (heisO ψ S T u f) :=
  (hψ.1.comp (continuous_const.mul (continuous_symplO S T continuous_id continuous_const))).mul
    (hf.comp (continuous_id.add continuous_const))

theorem norm_heisO (hψ : IsCharAF D.host.F ψ) (f : WO S T → ℂ) (u w : WO S T) :
    ‖heisO ψ S T u f w‖ = ‖f (w + u)‖ := by
  rw [heisO, norm_mul, hψ.2.1, one_mul]

theorem mul_conj_of_norm_one {z : ℂ} (h : ‖z‖ = 1) : z * (starRingEnd ℂ) z = 1 := by
  rw [Complex.mul_conj', h]; simp

theorem thetaNormSq_sum_heisenbergTranslates_distinctChars (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (hψ : IsCharAF D.host.F ψ)
    (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) (hμ : IsCovolOne (ratL T S) μ 𝓕) (f : WO S T → ℂ)
    (hf : IsThetaFunO ψ S T f) (hn : nrm2 μ 𝓕 f = 1) (ι : Type) (s : Finset ι) (a : ι → WO S T) (c : ι → ℂ)
    (hc : ∀ i ∈ s, ‖c i‖ = 1)
    (hl : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∃ (l : WO S T) (ε : ℂ), ‖ε‖ = 1 ∧ heisO ψ S T l f = ε • f ∧
      ψ (symplO S T (a i - a j) l) ≠ 1) :
    nrm2 μ 𝓕 (∑ i ∈ s, c i • heisO ψ S T (a i) f) = (s.card : ℝ) := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  obtain ⟨hμ, h𝓕, h1⟩ := hμ
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : Countable (ratL T S) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
  have hp : ∀ γ ∈ ratL T S, ∀ w, ‖f (γ + w)‖ = ‖f w‖ := by
    rintro _ ⟨γ, rfl⟩ w
    exact (congrArg norm (hf.quasi γ w)).trans (by rw [norm_mul, hψ.2.1, one_mul])
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.cont.continuousOn
  have hC' : ∀ w, ‖f w‖ ≤ C := fun w => by
    obtain ⟨γ, hγ, h⟩ := hKc w
    rw [← hp γ hγ w]
    exact hC _ h
  refine integral_norm_sq_sum (μ.restrict 𝓕) s (fun i => heisO ψ S T (a i) f) c C
    (fun i => (continuous_heisO hψ hf.cont _).measurable) (fun i x => by rw [norm_heisO hψ]; exact hC' _) hc
    (fun i _ => ?_) fun i hi j hj hij => ?_
  · simp_rw [norm_heisO hψ]
    exact (setIntegral_add_right (G := WO S T) (ratL T S) μ 𝓕 h𝓕 (fun w => ‖f w‖ ^ 2)
      (fun γ hγ w => by simp only [hp γ hγ w]) (a i)).trans hn
  · obtain ⟨l, ε, hε, he, hne⟩ := hl i hi j hj hij
    have ev : ∀ b w, ψ (symplOH S T w l) * heisO ψ S T b f (w + l) =
        ψ (symplO S T l b) * (ε * heisO ψ S T b f w) := fun b w => by
      have := congrFun (heisO_comm ψ S T l b f) w
      rw [he, heisO_smul] at this
      exact this
    have key := setIntegral_add_right (G := WO S T) (ratL T S) μ 𝓕 h𝓕
      (fun w => heisO ψ S T (a i) f w * (starRingEnd ℂ) (heisO ψ S T (a j) f w)) (fun γ hγ w => by
        have := mul_conj_of_norm_one (hψ.2.1 (-(symplOH S T γ w)))
        simp only [heisO_quasi hf _ γ hγ, map_mul]
        linear_combination (heisO ψ S T (a i) f w * (starRingEnd ℂ) (heisO ψ S T (a j) f w)) * this) l
    have hκ : ψ (symplO S T (a i - a j) l) * (ψ (symplO S T l (a i)) * (starRingEnd ℂ) (ψ (symplO S T l (a j)))) = 1 := by
      rw [← mul_assoc, ← AddChar.map_add_eq_mul, symplO_sub_left, symplO_skew S T l (a i), symplO_skew S T l (a j),
        show -symplO S T l (a i) - -symplO S T l (a j) + symplO S T l (a i) = symplO S T l (a j) by abel]
      exact mul_conj_of_norm_one (hψ.2.1 _)
    have e : ∀ w, heisO ψ S T (a i) f w * (starRingEnd ℂ) (heisO ψ S T (a j) f w) =
        ψ (symplO S T (a i - a j) l) *
          (heisO ψ S T (a i) f (w + l) * (starRingEnd ℂ) (heisO ψ S T (a j) f (w + l))) := fun w => by
      have e1 := mul_conj_of_norm_one (hψ.2.1 (symplOH S T w l))
      have e2 := mul_conj_of_norm_one hε
      have e3 := ev (a i) w
      have e4 := congrArg (starRingEnd ℂ) (ev (a j) w)
      rw [map_mul, map_mul, map_mul] at e4
      have e5 := congrArg₂ (· * ·) e3 e4
      rw [mul_mul_mul_comm, e1, one_mul] at e5
      rw [e5, mul_mul_mul_comm (ψ _), ← mul_assoc, hκ, one_mul, mul_mul_mul_comm, e2, one_mul]
    have k2 : ∫ w in 𝓕, heisO ψ S T (a i) f w * (starRingEnd ℂ) (heisO ψ S T (a j) f w) ∂μ =
        ψ (symplO S T (a i - a j) l) *
          ∫ w in 𝓕, heisO ψ S T (a i) f w * (starRingEnd ℂ) (heisO ψ S T (a j) f w) ∂μ := by
      conv_rhs => rw [← key, ← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall e)
    have k3 : (ψ (symplO S T (a i - a j) l) - 1) *
        ∫ w in 𝓕, heisO ψ S T (a i) f w * (starRingEnd ℂ) (heisO ψ S T (a j) f w) ∂μ = 0 := by
      rw [sub_mul, one_mul, ← k2, sub_self]
    exact (mul_eq_zero.1 k3).resolve_left (sub_ne_zero.2 hne)

end GlobalTheory.HeisOrtho

end
end

section

open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory


open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical in
open scoped ContDiff nonZeroDivisors in
theorem _root_.GlobalTheory.dedekindZeta_eulerProduct_mul_sub_one_entire (K : Type) [Field K] [NumberField K] :
    ∃ Z : ℂ → ℂ, Differentiable ℂ Z ∧ ∀ s : ℂ, 1 < s.re → Z s = (s - 1) *
      Complex.exp (∑' P : HeightOneSpectrum (𝓞 K),
        -Complex.log (1 - 1 * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s))) := by
  let X : Ideal (𝓞 K) → ℂ := fun I => if I = ⊥ then 0 else 1
  have hXbot : X ⊥ = 0 := if_pos rfl
  have hXne : ∀ I, I ≠ ⊥ → X I = 1 := fun I hI => if_neg hI
  have hXmul : ∀ I J, X (I * J) = X I * X J := by
    intro I J
    by_cases hI : I = ⊥
    · simp [X, hI]
    by_cases hJ : J = ⊥
    · simp [X, hJ]
    rw [hXne _ (Ideal.mul_eq_bot.not.mpr (not_or.mpr ⟨hI, hJ⟩)), hXne _ hI, hXne _ hJ, one_mul]
  obtain ⟨Z, hZd, hZ, -⟩ := _root_.GlobalTheory.idealCharacter_LSeries_continuation K ⊤ X (fun _ => 1) top_ne_bot
    hXbot hXmul (fun I hI _ => by rw [hXne I hI, norm_one]) (fun I hI => absurd (sup_top_eq I) hI)
    (fun _ _ => (mul_one 1).symm) (fun _ _ _ => rfl) contDiffOn_const (fun _ _ => norm_one)
    (fun β hβ _ => hXne _ (by simpa using hβ))
  refine ⟨Z, hZd, fun s hs => ?_⟩
  rw [hZ s hs, _root_.GlobalTheory.tsum_ideal_mul_absNorm_cpow_eq_exp_tsum K X hXbot (hXne ⊤ top_ne_bot) hXmul
    (fun I => by by_cases hI : I = ⊥ <;> simp [X, hI]) s hs]
  have h1 : ∀ P : HeightOneSpectrum (𝓞 K), X P.asIdeal = 1 := fun P => hXne _ P.ne_bot
  simp only [h1]

end GlobalTheory
end
