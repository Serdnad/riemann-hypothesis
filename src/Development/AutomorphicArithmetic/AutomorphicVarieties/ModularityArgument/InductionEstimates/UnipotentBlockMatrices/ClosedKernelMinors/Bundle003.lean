module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs
public import CompanionTheory.AutomorphicTheory.UnitriangularMeasure.AdeleCoordinateMeasure.GJGlobalModulus
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

open scoped Matrix Kronecker in
private theorem adMeas_pi {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι 𝔸[K]) (u : (𝔸[K])ˣ) (hu : (u : 𝔸[K]) = M.det) :
    (Measure.pi fun _ : ι => GroundTheory.Global.adeleMeasure K).map (fun x => x ᵥ* M) =
      ENNReal.ofReal ((GroundTheory.Global.IdeleGroup.ideleModule K u : ℝ))⁻¹ •
        Measure.pi fun _ : ι => GroundTheory.Global.adeleMeasure K := by
  let σ := Fintype.equivFin ι
  have hd : (Matrix.reindex σ σ M).det = u := by rw [Matrix.det_reindex_self, hu]
  let g : GL (Fin (Fintype.card ι)) 𝔸[K] :=
    Matrix.GeneralLinearGroup.mk'' (Matrix.reindex σ σ M) (hd ▸ u.isUnit)
  have hg : (g : Matrix _ _ 𝔸[K]) = Matrix.reindex σ σ M := rfl
  have hdet : Matrix.GeneralLinearGroup.det g = u := Units.ext (by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hg, hd])
  have h := GJGlobal.Modulus.map_vecMul_adeleMeasurePi g
  rw [hdet] at h
  let E := MeasurableEquiv.piCongrLeft (fun _ : Fin (Fintype.card ι) => 𝔸[K]) σ
  have hE : MeasurePreserving E (Measure.pi fun _ : ι => GroundTheory.Global.adeleMeasure K)
      (GJMatrix.adeleMeasurePi K) :=
    measurePreserving_piCongrLeft (fun _ : Fin (Fintype.card ι) => GroundTheory.Global.adeleMeasure K) σ
  have hfun : (fun x : ι → 𝔸[K] => x ᵥ* M) =
      E.symm ∘ (fun x => x ᵥ* (g : Matrix _ _ 𝔸[K])) ∘ E := by
    funext x
    have hx : E x = x ∘ σ.symm := by
      funext i
      obtain ⟨j, rfl⟩ := σ.surjective i
      simp [E, MeasurableEquiv.piCongrLeft_apply_apply]
    funext i
    change _ = (E x ᵥ* (g : Matrix _ _ 𝔸[K])) (σ i)
    rw [hx, hg, Matrix.reindex_apply, Matrix.submatrix_vecMul_equiv]
    simp [Function.comp_assoc]
  have hm := GJGlobal.Modulus.measurable_vecMul' g
  rw [hfun, ← Measure.map_map E.symm.measurable (hm.comp E.measurable),
    ← Measure.map_map hm E.measurable, hE.map_eq, h, Measure.map_smul, hE.symm.map_eq]
  exact E.symm.measurable.aemeasurable

private def adMeas_tau : Fin 2 × Fin 2 ≃ UPos (2 + 2) 2 where
  toFun p := ⟨(Fin.castAdd 2 p.1, Fin.natAdd 2 p.2), p.1.2, Nat.le_add_right _ _⟩
  invFun p := (⟨p.1.1, p.2.1⟩, ⟨p.1.2 - 2, by have := p.1.2.2; omega⟩)
  left_inv := by decide
  right_inv := by decide

private theorem adMeas_unip {R : Type} [CommRing R] (X : UPos (2 + 2) 2 → R) :
    unipMatrix X = Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks 1 (Matrix.of fun i j => X (adMeas_tau (i, j))) 0 1) := by
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rw [unipMatrix, Matrix.add_apply, blockEntry_apply, Matrix.one_apply]
  rcases i with i | i <;> rcases j with j | j <;>
    simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right] <;>
    fin_cases i <;> fin_cases j <;> simp [adMeas_tau, Fin.ext_iff]

open scoped Matrix Kronecker in
private noncomputable def adMeas_M {R : Type} [CommRing R] (a b : GL (Fin 2) R) :
    Matrix (UPos (2 + 2) 2) (UPos (2 + 2) 2) R :=
  Matrix.reindex adMeas_tau adMeas_tau (((a⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)ᵀ ⊗ₖ (b : Matrix (Fin 2) (Fin 2) R))

private theorem adMeas_M_mul {R : Type} [CommRing R] (a b : GL (Fin 2) R) :
    adMeas_M a b * adMeas_M a⁻¹ b⁻¹ = 1 := by
  simp only [adMeas_M, Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  rw [← Matrix.mul_kronecker_mul, ← Matrix.transpose_mul, ← Units.val_mul, ← Units.val_mul]
  simp

open scoped Matrix in
private theorem adMeas_conj {R : Type} [CommRing R] (a b : GL (Fin 2) R) (X : UPos (2 + 2) 2 → R) :
    unipGL X * blk a b = blk a b * unipGL (X ᵥ* adMeas_M a b) := by
  have h : (Matrix.of fun i j => (X ᵥ* adMeas_M a b) (adMeas_tau (i, j))) =
      ((a⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) * (Matrix.of fun i j => X (adMeas_tau (i, j))) *
        (b : Matrix (Fin 2) (Fin 2) R) := by
    ext i j
    rw [adMeas_M, Matrix.reindex_apply, Matrix.of_apply, Matrix.submatrix_vecMul_equiv]
    simp only [Function.comp_apply, Equiv.symm_apply_apply, Equiv.symm_symm, Matrix.vecMul, dotProduct,
      Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.transpose_apply, Matrix.mul_apply,
      Matrix.of_apply, Fin.sum_univ_two]
    ring
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_unipGL, coe_unipGL, adMeas_unip, adMeas_unip, h]
  simp only [blk, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply,
    ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel]
  simp

open scoped Matrix in
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.adMeas :
    ∀ {K : Type} [Field K] [NumberField K] (m₁ m₂ : G1 K 2) (t : ℝ),
    ∃ e : (UPos (2 + 2) 2 → 𝔸[K]) ≃ₜ+ (UPos (2 + 2) 2 → 𝔸[K]),
      (∀ X, unipOne (K := K) (n := 2 + 2) 2 X * lv m₁ m₂ t =
        lv m₁ m₂ t * unipOne (K := K) (n := 2 + 2) 2 (e X)) ∧
      (unipMeasure K (2 + 2) 2).map e = ENNReal.ofReal (Real.exp (4 * t)) • unipMeasure K (2 + 2) 2 := by
  intro K _ _ m₁ m₂ t
  set a : AdelicGLn.AdelicGL K 2 := (m₁ : AdelicGLn.AdelicGL K 2) * zt K t with ha
  set b : AdelicGLn.AdelicGL K 2 := (m₂ : AdelicGLn.AdelicGL K 2) * zt K (-t) with hb
  have h2 : adMeas_M a⁻¹ b⁻¹ * adMeas_M a b = 1 := by
    simpa using adMeas_M_mul a⁻¹ b⁻¹
  refine ⟨{ toFun := fun X => X ᵥ* adMeas_M a b
            invFun := fun X => X ᵥ* adMeas_M a⁻¹ b⁻¹
            left_inv := fun X => by simp only [Matrix.vecMul_vecMul, adMeas_M_mul, Matrix.vecMul_one]
            right_inv := fun X => by simp only [Matrix.vecMul_vecMul, h2, Matrix.vecMul_one]
            map_add' := fun X Y => Matrix.add_vecMul _ _ _
            continuous_toFun := continuous_id.matrix_vecMul continuous_const
            continuous_invFun := continuous_id.matrix_vecMul continuous_const }, fun X => ?_, ?_⟩
  · refine Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, (blkLaws (K := K)).1 m₁ m₂ t]
    exact adMeas_conj a b X
  · have hm : ∀ (m : G1 K 2) (s : ℝ),
        (detModule K 2 ((m : AdelicGLn.AdelicGL K 2) * zt K s) : ℝ) = Real.exp s := by
      intro m s
      rw [map_mul, mem_normOneGL_iff_detModule.1 m.2, one_mul, zt, detModule_centralSection two_pos]
    have h := adMeas_pi (adMeas_M a b)
      (Matrix.GeneralLinearGroup.det a⁻¹ ^ 2 * Matrix.GeneralLinearGroup.det b ^ 2) (by
        rw [adMeas_M, Matrix.det_reindex_self, Matrix.det_kronecker, Matrix.det_transpose]
        simp only [Units.val_mul, Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.val_det_apply,
          Fintype.card_fin])
    have hv : ((GroundTheory.Global.IdeleGroup.ideleModule K
        (Matrix.GeneralLinearGroup.det a⁻¹ ^ 2 * Matrix.GeneralLinearGroup.det b ^ 2) : ℝ))⁻¹ =
        Real.exp (4 * t) := by
      have e1 : GroundTheory.Global.IdeleGroup.ideleModule K
          (Matrix.GeneralLinearGroup.det a⁻¹ ^ 2 * Matrix.GeneralLinearGroup.det b ^ 2) =
          (detModule K 2 a)⁻¹ ^ 2 * detModule K 2 b ^ 2 := by
        rw [map_mul, map_pow, map_pow, ← map_inv (detModule K 2)]
        rfl
      rw [e1, Positive.val_mul, Positive.val_pow, Positive.val_pow, Positive.coe_inv, hm, hm,
        ← Real.exp_neg, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_neg]
      congr 1
      push_cast
      ring
    rw [hv] at h
    exact h
end

section

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

section General

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [OpensMeasurableSpace G]
  [T2Space G]

private theorem integ {U : Set G} (hU : IsCompact U) {ν : Measure G} [IsProbabilityMeasure ν] (hs : ∀ᵐ k ∂ν, k ∈ U)
    {F : G → ℂ} (hF : Continuous F) : Integrable F ν := by
  have h := hF.continuousOn.integrableOn_compact (μ := ν) hU
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hs] at h

private def fixSub {U : Set G} (hU : IsCompact U) (ν : Measure G) [IsProbabilityMeasure ν] (hs : ∀ᵐ k ∂ν, k ∈ U)
    {e : G → ℂ} (he : Continuous e) : Submodule ℂ (G → ℂ) where
  carrier := {F | Continuous F ∧ ∀ g, ∫ k, e k * F (g * k) ∂ν = F g}
  add_mem' := by
    rintro F F' ⟨hF, h⟩ ⟨hF', h'⟩
    refine ⟨hF.add hF', fun g => ?_⟩
    simp only [Pi.add_apply, mul_add]
    rw [integral_add (integ hU hs (by fun_prop)) (integ hU hs (by fun_prop)), h, h']
  zero_mem' := ⟨continuous_const, by simp⟩
  smul_mem' := by
    rintro c F ⟨hF, h⟩
    refine ⟨hF.const_smul c, fun g => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm _ c]
    rw [integral_const_mul, h]

private theorem detect (U : Subgroup G) (hU : IsCompact (U : Set G)) (ν : Measure G) [IsProbabilityMeasure ν]
    (hs : ∀ᵐ k ∂ν, k ∈ U) (hinv : ∀ k ∈ U, MeasurePreserving (k * ·) ν ν) {e : G → ℂ} (he : Continuous e) :
    ∃ t : Finset G, (∀ x ∈ t, x ∈ U) ∧ ∀ F : G → ℂ, Continuous F → (∀ g, ∫ k, e k * F (g * k) ∂ν = F g) →
      (∀ x ∈ t, F x = 0) → ∀ x ∈ U, F x = 0 := by
  have h1 : ∀ u ∈ (U : Set G), {x : G | ∀ k ∈ (U : Set G), ‖e (x⁻¹ * k) - e (u⁻¹ * k)‖ < 1 / 2} ∈ 𝓝 u := by
    intro u _
    refine hU.eventually_forall_of_forall_eventually (x₀ := u)
      (P := fun x k => ‖e (x⁻¹ * k) - e (u⁻¹ * k)‖ < 1 / 2) fun k _ => ?_
    have hc : Continuous fun p : G × G => ‖e (p.1⁻¹ * p.2) - e (u⁻¹ * p.2)‖ := by fun_prop
    exact (isOpen_lt hc continuous_const).mem_nhds (by simp)
  obtain ⟨t, ht, hcov⟩ := hU.elim_nhds_subcover _ h1
  refine ⟨t, ht, fun F hF hfix h0 => ?_⟩
  have hrep : ∀ u ∈ U, F u = ∫ k, e (u⁻¹ * k) * F k ∂ν := by
    intro u hu
    rw [← hfix u]
    conv_rhs => rw [← (hinv u hu).map_eq]
    rw [integral_map (hinv u hu).measurable.aemeasurable (Continuous.aestronglyMeasurable (by fun_prop))]
    simp
  obtain ⟨x, hx, hmax⟩ := hU.exists_isMaxOn ⟨1, U.one_mem⟩ hF.norm.continuousOn
  have hx0 : ‖F x‖ ≤ 1 / 2 * ‖F x‖ := by
    obtain ⟨u, hu, hxu⟩ := mem_iUnion₂.1 (hcov hx)
    have e1 : F x = ∫ k, (e (x⁻¹ * k) - e (u⁻¹ * k)) * F k ∂ν := by
      simp only [sub_mul]
      rw [integral_sub (integ hU hs (by fun_prop)) (integ hU hs (by fun_prop)), ← hrep x hx, ← hrep u (ht u hu), h0 u hu,
        sub_zero]
    have e2 := norm_integral_le_of_norm_le_const (μ := ν) (f := fun k => (e (x⁻¹ * k) - e (u⁻¹ * k)) * F k)
      (C := 1 / 2 * ‖F x‖) (by
        filter_upwards [hs] with k hk
        rw [norm_mul]
        exact mul_le_mul (hxu k hk).le (hmax hk) (norm_nonneg _) (by norm_num))
    rw [← e1] at e2
    simpa using e2
  intro y hy
  have : ‖F y‖ ≤ ‖F x‖ := hmax hy
  have := norm_nonneg (F x)
  exact norm_le_zero_iff.1 (by linarith)

end General

private theorem leftRight {H : Type} [Group H] (V : Submodule ℂ (H → ℂ)) [FiniteDimensional ℂ V]
    (hV : ∀ a ∈ V, ∀ g, (fun x => a (g * x)) ∈ V) :
    FiniteDimensional ℂ (Submodule.span ℂ {b : H → ℂ | ∃ a ∈ V, ∃ u, b = fun x => a (x * u)}) := by
  classical
  let B := Module.finBasis ℂ V
  let L : H → V →ₗ[ℂ] V := fun g =>
    { toFun := fun a => ⟨fun x => (a : H → ℂ) (g * x), hV a a.2 g⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let c : Fin (Module.finrank ℂ V) × Fin (Module.finrank ℂ V) → H → ℂ := fun p x => B.repr (L x (B p.2)) p.1
  have hfin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range c)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range c)
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range c)) (Submodule.span_le.2 ?_)
  rintro _ ⟨a, ha, u, rfl⟩
  have key : (fun x => a (x * u)) = ∑ p : Fin (Module.finrank ℂ V) × Fin (Module.finrank ℂ V),
      (B.repr ⟨a, ha⟩ p.2 * (B p.1 : H → ℂ) u) • c p := by
    funext x
    have h1 : a (x * u) = (L x ⟨a, ha⟩ : H → ℂ) u := rfl
    have h2 : L x ⟨a, ha⟩ = ∑ i, ∑ j, (B.repr ⟨a, ha⟩ j * c (i, j) x) • B i := by

      conv_lhs => rw [← B.sum_repr ⟨a, ha⟩, map_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul]
      conv_lhs => rw [← B.sum_repr (L x (B j))]
      rw [Finset.smul_sum]
      simp only [smul_smul, c]
    rw [h1, h2, Fintype.sum_prod_type]
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [SetLike.mem_coe, key]
  exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.typeFin :
    ∀ {K : Type} [Field K] [NumberField K] {n : ℕ} (D : TypeDat K n), IsCompact (D.U : Set (G1 K n)) ∧ D.U ≤ KG K n ∧ ∃ 𝒜 : Submodule ℂ (D.U → ℂ), FiniteDimensional ℂ 𝒜 ∧
      (∀ a ∈ 𝒜, Continuous a ∧ ∀ u : D.U, (fun x => a (x * u)) ∈ 𝒜) ∧
      ∀ f : G1 K n → ℂ, Continuous f → D.Fix f → ∀ g, (fun u : D.U => f (g * u)) ∈ 𝒜 := by
  intro K _ _ n D
  obtain ⟨O, hO, hUO⟩ := D.isOpen
  have hle : D.U ≤ KG K n := fun g hg => ((hUO g).1 hg).2
  have hK : IsCompact (KG K n : Set (G1 K n)) := ((blkLaws (K := K)).2.2.2.2.2.2.2.2.2.2.2 n).1
  have hU : IsCompact (D.U : Set (G1 K n)) := by
    haveI : CompactSpace (KG K n) := isCompact_iff_compactSpace.1 hK
    have hop : IsOpen ((D.U.subgroupOf (KG K n) : Subgroup (KG K n)) : Set (KG K n)) := by
      have : ((D.U.subgroupOf (KG K n) : Subgroup (KG K n)) : Set (KG K n)) =
          (fun k : KG K n => ((k : G1 K n) : AdelicGLn.AdelicGL K n)) ⁻¹' O := by
        ext k
        exact ⟨fun h => ((hUO k).1 h).1, fun h => (hUO k).2 ⟨h, k.2⟩⟩
      rw [this]
      exact hO.preimage (continuous_subtype_val.comp continuous_subtype_val)
    have := ((Subgroup.isClosed_of_isOpen _ hop).isCompact).image continuous_subtype_val
    convert this using 1
    ext g
    exact ⟨fun h => ⟨⟨g, hle h⟩, h, rfl⟩, by rintro ⟨k, hk, rfl⟩; exact hk⟩
  refine ⟨hU, hle, ?_⟩
  haveI := D.prob
  let V : Submodule ℂ (D.U → ℂ) := (fixSub hU D.ν D.supp D.cont).map (LinearMap.funLeft ℂ ℂ (Subtype.val : D.U → G1 K n))
  have hmem : ∀ f : G1 K n → ℂ, Continuous f → D.Fix f → ∀ g, (fun u : D.U => f (g * u)) ∈ V := by
    intro f hf hfix g
    refine ⟨fun x => f (g * x), ⟨by fun_prop, fun y => ?_⟩, rfl⟩
    simp only [← mul_assoc]
    exact hfix (g * y)
  haveI : FiniteDimensional ℂ V := by
    obtain ⟨t, ht, h⟩ := detect D.U hU D.ν D.supp D.inv D.cont
    let ev : V →ₗ[ℂ] (t → ℂ) := (LinearMap.funLeft ℂ ℂ (fun x : t => (⟨x, ht x x.2⟩ : D.U))).comp V.subtype
    refine FiniteDimensional.of_injective ev ((injective_iff_map_eq_zero _).2 ?_)
    rintro ⟨_, F, ⟨hF, hfix⟩, rfl⟩ h0
    apply Subtype.ext
    funext u
    exact h F hF hfix (fun x hx => congrFun h0 ⟨x, hx⟩) u u.2
  refine ⟨_, leftRight V ?_, fun a ha => ?_, fun f hf hfix g => Submodule.subset_span ⟨_, hmem f hf hfix g, 1, by simp⟩⟩
  · rintro _ ⟨F, ⟨hF, hfix⟩, rfl⟩ g
    exact hmem F hF hfix g
  · induction ha using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨_, ⟨F, ⟨hF, hfix⟩, rfl⟩, u, rfl⟩ := hb
      refine ⟨?_, fun w => Submodule.subset_span ⟨_, ⟨F, ⟨hF, hfix⟩, rfl⟩, w * u, by simp only [mul_assoc]⟩⟩
      exact hF.comp (continuous_subtype_val.comp (continuous_id.mul continuous_const))
    | zero => exact ⟨continuous_const, fun _ => Submodule.zero_mem _⟩
    | add a b _ _ ha hb => exact ⟨ha.1.add hb.1, fun u => Submodule.add_mem _ (ha.2 u) (hb.2 u)⟩
    | smul c a _ ha => exact ⟨ha.1.const_smul c, fun u => Submodule.smul_mem _ c (ha.2 u)⟩
end
