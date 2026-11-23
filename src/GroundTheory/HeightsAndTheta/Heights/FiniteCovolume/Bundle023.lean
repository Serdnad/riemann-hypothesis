module

public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.IsIntegralVecCoordsOfMemAdelicLatticeOne
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle010
import GroundTheory.AutomorphicForms.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsVecFixGroup
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
public import Mathlib.GroupTheory.IndexNSmul
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Examples

@[expose] public section

section

set_option linter.unusedSectionVars false

noncomputable section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open Module Matrix TensorProduct NumberField IsDedekindDomain GroundTheory.Automorphic
open scoped Pointwise

section Index

theorem relIndex_ne_zero_and_le_of_nsmul_mem {W : Type*} [AddCommGroup W]
    [Module.IsTorsionFree ℤ W] {L P : AddSubgroup W} {Q : Submodule ℤ W} [Module.Finite ℤ Q]
    (hLP : L ≤ P) (hPQ : P.toIntSubmodule ≤ Q) {n : ℕ} (hn : n ≠ 0) (hnL : ∀ y ∈ P, n • y ∈ L) :
    L.relIndex P ≠ 0 ∧ L.relIndex P ≤ n ^ finrank ℤ Q := by
  haveI : Module.Finite ℤ P.toIntSubmodule :=
    Module.Finite.of_injective (Submodule.inclusion hPQ) (Submodule.inclusion_injective hPQ)
  have key := AddSubgroup.relIndex_map_nsmul n P
  have hle : P.map (nsmulAddMonoidHom (α := W) n) ≤ L := by
    rintro _ ⟨y, hy, rfl⟩
    exact hnL y hy
  have hne : (P.map (nsmulAddMonoidHom (α := W) n)).relIndex P ≠ 0 := by
    rw [key]
    exact pow_ne_zero _ hn
  have hrank : finrank ℤ P.toIntSubmodule ≤ finrank ℤ Q := Submodule.finrank_mono hPQ
  refine ⟨fun h0 => hne (AddSubgroup.relIndex_eq_zero_of_le_left hle h0), ?_⟩
  calc L.relIndex P ≤ (P.map (nsmulAddMonoidHom (α := W) n)).relIndex P :=
        AddSubgroup.relIndex_le_of_le_left hle hne
    _ = n ^ finrank ℤ P.toIntSubmodule := key
    _ ≤ n ^ finrank ℤ Q := Nat.pow_le_pow_right (Nat.pos_of_ne_zero hn) hrank

end Index

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

section Coordinates


variable (F) in
def coordEquiv (v : Basis ι E W) : W ≃+ (ι → F ⊗[F] E) :=
  v.equivFun.toAddEquiv.trans
    (AddEquiv.piCongrRight fun _ => (Algebra.TensorProduct.lid F E).symm.toAddEquiv)

theorem coordEquiv_apply (v : Basis ι E W) (x : W) (i : ι) :
    coordEquiv F v x i = (1 : F) ⊗ₜ[F] v.repr x i := by
  simp [coordEquiv, Algebra.TensorProduct.lid_symm_apply]

theorem coordEquiv_smul (v : Basis ι E W) (e : E) (x : W) :
    coordEquiv F v (e • x) = ((1 : F) ⊗ₜ[F] e) • coordEquiv F v x := by
  funext i
  simp only [coordEquiv_apply, Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul,
    mul_one, map_smul, Finsupp.smul_apply]

theorem pairE_coordEquiv (h : HermitianForm F E W) (v : Basis ι E W) (x y : W) :
    pairE (gram h.toSesq v) (coordEquiv F v x) (coordEquiv F v y) = h.toSesq x y := by
  rw [sesq_eq_sum h.toSesq v x y, pairE, hermPair]
  simp only [dotProduct, mulVec, baseMatrix, Matrix.map_apply, coordEquiv_apply, conjBase_tmul,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
    Finset.mul_sum, ← TensorProduct.tmul_sum, Algebra.TensorProduct.lid_tmul, one_smul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem vecCoords_coordEquiv {κ : Type*} [Fintype κ] (b : Basis κ F E) (v : Basis ι E W) (x : W)
    (i : ι) (k : κ) : vecCoords F b (coordEquiv F v x) (i, k) = b.repr (v.repr x i) k := by
  rw [vecCoords, coordEquiv_apply, repr_one_tmul, Algebra.algebraMap_self, RingHom.id_apply]

end Coordinates

section Equivariance

variable (h : HermitianForm F E W) (v : Basis ι E W)

theorem mulVec_coordEquiv (γ : h.unitaryGroup) (y : W) :
    unitaryMat ((unitaryPointsRationalEquivHermitian F E h v).symm γ) *ᵥ coordEquiv F v y =
      coordEquiv F v ((γ : W ≃ₗ[E] W) y) := by
  set γ' := (unitaryPointsRationalEquivHermitian F E h v).symm γ
  have h1 : unitaryPointsRationalEquiv F E (gram h.toSesq v) γ' = unitaryGroupEquivMatrix h v γ := by
    show unitaryPointsRationalEquiv F E _ (((unitaryPointsRationalEquiv F E _).trans
      (unitaryGroupEquivMatrix h v).symm).symm γ) = _
    rw [MulEquiv.symm_trans_apply, MulEquiv.apply_symm_apply, MulEquiv.symm_symm]
  have hM : (unitaryMat γ').map (Algebra.TensorProduct.lid F E) =
      LinearMap.toMatrix v v ((γ : W ≃ₗ[E] W) : W →ₗ[E] W) := by
    rw [← unitaryGroupEquivMatrix_apply, ← h1]
    rfl
  funext i
  apply (Algebra.TensorProduct.lid F E).injective
  rw [coordEquiv_apply, Algebra.TensorProduct.lid_tmul, one_smul,
    show v.repr ((γ : W ≃ₗ[E] W) y) = v.repr (((γ : W ≃ₗ[E] W) : W →ₗ[E] W) y) from rfl,
    ← LinearMap.toMatrix_mulVec_repr v v, ← hM]

  simp only [mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, coordEquiv_apply,
  Algebra.TensorProduct.lid_tmul, one_smul]

variable [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]

theorem adeleSplit_snd_hermitianDiagonal (γ : h.unitaryGroup) :
    (adeleSplit h v (hermitianDiagonal h v γ)).2 =
      finDiag (gram h.toSesq v) ((unitaryPointsRationalEquivHermitian F E h v).symm γ) := by
  apply unitaryCoords_injective _ _ (Module.finBasis F E)
  funext p
  simp [adeleSplit, unitaryCongr_apply, hermitianDiagonal, unitaryDiagonal, finDiag,
    unitaryCoords_unitaryMap, adeleRingEquivProd]
  have hprod (x : unitaryPoints F E (gram h.toSesq v)
      (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)) :
      (unitaryProdEquiv F (gram h.toSesq v) _ _ (isUnit_det_gram h v) x).2 =
        unitaryMap F E _ (AlgHom.snd F _ _) x := rfl
  rw [hprod]
  simp only [unitaryCoords_unitaryMap, Function.comp_apply]
  rfl

end Equivariance

section Lattice

variable {κ : Type*} [Fintype κ] [DecidableEq κ] (b : Basis κ F E) (h : HermitianForm F E W)
  (v : Basis ι E W)

def dictLattice (d : ℤ) (g : unitaryPoints F E (gram h.toSesq v) (FinAdele F)) : AddSubgroup W :=
  (coreLattice b (gram h.toSesq v) g).comap
    ((coordEquiv F v : W →+ (ι → F ⊗[F] E)).comp (DistribSMul.toAddMonoidHom W ((d : E)⁻¹)))

variable {b h v}

theorem mem_dictLattice {d : ℤ} {g : unitaryPoints F E (gram h.toSesq v) (FinAdele F)} {x : W} :
    x ∈ dictLattice b h v d g ↔ coordEquiv F v ((d : E)⁻¹ • x) ∈ coreLattice b (gram h.toSesq v) g :=
  Iff.rfl

theorem dictLattice_eq_iff {d : ℤ} (hd : d ≠ 0) {g g' : unitaryPoints F E (gram h.toSesq v) (FinAdele F)} :
    dictLattice b h v d g = dictLattice b h v d g' ↔ g⁻¹ * g' ∈ coreStabilizer b (gram h.toSesq v) := by
  rw [← coreLattice_eq_iff b]
  have hsurj : Function.Surjective ((coordEquiv F v : W →+ (ι → F ⊗[F] E)).comp
      (DistribSMul.toAddMonoidHom W ((d : E)⁻¹))) := by
    intro X
    refine ⟨(d : E) • (coordEquiv F v).symm X, ?_⟩
    show coordEquiv F v ((d : E)⁻¹ • ((d : E) • (coordEquiv F v).symm X)) = X
    rw [inv_smul_smul₀ (by exact_mod_cast hd), AddEquiv.apply_symm_apply]
  exact (AddSubgroup.comap_injective hsurj).eq_iff

theorem mem_smul_addSubgroup_iff (γ : h.unitaryGroup) (S : AddSubgroup W) (x : W) :
    x ∈ γ • S ↔ γ⁻¹ • x ∈ S := by
  exact AddSubgroup.mem_pointwise_smul_iff_inv_smul_mem

variable [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]

theorem dictLattice_diagonal_mul (d : ℤ) (γ : h.unitaryGroup)
    (g : unitaryPoints F E (gram h.toSesq v) (FinAdele F)) :
    dictLattice b h v d ((adeleSplit h v (hermitianDiagonal h v γ)).2 * g) = γ • dictLattice b h v d g := by
  ext x
  rw [mem_smul_addSubgroup_iff, mem_dictLattice, mem_dictLattice, adeleSplit_snd_hermitianDiagonal,
    ← mulVec_mem_coreLattice_iff b ((unitaryPointsRationalEquivHermitian F E h v).symm γ) g,
    mulVec_coordEquiv]
  have : ((γ : W ≃ₗ[E] W) ((d : E)⁻¹ • (γ⁻¹ • x))) = (d : E)⁻¹ • x := by
    rw [map_smul]
    congr 1
    show (γ : W ≃ₗ[E] W) (((γ⁻¹ : h.unitaryGroup) : W ≃ₗ[E] W) x) = x
    rw [Subgroup.coe_inv]
    exact LinearEquiv.apply_symm_apply _ x
  rw [this]

end Lattice

end GroundTheory.Heights₂.Heights.FiniteCovolume
end
end

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory
open scoped ENNReal

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def HaarParabolicCoordinates.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (M : Majorant h v) (μ : Measure (archUnitary h v)) [μ.IsHaarMeasure] (x₀ : W), x₀ ≠ 0 →
    h.toSesq x₀ x₀ = 0 →
    ∃ (ν : Measure (vecFixGroup h v x₀)) (κ : Measure M.stab)
      (τ : (InfinitePlace E → ℂ) → archUnitary h v),
      ν.IsHaarMeasure ∧ κ.IsHaarMeasure ∧ IsProbabilityMeasure κ ∧ Measurable τ ∧
      (∀ b : InfinitePlace E → ℂ, (∀ w, b w ≠ 0) →
        invApply (τ b) (vecAt v x₀) = fun w => b w • vecAt v x₀ w) ∧
      ∀ f : archUnitary h v → ℝ≥0∞, Measurable f →
        ∫⁻ g, f g ∂μ = ∫⁻ b : InfinitePlace E → ℂ, (∏ w, ‖b w‖ₑ ^ (2 * (finrank E W - 2))) *
          ∫⁻ k : M.stab, ∫⁻ x : vecFixGroup h v x₀, f (x * (τ b * k)) ∂ν ∂κ

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory
open scoped ENNReal

noncomputable section

section LineStab

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [NumberField E]

def lineStab (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W) :
    Subgroup (archUnitary h v) where
  carrier := {g | ∀ w, ∃ c : ℂ, ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w =
    c • vecAt v x₀ w}
  one_mem' w := ⟨1, by simp⟩
  mul_mem' {a b} ha hb w := by
    obtain ⟨c, hc⟩ := ha w
    obtain ⟨d, hd⟩ := hb w
    refine ⟨c * d, ?_⟩
    simp only [Subgroup.coe_mul, Pi.mul_apply, Units.val_mul, ← Matrix.mulVec_mulVec, hd,
      Matrix.mulVec_smul, hc, smul_smul, mul_comm d c]
  inv_mem' {a} ha w := by
    obtain ⟨c, hc⟩ := ha w
    have e : (((a⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *
        ((a : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) = 1 := by
      rw [Subgroup.coe_inv, Pi.inv_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hz : vecAt v x₀ w = (((a⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w :
        Matrix ι ι ℂ) *ᵥ (((a : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w) := by
      rw [Matrix.mulVec_mulVec, e, Matrix.one_mulVec]
    by_cases hc0 : c = 0
    · have h0 : vecAt v x₀ w = 0 := by
        rw [hz, hc, hc0, zero_smul, Matrix.mulVec_zero]
      exact ⟨0, by rw [h0, Matrix.mulVec_zero, smul_zero]⟩
    · refine ⟨c⁻¹, ?_⟩
      calc (((a⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w
          = c⁻¹ • ((((a⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ
              (c • vecAt v x₀ w)) := by
            rw [Matrix.mulVec_smul, smul_smul, inv_mul_cancel₀ hc0, one_smul]
        _ = c⁻¹ • vecAt v x₀ w := by rw [← hc, ← hz]

omit [NumberField E] in
theorem mem_lineStab {h : HermitianForm F E W} {v : Basis ι E W} {x₀ : W} {g : archUnitary h v} :
    g ∈ lineStab h v x₀ ↔ ∀ w, ∃ c : ℂ,
      ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w = c • vecAt v x₀ w :=
  Iff.rfl


omit [NumberField E] in
theorem vecFixGroup_le_lineStab (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W) :
    vecFixGroup h v x₀ ≤ lineStab h v x₀ := fun g hg w => ⟨1, by rw [one_smul]; exact hg w⟩


omit [NumberField E] in
theorem isClosed_lineStab (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W) :
    IsClosed (lineStab h v x₀ : Set (archUnitary h v)) := by
  have : (lineStab h v x₀ : Set (archUnitary h v)) = ⋂ w, (fun g : archUnitary h v =>
      ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w) ⁻¹'
        (Submodule.span ℂ {vecAt v x₀ w} : Set (ι → ℂ)) := by
    ext g
    simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe, Submodule.mem_span_singleton,
      mem_lineStab]
    exact forall_congr' fun w => ⟨fun ⟨c, hc⟩ => ⟨c, hc.symm⟩, fun ⟨c, hc⟩ => ⟨c, hc.symm⟩⟩
  rw [this]
  refine isClosed_iInter fun w => IsClosed.preimage ?_ (Submodule.closed_of_finiteDimensional _)
  exact (Units.continuous_val.comp ((continuous_apply w).comp continuous_subtype_val)).matrix_mulVec
    continuous_const

instance locallyCompactSpace_lineStab (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W) :
    LocallyCompactSpace (lineStab h v x₀) :=
  (isClosed_lineStab h v x₀).isClosedEmbedding_subtypeVal.locallyCompactSpace

end LineStab

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def LineStabHaar.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ x₀ : W, x₀ ≠ 0 → h.toSesq x₀ x₀ = 0 →
    ∀ (μP : Measure (lineStab h v x₀)) [μP.IsHaarMeasure],
    ∃ (ν : Measure (vecFixGroup h v x₀)) (τ : (InfinitePlace E → ℂ) → archUnitary h v),
      ν.IsHaarMeasure ∧ Measurable τ ∧ (∀ b, τ b ∈ lineStab h v x₀) ∧
      (∀ b : InfinitePlace E → ℂ, (∀ w, b w ≠ 0) →
        invApply (τ b) (vecAt v x₀) = fun w => b w • vecAt v x₀ w) ∧
      ∀ φ : archUnitary h v → ℝ≥0∞, Measurable φ →
        ∫⁻ p, φ (p : archUnitary h v) ∂μP = ∫⁻ b : InfinitePlace E → ℂ,
          (∏ w, ‖b w‖ₑ ^ (2 * (finrank E W - 2))) *
            ∫⁻ x : vecFixGroup h v x₀, φ ((x : archUnitary h v) * τ b) ∂ν

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end
