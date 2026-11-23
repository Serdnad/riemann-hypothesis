module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle002
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle022
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsBorelSectionUnitaryOrbitQuadric
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsFibreFamilyEqAtContinuityPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle035
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle003
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MahlerCoefficientNormLeOneIffJetsBoundedMeasureM
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MahlerJetCoefficientMul
public import Mathlib.Data.FunLike.Fintype
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IteratedDerivLogDerivDirichletLViaNearbyZeros
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle004
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LamIdealOfNotPrimePow
public import Mathlib.NumberTheory.LSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RayClassLFunctionFamilyContinuationGrowth
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle002
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FinsumMemLeOfSubset
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
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Uniformizable

@[expose] public section

section

noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal

namespace GlobalTheory.SelfDualLatticeSplit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (v : HeightOneSpectrum (𝓞 F))

open scoped TensorProduct Matrix in
open NumberField IsDedekindDomain in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (v : HeightOneSpectrum (𝓞 F)) in
theorem _root_.GlobalTheory.SelfDualLatticeSplit.hR_add_right (x y z : Fin M → _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.Ev F E v) :
    _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ J x (y + z) =
      _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ J x y + _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ J x z := by
  unfold _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR _root_.Formalism.UG.hform
  simp [mul_add, Finset.sum_add_distrib]

def formAt (x : Fin M → Ev F E v) : (Fin M → Ev F E v) →ₗ[Ev F E v] Ev F E v where
  toFun y := hR (Fv F v) σ J x y
  map_add' := hR_add_right σ J v x
  map_smul' c y := GlobalTheory.SelfDualLatticeCompare.hR_smul_right _ J x y c

def proj (x : Fin M → Ev F E v) (b : Ev F E v) :
    (Fin M → Ev F E v) →ₗ[Ev F E v] (Fin M → Ev F E v) :=
  LinearMap.id - (b • formAt σ J v x).smulRight x

open scoped TensorProduct Matrix in
open NumberField IsDedekindDomain in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (v : HeightOneSpectrum (𝓞 F)) in
private lemma selfDualLatticeSplit_proj_eq_sub_smul (x : Fin M → _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.Ev F E v)
    (b : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.Ev F E v) (y : Fin M → _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.Ev F E v) :
    _root_.GlobalTheory.SelfDualLatticeSplit.proj σ J v x b y =
      y - (b * _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ J x y) • x := by
  simp [_root_.GlobalTheory.SelfDualLatticeSplit.proj, _root_.GlobalTheory.SelfDualLatticeSplit.formAt]

open scoped TensorProduct Matrix in
open NumberField IsDedekindDomain in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (v : HeightOneSpectrum (𝓞 F)) in
private lemma hR_selfDualLatticeSplit_proj_eq_zero (x : Fin M → _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.Ev F E v)
    (b : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.Ev F E v) (hb : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ J x x * b = 1)
    (y : Fin M → _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.Ev F E v) :
    _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ J x (_root_.GlobalTheory.SelfDualLatticeSplit.proj σ J v x b y) = 0 := by
  rw [selfDualLatticeSplit_proj_eq_sub_smul, sub_eq_add_neg, _root_.GlobalTheory.SelfDualLatticeSplit.hR_add_right, ← neg_smul,
    _root_.GlobalTheory.SelfDualLatticeCompare.hR_smul_right]
  linear_combination (-(_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ J x y)) * hb

open scoped TensorProduct Matrix in
open NumberField IsDedekindDomain in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (v : HeightOneSpectrum (𝓞 F)) in
private lemma form_smul_add_left_lemma_3 (c : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.Ev F E v)
    (x p y : Fin M → _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.Ev F E v) :
    _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ J (c • x + p) y =
      _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ c * _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ J x y +
        _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ J p y := by
  unfold _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR _root_.Formalism.UG.hform _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR
  simp [add_mul, mul_assoc, Finset.sum_add_distrib, Finset.mul_sum]


open scoped TensorProduct Matrix in
open NumberField IsDedekindDomain in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (v : HeightOneSpectrum (𝓞 F)) in
theorem _root_.GlobalTheory.SelfDualLatticeSplit.unit_vector_splits :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
      (σ : E →ₐ[F] E), _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND σ J →
      ∀ (v : HeightOneSpectrum (𝓞 F))
        (L : Submodule (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.OEv F E v) (Fin M → _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.Ev F E v)),
        _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.IsSDLat σ J v L → ∀ x ∈ L,
          (∃ b ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.OEv F E v, _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ J x x * b = 1) →
          L = Submodule.span (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.OEv F E v) {x} ⊔
              _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.perpLat σ J v L x ∧
            _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.IsSDLatIn σ J v (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.perp σ J v x)
              (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.perpLat σ J v L x) := by
  intro F E _ _ _ _ _ σ _ M J _ v L hL x hx hbex
  obtain ⟨b, hbO, hb⟩ := hbex
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.IsSDLat _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.IsSDLatIn at hL
  obtain ⟨hFG, hspan, hdual⟩ := hL
  have hperp : ∀ y, y ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.perpLat σ J v L x ↔
      _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ J x y = 0 ∧ y ∈ L := fun y ↦ Iff.rfl
  have hxy : ∀ y ∈ L, _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ J x y ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.OEv F E v :=
    fun y hy ↦ ((hdual y).1 hy).2 x hx
  have hsmul : ∀ y ∈ L, (b * _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ J x y) • x ∈ L := fun y hy ↦
    L.smul_mem (⟨_, mul_mem hbO (hxy y hy)⟩ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.OEv F E v) hx
  have hprojL : ∀ y ∈ L, _root_.GlobalTheory.SelfDualLatticeSplit.proj σ J v x b y ∈
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.perpLat σ J v L x := fun y hy ↦ by
    refine (hperp _).2 ⟨hR_selfDualLatticeSplit_proj_eq_zero σ J v x b hb y, ?_⟩
    rw [selfDualLatticeSplit_proj_eq_sub_smul]
    exact L.sub_mem hy (hsmul y hy)
  have hdecomp : ∀ y, y = (b * _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ J x y) • x +
      _root_.GlobalTheory.SelfDualLatticeSplit.proj σ J v x b y := fun y ↦ by
    rw [selfDualLatticeSplit_proj_eq_sub_smul]
    abel
  have hfix : ∀ y, _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ J x y = 0 →
      _root_.GlobalTheory.SelfDualLatticeSplit.proj σ J v x b y = y := fun y hy ↦ by
    rw [selfDualLatticeSplit_proj_eq_sub_smul, hy, mul_zero, zero_smul, sub_zero]
  refine ⟨le_antisymm (fun y hy ↦ ?_) (sup_le ?_ (fun y hy ↦ ((hperp y).1 hy).2)), ?_, ?_, ?_⟩
  · rw [hdecomp y]
    refine Submodule.add_mem _ (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right (hprojL y hy))
    exact Submodule.smul_mem _ (⟨_, mul_mem hbO (hxy y hy)⟩ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.OEv F E v)
      (Submodule.subset_span rfl)
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hx
  · have heq : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.perpLat σ J v L x =
        L.map ((_root_.GlobalTheory.SelfDualLatticeSplit.proj σ J v x b).restrictScalars
          (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.OEv F E v)) := by
      ext y
      constructor
      · intro hy
        exact ⟨y, ((hperp y).1 hy).2, hfix y ((hperp y).1 hy).1⟩
      · rintro ⟨z, hz, rfl⟩
        exact hprojL z hz
    rw [heq]
    exact hFG.map _
  · refine le_antisymm (Submodule.span_le.2 fun y hy ↦ ((hperp y).1 hy).1) (fun y hy ↦ ?_)
    have hy' : _root_.GlobalTheory.SelfDualLatticeSplit.proj σ J v x b y ∈
        Submodule.span (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.Ev F E v)
          (_root_.GlobalTheory.SelfDualLatticeSplit.proj σ J v x b '' (L : Set _)) := by
      rw [← Submodule.map_span, hspan]
      exact ⟨y, trivial, rfl⟩
    rw [hfix y hy] at hy'
    refine Submodule.span_mono ?_ hy'
    rintro _ ⟨z, hz, rfl⟩
    exact hprojL z hz
  · intro y
    constructor
    · intro hy
      exact ⟨((hperp y).1 hy).1, fun z hz ↦ ((hdual y).1 ((hperp y).1 hy).2).2 z ((hperp z).1 hz).2⟩
    · rintro ⟨hy0, hz⟩
      refine (hperp y).2 ⟨hy0, (hdual y).2 ⟨trivial, fun z hzL ↦ ?_⟩⟩
      have hy0' : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ J x y = 0 := hy0
      rw [hdecomp z, form_smul_add_left_lemma_3, hy0', mul_zero, zero_add]
      exact hz _ (hprojL z hzL)

end GlobalTheory.SelfDualLatticeSplit
end
end

section

noncomputable section

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding
open scoped ENNReal NNReal

namespace GlobalTheory.FibreInvariance

variable {P Q : ℕ}

theorem qf_continuous : Continuous (qf : Sp P Q → ℝ) := by
  unfold qf
  fun_prop

theorem qf_act (g : UpqT P Q) (x : Sp P Q) : qf (act g x) = qf x := by
  have hu := GlobalTheory.UpqTopology.mat_unitary g
  apply Complex.ofReal_injective
  rw [← GlobalTheory.QuadricSection.form_self, ← GlobalTheory.QuadricSection.form_self]
  show star (UpqT.mat g *ᵥ x) ⬝ᵥ (Formalism.UG.Jpq P Q *ᵥ (UpqT.mat g *ᵥ x)) = _
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hu]

theorem normSq_det (g : UpqT P Q) : Complex.normSq (UpqT.mat g).det = 1 := by
  have h := congrArg Matrix.det (GlobalTheory.UpqTopology.mat_unitary g)
  have hJ : (Formalism.UG.Jpq P Q).det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det (GlobalTheory.UpqTopology.jpq_sq (P := P) (Q := Q))
    rw [det_mul, h0, zero_mul, det_one] at h1
    exact zero_ne_one h1
  rw [det_mul, det_mul, det_conjTranspose] at h
  have h2 : star (UpqT.mat g).det * (UpqT.mat g).det = 1 := by
    apply mul_right_cancel₀ hJ
    linear_combination h
  apply Complex.ofReal_injective
  rw [Complex.normSq_eq_conj_mul_self, starRingEnd_apply, h2, Complex.ofReal_one]

theorem map_volume_act (g : UpqT P Q) :
    (volume : Measure (Sp P Q)).map (act g) = volume := by
  have hdetC : LinearMap.det (Matrix.mulVecLin (UpqT.mat g)) = (UpqT.mat g).det :=
    LinearMap.det_toLin' _
  have hdet : LinearMap.det ((Matrix.mulVecLin (UpqT.mat g)).restrictScalars ℝ) = 1 := by
    rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply, hdetC, normSq_det]
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (Sp P Q))
    (f := (Matrix.mulVecLin (UpqT.mat g)).restrictScalars ℝ) (by rw [hdet]; exact one_ne_zero)
  rw [hdet, inv_one, abs_one, ENNReal.ofReal_one, one_smul] at hmap
  exact hmap

theorem continuous_act (g : UpqT P Q) : Continuous (act g : Sp P Q → Sp P Q) :=
  continuous_const.matrix_mulVec continuous_id

private lemma UpqT_mat_mul' (a b : UpqT P Q) : UpqT.mat (a * b) = UpqT.mat a * UpqT.mat b := rfl

private lemma UpqT_mat_one' : UpqT.mat (1 : UpqT P Q) = 1 := rfl

theorem act_inv_act (g : UpqT P Q) (x : Sp P Q) : act g⁻¹ (act g x) = x := by
  show UpqT.mat g⁻¹ *ᵥ (UpqT.mat g *ᵥ x) = x
  rw [mulVec_mulVec, ← UpqT_mat_mul', inv_mul_cancel, UpqT_mat_one', one_mulVec]

def actHomeo (g : UpqT P Q) : Sp P Q ≃ₜ Sp P Q where
  toFun := act g
  invFun := act g⁻¹
  left_inv := act_inv_act g
  right_inv x := by simpa using act_inv_act g⁻¹ x
  continuous_toFun := continuous_act g
  continuous_invFun := continuous_act g⁻¹

theorem act_ne_zero_iff (g : UpqT P Q) (x : Sp P Q) : act g x ≠ 0 ↔ x ≠ 0 := by
  constructor
  · rintro h rfl
    exact h (mulVec_zero _)
  · intro hx h
    apply hx
    rw [← act_inv_act g x, h]
    exact mulVec_zero _

theorem isDxDq_map {fib : ℝ → Measure (Sp P Q)} (h : IsDxDq fib) (g : UpqT P Q) :
    IsDxDq fun t => (fib t).map (act g) := by
  have hm : Measurable (act g) := (continuous_act g).measurable
  have hO : IsOpen {x : Sp P Q | x ≠ 0} := isOpen_ne
  have hU : act g ⁻¹' {x : Sp P Q | x ≠ 0} = {x | x ≠ 0} := by
    ext x
    exact act_ne_zero_iff g x
  have hpre : ∀ t : ℝ, act g ⁻¹' (qf ⁻¹' {id t} ∩ {x : Sp P Q | x ≠ 0}) =
      qf ⁻¹' {id t} ∩ {x | x ≠ 0} := by
    intro t
    rw [Set.preimage_inter, hU, ← Set.preimage_comp]
    congr 1
    ext x
    simp only [Set.mem_preimage, Function.comp_apply, qf_act]
  have hS : ∀ t : ℝ, MeasurableSet (qf ⁻¹' {id t} ∩ {x : Sp P Q | x ≠ 0}) := fun t =>
    (qf_continuous.measurable (measurableSet_singleton _)).inter hO.measurableSet
  have h' : IsFibreFamily (dx P Q) qf id {x | x ≠ 0} volume Set.univ fib := h
  obtain ⟨h1, h2, h3⟩ := h'
  show IsFibreFamily (dx P Q) qf id {x | x ≠ 0} volume Set.univ fun t => (fib t).map (act g)
  refine ⟨fun t => ?_, fun φ hφ => ?_, fun φ hφc hφs hφU => ?_⟩
  · dsimp only
    rw [Measure.map_apply hm (hS t).compl, Set.preimage_compl, hpre t]
    exact h1 t
  · dsimp only
    simp_rw [lintegral_map hφ hm]
    rw [← h2 (fun v => φ (act g v)) (hφ.comp hm)]
    have hdx : (dx P Q).map (act g) = dx P Q := by
      unfold dx
      rw [Measure.map_smul, map_volume_act]
      exact hm.aemeasurable
    conv_lhs => rw [← hdx]
    rw [setLIntegral_map hO.measurableSet hφ hm, hU]
  · have hc : Continuous (φ ∘ act g) := hφc.comp (continuous_act g)
    have hs : HasCompactSupport (φ ∘ act g) := hφs.comp_homeomorph (actHomeo g)
    have hU' : tsupport (φ ∘ act g) ⊆ {x | x ≠ 0} := by
      intro x hx
      exact (act_ne_zero_iff g x).1 (hφU (tsupport_comp_subset_preimage φ (continuous_act g) hx))
    obtain ⟨hi, hcont⟩ := h3 _ hc hs hU'
    refine ⟨fun b hb => ?_, ?_⟩
    · exact (integrable_map_measure hφc.aestronglyMeasurable hm.aemeasurable).2 (hi b hb)
    · have he : (fun b => ∫ v, φ v ∂((fib b).map (act g))) = fun b => ∫ v, (φ ∘ act g) v ∂(fib b) := by
        funext b
        exact integral_map hm.aemeasurable hφc.aestronglyMeasurable
      dsimp only
      rw [he]
      exact hcont

theorem fibre_finite_invariant : ∀ (P Q : ℕ) (fib : ℝ → Measure (Sp P Q)) (β : ℝ), IsDxDq fib →
    β ≠ 0 → IsFiniteMeasureOnCompacts (fib β) ∧
      ∀ g : UpqT P Q, (fib β).map (act g) = fib β := by
  intro P Q fib β h hβ
  have hq : Continuous (qf : Sp P Q → ℝ) := qf_continuous
  have hO : IsOpen {x : Sp P Q | x ≠ 0} := isOpen_ne
  have hz : qf (0 : Sp P Q) = 0 := by simp [qf]
  have hqO : qf ⁻¹' {β} ⊆ {x : Sp P Q | x ≠ 0} := by
    rintro x hx rfl
    apply hβ
    rw [← (hx : qf (0 : Sp P Q) = β), hz]
  refine ⟨⟨fun K hK => ?_⟩, fun g => ?_⟩
  · have h' : IsFibreFamily (dx P Q) qf id {x | x ≠ 0} volume Set.univ fib := h
    obtain ⟨h1, -, h3⟩ := h'
    have hb : 0 < |β| := abs_pos.mpr hβ
    have hK' : IsCompact (K ∩ qf ⁻¹' {β}) := hK.inter_right (isClosed_singleton.preimage hq)
    have hT : IsClosed {x : Sp P Q | |qf x| ≤ |β| / 2} :=
      isClosed_le (continuous_abs.comp hq) continuous_const
    have hdisj : Disjoint (K ∩ qf ⁻¹' {β}) {x : Sp P Q | |qf x| ≤ |β| / 2} := by
      rw [Set.disjoint_left]
      rintro x ⟨-, hx⟩ hx2
      have hx' : qf x = β := hx
      rw [Set.mem_ofPred_eq, hx'] at hx2
      linarith
    obtain ⟨φ, hφ1, hφ0, hφs, -⟩ := exists_continuous_one_zero_of_isCompact hK' hT hdisj
    have hsupp : tsupport φ ⊆ {x : Sp P Q | x ≠ 0} := by
      have hcl : tsupport φ ⊆ {x : Sp P Q | |β| / 2 ≤ |qf x|} := by
        apply closure_minimal _ (isClosed_le continuous_const (continuous_abs.comp hq))
        intro x hx
        by_contra hc
        have hc' : ¬ (|β| / 2 ≤ |qf x|) := hc
        exact hx (hφ0 (show |qf x| ≤ |β| / 2 from le_of_lt (not_le.mp hc')))
      intro x hx hx0
      have hx2 := hcl hx
      rw [Set.mem_ofPred_eq, hx0, hz, abs_zero] at hx2
      linarith
    obtain ⟨hint, -⟩ := h3 φ φ.continuous hφs hsupp
    have hfin := (hint β (Set.mem_univ β)).lintegral_lt_top
    have hnull : fib β (qf ⁻¹' {β} ∩ {x | x ≠ 0})ᶜ = 0 := h1 β
    have hmeas : Measurable fun x => ENNReal.ofReal (φ x) :=
      ENNReal.measurable_ofReal.comp φ.continuous.measurable
    calc fib β K ≤ fib β ((K ∩ qf ⁻¹' {β}) ∪ (qf ⁻¹' {β} ∩ {x | x ≠ 0})ᶜ) := by
          apply measure_mono
          intro x hx
          by_cases hxS : qf x = β
          · exact Or.inl ⟨hx, hxS⟩
          · exact Or.inr fun hx' => hxS hx'.1
      _ ≤ fib β (K ∩ qf ⁻¹' {β}) + fib β (qf ⁻¹' {β} ∩ {x | x ≠ 0})ᶜ := measure_union_le _ _
      _ = ∫⁻ _ in K ∩ qf ⁻¹' {β}, 1 ∂(fib β) := by rw [hnull, add_zero, setLIntegral_one]
      _ ≤ ∫⁻ x in K ∩ qf ⁻¹' {β}, ENNReal.ofReal (φ x) ∂(fib β) :=
          setLIntegral_mono hmeas fun x hx => by rw [hφ1 hx]; simp
      _ ≤ ∫⁻ x, ENNReal.ofReal (φ x) ∂(fib β) := setLIntegral_le_lintegral _ _
      _ < ⊤ := hfin
  · exact GlobalTheory.IsFibreFamily_eq_at (dx P Q) qf {x | x ≠ 0} {x | x ≠ 0} {x | x ≠ 0} Set.univ
      Set.univ _ fib β hq.measurable hO subset_rfl subset_rfl hqO isOpen_univ isOpen_univ
      (Set.mem_univ β) (Set.mem_univ β) (isDxDq_map h g) h

end GlobalTheory.FibreInvariance
end
end

section

open GlobalTheory.MomOne GlobalTheory.MomN PowerSeries
open scoped ComplexConjugate

theorem _root_.GlobalTheory.T.mahlerCoefficient_norm_le_one_iff_jets_boundedMeasureMoments : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (κ : Type) [Fintype κ] (v : κ → V) (G : V → ℂ), ContDiff ℂ ⊤ G → (MomInt ι v G ↔ ∀ n, ‖ι (mahler v G n)‖ ≤ 1) := by
  first | exact @GlobalTheory.MomCrit.momInt_iff_norm_mahler_le | exact GlobalTheory.MomCrit.momInt_iff_norm_mahler_le | (intros; apply GlobalTheory.MomCrit.momInt_iff_norm_mahler_le <;> assumption)
end

section

open GlobalTheory.MomOne GlobalTheory.MomN PowerSeries
open scoped ComplexConjugate

theorem _root_.GlobalTheory.T.mahlerJetCoefficient_mul : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (κ : Type) [Fintype κ] [DecidableEq κ] (v : κ → V) (F G : V → ℂ), ContDiff ℂ ⊤ F → ContDiff ℂ ⊤ G → ∀ n : κ → ℕ, mahler v (fun z => F z * G z) n = ∑ k ∈ Fintype.piFinset (fun i => Finset.range (n i + 1)), mahler v F k * mahler v G (fun i => n i - k i) := by
  first | exact @GlobalTheory.MomN.mahler_mul | exact GlobalTheory.MomN.mahler_mul | (intros; apply GlobalTheory.MomN.mahler_mul <;> assumption)
end

section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

theorem _root_.GlobalTheory.T.iteratedDeriv_logDeriv_dirichletL_via_nearby_zeros : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (σ t : ℝ) (k : ℕ), 1 < σ → σ ≤ 2 → (zerosDisc χ (2 + t * I) 3).Finite ∧ (∑ᶠ w ∈ zerosDisc χ (2 + t * I) 3, (ord χ w : ℝ)) ≤ C * Real.log (q * (|t| + 2)) ∧ ‖derSeries (fun n : ℕ => χ (n : ZMod q)) k (σ + t * I) - (if χ = 1 then 1 / ((σ : ℂ) + t * I - 1) ^ (k + 1) else 0) + ∑ᶠ w ∈ zerosDisc χ (2 + t * I) 3, (ord χ w : ℂ) / ((σ : ℂ) + t * I - w) ^ (k + 1)‖ ≤ C * Real.log (q * (|t| + 2)) / σ ^ k := by
  first | exact @GlobalTheory.LogDerivHigher.main | exact GlobalTheory.LogDerivHigher.main | (intros; apply GlobalTheory.LogDerivHigher.main <;> assumption)
end

section

namespace GlobalTheory.CommutatorPowerEntry

open Finset

theorem comm_pow_entry (A : Type) [Ring A] (N : ℕ) (E : Matrix (Fin N) (Fin N) A)
    (h : GlobalTheory.Alc.GlRel E) (k : ℕ) :
    ∀ (a b c d : Fin N), E a b * (E ^ k) c d - (E ^ k) c d * E a b =
      (if b = c then (E ^ k) a d else (0 : A)) - if d = a then (E ^ k) c b else (0 : A) := by
  induction k with
  | zero =>
    intro a b c d
    simp only [pow_zero, Matrix.one_apply]
    by_cases hcd : c = d <;> by_cases hbc : b = c <;> by_cases hda : d = a <;>
      simp_all [eq_comm]
  | succ k ih =>
    intro a b c d
    have h' : ∀ c d : Fin N, E a b * E c d - E c d * E a b =
        (if b = c then E a d else 0) - (if d = a then E c b else 0) := h a b
    have key : ∀ x y : A, E a b * (x * y) - (x * y) * E a b =
        (E a b * x - x * E a b) * y + x * (E a b * y - y * E a b) := by
      intro x y; noncomm_ring
    simp only [pow_succ, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, key, ih, h']
    simp only [sub_mul, mul_sub, ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    by_cases hbc : b = c <;> by_cases hda : d = a <;> simp only [hbc, hda, if_true, if_false,
      Finset.sum_const_zero] <;> abel

theorem comm_trace_pow (A : Type) [Ring A] (N : ℕ) (E : Matrix (Fin N) (Fin N) A)
    (h : GlobalTheory.Alc.GlRel E) (k : ℕ) (a b : Fin N) :
    E a b * Matrix.trace (E ^ k) = Matrix.trace (E ^ k) * E a b := by
  rw [← sub_eq_zero]
  simp only [Matrix.trace, Matrix.diag, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib,
    comm_pow_entry A N E h k]
  simp [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem main : ∀ (A : Type) [inst : Ring A] (N : ℕ) (E : Matrix (Fin N) (Fin N) A), GlobalTheory.Alc.GlRel E → ∀ (k : ℕ), (∀ (a b c d : Fin N), E a b * (E ^ k) c d - (E ^ k) c d * E a b = (if b = c then (E ^ k) a d else (0 : A)) - if d = a then (E ^ k) c b else (0 : A)) ∧ ∀ (a b : Fin N), E a b * Matrix.trace (E ^ k) = Matrix.trace (E ^ k) * E a b := by
  intro A _ N E h k
  exact ⟨comm_pow_entry A N E h k, comm_trace_pow A N E h k⟩

end GlobalTheory.CommutatorPowerEntry
end

section

open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

theorem _root_.GlobalTheory.T.rayClassLFunctionFamily_continuation_growth : ∀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ), AnalyticOnNhd ℂ (𝓕.F χ) {s | 1 / 2 < s.re} ∧ (∀ s : ℂ, 1 < s.re → LSeriesSummable (𝓕.aChi χ) s ∧ 𝓕.F χ s = (if χ = 1 then s - 1 else 1) * LSeries (𝓕.aChi χ) s) ∧ (∀ s : ℂ, 11 / 20 ≤ s.re → ‖𝓕.F χ s‖ ≤ 300 * 𝓕.B * (‖s‖ + 1) ^ 2) ∧ (χ * χ = 1 → ∀ s : ℂ, 𝓕.F χ ((starRingEnd ℂ) s) = (starRingEnd ℂ) (𝓕.F χ s)) := by
  first | exact @GlobalTheory.Hk.RayCont.continuation_growth | exact GlobalTheory.Hk.RayCont.continuation_growth | (intros; apply GlobalTheory.Hk.RayCont.continuation_growth <;> assumption)
end

section

namespace GlobalTheory.Mem.An

theorem zeroCount_holds : GlobalTheory.Mem.An.ZeroCount := by
  obtain ⟨C, -, H⟩ := GlobalTheory.ZeroWindow.count_zeros_window
  refine ⟨C, fun q _ χ hχ t => ?_⟩
  have h := (H q χ hχ t).2
  simpa only [zsumR, zerosIn, zmult, mul_one] using h

end GlobalTheory.Mem.An
end
