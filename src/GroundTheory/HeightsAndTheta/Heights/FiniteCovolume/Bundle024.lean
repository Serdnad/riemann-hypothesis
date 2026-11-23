module

public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle020
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle023
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsStabilizerLevi
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle075
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle010
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle022
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PScalingLaw
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
import Mathlib.GroupTheory.FiniteAbelian.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Examples

@[expose] public section

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory
open scoped ENNReal

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]


omit [NumberField F] [NumberField E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem invApply_mul {h : HermitianForm F E W} {v : Basis ι E W} (a b : archUnitary h v)
    (y : InfinitePlace E → ι → ℂ) : invApply (a * b) y = invApply b (invApply a y) := by
  funext w
  simp only [invApply, _root_.mul_inv_rev, Subgroup.coe_mul, Pi.mul_apply, Units.val_mul,
    Matrix.mulVec_mulVec]


omit [NumberField F] [NumberField E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem invApply_of_mem_vecFixGroup {h : HermitianForm F E W} {v : Basis ι E W} {x₀ : W}
    {x : archUnitary h v} (hx : x ∈ vecFixGroup h v x₀) : invApply x (vecAt v x₀) = vecAt v x₀ :=
  funext fun w => mem_vecFixGroup.1 (inv_mem hx) w


omit [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem len_invApply_of_mem_stab {h : HermitianForm F E W} {v : Basis ι E W} (M : Majorant h v)
    {k : archUnitary h v} (hk : k ∈ M.stab) (y : InfinitePlace E → ι → ℂ) :
    M.len (invApply k y) = M.len y := by
  unfold Majorant.len
  congr 1
  refine Finset.sum_congr rfl fun w _ => ?_
  have hk' := inv_mem hk
  rw [Majorant.stab, Subgroup.mem_subgroupOf] at hk'
  have hA := mem_unitaryGroupMatrix.1 ((Subgroup.mem_pi _).1 hk' w (Set.mem_univ w))
  set A : Matrix ι ι ℂ := (((k⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)
    with hA_def
  have hA' : Aᴴ * M.P w * A = M.P w := hA
  simp only [invApply]
  rw [← hA_def, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, hA']


omit [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem vecStabGroup_le_vecFixGroup [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
    (h : HermitianForm F E W) (v : Basis ι E W) (La : AddSubgroup W) (x₀ : W) :
    vecStabGroup h v La x₀ ≤ vecFixGroup h v x₀ := by
  rintro _ ⟨γ, hγ, rfl⟩
  have e := archEmbed_smul_vecAt h v (γ : h.unitaryGroup) x₀
  rw [show (γ : h.unitaryGroup) • x₀ = x₀ from MulAction.mem_stabilizer_iff.1 hγ] at e
  exact fun w => congrFun e w

theorem ae_forall_ne_zero (κ : Type*) [Fintype κ] : ∀ᵐ b : κ → ℂ, ∀ w, b w ≠ 0 := by
  rw [ae_all_iff]
  intro w
  have h0 : volume ((fun b : κ → ℂ => b w) ⁻¹' {0}) = 0 :=
    Measure.pi_eval_preimage_null _ (measure_singleton 0)
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with b hb
  exact hb

theorem UnfoldingTorus.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (h₁ : ∀ M : Majorant h v,
      UnfoldAlongSubgroup.Statement (archUnitary h v) ((InfinitePlace E → ℂ) × M.stab))
    (h₂ : HaarParabolicCoordinates.Statement h v) (h₃ : StabilizerCovolumeFinite.Statement h v) :
    UnfoldingTorus.Statement h v := by
  intro M μ _ D La x₀ hLa hx₀ hne hiso
  obtain ⟨ν, κ, τ, hν, -, hκ, hτm, hτ, hμ⟩ := h₂ M μ x₀ hne hiso
  obtain ⟨FD₀, hFD₀, h0, htop⟩ := h₃ D La x₀ hLa hx₀ hne hiso ν hν
  refine ⟨ν FD₀, h0, htop, fun FD hFD t ht => ?_⟩
  set y₀ := vecAt v x₀ with hy₀
  set wt : (InfinitePlace E → ℂ) → ℝ≥0∞ := fun b => ∏ w, ‖b w‖ₑ ^ (2 * (finrank E W - 2))
    with hwt
  set S := {g : archUnitary h v | M.len (invApply g y₀) < t} with hS_def
  set T := {b : InfinitePlace E → ℂ | M.len (fun w => b w • y₀ w) < t} with hT_def
  have hS : MeasurableSet S := measurableSet_below M y₀ t

  have : SecondCountableTopology (vecStabGroup h v La x₀) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  have : DiscreteTopology (vecStabGroup h v La x₀) := by
    have := ArchLatticeDiscrete.proof h v La hLa.isLattice
    have hle : vecStabGroup h v La x₀ ≤ archLatticeGroup h v La := by
      rintro _ ⟨γ, -, rfl⟩
      exact ⟨(γ : h.unitaryGroup), γ.2, rfl⟩
    exact DiscreteTopology.of_continuous_injective (f := Subgroup.inclusion hle)
      (continuous_subtype_val.subtype_mk _) (Subgroup.inclusion_injective hle)
  have : Countable (vecStabGroup h v La x₀) :=
    TopologicalSpace.separableSpace_iff_countable.1 inferInstance

  let s : (InfinitePlace E → ℂ) × M.stab → archUnitary h v := fun y => τ y.1 * y.2
  have hwtm : Measurable wt :=
    Finset.measurable_prod _ fun w _ => (measurable_pi_apply w).enorm.pow_const _
  have hsm' : Measurable s := (hτm.comp measurable_fst).mul (measurable_subtype_coe.comp measurable_snd)
  have hsm : Measurable fun p : vecFixGroup h v x₀ × ((InfinitePlace E → ℂ) × M.stab) =>
      (p.1 : archUnitary h v) * s p.2 :=
    (measurable_subtype_coe.comp measurable_fst).mul (hsm'.comp measurable_snd)
  have hform : ∀ f : archUnitary h v → ℝ≥0∞, Measurable f → ∫⁻ g, f g ∂μ =
      ∫⁻ y, ∫⁻ x, f (x * s y) ∂ν ∂((volume.withDensity wt).prod κ) := by
    intro f hf
    have hin : Measurable fun y => ∫⁻ x : vecFixGroup h v x₀, f (x * s y) ∂ν :=
      (hf.comp hsm).lintegral_prod_left'
    rw [hμ f hf, lintegral_prod _ hin.aemeasurable,
      lintegral_withDensity_eq_lintegral_mul _ hwtm hin.lintegral_prod_right']
    rfl

  have hf : Measurable (S.indicator (1 : archUnitary h v → ℝ≥0∞)) := measurable_one.indicator hS
  have hinv : ∀ x : vecFixGroup h v x₀, ∀ g,
      S.indicator (1 : archUnitary h v → ℝ≥0∞) (x * g) = S.indicator 1 g := by
    intro x g
    have hx : invApply (x : archUnitary h v) y₀ = y₀ := invApply_of_mem_vecFixGroup x.2
    simp only [hS_def, Set.indicator_apply, Set.mem_ofPred_eq, invApply_mul, hx, Pi.one_apply]
  have key := h₁ M μ (vecFixGroup h v x₀) ν ((volume.withDensity wt).prod κ) s hsm hform
    (vecStabGroup h v La x₀) (vecStabGroup_le_vecFixGroup h v La x₀) FD FD₀ hFD hFD₀ _ hf hinv
  rw [Set.inter_comm, ← Measure.restrict_apply hS, ← lintegral_indicator_one hS, key]
  congr 1

  have hmS : Measurable fun y => S.indicator (1 : archUnitary h v → ℝ≥0∞) (s y) := hf.comp hsm'
  rw [lintegral_prod _ hmS.aemeasurable,
    lintegral_withDensity_eq_lintegral_mul _ hwtm hmS.lintegral_prod_right']
  refine lintegral_congr_ae ?_
  filter_upwards [ae_forall_ne_zero (InfinitePlace E)] with b hb
  have hk : ∀ k : M.stab, S.indicator (1 : archUnitary h v → ℝ≥0∞) (s (b, k)) =
      T.indicator 1 b := by
    intro k
    simp only [s, Set.indicator_apply, hS_def, hT_def, Set.mem_ofPred_eq, invApply_mul, hτ b hb,
      len_invApply_of_mem_stab M k.2, Pi.one_apply]
  simp only [Pi.mul_apply, hk, lintegral_const, measure_univ, mul_one]
  by_cases hbT : b ∈ T
  · simp [Set.indicator_of_mem hbT]
  · simp [Set.indicator_of_notMem hbT]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix

noncomputable section

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [NumberField E]

def LineEigenvalue.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ x₀ : W, x₀ ≠ 0 → ∃ β : lineStab h v x₀ → (InfinitePlace E → ℂˣ), Continuous β ∧
    ∀ (p : lineStab h v x₀) (w : InfinitePlace E),
      (((p : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w =
        (β p w : ℂ) • vecAt v x₀ w

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def UnipRadicalOfRational.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (x₀ : W) (γ : h.unitaryGroup), γ • x₀ = x₀ →
    (∀ z : W, h.toSesq x₀ z = 0 → ∃ a : E, γ • z = z + a • x₀) →
    archEmbed h v γ ∈ unipRadical h v x₀

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology

noncomputable section

section Coordinate

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
  [NumberField E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def unipCoord (h : HermitianForm F E W) (v : Basis ι E W) (x₀ w₀ : W) (n : unipRadical h v x₀) :
    InfinitePlace E → ι → ℂ :=
  fun w => (((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v w₀ w -
    vecAt v w₀ w

omit [NumberField E] in
theorem unipCoord_apply (h : HermitianForm F E W) (v : Basis ι E W) (x₀ w₀ : W)
    (n : unipRadical h v x₀) (w : InfinitePlace E) :
    unipCoord h v x₀ w₀ n w =
      (((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v w₀ w -
        vecAt v w₀ w :=
  rfl


omit [NumberField E] in
theorem continuous_unipCoord (h : HermitianForm F E W) (v : Basis ι E W) (x₀ w₀ : W) :
    Continuous (unipCoord h v x₀ w₀) := by
  refine continuous_pi fun w => ?_
  have hc : Continuous fun n : unipRadical h v x₀ =>
      (((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) :=
    Units.continuous_val.comp ((continuous_apply w).comp
      (continuous_subtype_val.comp continuous_subtype_val))
  exact (hc.matrix_mulVec continuous_const).sub continuous_const

def UnipotentCoordProper.Statement [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
    (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ x₀ w₀ : W, IsHyperbolicPair h x₀ w₀ → ∀ K : Set (InfinitePlace E → ι → ℂ), IsCompact K →
    IsCompact {n : unipRadical h v x₀ | unipCoord h v x₀ w₀ n ∈ K}

end Coordinate

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

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def RadicalTorusModulus.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ x₀ w₀ : W, IsHyperbolicPair h x₀ w₀ →
    ∀ (g : archUnitary h v) (a : InfinitePlace E → ℂ),
    (∀ w, ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w = a w • vecAt v x₀ w) →
    (∀ w, ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v w₀ w =
      (starRingEnd ℂ (a w))⁻¹ • vecAt v w₀ w) →
    (∀ w (z : ι → ℂ), star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ z) = 0 →
      star (vecAt v w₀ w) ⬝ᵥ (gramAt h v w *ᵥ z) = 0 →
      ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ z = z) →
    ∀ (μ : Measure (unipRadical h v x₀)) [μ.IsHaarMeasure] (f : archUnitary h v → ℝ≥0∞),
      Measurable f →
      ∫⁻ n, f (g * n * g⁻¹) ∂μ = (∏ w, ‖a w‖ₑ⁻¹ ^ (2 * (finrank E W - 1))) * ∫⁻ n, f n ∂μ

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module
open scoped Pointwise

noncomputable section

namespace CongruenceLift

theorem exists_nsmul_mem {E W : Type*} [Field E] [NumberField E] [AddCommGroup W] [Module E W]
    {La : AddSubgroup W} (hLa : IsLattice E La) (w : W) : ∃ d : ℕ, 0 < d ∧ d • w ∈ La :=
  _root_.UpperTheory.Reformulated.B.ExistsNsmulMem.exists_nsmul_mem hLa w

theorem exists_congruence {V G : Type*} [AddCommGroup V] [Group G] [DistribMulAction G V]
    (L : AddSubgroup V) (hL : L.FG) (d : ℕ) (hd : 0 < d) :
    ∃ K : Subgroup (MulAction.stabilizer G L), K.index ≠ 0 ∧
      ∀ k ∈ K, ∀ y ∈ L, ∃ u ∈ L, d • u = (k : G) • y - y := by
  set S := MulAction.stabilizer G L
  have hS : ∀ (s : S) (y : V), y ∈ L → (s : G) • y ∈ L := fun s y hy => by
    have := AddSubgroup.smul_mem_pointwise_smul y (s : G) L hy
    rwa [MulAction.mem_stabilizer_iff.1 s.2] at this
  let f : S → L →+ L := fun s =>
    { toFun := fun y => ⟨(s : G) • (y : V), hS s y y.2⟩
      map_zero' := Subtype.ext (smul_zero _)
      map_add' := fun y z => Subtype.ext (smul_add _ _ _) }
  set N : AddSubgroup L := (nsmulAddMonoidHom (α := L) d).range
  have hN : ∀ s, N ≤ N.comap (f s) := by
    rintro s _ ⟨u, rfl⟩
    exact ⟨f s u, by simp [map_nsmul]⟩
  let _ : MulAction S (L ⧸ N) :=
    { smul := fun s q => QuotientAddGroup.map N N (f s) (hN s) q
      one_smul := fun q => QuotientAddGroup.induction_on q fun y => by
        change QuotientAddGroup.map N N (f 1) (hN 1) (y : L ⧸ N) = y
        rw [QuotientAddGroup.map_mk]
        congr 1
        exact Subtype.ext (one_smul G (y : V))
      mul_smul := fun s t q => QuotientAddGroup.induction_on q fun y => by
        change QuotientAddGroup.map N N (f (s * t)) (hN _) (y : L ⧸ N) =
          QuotientAddGroup.map N N (f s) (hN s) (QuotientAddGroup.map N N (f t) (hN t) y)
        rw [QuotientAddGroup.map_mk, QuotientAddGroup.map_mk, QuotientAddGroup.map_mk]
        congr 1
        exact Subtype.ext (mul_smul (s : G) (t : G) (y : V)) }
  have hfg : AddGroup.FG L := (AddGroup.fg_iff_addSubgroup_fg L).2 hL
  have hfin : Finite (L ⧸ N) := by
    refine AddCommGroup.finite_of_fg_isAddTorsion _ fun q => ?_
    refine QuotientAddGroup.induction_on q fun y => ?_
    rw [isOfFinAddOrder_iff_nsmul_eq_zero]
    refine ⟨d, hd, ?_⟩
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
    exact ⟨y, rfl⟩
  refine ⟨(MulAction.toPermHom S (L ⧸ N)).ker, Subgroup.FiniteIndex.index_ne_zero, ?_⟩
  intro k hk y hy
  have hq := DFunLike.congr_fun (MonoidHom.mem_ker.1 hk) ((⟨y, hy⟩ : L) : L ⧸ N)
  simp only [MulAction.toPermHom_apply, MulAction.toPerm_apply, Equiv.Perm.coe_one, id_eq] at hq
  change QuotientAddGroup.map N N (f k) (hN k) _ = _ at hq
  rw [QuotientAddGroup.map_mk, QuotientAddGroup.eq] at hq
  obtain ⟨u, hu⟩ := hq
  refine ⟨-(u : V), L.neg_mem u.2, ?_⟩
  have := congrArg Subtype.val hu
  simp only [nsmulAddMonoidHom_apply, AddSubgroup.coe_nsmul, AddSubgroup.coe_add,
    AddSubgroup.coe_neg] at this
  rw [smul_neg, this]
  change -(-((k : G) • y) + y) = (k : G) • y - y
  abel

end CongruenceLift

variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

theorem CongruenceLift.proof [FiniteDimensional E W] (h : HermitianForm F E W) :
    CongruenceLift.Statement h := by
  intro D La x₀ w₀ hLa hx₀ hp h' hh'
  obtain ⟨d, hd, hdw⟩ := CongruenceLift.exists_nsmul_mem hLa.isLattice w₀
  set La' : AddSubgroup (hypComplement h x₀ w₀) := La.comap (hypComplement h x₀ w₀).subtype.toAddMonoidHom
  have dec : ∀ x ∈ La, h.toSesq (d • w₀) x • x₀ ∈ La ∧ (h.toSesq x₀ x * d) • w₀ ∈ La ∧
      d • x - h.toSesq (d • w₀) x • x₀ - (h.toSesq x₀ x * d) • w₀ =
        ((d • ComplementExtension.proj hp x : hypComplement h x₀ w₀) : W) := by
    intro x hx
    refine ⟨hLa.isLattice.smul_mem ⟨_, hLa.integral _ hdw x hx⟩ x₀ hx₀, ?_, ?_⟩
    · have := hLa.isLattice.smul_mem ⟨_, hLa.integral _ hx₀ x hx⟩ _ hdw
      rwa [← Nat.cast_smul_eq_nsmul E, smul_smul] at this
    · rw [Submodule.coe_smul_of_tower, ComplementExtension.proj_apply, map_nsmul,
        LinearMap.smul_apply]
      simp only [← Nat.cast_smul_eq_nsmul E, smul_eq_mul]
      module
  obtain ⟨D', hD'⟩ := ComplementLattice.proof h x₀ w₀ hp h' hh' D d hd
  have hLa' : IsDIntegral h' D' La' := hD' La hLa fun x hx =>
    ⟨_, (dec x hx).1, _, (dec x hx).2.1, by rw [(dec x hx).2.2]; exact Submodule.coe_mem _⟩
  obtain ⟨K, hK, hcong⟩ : ∃ K : Subgroup (latticeStab h' La'), K.index ≠ 0 ∧
      ∀ k ∈ K, ∀ y ∈ La', ∃ u ∈ La', d • u = (k : h'.unitaryGroup) • y - y :=
    CongruenceLift.exists_congruence (G := h'.unitaryGroup) La' hLa'.isLattice.fg d hd
  have key : ∀ k ∈ K, ∀ γ : h.unitaryGroup, γ • x₀ = x₀ → γ • w₀ = w₀ →
      (∀ x : hypComplement h x₀ w₀, γ • (x : W) = ((((k : latticeStab h' La') : h'.unitaryGroup) • x : hypComplement h x₀ w₀) : W)) →
      ∀ x ∈ La, γ • x ∈ La := by
    intro k hk γ h1 h2 h3 x hx
    obtain ⟨hA, hB, hC⟩ := dec x hx
    set y : hypComplement h x₀ w₀ := d • ComplementExtension.proj hp x
    have hy : y ∈ La' := by
      change (y : W) ∈ La
      rw [← hC]
      exact La.sub_mem (La.sub_mem (La.nsmul_mem hx d) hA) hB
    obtain ⟨u, hu, hdu⟩ := hcong k hk y hy
    have hx' : d • x = h.toSesq (d • w₀) x • x₀ + (y : W) + (h.toSesq x₀ x * d) • w₀ := by
      rw [← hC]
      abel
    have hγ : d • (γ • x) = d • (x + (u : W)) := by
      have hdu' : (((k : latticeStab h' La') : h'.unitaryGroup) • y : hypComplement h x₀ w₀) = (y : W) + d • (u : W) := by
        rw [← Submodule.coe_smul_of_tower, hdu]
        simp
      rw [← smul_comm, hx', smul_add, smul_add, smul_comm γ (h.toSesq (d • w₀) x),
        smul_comm γ (h.toSesq x₀ x * d), h1, h2, h3, hdu', smul_add, hx']
      abel
    have hne : (d : E) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
    have := smul_right_injective W hne (by simpa only [Nat.cast_smul_eq_nsmul] using hγ)
    rw [this]
    exact La.add_mem hx hu
  refine ⟨D', La', K.map (latticeStab h' La').subtype, hLa', Subgroup.map_subtype_le K, ?_, ?_⟩
  · rw [Subgroup.relIndex, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective (latticeStab h' La').subtype_injective]
    exact hK
  · rintro _ ⟨k, hk, rfl⟩ γ h1 h2 h3
    refine MulAction.mem_stabilizer_iff.2 (le_antisymm ?_ ?_)
    · intro z hz
      obtain ⟨x, hx, rfl⟩ := (AddSubgroup.mem_smul_pointwise_iff_exists z γ La).1 hz
      exact key k hk γ h1 h2 h3 x hx
    · intro z hz
      refine AddSubgroup.mem_pointwise_smul_iff_inv_smul_mem.2 ?_
      refine key k⁻¹ (K.inv_mem hk) γ⁻¹ (inv_smul_eq_iff.2 h1.symm) (inv_smul_eq_iff.2 h2.symm)
        (fun x => inv_smul_eq_iff.2 ?_) z hz
      rw [h3]
      simp

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end
