module

public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsVecFixGroup
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary
public import Mathlib.Topology.Algebra.Group.Units
import GroundTheory.AutomorphicForms.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle020
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle010
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PLinePairOrbitsFinite
import Mathlib.Algebra.Module.StablyFree.Basic
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

def TorusModulus.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ x₀ w₀ : W, IsHyperbolicPair h x₀ w₀ →
    ∀ (g : archUnitary h v) (a : InfinitePlace E → ℂ),
    (∀ w, ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w = a w • vecAt v x₀ w) →
    (∀ w, ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v w₀ w =
      (starRingEnd ℂ (a w))⁻¹ • vecAt v w₀ w) →
    (∀ w (z : ι → ℂ), star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ z) = 0 →
      star (vecAt v w₀ w) ⬝ᵥ (gramAt h v w *ᵥ z) = 0 →
      ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ z = z) →
    ∀ (ν : Measure (vecFixGroup h v x₀)) [ν.IsHaarMeasure] (f : archUnitary h v → ℝ≥0∞),
      Measurable f →
      ∫⁻ x, f (g * x * g⁻¹) ∂ν = (∏ w, ‖a w‖ₑ⁻¹ ^ (2 * (finrank E W - 1))) * ∫⁻ x, f x ∂ν

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory
open scoped ENNReal ComplexOrder

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]


omit [NumberField F] [NumberField E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] [Fintype ι]
  [DecidableEq ι] in
theorem two_le_finrank_of_isotropic [FiniteDimensional E W] (h : HermitianForm F E W) {x₀ : W}
    (hne : x₀ ≠ 0) (hiso : h.toSesq x₀ x₀ = 0) : 2 ≤ finrank E W := by
  by_contra hlt
  have hpos : 0 < finrank E W := Module.finrank_pos_iff_exists_ne_zero.mpr ⟨x₀, hne⟩
  have h1 : finrank E W = 1 := by omega
  have hspan := (finrank_eq_one_iff_of_nonzero' x₀ hne).mp h1
  apply hne
  apply h.nonsingular.1
  rw [map_zero]
  ext y
  obtain ⟨c, rfl⟩ := hspan y
  rw [LinearMap.zero_apply, map_smul, hiso, smul_zero]


omit [DecidableEq ι] in
theorem re_form_smul (P : Matrix ι ι ℂ) (b : ℂ) (y : ι → ℂ) :
    (star (b • y) ⬝ᵥ (P *ᵥ (b • y))).re = (star y ⬝ᵥ (P *ᵥ y)).re * ‖b‖ ^ 2 := by
  have hb : star b * b = ((‖b‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_mul']
    norm_cast
  rw [star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
    ← mul_assoc, hb, Complex.re_ofReal_mul, mul_comm]

theorem UnfoldingIntegral.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (h₁ : UnfoldingTorus.Statement h v)
    (h₂ : TorusIntegralHomogeneous.Statement (InfinitePlace E))
    (h₃ : DiscreteFundamentalDomain.Statement (archUnitary h v)) :
    UnfoldingIntegral.Statement h v := by
  intro M μ _ D La x₀ hLa hx₀ hne hiso
  have : FiniteDimensional E W := v.finiteDimensional_of_finite

  have hdisc : DiscreteTopology (vecStabGroup h v La x₀) := by
    have := ArchLatticeDiscrete.proof h v La hLa.isLattice
    have hle : vecStabGroup h v La x₀ ≤ archLatticeGroup h v La := by
      rintro _ ⟨γ, -, rfl⟩
      exact ⟨(γ : h.unitaryGroup), γ.2, rfl⟩
    exact DiscreteTopology.of_continuous_injective (f := Subgroup.inclusion hle)
      (continuous_subtype_val.subtype_mk _) (Subgroup.inclusion_injective hle)
  obtain ⟨FD, -, hFD⟩ := h₃ μ _ hdisc
  obtain ⟨c, hc0, hctop, hc⟩ := h₁ M μ D La x₀ hLa hx₀ hne hiso
  set y := vecAt v x₀ with hy
  set q : InfinitePlace E → ℝ := fun w => (star (y w) ⬝ᵥ (M.P w *ᵥ y w)).re with hq_def
  have hq : ∀ w, 0 < q w := fun w =>
    (Complex.pos_iff.mp ((M.posDef w).dotProduct_mulVec_pos (VecAtNeZero.proof v x₀ hne w))).1
  obtain ⟨C, hC0, hCtop, hC⟩ := h₂ q hq (finrank E W - 2)

  obtain ⟨k, hk⟩ : ∃ k, finrank E W = k + 2 :=
    ⟨finrank E W - 2, by have := two_le_finrank_of_isotropic h hne hiso; omega⟩
  have hcard : Fintype.card (InfinitePlace E) = finrank ℚ F := by
    have h1 := IsTotallyComplex.finrank (K := E)
    have h2 : finrank ℚ F * finrank F E = finrank ℚ E := Module.finrank_mul_finrank ℚ F E
    rw [Algebra.IsQuadraticExtension.finrank_eq_two F E] at h2
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero]
    omega
  have hexp : (2 * (finrank E W - 2) + 2) * Fintype.card (InfinitePlace E) =
      2 * finrank ℚ F * (finrank E W - 1) := by
    rw [hcard, hk, Nat.add_sub_cancel, show k + 2 - 1 = k + 1 by omega]
    ring
  refine ⟨FD, hFD, c * C, ENNReal.mul_pos hc0.ne' hC0.ne', ENNReal.mul_lt_top hctop hCtop,
    fun t ht => ?_⟩

  have hset : {b : InfinitePlace E → ℂ | M.len (fun w => b w • y w) < t} =
      {b | ∑ w, q w * ‖b w‖ ^ 2 < t ^ 2} := by
    ext b
    simp only [Set.mem_ofPred_eq, Majorant.len, Real.sqrt_lt' ht, re_form_smul, hq_def,
      mul_comm]
  rw [hc FD hFD t ht, hset, hC t ht, hexp]
  exact (mul_assoc c C _).symm

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module

noncomputable section

theorem isAddTorsionFree_of_module (K V : Type*) [Field K] [CharZero K] [AddCommGroup V]
    [Module K V] : IsAddTorsionFree V := by
  letI : HasUniqueDiv V := HasUniqueDiv.of_isTorsionFree K V
  infer_instance

theorem fg_of_fg_map_of_injective {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    {H : AddSubgroup A} (φ : A →+ B) (hφ : Function.Injective φ) (hH : (H.map φ).FG) : H.FG := by
  have h2 : H.toIntSubmodule.FG := by
    refine Submodule.fg_of_fg_map_injective φ.toIntLinearMap hφ ?_
    have : H.toIntSubmodule.map φ.toIntLinearMap = (H.map φ).toIntSubmodule := by
      ext x
      simp
    rw [this]
    exact (Submodule.fg_iff_addSubgroup_fg _).2 hH
  exact (Submodule.fg_iff_addSubgroup_fg _).1 h2

section Complement

variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]


omit [NumberField E] in
theorem factorial_nsmul_mem_of_mem_dual {h : HermitianForm F E W} {D : ℕ} {La : AddSubgroup W}
    (hLa : IsDIntegral h D La) {y : W} (hy : y ∈ dualLattice h La) : D.factorial • y ∈ La := by
  have hk : La.relIndex (dualLattice h La) • y ∈ La := by
    have := AddSubgroup.nsmul_index_mem (La.addSubgroupOf (dualLattice h La)) ⟨y, hy⟩
    exact AddSubgroup.mem_addSubgroupOf.1 this
  obtain ⟨c, hc⟩ := Nat.dvd_factorial (Nat.pos_of_ne_zero hLa.index_ne_zero) hLa.index_le
  rw [hc, mul_comm, ← smul_smul]
  exact La.nsmul_mem hk c

theorem ComplementLattice.proof (h : HermitianForm F E W) [FiniteDimensional E W] :
    ComplementLattice.Statement h := by
  intro v₀ w₀ hvw h' hh' D n hn
  refine ⟨(D.factorial * n) ^ (finrank ℚ E * finrank E W), ?_⟩
  intro La hLa hdec
  set P : AddSubgroup (hypComplement h v₀ w₀) := La.comap (hypComplement h v₀ w₀).subtype.toAddMonoidHom with hP
  obtain ⟨hvv, hww, hvw1⟩ := hvw
  have hwv1 : h.toSesq w₀ v₀ = 1 := by
    rw [← h.isSymm.eq v₀ w₀, hvw1, map_one]
  have hsymm0 : ∀ x y : W, h.toSesq x y = 0 → h.toSesq y x = 0 := fun x y hxy => by
    rw [← h.isSymm.eq x y, hxy, map_zero]
  have memP : ∀ x : (hypComplement h v₀ w₀), x ∈ P ↔ (x : W) ∈ La := fun x => Iff.rfl

  let π₀ : W →ₗ[E] W :=
    LinearMap.id - (h.toSesq w₀).smulRight v₀ - (h.toSesq v₀).smulRight w₀
  have hπ₀ : ∀ x, π₀ x = x - h.toSesq w₀ x • v₀ - h.toSesq v₀ x • w₀ := fun x => rfl
  have hπ₀mem : ∀ x, π₀ x ∈ (hypComplement h v₀ w₀) := by
    intro x
    rw [hπ₀, mem_hypComplement]
    constructor <;> simp only [map_sub, map_smul, smul_eq_mul, hvv, hww, hvw1, hwv1] <;> ring
  have hfix : ∀ y ∈ (hypComplement h v₀ w₀), π₀ y = y := fun y hy => by
    rw [mem_hypComplement] at hy
    rw [hπ₀, hy.1, hy.2]
    simp
  have hπv : π₀ v₀ = 0 := by
    rw [hπ₀, hwv1, hvv]
    simp
  have hπw : π₀ w₀ = 0 := by
    rw [hπ₀, hww, hvw1]
    simp

  have hz : ∀ x ∈ La, ∃ a b : E, a • v₀ ∈ La ∧ b • w₀ ∈ La ∧
      n • x - a • v₀ - b • w₀ ∈ (hypComplement h v₀ w₀) ∧ n • x - a • v₀ - b • w₀ ∈ La ∧
      n • π₀ x = n • x - a • v₀ - b • w₀ := by
    intro x hx
    obtain ⟨a, ha, b, hb, hmem⟩ := hdec x hx
    change a • v₀ ∈ La at ha
    change b • w₀ ∈ La at hb
    refine ⟨a, b, ha, hb, hmem, La.sub_mem (La.sub_mem (La.nsmul_mem hx n) ha) hb, ?_⟩
    rw [← hfix _ hmem, map_sub, map_sub, map_nsmul, map_smul, map_smul, hπv, hπw]
    simp

  have hPlat : IsLattice E P := by
    refine ⟨fun a x hx => ?_, ?_, ?_⟩
    · rw [memP] at hx ⊢
      exact hLa.isLattice.smul_mem a _ hx
    · refine fg_of_fg_map_of_injective (hypComplement h v₀ w₀).subtype.toAddMonoidHom Subtype.val_injective ?_
      exact fg_of_le_fg (AddSubgroup.map_comap_le _ _) hLa.isLattice.fg
    · let π : W →ₗ[E] (hypComplement h v₀ w₀) := π₀.codRestrict (hypComplement h v₀ w₀) hπ₀mem
      have hrange : LinearMap.range π = ⊤ :=
        LinearMap.range_eq_top.2 fun y => ⟨y, Subtype.ext (hfix y y.2)⟩
      rw [eq_top_iff, ← hrange, LinearMap.range_eq_map, ← hLa.isLattice.span_eq_top,
        Submodule.map_span, Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨a, b, -, -, -, hzLa, hkey⟩ := hz x hx
      have hnE : (n : E) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
      have hnx : (n : E) • π x ∈ P := by
        rw [memP, Submodule.coe_smul_of_tower, Nat.cast_smul_eq_nsmul]
        change n • π₀ x ∈ La
        rw [hkey]
        exact hzLa
      have : π x = (n : E)⁻¹ • ((n : E) • π x) := by
        rw [smul_smul, inv_mul_cancel₀ hnE, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span hnx)

  have hPint : IsIntegralOn h' P := fun x hx y hy => by
    rw [hh']
    exact hLa.integral _ hx _ hy
  set N := D.factorial * n with hN
  have hNpos : 0 < N := Nat.mul_pos (Nat.factorial_pos D) hn
  set G := dualLattice h' P with hG
  have hPG : P ≤ G := fun x hx y hy => hPint x hx y hy

  have hNG : G.map (nsmulAddMonoidHom N) ≤ P := by
    rintro _ ⟨y', hy', rfl⟩
    have hdual : n • (y' : W) ∈ dualLattice h La := by
      intro x hx
      obtain ⟨a, b, -, -, hmem, hzLa, -⟩ := hz x hx
      have hy0 := (mem_hypComplement.1 y'.2)
      have e1 : h.toSesq (y' : W) v₀ = 0 := hsymm0 _ _ hy0.1
      have e2 : h.toSesq (y' : W) w₀ = 0 := hsymm0 _ _ hy0.2
      have hnx : n • x = (n • x - a • v₀ - b • w₀) + a • v₀ + b • w₀ := by abel
      have key : h.toSesq (n • (y' : W)) x = h.toSesq (y' : W) (n • x - a • v₀ - b • w₀) := by
        rw [map_nsmul, LinearMap.smul_apply, ← map_nsmul]
        conv_lhs => rw [hnx]
        rw [map_add (f := _), map_add (f := _), map_smul, map_smul, e1, e2]
        simp
      rw [key]
      have := hy' ⟨_, hmem⟩ hzLa
      rwa [hh'] at this
    have h2 := factorial_nsmul_mem_of_mem_dual hLa hdual
    rw [nsmulAddMonoidHom_apply, memP, Submodule.coe_smul_of_tower, hN, ← smul_smul]
    exact h2

  have : IsAddTorsionFree (hypComplement h v₀ w₀) := isAddTorsionFree_of_module E (hypComplement h v₀ w₀)
  have : HasUniqueDiv (hypComplement h v₀ w₀) := HasUniqueDiv.of_isTorsionFree E _
  have hGfg : G.FG := fg_of_fg_map_of_injective (nsmulAddMonoidHom N)
    (AddSubgroup.nsmulAddMonoidHom_injective_of_isTorsionFree hNpos.ne')
    (fg_of_le_fg hNG hPlat.fg)
  have : Module.Finite ℤ G.toIntSubmodule :=
    Module.Finite.iff_fg.2 ((Submodule.fg_iff_addSubgroup_fg _).2 hGfg)
  have : Module.Finite ℤ G := inferInstanceAs (Module.Finite ℤ G.toIntSubmodule)
  have hrank : finrank ℤ G ≤ finrank ℚ E * finrank E W := by
    letI : Module ℚ W := Module.compHom W (algebraMap ℚ E)
    have : IsScalarTower ℚ E W := ⟨fun q e w => by
      change (q • e) • w = algebraMap ℚ E q • e • w
      rw [Algebra.smul_def, mul_smul]⟩
    have : Module.Finite ℚ W := Module.Finite.trans E W
    let b := Module.finBasis ℤ G
    let f : G →ₗ[ℤ] W := ((hypComplement h v₀ w₀).subtype.toAddMonoidHom.comp G.subtype).toIntLinearMap
    have hf : Function.Injective f := Subtype.val_injective.comp Subtype.val_injective
    have hliZ : LinearIndependent ℤ (f ∘ b) :=
      b.linearIndependent.map' f (LinearMap.ker_eq_bot.mpr hf)
    have hliQ : LinearIndependent ℚ (f ∘ b) := (LinearIndependent.iff_fractionRing ℤ ℚ).mp hliZ
    have := hliQ.fintype_card_le_finrank
    rw [Fintype.card_fin, ← Module.finrank_mul_finrank ℚ E W] at this
    exact this
  have hidx : P.relIndex G ≤ N ^ finrank ℤ G := by
    rw [← AddSubgroup.relIndex_map_nsmul N G]
    refine AddSubgroup.relIndex_le_of_le_left hNG ?_
    rw [AddSubgroup.relIndex_map_nsmul]
    positivity
  refine ⟨hPlat, hPint, fun h0 => ?_, ?_⟩
  · have := AddSubgroup.relIndex_eq_zero_of_le_left hNG h0
    rw [AddSubgroup.relIndex_map_nsmul] at this
    exact (pow_ne_zero _ hNpos.ne') this
  · exact hidx.trans (Nat.pow_le_pow_right hNpos hrank)

end Complement

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open MeasureTheory
open scoped ENNReal Pointwise

theorem UnfoldAlongSubgroup.proof (G Y : Type*) [Group G] [MeasurableSpace G] [MeasurableSpace Y] :
    UnfoldAlongSubgroup.Statement G Y := by
  intro μ H _ ν _ _ ρ _ s hm hμ Γ _ hΓH FD FD₀ hFD hFD₀ f hf hfH
  have hms : ∀ y, Measurable (fun x : H => (x : G) * s y) := fun y =>
    hm.comp measurable_prodMk_right

  have hnull : ∀ Z : Set G, μ Z = 0 →
      ∀ᵐ y ∂ρ, ν ((fun x : H => (x : G) * s y) ⁻¹' Z) = 0 := by
    intro Z hZ
    have hZm : MeasurableSet (toMeasurable μ Z) := measurableSet_toMeasurable μ Z
    have hin : ∀ y, ∫⁻ x, (toMeasurable μ Z).indicator 1 ((x : G) * s y) ∂ν =
        ν ((fun x : H => (x : G) * s y) ⁻¹' toMeasurable μ Z) := fun y => by
      rw [← lintegral_indicator_one (hZm.preimage (hms y))]
      rfl
    have h0 := hμ ((toMeasurable μ Z).indicator 1) (measurable_one.indicator hZm)
    rw [lintegral_indicator_one hZm, measure_toMeasurable, hZ] at h0
    simp only [hin] at h0
    have hmeas : Measurable fun y => ν ((fun x : H => (x : G) * s y) ⁻¹' toMeasurable μ Z) := by
      simp only [← hin]
      exact ((measurable_one.indicator hZm).comp hm).lintegral_prod_left'
    filter_upwards [(lintegral_eq_zero_iff hmeas).1 h0.symm] with y hy
    exact measure_mono_null (Set.preimage_mono (subset_toMeasurable μ Z)) hy

  let toΓ : Γ.subgroupOf H → Γ := fun γ => ⟨((γ : H) : G), Subgroup.mem_subgroupOf.1 γ.2⟩
  have htoΓ : Function.Injective toΓ := fun a b h => by
    simp only [toΓ, Subtype.mk.injEq] at h
    exact Subtype.ext (Subtype.ext h)
  have : Countable (Γ.subgroupOf H) := htoΓ.countable

  have hslice : ∀ y (γ : Γ.subgroupOf H) (A : Set G),
      (fun x : H => (x : G) * s y) ⁻¹' ((toΓ γ) • A) =
        γ • ((fun x : H => (x : G) * s y) ⁻¹' A) := by
    intro y γ A
    ext x
    simp only [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem, Subgroup.smul_def,
      smul_eq_mul, toΓ, InvMemClass.coe_inv, Subgroup.coe_mul, mul_assoc]

  obtain ⟨t, htFD, htm, htae⟩ := hFD.nullMeasurableSet.exists_measurable_subset_ae_eq
  have hZ1 : μ {g | ¬ ∃ γ : Γ, γ • g ∈ FD} = 0 := ae_iff.1 hFD.ae_covers
  have hZ2 : μ (FD \ t) = 0 := (ae_eq_set.1 htae).2
  have hZ3 : ∀ γ δ : Γ, ∀ᵐ y ∂ρ, γ ≠ δ →
      ν ((fun x : H => (x : G) * s y) ⁻¹' (γ • FD ∩ δ • FD)) = 0 := by
    intro γ δ
    by_cases h : γ = δ
    · exact ae_of_all _ fun _ h' => absurd h h'
    · filter_upwards [hnull _ (hFD.aedisjoint h)] with y hy _ using hy
  have hgood : ∀ᵐ y ∂ρ, ν ((fun x : H => (x : G) * s y) ⁻¹' t) = ν FD₀ := by
    filter_upwards [hnull _ hZ1, hnull _ hZ2, ae_all_iff.2 fun γ => ae_all_iff.2 (hZ3 γ)]
      with y h1 h2 h3
    have hae : (fun x : H => (x : G) * s y) ⁻¹' t =ᵐ[ν] (fun x : H => (x : G) * s y) ⁻¹' FD := by
      refine ae_eq_set.2 ⟨?_, h2⟩
      rw [Set.sdiff_eq_empty.2 (Set.preimage_mono htFD), measure_empty]
    have hFDy : IsFundamentalDomain (Γ.subgroupOf H) ((fun x : H => (x : G) * s y) ⁻¹' FD) ν :=
      { nullMeasurableSet := (htm.preimage (hms y)).nullMeasurableSet.congr hae
        ae_covers := by
          filter_upwards [measure_eq_zero_iff_ae_notMem.1 h1] with x hx
          simp only [Set.mem_preimage, Set.mem_ofPred_eq, not_not] at hx
          obtain ⟨γ, hγ⟩ := hx
          refine ⟨⟨⟨γ, hΓH γ.2⟩, Subgroup.mem_subgroupOf.2 γ.2⟩, ?_⟩
          simpa only [Set.mem_preimage, Subgroup.smul_def, smul_eq_mul, Subgroup.coe_mul,
            mul_assoc] using hγ
        aedisjoint := by
          intro γ δ hγδ
          change ν (γ • _ ∩ δ • _) = 0
          rw [← hslice, ← hslice, ← Set.preimage_inter]
          exact h3 _ _ (htoΓ.ne hγδ) }
    rw [measure_congr hae, hFDy.measure_eq hFD₀]
  have hsm : Measurable s := by
    convert hm.comp ((measurable_const : Measurable fun _ : Y => (1 : H)).prodMk measurable_id) using 1
    ext y
    simp
  calc ∫⁻ g in FD, f g ∂μ = ∫⁻ g in t, f g ∂μ := setLIntegral_congr htae.symm
    _ = ∫⁻ g, t.indicator f g ∂μ := (lintegral_indicator htm _).symm
    _ = ∫⁻ y, ∫⁻ x, t.indicator f ((x : G) * s y) ∂ν ∂ρ := hμ _ (hf.indicator htm)
    _ = ∫⁻ y, f (s y) * ν ((fun x : H => (x : G) * s y) ⁻¹' t) ∂ρ := by
      refine lintegral_congr fun y => ?_
      have he : (fun x : H => t.indicator f ((x : G) * s y)) =
          ((fun x : H => (x : G) * s y) ⁻¹' t).indicator fun _ => f (s y) := by
        ext x
        by_cases hx : (x : G) * s y ∈ t
        · simp [hx, hfH]
        · simp [hx]
      rw [he, lintegral_indicator_const (htm.preimage (hms y))]
    _ = ∫⁻ y, ν FD₀ * f (s y) ∂ρ := lintegral_congr_ae (by
      filter_upwards [hgood] with y hy
      rw [hy, mul_comm])
    _ = ν FD₀ * ∫⁻ y, f (s y) ∂ρ := lintegral_const_mul _ (hf.comp hsm)

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

def StabilizerCovolumeFinite.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (D : ℕ) (La : AddSubgroup W) (x₀ : W), IsDIntegral h D La → x₀ ∈ La → x₀ ≠ 0 →
    h.toSesq x₀ x₀ = 0 → ∀ (ν : Measure (vecFixGroup h v x₀)), ν.IsHaarMeasure →
    ∃ FD₀ : Set (vecFixGroup h v x₀),
      IsFundamentalDomain ((vecStabGroup h v La x₀).subgroupOf (vecFixGroup h v x₀)) FD₀ ν ∧
      0 < ν FD₀ ∧ ν FD₀ < ⊤

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end
