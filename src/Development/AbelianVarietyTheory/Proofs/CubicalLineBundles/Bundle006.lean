module

public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.TraceFormDualOneTraceFormDual
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.DedekindZetaEqSumRealEisenstein
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogCovolumeEqMeanClassGroup
public import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ArakelovDegreeEqDegreeOfFamily
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CMField
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot

@[expose] public section

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open scoped Matrix

namespace GlobalTheory

theorem exists_pos_nat_mem_fractionalIdeal {E : Type} [Field E] [NumberField E]
    {a : FractionalIdeal (nonZeroDivisors (𝓞 E)) E} (ha : a ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ (n : E) ∈ a := by
  obtain ⟨x, hx0, hx⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger ha
  have hI : (Ideal.span {x} : Ideal (𝓞 E)) ≠ ⊥ := by simpa using hx0
  obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {x}))
  refine ⟨Ideal.absNorm (Ideal.span {x}),
    Nat.pos_of_ne_zero fun h => hI (Ideal.absNorm_eq_zero_iff.1 h), ?_⟩
  have h := (a : Submodule (𝓞 E) E).smul_mem e hx
  rw [Algebra.smul_def, ← map_mul, he, map_natCast] at h
  exact h

theorem fractionalIdeal_smul_eq_span {E : Type} [Field E] [NumberField E] {r : ℕ}
    (a : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (L : Submodule (𝓞 E) (Fin r → E)) :
    (a : Submodule (𝓞 E) E) • L =
      Submodule.span (𝓞 E) {v | ∃ α ∈ a, ∃ u ∈ L, v = α • u} := by
  refine le_antisymm (Submodule.smul_le.2 fun α hα u hu => Submodule.subset_span ⟨α, hα, u, hu, rfl⟩)
    (Submodule.span_le.2 ?_)
  rintro _ ⟨α, hα, u, hu, rfl⟩
  exact Submodule.smul_mem_smul hα hu

theorem exists_dataX_of_perfect_traceForm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (𝔄 𝔄b : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (k : ℝ) (g : ℕ), (∀ a : E, a ∈ 𝔄b ↔ cc a ∈ 𝔄) → FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) X.ξ0 * 𝔄 * 𝔄b * (differentIdeal ℤ (𝓞 E) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) = 1 → (∀ τ : E →+* ℂ, ‖τ X.ξ0‖ = k) → k ≤ 1 → (∀ x ∈ X.Λ, ∀ y ∈ X.Λ, ∃ n : ℤ, EFf X.ξ0 X.Gm x y = n) → (∀ φ : X.Λ →+ ℤ, ∃ x ∈ X.Λ, ∀ y : X.Λ, (φ y : ℚ) = EFf X.ξ0 X.Gm x y) → 0 < g → (∀ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ → (∀ x ∈ X.Λ, ∃ y ∈ X.Λ, Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) x - x = (g : E) • y) → γ ∈ X.Γ) → ∃ Xx : DataX E r, Xx.toData = X ∧ Xx.g = g ∧ Xx.Λ = Submodule.span (𝓞 E) {v | ∃ a ∈ 𝔄, ∃ u ∈ Xx.L', v = a • u} := by
  intro E _ _ _ r X 𝔄 𝔄b k g hb hone habs hk hint hperf hg hcong
  have hbc : 𝔄b = conjFrac 𝔄 := by
    ext a; rw [mem_conjFrac]; exact hb a
  subst hbc
  have hA : 𝔄 ≠ 0 := by
    rintro rfl
    simp at hone
  have hΛ : ReciprocityTheory.MultiplicativeHeights.IsLattice X.Λ := ⟨X.Λ_fg, X.Λ_span⟩
  have hd := (perfect_iff_hermDual_eq X.ξ0_ne X.Gm_det hΛ).1 ⟨hint, hperf⟩
  have hself : hermDual X.Gm (((𝔄⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :
      Submodule (𝓞 E) E) • X.Λ) =
      ((𝔄⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) • X.Λ := by
    rw [hermDual_smul (inv_ne_zero hA), conjFrac_inv, inv_inv, hd, ← fractionalIdeal_mul_smul]
    congr 2
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← hone]; ring
  obtain ⟨hi, hdual⟩ := hermDual_eq_self_iff.1 hself
  obtain ⟨NA, hNA, hNA'⟩ := exists_pos_nat_mem_fractionalIdeal (inv_ne_zero hA)
  obtain ⟨NC, hNC, hNC'⟩ := exists_pos_nat_mem_fractionalIdeal hA
  have hk0 : 0 < k := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    rw [← habs τ, norm_pos_iff]
    exact (map_ne_zero τ).2 X.ξ0_ne
  refine ⟨{ toData := X
            k0 := 2 * k
            minWeight_pos := by positivity
            k0_le := by linarith
            ξ0_abs := fun τ => by rw [habs]; ring
            EF_int := hint
            EF_perf := hperf
            L' := ((𝔄⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) • X.Λ
            L'_fg := (isLattice_fractionalIdeal_smul (inv_ne_zero hA) hΛ).1
            L'_int := hi
            L'_dual := hdual
            NA := NA
            NC := NC
            NA_pos := hNA
            NC_pos := hNC
            NA_sub := fun x hx => Submodule.smul_mem_smul hNA' hx
            NC_sub := fun x hx => ?_
            g := g
            g_pos := hg
            cong := hcong }, rfl, rfl, ?_⟩
  · have h := Submodule.smul_mem_smul (show (NC : E) ∈ (𝔄 : Submodule (𝓞 E) E) from hNC') hx
    rwa [fractionalIdeal_smul_inv_smul hA] at h
  · change X.Λ = _
    rw [← fractionalIdeal_smul_eq_span, fractionalIdeal_smul_inv_smul hA]

end GlobalTheory
end

section

open NumberField
open scoped nonZeroDivisors UpperHalfPlane

namespace GlobalTheory

theorem IsIdealClassPoint.exists_lattice_eq {K : Type} [Field K] [NumberField K] {σ : K →+* ℂ}
    {𝔟 : (Ideal (𝓞 K))⁰} {τ : ℍ} (hτ : IsIdealClassPoint σ (ClassGroup.mk0 𝔟) τ)
    {P : PeriodPair} (hP : ∀ z, z ∈ P.lattice ↔ ∃ a ∈ (𝔟 : Ideal (𝓞 K)), z = σ (a : K)) :
    ∃ a : ℂ, a ≠ 0 ∧ ∀ x, x ∈ P.lattice ↔ ∃ m n : ℤ, a * (m * (τ : ℂ) + n) = x := by
  classical
  obtain ⟨𝔞, ω, h𝔞, hω⟩ := hτ
  set J := FractionalIdeal.mk0 K 𝔟 with hJ
  have hcl : ClassGroup.mk K (𝔞⁻¹ * J) = 1 := by
    rw [map_mul, map_inv, h𝔞, hJ, ClassGroup.mk_mk0, inv_mul_cancel]
  obtain ⟨x₀, hx₀⟩ := (ClassGroup.mk_eq_one_iff.1 hcl).principal

  have hJx : ((J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ x₀ * (𝔞 : FractionalIdeal (𝓞 K)⁰ K) := by
    have h1 : ((𝔞⁻¹ * J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
        FractionalIdeal.spanSingleton (𝓞 K)⁰ x₀ := by
      apply FractionalIdeal.coeToSubmodule_injective
      dsimp only
      rw [FractionalIdeal.coe_spanSingleton]
      exact hx₀
    have h2 : J = 𝔞 * (𝔞⁻¹ * J) := (mul_inv_cancel_left 𝔞 J).symm
    conv_lhs => rw [h2]
    rw [Units.val_mul, h1, mul_comm]
  have hmemJ : ∀ y : K, (∃ b ∈ (𝔟 : Ideal (𝓞 K)), (b : K) = y) ↔
      ∃ y' ∈ (𝔞 : FractionalIdeal (𝓞 K)⁰ K), y = x₀ * y' := by
    intro y
    rw [← FractionalIdeal.mem_singleton_mul, ← hJx, hJ, FractionalIdeal.coe_mk0,
      FractionalIdeal.mem_coeIdeal]
  have hmem : ∀ z, z ∈ P.lattice ↔ ∃ m n : ℤ, σ x₀ * ω * (m * (τ : ℂ) + n) = z := by
    intro z
    rw [hP]
    constructor
    · rintro ⟨b, hb, rfl⟩
      obtain ⟨y', hy', hby⟩ := (hmemJ _).1 ⟨b, hb, rfl⟩
      obtain ⟨m, n, hmn⟩ := (hω (σ y')).1 ⟨y', hy', rfl⟩
      exact ⟨m, n, by rw [hby, map_mul, ← hmn]; ring⟩
    · rintro ⟨m, n, rfl⟩
      obtain ⟨y', hy', hy'eq⟩ := (hω (ω * (m * (τ : ℂ) + n))).2 ⟨m, n, rfl⟩
      obtain ⟨b, hb, hbeq⟩ := (hmemJ (x₀ * y')).2 ⟨y', hy', rfl⟩
      exact ⟨b, hb, by rw [hbeq, map_mul, hy'eq]; ring⟩
  refine ⟨σ x₀ * ω, ?_, hmem⟩
  intro ha
  obtain ⟨m, n, hmn⟩ := (hmem P.ω₁).1 P.ω₁_mem_lattice
  rw [ha, zero_mul] at hmn
  exact P.indep.ne_zero 0 (by simpa using hmn.symm)

theorem log_pi_sub_mean_log_latticeNormDisc :
    ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (σ₀ : K →+* ℂ), ¬ ComplexEmbedding.IsReal σ₀ → ∀ (𝔟 : ClassGroup (𝓞 K) → nonZeroDivisors (Ideal (𝓞 K))), ∀ (Lc : ClassGroup (𝓞 K) → PeriodPair), (∀ C, ClassGroup.mk0 (𝔟 C) = C) → (∀ C z, z ∈ (Lc C).lattice ↔ ∃ a ∈ (𝔟 C : Ideal (𝓞 K)), z = σ₀ (a : K)) → ∀ (σ : K →+* ℂ) (τ : ClassGroup (𝓞 K) → ℍ), (∀ C, IsIdealClassPoint σ C (τ C)) → Real.log Real.pi - (∑ C, Real.log (|((Lc C).ω₁ * starRingEnd ℂ (Lc C).ω₂).im| ^ 6 * ‖(Lc C).g₂ ^ 3 - 27 * (Lc C).g₃ ^ 2‖)) / (6 * Fintype.card (ClassGroup (𝓞 K))) = (∑ C, -Real.log (4 * Real.pi * (τ C).im * ‖ModularForm.eta (τ C)‖ ^ 4)) / classNumber K := by
  intro K _ _ hK σ₀ h₀ 𝔟 Lc h𝔟 hL σ τ hτ
  classical

  have key : ∀ C, Real.log Real.pi - Real.log (|((Lc C).ω₁ * starRingEnd ℂ (Lc C).ω₂).im| ^ 6 *
      ‖(Lc C).g₂ ^ 3 - 27 * (Lc C).g₃ ^ 2‖) / 6 =
      -Real.log (4 * Real.pi * (τ C).im * ‖ModularForm.eta (τ C)‖ ^ 4) := by
    intro C
    have hτC : IsIdealClassPoint σ (ClassGroup.mk0 (𝔟 C)) (τ C) := by
      rw [h𝔟 C]
      exact hτ C
    rcases embedding_eq_or_eq_conjugate hK h₀ σ with rfl | rfl
    · obtain ⟨a, ha, h⟩ := hτC.exists_lattice_eq (hL C)
      exact log_pi_sub_log_latticeNormDisc ha h
    · have hP : ∀ z, z ∈ (conjPeriods (Lc C)).lattice ↔
          ∃ a ∈ (𝔟 C : Ideal (𝓞 K)), z = ComplexEmbedding.conjugate σ₀ (a : K) := by
        intro z
        rw [mem_conjPeriods_lattice, hL]
        refine exists_congr fun a => and_congr_right fun _ => ?_
        rw [ComplexEmbedding.conjugate_coe_eq]
        constructor
        · intro h
          rw [← h, Complex.conj_conj]
        · intro h
          rw [h, Complex.conj_conj]
      obtain ⟨a, ha, h⟩ := hτC.exists_lattice_eq hP
      have e := log_pi_sub_log_latticeNormDisc ha h
      rw [← latticeNormDisc_eq, latticeNormDisc_conjPeriods, latticeNormDisc_eq] at e
      exact e
  have hh : (Fintype.card (ClassGroup (𝓞 K)) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  simp_rw [← key]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.sum_div]
  simp only [NumberField.classNumber]
  field_simp

end GlobalTheory
end

section

open NumberField ReciprocityTheory.GeometryOfNumbersTheory
open scoped ComplexOrder

namespace GlobalTheory.LamF

theorem hermFam_isometry_injective {K : Type*} [Field K] [NumberField K] {V V' : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']
    (h : HermFam K V) (h' : HermFam K V') (M : V →ₗ[K] V')
    (hM : ∀ s a b, h'.form s (M a) (M b) = h.form s a b) : Function.Injective M := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra h0
  obtain ⟨s⟩ : Nonempty (K →+* ℂ) := inferInstance
  have hli : LinearIndependent K ![x] := by
    rw [linearIndependent_unique_iff]; simpa using h0
  have h1 := (h.posDef s 1 ![x] hli).diag_pos (i := 0)
  have h2 : h'.form s (M x) (M x) = 0 := by
    have := h'.smul_right s 0 (M x) (M x)
    rw [zero_smul, map_zero, zero_mul] at this
    rw [← this, hx]
  rw [hM] at h2
  simp [h2] at h1

theorem deg_map_isometry : ∀ (K : Type) [Field K] [NumberField K] (V V' : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] (h : HermFam K V) (h' : HermFam K V') (M : V →ₗ[K] V') (Λ : Submodule (𝓞 K) V), Λ.FG → (∀ s a b, h'.form s (M a) (M b) = h.form s a b) → ReciprocityTheory.GeometryOfNumbersTheory.deg h' (Λ.map (M.restrictScalars (𝓞 K))) = ReciprocityTheory.GeometryOfNumbersTheory.deg h Λ := by
  intro K _ _ V V' _ _ _ _ _ _ _ _ h h' M E hE hM
  have hinj := hermFam_isometry_injective h h' M hM
  obtain ⟨v, hv⟩ := exists_isFrame E hE
  have hv' : IsFrame K (E.map (M.restrictScalars (𝓞 K))) (M ∘ v) := by
    refine ⟨fun i => ⟨v i, hv.1 i, rfl⟩, hv.2.1.map' M (LinearMap.ker_eq_bot.2 hinj), ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    rw [Set.range_comp, Submodule.span_image]
    exact ⟨x, hv.2.2 hx, rfl⟩
  rw [arakelovDegree_eq_degreeOfFamily h hE hv, arakelovDegree_eq_degreeOfFamily h' (hE.map _) hv']
  unfold degreeOfFamily
  have e1 : ∀ s, h'.gram s (M ∘ v) = h.gram s v := fun s => by
    ext i j; simp [HermFam.gram, hM]
  have e2 : Submodule.span (𝓞 K) (Set.range (M ∘ v)) =
      (Submodule.span (𝓞 K) (Set.range v)).map (M.restrictScalars (𝓞 K)) := by
    rw [Submodule.map_span, Set.range_comp]; rfl
  simp only [e1, e2, Submodule.map_toAddSubgroup]
  rw [AddSubgroup.relIndex_map_map_of_injective _ _ (by exact hinj)]

end GlobalTheory.LamF
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory

namespace PureType

section Grp

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {B G : Over S} {B' G' : Over S'}
  {β : B'.left ⟶ B.left} {π : G'.left ⟶ G.left}


set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj in
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {B G : Over S} {B' G' : Over S'}
  {β : B'.left ⟶ B.left} {π : G'.left ⟶ G.left} in
theorem _root_.GlobalTheory.PureType.exists_hom_over (hβ : β ≫ B.hom = B'.hom ≫ f)
    (hπ : IsPullback π G'.hom G.hom f) (φ : B ⟶ G) :
    ∃ φ' : B' ⟶ G', φ'.left ≫ π = β ≫ φ.left := by
  refine ⟨Over.homMk (hπ.lift (β ≫ φ.left) B'.hom ?_) (hπ.lift_snd _ _ _), ?_⟩
  · rw [Category.assoc, Over.w φ, hβ]
  · exact hπ.lift_fst _ _ _


set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj in
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {B G : Over S} {B' G' : Over S'}
  {β : B'.left ⟶ B.left} {π : G'.left ⟶ G.left} in
theorem _root_.GlobalTheory.PureType.eq_of_comp_eq (hπ : IsPullback π G'.hom G.hom f) {T : Over S'}
    {x y : T ⟶ G'} (h : x.left ≫ π = y.left ≫ π) : x = y :=
  Over.OverMorphism.ext (hπ.hom_ext h (by simp))

variable [GrpObj B] [GrpObj G] [GrpObj B'] [GrpObj G']


set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj in
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {B G : Over S} {B' G' : Over S'}
  {β : B'.left ⟶ B.left} {π : G'.left ⟶ G.left} in
variable [GrpObj B] [GrpObj G] [GrpObj B'] [GrpObj G'] in
theorem _root_.GlobalTheory.PureType.isMonHom_over (hβ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback B' B f β) (hπ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G f π) {φ : B ⟶ G}
    [IsMonHom φ] {φ' : B' ⟶ G'} (h : φ'.left ≫ π = β ≫ φ.left) : IsMonHom φ' := by
  have key : ∀ (T : Over S') (x y : T ⟶ B'), (x * y) ≫ φ' = (x ≫ φ') * (y ≫ φ') := by
    intro T x y
    have hw : ∀ z : T ⟶ B', (z.left ≫ β) ≫ B.hom = (Over.mk (T.hom ≫ f)).hom := by
      intro z
      rw [Category.assoc, hβ.1.w, ← Category.assoc, Over.w z]
      rfl
    let x₀ : Over.mk (T.hom ≫ f) ⟶ B := Over.homMk (x.left ≫ β) (hw x)
    let y₀ : Over.mk (T.hom ≫ f) ⟶ B := Over.homMk (y.left ≫ β) (hw y)
    have h₁ := hβ.2 T x y x₀ y₀ rfl rfl
    have h₂ := hπ.2 T (x ≫ φ') (y ≫ φ') (x₀ ≫ φ) (y₀ ≫ φ) (by simp [x₀, h]) (by simp [y₀, h])
    apply _root_.GlobalTheory.PureType.eq_of_comp_eq hπ.1
    rw [← h₂, ← MonObj.mul_comp]
    simp only [Over.comp_left, h₁, Category.assoc, h]
  have one : ∀ (T : Over S'), (1 : T ⟶ B') ≫ φ' = 1 := by
    intro T
    have := key T 1 1
    rw [_root_.mul_one] at this
    exact mul_left_cancel (a := (1 : T ⟶ B') ≫ φ') (by rw [_root_.mul_one]; exact this.symm)
  constructor
  · simpa [Hom.one_def] using one (𝟙_ _)
  · have := key (B' ⊗ B') (fst B' B') (snd B' B')
    simpa [Hom.mul_def] using this


end Grp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

end PureType

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.isoLineBundle_of_regularPullbacks_sameZeroScheme : ∀ (X Y : Scheme.{0}) (L : LB X) (θ : L.Sec) (φ ψ : Y ⟶ X), L.IsLB → (∀ (i : L.ι) (V : Y.Opens) (h : V ≤ φ ⁻¹ᵁ L.U i), (φ.appLE (L.U i) V h).hom (θ.f i) ∈ nonZeroDivisors Γ(Y, V)) → (∀ (i : L.ι) (V : Y.Opens) (h : V ≤ ψ ⁻¹ᵁ L.U i), (ψ.appLE (L.U i) V h).hom (θ.f i) ∈ nonZeroDivisors Γ(Y, V)) → (∀ (T : Scheme.{0}) (t : T ⟶ Y) (i j : L.ι) (h : ⊤ ≤ (t ≫ φ) ⁻¹ᵁ L.U i) (h' : ⊤ ≤ (t ≫ ψ) ⁻¹ᵁ L.U j), ((t ≫ φ).appLE (L.U i) ⊤ h).hom (θ.f i) = 0 ↔ ((t ≫ ψ).appLE (L.U j) ⊤ h').hom (θ.f j) = 0) → ∃ t : LB.Gen (LB.LinComb L (K := Fin 2) ![φ, ψ] ![1, -1]), t.IsGen := by
  first | exact @GlobalTheory.SameZeroScheme.exists_isGen_linComb | exact GlobalTheory.SameZeroScheme.exists_isGen_linComb | (intros; apply GlobalTheory.SameZeroScheme.exists_isGen_linComb <;> assumption)
end
