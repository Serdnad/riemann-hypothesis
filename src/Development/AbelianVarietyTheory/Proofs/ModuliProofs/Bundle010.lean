module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.Algebra.MvPolynomial.Cardinal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Complex.Cardinality
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

noncomputable def complexExtend {O M : Type} [CommRing O] [Ring M] [Algebra ℂ M]
    (f : O →+* M) : ℂ ⊗[ℤ] O →ₐ[ℂ] M :=
  Algebra.TensorProduct.lift (Algebra.ofId ℂ M) f.toIntAlgHom
    (fun x y => Algebra.commute_algebraMap_left x (f y))

theorem complexExtend_tmul {O M : Type} [CommRing O] [Ring M] [Algebra ℂ M]
    (f : O →+* M) (c : ℂ) (a : O) : complexExtend f (c ⊗ₜ a) = c • f a := by
  rw [Algebra.smul_def]
  exact Algebra.TensorProduct.lift_tmul _ _ _ c a

theorem exists_eigen_element (O : Type) [CommRing O] [Module.Finite ℤ O]
    [IsReduced (ℂ ⊗[ℤ] O)] (τ : O →+* ℂ) :
    ∃ e : ℂ ⊗[ℤ] O, complexExtend τ e = 1 ∧ ∀ a : O, ((1 : ℂ) ⊗ₜ[ℤ] a) * e = τ a • e := by
  haveI : IsArtinianRing (ℂ ⊗[ℤ] O) := IsArtinianRing.of_finite ℂ _
  haveI : IsSemisimpleRing (ℂ ⊗[ℤ] O) := IsArtinianRing.isSemisimpleRing_of_isReduced _
  obtain ⟨f, hf, hI⟩ := IsSemisimpleRing.ideal_eq_span_idempotent
    (RingHom.ker (complexExtend τ))
  have hf0 : complexExtend τ f = 0 := by
    have : f ∈ RingHom.ker (complexExtend τ) := hI ▸ Ideal.mem_span_singleton_self f
    exact this
  refine ⟨1 - f, by simp [hf0], fun a => ?_⟩
  have hk : ((1 : ℂ) ⊗ₜ[ℤ] a) - algebraMap ℂ (ℂ ⊗[ℤ] O) (τ a) ∈
      RingHom.ker (complexExtend τ) := by
    rw [RingHom.mem_ker, map_sub, complexExtend_tmul, AlgHom.commutes]
    simp
  rw [hI, Ideal.mem_span_singleton'] at hk
  obtain ⟨y, hy⟩ := hk
  rw [Algebra.smul_def, ← sub_eq_zero, ← sub_mul, ← hy, _root_.mul_assoc, mul_sub, _root_.mul_one, hf.eq,
    sub_self, mul_zero]

theorem complexExtend_diagonal {O : Type} [CommRing O] {g : ℕ}
    (f : O →+* Matrix (Fin g) (Fin g) ℂ) (ty : Fin g → (O →+* ℂ))
    (hf : ∀ a, f a = Matrix.diagonal (fun i => ty i a)) (x : ℂ ⊗[ℤ] O) :
    complexExtend f x = Matrix.diagonal (fun i => complexExtend (ty i) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c a =>
    simp only [complexExtend_tmul, hf]
    ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  | add x y hx hy => simp only [map_add (f := _), hx, hy, Matrix.diagonal_add]

theorem differentiableOn_complexExtend {O : Type} [CommRing O] {g m : ℕ}
    {B : Set (Fin m → ℂ)} (F : (Fin m → ℂ) → (O →+* Matrix (Fin g) (Fin g) ℂ))
    (hF : ∀ a i j, DifferentiableOn ℂ (fun b => F b a i j) B) (x : ℂ ⊗[ℤ] O) (i j : Fin g) :
    DifferentiableOn ℂ (fun b => complexExtend (F b) x i j) B := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c a =>
    simp only [complexExtend_tmul, Matrix.smul_apply, smul_eq_mul]
    exact (hF a i j).const_mul c
  | add x y hx hy =>
    simp only [map_add (f := _), Matrix.add_apply]
    exact hx.add hy

theorem holomorphic_diagonalisation :
    ∀ (O : Type) [CommRing O] (g m : ℕ) (B : Set (Fin m → ℂ)) (b₀ : Fin m → ℂ) (F : (Fin m → ℂ) → (O →+* Matrix (Fin g) (Fin g) ℂ)) (ty : Fin g → (O →+* ℂ)), Module.Finite ℤ O → IsReduced (ℂ ⊗[ℤ] O) → IsOpen B → b₀ ∈ B → (∀ a i j, DifferentiableOn ℂ (fun b => F b a i j) B) → (∀ a, F b₀ a = Matrix.diagonal (fun i => ty i a)) → ∃ (B' : Set (Fin m → ℂ)) (h : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ h b₀ = 1 ∧ (∀ i j, DifferentiableOn ℂ (fun b => h b i j) B') ∧ ∀ b ∈ B', IsUnit (h b) ∧ ∀ a, F b a * h b = h b * Matrix.diagonal (fun i => ty i a) := by
  intro O _ g m B b₀ F ty hfin hred hB hb₀ hF hF₀
  choose e he1 he using fun τ => exists_eigen_element O τ
  let h : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ :=
    fun b => Matrix.of fun i j => complexExtend (F b) (e (ty j)) i j
  have hd : ∀ i j, DifferentiableOn ℂ (fun b => h b i j) B := fun i j =>
    differentiableOn_complexExtend F hF _ i j
  have h0 : h b₀ = 1 := by
    ext i j
    simp only [h, Matrix.of_apply, complexExtend_diagonal _ ty hF₀]
    by_cases hij : i = j
    · subst hij; simp [he1]
    · simp [hij]
  have hc : ContinuousOn h B :=
    continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => (hd i j).continuousOn
  have hdet : ContinuousOn (fun b => (h b).det) B :=
    (Continuous.matrix_det continuous_id).comp_continuousOn hc
  refine ⟨B ∩ (fun b => (h b).det) ⁻¹' {0}ᶜ, h,
    hdet.isOpen_inter_preimage hB isOpen_compl_singleton, ⟨hb₀, by simp [h0]⟩,
    Set.inter_subset_left, h0, fun i j => (hd i j).mono Set.inter_subset_left, ?_⟩
  rintro b ⟨-, hb⟩
  refine ⟨(Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hb), fun a => ?_⟩
  ext i j
  have key := congrArg (fun x => complexExtend (F b) x i j) (he (ty j) a)
  simp only [map_mul, map_smul, complexExtend_tmul, one_smul, Matrix.smul_apply,
    smul_eq_mul] at key
  rw [Matrix.mul_diagonal, mul_comm]
  exact key

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem latCont_discrete {E : Type} [NormedAddCommGroup E] (H : AddSubgroup E) (r : ℝ) (hr : 0 < r)
    (h : ∀ z ∈ H, ‖z‖ < r → z = 0) : DiscreteTopology H := by
  apply discreteTopology_of_isOpen_singleton_zero
  have e : ({0} : Set H) = Subtype.val ⁻¹' Metric.ball (0 : E) r := by
    ext z
    simp only [Set.mem_singleton_iff, Set.mem_preimage, Metric.mem_ball, dist_zero_right]
    constructor
    · rintro rfl
      simpa using hr
    · intro hz
      have := h z z.2 hz
      simpa using this
  rw [e]
  exact Metric.isOpen_ball.preimage continuous_subtype_val

noncomputable def latContMap {E J : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype J]
    (v : J → E) : (J → ℝ) →L[ℝ] E :=
  ∑ i, (ContinuousLinearMap.proj i : (J → ℝ) →L[ℝ] ℝ).smulRight (v i)

theorem latContMap_apply {E J : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype J]
    (v : J → E) (c : J → ℝ) : latContMap v c = ∑ i, c i • v i := by
  simp [latContMap]

theorem latContMap_repr {La E J : Type} [AddCommGroup La] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype J] (e : Module.Basis J ℤ La) (p : La →+ E) (n : J → ℤ) :
    latContMap (fun i => p (e i)) (fun i => (n i : ℝ)) = p (e.equivFun.symm n) := by

  rw [latContMap_apply, Module.Basis.equivFun_symm_apply, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_zsmul, Int.cast_smul_eq_zsmul]

theorem latCont_card {La E J : Type} [AddCommGroup La] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Fintype J] (e : Module.Basis J ℤ La) (p : La →+ E)
    (hd : DiscreteTopology p.range) (hi : Function.Injective p)
    (hs : Submodule.span ℝ (Set.range p) = ⊤) :
    Module.finrank ℝ (J → ℝ) = Module.finrank ℝ E := by
  let L : Submodule ℤ E := AddSubgroup.toIntSubmodule p.range
  have : DiscreteTopology L := hd
  have : IsZLattice ℝ L := ⟨by simpa [L] using hs⟩
  have h1 : Module.finrank ℤ L = Module.finrank ℝ E := ZLattice.rank (K := ℝ) (L := L)
  have hL : LinearMap.range p.toIntLinearMap = L := by
    ext x
    simp [L]
  have h2 : Module.finrank ℤ La = Module.finrank ℤ L := by
    rw [← hL]
    exact (LinearEquiv.ofInjective p.toIntLinearMap hi).finrank_eq
  rw [Module.finrank_fintype_fun_eq_card, ← Module.finrank_eq_card_basis e, h2, h1]

theorem latContinuation : ∀ (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (g m : ℕ) (B : Set (Fin m → ℂ)) (b₀ : Fin m → ℂ) (K : (Fin m → ℂ) → AddSubgroup (Fin g → ℂ)) (P : (Fin m → ℂ) → (La →+ (Fin g → ℂ))) (r : ℝ), IsOpen B → b₀ ∈ B → 0 < r → (∀ b ∈ B, ∀ z ∈ K b, ‖z‖ < r → z = 0) → (∀ (b : ℕ → (Fin m → ℂ)) (z : ℕ → (Fin g → ℂ)) (z₀ : Fin g → ℂ), Filter.Tendsto b Filter.atTop (nhds b₀) → Filter.Tendsto z Filter.atTop (nhds z₀) → (∀ i, z i ∈ K (b i)) → z₀ ∈ K b₀) → (∀ x, ContinuousAt (fun b => P b x) b₀) → (∀ b ∈ B, (P b).range ≤ K b) → (P b₀).range = K b₀ → Function.Injective (P b₀) → Submodule.span ℝ (Set.range (P b₀)) = ⊤ → ∀ᶠ b in nhds b₀, (P b).range = K b ∧ Function.Injective (P b) ∧ Submodule.span ℝ (Set.range (P b)) = ⊤ ∧ DiscreteTopology (P b).range := by
  intro La _ _ _ g m B b₀ K P r hB hb₀ hr hdisc hclosed hcont hle heq hinj hspan
  obtain ⟨J, _, ⟨e⟩⟩ : ∃ (J : Type) (_ : Fintype J), Nonempty (Module.Basis J ℤ La) :=
    ⟨_, inferInstance, ⟨Module.Free.chooseBasis ℤ La⟩⟩
  have hrepr : ∀ b (k : J → ℤ), P b (e.equivFun.symm k) = ∑ j, ((k j : ℤ) : ℝ) • P b (e j) := by
    intro b k
    rw [← latContMap_repr e (P b) k, latContMap_apply]
  have hcoord : ∀ b x, P b x = ∑ j, ((e.equivFun x j : ℤ) : ℝ) • P b (e j) := by
    intro b x
    rw [← hrepr]
    simp
  have hdiscR : ∀ b ∈ B, DiscreteTopology (P b).range := fun b hb =>
    latCont_discrete _ r hr (fun z hz hzr => hdisc b hb z (hle b hb hz) hzr)
  have hcard : Fintype.card J = Module.finrank ℝ (Fin g → ℂ) := by
    rw [← Module.finrank_fintype_fun_eq_card ℝ]
    exact latCont_card e (P b₀) (hdiscR b₀ hb₀) hinj hspan
  have hspan0 : ⊤ ≤ Submodule.span ℝ (Set.range (fun j => P b₀ (e j))) := by
    rw [← hspan]
    apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    rw [hcoord]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
  have hli0 : LinearIndependent ℝ (fun j => P b₀ (e j)) :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspan0 hcard
  have hvc : ContinuousAt (fun b => fun j => P b (e j)) b₀ :=
    continuousAt_pi.mpr (fun j => hcont (e j))
  have hev_li : ∀ᶠ b in nhds b₀, LinearIndependent ℝ (fun j => P b (e j)) :=
    hvc.tendsto.eventually hli0.eventually
  have hev_B : ∀ᶠ b in nhds b₀, b ∈ B := hB.mem_nhds hb₀
  have hspanv : ∀ b, LinearIndependent ℝ (fun j => P b (e j)) →
      Submodule.span ℝ (Set.range (fun j => P b (e j))) = ⊤ :=
    fun b hb => hb.span_eq_top_of_card_eq_finrank' hcard
  have hsurj : ∀ b, LinearIndependent ℝ (fun j => P b (e j)) →
      ∀ z, ∃ c : J → ℝ, ∑ j, c j • P b (e j) = z := by
    intro b hb z
    have hz : z ∈ Submodule.span ℝ (Set.range (fun j => P b (e j))) := by
      rw [hspanv b hb]
      trivial
    exact (Submodule.mem_span_range_iff_exists_fun ℝ).mp hz
  have hev_eq : ∀ᶠ b in nhds b₀, ∀ z ∈ K b, z ∈ (P b).range := by
    by_contra hne
    rw [Filter.not_eventually] at hne
    have hfr : ∃ᶠ b in nhds b₀, b ∈ B ∧ LinearIndependent ℝ (fun j => P b (e j)) ∧
        ∃ z ∈ K b, z ∉ (P b).range := by
      refine (hne.and_eventually (hev_B.and hev_li)).mono ?_
      rintro b ⟨h1, h2, h3⟩
      push Not at h1
      exact ⟨h2, h3, h1⟩
    obtain ⟨bs, hbs, hprop⟩ := Filter.exists_seq_forall_of_frequently hfr
    choose hbsB hbsli z hzK hzR using hprop
    choose c hc using fun i => hsurj (bs i) (hbsli i) (z i)
    have hshift : ∀ i (k : J → ℤ),
        (∑ j, (Int.fract (c i j) - (k j : ℝ)) • P (bs i) (e j)) ∈ K (bs i) ∧
        (∑ j, (Int.fract (c i j) - (k j : ℝ)) • P (bs i) (e j)) ∉ (P (bs i)).range := by
      intro i k
      have e1 : ∑ j, (Int.fract (c i j) - (k j : ℝ)) • P (bs i) (e j)
          = z i - P (bs i) (e.equivFun.symm (fun j => ⌊c i j⌋ + k j)) := by
        rw [hrepr, ← hc i, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [← sub_smul]
        congr 1
        push_cast
        rw [← Int.self_sub_floor]
        ring
      rw [e1]
      have hmem : P (bs i) (e.equivFun.symm (fun j => ⌊c i j⌋ + k j)) ∈ (P (bs i)).range :=
        ⟨_, rfl⟩
      refine ⟨sub_mem (hzK i) (hle _ (hbsB i) hmem), fun h => hzR i ?_⟩
      have := add_mem h hmem
      rwa [sub_add_cancel] at this
    have hIcc : ∀ i, (fun j => Int.fract (c i j)) ∈ Set.Icc (0 : J → ℝ) 1 := fun i =>
      ⟨fun j => Int.fract_nonneg _, fun j => (Int.fract_lt_one _).le⟩
    obtain ⟨a, -, φ, hφ, ha⟩ := (isCompact_Icc (a := (0 : J → ℝ)) (b := 1)).tendsto_subseq hIcc
    have hbφ : Filter.Tendsto (bs ∘ φ) Filter.atTop (nhds b₀) := hbs.comp hφ.tendsto_atTop
    have hvφ : ∀ j, Filter.Tendsto (fun i => P (bs (φ i)) (e j)) Filter.atTop
        (nhds (P b₀ (e j))) := fun j => (hcont (e j)).tendsto.comp hbφ
    have haj : ∀ j, Filter.Tendsto (fun i => Int.fract (c (φ i) j)) Filter.atTop (nhds (a j)) :=
      fun j => ((continuous_apply j).tendsto a).comp ha
    have hlim : ∀ k : J → ℤ, Filter.Tendsto
        (fun i => ∑ j, (Int.fract (c (φ i) j) - (k j : ℝ)) • P (bs (φ i)) (e j)) Filter.atTop
        (nhds (∑ j, (a j - (k j : ℝ)) • P b₀ (e j))) := fun k =>
      tendsto_finsetSum _ (fun j _ => ((haj j).sub_const _).smul (hvφ j))
    have hz0 : (∑ j, (a j - ((0 : J → ℤ) j : ℝ)) • P b₀ (e j)) ∈ K b₀ :=
      hclosed (bs ∘ φ) _ _ hbφ (hlim 0) (fun i => (hshift (φ i) 0).1)
    simp only [Pi.zero_apply, Int.cast_zero, sub_zero] at hz0
    rw [← heq] at hz0
    obtain ⟨x, hx⟩ := AddMonoidHom.mem_range.mp hz0
    have hzero : ∑ j, (a j - ((e.equivFun x j : ℤ) : ℝ)) • P b₀ (e j) = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [← hcoord b₀ x, ← hx, sub_self]
    have hlim0 := hlim (e.equivFun x)
    rw [hzero] at hlim0
    obtain ⟨i, hi⟩ := (hlim0.eventually (Metric.ball_mem_nhds (0 : Fin g → ℂ) hr)).exists
    rw [dist_zero_right] at hi
    obtain ⟨hK', hR'⟩ := hshift (φ i) (e.equivFun x)
    exact hR' (by rw [hdisc _ (hbsB (φ i)) _ hK' hi]; exact zero_mem _)
  filter_upwards [hev_B, hev_li, hev_eq] with b hb hli hrange
  refine ⟨le_antisymm (hle b hb) (fun z hz => hrange z hz), ?_, ?_, hdiscR b hb⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    rw [hcoord] at hx
    have h0 := (Fintype.linearIndependent_iff.mp hli) _ hx
    have h1 : e.equivFun x = 0 := funext fun j => by simpa using h0 j
    simpa using congrArg e.equivFun.symm h1
  · rw [eq_top_iff, ← hspanv b hli]
    apply Submodule.span_mono
    rintro _ ⟨j, rfl⟩
    exact ⟨e j, rfl⟩

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem nonempty_algHom_complex_of_countable (R K : Type) [CommRing R] [IsDomain R] [Countable R]
    [Field K] [Countable K] [Algebra R K] [Algebra R ℂ] [FaithfulSMul R K] [FaithfulSMul R ℂ] :
    Nonempty (K →ₐ[R] ℂ) := by
  obtain ⟨J, v, hv⟩ := exists_isTranscendenceBasis' R K
  obtain ⟨Jc, w, hw⟩ := exists_isTranscendenceBasis' R ℂ
  haveI : Countable J := hv.1.injective.countable
  have hκ : Cardinal.aleph0 < Cardinal.mk Jc := by
    by_contra hlt
    have hle := not_lt.1 hlt
    have h1 := IsAlgClosed.cardinal_le_max_transcendence_basis' w hw
    rw [Cardinal.mk_complex] at h1
    exact absurd (h1.trans (max_le (max_le Cardinal.mk_le_aleph0 hle) le_rfl))
      (not_le.2 Cardinal.aleph0_lt_continuum)
  obtain ⟨e⟩ : Nonempty (J ↪ Jc) :=
    (Cardinal.le_def J Jc).1 (Cardinal.mk_le_aleph0.trans hκ.le)
  let S := Algebra.adjoin R (Set.range v)
  let φ : S →ₐ[R] ℂ := (MvPolynomial.aeval (w ∘ e)).comp hv.1.aevalEquiv.symm.toAlgHom
  have hind : AlgebraicIndependent R (w ∘ e) := hw.1.comp e e.injective
  have hφ : Function.Injective φ := by
    have hind' : Function.Injective (MvPolynomial.aeval (R := R) (w ∘ e)) := hind
    simp only [φ, AlgHom.coe_comp]
    exact hind'.comp hv.1.aevalEquiv.symm.injective
  letI : Algebra S ℂ := φ.toRingHom.toAlgebra
  haveI : Module.IsTorsionFree S ℂ := Module.isTorsionFree_iff_algebraMap_injective.2 hφ
  haveI : Module.IsTorsionFree S K :=
    Module.isTorsionFree_iff_algebraMap_injective.2 Subtype.val_injective
  haveI : Algebra.IsAlgebraic S K := hv.isAlgebraic
  let g : K →ₐ[S] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨{ g.toRingHom with commutes' := fun r => ?_ }⟩
  show g (algebraMap R K r) = algebraMap R ℂ r
  rw [IsScalarTower.algebraMap_apply R S K r, g.commutes]
  exact φ.commutes r

private theorem isJacobsonRing_int' : IsJacobsonRing ℤ := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  by_cases hbot : P = ⊥
  · subst hbot
    refine le_antisymm (fun x hx => ?_) Ideal.le_jacobson
    obtain ⟨z, hz⟩ := (Ideal.mem_jacobson_iff.1 hx) x
    rw [Ideal.mem_bot] at hz ⊢
    have hu : IsUnit (x * x + 1) := IsUnit.of_mul_eq_one z (by linear_combination hz)
    rcases Int.isUnit_iff.1 hu with h | h
    · exact mul_self_eq_zero.1 (by linarith)
    · nlinarith [mul_self_nonneg x]
  · haveI := hP.isMaximal hbot
    exact Ideal.jacobson_eq_self_of_isMaximal

theorem injective_of_finiteType_int_of_charZero {o K : Type} [CommRing o] [IsDomain o]
    [Ring.DimensionLEOne o] [Algebra.FiniteType ℤ o] [Field K] [CharZero K] (β : o →+* K) :
    Function.Injective β := by
  haveI := isJacobsonRing_int'
  by_contra hβ
  have hker : RingHom.ker β ≠ ⊥ := fun h => hβ ((RingHom.injective_iff_ker_eq_bot β).2 h)
  haveI : (RingHom.ker β).IsMaximal := (RingHom.ker_isPrime β).isMaximal hker
  letI : Field (o ⧸ RingHom.ker β) := Ideal.Quotient.field _
  haveI : Algebra.FiniteType ℤ (o ⧸ RingHom.ker β) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℤ _)
      (Ideal.Quotient.mkₐ_surjective ℤ _)
  haveI : Module.Finite ℤ (o ⧸ RingHom.ker β) := finite_of_finite_type_of_isJacobsonRing ℤ _
  haveI : Algebra.IsIntegral ℤ (o ⧸ RingHom.ker β) := Algebra.IsIntegral.of_finite ℤ _
  have hinj : Function.Injective (algebraMap ℤ (o ⧸ RingHom.ker β)) := by
    intro a b hab
    have hk := congrArg (RingHom.kerLift β) hab
    simp only [eq_intCast, map_intCast] at hk
    exact Int.cast_injective hk
  exact Int.not_isField (isField_of_isIntegral_of_isField hinj (Field.toIsField _))

theorem exists_ringHom_complex_comp_eq_of_countable :
    ∀ (o : Type) [CommRing o] (em : o →+* ℂ) (K₀ : Type) [Field K₀] [CharZero K₀] [Countable K₀] (β : o →+* K₀), IsDedekindDomain o → Algebra.FiniteType ℤ o → Function.Injective em → Countable o ∧ ∃ j : K₀ →+* ℂ, j.comp β = em := by
  intro o _ em K₀ _ _ _ β hD hF hem
  haveI := hD
  haveI := hF
  have hβ : Function.Injective β := injective_of_finiteType_int_of_charZero β
  have hcount : Countable o := by
    obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 hF
    have hc : Countable (MvPolynomial (Fin n) ℤ) := by
      rw [← Cardinal.mk_le_aleph0_iff]
      exact MvPolynomial.cardinalMk_le_max.trans
        (max_le (max_le Cardinal.mk_le_aleph0 Cardinal.mk_le_aleph0) le_rfl)
    exact hf.countable
  refine ⟨hcount, ?_⟩
  haveI := hcount
  letI : Algebra o K₀ := β.toAlgebra
  letI : Algebra o ℂ := em.toAlgebra
  haveI : FaithfulSMul o K₀ := (faithfulSMul_iff_algebraMap_injective o K₀).2 hβ
  haveI : FaithfulSMul o ℂ := (faithfulSMul_iff_algebraMap_injective o ℂ).2 hem
  obtain ⟨g⟩ := nonempty_algHom_complex_of_countable o K₀
  exact ⟨g.toRingHom, RingHom.ext fun x => g.commutes x⟩

end GlobalTheory
end
