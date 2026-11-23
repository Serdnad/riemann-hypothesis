module

public import Mathlib.Algebra.Module.Pi
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.LocallyConstant.Basic
public import GroundTheory.AutomorphicForms.LocallyProfinite
public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Analysis.CStarAlgebra.ContinuousMap
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsCharNeOne
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
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.Sheaves.Init
import GroundTheory.GlobalFields.HerbrandQuotients.RationalForm
import GroundTheory.GlobalFields.SemilocalAlgebras.Bundle001
public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances

@[expose] public section

section

noncomputable section

namespace GroundTheory.Automorphic

open Set Filter Topology
open scoped Pointwise

section Space

variable (X : Type*) [TopologicalSpace X] (R E : Type*) [Semiring R] [AddCommMonoid E]
  [Module R E]

def locallyConstantCompactSupport : Submodule R (X → E) where
  carrier := {f | IsLocallyConstant f ∧ HasCompactSupport f}
  add_mem' {f g} hf hg := ⟨hf.1.comp₂ hg.1 (· + ·), hf.2.add hg.2⟩
  zero_mem' := ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩
  smul_mem' c f hf := ⟨hf.1.comp (c • ·), hf.2.mono fun x hx => by
    by_contra h
    exact hx (by simp [Function.notMem_support.1 h])⟩

variable {X R E}

theorem mem_locallyConstantCompactSupport {f : X → E} :
    f ∈ locallyConstantCompactSupport X R E ↔ IsLocallyConstant f ∧ HasCompactSupport f :=
  Iff.rfl

theorem indicator_mem_locallyConstantCompactSupport [T2Space X] {U : Set X} (hc : IsCompact U)
    (ho : IsOpen U) (e : E) :
    U.indicator (fun _ => e) ∈ locallyConstantCompactSupport X R E := by
  refine ⟨?_, HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩
  exact (LocallyConstant.indicator (LocallyConstant.const X e) ⟨hc.isClosed, ho⟩).isLocallyConstant

theorem range_finite_of_mem_locallyConstantCompactSupport {f : X → E}
    (hf : f ∈ locallyConstantCompactSupport X R E) : (range f).Finite := by
  have : CompactSpace (tsupport f) := isCompact_iff_compactSpace.1 hf.2
  have h1 : (range fun x : tsupport f => f x).Finite :=
    (hf.1.comp_continuous continuous_subtype_val).range_finite
  refine (h1.insert 0).subset ?_
  rintro _ ⟨x, rfl⟩
  by_cases hx : x ∈ tsupport f
  · exact mem_insert_of_mem _ ⟨⟨x, hx⟩, rfl⟩
  · rw [image_eq_zero_of_notMem_tsupport hx]
    exact mem_insert _ _

theorem isCompact_isOpen_fiber {f : X → E} (hf : f ∈ locallyConstantCompactSupport X R E)
    {v : E} (hv : v ≠ 0) : IsCompact {x | f x = v} ∧ IsOpen {x | f x = v} := by
  refine ⟨hf.2.of_isClosed_subset (hf.1.isClosed_fiber v) fun x hx => ?_, hf.1.isOpen_fiber v⟩
  refine subset_tsupport f ?_
  have hx : f x = v := hx
  simp [Function.mem_support, hx, hv]

end Space

section Group

variable {G : Type*} [Group G] {E : Type*}

theorem mk_eq_iff_mem_out_smul (K : Subgroup G) (x : G ⧸ K) (y : G) :
    (y : G ⧸ K) = x ↔ y ∈ x.out • (K : Set G) := by
  conv_lhs => rw [← QuotientGroup.out_eq' x]
  rw [eq_comm, QuotientGroup.eq, mem_leftCoset_iff, SetLike.mem_coe]

theorem apply_eq_of_mem_smul {K : Subgroup G} {f : G → E}
    (hK : ∀ g, ∀ k ∈ K, f (g * k) = f g) {g y : G} (hy : y ∈ g • (K : Set G)) : f y = f g := by
  obtain ⟨k, hk, rfl⟩ := Set.mem_smul_set.1 hy
  exact hK g k hk

variable [TopologicalSpace G] [IsTopologicalGroup G] {R : Type*} [Semiring R] [AddCommMonoid E]
  [Module R E]

theorem mem_locallyConstantCompactSupport_of_forall_mul_right (K : OpenSubgroup G)
    {f : G → E} (hf : HasCompactSupport f) (hK : ∀ g, ∀ k ∈ K, f (g * k) = f g) :
    f ∈ locallyConstantCompactSupport G R E := by
  refine ⟨(IsLocallyConstant.iff_exists_open f).2 fun g => ?_, hf⟩
  refine ⟨g • (K : Set G), K.isOpen.smul g, ?_, fun y hy => apply_eq_of_mem_smul hK hy⟩
  exact Set.mem_smul_set.2 ⟨1, K.one_mem, mul_one g⟩

theorem finite_image_mk_tsupport (K : OpenSubgroup G) {f : G → E} (hf : HasCompactSupport f) :
    (QuotientGroup.mk '' tsupport f : Set (G ⧸ (K : Subgroup G))).Finite :=
  (hf.image QuotientGroup.continuous_mk).finite_of_discrete

theorem eq_sum_indicator_coset (K : OpenSubgroup G) {f : G → E} (hf : HasCompactSupport f)
    (hK : ∀ g, ∀ k ∈ K, f (g * k) = f g) :
    f = ∑ x ∈ (finite_image_mk_tsupport K hf).toFinset,
      (x.out • (K : Set G)).indicator (fun _ => f x.out) := by
  classical
  funext y
  rw [Finset.sum_apply]
  by_cases hy : (y : G ⧸ (K : Subgroup G)) ∈ (finite_image_mk_tsupport K hf).toFinset
  · rw [Finset.sum_eq_single (y : G ⧸ (K : Subgroup G))]
    · have hmem : y ∈ (y : G ⧸ (K : Subgroup G)).out • (K : Set G) :=
        (mk_eq_iff_mem_out_smul (K : Subgroup G) _ y).1 rfl
      rw [Set.indicator_of_mem hmem]
      exact apply_eq_of_mem_smul hK hmem
    · intro b _ hb
      exact Set.indicator_of_notMem
        (fun h => hb ((mk_eq_iff_mem_out_smul (K : Subgroup G) b y).2 h).symm) _
    · intro h
      exact absurd hy h
  · rw [Finset.sum_eq_zero]
    · by_contra h
      exact hy ((Set.Finite.mem_toFinset _).2 ⟨y, subset_tsupport f h, rfl⟩)
    · intro b hb
      refine Set.indicator_of_notMem (fun h => hy ?_) _
      rwa [(mk_eq_iff_mem_out_smul (K : Subgroup G) b y).2 h]

variable [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

theorem exists_forall_mul_right {f : G → E} (hf : f ∈ locallyConstantCompactSupport G R E) :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ ∀ g, ∀ k ∈ K, f (g * k) = f g := by
  let W : Set (G × G) := {p | f (p.1 * p.2) = f p.1}
  have hW : IsOpen W := by
    have hF : IsLocallyConstant fun p : G × G => (f (p.1 * p.2), f p.1) :=
      (hf.1.comp_continuous continuous_mul).prodMk (hf.1.comp_continuous continuous_fst)
    exact hF {q | q.1 = q.2}
  have hsub : tsupport f ×ˢ ({1} : Set G) ⊆ W := by
    rintro ⟨g, k⟩ ⟨-, hk⟩
    simp only [mem_singleton_iff] at hk
    simp [W, hk]
  obtain ⟨u, v, -, hv, hSu, h1v, huv⟩ := generalized_tube_lemma hf.2 isCompact_singleton hW hsub
  obtain ⟨K, hKc, hKv⟩ := exists_openSubgroup_isCompact_subset (hv.mem_nhds (h1v rfl))
  have key : ∀ s ∈ tsupport f, ∀ k ∈ K, f (s * k) = f s := fun s hs k hk =>
    huv (show (s, k) ∈ u ×ˢ v from ⟨hSu hs, hKv hk⟩)
  refine ⟨K, hKc, fun g k hk => ?_⟩
  by_cases hg : g ∈ tsupport f
  · exact key g hg k hk
  · rw [image_eq_zero_of_notMem_tsupport hg]
    by_contra h
    have := key (g * k) (subset_tsupport f h) k⁻¹ (inv_mem hk)
    rw [mul_inv_cancel_right, image_eq_zero_of_notMem_tsupport hg] at this
    exact h this.symm

theorem exists_forall_mul_left {f : G → E} (hf : f ∈ locallyConstantCompactSupport G R E) :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ ∀ k ∈ K, ∀ g, f (k * g) = f g := by
  have hf' : (fun g => f g⁻¹) ∈ locallyConstantCompactSupport G R E :=
    ⟨hf.1.comp_continuous continuous_inv, hf.2.comp_homeomorph (Homeomorph.inv G)⟩
  obtain ⟨K, hKc, hK⟩ := exists_forall_mul_right hf'
  refine ⟨K, hKc, fun k hk g => ?_⟩
  have := hK g⁻¹ k⁻¹ (inv_mem hk)
  simpa [mul_inv_rev] using this

theorem exists_forall_mul_left_mul_right {f : G → E}
    (hf : f ∈ locallyConstantCompactSupport G R E) :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧
      ∀ k ∈ K, ∀ g, ∀ k' ∈ K, f (k * g * k') = f g := by
  obtain ⟨K₁, h₁, hK₁⟩ := exists_forall_mul_right hf
  obtain ⟨K₂, -, hK₂⟩ := exists_forall_mul_left hf
  refine ⟨K₁ ⊓ K₂, isCompact_inf_left h₁, fun k hk g k' hk' => ?_⟩
  rw [mul_assoc, hK₂ k (OpenSubgroup.mem_inf.1 hk).2, hK₁ g k' (OpenSubgroup.mem_inf.1 hk').1]

end Group

end GroundTheory.Automorphic
end
end

section

namespace GroundTheory.Automorphic

open Module TensorProduct

section QuadAlg

variable {R : Type*} [CommRing R]

end QuadAlg

section BaseChange

variable {L : Type*} [Field L] (d : L) (R : Type*) [CommRing R] [Algebra L R]

theorem algebraMap_quadraticAlgebra_apply (x : L) :
    algebraMap L (QuadraticAlgebra R (algebraMap L R d) 0) x = ⟨algebraMap L R x, 0⟩ := rfl

omit [Algebra L R] in
theorem quadraticAlgebra_re_one (a : R) : (1 : QuadraticAlgebra R a 0).re = 1 := rfl

omit [Algebra L R] in
theorem quadraticAlgebra_im_one (a : R) : (1 : QuadraticAlgebra R a 0).im = 0 := rfl

def omegaRoot : {u : QuadraticAlgebra R (algebraMap L R d) 0 //
    u * u = d • 1 + (0 : L) • u} :=
  ⟨QuadraticAlgebra.omega, by
    rw [QuadraticAlgebra.omega_mul_omega_eq_mk]
    ext <;> simp [Algebra.smul_def, algebraMap_quadraticAlgebra_apply]⟩

noncomputable def quadMap : QuadraticAlgebra L d 0 →ₐ[L] QuadraticAlgebra R (algebraMap L R d) 0 :=
  QuadraticAlgebra.lift (omegaRoot d R)

theorem quadMap_apply (z : QuadraticAlgebra L d 0) :
    quadMap d R z = ⟨algebraMap L R z.re, algebraMap L R z.im⟩ := by
  simp only [quadMap, QuadraticAlgebra.lift_apply_apply, omegaRoot]
  ext <;> simp [Algebra.smul_def, algebraMap_quadraticAlgebra_apply]

noncomputable def quadTensorHom :
    R ⊗[L] QuadraticAlgebra L d 0 →ₐ[R] QuadraticAlgebra R (algebraMap L R d) 0 :=
  Algebra.TensorProduct.lift (Algebra.ofId R _) (quadMap d R) (fun _ _ => Commute.all _ _)

theorem quadTensorHom_tmul (r : R) (z : QuadraticAlgebra L d 0) :
    quadTensorHom d R (r ⊗ₜ z) = ⟨r * algebraMap L R z.re, r * algebraMap L R z.im⟩ := by
  simp only [quadTensorHom, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, quadMap_apply]
  ext <;> simp [QuadraticAlgebra.algebraMap_eq, -QuadraticAlgebra.C_eq_algebraMap]

noncomputable def quadTensorInv (z : QuadraticAlgebra R (algebraMap L R d) 0) :
    R ⊗[L] QuadraticAlgebra L d 0 :=
  z.re ⊗ₜ 1 + z.im ⊗ₜ QuadraticAlgebra.omega

theorem quadTensorHom_inv (z : QuadraticAlgebra R (algebraMap L R d) 0) :
    quadTensorHom d R (quadTensorInv d R z) = z := by
  simp only [quadTensorInv, map_add (f := _), quadTensorHom_tmul]
  ext <;> simp [quadraticAlgebra_re_one, quadraticAlgebra_im_one]

theorem quadTensorInv_hom (z : R ⊗[L] QuadraticAlgebra L d 0) :
    quadTensorInv d R (quadTensorHom d R z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp [quadTensorInv]
  | tmul r q =>
    rw [quadTensorHom_tmul, quadTensorInv]
    dsimp only
    have hq : q = q.re • (1 : QuadraticAlgebra L d 0) + q.im • QuadraticAlgebra.omega := by
      ext <;> simp [quadraticAlgebra_re_one, quadraticAlgebra_im_one]
    conv_rhs => rw [hq]
    have h1 : ∀ c : L, r * algebraMap L R c = c • r := fun c => by
      rw [Algebra.smul_def, mul_comm]
    rw [TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.tmul_smul, h1, h1,
      TensorProduct.smul_tmul', TensorProduct.smul_tmul']
  | add x y hx hy =>
    have hadd : quadTensorInv d R (quadTensorHom d R (x + y)) =
        quadTensorInv d R (quadTensorHom d R x) + quadTensorInv d R (quadTensorHom d R y) := by
      simp only [map_add (f := _), quadTensorInv, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add,
        TensorProduct.add_tmul]
      abel
    rw [hadd, hx, hy]

noncomputable def quadTensorEquiv :
    R ⊗[L] QuadraticAlgebra L d 0 ≃ₐ[R] QuadraticAlgebra R (algebraMap L R d) 0 :=
  AlgEquiv.ofBijective (quadTensorHom d R)
    ⟨Function.LeftInverse.injective (quadTensorInv_hom d R),
      Function.RightInverse.surjective (quadTensorHom_inv d R)⟩

theorem quadTensorEquiv_tmul (r : R) (z : QuadraticAlgebra L d 0) :
    quadTensorEquiv d R (r ⊗ₜ z) = ⟨r * algebraMap L R z.re, r * algebraMap L R z.im⟩ :=
  quadTensorHom_tmul d R r z

end BaseChange

section Bridge

open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.Global.SemiLocal
open scoped NumberField.LiesOver

variable {L : Type*} [Field L] [NumberField L] (d : L) [Fact (∀ r : L, r ^ 2 ≠ d + 0 * r)]



end Bridge

section HasseNorm

open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.Global.SemiLocal Filter

universe u

variable {L : Type u} [Field L] [NumberField L]

end HasseNorm

end GroundTheory.Automorphic
end

section

set_option maxSynthPendingDepth 1

open MeasureTheory Filter Topology Module End
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace GroundTheory.Automorphic.CompactAbelianFourier

noncomputable section

set_option linter.unusedSectionVars false

variable {C : Type*} [CommGroup C] [TopologicalSpace C] [IsTopologicalGroup C] [CompactSpace C]
  [T2Space C]

section Metrizable

variable [SecondCountableTopology C] [MeasurableSpace C] [BorelSpace C]
  (μ : Measure C) [μ.IsHaarMeasure]

def transl (h : C) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (Lp.compMeasurePreservingₗᵢ ℂ (fun x => h * x) (measurePreserving_mul_left μ h)).toContinuousLinearMap

variable (ψ : C(C, ℝ))


end Metrizable

theorem exists_char_ne_one {g : C} (hg : g ≠ 1) : ∃ χ : C →ₜ* Circle, χ g ≠ 1 :=
  _root_.UpperTheory.Reformulated.B.CharactersSeparatePoints.exists_char_ne_one hg

theorem exists_char_ne {x y : C} (hxy : x ≠ y) : ∃ χ : C →ₜ* Circle, χ x ≠ χ y := by
  obtain ⟨χ, hχ⟩ := exists_char_ne_one (g := x * y⁻¹) (fun h => hxy (mul_inv_eq_one.1 h))
  refine ⟨χ, fun h => hχ ?_⟩
  rw [map_mul, map_inv, h, mul_inv_cancel]

def charCM (χ : C →ₜ* Circle) : C(C, ℂ) := ⟨fun x => (χ x : ℂ), continuous_subtype_val.comp χ.continuous⟩

theorem charCM_apply (χ : C →ₜ* Circle) (x : C) : charCM χ x = (χ x : ℂ) := rfl

theorem charCM_mul (χ χ' : C →ₜ* Circle) : charCM (χ * χ') = charCM χ * charCM χ' := by
  ext x
  simp [charCM_apply]

theorem charCM_one : charCM (1 : C →ₜ* Circle) = 1 := by
  ext x
  simp [charCM_apply]

theorem star_charCM (χ : C →ₜ* Circle) : star (charCM χ) = charCM χ⁻¹ := by
  ext x
  change conj ((χ x : Circle) : ℂ) = (((χ x)⁻¹ : Circle) : ℂ)
  rw [Circle.coe_inv_eq_conj]

def charAlgebra : StarSubalgebra ℂ C(C, ℂ) :=
  { (Submodule.span ℂ (Set.range (charCM (C := C)))).toSubalgebra
      (Submodule.subset_span ⟨1, charCM_one⟩)
      (fun a b ha hb => by
        induction ha using Submodule.span_induction with
        | mem x hx =>
          induction hb using Submodule.span_induction with
          | mem y hy =>
            obtain ⟨χ, rfl⟩ := hx
            obtain ⟨χ', rfl⟩ := hy
            exact Submodule.subset_span ⟨χ * χ', charCM_mul χ χ'⟩
          | zero => rw [mul_zero]; exact Submodule.zero_mem _
          | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
          | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hy
        | zero => rw [zero_mul]; exact Submodule.zero_mem _
        | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
        | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx) with
    star_mem' := fun {a} ha => by
      change a ∈ Submodule.span ℂ (Set.range (charCM (C := C))) at ha
      change star a ∈ Submodule.span ℂ (Set.range (charCM (C := C)))
      induction ha using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨χ, rfl⟩ := hx
        exact Submodule.subset_span ⟨χ⁻¹, (star_charCM χ).symm⟩
      | zero => rw [star_zero]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [star_add]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx => rw [star_smul]; exact Submodule.smul_mem _ _ hx }

theorem charAlgebra_separatesPoints : (charAlgebra (C := C)).SeparatesPoints := by
  intro x y hxy
  obtain ⟨χ, hχ⟩ := exists_char_ne hxy
  exact ⟨charCM χ, ⟨charCM χ, Submodule.subset_span ⟨χ, rfl⟩, rfl⟩, fun h => hχ (Circle.coe_injective h)⟩

theorem span_charCM_dense :
    (Submodule.span ℂ (Set.range (charCM (C := C)))).topologicalClosure = ⊤ := by
  have h := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _
    (charAlgebra_separatesPoints (C := C))
  rw [eq_top_iff]
  intro f _
  have hf : f ∈ (charAlgebra (C := C)).topologicalClosure := by rw [h]; trivial
  exact hf

section L2

variable [MeasurableSpace C] [BorelSpace C] (μ : Measure C) [μ.IsHaarMeasure]

variable [IsProbabilityMeasure μ]

end L2

end

end GroundTheory.Automorphic.CompactAbelianFourier
end
