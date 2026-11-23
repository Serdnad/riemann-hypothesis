module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.RingTheory.LaurentSeries
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Integral.ExpDecay
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity

@[expose] public section

section

open scoped LaurentSeries PowerSeries
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.OnePoint

universe u v w

section Algebra

variable {K : Type u} [Field K]

theorem exists_algHom_of_isIntegrallyClosedIn {L : Type w} [Field L] [Algebra K L]
    [IsIntegrallyClosedIn K L] {A : Type v} [CommRing A] [Algebra K A] [Algebra.IsIntegral K A]
    (φ : A →ₐ[K] L) : ∃ ψ : A →ₐ[K] K, (Algebra.ofId K L).comp ψ = φ := by
  have hmem : ∀ a : A, φ a ∈ (Algebra.ofId K L).range := fun a ↦
    (isIntegrallyClosedIn_iff.mp ‹_›).2 ((Algebra.IsIntegral.isIntegral (R := K) a).map φ)
  let e := AlgEquiv.ofInjective (Algebra.ofId K L) (algebraMap K L).injective
  refine ⟨(e.symm : _ →ₐ[K] K).comp (φ.codRestrict _ hmem), ?_⟩
  ext a
  exact congrArg Subtype.val (e.apply_symm_apply (φ.codRestrict _ hmem a))

end Algebra

section Scheme

variable {K : Type u} [Field K]

theorem epi_of_nonempty {T : Scheme.{u}} [Nonempty T] (g : T ⟶ Spec (.of K)) : Epi g :=
  have : Surjective g := ⟨Function.surjective_to_subsingleton _⟩
  Flat.epi_of_flat_of_surjective g

theorem point_ext {X T : Scheme.{u}} [Nonempty T] (g : T ⟶ Spec (.of K))
    {s s' : Spec (.of K) ⟶ X} (h : g ≫ s = g ≫ s') : s = s' :=
  have := epi_of_nonempty g
  (cancel_epi g).mp h

theorem exists_section_of_locallyQuasiFinite {F : Scheme.{u}} (f : F ⟶ Spec (.of K))
    [LocallyQuasiFinite f] (L : Type u) [Field L] [Algebra K L] [IsIntegrallyClosedIn K L]
    (x : Spec (.of L) ⟶ F) (hx : x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K L))) :
    ∃ x₀ : Spec (.of K) ⟶ F, Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ x₀ = x ∧
      x₀ ≫ f = 𝟙 _ ∧
      ∀ x₁ : Spec (.of K) ⟶ F, Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ x₁ = x →
        x₁ = x₀ := by
  suffices H : ∃ x₀ : Spec (.of K) ⟶ F,
      Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ x₀ = x by
    obtain ⟨x₀, h₀⟩ := H
    refine ⟨x₀, h₀, point_ext (Spec.map (CommRingCat.ofHom (algebraMap K L))) ?_,
      fun x₁ h₁ ↦ point_ext _ (h₁.trans h₀.symm)⟩
    rw [reassoc_of% h₀, hx, Category.comp_id]
  obtain ⟨A, i, _, q, hq⟩ := Scheme.exists_Spec_apply_eq (x (Classical.arbitrary _))
  have hle : Set.range x ⊆ Set.range i := by
    rintro _ ⟨t, rfl⟩
    exact ⟨q, hq.trans (congrArg x (Subsingleton.elim _ _))⟩
  obtain ⟨l, rfl⟩ : ∃ l, l ≫ i = x := ⟨_, IsOpenImmersion.lift_fac i x hle⟩
  obtain ⟨a, rfl⟩ := Spec.map_surjective l
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (i ≫ f)
  have hqf : φ.hom.QuasiFinite := by
    have : LocallyQuasiFinite (Spec.map φ) := hφ ▸ inferInstance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite)).mp this
  let : Algebra K A := φ.hom.toAlgebra
  have : Algebra.QuasiFinite K A := hqf
  have : Module.Finite K A := .of_quasiFinite
  rw [Category.assoc, ← hφ, ← Spec.map_comp] at hx
  have hc := congrArg CommRingCat.Hom.hom (Spec.map_injective hx)
  let a' : A →ₐ[K] L := ⟨a.hom, fun c ↦ DFunLike.congr_fun hc c⟩
  obtain ⟨ψ, hψ⟩ := exists_algHom_of_isIntegrallyClosedIn a'
  refine ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ i, ?_⟩
  rw [← Category.assoc, ← Spec.map_comp]
  congr 2
  ext t
  exact DFunLike.congr_fun hψ t

end Scheme
end GlobalTheory.OnePoint
end

section

open MeasureTheory
open scoped BigOperators

namespace GlobalTheory.LatticeMean

theorem exists_strict_domain (Λ : AddSubgroup ℂ)
    (h : ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}) :
    Countable Λ ∧ ∃ F : Set ℂ, MeasurableSet F ∧ ∀ x : ℂ, ∃! g : Λ, (g : ℂ) + x ∈ F := by
  obtain ⟨w₁, w₂, hli, hΛ⟩ := h
  let b : Module.Basis (Fin 2) ℝ ℂ :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp)
  have hb : Set.range b = {w₁, w₂} := by
    simp only [b, coe_basisOfLinearIndependentOfCardEqFinrank]
    ext x
    simp [or_comm]
  have hΛ' : Λ = (Submodule.span ℤ (Set.range b)).toAddSubgroup := by
    rw [hΛ, hb, Submodule.span_int_eq_addSubgroupClosure]
  subst hΛ'
  refine ⟨?_, ZSpan.fundamentalDomain b, ZSpan.fundamentalDomain_measurableSet b, fun x => ?_⟩
  · exact inferInstanceAs (Countable (Submodule.span ℤ (Set.range b)))
  · exact ZSpan.exist_unique_vadd_mem_fundamentalDomain b x

theorem setAverage_eq_of_domain {V : Type} [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]
    [SecondCountableTopology V]
    (μ : Measure V) [μ.IsAddLeftInvariant] (A : AddSubgroup V) [Countable A] (f : V → ℝ)
    (hf : ∀ a ∈ A, ∀ z, f (a + z) = f z) (P : Set V) (hP : IsAddFundamentalDomain A P μ) :
    ⨍ z in Classical.epsilon (fun Fd : Set V => IsAddFundamentalDomain A Fd μ), f z ∂μ
      = ⨍ z in P, f z ∂μ := by
  have hE := Classical.epsilon_spec (p := fun Fd : Set V => IsAddFundamentalDomain A Fd μ) ⟨P, hP⟩
  rw [setAverage_eq, setAverage_eq, hE.setIntegral_eq hP (fun g x => hf g g.2 x),
    measureReal_def, measureReal_def, hE.measure_eq hP]

theorem setAverage_pi (r : ℕ) (F : Set ℂ) (f : ℂ → ℝ) :
    ⨍ z in Set.univ.pi (fun _ : Fin r => F), ∏ k, f (z k) = (⨍ z in F, f z) ^ r := by
  rw [setAverage_eq, setAverage_eq, volume_pi, Measure.restrict_pi_pi,
    integral_fintype_prod_eq_pow, measureReal_def, Measure.pi_pi]
  simp [measureReal_def, mul_pow]

theorem mean_prod_eq_pow : ∀ (Λ : AddSubgroup ℂ), (∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}) → ∀ (f : ℂ → ℝ), (∀ ω ∈ Λ, ∀ z, f (ω + z) = f z) → ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : MeasureTheory.Measure V) [μ.IsAddHaarMeasure] (r : ℕ) (e : V ≃ₗ[ℝ] (Fin r → ℂ)) (A : AddSubgroup V), (∀ x, x ∈ A ↔ ∀ k, e x k ∈ Λ) → ⨍ z in Classical.epsilon (fun Fd : Set V => MeasureTheory.IsAddFundamentalDomain A Fd μ), ∏ k, f (e z k) ∂μ = (⨍ z in Classical.epsilon (fun Fd : Set ℂ => MeasureTheory.IsAddFundamentalDomain Λ Fd MeasureTheory.volume), f z) ^ r := by
  intro Λ hΛ f hf V _ _ _ _ _ μ _ r e A hA
  obtain ⟨hc, F, hFm, hF⟩ := exists_strict_domain Λ hΛ
  let ec : V ≃L[ℝ] (Fin r → ℂ) := e.toContinuousLinearEquiv
  let em : V ≃ᵐ (Fin r → ℂ) := ec.toHomeomorph.toMeasurableEquiv
  have hem : ∀ x, em x = e x := fun _ => rfl
  have hAc : Countable A := by
    refine Function.Injective.countable
      (f := fun (a : A) (k : Fin r) => (⟨e a k, (hA a).1 a.2 k⟩ : Λ)) ?_
    intro a b hab
    apply Subtype.ext
    apply e.injective
    funext k
    exact congrArg Subtype.val (congrFun hab k)
  have hQm : MeasurableSet (Set.univ.pi (fun _ : Fin r => F)) :=
    MeasurableSet.univ_pi fun _ => hFm
  have hP : IsAddFundamentalDomain A (em ⁻¹' Set.univ.pi (fun _ : Fin r => F)) μ := by
    refine IsAddFundamentalDomain.mk' (em.measurable hQm).nullMeasurableSet fun x => ?_
    choose g hg hu using fun k => hF (e x k)
    refine ⟨⟨e.symm fun k => (g k : ℂ), (hA _).2 fun k => by simp⟩, ?_, ?_⟩
    · intro k _
      show e (e.symm (fun k => (g k : ℂ)) + x) k ∈ F
      simpa using hg k
    · intro a ha
      apply Subtype.ext
      apply e.injective
      funext k
      have h1 : e ((a : V) + x) k ∈ F := ha k (Set.mem_univ k)
      have h2 := hu k ⟨e a k, (hA a).1 a.2 k⟩ (by simpa using h1)
      simpa using congrArg Subtype.val h2
  have hF' : IsAddFundamentalDomain Λ F volume :=
    IsAddFundamentalDomain.mk' hFm.nullMeasurableSet hF
  rw [setAverage_eq_of_domain μ A (fun z => ∏ k, f (e z k)) ?_ _ hP,
    setAverage_eq_of_domain volume Λ f hf F hF', ← setAverage_pi]
  swap
  · intro a ha z
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [map_add (f := _), Pi.add_apply, hf _ ((hA a).1 ha k)]
  haveI : (μ.map em).IsAddHaarMeasure := ec.isAddHaarMeasure_map μ
  have hs := Measure.isAddLeftInvariant_eq_smul (μ.map em) (volume : Measure (Fin r → ℂ))
  have hc0 : Measure.addHaarScalarFactor (μ.map em) (volume : Measure (Fin r → ℂ)) ≠ 0 :=
    (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne'
  have h1 : ⨍ z in em ⁻¹' Set.univ.pi (fun _ : Fin r => F), ∏ k, f (e z k) ∂μ
      = ⨍ z in Set.univ.pi (fun _ : Fin r => F), ∏ k, f (z k) ∂(μ.map em) := by
    rw [setAverage_eq, setAverage_eq, setIntegral_map_equiv, measureReal_def, measureReal_def,
      em.map_apply]
    rfl
  rw [h1, hs, setAverage_eq, setAverage_eq, Measure.restrict_smul, integral_smul_nnreal_measure,
    measureReal_nnreal_smul_apply]
  have hc1 : ((Measure.addHaarScalarFactor (μ.map em) (volume : Measure (Fin r → ℂ)) : NNReal) : ℝ) ≠ 0 := by
    exact_mod_cast hc0
  rw [NNReal.smul_def, smul_eq_mul, smul_eq_mul, smul_eq_mul, mul_inv]
  field_simp

end GlobalTheory.LatticeMean
end

section

open MeasureTheory Filter Topology Set

namespace GlobalTheory

theorem vertRay_expPow_weight_integrableOn (c : ℝ) (m : ℕ) (hc : 0 < c) :
    IntegrableOn (fun s : ℝ => Real.exp (-c * s) * (1 + s) ^ m) (Ioi 0) := by
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = c / 2 := ⟨_, rfl⟩
  have hb : 0 < b := by rw [hbdef]; positivity
  have hI : IntegrableOn (fun s : ℝ =>
      ((m.factorial : ℝ) / b ^ m * Real.exp b) * Real.exp (-b * s)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 hb).const_mul _
  refine Integrable.mono' hI ?_ ?_
  · exact (Continuous.aestronglyMeasurable (by fun_prop))
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => ?_)
    have hs0 : (0:ℝ) ≤ s := le_of_lt hs
    have h1 := Real.pow_div_factorial_le_exp (b * (1 + s)) (mul_nonneg hb.le (by linarith)) m
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg (by linarith) _))]
    have hf : (0:ℝ) < m.factorial := by exact_mod_cast m.factorial_pos
    rw [div_le_iff₀ hf, mul_pow] at h1
    have key : (1 + s) ^ m ≤ (m.factorial : ℝ) / b ^ m * Real.exp (b * (1 + s)) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hb m)]
      linarith [h1]
    have he : Real.exp (b * (1 + s)) = Real.exp b * Real.exp (b * s) := by
      rw [← Real.exp_add]; ring_nf
    have hcs : Real.exp (-c * s) * Real.exp (b * s) = Real.exp (-b * s) := by
      rw [← Real.exp_add]; congr 1; rw [hbdef]; ring
    calc Real.exp (-c * s) * (1 + s) ^ m
        ≤ Real.exp (-c * s) * ((m.factorial : ℝ) / b ^ m * Real.exp (b * (1 + s))) :=
          mul_le_mul_of_nonneg_left key (Real.exp_pos _).le
      _ = ((m.factorial : ℝ) / b ^ m * Real.exp b) * (Real.exp (-c * s) * Real.exp (b * s)) := by
          rw [he]; ring
      _ = ((m.factorial : ℝ) / b ^ m * Real.exp b) * Real.exp (-b * s) := by rw [hcs]

theorem vertRay_integral_expPow_bound : ∀ (g : ℂ → ℂ) (K c : ℝ) (m : ℕ) (τ : ℂ),
    ContinuousOn g {z : ℂ | 0 < z.im} → 0 < c →
    (∀ z : ℂ, 1 ≤ z.im → ‖g z‖ ≤ K * Real.exp (-c * z.im) * (1 + ‖z‖) ^ m) → 1 ≤ τ.im →
    IntegrableOn (fun s : ℝ => g (τ + s * Complex.I)) (Ioi 0) ∧
      ‖∫ s in Ioi (0:ℝ), g (τ + s * Complex.I)‖ ≤
        K * Real.exp (-c * τ.im) * (1 + ‖τ‖) ^ m *
          ∫ s in Ioi (0:ℝ), Real.exp (-c * s) * (1 + s) ^ m := by
  intro g K c m τ hg hc hb hτ
  have hK : 0 ≤ K := by
    have h := hb Complex.I (by simp)
    have hpos : 0 < Real.exp (-c * Complex.I.im) * (1 + ‖Complex.I‖) ^ m := by positivity
    by_contra hneg
    have hneg' : K < 0 := not_le.mp hneg
    have : K * Real.exp (-c * Complex.I.im) * (1 + ‖Complex.I‖) ^ m < 0 := by
      rw [mul_assoc]; exact mul_neg_of_neg_of_pos hneg' hpos
    linarith [norm_nonneg (g Complex.I)]
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = K * Real.exp (-c * τ.im) * (1 + ‖τ‖) ^ m := ⟨_, rfl⟩
  rw [← hA]
  have hw := vertRay_expPow_weight_integrableOn c m hc
  have hbound : ∀ s : ℝ, 0 < s →
      ‖g (τ + s * Complex.I)‖ ≤ A * (Real.exp (-c * s) * (1 + s) ^ m) := by
    intro s hs
    have him : (τ + s * Complex.I).im = τ.im + s := by simp
    have h1 := hb (τ + s * Complex.I) (by rw [him]; linarith)
    rw [him] at h1
    have hn : ‖τ + s * Complex.I‖ ≤ ‖τ‖ + s := by
      calc ‖τ + s * Complex.I‖ ≤ ‖τ‖ + ‖(s:ℂ) * Complex.I‖ := norm_add_le _ _
        _ = ‖τ‖ + s := by
          rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    have hp : (1 + ‖τ + s * Complex.I‖) ^ m ≤ (1 + ‖τ‖) ^ m * (1 + s) ^ m := by
      rw [← mul_pow]
      apply pow_le_pow_left₀ (by positivity)
      nlinarith [mul_nonneg (norm_nonneg τ) hs.le]
    have he : Real.exp (-c * (τ.im + s)) = Real.exp (-c * τ.im) * Real.exp (-c * s) := by
      rw [← Real.exp_add]; ring_nf
    calc ‖g (τ + s * Complex.I)‖
        ≤ K * Real.exp (-c * (τ.im + s)) * (1 + ‖τ + s * Complex.I‖) ^ m := h1
      _ ≤ K * Real.exp (-c * (τ.im + s)) * ((1 + ‖τ‖) ^ m * (1 + s) ^ m) :=
          mul_le_mul_of_nonneg_left hp (mul_nonneg hK (Real.exp_pos _).le)
      _ = A * (Real.exp (-c * s) * (1 + s) ^ m) := by rw [he, hA]; ring
  have hmeas : AEStronglyMeasurable (fun s : ℝ => g (τ + s * Complex.I))
      (volume.restrict (Ioi 0)) := by
    have hc' : ContinuousOn (fun s : ℝ => g (τ + s * Complex.I)) (Ioi 0) := by
      refine ContinuousOn.comp (g := g) (f := fun s : ℝ => τ + s * Complex.I) hg (by fun_prop) ?_
      intro s hs
      have him : (τ + s * Complex.I).im = τ.im + s := by simp
      show 0 < (τ + s * Complex.I).im
      rw [him]
      linarith [mem_Ioi.mp hs]
    exact hc'.aestronglyMeasurable measurableSet_Ioi
  have hae : ∀ᵐ s : ℝ ∂(volume.restrict (Ioi (0:ℝ))),
      ‖g (τ + s * Complex.I)‖ ≤ A * (Real.exp (-c * s) * (1 + s) ^ m) :=
    (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => hbound s hs)
  have hint : IntegrableOn (fun s : ℝ => g (τ + s * Complex.I)) (Ioi 0) :=
    Integrable.mono' (hw.const_mul A) hmeas hae
  refine ⟨hint, ?_⟩
  calc ‖∫ s in Ioi (0:ℝ), g (τ + s * Complex.I)‖
      ≤ ∫ s in Ioi (0:ℝ), A * (Real.exp (-c * s) * (1 + s) ^ m) :=
        norm_integral_le_of_norm_le (hw.const_mul A) hae
    _ = A * ∫ s in Ioi (0:ℝ), Real.exp (-c * s) * (1 + s) ^ m := integral_const_mul A _

end GlobalTheory
end

section

open MeasureTheory Filter Topology Set

namespace GlobalTheory

theorem top_side_integral_tendsto_zero : ∀ (g : ℂ → ℂ) (K c : ℝ) (m : ℕ) (τ : ℂ), ContinuousOn g {z : ℂ | 0 < z.im} → 0 < c →
    (∀ z : ℂ, 1 ≤ z.im → ‖g z‖ ≤ K * Real.exp (-c * z.im) * (1 + ‖z‖) ^ m) → 1 ≤ τ.im →
    Tendsto (fun S : ℝ => ∫ t in (0:ℝ)..1, g (Complex.I + t * (τ - Complex.I) + S * Complex.I)) atTop (𝓝 0) := by
  intro g K c m τ _ hc hg hτ
  set B : ℝ := 2 + ‖τ - Complex.I‖ with hB
  have hB0 : 0 ≤ B := by positivity
  set F : ℝ → ℝ := fun S => |K| * Real.exp (-c * (1 + S)) * (B + S) ^ m with hF
  have hpt : ∀ S : ℝ, 0 ≤ S → ∀ t ∈ Set.uIoc (0:ℝ) 1,
      ‖g (Complex.I + t * (τ - Complex.I) + S * Complex.I)‖ ≤ F S := by
    intro S hS t ht
    rw [Set.uIoc_of_le zero_le_one] at ht
    obtain ⟨ht0, ht1⟩ := ht
    set z := Complex.I + t * (τ - Complex.I) + S * Complex.I with hz
    have him : z.im = 1 + t * (τ.im - 1) + S := by
      simp [hz]
    have him1 : 1 + S ≤ z.im := by
      rw [him]; nlinarith
    have hnorm : 1 + ‖z‖ ≤ B + S := by
      have h1 : ‖z‖ ≤ ‖Complex.I‖ + ‖(t:ℂ) * (τ - Complex.I)‖ + ‖(S:ℂ) * Complex.I‖ := by
        rw [hz]; exact norm_add₃_le
      have h2 : ‖(t:ℂ) * (τ - Complex.I)‖ ≤ ‖τ - Complex.I‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
        exact mul_le_of_le_one_left (norm_nonneg _) ht1
      have h3 : ‖(S:ℂ) * Complex.I‖ = S := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hS]
      rw [Complex.norm_I] at h1
      rw [hB]; linarith
    have he : Real.exp (-c * z.im) ≤ Real.exp (-c * (1 + S)) := Real.exp_le_exp.mpr (by nlinarith)
    have hp : (1 + ‖z‖) ^ m ≤ (B + S) ^ m := pow_le_pow_left₀ (by positivity) hnorm m
    calc ‖g z‖ ≤ K * Real.exp (-c * z.im) * (1 + ‖z‖) ^ m := hg z (by linarith)
      _ ≤ |K| * Real.exp (-c * z.im) * (1 + ‖z‖) ^ m := by
          gcongr; exact le_abs_self K
      _ ≤ |K| * Real.exp (-c * (1 + S)) * (B + S) ^ m :=
          mul_le_mul (mul_le_mul_of_nonneg_left he (abs_nonneg K)) hp (by positivity) (by positivity)
  have hlim : Tendsto F atTop (𝓝 0) := by
    have h1 : Tendsto (fun S : ℝ => c * (B + S)) atTop atTop :=
      (tendsto_atTop_add_const_left atTop B tendsto_id).const_mul_atTop hc
    have h2 := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero m).comp h1).const_mul
      (|K| * (c ^ m)⁻¹ * Real.exp (c * B - c))
    rw [mul_zero] at h2
    refine h2.congr' ?_
    filter_upwards with S
    have hcm : c ^ m ≠ 0 := pow_ne_zero _ hc.ne'
    have hexp : Real.exp (c * B - c) * Real.exp (-(c * (B + S))) = Real.exp (-c * (1 + S)) := by
      rw [← Real.exp_add]; ring_nf
    simp only [Function.comp, hF]
    rw [mul_pow]
    calc |K| * (c ^ m)⁻¹ * Real.exp (c * B - c) * (c ^ m * (B + S) ^ m * Real.exp (-(c * (B + S))))
        = |K| * (Real.exp (c * B - c) * Real.exp (-(c * (B + S)))) * ((c ^ m)⁻¹ * c ^ m) * (B + S) ^ m := by ring
      _ = |K| * Real.exp (-c * (1 + S)) * (B + S) ^ m := by rw [hexp, inv_mul_cancel₀ hcm, mul_one]
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop (0:ℝ)] with S hS
  have := intervalIntegral.norm_integral_le_of_norm_le_const (hpt S hS)
  rwa [sub_zero, abs_one, mul_one] at this

end GlobalTheory
end

section

open scoped Matrix
open NumberField IsDedekindDomain

namespace GlobalTheory


open NumberField.InfinitePlace NumberField.mixedEmbedding in
theorem totallyComplex_span_embeddings_and_finrank :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E],
      Submodule.span ℝ (Set.range (Pi.ringHom fun w : InfinitePlace E => w.embedding)) = ⊤ ∧
        Module.finrank ℝ (InfinitePlace E → ℂ) = Module.finrank ℚ E := by
  intro E _ _ _
  constructor
  ·
    let f : mixedSpace E →ₗ[ℝ] (InfinitePlace E → ℂ) :=
      { toFun := fun x w => x.2 ⟨w, IsTotallyComplex.isComplex w⟩
        map_add' := fun x y => rfl
        map_smul' := fun c x => rfl }
    have hf : Function.Surjective f := by
      intro y
      exact ⟨(0, fun w => y w.1), rfl⟩
    have hcomp : ∀ x : E, f (mixedEmbedding E x) = Pi.ringHom (fun w : InfinitePlace E => w.embedding) x := by
      intro x
      funext w
      simp only [f, LinearMap.coe_mk, AddHom.coe_mk, mixedEmbedding_apply_isComplex]
      rfl
    have hspan : Submodule.span ℝ (Set.range (mixedEmbedding E)) = ⊤ := by
      apply eq_top_iff.mpr
      rw [← (latticeBasis E).span_eq]
      apply Submodule.span_mono
      rintro _ ⟨i, rfl⟩
      exact ⟨_, (latticeBasis_apply E i).symm⟩
    have himg : f '' Set.range (mixedEmbedding E) =
        Set.range (Pi.ringHom fun w : InfinitePlace E => w.embedding) := by
      rw [← Set.range_comp]
      exact congrArg Set.range (funext hcomp)
    rw [← himg, ← Submodule.map_span, hspan, Submodule.map_top, LinearMap.range_eq_top]
    exact hf
  · rw [Module.finrank_pi_fintype]
    simp only [Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    rw [IsTotallyComplex.finrank, card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero]
    ring

end GlobalTheory
end

section

open Polynomial

namespace GlobalTheory.KummerCob

theorem zeta_mem_range : ∀ (k K Ω : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k[X] K] [Field Ω] [Algebra K Ω]
    (N : ℕ) (ζ : Ω), 0 < N → IsPrimitiveRoot ζ N → ζ ∈ Set.range (algebraMap K Ω) := by
  intro k K Ω _ _ _ _ _ _ _ N ζ hN hζ
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero (N : k) := ⟨by exact_mod_cast hN.ne'⟩
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot k N
  let φ : k →+* Ω := (algebraMap K Ω).comp ((algebraMap k[X] K).comp Polynomial.C)
  have hφ : Function.Injective φ := φ.injective
  have hξ' : IsPrimitiveRoot (φ ξ) N := hξ.map_of_injective hφ
  obtain ⟨i, -, hi⟩ := hξ'.eq_pow_of_pow_eq_one hζ.pow_eq_one
  refine ⟨(algebraMap k[X] K (Polynomial.C ξ)) ^ i, ?_⟩
  rw [map_pow, ← hi]
  rfl

end GlobalTheory.KummerCob
end
