module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1594
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle010
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1599
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle226
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle025
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1608
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAwaySurjective
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1604
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1607
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle977
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1597
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Shapes.Connected
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle039
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle026

@[expose] public section

section

open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

theorem _root_.GlobalTheory.T.continuous_heisenbergOperatorBoundedThetaFunctions : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (nS nT : ℕ)
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ), ∀ f : BBF σ JS JT ξ₀ ψ, Continuous fun w => rhoBF σ JS JT ξ₀ ψ hψ w f := by
  first | exact @GlobalTheory.RealWeilF.continuous_rhoBF | exact GlobalTheory.RealWeilF.continuous_rhoBF | (intros; apply GlobalTheory.RealWeilF.continuous_rhoBF <;> assumption)
end

section

open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

theorem _root_.GlobalTheory.T.exists_finiteAdelic_add_realChartPoint : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (nS nT : ℕ)
    (θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)) (ι : (InfinitePlace F → ℂ) →+ AEF F E), IsChartF θ ι →
      ∀ w : WOF F E nS nT, ∃ (u : WOF F E nS nT) (v : IxF F nS nT → ℂ), u.map (infPartF F E) = 0 ∧ w = u + iotaVF ι v := by
  first | exact @GlobalTheory.RealWeilF.exists_realZero_add_iotaVF | exact GlobalTheory.RealWeilF.exists_realZero_add_iotaVF | (intros; apply GlobalTheory.RealWeilF.exists_realZero_add_iotaVF <;> assumption)
end

section

open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

theorem _root_.GlobalTheory.T.lintegral_eq_of_heisenbergInvariant_norms : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (nS nT : ℕ)
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ), ∀ (μ : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), μ.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 μ → ∀ f f' : BBF σ JS JT ξ₀ ψ,
      (∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (Φ : BBF σ JS JT ξ₀ ψ →L[ℂ] H),
        (∀ w g, ‖Φ (rhoBF σ JS JT ξ₀ ψ hψ w g)‖ = ‖Φ g‖) → ‖Φ f'‖ = ‖Φ f‖) →
      ∫⁻ w in 𝓕, ‖f'.1 w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f.1 w‖ₑ ^ 2 ∂μ := by
  first | exact @GlobalTheory.RealWeilF.lintegral_eq_of_normsF | exact GlobalTheory.RealWeilF.lintegral_eq_of_normsF | (intros; apply GlobalTheory.RealWeilF.lintegral_eq_of_normsF <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open MvPolynomial
open GlobalTheory.CxForm GlobalTheory.GoodMetric GlobalTheory.CxForm.DensPow GlobalTheory.GrassModel GlobalTheory.GrassModel.TopRead

namespace GlobalTheory.ChernCalc.DensTop

variable {n : ℕ}

theorem bas_mul_smul (S T : Finset (Fin (n + n))) : ∃ c : ℂ, bas n S * bas n T = c • bas n (S ∪ T) := by
  by_cases h : Disjoint S T
  · obtain ⟨ε, e⟩ := bas_mul h
    exact ⟨_, by rw [e, Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ]⟩
  · have := ExteriorAlgebra.basis_mul_of_not_disjoint ((Pi.basisFun ℂ (Fin n ⊕ Fin n)).reindex finSumFinEquiv)
      (Set.powersetCard.ofCard (s := S) rfl) (Set.powersetCard.ofCard (s := T) rfl) h
    have e : bas n S * bas n T = 0 := this
    exact ⟨0, by rw [e, zero_smul]⟩

theorem prod_sym_eq {ι : Type} [DecidableEq ι] (x : ι → Fin n × Fin n) (s : Finset ι) :
    ∃ (c : ℂ) (S : Finset (Fin (n + n))), S.card ≤ 2 * s.card ∧ ((∏ j ∈ s, sym (x j) : Ev n) : Alt n) = c • bas n S := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, ∅, by simp, by simp [bas_empty]⟩
  | insert a s ha ih =>
    obtain ⟨c, S, hS, e⟩ := ih
    obtain ⟨c₁, h₁⟩ := bas_mul_smul {finSumFinEquiv (.inl (x a).1)} {finSumFinEquiv (.inr (x a).2)}
    obtain ⟨c₂, h₂⟩ := bas_mul_smul ({finSumFinEquiv (.inl (x a).1)} ∪ {finSumFinEquiv (.inr (x a).2)}) S
    refine ⟨c₁ * c * c₂, ({finSumFinEquiv (.inl (x a).1)} ∪ {finSumFinEquiv (.inr (x a).2)}) ∪ S, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem ha]
      refine (Finset.card_union_le _ _).trans ?_
      have := Finset.card_union_le ({finSumFinEquiv (.inl (x a).1)} : Finset (Fin (n + n)))
        {finSumFinEquiv (.inr (x a).2)}
      rw [Finset.card_singleton, Finset.card_singleton] at this
      omega
    · rw [Finset.prod_insert ha, Subalgebra.coe_mul, e,
        show (sym (x a) : Alt n) = dz (x a).1 * dzb (x a).2 from rfl, dz, dzb, ← bas_singleton,
        ← bas_singleton, h₁, smul_mul_smul_comm, h₂, smul_smul]

theorem prod_sym_not_inj {m : ℕ} (x : Fin m → Fin n × Fin n) (h : ¬ Function.Injective fun j => (x j).1) :
    (∏ j, sym (x j) : Ev n) = 0 := by
  simp only [Function.Injective, not_forall] at h
  obtain ⟨i, j, hij, hne⟩ := h
  have h0 : sym (x i) * sym (x j) = 0 := by
    apply Subtype.ext
    change dz (x i).1 * dzb (x i).2 * (dz (x j).1 * dzb (x j).2) = 0
    rw [hij]
    exact ι_mul_ι_mul_ι_mul_ι_left _ _ _
  rw [← Finset.mul_prod_erase Finset.univ (fun a => sym (x a)) (Finset.mem_univ i),
    ← Finset.mul_prod_erase (Finset.univ.erase i) (fun a => sym (x a))
      (Finset.mem_erase.2 ⟨fun e => hne e.symm, Finset.mem_univ j⟩), ← mul_assoc, h0, zero_mul]

theorem dens_zero' : dens (0 : Alt n) = 0 := by simp [dens]

theorem dens_add' (x y : Alt n) : dens (x + y) = dens x + dens y := by simp [dens, add_div]

theorem dens_prod_diag : dens ((∏ a, sym (a, a) : Ev n) : Alt n) = ((Complex.I / 2) ^ n)⁻¹ := by
  have h1 := dens_vol n
  rw [vol_eq_smul_prod, Subalgebra.coe_smul, dens_smul] at h1
  exact eq_inv_of_mul_eq_one_right h1

theorem dens_prod {m : ℕ} (x : Fin m → Fin n × Fin n) :
    dens ((∏ j, sym (x j) : Ev n) : Alt n) =
      topForm n m (fun j => Pi.single (x j).1 1) * topForm n m (fun j => Pi.single (x j).2 1) /
        (Complex.I / 2) ^ n := by
  by_cases hm : m = n
  swap
  · have h0 : topForm n m = 0 := by simp [topForm, hm]
    rw [h0]
    simp only [AlternatingMap.zero_apply, mul_zero, zero_div]
    rcases lt_or_gt_of_ne hm with h | h
    · obtain ⟨c, S, hS, e⟩ := prod_sym_eq x Finset.univ
      have hne : S ≠ Finset.univ := by
        rintro rfl
        simp at hS
        omega
      rw [e]
      simp [dens, Finsupp.single_apply, hne]
    · rw [prod_sym_not_inj x, Subalgebra.coe_zero, dens_zero']
      intro hi
      have := Fintype.card_le_of_injective _ hi
      simp at this
      omega
  subst hm
  rw [topForm_self, topForm_self]
  by_cases ha : Function.Injective fun j => (x j).1
  swap
  · rw [prod_sym_not_inj x ha, Subalgebra.coe_zero, dens_zero', det_single_not_inj _ ha, zero_mul, zero_div]
  let π : Equiv.Perm (Fin m) := Equiv.ofBijective _ (Finite.injective_iff_bijective.mp ha)
  have hπ : ∀ j, (x j).1 = π j := fun j => rfl
  have e1 : (∏ j, sym (x j) : Ev m) = ∏ c, row c (Pi.single (x (π.symm c)).2 1) := by
    rw [← Equiv.prod_comp π fun c => row c (Pi.single (x (π.symm c)).2 1)]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Equiv.symm_apply_apply, ← hπ]
    simp [row, Pi.single_apply]
  have e2 := prod_row (n := m) (Matrix.of fun c => Pi.single (x (π.symm c)).2 1)
  have e3 : (Matrix.of fun c => (Pi.single (x (π.symm c)).2 1 : Fin m → ℂ)).det =
      (Pi.basisFun ℂ (Fin m)).det ((fun j => Pi.single (x j).2 1) ∘ π.symm) := by
    rw [Pi.basisFun_det]; rfl
  rw [e1]
  refine (congrArg (fun z : Ev m => dens (z : Alt m)) e2).trans ?_
  simp only [hπ, det_single_perm]
  rw [Subalgebra.coe_smul, dens_smul, dens_prod_diag, e3, AlternatingMap.map_perm, Equiv.Perm.sign_symm,
    Units.smul_def, zsmul_eq_mul, ← div_eq_mul_inv]

theorem dens_aeval_sym (n : ℕ) (P : MvPolynomial (Fin n × Fin n) ℂ) :
    dens ((aeval sym P : Ev n) : Alt n) = topCoeff P / (Complex.I / 2) ^ n := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial u c =>
    obtain ⟨l, hl⟩ : ∃ l : List (Fin n × Fin n), (l : Multiset _) = Finsupp.toMultiset u :=
      ⟨_, Multiset.coe_toList _⟩
    have hu : u = ∑ j, Finsupp.single (l.get j) 1 := by
      apply toMultiset_injective'
      rw [toMultiset_sum_single, Fin.univ_val_map, List.ofFn_get, hl]
    have hmon : (monomial u c : MvPolynomial (Fin n × Fin n) ℂ) = c • ∏ j, X (l.get j) := by
      rw [hu, show (∏ j, X (l.get j) : MvPolynomial (Fin n × Fin n) ℂ) = monomial (∑ j, Finsupp.single (l.get j) 1) 1 from
        (monomial_sum_one _ _).symm, smul_monomial, smul_eq_mul, mul_one]
    rw [hmon, map_smul, Subalgebra.coe_smul, dens_smul, map_prod]
    simp only [aeval_X]
    rw [dens_prod, ← topCoeff_prod, ← mul_div_assoc]
    congr 1
    unfold topCoeff
    simp only [MvPolynomial.coeff_smul, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => by ring
  | add p q hp hq =>
    rw [map_add (f := _), Subalgebra.coe_add, dens_add', hp, hq, ← add_div]
    congr 1
    unfold topCoeff
    simp only [MvPolynomial.coeff_add, mul_add, Finset.sum_add_distrib]

end GlobalTheory.ChernCalc.DensTop
end
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbMonoIsoAny

open GlobalTheory.NearFibreIso GlobalTheory.DenseFibreIso

theorem exists_away_bijective_of_fg {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
    (R K : Type) [CommRing R] [CommRing K]
    [Algebra R K] [Algebra R A] [Algebra R B] [IsScalarTower R A B] [Module.Flat R B]
    (hs : Function.Surjective (algebraMap A B))
    (hfg : (RingHom.ker (algebraMap A B)).FG)
    (h : Function.Injective
      (Algebra.TensorProduct.includeLeftRingHom : (A ⊗[R] K) →+* (A ⊗[R] K) ⊗[A] B))
    (m : PrimeSpectrum (A ⊗[R] K)) :
    ∃ a : A, algebraMap A (A ⊗[R] K) a ∉ m.asIdeal ∧ Function.Bijective
      (Algebra.TensorProduct.includeLeftRingHom :
        Localization.Away a →+* Localization.Away a ⊗[A] B) := by
  let I : Submodule A A := LinearMap.ker (Algebra.linearMap A B)
  have : Module.Finite A I := Module.Finite.iff_fg.2 hfg
  have hex : Function.Exact I.subtype (Algebra.linearMap A B) := LinearMap.exact_subtype_ker_map _
  have hinj : Function.Injective ((I.subtype.restrictScalars R).rTensor K) :=
    (LinearMap.lTensor_inj_iff_rTensor_inj K _).1
      (LinearMap.lTensor_injective_of_exact_of_flat ((Algebra.linearMap A B).restrictScalars R) hs
        (I.subtype.restrictScalars R) Subtype.val_injective hex K)
  have h1 : Subsingleton (I ⊗[R] K) := by
    refine subsingleton_of_forall_eq 0 fun z => hinj (h ?_)
    rw [map_zero, map_zero]
    induction z with
    | add y z hy hz => rw [map_add (f := _), map_add (f := _), hy, hz, add_zero]
    | tmul x c =>
      have e : (x : A) ⊗ₜ[R] c = (x : A) • ((1 : A) ⊗ₜ[R] c) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      have hx : (x : A) • (1 : B) = 0 := by
        rw [← Algebra.algebraMap_eq_smul_one]; exact x.2
      change ((x : A) ⊗ₜ[R] c) ⊗ₜ[A] (1 : B) = 0
      rw [e, TensorProduct.smul_tmul, hx, TensorProduct.tmul_zero]
  have h2 : Subsingleton ((A ⊗[R] K) ⊗[A] I) :=
    ((TensorProduct.comm A _ _).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R A A I K)).toEquiv.subsingleton
  obtain ⟨a, ha, ha'⟩ := exists_smul_eq_zero (A := A) (N := I) (A ⊗[R] K) m
  refine ⟨a, ha, ?_⟩
  have h3 := subsingleton_of_isUnit ha' (Localization.Away a)
    (IsLocalization.Away.algebraMap_isUnit a)
  rw [includeLeft_eq, EquivLike.bijective_comp]
  refine ⟨(injective_iff_map_eq_zero _).2 fun z hz => ?_, LinearMap.lTensor_surjective _ hs⟩
  obtain ⟨y, rfl⟩ := (lTensor_exact (Localization.Away a) hex hs z).1 hz
  rw [Subsingleton.elim y 0, map_zero]


set_option backward.isDefEq.respectTransparency.types false in
theorem near_isIso_of_finitePresentation {R : Type} [CommRing R] {Y X : Scheme.{0}} (s : X ⟶ Sp R)
    (f : Y ⟶ X) (K : Type) [Field K] [Algebra R K] [hcl : IsClosedImmersion f]
    [LocallyOfFinitePresentation s] [LocallyOfFinitePresentation (f ≫ s)] [Flat (f ≫ s)]
    [IsIso (pullback.snd f (pullback.fst s (spMap (algebraMap R K))))]
    (x : X) (hx : RingHom.ker (algebraMap R K) = (s x).asIdeal) :
    Near f (MorphismProperty.isomorphisms _) x := by
  refine local_of_ring (K := K) s f _ (fun A B _ _ _ _ _ _ j j' _ H hj hb m => ?_) x hx
  have h1 : IsClosedImmersion (spMap (algebraMap A B)) :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) H.flip hcl
  have hs : Function.Surjective (algebraMap A B) := by
    have h2 := (IsClosedImmersion.isAffine_surjective_of_isAffine (spMap (algebraMap A B))).2
    have e := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap A B))
    have h3 := (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of B)).hom).2.comp h2
    rw [← ConcreteCategory.coe_comp, e, ConcreteCategory.coe_comp] at h3
    exact h3.of_comp
  have : IsOpenImmersion j' := MorphismProperty.of_isPullback (P := @IsOpenImmersion) H ‹_›
  have e : spMap (algebraMap R B) = j' ≫ f ≫ s := by
    rw [← H.w_assoc, hj, ← Spec.map_comp, IsScalarTower.algebraMap_eq R A B]; rfl
  have h2 : Flat (spMap (algebraMap R B)) := by
    rw [e]; infer_instance
  have : Module.Flat R B := RingHom.flat_algebraMap_iff.1 (Flat.SpecMap_iff.1 h2)
  have h3 : LocallyOfFinitePresentation (spMap (algebraMap R B)) := by
    rw [e]; infer_instance
  have h4 : LocallyOfFinitePresentation (spMap (algebraMap R A)) := by
    rw [← hj]; infer_instance
  have : Algebra.FinitePresentation R B := RingHom.finitePresentation_algebraMap.1
    ((HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).1 h3)
  have : Algebra.FinitePresentation R A := RingHom.finitePresentation_algebraMap.1
    ((HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).1 h4)
  have hfg : (RingHom.ker (algebraMap A B)).FG :=
    Algebra.FinitePresentation.ker_fG_of_surjective (IsScalarTower.toAlgHom R A B) hs
  obtain ⟨a, ha, ha'⟩ := exists_away_bijective_of_fg R K hs hfg hb.1 m
  exact ⟨a, ha, isIso_SpecMap_iff.2 ha'⟩

theorem isIso_of_isClosedImmersion {S X Y : Scheme.{0}} (p : X ⟶ S)
    (f : Y ⟶ X) [IsClosedImmersion f] [GeometricallyConnected p] [Surjective (f ≫ p)]
    {g g' : ℕ} (hg' : SmoothOfRelativeDimension g' p)
    (hg : SmoothOfRelativeDimension g (f ≫ p)) (hle : g' ≤ g) : IsIso f := by
  have hn : ∀ y : X, Near f (MorphismProperty.isomorphisms _) y := by
    intro y
    obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (p y)) isOpen_univ
    replace hU : IsAffineOpen U := hU
    let j : Sp Γ(S, U) ⟶ S := hU.fromSpec
    obtain ⟨z, hz⟩ : p y ∈ Set.range j := by rw [hU.range_fromSpec]; exact hyU
    let gX := pullback.fst p j
    let s := pullback.snd p j
    let f' := pullback.snd f gX
    have HX := IsPullback.of_hasPullback p j
    have HY := IsPullback.of_hasPullback f gX
    have HYS := HY.paste_vert HX
    obtain ⟨y', hy', hy's⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := j) y z hz.symm
    have : Surjective (f' ≫ s) := MorphismProperty.of_isPullback HYS ‹_›
    have h₁ : SmoothOfRelativeDimension g' s :=
      (smoothOfRelativeDimension_isStableUnderBaseChange g').of_isPullback HX hg'
    have h₂ : SmoothOfRelativeDimension g (f' ≫ s) :=
      (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback HYS hg
    have : Smooth s := h₁.smooth
    have : Smooth (f' ≫ s) := h₂.smooth
    have : (s y').asIdeal.IsPrime := (s y').isPrime
    have := GlobalTheory.AbMonoIso.fibre_isIso s f' h₁ h₂ hle (s y').asIdeal.ResidueField
    have h := near_isIso_of_finitePresentation s f' (s y').asIdeal.ResidueField y'
      (Ideal.ker_algebraMap_residueField (s y').asIdeal)
    have h' := Near.of_pullback f HY.flip h
    rwa [hy'] at h'
  have h := isIso_of_near f (𝟙 _) (fun y => by simpa using hn y)
  have e : f = inv (pullback.fst f (𝟙 X)) ≫ pullback.snd f (𝟙 X) := by
    rw [IsIso.eq_inv_comp, pullback.condition, Category.comp_id]
  rw [e]
  infer_instance

theorem isIso_of_mono : ∀ (S : Scheme.{0}) (B B' : Over S) [GrpObj B] [GrpObj B'], IsAbelianScheme B → IsAbelianScheme B' → ∀ g : ℕ, SmoothOfRelativeDimension g B.hom → SmoothOfRelativeDimension g B'.hom → ∀ x : B ⟶ B', IsMonHom x → Mono x → IsIso x := by
  intro S B B' _ _ hB hB' g hg hg' x _ _
  have := hB.proper
  have := hB'.proper
  have := hB'.geomConnected
  have : Mono x.left := inferInstanceAs (Mono ((Over.forget S).map x))
  have : IsProper (x.left ≫ B'.hom) := by rw [Over.w]; infer_instance
  have : IsProper x.left := IsProper.of_comp x.left B'.hom
  have : IsClosedImmersion x.left := (IsClosedImmersion.iff_isProper_and_mono _).2 ⟨‹_›, ‹_›⟩
  have hs : Surjective B.hom := ⟨fun t => ⟨(η[B] : 𝟙_ (Over S) ⟶ B).left t, by
    rw [← Scheme.Hom.comp_apply, Over.w]; rfl⟩⟩
  have : Surjective (x.left ≫ B'.hom) := by rw [Over.w]; exact hs
  have : IsIso x.left :=
    isIso_of_isClosedImmersion B'.hom x.left hg' (by rw [Over.w]; exact hg) le_rfl
  have : IsIso ((Over.forget _).map x) := ‹_›
  exact isIso_of_reflects_iso x (Over.forget _)

end GlobalTheory.AbMonoIsoAny
end
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem integrableOn_poinVol {n : ℕ} (S : Finset (Fin n)) (K : Set (V n)) (hK : IsCompact K)
    (hS : ∀ v ∈ K, ∀ a ∈ S, ‖v a‖ ≤ 1 / 2) :
    IntegrableOn (fun v => ∏ a, (poinWt S v a)⁻¹ ^ 2) K := by
  classical
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  let g : Fin n → ℂ → ℝ := fun a =>
    if a ∈ S then (Metric.closedBall (0 : ℂ) (1 / 2)).indicator (fun z : ℂ => (‖z‖ * |Real.log ‖z‖|)⁻¹ ^ 2)
    else (Metric.closedBall (0 : ℂ) R).indicator (fun _ => 1)
  have hg : ∀ a, Integrable (g a) := by
    intro a
    by_cases h : a ∈ S
    · simp only [g, h, if_true]
      exact (integrable_indicator_iff measurableSet_closedBall).2 GlobalTheory.T.integrableOn_poincareAreaDensity_punctured_disc
    · simp only [g, h, if_false]
      exact (integrable_indicator_iff measurableSet_closedBall).2
        (continuousOn_const.integrableOn_compact (isCompact_closedBall _ _))
  have h1 : Integrable (fun x : Fin n → ℂ => ∏ a, g a (x a)) := Integrable.fintype_prod hg
  have h2 := (GlobalTheory.volume_preserving_ofLp_complex (Fin n)).integrable_comp_of_integrable h1
  refine (h2.integrableOn (s := K)).congr_fun ?_ hK.measurableSet
  intro v hv
  simp only [Function.comp]
  refine Finset.prod_congr rfl fun a _ => ?_
  by_cases h : a ∈ S
  · have : v.ofLp a ∈ Metric.closedBall (0 : ℂ) (1 / 2) := by
      simpa using hS v hv a h
    simp only [g, h, if_true, poinWt]
    exact Set.indicator_of_mem this _
  · have : v.ofLp a ∈ Metric.closedBall (0 : ℂ) R := by
      simpa using (PiLp.norm_apply_le v a).trans (hR v hv)
    simp only [g, h, if_false, poinWt, inv_one, one_pow]
    exact Set.indicator_of_mem this _

end GlobalTheory.GoodTop
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem liftHom_exists_of_noetherian : AbelianDeRham → (∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (hI : I ^ 2 = 0) (R₀ : Type) [CommRing R₀] (π : R →+* R₀),
    Function.Surjective π → RingHom.ker π = I → LiftObj (divided₂ hI) π ∧ LiftHom (divided₂ hI) π) →
  ∀ (R : Type) [CommRing R] (I : Ideal R) (h : I ^ 2 = 0) (R₀ : Type) [CommRing R₀] (π : R →+* R₀),
    Function.Surjective π → RingHom.ker π = I →
  ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A : Over (Sp R)) [GrpObj A] (i : A₀.left ⟶ A.left)
    (hA : IsGrpPullback A₀ A (spMap π) i), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
  ∀ (g' : ℕ) (B₀ : Over (Sp R₀)) [GrpObj B₀] (B : Over (Sp R)) [GrpObj B] (j : B₀.left ⟶ B.left)
    (hB : IsGrpPullback B₀ B (spMap π) j), IsAbelianScheme B → SmoothOfRelativeDimension g' B.hom →
  ∀ (f₀ : A₀ ⟶ B₀) [IsMonHom f₀], (∀ d ∈ liftFil (divided₂ h) hA, push (divided₂ h) (spMap π) f₀ d ∈ liftFil (divided₂ h) hB) →
    ∃ f : A ⟶ B, i ≫ f.left = f₀.left ≫ j := by
  intro P H R _ I h R₀ _ π hπ hker g A₀ _ A _ i hA abA smA g' B₀ _ B _ j hB abB smB f₀ _ hfil
  obtain ⟨S, ι₀, AS₀, _, AS, _, iS, BS₀, _, BS, _, jS, fS₀, φA, φB, ψA, ψB, hfg, hι, _, hAS, hBS, abAS, smAS,
    abBS, smBS, pA, pB, qA, qB, cA, cB, cf⟩ := GlobalTheory.T.abelian_hom_reduction_descends_finitely_generated R I R₀ π hπ hker g A₀ A i hA abA smA g' B₀ B j hB abB smB f₀
  have hS : (I.comap S.subtype) ^ 2 = 0 := by
    rw [Ideal.zero_eq_bot, eq_bot_iff]
    refine (Ideal.le_comap_pow _ 2).trans ?_
    rw [h, Ideal.zero_eq_bot, Ideal.comap_bot_of_injective _ Subtype.val_injective]
  haveI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing ℤ S
  have hfilS := GlobalTheory.T.push_mem_liftFil_of_injective_alt P R I h R₀ π hπ hker S S.subtype Subtype.val_injective (I.comap S.subtype) hS
    (S ⧸ I.comap S.subtype) (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective (Ideal.mk_ker) ι₀ hι
    g A₀ A i hA AS₀ AS iS hAS abA smA abAS smAS φA ψA pA qA cA
    g' B₀ B j hB BS₀ BS jS hBS abB smB abBS smBS φB ψB pB qB cB f₀ fS₀ cf hfil
  obtain ⟨fS, ⟨_, efS⟩, -⟩ := (H S (I.comap S.subtype) hS (S ⧸ I.comap S.subtype) (Ideal.Quotient.mk _)
    Ideal.Quotient.mk_surjective Ideal.mk_ker).2 g AS₀ AS iS hAS abAS smAS g' BS₀ BS jS hBS abBS smBS fS₀ hfilS
  let fl : A.left ⟶ B.left := pB.1.lift (φA ≫ fS.left) A.hom (by
    rw [Category.assoc, Over.w fS, pA.1.w])
  refine ⟨Over.homMk fl (pB.1.lift_snd _ _ _), ?_⟩
  apply pB.1.hom_ext
  · simp only [Over.homMk_left, Category.assoc, fl, pB.1.lift_fst]
    rw [reassoc_of% cA, efS, ← Category.assoc, ← cf, Category.assoc, cB]
  · simp only [Over.homMk_left, Category.assoc, fl, pB.1.lift_snd]
    rw [hA.1.w, hB.1.w, ← Category.assoc, Over.w f₀]

end GlobalTheory
end

section

open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

theorem _root_.GlobalTheory.T.contDiffOn_repr_pullbackComplexForm_fderiv : ∀ (m n : ℕ) (τ : V m → V n) (U : Set (V m)) (γ : Alt n), IsOpen U → DifferentiableOn ℂ τ U →
    ∀ S, ContDiffOn ℝ ∞ (fun x => (bas m).repr (pull (fderiv ℂ τ x) γ) S) U := by
  first | exact @GlobalTheory.PullSmooth.contDiffOn_repr_pull_fderiv | exact GlobalTheory.PullSmooth.contDiffOn_repr_pull_fderiv | (intros; apply GlobalTheory.PullSmooth.contDiffOn_repr_pull_fderiv <;> assumption)
end
