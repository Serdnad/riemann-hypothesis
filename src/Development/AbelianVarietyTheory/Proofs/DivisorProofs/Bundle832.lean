module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CyclotomicFrobeniusPowerSeriesXEqMulQuotient
public import Mathlib.Algebra.CharP.IntermediateField
public import Mathlib.RingTheory.PowerSeries.Exp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle279
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddXMulDerivativeBinomial
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianEndomorphismSpreadSpecialise
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle099
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle120
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle263
public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle511
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle126
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle148
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle802
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle694
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle771
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle266
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle803
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Abelian.Refinements
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

theorem _root_.GlobalTheory.T.fockAction_pow_analyticVector_norm_le : ∀ (p q r s : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : Pol p q r s →ₗ[ℂ] H), IsFockIP ι → ∀ (Y : Matrix (Ln p q r s) (Ln p q r s) ℂ) (d k : ℕ) (P : Pol p q r s), P.totalDegree ≤ d → ((omAct p q r s Y ^ k) P).totalDegree ≤ d + 2 * k ∧ ‖ι ((omAct p q r s Y ^ k) P)‖ ≤ (4 * ∑ l, ∑ l', ‖Y l l'‖) ^ k * (k.factorial : ℝ) * (2 : ℝ) ^ ((d : ℝ) / 2 + 1) * ‖ι P‖ := by
  first | exact @GlobalTheory.FockAnalytic.omAct_pow_norm_le | exact GlobalTheory.FockAnalytic.omAct_pow_norm_le | (intros; apply GlobalTheory.FockAnalytic.omAct_pow_norm_le <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc IsLocalRing

namespace GlobalTheory.WachExp

open PowerSeries

theorem ringHom_gam_X {l : ℕ} [Fact l.Prime] {O L : Type} [CommRing O] [Field L] [CharZero L] [Algebra ℚ L]
    [Algebra ℤ_[l] O] [Algebra ℤ_[l] L] [Algebra O L] [IsScalarTower ℤ_[l] O L] (φ : O⟦X⟧ →+* L⟦X⟧)
    (hφ : ∀ a : O, φ (C a) = C (algebraMap O L a)) (z : L) (hX : φ X = C z * exp L - 1) (hz : z ^ l = 1)
    (c : ℤ_[l]) (hc : (l : ℤ_[l]) ∣ c - 1) :
    φ (GlobalTheory.Fon.gam O c X) = C z * rescale (algebraMap ℤ_[l] L c) (exp L) - 1 := by
  let f : O⟦X⟧ →ₐ[O] L⟦X⟧ :=
    { toRingHom := φ
      commutes' := fun a => (congrArg φ (PowerSeries.algebraMap_apply (R := O) (A := O))).trans
        ((hφ a).trans (PowerSeries.algebraMap_apply (R := O) (A := L)).symm) }
  have h := GlobalTheory.HWL.Ser.map_gam_X f z hX 1 1 (by rw [pow_one]; exact hz) c (by simpa using hc)
  rw [pow_one] at h
  exact h

end GlobalTheory.WachExp

namespace GlobalTheory.WachExp

open PowerSeries

variable {l : ℕ} [Fact l.Prime] (LL : FinExt l)

theorem norm_root_sub_one_lt {z : ↥LL.1} (hz : z ^ l = 1) : ‖(((z - 1 : ↥LL.1)) : Om l)‖ < 1 := by
  have h : ((z : Om l)) ^ l ^ 1 = 1 := by
    rw [pow_one]; exact_mod_cast congrArg (fun y : ↥LL.1 => (y : Om l)) hz
  have := GlobalTheory.HWL.Ser.norm_sub_one_lt h
  push_cast
  exact this

theorem constantCoeff_exp_sub (z a : ↥LL.1) :
    constantCoeff (C z * rescale a (exp ↥LL.1) - 1) = z - 1 := by
  rw [map_sub, map_mul, GlobalTheory.HWL.Ser.constantCoeff_rescale_exp, constantCoeff_C, mul_one, map_one]

theorem ev_unique (x : PowerSeries ↥LL.1) (hx : ‖((constantCoeff x : ↥LL.1) : Om l)‖ < 1)
    (φ ψ : PowerSeries ↥(OL LL) →+* PowerSeries ↥LL.1)
    (hφ : ∀ a : ↥(OL LL), φ (C a) = C (a : ↥LL.1)) (hψ : ∀ a : ↥(OL LL), ψ (C a) = C (a : ↥LL.1))
    (hφX : φ X = x) (hψX : ψ X = x) : φ = ψ := by
  let φ' : PowerSeries ↥(OL LL) →ₐ[↥(OL LL)] PowerSeries ↥LL.1 :=
    { toRingHom := φ, commutes' := fun a => by change φ (C a) = C (a : ↥LL.1); exact hφ a }
  let ψ' : PowerSeries ↥(OL LL) →ₐ[↥(OL LL)] PowerSeries ↥LL.1 :=
    { toRingHom := ψ, commutes' := fun a => by change ψ (C a) = C (a : ↥LL.1); exact hψ a }
  have h := (GlobalTheory.HWL.SeriesEval.existsUnique_ev l LL x hx).1.unique (y₁ := φ') (y₂ := ψ') hφX hψX
  exact RingHom.ext fun f => AlgHom.congr_fun h f

theorem exists_ev (z : ↥LL.1) (hz : z ^ l = 1) :
    ∃ φ : PowerSeries ↥(OL LL) →+* PowerSeries ↥LL.1,
      (∀ a : ↥(OL LL), φ (C a) = C (a : ↥LL.1)) ∧ φ X = C z * exp ↥LL.1 - 1 := by
  have h := GlobalTheory.HWL.SeriesEval.existsUnique_ev l LL (C z * rescale 1 (exp ↥LL.1) - 1)
    (by rw [constantCoeff_exp_sub]; exact norm_root_sub_one_lt LL hz)
  obtain ⟨ev, hev, -⟩ := h.1
  refine ⟨ev.toRingHom, fun a => ?_, by
    change ev X = _
    rw [hev, rescale_one, RingHom.id_apply]⟩
  have := ev.commutes a
  exact this

theorem rescale_C' (r z : ↥LL.1) : rescale r (C z) = C z := by
  ext n
  by_cases h : n = 0 <;> simp [coeff_rescale, coeff_C, h]

end GlobalTheory.WachExp

namespace GlobalTheory.WachExp

open PowerSeries

end GlobalTheory.WachExp
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_abelian_endomorphism_spread_specialise : ∀ (k₀ K : Type) [Field k₀] [IsAlgClosed k₀] [Field K] [Algebra k₀ K] (B : Over (Sp k₀)) [GrpObj B], IsAbelianScheme B → ∀ f : (Over.pullback (spMap (algebraMap k₀ K))).obj B ⟶ (Over.pullback (spMap (algebraMap k₀ K))).obj B, IsMonHom f → ∃ (R : Subalgebra k₀ K) (g : R →ₐ[k₀] k₀) (Ψ : (Over.pullback (spMap (algebraMap k₀ R))).obj B ⟶ (Over.pullback (spMap (algebraMap k₀ R))).obj B) (f₀ : B ⟶ B) (σ : B.left ⟶ pullback B.hom (spMap (algebraMap k₀ R))), IsMonHom Ψ ∧ IsMonHom f₀ ∧ GlobalTheory.Spread.bcMap B.hom R.val ≫ Ψ.left ≫ pullback.fst _ _ = f.left ≫ pullback.fst _ _ ∧ σ ≫ pullback.fst _ _ = 𝟙 _ ∧ σ ≫ pullback.snd _ _ = B.hom ≫ spMap g.toRingHom ∧ f₀.left = σ ≫ Ψ.left ≫ pullback.fst _ _ := by
  first | exact @GlobalTheory.Spread.exists_endo_spread_specialise | exact GlobalTheory.Spread.exists_endo_spread_specialise | (intros; apply GlobalTheory.Spread.exists_endo_spread_specialise <;> assumption)
end

section

open NumberField MeasureTheory GlobalTheory.CuspRep

theorem _root_.GlobalTheory.T.levi_restriction_vanishing_preserved_by_operator : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ) (hr : r ≤ a) (f : Sm E a), (∀ (m₁ : GA E r) (m₂ : GA E (a - r)), f.1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂)) = 0) → ∀ (τ : E →+* ℂ) (i j : Fin a), ((i : ℕ) < r ↔ (j : ℕ) < r) → ∀ (m₁ : GA E r) (m₂ : GA E (a - r)), (Eop τ i j f).1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂)) = 0 := by
  first | exact @GlobalTheory.LeviDeriv.Eop_blkGL_eq_zero | exact GlobalTheory.LeviDeriv.Eop_blkGL_eq_zero | (intros; apply GlobalTheory.LeviDeriv.Eop_blkGL_eq_zero <;> assumption)
end

section

open NumberField MeasureTheory GlobalTheory.CuspRep

theorem _root_.GlobalTheory.T.leviSlice_smooth_and_matrixUnit_action : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ) (hr : r ≤ a) (m₁ : GA E r) (f : Sm E a), (fun m₂ : GA E (a - r) => f.1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂))) ∈ Sm E (a - r) ∧ ∀ (τ : E →+* ℂ) (p p' : Fin (a - r)) (ψ : Sm E (a - r)), ψ.1 = (fun m₂ : GA E (a - r) => f.1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂))) → (Eop τ p p' ψ).1 = fun m₂ : GA E (a - r) => (Eop τ (GlobalTheory.LeviGA.blkEquiv hr (Sum.inr p)) (GlobalTheory.LeviGA.blkEquiv hr (Sum.inr p')) f).1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂)) := by
  first | exact @GlobalTheory.LeviSliceGA.slice_smooth_Eop | exact GlobalTheory.LeviSliceGA.slice_smooth_Eop | (intros; apply GlobalTheory.LeviSliceGA.slice_smooth_Eop <;> assumption)
end

section

open NumberField MeasureTheory GlobalTheory.CuspRep

theorem _root_.GlobalTheory.T.matrixUnitOp_upperBlock_levi_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ) (hr : r ≤ a) (f : Sm E a), (∀ (x : BlockIx a r → Ad E) (g : GA E a), f.1 (unip x * g) = f.1 g) → ∀ (τ : E →+* ℂ) (i j : Fin a), (i : ℕ) < r → r ≤ (j : ℕ) → ∀ (m₁ : GA E r) (m₂ : GA E (a - r)), (Eop τ i j f).1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂)) = 0 := by
  first | exact @GlobalTheory.LeviGA.Eop_upper_blkGL_eq_zero | exact GlobalTheory.LeviGA.Eop_upper_blkGL_eq_zero | (intros; apply GlobalTheory.LeviGA.Eop_upper_blkGL_eq_zero <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.ExcisionQis

theorem map_descShortComplex {C : Type*} [Category C] [Abelian C] {K₁ K₂ L₁ L₂ M : CochainComplex C ℤ}
    (f' : K₁ ⟶ K₂) (g' : K₂ ⟶ M) (w' : f' ≫ g' = 0) (f : L₁ ⟶ L₂) (g : L₂ ⟶ M) (w : f ≫ g = 0)
    (a : K₁ ⟶ L₁) (b : K₂ ⟶ L₂) (comm : f' ≫ b = a ≫ f) (hg : g' = b ≫ g) :
    mappingCone.map f' f a b comm ≫ mappingCone.descShortComplex (ShortComplex.mk f g w) =
      mappingCone.descShortComplex (ShortComplex.mk f' g' w') := by
  ext n : 1
  apply mappingCone.ext_from _ (n + 1) n rfl
  · simp [mappingCone.map, mappingCone.descShortComplex, HomComplex.Cochain.zero_cochain_comp_v]
  · simp [mappingCone.map, mappingCone.descShortComplex, hg]

theorem cone_single_qis {C : Type*} [Category C] [Abelian C] {F1 F2 F3 F4 : C} (u' : F1 ⟶ F2) (u : F3 ⟶ F4)
    (a : F1 ⟶ F3) (b : F2 ⟶ F4) (comm : u' ≫ b = a ≫ u) [Mono u] (w : biprod.lift a (-u') ≫ biprod.desc u b = 0)
    (hS : (ShortComplex.mk _ _ w).ShortExact) :
    QuasiIso (mappingCone.map ((singleFunctor C 0).map u') ((singleFunctor C 0).map u) ((singleFunctor C 0).map a)
      ((singleFunctor C 0).map b) (by rw [← Functor.map_comp, ← Functor.map_comp, comm])) := by
  haveI : Mono (biprod.lift a (-u')) := hS.mono_f
  haveI : Epi (biprod.desc u b) := hS.epi_g
  let T : ShortComplex C := ShortComplex.mk u (cokernel.π u) (cokernel.condition u)
  have hT : T.ShortExact := ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel u))
    inferInstance inferInstance
  have w' : u' ≫ b ≫ cokernel.π u = 0 := by
    rw [← Category.assoc, comm, Category.assoc, cokernel.condition, Limits.comp_zero]
  let T' : ShortComplex C := ShortComplex.mk u' (b ≫ cokernel.π u) w'
  have hmono : Mono u' := by
    refine Preadditive.mono_of_cancel_zero _ fun {Q} g hg => ?_
    have hga : g ≫ a = 0 := by
      rw [← cancel_mono u, Category.assoc, ← comm, ← Category.assoc, hg, Limits.zero_comp, Limits.zero_comp]
    have : g ≫ biprod.lift a (-u') = 0 := by
      apply biprod.hom_ext <;> simp [hga, hg]
    rw [← cancel_mono (biprod.lift a (-u')), this, Limits.zero_comp]
  have hepi : Epi (b ≫ cokernel.π u) := by
    refine Preadditive.epi_of_cancel_zero _ fun {Q} h hh => ?_
    have h1 : biprod.desc u b ≫ cokernel.π u ≫ h = 0 := by
      apply biprod.hom_ext'
      · simp
      · simpa using hh
    have h2 : cokernel.π u ≫ h = 0 := by
      rw [← cancel_epi (biprod.desc u b), h1, Limits.comp_zero]
    rw [← cancel_epi (cokernel.π u), h2, Limits.comp_zero]
  have hexact : T'.Exact := by
    rw [ShortComplex.exact_iff_exact_up_to_refinements]
    intro A₀ y hy
    have hy' : (y ≫ b) ≫ T.g = 0 := by simpa using hy
    obtain ⟨A₁, e₁, he₁, z, hz⟩ := (ShortComplex.exact_iff_exact_up_to_refinements T).1 hT.exact (y ≫ b) hy'
    have hw : biprod.lift (-z) (e₁ ≫ y) ≫ (ShortComplex.mk _ _ w).g = 0 := by
      change biprod.lift (-z) (e₁ ≫ y) ≫ biprod.desc u b = 0
      rw [biprod.lift_desc, Preadditive.neg_comp, Category.assoc, hz]
      exact neg_add_cancel _
    obtain ⟨A₂, e₂, he₂, x, hx⟩ := (ShortComplex.exact_iff_exact_up_to_refinements _).1 hS.exact _ hw
    refine ⟨A₂, e₂ ≫ e₁, inferInstance, -x, ?_⟩
    have h2 := congrArg (· ≫ biprod.snd) hx
    simp only [Category.assoc] at h2
    rw [biprod.lift_snd, biprod.lift_snd] at h2
    show (e₂ ≫ e₁) ≫ y = (-x) ≫ u'
    rw [Category.assoc, h2, Preadditive.neg_comp, Preadditive.comp_neg]
  have hT' : T'.ShortExact := ShortComplex.ShortExact.mk' hexact hmono hepi
  have z1 : (singleFunctor C 0).map u ≫ (singleFunctor C 0).map (cokernel.π u) = 0 := by
    rw [← Functor.map_comp, cokernel.condition, Functor.map_zero]
  have z2 : (singleFunctor C 0).map u' ≫ (singleFunctor C 0).map (b ≫ cokernel.π u) = 0 := by
    rw [← Functor.map_comp, w', Functor.map_zero]
  have c2 : (singleFunctor C 0).map u' ≫ (singleFunctor C 0).map b = (singleFunctor C 0).map a ≫ (singleFunctor C 0).map u := by
    rw [← Functor.map_comp, ← Functor.map_comp, comm]
  have hST : (ShortComplex.mk _ _ z1).ShortExact := hT.map_of_exact (HomologicalComplex.single C (ComplexShape.up ℤ) 0)
  have hST' : (ShortComplex.mk _ _ z2).ShortExact := hT'.map_of_exact (HomologicalComplex.single C (ComplexShape.up ℤ) 0)
  haveI := mappingCone.quasiIso_descShortComplex hST
  haveI := mappingCone.quasiIso_descShortComplex hST'
  have key := map_descShortComplex _ _ z2 _ _ z1 ((singleFunctor C 0).map a) ((singleFunctor C 0).map b) c2
    (Functor.map_comp _ _ _)
  haveI : QuasiIso (mappingCone.map _ _ _ _ c2 ≫ mappingCone.descShortComplex (ShortComplex.mk _ _ z1)) := by
    rw [key]; exact mappingCone.quasiIso_descShortComplex hST'
  exact quasiIso_of_comp_right _ (mappingCone.descShortComplex (ShortComplex.mk _ _ z1))

theorem mono_free_away (R : Type) [CommRing R] (A : Type) [CommRing A] (f : A) :
    Mono ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f)))))) := by
  haveI : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f)))) :=
    IsOpenImmersion.of_isLocalization f
  have h1 : Mono (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f))))) := inferInstance
  have h2 : Mono ((freeP R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f)))))) := by
    have happ : ∀ U, Mono (((freeP R).map (yoneda.map (Spec.map (CommRingCat.ofHom
        (algebraMap A (Localization.Away f)))))).app U) := fun U => by
      have hinj : Function.Injective
          ((yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f))))).app U) :=
        (mono_iff_injective _).1 inferInstance
      rw [ModuleCat.mono_iff_injective]
      change Function.Injective (Finsupp.mapDomain _)
      exact Finsupp.mapDomain_injective (fun x y hxy => ULift.ext (hinj (congrArg ULift.down hxy)))
    exact NatTrans.mono_of_mono_app _
  change Mono ((presheafToSheaf _ _).map ((freeP R).map _))
  infer_instance

theorem quasiIso_map_of_corners {C : Type*} [Category C] [Abelian C] {K₁ K₂ K₃ K₄ L₁ L₂ L₃ L₄ : CochainComplex C ℤ}
    (φ' : K₁ ⟶ K₂) (φ : K₃ ⟶ K₄) (α : K₁ ⟶ K₃) (β : K₂ ⟶ K₄) (c₀ : φ' ≫ β = α ≫ φ)
    (ψ' : L₁ ⟶ L₂) (ψ : L₃ ⟶ L₄) (α' : L₁ ⟶ L₃) (β' : L₂ ⟶ L₄) (c₁ : ψ' ≫ β' = α' ≫ ψ)
    (e₁ : K₁ ⟶ L₁) (e₂ : K₂ ⟶ L₂) (e₃ : K₃ ⟶ L₃) (e₄ : K₄ ⟶ L₄) (q₁ : QuasiIso e₁) (q₂ : QuasiIso e₂)
    (q₃ : QuasiIso e₃) (q₄ : QuasiIso e₄) (h₁₂ : φ' ≫ e₂ = e₁ ≫ ψ') (h₃₄ : φ ≫ e₄ = e₃ ≫ ψ) (h₁₃ : α ≫ e₃ = e₁ ≫ α')
    (h₂₄ : β ≫ e₄ = e₂ ≫ β') [QuasiIso (mappingCone.map φ' φ α β c₀)] :
    QuasiIso (mappingCone.map ψ' ψ α' β' c₁) := by
  haveI := q₁; haveI := q₂; haveI := q₃; haveI := q₄
  have key : mappingCone.map φ' ψ' e₁ e₂ h₁₂ ≫ mappingCone.map ψ' ψ α' β' c₁ =
      mappingCone.map φ' φ α β c₀ ≫ mappingCone.map φ ψ e₃ e₄ h₃₄ := by
    rw [← mappingCone.map_comp, ← mappingCone.map_comp]
    congr 1
    · exact h₁₃.symm
    · exact h₂₄.symm
  haveI := GlobalTheory.EtC.ConeRes.quasiIso_mappingCone_map φ' ψ' e₁ e₂ h₁₂
  haveI := GlobalTheory.EtC.ConeRes.quasiIso_mappingCone_map φ ψ e₃ e₄ h₃₄
  haveI : QuasiIso (mappingCone.map φ' ψ' e₁ e₂ h₁₂ ≫ mappingCone.map ψ' ψ α' β' c₁) := by
    rw [key]; infer_instance
  exact quasiIso_of_comp_left (mappingCone.map φ' ψ' e₁ e₂ h₁₂) _

private theorem biprod_lift_neg_desc_eq_zero {C : Type*} [Category C] [Abelian C]
    {X₁ X₂ X₃ X₄ : C} {u' : X₁ ⟶ X₂} {u : X₃ ⟶ X₄} {a : X₁ ⟶ X₃} {b : X₂ ⟶ X₄}
    (comm : u' ≫ b = a ≫ u) : biprod.lift a (-u') ≫ biprod.desc u b = 0 := by
  rw [biprod.lift_desc, Preadditive.neg_comp, ← comm, add_neg_cancel]

private theorem cone_qis_of_natural_homotopyEquiv {P C : Type*} [Category P] [Category C] [Abelian C]
    (F : P ⥤ C) (G : P ⥤ CochainComplex C ℤ) {X₁ X₂ X₃ X₄ : P}
    (u' : X₁ ⟶ X₂) (u : X₃ ⟶ X₄) (a : X₁ ⟶ X₃) (b : X₂ ⟶ X₄)
    (sq : CommSq u' a b u) [Mono (F.map u)]
    (hS : ∀ w : biprod.lift (F.map a) (-F.map u') ≫ biprod.desc (F.map u) (F.map b) = 0,
      (ShortComplex.mk _ _ w).ShortExact)
    (e : ∀ X, HomotopyEquiv ((singleFunctor C 0).obj (F.obj X)) (G.obj X))
    (he : ∀ {X Y : P} (g : X ⟶ Y),
      (e X).hom ≫ G.map g = (singleFunctor C 0).map (F.map g) ≫ (e Y).hom) :
    QuasiIso (mappingCone.map (G.map u') (G.map u) (G.map a) (G.map b) (G.map_commSq sq).w) := by
  let S := F ⋙ singleFunctor C 0
  have commS := (S.map_commSq sq).w
  have commF := (F.map_commSq sq).w
  have w := biprod_lift_neg_desc_eq_zero commF
  have : QuasiIso (mappingCone.map (S.map u') (S.map u) (S.map a) (S.map b) commS) :=
    cone_single_qis (F.map u') (F.map u) (F.map a) (F.map b) commF w (hS w)
  exact quasiIso_map_of_corners (S.map u') (S.map u) (S.map a) (S.map b) commS
    (G.map u') (G.map u) (G.map a) (G.map b) (G.map_commSq sq).w
    (e X₁).hom (e X₂).hom (e X₃).hom (e X₄).hom
    (e X₁).quasiIso_hom (e X₂).quasiIso_hom (e X₃).quasiIso_hom (e X₄).quasiIso_hom
    (he u').symm (he u).symm (he a).symm (he b).symm

theorem _root_.GlobalTheory.EtC.excisionConeMap_quasiIso : ∀ (R : Type) [CommRing R] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A), IsExcisionNbhd A A' f → QuasiIso (excisionConeMap R A A' f) := by
  intro R _ A A' _ _ _ f h
  obtain ⟨e, -, he⟩ := chains_disc_homotopyEquiv R
  have : Algebra.Etale A A' := h.1
  let u' := (CommRingCat.ofHom (algebraMap A' (Localization.Away (algebraMap A A' f)))).op
  let u := (CommRingCat.ofHom (algebraMap A (Localization.Away f))).op
  let a := (CommRingCat.ofHom (Localization.awayMap (algebraMap A A') f)).op
  let b := (CommRingCat.ofHom (algebraMap A A')).op
  have sq : CommSq u' a b u := ⟨
    congrArg (fun g => (CommRingCat.ofHom g).op) (awayMap_comp_algebraMap (algebraMap A A') f).symm⟩
  let Y : CommRingCat.{0}ᵒᵖ ⥤ PSh := Scheme.Spec ⋙ yoneda
  let F := Y ⋙ free R
  have hS := GlobalTheory.T.freeEtaleSheaf_excision_shortExact R A A' f ⟨h.2.1, h.2.2⟩
  have : Mono (F.map u) := mono_free_away R A f
  exact cone_qis_of_natural_homotopyEquiv F (Y ⋙ disc ⋙ chains R) u' u a b sq
    hS (fun X => e (Y.obj X)) (fun g => he (Y.map g))

end GlobalTheory.EtC.ExcisionQis

end
end

section

open IsLocalRing Polynomial

noncomputable section

namespace GlobalTheory.GoodStageOrigin

theorem local_props (A' : Type) [CommRing A'] [IsDomain A'] [IsNoetherianRing A'] [IsIntegrallyClosed A']
    (E : Type) [CommRing E] [Algebra (Polynomial A') E] [Algebra.Etale (Polynomial A') E]
    (Q : Ideal E) [Q.IsPrime] :
    IsDomain (Localization.AtPrime Q) ∧ IsNoetherianRing (Localization.AtPrime Q) ∧
      IsIntegrallyClosed (Localization.AtPrime Q) ∧
      (letI : Algebra A' (Localization.AtPrime Q) :=
        ((algebraMap (Polynomial A') (Localization.AtPrime Q)).comp Polynomial.C).toAlgebra
       Module.Flat A' (Localization.AtPrime Q)) := by
  haveI : IsIntegrallyClosed (Polynomial A') := by
    haveI := GlobalTheory.isIntegrallyClosed_mvPolynomial_fin A' 1
    exact IsIntegrallyClosed.of_equiv
      (MvPolynomial.uniqueAlgEquiv A' (Fin 1)).toRingEquiv
  obtain ⟨h1, h2⟩ := GlobalTheory.etale_localization_atPrime_isDomain_isIntegrallyClosed (Polynomial A') E Q
  haveI : IsNoetherianRing E := Algebra.FiniteType.isNoetherianRing (Polynomial A') E
  refine ⟨h1, IsLocalization.isNoetherianRing Q.primeCompl _ inferInstance, h2, ?_⟩
  letI : Algebra A' (Localization.AtPrime Q) :=
    ((algebraMap (Polynomial A') (Localization.AtPrime Q)).comp Polynomial.C).toAlgebra
  haveI : IsScalarTower A' (Polynomial A') (Localization.AtPrime Q) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Module.Flat (Polynomial A') E := inferInstance
  haveI : Module.Flat E (Localization.AtPrime Q) := IsLocalization.flat _ Q.primeCompl
  haveI : Module.Flat (Polynomial A') (Localization.AtPrime Q) := Module.Flat.trans (Polynomial A') E _
  exact Module.Flat.trans A' (Polynomial A') _

theorem good_stage : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T), Function.Injective i → IsLocalHom i →
    ∀ (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime],
      QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ (jA : Localization.AtPrime QA →+* O),
      jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
        (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) →
    ∀ (sA : A), sA ≠ 0 →
    ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : IsNoetherianRing A') (_ : IsIntegrallyClosed A')
      (B' : Type) (_ : CommRing B') (_ : IsDomain B') (_ : IsLocalRing B') (_ : IsNoetherianRing B')
      (_ : IsIntegrallyClosed B') (_ : Algebra A' B') (_ : Module.Flat A' B')
      (ι : A →+* A') (α : A' →+* T) (β : Localization.AtPrime QA →+* B') (γ : B' →+* O),
      (algebraMap A' B').comp ι = β.comp (algebraMap A (Localization.AtPrime QA)) ∧
      γ.comp β = jA ∧ γ.comp (algebraMap A' B') = (algebraMap T O).comp α ∧ ι sA ≠ 0 ∧
      ∀ 𝔭 : Ideal A', 𝔭.IsPrime → 𝔭.height = 1 → ι sA ∈ 𝔭 →
        (𝔭.map (algebraMap A' B')).IsPrime := by
  intro T O _ _ _ _ _ _ _ _ hT P _ φ hφ hsh hP A _ _ _ _ _ _ i hi hil EA _ _ _ _ _ QA _ hQA jA hjA sA hsA
  have hO : (maximalIdeal O).comap (algebraMap (Polynomial T) O) = GlobalTheory.KeyOriginCut.originIdeal T := by
    haveI : IsLocalHom φ := hsh.2.2.1
    rw [← hφ, ← Ideal.comap_comap, GlobalTheory.comap_maximalIdeal_of_localHom_strictHens φ, ← hP]
    first
      | exact Localization.AtPrime.under_maximalIdeal (Localization.AtPrime P) P
      | exact Localization.AtPrime.under_maximalIdeal
      | simpa [Ideal.under] using Localization.AtPrime.under_maximalIdeal (Localization.AtPrime P) P
  obtain ⟨A', _, _, _, _, _, _, ι, α, hια, hα⟩ := GlobalTheory.T.exists_local_hom_to_strictly_henselian_normal T hT A i hil
  obtain ⟨E', _, _, _, Q', _, hQ', β, γ, h1, h2, h3⟩ :=
    GlobalTheory.T.exists_localStage_tensor_polynomial_origin T O hO A i hil EA QA hQA jA hjA A' ι α hια hα
  obtain ⟨hd, hn, hic, hfl⟩ := local_props A' E' Q'
  letI alg : Algebra A' (Localization.AtPrime Q') :=
    ((algebraMap (Polynomial A') (Localization.AtPrime Q')).comp Polynomial.C).toAlgebra
  refine ⟨A', inferInstance, inferInstance, inferInstance, inferInstance, Localization.AtPrime Q',
    inferInstance, hd, inferInstance, hn, hic, alg, hfl, ι, α, β, γ, ?_, h2, h3, ?_, ?_⟩
  · have e : algebraMap A (Localization.AtPrime QA) =
        (algebraMap (Polynomial A) (Localization.AtPrime QA)).comp Polynomial.C := by
      rw [IsScalarTower.algebraMap_eq A EA (Localization.AtPrime QA),
        IsScalarTower.algebraMap_eq A (Polynomial A) EA, Polynomial.algebraMap_eq,
        IsScalarTower.algebraMap_eq (Polynomial A) EA (Localization.AtPrime QA)]
      rfl
    rw [e]
    exact h1
  · intro h
    apply hsA
    apply hi
    rw [map_zero, ← hια, RingHom.comp_apply, h, map_zero]
  · intro 𝔭 _ _ _
    exact GlobalTheory.T.origin_ideal_extension_prime A' 𝔭 E' Q' hQ'

end GlobalTheory.GoodStageOrigin
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDiv

theorem frobKerIdeal_le_kerIdeal_relFrob (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    (h : (p : R) = 0) (G : PDivGroup p R) (n : ℕ) :
    frobKerIdeal p R (G.A n) ≤ kerIdeal ((relFrob h G).app n) := by
  refine Ideal.span_le.2 ?_
  rintro _ ⟨a, ha, rfl⟩
  have ha' : counit (R := R) a = 0 := ha
  have hb : (frobProj h G).app n a ∈ augIdeal R ((frobTwist h G).A n) := by
    change counit (R := R) ((frobProj h G).app n a) = 0
    exact (SemiBialgHom.counit_map ((frobProj h G).app n) a).trans
      ((congrArg (frobRing h) ha').trans (map_zero (frobRing h)))
  change a ^ p ∈ kerIdeal ((relFrob h G).app n)
  rw [← relFrob_app_frobProj h n a]
  exact Ideal.mem_map_of_mem ((relFrob h G).app n).toAlgHom hb

theorem frobKerIdeal_eq_kerIdeal_relFrob (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    (h : (p : R) = 0) (G : PDivGroup p R) (n : ℕ) :
    frobKerIdeal p R (G.A n) = kerIdeal ((relFrob h G).app n) :=
  le_antisymm (frobKerIdeal_le_kerIdeal_relFrob p R h G n)
    (kerIdeal_relFrob_le_frobKerIdeal p R h G n)

end GlobalTheory.PDiv
end
end

section

open GlobalTheory GlobalTheory.PDiv

theorem _root_.GlobalTheory.T.relativeFrobeniusKernelIdeal_le_frobeniusKernelIdeal
    (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (h : (p : R) = 0)
    (G : PDivGroup p R) (n : ℕ) :
    kerIdeal ((PDivGroup.relFrob h G).app n) ≤ frobKerIdeal p R (G.A n) :=
  kerIdeal_relFrob_le_frobKerIdeal p R h G n
end
