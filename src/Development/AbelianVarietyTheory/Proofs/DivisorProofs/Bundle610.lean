module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotIsUnitCoeffOfCoboundarySmall
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle564
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle511
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle548
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle558
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle584
public import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Smooth.StandardSmooth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle560
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle562
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.coeff_sumElim_powerSeriesSwapVariableGroups : ∀ (R : Type) [CommRing R] (d : ℕ) (c : MvPowerSeries (Fin d ⊕ Fin d) R) (a e : Fin d →₀ ℕ), coeff (Finsupp.sumElim a e) (swap c) = coeff (Finsupp.sumElim e a) c := by
  first | exact @GlobalTheory.SwapCoeff.coeff_swap | exact GlobalTheory.SwapCoeff.coeff_swap | (intros; apply GlobalTheory.SwapCoeff.coeff_swap <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.formalGroupLawCoboundary_swap_sub_rules : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) → ∀ (c c' : MvPowerSeries (Fin d ⊕ Fin d) R) (f f' : MvPowerSeries (Fin d) R), cob2 μ (c - c') = cob2 μ c - cob2 μ c' ∧ swap (c - c') = swap c - swap c' ∧ cob1 μ (f - f') = cob1 μ f - cob1 μ f' := by
  first | exact @GlobalTheory.CobLin.sub_rules | exact GlobalTheory.CobLin.sub_rules | (intros; apply GlobalTheory.CobLin.sub_rules <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.not_isUnit_coeff_of_coboundary_small' : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), IsLaw μ → ∀ t : MvPowerSeries (Fin d) O, (∀ i, ¬IsUnit (lin t i)) → (∀ α : Fin d ⊕ Fin d →₀ ℕ, (∃ i, ¬ p ∣ α i) → ¬IsUnit (coeff α (cob1 μ t))) → ∀ α : Fin d →₀ ℕ, (∃ i, ¬ p ∣ α i) → ¬IsUnit (coeff α t) := by
  first | exact @GlobalTheory.Katz.not_isUnit_coeff_of_coboundary_small | exact GlobalTheory.Katz.not_isUnit_coeff_of_coboundary_small | (intros; apply GlobalTheory.Katz.not_isUnit_coeff_of_coboundary_small <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

theorem _root_.GlobalTheory.T.etaleMayerVietoris_free_right_epi : ∀ (R : Type) [CommRing R] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] [Algebra.Etale A A'] (f : A), (∀ a' : A', ∃ a : A, a' - algebraMap A A' a ∈ Ideal.span {algebraMap A A' f}) → (∀ a : A, algebraMap A A' a ∈ Ideal.span {algebraMap A A' f} → a ∈ Ideal.span {f}) → Epi (biprod.desc ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f)))))) ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A A')))))) := by
  first | (exact @GlobalTheory.EtC.MVEpi.mv_right_epi) | (exact GlobalTheory.EtC.MVEpi.mv_right_epi) | (intros; apply GlobalTheory.EtC.MVEpi.mv_right_epi <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.DiscElt

variable (R : Type) [CommRing R]

theorem hkpull_comp {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (F : Shv R) (n : ℤ) (x : HK R M F n) :
    HK.pull R (f ≫ g) F n x = HK.pull R f F n (HK.pull R g F n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_comp]

theorem hkpull_single {X Y : Shv R} (g : X ⟶ Y) (F : Shv R) (n : ℤ) (t : Y ⟶ (res R F).X n)
    (ht : t ≫ (res R F).d n (n + 1) = 0) :
    HK.pull R ((CochainComplex.singleFunctor (Shv R) 0).map g) F n
      (CohomologyClass.mk (Cocycle.fromSingleMk t (zero_add n) (n + 1) rfl ht)) =
      CohomologyClass.mk (Cocycle.fromSingleMk (g ≫ t) (zero_add n) (n + 1) rfl (by simp [ht])) := by
  rw [Cocycle.fromSingleMk_precomp g t (zero_add n) (n + 1) rfl ht]
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cocycle.precomp]

end GlobalTheory.EtC.DiscElt

namespace GlobalTheory.EtC


open GlobalTheory.EtC.DiscElt in
theorem disc_elt_cls : ∀ (R : Type) [CommRing R] (F : Shv R), ∃ cl : ∀ (P : PSh) (n : ℤ) (t : (free R).obj P ⟶ (res R F).X n), t ≫ (res R F).d n (n + 1) = 0 → H R (disc.obj P) F n, (∀ P n x, ∃ t ht, cl P n t ht = x) ∧ (∀ P n t ht t' ht', cl P n t ht = cl P n t' ht' ↔ ∃ y : (free R).obj P ⟶ (res R F).X (n - 1), t = t' + y ≫ (res R F).d (n - 1) n) ∧ (∀ P n, cl P n 0 zero_comp = 0) ∧ ∀ (P P' : PSh) (f : P ⟶ P') n t ht, ∃ h, pull R (disc.map f) F n (cl P' n t ht) = cl P n ((free R).map f ≫ t) h := by
  intro R _ F
  obtain ⟨e, -, hnat⟩ := chains_disc_homotopyEquiv R
  have hb : ∀ (P : PSh) (n : ℤ), Function.Bijective (HK.pull R (e P).hom F n) := fun P n => by
    haveI : QuasiIso (e P).hom := (e P).quasiIso_hom
    exact quasiIso_hypercohomology_bijective' R (e P).hom F n
  let E : ∀ (P : PSh) (n : ℤ), H R (disc.obj P) F n ≃ HK R (sgl ((free R).obj P)) F n :=
    fun P n => Equiv.ofBijective _ (hb P n)
  have hE : ∀ P n x, E P n x = HK.pull R (e P).hom F n x := fun _ _ _ => rfl
  let c : ∀ (P : PSh) (n : ℤ) (t : (free R).obj P ⟶ (res R F).X n), t ≫ (res R F).d n (n + 1) = 0 →
      HK R (sgl ((free R).obj P)) F n :=
    fun P n t ht => CohomologyClass.mk (Cocycle.fromSingleMk t (zero_add n) (n + 1) rfl ht)
  refine ⟨fun P n t ht => (E P n).symm (c P n t ht), ?_, ?_, ?_, ?_⟩
  · intro P n x
    obtain ⟨z, hz⟩ := (E P n x).mk_surjective
    obtain ⟨t, ht, rfl⟩ := Cocycle.fromSingleMk_surjective z n (zero_add n) (n + 1) rfl
    exact ⟨t, ht, by rw [Equiv.symm_apply_eq]; exact hz⟩
  · intro P n t ht t' ht'
    rw [(E P n).symm.injective.eq_iff]
    change CohomologyClass.mk _ = CohomologyClass.mk _ ↔ _
    rw [← sub_eq_zero, ← CohomologyClass.mk_sub, ← Cocycle.fromSingleMk_sub _ _ _ _ _ ht ht',
      CohomologyClass.mk_eq_zero_iff,
      Cocycle.fromSingleMk_mem_coboundaries_iff _ _ _ _ _ (n - 1) (by omega)]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, by rw [hy]; abel⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, by rw [hy]; abel⟩
  · intro P n
    change (E P n).symm (CohomologyClass.mk _) = 0
    rw [Equiv.symm_apply_eq, hE, map_zero, Cocycle.fromSingleMk_zero, CohomologyClass.mk_zero]
  · intro P P' f n t ht
    refine ⟨by simp [ht], ?_⟩
    rw [Equiv.eq_symm_apply, hE]
    change HK.pull R (e P).hom F n (HK.pull R ((chains R).map (disc.map f)) F n _) = _
    rw [← hkpull_comp, hnat f, hkpull_comp]
    have h1 : HK.pull R (e P').hom F n ((E P' n).symm (c P' n t ht)) = c P' n t ht := by
      rw [← hE, Equiv.apply_symm_apply]
    rw [h1]
    exact hkpull_single R ((free R).map f) F n t ht

end GlobalTheory.EtC
end
end

section

open MeasureTheory Matrix


theorem _root_.GlobalTheory.T.abs_weilCharacter_det_eq_abs_det_pow : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ} (ψ0 : AddChar k ℂ), Continuous ψ0 → ψ0 ≠ 1 →
    ∀ (ι : ((Fin n × Fin d → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ)),
    Set.BijOn ι (GlobalTheory.WeilM.SB (Fin n × Fin d → k) : Set _) (GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) : Set _) →
    ∀ (Tr : Matrix (Fin n) (Fin d) k → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ)
      (Mu : (Matrix (Fin n) (Fin d) k →ₗ[k] k) → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ),
    (∀ C, ∀ φ ∈ GlobalTheory.WeilM.SB _, Tr C φ ∈ GlobalTheory.WeilM.SB _ ∧ ι (Tr C φ) = fun Y => ι φ (Y + C)) →
    (∀ l, ∀ φ ∈ GlobalTheory.WeilM.SB _, Mu l φ ∈ GlobalTheory.WeilM.SB _ ∧ ι (Mu l φ) = fun Y => ψ0 (l Y) * ι φ Y) →
    (∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ C, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ' ∈ GlobalTheory.WeilM.SB _,
        ∫ y, Tr C φ y * (starRingEnd ℂ) (Tr C φ' y) ∂μ = ∫ y, φ y * (starRingEnd ℂ) (φ' y) ∂μ) →
    (∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ l, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ' ∈ GlobalTheory.WeilM.SB _,
        ∫ y, Mu l φ y * (starRingEnd ℂ) (Mu l φ' y) ∂μ = ∫ y, φ y * (starRingEnd ℂ) (φ' y) ∂μ) →
    ∀ (S : GL (Fin n) k → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ),
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, S g φ ∈ GlobalTheory.WeilM.SB _) →
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ μ : @Measure (Fin n × Fin d → k) (borel _),
      @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∫⁻ y, ‖S g φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ) →
    ∀ χ : kˣ →* ℂˣ, (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ι (S g φ) = fun Y => (χ (Matrix.GeneralLinearGroup.det g) : ℂ) * ι φ (g.valᵀ * Y)) →
    ∃ ν : kˣ →* ℂˣ, (∀ x, ‖(ν x : ℂ)‖ = 1) ∧ ∀ g : GL (Fin n) k,
      (χ (Matrix.GeneralLinearGroup.det g) : ℂ) = ν (Matrix.GeneralLinearGroup.det g) * GlobalTheory.SplitFlip.apow (Matrix.GeneralLinearGroup.det g) ((d : ℂ) / 2) := by
  first | exact @GlobalTheory.HeisUnit.exists_unitary_factor | exact GlobalTheory.HeisUnit.exists_unitary_factor | (intros; apply GlobalTheory.HeisUnit.exists_unitary_factor <;> assumption)
end

section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

theorem map_mul_left_eq_norm_smul (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (z : Eˣ) :
    μ.map (fun x => (z : E) * x) =
      (distribHaarChar F ((Units.map (Algebra.norm F : E →* F)) z))⁻¹ • μ := by
  obtain ⟨b, -, -⟩ := hE.basis
  have : FiniteDimensional F E := Module.Finite.of_basis b
  let T : E ≃ₗ[F] E :=
    { LinearMap.mulLeft F (z : E) with
      invFun := fun x => ((z⁻¹ : Eˣ) : E) * x
      left_inv := fun x => by simp
      right_inv := fun x => by simp }
  have hT : LinearEquiv.det T = Units.map (Algebra.norm F : E →* F) z := by
    ext
    rw [LinearEquiv.coe_det, Units.coe_map, Algebra.norm_apply]
    rfl
  rw [← hT]
  exact GlobalTheory.T.map_linearEquiv_addHaar_localField F E μ T

end GlobalTheory.KSp
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.standardSmooth_lift_over_sqZero_thickening : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (B₀ : Type) [CommRing B₀] [Algebra R₀ B₀], Algebra.IsStandardSmooth R₀ B₀ → ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B) (p : B →+* B₀), SemiHom π p ∧ Function.Surjective p ∧ (∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) ∧ Algebra.Smooth R B := by
  first | exact @GlobalTheory.Obs.standardSmooth_lift_of_sqZero | exact GlobalTheory.Obs.standardSmooth_lift_of_sqZero | (intros; apply GlobalTheory.Obs.standardSmooth_lift_of_sqZero <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
theorem _root_.GlobalTheory.T.isAW_existsUnique_biadditive_etale : ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k), (∀ (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m), ∃! γ, μ.IsAW hk α β γ) ∧ (∀ α α' β γ γ', μ.IsAW (E := E) hk α β γ → μ.IsAW hk α' β γ' → μ.IsAW hk (α + α') β (γ + γ')) ∧ (∀ α β β' γ γ', μ.IsAW (E := E) hk α β γ → μ.IsAW hk α β' γ' → μ.IsAW hk α (β + β') (γ + γ')) := by
  first | exact @GlobalTheory.EtC.isAW_existsUnique_biadditive | exact GlobalTheory.EtC.isAW_existsUnique_biadditive | (intros; apply GlobalTheory.EtC.isAW_existsUnique_biadditive <;> assumption)
end

section

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

theorem _root_.GlobalTheory.T.exists_dividedPowers_ext_isStd : ∀ (B : Type) [CommRing B] (J : Ideal B) (δ : DividedPowers J) (Q : PDPoly B), ∃ η : DividedPowers (Q.ext J), Q.IsStd δ η := by
  first | exact @GlobalTheory.PDA.PDPoly.exists_isStd | exact GlobalTheory.PDA.PDPoly.exists_isStd | (intros; apply GlobalTheory.PDA.PDPoly.exists_isStd <;> assumption)
end
