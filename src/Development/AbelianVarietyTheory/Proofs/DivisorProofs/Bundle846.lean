module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle815
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle002
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle032
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle005
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle816
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle817
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle818
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.RingTheory.TotallySplit
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfK
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KaUnfoldPfA
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle763
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior

@[expose] public section

section

open IsLocalRing

namespace GlobalTheory.PurityProd

theorem etale_of_etale_atMaximal {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [Algebra A B]
    (h : Algebra.Etale (Localization.AtPrime (maximalIdeal A))
      (TensorProduct A (Localization.AtPrime (maximalIdeal A)) B)) :
    Algebra.Etale A B := by
  let e : A ≃ₐ[A] Localization.AtPrime (maximalIdeal A) :=
    IsLocalization.atUnits A (maximalIdeal A).primeCompl (fun x hx => by
      simpa [IsUnit.mem_submonoid_iff] using IsLocalRing.notMem_maximalIdeal.mp hx)
  haveI : Algebra.Etale A (Localization.AtPrime (maximalIdeal A)) := Algebra.Etale.of_equiv e
  haveI : Algebra.Etale A (TensorProduct A (Localization.AtPrime (maximalIdeal A)) B) :=
    Algebra.Etale.comp A (Localization.AtPrime (maximalIdeal A)) _
  let f : TensorProduct A (Localization.AtPrime (maximalIdeal A)) B ≃ₐ[A] B :=
    (Algebra.TensorProduct.congr e.symm AlgEquiv.refl).trans (Algebra.TensorProduct.lid A B)
  exact Algebra.Etale.of_equiv f

theorem isIntegral_of_forall_apply {O : Type} [CommRing O] {ι : Type} [Finite ι] {R : ι → Type}
    [∀ i, CommRing (R i)] [∀ i, Algebra O (R i)] (x : ∀ i, R i) (hx : ∀ i, IsIntegral O (x i)) :
    IsIntegral O x := by
  first
  | exact @_root_.GlobalTheory.IntegralPi.main
  | exact _root_.GlobalTheory.IntegralPi.main
  | (apply _root_.GlobalTheory.IntegralPi.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralPi.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralPi.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralPi.main ..)

theorem etale_of_etale_pi {R : Type} [CommRing R] [IsNoetherianRing R] {ι : Type} [Finite ι]
    (C : ι → Type) [∀ i, CommRing (C i)] [∀ i, Algebra R (C i)] [∀ i, Module.Finite R (C i)]
    (h : Algebra.Etale R (∀ i, C i)) (i : ι) : Algebra.Etale R (C i) :=
  ⟨(Algebra.FormallyEtale.pi_iff C).mp inferInstance i,
    Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩

end GlobalTheory.PurityProd

namespace GlobalTheory.PurityProd

theorem etale_integralClosure_of_isArtinianRing : ∀ (A E : Type) [CommRing A] [IsRegularLocalRing A]
    [CommRing E] [Algebra A E], IsReduced E → IsArtinianRing E → NoZeroSMulDivisors A E →
    Module.Finite A (integralClosure A E) →
    (∀ (q : Ideal A) [q.IsPrime], q.height ≤ 1 → Algebra.Etale (Localization.AtPrime q)
      (TensorProduct A (Localization.AtPrime q) (integralClosure A E))) →
    Algebra.Etale A (integralClosure A E) := by
  intro A E _ _ _ _ hred hart hnz hfin hq
  classical
  by_cases hm : (maximalIdeal A).height ≤ 1
  · exact etale_of_etale_atMaximal (hq (maximalIdeal A) hm)
  obtain ⟨hdom, hint⟩ := GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing A
  haveI := hdom
  haveI : Fintype (MaximalSpectrum E) := Fintype.ofFinite _
  letI (I : MaximalSpectrum E) : Field (E ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
  let F : MaximalSpectrum E → Type := fun I => E ⧸ I.asIdeal
  let ψ : E ≃ₐ[A] (∀ I, F I) := (IsArtinianRing.equivPi E).restrictScalars A
  let C : MaximalSpectrum E → Type := fun I => integralClosure A (F I)
  let Ψ : integralClosure A E →ₐ[A] ∀ I, C I := AlgHom.pi fun I =>
    ((Pi.evalAlgHom A F I).comp (ψ.toAlgHom.comp (integralClosure A E).val)).codRestrict
      (integralClosure A (F I)) fun x => x.2.map ((Pi.evalAlgHom A F I).comp ψ.toAlgHom)
  have hΨ : Function.Bijective Ψ := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      apply ψ.injective
      funext I
      exact congrArg Subtype.val (congrFun hxy I)
    · intro l
      refine ⟨⟨ψ.symm fun I => (l I).1, ?_⟩, ?_⟩
      · exact (isIntegral_of_forall_apply (fun I => ((l I : F I))) fun I => (l I).2).map
          ψ.symm.toAlgHom
      · funext I
        apply Subtype.ext
        change ψ (ψ.symm fun I => (l I).1) I = (l I).1
        rw [AlgEquiv.apply_symm_apply]
  let Φ : integralClosure A E ≃ₐ[A] ∀ I, C I := AlgEquiv.ofBijective Ψ hΨ
  have hinjF : ∀ I, Function.Injective (algebraMap A (F I)) := by
    intro I
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    have hne : ψ.symm (Pi.single I 1) ≠ 0 := by
      intro h0
      have := congrArg ψ h0
      rw [AlgEquiv.apply_symm_apply, map_zero] at this
      exact one_ne_zero (by simpa using congrFun this I : (1 : F I) = 0)
    have h0 : a • ψ.symm (Pi.single I 1) = 0 := by
      apply ψ.injective
      rw [map_smul, AlgEquiv.apply_symm_apply, map_zero]
      funext J
      by_cases hJ : J = I
      · subst hJ; simp [Algebra.smul_def, ha]
      · simp [hJ]
    rcases smul_eq_zero.mp h0 with h | h
    · exact h
    · exact absurd h hne
  haveI hfaith : ∀ I, FaithfulSMul A (C I) := fun I => by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b hab
    apply hinjF I
    exact congrArg Subtype.val hab
  haveI hfC : ∀ I, FaithfulSMul (C I) (F I) := fun I =>
    (faithfulSMul_iff_algebraMap_injective _ _).mpr Subtype.val_injective
  haveI hintC : ∀ I, IsIntegrallyClosed (C I) := fun I =>
    IsIntegrallyClosed.of_isIntegrallyClosedIn (C I) (F I)
  haveI hfinC : ∀ I, Module.Finite A (C I) := fun I =>
    Module.Finite.of_surjective ((Pi.evalAlgHom A C I).toLinearMap.comp Φ.toLinearMap) (by
      intro c
      obtain ⟨x, hx⟩ := Φ.surjective (Pi.single I c)
      exact ⟨x, by simp [hx]⟩)
  haveI : ∀ I, Algebra.Etale A (C I) := by
    intro I
    have key := GlobalTheory.T.etale_of_etale_height_one_of_regularLocalRing A (C I)
    refine key ?_ ?_ ?_ ?_
    · exact IsRegularLocalRing.spanFinrank_maximalIdeal
    · rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
      exact_mod_cast (le_of_lt (not_le.mp hm))
    · intro hf
      apply hm
      rw [(IsLocalRing.isField_iff_maximalIdeal_eq).mp hf, Ideal.height_bot]
      exact zero_le_one
    · intro p _ hp
      have h1 := hq p (le_of_eq hp)
      let G : TensorProduct A (Localization.AtPrime p) (integralClosure A E) ≃ₐ[Localization.AtPrime p]
          ∀ J, TensorProduct A (Localization.AtPrime p) (C J) :=
        (Algebra.TensorProduct.congr AlgEquiv.refl Φ).trans
          (Algebra.TensorProduct.piRight A (Localization.AtPrime p) (Localization.AtPrime p) C)
      haveI : Algebra.Etale (Localization.AtPrime p)
          (∀ J, TensorProduct A (Localization.AtPrime p) (C J)) := Algebra.Etale.of_equiv G
      exact etale_of_etale_pi (fun J => TensorProduct A (Localization.AtPrime p) (C J)) this I
  exact Algebra.Etale.of_equiv Φ.symm

end GlobalTheory.PurityProd
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.PeakWeightSmooth

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem lact_inv_lact (X : Data E r) (γ : GL (Fin r) E) (y : Frame X.Ψ r) : lact γ⁻¹ (lact γ y) = y := by
  rw [KU.lact_lact X, inv_mul_cancel, KU.lact_one X]

theorem lact_lact_inv (X : Data E r) (γ : GL (Fin r) E) (y : Frame X.Ψ r) : lact γ (lact γ⁻¹ y) = y := by
  rw [KU.lact_lact X, mul_inv_cancel, KU.lact_one X]

theorem local_form (X : Data E r) (x : Frame X.Ψ r) (hx : IsOrth X x) (ρ R : ℝ) (η : V (nd X) → ℝ)
    (ψ : Frame X.Ψ r → ℝ) (hρR : ρ < R) (hR : ∀ z : V (nd X), ‖z‖ ≤ R → z ∈ OmF X x)
    (hψ : ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, ∀ z : V (nd X), ‖z‖ ≤ R → ψ (lact γ (rmul (cpt X x z) b)) = η z)
    (h0 : ∀ y, (¬ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ ρ ∧ y = lact γ (rmul (cpt X x z) b)) →
      ψ y = 0)
    (hloc : ∀ y ∈ X.dom, (¬ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ ρ ∧
      y = lact γ (rmul (cpt X x z) b)) → ∀ᶠ y' in 𝓝 y, ¬ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X),
        ‖z‖ ≤ ρ ∧ y' = lact γ (rmul (cpt X x z) b))
    {y : Frame X.Ψ r} (hy : y ∈ X.dom) :
    (∀ᶠ y' in 𝓝 y, ψ y' = 0) ∨
    ∃ (γ : GL (Fin r) E) (zOf : Frame X.Ψ r → V (nd X)) (U : Set (Frame X.Ψ r)),
      IsOpen U ∧ lact γ⁻¹ y ∈ U ∧ DifferentiableOn ℂ zOf U ∧
      ∀ᶠ y' in 𝓝 y, ψ y' = η (zOf (lact γ⁻¹ y')) := by
  by_cases hS : ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ ρ ∧ y = lact γ (rmul (cpt X x z) b)
  · right
    obtain ⟨γ, hγ, b, hb, z, hz, rfl⟩ := hS
    obtain ⟨Δ, zOf, bOf, hΔ, -, hzd, -, hsplit, hinv⟩ := lu_holds r X x hx
    have hUo : IsOpen {w | w ∈ X.dom ∧ Δ w ≠ 0} :=
      (IW.isOpen_dom X).inter (isOpen_ne_fun hΔ.continuous continuous_const)
    have hzO : z ∈ OmF X x := hR z (hz.trans hρR.le)
    have hmem : lact γ⁻¹ (lact γ (rmul (cpt X x z) b)) ∈ {w | w ∈ X.dom ∧ Δ w ≠ 0} := by
      rw [lact_inv_lact]
      exact ⟨OntoS.dom_rmul X hzO hb, (hinv z hzO b hb).1⟩
    refine ⟨γ, zOf, _, hUo, hmem, hzd, ?_⟩
    have hcont : ContinuousAt (fun y' => lact γ⁻¹ y') (lact γ (rmul (cpt X x z) b)) :=
      (KU.cont_lact X γ⁻¹).continuousAt
    have hU' : ∀ᶠ y' in 𝓝 (lact γ (rmul (cpt X x z) b)), lact γ⁻¹ y' ∈ {w | w ∈ X.dom ∧ Δ w ≠ 0} :=
      hcont.preimage_mem_nhds (hUo.mem_nhds hmem)
    have hzc : ContinuousAt (fun y' => zOf (lact γ⁻¹ y')) (lact γ (rmul (cpt X x z) b)) :=
      ContinuousAt.comp (f := fun y' => lact γ⁻¹ y')
        ((hzd.differentiableAt (hUo.mem_nhds hmem)).continuousAt) hcont
    have hval : zOf (lact γ⁻¹ (lact γ (rmul (cpt X x z) b))) = z := by
      rw [lact_inv_lact]; exact (hinv z hzO b hb).2.1
    have h2 : ‖zOf (lact γ⁻¹ (lact γ (rmul (cpt X x z) b)))‖ < R := by
      rw [hval]; exact lt_of_le_of_lt hz hρR
    have hnear : ∀ᶠ y' in 𝓝 (lact γ (rmul (cpt X x z) b)), ‖zOf (lact γ⁻¹ y')‖ < R :=
      hzc.norm.eventually_lt continuousAt_const h2
    filter_upwards [hU', hnear] with y' hy'U hy'n
    obtain ⟨hy'd, hy'Δ⟩ := hy'U
    obtain ⟨-, hbO, heq⟩ := hsplit _ hy'd hy'Δ
    have hy' : y' = lact γ (rmul (cpt X x (zOf (lact γ⁻¹ y'))) (bOf (lact γ⁻¹ y'))) := by
      rw [← heq, lact_lact_inv]
    conv_lhs => rw [hy']
    exact hψ γ hγ _ hbO _ hy'n.le
  · left
    filter_upwards [hloc y hy hS] with y' hy'
    exact h0 y' hy'

end GlobalTheory.PeakWeightSmooth

namespace GlobalTheory.PeakWeightSmooth

theorem measurable_and_contDiffOn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) (ρ R : ℝ) (η : V (nd X) → ℝ) (ψ : Frame X.Ψ r → ℝ), IsOrth X x → ρ < R → (∀ z : V (nd X), ‖z‖ ≤ R → z ∈ OmF X x) → ContDiff ℝ ∞ η → (∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, ∀ z : V (nd X), ‖z‖ ≤ R → ψ (lact γ (rmul (cpt X x z) b)) = η z) → (∀ y, (¬ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ ρ ∧ y = lact γ (rmul (cpt X x z) b)) → ψ y = 0) → (∀ y ∈ X.dom, (¬ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ ρ ∧ y = lact γ (rmul (cpt X x z) b)) → ∀ᶠ y' in 𝓝 y, ¬ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ ρ ∧ y' = lact γ (rmul (cpt X x z) b)) → Measurable ψ ∧ ContDiffOn ℝ ∞ (fun w => ψ (cpt X x w)) (OmF X x) := by
  intro E _ _ _ r X x ρ R η ψ hx hρR hR hη hψ h0 hloc
  classical
  have hS_dom : ∀ y, (∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ ρ ∧
      y = lact γ (rmul (cpt X x z) b)) → y ∈ X.dom := by
    rintro y ⟨γ, hγ, b, hb, z, hz, rfl⟩
    exact KU.lact_dom X hγ (OntoS.dom_rmul X (hR z (hz.trans hρR.le)) hb)
  have hcont : ∀ y ∈ X.dom, ContinuousAt ψ y := by
    intro y hy
    rcases local_form X x hx ρ R η ψ hρR hR hψ h0 hloc hy with h | ⟨γ, zOf, U, hUo, hyU, hzd, hev⟩
    · exact (continuousAt_const (y := (0 : ℝ))).congr (h.mono fun _ h => h.symm)
    · have : ContinuousAt (fun y' => η (zOf (lact γ⁻¹ y'))) y :=
        hη.continuous.continuousAt.comp (((hzd.differentiableAt (hUo.mem_nhds hyU)).continuousAt).comp
          (KU.cont_lact X γ⁻¹).continuousAt)
      exact this.congr (hev.mono fun _ h => h.symm)
  have hzero : ∀ y, y ∉ X.dom → ψ y = 0 := fun y hy => h0 y (fun h => hy (hS_dom y h))
  constructor
  · have heq : ψ = X.dom.piecewise ψ (fun _ => 0) := by
      funext y
      by_cases hy : y ∈ X.dom
      · simp [Set.piecewise, hy]
      · simp [Set.piecewise, hy, hzero y hy]
    rw [heq]
    exact ContinuousOn.measurable_piecewise (fun y hy => (hcont y hy).continuousWithinAt)
      continuousOn_const (IW.isOpen_dom X).measurableSet
  · intro w hw
    refine ContDiffAt.contDiffWithinAt ?_
    have hc : ContinuousAt (cpt X x) w := (IW.cpt_diff X x).continuous.continuousAt
    rcases local_form X x hx ρ R η ψ hρR hR hψ h0 hloc (y := cpt X x w) hw with
      h | ⟨γ, zOf, U, hUo, hyU, hzd, hev⟩
    · have h' : ∀ᶠ w' in 𝓝 w, ψ (cpt X x w') = 0 := hc.eventually h
      exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq h'
    · have hg : Differentiable ℂ (fun w' => lact γ⁻¹ (cpt X x w')) := by
        have e : (fun w' => lact γ⁻¹ (cpt X x w')) = cpt X (lact γ⁻¹ x) := by
          funext w'; rw [KU.cpt_lact]
        rw [e]; exact IW.cpt_diff X _
      have hN : (fun w' => lact γ⁻¹ (cpt X x w')) ⁻¹' U ∈ 𝓝 w :=
        hg.continuous.continuousAt.preimage_mem_nhds (hUo.mem_nhds hyU)
      have hΦd : DifferentiableOn ℂ (fun w' => zOf (lact γ⁻¹ (cpt X x w')))
          ((fun w' => lact γ⁻¹ (cpt X x w')) ⁻¹' U) :=
        hzd.comp hg.differentiableOn (fun _ h => h)
      have hΦ : ContDiffAt ℂ ∞ (fun w' => zOf (lact γ⁻¹ (cpt X x w'))) w :=
        GlobalTheory.SCV.contDiffAt_of_differentiableOn hΦd hN _
      have hev' : ∀ᶠ w' in 𝓝 w, ψ (cpt X x w') = η (zOf (lact γ⁻¹ (cpt X x w'))) := hc.eventually hev
      exact ((hη.contDiffAt).comp w (hΦ.restrict_scalars ℝ)).congr_of_eventuallyEq hev'

end GlobalTheory.PeakWeightSmooth
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_grpPullback_powObj_projections : ∀ (S T : Scheme.{0}) (t : T ⟶ S) (A : Over S) [GrpObj A] (A' : Over T) [GrpObj A'] (φ' : A'.left ⟶ A.left) (B' : Over T) [GrpObj B'] (r : ℕ) (φB : B'.left ⟶ (Out.powObj A r).left), IsGrpPullback A' A t φ' → IsGrpPullback B' (Out.powObj A r) t φB → ∃ pr' : Fin r → (B' ⟶ A'), (∀ u, IsMonHom (pr' u)) ∧ (∀ u, (pr' u).left ≫ φ' = φB ≫ (Out.powPr A u).left) ∧ ∀ (X : Over T) (y : Fin r → (X ⟶ A')), ∃! x : X ⟶ B', ∀ u, x ≫ pr' u = y u := by
  first | (exact @GlobalTheory.ActFin.exists_powPr_of_isGrpPullback) | (exact GlobalTheory.ActFin.exists_powPr_of_isGrpPullback) | (intros; apply GlobalTheory.ActFin.exists_powPr_of_isGrpPullback  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem siegel_levels_spread_to_subring : ∀ (g n : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Type) [CommRing S] (R₀ : Subring S) (s₀ : Sp R₀ ⟶ Sp B) (d₀ : SiegPre g n ζ s₀) (Y : Scheme.{0}) (sY : Y ⟶ Sp B) (u : SiegPre g n ζ sY) (h₀ : Sp R₀ ⟶ Y) (ψ : d₀.A.left ⟶ u.A.left) (sE : Sp S ⟶ Sp B) (e : SiegPre g n ζ sE) (j : e.A.left ⟶ d₀.A.left), IsPullback ψ d₀.A.hom u.A.hom h₀ → (∀ a, (e.lev a).left ≫ j = spMap R₀.subtype ≫ (d₀.lev a).left) → (∀ a, (e.lev a).left ≫ (j ≫ ψ) = (spMap R₀.subtype ≫ h₀) ≫ (u.lev a).left) → ∃ F : Finset S, ∀ (R₁ : Subring S) (hle : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (s₁ : Sp R₁ ⟶ Sp B) (d₁ : SiegPre g n ζ s₁) (φ₁ : d₁.A.left ⟶ d₀.A.left), IsGrpPullback d₁.A u.A (spMap (Subring.inclusion hle) ≫ h₀) (φ₁ ≫ ψ) → (∀ a, (d₁.lev a).left ≫ φ₁ = spMap (Subring.inclusion hle) ≫ (d₀.lev a).left) → ∀ a, (d₁.lev a).left ≫ (φ₁ ≫ ψ) = (spMap (Subring.inclusion hle) ≫ h₀) ≫ (u.lev a).left := by
  intro g n B _ ζ S _ R₀ s₀ d₀ Y sY u h₀ ψ sE e j hψ hj hjψ
  classical
  haveI : Smooth u.A.hom := u.ab.smooth
  have hsec₀ : ∀ a, (d₀.lev a).left ≫ d₀.A.hom = 𝟙 (Sp R₀) := fun a => Over.w (d₀.lev a)
  have hsecu : ∀ a, (u.lev a).left ≫ u.A.hom = 𝟙 Y := fun a => Over.w (u.lev a)
  have key : ∀ i : Fin g ⊕ Fin g, ∃ F : Finset S, ∀ (R₁ : Subring S) (hle : R₀ ≤ R₁), (F : Set S) ⊆ R₁ →
      spMap (Subring.inclusion hle) ≫ (d₀.lev (Pi.single i 1)).left ≫ ψ =
        spMap (Subring.inclusion hle) ≫ h₀ ≫ (u.lev (Pi.single i 1)).left := by
    intro i
    let x : Sp R₀ ⟶ pullback u.A.hom h₀ := pullback.lift ((d₀.lev (Pi.single i 1)).left ≫ ψ) (𝟙 _) (by
      rw [Category.assoc, hψ.w, ← Category.assoc, hsec₀, Category.id_comp])
    let y : Sp R₀ ⟶ pullback u.A.hom h₀ := pullback.lift (h₀ ≫ (u.lev (Pi.single i 1)).left) (𝟙 _) (by
      rw [Category.assoc, hsecu, Category.comp_id, Category.id_comp])
    have hx : x ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
    have hy : y ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
    have hxy : spMap R₀.subtype ≫ x = spMap R₀.subtype ≫ y := by
      apply pullback.hom_ext
      · simp only [x, y, Category.assoc, pullback.lift_fst]
        rw [← Category.assoc, ← hj, Category.assoc, hjψ, Category.assoc]
      · simp only [x, y, Category.assoc, pullback.lift_snd]
    obtain ⟨F, hF⟩ := morphisms_eq_spread_to_subring S R₀ (Sp S) (Sp R₀) (pullback u.A.hom h₀) (𝟙 _) (𝟙 _)
      (pullback.snd _ _) (spMap R₀.subtype) x y (IsPullback.id_vert _) hx hy hxy
    refine ⟨F, fun R₁ hle hF₁ => ?_⟩
    have := congrArg (· ≫ pullback.fst u.A.hom h₀)
      (hF R₁ hle hF₁ (Sp R₁) (𝟙 _) (spMap (Subring.inclusion hle)) (IsPullback.id_vert _))
    simpa only [x, y, Category.assoc, pullback.lift_fst] using this
  choose F hF using key
  refine ⟨Finset.univ.biUnion F, fun R₁ hle hsub s₁ d₁ φ₁ hgp hlev₁ a => ?_⟩
  have hbasis : ∀ i : Fin g ⊕ Fin g, (d₁.lev (Pi.single i 1)).left ≫ (φ₁ ≫ ψ) =
      (spMap (Subring.inclusion hle) ≫ h₀) ≫ (u.lev (Pi.single i 1)).left := by
    intro i
    have hFi : (F i : Set S) ⊆ R₁ := fun x hx => hsub (by
      simp only [Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Set.iUnion_true, Set.mem_iUnion]
      exact ⟨i, hx⟩)
    rw [← Category.assoc, hlev₁, Category.assoc, hF i R₁ hle hFi, Category.assoc]
  let f : Sp R₁ ⟶ Y := spMap (Subring.inclusion hle) ≫ h₀
  let M : Over Y := Over.mk ((𝟙_ (Over (Sp R₁))).hom ≫ f)
  have hunit : (toUnit M).left = f := by
    have := Over.w (toUnit M)
    exact (Category.comp_id _).symm.trans (this.trans (Category.id_comp _))
  have w : ∀ a, ((d₁.lev a).left ≫ (φ₁ ≫ ψ)) ≫ u.A.hom = M.hom := by
    intro a
    rw [Category.assoc, hgp.1.w, ← Category.assoc, Over.w (d₁.lev a)]
    rfl
  let Ψ₁ : (Fin g ⊕ Fin g → ℤ) →+ Additive (M ⟶ u.A) :=
    AddMonoidHom.mk' (fun a => Additive.ofMul (toUnit M ≫ u.lev a)) (by
      intro a b
      rw [u.lev_add, comp_mul]
      rfl)
  let Ψ₂ : (Fin g ⊕ Fin g → ℤ) →+ Additive (M ⟶ u.A) :=
    AddMonoidHom.mk' (fun a => Additive.ofMul (Over.homMk ((d₁.lev a).left ≫ (φ₁ ≫ ψ)) (w a) : M ⟶ u.A)) (by
      intro a b
      show Additive.ofMul _ = Additive.ofMul (_ * _)
      congr 1
      apply Over.OverMorphism.ext
      rw [hgp.2 (𝟙_ _) (d₁.lev a) (d₁.lev b) _ _ rfl rfl, ← d₁.lev_add]
      rfl)
  have hΨ : Ψ₁ = Ψ₂ := by
    refine AddMonoidHom.functions_ext' _ _ _ (fun i => AddMonoidHom.ext_int ?_)
    show Additive.ofMul (toUnit M ≫ u.lev (Pi.single i 1)) =
      Additive.ofMul (Over.homMk ((d₁.lev (Pi.single i 1)).left ≫ (φ₁ ≫ ψ)) (w (Pi.single i 1)) : M ⟶ u.A)
    refine congrArg Additive.ofMul (Over.OverMorphism.ext ?_)
    rw [Over.comp_left, hunit]
    exact (hbasis i).symm
  have := congrArg (fun φ => (Additive.toMul (φ a)).left) hΨ
  simp only [Ψ₁, Ψ₂, AddMonoidHom.mk'_apply, toMul_ofMul, Over.comp_left, Over.homMk_left] at this
  rw [← this, hunit]

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

theorem _root_.GlobalTheory.T.isHolTo_baseChange_complex_iff : ∀ (R : Type) [CommRing R] (σ : R →+* ℂ) (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp ℂ) (f : X' ⟶ X), IsPullback f s' s (spMap σ) → ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (B : Set V) (y : V → (Sp ℂ ⟶ X')), (∀ b ∈ B, y b ≫ s' = spMap (RingHom.id ℂ)) → (IsHolTo B y ↔ IsHolTo B (fun b => y b ≫ f)) := by
  first | exact @GlobalTheory.PELU.isHolTo_bc_iff | exact GlobalTheory.PELU.isHolTo_bc_iff | (intros; apply GlobalTheory.PELU.isHolTo_bc_iff <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_idempotents_abelianScheme_constant_dimension : ∀ (R₀ : Type) [CommRing R₀] (A : Over (Sp R₀)) [GrpObj A], IsAbelianScheme A → ∃ (n : ℕ) (e : Fin n → R₀), CompleteOrthogonalIdempotents e ∧ ∀ k, ∃ g : ℕ, SmoothOfRelativeDimension g (Limits.pullback.snd A.hom (spMap (Ideal.Quotient.mk (Ideal.span {1 - e k})))) := by
  first | exact @GlobalTheory.DimSplit.exists_idempotents_smoothOfRelativeDimension | exact GlobalTheory.DimSplit.exists_idempotents_smoothOfRelativeDimension | (intros; apply GlobalTheory.DimSplit.exists_idempotents_smoothOfRelativeDimension <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechFin

theorem _root_.GlobalTheory.T.properSemiAbelian_affineOpen_baseChange_compact_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → ∀ (U : X.affineOpens) (J : Type) (W : J → t.G.left.Opens), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → CompactSpace ↑(pullback t.G.hom U.2.fromSpec : Scheme.{0}) ∧ (∀ I : Finset J, I.Nonempty → IsAffineOpen (⨅ i ∈ I, pullback.fst t.G.hom U.2.fromSpec ⁻¹ᵁ W i)) ∧ ⨆ i, pullback.fst t.G.hom U.2.fromSpec ⁻¹ᵁ W i = ⊤ := by
  first | exact @GlobalTheory.pullback_fromSpec_compact_affineCover | exact GlobalTheory.pullback_fromSpec_compact_affineCover | (intros; apply GlobalTheory.pullback_fromSpec_compact_affineCover <;> assumption)
end
