module

public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle006
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SvalEqZeroOfExpandsAt
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermFunPf
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle073
public import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle071
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle044
public import Formalism.LocalToGlobal.CharacterGerms.Bundle005
public import Formalism.RealPlaceAnalysis.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle075
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle058
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle072
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle074
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmoothMapsClosure
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DerivedActionDiscreteSeriesProperties
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrechetContinuousContinuousOnOrbitHasDerivAt
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle004
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle076
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle003
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Formalism.LocalToGlobal.Divisibility.Numbers
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.IntegralGerm

section Val

variable {X Y Y' Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

theorem gs_comp (r : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (h : g (r z) ∈ U) (a : Γ(X, U)) :
    gs (r ≫ g) z U a = (r.stalkMap z).hom (gs g (r z) U a) := by
  rw [← gs_pull r g z U h, gs_stalkMap r z _ h]
  exact congrArg _ ((gs_pull (𝟙 Y) g (r z) U h a).trans (by rw [Category.id_comp]))

theorem sval_comp {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y') (h : Y' ⟶ Y) (z : Z)
    {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval s (r ≫ h) z J = (r.stalkMap z).hom (sval s h (r z) fun ψ => J (r ≫ ψ)) := by
  rw [sval_of s (r ≫ h) z J (fun k => J (r ≫ h ≫ φ k)) (fun k => by rw [Category.assoc])]
  exact gs_comp r h z _ (Set.mem_iInter.2 fun k => hJ (r ≫ h ≫ φ k)) _

theorem sval_secLin (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ₁ : K' → (Y' ⟶ X)} {ε₁ : K' → ℤ}
    {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)} {n : ℕ} {s : Fin n → LB.Sec (LB.LinComb L φ ε)} {h : Y' ⟶ Y}
    {c : Fin n → Γ(Y', ⊤)} (H : GeneratorPullback.SecLin L φ₁ ε₁ s₁ φ ε s h c) (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : sval s₁ r z J = ∑ i, gs r z ⊤ (c i) * sval (s i) (r ≫ h) z J := by
  have e := (FieldBaseChange.secLin_iff_val hL s₁ s h c).1 H (r z) (fun ψ => J (r ≫ ψ)) fun ψ => hJ (r ≫ ψ)
  have e₁ := sval_comp s₁ r (𝟙 _) z hJ

  rw [Category.comp_id, e, map_sum] at e₁
  refine e₁.trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [map_mul, ← gs_stalkMap r z ⊤ trivial, Category.id_comp, ← sval_comp (s i) r h z hJ]

theorem exists_value (hL : L.IsLB) {q : ℕ} (s : H0 L q) (h : Y ⟶ X)
    (t : LB.Gen (LB.LinComb L (K := Fin 1) (fun _ => h) (fun _ => (1 : ℤ)))) (ht : t.IsGen) :
    ∃ u : Γ(Y, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J →
      sval s (r ≫ h) z J = gs r z ⊤ u * (val t r z J ^ q).val := by
  obtain ⟨w, hw⟩ := exists_sec hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim)
    (fun U _ hh => by simp [Fintype.prod_sum_type])
    (pullMulSec s h (LB.invGen L _ _ (GeneratorPullback.powGen L _ _ t q))
      (invGen_isGen _ _ _ _ (DVR.powGen_isGen _ _ _ _ ht q)))
  have le : (⊤ : Y.Opens) ≤ LB.wchart L (K := PEmpty) (Y := Y) PEmpty.elim PEmpty.elim :=
    fun _ _ => Set.mem_iInter.2 fun k => k.elim
  refine ⟨(Y.presheaf.map (homOfLE le).op).hom (w.f PEmpty.elim), fun Z r z J hJ => ?_⟩
  have e := hw Z r z J hJ
  have ep : val (GeneratorPullback.powGen L _ _ t q) r z J = val t r z J ^ q := map_pow _ _ _
  rw [sval_pullMulSec _ _ _ _ _ z hJ, val_inv, ep, sval_of w _ z J PEmpty.elim (fun k => k.elim)] at e
  refine Eq.trans ?_ (congrArg (· * _) ((gs_res r z le trivial _).trans e).symm)
  rw [_root_.mul_assoc, Units.inv_mul, _root_.mul_one]

end Val

theorem gs_spMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (y : Sp B) (a : A) :
    gs (spMap f) y ⊤ (toΓ A a) = gs (𝟙 _) y ⊤ (toΓ B (f a)) := by
  have e := FieldBaseChange.constVal_specMap (𝟙 (Sp B)) f y a
  rw [Category.id_comp] at e
  exact e

theorem toΓ_surjective (A : Type) [CommRing A] : Function.Surjective (toΓ A) :=
  (Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv.surjective

theorem coeff_of_jet {V F κ : Type} [CommRing V] [CommRing F] (g : V →+* F) [Fintype κ] [DecidableEq κ]
    (f : MvPowerSeries κ F) (e : κ →₀ ℕ) {n : ℕ} (c : Fin n → F) (a : Fin n → Jet V κ e.degree)
    (h : psJet e.degree f = ∑ i, algebraMap F (Jet F κ e.degree) (c i) * jetCoef g κ e.degree (a i)) :
    ∃ b : Fin n → V, MvPowerSeries.coeff e f = ∑ i, c i * g (b i) := by
  choose p hp using fun i => Ideal.Quotient.mk_surjective (a i)
  refine ⟨fun i => AddMonoidAlgebra.coeff (p i) e, ?_⟩
  have h1 : psJet e.degree f = Ideal.Quotient.mk _ (∑ i, MvPolynomial.C (c i) * MvPolynomial.map g (p i)) := by

    rw [h, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, ← hp]
    rfl
  rw [psJet, Ideal.Quotient.eq] at h1
  have h2 := GermFun.coeff_eq_zero_of_mem h1 (Nat.lt_succ_self _)
  rw [MvPolynomial.coeff_sub, GermFun.coeff_psTrunc _ _ _ le_rfl, sub_eq_zero] at h2
  rw [h2, MvPolynomial.coeff_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map]

theorem main : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → AIntSt := by
  intro hLaw _ _ hT V _ _ _ _ ϖ hϖ D A G _ _ U κ _ _ z _ τ hτ F _ _ _ _ v hv q hq σ' s f hE hG hs e
  obtain ⟨n, c, σ, hc, hlin⟩ := IntegralCombination.main hLaw.globalFns hT V ϖ hϖ D A G U F v hv q hq σ' s hE hs
  obtain ⟨zF, h1, h2, h3⟩ := hG e.degree
  have hL := U.LG.isLB
  choose u hu using fun i => exists_value hL (σ i) (z e.degree).left (τ e.degree) (hτ e.degree)
  choose a ha using fun i => toΓ_surjective (Jet V κ e.degree) (u i)
  obtain ⟨b, hb⟩ := coeff_of_jet (algebraMap V F) f e c a (GermFun.toΓ_injective _ (fn_ext fun y _ => by
    choose J hJ using fun χ : Sp (Jet F κ e.degree) ⟶ G.left => exists_chart hL (χ y)
    have e₁ := (h3 y J hJ).symm.trans (sval_secLin hL hlin zF y hJ)
    refine (Units.mul_left_inj _).1 (e₁.trans ?_)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, gs_eq _ y ⊤ trivial, map_sum, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← gs_eq _ y ⊤ trivial, map_mul, gs_mul _ y ⊤ trivial, h2, hu i _ _ y J hJ, ← ha, gs_spMap, _root_.mul_assoc,
      FieldBaseChange.gs_scal, h1]
    exact congrArg (· * _) (gs_spMap _ y _)))
  rw [hb]
  refine v.map_le_sum fun i _ => ?_
  rw [AddValuation.map_mul, IsScalarTower.algebraMap_apply V (FractionRing V) F]
  exact add_nonneg (hc i) (GC.v_alg_nonneg hϖ hv _)

end GlobalTheory.IntegralGerm
end
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.exists_K_type_nonzero_bessel : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (l : R.H → Wp), R.IsDS ε mu → IsBes R z π l → NzOn R l → ∃ v ∈ R.TK, l v ≠ 0 := by
  first | exact @GlobalTheory.bessel_nonzero_on_translates | exact GlobalTheory.bessel_nonzero_on_translates | (intros; apply GlobalTheory.bessel_nonzero_on_translates <;> assumption)
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.bessel_functional_side_growth : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (l l₁ : R.H → Wp), R.IsDS ε mu → SideG k r z π u μW μN μG νq → IsBes R z π l → NzOn R l → IsBes R z π l₁ → ∃ c : ℂ, ∀ v ∈ R.sm, l₁ v = c • l v := by
  first | exact @GlobalTheory.BesselLine.bessel_line | exact GlobalTheory.BesselLine.bessel_line | (intros; apply GlobalTheory.BesselLine.bessel_line <;> assumption)
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem exists_coef_family : Hyps → ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R : (Fin (2 * P.r + P.k + 1) → ℤ) → Rep P.k P.r) (l : ∀ ν, (R ν).H → Wp) (l' : ∀ ν, (R ν).H → Wq) (dg : (Fin (2 * P.r + P.k + 1) → ℤ) → ℝ) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (s₀ : ℂ), IsFam lam q0 R → (haveI := FiniteDimensional.complete ℂ Wp; SideFam p.T.base.z p.T.base.π p.T.base.μW p.T.base.μN p.T.base.μG q0 R l dg) → (haveI := FiniteDimensional.complete ℂ Wq; SideFam p.T.base.z' p.T.base.π' p.T.base.μW' p.T.base.μN p.T.base.μG q0 R l' dg) → IsCoef (R 0) (l 0) (l' 0) f s₀ → s₀ ≠ 0 → ∃ (s : (Fin (2 * P.r + P.k + 1) → ℤ) → ℂ) (J : (Fin (2 * P.r + P.k + 1) → ℤ) → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (t : ℝ), 0 < t ∧ J 0 = (fun g => (t : ℂ) • f g) ∧ (NzOn (R 0) (l 0) ∧ NzOn (R 0) (l' 0)) ∧ (∀ ν, n1 ν ≤ q0 → NzOn (R ν) (l ν) → NzOn (R ν) (l' ν) → IsCoef (R ν) (l ν) (l' ν) (J ν) (s ν) ∧ ‖s ν‖ = dg ν) ∧ (∀ ν, ¬ (n1 ν ≤ q0 ∧ NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν)) → J ν = 0) := by
  intro hH P Wp Wq _ _ _ _ _ _ p lam b bv ga h q0 R l l' dg f s₀ hfam hL hR hf hs₀
  haveI := FiniteDimensional.complete ℂ Wp
  haveI := FiniteDimensional.complete ℂ Wq
  classical
  have hK : PI.KFinSmooth := hH.1.2.2.1
  have h0 : n1 (0 : Fin (2 * P.r + P.k + 1) → ℤ) ≤ q0 := by simp [n1]
  have hDS : ∀ ν, n1 ν ≤ q0 → (R ν).IsDS (PI.BesselPeriodGGP.eps48 P.k P.r) (fun a => lam a + (ν a : ℝ)) :=
    fun ν hν => hfam ν hν
  have hdg0 : 0 < dg 0 := (hL 0 h0).2.1
  have hsn : 0 < ‖s₀‖ := norm_pos_iff.mpr hs₀
  have hnz : NzOn (R 0) (l 0) ∧ NzOn (R 0) (l' 0) := by
    obtain ⟨m, x, y, X, hxy, -, hs⟩ := hf
    have hsm := (GlobalTheory.rep_basic_of_isDS hK _ _ _ _ (R 0) (hDS 0 h0)).2.2.2.2.1
    rw [hs] at hs₀
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs₀
    refine ⟨⟨x i, hsm _ (hxy i).1, fun h => hi ?_⟩, ⟨y i, hsm _ (hxy i).2, fun h => hi ?_⟩⟩
    · rw [h, inner_zero_left]
    · rw [h, map_zero, inner_zero_right]
  have hex : ∀ ν, ∃ (s : ℂ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)),
      (ν = 0 → F = fun g => ((dg 0 / ‖s₀‖ : ℝ) : ℂ) • f g) ∧
      (n1 ν ≤ q0 → NzOn (R ν) (l ν) → NzOn (R ν) (l' ν) → IsCoef (R ν) (l ν) (l' ν) F s ∧ ‖s‖ = dg ν) ∧
      (¬ (n1 ν ≤ q0 ∧ NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν)) → F = 0) := by
    intro ν
    by_cases hν : ν = 0
    · subst hν
      refine ⟨((dg 0 / ‖s₀‖ : ℝ) : ℂ) * s₀, _, fun _ => rfl, fun _ _ _ => ⟨?_, ?_⟩, fun hn => ?_⟩
      · exact (GlobalTheory.isCoef_of_translate_smul_exists hK _ _ _ _ (R 0) Wp Wq (l 0) (l' 0) (hDS 0 h0)).2.1 f s₀ _ hf
      · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (div_pos hdg0 hsn).le]
        field_simp
      · exact absurd ⟨h0, hnz⟩ hn
    · by_cases hc : n1 ν ≤ q0 ∧ NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν)
      · obtain ⟨h1, h2, h3⟩ := hc
        have e1 := GlobalTheory.bessel_nonzero_on_translates hH _ _ _ _ (R ν) Wp _ _ (l ν) (hDS ν h1) (hL ν h1).1.1 h2
        have e2 := GlobalTheory.bessel_nonzero_on_translates hH _ _ _ _ (R ν) Wq _ _ (l' ν) (hDS ν h1) (hR ν h1).1.1 h3
        obtain ⟨F, hF⟩ := (GlobalTheory.isCoef_of_translate_smul_exists hK _ _ _ _ (R ν) Wp Wq (l ν) (l' ν)
          (hDS ν h1)).2.2 e1 e2 (dg ν : ℂ)
        refine ⟨_, F, fun h => absurd h hν, fun _ _ _ => ⟨hF, ?_⟩, fun hn => absurd ⟨h1, h2, h3⟩ hn⟩
        rw [Complex.norm_real, Real.norm_of_nonneg (hL ν h1).2.1.le]
      · exact ⟨0, 0, fun h => absurd h hν, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ hc, fun _ => rfl⟩
  choose s J h1 h2 h3 using hex
  exact ⟨s, J, dg 0 / ‖s₀‖, div_pos hdg0 hsn, h1 0 rfl, hnz, h2, h3⟩

end GlobalTheory
end

section

open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

theorem lev_proj_and_sum_sq_le : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (N : Fin n → Type) [∀ s, NormedAddCommGroup (N s)] [∀ s, InnerProductSpace ℂ (N s)] (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s)) (io : ∀ s, N s →ₗ[ℂ] (Fin n → M)) (pr : ∀ s, (Fin n → M) →ₗ[ℂ] N s) (μ : Fin n → ℝ) (kk j : ℕ) (bv : ℝ) (w : M), IsMod ε E μ → (∀ s, IsMod ε (F s) (μ - Pi.single s 1)) → AlgTens ε E N F io pr → Shape ε kk μ bv → j ≤ 4 * n ^ 2 → Lev ε E μ j w → ∀ c, (∀ s, Lev ε (F s) (μ - Pi.single s 1) (j + 2) (pr s (Pi.single c w))) ∧ ∑ s, ‖pr s (Pi.single c w)‖ ^ 2 ≤ (6 * bv) ^ (2 * (n + 1 - kk)) * ‖w‖ ^ 2 := by
  intro M _ _ n ε E N _ _ F io pr μ kk j bv w h1 h2 h3 h4 h5 h6 c
  exact ⟨GlobalTheory.T.unitary_glModule_proj_dual_tensor_level_add_two M n ε E N F io pr μ kk j bv w h1 h2 h3 h4 h5 h6 c,
    GlobalTheory.T.sum_normSq_projections_tensor_unitary_gl_le M n ε E N F io pr μ kk j bv w h1 h2 h3 h4 h5 h6 c⟩

end GlobalTheory
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.isFRep_exteriorPower_standardRep : ∀ (k r : ℕ) (l : ℕ), IsFRep (k := k) (r := r) (cmp l) (cmp l (Formalism.QuantumDeterminants.Hpk k r)) l := by
  first | exact @GlobalTheory.WedgeFRep.isFRep_cmp | exact GlobalTheory.WedgeFRep.isFRep_cmp | (intros; apply GlobalTheory.WedgeFRep.isFRep_cmp <;> assumption)
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.complexifiedDerivedAction_lieHom_gramAdjoint : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → (∀ Y, ∀ v ∈ R.sm, R.dC Y v ∈ R.sm) ∧ (∀ Y (a : ℂ), ∀ v ∈ R.sm, ∀ w ∈ R.sm, R.dC Y (a • v + w) = a • R.dC Y v + R.dC Y w) ∧ (∀ Y Z (a : ℂ), ∀ v ∈ R.sm, R.dC (a • Y + Z) v = a • R.dC Y v + R.dC Z v) ∧ (∀ X, PI.UpqRep.InLieHpk k r X → ∀ v ∈ R.sm, R.dC X v = PI.UpqRep.dsig (k := k) (r := r) R.σ X v) ∧ (∀ Y Z, ∀ v ∈ R.sm, R.dC Y (R.dC Z v) - R.dC Z (R.dC Y v) = R.dC (Y * Z - Z * Y) v) ∧ ∀ Y, ∀ v ∈ R.sm, ∀ w ∈ R.sm, ⟪R.dC Y v, w⟫_ℂ = ⟪v, R.dC ((Formalism.QuantumDeterminants.Hpk k r) * Yᴴ * (Formalism.QuantumDeterminants.Hpk k r)) w⟫_ℂ := by
  first | exact @GlobalTheory.ComplexifiedAction.complexified_action | exact GlobalTheory.ComplexifiedAction.complexified_action | (intros; apply GlobalTheory.ComplexifiedAction.complexified_action <;> assumption)
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.smooth_maps_closure : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (mu' mu'' : Fin (2 * r + k + 1) → ℝ) (R R' R'' : Rep k r), R.IsDS ε mu → R'.IsDS ε mu' → R''.IsDS ε mu'' → (∀ g ∈ GG k r, SmMap R R (fun v => R.σ g v)) ∧ (∀ (T : R.H → R'.H) (T' : R'.H → R''.H), SmMap R R' T → SmMap R' R'' T' → SmMap R R'' (fun v => T' (T v))) ∧ (∀ (T T' : R.H → R'.H) (a : ℂ), SmMap R R' T → SmMap R R' T' → SmMap R R' (fun v => a • T v + T' v)) ∧ ∀ (Wp : Type) [NormedAddCommGroup Wp] (T : R.H → R'.H) (Bm : R'.H → Wp), SmMap R R' T → PI.BesselMapUniq.IsCWCont (k := k) (r := r) R'.σ Bm → PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ (fun v => Bm (T v)) := by
  first | exact @GlobalTheory.SmMapAct.smMap_act | exact GlobalTheory.SmMapAct.smMap_act | (intros; apply GlobalTheory.SmMapAct.smMap_act <;> assumption)
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.DualEmb

open PI.UpqRep GlobalTheory.DerivedAction

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem hasDerivAt_inv_exp_entry (X : Mx k r) (j c : Fin (2 * r + k + 1)) :
    HasDerivAt (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X))⁻¹ j c) (-X j c) 0 := by
  have h := Formalism.REAL.hasDerivAt_mul_exp_smul_zero 1 (-X)
  simp only [Matrix.one_mul] at h
  have h2 : HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • (-X)) j c) ((-X) j c) 0 :=
    hasDerivAt_pi.1 (hasDerivAt_pi.1 h j) c
  have e : (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X))⁻¹ j c) =
      fun t : ℝ => NormedSpace.exp ((t : ℂ) • (-X)) j c := by
    funext t
    rw [smul_neg, Matrix.exp_neg]
  rw [e]
  exact h2

theorem lie_part₁ (Y : Mx k r) :
    InLieHpk k r ((1 / 2 : ℂ) • (Y + -(Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r))) := by
  have hh : (Formalism.QuantumDeterminants.Hpk k r)ᴴ = Formalism.QuantumDeterminants.Hpk k r := Formalism.QuantumDeterminants.GBasic.Hpk_herm k r
  have hs : Formalism.QuantumDeterminants.Hpk k r * Formalism.QuantumDeterminants.Hpk k r = 1 := Formalism.QuantumDeterminants.GBasic.Hpk_sq k r
  show (_ : Mx k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r + Formalism.QuantumDeterminants.Hpk k r * _ = 0
  generalize Formalism.QuantumDeterminants.Hpk k r = H at hh hs
  have hs' : ∀ A : Mx k r, H * (H * A) = A := fun A => by rw [← Matrix.mul_assoc, hs, Matrix.one_mul]
  have h2 : star (1 / 2 : ℂ) = 1 / 2 := by simp
  simp only [conjTranspose_smul, conjTranspose_add, conjTranspose_neg, conjTranspose_mul,
    conjTranspose_conjTranspose, hh, h2, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add,
    Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc, hs, hs', Matrix.mul_one]
  module

theorem lie_part₂ (Y : Mx k r) :
    InLieHpk k r ((1 / (2 * Complex.I)) • (Y - -(Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r))) := by
  have hh : (Formalism.QuantumDeterminants.Hpk k r)ᴴ = Formalism.QuantumDeterminants.Hpk k r := Formalism.QuantumDeterminants.GBasic.Hpk_herm k r
  have hs : Formalism.QuantumDeterminants.Hpk k r * Formalism.QuantumDeterminants.Hpk k r = 1 := Formalism.QuantumDeterminants.GBasic.Hpk_sq k r
  show (_ : Mx k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r + Formalism.QuantumDeterminants.Hpk k r * _ = 0
  generalize Formalism.QuantumDeterminants.Hpk k r = H at hh hs
  have hs' : ∀ A : Mx k r, H * (H * A) = A := fun A => by rw [← Matrix.mul_assoc, hs, Matrix.one_mul]
  have h2 : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by simp
  simp only [conjTranspose_smul, conjTranspose_sub, conjTranspose_neg, conjTranspose_mul,
    conjTranspose_conjTranspose, hh, h2, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc, hs, hs', Matrix.mul_one]
  module

theorem io_dsig (hK : PI.KFinSmooth) {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ} {R : Rep k r}
    (hR : R.IsDS ε mu) {RI : Fin (2 * r + k + 1) → Rep k r}
    {muI : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℝ}
    {io : ∀ s, Fin (2 * r + k + 1) → (RI s).H → R.H} {pr : ∀ s, Fin (2 * r + k + 1) → R.H → (RI s).H}
    (hI : ∀ s, (RI s).IsDS ε (muI s)) (hT : TensRaw dualM R RI io pr) (s : Fin (2 * r + k + 1))
    {X : Mx k r} (hX : InLieHpk k r X) {y : (RI s).H} (hy : y ∈ (RI s).sm) (c : Fin (2 * r + k + 1)) :
    io s c (dsig (k := k) (r := r) (RI s).σ X y) =
      dsig (k := k) (r := r) R.σ X (io s c y) - ∑ j, X j c • io s j y := by
  have hL := (GlobalTheory.cwCont_continuousOn_hasDerivAt hK k r ε (muI s) (RI s) (hI s) R.H (io s c) (hT.io_sm s c).add
    (hT.io_sm s c).smul ((hT.io_sm s c).cont [] (by simp)) y hy).2 X hX
  have h1 : R.σ 1 = 1 := (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.sigma_facts hR.2).1
  have e : (fun t : ℝ => io s c ((RI s).σ (NormedSpace.exp ((t : ℂ) • X)) y)) =
      fun t : ℝ => ∑ j, (NormedSpace.exp ((t : ℂ) • X))⁻¹ j c •
        R.σ (NormedSpace.exp ((t : ℂ) • X)) (io s j y) := by
    funext t
    exact congrFun (hT.io_eq s _ (exp_mem hX t) y hy) c
  rw [e] at hL
  have hR' := HasDerivAt.fun_sum (u := Finset.univ) fun j _ =>
    (hasDerivAt_inv_exp_entry X j c).fun_smul (hasDerivAt_dsig hX ((hT.io_sm s j).mem y hy))
  rw [hL.unique hR']
  simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, inv_one, h1, one_apply_eq_self,
    Finset.sum_add_distrib, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, neg_smul, Finset.sum_neg_distrib, sub_eq_add_neg]

end GlobalTheory.DualEmb

namespace GlobalTheory

open DualEmb

theorem dualTens_io_dC : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ (RI : Fin (2 * r + k + 1) → Rep k r) (muI : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℝ) (io : ∀ s, Fin (2 * r + k + 1) → (RI s).H → R.H) (pr : ∀ s, Fin (2 * r + k + 1) → R.H → (RI s).H), (∀ s, (RI s).IsDS ε (muI s)) → TensRaw dualM R RI io pr → ∀ s Y, ∀ y ∈ (RI s).sm, ∀ c, io s c ((RI s).dC Y y) = R.dC Y (io s c y) - ∑ j, Y j c • io s j y := by
  intro hK k r ε mu R hR RI muI io pr hI hT s Y y hy c
  have h1 := lie_part₁ Y
  have h2 := lie_part₂ Y
  have hY : Y = (1 / 2 : ℂ) • (Y + -(Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r)) +
      Complex.I • ((1 / (2 * Complex.I)) • (Y - -(Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r))) := by
    have hI : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by
      field_simp
    rw [smul_smul, hI]
    module
  unfold Rep.dC
  generalize (1 / 2 : ℂ) • (Y + -(Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r)) = X₁ at h1 hY ⊢
  generalize (1 / (2 * Complex.I)) • (Y - -(Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r)) = X₂ at h2 hY ⊢
  have m1 := DerivedAction.dsig_smooth (hI s).2 h1 hy
  have m2 := DerivedAction.dsig_smooth (hI s).2 h2 hy
  rw [(hT.io_sm s c).add _ m1 _ ((RI s).smSub.smul_mem _ m2), (hT.io_sm s c).smul _ _ m2,
    io_dsig hK hR hI hT s h1 hy c, io_dsig hK hR hI hT s h2 hy c, hY]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_smul, mul_smul, Finset.sum_add_distrib,
    ← Finset.smul_sum, smul_sub]
  abel

end GlobalTheory

end
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.frechetContinuous_continuousOn_orbit_hasDerivAt : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (Bm : R.H → V), (∀ v ∈ R.sm, ∀ w ∈ R.sm, Bm (v + w) = Bm v + Bm w) → (∀ (a : ℂ), ∀ v ∈ R.sm, Bm (a • v) = a • Bm v) → PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ Bm → ∀ v ∈ R.sm, ContinuousOn (fun g => Bm (R.σ g v)) (GG k r) ∧ ∀ X, PI.UpqRep.InLieHpk k r X → HasDerivAt (fun t : ℝ => Bm (R.σ (NormedSpace.exp ((t : ℂ) • X)) v)) (Bm (PI.UpqRep.dsig (k := k) (r := r) R.σ X v)) 0 := by
  first | exact @GlobalTheory.cwCont_continuousOn_hasDerivAt | exact GlobalTheory.cwCont_continuousOn_hasDerivAt | (intros; apply GlobalTheory.cwCont_continuousOn_hasDerivAt <;> assumption)
end

section

set_option autoImplicit false

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory

theorem card_sigma_fibre {A B : Type} [Fintype A] (m : A → ℕ) (ty : A ≃ B) (s : A) :
    (Finset.univ.filter fun c : (Σ s : A, Fin (m s)) => ty c.1 = ty s).card = m s := by
  have h : (Finset.univ.filter fun c : (Σ s : A, Fin (m s)) => ty c.1 = ty s)
      = (Finset.univ : Finset (Fin (m s))).map (Function.Embedding.sigmaMk (β := fun s => Fin (m s)) s) := by
    ext ⟨a, c⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, EmbeddingLike.apply_eq_iff_eq, Finset.mem_map,
      Function.Embedding.sigmaMk_apply]
    constructor
    · rintro rfl
      exact ⟨c, rfl⟩
    · rintro ⟨c', h⟩
      exact (congrArg Sigma.fst h).symm
  rw [h, Finset.card_map, Finset.card_univ, Fintype.card_fin]

theorem flag_of_numbering : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (A : Fin 2 → Type) [∀ g, Fintype (A g)] (m : ∀ g, A g → ℕ) (ty : ∀ g, A g ≃ ZMod d) (J : Fin 2 → Type) [∀ g, Fintype (J g)] (X : RowData C V d (fun g => Σ s : A g, Fin (m g s)) J), (∀ g x, (X.G g).ty (Sum.inl x) = ty g x.1) → (∀ g s, X.rkF g (ty g s) = m g s) ∧ ∃ F : RF.Flag X, ∀ g a c, (F.en g a c).1 = (ty g).symm a ∧ ((F.en g a c).2 : ℕ) = c := by
  intro C _ V d _ A _ m ty J _ X h
  have h1 : ∀ g s, X.rkF g (ty g s) = m g s := by
    intro g s
    unfold RowData.rkF
    simp only [h]
    convert card_sigma_fibre (m g) (ty g) s
  have h2 : ∀ g a, X.rkF g a = m g ((ty g).symm a) := by
    intro g a
    rw [← h1, Equiv.apply_symm_apply]
  refine ⟨h1, ⟨⟨fun g a c => ⟨(ty g).symm a, Fin.cast (h2 g a) c⟩, ?_, ?_⟩, fun g a c => ⟨rfl, rfl⟩⟩⟩
  · intro g a c c' hc
    exact Fin.cast_injective _ (eq_of_heq (Sigma.mk.inj hc).2)
  · intro g a c
    rw [h]
    exact Equiv.apply_symm_apply _ _

end GlobalTheory
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.exists_lowest_kFinite_vector_discreteSeries : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ (Q : Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)), PI.UpqRep.IsCayleyU k r ε Q → R.IsE Q E → ∃ w : R.smSub, ‖w‖ = 1 ∧ R.KFin (w : R.H) ∧ Formalism.REAL.KHighest ε E (Formalism.QuantumDeterminants.lowK ε mu) w ∧ FiniteDimensional ℂ (Formalism.REAL.kSpan ε E w) := by
  first | exact @GlobalTheory.LowestVector.exists_lowest_vector | exact GlobalTheory.LowestVector.exists_lowest_vector | (intros; apply GlobalTheory.LowestVector.exists_lowest_vector <;> assumption)
end
