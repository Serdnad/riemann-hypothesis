module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2710
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjSpaceStandardChartFubiniStudy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1190
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1382
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle233
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle039
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1383
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2978
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2914
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.InterNumConsEqCokernel
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2937
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1746
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2915
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.KrullDimension.PID
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.Bundle001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle041
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
open ReciprocityTheory.AnForm.M
open GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PSpaceDeg

theorem ringKrullDim_eq_one (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] :
    ringKrullDim k = 1 := by
  rw [ReciprocityTheory.CA.ringKrullDim_eq_of_isIntegral_of_injective (A := ℤ) (B := k)
    (algebraMap ℤ k).injective_int]
  exact IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField

theorem isArithVar (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] (D : ℕ) :
    IsArithVar (PSpace.str k D) D :=
  ProjModel.isArithVar_pspace k (ringKrullDim_eq_one k) D

theorem injective_ringHom {k : Type} [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k]
    (ψ : k →+* ℂ) : Function.Injective ψ := by
  refine (RingHom.injective_iff_ker_eq_bot ψ).2 (Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_)
  change Ideal.comap (algebraMap ℤ k) (RingHom.ker ψ) = ⊥
  rw [RingHom.comap_ker]
  exact (RingHom.injective_iff_ker_eq_bot _).1 (RingHom.injective_int _)

def ringHomEquiv (k K : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] [Field K]
    [Algebra k K] [IsFractionRing k K] : (k →+* ℂ) ≃ (K →+* ℂ) where
  toFun ψ := IsFractionRing.lift (injective_ringHom ψ)
  invFun φ := φ.comp (algebraMap k K)
  left_inv ψ := by
    ext x
    rw [RingHom.comp_apply]
    exact IsFractionRing.lift_algebraMap (injective_ringHom ψ) x
  right_inv φ := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors k) (RingHom.ext fun x => ?_)
    rw [RingHom.comp_apply, RingHom.comp_apply]
    exact IsFractionRing.lift_algebraMap (injective_ringHom (φ.comp (algebraMap k K))) x

end GlobalTheory.PSpaceDeg

namespace GlobalTheory.PSpaceDeg

theorem finrank_fractionRing (k K : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k]
    [Field K] [Algebra k K] [IsFractionRing k K] [CharZero K] :
    Module.finrank ℚ K = Module.finrank ℤ k ∧ FiniteDimensional ℚ K := by
  haveI : Module.Free ℤ k := Module.free_of_finite_type_torsion_free'
  haveI : @IsScalarTower ℤ ℚ K Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)
  haveI : IsLocalization (Algebra.algebraMapSubmonoid k (nonZeroDivisors ℤ)) K := inferInstance
  let b := Module.Free.chooseBasis ℤ k
  let b' := b.localizationLocalization ℚ (nonZeroDivisors ℤ) K
  exact ⟨(Module.finrank_eq_card_basis b').trans (Module.finrank_eq_card_basis b).symm,
    Module.Finite.of_basis b'⟩

end GlobalTheory.PSpaceDeg

namespace GlobalTheory.PSpaceDeg

theorem card_ringHom (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] :
    Nat.card (k →+* ℂ) = Module.finrank ℤ k := by
  haveI : CharZero (FractionRing k) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective k (FractionRing k))
  obtain ⟨h1, h2⟩ := finrank_fractionRing k (FractionRing k)
  haveI : NumberField (FractionRing k) := ⟨⟩
  rw [Nat.card_congr (ringHomEquiv k (FractionRing k)), Nat.card_eq_fintype_card,
    NumberField.Embeddings.card, h1]

end GlobalTheory.PSpaceDeg

namespace GlobalTheory.PSpaceDeg

open Set
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open ReciprocityTheory.L2DbarEstimates (V)

theorem exists_stdChart (k : Type) [CommRing k] (σ : k →+* ℂ) (N : ℕ) :
    ∃ (c : AlgChart (PSpace.str k N) σ N) (i : (ProjSpace.hermitianTwistingSheaf k N).B.ι),
      c.e.source = ptsIn (PSpace.str k N) σ (ProjSpace.chart k N 0) ∧ c.e.target = Set.univ ∧
      c.e.source ⊆ ptsIn (PSpace.str k N) σ ((ProjSpace.hermitianTwistingSheaf k N).B.U i) ∧
      ∀ v, ((ProjSpace.hermitianTwistingSheaf k N).φ σ).φ i (c.e.symm v) = Real.log (1 + ‖v‖ ^ 2) := by
  obtain ⟨c, h₁, h₂, h₃⟩ := StdProjChart.exists_of_bijective (p := PSpace.str k N) σ
    (ProjSpace.isAffineOpen_chart k N 0) _ (StdProjChart.bijective_ratio k N 0)
  refine ⟨c, (0 : Fin (N + 1)), h₁, h₂, h₁.le, fun v => ?_⟩
  have hv : c.e.symm v ∈ ptsIn (PSpace.str k N) σ (ProjSpace.chart k N 0) :=
    h₁ ▸ c.e.map_target (h₂ ▸ trivial)
  have h := Weight.fsBasis_φ (p := PSpace.str k N) (σ := σ) (ProjSpace.O1_isLB k N)
    (ProjSpace.coord k N) (ProjSpace.iSup_nonzeroLocus_coord k N) 1 (by simp) (0 : Fin (N + 1))
    (c.e.symm v)
  refine h.trans ?_
  have h0 : ev (PSpace.str k N) σ (ProjSpace.chart k N 0) (ProjSpace.ratio k N 0 0)
      (c.e.symm v) = 1 := by
    simp only [ProjSpace.ratio, ProjSpace.ratioOn_self]
    rw [ev_eq hv, map_one]
  have key : ∑ a : Fin (N + 1), ‖ev (PSpace.str k N) σ (ProjSpace.chart k N 0)
      (ProjSpace.ratio k N 0 a) (c.e.symm v)‖ ^ 2 = 1 + ‖v‖ ^ 2 := by
    rw [Fin.sum_univ_succ, h0, EuclideanSpace.norm_sq_eq]
    simp only [Fin.succAbove_zero] at h₃
    simp only [h₃, norm_one, one_pow]
  rw [← key]
  simp [Matrix.one_apply, ev, ProjSpace.O1]

theorem chern_mass_hermitian_O_one_projective (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k]
    (N : ℕ) (σ : k →+* ℂ) :
    ((ProjSpace.hermitianTwistingSheaf k N).φ σ).chernPart N 1 Set.univ = 1 ∧
      ((ProjSpace.hermitianTwistingSheaf k N).φ σ).chernPart N (-1) Set.univ = 0 := by
  have hA := isArithVar k N
  have hproj : IsProjOver (PSpace.str k N) := hA.isProjOver
  haveI : IsIntegral (PSpace k N) := ProjSpace.isIntegral_of_isDomain k N
  haveI := CxPts.secondCountableTopology_of_isProjOver (σ := σ) hproj
  have hC : ((ProjSpace.hermitianTwistingSheaf k N).φ σ).IsCInf := (ProjSpace.hermitianTwistingSheaf k N).cInf _
  have hSP : ((ProjSpace.hermitianTwistingSheaf k N).φ σ).SemiPosReg N :=
    (HermLB.semiPos_fs _ _ _ _ _ _ : (ProjSpace.hermitianTwistingSheaf k N).SemiPos N) _
  refine ⟨?_, by rw [Weight.chernPart_neg_eq_zero hC hSP]; rfl⟩
  obtain ⟨c, i, hsrc, htgt, hsub, hφv⟩ := exists_stdChart k σ N
  have hmem : c.e.symm 0 ∈ c.e.source := c.e.map_target (htgt ▸ mem_univ _)
  have hgen : genericPoint (PSpace k N) ∈ ProjSpace.chart k N 0 := by
    have h0 : c.e.symm 0 ∈ ptsIn (PSpace.str k N) σ (ProjSpace.chart k N 0) := hsrc ▸ hmem
    exact ((genericPoint_spec (PSpace k N)).mem_open_set_iff (ProjSpace.chart k N 0).isOpen).2
      ⟨_, by simp, mem_ptsIn.1 h0⟩
  have hnull := ChernNull.chernPart_over_closed hA ((ProjSpace.chart k N 0 : (PSpace k N).Opens) : Set (PSpace k N))ᶜ
    (ProjSpace.chart k N 0).isOpen.isClosed_compl (by simpa using hgen) σ ((ProjSpace.hermitianTwistingSheaf k N).φ σ) 1
  have hcX : (ptsIn (PSpace.str k N) σ (ProjSpace.chart k N 0))ᶜ =
      {y : CxPts (PSpace.str k N) σ | y.1 (IsLocalRing.closedPoint ℂ) ∈
        ((ProjSpace.chart k N 0 : (PSpace k N).Opens) : Set (PSpace k N))ᶜ} := by
    ext y
    simp [mem_ptsIn]
  rw [← hcX, ← hsrc] at hnull
  have hmeas : MeasurableSet c.e.source := c.e.open_source.measurableSet
  rw [← union_compl_self c.e.source, measure_union disjoint_compl_right hmeas.compl, hnull, add_zero,
    Weight.chernPart_apply hC 1 c hmeas subset_rfl, c.e.image_source_eq_target, htgt,
    Measure.restrict_univ]
  refine Eq.trans (lintegral_congr fun v => ?_) (lintegral_fubiniStudy_density_eq_one N)
  have hv : c.e.symm v ∈ c.e.source := c.e.map_target (htgt ▸ mem_univ _)
  rw [AlgChart.chernDens_eq c hC hv (hsub hv), AlgChart.hess, c.e.right_inv (htgt ▸ mem_univ _)]
  have hf : (fun w => ((((ProjSpace.hermitianTwistingSheaf k N).φ σ).φ i (c.e.symm w) : ℝ) : ℂ)) =
      fun w => ((Real.log (1 + ‖w‖ ^ 2) : ℝ) : ℂ) := funext fun w => by rw [hφv w]
  rw [hf, FSDet.det_fubiniStudy_hess N v]
  simp

end GlobalTheory.PSpaceDeg

namespace GlobalTheory.PSpaceDeg

theorem degree_hermitian_O_one_projective (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] (D : ℕ) :
    gdeg (ProjSpace.hermitianTwistingSheaf k D) D = Nat.card (k →+* ℂ) := by
  have hσ : ∀ σ : k →+* ℂ, ((ProjSpace.hermitianTwistingSheaf k D).φ σ).chernInt D Set.univ (fun _ => 1) = 1 := by
    intro σ
    obtain ⟨h1, h0⟩ := chern_mass_hermitian_O_one_projective k D σ
    rw [GdegPullProof.chernInt_one, h1, h0]
    simp
  haveI : Finite (k →+* ℂ) := by
    haveI : CharZero (FractionRing k) :=
      charZero_of_injective_algebraMap (IsFractionRing.injective k (FractionRing k))
    haveI : FiniteDimensional ℚ (FractionRing k) := (finrank_fractionRing k (FractionRing k)).2
    haveI : NumberField (FractionRing k) := ⟨⟩
    exact Finite.of_equiv _ (ringHomEquiv k (FractionRing k)).symm
  haveI := Fintype.ofFinite (k →+* ℂ)
  simp only [gdeg, chInt, hσ]
  rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card,
    nsmul_eq_mul, mul_one]

theorem main : ∀ (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] (D : ℕ),
    IsArithVar (PSpace.str k D) D ∧ gdeg (ProjSpace.hermitianTwistingSheaf k D) D = Nat.card (k →+* ℂ) ∧
      Nat.card (k →+* ℂ) = Module.finrank ℤ k :=
  fun k _ _ _ _ D => ⟨isArithVar k D, degree_hermitian_O_one_projective k D, card_ringHom k⟩

end GlobalTheory.PSpaceDeg
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.exists_blowup_model_regular_function_or_inverse : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ g : X.functionField, g ≠ 0 → ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (π : Y ⟶ X) (φ : X.functionField →+* Y.functionField), IsArithVar (π ≫ p) D ∧ IsModel π φ ∧ ∀ y : Y, RegAt y (φ g) ∨ RegAt y (φ g)⁻¹ := by
  first | exact @GlobalTheory.RegOrInvModel.exists_model_regAt_or_regAt_inv | exact GlobalTheory.RegOrInvModel.exists_model_regAt_or_regAt_inv | (intros; apply GlobalTheory.RegOrInvModel.exists_model_regAt_or_regAt_inv <;> assumption)
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GoodTop

theorem topCoeff_finsum {n : ℕ} {ι : Type} (s : Finset ι) (f : ι → MvPolynomial (Fin n × Fin n) ℂ) :
    topCoeff (∑ i ∈ s, f i) = ∑ i ∈ s, topCoeff (f i) := by
  simp only [topCoeff, MvPolynomial.coeff_sum, Finset.mul_sum]
  exact Finset.sum_comm

theorem topCoeff_const_mul {n : ℕ} (a : ℂ) (P : MvPolynomial (Fin n × Fin n) ℂ) :
    topCoeff (MvPolynomial.C a * P) = a * topCoeff P := by
  simp only [topCoeff, MvPolynomial.coeff_C_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem topCoeff_chernPoly_eq_mixTop : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (G : V n → Matrix r r ℂ) (v : V n),
    topCoeff (chernPoly G v n) = mixTop fun _ => curvAt G v := by
  intro n r _ _ G v
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have key := GlobalTheory.T.factorial_mul_coeff_charpolyRev_neg_eq_sum (curvPoly G v) n
  have h1 : (n.factorial : ℂ) * topCoeff (chernPoly G v n) =
      ∑ p : Fin n → r, ∑ π : Equiv.Perm (Fin n), ∑ u : Equiv.Perm (Fin n),
        ((Equiv.Perm.sign π : ℤ) : ℂ) * ((Equiv.Perm.sign u : ℤ) : ℂ) *
          (Matrix.of fun i b => curvAt G v (u i) b (p i) (p (π i))).det := by
    rw [← topCoeff_const_mul, map_natCast, chernPoly, key, topCoeff_finsum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [topCoeff_finsum]
    refine Finset.sum_congr rfl fun π _ => ?_
    rw [← map_intCast (MvPolynomial.C : ℂ →+* MvPolynomial (Fin n × Fin n) ℂ), topCoeff_const_mul]
    have hp : (∏ i, curvPoly G v (p i) (p (π i))) = ∏ i, ∑ a, ∑ b,
        MvPolynomial.C (curv G v (coordVec a) (coordVec b) (p i) (p (π i))) * MvPolynomial.X (a, b) := by
      simp [curvPoly]
    rw [hp, GlobalTheory.T.topDegreeFormCoeff_prod_oneOneForms, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp only [curvAt, mul_assoc]
  rw [mixTop, ← h1, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]

end GlobalTheory.GoodTop
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHtVert

theorem isEmpty_cxPts {k : Type} [CommRing k] {Z : Scheme.{0}} (q : Z ⟶ Sp k) (σ : k →+* ℂ) (κ : Type) [Field κ]
    [Finite κ] [Algebra κ Γ(Z, ⊤)] : IsEmpty (CxPts q σ) := by
  refine ⟨fun y => ?_⟩
  let f : κ →+* ℂ := (Scheme.ΓSpecIso (.of ℂ)).hom.hom.comp (y.1.appTop.hom.comp (algebraMap κ Γ(Z, ⊤)))
  have : CharZero κ := f.charZero
  exact not_finite κ

theorem mixArch_eq_zero {k : Type} [CommRing k] {Z : Scheme.{0}} [IsIntegral Z] {q : Z ⟶ Sp k}
    (h : ∀ σ : k →+* ℂ, IsEmpty (CxPts q σ)) {e : ℕ} (L : Fin e → HermLB q) (M : HermLB q)
    {r : M.B.ι → Z.functionFieldˣ} (hr : IsRatSec M.B r) : mixArch L M hr = 0 := by
  have h0 : ∀ (L' : HermLB q), L'.archInt M e hr = 0 := by
    intro L'
    refine finsum_eq_zero_of_forall_eq_zero fun σ => ?_
    have := h σ
    simp [Weight.chernInt, MeasureTheory.integral_of_isEmpty]
  simp [mixArch, FibreProj.pol, h0]

end GlobalTheory.MixHtVert

namespace GlobalTheory.MixHtVert

theorem finite_Γ {Z : Scheme.{0}} [IsIntegral Z] (κ : Type) [Field κ] [Finite κ] [Algebra κ Γ(Z, ⊤)] [IsAffine Z]
    (hp : IsProjOver (strHom κ (X := Z))) (φ : Γ(Z, ⊤) →+* Z.residueField (genericPoint Z)) (hφ : Function.Bijective φ) :
    Finite Γ(Z, ⊤) := by
  have : IsProper (strHom κ (X := Z)) := (isProper_and_exists_isAmpleLB_of_isProjOver hp).1
  have h1 : (strHom κ Z).appTop.hom.FiniteType :=
    HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType) |>.1 inferInstance
  have h2 : (algebraMap κ Γ(Z, ⊤)).FiniteType := by
    have e : algebraMap κ Γ(Z, ⊤) = (strHom κ Z).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of κ)).inv.hom :=
      RingHom.ext (algebraMap_eq_strHom κ Z)
    rw [e]
    exact h1.comp (RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso _).2)
  have hft : Algebra.FiniteType κ Γ(Z, ⊤) := RingHom.finiteType_algebraMap.1 h2
  letI : Algebra κ (Z.residueField (genericPoint Z)) := (φ.comp (algebraMap κ Γ(Z, ⊤))).toAlgebra
  let ψ : Γ(Z, ⊤) →ₐ[κ] Z.residueField (genericPoint Z) := { φ with commutes' := fun _ => rfl }
  have : Algebra.FiniteType κ (Z.residueField (genericPoint Z)) := Algebra.FiniteType.of_surjective ψ hφ.2
  have : Module.Finite κ (Z.residueField (genericPoint Z)) := finite_of_finite_type_of_isJacobsonRing _ _
  have : Finite (Z.residueField (genericPoint Z)) := Module.finite_of_finite κ
  exact Finite.of_injective φ hφ.1

end GlobalTheory.MixHtVert

namespace GlobalTheory.MixHtVert

theorem hasDim_iff {X Z : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] (d : ℕ) :
    HasDim (i (genericPoint Z)) d ↔ topologicalKrullDim Z = d := by
  have h₁ := (genericPoint_spec Z).image i.continuous
  rw [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq] at h₁
  rw [HasDim, topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding h₁.def.symm]

theorem dim_zero {X : Scheme.{0}} {Z : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] (κ : Type) [Field κ]
    [Finite κ] [Algebra κ Γ(Z, ⊤)] (h0 : topologicalKrullDim Z = (0 : ℕ))
    (hp : IsProjOver (strHom κ (X := Z))) :
    Real.log (Nat.card (X.residueField (i (genericPoint Z)))) = chi κ (structureModule Z) * Real.log (Nat.card κ) := by
  have hu (w : Z) : w = genericPoint Z := by
    have := Order.krullDim_nonpos_iff_forall_isMax.1 (show Order.krullDim (IrreducibleCloseds Z) ≤ 0
      from h0.le) ⟨closure {w}, isIrreducible_singleton.closure, isClosed_closure⟩
    exact IsGenericPoint.eq (Set.eq_univ_of_univ_subset (@this
      ⟨Set.univ, IrreducibleSpace.isIrreducible_univ Z, isClosed_univ⟩ (Set.subset_univ _))) (genericPoint_spec Z)
  have hZ : ({genericPoint Z} : Set Z) = Set.univ := Set.eq_univ_of_forall hu
  have hc : IsClosed ({genericPoint Z} : Set Z) := hZ ▸ isClosed_univ
  have := isClosed_singleton_iff_isClosedImmersion.1 hc
  have : Surjective (Z.fromSpecResidueField (genericPoint Z)) :=
    ⟨fun w => ⟨IsLocalRing.closedPoint _, (hu _).trans (hu w).symm⟩⟩
  have := isIso_of_isClosedImmersion_of_surjective (Z.fromSpecResidueField (genericPoint Z))
  have : IsAffine Z := .of_isIso (inv (Z.fromSpecResidueField (genericPoint Z)))
  have : IsIso (Z.fromSpecResidueField (genericPoint Z)).appTop := inferInstanceAs (IsIso (Scheme.Hom.app _ ⊤))
  have b₁ : Function.Bijective (i.residueFieldMap (genericPoint Z)) := by
    refine ⟨RingHom.injective _, fun a => ?_⟩
    obtain ⟨a, rfl⟩ := Z.residue_surjective _ a
    obtain ⟨b, rfl⟩ := i.stalkMap_surjective _ a
    exact ⟨X.residue _ b, by rw [← CommRingCat.comp_apply, Scheme.residue_residueFieldMap, CommRingCat.comp_apply]⟩
  have b₂ : Function.Bijective ((Z.fromSpecResidueField (genericPoint Z)).appTop ≫
      (Scheme.ΓSpecIso (Z.residueField (genericPoint Z))).hom) := ConcreteCategory.bijective_of_isIso _
  have e : Γ(Z, ⊤) ≃ X.residueField (i (genericPoint Z)) :=
    (Equiv.ofBijective _ b₂).trans (Equiv.ofBijective _ b₁).symm
  have : Finite Γ(Z, ⊤) := finite_Γ κ hp _ b₂
  rw [← Nat.card_congr e, chi_structureModule_of_isAffine, Module.natCard_eq_pow_finrank (K := κ)]
  simp

theorem isProjOver_strHom {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} (hX : IsAmb p) {Z : Scheme.{0}}
    (i : Z ⟶ X) [IsClosedImmersion i] (κ : Type) [Field κ] [Algebra κ Γ(Z, ⊤)] : IsProjOver (strHom κ (X := Z)) := by
  have := hX.finite
  obtain ⟨hpr, H, hH⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hX.isProjOver
  have : IsFinite (spMap (Int.castRingHom k)) := by
    rw [spMap, IsFinite.SpecMap_iff]
    exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
  have e : strHom κ Z ≫ spMap (Int.castRingHom κ) = i ≫ p ≫ spMap (Int.castRingHom k) :=
    specZIsTerminal.hom_ext _ _
  have : IsProper (strHom κ Z ≫ spMap (Int.castRingHom κ)) := by rw [e]; infer_instance
  have hpr' : IsProper (strHom κ (X := Z)) := IsProper.of_comp _ (spMap (Int.castRingHom κ))
  exact (isProjOver_iff_isProper_and_exists_isAmpleLB (strHom κ Z)).2 ⟨hpr', _, hH.pull_of_isClosedImmersion i⟩

end GlobalTheory.MixHtVert

namespace GlobalTheory.MixHtVert

theorem mixHt_pow_eq_topSelf : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsAmb p → ∀ (m : ℕ) T, IsMix p m T → ∀ (N : HermLB p) (d : ℕ), d ≤ m → ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] (κ : Type) [Field κ] [Finite κ] [Algebra κ Γ(Z, ⊤)], topologicalKrullDim Z = d → T d (fun _ => N) (i (genericPoint Z)) = topSelfIntersection κ (N.B.pull i) d * Real.log (Nat.card κ) := by
  intro k _ X p hA m T hT N d
  induction d with
  | zero =>
    intro _ Z i _ _ κ _ _ _ hd
    rw [hT.zero _ _ ((hasDim_iff i 0).2 hd), dim_zero i κ hd (isProjOver_strHom hA i κ), topSelf_def,
      interNum_of_isEmpty]
  | succ e ih =>
    intro hm Z i _ _ κ _ _ _ hd
    have hZa : IsAmb (i ≫ p) := hA.sub i
    have : IsNoetherian Z := hZa.isNoetherian
    have hp := isProjOver_strHom hA i κ
    have : IsProper (strHom κ (X := Z)) := (isProper_and_exists_isAmpleLB_of_isProjOver hp).1
    obtain ⟨r, hr⟩ := exists_isRatSec (N.restr i).isLB
    have hL : (N.B.pull i).IsLB := (N.restr i).isLB
    have hrec := hT.recur Z (i ≫ p) i rfl e hm hd N (fun _ => N) (N.restr i) (fun _ => N.restr i)
      (HermLB.Isometric.refl _) (fun _ => HermLB.Isometric.refl _) r hr
    have ec : (Fin.cons N (fun _ => N) : Fin (e + 1) → HermLB p) = fun _ => N :=
      funext (Fin.cases rfl fun _ => rfl)
    rw [ec] at hrec
    rw [hrec, recVal, mixArch_eq_zero (fun σ => isEmpty_cxPts (i ≫ p) σ κ), sub_zero]
    have key := GlobalTheory.ratSec_cycle_formula κ Z hp e hd.le (N.B.pull i) hL (fun _ => N.B.pull i) (fun _ => hL) r hr
    have ec' : (Fin.cons (N.B.pull i) (fun _ => N.B.pull i) : Fin (e + 1) → LB Z) = fun _ => N.B.pull i :=
      funext (Fin.cases rfl fun _ => rfl)
    rw [ec', ← topSelf_def] at key
    have hfin : Function.HasFiniteSupport fun w => (divOfRatSec hL hr).mult w *
        interNumRed κ (⟨closure {w}, isClosed_closure⟩ : Closeds _) fun _ : Fin e => N.B.pull i :=
      (CartierDiv.finite_support_mult _).subset (Function.support_mul_subset_left _ _)
    rw [key]
    have em := (AddMonoidHom.mulRight (Real.log (Nat.card κ))).comp (Int.castAddHom ℝ) |>.map_finsum hfin
    refine .trans (finsum_congr fun z => ?_) em.symm
    change ((divOfRatSec hL hr).mult z : ℝ) * _ = (((divOfRatSec hL hr).mult z * _ : ℤ) : ℝ) * _
    by_cases hz : (divOfRatSec hL hr).mult z = 0
    · simp [hz]
    rw [Int.cast_mul, mul_assoc]
    refine congrArg _ ?_
    have hdim := VdmRec.CutSec.dim_closure_of_coheight_field (strHom κ Z) hd
      (CartierDiv.coheight_eq_one_of_mult_ne_zero hz)
    obtain ⟨W, j, _, _, rfl⟩ := exists_isClosedImmersion_genericPoint z
    have hrange : Set.range j = closure {j (genericPoint W)} := by
      rw [← Set.image_singleton, j.isClosedEmbedding.closure_image_eq, (genericPoint_spec _).def, Set.image_univ]
    letI := algebraΓAlong κ j
    have hW : topologicalKrullDim W = e :=
      (topologicalKrullDim_eq_of_isEmbedding j.isClosedEmbedding.isEmbedding hrange).symm.trans hdim
    rw [← Scheme.Hom.comp_apply, ih (by omega) W (j ≫ i) κ hW, InterModel.interNumRed_eq_interNumOn _ j _ hrange,
      interNumOn_eq_interNum_pull (appTop_algebraMap_along κ j) (fun _ => hL), topSelf_def]
    congr 2
    refine interNum_congr_cls κ _ (fun _ => LB.isLB_pull N.isLB _) (fun _ => LB.isLB_pull hL _) fun _ => ?_
    rw [CechPic.cls_pull hL, CechPic.cls_pull N.isLB, CechPic.cls_pull N.isLB, CechPic.pull_comp]

end GlobalTheory.MixHtVert
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

theorem _root_.GlobalTheory.T.arith_height_pullback_residue_degree : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D E : ℕ), IsArithVar p D → IsArithVar q E → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (L : HermLB p) (h : X → ℝ) (h' : Y → ℝ), L.IsArithHeight h → (L.pull π hπ).IsArithHeight h' → ∀ (y : Y) (l : ℕ) [Fact l.Prime], Nonempty (Algebra (ZMod l) Γ(clo y, ⊤)) → h' y = (π.residueDegree y : ℝ) * h (π y) := by
  first | exact @GlobalTheory.ProjFormulaVert.height_pull_vertical | exact GlobalTheory.ProjFormulaVert.height_pull_vertical | (intros; apply GlobalTheory.ProjFormulaVert.height_pull_vertical <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.mixedChernMeasure_integral_eq_genericFibre : ∀ (k K : Type) [CommRing k] [Field K] [Algebra k K] [IsFractionRing k K] (X G : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (q : G ⟶ Sp K) (j : G ⟶ X) (hp : IsPullback j q p (spMap (algebraMap k K))) (τ : K →+* ℂ) (D : ℕ), IsArithVar p D → ∀ (L : Fin D → MLine p (τ.comp (algebraMap k K))), (∀ ε : ℤˣ, Measure.map (bcPt hp.w τ) (part (fun i => (L i).bc hp.w τ) ε) = part L ε) ∧ ∀ f : CxPts p (τ.comp (algebraMap k K)) → ℝ, (Intg (fun i => (L i).bc hp.w τ) (fun y => f (bcPt hp.w τ y)) ↔ Intg L f) ∧ Mix.int (fun i => (L i).bc hp.w τ) (fun y => f (bcPt hp.w τ y)) = Mix.int L f := by
  first | exact @GlobalTheory.MixGen.part_int_generic | exact GlobalTheory.MixGen.part_int_generic | (intros; apply GlobalTheory.MixGen.part_int_generic <;> assumption)
end
