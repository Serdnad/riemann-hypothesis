module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle010
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle225
public import Formalism.DegreeFormula.Statement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle029
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle226
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle227
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle219
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle163
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle109
public import Development.AutomorphicArithmetic.WeightCongruences.ExistsUnitEqRootOfUnityMulConjPhaseOne
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.Bundle001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle044
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle050
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.OhatCompact
public import Mathlib.Topology.Instances.Matrix
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.CartierFrobeniusFormLocal
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.TypeStar
public import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle218
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary

@[expose] public section

section

open MvPolynomial

theorem _root_.GlobalTheory.T.topDegreeFormCoeff_eq_tensorSquareTopCoefficient : ∀ (n : ℕ) (P : MvPolynomial (Fin n × Fin n) ℂ), GlobalTheory.GoodMetric.topCoeff P = GlobalTheory.GrassModel.topBig n (GlobalTheory.GrassModel.toEven n P : GlobalTheory.GrassModel.Big n) := by
  first | exact @GlobalTheory.GrassModel.TopRead.topCoeff_eq_topBig | exact GlobalTheory.GrassModel.TopRead.topCoeff_eq_topBig | (intros; apply GlobalTheory.GrassModel.TopRead.topCoeff_eq_topBig <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial MeasureTheory
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric


theorem _root_.GlobalTheory.T.chernTopForm_negativePart_eq_zero_of_nonneg_on_open : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {ι : Type} {m : ι → ℕ} (E : Fr (ratOf X) m 0) (O : X.X.Opens) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ) (R : MvPolynomial (ι × ℕ) ℝ), (∀ y ∈ ptsIn X.str σ O, ∀ c : AlgChart X.str σ X.dim, y ∈ c.e.source → ∀ A ∈ E.S (under y), 0 ≤ chernTop R (fun w => H A (c.e.symm w)) (c.e y)) → chernTopPart E H R (-1) (ptsIn X.str σ O) = 0 := by
  first | exact @GlobalTheory.chernTopPart_neg_eq_zero_of_nonneg | exact GlobalTheory.chernTopPart_neg_eq_zero_of_nonneg | (intros; apply GlobalTheory.chernTopPart_neg_eq_zero_of_nonneg <;> assumption)
end

section

open AlgebraicGeometry MvPolynomial GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)

theorem _root_.GlobalTheory.T.exists_smooth_hermitianMetric_projective_variety : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0), ∃ H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ, IsMetricOn E ⊤ H := by
  first | exact @GlobalTheory.GoodMetric.SmoothMetric.exists_isMetricOn_top | exact GlobalTheory.GoodMetric.SmoothMetric.exists_isMetricOn_top | (intros; apply GlobalTheory.GoodMetric.SmoothMetric.exists_isMetricOn_top <;> assumption)
end

section

open MvPolynomial GlobalTheory GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)

theorem _root_.GlobalTheory.T.measurable_chernPolyTopDensity : ∀ {n : ℕ} {ι : Type} {m : ι → ℕ} (R : MvPolynomial (ι × ℕ) ℝ) (G : V n → Mat m ℂ), Measurable (fun v => chernTop R G v) := by
  first | exact @GlobalTheory.ChernMeas.measurable_chernTop | exact GlobalTheory.ChernMeas.measurable_chernTop | (intros; apply GlobalTheory.ChernMeas.measurable_chernTop <;> assumption)
end

section


theorem _root_.GlobalTheory.T.curvatureFormMatrix_boundedDomainModelMetric_at_zero : ∀ (ι : Type) [Fintype ι] (p q n : ℕ) (h : Fintype.card (ι × Fin p × Fin q) = n) (τ : ι), GlobalTheory.GoodMetric.curvPoly (fun u => Matrix.transpose (Formalism.DegreeFormula.hP (Formalism.DegreeFormula.unflat (GlobalTheory.UnifDens.flatL h u) τ))⁻¹) 0 = -GlobalTheory.DomainDens.blockSym h τ := by
  first | exact @GlobalTheory.DomainDens.curvPoly_model_zero | exact GlobalTheory.DomainDens.curvPoly_model_zero | (intros; apply GlobalTheory.DomainDens.curvPoly_model_zero <;> assumption)
end

section

open Formalism.BasicNotions

theorem _root_.GlobalTheory.T.chainStepVectors_and_adjointVectors_areTheta : ∀ D : D7, Formalism.IndefR.Fin.VecThetaSD D := by
  first | exact @GlobalTheory.VecTheta.vecThetaSD | exact GlobalTheory.VecTheta.vecThetaSD | (intros; apply GlobalTheory.VecTheta.vecThetaSD <;> assumption)
end

section

open Formalism.BasicNotions

theorem _root_.GlobalTheory.T.fockPolynomialVectors_of_smoothTheta_stable : ∀ D : D7, Formalism.IndefR.Fin.PtStable D := by
  first | exact @GlobalTheory.FockTheta.ptStable | exact GlobalTheory.FockTheta.ptStable | (intros; apply GlobalTheory.FockTheta.ptStable <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift

namespace GlobalTheory.MinorHarmonic

theorem pderiv_comm {σ R : Type*} [CommRing R] (i j : σ) (f : MvPolynomial σ R) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j f) = MvPolynomial.pderiv j (MvPolynomial.pderiv i f) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p k hp =>
    have h : ∀ a b : σ, MvPolynomial.pderiv a (MvPolynomial.pderiv b (MvPolynomial.X k : MvPolynomial σ R)) = 0 := by
      intro a b
      rw [MvPolynomial.pderiv_X]
      by_cases hk : k = b
      · subst hk; simp
      · simp [Pi.single_eq_of_ne hk]
    simp only [Derivation.leibniz, map_add (f := _), smul_eq_mul, hp, h]
    ring

def ker {σ : Type*} (v : σ) : Subring (MvPolynomial σ ℂ) where
  carrier := {f | MvPolynomial.pderiv v f = 0}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    simp [Derivation.leibniz, ha, hb]
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    simp [ha, hb]
  zero_mem' := by simp
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    simp [ha]

theorem det_mem {R : Type*} [CommRing R] (S : Subring R) {k : ℕ} (M : Matrix (Fin k) (Fin k) R)
    (h : ∀ i j, M i j ∈ S) : M.det ∈ S := by
  rw [Matrix.det_apply']
  exact S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.prod_mem fun i _ => h _ _)

variable {D : D7} {m n : ℕ}

theorem varF_mem (τ τ' : D.what₂.Tau) (a : Fin m) (c : Fin n) (i j : ℕ)
    (h : τ' = τ → i = a → j = c → False) :
    (varF τ' i j : MvPolynomial (FVar D m n) ℂ) ∈ ker ((τ, a, c) : FVar D m n) := by
  classical
  unfold varF
  split_ifs with h1
  · show MvPolynomial.pderiv _ _ = 0
    apply MvPolynomial.pderiv_X_of_ne
    intro he
    simp only [Prod.mk.injEq] at he
    exact h he.1 (congrArg Fin.val he.2.1) (congrArg Fin.val he.2.2)
  · exact Subring.zero_mem _

theorem delta_mem (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ) (hpq : ∀ τ, p τ + q τ ≤ n)
    (τ : D.what₂.Tau) (a : Fin m) (c : Fin n)
    (h : ((a : ℕ) < p τ ∧ p τ ≤ c) ∨ (p τ ≤ (a : ℕ) ∧ (c : ℕ) < p τ)) :
    (delta p q ap am : MvPolynomial (FVar D m n) ℂ) ∈ ker ((τ, a, c) : FVar D m n) := by
  unfold delta deltaAt
  refine Subring.prod_mem _ fun τ' _ => Subring.mul_mem _ ?_ ?_
  · refine Subring.prod_mem _ fun i hi => Subring.pow_mem _ ?_ _
    refine det_mem _ _ fun α β => varF_mem τ τ' a c _ _ ?_
    rintro rfl h1 h2
    have := Finset.mem_range.1 hi
    have := α.2
    have := β.2
    omega
  · refine Subring.prod_mem _ fun i hi => Subring.pow_mem _ ?_ _
    refine det_mem _ _ fun α β => varF_mem τ τ' a c _ _ ?_
    rintro rfl h1 h2
    have := Finset.mem_range.1 hi
    have := hpq τ'
    omega

theorem laplacian_delta : ∀ (D : D7) (m n : ℕ) (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ), (∀ τ, p τ + q τ ≤ n) → ∀ τ (a b : Fin m), p τ ≤ (a : ℕ) → (b : ℕ) < p τ → ∑ c : Fin n, MvPolynomial.pderiv (τ, a, c) (MvPolynomial.pderiv (τ, b, c) (delta p q ap am : PolF D m n)) = 0 := by
  intro D m n p q ap am hpq τ a b ha hb
  refine Finset.sum_eq_zero fun c _ => ?_
  rcases lt_or_ge (c : ℕ) (p τ) with hc | hc
  · rw [pderiv_comm]
    have : MvPolynomial.pderiv (τ, a, c) (delta p q ap am : PolF D m n) = 0 :=
      delta_mem p q ap am hpq τ a c (Or.inr ⟨ha, hc⟩)
    rw [this, map_zero]
  · have : MvPolynomial.pderiv (τ, b, c) (delta p q ap am : PolF D m n) = 0 :=
      delta_mem p q ap am hpq τ b c (Or.inl ⟨hb, hc⟩)
    rw [this, map_zero]

end GlobalTheory.MinorHarmonic

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.EtaT

theorem card_above {F L : Type} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
    (v : HeightOneSpectrum (𝓞 F)) :
    (_root_.Formalism.L2.Host.aboveF (L := L) F v).card = (Ideal.primesOver v.asIdeal (𝓞 L)).ncard := by
  rw [← Set.ncard_coe_finset, ← Set.ncard_image_of_injective _
    (f := HeightOneSpectrum.asIdeal) (fun _ _ h => HeightOneSpectrum.ext h)]
  congr 1
  ext Q
  simp only [_root_.Formalism.L2.Host.aboveF, Set.Finite.coe_toFinset, Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨P, rfl, rfl⟩
    exact ⟨P.isPrime, ⟨rfl⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨Q, h1, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩,
      HeightOneSpectrum.ext h2.over.symm, rfl⟩

private theorem card_above_of_prime {R : Ranks} (H : Formalism.BasicNotions.Host R) (l : ℕ) (hp : l.Prime) (hl : l ∣ H.condN)
    (P : HeightOneSpectrum (𝓞 H.E)) (hP : ((l : ℕ) : 𝓞 H.E) ∈ P.asIdeal) :
    (_root_.Formalism.L2.Host.aboveF (L := H.E) H.F (P.under (𝓞 H.F))).card = 2 := by
  have : Fact l.Prime := ⟨hp⟩
  have hPp := P.isPrime
  have hPZ : P.asIdeal.LiesOver (Ideal.span {(l : ℤ)}) := by
    have hm : (Ideal.span {(l : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
    refine ⟨hm.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_⟩
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
    exact hP
  have he := H.der.eta.2.2 l hl P.asIdeal
  change (if (Ideal.primesOver (P.under (𝓞 H.F)).asIdeal (𝓞 H.E)).ncard = 2 then (1 : ℤ) else -1) = 1 at he
  rw [card_above]
  by_contra hc
  rw [if_neg hc] at he
  exact absurd he (by decide)

private theorem exists_prime_mem {A : Type} [CommRing A] (P : Ideal A) (hP : P.IsPrime) (N : ℕ) (hN : N ≠ 0)
    (h : (N : A) ∈ P) : ∃ l : ℕ, l.Prime ∧ l ∣ N ∧ (l : A) ∈ P := by
  induction N using induction_on_primes with
  | zero => exact absurd rfl hN
  | one => exact absurd (P.eq_top_iff_one.2 (by simpa using h)) hP.ne_top
  | prime_mul p a hp ih =>
    rw [Nat.cast_mul] at h
    rcases hP.mem_or_mem h with h | h
    · exact ⟨p, hp, Dvd.intro _ rfl, h⟩
    · obtain ⟨l, h1, h2, h3⟩ := ih (fun h0 => hN (by rw [h0, mul_zero])) h
      exact ⟨l, h1, h2.mul_left _, h3⟩


open Classical in
theorem etaT_exists : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R), _root_.Formalism.L2.Host.EtaTExists H := by
  intro R H
  obtain ⟨c, hc, hcm, hunr, -, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  obtain ⟨χ, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_unramified_resEta_alt H.F H.E c (R.Psi) (_root_.Formalism.L2.Host.embPsi H) hcm hunr (GlobalTheory.T.quadraticChar_product_formula_CM_host R H)
    (fun _ => 1) (fun _ => odd_one) (fun ζ hζ => by
      obtain ⟨δ, hδ, hval, hprod⟩ := UpperTheory.exists_unit_eq_rootOfUnity_mul_conj_phase_one R H R.Psi (Equiv.refl _) ζ hζ
      refine ⟨δ, by rw [hc]; exact hδ, fun P hP => ?_, ?_⟩
      · have hn : ((H.condN : ℕ) : 𝓞 H.E) ∉ P.asIdeal := fun hm => by
          obtain ⟨l, hl, hlN, hlP⟩ := exists_prime_mem P.asIdeal P.isPrime H.condN H.condN_ne_zero hm
          rw [card_above_of_prime H l hl hlN P hlP] at hP
          exact absurd hP (by decide)
        have h0 : _root_.Formalism.L2.Host.ordF P δ = 0 := by simp [_root_.Formalism.L2.Host.ordF, hval P hn]
        rw [h0]
        exact Even.zero
      · simp only [zpow_one]
        exact hprod)
  exact ⟨χ, h1, h2, h3, h4⟩

end GlobalTheory.Mem.EtaT
end

section

open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL


theorem _root_.GlobalTheory.T.strongApproximation_upperUnitriangular_finiteAdeles : PIW.ClassFinD.UnipApprox := by
  first | exact @GlobalTheory.UnipApproxGL.unipApprox | exact GlobalTheory.UnipApproxGL.unipApprox | (intros; apply GlobalTheory.UnipApproxGL.unipApprox <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL


theorem _root_.GlobalTheory.T.iwasawaDecomposition_finiteAdeles_GL : PIW.ClassFinD.IwasawaAf := by
  first | exact @GlobalTheory.IwasawaFinAd.iwasawaAf | exact GlobalTheory.IwasawaFinAd.iwasawaAf | (intros; apply GlobalTheory.IwasawaFinAd.iwasawaAf <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory

theorem isCompact_matInt_set (F : Type) [Field F] [NumberField F] (n : ℕ) :
    IsCompact {M : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F) | PIW.ClassFinD.MatInt M} := by
  have hO : IsCompact ((PIW.ClassFinD.Ohat F : Subring (FiniteAdeleRing (𝓞 F) F)) :
      Set (FiniteAdeleRing (𝓞 F) F)) := PI.WAU.isCompact_Ohat (F := F)
  have h := isCompact_univ_pi (fun _ : Fin n => isCompact_univ_pi (fun _ : Fin n => hO))
  have he : {M : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F) | PIW.ClassFinD.MatInt M} =
      Set.univ.pi (fun _ : Fin n => Set.univ.pi (fun _ : Fin n =>
        ((PIW.ClassFinD.Ohat F : Subring (FiniteAdeleRing (𝓞 F) F)) : Set (FiniteAdeleRing (𝓞 F) F)))) := by
    ext M
    exact ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
  rw [he]
  exact h

theorem isCompact_KGL (F : Type) [Field F] [NumberField F] (n : ℕ) :
    IsCompact (PIW.ClassFinD.KGL F n : Set (GL (Fin n) (FiniteAdeleRing (𝓞 F) F))) := by
  have hA := isCompact_matInt_set F n
  have hA' := (MulOpposite.opHomeomorph
    (M := Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F))).symm.isCompact_preimage.2 hA
  have h := (Units.isClosedEmbedding_embedProduct
    (α := Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F))).isCompact_preimage (hA.prod hA')
  convert h using 1
  ext g
  exact Iff.rfl

end GlobalTheory
end
