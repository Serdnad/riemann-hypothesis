module

import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle503
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle397
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle174
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle176
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle500
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle501
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowBoundsOfAllLettersThick
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle419
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle014
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle495
public import Development.AbelianVarietyTheory.Definitions.Divisors.NAInterSupSSubset
public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle504
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorsionCoinvariantsTwistedCyclotomicGenerator
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.Per.FontaineAll

noncomputable def extRep {G : Type} [Group G] {LL : Type} [Field LL] (LL' : Type) [Field LL']
    [Algebra LL LL'] {V : Type} [AddCommGroup V] [Module LL V] (ρ : Representation LL G V) :
    Representation LL' G (LL' ⊗[LL] V) where
  toFun g := (ρ g).baseChange LL'
  map_one' := by rw [map_one]; exact LinearMap.baseChange_one LL V
  map_mul' g h := by rw [map_mul]; exact LinearMap.baseChange_mul _ _

theorem fontCore_of_tied (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (hT : LocTied l P AI) (K : FinExt l) : Formalism.MainNotions.LocalSituation.fontCore (P.PD K) := by
  apply GlobalTheory.FontaineExtensionCriteria.fontCore_of_tied <;> assumption

theorem fontaine_bounds : ∀ D : D7, Formalism.MainNotions.LocalSituation.adm7 D :=
  fun D l _ K => fontCore_of_tied l (D.loc l) (D.locA l) (D.locT l) K

end GlobalTheory.Per.FontaineAll
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

noncomputable section

namespace GlobalTheory.NLink.RowCDSize

open Classical

theorem ratIn_le {x y c : ℝ} (hy : y ≤ c) (hc : 0 ≤ c) : ((Formalism.MainNotions.N.ratIn x y : ℚ) : ℝ) ≤ c := by
  by_cases h : x < y
  · exact (RowBSize.ratIn_lt h).le.trans hy
  · rw [RowBSize.ratIn_of_not_lt h]; simpa using hc

theorem one_le_hB {D : D7} (L : SizeData₂ D) : 1 ≤ TwistedPlaces.hB L := by
  unfold TwistedPlaces.hB
  have := RowBSize.one_le_b' L
  have := L.Sc_pos
  have := L.etaSz_pos
  have : (0 : ℝ) ≤ D.R.t := by positivity
  linarith

theorem etaP_nonneg {D : D7} (L : SizeData₂ D) : 0 ≤ TwistedPlaces.eta₃ L := by
  unfold TwistedPlaces.eta₃
  have := L.etaSz_pos
  positivity

theorem placeWeight_nonneg {D : D7} (L : SizeData₂ D) : 0 ≤ TwistedPlaces.wP L := by
  apply GlobalTheory.RowsThick.placeWeight_nonneg <;> assumption

theorem coreE_nonneg {D : D7} (L : SizeData₂ D) (l : ℕ) : 0 ≤ coreE L l := by
  unfold coreE
  have h1 : 0 ≤ TwistedPlaces.hB L / l := div_nonneg (by linarith [one_le_hB L]) (by positivity)
  have h2 : 0 ≤ Real.logb l (TwistedPlaces.hB L) := by
    unfold Real.logb
    exact div_nonneg (Real.log_nonneg (one_le_hB L)) (Real.log_natCast_nonneg l)
  linarith

theorem flat_nonneg {D : D7} (L : SizeData₂ D) (bd : Prop) (l : ℕ) : 0 ≤ flat L bd l := by
  unfold flat
  have := placeWeight_nonneg L
  have := etaP_nonneg L
  have := L.Sc_pos
  have := RowBSize.one_le_Lg L
  have h1 : 0 ≤ (TwistedPlaces.wP L + TwistedPlaces.eta₃ L) / l := by positivity
  have h2 : 0 ≤ TwistedPlaces.eta₃ L * (if bd then (1:ℝ) else 0) := by split_ifs <;> simp [*]
  linarith

theorem coreH_nonneg {D : D7} (L : SizeData₂ D) (l : ℕ) (lam : HeightOneSpectrum (𝓞 D.host.E)) :
    0 ≤ coreH L l lam := by
  unfold coreH
  have := RowBSize.hB_nonneg L
  positivity

theorem coreF_nonneg {D : D7} (L : SizeData₂ D) (bd : Prop) (l : ℕ) (lam : HeightOneSpectrum (𝓞 D.host.E)) :
    0 ≤ coreF L bd l lam := by
  unfold coreF
  have := flat_nonneg L bd l
  positivity

theorem coreM_nonneg {D : D7} (L : SizeData₂ D) (l : ℕ) (lam : HeightOneSpectrum (𝓞 D.host.E)) :
    0 ≤ coreM L l lam := by
  unfold coreM
  have := coreE_nonneg L l
  positivity

theorem len_le {D : D7} (L : SizeData₂ D) (HW : HWOf D.loc) (X : KillingConditions.HubData D) (R : KillingConditions.RowK) (C : ℝ)
    (hD : KillingConditions.DataAD L HW X R) (hR : R.Le C) (i : D.nd.Loc) (hI : TwistedPlaces.InertK D (D.nd.l i))
    (hB : ¬ KillingConditions.IsRowB L (D.nd.l i)) (lam : HeightOneSpectrum (𝓞 D.host.E)) :
    (tabX L X).len i lam ≤ C * coreH L (D.nd.l i) lam + C * coreF L (X.band i lam) (D.nd.l i) lam +
      C * C * coreM L (D.nd.l i) lam := by
  obtain ⟨-, -, -, -, hC1, -, h1, h2, h3, -⟩ := hR
  have hH := coreH_nonneg L (D.nd.l i) lam
  have hF := coreF_nonneg L (X.band i lam) (D.nd.l i) lam
  have hM := coreM_nonneg L (D.nd.l i) lam
  have hC0 : (0:ℝ) ≤ C := by linarith
  have h0 : 0 ≤ C * coreH L (D.nd.l i) lam + C * coreF L (X.band i lam) (D.nd.l i) lam +
      C * C * coreM L (D.nd.l i) lam := by positivity
  have key : (tabX L X).len i lam = KillingConditions.supZ i
      (fun _ => ((lenRowCD L (X.band i) R.K₁ R.K₂ R.K₃ (D.nd.l i) lam : ℚ) : ℝ)) := by
    show KillingConditions.lenR X.len0 i lam = _
    unfold KillingConditions.lenR
    congr 1
    funext π
    rw [hD.len0I i hI π lam, hD.rowCD i hI hB]
  rw [key]
  unfold KillingConditions.supZ
  split_ifs with hne
  · rw [Finset.sup'_const]
    unfold lenRowCD
    refine ratIn_le ?_ h0
    unfold bdCD
    have h4 : R.K₃ ≤ C * C := by nlinarith
    have := mul_le_mul_of_nonneg_right h1 hH
    have := mul_le_mul_of_nonneg_right h2 hF
    have := mul_le_mul_of_nonneg_right h4 hM
    linarith
  · exact h0

end GlobalTheory.NLink.RowCDSize

theorem GlobalTheory.NLink.localBoundTable_rowsCD_admissible : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (X : KillingConditions.HubData D) (R : KillingConditions.RowK) (C : ℝ), KillingConditions.DataAD L HW X R → R.Le C → TwistedPlaces.MediumInertPrimeLengthBound L (tabX L X) C ∧ TwistedPlaces.SmallInertPrimeSmallOrderLengthBound L (tabX L X) C := by
  intro D L P HW X R C hD hR
  have hfl : ∀ i lam l, TwistedPlaces.flatCD L (tabX L X) i lam l = flat L (X.band i lam) l := fun _ _ _ => rfl
  have he : ∀ l, TwistedPlaces.eP L C l = C * coreE L l := fun _ => rfl
  constructor
  · rintro i - ⟨hI, hA, -, -⟩ lam -
    have h := GlobalTheory.NLink.RowCDSize.len_le L HW X R C hD hR i hI (fun h => absurd h.1 (not_lt.2 hA)) lam
    rw [hfl, he]
    refine h.trans (le_of_eq ?_)
    unfold coreH coreF coreM
    ring
  · rintro i - ⟨hI, -, hO, -⟩ lam -
    have h := GlobalTheory.NLink.RowCDSize.len_le L HW X R C hD hR i hI (fun h => absurd h.2 (not_lt.2 hO)) lam
    rw [hfl, he]
    refine h.trans (le_of_eq ?_)
    unfold coreH coreF coreM
    ring

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.IndefR.Links

namespace GlobalTheory.LowestKType

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {n m : ℕ}

def kop (w : GlobalTheory.ExportSeries.Weight D n) (τ : D.what₂.Tau) (a b : Fin m) : Module.End ℂ (PolF D m n) :=
  GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ)) (Matrix.single a b (1 : ℂ))

def sop (w : GlobalTheory.ExportSeries.Weight D n) (τ : D.what₂.Tau) (a b : Fin n) : Module.End ℂ (PolF D m n) :=
  GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockS τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ)) (Matrix.single a b (1 : ℂ))

def Cpt (w : GlobalTheory.ExportSeries.Weight D n) (τ : D.what₂.Tau) (a b : Fin m) : Prop :=
  ((a : ℕ) < w.p τ ↔ (b : ℕ) < w.p τ)

def IsHarm (w : GlobalTheory.ExportSeries.Weight D n) (P : PolF D m n) : Prop :=
  ∀ (τ : D.what₂.Tau) (i l : Fin m), w.p τ ≤ (i : ℕ) → (l : ℕ) < w.p τ → kop w τ i l P = 0

def IsKHw (w : GlobalTheory.ExportSeries.Weight D n) (P : PolF D m n) : Prop :=
  (∀ (τ : D.what₂.Tau) (a b : Fin m), Cpt w τ a b → a < b → kop w τ a b P = 0) ∧
    ∀ (τ : D.what₂.Tau) (a : Fin m), ∃ c : ℂ, kop w τ a a P = c • P

def IsKHwMap {W : Type} [AddCommGroup W] [Module ℂ W] (w : GlobalTheory.ExportSeries.Weight D n)
    (ψ : W →ₗ[ℂ] PolF D m n) : Prop :=
  (∀ (τ : D.what₂.Tau) (a b : Fin m), Cpt w τ a b → a < b → kop w τ a b ∘ₗ ψ = 0) ∧
    ∀ (τ : D.what₂.Tau) (a : Fin m), ∃ c : ℂ, kop w τ a a ∘ₗ ψ = c • ψ

def IsNHw (w : GlobalTheory.ExportSeries.Weight D n) (lam : D.what₂.Tau → Fin n → ℂ) (P : PolF D m n) : Prop :=
  (∀ (τ : D.what₂.Tau) (a b : Fin n), a < b → sop w τ a b P = 0) ∧
    ∀ (τ : D.what₂.Tau) (a : Fin n), sop w τ a a P = lam τ a • P

end GlobalTheory.LowestKType

end
end

section

noncomputable section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW
open scoped ContDiff

namespace GlobalTheory.SmOfDeriv

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def compLmul (ℓ : Lie E a →L[ℝ] ℂ) : Lie E a →L[ℝ] (Lie E a →L[ℝ] ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => ℓ.comp (lmul M)
      map_add' := fun M N => by
        ext v
        change ℓ (toL ((Matrix.of M + Matrix.of N) * Matrix.of v)) = ℓ (toL (Matrix.of M * Matrix.of v)) + ℓ (toL (Matrix.of N * Matrix.of v))
        rw [Matrix.add_mul]
        exact map_add ℓ (toL (Matrix.of M * Matrix.of v)) (toL (Matrix.of N * Matrix.of v))
      map_smul' := fun c M => by
        ext v
        change ℓ (toL ((c • Matrix.of M) * Matrix.of v)) = c • ℓ (toL (Matrix.of M * Matrix.of v))
        rw [Matrix.smul_mul]
        exact map_smul ℓ c (toL (Matrix.of M * Matrix.of v)) }

theorem contDiffAt_inv {z : Lie E a} (hz : z ∈ invSet E a) :
    ContDiffAt ℝ ∞ (fun x : Lie E a => toL (Matrix.of x)⁻¹) z := by
  have hdet : IsUnit (Matrix.of z).det := (Matrix.isUnit_iff_isUnit_det _).1 hz
  have h1 : ContDiffAt ℝ ∞ (fun x : Lie E a => Ring.inverse (Matrix.of x).det) z := by
    have h := contDiffAt_ringInverse ℝ (n := ∞) hdet.unit
    rw [IsUnit.unit_spec] at h
    exact h.comp z (contDiff_det (E := E)).contDiffAt
  refine contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun j => ?_
  have h2 : ContDiff ℝ ∞ fun x : Lie E a => Matrix.adjugate (Matrix.of x) i j := by
    simp only [Matrix.adjugate_apply, Matrix.det_apply']
    refine ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun k _ => ?_)
    simp only [Matrix.updateRow_apply]
    split_ifs
    · exact contDiff_const
    · exact (contDiff_apply ℝ _ k).comp (contDiff_apply ℝ _ (σ k))
  have e : (fun x : Lie E a => toL (Matrix.of x)⁻¹ i j) =
      fun x => Ring.inverse (Matrix.of x).det * Matrix.adjugate (Matrix.of x) i j := by
    funext x
    rw [Matrix.inv_def]
    rfl
  rw [e]
  exact h1.mul h2.contDiffAt

theorem hasFDerivAt_chart {f : GA E a → ℂ} {ι : Type} [Fintype ι] {fs : ι → GA E a → ℂ}
    {ℓ : ι → (Lie E a →L[ℝ] ℂ)} (hd : ∀ g, HasFDerivAt (chart f g) (∑ i, fs i g • ℓ i) (oneL E a))
    (g : GA E a) {z : Lie E a} (hz : z ∈ invSet E a) :
    HasFDerivAt (chart f g) (∑ i, chart (fs i) g z • compLmul (ℓ i) (toL (Matrix.of z)⁻¹)) z := by
  obtain ⟨y, hy⟩ := hz
  obtain rfl : z = toL y.val := hy.symm
  have e : chart f g = chart f (g * infGL E a y) ∘ lmul (toL (y⁻¹).val) := by
    rw [← chart_mul, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
  have e1 : lmul (toL (y⁻¹).val) (toL y.val) = oneL E a := y.inv_mul
  have h := hd (g * infGL E a y)
  rw [← e1] at h
  have h2 := h.comp (toL y.val) (lmul (toL (y⁻¹).val)).hasFDerivAt
  rw [← e] at h2
  refine h2.congr_fderiv ?_
  have ei : toL (Matrix.of (toL y.val))⁻¹ = toL (y⁻¹).val := by
    change toL (y.val)⁻¹ = toL (y⁻¹).val
    rw [Matrix.coe_units_inv]
  rw [ei]
  ext v
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [chart_val]
  rfl

theorem mem_Sm_of_hasFDerivAt : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (K : Set (GA E a → ℂ)),
    (∀ f ∈ K, ∃ (ι : Type) (_ : Fintype ι) (fs : ι → GA E a → ℂ) (ℓ : ι → (Lie E a →L[ℝ] ℂ)), (∀ i, fs i ∈ K) ∧
      ∀ g, HasFDerivAt (chart f g) (∑ i, fs i g • ℓ i) (oneL E a)) → ∀ f ∈ K, f ∈ Sm E a := by
  intro E _ _ _ a K hK
  have key : ∀ n : ℕ, ∀ f ∈ K, ∀ g, ∀ z ∈ invSet E a, ContDiffAt ℝ n (chart f g) z := by
    intro n
    induction n with
    | zero =>
      intro f hf g z hz
      obtain ⟨ι, _, fs, ℓ, -, hd⟩ := hK f hf
      exact contDiffAt_zero.2 ⟨invSet E a, isOpen_invSet.mem_nhds hz, fun x hx =>
        (hasFDerivAt_chart hd g hx).continuousAt.continuousWithinAt⟩
    | succ n ih =>
      intro f hf g z hz
      obtain ⟨ι, _, fs, ℓ, hfs, hd⟩ := hK f hf
      rw [Nat.cast_succ]
      refine contDiffAt_succ_iff_hasFDerivAt.2 ⟨_, ⟨invSet E a, isOpen_invSet.mem_nhds hz,
        fun x hx => hasFDerivAt_chart hd g hx⟩, ?_⟩
      refine ContDiffAt.sum fun i _ => (ih (fs i) (hfs i) g z hz).smul ?_
      exact (compLmul (ℓ i)).contDiff.contDiffAt.comp z (contDiffAt_infty.1 (contDiffAt_inv hz) n)
  intro f hf g z hz
  exact (contDiffAt_infty.2 fun n => key n f hf g z hz).contDiffWithinAt

end GlobalTheory.SmOfDeriv
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_equivariant_log_semistable_to_deRham : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI), ∃ ι : Bst P →ₐ[ℚ_[l]] P.R.BdR, (∀ b, ι (Polynomial.C b) = P.ιB b) ∧ (∀ (g : GQ l) (x : Bst P), ι (actSt P g x) = P.actQdR g (ι x)) := by
  first | exact @GlobalTheory.BstLog.iota_exists | exact GlobalTheory.BstLog.iota_exists | (intros; apply GlobalTheory.BstLog.iota_exists <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

namespace GlobalTheory.JSW

theorem mspanR_left_invariant : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a), ∀ F ∈ GlobalTheory.JSW.mspanR π,
    ∀ (γ : GL (Fin a) E) (g : GA E a), F (ratGL E a γ * g) = F g := by
  intro E _ _ _ a π
  let S : Submodule ℂ (GA E a → ℂ) :=
    { carrier := {F | ∀ (γ : GL (Fin a) E) (g : GA E a), F (ratGL E a γ * g) = F g}
      add_mem' := by
        intro F G hF hG γ g
        simp only [Pi.add_apply, hF γ g, hG γ g]
      zero_mem' := by intro γ g; rfl
      smul_mem' := by
        intro c F hF γ g
        simp only [Pi.smul_apply, hF γ g] }
  have hS : mspanR π ≤ S := by
    refine sInf_le ⟨?_, ?_, ?_⟩
    · intro φ hφ γ g
      exact (π.cusp φ hφ).1.left γ g
    · intro F hF h γ g
      show F (ratGL E a γ * g * h) = F (g * h)
      rw [mul_assoc]; exact hF γ (g * h)
    · intro F hF X _ ν _ k γ' _ γ g
      show (∫ x, k x * F (ratGL E a γ * g * infGL E a (γ' x)) ∂ν) = ∫ x, k x * F (g * infGL E a (γ' x)) ∂ν
      congr 1
      funext x
      rw [mul_assoc, hF γ (g * infGL E a (γ' x))]
  intro F hF
  exact hS hF

end GlobalTheory.JSW
end

section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open Matrix

namespace GlobalTheory.BlockMirabolic

theorem blockGL_mem_mirS : ∀ (E : Type) [Field E] [NumberField E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))),
    ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S,
      GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h ∈ (GlobalTheory.JSW.supS (E := E) (a := (m + r + 1) + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) (m + r + 1)) := by
  intro E _ _ m r S h hh
  constructor
  · intro w hw
    have hw1 := congrArg Units.val (hh w hw)
    apply Units.ext
    simp only [Units.val_one] at hw1 ⊢
    change ((GroundTheory.Automorphic.FourierWhittaker.blockMat _ h.val).map _) = 1
    change (h.val.map _) = 1 at hw1
    rw [GroundTheory.Automorphic.FourierWhittaker.map_blockMat, hw1, GroundTheory.Automorphic.FourierWhittaker.blockMat_one]
  · intro j
    change GroundTheory.Automorphic.FourierWhittaker.blockMat _ h.val (Fin.last (m + r + 1)) j = _
    rw [GroundTheory.Automorphic.FourierWhittaker.blockMat_apply, dite_eq_right (by simp)]
    simp only [eq_comm]

end GlobalTheory.BlockMirabolic
end

section

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

noncomputable section

namespace GlobalTheory.JSW.WhitNorm

theorem continuous_whit_and_norm_mul : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (F : GA E a → ℂ), Continuous F →
    (∀ γ g, F (ratGL E a γ * g) = F g) →
    Continuous (GlobalTheory.JSW.whit F) ∧ ∀ u ∈ GlobalTheory.CellDec.NA E a, ∀ g, ‖GlobalTheory.JSW.whit F (u * g)‖ = ‖GlobalTheory.JSW.whit F g‖ := by
  intro E _ _ _ a F hF hl
  refine ⟨?_, fun u hu g => ?_⟩
  · have e : GlobalTheory.JSW.whit F = GroundTheory.Automorphic.FourierWhittaker.partialCoeff F 0 :=
      funext fun g => GroundTheory.Automorphic.FourierWhittaker.whittaker_eq_partialCoeff_zero hF g
    rw [e]
    exact GroundTheory.Automorphic.FourierWhittaker.continuous_partialCoeff hF 0
  · have hu' : u ∈ GlobalTheory.JSW.NA (E := E) (a := a) := (GlobalTheory.SmGL.mem_unipB _).1 hu
    rw [GlobalTheory.JSW.WhitModel.whit_mul hF hl hu' g, norm_mul, GlobalTheory.JSW.psiN, Circle.norm_coe, one_mul]

end GlobalTheory.JSW.WhitNorm
end
end

section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors

theorem _root_.GlobalTheory.T.adelicDiagonalUniformizer_eq_prod_localDiagonal : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ)
    (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) (l' : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℕ)),
    (∀ w i, ((l' w i : ℕ) : ℤ) = l w i) → GlobalTheory.CellDec.tl n ϖ l = GlobalTheory.JSW.tl ϖ l' := by
  first | exact @GlobalTheory.CellDecNat.tl_eq_jsw_tl | exact GlobalTheory.CellDecNat.tl_eq_jsw_tl | (intros; apply GlobalTheory.CellDecNat.tl_eq_jsw_tl <;> assumption)
end

section

open MeasureTheory GlobalTheory.AutomorphicL2Unitary

theorem _root_.GlobalTheory.T.inner_rightRegularRep_sub_eq_intervalIntegral_derivative : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μ] (c : ℝ → G), Continuous c → c 0 = 1 → ∀ {f f' : G → ℂ} (hf : MemL2Quotient Γ μ f) (hf' : MemL2Quotient Γ μ f'), Continuous f' → (∀ x t, HasDerivAt (fun s => f (x * c s)) (f' (x * c t)) t) → ∀ (H : L2 Γ μ) (t : ℝ), Integrable (Function.uncurry fun (s : ℝ) (q : GlobalTheory.AutomorphicL2Unitary.Quot Γ) => starRingEnd ℂ (H q) * f' (sec Γ q * c s)) ((volume.restrict (Set.uIoc 0 t)).prod (quotMeasure Γ μ)) → inner ℂ H (R Γ μ (c t) hf.toL2) - inner ℂ H hf.toL2 = ∫ s in (0 : ℝ)..t, inner ℂ H (R Γ μ (c s) hf'.toL2) := by
  first | exact @GlobalTheory.AutomorphicL2Unitary.inner_R_sub_eq_intervalIntegral | exact GlobalTheory.AutomorphicL2Unitary.inner_R_sub_eq_intervalIntegral | (intros; apply GlobalTheory.AutomorphicL2Unitary.inner_R_sub_eq_intervalIntegral <;> assumption)
end

section

open MeasureTheory GlobalTheory.AutomorphicL2Unitary

theorem _root_.GlobalTheory.T.integrable_conj_mul_translate_path' : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μ] (c : ℝ → G), Continuous c → ∀ {f' : G → ℂ}, MemL2Quotient Γ μ f' → Continuous f' → ∀ (H : L2 Γ μ) (t : ℝ), Integrable (Function.uncurry fun (s : ℝ) (q : GlobalTheory.AutomorphicL2Unitary.Quot Γ) => starRingEnd ℂ (H q) * f' (sec Γ q * c s)) ((volume.restrict (Set.uIoc 0 t)).prod (quotMeasure Γ μ)) := by
  first | exact @GlobalTheory.integrable_conj_mul_translate_path | exact GlobalTheory.integrable_conj_mul_translate_path | (intros; apply GlobalTheory.integrable_conj_mul_translate_path <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

theorem _root_.GlobalTheory.T.torsion_coinvariants_twistedCyclotomicGenerator : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ (m r : ℕ), Lev l m → ∀ (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)) (g : GQ l), Frame χ K m U g → ∀ J : Finset ℤ, HTBasis act χ (Gj K m) U (J : Set ℤ) → ∀ (i : ℤ) (w w' : Fin r → PadicComplex l) (k : ℕ), (∀ a, w a ∈ Ohat K) → (∀ a, w' a ∈ Ohat K) → twAct act χ i U g w' - w' = (l : PadicComplex l) ^ k • w → ∃ y : Fin r → PadicComplex l, (∀ a, y a ∈ Ohat K) ∧ twAct act χ i U g y - y = (l : PadicComplex l) ^ (max 1 (∑ u ∈ J.erase i, (m + padicValInt l (u - i)))) • w := by
  first | exact @GlobalTheory.CycCoinv.torsion_coinvariants | exact GlobalTheory.CycCoinv.torsion_coinvariants | (intros; apply GlobalTheory.CycCoinv.torsion_coinvariants <;> assumption)
end
