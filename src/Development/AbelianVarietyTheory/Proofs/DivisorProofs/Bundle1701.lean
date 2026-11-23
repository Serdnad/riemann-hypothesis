module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle387
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqSucc
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1657
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1480
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1307
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1405
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmFnAndKilledFnOfHolFn
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1616
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1494
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1659
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle037
public import Mathlib.GroupTheory.Commensurable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzPointCountOneClassCommensurable
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1660
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.ValuativeCriterion
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.RegDom
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsQuasiRegularSeqOfIsFreeGen
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle040

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem ratRigid_of_isProper_of_charZero : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (H : Over (Sp Ω)) [GrpObj H],
    IsProper H.hom → RatRigid H (𝟙 (Sp Ω)) := by
  intro Ω _ _ H _ hP ξ hξ hrat
  obtain ⟨β, hβ⟩ := hrat
  obtain ⟨σ, j, r₂, rh, h1, h2, h3, h4, h5, h6⟩ := GlobalTheory.T.exists_scaling_compatible_expansion_at_infinity Ω
  have comp : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C),
      spMap g ≫ spMap f = spMap (g.comp f) := fun f g => by rw [← Spec.map_comp]; rfl
  have compA : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C)
      {Z : Scheme.{0}} (h : Sp A ⟶ Z), spMap g ≫ spMap f ≫ h = spMap (g.comp f) ≫ h := by
    intros; rw [← Category.assoc, comp]
  have canc := (GlobalTheory.T.spec_injectiveRingMap_cancellation).1
  have cancS := (GlobalTheory.T.spec_injectiveRingMap_cancellation).2
  haveI := hP
  haveI : IsSeparated H.hom := inferInstance
  have sqr_hom : sqr H ≫ H.hom = H.hom := Over.w (𝟙 H * 𝟙 H)
  have hi : Function.Injective (algebraMap (PowerSeries Ω) (LaurentSeries Ω)) :=
    IsFractionRing.injective _ _
  have ha : Function.Injective (algebraMap (RatFunc Ω) (LaurentSeries Ω)) := RingHom.injective _
  have hj : Function.Injective j := RingHom.injective _

  have hσ : spMap σ ≫ β = β ≫ sqr H := by
    refine canc _ _ (algebraMap (RatFunc Ω) (LaurentSeries Ω)) ha _ _ _ ?_
    rw [compA, ← h2, ← comp, Category.assoc, hβ, compA, h1, ← compA, hξ.scale, ← Category.assoc,
      ← Category.assoc, hβ]

  have hβb : β ≫ H.hom = spMap RatFunc.C := by
    refine canc _ _ (algebraMap (RatFunc Ω) (LaurentSeries Ω)) ha _ _ _ ?_
    rw [← Category.assoc, hβ, Category.assoc, hξ.base, Category.comp_id, comp, comp, h6]
  have hsq : (spMap j ≫ β) ≫ H.hom =
      Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries Ω) (LaurentSeries Ω))) ≫ spMap PowerSeries.C := by
    rw [Category.assoc, hβb, comp, h5]; exact (comp _ _).symm
  have hE : ValuativeCriterion.Existence H.hom :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed H.hom) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact) H.hom).1
  let V : ValuativeCommSq H.hom :=
    { R := PowerSeries Ω
      K := LaurentSeries Ω
      i₁ := spMap j ≫ β
      i₂ := spMap PowerSeries.C
      commSq := ⟨hsq⟩ }
  obtain ⟨⟨l⟩⟩ := hE V
  have hζ1 : spMap (algebraMap (PowerSeries Ω) (LaurentSeries Ω)) ≫ l.l = spMap j ≫ β := l.fac_left
  have hζ2 : l.l ≫ H.hom = spMap PowerSeries.C := l.fac_right
  have hrC : (PowerSeries.rescale (2⁻¹ : Ω)).comp PowerSeries.C = PowerSeries.C := by
    refine RingHom.ext fun x => PowerSeries.ext fun n => ?_
    rw [RingHom.comp_apply, PowerSeries.coeff_rescale, PowerSeries.coeff_C]
    split_ifs with hn
    · subst hn; rw [pow_zero, _root_.one_mul]
    · rw [MulZeroClass.mul_zero]
  have hcc : (PowerSeries.constantCoeff (R := Ω)).comp (PowerSeries.rescale (2⁻¹ : Ω)) =
      PowerSeries.constantCoeff (R := Ω) := RingHom.ext fun x => by
    rw [RingHom.comp_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale, pow_zero,
      _root_.one_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have hcC : (PowerSeries.constantCoeff (R := Ω)).comp PowerSeries.C = RingHom.id Ω :=
    RingHom.ext fun x => by rw [RingHom.comp_apply, PowerSeries.constantCoeff_C]; rfl

  have hζs : spMap (PowerSeries.rescale (2⁻¹ : Ω)) ≫ l.l = l.l ≫ sqr H := by
    refine cancS _ _ (algebraMap (PowerSeries Ω) (LaurentSeries Ω)) hi _ _ H.hom _ _ ?_ ?_
    · rw [Category.assoc, Category.assoc, hζ2, comp, hrC, sqr_hom, hζ2]
    · rw [compA, ← h3, ← comp, Category.assoc, hζ1, compA, h4, ← compA, hσ, ← Category.assoc,
        ← Category.assoc, hζ1]

  have hunit : ∀ n : ℕ, 1 ≤ n → IsUnit ((2⁻¹ : Ω) ^ n - 2) := by
    intro n hn
    rw [isUnit_iff_ne_zero, sub_ne_zero, inv_pow]
    intro h
    have h0 : (2 : Ω) ^ n ≠ 0 := pow_ne_zero _ two_ne_zero
    have e : (2 : Ω) ^ (n + 1) = 1 := by
      calc (2 : Ω) ^ (n + 1) = 2 ^ n * 2 := pow_succ _ _
        _ = 2 ^ n * (2 ^ n)⁻¹ := by rw [h]
        _ = 1 := mul_inv_cancel₀ h0
    have e' : (2 : ℕ) ^ (n + 1) = 1 := by exact_mod_cast e
    have : 1 < (2 : ℕ) ^ (n + 1) := Nat.one_lt_two_pow (by omega)
    omega
  have hz := (GlobalTheory.T.formalSquaringPath_unique_constant_localRing (Sp Ω) H Ω).2.1 (spMap (PowerSeries.constantCoeff (R := Ω)) ≫ l.l)
    (by rw [Category.assoc, ← hζs, compA, hcc])
  have hzero : spMap (PowerSeries.constantCoeff (R := Ω)) ≫ l.l = 𝟙 (Sp Ω) ≫ unitSec H := by
    rw [hz, Category.assoc (spMap _) l.l H.hom, hζ2, comp, hcC, show spMap (RingHom.id Ω) = 𝟙 (Sp Ω) from Spec.map_id _]
  have hζt : l.l = triv H (𝟙 (Sp Ω)) :=
    (GlobalTheory.T.formalSquaringPath_unique_constant_localRing (Sp Ω) H Ω).2.2 inferInstance (2⁻¹) hunit (𝟙 _) l.l
      ⟨by rw [Category.comp_id]; exact hζ2, hzero, hζs⟩

  have hβu : β = spMap RatFunc.C ≫ unitSec H := by
    refine canc _ _ j hj _ _ _ ?_
    rw [← hζ1, hζt, triv, Category.id_comp, compA, ← h5, ← compA]
  refine cancS _ _ (algebraMap (PowerSeries Ω) (LaurentSeries Ω)) hi _ _ H.hom _ _ ?_ ?_
  · rw [hξ.base, triv_over]
  · rw [← hβ, hβu, compA, h6, triv, Category.id_comp, compA]

end GlobalTheory.Nef
end

section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.SncComp

theorem smooth_of_regular_stalk (K : Type) [Field K] [PerfectField K] (Y : Scheme.{0}) (q : Y ⟶ Sp K)
    [LocallyOfFiniteType q] (d : ℕ)
    (h : ∀ y : Y, IsClosed ({y} : Set Y) →
      IsRegularLocalRing (Y.presheaf.stalk y) ∧ ringKrullDim (Y.presheaf.stalk y) = d) :
    SmoothOfRelativeDimension d q := by
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace q
  choose A _ _ j _ pt hj hq using exists_affine_chart_over q
  let 𝒰 : Y.OpenCover := Scheme.Cover.mkOfCovers Y (fun y => Spec (.of (A y))) j (fun y => ⟨y, pt y, hj y⟩)
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @SmoothOfRelativeDimension d)
  refine IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension d) 𝒰 fun (y : Y) => ?_
  change SmoothOfRelativeDimension d (j y ≫ q)
  have hft : LocallyOfFiniteType (spMap (algebraMap K (A y))) := by
    have : LocallyOfFiniteType (j y ≫ q) := inferInstance
    rwa [hq y] at this
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at hft
  have : Algebra.FiniteType K (A y) := RingHom.finiteType_algebraMap.mp hft
  rw [hq y]
  refine RegGenSmooth.smooth_of_regular K (A y) d fun m hm => ?_
  let w : Spec (.of (A y)) := (⟨m, inferInstance⟩ : PrimeSpectrum _)
  have hw : IsClosed ({w} : Set (Spec (.of (A y)))) := (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2 hm
  have hc : IsClosed ({j y w} : Set Y) := by
    have h1 := (j y).isOpenEmbedding.preimage_closedPoints
    have h2 : w ∈ (j y) ⁻¹' closedPoints Y := by rw [h1]; exact hw
    exact h2
  obtain ⟨h1, h2⟩ := h _ hc
  let e := (asIso ((j y).stalkMap w) ≪≫ Spec.stalkIso (.of _) w).commRingCatIsoToRingEquiv
  exact ⟨IsRegularLocalRing.of_ringEquiv e, (ringKrullDim_eq_of_ringEquiv e).symm.trans h2⟩

theorem smooth_component : ∀ (F : Type) [Field F] [CharZero F] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp F) (e : ℕ), IsProjOver p → SmoothOfRelativeDimension (e + 1) p → ∀ (r : ℕ) (z : Fin r → X), (∀ x : X, FinalTheorems.LSncAt X (fun a => (Closeds.closure {z a})) x) → ∀ a, SmoothOfRelativeDimension e (closι (z a) ≫ p) := by
  intro F _ _ X _ p e _ hsm r z hL a
  have : Smooth p := SmoothOfRelativeDimension.smooth (e + 1) p
  have hdim := GlobalTheory.HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth p (e + 1) hsm
  refine smooth_of_regular_stalk F _ _ e fun y hy => ?_
  let I := Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {z a})
  have hc : IsClosed ({closι (z a) y} : Set X) := by
    simpa using (closι (z a)).isClosedEmbedding.isClosedMap _ hy
  have hd := (ProperCut.ringKrullDim_stalk_eq p hc).trans hdim
  obtain ⟨hreg, n, t, ε, hR, hI⟩ := hL (closι (z a) y)
  have hmem : closι (z a) y ∈ Closeds.closure {z a} := by
    have := Vanishing.ι_mem_support I y
    have h := Scheme.IdealSheafData.coe_support_vanishingIdeal (Closeds.closure {z a})
    exact h.le this
  have hker : RingHom.ker ((closι (z a)).stalkMap y).hom = Ideal.span {t (ε ⟨a, hmem⟩)} :=
    (Vanishing.ker_stalkMap I y).trans (hI ⟨a, hmem⟩)
  have hm : t (ε ⟨a, hmem⟩) ∈ IsLocalRing.maximalIdeal _ := hR.1 ▸ Ideal.subset_span ⟨_, rfl⟩
  obtain ⟨h1, h2⟩ := isRegularLocalRing_quotient_of_not_mem_sq hm ((regular_params_spec t hR.1 hR.2).1 _)
  let φ := (Ideal.quotEquivOfEq hker.symm).trans
    (RingHom.quotientKerEquivOfSurjective ((closι (z a)).stalkMap_surjective y))
  refine ⟨IsRegularLocalRing.of_ringEquiv φ, ?_⟩
  rw [← ringKrullDim_eq_of_ringEquiv φ]
  rw [hd] at h2
  generalize ringKrullDim (X.presheaf.stalk (closι (z a) y) ⧸ Ideal.span {t (ε ⟨a, hmem⟩)}) = u at h2
  induction u using WithBot.recBotCoe with
  | bot => exact absurd h2 (by rw [WithBot.bot_add]; exact WithBot.bot_ne_coe)
  | coe u =>
    induction u using ENat.recTopCoe with
    | top => exact absurd (WithBot.coe_injective h2) (ENat.top_ne_coe _)
    | coe u =>
      have : u + 1 = e + 1 := by exact_mod_cast h2
      exact_mod_cast Nat.succ_injective this

end GlobalTheory.SncComp
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict.CoefExt

open GlobalTheory.HolDict.HolTo

section General

variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {Hm : ι → Mt n} {H : ι → Type}
  [∀ τ, NormedAddCommGroup (H τ)] [∀ τ, InnerProductSpace ℂ (H τ)] {σ : ∀ τ, Mt n → (H τ →L[ℂ] H τ)} {v : ∀ τ, H τ}

omit [Fintype ι] in
theorem prod_single_apply (k : ℕ) (τs : Fin k → ι) (Xs : Fin k → Mt n) (t : Fin k → ℝ) (ρ : ι) :
    (List.ofFn fun i => (Pi.mulSingle (τs i) (NormedSpace.exp (t i • Xs i)) : ι → Mt n)).prod ρ =
      (List.ofFn fun i => NormedSpace.exp (t i • (if ρ = τs i then Xs i else 0))).prod := by
  rw [Pi.list_prod_apply, List.map_ofFn]
  congr 2
  funext i
  by_cases h : ρ = τs i
  · subst h
    simp
  · simp [h]

theorem smFn_coef (hσ : ∀ τ, Formalism.QuantumDeterminants.IsCRepOn (Formalism.QuantumDeterminants.UH (Hm τ)) (σ τ))
    (hv : ∀ τ, SmoothVec (lieH (Hm τ)) (σ τ) (v τ)) :
    SmFn Hm fun u => ∏ τ, ⟪v τ, σ τ (u τ) (v τ)⟫_ℂ := by
  intro k τs Xs hX u hu
  have hmem : ∀ t : Fin k → ℝ, (List.ofFn fun i =>
      (Pi.mulSingle (τs i) (NormedSpace.exp (t i • Xs i)) : ι → Mt n)).prod ∈ UG Hm := fun t =>
    prod_mem_UG _ fun v hv => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hv
      exact single_mem_UG Hm _ (hX i) _
  refine contDiff_prod fun ρ _ => ?_
  simp only [Pi.mul_apply, (hσ ρ).2 _ (hu ρ) _ (hmem _ ρ), ContinuousLinearMap.comp_apply]
  simp only [prod_single_apply]
  have h1 := hv ρ k (fun i => if ρ = τs i then Xs i else 0) fun i => by
    split_ifs with h
    · subst h
      exact hX i
    · show _ = _
      simp
  exact (((innerSL ℂ (v ρ)).comp (σ ρ (u ρ))).restrictScalars ℝ).contDiff.comp h1

theorem hasDerivAt_of_smooth {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] {L : Set (Mt n)}
    {π : Mt n → (K →L[ℂ] K)} {x : K} (hx : SmoothVec L π x) {X : Mt n} (hX : X ∈ L) :
    HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) x) (dRep π X x) 0 := by
  have h1 := hx 1 (fun _ => X) fun _ => hX
  have h2 : ContDiff ℝ ∞ (fun r : ℝ => (fun _ => r : Fin 1 → ℝ)) := by fun_prop
  have h3 := (h1.comp h2).differentiable (by simp)
  have h4 : Differentiable ℝ fun t : ℝ => π (NormedSpace.exp (t • X)) x := by
    have e : (fun t : ℝ => π (NormedSpace.exp (t • X)) x) = ((fun t : Fin 1 → ℝ =>
        π ((List.ofFn fun i => NormedSpace.exp (t i • X)).prod) x) ∘ fun r _ => r) := by
      funext r
      simp
    rw [e]
    exact h3
  exact (h4 0).hasDerivAt

theorem der_coef (hσ : ∀ τ, Formalism.QuantumDeterminants.IsCRepOn (Formalism.QuantumDeterminants.UH (Hm τ)) (σ τ))
    (hv : ∀ τ, SmoothVec (lieH (Hm τ)) (σ τ) (v τ)) (τ : ι) {X : Mt n} (hX : X ∈ lieH (Hm τ)) {u : ι → Mt n}
    (hu : u ∈ UG Hm) :
    der τ X (fun u => ∏ τ, ⟪v τ, σ τ (u τ) (v τ)⟫_ℂ) u =
      ⟪v τ, σ τ (u τ) (dRep (σ τ) X (v τ))⟫_ℂ * ∏ ρ ∈ Finset.univ.erase τ, ⟪v ρ, σ ρ (u ρ) (v ρ)⟫_ℂ := by
  unfold der
  have e : (fun t : ℝ => ∏ ρ, ⟪v ρ, σ ρ ((u * (Pi.mulSingle τ (NormedSpace.exp (t • X)) : ι → Mt n)) ρ) (v ρ)⟫_ℂ) =
      fun t : ℝ => ⟪v τ, σ τ (u τ) (σ τ (NormedSpace.exp (t • X)) (v τ))⟫_ℂ *
        ∏ ρ ∈ Finset.univ.erase τ, ⟪v ρ, σ ρ (u ρ) (v ρ)⟫_ℂ := by
    funext t
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ), Pi.mul_apply,
      (hσ τ).2 _ (hu τ) _ (single_mem_UG Hm τ hX t τ), Pi.mulSingle_eq_same]
    congr 1
    refine Finset.prod_congr rfl fun ρ hρ => ?_
    rw [Pi.mul_apply, Pi.mulSingle_eq_of_ne (Finset.ne_of_mem_erase hρ), mul_one]
  rw [e]
  have h1 := (((innerSL ℂ (v τ)).comp (σ τ (u τ))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (hasDerivAt_of_smooth (hv τ) hX)
  exact (h1.mul_const _).deriv

theorem derC_coef {q : ι → ℕ} {x₀ : ι → Mt n} (h : ∀ τ, OrthFr (Hm τ) (q τ) (x₀ τ))
    (hσ : ∀ τ, Formalism.QuantumDeterminants.IsCRepOn (Formalism.QuantumDeterminants.UH (Hm τ)) (σ τ))
    (hv : ∀ τ, SmoothVec (lieH (Hm τ)) (σ τ) (v τ)) (τ : ι) (Z : Mt n) {u : ι → Mt n} (hu : u ∈ UG Hm) :
    derC Hm τ Z (fun u => ∏ τ, ⟪v τ, σ τ (u τ) (v τ)⟫_ℂ) u =
      ⟪v τ, σ τ (u τ) (dRepC (Hm τ) (σ τ) Z (v τ))⟫_ℂ * ∏ ρ ∈ Finset.univ.erase τ, ⟪v ρ, σ ρ (u ρ) (v ρ)⟫_ℂ := by
  obtain ⟨h1, h2⟩ := conj_facts (herm_of_orth (h τ)) (dets_ne (h τ)).1 Z
  have hA : (1 / 2 : ℂ) • (Z + conjH (Hm τ) Z) ∈ lieH (Hm τ) := by
    show _ = _
    rw [conjTranspose_smul, conjTranspose_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, h1, h2]
    have : star (1 / 2 : ℂ) = 1 / 2 := by simp
    rw [this, ← smul_add]
    abel_nf
    simp
  have hB : (1 / (2 * Complex.I) : ℂ) • (Z - conjH (Hm τ) Z) ∈ lieH (Hm τ) := by
    show _ = _
    rw [conjTranspose_smul, conjTranspose_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, h1, h2]
    have : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I)) := by simp
    rw [this, neg_smul, ← smul_neg, ← smul_add]
    abel_nf
    simp
  unfold derC dRepC
  rw [der_coef hσ hv τ hA hu, der_coef hσ hv τ hB hu, map_add (f := _), map_smul, inner_add_right, inner_smul_right]
  ring

theorem killedFn_coef {q : ι → ℕ} {x₀ : ι → Mt n} {w : ι → Fin n → ℤ} (h : ∀ τ, OrthFr (Hm τ) (q τ) (x₀ τ))
    (hσ : ∀ τ, Formalism.QuantumDeterminants.IsCRepOn (Formalism.QuantumDeterminants.UH (Hm τ)) (σ τ))
    (hv : ∀ τ, SmoothVec (lieH (Hm τ)) (σ τ) (v τ))
    (hk : ∀ τ (a c : Fin n), a ≤ c → dRepC (Hm τ) (σ τ) (x₀ τ * Matrix.single a c 1 * (x₀ τ)⁻¹) (v τ) =
      if a = c then (w τ a : ℂ) • v τ else 0) :
    KilledFn Hm x₀ w fun u => ∏ τ, ⟪v τ, σ τ (u τ) (v τ)⟫_ℂ := by
  intro τ a c hac u hu
  rw [derC_coef h hσ hv τ _ hu, hk τ a c hac]
  split_ifs
  · rw [map_smul, inner_smul_right, mul_assoc]
    beta_reduce
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ)]
  · simp

end General

theorem arr_bijective {n q : ℕ} (hq : q ≤ n) : Function.Bijective (arr (n := n) q) := by
  refine Finite.injective_iff_bijective.1 fun a b hab => ?_
  have h := congrArg Fin.val hab
  have := a.2
  have := b.2
  unfold arr at h
  apply Fin.ext
  split_ifs at h <;> simp only at h <;> omega

theorem diagonal_mem_Kset {n : ℕ} (ε : Fin n → Bool) (s : Fin n → ℝ) :
    diagonal (fun a => Complex.exp ((s a : ℂ) * Complex.I)) ∈ Formalism.REAL.Kset ε := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    simp only [Pi.star_apply]
    change Complex.exp ((s i : ℂ) * Complex.I) * (starRingEnd ℂ) (Complex.exp ((s i : ℂ) * Complex.I)) = 1
    rw [← Complex.exp_conj, ← Complex.exp_add]
    simp
  · unfold Formalism.REAL.Jm
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext a
    ring

theorem torus_ext {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) {w : D.what₂.Tau → Fin V.rank → ℤ}
    {v : M.Vec} (hw : WtIs M w) (hv : IsExtVec M v) (s : D.what₂.Tau → Fin V.rank → ℝ) (τ : D.what₂.Tau)
    (hx : (x0Mat M τ).det ≠ 0) :
    M.rep τ (torEl (x0Mat M) s τ) (v τ : M.H τ) =
      (∏ a, Complex.exp ((s τ a : ℂ) * Complex.I) ^ w τ a) • (v τ : M.H τ) := by
  set e := Equiv.ofBijective _ (arr_bijective (nNeg_le (M.ε τ))) with he
  have hfr : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have h1 := torus_x0Mat M τ fun a => Complex.exp ((s τ (e.symm a) : ℂ) * Complex.I)
  have h2 : ∀ c, e.symm (arr (nNeg (M.ε τ)) c) = c := fun c => e.symm_apply_apply c
  simp only [h2] at h1
  have h3 : M.fr τ * torEl (x0Mat M) s τ * (M.fr τ)⁻¹ =
      diagonal fun a => Complex.exp ((s τ (e.symm a) : ℂ) * Complex.I) := by
    unfold torEl
    rw [← h1, Matrix.mul_nonsing_inv_cancel_right _ _ hx.isUnit, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv_cancel_left _ _ hfr, Matrix.mul_nonsing_inv_cancel_right _ _ hfr]
  unfold DSModel.rep
  rw [h3, (hv τ).2.2 (fun a => s τ (e.symm a)) (diagonal_mem_Kset _ _)]
  congr 1
  rw [← e.sum_comp]
  simp only [← Complex.exp_int_mul, ← Complex.exp_sum, Equiv.symm_apply_apply]
  congr 1
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  have h4 : extWt M τ (e c) = (w τ c : ℝ) := (hw τ c).symm
  rw [h4]
  push_cast
  ring

end GlobalTheory.HolDict.CoefExt

namespace GlobalTheory.HolDict


open CoefExt in
theorem holFn_coef_extVec : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) (v : M.Vec), IsInfFam θ → HolShape M → WtIs M w → IsExtVec M v → HolFn (gramAt D V) (fun τ => nNeg (M.ε τ)) (x0Mat M) w (fun u => ∏ τ, ⟪(v τ : M.H τ), M.rep τ (u τ) (v τ : M.H τ)⟫_ℂ) ∧ ∀ s τ, M.rep τ (torEl (x0Mat M) s τ) (v τ : M.H τ) = (∏ a, Complex.exp ((s τ a : ℂ) * Complex.I) ^ w τ a) • (v τ : M.H τ) := by
  intro D θ V S M w v hθ hM hw hv
  classical
  have ho : ∀ τ, OrthFr (gramAt D V τ) (nNeg (M.ε τ)) (x0Mat M τ) := fun τ => ((GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M τ).2.2.2 hM).1
  have hσ : ∀ τ, Formalism.QuantumDeterminants.IsCRepOn (Formalism.QuantumDeterminants.UH (gramAt D V τ)) (M.rep τ) := fun τ => (GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M τ).2.1.1
  have hk := GlobalTheory.T.baseFrameBorel_acts_extremalVector_by_weight D θ V S M w v hθ hM hw hv
  refine ⟨GlobalTheory.T.holomorphicType_of_smooth_borelKilled _ _ _ _ _ _ ho _ (smFn_coef hσ fun τ => (hk τ).1)
    (killedFn_coef ho hσ (fun τ => (hk τ).1) fun τ => (hk τ).2), fun s τ => ?_⟩
  exact torus_ext M hw hv s τ (HolTo.dets_ne (ho τ)).2

end GlobalTheory.HolDict
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.pairSection_mem_ball_exp_of_projArithVariety : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (a b : ℤ) (f : X.functionField), f ∈ P.H a b → ∃ u : ℝ, 0 ≤ u ∧ f ∈ P.Bl a b (Real.exp u) := by
  first | exact @GlobalTheory.HSNef.bounded_norm | exact GlobalTheory.HSNef.bounded_norm | (intros; apply GlobalTheory.HSNef.bounded_norm <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.VolBr

theorem log_ncard_ball_one_ge_of_shift_nef : GlobalTheory.Published.ArithHilbertSamuel → GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (b : ℕ) (s t : X.functionField), P.Good D b s t → ∀ (a c : ℤ) (M : HermLB p) (α t₀ : ℝ), P.Rep a c M → M.IsSelfInter α → (M.shift (fun _ => t₀) fun _ => rfl).IsNef D → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, (α / (D + 1).factorial - ε) * (m : ℝ) ^ (D + 1) ≤ P.lc (m * a) (m * c) 1 := by
  intro hHS hAC k _ X _ p D hX P b s t hG a c M α t₀ hRep hSI hNef ε hε
  exact GlobalTheory.T.eventually_log_ncard_seminormBall_one_ge X.functionField (fun m : ℕ => P.H (m * a) (m * c)) (fun m : ℕ => P.Bl (m * a) (m * c))
    (D + 1) (Nat.succ_pos D) (fun m => GlobalTheory.T.isSeminormBallFamily_sectionBalls k X p P _ _)
    (fun m R => GlobalTheory.T.hermLineBundlePair_balls_finite hHS k X p D hX P b s t hG _ _ R hAC)
    (α / (D + 1).factorial) ((D + 1) * gdeg M D / (D + 1).factorial) t₀
    (fun t ht => GlobalTheory.T.arith_hilbertSamuel_log_ball_count_tendsto hHS hAC k X p D hX P a c M α t₀ hRep hSI hNef t ht) ε hε

end GlobalTheory.VolBr
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.kottwitz_pointCount_one_class_commensurable : ∀ {Γ G₁ G₂ : Type} [Group Γ] [Group G₁] [Group G₂] (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (θ : G₂ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (γ : G₁) (δ : G₂) (f₁ : G₁ → ℂ) (φ : G₂ → ℂ), (∀ g : G₁, Subgroup.Commensurable (K₁.map (MulAut.conj g).toMonoidHom) K₁) → (∀ g : G₂, Subgroup.Commensurable (K₂.map (MulAut.conj g).toMonoidHom) K₂) → K₂.map θ ≤ K₂ → (∀ k ∈ K₁, ∀ x, f₁ (k⁻¹ * x * k) = f₁ x) → (∀ k ∈ K₂, ∀ x, φ (k⁻¹ * x * θ k) = φ x) → (∀ g : Γ, ι₁ g * γ = γ * ι₁ g) → (∀ g : Γ, ι₂ g * δ = δ * θ (ι₂ g)) → Function.Injective (ι₁.prod ι₂) → (∀ x : G₁ × G₂, Finite (stab ι₁ ι₂ K₁ K₂ x)) → {q : DoubleCoset.Quotient ((ι₁.prod ι₂).range : Set (G₁ × G₂)) ((K₁.prod K₂ : Subgroup (G₁ × G₂)) : Set (G₁ × G₂)) | f₁ ((Quotient.out q).1⁻¹ * γ * (Quotient.out q).1) * φ ((Quotient.out q).2⁻¹ * δ * θ (Quotient.out q).2) ≠ 0}.Finite → pointSum ι₁ ι₂ θ K₁ K₂ γ δ f₁ φ = pointSide ι₁ ι₂ θ K₁ K₂ γ δ f₁ φ := by
  first | (exact @GlobalTheory.LKCountComm.pointSum_eq_pointSide_of_commensurable) | (exact GlobalTheory.LKCountComm.pointSum_eq_pointSide_of_commensurable) | (intros; apply GlobalTheory.LKCountComm.pointSum_eq_pointSide_of_commensurable  <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair

theorem _root_.GlobalTheory.T.adjunctionKlt_of_klt_along_residue_subring : ∀ {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K) (n : ℕ) (T : Subring L) (S : Place cL) (hS : S.Contains T) (ψ : S.ring →+* K) (f : S.ring) (w : Fin n → S.ring) (θ : S.ring →₀ ℚ) (R : Subring K), Function.Surjective ψ → (∀ a, ψ (S.const a) = cK a) → Irreducible f → TrBasis cK (fun i => ψ (w i)) → (∀ g ∈ θ.support, ψ g ≠ 0) → (∀ a ∈ R, ∃ t : T, ψ ⟨t, hS t t.2⟩ = a) → Klt cK n R (dForm cK (fun i => ψ (w i))) (Finsupp.mapDomain ψ θ) → AdjKlt cL (n + 1) T S (dForm cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L)) (Finsupp.mapDomain (fun g : S.ring => (g : L)) θ + Finsupp.single (f : L) 1) := by
  first | exact @GlobalTheory.FieldPair.adjKlt_of_klt_restrict | exact GlobalTheory.FieldPair.adjKlt_of_klt_restrict | (intros; apply GlobalTheory.FieldPair.adjKlt_of_klt_restrict <;> assumption)
end
