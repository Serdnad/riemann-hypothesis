module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Statements
public import Mathlib.Topology.Separation.CompletelyRegular
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LogIntPoly
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ReducedTensorPerfect
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LogGaussNormSupportFinite
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.Nullstellensatz
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
public import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix

noncomputable section

namespace ConeFibreDegree

theorem ae_eval_ne_zero_univ {ι : Type*} [Fintype ι] (g : MvPolynomial ι ℂ) (hg : g ≠ 0) :
    ∀ᵐ u : ι → ℂ, eval u g ≠ 0 := by
  have hU : (⋃ r : ℕ, LogInt.polydisc ι r) = Set.univ := by
    refine Set.eq_univ_of_forall fun u => ?_
    obtain ⟨r, hr⟩ := exists_nat_ge ‖u‖
    refine Set.mem_iUnion.mpr ⟨r, Set.mem_univ_pi.mpr fun i => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (norm_le_pi_norm u i).trans hr
  have h := (ae_restrict_iUnion_iff (fun r : ℕ => LogInt.polydisc ι r) (fun u => eval u g ≠ 0)).mpr
    fun r => LogInt.ae_eval_ne_zero g hg r
  rwa [hU, Measure.restrict_univ] at h

theorem ae_eval_matrix_ne_zero {k n : ℕ} (g : MvPolynomial (Fin k × Fin n) ℂ) (hg : g ≠ 0) :
    ∀ᵐ π : Fin k → Fin n → ℂ, eval (fun ij => π ij.1 ij.2) g ≠ 0 := by
  have hmap : (volume : Measure (Fin k → Fin n → ℂ)) =
      (volume : Measure (Fin k × Fin n → ℂ)).map (MeasurableEquiv.curry (Fin k) (Fin n) ℂ) := by
    rw [ObjectsHeight.map_curry_volume]
    rfl
  rw [hmap, (MeasurableEquiv.curry (Fin k) (Fin n) ℂ).measurableEmbedding.ae_map_iff]
  exact ae_eval_ne_zero_univ g hg

theorem ae_eval_euclid_ne_zero {m : ℕ} (g : MvPolynomial (Fin m) ℂ) (hg : g ≠ 0) :
    ∀ᵐ w : EuclideanSpace ℂ (Fin m), eval (WithLp.ofLp w) g ≠ 0 := by
  let L : EuclideanSpace ℂ (Fin m) ≃L[ℝ] (Fin m → ℂ) :=
    (PiLp.continuousLinearEquiv 2 ℝ fun _ : Fin m => ℂ)
  have hac : (volume : Measure (EuclideanSpace ℂ (Fin m))).map L ≪ volume :=
    Measure.absolutelyContinuous_isAddHaarMeasure _ _
  have h : ∀ᵐ u ∂(volume : Measure (EuclideanSpace ℂ (Fin m))).map L, eval u g ≠ 0 :=
    hac.ae_le (ae_eval_ne_zero_univ g hg)
  rw [ae_map_iff L.continuous.measurable.aemeasurable] at h
  · exact h
  · exact (isClosed_eq (continuous_eval g) continuous_const).isOpen_compl.measurableSet

theorem fibreCount_eq {k n : ℕ} (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (π : Fin k → Fin n → ℂ) (w : EuclideanSpace ℂ (Fin k)) :
    fibreCount h W π w =
      (ComplexSets.fibre W (Matrix.of π * (h.matᵀ)⁻¹) (WithLp.ofLp w)).encard := by
  have hu : IsUnit h.matᵀ.det := by rw [det_transpose]; exact h.isUnit_det
  have hinj : Function.Injective h.pointOf := by
    intro y y' hyy
    have hv := congrArg (fun v => (h.matᵀ)⁻¹ *ᵥ v) hyy
    simp only [HermNorm.pointOf, mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec] at hv
    exact WithLp.ofLp_injective 2 hv
  have hπ : ∀ y : EuclideanSpace ℂ (Fin n),
      (Matrix.of π * (h.matᵀ)⁻¹) *ᵥ h.pointOf y = WithLp.ofLp (linProj π y) := by
    intro y
    rw [HermNorm.pointOf, mulVec_mulVec, Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.mul_one]
    ext i
    simp [linProj, mulVec, dotProduct]
  rw [fibreCount, ← hinj.injOn.encard_image]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_ofPred_eq, ComplexSets.fibre, ComplexSets.zeroSet, coneSet]
  constructor
  · rintro ⟨y, ⟨hy, rfl⟩, rfl⟩
    exact ⟨hy, hπ y⟩
  · rintro ⟨hx, hxw⟩
    have hpt : h.pointOf (WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)) = x := by
      simp [HermNorm.pointOf, mulVec_mulVec, mul_nonsing_inv _ hu]
    refine ⟨WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x), ⟨?_, ?_⟩, hpt⟩
    · rw [hpt]; exact hx
    · apply WithLp.ofLp_injective 2
      rw [← hπ, hpt, hxw]

theorem proof (hD : ConeDimOfChowForm.Statement)
    (hG : ComplexSets.GenericProjectionFinite.Statement)
    (hC : ComplexSets.DiscriminantCover.Statement) (hP : ProjDegreeChow.Statement) :
    ConeFibreDegree.Statement := by
  intro n e δ h W f hW hf hδ
  have hdim := hD ℂ n (e + 1) W f hW hf
  obtain ⟨⟨U, ⟨S, hS⟩, ⟨A₀, hA₀⟩, hUfin⟩, -, -, -⟩ := hG n (e + 1) W hW.isPrime hdim
  rw [hS] at hA₀
  obtain ⟨p, hpS, hp⟩ := hA₀
  have hu : IsUnit h.matᵀ.det := by rw [det_transpose]; exact h.isUnit_det
  set B := (h.matᵀ)⁻¹ with hB
  set q : MvPolynomial (Fin (e + 1) × Fin n) ℂ :=
    bind₁ (fun ij => ∑ k, X (ij.1, k) * C (B k ij.2)) p with hqdef
  have hq : ∀ π : Fin (e + 1) → Fin n → ℂ,
      eval (fun ij => π ij.1 ij.2) q = eval (fun ij => (Matrix.of π * B) ij.1 ij.2) p := by
    intro π
    show eval₂Hom (RingHom.id ℂ) _ q = eval₂Hom (RingHom.id ℂ) _ p
    rw [hqdef, eval₂Hom_bind₁]
    congr 2
    funext ij
    simp [Matrix.mul_apply]
  have hq0 : q ≠ 0 := by
    intro h0
    have h1 := hq fun i j => (A₀ * h.matᵀ) i j
    have hA : Matrix.of (fun i j => (A₀ * h.matᵀ) i j) * B = A₀ := by
      rw [hB, show Matrix.of (fun i j => (A₀ * h.matᵀ) i j) = A₀ * h.matᵀ from rfl, Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.mul_one]
    rw [h0, map_zero, hA] at h1
    exact hp h1.symm
  filter_upwards [ae_eval_matrix_ne_zero q hq0] with π hπ
  have hfin : ComplexSets.IsFiniteProjection W (Matrix.of π * B) := by
    have hmem : Matrix.of π * B ∈ {A : Matrix (Fin (e + 1)) (Fin n) ℂ |
        ∃ p ∈ S, eval (fun ij => A ij.1 ij.2) p ≠ 0} := ⟨p, hpS, by rw [← hq]; exact hπ⟩
    rw [← hS] at hmem
    exact hUfin _ hmem
  obtain ⟨P, hP0, hPy⟩ := hC n (e + 1) W (Matrix.of π * B) hW.isPrime hdim hfin
  filter_upwards [ae_eval_euclid_ne_zero P hP0] with w hw
  obtain ⟨hfinite, hcard, -⟩ := hPy _ hw
  rw [fibreCount_eq, ← hfinite.cast_ncard_eq, hcard, hP n e δ W f _ hW hf hδ hfin]

end ConeFibreDegree

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace ChartChoiceAlgClosed

variable {F : Type} [Field F] {n e : ℕ}

theorem isChowForm_iff_span {P : Ideal (MvPolynomial (Fin n) F)} {k : ℕ}
    {g : MvPolynomial (Fin k × Fin n) F} :
    IsChowForm P k g ↔ g ≠ 0 ∧ incIdeal P k = Ideal.span {g} := by
  have hmem : ∀ G : MvPolynomial (Fin k × Fin n) F,
      G ∈ incIdeal P k ↔ ∀ v ∈ incidence P k, aeval v G = 0 := fun G => by
    simp [incIdeal, Submodule.mem_iInf, RingHom.mem_ker]
  constructor
  · rintro ⟨h0, h⟩
    refine ⟨h0, ?_⟩
    ext G
    rw [hmem, Ideal.mem_span_singleton]
    exact h G
  · rintro ⟨h0, h⟩
    refine ⟨h0, fun G => ?_⟩
    rw [← hmem, h, Ideal.mem_span_singleton]

def shiftVar (e n : ℕ) : Fin e × Fin n → Fin (e + 1) × Fin n := fun jm => (jm.1.succ, jm.2)

def splitFirst (F : Type) [Field F] (e n : ℕ) :
    MvPolynomial (Fin (e + 1) × Fin n) F →ₐ[F] MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) F) :=
  aeval fun ij => Fin.cases (motive := fun _ => MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) F))
    (X ij.2) (fun j => C (X (j, ij.2))) ij.1

def joinFirst (F : Type) [Field F] (e n : ℕ) :
    MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) F) →+* MvPolynomial (Fin (e + 1) × Fin n) F :=
  eval₂Hom (rename (shiftVar e n)).toRingHom (fun m => X (0, m))

theorem joinFirst_splitFirst (p : MvPolynomial (Fin (e + 1) × Fin n) F) :
    joinFirst F e n (splitFirst F e n p) = p := by
  have h : (joinFirst F e n).comp (splitFirst F e n).toRingHom = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [joinFirst, splitFirst, MvPolynomial.algebraMap_eq]
    · rintro ⟨i, m⟩
      induction i using Fin.cases <;> simp [joinFirst, splitFirst, shiftVar]
  exact RingHom.congr_fun h p

theorem joinFirst_C (a : MvPolynomial (Fin e × Fin n) F) :
    joinFirst F e n (C a) = rename (shiftVar e n) a := by
  simp [joinFirst]

theorem specFirst_rename_shiftVar (q : MvPolynomial (Fin e × Fin n) F) :
    specFirst (rename (shiftVar e n) q) 0 = q := by
  unfold specFirst
  rw [bind₁_rename]
  have : (specFirstVar (0 : Fin n → F) ∘ shiftVar e n) = X := by
    funext jm
    simp [specFirstVar, shiftVar]
  rw [this, bind₁_X_left]
  rfl

theorem specFirst_zero_of_isMultiHomog {δ : ℕ} (hδ : 1 ≤ δ) {f : MvPolynomial (Fin (e + 1) × Fin n) F}
    (hf : IsMultiHomog δ f) : specFirst f 0 = 0 := by
  classical
  unfold specFirst
  conv_lhs => rw [f.as_sum]

  rw [map_sum]
  refine Finset.sum_eq_zero fun s hs => ?_
  rw [bind₁_monomial]
  obtain ⟨i, hi, h0⟩ : ∃ i ∈ s.support, i.1 = 0 := by
    by_contra hno
    push Not at hno
    have hw := congrFun (hf (mem_support_iff.mp hs)) 0
    rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply] at hw
    have : ∑ c ∈ s.support, (s c • groupWeight (e + 1) n c) 0 = 0 := by
      refine Finset.sum_eq_zero fun c hc => ?_
      simp [groupWeight, Ne.symm (hno c hc)]
    omega
  rw [Finset.prod_eq_zero hi, mul_zero]
  obtain ⟨a, m⟩ := i
  simp only at h0
  subst h0
  simp [specFirstVar, zero_pow (Finsupp.mem_support_iff.mp hi)]

theorem eval_map_splitFirst (J : Ideal (MvPolynomial (Fin e × Fin n) F)) (t : Fin n → F)
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) :
    eval (fun m => Ideal.Quotient.mk J (C (t m))) (map (Ideal.Quotient.mk J) (splitFirst F e n f)) =
      Ideal.Quotient.mk J (specFirst f t) := by
  rw [eval_map]
  have h : (eval₂Hom (Ideal.Quotient.mk J) (fun m => Ideal.Quotient.mk J (C (t m)))).comp
      (splitFirst F e n).toRingHom = (Ideal.Quotient.mk J).comp (bind₁ (specFirstVar t)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [splitFirst, MvPolynomial.algebraMap_eq]
    · rintro ⟨i, m⟩
      induction i using Fin.cases <;> simp [splitFirst, specFirstVar, MvPolynomial.algebraMap_eq, MvPolynomial.bind₁_X_right] <;> rfl
  exact RingHom.congr_fun h f

end ChartChoiceAlgClosed


open ChartChoiceAlgClosed in
theorem ChartChoiceAlgClosed.proof (h₁ : IncIdealPrime.Statement) (h₂ : ChowFormMultiHomog.Statement) :
    ChartChoiceAlgClosed.Statement := by
  intro F _ _ n e I f q hI hf hq
  classical
  obtain ⟨hf0, hspan⟩ := isChowForm_iff_span.mp hf
  have hfp : Prime f := by
    have := h₁ F n (e + 1) I hI.isPrime hI.isRelevant
    rw [hspan] at this
    exact (Ideal.span_singleton_prime hf0).mp this
  obtain ⟨δ, hδ, hhom⟩ := h₂ F n (e + 1) I f hI hf

  have hndvd : ¬ rename (shiftVar e n) q ∣ f := by
    rintro ⟨g, hg⟩
    rcases hfp.2.2 (rename (shiftVar e n) q) g (hg ▸ dvd_refl f) with ⟨h, hh⟩ | ⟨h, hh⟩
    · have := congrArg (fun p => specFirst p 0) hh
      rw [specFirst_rename_shiftVar] at this
      unfold specFirst at this
      rw [map_mul] at this
      have h0 : specFirst f 0 = 0 := specFirst_zero_of_isMultiHomog hδ hhom
      unfold specFirst at h0
      rw [h0, zero_mul] at this
      exact hq.ne_zero this
    · have hunit : IsUnit (rename (shiftVar e n) q) := by
        refine isUnit_iff_exists_inv.mpr ⟨h, ?_⟩
        apply mul_left_cancel₀ hf0
        calc f * (rename (shiftVar e n) q * h) = rename (shiftVar e n) q * (f * h) := by ring
          _ = f * 1 := by rw [← hh, ← hg, mul_one]
      have := hunit.map (bind₁ (specFirstVar (0 : Fin n → F)))
      have h' : bind₁ (specFirstVar (0 : Fin n → F)) (rename (shiftVar e n) q) = q :=
        specFirst_rename_shiftVar q
      rw [h'] at this
      exact hq.not_isUnit this
  set J : Ideal (MvPolynomial (Fin e × Fin n) F) := Ideal.span {q} with hJ
  have : J.IsPrime := (Ideal.span_singleton_prime hq.ne_zero).mpr hq
  set P := map (Ideal.Quotient.mk J) (splitFirst F e n f) with hP
  have hP0 : P ≠ 0 := by
    intro h0
    have hmem : splitFirst F e n f ∈ RingHom.ker (map (σ := Fin n) (Ideal.Quotient.mk J)) := by
      rw [RingHom.mem_ker]; exact h0
    rw [MvPolynomial.ker_map, Ideal.mk_ker, hJ, Ideal.map_span, Set.image_singleton,
      Ideal.mem_span_singleton] at hmem
    apply hndvd
    have := map_dvd (joinFirst F e n) hmem
    rwa [joinFirst_splitFirst, joinFirst_C] at this

  let g : ℕ ↪ F := Infinite.natEmbedding F
  have hinj : Function.Injective fun k : ℕ => Ideal.Quotient.mk J (C (g k)) := by
    intro a b hab
    apply g.injective
    apply (algebraMap F (MvPolynomial (Fin e × Fin n) F ⧸ J)).injective
    exact hab
  by_contra hall
  push Not at hall
  apply hP0
  refine eq_zero_of_eval_zero_at_prod_finset P
    (fun _ => (Finset.range (P.totalDegree + 1)).image (fun k : ℕ => Ideal.Quotient.mk J (C (g k))))
    (fun i => ?_) (fun x hx => ?_)
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_range]
    exact Nat.lt_succ_of_le (degreeOf_le_totalDegree P i)
  · choose k _ hk using fun i => Finset.mem_image.mp (hx i)
    have hx' : x = fun m => Ideal.Quotient.mk J (C ((fun m => g (k m)) m)) := by
      funext m
      rw [← hk m]
    rw [hx', hP, eval_map_splitFirst]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (hall _))

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem BaseChangeAvoid.comap_eq_of_mem_minimalPrimes {K L : Type*} [Field K] [Field L] {n : ℕ}
    (σ : K →+* L) (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    {W : Ideal (MvPolynomial (Fin n) L)} (hW : W ∈ (I.map (MvPolynomial.map σ)).minimalPrimes) :
    W.comap (MvPolynomial.map σ) = I := by
  let : Algebra K L := σ.toAlgebra
  let : Algebra (MvPolynomial (Fin n) K) (MvPolynomial (Fin n) L) := algebraMvPolynomial
  have : Module.Free K L := Module.Free.of_divisionRing K L
  have : Module.Flat (MvPolynomial (Fin n) K) (MvPolynomial (Fin n) L) :=
    Module.Flat.isBaseChange K (MvPolynomial (Fin n) K) L (MvPolynomial (Fin n) L)
      Algebra.IsPushout.out
  have halg : algebraMap (MvPolynomial (Fin n) K) (MvPolynomial (Fin n) L) = MvPolynomial.map σ :=
    rfl
  obtain ⟨⟨hWp, hIW⟩, hmin⟩ := hW
  have := hWp
  have hIP : I ≤ W.comap (MvPolynomial.map σ) := Ideal.map_le_iff_le_comap.mp hIW
  have : (W.comap (MvPolynomial.map σ)).IsPrime := Ideal.comap_isPrime _ W
  have : W.LiesOver (W.comap (MvPolynomial.map σ)) := ⟨by rw [Ideal.under_def, halg]⟩
  obtain ⟨W', hW'W, hW'p, hW'I⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := I) W hIP
  have hI' : I = W'.comap (MvPolynomial.map σ) := by rw [hW'I.over, Ideal.under_def, halg]
  have hIW' : I.map (MvPolynomial.map σ) ≤ W' := Ideal.map_le_iff_le_comap.mpr hI'.le
  have hWW' : W ≤ W' := hmin ⟨hW'p, hIW'⟩ hW'W
  rw [hI', le_antisymm hW'W hWW']

theorem BaseChangeAvoid.proof : BaseChangeAvoid.Statement := by
  intro K _ _ n I u σ hI hu W hW h
  have hW' : W ∈ relComps (I.map (MvPolynomial.map σ)) := by
    by_contra hn
    rw [Finsupp.mem_support_iff] at hW
    exact hW (by simp [fundCycle, Finsupp.onFinset_apply, hn])
  have := hI.isPrime
  have hc := BaseChangeAvoid.comap_eq_of_mem_minimalPrimes σ I hW'.1
  apply hu
  rw [← hc, Ideal.mem_comap]
  convert h using 1

  simp [linForm, map_sum]

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open TensorProduct

noncomputable section

theorem RadicalBaseChange.proof : RadicalBaseChange.Statement := by
  intro K L _ _ _ σ ι I hI
  let : Algebra K L := σ.toAlgebra
  rw [Ideal.isRadical_iff_quotient_reduced] at hI ⊢
  have h1 : IsReduced (L ⊗[K] (MvPolynomial ι K ⧸ I)) :=
    isReduced_tensorProduct_of_perfectField K L _
  let e1 := Algebra.TensorProduct.tensorQuotientEquiv (R := K) L (MvPolynomial ι K) L I
  let e2 : L ⊗[K] MvPolynomial ι K ≃ₐ[L] MvPolynomial ι L := MvPolynomial.algebraTensorAlgEquiv K L
  have hmap : I.map (MvPolynomial.map σ) =
      (I.map (Algebra.TensorProduct.includeRight (R := K) (A := L))).map
        (e2 : L ⊗[K] MvPolynomial ι K →+* MvPolynomial ι L) := by
    rw [← Ideal.map_coe (Algebra.TensorProduct.includeRight (R := K) (A := L)), Ideal.map_map]
    congr 1
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [e2, MvPolynomial.algebraTensorAlgEquiv_tmul, RingHom.algebraMap_toAlgebra]
    · intro i
      simp [e2, MvPolynomial.algebraTensorAlgEquiv_tmul]
  let e3 := Ideal.quotientEquivAlg (I.map (Algebra.TensorProduct.includeRight (R := K) (A := L)))
    (I.map (MvPolynomial.map σ)) e2 hmap
  exact isReduced_of_injective (e1.toRingEquiv.trans e3.toRingEquiv).symm (RingEquiv.injective _)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

theorem finsum_log_gaussNorm_mul {ι : Type*} {f g : MvPolynomial ι K} (hf : f ≠ 0) (hg : g ≠ 0) :
    ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), Real.log (gaussNorm v (f * g)) =
      (∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), Real.log (gaussNorm v f)) +
        ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), Real.log (gaussNorm v g) := by
  rw [← finsum_add_distrib (log_gaussNorm_support_finite hf) (log_gaussNorm_support_finite hg)]
  refine finsum_congr fun v => ?_
  rw [gaussNorm_mul, Real.log_mul (gaussNorm_pos v hf).ne' (gaussNorm_pos v hg).ne']

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial


open Classical in
def SectionOrderAlgClosed.Statement : Prop :=
  ∀ (F : Type) [Field F] [IsAlgClosed F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (u : Fin n → F),
    IsProjPrime I → IsChowForm I (e + 1) f → linForm u ∉ I →
      specFirst f u ≠ 0 ∧ ∀ q : MvPolynomial (Fin e × Fin n) F, Irreducible q →
        emultiplicity q (specFirst f u) =
          ∑ W ∈ (divCycle I u).support with Ideal.span {q} = incIdeal W e,
            ((divCycle I u W : ℕ) : ℕ∞)

end GroundTheory.Heights₂.Heights
end
