module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle085
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle083
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle024
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle084
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle041
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StHolomorphicFibreSumInt
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle007
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle074
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle003

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

theorem PrimePlaceBranchExists.proof (hA : NormalModelPointOfPlace.Statement) (hB : NormalModelDisc.Statement)
    (hC : NormalModelProjectionLocallyInjective.Statement) (hO : NormalCurveBranchOrder.Statement) :
    PrimePlaceBranchExists.Statement := by
  intro n J q hJ hdim P

  have hq : q ∈ zeroSet J := by
    by_contra h
    have := curveLocalRing_subsingleton J q h
    rw [ringKrullDim_eq_bot_of_subsingleton] at hdim
    exact absurd hdim (by decide)
  have hle : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤ (n : ℕ) := by
    refine (ringKrullDim_quotient_le J).trans ?_
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  obtain ⟨e, he⟩ : ∃ e : ℕ, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = e := by
    have h0 : (0 : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) :=
      ringKrullDim_nonneg_of_nontrivial
    generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d at h0 hle ⊢
    induction d using WithBot.recBotCoe with
    | bot => simp at h0
    | coe x =>
      induction x using ENat.recTopCoe with
      | top =>
        exfalso
        simp only [not_le.2 (show ((n : ℕ) : WithBot ℕ∞) < ((⊤ : ℕ∞) : WithBot ℕ∞) from
          WithBot.coe_lt_coe.2 (ENat.natCast_lt_top n))] at hle
      | coe e => exact ⟨e, rfl⟩
  have hloc : ringKrullDim (curveLocalRing J q) = (e : ℕ) := LocalDimDomain.proof n e J hJ he q hq
  have hdim1 : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (1 : ℕ) := by
    rw [he]
    rw [hloc] at hdim
    exact_mod_cast hdim
  obtain ⟨M⟩ := IndefiniteRowSideFullHecke.ComplexSets.NormalModelExists.proof n J hJ
  obtain ⟨w, hw, hwq, hord⟩ := hA n J q M hJ P
  obtain ⟨r, hr, φ, hφd, hφi, hφm, hφ0⟩ := hB n J M w hJ hdim1 hw
  obtain ⟨U, hU, hUi⟩ := hC n J M w hJ hdim1 hw

  have hcont : ContinuousAt φ 0 := hφd.continuousOn.continuousAt (Metric.ball_mem_nhds 0 hr)
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 (hcont.preimage_mem_nhds (hφ0 ▸ hU))
  have hρ : 0 < min r ε := lt_min hr hε
  have hsub : Metric.ball (0 : Fin 1 → ℂ) (min r ε) ⊆ Metric.ball 0 r :=
    Metric.ball_subset_ball (min_le_left _ _)
  have hsubU : ∀ t ∈ Metric.ball (0 : Fin 1 → ℂ) (min r ε), φ t ∈ U := fun t ht ↦
    hεU (Metric.ball_subset_ball (min_le_right _ _) ht)
  let ν : VarBranch J 1 q :=
    { radius := min r ε, radius_pos := hρ, toFun := fun t i ↦ φ t (Sum.inl i),
      differentiableOn := differentiableOn_pi.2 fun i ↦ differentiableOn_pi.1 (hφd.mono hsub) (Sum.inl i),
      injOn := fun a ha b hb hab ↦ hφi (hsub ha) (hsub hb)
        (hUi ⟨hφm (hsub ha), hsubU a ha⟩ ⟨hφm (hsub hb), hsubU b hb⟩ hab),
      map_zero := by
        funext i
        rw [hφ0]
        exact congrFun hwq i,
      mapsTo := fun t ht g hg ↦ by
        have hg' : rename Sum.inl g ∈ M.ideal := Ideal.mem_comap.1 (M.comap_eq.symm ▸ hg)
        have h := hφm (hsub ht) _ hg'
        rw [eval_rename] at h
        exact h }
  refine ⟨ν, fun f ↦ ?_⟩
  rw [hord f, hO n J M w (min r ε) φ hJ hdim1 hρ (hφd.mono hsub) (hφi.mono hsub) (fun t ht ↦ hφm (hsub ht)) hφ0]
  unfold branchOrder
  simp only [eval_rename]
  rfl

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory ReciprocityTheory.AnForm.A

noncomputable section

theorem abs_det_fderiv_real_mul_eq_normSq {d : ℕ} {Ω : Set (Fin d → ℂ)} {τ : (Fin d → ℂ) → Fin d → ℂ}
    (hΩ : IsOpen Ω) (hτ : DifferentiableOn ℂ τ Ω) (H : (Fin d → ℂ) → ℝ) :
    Set.EqOn (fun t => |(fderiv ℝ τ t).det| * H t) (fun t => Complex.normSq (jacC τ t).det * H t) Ω := by
  intro t ht
  simp only
  rw [det_fderiv_real_eq_normSq τ t (hτ.differentiableAt (hΩ.mem_nhds ht)),
    abs_of_nonneg (Complex.normSq_nonneg _)]

theorem HolomorphicFibreSumInt.proof (h : WeightedAreaFormula.Statement) :
    HolomorphicFibreSumInt.Statement := by
  intro d Ω τ H hΩ hτ hfin hint
  have heq := abs_det_fderiv_real_mul_eq_normSq hΩ hτ H
  have hint' : IntegrableOn (fun t => |(fderiv ℝ τ t).det| * H t) Ω :=
    (integrableOn_congr_fun heq hΩ.measurableSet).2 hint
  obtain ⟨h1, h2⟩ := h (Fin d → ℂ) volume Ω τ H hΩ (hτ.restrictScalars ℝ) hfin hint'
  exact ⟨h1, h2.trans (setIntegral_congr_fun hΩ.measurableSet heq)⟩

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology ComplexSets

noncomputable section

theorem graphChart_of_eq_on_open {n d : ℕ} {Y Y' U : Set (Fin n → ℂ)} {q : Fin n → ℂ}
    (hU : IsOpen U) (hqU : q ∈ U) (hYU : Y' ∩ U = Y ∩ U)
    (h : ∃ (A : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ)) (O : Set (Fin d → ℂ)) (V : Set (Fin n → ℂ))
      (g : (Fin d → ℂ) → Fin n → ℂ), IsOpen O ∧ IsOpen V ∧ q ∈ V ∧ AnalyticOnNhd ℂ g O ∧
        (∀ y ∈ O, A (g y) = y) ∧ Y ∩ V = g '' O) :
    ∃ (A : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ)) (O : Set (Fin d → ℂ)) (V : Set (Fin n → ℂ))
      (g : (Fin d → ℂ) → Fin n → ℂ), IsOpen O ∧ IsOpen V ∧ q ∈ V ∧ AnalyticOnNhd ℂ g O ∧
        (∀ y ∈ O, A (g y) = y) ∧ Y' ∩ V = g '' O := by
  obtain ⟨A, O, V, g, hO, hV, hqV, hg, hAg, hYV⟩ := h
  refine ⟨A, O ∩ g ⁻¹' U, V ∩ U, g, hg.continuousOn.isOpen_inter_preimage hO hU, hV.inter hU, ⟨hqV, hqU⟩,
    fun y hy => hg y hy.1, fun y hy => hAg y hy.1, ?_⟩
  rw [Set.image_inter_preimage, ← hYV]
  ext x
  constructor
  · rintro ⟨hx, hxV, hxU⟩
    have hx' : x ∈ Y ∩ U := by rw [← hYU]; exact ⟨hx, hxU⟩
    exact ⟨⟨hx'.1, hxV⟩, hxU⟩
  · rintro ⟨⟨hx, hxV⟩, hxU⟩
    have hx' : x ∈ Y' ∩ U := by rw [hYU]; exact ⟨hx, hxU⟩
    exact ⟨hx'.1, hxV, hxU⟩

theorem ringKrullDim_quotient_minimalPrime_add_one {n : ℕ} {V W : Ideal (MvPolynomial (Fin n) ℂ)} [hVp : V.IsPrime]
    {f : MvPolynomial (Fin n) ℂ} (hf : f ∉ V) (hW : W ∈ (V ⊔ Ideal.span {f}).minimalPrimes)
    (hfin : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ V) ≠ ⊤) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) + 1 = ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ V) := by
  have hPW : V ≤ W := le_sup_left.trans hW.1.2
  have hfW : f ∈ W := hW.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
  have hq : W.map (Ideal.Quotient.mk V) ∈ (Ideal.span {Ideal.Quotient.mk V f}).minimalPrimes := by
    have e : Ideal.span {Ideal.Quotient.mk V f} = (Ideal.span {f}).map (Ideal.Quotient.mk V) := by
      rw [Ideal.map_span, Set.image_singleton]
    rw [e, Ideal.minimalPrimes_map_of_surjective Ideal.Quotient.mk_surjective, Ideal.mk_ker, sup_comm]
    exact ⟨W, hW, rfl⟩
  have : (W.map (Ideal.Quotient.mk V)).IsPrime := hq.1.1
  have : (Ideal.span {Ideal.Quotient.mk V f}).IsPrincipal := ⟨⟨_, rfl⟩⟩
  have hh : (W.map (Ideal.Quotient.mk V)).height = 1 := by
    refine le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hq) ?_
    rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
    intro h0
    have : Ideal.Quotient.mk V f ∈ W.map (Ideal.Quotient.mk V) := Ideal.mem_map_of_mem _ hfW
    rw [h0, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at this
    exact hf this
  have : IsDomain (MvPolynomial (Fin n) ℂ ⧸ V) := Ideal.Quotient.isDomain V
  have : Algebra.FiniteType ℂ (MvPolynomial (Fin n) ℂ ⧸ V) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ V) (Ideal.Quotient.mkₐ_surjective ℂ V)
  have : IsNoetherianRing (MvPolynomial (Fin n) ℂ ⧸ V) := Algebra.FiniteType.isNoetherianRing ℂ _
  have : FiniteRingKrullDim (MvPolynomial (Fin n) ℂ ⧸ V) :=
    finiteRingKrullDim_iff_ne_bot_and_top.mpr ⟨fun h => by
      have h0 := ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial (Fin n) ℂ ⧸ V)
      rw [h] at h0
      exact absurd h0 (by simp), hfin⟩
  obtain ⟨s, hs⟩ := ReciprocityTheory.ChartRestriction.G.Geo.DimF.exists_height_of_isMaximal_of_field ℂ (MvPolynomial (Fin n) ℂ ⧸ V)
  have key := ReciprocityTheory.ChartRestriction.G.Geo.DimF.dim_quot_add_height (A := MvPolynomial (Fin n) ℂ ⧸ V)
    (fun M N hM hN => (hs M hM).trans (hs N hN).symm) (W.map (Ideal.Quotient.mk V))
  rw [hh, ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hPW)] at key
  exact_mod_cast key

theorem ringKrullDim_quotient_sup_span_lt {R : Type*} [CommRing R] {L : Ideal R} {f : R} {d : ℕ}
    (hf : ∀ W ∈ L.minimalPrimes, f ∉ W) (hd : ∀ W ∈ L.minimalPrimes, ringKrullDim (R ⧸ W) = d) :
    ringKrullDim (R ⧸ (L ⊔ Ideal.span {f})) < d := by
  rw [ringKrullDim_quotient, Order.krullDim_lt_coe_iff]
  intro l
  have hLP : L ≤ l.head.1.asIdeal := fun x hx => l.head.2 (Ideal.mem_sup_left hx)
  have hfP : f ∈ l.head.1.asIdeal := l.head.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
  obtain ⟨W, hW, hWP⟩ := Ideal.exists_minimalPrimes_le hLP
  let W' : PrimeSpectrum R := ⟨W, hW.1.1⟩
  have hlt : W' < l.head.1 := lt_of_le_of_ne hWP fun h => hf W hW (by rw [← h] at hfP; exact hfP)
  have h1 : (l.length : ℕ∞) ≤ Order.coheight l.head.1 := by
    exact Order.length_le_coheight_head (p := l.map Subtype.val (fun _ _ => id))
  have h2 : Order.coheight l.head.1 + 1 ≤ Order.coheight W' := Order.coheight_add_one_le hlt
  have hIci : Set.Ici W' = PrimeSpectrum.zeroLocus (R := R) (W : Set R) := by
    ext p
    exact Iff.rfl
  have h3 : ((Order.coheight W' : ℕ∞) : WithBot ℕ∞) = (d : WithBot ℕ∞) := by
    rw [Order.coheight_eq_krullDim_Ici, hIci, ← ringKrullDim_quotient]
    exact hd W hW
  have h3' : Order.coheight W' = (d : ℕ∞) := by exact_mod_cast h3
  have h4 : ((l.length + 1 : ℕ) : ℕ∞) ≤ (d : ℕ∞) := by
    rw [← h3']
    push_cast
    calc (l.length : ℕ∞) + 1 ≤ Order.coheight l.head.1 + 1 := by gcongr
      _ ≤ Order.coheight W' := h2
  have h5 : l.length + 1 ≤ d := by exact_mod_cast h4
  omega

theorem graphChart_of_frameGraphGeneric (hG : FrameGraphGeneric.Statement) {n e : ℕ}
    (W : Ideal (MvPolynomial (Fin n) ℂ)) (hW : W.IsPrime)
    (he : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = e) :
    ∃ h : MvPolynomial (Fin n) ℂ, h ∉ W ∧ ∀ z ∈ zeroSet W, eval z h ≠ 0 →
      ∃ (A : (Fin n → ℂ) →L[ℂ] (Fin e → ℂ)) (O : Set (Fin e → ℂ)) (V : Set (Fin n → ℂ))
        (g : (Fin e → ℂ) → Fin n → ℂ), IsOpen O ∧ IsOpen V ∧ z ∈ V ∧ AnalyticOnNhd ℂ g O ∧
          (∀ y ∈ O, A (g y) = y) ∧ zeroSet W ∩ V = g '' O := by
  obtain ⟨I₀, h, hcard, hhW, hreg⟩ := hG n e W hW he (EuclideanSpace.basisFun (Fin n) ℂ)
  let T : (Fin n → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    ((EuclideanSpace.equiv (Fin n) ℂ).symm : (Fin n → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n))
  let S : EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin n → ℂ) :=
    ((EuclideanSpace.equiv (Fin n) ℂ : EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin n → ℂ)))
  have hT : ∀ x i, T x i = x i := fun x i => rfl
  have hS : ∀ w i, S w i = w i := fun w i => rfl
  have hST : ∀ x, S (T x) = x := fun x => funext fun i => by rw [hS, hT]
  have hTS : ∀ w, T (S w) = w := fun w => by ext i; rw [hT, hS]
  have hZ : ∀ x : Fin n → ℂ, x ∈ zeroSet W ↔ T x ∈ zeroSetEuc W := by
    intro x
    have hx : (fun i => T x i) = x := funext fun i => hT x i
    simp only [zeroSet, zeroSetEuc, Set.mem_ofPred_eq, hx]
  refine ⟨h, hhW, fun z hz hzh => ?_⟩
  have hzh' : eval (fun i => T z i) h ≠ 0 := by
    have hx : (fun i => T z i) = z := funext fun i => hT z i
    rwa [hx]
  obtain ⟨Ω, V, g, hΩ, hV, hzV, hg, hproj, hgraph⟩ := hreg (T z) ((hZ z).mp hz) hzh'
  let eI : I₀ ≃ Fin e := I₀.equivFinOfCardEq hcard
  let Ψ : (Fin e → ℂ) →L[ℂ] (I₀ → ℂ) :=
    ContinuousLinearMap.pi fun i : I₀ => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin e => ℂ) (eI i)
  let A : (Fin n → ℂ) →L[ℂ] (Fin e → ℂ) :=
    ContinuousLinearMap.pi fun k : Fin e =>
      ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) ((eI.symm k : I₀) : Fin n)
  have hΨ : ∀ y i, Ψ y i = y (eI i) := fun y i => rfl
  have hA : ∀ x k, A x k = x ((eI.symm k : I₀) : Fin n) := fun x k => rfl
  have hO : IsOpen (Ψ ⁻¹' Ω) := hΩ.preimage Ψ.continuous
  refine ⟨A, Ψ ⁻¹' Ω, T ⁻¹' V, fun y => S (g (Ψ y)), hO, hV.preimage T.continuous, hzV, ?_, ?_, ?_⟩
  · exact IndefiniteRowSideFullHecke.ComplexSets.analyticOnNhd_of_differentiableOn_fin hO (S.differentiable.comp_differentiableOn
      (hg.comp Ψ.differentiable.differentiableOn fun y hy => hy))
  · intro y hy
    ext k
    have h1 := congrFun (hproj (Ψ y) hy) (eI.symm k)
    simp only [frameProj, EuclideanSpace.basisFun_inner] at h1
    show A (S (g (Ψ y))) k = y k
    rw [hA, hS, h1, hΨ, Equiv.apply_symm_apply]
  · ext x
    constructor
    · rintro ⟨hxZ, hxV⟩
      have hmem : T x ∈ zeroSetEuc W ∩ V := ⟨(hZ x).mp hxZ, hxV⟩
      rw [hgraph] at hmem
      obtain ⟨w, hw, hgw⟩ := hmem
      have hΨw : Ψ (fun k => w (eI.symm k)) = w := funext fun i => by simp [hΨ]
      refine ⟨fun k => w (eI.symm k), ?_, ?_⟩
      · show Ψ _ ∈ Ω
        rwa [hΨw]
      · simp only [hΨw, hgw, hST]
    · rintro ⟨y, hy, rfl⟩
      have hmem : g (Ψ y) ∈ zeroSetEuc W ∩ V := hgraph ▸ Set.mem_image_of_mem g hy
      refine ⟨(hZ _).mpr ?_, ?_⟩
      · rw [hTS]
        exact hmem.1
      · show T (S (g (Ψ y))) ∈ V
        rw [hTS]
        exact hmem.2

end

end GroundTheory.Heights₂.Heights
end
