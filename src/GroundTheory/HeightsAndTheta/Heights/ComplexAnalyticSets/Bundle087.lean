module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle067
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle051
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetSumMeasurable
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle068
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle033
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle071
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.Ideal.HasGoingUp
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

namespace PosPartLocal

variable {n d : ℕ}

theorem chartPosDens_eq {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {s : (Fin d → ℂ) → Fin n → ℂ} {U : Set (Fin d → ℂ)} {W E : Set (Fin n → ℂ)}
    (hU : IsOpen U) (hsd : DifferentiableOn ℂ s U)
    (hsec : ∀ y ∈ U, A *ᵥ s y = y ∧ s y ∈ zeroSet J)
    (hW : IsOpen W) (hWs : ∀ x' ∈ zeroSet J ∩ W, A *ᵥ x' ∈ U ∧ s (A *ᵥ x') = x')
    (hEW : E ⊆ W) (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (y : Fin d → ℂ) :
    chartPosDens J A (E.indicator f) φ y = (U ∩ s ⁻¹' E).indicator
      (fun y => max (f (s y) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) y) 0) y := by
  classical
  unfold chartPosDens sheetSum
  by_cases hy : y ∈ U ∩ s ⁻¹' E
  · rw [Set.indicator_of_mem hy]
    have hfib : s y ∈ fibre J A y := ⟨(hsec y hy.1).2, (hsec y hy.1).1⟩
    have hsh : IsSheetAt J A (s y) s :=
      ⟨U, hU, by rw [(hsec y hy.1).1]; exact hy.1, hsd, by rw [(hsec y hy.1).1], hsec, W,
        hW.mem_nhds (hEW hy.2), fun x' hx' _ => (hWs x' hx').2.symm⟩
    rw [finsum_eq_single _ (s y) ?_, finsum_eq_if, if_pos hfib, dite_eq_left ⟨s, hsh⟩]
    · have h := SheetSumMeasurable.term_eq (fun a b => max (a * b) 0) (E.indicator f) φ hsh ⟨s, hsh⟩
      rw [(hsec y hy.1).1] at h
      dsimp only
      rw [h, Set.indicator_of_mem (show s y ∈ E from hy.2)]
    · intro x hne
      rw [finsum_eq_if]
      split_ifs with hx h
      · have hxE : x ∉ E := fun hxE => hne (by
          have h' := (hWs x ⟨hx.1, hEW hxE⟩).2
          rw [hx.2] at h'
          exact h'.symm)
        dsimp only
        rw [Set.indicator_of_notMem hxE, zero_mul, max_self]
      · rfl
      · rfl
  · rw [Set.indicator_of_notMem hy]
    refine finsum_mem_eq_zero_of_forall_eq_zero fun x hx => ?_
    split_ifs with h
    · have hxE : x ∉ E := fun hxE => hy (by
        obtain ⟨h1, h2⟩ := hWs x ⟨hx.1, hEW hxE⟩
        rw [hx.2] at h1 h2
        exact ⟨h1, by rw [Set.mem_preimage, h2]; exact hxE⟩)
      dsimp only
      rw [Set.indicator_of_notMem hxE, zero_mul, max_self]
    · rfl

end PosPartLocal

theorem PosPartLocal.proof : PosPartLocal.Statement := by
  rintro n d J A A' f φ x - hφ ⟨s, U, hU, hxU, hsd, -, hsec, V, hV, hVs⟩
    ⟨s', U', hU', hxU', hsd', -, hsec', V', hV', hVs'⟩
  have hAc : Continuous fun z : Fin n → ℂ => A *ᵥ z := by fun_prop
  have hAc' : Continuous fun z : Fin n → ℂ => A' *ᵥ z := by fun_prop
  set W := (interior V ∩ (fun z => A *ᵥ z) ⁻¹' U) ∩ (interior V' ∩ (fun z => A' *ᵥ z) ⁻¹' U')
    with hWdef
  have hW : IsOpen W :=
    (isOpen_interior.inter (hU.preimage hAc)).inter (isOpen_interior.inter (hU'.preimage hAc'))
  have hWs : ∀ x' ∈ zeroSet J ∩ W, A *ᵥ x' ∈ U ∧ s (A *ᵥ x') = x' :=
    by rintro x' ⟨hZ, ⟨hV1, hU1⟩, -⟩; exact ⟨hU1, (hVs x' ⟨hZ, interior_subset hV1⟩ hU1).symm⟩
  have hWs' : ∀ x' ∈ zeroSet J ∩ W, A' *ᵥ x' ∈ U' ∧ s' (A' *ᵥ x') = x' :=
    by rintro x' ⟨hZ, -, ⟨hV1, hU1⟩⟩; exact ⟨hU1, (hVs' x' ⟨hZ, interior_subset hV1⟩ hU1).symm⟩
  refine ⟨W, hW, ⟨⟨mem_interior_iff_mem_nhds.2 hV, hxU⟩, ⟨mem_interior_iff_mem_nhds.2 hV', hxU'⟩⟩,
    fun E _ hEW => ?_⟩
  simp_rw [PosPartLocal.chartPosDens_eq hU hsd hsec hW hWs hEW,
    PosPartLocal.chartPosDens_eq hU' hsd' hsec' hW hWs' hEW]

  set O' := U' ∩ s' ⁻¹' W with hO'def
  set τ : (Fin d → ℂ) → Fin d → ℂ := fun z => A *ᵥ s' z with hτdef
  have hO' : IsOpen O' := hsd'.continuousOn.isOpen_inter_preimage hU' hW
  have hτU : ∀ z ∈ O', τ z ∈ U ∧ s (τ z) = s' z := fun z hz => hWs _ ⟨(hsec' z hz.1).2, hz.2⟩
  have hτd : DifferentiableOn ℂ τ O' := by
    have hs'O : DifferentiableOn ℂ s' O' := hsd'.mono Set.inter_subset_left
    exact ((Matrix.mulVecLin A).toContinuousLinearMap.differentiable.comp_differentiableOn hs'O)
  have hτan : AnalyticOnNhd ℂ τ O' := IndefiniteRowSideFullHecke.ComplexSets.analyticOnNhd_of_differentiableOn hO' hτd
  have hτinj : Set.InjOn τ O' := fun z₁ h₁ z₂ h₂ h => by
    have h' := congrArg s h
    rw [(hτU z₁ h₁).2, (hτU z₂ h₂).2] at h'
    rw [← (hsec' z₁ h₁.1).1, ← (hsec' z₂ h₂.1).1, h']
  have hsan : AnalyticOnNhd ℂ s U := IndefiniteRowSideFullHecke.ComplexSets.analyticOnNhd_of_differentiableOn hU hsd
  calc _ = ∫⁻ y in τ '' O', ENNReal.ofReal ((U ∩ s ⁻¹' E).indicator
          (fun y => max (f (s y) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) y) 0) y) := by
        refine (setLIntegral_eq_of_support_subset fun y hy => ?_).symm
        have hyE : y ∈ U ∩ s ⁻¹' E := by
          by_contra h
          exact hy (by simp [Set.indicator_of_notMem h])
        have hZ : s y ∈ zeroSet J ∩ W := ⟨(hsec y hyE.1).2, hEW hyE.2⟩
        refine ⟨A' *ᵥ s y, ⟨(hWs' _ hZ).1, ?_⟩, ?_⟩
        · show s' (A' *ᵥ s y) ∈ W
          rw [(hWs' _ hZ).2]
          exact hZ.2
        · show A *ᵥ s' (A' *ᵥ s y) = y
          rw [(hWs' _ hZ).2, (hsec y hyE.1).1]
    _ = ∫⁻ z in O', ENNReal.ofReal (Complex.normSq (ReciprocityTheory.AnForm.A.jacC τ z).det) *
          ENNReal.ofReal ((U ∩ s ⁻¹' E).indicator
            (fun y => max (f (s y) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) y) 0) (τ z)) :=
        ReciprocityTheory.AnForm.A.lintegral_image_eq_lintegral_normSq_det_mul τ O' hO' hτan hτinj _
    _ = ∫⁻ z in O', ENNReal.ofReal ((U' ∩ s' ⁻¹' E).indicator
          (fun y => max (f (s' y) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s') y) 0) z) := by
        refine setLIntegral_congr_fun hO'.measurableSet fun z hz => ?_
        by_cases hzE : s' z ∈ E
        · have hm : τ z ∈ U ∩ s ⁻¹' E :=
            ⟨(hτU z hz).1, by rw [Set.mem_preimage, (hτU z hz).2]; exact hzE⟩
          rw [Set.indicator_of_mem hm, Set.indicator_of_mem (show z ∈ U' ∩ s' ⁻¹' E from ⟨hz.1, hzE⟩)]
          have h1 : ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s') z =
              ReciprocityTheory.AnForm.maDens (fun k => (φ k ∘ s) ∘ τ) z :=
            IndefiniteRowSideFullHecke.ComplexSets.maDens_congr_of_eventuallyEq fun k => by
              filter_upwards [hO'.mem_nhds hz] with w hw
              show φ k (s' w) = φ k (s (τ w))
              rw [(hτU w hw).2]
          have h2 : ReciprocityTheory.AnForm.maDens (fun k => (φ k ∘ s) ∘ τ) z =
              ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) (τ z) *
                Complex.normSq (ReciprocityTheory.AnForm.A.jacC τ z).det := by
            refine ReciprocityTheory.AnForm.A.maDens_comp (fun k => φ k ∘ s) τ z (hτan z hz) fun k => ?_
            obtain ⟨Ok, hOk, hZOk, hφk⟩ := hφ k
            have hsZ : s (τ z) ∈ Ok := hZOk (by rw [(hτU z hz).2]; exact (hsec' z hz.1).2)
            have hφa : ContDiffAt ℝ 2 (φ k) (s (τ z)) :=
              (hφk.contDiffAt (hOk.mem_nhds hsZ)).of_le (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
            have hsa : ContDiffAt ℝ 2 s (τ z) :=
              ((hsan (τ z) (hτU z hz).1).contDiffAt).restrict_scalars ℝ
            exact hφa.comp (τ z) hsa
          rw [h1, h2, (hτU z hz).2, ← ENNReal.ofReal_mul (Complex.normSq_nonneg _), mul_comm,
            max_mul_of_nonneg _ _ (Complex.normSq_nonneg _), zero_mul, mul_assoc]
        · rw [Set.indicator_of_notMem (fun hm => hzE (by
              have := hm.2
              rw [Set.mem_preimage, (hτU z hz).2] at this
              exact this)),
            Set.indicator_of_notMem (show z ∉ U' ∩ s' ⁻¹' E from fun hm => hzE hm.2)]
          simp
    _ = _ := by
        refine setLIntegral_eq_of_support_subset fun z hz => ?_
        have hzE : z ∈ U' ∩ s' ⁻¹' E := by
          by_contra h
          exact hz (by simp [Set.indicator_of_notMem h])
        exact ⟨hzE.1, hEW hzE.2⟩

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology ComplexSets

noncomputable section

namespace NormalDoublePointsGeneric

theorem ringKrullDim_quotient_le_of_primes {R : Type*} [CommRing R] (I : Ideal R) (k : WithBot ℕ∞)
    (h : ∀ W : Ideal R, W.IsPrime → I ≤ W → ∃ K : Ideal R, K ≤ W ∧ ringKrullDim (R ⧸ K) ≤ k) :
    ringKrullDim (R ⧸ I) ≤ k := by
  rw [ringKrullDim_quotient]
  refine iSup_le fun l => ?_
  obtain ⟨K, hKW, hK⟩ := h l.head.1.asIdeal l.head.1.isPrime l.head.2
  let l' : LTSeries (PrimeSpectrum.zeroLocus (R := R) K) :=
    ⟨l.length, fun i => ⟨(l i).1, show (K : Set R) ⊆ (l i).1.asIdeal from hKW.trans (l.head_le i)⟩,
      fun i => l.step i⟩
  calc (l.length : WithBot ℕ∞) = l'.length := rfl
    _ ≤ Order.krullDim (PrimeSpectrum.zeroLocus (R := R) K) := Order.LTSeries.length_le_krullDim l'
    _ = ringKrullDim (R ⧸ K) := (ringKrullDim_quotient K).symm
    _ ≤ k := hK

theorem ringKrullDim_quotient_anti {R : Type*} [CommRing R] {K K' : Ideal R} (h : K ≤ K') :
    ringKrullDim (R ⧸ K') ≤ ringKrullDim (R ⧸ K) :=
  ringKrullDim_le_of_surjective (Ideal.Quotient.factor h) (Ideal.Quotient.factor_surjective h)

theorem ringKrullDim_quot_sup_span_add_one_le {n : ℕ} (p : Ideal (MvPolynomial (Fin n) ℂ)) [p.IsPrime]
    {g : MvPolynomial (Fin n) ℂ} (hg : g ∉ p) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (p ⊔ Ideal.span {g})) + 1 ≤
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ p) := by
  have hne : Ideal.Quotient.mk p g ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have h := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hne)
  have e : ((MvPolynomial (Fin n) ℂ ⧸ p) ⧸ Ideal.span {Ideal.Quotient.mk p g}) ≃+*
      MvPolynomial (Fin n) ℂ ⧸ (p ⊔ Ideal.span {g}) :=
    (Ideal.quotEquivOfEq (by rw [Ideal.map_span, Set.image_singleton])).trans
      (DoubleQuot.quotQuotEquivQuotSup p (Ideal.span {g}))
  rwa [ringKrullDim_eq_of_ringEquiv e] at h

def belowNat : ℕ → WithBot ℕ∞
  | 0 => ⊥
  | e + 1 => (e : WithBot ℕ∞)

theorem belowNat_lt (d : ℕ) : belowNat d < (d : WithBot ℕ∞) := by
  cases d with
  | zero => exact WithBot.bot_lt_coe _
  | succ e =>
    show ((e : ℕ) : WithBot ℕ∞) < ((e + 1 : ℕ) : WithBot ℕ∞)
    exact_mod_cast Nat.lt_succ_self e

theorem le_belowNat_of_add_two_le {x : WithBot ℕ∞} {d : ℕ}
    (h : x + 1 + 1 ≤ ((d + 1 : ℕ) : WithBot ℕ∞)) : x ≤ belowNat d := by
  induction x using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      exfalso
      have h2 : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ (((d + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
        rw [← WithBot.coe_one, ← WithBot.coe_add, top_add, ← WithBot.coe_add, top_add] at h
        exact_mod_cast h
      exact absurd (WithBot.coe_le_coe.1 h2) (by simp)
    | coe k =>
      have h2 : k + 1 + 1 ≤ d + 1 := by exact_mod_cast h
      cases d with
      | zero => omega
      | succ e => show ((k : ℕ∞) : WithBot ℕ∞) ≤ ((e : ℕ) : WithBot ℕ∞); exact_mod_cast (by omega : k ≤ e)

theorem proof : NormalDoublePointsGeneric.Statement := by
  intro n d J u M hJ hdim hu
  classical
  choose a b hbJ hab using M.birational
  set bb : MvPolynomial (Fin n) ℂ := ∏ i, b i with hbb
  have hbbJ : bb ∉ J := fun h => by
    obtain ⟨i, -, hi⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hJ)).1 h
    exact hbJ i hi
  set K : Ideal (MvPolynomial (Fin n) ℂ) := J ⊔ Ideal.span {bb} with hK
  have hfin : K.minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ K
  set S : Finset (Ideal (MvPolynomial (Fin n) ℂ)) := hfin.toFinset.filter (fun P => linForm u ∉ P) with hS
  have memS : ∀ P, P ∈ S ↔ P ∈ K.minimalPrimes ∧ linForm u ∉ P := fun P => by
    simp [hS]
  refine ⟨S.inf (fun P => P ⊔ Ideal.span {linForm u}), ?_, ?_, ?_⟩
  · refine Finset.le_inf fun P hP => sup_le_sup_right ?_ _
    exact le_sup_left.trans ((memS P).1 hP).1.1.2
  · have := hJ
    have hdimK : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ K) + 1 ≤ ((d + 1 : ℕ) : WithBot ℕ∞) :=
      hdim ▸ ringKrullDim_quot_sup_span_add_one_le J hbbJ
    refine lt_of_le_of_lt (ringKrullDim_quotient_le_of_primes _ (belowNat d) fun W hW hIW => ?_) (belowNat_lt d)
    obtain ⟨P, hPS, hPW⟩ := (hW.inf_le').1 hIW
    refine ⟨_, hPW, le_belowNat_of_add_two_le ?_⟩
    obtain ⟨hPm, huP⟩ := (memS P).1 hPS
    have := hPm.1.1
    have h1 := ringKrullDim_quot_sup_span_add_one_le P huP
    have h2 : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ P) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ K) :=
      ringKrullDim_quotient_anti hPm.1.2
    calc ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (P ⊔ Ideal.span {linForm u})) + 1 + 1
        ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ K) + 1 := by gcongr; exact h1.trans h2
      _ ≤ _ := hdimK
  · intro q _ hqu hqI
    have evu : ∀ x, eval x (linForm u) = linEval u x := fun x => by simp [linForm, linEval]
    have hqP : ∀ P ∈ S, q ∉ zeroSet P := by
      intro P hP hqP
      apply hqI
      intro f hf
      have hf' : f ∈ P ⊔ Ideal.span {linForm u} := (Finset.inf_le (f := fun P => P ⊔ Ideal.span {linForm u}) hP) hf
      obtain ⟨p, hp, r, hr, rfl⟩ := Submodule.mem_sup.1 hf'
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hr
      simp [hqP p hp, evu, hqu]
    have hclosed : ∀ P : Ideal (MvPolynomial (Fin n) ℂ), IsClosed (zeroSet P) := fun P => by
      have : zeroSet P = ⋂ f ∈ P, {x : Fin n → ℂ | eval x f = 0} := by
        ext x; simp [zeroSet]
      rw [this]
      exact isClosed_biInter fun f _ => isClosed_eq (MvPolynomial.continuous_eval f) continuous_const
    refine ⟨⋂ P ∈ S, (zeroSet P)ᶜ, (Filter.biInter_finset_mem S).2 fun P hP =>
      (hclosed P).isOpen_compl.mem_nhds (hqP P hP), ?_⟩
    intro w hw w' hw' hww hxN hne
    set x := IndefiniteRowSideFullHecke.ComplexSets.firstCoords w with hx
    have hwx : (w ∘ Sum.inl) = x := rfl
    have hw'x : (w' ∘ Sum.inl) = x := by rw [hww]; rfl
    have hxJ : ∀ f ∈ J, eval x f = 0 := fun f hf => by
      have hf' : rename Sum.inl f ∈ M.ideal := by
        rw [← M.comap_eq] at hf; exact hf
      have := hw _ hf'
      rwa [eval_rename, hwx] at this
    have hbx : eval x bb = 0 := by
      by_contra hb
      apply hne
      funext s
      rcases s with i | i
      · exact congrFun hww i
      · have hbi : eval x (b i) ≠ 0 := fun h0 => hb (by
          rw [hbb, map_prod]; exact Finset.prod_eq_zero (Finset.mem_univ i) h0)
        have e1 := hw _ (hab i)
        have e2 := hw' _ (hab i)
        simp only [map_sub, map_mul, eval_rename, eval_X, hwx, hw'x] at e1 e2
        exact mul_left_cancel₀ hbi (by linear_combination e1 - e2)
    have hKx : K ≤ RingHom.ker (eval x) := sup_le (fun f hf => RingHom.mem_ker.2 (hxJ f hf))
      (Ideal.span_le.2 (Set.singleton_subset_iff.2 (RingHom.mem_ker.2 hbx)))
    have : (RingHom.ker (eval x)).IsPrime := RingHom.ker_isPrime _
    obtain ⟨P, hPm, hPx⟩ := Ideal.exists_minimalPrimes_le hKx
    by_cases huP : linForm u ∈ P
    · rw [← evu]; exact RingHom.mem_ker.1 (hPx huP)
    · exfalso
      have hPS : P ∈ S := (memS P).2 ⟨hPm, huP⟩
      have hxP : x ∈ zeroSet P := fun f hf => RingHom.mem_ker.1 (hPx hf)
      exact (Set.mem_iInter₂.1 hxN P hPS) hxP

end NormalDoublePointsGeneric

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace NormalDivisorChartGeneric

theorem ringKrullDim_le_of_injective_isIntegral {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hinj : Function.Injective f) (hint : f.IsIntegral) : ringKrullDim R ≤ ringKrullDim S := by
  let : Algebra R S := f.toAlgebra
  have : Algebra.IsIntegral R S := ⟨hint⟩
  refine iSup_le fun l => ?_
  have hker : (⊥ : Ideal S).comap (algebraMap R S) ≤ (RelSeries.head l).asIdeal := by
    intro r hr
    have : f r = 0 := hr
    rw [show r = 0 from hinj (by rw [this, map_zero])]
    exact Ideal.zero_mem _
  obtain ⟨P, -, hP, hPo⟩ := Ideal.exists_ideal_over_prime_of_isIntegral _ ⊥ hker
  have : P.LiesOver (RelSeries.head l).asIdeal := ⟨hPo.symm⟩
  obtain ⟨L, hlen, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
  exact le_iSup_of_le L (by rw [hlen])

theorem isIntegral_mk_comp_rename {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J) {B : Ideal (MvPolynomial (Fin n ⊕ Fin M.m) ℂ)} (hB : M.ideal ≤ B) :
    ((Ideal.Quotient.mk B).comp (rename (Sum.inl : Fin n → Fin n ⊕ Fin M.m)).toRingHom).IsIntegral := by
  set f := (Ideal.Quotient.mk B).comp (rename (Sum.inl : Fin n → Fin n ⊕ Fin M.m)).toRingHom with hf
  let : Algebra (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ B) := f.toAlgebra
  have hX : ∀ s, IsIntegral (MvPolynomial (Fin n) ℂ) (Ideal.Quotient.mk B (X s)) := by
    rintro (i | i)
    · have h : Ideal.Quotient.mk B (X (Sum.inl i)) =
          algebraMap (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ B) (X i) := by
        show _ = f (X i)
        simp [hf]
      rw [h]
      exact isIntegral_algebraMap
    · obtain ⟨P, hPm, hP⟩ := M.integral i
      refine ⟨P, hPm, ?_⟩
      have h := Ideal.Quotient.eq_zero_iff_mem.mpr (hB hP)
      rw [Polynomial.hom_eval₂] at h
      exact h
  intro z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  show IsIntegral (MvPolynomial (Fin n) ℂ) (Ideal.Quotient.mk B p)
  induction p using MvPolynomial.induction_on with
  | C a =>
    have h : Ideal.Quotient.mk B (C a) =
        algebraMap (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ B) (C a) := by
      show _ = f (C a)
      simp [hf]
    rw [h]
    exact isIntegral_algebraMap
  | add p q hp hq =>
    rw [map_add (f := _)]
    exact hp.add hq
  | mul_X p s hp =>
    rw [map_mul]
    exact hp.mul (hX s)

theorem proof (hUp : NormalModelDivisorChartGeneric.Statement) : NormalDivisorChartGeneric.Statement := by
  intro n d J u M hJ hdim hu
  obtain ⟨B, hleB, hdimB, hB⟩ := hUp n d J u M hJ hdim hu
  refine ⟨B.comap (rename (Sum.inl : Fin n → Fin n ⊕ Fin M.m)).toRingHom, ?_, ?_, ?_⟩
  · refine sup_le ?_ ((Ideal.span_le).2 (Set.singleton_subset_iff.2 ?_))
    · exact M.comap_eq.symm.le.trans (Ideal.comap_mono (le_sup_left.trans hleB))
    · exact hleB (Ideal.mem_sup_right (Ideal.subset_span rfl))
  · refine lt_of_le_of_lt ?_ hdimB
    exact ringKrullDim_le_of_injective_isIntegral _ Ideal.quotientMap_injective
      ((isIntegral_quotientMap_iff _).2 (isIntegral_mk_comp_rename M (le_sup_left.trans hleB)))
  · intro q _ hqu hqI w hw hwq
    refine hB w hw (hwq ▸ hqu) fun hwB => hqI fun f hf => ?_
    have h := hwB _ hf
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, eval_rename] at h
    rw [← hwq]
    exact h

end NormalDivisorChartGeneric

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets
open scoped ENNReal

noncomputable section

def TubeDeepAreaCount.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (P : MvPolynomial (Fin (d + 1)) ℂ) (R : ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
      ∃ N : ℕ, ∀ g : (Fin (d + 1) → ℂ) → ℝ, Measurable g → (∀ z, 0 ≤ g z) →
        ∫⁻ y, ENNReal.ofReal (sheetSum J A (fun x s =>
            (Metric.closedBall (0 : Fin n → ℂ) R).indicator (fun _ => (1 : ℝ)) x *
              ∑ I : Fin d → Fin n, ‖deepJacDet P s I y‖ ^ 2 * g (deepMap P s I y)) y) ≤
          (N : ℝ≥0∞) * ∫⁻ z in {z : Fin (d + 1) → ℂ | ∀ i : Fin d, ‖z i.succ‖ ≤ R}, ENNReal.ofReal (g z)

end

end GroundTheory.Heights₂.Heights
end
