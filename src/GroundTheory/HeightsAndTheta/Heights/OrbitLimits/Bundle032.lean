module

public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle030
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle027
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle049
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsFieldIntersectionExample
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle027
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle026
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle014
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle002
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PPFContracted
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle014
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle013
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle015
public import GroundTheory.HeightsAndTheta.Heights.Intersections.TableDegreeThreeBase
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
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
import GroundTheory.HeightsAndTheta.Heights.Intersections.Statements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle015
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle013
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle005

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GroundTheory.Heights₂.Heights.Inter

theorem CurveCountLower.proof (hD : CurveDegreeVert.Statement) (hV : CurveVertIndex.Statement)
    (hL : CurveIndexLinear.Statement) (hN : CurveBoxCount.Statement) : CurveCountLower.Statement := by
  intro K _ ι _ Ω _ y A II hII hP hB hS hC
  obtain ⟨c, hcX, hc⟩ := exists_chart hP
  obtain ⟨R, hRP, hRu, -⟩ := regularityPointsSum_holds.proof K ι _ hP
  set b : K → ℕ := fun k => (A.a k).natAbs with hb
  set d : K → ℕ := fun k => (A.a k + b k).toNat with hd'
  have hd : ∀ k, (d k : ℤ) = A.a k + b k := fun k =>
    Int.toNat_of_nonneg (by simp only [hb]; omega)
  have h1 := hD K ι _ A II c R b d hII hP hS hcX hRP hRu hd
  have h2 := hV K ι Ω y _ d hP (isMultiHomog_curveChartMono c d) (curveChartMono_notMem hc d)
  have h3 := hV K ι Ω y _ b hP (isMultiHomog_curveChartMono c b) (curveChartMono_notMem hc b)
  rw [aeval_curveChartMono] at h2 h3
  obtain ⟨hadd, hpow⟩ := hL K ι Ω y c hP hc
  have h4 := hadd A.a (fun k => (b k : ℤ))
  rw [show A.a + (fun k => (b k : ℤ)) = fun k => (d k : ℤ) from funext fun k => (hd k).symm] at h4
  have hI : II K ι (mCoordIdeal y) 1 (fun _ => A) =
      chartIndexLog y c A.a 1 + ∑ t ∈ R, Real.log (chartRadius A c t) := by
    have e2 : vertR (mCoordIdeal y) (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (curveChartMono c d) =
        chartIndexLog y c (fun k => (d k : ℤ)) 1 := h2
    have e3 : vertR (mCoordIdeal y) (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (curveChartMono c b) =
        chartIndexLog y c (fun k => (b k : ℤ)) 1 := h3
    rw [h1, e2, e3, h4]
    ring
  obtain ⟨C, hCC⟩ := hN K ι Ω y A c R hP hB hC hc hRP hRu
  refine ⟨C, fun τ hτ => ?_⟩
  have h5 := hCC τ hτ
  rw [hpow A.a τ] at h5
  rw [hI]
  linarith [mul_add (τ : ℝ) (chartIndexLog y c A.a 1) (∑ t ∈ R, Real.log (chartRadius A c t))]

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

namespace ContractMixedField

variable {F : Type} [Field F] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]


omit [Fintype K] [Fintype K'] in
theorem isMultiHomog_rename {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {t : MRingOver F ι} {a : K → ℕ} (ht : _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog t a) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (rename v t) (Function.extend κ a 0) := by
  classical
  have ht' := (Bridge.isMultiHomog_iff t a).mpr ht
  refine (Bridge.isMultiHomog_iff _ _).mp ?_
  have e := FieldNumbers.ContractRelevant.rename_weightedHomogeneousComponent hv.2.2.1 hv.1 hv.2.1 a t
  rw [IsWeightedHomogeneous.weightedHomogeneousComponent_same ht'] at e
  rw [e]
  exact weightedHomogeneousComponent_isWeightedHomogeneous _ _


omit [Fintype K] [Fintype K'] in
theorem isMultiProjPrime_imageVar {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {W : Ideal (MRingOver F ι')} (hW : IsMultiProjPrime W) : IsMultiProjPrime (imageVar F v W) := by
  classical
  have h := FieldNumbers.ContractRelevant.isMultiProjPrime_comap_rename (R := F) hv.2.2.1 hv.1 hv.2.1
    (fun w hw => hv.2.2.2 w hw) ((Bridge.isMultiProjPrime_iff W).mpr hW)
  exact (Bridge.isMultiProjPrime_iff _).mp h

theorem exists_dim {V : Ideal (MRingOver F ι)} (hV : IsMultiProjPrime V) :
    ∃ D : ℕ, Fintype.card K ≤ D ∧ ringKrullDim (MRingOver F ι ⧸ V) = D := by
  classical
  have := hV.1
  have hmh := (Bridge.isMultiHomogIdeal_iff V).mpr hV.2.1
  exact FieldNumbers.PFContracted.exists_ringKrullDim_eq
    (fun T q hq => FieldNumbers.PFContracted.killBlocks_mem_of_isMultiHomogIdeal hmh T hq) hV.2.2

theorem mem_divSupp_of_ne_zero {P : Ideal (MRingOver F ι)} {s : MRingOver F ι} {W : Ideal (MRingOver F ι)}
    (h : _root_.ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s W ≠ 0) : W ∈ divSupp P s := by
  classical
  by_contra hW
  apply h
  simp [_root_.ReciprocityTheory.ChartRestriction.G.Geo.divCycle, Finsupp.ofSupportFinite_coe, hW]

theorem component [DecidableEq K'] {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {V' : Ideal (MRingOver F ι')} {n d₀ : ℕ} (hV' : IsProjVarF V' (n + 1))
    (hI : IsProjVarF (imageVar F v V') d₀) {t : MRingOver F ι} {a : K → ℕ} (ht : _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog t a)
    (htV : t ∉ imageVar F v V') {W : Ideal (MRingOver F ι')} (hW : _root_.ReciprocityTheory.ChartRestriction.G.Geo.divCycle V' (rename v t) W ≠ 0) :
    IsProjVarF W n ∧ ∃ d₁ : ℕ, d₁ < d₀ ∧ IsProjVarF (imageVar F v W) d₁ := by
  classical
  have hWs := mem_divSupp_of_ne_zero hW
  have hVW : V' ≤ W := le_sup_left.trans hWs.1.1.2
  have htW : rename v t ∈ W := hWs.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hrel : FieldNumbers.relDim V' = ((n + 1 : ℕ) : WithBot (WithTop ℤ)) :=
    NumbersDVR.relDim_eq_of_ringKrullDim V' (n + 1) hV'.2
  have hW' : NumbersDVR.divCycle V' (rename v t) W ≠ 0 := by
    rw [← NumbersDVR.VocabDivCycle.proof F K' ι' V' (rename v t) W]
    exact_mod_cast hW
  obtain ⟨hWm, hWd⟩ := FieldNumbers.DivCycleSupport.full F K' ι' V' ((Bridge.isMultiProjPrime_iff V').mpr hV'.1)
    n hrel (Function.extend κ a 0) (rename v t)
    ((Bridge.isMultiHomog_iff _ _).mpr (isMultiHomog_rename hv ht)) (fun h => htV h) W hW'
  have hWm' := (Bridge.isMultiProjPrime_iff W).mp hWm
  refine ⟨⟨hWm', NumbersDVR.Numbers.ringKrullDim_eq_of_relDim W n hWd⟩, ?_⟩
  have hIm := isMultiProjPrime_imageVar hv hWm'
  obtain ⟨D, hKD, hD⟩ := exists_dim hIm
  have hle : imageVar F v V' ≤ imageVar F v W := Ideal.comap_mono hVW
  have : (imageVar F v V').IsPrime := hI.1.1
  have hdim := Inter.krullDim_quot_add_one_le hle (show t ∈ imageVar F v W from htW) htV
  rw [hD, hI.2] at hdim
  have hD' : D + 1 ≤ d₀ + Fintype.card K := by exact_mod_cast hdim
  refine ⟨D - Fintype.card K, by omega, hIm, ?_⟩
  rw [hD, Nat.sub_add_cancel hKD]


open Classical in
theorem intNum_eq_zero [DecidableEq K'] {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v) :
    ∀ (n : ℕ) (V' : Ideal (MRingOver F ι')) (d₀ : ℕ) (bs : Fin n → K' → ℤ),
      IsProjVarF V' n → IsProjVarF (imageVar F v V') d₀ →
      d₀ < (∑ i, if ∃ a : K → ℤ, bs i = pullDeg κ a then 1 else 0) →
      NumbersDVR.intNum F V' bs = 0 := by
  intro n
  induction n with
  | zero =>
    intro V' d₀ bs _ _ h
    simp at h
  | succ n ih =>
    intro V' d₀ bs hV' hI hcount
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero
      (ne_of_gt (lt_of_le_of_lt (Nat.zero_le d₀) hcount))
    obtain ⟨a, ha⟩ : ∃ a : K → ℤ, bs i = pullDeg κ a := by
      by_contra h
      exact hi (if_neg h)
    obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin (n + 1)), σ (Fin.last n) = i :=
      ⟨Equiv.swap i (Fin.last n), Equiv.swap_apply_right _ _⟩
    rw [← FieldNumbers.IntNumSymm.full F K' ι' V' (n + 1) bs σ]
    have hlast : (bs ∘ σ) (Fin.last n) = pullDeg κ a := by
      show bs (σ (Fin.last n)) = _
      rw [hσ, ha]
    have e : bs ∘ σ = Fin.snoc (α := fun _ => K' → ℤ) (Fin.init (bs ∘ σ)) (pullDeg κ a) := by
      rw [← hlast]
      exact (Fin.snoc_init_self _).symm

    have hsum : (∑ i, if ∃ a : K → ℤ, bs i = pullDeg κ a then 1 else 0) =
        (∑ j : Fin n, if ∃ a : K → ℤ, Fin.init (bs ∘ σ) j = pullDeg κ a then 1 else 0) + 1 := by
      rw [← Equiv.sum_comp σ (fun j => if ∃ a : K → ℤ, bs j = pullDeg κ a then 1 else 0),
        Fin.sum_univ_castSucc, hσ, if_pos ⟨a, ha⟩]
      rfl

    classical
    obtain ⟨bf, bg, f, g, hf, hg, hfI, hgI, hfg⟩ :=
      FieldNumbers.ExistsForm.full F K ι _ ((Bridge.isMultiProjPrime_iff _).mpr hI.1) a
    have hf' := (Bridge.isMultiHomog_iff f bf).mp hf
    have hg' := (Bridge.isMultiHomog_iff g bg).mp hg
    have hsec : IsRatSection V' (pullDeg κ a) (rename v f) (rename v g) := by
      refine ⟨Function.extend κ bf 0, Function.extend κ bg 0, isMultiHomog_rename hv hf',
        isMultiHomog_rename hv hg', fun h => hfI h, fun h => hgI h, fun k' => ?_⟩
      by_cases hk : ∃ k, κ k = k'
      · obtain ⟨k, rfl⟩ := hk
        simp only [ReciprocityTheory.ChartRestriction.G.AI.I1.pullDeg, hv.1.extend_apply, ← hfg]
      · simp only [ReciprocityTheory.ChartRestriction.G.AI.I1.pullDeg, Function.extend_apply' _ _ _ hk, Pi.zero_apply,
          Nat.cast_zero, sub_zero]
    have key := (NumbersDVR.IntNumIsFieldIntersection.full F K' ι').2 V' n (Fin.init (bs ∘ σ)) _ _ _ hV' hsec
    dsimp only at key
    rw [e, key]
    unfold cycEval Finsupp.sum
    refine Finset.sum_eq_zero fun W hW => ?_
    rw [Finsupp.mem_support_iff] at hW
    suffices h0 : NumbersDVR.intNum F W (Fin.init (bs ∘ σ)) = 0 by simp only [h0, mul_zero]
    have hcases : _root_.ReciprocityTheory.ChartRestriction.G.Geo.divCycle V' (rename v f) W ≠ 0 ∨ _root_.ReciprocityTheory.ChartRestriction.G.Geo.divCycle V' (rename v g) W ≠ 0 := by
      by_contra hc
      push Not at hc
      apply hW
      simp [ratDiv, hc.1, hc.2]
    have hpair : IsProjVarF W n ∧ ∃ d₁ : ℕ, d₁ < d₀ ∧ IsProjVarF (imageVar F v W) d₁ := by
      rcases hcases with hc | hc
      · exact component hv hV' hI hf' (fun h => hfI h) hc
      · exact component hv hV' hI hg' (fun h => hgI h) hc
    obtain ⟨hWn, d₁, hd₁, hWI⟩ := hpair
    exact ih W d₁ _ hWn hWI (by omega)

end ContractMixedField


open ContractMixedField in
theorem contractMixedField : ReciprocityTheory.ChartRestriction.G.AI.I4.ContractMixedFieldStatement := by
  unfold ReciprocityTheory.ChartRestriction.G.AI.I4.ContractMixedFieldStatement
  intro F _ K _ ι _ K' _ ι' _ J' hJ' κ v V' d₀ d r L N hv hV' hI hd
  classical
  rw [NumbersDVR.Numbers.agree_of FieldNumbers.IntNumBase.full FieldNumbers.CutRational.full
    FieldNumbers.ExistsForm.full FieldNumbers.DivCycleSupport.full J' hJ' V' (d + r) _ hV']
  refine intNum_eq_zero hv (d + r) V' d₀ _ hV' hI ?_
  rw [Fin.sum_univ_add]
  have h1 : ∀ j : Fin d, (if ∃ a : K → ℤ, Fin.append (fun j => pullDeg κ (L j)) N (Fin.castAdd r j) =
      pullDeg κ a then 1 else 0) = 1 := fun j => if_pos ⟨L j, by rw [Fin.append_left]⟩
  rw [Finset.sum_congr rfl fun j _ => h1 j]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  omega

end GroundTheory.Heights₂.Heights.Targets
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.Inter

namespace ContractMixed

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

def PrefixPull (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (p : ℕ) {n : ℕ} (L' : Fin n → _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι') :
    Prop :=
  ∃ (h : p ≤ n) (L : Fin p → _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι), (∀ j, IsSmoothHerm (L j)) ∧
    ∀ j, IsPullHerm κ v (L j) (L' (Fin.castLE h j))


omit [∀ k, Fintype (ι' k)] in
theorem PrefixPull.mono {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {p q n : ℕ} {L' : Fin n → _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι'}
    (h : PrefixPull κ v p L') (hqp : q ≤ p) : PrefixPull κ v q L' := by
  obtain ⟨hpn, L, hL, hLL⟩ := h
  exact ⟨hqp.trans hpn, fun j => L (Fin.castLE hqp j), fun j => hL _, fun j => hLL (Fin.castLE hqp j)⟩


omit [∀ k, Fintype (ι' k)] in
theorem PrefixPull.init {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {p n : ℕ} {L' : Fin (n + 1) → _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι'}
    (h : PrefixPull κ v p L') (hpn : p ≤ n) : PrefixPull κ v p (Fin.init L') := by
  obtain ⟨_, L, hL, hLL⟩ := h
  exact ⟨hpn, L, hL, fun j => hLL j⟩

theorem arInt_eq_zero (hInt : PFIntZero.Statement) {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')}
    (hv : IsBlockMap κ v) {P' : Ideal (MRing ι')} {d₀ n : ℕ} (hP' : IsArithVar P' (n + 1))
    (hQ : IsArithVar (imageZ v P') d₀) {L' : Fin n → _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι'} (hpre : PrefixPull κ v d₀ L')
    (A : _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι') (s : MRing ι') : arInt P' s A L' = 0 := by
  obtain ⟨h, L, hL, hLL⟩ := hpre
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [← Fin.append_castAdd_natAdd (f := L')]
  exact hInt K ι K' ι' κ v P' d₀ m L _ _ A s hv hP' hQ hL hLL

theorem geoNum_eq_zero (hVert : PFVert.Statement) {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')}
    (hv : IsBlockMap κ v) {P' : Ideal (MRing ι')} {d₀ n : ℕ} (hP' : IsArithVar P' (n + 1))
    (hQ : IsArithVar (imageZ v P') d₀) {L' : Fin n → _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι'} (hpre : PrefixPull κ v d₀ L')
    {s : MRing ι'} {a : K' → ℕ} (hs : _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a) (hsP : s ∉ P') {W : Ideal (MRing ι')}
    (hW : W ∈ divSupp P' s) (hh : ¬ IsHorizontal W) : geoNum n W (fun j => (L' j).a) = 0 := by
  obtain ⟨h, L, -, hLL⟩ := hpre
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [← Fin.append_castAdd_natAdd (f := L')]
  exact hVert K ι K' ι' κ v P' d₀ m L _ _ s a W hv hP' hQ hLL hs hsP hW hh

theorem aux (hC : ContractStatement) (hIm : ImageArithStatement) (hInt : PFIntZero.Statement)
    (hVert : PFVert.Statement) (I : AllFam) (hI : I.IsFamily) {κ : K → K'}
    {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v) :
    ∀ (n p : ℕ) (P' : Ideal (MRing ι')) (d₀ : ℕ) (L' : Fin n → _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι'),
      IsArithVar P' n → IsArithVar (imageZ v P') d₀ → d₀ < p → PrefixPull κ v p L' →
      (∀ j, IsSmoothHerm (L' j)) → I K' ι' P' n L' = 0 := by
  intro n
  induction n with
  | zero =>
    intro p _ d₀ _ _ _ hdp hpre _
    obtain ⟨h, -⟩ := hpre
    omega
  | succ n ih =>
    intro p P' d₀ L' hP' hQ hdp hpre hL'
    classical
    rcases Nat.lt_or_ge n p with hnp | hpn
    ·
      obtain ⟨h, L, hL, hLL⟩ := hpre
      have hp : p = n + 1 := by omega
      subst hp
      have e : (fun j => L' (Fin.castLE h j)) = L' := funext fun j => congrArg L' (Fin.ext rfl)
      have key := hC I hI K ι K' ι' κ v P' d₀ (n + 1) L (fun j => L' (Fin.castLE h j)) hv hP' hQ hdp hL hLL
      rwa [e] at key
    ·
      have hpre0 : PrefixPull κ v p (Fin.init L') := hpre.init hpn
      have hL0 : ∀ j, IsSmoothHerm (Fin.init L' j) := fun j => hL' _
      have hPp : P'.IsPrime := hP'.2.1.1
      choose i hi using hP'.2.1.2.2

      have key : ∀ B' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι', IsSmoothHerm B' → (∀ k, 0 ≤ B'.a k) →
          I K' ι' P' (n + 1) (Fin.snoc (Fin.init L') B') = 0 := by
        intro B' hB' hBa
        let b : K' → ℕ := fun k => (B'.a k).toNat
        let s : MRing ι' := ∏ k, X ⟨k, i k⟩ ^ b k
        have hs : s ∉ P' := by
          intro h
          obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hPp)).1 h
          exact hi k (hPp.mem_of_pow_mem _ hk)
        have hsm : _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s b := by
          convert isMultiHomog_prod_X_pow (fun k => (⟨k, i k⟩ : Σ k, ι' k)) b using 1
          funext k
          simp [Finset.sum_filter]
        have hBa' : ∀ k, B'.a k = b k := fun k => (Int.toNat_of_nonneg (hBa k)).symm
        have hsec : IsSectionOn P' B' s := ⟨b, hBa', hsm, hs⟩
        rw [(hI K' ι').2.2 P' n (Fin.init L') B' s b hP' hL0 hB' hBa' hsm hs, recR_eq]
        have h1 : arInt P' s B' (Fin.init L') = 0 :=
          arInt_eq_zero hInt hv hP' hQ (hpre0.mono hdp.le) B' s
        have h2 : cycR (I K' ι') P' (Fin.init L') s = 0 := by
          unfold cycR
          refine (finsum_mem_congr rfl fun W hW => ?_).trans (finsum_mem_zero _)
          split_ifs with hH
          · have hWn : IsArithVar W n := (divSuppArith K' ι' P' n B' s W hP' hsec hW).1 hH
            obtain ⟨dW, -, hQW⟩ := hIm K ι K' ι' κ v W n hQ.1 hv hWn
            have hPW : P' ≤ W := le_sup_left.trans hW.1.1.2
            have hle : imageZ v P' ≤ imageZ v W := Ideal.comap_mono hPW
            have hdim := ringKrullDim_le_of_surjective (Ideal.Quotient.factor hle)
              (Ideal.Quotient.factor_surjective hle)
            rw [hQW.2.2.2, hQ.2.2.2] at hdim
            have hlt : dW + Fintype.card K ≤ d₀ + Fintype.card K := by exact_mod_cast hdim
            rw [ih p W dW (Fin.init L') hWn hQW (by omega) hpre0 hL0, mul_zero]
          · rw [geoNum_eq_zero hVert hv hP' hQ (hpre0.mono hdp.le) hsm hs hW hH]
            simp
        rw [h1, h2, sub_zero]

      let A' := L' (Fin.last n)
      let M : _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι' := _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine.sqMetric fun k => (-(A'.a k)).toNat
      have hM : IsSmoothHerm M := isSmoothHerm_sqMetric _
      have hA' : IsSmoothHerm A' := hL' _
      have hadd := (hI K' ι').2.1 P' n (Fin.init L') A' M hP' hL0 hA' hM
      have h3 := key (A'.tensor M) (isSmoothHerm_tensor hA' hM) fun k => by
        show 0 ≤ A'.a k + ((-(A'.a k)).toNat : ℤ)
        omega
      have h4 := key M hM fun k => by
        show (0 : ℤ) ≤ ((-(A'.a k)).toNat : ℤ)
        omega
      have e : L' = Fin.snoc (Fin.init L') A' := (Fin.snoc_init_self L').symm
      rw [e]
      linarith

theorem of_contract (hC : ContractStatement) (hIm : ImageArithStatement) (hInt : PFIntZero.Statement)
    (hVert : PFVert.Statement) : ReciprocityTheory.ChartRestriction.G.AI.I4.ContractMixedStatement := by
  intro I hI K _ ι _ K' _ ι' _ κ v P' d₀ d r L L' N hv hP' hQ hdd hL hLL hN
  refine aux hC hIm hInt hVert I hI hv (d + r) d P' d₀ (Fin.append L' N) hP' hQ hdd ?_ ?_
  · refine ⟨Nat.le_add_right d r, L, hL, fun j => ?_⟩
    have e : Fin.castLE (Nat.le_add_right d r) j = Fin.castAdd r j := rfl
    rw [e, Fin.append_left]
    exact hLL j
  · intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · rw [Fin.append_left]
      exact IsPullHerm.isSmoothHerm hv (hLL i) (hL i)
    · rw [Fin.append_right]
      exact hN i

theorem of_found (hIm : ImageArithStatement) (hF : pointForm_holds.Statement) (hV : ProjectivePointVertical.Statement)
    (hInt : PFIntZero.Statement) (hVert : PFVert.Statement) : ReciprocityTheory.ChartRestriction.G.AI.I4.ContractMixedStatement :=
  of_contract (contract_of hIm hF hV) hIm hInt hVert

end ContractMixed

end GroundTheory.Heights₂.Heights.Targets
end
end
