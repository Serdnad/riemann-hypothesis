module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle028
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle038
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle056
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle057
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle037
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle049
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle026
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle027
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle014
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PCutRegular
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PNefProductNonneg
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle053
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle012

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

theorem SectionRingFinite.proof (hL : SectionLatticeFinite.Statement) (hS : SectionSpanStep.Statement) :
    SectionRingFinite.Statement := by
  intro K _ ι _ Ω _ y a q w hy hw hgen
  classical
  obtain ⟨n₀, hn₀⟩ := hS K ι Ω y a q w hy hw hgen
  choose G hG using fun m : ℕ => _root_.AddSubgroup.isAddFG_iff.mp (hL K ι Ω y a m hy)
  set P : Finset (ℕ × Ω) :=
    (Finset.range (n₀ + 1)).biUnion fun m => (G m).image fun g => (m, g) with hP
  have memP : ∀ m g, m ≤ n₀ → g ∈ G m → (m, g) ∈ P := by
    intro m g hm hg
    rw [hP, Finset.mem_biUnion]
    exact ⟨m, Finset.mem_range.2 (Nat.lt_succ_of_le hm), Finset.mem_image.2 ⟨g, hg, rfl⟩⟩
  have ofP : ∀ x ∈ P, x.2 ∈ chartLat y a x.1 := by
    intro x hx
    rw [hP, Finset.mem_biUnion] at hx
    obtain ⟨m, _, hx⟩ := hx
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hx
    rw [← hG m]
    exact AddSubgroup.subset_closure hg
  let f : Fin P.card → ℕ × Ω := fun i => (P.equivFin.symm i).1
  let T : ℕ → Set Ω := fun n =>
    {s | ∃ (i : Fin P.card) (μ : Fin q → ℕ), (f i).1 + ∑ j, μ j = n ∧ s = (f i).2 * ∏ j, w j ^ μ j}
  have base : ∀ n, n ≤ n₀ → chartLat y a n ≤ AddSubgroup.closure (T n) := by
    intro n hn
    rw [← hG n, AddSubgroup.closure_le]
    intro g hg
    apply AddSubgroup.subset_closure
    refine ⟨P.equivFin ⟨(n, g), memP n g hn hg⟩, 0, ?_, ?_⟩ <;> simp [f]
  have step : ∀ n (j : Fin q), ∀ s ∈ AddSubgroup.closure (T n),
      s * w j ∈ AddSubgroup.closure (T (n + 1)) := by
    intro n j s hs
    induction hs using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, μ, hdeg, rfl⟩ := hx
      apply AddSubgroup.subset_closure
      refine ⟨i, μ + Pi.single j 1, ?_, ?_⟩
      · simp only [Pi.add_apply, Finset.sum_add_distrib]
        rw [← hdeg, Finset.sum_pi_single']
        simp [add_assoc]
      · have hprod : ∏ k, w k ^ ((μ + Pi.single j 1 : Fin q → ℕ) k) = (∏ k, w k ^ μ k) * w j := by
          simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
          congr 1
          rw [Fintype.prod_eq_single j]
          · simp
          · intro k hk
            simp [hk]
        rw [hprod, mul_assoc]
    | zero => simp
    | add x z _ _ hx hz => rw [add_mul]; exact add_mem hx hz
    | neg x _ hx => rw [neg_mul]; exact neg_mem hx
  refine ⟨P.card, fun i => (f i).1, fun i => (f i).2, fun i => ofP _ (P.equivFin.symm i).2, ?_⟩
  intro n
  induction n with
  | zero => exact base 0 (Nat.zero_le _)
  | succ n ih =>
    by_cases h : n + 1 ≤ n₀
    · exact base _ h
    · have hn : n₀ ≤ n := by omega
      refine (hn₀ n hn).trans ?_
      rw [AddSubgroup.closure_le]
      rintro t ⟨s, hs, j, rfl⟩
      exact step n j s (ih hs)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 Filter Topology MeasureTheory

noncomputable section

namespace ConstantShift

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


omit [∀ k, Fintype (ι k)] in
theorem sheetDensity_add_const (P : Ideal (MRing ι)) {e : ℕ} {φ φ' : Fin e → ((Σ k, ι k) → ℂ) → ℝ}
    (h : ∀ j, ∃ c : ℝ, ∀ z ∈ mcPts P, φ' j z = φ j z + c)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (g : ((Σ k, ι k) → ℂ) → ℝ)
    (y : Fin e → ℂ) (w : ((k : K) → ι k) → ℂ) :
    sheetDensity P Ψ φ' g y w = sheetDensity P Ψ φ g y w := by
  unfold sheetDensity
  split_ifs with hγ
  · congr 1
    have hH : ∀ k, cxHessian (fun y' => φ' k (hγ.choose y')) y =
        cxHessian (fun y' => φ k (hγ.choose y')) y := by
      intro k
      obtain ⟨c, hc⟩ := h k
      have h1 : (fun y' => φ' k (hγ.choose y')) =ᶠ[𝓝 y] fun y' => φ k (hγ.choose y') + c := by
        filter_upwards [hγ.choose_spec.2] with y' hy'
        exact hc _ hy'.2.1
      have h2 : fderiv ℝ (fun y' => φ' k (hγ.choose y')) =ᶠ[𝓝 y]
          fderiv ℝ (fun y' => φ k (hγ.choose y')) := by
        filter_upwards [h1.eventuallyEq_nhds] with x hx
        rw [hx.fderiv_eq, fderiv_add_const]
      unfold cxHessian
      rw [h2.fderiv_eq]
    simp only [maDensity, hH]
  · rfl


omit [∀ k, Fintype (ι k)] in
theorem ptsIntegral_add_const (P : Ideal (MRing ι)) {e : ℕ} {φ φ' : Fin e → ((Σ k, ι k) → ℂ) → ℝ}
    (h : ∀ j, ∃ c : ℝ, ∀ z ∈ mcPts P, φ' j z = φ j z + c) (g : ((Σ k, ι k) → ℂ) → ℝ) :
    ptsIntegral P φ' g = ptsIntegral P φ g := by
  unfold ptsIntegral
  split_ifs
  · simp only [ptsIntegralAt, sheetDensity_add_const P h]
  · rfl


omit [∀ k, Fintype (ι k)] in
theorem ptsIntegral_const (P : Ideal (MRing ι)) {e : ℕ} (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (r : ℝ) :
    ptsIntegral P φ (fun _ => r) = r * ptsIntegral P φ (fun _ => 1) := by
  have hs : ∀ Ψ y w, sheetDensity P Ψ φ (fun _ => r) y w = r * sheetDensity P Ψ φ (fun _ => 1) y w := by
    intro Ψ y w
    unfold sheetDensity
    split_ifs <;> simp
  unfold ptsIntegral
  split_ifs
  · simp only [ptsIntegralAt, hs]
    rw [← integral_const_mul]
    congr 1
    funext y
    rw [mul_finsum_mem]
  · simp

theorem proof : ConstantShift.Statement := by
  intro K _ ι _ I P D A η hI hP hA
  have hS : IsSmoothHerm (HermLine.constShift A η) := isSmoothHerm_constShift hA η
  set g := geomDeg P A D with hg
  let L : ℕ → Fin (D + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := fun n i =>
    if (i : ℕ) < n then HermLine.constShift A η else A
  have hLs : ∀ n i, IsSmoothHerm (L n i) := by
    intro n i
    dsimp only [L]
    split_ifs
    exacts [hS, hA]
  have hLpot : ∀ n i, ∃ c : ℝ, ∀ z ∈ mcPts P, Real.log ((L n i).h z) = Real.log (A.h z) + c := by
    intro n i
    dsimp only [L]
    split_ifs
    · refine ⟨-η, fun z hz => ?_⟩
      rw [constShift_h, Real.log_mul (A.pos z hz.1).ne' (Real.exp_pos _).ne', Real.log_exp]
    · exact ⟨0, fun z _ => by rw [add_zero]⟩
  have step : ∀ n, n < D + 1 → I P (D + 1) (L (n + 1)) = I P (D + 1) (L n) - η * g := by
    intro n hn
    set j : Fin (D + 1) := ⟨n, hn⟩ with hj
    set σ : Equiv.Perm (Fin (D + 1)) := Equiv.swap j (Fin.last D) with hσ
    set M : Fin D → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := Fin.init (L n ∘ σ) with hMdef
    have hσl : σ (Fin.last D) = j := Equiv.swap_apply_right _ _
    have hne : ∀ i : Fin D, σ (Fin.castSucc i) ≠ j := by
      intro i h'
      rw [← hσl] at h'
      exact (Fin.castSucc_lt_last i).ne (σ.injective h')
    have hM : Fin.init (L (n + 1) ∘ σ) = M := by
      funext i
      have hv : ((σ (Fin.castSucc i) : Fin (D + 1)) : ℕ) ≠ n := fun h' => hne i (Fin.ext h')
      have hiff : ((σ (Fin.castSucc i) : Fin (D + 1)) : ℕ) < n + 1 ↔
          ((σ (Fin.castSucc i) : Fin (D + 1)) : ℕ) < n := by omega
      simp only [hMdef, Fin.init, Function.comp, L, hiff]
    have e0 : L n ∘ σ = Fin.snoc M A := by
      have h0 := Fin.snoc_init_self (q := L n ∘ σ)
      have hl : (L n ∘ σ) (Fin.last D) = A := by
        simp only [Function.comp, hσl, hj, L, lt_irrefl, if_false]
      rw [hl] at h0
      exact h0.symm
    have e1 : L (n + 1) ∘ σ = Fin.snoc M (HermLine.constShift A η) := by
      have h0 := Fin.snoc_init_self (q := L (n + 1) ∘ σ)
      have hl : (L (n + 1) ∘ σ) (Fin.last D) = HermLine.constShift A η := by
        simp only [Function.comp, hσl, hj, L, lt_add_one, if_true]
      rw [hl, hM] at h0
      exact h0.symm
    have hMs : ∀ i, IsSmoothHerm (M i) := fun i => hLs n _
    have hmc : I P (D + 1) (Fin.snoc M (HermLine.constShift A η)) =
        I P (D + 1) (Fin.snoc M A) - ptsIntegral P (pot M) (fun _ => η) :=
      metricChange K ι I hI P D M A (fun _ => η) (fun _ _ _ => rfl) hP hMs hA contDiffOn_const
    have hint : ptsIntegral P (pot M) (fun _ => η) = η * g := by
      rw [ptsIntegral_const, hg, geomDeg]
      congr 1
      exact ptsIntegral_add_const P (fun i => hLpot n _) _
    rw [← hI.1 P (D + 1) (L (n + 1)) σ hP (hLs (n + 1)), ← hI.1 P (D + 1) (L n) σ hP (hLs n), e0, e1,
      hmc, hint]
  have hall : ∀ n, n ≤ D + 1 → I P (D + 1) (L n) = I P (D + 1) (L 0) - n * η * g := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      rw [step n (by omega), ih (by omega)]
      push_cast
      ring
  have hL0 : L 0 = fun _ => A := by
    funext i
    simp [L]
  have hLD : L (D + 1) = fun _ => HermLine.constShift A η := by
    funext i
    simp [L, i.isLt]
  have := hall (D + 1) le_rfl
  rw [hL0, hLD] at this
  rw [this]
  push_cast
  ring

end ConstantShift

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace KleimanNefF

variable {F : Type} [Field F] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isMultiProjPrime_dvr [DecidableEq K] {V : Ideal (MRingOver F ι)} (hV : IsMultiProjPrime V) :
    NumbersDVR.IsMultiProjPrime (R := F) (ι := ι) V :=
  ⟨hV.1, (NumbersDVR.VocabMultiHomogIdeal.proof NumbersDVR.VocabMultiHomog.proof F K ι V).1 hV.2.1, hV.2.2⟩

theorem isProjVarF_of_mem_support [DecidableEq K] {V : Ideal (MRingOver F ι)} {n : ℕ}
    (hV : IsProjVarF V (n + 1)) {f g : MRingOver F ι} {bf bg : K → ℕ}
    (hf : NumbersDVR.IsMultiHomog f bf) (hg : NumbersDVR.IsMultiHomog g bg) (hfV : f ∉ V) (hgV : g ∉ V)
    {W : Ideal (MRingOver F ι)} (hW : W ∈ (ReciprocityTheory.ChartRestriction.G.AI.I1.ratDiv V f g).support) :
    IsProjVarF W n := by
  have hVd := isMultiProjPrime_dvr hV.1
  have hrel : FieldNumbers.relDim V = ((n + 1 : ℕ) : WithBot (WithTop ℤ)) :=
    (FieldNumbers.CutRegular.relDim_eq_natCast_iff V (n + 1)).2 hV.2
  have key : ∀ (s : MRingOver F ι) (b : K → ℕ), NumbersDVR.IsMultiHomog s b → s ∉ V →
      ReciprocityTheory.ChartRestriction.G.Geo.divCycle V s W ≠ 0 → IsProjVarF W n := by
    intro s b hs hsV hne
    have hne' : NumbersDVR.divCycle V s W ≠ 0 := by
      rw [← NumbersDVR.VocabDivCycle.proof F K ι V s W]
      exact_mod_cast hne
    obtain ⟨hW1, hW2⟩ := FieldNumbers.DivCycleSupport.full F K ι V hVd n hrel b s hs hsV W hne'
    exact ⟨⟨hW1.isPrime, (NumbersDVR.VocabMultiHomogIdeal.proof NumbersDVR.VocabMultiHomog.proof F K ι W).2
      hW1.multiHomog, hW1.relevant⟩, (FieldNumbers.CutRegular.relDim_eq_natCast_iff W n).1 hW2⟩
  rw [Finsupp.mem_support_iff, ReciprocityTheory.ChartRestriction.G.AI.I1.ratDiv, Finsupp.sub_apply, Finsupp.mapRange_apply,
    Finsupp.mapRange_apply] at hW
  by_cases hfW : ReciprocityTheory.ChartRestriction.G.Geo.divCycle V f W = 0
  · refine key g bg hg hgV fun h => hW ?_
    rw [hfW, h]
    simp
  · exact key f bf hf hfV hfW

theorem eq_intNum [DecidableEq K] {I : IFamily F ι} (hI : IsFieldIntersection I) :
    ∀ (n : ℕ) (V : Ideal (MRingOver F ι)) (L : Fin n → K → ℤ), IsProjVarF V n →
      I V n L = NumbersDVR.intNum F V L := by
  have hJ : IsFieldIntersection (F := F) (ι := ι) (fun V _ L => NumbersDVR.intNum F V L) :=
    NumbersDVR.IntNumIsFieldIntersection.full F K ι
  intro n
  induction n with
  | zero =>
    intro V L hV
    choose i hi using hV.1.2.2
    exact (hI.1 V L i hV hi).trans (hJ.1 V L i hV hi).symm
  | succ n ih =>
    intro V L hV
    obtain ⟨bf, bg, f, g, hf, hg, hfV, hgV, hb⟩ :=
      FieldNumbers.ExistsForm.full F K ι V (isMultiProjPrime_dvr hV.1) (L (Fin.last n))
    have hs : IsRatSection V (L (Fin.last n)) f g :=
      ⟨bf, bg, (NumbersDVR.VocabMultiHomog.proof F K ι f bf).2 hf,
        (NumbersDVR.VocabMultiHomog.proof F K ι g bg).2 hg, hfV, hgV, fun k => congrFun hb k⟩
    have e1 : I V (n + 1) L = ReciprocityTheory.ChartRestriction.G.AI.I1.cycEval (fun W => I W n (Fin.init L))
        (ReciprocityTheory.ChartRestriction.G.AI.I1.ratDiv V f g) := by
      have h := hI.2 V n (Fin.init L) (L (Fin.last n)) f g hV hs
      rwa [Fin.snoc_init_self] at h
    have e2 : NumbersDVR.intNum F V L = ReciprocityTheory.ChartRestriction.G.AI.I1.cycEval
        (fun W => NumbersDVR.intNum F W (Fin.init L)) (ReciprocityTheory.ChartRestriction.G.AI.I1.ratDiv V f g) := by
      have h := hJ.2 V n (Fin.init L) (L (Fin.last n)) f g hV hs
      rwa [Fin.snoc_init_self] at h
    rw [e1, e2, ReciprocityTheory.ChartRestriction.G.AI.I1.cycEval, ReciprocityTheory.ChartRestriction.G.AI.I1.cycEval]
    refine Finsupp.sum_congr fun W hW => ?_
    rw [ih W _ (isProjVarF_of_mem_support hV hf hg hfV hgV hW)]

theorem map_update_add₂ {I : IFamily F ι} (hI : IsFieldIntersection I) {V : Ideal (MRingOver F ι)} {n : ℕ}
    (hV : IsProjVarF V n) (L : Fin n → K → ℤ) (j : Fin n) (x y : K → ℤ) :
    I V n (Function.update L j (x + y)) = I V n (Function.update L j x) + I V n (Function.update L j y) := by
  classical
  rw [eq_intNum hI n V _ hV, eq_intNum hI n V _ hV, eq_intNum hI n V _ hV]
  have hVd := isMultiProjPrime_dvr hV.1
  exact FieldNumbers.IntNumAdd.full F K ι V hVd.multiHomog hVd.relevant n
    ((FieldNumbers.CutRegular.relDim_eq_natCast_iff V n).2 hV.2) L j x y

theorem nsmul_position {I : IFamily F ι} (hI : IsFieldIntersection I) {V : Ideal (MRingOver F ι)} {n : ℕ}
    (hV : IsProjVarF V n) (L : Fin n → K → ℤ) (j : Fin n) (m : ℕ) (x : K → ℤ) :
    I V n (Function.update L j ((m : ℤ) • x)) = m * I V n (Function.update L j x) := by
  induction m with
  | zero =>
    have h := map_update_add₂ hI hV L j 0 0
    rw [add_zero] at h
    rw [Nat.cast_zero, zero_smul, zero_mul]
    linarith
  | succ m ih =>
    rw [Nat.cast_succ, add_smul, one_smul, map_update_add₂ hI hV, ih]
    ring

end KleimanNefF

theorem KleimanNefF.proof (hKA : KH.KAmpStatement) (hGP : GeneratedProductNonneg.Statement) :
    KH.KleimanNefFStatement := by
  classical
  intro F _ K _ ι _ I V n a hI hV hnef
  let _ : LinearOrder K := LinearOrder.lift' (Fintype.equivFin K) (Fintype.equivFin K).injective
  let _ : ∀ k, LinearOrder (ι k) := fun k =>
    LinearOrder.lift' (Fintype.equivFin (ι k)) (Fintype.equivFin (ι k)).injective
  let H : K → ℤ := fun _ => ((1 : ℕ) : ℤ)
  let c : Finset (Fin n) → ℤ := fun S => I V n (fun i => if i ∈ S then H else a i)
  have key : ∀ q : ℕ, 1 ≤ q → 0 ≤ ∑ S : Finset (Fin n), (q : ℤ) ^ Sᶜ.card * c S := by
    intro q hq
    have hamp := fun j => hKA F K ι I V n (a j) q 1 hI hV (hnef j) hq le_rfl
    choose p hp hgen _ using hamp
    let B : Fin n → K → ℤ := fun j => p j • (q • a j + H)
    have hB : 0 ≤ I V n B := hGP F K ι I V n B hI hV hgen
    have hposition : ∀ (L : Fin n → K → ℤ) (i : Fin n), I V n (Function.update L i (B i)) =
        ((q : ℤ) * p i) * I V n (Function.update L i (a i)) + (p i : ℤ) * I V n (Function.update L i H) := by
      intro L i
      have e : B i = ((q * p i : ℕ) : ℤ) • a i + ((p i : ℕ) : ℤ) • H := by
        funext k
        simp only [B, Pi.add_apply, Pi.smul_apply]
        simp only [H, nsmul_eq_mul, smul_eq_mul]
        push_cast
        ring
      rw [e, KleimanNefF.map_update_add₂ hI hV, KleimanNefF.nsmul_position hI hV, KleimanNefF.nsmul_position hI hV]
      push_cast
      ring
    have hexp := Kleiman.sum_expand_positions (I V n) B a (fun _ => H) (fun i => (q : ℤ) * p i)
      (fun i => (p i : ℤ)) hposition
    have hw : ∀ S : Finset (Fin n), (∏ i ∈ S, (p i : ℤ)) * (∏ i ∈ Sᶜ, ((q : ℤ) * p i)) =
        (∏ i, (p i : ℤ)) * (q : ℤ) ^ Sᶜ.card := by
      intro S
      rw [Finset.prod_mul_distrib, Finset.prod_const, ← mul_assoc, mul_comm _ ((q : ℤ) ^ _), mul_assoc,
        Finset.prod_mul_prod_compl, mul_comm]
    simp only [hw, mul_assoc] at hexp
    rw [← Finset.mul_sum] at hexp
    have hprod : 0 < ∏ i, (p i : ℤ) := Finset.prod_pos fun i _ => by exact_mod_cast hp i
    rw [hexp] at hB
    exact (mul_nonneg_iff_of_pos_left hprod).mp hB
  have h0 := Kleiman.nonneg_of_poly c key
  simpa [c] using h0

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M

noncomputable section

def BlockResolutionDegree.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (d : HSMBlockDatum D K ι Ω) (A₀ A₁ : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι),
    A₀.a = ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg d.k₀ → A₁.a = ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg d.k₀ → IsSmoothHerm A₀ → IsSmoothHerm A₁ →
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ C : ℝ, ∀ n : ℕ,
      |(Module.finrank ℤ (secM d.y (blockDeg d.k₀ n)) : ℝ) -
          mInt d.R.A (fun _ => blockInterpPot d A₀ A₁ t) (fun _ => 1) * (n : ℝ) ^ D / (D.factorial : ℝ)| ≤
        C * ((n : ℝ) + 1) ^ (D - 1)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M

noncomputable section

def BlockResolutionDegreeIntegral.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (d : HSMBlockDatum D K ι Ω) (A₀ A₁ : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι),
    A₀.a = ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg d.k₀ → A₁.a = ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg d.k₀ → IsSmoothHerm A₀ → IsSmoothHerm A₁ →
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      mInt d.R.A (fun _ => blockInterpPot d A₀ A₁ t) (fun _ => 1) =
        (genDeg (mCoordIdeal d.y) D (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg d.k₀) : ℝ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
