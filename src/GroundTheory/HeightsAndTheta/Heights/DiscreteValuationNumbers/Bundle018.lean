module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle007
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle015
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleMul
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PRepresentative
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle009
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle013
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle008
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Sub.Prod
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.LinearAlgebra.Dual.Basis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

section General

variable {A : Type*} [CommRing A]

theorem localizedQuot_nontrivial_of_le (J W : Ideal A) [W.IsPrime] (h : J ≤ W) :
    Nontrivial (LocalizedModule W.primeCompl (A ⧸ J)) := by
  refine ⟨⟨LocalizedModule.mk 1 1, 0, fun e => ?_⟩⟩
  rw [← LocalizedModule.zero_mk (1 : W.primeCompl), LocalizedModule.mk_eq] at e
  obtain ⟨u, hu⟩ := e
  simp only [one_smul, smul_zero] at hu
  rw [Submonoid.smul_def, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, mul_one,
    Ideal.Quotient.eq_zero_iff_mem] at hu
  exact u.2 (h hu)

theorem withBot_lt_natCast_of_add_one_le (x : WithBot ℕ∞) (N : ℕ) (h : x + 1 ≤ (N : WithBot ℕ∞)) :
    x < (N : WithBot ℕ∞) := by
  induction x using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe y =>
    have h' : y + 1 ≤ (N : ℕ∞) := by exact_mod_cast h
    have hy : y ≠ ⊤ := by
      rintro rfl
      simp at h'
    exact_mod_cast (ENat.add_one_le_iff hy).mp h'

end General

theorem LeftExpansion.proof (hcut : VNumCut.Statement.{u}) : LeftExpansion.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c s hs hsP hno L
  classical
  have : P.IsPrime := hP.multiProj.isPrime

  have key : ∀ G, ratDiv P f g G ≠ 0 →
      vNum G (Matrix.vecCons (fun k => (c k : ℤ)) L) = cycEval (fun U => vNum U L) (divCycle G s) := by
    intro G hG
    have hmin : ∃ h : MRing ι O, h ∉ P ∧ (∃ e : K → ℕ, IsMultiHomog h e) ∧
        G ∈ (P ⊔ Ideal.span {h}).minimalPrimes ∧ IsRelevant G := by
      obtain ⟨bf, bg, hf, hg, -⟩ := hD.degrees
      by_cases hfG : divCycle P f G = 0
      · have hgG : divCycle P g G ≠ 0 := by
          intro h0
          apply hG
          simp [ratDiv, hfG, h0]
        unfold divCycle at hgG
        split_ifs at hgG with hW
        · exact ⟨g, hD.den_not_mem, ⟨bg, hg⟩, hW.1, hW.2⟩
        · exact absurd rfl hgG
      · unfold divCycle at hfG
        split_ifs at hfG with hW
        · exact ⟨f, hD.num_not_mem, ⟨bf, hf⟩, hW.1, hW.2⟩
        · exact absurd rfl hfG
    obtain ⟨h, hhP, ⟨e, he⟩, hGmin, hGrel⟩ := hmin
    have hGp : G.IsPrime := hGmin.1.1
    have hPG : P ≤ G := le_sup_left.trans hGmin.1.2
    have hhG : h ∈ G := hGmin.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))
    have hPltG : P < G := lt_of_le_of_ne hPG (fun hPeq => hhP (hPeq ▸ hhG))
    have hGmh : IsMultiHomogIdeal G :=
      MinimalPrimeMultiHomog.proof O K ι _ G
        (SupSpanMultiHomog.proof O K ι P h e hP.multiProj.multiHomog he) hGmin
    have hϖG : (C ϖ : MRing ι O) ∈ G := hD.vertical G hG
    have hdim : ringKrullDim (MRing ι O ⧸ G) < ((d + 2 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
      have hdrop := DimStrictDrop.proof (MRing ι O) P G hPltG
      rw [hP.dim] at hdrop
      have hN : d + 1 + 1 + Fintype.card K = d + 2 + Fintype.card K := by omega
      rw [hN] at hdrop
      exact withBot_lt_natCast_of_add_one_le _ _ hdrop
    have hsG : s ∉ G := by
      intro hsG
      have h1 := mem_minimalPrimes_sup_span_mul (x := h) hsP hGmin
      have hGs : G ∈ (P ⊔ Ideal.span {s}).minimalPrimes := by
        refine ⟨⟨hGp, sup_le hPG ((Ideal.span_singleton_le_iff_mem _).mpr hsG)⟩, fun Q hQ hQG => ?_⟩
        have hsQ : s ∈ Q := hQ.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))
        exact h1.2 ⟨hQ.1, sup_le (le_sup_left.trans hQ.2)
          ((Ideal.span_singleton_le_iff_mem _).mpr (Q.mul_mem_left h hsQ))⟩ hQG
      have hne : divCycle P s G ≠ 0 := by
        unfold divCycle
        rw [dite_eq_left ⟨hGs, hGrel⟩]
        have := localizedQuot_nontrivial_of_le (P ⊔ Ideal.span {s}) G hGs.1.2
        have h0 : multAt (P ⊔ Ideal.span {s}) G ≠ 0 :=
          (Module.length_pos (R := Localization.AtPrime G)
            (M := LocalizedModule G.primeCompl (MRing ι O ⧸ (P ⊔ Ideal.span {s})))).ne'
        have htop := length_localizedQuot_ne_top _ G hGs
        exact_mod_cast (ENat.toNat_pos h0 htop).ne'
      exact hG (hno G hϖG hne)
    exact hcut O ϖ hϖ K ι G d hGp hGmh hϖG hdim s c hs hsG L

  have hfinR : (Function.support (ratDiv P f g)).Finite :=
    ((DivCycleFiniteSupport.proof O K ι P f).union (DivCycleFiniteSupport.proof O K ι P g)).subset
      (fun G hG => by
        by_contra hc
        simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hc
        exact hG (by simp [ratDiv, hc.1, hc.2]))
  set A := hfinR.toFinset with hAdef
  have hfinB : (⋃ G ∈ A, Function.support (divCycle G s)).Finite :=
    A.finite_toSet.biUnion (fun G _ => DivCycleFiniteSupport.proof O K ι G s)
  set B := hfinB.toFinset with hBdef
  have hA : ∀ G, ratDiv P f g G ≠ 0 → G ∈ A := fun G hG => hfinR.mem_toFinset.mpr hG
  have hB : ∀ G ∈ A, ∀ U, divCycle G s U ≠ 0 → U ∈ B :=
    fun G hGA U hU => hfinB.mem_toFinset.mpr (Set.mem_biUnion hGA hU)
  have eL : cycEval (fun G => vNum G (Matrix.vecCons (fun k => (c k : ℤ)) L)) (ratDiv P f g) =
      ∑ G ∈ A, ∑ U ∈ B, ratDiv P f g G * divCycle G s U * vNum U L := by
    unfold cycEval
    rw [finsum_eq_sum_of_support_subset _ (s := A) (fun G hG => hA G (left_ne_zero_of_mul hG))]
    refine Finset.sum_congr rfl fun G _ => ?_
    by_cases hr : ratDiv P f g G = 0
    · simp [hr]
    · rw [key G hr, cycEval, finsum_eq_sum_of_support_subset _ (s := B)
        (fun U hU => hB G (hA G hr) U (left_ne_zero_of_mul hU)), Finset.mul_sum]
      exact Finset.sum_congr rfl fun U _ => by ring
  have eR : cycEval (fun U => vNum U L) (fun U => cycEval (fun G => divCycle G s U) (ratDiv P f g)) =
      ∑ U ∈ B, ∑ G ∈ A, ratDiv P f g G * divCycle G s U * vNum U L := by
    unfold cycEval
    have hsub : Function.support (fun U =>
        (∑ᶠ G, ratDiv P f g G * divCycle G s U) * vNum U L) ⊆ ↑B := by
      intro U hU
      have h1 := left_ne_zero_of_mul hU
      obtain ⟨G, hG⟩ : ∃ G, ratDiv P f g G * divCycle G s U ≠ 0 := by
        by_contra hc
        push Not at hc
        exact h1 (finsum_eq_zero_of_forall_eq_zero hc)
      exact hB G (hA G (left_ne_zero_of_mul hG)) U (right_ne_zero_of_mul hG)
    rw [finsum_eq_sum_of_support_subset _ hsub]
    refine Finset.sum_congr rfl fun U _ => ?_
    rw [finsum_eq_sum_of_support_subset _ (s := A) (fun G hG => hA G (left_ne_zero_of_mul hG)),
      Finset.sum_mul]
  rw [eL, eR, Finset.sum_comm]

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Helpers

variable {K : Type*} [DecidableEq K] {ι : K → Type*} {R : Type*} [CommRing R]

theorem exists_form_pair_left {P H : Ideal (MRing ι R)} [hP : P.IsPrime]
    (hPm : IsMultiHomogIdeal P) (hPH : P ≤ H) {f g u v : MRing ι R} {bf bg : K → ℕ}
    (hf : IsMultiHomog f bf) (hg : IsMultiHomog g bg) (hfP : f ∉ P) (hu : u ∉ H)
    (h : u * f - v * g ∈ P) :
    ∃ (u' v' : MRing ι R) (e d : K → ℕ), IsMultiHomog u' e ∧ IsMultiHomog v' d ∧
      d + bg = e + bf ∧ u' ∉ H ∧ u' * f - v' * g ∈ P := by
  classical
  obtain ⟨e, he⟩ := exists_component_not_mem hu
  set u' := weightedHomogeneousComponent (blockWeight ι) e u with hu'
  have hc := hPm _ h (e + bf)
  rw [map_sub, weightedHomogeneousComponent_mul_form hf, weightedHomogeneousComponent_mul_form hg,
    if_pos le_add_self, add_tsub_cancel_right, ← hu'] at hc
  by_cases hle : bg ≤ e + bf
  · rw [if_pos hle] at hc
    exact ⟨u', _, e, e + bf - bg, weightedHomogeneousComponent_isWeightedHomogeneous _ _,
      weightedHomogeneousComponent_isWeightedHomogeneous _ _, tsub_add_cancel_of_le hle, he, hc⟩
  · rw [if_neg hle, sub_zero] at hc
    exact ((hP.mem_or_mem hc).elim (fun h' => he (hPH h')) hfP).elim

end Helpers

theorem VertCutEff.proof (h1 : VNumCut.Statement.{u}) (h2 : DivisorIdealCycle.Statement.{u})
    (h3 : IntNumAddFirst.Statement.{u}) : VertCutEff.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P n hmodel b f g hE W x hxP hWmin hrel hWmh hϖW hcyc L
  have hP : P.IsPrime := hmodel.multiProj.isPrime
  have hWp : W.IsPrime := hWmin.1.1
  have hPW : P ≤ W := le_sup_left.trans hWmin.1.2
  obtain ⟨hV, hreg⟩ := hE
  obtain ⟨bf, bg, hf, hg, hb⟩ := hV.degrees
  obtain ⟨u₀, v₀, hu₀, h₀⟩ := hreg W hWp hPW hrel
  obtain ⟨u, v, e, d, hu, hv, hde, huW, huv⟩ :=
    exists_form_pair_left hmodel.multiProj.multiHomog hPW hf hg hV.num_not_mem hu₀ h₀
  have huP : u ∉ P := fun h => huW (hPW h)

  have hvW : v ∉ W := by
    intro hvW
    have hvP : v ∉ P := by
      intro hvP
      have hufP : u * f ∈ P := by
        have h' := P.add_mem huv (P.mul_mem_right g hvP)
        rwa [sub_add_cancel] at h'
      exact (hP.mem_or_mem hufP).elim huP hV.num_not_mem
    have hmul := mem_minimalPrimes_sup_span_mul (P := P) (x := x) (y := v) hvP hWmin
    have hWv : W ∈ (P ⊔ Ideal.span {v}).minimalPrimes :=
      ⟨⟨hWp, sup_le hPW ((Ideal.span_singleton_le_iff_mem _).mpr hvW)⟩, fun Q hQ hQW =>
        hmul.2 ⟨hQ.1, sup_le (le_sup_left.trans hQ.2) ((Ideal.span_singleton_le_iff_mem _).mpr
          (Q.mul_mem_left x (hQ.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self v)))))⟩ hQW⟩
    have hpos : divCycle P v W ≠ 0 := by
      unfold divCycle
      rw [dite_eq_left ⟨hWv, hrel⟩]
      have hne := length_localizedQuot_ne_top (P ⊔ Ideal.span {v}) W hWv
      have hnz : multAt (P ⊔ Ideal.span {v}) W ≠ 0 := by
        unfold multAt
        rw [Ne, Module.length_eq_zero_iff, LocalizedModule.subsingleton_iff]
        intro hs
        obtain ⟨r, hr, hr0⟩ := hs (Ideal.Quotient.mk _ 1)
        rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, mul_one,
          Ideal.Quotient.eq_zero_iff_mem] at hr0
        exact hr (hWv.1.2 hr0)
      have htn : (multAt (P ⊔ Ideal.span {v}) W).toNat ≠ 0 :=
        fun h0 => (ENat.toNat_eq_zero.mp h0).elim hnz hne
      exact_mod_cast htn
    have hu0 : divCycle P u W = 0 := by
      unfold divCycle
      rw [dite_eq_right]
      rintro ⟨h, -⟩
      exact huW (h.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self u)))
    have e1 := congrFun (DivCycleMul.proof O K ι P u f hP huP hV.num_not_mem) W
    have e2 := congrFun (DivCycleMul.proof O K ι P v g hP hvP hV.den_not_mem) W
    have e3 := congrFun (divCycle_eq_of_sub_mem huv) W
    simp only [Pi.add_apply] at e1 e2
    unfold ratDiv at hcyc
    omega

  have hϖP : (C ϖ : MRing ι O) ∉ P := by
    intro h
    have h' : ϖ ∈ P.comap (C : O →+* MRing ι O) := h
    rw [hmodel.noTorsion, Ideal.mem_bot] at h'
    exact hϖ.ne_zero h'
  have hlt : P < W := lt_of_le_of_ne hPW (fun h => hϖP (h ▸ hϖW))
  have hdim : ringKrullDim (MRing ι O ⧸ W) < ((n + 2 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    have h' := DimStrictDrop.proof (MRing ι O) P W hlt
    rw [hmodel.dim, show n + 1 + 1 + Fintype.card K = n + 2 + Fintype.card K by omega] at h'
    exact withBotENat_lt_of_add_one_le h'

  have hcu := h1 O ϖ hϖ K ι W n hWp hWmh hϖW hdim u e hu huW L
  have hcv := h1 O ϖ hϖ K ι W n hWp hWmh hϖW hdim v d hv hvW L
  have hWbar : (specialIdeal W).IsPrime := (SpecialIdealCorresp.proof O ϖ hϖ K ι P W hWp hϖW).1
  have hadd := h3 (IsLocalRing.ResidueField O) K ι n (specialIdeal W) hWbar
    (SpecialIdealMultiHomog.proof O K ι W hWmh)
    (by rw [SpecialQuotDim.proof O ϖ hϖ K ι W hϖW]; exact hdim) b (fun k => (e k : ℤ)) L
  have hdeg : (fun k => (d k : ℤ)) = b + fun k => (e k : ℤ) := by
    rw [← hb]
    funext k
    have hk := congrFun hde k
    simp only [Pi.add_apply] at hk ⊢
    omega
  have key : vNum W (Matrix.vecCons b L) = vNum W (Matrix.vecCons (fun k => (d k : ℤ)) L) -
      vNum W (Matrix.vecCons (fun k => (e k : ℤ)) L) := by
    rw [hdeg]
    unfold vNum
    rw [hadd]
    ring
  rw [key, hcv, hcu, ← h2 O K ι P W f g u v hP hWp hPW hV.den_not_mem
    (fun U hU hWU hUrel => hreg U hU (hPW.trans hWU) hUrel) huW hvW huv]

  unfold cycEval ratDiv
  rw [← finsum_sub_distrib
    ((DivCycleFiniteSupport.proof O K ι W v).subset (Function.support_mul_subset_left _ _))
    ((DivCycleFiniteSupport.proof O K ι W u).subset (Function.support_mul_subset_left _ _))]
  refine finsum_congr fun U => ?_
  ring

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem TwistedDualGensSpan.sum_mul_mem_localized {R Ω : Type*} [CommRing R] [Field Ω] [Algebra R Ω]
    (A : Subalgebra R Ω) {f : Ω} (hf : f ∈ A) {r : ℕ} (a t : Fin r → Ω)
    (ha : ∀ q, ∃ n : ℕ, f ^ n * a q ∈ A) (ht : ∀ q, t q ∈ A) :
    ∃ n : ℕ, f ^ n * ∑ q, a q * t q ∈ A := by
  refine Finset.sum_induction _ (fun x => ∃ n : ℕ, f ^ n * x ∈ A) ?_ ⟨0, by simp⟩ ?_
  · rintro x z ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨n + m, ?_⟩
    have : f ^ (n + m) * (x + z) = f ^ m * (f ^ n * x) + f ^ n * (f ^ m * z) := by ring
    rw [this]
    exact add_mem (mul_mem (pow_mem hf _) hn) (mul_mem (pow_mem hf _) hm)
  · intro q _
    obtain ⟨n, hn⟩ := ha q
    exact ⟨n, by rw [← mul_assoc]; exact mul_mem hn (ht q)⟩

theorem TwistedDualGensSpan.proof : TwistedDualGensSpan.Statement := by
  unfold TwistedDualGensSpan.Statement
  intro R _ Ω _ _ K _ ι y N E _ _ B a M φ hφ c hc
  obtain ⟨k, f, cc, hf, hcc, hsum, hb⟩ := B.frame c hc
  choose b hli hsp hiff using hb
  obtain ⟨l0, hl0⟩ : ∃ l0, f l0 ≠ 0 := by
    by_contra! h
    simp [h] at hsum
  obtain ⟨β, hβ⟩ : ∃ β : Module.Basis (Fin N) Ω E, ∀ q, β q = b l0 q :=
    ⟨Module.Basis.mk (hli l0) (hsp l0).ge, fun q => Module.Basis.mk_apply _ _ _⟩
  have key : ∀ q, β.coord q ∈ Submodule.span Ω (Set.range φ) := by
    intro q
    have hden : ∀ l r, ∃ D ∈ chartRing R (segreVec y) c, D ≠ 0 ∧
        (f l ≠ 0 → D * β.coord q (b l r) ∈ chartRing R (segreVec y) c) := by
      intro l r
      by_cases hl : f l = 0
      · exact ⟨1, one_mem _, one_ne_zero, fun h => (h hl).elim⟩
      obtain ⟨n, hn⟩ := (hiff l (b l r)).2 ⟨Pi.single r 1, fun q' => ⟨0, by
        by_cases h : q' = r
        · subst h; simp
        · simp [h]⟩, by simp [Pi.single_apply]⟩
      obtain ⟨a', ha', hrep⟩ := (hiff l0 _).1 ⟨0, by simpa using hn⟩
      obtain ⟨m, hm⟩ := ha' q
      refine ⟨f l0 ^ m * f l ^ n, mul_mem (pow_mem (hf l0) _) (pow_mem (hf l) _),
        mul_ne_zero (pow_ne_zero _ hl0) (pow_ne_zero _ hl), fun _ => ?_⟩
      have hc' : β.coord q (f l ^ n • b l r) = a' q := by
        rw [hrep, show ∑ q, a' q • b l0 q = ∑ q, a' q • β q by simp [hβ],
          Module.Basis.coord_apply, Module.Basis.repr_sum_self]
      have : f l0 ^ m * f l ^ n * β.coord q (b l r) = f l0 ^ m * a' q := by
        rw [← hc', map_smul, smul_eq_mul]; ring
      rw [this]
      exact hm
    choose D hDA hD0 hDc using hden
    set d : Ω := ∏ p : Fin k × Fin N, D p.1 p.2 with hd
    have hd0 : d ≠ 0 := Finset.prod_ne_zero_iff.2 fun p _ => hD0 _ _
    have hdc : ∀ l r, f l ≠ 0 → d * β.coord q (b l r) ∈ chartRing R (segreVec y) c := by
      intro l r hl
      have hsplit := Finset.mul_prod_erase Finset.univ (fun p : Fin k × Fin N => D p.1 p.2)
        (Finset.mem_univ (l, r))
      dsimp only at hsplit
      rw [hd, ← hsplit]
      have : D l r * (∏ p ∈ Finset.univ.erase (l, r), D p.1 p.2) * β.coord q (b l r) =
          (∏ p ∈ Finset.univ.erase (l, r), D p.1 p.2) * (D l r * β.coord q (b l r)) := by ring
      rw [this]
      exact mul_mem (prod_mem fun p _ => hDA _ _) (hDc l r hl)
    have hψ : ∀ v ∈ B.lat c, (d • β.coord q) v ∈ chartRing R (segreVec y) c := by
      intro v hv
      rw [LinearMap.smul_apply, smul_eq_mul]
      refine Subalgebra.mem_of_finsetSum_eq_one_of_pow_smul_mem _ Finset.univ f cc hsum hf hcc _ ?_
      intro l
      by_cases hl : f l = 0
      · exact ⟨1, by simp [hl]⟩
      obtain ⟨a', ha', hrep⟩ := (hiff l v).1 ⟨0, by simpa using hv⟩
      obtain ⟨n, hn⟩ := TwistedDualGensSpan.sum_mul_mem_localized _ (hf l) a'
        (fun r => d * β.coord q (b l r)) ha' (fun r => hdc l r hl)
      refine ⟨n, ?_⟩
      have : d * β.coord q v = ∑ r, a' r * (d * β.coord q (b l r)) := by

        rw [hrep, map_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [map_smul, smul_eq_mul]; ring
      rw [smul_eq_mul, this]
      exact hn
    obtain ⟨u, -, hu⟩ := hφ.generate c hc (d • β.coord q) hψ
    have hmem : d • β.coord q ∈ Submodule.span Ω (Set.range φ) := by
      rw [hu]
      exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
    have : β.coord q = d⁻¹ • (d • β.coord q) := by rw [smul_smul, inv_mul_cancel₀ hd0, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ hmem
  rw [eq_top_iff, ← β.dualBasis.span_eq, Module.Basis.coe_dualBasis]
  exact Submodule.span_le.2 (by rintro _ ⟨q, rfl⟩; exact key q)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def GenericProjClosureDim.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω]
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (N : ℕ), 0 < N → ∀ (E : Type) [AddCommGroup E] [Module Ω E]
      (B B' : ChartBundle O (segreVec y) N E), SameGenericFibre ϖ B B' →
    ∀ (M M' : ℕ) (a₀ a₀' : K → ℤ) (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E),
      IsTwistedDualGens y B a₀ φ → IsTwistedDualGens y B' a₀' φ' →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]
      (e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ), AlgebraicIndependent Ω t →
      IsModelOver (pointIdeal O (pairProjCoord y e φ φ' t)) (d + (N - 1))

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def TruncSpecialize.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω]
    (K : Type) (ι : K → Type) (y : (Σ k, ι k) → Ω)
    (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E] (w : Module.Basis (Fin N) Ω E)
    (M : ℕ) (φ : Fin M → Module.Dual Ω E) (Φ : Type) [Field Φ] [Algebra Ω Φ] (t : Fin N → Φ),
    AlgebraicIndependent Ω t → ∀ i : Fin N,
      projIdeal F y w φ (truncCoord t ((i : ℕ) + 1)) ≤ projIdeal F y w φ (truncCoord t i) ∧
      ∀ x z : MRing (bundleIdx ι M) F,
        eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ (truncCoord t ((i : ℕ) + 1))) x =
          t i * eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω))
            (projCoord y w φ (truncCoord t ((i : ℕ) + 1))) z →
        eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ (truncCoord t i)) x = 0

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end
