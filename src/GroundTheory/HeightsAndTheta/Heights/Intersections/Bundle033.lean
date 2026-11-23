module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle021
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle014
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle007
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle010
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle030
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle031
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle024
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle029
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
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle003
public import Mathlib.RingTheory.OrderOfVanishing.Basic
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle006

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem pot_cons {e : ℕ} (M : HermLine ι) (L : Fin e → HermLine ι) :
    pot (Fin.cons M L : Fin (e + 1) → HermLine ι) = Fin.cons (fun z => Real.log (M.h z)) (pot L) := by
  funext j z
  refine Fin.cases ?_ (fun i => ?_) j <;> simp [pot]

theorem forall_cons {m : ℕ} {p : HermLine ι → Prop} {M : HermLine ι} {N : Fin m → HermLine ι}
    (hM : p M) (hN : ∀ j, p (N j)) : ∀ j, p ((Fin.cons M N : Fin (m + 1) → HermLine ι) j) :=
  fun j => Fin.cases (by simpa using hM) (fun i => by simpa using hN i) j

theorem ptsIntegral_neg {e : ℕ} (Q : Ideal (MRing ι)) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    (f : ((Σ k, ι k) → ℂ) → ℝ) : ptsIntegral Q φ (fun z => -f z) = -ptsIntegral Q φ f := by
  have key : ∀ (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) y w,
      sheetDensity Q Ψ φ (fun z => -f z) y w = -sheetDensity Q Ψ φ f y w := by
    intro Ψ y w
    unfold sheetDensity
    split_ifs <;> simp
  unfold ptsIntegral ptsIntegralAt
  split_ifs
  · simp only [key, finsum_neg_distrib, MeasureTheory.integral_neg]
  · simp

theorem log_h_eq_neg_logNorm_one (D : HermLine ι) :
    (fun z => Real.log (D.h z)) = fun z => -logNorm D 1 z := by
  funext z
  simp [logNorm, Real.log_inv]

theorem isSectionOn_one {Q : Ideal (MRing ι)} {d : ℕ} (hQ : IsArithVar Q d) {D : HermLine ι}
    (hDa : D.a = 0) : IsSectionOn Q D 1 := by
  refine ⟨0, fun k => by simp [hDa], fun m hm k => ?_,
    fun h => hQ.2.1.1.ne_top ((Ideal.eq_top_iff_one Q).2 h)⟩
  rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
  subst hm
  simp

theorem ptsIntegral_add_first_log (hAdd : PtsAddFirst.Statement) {Q : Ideal (MRing ι)} {e : ℕ}
    {L : Fin e → HermLine ι} {M N D : HermLine ι} (hQ : IsArithVar Q (e + 2))
    (hL : ∀ j, IsSmoothHerm (L j)) (hM : IsSmoothHerm M) (hN : IsSmoothHerm N) (hD : IsSmoothHerm D)
    (hDa : D.a = 0) :
    ptsIntegral Q (Fin.cons (fun z => Real.log ((M.tensor N).h z)) (pot L)) (fun z => Real.log (D.h z)) =
      ptsIntegral Q (Fin.cons (fun z => Real.log (M.h z)) (pot L)) (fun z => Real.log (D.h z)) +
        ptsIntegral Q (Fin.cons (fun z => Real.log (N.h z)) (pot L)) (fun z => Real.log (D.h z)) := by
  rw [log_h_eq_neg_logNorm_one D, ptsIntegral_neg, ptsIntegral_neg, ptsIntegral_neg,
    hAdd K ι Q e L M N D 1 hQ hL hM hN hD (isSectionOn_one hQ hDa)]
  ring

theorem tendsto_finsum_of_finite {α : Type*} {p : α → Prop} (hp : {W | p W}.Finite) {f : ℝ → α → ℝ}
    {g : α → ℝ} {l : Filter ℝ} (h : ∀ W, p W → Tendsto (fun ε => f ε W) l (𝓝 (g W))) :
    Tendsto (fun ε => ∑ᶠ (W) (_ : p W), f ε W) l (𝓝 (∑ᶠ (W) (_ : p W), g W)) := by
  have e : ∀ u : α → ℝ, ∑ᶠ (W) (_ : p W), u W = ∑ W ∈ hp.toFinset, u W :=
    fun u => finsum_mem_eq_finite_toFinset_sum u hp
  have e1 : (fun ε => ∑ᶠ (W) (_ : p W), f ε W) = fun ε => ∑ W ∈ hp.toFinset, f ε W :=
    funext fun ε => e (f ε)
  rw [e1, e g]
  exact tendsto_finsetSum _ fun W hW => h W (hp.mem_toFinset.mp hW)

theorem DeLeSemiPos.proof (hPL1 : ArithmeticPoincareLelongFormula) (hSt : StokesStatement) (hAdd : PtsAddFirst.Statement)
    (hLim : PtsRegLimit.Statement) (hMono : PtsMonoSemiPos.Statement) (hCurv : RegCurvBound.Statement)
    (hNot : HorizNotMem.Statement) : DeLeSemiPos.Statement := by
  intro K _ ι _ P n L A A' s s' hP hL hLp hA hA' hs hs' hnc
  obtain ⟨a, haA, hsa, hsP⟩ := id hs
  obtain ⟨a', haA', hsa', hs'P⟩ := id hs'
  have ht : ∃ b : K → ℕ, (∀ k, A.a k = b k) ∧ IsMultiHomog s b := ⟨a, haA, hsa⟩
  have ht' : ∃ b : K → ℕ, (∀ k, A'.a k = b k) ∧ IsMultiHomog s' b := ⟨a', haA', hsa'⟩
  obtain ⟨C, hC⟩ := hCurv K ι A' s' ht' hA'
  have hT := isSmoothHerm_ofMetrics_fs (ι := ι) (fun _ => (C : ℤ))
  generalize HermLine.ofMetrics (fun k => fsMetric (ι := ι k)) (fun _ => (C : ℤ)) = T at hC hT
  have hfin : ∀ t : MRing ι, {W | W ∈ divSupp P t ∧ IsHorizontal W}.Finite :=
    fun t => (divSupp_finite P t).subset fun W h => h.1

  have e1 : ∀ ε : ℝ, 0 < ε →
      ptsIntegral P (pot (Fin.cons ((A'.tensor (regLine A' s' ht' ε)).tensor T) L)) (logNorm A s) =
        ptsIntegral P (Fin.cons (fun z => Real.log (A'.h z)) (pot L)) (logNorm A s) +
          ((∑ᶠ (W) (_ : W ∈ divSupp P s ∧ IsHorizontal W), (multAt (P ⊔ Ideal.span {s}) W : ℝ) *
              ptsIntegral W (pot L) (fun z => Real.log ((regLine A' s' ht' ε).h z))) -
            ptsIntegral P (Fin.cons (fun z => Real.log (A.h z)) (pot L))
              (fun z => Real.log ((regLine A' s' ht' ε).h z))) +
          ptsIntegral P (Fin.cons (fun z => Real.log (T.h z)) (pot L)) (logNorm A s) := by
    intro ε hε
    have hB : IsSmoothHerm (regLine A' s' ht' ε) := isSmoothHerm_regLine hA' hε
    rw [pot_cons, hAdd K ι P n L _ T A s hP hL (isSmoothHerm_tensor hA' hB) hT hA hs,
      hAdd K ι P n L A' _ A s hP hL hA' hB hA hs, hPL1 K ι P n L A _ s hP hL hA hB rfl hs]
  have h1 : Tendsto
      (fun ε => ptsIntegral P (pot (Fin.cons ((A'.tensor (regLine A' s' ht' ε)).tensor T) L)) (logNorm A s))
      (𝓝[>] 0)
      (𝓝 (ptsIntegral P (Fin.cons (fun z => Real.log (A'.h z)) (pot L)) (logNorm A s) +
        ((∑ᶠ (W) (_ : W ∈ divSupp P s ∧ IsHorizontal W), (multAt (P ⊔ Ideal.span {s}) W : ℝ) *
            ptsIntegral W (pot L) (logNorm A' s')) -
          ptsIntegral P (Fin.cons (fun z => Real.log (A.h z)) (pot L)) (logNorm A' s')) +
        ptsIntegral P (Fin.cons (fun z => Real.log (T.h z)) (pot L)) (logNorm A s))) := by
    have ev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), _ := eventually_mem_nhdsWithin.mono fun ε hε => (e1 ε hε).symm
    refine Tendsto.congr' ev ((tendsto_const_nhds.add
      ((tendsto_finsum_of_finite (hfin s) fun W hW => ?_).sub ?_)).add tendsto_const_nhds)
    · exact (hLim K ι W n L A' s' ht' ((divSuppArith K ι P (n + 1) A s W hP hs hW.1).1 hW.2) hL hA'
        (hNot K ι P (n + 2) s s' W hP hsP hs'P hnc hW.1 hW.2)).const_mul _
    · have h := hLim K ι P (n + 1) (Fin.cons A L) A' s' ht' hP (forall_cons hA hL) hA' hs'P
      rwa [pot_cons] at h

  have h2 : ∀ δ : ℝ, 0 < δ →
      ptsIntegral P (Fin.cons (fun z => Real.log (A'.h z)) (pot L)) (logNorm A s) +
        ((∑ᶠ (W) (_ : W ∈ divSupp P s ∧ IsHorizontal W), (multAt (P ⊔ Ideal.span {s}) W : ℝ) *
            ptsIntegral W (pot L) (logNorm A' s')) -
          ptsIntegral P (Fin.cons (fun z => Real.log (A.h z)) (pot L)) (logNorm A' s')) +
        ptsIntegral P (Fin.cons (fun z => Real.log (T.h z)) (pot L)) (logNorm A s) ≤
      (∑ᶠ (W) (_ : W ∈ divSupp P s' ∧ IsHorizontal W), (multAt (P ⊔ Ideal.span {s'}) W : ℝ) *
          ptsIntegral W (pot L) (fun z => Real.log ((regLine A s ht δ).h z))) +
        ptsIntegral P (Fin.cons (fun z => Real.log (T.h z)) (pot L))
          (fun z => Real.log ((regLine A s ht δ).h z)) := by
    intro δ hδ
    have hD : IsSmoothHerm (regLine A s ht δ) := isSmoothHerm_regLine hA hδ
    have hlimD := hLim K ι P (n + 1) (Fin.cons (regLine A s ht δ) L) A' s' ht' hP (forall_cons hD hL) hA'
      hs'P
    rw [pot_cons, hPL1 K ι P n L A' _ s' hP hL hA' hD rfl hs'] at hlimD
    have hR : Tendsto
        (fun ε => ptsIntegral P (pot (Fin.cons ((A'.tensor (regLine A' s' ht' ε)).tensor T) L))
          (fun z => Real.log ((regLine A s ht δ).h z))) (𝓝[>] 0)
        (𝓝 (ptsIntegral P (Fin.cons (fun z => Real.log (A'.h z)) (pot L))
            (fun z => Real.log ((regLine A s ht δ).h z)) +
          ((∑ᶠ (W) (_ : W ∈ divSupp P s' ∧ IsHorizontal W), (multAt (P ⊔ Ideal.span {s'}) W : ℝ) *
              ptsIntegral W (pot L) (fun z => Real.log ((regLine A s ht δ).h z))) -
            ptsIntegral P (Fin.cons (fun z => Real.log (A'.h z)) (pot L))
              (fun z => Real.log ((regLine A s ht δ).h z))) +
          ptsIntegral P (Fin.cons (fun z => Real.log (T.h z)) (pot L))
            (fun z => Real.log ((regLine A s ht δ).h z)))) := by
      have eR : ∀ ε : ℝ, 0 < ε →
          ptsIntegral P (Fin.cons (fun z => Real.log (A'.h z)) (pot L))
              (fun z => Real.log ((regLine A s ht δ).h z)) +
            ptsIntegral P (Fin.cons (fun z => Real.log ((regLine A s ht δ).h z)) (pot L))
              (fun z => Real.log ((regLine A' s' ht' ε).h z)) +
            ptsIntegral P (Fin.cons (fun z => Real.log (T.h z)) (pot L))
              (fun z => Real.log ((regLine A s ht δ).h z)) =
          ptsIntegral P (pot (Fin.cons ((A'.tensor (regLine A' s' ht' ε)).tensor T) L))
            (fun z => Real.log ((regLine A s ht δ).h z)) := by
        intro ε hε
        have hB : IsSmoothHerm (regLine A' s' ht' ε) := isSmoothHerm_regLine hA' hε
        rw [pot_cons, ptsIntegral_add_first_log hAdd hP hL (isSmoothHerm_tensor hA' hB) hT hD rfl,
          ptsIntegral_add_first_log hAdd hP hL hA' hB hD rfl,
          hSt K ι P n L (regLine A s ht δ) (regLine A' s' ht' ε) hP hL hD hB rfl rfl]
      have ev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), _ := eventually_mem_nhdsWithin.mono fun ε hε => eR ε hε
      exact Tendsto.congr' ev ((tendsto_const_nhds.add hlimD).add tendsto_const_nhds)
    have hle := le_of_tendsto_of_tendsto h1 hR (by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact hMono K ι P (n + 1) _ A (regLine A s ht δ) s hP
        (forall_cons (isSmoothHerm_tensor (isSmoothHerm_tensor hA' (isSmoothHerm_regLine hA' hε)) hT) hL)
        (forall_cons (hC ε hε) hLp) hA hs hD rfl
        (fun z hz h0 => logNorm_le_log_regLine_h hδ.le hz.1 h0))
    linarith

  have h3 : Tendsto
      (fun δ => (∑ᶠ (W) (_ : W ∈ divSupp P s' ∧ IsHorizontal W), (multAt (P ⊔ Ideal.span {s'}) W : ℝ) *
          ptsIntegral W (pot L) (fun z => Real.log ((regLine A s ht δ).h z))) +
        ptsIntegral P (Fin.cons (fun z => Real.log (T.h z)) (pot L))
          (fun z => Real.log ((regLine A s ht δ).h z))) (𝓝[>] 0)
      (𝓝 ((∑ᶠ (W) (_ : W ∈ divSupp P s' ∧ IsHorizontal W), (multAt (P ⊔ Ideal.span {s'}) W : ℝ) *
          ptsIntegral W (pot L) (logNorm A s)) +
        ptsIntegral P (Fin.cons (fun z => Real.log (T.h z)) (pot L)) (logNorm A s))) := by
    refine (tendsto_finsum_of_finite (hfin s') fun W hW => ?_).add ?_
    · exact (hLim K ι W n L A s ht ((divSuppArith K ι P (n + 1) A' s' W hP hs' hW.1).1 hW.2) hL hA
        (hNot K ι P (n + 2) s' s W hP hs'P hsP (fun W h h' => hnc W h' h) hW.1 hW.2)).const_mul _
    · have h := hLim K ι P (n + 1) (Fin.cons T L) A s ht hP (forall_cons hT hL) hA hsP
      rwa [pot_cons] at h
  have h4 := ge_of_tendsto h3 (by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact h2 δ hδ)
  unfold De
  linarith

end GroundTheory.Heights₂.Heights.Inter
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem ArithmeticIntersectionDivisorPushforward.proof (hDeh : regularityDehomogenization_holds.Statement) (hLoc : LocRingDimOne.Statement)
    (hFin : SemilocFinite.Statement) (hRank : SemilocRank.Statement) (hLen : SemilocLength.Statement) :
    ArithmeticIntersectionDivisorPushforward.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n G J s α W E hv hP' hP hJ hs hsP hW hE
  have : P'.IsPrime := hP'.2.1.1
  have : (imageZ v P').IsPrime := hP.2.1.1

  obtain ⟨t, ht, htW⟩ := exists_form_notMem hW.2 hW.1.1.1 α
  have ht0 : algebraMap (MRing ι ⧸ imageZ v P') (FractionRing (MRing ι ⧸ imageZ v P'))
      (Ideal.Quotient.mk _ t) ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
    exact fun h => htW (hW.1.1.2 (Ideal.mem_sup_left h))
  set y : FractionRing (MRing ι ⧸ imageZ v P') := algebraMap _ _ (Ideal.Quotient.mk (imageZ v P') s) /
    algebraMap _ _ (Ideal.Quotient.mk (imageZ v P') t) with hy
  have hyt : y * algebraMap _ _ (Ideal.Quotient.mk (imageZ v P') t) =
      algebraMap _ _ (Ideal.Quotient.mk (imageZ v P') s) := div_mul_cancel₀ _ ht0
  obtain ⟨hyA, hm⟩ := hDeh K ι (imageZ v P') s t α W y hP.2.1 hs hsP hW ht htW hyt
  obtain ⟨hNoeth, hLocal, hDim⟩ := hLoc K ι (imageZ v P') s α W hP.2.1 hs hsP hW
  let _ : Algebra (locRing (imageZ v P') W) (semiLocRing P' (fibreOver v P' W)) := (locToSemiloc hv P' W).toAlgebra
  obtain ⟨hBf, hBt⟩ := hFin K ι K' ι' κ v P' n s α W hv hP' hP hs hsP hW
  have hrk := hRank K ι K' ι' κ v P' n G J s α W hv hP' hP hJ hs hsP hW
  obtain ⟨N, hlen, hN⟩ := hLen K ι K' ι' κ v P' n s t α W E hv hP' ⟨y, hyA⟩ hP hs ht hsP hW htW hyt hE
  have hy0 : (⟨y, hyA⟩ : locRing (imageZ v P') W) ≠ 0 := fun h => by
    have h' : y = 0 := congrArg Subtype.val h
    rw [hy, div_eq_zero_iff, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at h'
    exact h'.elim hsP ht0

  have := ReciprocityTheory.ChartRestriction.G.AI.krullDimLE_one_of_krullDim_eq hDim
  have key := ReciprocityTheory.ChartRestriction.G.AI.dimOneTorsionFreeFormula _ (semiLocRing P' (fibreOver v P' W)) ⟨y, hyA⟩ hDim hy0
  have hord : Ring.ord (locRing (imageZ v P') W) ⟨y, hyA⟩ =
      (multAt (imageZ v P' ⊔ Ideal.span {s}) W : ℕ∞) := by
    have hfin := Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hy0)
    rw [hm, locIdeal_eq_span hyA]
    exact (ENat.natCast_toNat hfin).symm
  rw [hlen, hord] at key
  have hNat : N = Module.finrank (locRing (imageZ v P') W) (semiLocRing P' (fibreOver v P' W)) *
      multAt (imageZ v P' ⊔ Ideal.span {s}) W := by
    exact_mod_cast key
  rw [← hN, hNat, ← hrk]
  push_cast
  rfl

end GroundTheory.Heights₂.Heights.Inter
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

section SlopeTestRemainingChoices

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

theorem isSmoothHerm_of_isPullHerm' {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {A : HermLine ι} {A' : HermLine ι'} (hA : IsSmoothHerm A) (h : IsPullHerm κ v A A') :
    IsSmoothHerm A' := by
  have e : A'.h = A.h ∘ fun z' p => z' (v p) := funext h.2
  unfold IsSmoothHerm
  rw [e]
  refine hA.comp (contDiff_pi.2 fun p => contDiff_apply ℝ (fun _ => ℂ) (v p)).contDiffOn ?_
  intro z' hz'
  simp only [Set.mem_ofPred_eq] at hz' ⊢
  intro k
  obtain ⟨i', hi'⟩ := hz' (κ k)
  obtain ⟨p, hp⟩ := hv.2.2.2 ⟨κ k, i'⟩ ⟨k, rfl⟩
  have h2 : p.1 = k := hv.1 (by rw [← hv.2.2.1 p, hp])
  obtain ⟨pk, pi⟩ := p
  simp only at h2
  subst h2
  exact ⟨pi, by rw [hp]; exact hi'⟩

theorem arithDim_lt_of_lt {P Q : Ideal (MRing ι)} {d d₀ : ℕ} (hP : IsArithVar P d) (hQ : IsArithVar Q d₀)
    (hle : P ≤ Q) (hne : P ≠ Q) : d₀ < d := by
  obtain ⟨f, hfQ, hfP⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hle hne)
  have := hP.2.1.1
  have hf0 : Ideal.Quotient.mk P f ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hf0)
  have h2 : ringKrullDim (MRing ι ⧸ Q) ≤
      ringKrullDim ((MRing ι ⧸ P) ⧸ Ideal.span {Ideal.Quotient.mk P f}) := by
    refine ringKrullDim_le_of_surjective (Ideal.Quotient.lift _ (Ideal.Quotient.factor hle) ?_) ?_
    · intro x hx
      obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hx
      rw [map_mul, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem.mpr hfQ, mul_zero]
    · intro z
      obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
      exact ⟨Ideal.Quotient.mk _ (Ideal.Quotient.mk P z), rfl⟩
  rw [hP.2.2.2] at h1
  rw [hQ.2.2.2] at h2
  have h3 : ((d₀ + Fintype.card K : ℕ) : WithBot ℕ∞) + 1 ≤ ((d + Fintype.card K : ℕ) : WithBot ℕ∞) :=
    le_trans (by gcongr) h1
  have h4 : ((d₀ + Fintype.card K + 1 : ℕ) : WithBot ℕ∞) ≤ ((d + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    exact_mod_cast h3
  have h5 : d₀ + Fintype.card K + 1 ≤ d + Fintype.card K := by exact_mod_cast h4
  omega

end SlopeTestRemainingChoices

theorem PFStep.proof (hSec : PFSecRed.Statement) (hVert : PFVert.Statement) (hInt : PFIntZero.Statement)
    (hHor : PFHoriz.Statement) (hSum : PFFibreSum.Statement) (hIm : ImageArithStatement) (hCM : ContractMixedStatement) : PFStep.Statement := by
  intro I hI r hr
  refine hSec I hI r ?_
  intro K _ ι _ K' _ ι' _ κ v P' d G J L L' N s a hv hP' hP hJ hL hL' hN ha hs hsP
  have hP1 : IsArithVar P' (d + r + 1) := hP'
  have hsec : IsSectionOn P' (N (Fin.last r)) s := ⟨a, ha, hs, hsP⟩
  have hM : ∀ j, IsSmoothHerm (Fin.append L' (Fin.init N) j) := by
    intro j
    induction j using Fin.addCases with
    | left i => rw [Fin.append_left]; exact isSmoothHerm_of_isPullHerm' hv (hL i) (hL' i)
    | right i => rw [Fin.append_right]; exact hN _
  have hR := (hI K' ι').2.2 P' (d + r) (Fin.append L' (Fin.init N)) (N (Fin.last r)) s a hP1 hM (hN _) ha hs hsP
  rw [← Fin.append_snoc, Fin.snoc_init_self] at hR
  refine hR.trans ?_
  rw [recR_eq, hInt K ι K' ι' κ v P' d r L L' (Fin.init N) (N (Fin.last r)) s hv hP1 hP hL hL', sub_zero, cycR,
    ← hSum K ι K' ι' κ v P' d r G J N s a hv hP1 hP hJ ha hs hsP, finsum_mem_mul]
  refine finsum_mem_congr rfl fun W hW => ?_
  by_cases hh : IsHorizontal W
  · have hWa : IsArithVar W (d + r) := (divSuppArith K' ι' P' (d + r) (N (Fin.last r)) s W hP1 hsec hW).1 hh
    by_cases hd : imageZ v W = imageZ v P'
    · rw [if_pos hh, if_pos ⟨hh, hd⟩,
        hHor I r hr K ι K' ι' κ v P' W d G J L L' (Fin.init N) hv hWa hd hP hJ hL hL' (fun j => hN _)]
      exact (mul_assoc _ _ _).symm
    · rw [if_pos hh, if_neg (fun h => hd h.2), mul_zero, zero_mul]
      obtain ⟨d₀, -, hd₀⟩ := hIm K ι K' ι' κ v W (d + r) hP.1 hv hWa
      have hle : imageZ v P' ≤ imageZ v W := Ideal.comap_mono (le_sup_left.trans hW.1.1.2)
      rw [hCM I hI K ι K' ι' κ v W d₀ d r L L' (Fin.init N) hv hWa hd₀
        (arithDim_lt_of_lt hP hd₀ hle (Ne.symm hd)) hL hL' (fun j => hN _), mul_zero]
  · rw [if_neg hh, if_neg (fun h => hh h.1),
      hVert K ι K' ι' κ v P' d r L L' (Fin.init N) s a W hv hP1 hP hL' hs hsP hW hh]
    simp

end

end GroundTheory.Heights₂.Heights.Inter
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

def SemilocResidueDeg.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ) (s : MRing ι) (α : K → ℕ)
    (W : Ideal (MRing ι)) (hv : IsBlockMap κ v) (hP' : IsArithVar P' (n + 1)),
    IsArithVar (imageZ v P') (n + 1) → IsMultiHomog s α → s ∉ imageZ v P' → W ∈ divSupp (imageZ v P') s →
    ∀ (W' : Ideal (MRing ι')) (hW' : W' ∈ fibreOver v P' W) [IsLocalRing (locRing P' W')]
      (G' : GenFibre v W') (J' : IFamily G'.Φ (fibreIdx ι' κ)), IsFieldIntersection J' →
    haveI := hP'.2.1.1
    letI := (locToSemiloc hv P' W).toAlgebra
    ∃ d : ℕ, Module.length (locRing (imageZ v P') W)
        (semiLocRing P' (fibreOver v P' W) ⧸ semiMaxIdeal P' (fibreOver v P' W) W' hW') = d ∧
      (d : ℤ) = J' (fibreIdeal κ G') 0 Fin.elim0

end GroundTheory.Heights₂.Heights.Inter
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

theorem SemilocChartRatio.proof (hF : FibreOverFinite.Statement) : SemilocChartRatio.Statement := by
  classical
  intro K _ ι _ K' _ ι' _ κ v P' n s α W i' hv hP' hZ hs hsn hW hi' q
  have hSf : (insert P' (fibreOver v P' W)).Finite :=
    (hF K ι K' ι' κ v P' n s α W hv hP' hZ hs hsn hW).insert P'
  have hSp : ∀ V ∈ insert P' (fibreOver v P' W), IsMultiProjPrime V := by
    rintro V (rfl | hV)
    · exact hP'.2.1
    · exact hV.1
  obtain ⟨d₀, hd₀⟩ := AvoidRing.exists_form_avoid _ hSf hSp
  obtain ⟨w, hwd, hwS⟩ := hd₀ (Pi.single q.1 1 + d₀) le_add_self
  have hPp : P'.IsPrime := hP'.2.1.1
  have hwP' : w ∉ P' := hwS P' (Set.mem_insert _ _)
  have hwnz : Ideal.Quotient.mk P' w ∈ nonZeroDivisors (MRing ι' ⧸ P') :=
    mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  set N : MRing ι' := ∏ k, (X ⟨k, i' k⟩ : MRing ι') ^ d₀ k with hN
  have hNd : IsMultiHomog N d₀ := AvoidRing.isMultiHomog_coordProd i' d₀
  have hNP : N ∉ P' := AvoidRing.coordProd_not_mem hPp i' hi' d₀
  have hwW : ∀ W' ∈ fibreOver v P' W, w ∉ W' := fun W' hW' => hwS W' (Set.mem_insert_of_mem _ hW')
  have gen : ∀ u : MRing ι', IsMultiHomog u (Pi.single q.1 1 + d₀) →
      IsLocalization.mk' (FractionRing (MRing ι' ⧸ P')) (Ideal.Quotient.mk P' u) ⟨_, hwnz⟩ ∈
        semiLocRing P' (fibreOver v P' W) := fun u hu =>
    Subring.subset_closure ⟨u, w, _, hwnz, hwW, hu, hwd, rfl⟩
  have hq : IsMultiHomog (X q * N) (Pi.single q.1 1 + d₀) :=
    AvoidRing.isMultiHomog_mul (AvoidRing.isMultiHomog_X q.1 q.2) hNd
  have hc : IsMultiHomog (X ⟨q.1, i' q.1⟩ * N) (Pi.single q.1 1 + d₀) :=
    AvoidRing.isMultiHomog_mul (AvoidRing.isMultiHomog_X q.1 (i' q.1)) hNd
  refine ⟨⟨_, gen _ hq⟩, ⟨_, gen _ hc⟩, ?_, ?_⟩
  · show IsLocalization.mk' _ _ _ ≠ (0 : FractionRing (MRing ι' ⧸ P'))
    rw [Ne, IsFractionRing.mk'_eq_zero_iff_eq_zero, Ideal.Quotient.eq_zero_iff_mem]
    intro h
    rcases hPp.mem_or_mem h with h | h
    · exact hi' q.1 h
    · exact hNP h
  · show IsLocalization.mk' _ _ _ * _ = IsLocalization.mk' _ _ _ * _
    rw [mul_comm, IsLocalization.mul_mk'_eq_mk'_of_mul, mul_comm (IsLocalization.mk' _ _ _),
      IsLocalization.mul_mk'_eq_mk'_of_mul]
    congr 1
    simp only [map_mul]
    ring

end GroundTheory.Heights₂.Heights.Inter
end
end
