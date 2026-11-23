module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle010
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle040
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle015
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle014
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PHolomorphicFibreInfinite
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle035
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle023
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalModelOpenMapping
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle100
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle052
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle094
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Noetherian.Nilpotent
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.CycDim
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle003
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsAlg
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsPiola

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u

theorem isNilpotent_of_minimalPrimes_eq_singleton {B : Type*} [CommRing B] [IsNoetherianRing B] {P : Ideal B}
    (hmin : minimalPrimes B = {P}) : IsNilpotent P := by
  have h : sInf (minimalPrimes B) = nilradical B := Ideal.sInf_minimalPrimes
  rw [hmin, sInf_singleton] at h
  rw [h]
  exact IsNoetherianRing.isNilpotent_nilradical B

theorem length_localizedModule_self {B : Type*} [CommRing B] (P : Ideal B) [P.IsPrime] :
    Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl B) =
      Module.length (Localization.AtPrime P) (Localization.AtPrime P) :=
  ((IsLocalizedModule.iso P.primeCompl (Algebra.linearMap B (Localization.AtPrime P))).extendScalarsOfIsLocalization
    P.primeCompl (Localization.AtPrime P)).length_eq

theorem LengthLocalizedQuotient.proof (hCut : LengthCutLocalizedModule.Statement.{u, u}) :
    LengthLocalizedQuotient.Statement.{u} := by
  intro B _ _ P _ y hmin hnzd hy Q _ hQ
  have h1 := hCut B P y (Q.comap (Ideal.Quotient.mk (Ideal.span {y}))) B
    (isNilpotent_of_minimalPrimes_eq_singleton hmin) hy hQ (fun s hs m h => by
      rw [smul_eq_mul] at h
      exact (mem_nonZeroDivisors_iff.1 (hnzd s hs)).1 m h)
  have h2 := NumbersDVR.LocalizedQuotLength.proof B (Ideal.span {y}) Q 0
  have hE : (Ideal.span {y} • ⊤ : Submodule B B) = Ideal.span {y} ⊔ Ideal.span {(0 : B)} := by
    rw [Ideal.span_singleton_eq_bot.2 rfl, sup_bot_eq, smul_eq_mul, Ideal.mul_top]
  rw [hE, h2, length_localizedModule_self] at h1
  rw [← h1]
  have hb : Ideal.span {algebraMap (B ⧸ Ideal.span {y}) (Localization.AtPrime Q) (Ideal.Quotient.mk _ 0)} = ⊥ := by
    rw [map_zero, map_zero, Ideal.span_singleton_eq_bot]
  exact ((Submodule.quotEquivOfEqBot _ hb).length_eq).symm

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

theorem IrreducibleGermRegularDimGe.proof (hS : FiniteProjectionSheetsDense.Statement) :
    IrreducibleGermRegularDimGe.Statement := by
  intro σ _ X w d A hX hirr hiso hnd
  obtain ⟨N, hN, hsub⟩ := hS σ X w d A hX hirr hiso hnd
  refine ⟨N, hN, ?_⟩
  intro x hx e A' O V g hO hV hxV hg hleft hXV
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨y, hyV, hyX, O₁, V₁, g₁, hO₁, hV₁, hyV₁, hg₁, hleft₁, hXV₁⟩ :=
    mem_closure_iff.1 (hsub hx) V hV hxV
  have hy : y ∈ g₁ '' O₁ := hXV₁ ▸ ⟨hyX, hyV₁⟩
  obtain ⟨t₀, ht₀, rfl⟩ := hy
  set U : Set (Fin d → ℂ) := O₁ ∩ g₁ ⁻¹' V with hUdef
  have hU : IsOpen U := hg₁.continuousOn.isOpen_inter_preimage hO₁ hV
  have hUne : U.Nonempty := ⟨t₀, ht₀, hyV⟩
  have hdiff : DifferentiableOn ℂ (fun t => A' (g₁ t)) U :=
    A'.differentiable.comp_differentiableOn (hg₁.differentiableOn.mono Set.inter_subset_left)

  have hmem : ∀ t ∈ U, ∃ u ∈ O, g₁ t = g u := by
    intro t ht
    have h1 : g₁ t ∈ X ∩ V₁ := hXV₁ ▸ Set.mem_image_of_mem g₁ ht.1
    have h2 : g₁ t ∈ X ∩ V := ⟨h1.1, ht.2⟩
    rw [hXV] at h2
    obtain ⟨u, hu, hgu⟩ := h2
    exact ⟨u, hu, hgu.symm⟩
  obtain ⟨z, hz⟩ := HolomorphicFibreInfinite.proof d e U (fun t => A' (g₁ t)) hlt hU hUne hdiff
  apply hz
  refine Set.Subsingleton.finite ?_
  intro t₁ ht₁ t₂ ht₂
  obtain ⟨u₁, hu₁, hg1⟩ := hmem t₁ ht₁.1
  obtain ⟨u₂, hu₂, hg2⟩ := hmem t₂ ht₂.1
  have hz1 : A' (g₁ t₁) = z := ht₁.2
  have hz2 : A' (g₁ t₂) = z := ht₂.2
  rw [hg1, hleft u₁ hu₁] at hz1
  rw [hg2, hleft u₂ hu₂] at hz2
  have hgg : g₁ t₁ = g₁ t₂ := by rw [hg1, hg2, hz1, hz2]
  rw [← hleft₁ t₁ ht₁.1.1, ← hleft₁ t₂ ht₂.1.1, hgg]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem ringKrullDim_quotient_minimalPrime_add_one_of_fintype {σ : Type} [Fintype σ]
    {V W : Ideal (MvPolynomial σ ℂ)} [hVp : V.IsPrime]
    {f : MvPolynomial σ ℂ} (hf : f ∉ V) (hW : W ∈ (V ⊔ Ideal.span {f}).minimalPrimes)
    (hfin : ringKrullDim (MvPolynomial σ ℂ ⧸ V) ≠ ⊤) :
    ringKrullDim (MvPolynomial σ ℂ ⧸ W) + 1 = ringKrullDim (MvPolynomial σ ℂ ⧸ V) := by
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
  have : IsDomain (MvPolynomial σ ℂ ⧸ V) := Ideal.Quotient.isDomain V
  have : Algebra.FiniteType ℂ (MvPolynomial σ ℂ ⧸ V) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ V) (Ideal.Quotient.mkₐ_surjective ℂ V)
  have : IsNoetherianRing (MvPolynomial σ ℂ ⧸ V) := Algebra.FiniteType.isNoetherianRing ℂ _
  have : FiniteRingKrullDim (MvPolynomial σ ℂ ⧸ V) :=
    finiteRingKrullDim_iff_ne_bot_and_top.mpr ⟨fun h ↦ by
      have h0 := ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial σ ℂ ⧸ V)
      rw [h] at h0
      exact absurd h0 (by simp), hfin⟩
  obtain ⟨s, hs⟩ := ReciprocityTheory.ChartRestriction.G.Geo.DimF.exists_height_of_isMaximal_of_field ℂ (MvPolynomial σ ℂ ⧸ V)
  have key := ReciprocityTheory.ChartRestriction.G.Geo.DimF.dim_quot_add_height (A := MvPolynomial σ ℂ ⧸ V)
    (fun M N hM hN ↦ (hs M hM).trans (hs N hN).symm) (W.map (Ideal.Quotient.mk V))
  rw [hh, ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hPW)] at key
  exact_mod_cast key

theorem NormalModelGoodPointGeneric.proof (h₁ : NormalCodimOneCompleteIntersection.Statement)
    (h₂ : NormalCodimOneUniformiser.Statement) (h₃ : JacobianRankOffHypersurface.Statement)
    (h₄ : ProjectionUnramifiedGeneric.Statement) : NormalModelGoodPointGeneric.Statement := by
  classical
  intro n d J u M hJ hdim hu
  have hP : M.ideal.IsPrime := M.isPrime
  set ut : MvPolynomial (Fin n ⊕ Fin M.m) ℂ := rename Sum.inl (linForm u) with hut
  have hutP : ut ∉ M.ideal := by
    intro h
    apply hu
    rw [← M.comap_eq]
    exact h
  have hdimP : ringKrullDim (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) = (d + 1 : ℕ) := by
    rw [M.ringKrullDim_eq, hdim]
  have hev : ∀ x : Fin n ⊕ Fin M.m → ℂ, eval x ut = linEval u (IndefiniteRowSideFullHecke.ComplexSets.firstCoords x) := fun x ↦ by

    simp [hut, linForm, linEval, IndefiniteRowSideFullHecke.ComplexSets.firstCoords, map_sum]
  set L : Ideal (MvPolynomial (Fin n ⊕ Fin M.m) ℂ) := M.ideal ⊔ Ideal.span {ut} with hL
  have hfinM : L.minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ L
  set T := hfinM.toFinset with hT
  have hmemT : ∀ W, W ∈ T ↔ W ∈ L.minimalPrimes := fun W ↦ hfinM.mem_toFinset

  have hdimW : ∀ W ∈ L.minimalPrimes, ringKrullDim (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ W) = (d : ℕ) := by
    intro W hW
    have key := ringKrullDim_quotient_minimalPrime_add_one_of_fintype hutP hW (fun h ↦ by
      rw [hdimP] at h
      exact ENat.natCast_ne_top _ (WithBot.coe_injective h))
    rw [hdimP] at key
    exact ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_withBot_eq_of_add_one key

  have hgood : ∀ W ∈ L.minimalPrimes, ∃ β : MvPolynomial (Fin n ⊕ Fin M.m) ℂ, β ∉ W ∧
      ∀ w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn W, eval w β ≠ 0 → NormalModelDivisorGoodPoint M u d w := by
    intro W hW
    have hWp : W.IsPrime := hW.1.1
    have hPW : M.ideal ≤ W := le_sup_left.trans hW.1.2
    have hutW : ut ∈ W := hW.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    have hnm : ∀ x y, x ∉ W → y ∉ W → x * y ∉ W := fun x y hx hy hm ↦ (hWp.mem_or_mem hm).elim hx hy
    obtain ⟨c, f, h, hc, hfP, hhW, hgen⟩ :=
      h₁ _ M.ideal W d hP hWp hPW M.isIntegrallyClosed hdimP (hdimW W hW)
    obtain ⟨g, a, b, t, k, hgW, hk, haW, hbW, htW, hrel, hgenW⟩ :=
      h₂ _ M.ideal W d ut hP hWp hPW M.isIntegrallyClosed hdimP (hdimW W hW) hutW hutP
    set q : Fin (c + 1) → MvPolynomial (Fin n ⊕ Fin M.m) ℂ := Fin.cons g f with hq
    have hqW : ∀ j, q j ∈ W := fun j ↦ Fin.cases (by simpa [hq] using hgW)
      (fun j ↦ by simpa [hq] using hPW (hfP j)) j
    have hspan : Ideal.span (Set.range f) ≤ Ideal.span (Set.range q) :=
      Ideal.span_mono (Set.range_subset_iff.2 fun j ↦ ⟨j.succ, by simp [hq]⟩)
    have hgq : g ∈ Ideal.span (Set.range q) := Ideal.subset_span ⟨0, by simp [hq]⟩
    have hgenq : ∀ p ∈ W, ∃ i : ℕ, (h * t) ^ i * p ∈ Ideal.span (Set.range q) := by
      intro p hp
      obtain ⟨i₁, hi₁⟩ := hgenW p hp
      obtain ⟨r, hr, s, hs, hrs⟩ := Submodule.mem_sup.1 hi₁
      obtain ⟨i₂, hi₂⟩ := hgen r hr
      refine ⟨i₁ + i₂, ?_⟩
      have e : (h * t) ^ (i₁ + i₂) * p = h ^ i₁ * t ^ i₂ * (h ^ i₂ * r) + h ^ (i₁ + i₂) * t ^ i₂ * s := by
        linear_combination (-(h ^ (i₁ + i₂) * t ^ i₂)) * hrs
      rw [e]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (hspan hi₂))
        (Ideal.mul_mem_left _ _ ((Ideal.span_singleton_le_iff_mem _).2 hgq hs))
    have hint : ∀ i : Fin M.m, ∃ F : Polynomial (MvPolynomial (Fin n) ℂ), F.Monic ∧
        F.eval₂ (rename Sum.inl : MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n ⊕ Fin M.m) ℂ).toRingHom
          (X (Sum.inr i)) ∈ W := fun i ↦ by
      obtain ⟨F, hF, hmem⟩ := M.integral i
      exact ⟨F, hF, hPW hmem⟩
    obtain ⟨μ₁, hμ₁W, hμ₁⟩ := h₃ _ W d (c + 1) q (h * t) hWp (hdimW W hW) hqW (hnm _ _ hhW htW) hgenq
    obtain ⟨μ₂, hμ₂W, hμ₂⟩ := h₄ (Fin n) (Fin M.m) W (c + 1) q (h * t) hWp hint hqW (hnm _ _ hhW htW) hgenq
    refine ⟨h * t * a * b * μ₁ * μ₂,
      hnm _ _ (hnm _ _ (hnm _ _ (hnm _ _ (hnm _ _ hhW htW) haW) hbW) hμ₁W) hμ₂W, fun w hw hβ ↦ ?_⟩
    have hwP : w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal := fun p hp ↦ hw p (hPW hp)
    simp only [map_mul, ne_eq, mul_eq_zero, not_or] at hβ
    obtain ⟨⟨⟨⟨⟨hwh, hwt⟩, hwa⟩, hwb⟩, hwμ₁⟩, hwμ₂⟩ := hβ
    have hc' : c + (d + 1) = n + M.m := by simpa using hc
    have hfam : (Fin.cons (fun s ↦ eval w (pderiv s g)) (fun j s ↦ eval w (pderiv s (f j))) :
        Fin (c + 1) → Fin n ⊕ Fin M.m → ℂ) = fun j s ↦ eval w (pderiv s (q j)) := by
      funext j s
      refine Fin.cases ?_ (fun j ↦ ?_) j <;> simp [hq]
    refine ⟨hwP, c, f, h, g, a, b, k, hc', hfP, hwh, hgen, hw g hgW, ?_, hk, hwa, hwb, hrel, ?_⟩
    · rw [hfam, linearIndependent_iff_card_eq_finrank_span]
      have := hμ₁ w hw hwμ₁
      simp only [Fintype.card_sum, Fintype.card_fin] at this ⊢
      show c + 1 = Module.finrank ℂ (Submodule.span ℂ (Set.range fun j s ↦ eval w (pderiv s (q j))))
      omega
    · intro v hv hgv hfv
      refine hμ₂ w hw hwμ₂ v hv fun j ↦ Fin.cases ?_ (fun j ↦ ?_) j
      · simpa [hq] using hgv
      · simpa [hq] using hfv j
  choose! β hβW hβ using hgood

  have hcomp : ∀ x ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal, linEval u (IndefiniteRowSideFullHecke.ComplexSets.firstCoords x) = 0 →
      ∃ W ∈ L.minimalPrimes, x ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn W := by
    intro x hxJ hxu
    have hxL : L ≤ RingHom.ker (eval x) := sup_le (fun p hp ↦ RingHom.mem_ker.mpr (hxJ p hp))
      (Ideal.span_le.mpr (by simpa [hev] using hxu))
    have : (RingHom.ker (eval x)).IsPrime := RingHom.ker_isPrime _
    obtain ⟨W, hW, hWx⟩ := Ideal.exists_minimalPrimes_le hxL
    exact ⟨W, hW, fun p hp ↦ RingHom.mem_ker.mp (hWx hp)⟩

  have hsep : ∀ W ∈ L.minimalPrimes, ∀ V ∈ L.minimalPrimes, W ≠ V → ∃ g ∈ V, g ∉ W := by
    intro W hW V hV hne
    by_contra hcon
    push Not at hcon
    exact hne (le_antisymm (hW.2 hV.1 hcon) hcon)
  choose! gg hggV hggW using hsep
  set e : Ideal (MvPolynomial (Fin n ⊕ Fin M.m) ℂ) → MvPolynomial (Fin n ⊕ Fin M.m) ℂ :=
    fun W ↦ ∏ V ∈ T.erase W, gg W V with he
  have heW : ∀ W ∈ L.minimalPrimes, e W ∉ W := by
    intro W hW hmem
    have : W.IsPrime := hW.1.1
    obtain ⟨V, hV, hgV⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    exact hggW W hW V ((hmemT V).mp (Finset.mem_of_mem_erase hV)) (Finset.ne_of_mem_erase hV).symm hgV
  have heV : ∀ W ∈ L.minimalPrimes, ∀ V ∈ L.minimalPrimes, W ≠ V → e W ∈ V := by
    intro W hW V hV hne
    have : V.IsPrime := hV.1.1
    exact Ideal.IsPrime.prod_mem_iff.mpr
      ⟨V, Finset.mem_erase.mpr ⟨hne.symm, (hmemT V).mpr hV⟩, hggV W hW V hV hne⟩
  set F : MvPolynomial (Fin n ⊕ Fin M.m) ℂ := ∑ W ∈ T, β W * e W with hF
  have hsplit : ∀ W ∈ T, F = β W * e W + ∑ V ∈ T.erase W, β V * e V := fun W hW ↦
    (Finset.add_sum_erase T _ hW).symm
  have hrest : ∀ W ∈ L.minimalPrimes, ∑ V ∈ T.erase W, β V * e V ∈ W := by
    intro W hW
    refine Ideal.sum_mem _ fun V hV ↦ Ideal.mul_mem_left _ _ ?_
    exact heV V ((hmemT V).mp (Finset.mem_of_mem_erase hV)) W hW (Finset.ne_of_mem_erase hV)
  have hFW : ∀ W ∈ L.minimalPrimes, F ∉ W := by
    intro W hW hmem
    rw [hsplit W ((hmemT W).mpr hW), Ideal.add_mem_iff_left _ (hrest W hW)] at hmem
    rcases hW.1.1.mem_or_mem hmem with h | h
    · exact hβW W hW h
    · exact heW W hW h
  refine ⟨L ⊔ Ideal.span {F}, le_sup_left, ringKrullDim_quotient_sup_span_lt hFW hdimW, ?_⟩
  intro w hwJ hwu hwB
  obtain ⟨W, hW, hwW⟩ := hcomp w hwJ hwu
  have hFw : eval w F ≠ 0 := by
    intro h0
    refine hwB fun p hp ↦ ?_
    have hle : L ⊔ Ideal.span {F} ≤ RingHom.ker (eval w) := by
      refine sup_le (fun p hp ↦ RingHom.mem_ker.mpr (hwW p (hW.1.2 hp))) (Ideal.span_le.mpr (by simpa using h0))
    exact RingHom.mem_ker.mp (hle hp)
  rw [hsplit W ((hmemT W).mpr hW), map_add (f := _), hwW _ (hrest W hW), add_zero, map_mul] at hFw
  exact hβ W hW w hwW (left_ne_zero_of_mul hFw)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Filter Topology

noncomputable section

namespace MaDensChain

variable {D : ℕ}

theorem fderiv_comp_real (h : ℝ → ℝ) (g : (Fin D → ℂ) → ℝ) (y : Fin D → ℂ)
    (hh : DifferentiableAt ℝ h (g y)) (hg : DifferentiableAt ℝ g y) :
    fderiv ℝ (h ∘ g) y = deriv h (g y) • fderiv ℝ g y :=
  (hh.hasDerivAt.comp_hasFDerivAt y hg.hasFDerivAt).fderiv

theorem dz_cplx_comp (j : Fin D) (h : ℝ → ℝ) (g : (Fin D → ℂ) → ℝ) (y : Fin D → ℂ)
    (hh : DifferentiableAt ℝ h (g y)) (hg : DifferentiableAt ℝ g y) :
    dz j (cplx (h ∘ g)) y = ((deriv h (g y) : ℝ) : ℂ) * dz j (cplx g) y := by
  rw [dz_cplx, dz_cplx, fderiv_comp_real h g y hh hg]
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

theorem dzb_cplx_comp (k : Fin D) (h : ℝ → ℝ) (g : (Fin D → ℂ) → ℝ) (y : Fin D → ℂ)
    (hh : DifferentiableAt ℝ h (g y)) (hg : DifferentiableAt ℝ g y) :
    dzb k (cplx (h ∘ g)) y = ((deriv h (g y) : ℝ) : ℂ) * dzb k (cplx g) y := by
  rw [dzb_cplx, dzb_cplx, fderiv_comp_real h g y hh hg]
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

theorem hessC_comp_real (F : ℝ → ℝ) (g : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (hF : ContDiff ℝ 2 F)
    (hg : ContDiffAt ℝ 2 g z) :
    hessC (F ∘ g) z = ((deriv F (g z) : ℝ) : ℂ) • hessC g z + ((deriv (deriv F) (g z) : ℝ) : ℂ) • gradMat g g z := by
  obtain ⟨U, hU, hzU, hgU, -⟩ := MaDensLeibniz.exists_open_contDiffOn g g z hg hg
  have hF1 : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hF' : Differentiable ℝ (deriv F) :=
    (hF.deriv' (n := 1)).differentiable (by norm_num)
  ext j k
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [hessCDz_thm D _ U hU (hF.comp_contDiffOn hgU) z hzU j k, hessCDz_thm D g U hU hgU z hzU j k]
  have hev : dzb k (cplx (F ∘ g)) =ᶠ[𝓝 z] fun y => cplx (deriv F ∘ g) y * dzb k (cplx g) y := by
    filter_upwards [hU.mem_nhds hzU] with y hy
    exact dzb_cplx_comp k F g y (hF1 _)
      ((hgU.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num))
  have hgd : DifferentiableAt ℝ g z := hg.differentiableAt (by norm_num)
  have hA : DifferentiableAt ℝ (cplx (deriv F ∘ g)) z := by
    have h : cplx (deriv F ∘ g) = fun y => Complex.ofRealCLM ((deriv F ∘ g) y) := by
      funext y; simp [cplx]
    rw [h]
    exact Complex.ofRealCLM.differentiableAt.comp z ((hF' _).comp z hgd)
  have hB := differentiableAt_dzb (j := k) (MaDensLeibniz.contDiffAt_cplx hg)
  rw [dz_congr hev, dz_mul hA hB, dz_cplx_comp j (deriv F) g z (hF' _) hgd]
  simp only [gradMat, cplx, Function.comp_apply]
  ring

theorem gradMat_comp (F : ℝ → ℝ) (g : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ)
    (hF : DifferentiableAt ℝ F (g z)) (hg : DifferentiableAt ℝ g z) :
    gradMat (F ∘ g) (F ∘ g) z = ((deriv F (g z) ^ 2 : ℝ) : ℂ) • gradMat g g z := by
  ext j k
  simp only [gradMat, Matrix.smul_apply, smul_eq_mul]
  rw [dz_cplx_comp j F g z hF hg, dzb_cplx_comp k F g z hF hg]
  push_cast
  ring

theorem proof : MaDensChain.Statement := by
  intro D φ F g z hF hg
  have hF1 : DifferentiableAt ℝ F (g z) := (hF.differentiable (by norm_num)) _
  constructor
  · rw [maDens_cons_eq, maDens_cons_eq, hessC_comp_real F g z hF hg]
    unfold gradDens
    rw [mdisc_cons_smul_add]
    simp only [Complex.add_re, Complex.re_ofReal_mul]
    ring
  · unfold gradDens
    rw [gradMat_comp F g z hF1 (hg.differentiableAt (by norm_num)), mdisc_cons_smul_fst]
    simp only [Complex.re_ofReal_mul]
    ring

end MaDensChain

end

end GroundTheory.Heights₂.Heights
end
