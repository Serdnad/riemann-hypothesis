module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1708
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle050
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.Bundle005
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bridge
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CARUnit
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CsqDdPt
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.LayerLeGeneratedTensorFock
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.TraceEqTraceRestrictOfRangeLe
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.MemTensorFockOfCoeffs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle481

@[expose] public section

section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

theorem _root_.GlobalTheory.T.hilbertSamuelSectionBaseChange_properties : ∀ (F : Type) [Field F] [NumberField F] (X : Data F) (Λ₀ : ℝ) (E : Type) [Field E] [NumberField E] [Algebra F E], (∀ (m : ℕ) (v : Fin m → (sysOf X Λ₀).V X.T), LinearIndependent F v → LinearIndependent E fun i => totExt X.toGeo E (v i)) ∧ (∀ u x, shift (X.toGeo.baseChange E) (fun k => algebraMap F E (u k)) (totExt X.toGeo E x) = totExt X.toGeo E (shift X.toGeo u x)) ∧ ∀ j, Submodule.span E (totExt X.toGeo E '' (sysOf X Λ₀).V j) = LinearMap.range (incl (X.baseChange E) j) := by
  first | exact @GlobalTheory.HSShort.totExt_props | exact GlobalTheory.HSShort.totExt_props | (intros; apply GlobalTheory.HSShort.totExt_props <;> assumption)
end

section

section
open GlobalTheory.PsCo.PcEG

noncomputable section

open Finset ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap

namespace GlobalTheory.PsCo.PcEF.HarishChandraWeightIntegral

variable {n : ℕ}

theorem card_split (ε : Fin n → Bool) (a : Fin n) :
    (univ.filter fun b => a < b ∧ ε b = ε a).card + (univ.filter fun b => b < a ∧ ε b = ε a).card + 1 =
      (univ.filter fun b => ε b = ε a).card := by
  have h : (univ.filter fun b => ε b = ε a) =
      ((univ.filter fun b => a < b ∧ ε b = ε a) ∪ (univ.filter fun b => b < a ∧ ε b = ε a)) ∪ {a} := by
    ext b
    simp only [mem_filter, mem_univ, true_and, mem_union, mem_singleton]
    constructor
    · intro h
      rcases lt_trichotomy a b with h1 | h1 | h1
      · exact Or.inl (Or.inl ⟨h1, h⟩)
      · exact Or.inr h1.symm
      · exact Or.inl (Or.inr ⟨h1, h⟩)
    · rintro ((⟨_, h⟩ | ⟨_, h⟩) | rfl)
      · exact h
      · exact h
      · rfl
  have d1 : Disjoint (univ.filter fun b => a < b ∧ ε b = ε a) (univ.filter fun b => b < a ∧ ε b = ε a) := by
    rw [disjoint_filter]
    intro x _ h1 h2
    exact lt_asymm h1.1 h2.1
  have d2 : Disjoint ((univ.filter fun b => a < b ∧ ε b = ε a) ∪ (univ.filter fun b => b < a ∧ ε b = ε a))
      {a} := by
    rw [disjoint_singleton_right]
    simp
  rw [h, card_union_of_disjoint d2, card_union_of_disjoint d1, card_singleton]

theorem p_add_q (ε : Fin n → Bool) : pOf ε + qOf ε = n := by
  delta pOf qOf
  have := card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) (fun a => ε a = true)
  simpa using this

theorem gaW_eq (ε : Fin n → Bool) (lam : Fin n → ℝ) (m : Fin n → ℤ)
    (hm : ∀ a, lam a + ((n : ℝ) - 1) / 2 = m a) (a : Fin n) :
    gaW ε lam a = ((m a - (if ε a then 0 else (pOf ε : ℤ)) - ReciprocityTheory.ChartRestriction.TR.Weyl.rhoK ε a : ℤ) : ℝ) := by
  have hcR : ((univ.filter fun b => a < b ∧ ε b = ε a).card : ℝ) +
      ((univ.filter fun b => b < a ∧ ε b = ε a).card : ℝ) + 1 =
      ((univ.filter fun b => ε b = ε a).card : ℝ) := by exact_mod_cast card_split ε a
  have hpqR : (pOf ε : ℝ) + qOf ε = n := by exact_mod_cast p_add_q ε
  have hma := hm a
  delta gaW rhoC rhoHol ReciprocityTheory.ChartRestriction.TR.Weyl.rhoK
  simp only [Pi.add_apply, Pi.sub_apply]
  by_cases h : ε a = true
  · have hs : ((univ.filter fun b => ε b = ε a).card : ℝ) = pOf ε := by
      delta pOf
      rw [h]
    simp only [ite_eq_left h]
    push_cast
    linarith
  · have hs : ((univ.filter fun b => ε b = ε a).card : ℝ) = qOf ε := by
      delta qOf
      rw [Bool.eq_false_of_not_eq_true h]
    simp only [ite_eq_right h]
    push_cast
    linarith

end GlobalTheory.PsCo.PcEF.HarishChandraWeightIntegral

namespace GlobalTheory.PsCo.PcEF

theorem harishChandraWeight_integral_dominant : GaInt := by
  intro n ε lam hlam
  obtain ⟨hanti, hz⟩ := hlam
  choose z hz using hz
  let m : Fin n → ℤ := fun a => z a + ((n : ℤ) - 1)
  have hm : ∀ a, lam a + ((n : ℝ) - 1) / 2 = m a := by
    intro a
    have := hz a
    simp only [m]
    push_cast
    linarith
  let Λ : Fin n → ℤ := fun a =>
    m a - (if ε a then 0 else (pOf ε : ℤ)) - ReciprocityTheory.ChartRestriction.TR.Weyl.rhoK ε a
  have hg : gaW ε lam = fun a => (Λ a : ℝ) := funext fun a => HarishChandraWeightIntegral.gaW_eq ε lam m hm a
  refine ⟨Λ, m, hg, ?_, hm, ?_⟩
  · intro a b hab he
    have hBA : BlockAnti ε lam := by
      intro a b hab _
      have h1 := hanti hab
      have h2 : (m b : ℝ) < m a := by linarith [hm a, hm b]
      have h3 : m b < m a := by exact_mod_cast h2
      have h4 : ((m b : ℤ) : ℝ) + 1 ≤ m a := by exact_mod_cast Int.add_one_le_of_lt h3
      linarith [hm a, hm b]
    have h := lf_dom_block hBA a b hab he
    have e : lowK ε lam + (rhoHol ε - rhoN ε) = gaW ε lam := by
      funext x
      delta lowK gaW
      simp only [Pi.add_apply, Pi.sub_apply]
      ring
    rw [e, hg] at h
    have h' : (Λ b : ℝ) ≤ Λ a := h
    exact_mod_cast h'
  · intro a
    simp only [Λ, Pi.add_apply]
    ring

end GlobalTheory.PsCo.PcEF

end
end
end

section

noncomputable section

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap
open GlobalTheory.PsCo.Pc1 (Mat)

namespace GlobalTheory.PsCo.PcEF

open GlobalTheory.PsCo.PcEG


theorem supertrace_carriedBy_diracKernel : StrKer := by
  intro n ε H _ _ σ D E hσ hD Y _ hY hG hK
  classical
  let Z : Submodule ℂ (TensorProduct ℂ D (Fock n)) := Y ⊓ LinearMap.ker (dD ε E)
  have hZY : Z ≤ Y := inf_le_left
  haveI hZf : FiniteDimensional ℂ Z := Submodule.finiteDimensional_of_le hZY
  have hZK : ∀ (k : Mat n) (hk : k ∈ Kset ε), ∀ y ∈ Z, wK hD hk y ∈ Z := by
    intro k hk y hy
    refine ⟨hK k hk y hy.1, ?_⟩
    have h0 : dD ε E y = 0 := hy.2
    show dD ε E (wK hD hk y) = 0
    rw [← wK_D hσ hD hk, h0, map_zero]
  have hZG : ∀ y ∈ Z, gradT y ∈ Z := by
    intro y hy
    refine ⟨hG y hy.1, ?_⟩
    have h0 : dD ε E y = 0 := hy.2
    show dD ε E (gradT y) = 0
    have := gradT_D (ε := ε) E y
    rw [h0, map_zero] at this
    exact neg_eq_zero.1 this.symm
  let Γ : TSub Z →ₗ[ℂ] TSub Z := ((gradT.restrict hZG : Z →ₗ[ℂ] Z) : TSub Z →ₗ[ℂ] TSub Z)
  refine ⟨Z, hZf, hZK, Γ, hZY, fun y hy => hy.2, fun k hk => ?_⟩
  have hU : IsInfUnitary ε E := isInfUnitary_of_isDerivedOn hσ hD
  let Dl : TSub Y →ₗ[ℂ] TSub Y := (((dD ε E).restrict hY : Y →ₗ[ℂ] Y) : TSub Y →ₗ[ℂ] TSub Y)
  let Γy : TSub Y →ₗ[ℂ] TSub Y := ((gradT.restrict hG : Y →ₗ[ℂ] Y) : TSub Y →ₗ[ℂ] TSub Y)
  let B : TSub Y →ₗ[ℂ] TSub Y := (((wK hD hk).restrict (hK k hk) : Y →ₗ[ℂ] Y) : TSub Y →ₗ[ℂ] TSub Y)
  obtain ⟨hker, htr⟩ := str_eq_str_ker Dl Γy B
    (fun x y => by rw [tsub_inner, tsub_inner]; exact tform_D hU _ _)
    (fun x => Subtype.ext (gradT_D E _)) (fun x => Subtype.ext (wK_D hσ hD hk _))
  have h1 : LinearMap.trace ℂ Y ((gradT ∘ₗ wK hD hk).restrict (fun y hy => hG _ (hK k hk y hy))) =
      LinearMap.trace ℂ (TSub Y) (Γy ∘ₗ B) := rfl
  rw [h1, htr]
  have hmemZ : ∀ x : LinearMap.ker Dl, tsubVal Y (x : TSub Y) ∈ Z := by
    intro x
    have hx : Dl (x : TSub Y) = 0 := x.2
    exact ⟨tsubVal_mem (x : TSub Y), congrArg (tsubVal Y) hx⟩
  let f : LinearMap.ker Dl →ₗ[ℂ] TSub Z :=
    { toFun := fun x => ((⟨tsubVal Y (x : TSub Y), hmemZ x⟩ : Z) : TSub Z)
      map_add' := fun x y => rfl
      map_smul' := fun c x => rfl }
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      have : tsubVal Y (x : TSub Y) = tsubVal Y (y : TSub Y) := congrArg (tsubVal Z) hxy
      exact Subtype.ext (tsubVal_injective this)
    · intro z
      have hzY : tsubVal Z z ∈ Y := hZY (tsubVal_mem z)
      let x : TSub Y := ((⟨tsubVal Z z, hzY⟩ : Y) : TSub Y)
      have hx : x ∈ LinearMap.ker Dl := by
        rw [LinearMap.mem_ker]
        apply tsubVal_injective
        rw [map_zero]
        exact (tsubVal_mem z).2
      exact ⟨⟨x, hx⟩, rfl⟩
  let e := LinearEquiv.ofBijective f hf
  rw [← LinearMap.trace_conj' _ e]
  congr 1
  apply LinearMap.ext
  intro z
  rw [LinearEquiv.conj_apply_apply]
  apply tsubVal_injective
  obtain ⟨x, rfl⟩ := e.surjective z
  rw [LinearEquiv.symm_apply_apply]
  show tsubVal Z (f ((Γy ∘ₗ B).restrict hker x)) = tsubVal Z (Γ (tOp hD hZK k (f x)))
  have hΓ : ∀ w : TSub Z, tsubVal Z (Γ w) = gradT (tsubVal Z w) := fun w => rfl
  rw [hΓ, tOp_apply hD hZK hk]
  rfl

end GlobalTheory.PsCo.PcEF
end
end

section

noncomputable section

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap

namespace GlobalTheory.PsCo.PcEF

open GlobalTheory.PsCo.PcEG

theorem casimirScalar_stableSumSpace : BuildY := by
  intro n ε H _ _ σ D E hσ hD c hc L hLf hLK
  have hE : IsGlRep E := hD.glRep
  have hLk : IsKStableSub ε E L :=
    isKStableSub_of_kStable hσ hD L hLf fun k hk v hv => ⟨sigD hD hk v, hLK k hk v hv, rfl⟩
  set Dop := dOp ε (eT E) cpT + dOp' ε (eT E) cmT with hDop
  let Y0 : Submodule ℂ (TensorProduct ℂ D (Fock n)) := tensFock L ⊓ physicalSubspace ε
  have hA : ∀ a b, ε a = ε b → ∀ x ∈ Y0, diagE ε (eT E) cpT cmT a b x ∈ Y0 :=
    fun a b hab x hx => ⟨tensorFock_diagAction_stable ε hLk hab hx.1, (physSub_stable ε E).2.1 a b x hx.2⟩
  have hD2 : ∀ y ∈ Y0, Dop (Dop y) ∈ Y0 := by
    intro y hy
    have h2 := LinearMap.congr_fun (two_D_sq (eT_isGlRep hE) cpT_cmT_isCAR (eT_commutesCAR E) ε) y
    rw [LinearMap.smul_apply, Module.End.mul_apply] at h2
    have hcas : casimir (eT (n := n) E) y = c • y := by
      rw [TRGap.casimir_eT]
      exact map_eq_smul_of_tensFock (fun v _ => hc v) hy.1
    have hmem : (2 : ℂ) • Dop (Dop y) ∈ Y0 := by
      rw [hDop, h2]
      simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.neg_apply, LinearMap.smul_apply,
        LinearMap.sum_apply]
      rw [hcas]
      refine Submodule.sub_mem _ (Submodule.add_mem _ (Submodule.neg_mem _ (Submodule.smul_mem _ _ hy)) ?_)
        (Submodule.smul_mem _ _ (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (hA a a rfl y hy)))
      simp only [casimirK, LinearMap.sum_apply, Module.End.mul_apply]
      exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b hb =>
        hA a b (Finset.mem_filter.1 hb).2.symm _ (hA b a (Finset.mem_filter.1 hb).2 y hy)
    have := Submodule.smul_mem _ (1 / 2 : ℂ) hmem
    rwa [smul_smul, show (1 / 2 : ℂ) * 2 = 1 by norm_num, one_smul] at this
  have hG0 : ∀ z ∈ Y0, gradT z ∈ Y0 := fun z hz =>
    ⟨tensFock_lTensor_stable _ hz.1, (physSub_stable ε E).2.2.2.2 z hz.2⟩
  have hW0 : ∀ (k : Matrix (Fin n) (Fin n) ℂ) (hk : k ∈ Kset ε), ∀ y ∈ Y0, wK hD hk y ∈ Y0 :=
    fun k hk y hy => ⟨wK_tensFock hD hk (fun x hx => hLK k hk x hx) hy.1, wK_physSub hD hk hy.2⟩
  have hfd0 : FiniteDimensional ℂ Y0 := by
    haveI := tensorFock_finiteDimensional (n := n) hLf
    exact Submodule.finiteDimensional_of_le inf_le_left
  refine ⟨Y0 ⊔ Y0.map Dop, inferInstance, le_sup_left, sup_le inf_le_right ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact dD_physSub E hy.2
  · intro y hy
    obtain ⟨y0, hy0, y1, ⟨x, hx, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hy
    show Dop (y0 + Dop x) ∈ _
    rw [map_add (f := _)]
    exact Submodule.add_mem _ (Submodule.mem_sup_right ⟨y0, hy0, rfl⟩) (Submodule.mem_sup_left (hD2 x hx))
  · intro y hy
    obtain ⟨y0, hy0, y1, ⟨x, hx, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hy
    rw [map_add (f := _), hDop, gradT_D]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (hG0 y0 hy0))
      (Submodule.mem_sup_right ⟨-gradT x, Submodule.neg_mem _ (hG0 x hx), by rw [map_neg]⟩)
  · intro k hk y hy
    obtain ⟨y0, hy0, y1, ⟨x, hx, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hy
    rw [map_add (f := _), hDop, wK_D hσ hD hk]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (hW0 k hk y0 hy0))
      (Submodule.mem_sup_right ⟨_, hW0 k hk x hx, rfl⟩)

end GlobalTheory.PsCo.PcEF
end
end

section

noncomputable section

open Finset ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap

namespace GlobalTheory.PsCo.PcEF

open GlobalTheory.PsCo.PcEG

theorem casimirValue_highestWeightCoordinates : CasCoord := by
  intro n ε lam M _ _ E hE z hz hD s
  have hE' := eT_isGlRep (n := n) hE
  have h2 := LinearMap.congr_fun (two_D_sq hE' cpT_cmT_isCAR (eT_commutesCAR E) ε) z
  have hK := casimirK_khwVec_compact ε (diagE_compact hE' cpT_cmT_isCAR (eT_commutesCAR E) ε) hz
  have hs : ∑ a, ((rhoHol ε a : ℝ) : ℂ) • diagE ε (eT E) cpT cmT a a z =
      ((dot (rhoHol ε) (gaW ε lam) : ℝ) : ℂ) • z := by
    simp only [dot, Complex.ofReal_sum, Complex.ofReal_mul, sum_smul, hz.1, smul_smul]
  have h0 : ((2 : ℂ) • ((dOp ε (eT E) cpT + dOp' ε (eT E) cmT) * (dOp ε (eT E) cpT + dOp' ε (eT E) cmT))) z = 0 := by
    rw [LinearMap.smul_apply, mul_apply_eq_comp]
    have : (dOp ε (eT E) cpT + dOp' ε (eT E) cmT) z = 0 := hD
    rw [this, map_zero, smul_zero]
  rw [h0] at h2
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.neg_apply, LinearMap.smul_apply,
    LinearMap.sum_apply, hK, hs] at h2
  have hid := khw_real_identity ε (lam - rhoC ε)
  have hg : lam - rhoC ε + rhoHol ε = gaW ε lam := rfl
  have hl : lam - rhoC ε + rhoC ε = lam := sub_add_cancel _ _
  rw [hg, hl] at hid
  have hc : casimir (eT (n := n) E) z = ((casVal lam : ℝ) : ℂ) • z := by
    have e : casimir (eT (n := n) E) z =
        ((nsq (gaW ε lam + rhoC ε) - nsq (rhoC ε) : ℝ) : ℂ) • z -
          (2 : ℂ) • (((dot (rhoHol ε) (gaW ε lam) : ℝ) : ℂ) • z) := by
      linear_combination (norm := module) h2
    rw [e, casVal, ← hid]
    simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_ofNat, sub_smul, smul_smul]
  have hcoord := congrArg (tco s) hc
  rw [TRGap.casimir_eT, tco_map_left] at hcoord
  simpa only [tco, map_smul] using hcoord

end GlobalTheory.PsCo.PcEF
end
end

section

noncomputable section

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap

namespace GlobalTheory.PsCo.PcEF

open GlobalTheory.PsCo.PcEG

variable {n : ℕ}

theorem cpt_const {ε : Fin n → Bool} (h : pOf ε = 0 ∨ qOf ε = 0) (a b : Fin n) : ε a = ε b := by
  rcases h with hp | hq
  · have h1 : ∀ c, ε c = false := fun c => by
      have := Finset.filter_eq_empty_iff.1 (Finset.card_eq_zero.1 hp) (Finset.mem_univ c)
      simpa using this
    rw [h1 a, h1 b]
  · have h1 : ∀ c, ε c = true := fun c => by
      have := Finset.filter_eq_empty_iff.1 (Finset.card_eq_zero.1 hq) (Finset.mem_univ c)
      simpa using this
    rw [h1 a, h1 b]

theorem cpt_Jm_comm {ε : Fin n → Bool} (hc : ∀ a b, ε a = ε b) (M : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.Jm ε * M = M * Formalism.REAL.Jm ε := by
  ext i j
  delta Formalism.REAL.Jm
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, hc i j]
  ring

theorem cpt_Kset_eq {ε : Fin n → Bool} (hc : ∀ a b, ε a = ε b) :
    Formalism.REAL.Kset ε = Formalism.MainNotions.S.UJset ε := by
  ext g
  delta Formalism.REAL.Kset Formalism.MainNotions.S.UJset Formalism.REAL.inUJ
  simp only [Set.mem_ofPred_eq, Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  constructor
  · rintro ⟨hu, -⟩
    rw [Matrix.mul_assoc, cpt_Jm_comm hc g, ← Matrix.mul_assoc, hu, Matrix.one_mul]
  · intro h
    refine ⟨?_, (cpt_Jm_comm hc g).symm⟩
    have h2 : g.conjTranspose * g * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε := by
      rw [Matrix.mul_assoc, ← cpt_Jm_comm hc g, ← Matrix.mul_assoc]
      exact h
    have h3 := congrArg (· * Formalism.REAL.Jm ε) h2
    simp only [Matrix.mul_assoc, Formalism.REAL.Jm_mul_self, Matrix.mul_one] at h3
    exact h3

theorem compactDiscreteSeries_ownType : CptCase := by
  intro n ε lam h
  have hc := cpt_const h
  refine ⟨fun k => ?_, ?_, ?_⟩
  · have : IsEmpty {x : Fin n × Fin n // IsPhys ε x} :=
      ⟨fun x => by
        have h1 := x.2.1
        have h2 := x.2.2
        rw [hc x.1.1 x.1.2] at h1
        rw [h1] at h2
        exact Bool.noConfusion h2⟩
    unfold physDet
    exact Matrix.det_isEmpty
  · unfold sDeg sModes
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro x - ⟨h1, h2, -⟩
    rw [hc x.1 x.2] at h1
    rw [h1] at h2
    exact Bool.noConfusion h2
  · intro X _ _ D hD
    obtain ⟨hcs, hnt, hU, hirr, -, ⟨S, hS⟩, -⟩ := hD
    have := hcs
    have hKU := cpt_Kset_eq hc
    have : FiniteDimensional ℂ S := hS.1
    have hclosed : IsClosed (S : Set X) := S.isClosed_of_finiteDimensional
    have hstab : ∀ g ∈ Formalism.MainNotions.S.UJset ε, ∀ v ∈ S, D g v ∈ S := fun g hg v hv =>
      hS.2.1 g (hKU ▸ hg) v hv
    have htop : S = ⊤ := by
      rcases hirr S hclosed hstab with h0 | h0
      · exfalso
        obtain ⟨v, hv, hv0, -⟩ := hS.2.2.2.1
        rw [h0] at hv
        exact hv0 ((Submodule.mem_bot ℂ).1 hv)
      · exact h0
    subst htop
    have hga : gaW ε lam = Formalism.QuantumDeterminants.lowK ε lam := by
      funext a
      have hN : Formalism.REAL.rhoN ε a = 0 := by
        unfold Formalism.REAL.rhoN
        have e1 : (Finset.univ.filter fun b => a < b ∧ ε b ≠ ε a) = ∅ :=
          Finset.filter_eq_empty_iff.2 fun b _ hb => hb.2 (hc b a)
        have e2 : (Finset.univ.filter fun b => b < a ∧ ε b ≠ ε a) = ∅ :=
          Finset.filter_eq_empty_iff.2 fun b _ hb => hb.2 (hc b a)
        rw [e1, e2]
        simp
      have hH : rhoHol ε a = 0 := by
        unfold rhoHol
        rcases h with hp | hq
        · have ha : ε a = false := by
            have := Finset.filter_eq_empty_iff.1 (Finset.card_eq_zero.1 hp) (Finset.mem_univ a)
            simpa using this
          simp [ha, hp]
        · have ha : ε a = true := by
            have := Finset.filter_eq_empty_iff.1 (Finset.card_eq_zero.1 hq) (Finset.mem_univ a)
            simpa using this
          simp [ha, hq]
      delta gaW Formalism.QuantumDeterminants.lowK
      simp only [Pi.add_apply, Pi.sub_apply, hN, hH, add_zero]
      rfl
    refine ⟨LinearEquiv.finiteDimensional Submodule.topEquiv, hnt, hKU ▸ hU, ?_⟩
    rw [hga]
    exact hS

end GlobalTheory.PsCo.PcEF
end
end
