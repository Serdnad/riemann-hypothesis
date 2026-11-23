module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfAeFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle178
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalMeanEqVolumeMulRationalMean
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ArchimedeanUnitaryGroupStabilisersUnimodular
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle124
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle262
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle266
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle263
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle289
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FlatSpaceComponents
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualLatticeImageAdelicUnitary
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle286
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IsoMeanProd

variable {D : D7}

theorem symplOH_iso_mid {V V' W : HSp D} {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E}
    {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E} (hs : IsIsoSplit V V' C B)
    (q₀ : Matrix (Fin W.rank) (Fin r) D.host.E) (a : Mx D W.rank r) (x : WO V' W) :
    symplOH V W (isoPart V W C (q₀.map (incA D))) (isoPart V W C a + midPart V V' W B x) = 0 := by
  have rat_mul {l m n : ℕ} (M : Matrix (Fin l) (Fin m) D.host.E)
      (N : Matrix (Fin m) (Fin n) D.host.E) :
      GlobalTheory.MixModel.rat (M * N) = GlobalTheory.MixModel.rat M * GlobalTheory.MixModel.rat N := Matrix.map_mul
  have adj_mul {l m n : ℕ} (x : Mx D l m) (y : Mx D m n) :
      GlobalTheory.MixModel.adj (x * y) = GlobalTheory.MixModel.adj y * GlobalTheory.MixModel.adj x :=
    Formalism.UG.cT_mul (cA D) x y
  have hO_eq_trace (T : HSp D) (x y : WO V T) :
      hO V T x y = (GlobalTheory.MixModel.giA V * (GlobalTheory.MixModel.adj y * (GlobalTheory.MixModel.gA T * x))).trace := by
    simp only [hO, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Finset.mul_sum, mul_assoc]
    rfl
  set P : Mx D r V.rank := GlobalTheory.MixModel.rat (adj D C * V.gram) with hP
  set Q : Mx D V'.rank V.rank := GlobalTheory.MixModel.rat (V'.gram⁻¹ * adj D B * V.gram) with hQ
  have hG := GlobalTheory.MixModel.gram_conjTranspose V
  have hG' := GlobalTheory.MixModel.gramInv_conjTranspose V'
  have hU := GlobalTheory.MixModel.gram_isUnit_det V
  have hC0 : adj D C * V.gram * C = 0 := hs.frame.2.2
  have hO : adj D C * V.gram * B = 0 := hs.orth
  have k1 : P * GlobalTheory.MixModel.giA V * GlobalTheory.MixModel.adj P = 0 := by
    rw [hP, ← GlobalTheory.MixModel.rat_conjTranspose, GlobalTheory.MixModel.giA, ← rat_mul, ← rat_mul]
    have : adj D C * V.gram * V.gram⁻¹ * (adj D C * V.gram)ᴴ = 0 := by
      change Cᴴ * V.gram * V.gram⁻¹ * (Cᴴ * V.gram)ᴴ = 0
      change Cᴴ * V.gram * C = 0 at hC0
      rw [Matrix.conjTranspose_mul, hG, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc (Cᴴ * V.gram),
        ← Matrix.mul_assoc V.gram⁻¹, Matrix.nonsing_inv_mul _ hU, Matrix.one_mul, hC0]
    rw [this, GlobalTheory.MixModel.rat_zero]
  have k2 : P * GlobalTheory.MixModel.giA V * GlobalTheory.MixModel.adj Q = 0 := by
    rw [hP, hQ, ← GlobalTheory.MixModel.rat_conjTranspose, GlobalTheory.MixModel.giA, ← rat_mul, ← rat_mul]
    have : adj D C * V.gram * V.gram⁻¹ * (V'.gram⁻¹ * adj D B * V.gram)ᴴ = 0 := by
      change Cᴴ * V.gram * V.gram⁻¹ * (V'.gram⁻¹ * Bᴴ * V.gram)ᴴ = 0
      change Cᴴ * V.gram * B = 0 at hO
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hG, hG', Matrix.conjTranspose_conjTranspose,
        Matrix.mul_assoc (Cᴴ * V.gram), ← Matrix.mul_assoc V.gram⁻¹,
        Matrix.nonsing_inv_mul _ hU, Matrix.one_mul, ← Matrix.mul_assoc, hO, Matrix.zero_mul]
    rw [this, GlobalTheory.MixModel.rat_zero]
  have e1 : isoPart V W C (q₀.map (incA D)) = GlobalTheory.MixModel.rat q₀ * P := rfl
  have e2 : isoPart V W C a + midPart V V' W B x = a * P + x * Q := rfl
  have k3 : P * GlobalTheory.MixModel.giA V * GlobalTheory.MixModel.adj (a * P + x * Q) = 0 := by
    rw [GlobalTheory.MixModel.adj_add, adj_mul, adj_mul, Matrix.mul_add,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, k1, k2, Matrix.zero_mul, Matrix.zero_mul, add_zero]
  rw [GlobalTheory.MixModel.symplOH_eq, hO_eq_trace, e1, e2]
  have e3 : GlobalTheory.MixModel.giA V * (GlobalTheory.MixModel.adj (a * P + x * Q) * (GlobalTheory.MixModel.gA W * (GlobalTheory.MixModel.rat q₀ * P))) =
      (GlobalTheory.MixModel.giA V * GlobalTheory.MixModel.adj (a * P + x * Q) * GlobalTheory.MixModel.gA W * GlobalTheory.MixModel.rat q₀) * P := by
    simp only [Matrix.mul_assoc]
  rw [e3, Matrix.trace_mul_comm]
  have e4 : P * (GlobalTheory.MixModel.giA V * GlobalTheory.MixModel.adj (a * P + x * Q) * GlobalTheory.MixModel.gA W * GlobalTheory.MixModel.rat q₀) =
      (P * GlobalTheory.MixModel.giA V * GlobalTheory.MixModel.adj (a * P + x * Q)) * (GlobalTheory.MixModel.gA W * GlobalTheory.MixModel.rat q₀) := by
    simp only [Matrix.mul_assoc]
  rw [e4, k3, Matrix.zero_mul, Matrix.trace_zero, map_zero]

theorem iso_periodic {V V' W : HSp D} {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E}
    {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E} (hs : IsIsoSplit V V' C B) {ψ : AddChar (AF D.host.F) ℂ}
    {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) (x : WO V' W) :
    ∀ γ ∈ GlobalTheory.MixModel.ratMx D W.rank r, ∀ a,
      f (isoPart V W C (γ + a) + midPart V V' W B x) = f (isoPart V W C a + midPart V V' W B x) := by
  rintro _ ⟨q₀, rfl⟩ a
  have e3 : (incA D).toAddMonoidHom.mapMatrix q₀ = q₀.map (incA D) := rfl
  have hadd : isoPart V W C (q₀.map (incA D) + a) = isoPart V W C (q₀.map (incA D)) + isoPart V W C a :=
    Matrix.add_mul _ _ _
  have hrat : ratW W V (q₀ * (adj D C * V.gram)) = isoPart V W C (q₀.map (incA D)) := Matrix.map_mul
  rw [e3, hadd, add_assoc, ← hrat, hf.quasi, hrat, symplOH_iso_mid hs, neg_zero, AddChar.map_zero_eq_one, one_mul]

end GlobalTheory.IsoMeanProd

namespace GlobalTheory.IsoMeanProd

theorem mean_iso_mul_star : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), μ'.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V') 𝓕' μ' → ∀ F G, IsThetaFunO ψ V W F → IsThetaFunO ψ V W G → ∫ y in 𝓨, ∫ y' in 𝓨, ∫ x in 𝓕', F (isoPart V W C (y + y') + midPart V V' W B x) * star (G (isoPart V W C y' + midPart V V' W B x)) ∂μ' ∂μ ∂μ = ∫ x in 𝓕', res V V' W C B μ 𝓨 F x * star (res V V' W C B μ 𝓨 G x) ∂μ' := by
  intro D V V' W r C B hs ψ hψ μ 𝓨 hμ μ' 𝓕' hμ' h𝓕' F G hF hG
  have hμ1 : IsCovolOne (GlobalTheory.MixModel.ratMx D W.rank r) μ 𝓨 := hμ
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank r
  obtain ⟨j1, j2, j3, j4, j5, -⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank V'.rank
  haveI : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  haveI : BorelSpace (WO V' W) := ⟨rfl⟩
  haveI hfin1 : IsFiniteMeasure (μ.restrict 𝓨) :=
    ⟨by rw [Measure.restrict_apply_univ, hμ.2.2]; exact ENNReal.one_lt_top⟩
  haveI : IsFiniteMeasure (μ'.restrict 𝓕') :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 (GlobalTheory.Size.measure_dom hμ' h𝓕').2⟩
  haveI hsf1 : SigmaFinite (μ.restrict 𝓨) := @IsFiniteMeasure.toSigmaFinite _ _ _ hfin1
  haveI : SFinite (μ.restrict 𝓨) := @instSFiniteOfSigmaFinite _ _ _ hsf1
  haveI : SigmaFinite (μ'.restrict 𝓕') := inferInstance
  haveI : SFinite (μ'.restrict 𝓕') := inferInstance
  obtain ⟨cF, hcF⟩ := GlobalTheory.WeilVacMove.exists_bound hψ hF
  obtain ⟨cG, hcG⟩ := GlobalTheory.WeilVacMove.exists_bound hψ hG
  have ciso : Continuous (fun y : Mx D W.rank r => isoPart V W C y) := continuous_id.matrix_mul continuous_const
  have cmid : Continuous (fun x : WO V' W => midPart V V' W B x) := continuous_id.matrix_mul continuous_const
  obtain ⟨H, hH⟩ : ∃ H : Mx D W.rank r → Mx D W.rank r → WO V' W → ℂ, H = fun y y' x =>
      F (isoPart V W C (y + y') + midPart V V' W B x) * star (G (isoPart V W C y' + midPart V V' W B x)) := ⟨_, rfl⟩
  have hHb : ∀ y y' x, ‖H y y' x‖ ≤ cF * cG := by
    intro y y' x
    rw [hH, norm_mul, norm_star]
    exact mul_le_mul (hcF _) (hcG _) (norm_nonneg _) ((norm_nonneg _).trans (hcF 0))
  have hHc : Continuous fun p : Mx D W.rank r × Mx D W.rank r × WO V' W => H p.1 p.2.1 p.2.2 := by
    rw [hH]
    exact (hF.cont.comp ((ciso.comp (continuous_fst.add continuous_snd.fst)).add (cmid.comp continuous_snd.snd))).mul
      (continuous_star.comp (hG.cont.comp ((ciso.comp continuous_snd.fst).add (cmid.comp continuous_snd.snd))))
  have hint : ∀ {X : Type} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] (ν : Measure X)
      [IsFiniteMeasure ν] (g : X → ℂ), Continuous g → (∀ z, ‖g z‖ ≤ cF * cG) → Integrable g ν :=
    fun ν _ g hg hb => Integrable.of_bound hg.aestronglyMeasurable _ (Filter.Eventually.of_forall hb)
  have hI1 : ∀ y, Integrable (Function.uncurry fun y' x => H y y' x) ((μ.restrict 𝓨).prod (μ'.restrict 𝓕')) :=
    fun y => hint _ _ (hHc.comp (continuous_const.prodMk continuous_id)) fun z => hHb _ _ _
  have hI3 : Integrable (fun q : (Mx D W.rank r × WO V' W) × Mx D W.rank r => H q.1.1 q.2 q.1.2)
      (((μ.restrict 𝓨).prod (μ'.restrict 𝓕')).prod (μ.restrict 𝓨)) :=
    hint _ _ (hHc.comp (continuous_fst.fst.prodMk (continuous_snd.prodMk continuous_fst.snd))) fun z => hHb _ _ _
  have hI2 : Integrable (Function.uncurry fun y x => ∫ y', H y y' x ∂(μ.restrict 𝓨))
      ((μ.restrict 𝓨).prod (μ'.restrict 𝓕')) := hI3.integral_prod_left
  have hI4 : ∀ x, Integrable (Function.uncurry fun y y' => H y y' x) ((μ.restrict 𝓨).prod (μ.restrict 𝓨)) :=
    fun x => hint _ _ (hHc.comp (continuous_fst.prodMk (continuous_snd.prodMk continuous_const))) fun z => hHb _ _ _
  have step4 : ∀ x y', ∫ y in 𝓨, H y y' x ∂μ =
      res V V' W C B μ 𝓨 F x * star (G (isoPart V W C y' + midPart V V' W B x)) := by
    intro x y'
    rw [hH]
    simp only
    rw [integral_mul_const]
    congr 1
    exact GlobalTheory.MixModel.covolOne_integral_add hμ1 (fun a => F (isoPart V W C a + midPart V V' W B x))
      (iso_periodic hs hF x) y'
  have step5 : ∀ x, ∫ y' in 𝓨, res V V' W C B μ 𝓨 F x * star (G (isoPart V W C y' + midPart V V' W B x)) ∂μ =
      res V V' W C B μ 𝓨 F x * star (res V V' W C B μ 𝓨 G x) := by
    intro x
    rw [integral_const_mul]
    congr 1
    exact integral_conj
  have e0 : ∀ y y' x, F (isoPart V W C (y + y') + midPart V V' W B x) * star (G (isoPart V W C y' + midPart V V' W B x)) = H y y' x := by
    intro y y' x; rw [hH]
  simp only [e0]
  calc ∫ y in 𝓨, ∫ y' in 𝓨, ∫ x in 𝓕', H y y' x ∂μ' ∂μ ∂μ
      = ∫ y in 𝓨, ∫ x in 𝓕', ∫ y' in 𝓨, H y y' x ∂μ ∂μ' ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall fun y => integral_integral_swap (hI1 y))
    _ = ∫ x in 𝓕', ∫ y in 𝓨, ∫ y' in 𝓨, H y y' x ∂μ ∂μ ∂μ' := integral_integral_swap hI2
    _ = ∫ x in 𝓕', ∫ y' in 𝓨, ∫ y in 𝓨, H y y' x ∂μ ∂μ ∂μ' :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => integral_integral_swap (hI4 x))
    _ = ∫ x in 𝓕', ∫ y' in 𝓨, res V V' W C B μ 𝓨 F x * star (G (isoPart V W C y' + midPart V V' W B x)) ∂μ ∂μ' :=
        integral_congr_ae (Filter.Eventually.of_forall fun x =>
          integral_congr_ae (Filter.Eventually.of_forall fun y' => step4 x y'))
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun x => step5 x)

end GlobalTheory.IsoMeanProd
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistHaar

open scoped Pointwise

theorem isAddFundamentalDomain_prod {A B : Type*} [AddGroup A] [AddGroup B] [MeasurableSpace A]
    [MeasurableSpace B] {Γ : AddSubgroup A} {Δ : AddSubgroup B} {μ : Measure A} {ν : Measure B} [SFinite μ]
    [SFinite ν] {s : Set A} {t : Set B} (hs : IsAddFundamentalDomain Γ s μ) (ht : IsAddFundamentalDomain Δ t ν) :
    IsAddFundamentalDomain (Γ.prod Δ) (s ×ˢ t) (μ.prod ν) := by
  refine ⟨hs.nullMeasurableSet.prod ht.nullMeasurableSet, ?_, ?_⟩
  ·
    have h1 := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae hs.ae_covers
    have h2 := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae ht.ae_covers
    filter_upwards [h1, h2] with p hp hq
    obtain ⟨g, hg⟩ := hp
    obtain ⟨h, hh⟩ := hq
    exact ⟨⟨((g : A), (h : B)), AddSubgroup.mem_prod.2 ⟨g.2, h.2⟩⟩, hg, hh⟩
  ·
    intro g h hgh
    change μ.prod ν ((g +ᵥ s ×ˢ t) ∩ (h +ᵥ s ×ˢ t)) = 0
    let g1 : Γ := ⟨(g : A × B).1, (AddSubgroup.mem_prod.1 g.2).1⟩
    let h1 : Γ := ⟨(h : A × B).1, (AddSubgroup.mem_prod.1 h.2).1⟩
    let g2 : Δ := ⟨(g : A × B).2, (AddSubgroup.mem_prod.1 g.2).2⟩
    let h2 : Δ := ⟨(h : A × B).2, (AddSubgroup.mem_prod.1 h.2).2⟩
    by_cases e1 : g1 = h1
    · have e2 : g2 ≠ h2 := fun e2 => hgh (Subtype.ext (Prod.ext (congrArg Subtype.val e1) (congrArg Subtype.val e2)))
      have h0 : ν ((g2 +ᵥ t) ∩ (h2 +ᵥ t)) = 0 := ht.aedisjoint e2
      refine measure_mono_null (t := Set.univ ×ˢ ((g2 +ᵥ t) ∩ (h2 +ᵥ t))) ?_ ?_
      · rintro p ⟨hp1, hp2⟩
        rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hp1 hp2
        refine ⟨Set.mem_univ _, ?_, ?_⟩
        · rw [Set.mem_vadd_set_iff_neg_vadd_mem]; exact hp1.2
        · rw [Set.mem_vadd_set_iff_neg_vadd_mem]; exact hp2.2
      · rw [Measure.prod_prod, h0, mul_zero]
    · have h0 : μ ((g1 +ᵥ s) ∩ (h1 +ᵥ s)) = 0 := hs.aedisjoint e1
      refine measure_mono_null (t := ((g1 +ᵥ s) ∩ (h1 +ᵥ s)) ×ˢ Set.univ) ?_ ?_
      · rintro p ⟨hp1, hp2⟩
        rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hp1 hp2
        refine ⟨⟨?_, ?_⟩, Set.mem_univ _⟩
        · rw [Set.mem_vadd_set_iff_neg_vadd_mem]; exact hp1.1
        · rw [Set.mem_vadd_set_iff_neg_vadd_mem]; exact hp2.1
      · rw [Measure.prod_prod, h0, zero_mul]

end GlobalTheory.TwistHaar

namespace GlobalTheory.TwistHaar

open scoped Pointwise



theorem integral_fundamentalDomain_eq_iterated : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ (μV : Measure (WO V W)) (𝓕V : Set (WO V W)), μV.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕V μV → ∀ (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), μ'.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V') 𝓕' μ' → ∃ κ : ℝ, 0 < κ ∧ (∀ H : WO V W → ℂ, Continuous H → (∃ b : ℝ, ∀ w, ‖H w‖ ≤ b) → (∀ γ ∈ ratL W V, ∀ w, H (γ + w) = H w) → ∫ w in 𝓕V, H w ∂μV = κ • ∫ t in 𝓨, ∫ y in 𝓨, ∫ x in 𝓕', H (isoPart V W C' t + isoPart V W C y + midPart V V' W B x) ∂μ' ∂μ ∂μ) := by
  intro D V V' W r C B hs C' h1 h2 h3 μ 𝓨 hY μV 𝓕V hμV hFV μ' 𝓕' hμ' hF'
  obtain ⟨e, he, hrat⟩ := GlobalTheory.T.exists_homSpace_dual_isotropic_middle_decomposition D V V' W r C B hs C' h1 h2 h3
  obtain ⟨a1, a2, a3, a4, a5, -⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank r
  obtain ⟨b1, b2, b3, b4, b5, -⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank V'.rank
  obtain ⟨c1, c2, c3, c4, c5, -⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank V.rank
  have : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  have : BorelSpace (WO V' W) := ⟨rfl⟩
  have : BorelSpace (WO V W) := ⟨rfl⟩
  have : DiscreteTopology (ratMx D W.rank r) := a5
  have : DiscreteTopology (ratL W V') := b5
  have : DiscreteTopology (ratL W V) := c5
  have cA : Countable (ratMx D W.rank r) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have cB : Countable (ratL W V') := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have : μ.IsAddHaarMeasure := hY.1

  set Γ' : AddSubgroup (Mx D W.rank r × Mx D W.rank r × WO V' W) :=
    (ratMx D W.rank r).prod ((ratMx D W.rank r).prod (ratL W V')) with hΓ'
  have hmem : ∀ p, e p ∈ ratL W V ↔ p ∈ Γ' := by
    rintro ⟨t, y, x⟩
    rw [hrat]
    simp [Γ', AddSubgroup.mem_prod]
  have : Countable Γ' := Function.Injective.countable
    (f := fun g : Γ' => ((⟨(g : Mx D W.rank r × Mx D W.rank r × WO V' W).1, (AddSubgroup.mem_prod.1 g.2).1⟩ :
        ratMx D W.rank r),
      (⟨(g : Mx D W.rank r × Mx D W.rank r × WO V' W).2.1, (AddSubgroup.mem_prod.1 (AddSubgroup.mem_prod.1 g.2).2).1⟩ :
        ratMx D W.rank r),
      (⟨(g : Mx D W.rank r × Mx D W.rank r × WO V' W).2.2, (AddSubgroup.mem_prod.1 (AddSubgroup.mem_prod.1 g.2).2).2⟩ :
        ratL W V')))
    fun g h hgh => by
      simp only [Prod.mk.injEq, Subtype.mk.injEq] at hgh
      exact Subtype.ext (Prod.ext hgh.1 (Prod.ext hgh.2.1 hgh.2.2))
  set P : Measure (Mx D W.rank r × Mx D W.rank r × WO V' W) := μ.prod (μ.prod μ') with hP
  have hT : IsAddFundamentalDomain Γ' (𝓨 ×ˢ (𝓨 ×ˢ 𝓕')) P :=
    isAddFundamentalDomain_prod hY.2.1 (isAddFundamentalDomain_prod hY.2.1 hF')
  set m : Measure (WO V W) := P.map e with hm
  have : (μ.prod μ').IsAddHaarMeasure := inferInstance
  have : P.IsAddHaarMeasure := inferInstance
  have : m.IsAddHaarMeasure := e.isAddHaarMeasure_map P
  have : VAddInvariantMeasure Γ' (Mx D W.rank r × Mx D W.rank r × WO V' W) P :=
    ⟨fun g s _ => measure_preimage_add P (g : Mx D W.rank r × Mx D W.rank r × WO V' W) s⟩
  set c : NNReal := μV.addHaarScalarFactor m with hcdef
  have hc : μV = c • m := Measure.isAddLeftInvariant_eq_smul μV m
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hc
    exact (NeZero.ne μV) hc
  have hac : m ≪ μV := fun s hs0 => by
    rw [hc, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at hs0
    exact (mul_eq_zero.1 hs0).resolve_left (by simpa using hc0)
  have hFm : IsAddFundamentalDomain (ratL W V) 𝓕V m := hFV.mono hac
  have hemeas : Measurable e := e.continuous.measurable
  have hpre : IsAddFundamentalDomain Γ' (e ⁻¹' 𝓕V) P := by
    refine hFm.preimage_of_equiv (f := e) (MeasurePreserving.quasiMeasurePreserving ⟨hemeas, rfl⟩)
      (e := fun g => ⟨e.symm g, (hmem _).1 (by simpa using g.2)⟩) ⟨fun g h hgh => ?_, fun g => ?_⟩ fun g x => ?_
    · exact Subtype.ext (e.symm.injective (congrArg Subtype.val hgh))
    · exact ⟨⟨e g, (hmem g).2 g.2⟩, Subtype.ext (by simp)⟩
    · change e (e.symm g + x) = (g : WO V W) + e x
      rw [map_add (f := _), ContinuousAddEquiv.apply_symm_apply]
  have hfin : μ' 𝓕' ≠ ⊤ := (GlobalTheory.Size.measure_dom hμ' hF').2
  have : IsFiniteMeasure (μ.restrict 𝓨) := ⟨by rw [Measure.restrict_apply_univ, hY.2.2]; exact ENNReal.one_lt_top⟩
  have : IsFiniteMeasure (μ'.restrict 𝓕') := ⟨by rw [Measure.restrict_apply_univ]; exact hfin.lt_top⟩
  refine ⟨(c : ℝ), NNReal.coe_pos.2 (pos_iff_ne_zero.2 hc0), fun H hH hb hper => ?_⟩
  obtain ⟨b, hb⟩ := hb
  have hmeasH : Measurable (fun p => H (e p)) := (hH.comp e.continuous).measurable
  have step1 : ∫ w in 𝓕V, H w ∂μV = (c : ℝ) • ∫ w in 𝓕V, H w ∂m := by
    have : μV = (c : ENNReal) • m := by rw [hc]; rfl
    rw [this, Measure.restrict_smul, integral_smul_measure, ENNReal.coe_toReal]
  have step2 : ∫ w in 𝓕V, H w ∂m = ∫ p in e ⁻¹' 𝓕V, H (e p) ∂P :=
    (e.toHomeomorph.toMeasurableEquiv.measurableEmbedding).setIntegral_map H 𝓕V
  have step3 : ∫ p in e ⁻¹' 𝓕V, H (e p) ∂P = ∫ p in 𝓨 ×ˢ (𝓨 ×ˢ 𝓕'), H (e p) ∂P :=
    hpre.setIntegral_eq hT (f := fun p => H (e p)) fun g p => by
      change H (e ((g : Mx D W.rank r × Mx D W.rank r × WO V' W) + p)) = H (e p)
      rw [map_add (f := _)]
      exact hper _ ((hmem g).2 g.2) _
  have r1 : (μ.prod (μ.prod μ')).restrict (𝓨 ×ˢ (𝓨 ×ˢ 𝓕')) =
      (μ.restrict 𝓨).prod ((μ.restrict 𝓨).prod (μ'.restrict 𝓕')) :=
    ((congrArg (Measure.prod (μ.restrict 𝓨)) (Measure.prod_restrict 𝓨 𝓕')).trans
      (Measure.prod_restrict 𝓨 (𝓨 ×ˢ 𝓕'))).symm
  have step4 : ∫ p in 𝓨 ×ˢ (𝓨 ×ˢ 𝓕'), H (e p) ∂P = ∫ t in 𝓨, ∫ y in 𝓨, ∫ x in 𝓕',
      H (isoPart V W C' t + isoPart V W C y + midPart V V' W B x) ∂μ' ∂μ ∂μ := by
    refine (congrArg (fun ν => ∫ p, H (e p) ∂ν) r1).trans ?_
    refine (integral_prod _ (Integrable.of_bound hmeasH.aestronglyMeasurable b
      (Filter.Eventually.of_forall fun p => hb _))).trans ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    refine (integral_prod (fun q => H (e (t, q))) (Integrable.of_bound
      (hmeasH.comp measurable_prodMk_left).aestronglyMeasurable b (Filter.Eventually.of_forall fun p => hb _))).trans ?_
    simp only [he]
  exact step1.trans (congrArg (fun z : ℂ => (c : ℝ) • z) ((step2.trans step3).trans step4))

end GlobalTheory.TwistHaar
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.unipotentRadicalMean_eq_volume_mul_rationalMean : ∀ (D : D7) (V V' : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ (κ : Measure (NI V C)) (𝓝 : Set (NI V C)), κ.IsHaarMeasure → IsFundamentalDomain (NIQ V C) 𝓝 κ → ∀ (s : ℕ) (m : Matrix (Fin s) (Fin r) D.host.E), m.rank = s → ∃ (μ : Measure (Mx D s V'.rank)) (𝓐 : Set (Mx D s V'.rank)), IsCovolOne (ratMx D s V'.rank) μ 𝓐 ∧ ∀ φ : Mx D s V'.rank → ℂ, Continuous φ → (∀ γ ∈ ratMx D s V'.rank, ∀ a, φ (γ + a) = φ a) → ∫ n in 𝓝, φ (HMul.hMul (HMul.hMul ((m * adj D C' * V.gram).map (incA D) : Matrix (Fin s) (Fin V.rank) (AE D)) (mt V (n : GA D V) - 1)) (B.map (incA D) : Matrix (Fin V.rank) (Fin V'.rank) (AE D))) ∂κ = ((κ 𝓝).toReal : ℂ) * ∫ a in 𝓐, φ a ∂μ := by
  first | exact @GlobalTheory.UnipMean.mean_eq_volume_mul | exact GlobalTheory.UnipMean.mean_eq_volume_mul | (intros; apply GlobalTheory.UnipMean.mean_eq_volume_mul <;> assumption)
end

section

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section
namespace GlobalTheory.TrPhiOK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {r n : ℕ}
  {P : PPol σ r} {J : Matrix (Fin n) (Fin n) E}

theorem phiOK_of (hσ : IsCMExt F E σ) (hJ : IsHermND σ J) (k : Type) [Field k] [Algebra F k] [TopologicalSpace k]
    [IsTopologicalRing k] [T2Space k] [LocallyCompactSpace (HA k σ J)] [SecondCountableTopology (HA k σ J)]
    [T2Space (HA k σ J)] (hfin : Finite (Cls P k))
    (hU : ∀ μ : Measure (HA k σ J), μ.IsHaarMeasure → μ.IsMulRightInvariant)
    (hpr : ∀ g : HA k σ J, IsRegSS (matHom k σ J g).1 → IsProperOrbit (cent g) g)
    (μ : Measure (HA k σ J)) (dt : Measure (Tor P k)) (f : HA k σ J → ℂ) [hμ : μ.IsHaarMeasure]
    [hdt : dt.IsHaarMeasure] (hf : Continuous f) (hc : HasCompactSupport f) : PhiOK (J := J) μ dt f := by
  refine ⟨Set.toFinite _, fun x φ h => ?_⟩
  haveI := hU μ hμ
  set q : XSet P k J := ⟨QuotientGroup.mk x, x, φ, rfl, h⟩ with hq
  obtain ⟨hx0, h0⟩ := q.2.choose_spec.choose_spec
  set x0 := q.2.choose
  set φ0 := q.2.choose_spec.choose
  change HasOrbInt μ (gam h) (centMeas h dt) f (orbInt μ (gam h0) (centMeas h0 dt) f)

  have halg0 := GlobalTheory.T.torusElement_charpoly_regular_centralizer F E σ hσ r n P J hJ k x0 φ0 h0
  obtain ⟨e0, he0, hm0⟩ := GlobalTheory.T.unitaryTorus_equiv_centralizer_with_measure F E σ hσ r n P J hJ k x0 φ0 h0
  obtain ⟨e, he, hm⟩ := GlobalTheory.T.unitaryTorus_equiv_centralizer_with_measure F E σ hσ r n P J hJ k x φ h
  haveI : (centMeas h0 dt).IsHaarMeasure := by rw [hm0]; exact e0.isHaarMeasure_map dt
  haveI : (centMeas h0 dt).IsMulRightInvariant :=
    isMulRightInvariant_cent (isMulCommutative_cent_HA halg0.2.1) _
  have H0 : HasOrbInt μ (gam h0) (centMeas h0 dt) f (orbInt μ (gam h0) (centMeas h0 dt) f) :=
    (hpr _ halg0.2.1).hasOrbInt hf hc

  obtain ⟨g, hg⟩ := (GlobalTheory.T.normClasses_iff_conj_unitaryTorusEllipticElements F E σ hσ r n P J hJ k x0 φ0 h0 x φ h).1 (by rw [hx0])
  have hgam : g * gam h0 * g⁻¹ = gam h := (hg _).symm
  have hmeas : centMeas h dt = (centMeas h0 dt).map (centEquiv (conjEquiv g) (gam h0) hgam) := by
    rw [hm, hm0, Measure.map_map (map_continuous _).measurable (map_continuous _).measurable]
    congr 1
    funext t
    apply Subtype.ext
    change (e t).1 = g * (e0 t).1 * g⁻¹
    rw [he, he0, hg]
  rw [hmeas]
  exact ((hasOrbInt_conj (dh := μ) (dt := centMeas h0 dt) g hgam f _).1).2 H0

end GlobalTheory.TrPhiOK


open GlobalTheory.TrPhiOK in
theorem GlobalTheory.TrPhiOK.phiOK_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r n : ℕ) (P : PPol σ r) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → (∀ (v : HeightOneSpectrum (𝓞 F)) (μ : Measure (GLoc σ J v)) (dt : Measure (Tor P (Fv F v))) (f : GLoc σ J v → ℂ), μ.IsHaarMeasure → dt.IsHaarMeasure → Continuous f → HasCompactSupport f → PhiOK (J := J) μ dt f) ∧ ∀ (w : InfinitePlace F) (μ : Measure (GArch σ J w)) (dt : Measure (Tor P w.Completion)) (f : GArch σ J w → ℂ), μ.IsHaarMeasure → dt.IsHaarMeasure → Continuous f → HasCompactSupport f → PhiOK (J := J) μ dt f := by
  intro F E _ _ _ _ _ σ hσ r n P J hJ
  have hfin := GlobalTheory.T.finite_unitaryTorusNormClasses_at_all_places F E σ hσ r P
  refine ⟨fun v μ dt f hμ hdt hf hc => ?_, fun w μ dt f hμ hdt hf hc => ?_⟩
  · have hU := (GlobalTheory.LocalUnitaryUnimod.unimodularOver_adicCompletion F E σ hσ n J hJ v).1
    exact phiOK_of hσ hJ (Fv F v) (hfin.1 v) hU.2.2.2.2.2.2 (fun g hg => isProperOrbit_GLoc hσ hJ hg) μ dt f hf hc
  · haveI : SecondCountableTopology w.Completion :=
      (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
    have hU := (GlobalTheory.ArchUnitaryUnimod.unimodularOver_of_artinian (σ := σ) w.Completion hσ hJ).1
    exact phiOK_of hσ hJ w.Completion (hfin.2 w) hU.2.2.2.2.2.2 (fun g hg => isProperOrbit_GArch hσ hJ hg) μ dt f hf hc
end
end

section

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

theorem _root_.GlobalTheory.T.eventually_unitClass_realized_by_lattice_isometry : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r : ℕ) (P : PPol σ r) (J : Matrix (Fin r) (Fin r) E), IsHermND σ J → ∀ (L : Submodule (𝓞 E) (Fin r → E)) [Submodule.IsFullLattice E L], ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∃ (φ : (Fv F v ⊗[F] Fld P) ≃ₗ[Fv F v ⊗[F] E] (Fin r → Fv F v ⊗[F] E)) (h : IsIsom P (Fv F v) J (1 : plusUnits P (Fv F v)).1.1 φ), gam h ∈ stabLoc σ J L v ∧ ∀ t, torEmb h t ∈ stabLoc σ J L v ↔ t ∈ stabLoc (star' P) (one₁ P) (stdLattice (Fld P) 1) v := by
  first | exact @GlobalTheory.TrUnitLat.eventually_unitClass_isom | exact GlobalTheory.TrUnitLat.eventually_unitClass_isom | (intros; apply GlobalTheory.TrUnitLat.eventually_unitClass_isom <;> assumption)
end

section

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

theorem _root_.GlobalTheory.T.compact_unitaryTorus_real_place_tensor_eq_complex_pow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r : ℕ) (P : PPol σ r) (w : InfinitePlace F) (τ : EmbOver E w), CompactSpace (Tor P w.Completion) → ∃ Ψ : w.Completion ⊗[F] Fld P ≃+* (Fin r → ℂ), (∀ y i, Ψ (sigR w.Completion (star' P) y) i = conj (Ψ y i)) ∧ (∀ e i, Ψ (algebraMap (w.Completion ⊗[F] E) _ e) i = infEmb τ e) ∧ Ψ (1 ⊗ₜ[F] alpha P) = cxRoots τ.1 P ∧ (∀ y, infEmb τ (trBase P w.Completion y) = ∑ i, Ψ y i) ∧ Function.Injective (cxRoots τ.1 P) ∧ ∀ i, ‖cxRoots τ.1 P i‖ = 1 := by
  first | exact @GlobalTheory.TrEll.realTorus_split | exact GlobalTheory.TrEll.realTorus_split | (intros; apply GlobalTheory.TrEll.realTorus_split <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.selfDualLattice_image_adelicUnitary : ∀ D : D7, ImageSt D := by
  first | exact @GlobalTheory.AdIsomImage.imageSt | exact GlobalTheory.AdIsomImage.imageSt | (intros; apply GlobalTheory.AdIsomImage.imageSt <;> assumption)
end

section

open GlobalTheory.FunObj

theorem _root_.GlobalTheory.T.linearMapChainComposite_update_add : ∀ {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)] (k : ∀ j, V j →ₗ[ℂ] V (j + 1)) (j₀ : ℕ)
    (A B : V j₀ →ₗ[ℂ] V (j₀ + 1)) (n : ℕ), j₀ < n →
    chainTo (Function.update k j₀ (A + B)) n = chainTo (Function.update k j₀ A) n + chainTo (Function.update k j₀ B) n := by
  first | exact @GlobalTheory.chainTo_update_add | exact GlobalTheory.chainTo_update_add | (intros; apply GlobalTheory.chainTo_update_add <;> assumption)
end
