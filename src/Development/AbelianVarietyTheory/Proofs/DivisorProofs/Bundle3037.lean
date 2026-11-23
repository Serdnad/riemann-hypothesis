module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2710
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2929
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtLevi
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2933
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1322
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1103
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonFibre
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle169
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2937
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2938
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth
import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle012
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernLowDim

open MeasureTheory Set GlobalTheory.ChartGlue GlobalTheory.Points

theorem det_mul_mul_eq_zero {m n : ℕ} (hmn : m < n) (P : Matrix (Fin n) (Fin m) ℂ)
    (K : Matrix (Fin m) (Fin m) ℂ) (Q : Matrix (Fin m) (Fin n) ℂ) : (P * K * Q).det = 0 := by
  by_contra h
  have hu : IsUnit (P * K * Q) := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 h)
  have h1 := Matrix.rank_of_isUnit _ hu
  have h2 : (P * K * Q).rank ≤ m :=
    ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_left _ _)).trans
      ((Matrix.rank_le_card_width P).trans (by simp))
  simp only [Fintype.card_fin] at h1
  omega

theorem chernPart_pull_of_lt : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (e e' : ℕ), IsArithVar p e → IsArithVar q e' → e < e' → ∀ (g : Y ⟶ X) (hg : g ≫ p = q), g (genericPoint Y) = genericPoint X → ∀ (N : HermLB p) (σ : k →+* ℂ) (ε : ℤˣ), ((N.pull g hg).φ σ).chernPart e' ε = 0 := by
  intro k _ X Y _ _ p q e e' hX hY hlt g hg hgen N σ ε
  obtain ⟨T, hT, hTg, hc⟩ := GlobalTheory.GenericChart.exists_isClosed_chart k X p e hX
  set Z : Set Y := (⇑g) ⁻¹' T with hZdef
  have hZ : IsClosed Z := hT.preimage g.continuous
  have hZg : genericPoint Y ∉ Z := by
    simp only [hZdef, mem_preimage, hgen]
    exact hTg
  set φ := (N.pull g hg).φ σ
  set A : Set (CxPts q σ) := {y | y.1 (IsLocalRing.closedPoint ℂ) ∈ Z} with hAdef
  have h0 : φ.chernPart e' ε A = 0 := GlobalTheory.ChernNull.chernPart_over_closed hY Z hZ hZg σ φ ε
  have hA : MeasurableSet A := by
    have : A = (ptsIn q σ ⟨Zᶜ, hZ.isOpen_compl⟩)ᶜ := by
      ext y
      simp [hAdef, mem_ptsIn]
    rw [this]
    exact (isOpen_ptsIn _).measurableSet.compl

  have hdens : ∀ (c : AlgChart q σ e') (y : CxPts q σ), y ∈ c.e.source → y ∉ A →
      c.chernDens φ y = 0 := by
    intro c y hys hyA
    have hy' : (PtsOver.map g hg (spMap σ) y).1 (IsLocalRing.closedPoint ℂ) ∉ T := by
      intro hT'
      exact hyA (show g (y.1 (IsLocalRing.closedPoint ℂ)) ∈ T from hT')
    obtain ⟨c', hc'⟩ := hc σ _ hy'
    obtain ⟨P, Q, hPQ⟩ := GlobalTheory.HessPull.hess_pull_factor k X Y p q g hg σ e' e c c' y hys hc'
    obtain ⟨K, hK⟩ := hPQ N (pick φ.isLB y) (mem_pick _ y)
    rw [AlgChart.chernDens, hK, det_mul_mul_eq_zero hlt, Complex.zero_re, mul_zero]
  have key : φ.chernPart e' ε ≤ (φ.chernPart e' ε).restrict A := iSup_le fun c => by
    have e0 : chartMeas c.e (fun y => ENNReal.ofReal ((ε : ℤ) * c.chernDens φ y)) Aᶜ = 0 := by
      rw [chartMeas_apply _ _ hA.compl]
      have hm := measurableSet_image c.e (c.e.open_source.measurableSet.inter hA.compl)
        inter_subset_left
      rw [setLIntegral_congr_fun hm (g := fun _ => 0) ?_, lintegral_zero]
      rintro _ ⟨y, hy, rfl⟩
      simp only [c.e.left_inv hy.1, hdens c y hy.1 hy.2, mul_zero, ENNReal.ofReal_zero]
    rw [← Measure.restrict_eq_self_of_ae_mem (s := A) (mem_ae_iff.2 e0)]
    exact Measure.restrict_mono le_rfl (le_iSup (fun c : AlgChart q σ e' =>
      chartMeas c.e fun y => ENNReal.ofReal ((ε : ℤ) * c.chernDens φ y)) c)
  refine Measure.measure_univ_eq_zero.1 (le_antisymm ((key univ).trans_eq ?_) zero_le)
  rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, h0]

end GlobalTheory.ChernLowDim
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernNullField

theorem chernPart_compl_null : ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ), IsProjOver p → ∀ U : X.Opens, genericPoint X ∈ U → ∀ (B : LB X) (φ : Weight p σ B) (ε : ℤˣ), φ.chernPart D ε (ptsIn p σ U)ᶜ = 0 := by
  intro k _ X _ p σ D _ U hU B φ ε
  have hcX : (ptsIn p σ U)ᶜ =
      {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ ((U : X.Opens) : Set X)ᶜ} := by
    ext y
    simp [mem_ptsIn]
  have hA : MeasurableSet (ptsIn p σ U)ᶜ := (isOpen_ptsIn U).measurableSet.compl
  have glue_null {n : ℕ} {Y ι : Type} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
      (e : ι → OpenPartialHomeomorph Y (ReciprocityTheory.L2DbarEstimates.V n))
      (ρ : ι → Y → ENNReal) {F : Set Y} (hF : MeasurableSet F)
      (h0 : ∀ i, volume ((e i) '' ((e i).source ∩ F)) = 0) :
      GlobalTheory.ChartGlue.glueMeas e ρ F = 0 := by
    have hc : ∀ i, GlobalTheory.ChartGlue.chartMeas (e i) (ρ i) F = 0 := fun i => by
      rw [GlobalTheory.ChartGlue.chartMeas_apply (e i) (ρ i) hF]
      exact setLIntegral_measure_zero _ _ (h0 i)
    have hle : GlobalTheory.ChartGlue.glueMeas e ρ ≤ (GlobalTheory.ChartGlue.glueMeas e ρ).restrict Fᶜ := by
      refine iSup_le fun i => Measure.le_iff.2 fun B hB => ?_
      rw [Measure.restrict_apply hB]
      calc GlobalTheory.ChartGlue.chartMeas (e i) (ρ i) B ≤ GlobalTheory.ChartGlue.chartMeas (e i) (ρ i) (B ∩ Fᶜ ∪ F) :=
            measure_mono fun y hy => by
              by_cases h : y ∈ F
              · exact Or.inr h
              · exact Or.inl ⟨hy, h⟩
        _ ≤ GlobalTheory.ChartGlue.chartMeas (e i) (ρ i) (B ∩ Fᶜ) + GlobalTheory.ChartGlue.chartMeas (e i) (ρ i) F := measure_union_le _ _
        _ = GlobalTheory.ChartGlue.chartMeas (e i) (ρ i) (B ∩ Fᶜ) := by rw [hc i, add_zero]
        _ ≤ GlobalTheory.ChartGlue.glueMeas e ρ (B ∩ Fᶜ) :=
            Measure.le_iff'.1 (le_iSup (fun i => GlobalTheory.ChartGlue.chartMeas (e i) (ρ i)) i) _
    have h := Measure.le_iff'.1 hle F
    rw [Measure.restrict_apply hF, inter_compl_self, measure_empty] at h
    exact nonpos_iff_eq_zero.1 h
  refine glue_null _ _ hA fun c => ?_
  rw [hcX]
  exact GlobalTheory.T.volume_complexPoints_properClosed_chart_field k X p σ D _ U.isOpen.isClosed_compl (by simpa using hU) c

end GlobalTheory.ChernNullField

end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
open GlobalTheory.Points GlobalTheory.ChartGlue

namespace GlobalTheory.SemiPosUp

open ReciprocityTheory.L2DbarEstimates (V leviV)

theorem levi_pull_nonneg {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k}
    {q : Y ⟶ Sp k} {σ : k →+* ℂ} (π : Y ⟶ X) (hπ : π ≫ p = q) {D D' : ℕ} {B : LB X}
    (φ : Weight p σ B) (hC : φ.IsCInf) (hSP : φ.SemiPosReg D) (i : (B.pull π).ι)
    (c : AlgChart q σ D') {y : CxPts q σ} (hy : y ∈ c.e.source ∩ ptsIn q σ ((B.pull π).U i))
    (c0 : AlgChart p σ D) (h0 : PtsOver.map π hπ (spMap σ) y ∈ c0.e.source) (ξ : Fin D' → ℂ) :
    0 ≤ (leviV D' (fun v => ((φ.pull π hπ).φ i (c.e.symm v) : ℂ)) (c.e y) ξ).re := by
  set m := PtsOver.map π hπ (spMap σ)
  have hm : ∀ z, (m z).1 = z.1 ≫ π := fun _ => rfl
  have him : m y ∈ ptsIn p σ (B.U (i PUnit.unit)) :=
    mem_of_mem_linComb (m := fun _ => m y) (fun _ => rfl) hy.2 PUnit.unit
  set F : V D' → V D := c0.e ∘ m ∘ c.e.symm with hFdef
  set U := c.e.target ∩ c.e.symm ⁻¹' (m ⁻¹' c0.e.source)
  have hU : IsOpen U :=
    GlobalTheory.ChartGlue.isOpen_over c.e (c0.e.open_source.preimage (continuous_of_comp hm))
  have hyU : c.e y ∈ U := GlobalTheory.ChartGlue.mem_over c.e hy.1 h0
  have hF0 : DifferentiableOn ℂ F U := AlgChart.holo_map hm c c0
  have hF : ContDiffOn ℂ 2 F U := (contDiffOn_piLp 2).2 fun a =>
    (ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn D' _ U hU
      (differentiableOn_euclidean.1 hF0 a)).of_le (by norm_cast)
  have hFy : F (c.e y) = c0.e (m y) := by
    simp only [hFdef, Function.comp_apply, c.e.left_inv hy.1]
  set g : V D → ℂ := fun v => (φ.φ (i PUnit.unit) (c0.e.symm v) : ℂ) with hgdef
  have hg : ContDiffAt ℝ 2 g (F (c.e y)) := hFy ▸
    Complex.ofRealCLM.contDiff.contDiffAt.comp _ (hC.contDiffAt c0 h0 him)
  have e : (fun v => ((φ.pull π hπ).φ i (c.e.symm v) : ℂ)) =ᶠ[𝓝 (c.e y)] g ∘ F := by
    filter_upwards [hU.mem_nhds hyU] with v hv
    have := Weight.pull_φ φ π hπ i (c.e.symm v)
    simp only [g, hFdef, Function.comp_apply, c0.e.left_inv hv.2]
    exact congrArg _ this
  rw [ReciprocityTheory.L2DbarEstimates.leviV_congr e,
    ReciprocityTheory.ChartRestriction.G.AR.Up.RGF.gc_leviV_comp D' D g F U hU _ hyU hF hg ξ, hFy]
  exact hSP (i PUnit.unit) c0 (m y) ⟨h0, him⟩ _

theorem semiPos_pull_of_etale : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D : ℕ), IsArithVar p D → IsArithVar q D → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (V : Y.Opens), (V : Set Y).Nonempty → Etale (V.ι ≫ π) → ∀ L : HermLB p, L.SemiPos D → (L.pull π hπ).SemiPos D := by
  intro k _ X Y _ _ p q D hp hq π hπ V hV he L hL
  have := hq.isDomain
  have := hq.finite
  obtain ⟨T, hT, hηT, hch⟩ := GlobalTheory.GenericChart.exists_isClosed_chart k X p D hp
  let U : X.Opens := ⟨Tᶜ, hT.isOpen_compl⟩
  obtain ⟨v, hv⟩ := hV
  obtain ⟨v', -, hv'⟩ := Flat.generalizingMap (V.ι ≫ π)
    (genericPoint_specializes ((V.ι ≫ π) ⟨v, hv⟩))
  have hW : ((π ⁻¹ᵁ U : Y.Opens) : Set Y).Nonempty := by
    refine ⟨V.ι v', ?_⟩
    show π (V.ι v') ∈ Tᶜ
    rw [← Scheme.Hom.comp_apply, hv']
    exact hηT
  intro σ
  have hσ : Function.Injective σ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
    change Ideal.comap (algebraMap ℤ k) (RingHom.ker σ) = ⊥
    rw [RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
    exact RingHom.injective_int _
  intro i
  refine GlobalTheory.SemiPosBir.PosOn.of_inter hσ (isOpen_ptsIn _) ((L.cInf σ).pull π hπ i) hW ?_
  rintro c y ⟨hyc, hyS, hyW⟩ ξ
  obtain ⟨c0, h0⟩ := hch σ (PtsOver.map π hπ (spMap σ) y) (mem_ptsIn.1 hyW)
  exact levi_pull_nonneg π hπ (L.φ σ) (L.cInf σ) (hL σ) i c ⟨hyc, hyS⟩ c0 h0 ξ

end GlobalTheory.SemiPosUp
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UPoinc.USpreadU

open GlobalTheory.Poinc.GalTrans GlobalTheory.CechPic

theorem exists_model {O Ω R' R'' : Type} [CommRing O] [IsDomain O] [IsLocalRing O] [IsNoetherianRing O]
    [IsIntegrallyClosed O] [Field Ω] [Algebra O Ω] [IsFractionRing O Ω] [CommRing R'] [CommRing R'']
    (f' : R' →+* O) (f'' : R'' →+* O) (P' : PolAV (Sp R')) (P'' : PolAV (Sp R'')) (Q : PolAV (Sp Ω))
    {b' : Q.A.left ⟶ P'.A.left} {b'' : Q.A.left ⟶ P''.A.left}
    (hb' : IsGrpPullback Q.A P'.A (spMap ((algebraMap O Ω).comp f')) b')
    (hb'' : IsGrpPullback Q.A P''.A (spMap ((algebraMap O Ω).comp f'')) b'')
    (l' : LBIso Q.L (P'.L.pull b')) (l'' : LBIso Q.L (P''.L.pull b'')) :
    ∃ (B : PolAV (Sp O)) (c' : B.A.left ⟶ P'.A.left) (c'' : B.A.left ⟶ P''.A.left) (j : Q.A.left ⟶ B.A.left),
      IsGrpPullback B.A P'.A (spMap f') c' ∧ IsGrpPullback B.A P''.A (spMap f'') c'' ∧
      LBIso B.L (P'.L.pull c') ∧ LBIso B.L (P''.L.pull c'') ∧
      IsGrpPullback Q.A B.A (spMap (algebraMap O Ω)) j ∧ j ≫ c' = b' ∧ j ≫ c'' = b'' ∧
      ∀ (t' : Sp R' ⟶ P'.A.left) (t'' : Sp R'' ⟶ P''.A.left) (w : Sp Ω ⟶ Q.A.left), t' ≫ P'.A.hom = 𝟙 _ →
        t'' ≫ P''.A.hom = 𝟙 _ → w ≫ Q.A.hom = 𝟙 _ → w ≫ b' = spMap ((algebraMap O Ω).comp f') ≫ t' →
        w ≫ b'' = spMap ((algebraMap O Ω).comp f'') ≫ t'' →
        ∃ w₀ : Sp O ⟶ B.A.left, w₀ ≫ B.A.hom = 𝟙 _ ∧ w₀ ≫ c' = spMap f' ≫ t' ∧ w₀ ≫ c'' = spMap f'' ≫ t'' := by
  obtain ⟨B, c', -, hc', lc'⟩ := GlobalTheory.PureType.exists_baseChange GlobalTheory.polBaseChange_holds (spMap f') P'
  obtain ⟨B₂, c₂, -, hc₂, lc₂⟩ := GlobalTheory.PureType.exists_baseChange GlobalTheory.polBaseChange_holds (spMap f'') P''
  obtain ⟨j, hj, lj, ej⟩ := exists_factor P' B Q (sp_comp rfl) hc' hb' lc' l'
  obtain ⟨j₂, hj₂, lj₂, ej₂⟩ := exists_factor P'' B₂ Q (sp_comp rfl) hc₂ hb'' lc₂ l''
  obtain ⟨E, hE, lE, eE⟩ := exists_iso B B₂ Q hj hj₂ lj lj₂
  have hc'' : IsGrpPullback B.A P''.A (spMap f'') (E ≫ c₂) := (hE.comp hc₂).congr (Category.id_comp _) rfl
  have lc'' := lb_comp B.isLB B₂.isLB P''.isLB lE lc₂
  have ej'' : j ≫ E ≫ c₂ = b'' := by rw [← Category.assoc, eE, ej₂]
  generalize E ≫ c₂ = c'' at hc'' lc'' ej''
  obtain ⟨_, _⟩ : QuasiCompact (spMap (algebraMap O Ω)) ∧ IsSchemeTheoreticallyDominant (spMap (algebraMap O Ω)) :=
    ExtUnique.spec_fractionRing O Ω
  have := P''.isAb.proper
  refine ⟨B, c', c'', j, hc', hc'', lc', lc'', hj, ej, ej'', fun t' t'' w ht' ht'' hw e' e'' => ?_⟩
  have w₁ : (spMap f' ≫ t') ≫ P'.A.hom = 𝟙 _ ≫ spMap f' := by rw [Category.assoc, ht']; simp
  have k₁ := hc'.1.lift_fst _ _ w₁
  have k₂ := hc'.1.lift_snd _ _ w₁
  generalize hc'.1.lift _ _ w₁ = t at k₁ k₂
  have a₁ : spMap (algebraMap O Ω) ≫ t = w ≫ j := hc'.1.hom_ext
    (by rw [Category.assoc, k₁, Category.assoc, ej, e', ← Category.assoc, sp_comp rfl])
    (by rw [Category.assoc, k₂, Category.assoc, hj.1.w, reassoc_of% hw, Category.comp_id])
  have a₂ : t ≫ c'' = spMap f'' ≫ t'' := ExtUnique.hom_ext_of_dominant P''.A.hom
    (by rw [Category.assoc, hc''.1.w, reassoc_of% k₂, Category.assoc, ht'', Category.comp_id])
    (spMap (algebraMap O Ω))
    (by rw [reassoc_of% a₁, ej'', e'', ← Category.assoc, sp_comp rfl])
  exact ⟨t, k₂, k₁, a₂⟩

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (σ : X.Ω₁ →+* X.Ω₁) (s : X.M.Z ⟶ X.M.Z), X.M.pt ≫ s = spMap σ ≫ X.M.pt → ∀ (p : ℕ) [Fact p.Prime] (y : Sp (PadicAlgCl p) ⟶ X.M.Z) (S' S'' : ThetaSys X.o₁ X.Ω₁) (ρ' : S'.Real) (ρ'' : S''.Real), S'.R ≤ X.M.O (y (closedPoint (PadicAlgCl p))) → S''.R ≤ X.M.O ((y ≫ s) (closedPoint (PadicAlgCl p))) → ∀ (y₀ : S'.R →+* PadicAlgCl p) (y₁ : S''.R →+* PadicAlgCl p), (∀ a : S'.R, y₀ a = X.M.val y a) → (∀ a : S''.R, y₁ a = X.M.val (y ≫ s) a) → ∀ (u : ρ'.UTest p y₀) (u₁ : ρ''.UTest p y₁) (u' : Sp (ratHull S'.R) ⟶ Xo.XF cf) (u'' : Sp (ratHull S''.R) ⟶ Xo.XF cf) (G : Over (Sp (ratHull S'.R))) (_ : GrpObj G) (α : G.left ⟶ ρ'.P.A.left) (β : G.left ⟶ Xo.univ.t.G.left) (G'' : Over (Sp (ratHull S''.R))) (_ : GrpObj G'') (α'' : G''.left ⟶ ρ''.P.A.left) (β'' : G''.left ⟶ Xo.univ.t.G.left), IsGrpPullback G ρ'.P.A (spMap (toRat S'.R)) α → IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β → LBIso (ρ'.P.L.pull α) (Xo.univ.t.PP.L.pull β) → IsGrpPullback G'' ρ''.P.A (spMap (toRat S''.R)) α'' → IsGrpPullback G'' Xo.univ.t.G (u'' ≫ pullback.fst _ _) β'' → LBIso (ρ''.P.L.pull α'') (Xo.univ.t.PP.L.pull β'') → ∀ (W₀ : Over (Sp X.Ω₁)) (_ : GrpObj W₀) (k₀ : W₀.left ⟶ G.left) (k₀'' : W₀.left ⟶ G''.left), IsGrpPullback W₀ G (spMap (ratHull S'.R).val.toRingHom) k₀ → IsGrpPullback W₀ G'' (spMap (σ.comp (ratHull S''.R).val.toRingHom)) k₀'' → k₀ ≫ β = k₀'' ≫ β'' → ∃ (P₀ : PolAV (Sp (PadicAlgCl p))) (a : P₀.A.left ⟶ u.A.A.left) (a' : P₀.A.left ⟶ u₁.A.A.left), IsGrpPullback P₀.A u.A.A (spMap (algebraMap (FractionRing u.V) (PadicAlgCl p))) a ∧ IsGrpPullback P₀.A u₁.A.A (spMap (algebraMap (FractionRing u₁.V) (PadicAlgCl p))) a' ∧ LBIso P₀.L (u.A.L.pull a) ∧ LBIso P₀.L (u₁.A.L.pull a') ∧ (∀ (k' : S'.Gam) (k'' : S''.Gam) (w : Sp X.Ω₁ ⟶ W₀.left), w ≫ W₀.hom = 𝟙 _ → w ≫ k₀ ≫ α = spMap S'.R.val.toRingHom ≫ (ρ'.pt k').left → w ≫ k₀'' ≫ α'' = spMap (σ.comp S''.R.val.toRingHom) ≫ (ρ''.pt k'').left → ∃ (v : Sp (PadicAlgCl p) ⟶ P₀.A.left) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) (x' : TFK (R := u₁.V) (PadicAlgCl p) ⟶ u₁.A.A), v ≫ P₀.A.hom = 𝟙 _ ∧ v ≫ a = x.left ∧ v ≫ a' = x'.left ∧ x.left ≫ u.φ = spMap y₀ ≫ (ρ'.pt k').left ∧ x'.left ≫ u₁.φ = spMap y₁ ≫ (ρ''.pt k'').left) ∧ ∀ (v : Sp (PadicAlgCl p) ⟶ P₀.A.left) (g : Sp (PadicAlgCl p) ⟶ G.left) (h : Sp (PadicAlgCl p) ⟶ G''.left), v ≫ P₀.A.hom = 𝟙 _ → g ≫ α = v ≫ a ≫ u.φ → h ≫ α'' = v ≫ a' ≫ u₁.φ → g ≫ β = h ≫ β'' := by
  intro E _ _ _ H Dw l Xo cf C X σ s hs p _ y S' S'' ρ' ρ'' h' h'' y₀ y₁ hy₀ hy₁ u u₁ u' u'' G _ α β G'' _ α'' β'' hα hβ hL hα'' hβ'' hL'' W₀ _ k₀ k₀'' hk₀ hk₀'' hkb
  haveI := X.ar.char
  set z := y (closedPoint (PadicAlgCl p)) with hz
  have hyz : Set.range y = {z} := RatModel.range_eq_singleton y _
  haveI : IsDedekindDomain X.o₁ := ArithBase.ded (Ω := X.Ω₁)
  haveI : IsNoetherianRing (X.M.O z) := X.M.isNoetherianRing_O z
  haveI : IsIntegrallyClosed (X.M.Z.presheaf.stalk z) := X.normal.isIntegrallyClosed_stalk z
  haveI : IsIntegrallyClosed (X.M.O z) := IsIntegrallyClosed.of_equiv (X.M.stalkEquiv z)

  have hU : ∀ n : ℤ, n ≠ 0 → IsUnit (n : X.M.O z) := fun n hn => by
    rw [← RatModel.val_ne_zero_iff hyz]
    have e := map_intCast (RatModel.valHom y z hyz) n
    rw [RatModel.valHom_apply] at e
    rw [e]
    exact Int.cast_ne_zero.2 hn
  have hmem : ∀ {x : X.Ω₁} (n : ℤ), n ≠ 0 → (n : X.Ω₁) * x ∈ X.M.O z → x ∈ X.M.O z := fun {x} n hn h => by
    obtain ⟨w, hw⟩ := hU n hn
    have e1 : (((w⁻¹ : (X.M.O z)ˣ) : X.M.O z) : X.Ω₁) * (n : X.Ω₁) = 1 := by
      have := congrArg (fun t : X.M.O z => (t : X.Ω₁)) w.inv_mul
      simpa [hw] using this
    have : x = (((w⁻¹ : (X.M.O z)ˣ) : X.M.O z) : X.Ω₁) * ((n : X.Ω₁) * x) := by rw [← mul_assoc, e1, one_mul]
    rw [this]; exact mul_mem (SetLike.coe_mem _) h
  have hR' : ratHull S'.R ≤ X.M.O z := fun x hx => by
    obtain ⟨n, hn, h⟩ := mem_ratHull.1 hx
    exact hmem n hn (h' h)
  have hR'' : ∀ x ∈ ratHull S''.R, σ x ∈ X.M.O z := fun x hx => by
    obtain ⟨n, hn, h⟩ := mem_ratHull.1 hx
    refine hmem n hn ?_
    have := map_mem_O hs (h'' h)
    rwa [map_mul, map_intCast] at this
  let f'Q : ratHull S'.R →+* X.M.O z := (Subalgebra.inclusion hR').toRingHom
  let f''Q : ratHull S''.R →+* X.M.O z := (σ.comp (ratHull S''.R).val.toRingHom).codRestrict (X.M.O z) fun x => hR'' x x.2
  let f' : S'.R →+* X.M.O z := f'Q.comp (toRat S'.R)
  let f'' : S''.R →+* X.M.O z := f''Q.comp (toRat S''.R)

  obtain ⟨Q, c, hc, lc⟩ := exists_pol_baseChange ρ'.P (spMap S'.R.val.toRingHom)
  have hW : IsGrpPullback W₀ ρ'.P.A (spMap S'.R.val.toRingHom) (k₀ ≫ α) :=
    (hk₀.comp hα).congr (spMap_val_toRat S'.R) rfl
  have ec : hW.1.lift c Q.A.hom hc.1.w ≫ k₀ ≫ α = c := hW.1.lift_fst _ _ _
  have ew : hW.1.lift c Q.A.hom hc.1.w ≫ W₀.hom = Q.A.hom := hW.1.lift_snd _ _ _
  generalize hW.1.lift c Q.A.hom hc.1.w = e at ec ew
  have he : IsGrpPullback Q.A W₀ (𝟙 _) e :=
    hW.cancel (hc.congr (Category.id_comp _).symm ec.symm) (by rw [ew, Category.comp_id])
  have hb'' : IsGrpPullback Q.A ρ''.P.A (spMap (σ.comp S''.R.val.toRingHom)) (e ≫ k₀'' ≫ α'') :=
    (he.comp (hk₀''.comp hα'')).congr (by rw [Category.id_comp]; exact sp_comp (RingHom.ext fun _ => rfl)) rfl
  have iso_iff {X Y : Scheme.{0}} {L : LB X} {M : LB Y} (hL : L.IsLB) (hM : M.IsLB) (φ : X ⟶ Y) :
      LBIso L (M.pull φ) ↔ cls L hL = GlobalTheory.CechPic.pull φ (cls M hM) := by
    rw [← cls_pull hM φ (pull_isLB hM φ)]
    exact (cls_eq_iff hL _).symm
  have hA : GlobalTheory.CechPic.pull α (cls ρ'.P.L ρ'.P.isLB) = GlobalTheory.CechPic.pull β (cls _ Xo.univ.t.PP.isLB) := by
    rw [← cls_pull ρ'.P.isLB α (pull_isLB ρ'.P.isLB α)]
    exact (iso_iff (pull_isLB ρ'.P.isLB α) Xo.univ.t.PP.isLB β).1 hL
  have hA'' : GlobalTheory.CechPic.pull α'' (cls ρ''.P.L ρ''.P.isLB) = GlobalTheory.CechPic.pull β'' (cls _ Xo.univ.t.PP.isLB) := by
    rw [← cls_pull ρ''.P.isLB α'' (pull_isLB ρ''.P.isLB α'')]
    exact (iso_iff (pull_isLB ρ''.P.isLB α'') Xo.univ.t.PP.isLB β'').1 hL''
  have hk : GlobalTheory.CechPic.pull k₀ (GlobalTheory.CechPic.pull β (cls _ Xo.univ.t.PP.isLB)) = GlobalTheory.CechPic.pull k₀'' (GlobalTheory.CechPic.pull β'' (cls _ Xo.univ.t.PP.isLB)) := by
    rw [← pull_comp, ← pull_comp, hkb]
  have lb'' : LBIso Q.L (ρ''.P.L.pull (e ≫ k₀'' ≫ α'')) := by
    rw [iso_iff Q.isLB ρ''.P.isLB, (iso_iff Q.isLB ρ'.P.isLB _).1 lc, ← ec]
    simp only [pull_comp]
    rw [hA, hA'', hk]

  obtain ⟨B, c', c'', j, hc', hc'', lc', lc'', hj, ej', ej'', ht⟩ :=
    exists_model f' f'' ρ'.P ρ''.P Q (b' := c) (b'' := e ≫ k₀'' ≫ α'') hc hb'' lc lb''

  let v : X.M.O z →+* PadicAlgCl p := RatModel.valHom y z hyz
  have e₀ : v.comp f' = y₀ := RingHom.ext fun x => (hy₀ x).symm
  have e₁ : v.comp f'' = y₁ := RingHom.ext fun x => ((hy₁ x).trans (val_comp hs y _ (h'' x.2))).symm
  obtain ⟨P₀, d, hd, ld⟩ := exists_pol_baseChange B (spMap v)
  have hd' : IsGrpPullback P₀.A ρ'.P.A (spMap y₀) (d ≫ c') := (hd.comp hc').congr (sp_comp e₀) rfl
  have hd'' : IsGrpPullback P₀.A ρ''.P.A (spMap y₁) (d ≫ c'') := (hd.comp hc'').congr (sp_comp e₁) rfl
  obtain ⟨a, ha, la, ea, xa⟩ := exists_to_test u P₀ hd' (lb_comp P₀.isLB B.isLB ρ'.P.isLB ld lc')
  obtain ⟨a', ha', la', ea', xa'⟩ := exists_to_test u₁ P₀ hd'' (lb_comp P₀.isLB B.isLB ρ''.P.isLB ld lc'')
  refine ⟨P₀, a, a', ha, ha', la, la', fun k' k'' w hw c1 c2 => ?_, fun v₁ g h hv₁ hg hh => ?_⟩
  · have ww : w ≫ W₀.hom = 𝟙 _ ≫ 𝟙 _ := by rw [hw]; simp
    have q1 : he.1.lift w (𝟙 _) ww ≫ e = w := he.1.lift_fst _ _ _
    have q2 : he.1.lift w (𝟙 _) ww ≫ Q.A.hom = 𝟙 _ := he.1.lift_snd _ _ _
    generalize he.1.lift w (𝟙 _) ww = wQ at q1 q2
    obtain ⟨w₀, hw₀, g', g''⟩ := ht (ρ'.pt k').left (ρ''.pt k'').left wQ (Over.w (ρ'.pt k')) (Over.w (ρ''.pt k''))
      q2 (by rw [← ec, reassoc_of% q1, c1]; rfl) (by rw [reassoc_of% q1, c2]; rfl)
    have w₂ : (spMap v ≫ w₀) ≫ B.A.hom = 𝟙 _ ≫ spMap v := by rw [Category.assoc, hw₀]; simp
    have r1 : hd.1.lift _ _ w₂ ≫ d = spMap v ≫ w₀ := hd.1.lift_fst _ _ _
    have r2 : hd.1.lift _ _ w₂ ≫ P₀.A.hom = 𝟙 _ := hd.1.lift_snd _ _ _
    generalize hd.1.lift _ _ w₂ = wK at r1 r2
    obtain ⟨x, hx⟩ := xa wK r2
    obtain ⟨x', hx'⟩ := xa' wK r2
    refine ⟨wK, x, x', r2, hx, hx', ?_, ?_⟩
    · rw [← hx, Category.assoc, ea, reassoc_of% r1, g', ← Category.assoc, sp_comp e₀]
    · rw [← hx', Category.assoc, ea', reassoc_of% r1, g'', ← Category.assoc, sp_comp e₁]

  ·
    have wm' : c' ≫ ρ'.P.A.hom = (B.A.hom ≫ spMap f'Q) ≫ spMap (toRat S'.R) := by
      rw [Category.assoc, sp_comp rfl]; exact hc'.1.w
    have wm'' : c'' ≫ ρ''.P.A.hom = (B.A.hom ≫ spMap f''Q) ≫ spMap (toRat S''.R) := by
      rw [Category.assoc, sp_comp rfl]; exact hc''.1.w
    have m1 : hα.1.lift c' _ wm' ≫ α = c' := hα.1.lift_fst _ _ _
    have m2 : hα.1.lift c' _ wm' ≫ G.hom = B.A.hom ≫ spMap f'Q := hα.1.lift_snd _ _ _
    have m1'' : hα''.1.lift c'' _ wm'' ≫ α'' = c'' := hα''.1.lift_fst _ _ _
    have m2'' : hα''.1.lift c'' _ wm'' ≫ G''.hom = B.A.hom ≫ spMap f''Q := hα''.1.lift_snd _ _ _
    generalize hα.1.lift c' _ wm' = m' at m1 m2
    generalize hα''.1.lift c'' _ wm'' = m'' at m1'' m2''
    have key : m' ≫ β = m'' ≫ β'' := by
      haveI := Xo.univ.proper
      haveI : IsSeparated Xo.s := GlobalTheory.LevelQuotRep.isSeparated_of_qproj Xo.qproj
      obtain ⟨_, _⟩ : QuasiCompact (spMap (algebraMap (X.M.O z) X.Ω₁)) ∧
          IsSchemeTheoreticallyDominant (spMap (algebraMap (X.M.O z) X.Ω₁)) :=
        ExtUnique.spec_fractionRing (X.M.O z) X.Ω₁
      haveI := B.isAb.smooth
      haveI : IsSchemeTheoreticallyDominant j := .of_isPullback hj.1.flip
      refine ExtUnique.hom_ext_of_dominant (Xo.univ.t.G.hom ≫ Xo.s ≫ terminal.from _) (terminal.hom_ext _ _) j ?_
      have n1a : (j ≫ m') ≫ α = (e ≫ k₀) ≫ α := by rw [Category.assoc, m1, ej', Category.assoc, ec]
      have n1b : (j ≫ m') ≫ G.hom = (e ≫ k₀) ≫ G.hom := by
        rw [Category.assoc, m2, reassoc_of% hj.1.w, Category.assoc, hk₀.1.w, reassoc_of% ew]
        exact congrArg (Q.A.hom ≫ ·) (sp_comp (RingHom.ext fun _ => rfl))
      have n1 : j ≫ m' = e ≫ k₀ := hα.1.hom_ext n1a n1b
      have n2a : (j ≫ m'') ≫ α'' = (e ≫ k₀'') ≫ α'' := by rw [Category.assoc, m1'', ej'', Category.assoc]
      have n2b : (j ≫ m'') ≫ G''.hom = (e ≫ k₀'') ≫ G''.hom := by
        rw [Category.assoc, m2'', reassoc_of% hj.1.w, Category.assoc, hk₀''.1.w, reassoc_of% ew]
        exact congrArg (Q.A.hom ≫ ·) (sp_comp (RingHom.ext fun _ => rfl))
      have n2 : j ≫ m'' = e ≫ k₀'' := hα''.1.hom_ext n2a n2b
      rw [reassoc_of% n1, reassoc_of% n2, hkb]
    have hg' : g ≫ α = v₁ ≫ d ≫ c' := by rw [hg, ea]
    have hh' : h ≫ α'' = v₁ ≫ d ≫ c'' := by rw [hh, ea']
    have g1 : g = v₁ ≫ d ≫ m' := hα.1.hom_ext (by rw [hg', Category.assoc, Category.assoc, m1])
      ((existsUnique_ratPoint S'.R (g ≫ α ≫ ρ'.P.A.hom)).unique (by rw [Category.assoc, hα.1.w])
        (by simp only [Category.assoc]; rw [← hα.1.w, reassoc_of% m1, ← reassoc_of% hg']))
    have h1 : h = v₁ ≫ d ≫ m'' := hα''.1.hom_ext (by rw [hh', Category.assoc, Category.assoc, m1''])
      ((existsUnique_ratPoint S''.R (h ≫ α'' ≫ ρ''.P.A.hom)).unique (by rw [Category.assoc, hα''.1.w])
        (by simp only [Category.assoc]; rw [← hα''.1.w, reassoc_of% m1'', ← reassoc_of% hh']))
    rw [g1, h1]; simp only [Category.assoc, key]

end GlobalTheory.UPoinc.USpreadU
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.balanced_posDef_finite_projective_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : UTrait Xo c), T.be ∈ balForms H.bar T.P.D.toPre.X ∧ (∀ y, y ≠ 0 → 0 < T.be y y) ∧ Module.Finite (𝓞 E) T.P.D.toPre.X ∧ Module.Projective (𝓞 E) T.P.D.toPre.X ∧ ∃ n : ℕ, Nonempty (T.P.D.toPre.X ≃ₗ[ℤ] (Fin n → ℤ)) := by
  first | exact @GlobalTheory.UPoinc.UTrait.balanced_posDef_lattice | exact GlobalTheory.UPoinc.UTrait.balanced_posDef_lattice | (intros; apply GlobalTheory.UPoinc.UTrait.balanced_posDef_lattice <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

theorem _root_.GlobalTheory.T.exists_open_compactification_generic_subset_moduli : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∃ W : C.Z.Opens, Set.range C.i ⊆ W ∧ ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ C.Z), Set.range (gPt p ≫ y) ⊆ W → Set.range (gPt p ≫ y) ⊆ Set.range C.i := by
  first | exact @GlobalTheory.UPoinc.exists_open_generic_subset_moduli | exact GlobalTheory.UPoinc.exists_open_generic_subset_moduli | (intros; apply GlobalTheory.UPoinc.exists_open_generic_subset_moduli <;> assumption)
end
