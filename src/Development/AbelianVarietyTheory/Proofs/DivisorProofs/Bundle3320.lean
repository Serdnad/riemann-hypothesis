module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle019
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3239
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2912
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3310
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3240
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1492
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1304
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3311
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle048
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle191
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3316
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2905
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3299
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2694
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2706
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle689
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBigThetaSysWithAction
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle108
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelShapePrimitivityPullbackDescent
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle070
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealisedThetaSystemNormalLevelModel
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2795
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle075
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle071
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3312
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3270
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3313
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3104

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.finite_section_translates_cover_semiAbelian : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ N : Near π G', N.Law → ∃ (n : ℕ) (a : Fin n → (Sp R ⟶ N.U.left)) (x : Fin n → (Over.mk (𝟙 S) ⟶ G')), (∀ i, a i ≫ N.U.hom = 𝟙 _ ∧ N.Pt (𝟙 S) (π ≫ a i) (x i).left) ∧ ∀ (Ω : Type) [Field Ω] (s : Sp Ω ⟶ S) (g : Over.mk s ⟶ G'), Set.range g.left ⊆ Set.range N.u ∨ ∃ i, Set.range (g * (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫ x i).left ⊆ Set.range N.u := by
  first | exact @GlobalTheory.Mum.cover_by_translates | exact GlobalTheory.Mum.cover_by_translates | (intros; apply GlobalTheory.Mum.cover_by_translates <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CycPair

theorem cInfAt_log_nsq_add : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (M : MLine p σ) (s : M.B.Sec) (δ : ℝ), 0 < δ → ∀ y, CInfAt (fun y => Real.log (M.φ.nsq (secVal p σ s) y + δ)) y := by
  intro k _ X p σ M s δ hδ y
  obtain ⟨W, ι, _, g, F, O, h₁, h₂, h₃, h₄, h₅⟩ := (GlobalTheory.T.smoothWeightedLineBundle_logSectionNorm_properties k X p σ M s).2.2.1 y
  refine ⟨W, ι, inferInstance, g, fun w => Real.log (F w + δ), O ∩ F ⁻¹' Set.Ioi (-δ), h₁,
    h₄.continuousOn.isOpen_inter_preimage h₂ isOpen_Ioi, ⟨h₃, ?_⟩, ?_, ?_⟩
  · have h0 := M.φ.nsq_nonneg (secVal p σ s) y
    rw [h₅.eq_of_nhds] at h0
    exact lt_of_lt_of_le (neg_neg_of_pos hδ) h0
  · refine ((h₄.mono Set.inter_subset_left).add contDiffOn_const).log fun w hw => ?_
    have : -δ < F w := hw.2
    linarith
  · filter_upwards [h₅] with z hz
    rw [hz]

theorem int_cons_addFn : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ), IsProjOver p → ∀ (e : ℕ) (L : Fin e → MLine p σ) (A : MLine p σ) (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y) (f : CxPts p σ → ℝ), Intg (Fin.cons A L : Fin (e + 1) → MLine p σ) f → Intg (Fin.cons (MLine.ofFun u hu) L : Fin (e + 1) → MLine p σ) f → Intg (Fin.cons (A.addFn u hu) L : Fin (e + 1) → MLine p σ) f ∧ Mix.int (Fin.cons (A.addFn u hu) L : Fin (e + 1) → MLine p σ) f = Mix.int (Fin.cons A L : Fin (e + 1) → MLine p σ) f + Mix.int (Fin.cons (MLine.ofFun u hu) L : Fin (e + 1) → MLine p σ) f := by
  intro k _ X p σ hp e L A u hu f hA hU
  have hc := GlobalTheory.T.smoothWeightedLineBundle_isometry_calculus k X X p p σ (𝟙 X) (Category.id_comp p)
  have hpart := GlobalTheory.T.mixedChernFormSignedPartMeasure_eq_of_isometric_projOver k X p σ hp (e + 1) (Fin.cons (A.addFn u hu) L)
    (Fin.cons (A.tens (MLine.ofFun u hu)) L) (Fin.cases (hc.2.2.2.2.1 A u hu) fun i => hc.1 (L i))
  have h := GlobalTheory.T.mixedChernIntegral_additive_in_factor k X p σ hp (e + 1) (Fin.cons A L) 0 A (MLine.ofFun u hu) f
  simp only [Fin.update_cons_zero] at h
  have h' := h hA hU
  rw [← h'.2]
  have h1 := h'.1
  simp only [Intg, Mix.int, hpart] at h1 ⊢
  exact ⟨h1, trivial⟩

theorem int_logSec_le : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp F) (σ : F →+* ℂ), IsProjOver p → ∀ (D : ℕ) (L : Fin D → MLine p σ), (∀ i, (L i).φ.SemiPosReg D) → ∀ (M : MLine p σ) (s : M.B.Sec), genericPoint X ∈ nonzeroLocus s → ∀ δ : ℝ, 0 < δ → Intg L (M.logSec s) → Intg L (fun y => Real.log (M.φ.nsq (secVal p σ s) y + δ)) → Mix.int L (M.logSec s) ≤ Mix.int L (fun y => Real.log (M.φ.nsq (secVal p σ s) y + δ)) / 2 := by
  intro F _ X _ p σ hp D L hL M s hs δ hδ h₁ h₂
  haveI : SecondCountableTopology (CxPts p σ) := CxPts.secondCountableTopology_of_isProjOver σ hp
  have hneg := GlobalTheory.T.mixedChernFormSignedPartMeasure_neg_eq_zero_semiPositive F X p σ D L hL
  have hnull := GlobalTheory.T.mixedChernFormSignedPartMeasure_compl_open_genericPoint_eq_zero F X p σ σ.injective hp D L 1 _ hs
  have hpos := (GlobalTheory.T.smoothWeightedLineBundle_logSectionNorm_properties F X p σ M s).2.1
  simp only [Mix.int, hneg, integral_zero_measure, sub_zero]
  rw [← integral_div]
  refine integral_mono_ae h₁.1 (h₂.1.div_const 2) ?_
  have hae : ∀ᵐ y ∂part L 1, y ∈ ptsIn p σ (nonzeroLocus s) := hnull
  filter_upwards [hae] with y hy
  have h0 := (hpos y).2 hy
  have := Real.log_le_log h0 (le_add_of_nonneg_right hδ.le)
  simp only [MLine.logSec]
  linarith

theorem mem_of_mult_divOfSec_ne_zero {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] {A : LB X} (hA : A.IsLB) (s : A.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (U : X.Opens) (h : ∀ z : X, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ U) (z : X) (hz : (divOfSec hA s hs).mult z ≠ 0) : z ∈ U :=
  (h z (CartierDiv.coheight_eq_one_of_mult_ne_zero hz)).resolve_left fun h' =>
    notMem_supp_divOfSec.2 h' (CartierDiv.mem_supp_of_mult_ne_zero hz)

theorem side_le : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → ∀ (L : Fin e → MLine p σ) (M N : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (t : N.B.Sec) (ht : genericPoint X ∈ nonzeroLocus t), (∀ z : X, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t) → (∀ i, (L i).φ.SemiPosReg (e + 1)) → N.φ.SemiPosReg (e + 1) → side N L (M.logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs) ≤ side M L (N.logSec t) (M.logSec s) (divOfSec N.φ.isLB t ht) := by
  intro hP F _ X _ _ p σ e hproj hdim L M N s hs t ht hcod hL hN
  let δ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hδ : ∀ n, 0 < δ n := fun n => by positivity
  let v : ℕ → CxPts p σ → ℝ := fun n y => Real.log (N.φ.nsq (secVal p σ t) y + δ n)
  let u : ℕ → CxPts p σ → ℝ := fun m y => Real.log (M.φ.nsq (secVal p σ s) y + δ m)
  have hv : ∀ n y, CInfAt (v n) y := fun n => cInfAt_log_nsq_add F X p σ N t (δ n) (hδ n)
  have hu : ∀ m y, CInfAt (u m) y := fun m => cInfAt_log_nsq_add F X p σ M s (δ m) (hδ m)
  have cu : ∀ m, Continuous (u m) := fun m => continuous_iff_continuousAt.2 fun y => (hu m y).continuousAt
  have fin : ∀ (L' : Fin (e + 1) → MLine p σ) (f : CxPts p σ → ℝ), Continuous f → Intg L' f :=
    fun L' => (GlobalTheory.T.mixedChernMeasure_finite_integrable_projective hP F X p σ (e + 1) hproj hdim L').2
  have lint : ∀ L' : Fin (e + 1) → MLine p σ, Intg L' (M.logSec s) :=
    fun L' => GlobalTheory.T.log_norm_section_integrable_mixedChern_projective hP F X p σ (e + 1) hproj hdim L' M s hs
  have supS : ∀ z, (divOfSec M.φ.isLB s hs).mult z ≠ 0 → z ∈ nonzeroLocus t :=
    mem_of_mult_divOfSec_ne_zero M.φ.isLB s hs _ hcod
  have supT : ∀ z, (divOfSec N.φ.isLB t ht).mult z ≠ 0 → z ∈ nonzeroLocus s :=
    mem_of_mult_divOfSec_ne_zero N.φ.isLB t ht _ fun z hz => (hcod z hz).symm
  have key : ∀ m n, Mix.int (Fin.cons N L : Fin (e + 1) → MLine p σ) (M.logSec s)
      + Mix.int (Fin.cons (MLine.ofFun (v n) (hv n)) L : Fin (e + 1) → MLine p σ) (M.logSec s) ≤
      (Mix.int (Fin.cons N L : Fin (e + 1) → MLine p σ) (u m)
        + Mix.int (Fin.cons (MLine.ofFun (u m) (hu m)) L : Fin (e + 1) → MLine p σ) (v n)) / 2 := by
    intro m n
    obtain ⟨-, h1⟩ := int_cons_addFn F X p σ hproj e L N (v n) (hv n) (M.logSec s) (lint _) (lint _)
    obtain ⟨-, h2⟩ := int_cons_addFn F X p σ hproj e L N (v n) (hv n) (u m) (fin _ _ (cu m)) (fin _ _ (cu m))
    have hsp : ∀ i, ((Fin.cons (N.addFn (v n) (hv n)) L : Fin (e + 1) → MLine p σ) i).φ.SemiPosReg (e + 1) :=
      Fin.cases (GlobalTheory.T.semiPos_add_log_normSq_section_add_pos F X p σ (e + 1) N hN t (δ n) (hδ n)).2 hL
    have h3 := int_logSec_le F X p σ hproj (e + 1) _ hsp M s hs (δ m) (hδ m) (lint _) (fin _ _ (cu m))
    have h4 := GlobalTheory.T.mixedIntegral_ddc_pairing_symm_projective hP F X p σ e hproj hdim L (v n) (u m) (hv n) (hu m)
    rw [← h1]
    refine h3.trans (le_of_eq ?_)
    change Mix.int _ (u m) / 2 = _
    rw [h2, h4]
  have ps : ∀ n, 2 * Mix.int (Fin.cons (MLine.ofFun (v n) (hv n)) L : Fin (e + 1) → MLine p σ) (M.logSec s) =
      ∑ᶠ z, ((divOfSec M.φ.isLB s hs).mult z : ℝ) * cycInt L (v n) z
        - Mix.int (Fin.cons M L : Fin (e + 1) → MLine p σ) (v n) :=
    fun n => GlobalTheory.T.poincareLelong_formula_section_projective hP F X p σ e hproj hdim L M s hs (v n) (hv n)
  have pt : ∀ m, 2 * Mix.int (Fin.cons (MLine.ofFun (u m) (hu m)) L : Fin (e + 1) → MLine p σ) (N.logSec t) =
      ∑ᶠ z, ((divOfSec N.φ.isLB t ht).mult z : ℝ) * cycInt L (u m) z
        - Mix.int (Fin.cons N L : Fin (e + 1) → MLine p σ) (u m) :=
    fun m => GlobalTheory.T.poincareLelong_formula_section_projective hP F X p σ e hproj hdim L N t ht (u m) (hu m)
  have limT := GlobalTheory.T.tendsto_regularisedLogNorm_mixedMeasure_divisors hP F X p σ e hproj hdim N t
  have limS := GlobalTheory.T.tendsto_regularisedLogNorm_mixedMeasure_divisors hP F X p σ e hproj hdim M s
  have l1 : Tendsto (fun n => ∑ᶠ z, ((divOfSec M.φ.isLB s hs).mult z : ℝ) * cycInt L (v n) z) atTop
      (𝓝 (2 * ∑ᶠ z, ((divOfSec M.φ.isLB s hs).mult z : ℝ) * cycInt L (N.logSec t) z)) :=
    limT.2 L _ supS
  have l2 : Tendsto (fun n => Mix.int (Fin.cons M L : Fin (e + 1) → MLine p σ) (v n)) atTop
      (𝓝 (2 * Mix.int (Fin.cons M L : Fin (e + 1) → MLine p σ) (N.logSec t))) := limT.1 ht _
  have l3 : ∀ m, Tendsto (fun n => Mix.int (Fin.cons (MLine.ofFun (u m) (hu m)) L : Fin (e + 1) → MLine p σ) (v n))
      atTop (𝓝 (2 * Mix.int (Fin.cons (MLine.ofFun (u m) (hu m)) L : Fin (e + 1) → MLine p σ) (N.logSec t))) :=
    fun m => limT.1 ht _
  have l4 : Tendsto (fun m => ∑ᶠ z, ((divOfSec N.φ.isLB t ht).mult z : ℝ) * cycInt L (u m) z) atTop
      (𝓝 (2 * ∑ᶠ z, ((divOfSec N.φ.isLB t ht).mult z : ℝ) * cycInt L (M.logSec s) z)) :=
    limS.2 L _ supT
  have step : ∀ m, side N L (M.logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs)
      - Mix.int (Fin.cons M L : Fin (e + 1) → MLine p σ) (N.logSec t) ≤
      (∑ᶠ z, ((divOfSec N.φ.isLB t ht).mult z : ℝ) * cycInt L (u m) z) / 2 := by
    intro m
    have lim1 : Tendsto (fun n => Mix.int (Fin.cons N L : Fin (e + 1) → MLine p σ) (M.logSec s)
        + Mix.int (Fin.cons (MLine.ofFun (v n) (hv n)) L : Fin (e + 1) → MLine p σ) (M.logSec s)) atTop
        (𝓝 (side N L (M.logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs)
          - Mix.int (Fin.cons M L : Fin (e + 1) → MLine p σ) (N.logSec t))) := by
      have e1 : (fun n => Mix.int (Fin.cons N L : Fin (e + 1) → MLine p σ) (M.logSec s)
          + Mix.int (Fin.cons (MLine.ofFun (v n) (hv n)) L : Fin (e + 1) → MLine p σ) (M.logSec s)) =
          fun n => Mix.int (Fin.cons N L : Fin (e + 1) → MLine p σ) (M.logSec s)
            + (∑ᶠ z, ((divOfSec M.φ.isLB s hs).mult z : ℝ) * cycInt L (v n) z
              - Mix.int (Fin.cons M L : Fin (e + 1) → MLine p σ) (v n)) / 2 :=
        funext fun n => by rw [← ps n]; ring
      rw [e1]
      convert tendsto_const_nhds.add ((l1.sub l2).div_const 2) using 2
      simp only [side]
      ring
    have lim2 := (tendsto_const_nhds (x := Mix.int (Fin.cons N L : Fin (e + 1) → MLine p σ) (u m))).add (l3 m)
    have h := le_of_tendsto_of_tendsto' lim1 (lim2.div_const 2) (key m)
    have := pt m
    linarith
  have h := ge_of_tendsto' (l4.div_const 2) step
  simp only [side] at h ⊢
  linarith

end GlobalTheory.CycPair
end
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

theorem _root_.GlobalTheory.T.integral_chernFormPoly_eq_intersectionNumber : GlobalTheory.Published.ChernDegree → ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (κ : Type) [Fintype κ] (Δ : κ → X.Dv) (L : κ → LB X.X) (r : ∀ a, (L a).ι → X.Fnˣ) (ψ : ∀ a, Weight X.str σ (L a)), (∀ a, Presents (Δ a) (L a) (r a) ∧ (ψ a).IsCInf) → ∀ P : MvPolynomial κ ℝ, (atlas X σ).integral (evalF (atlas X σ) (fun a => c1W (ψ a)) P) = X.interPoly Δ P := by
  first | exact @GlobalTheory.ChernLine.integral_evalF_c1W_eq_interPoly | exact GlobalTheory.ChernLine.integral_evalF_c1W_eq_interPoly | (intros; apply GlobalTheory.ChernLine.integral_evalF_c1W_eq_interPoly <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

theorem _root_.GlobalTheory.T.exists_chart_siegelLevelCover_sharpTheta : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ η ∈ genericPoints F.X, ∃ ℓ : ℕ, ℓ.Prime ∧ Odd ℓ ∧ ∀ j : ℕ, 1 ≤ j → ∃ (o Ω : Type) (_ : CommRing o) (_ : Field Ω) (_ : Algebra o Ω) (_ : ArithBase o Ω) (κ : cycAway n →+* o) (R : Subalgebra o Ω) (J : Type) (b : TBase o ((ℓ ^ j) ^ 2)) (t : TObj (8 * g) ((ℓ ^ j) ^ 2) J b (spMap (algebraMap o R))) (w w' : J) (x : Sp R ⟶ F.X), R.FG ∧ (∀ y : Ω, ∃ a ∈ R, ∃ c ∈ R, y = a / c) ∧ t.Prim w w' ∧ (∀ (T : Scheme.{0}) (f : T ⟶ Sp R) (P : PolAV T) (φ : P.A.left ⟶ t.A.left), IsGrpPullback P.A t.A f φ → LBIso P.L (t.L.pull φ) → SharpOver F W P (f ≫ x)) ∧ (∀ w, (spMap R.val.toRingHom ≫ x) w = η) ∧ spMap R.val.toRingHom ≫ x ≫ F.s = spMap ((algebraMap o Ω).comp κ) ∧ κ.Finite ∧ ((spMap R.val.toRingHom ≫ x).stalkMap (genericPoint (Sp Ω))).hom.Finite := by
  first | exact @GlobalTheory.PoincChart.exists_chart | exact GlobalTheory.PoincChart.exists_chart | (intros; apply GlobalTheory.PoincChart.exists_chart <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_thetaMap_eighthPower_siegelModuli : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (P : PolAV F.X) (rig : LB.Gen (P.L.pull (eSec P.A))) (m : ℕ), P.g = 8 * g → GlobalTheory.Poinc.SharpOver F W P (𝟙 F.X) → rig.IsGen → Odd m → 3 ≤ m → IsUnit (m : cycAway n) → ∃ (N : ℕ) (f : F.X ⟶ PSpace (cycAway n) N), ThAt F W P rig m f := by
  first | exact @GlobalTheory.SiegTh.exists_thAt | exact GlobalTheory.SiegTh.exists_thAt | (intros; apply GlobalTheory.SiegTh.exists_thAt <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_realisedThetaSystem_normalLevelModel : ∀ (ℓ : ℕ), ℓ.Prime → Odd ℓ → ∀ j₀ : ℕ, ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ℓ ∣ n → (∃ bas : (Fin (2 * (8 * g)) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin g ⊕ Fin g → ℤ)), IsSharpBasis W bas) → ∃ (o Ω : Type) (_ : CommRing o) (_ : Field Ω) (_ : Algebra o Ω) (_ : ArithBase o Ω) (β : cycAway n →+* o) (S : ThetaSys o Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X) (Y : RatModel o Ω) (q : Y.Z ⟶ F.X), SysAt F W β S ρ u ∧ LevAt F β u Y q ∧ S.Big ∧ Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j, x = S.th j / S.th i})) Ω := by
  first | exact @GlobalTheory.SiegLevSys.exists_sys_levModel | exact GlobalTheory.SiegLevSys.exists_sys_levModel | (intros; apply GlobalTheory.SiegLevSys.exists_sys_levModel <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Poinc.SetupCov
open GlobalTheory.PoincChart

theorem chartAt : ∀ (n N : ℕ) (X Y Z : Scheme.{0}) (sX : X ⟶ Sp (cycAway n)) (sY : Y ⟶ Sp (cycAway N)) (q : Y ⟶ X) (i : X ⟶ Z), IsOpenImmersion i → 0 < n → 0 < N → Smooth sX → Smooth sY → IsFinite q → Etale q → Surjective q → ∀ (K : Type) [Field K] (y' : Sp K ⟶ Y), ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra (cycAway N) Ω) (_ : ArithBase (cycAway N) Ω) (R : Subalgebra (cycAway N) Ω) (x : Sp R ⟶ Y) (yR : Sp K ⟶ Sp R) (V : Z.Opens) (f : Sp R ⟶ V), R.FG ∧ (∀ z : Ω, ∃ a ∈ R, ∃ c ∈ R, z = a / c) ∧ IsIntegrallyClosed R ∧ x ≫ sY = spMap (algebraMap (cycAway N) R) ∧ yR ≫ x = y' ∧ (∀ w, (spMap R.val.toRingHom ≫ x ≫ q) w ∈ genericPoints X) ∧ ((spMap R.val.toRingHom ≫ x ≫ q ≫ i).stalkMap (genericPoint (Sp Ω))).hom.Finite ∧ IsAffineOpen V ∧ IsFinite f ∧ f ≫ V.ι = x ≫ q ≫ i := GlobalTheory.T.exists_finite_etale_cover_chart_at_field_point

theorem modelAt : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (Z : Scheme.{0}) (π : M.Z ⟶ Z), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → IsFinite π → ∀ (R : Subalgebra o Ω), (∀ z : Ω, ∃ a ∈ R, ∃ c ∈ R, z = a / c) → IsIntegrallyClosed R → ∀ (V : Z.Opens) (f : Sp R ⟶ V), IsAffineOpen V → IsFinite f → M.pt ≫ π = spMap R.val.toRingHom ≫ f ≫ V.ι → ∃ φ : Sp R ⟶ M.Z, φ ≫ π = f ≫ V.ι ∧ ∀ (P : Sp R) (a b : R), b ∉ P.asIdeal → (a : Ω) / (b : Ω) ∈ M.O (φ P) := GlobalTheory.T.exists_finite_chart_map_to_normal_finite_model

theorem exists_big_ge (g n : ℕ) (hn : 2 ≤ n) (B : ℕ) : ∃ k j₁ : ℕ, 2 ≤ k ∧ B ≤ (n ^ k) ^ 2 ∧ 1 ≤ j₁ ∧ ∀ j ≥ j₁,
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω),
      S.g = g → S.N = (n ^ k) ^ 2 → S.r = n ^ j → S.Big := by
  have lt : ∀ m : ℕ, m < n ^ m := fun m => Nat.lt_pow_self hn
  obtain ⟨k₀, hk₀⟩ := exists_nat_gt (1 + 2 * (g : ℝ) * (2 : ℝ) ^ ((g : ℝ) / 2))
  set K := max k₀ B with hK
  set N := (n ^ (K + 2)) ^ 2 with hN
  have hN₁ : K + 2 < N := (lt _).trans_le (Nat.le_self_pow two_ne_zero _)
  obtain ⟨j₀, hj₀⟩ := exists_nat_gt
    (2 * ((N ^ g * g.factorial : ℕ) : ℝ) * ((g : ℝ) * (3 / 2 : ℝ) ^ g * (2 : ℝ) ^ ((g : ℝ) / 2 - 1)))
  refine ⟨K + 2, j₀ + 6 * (N ^ g * g.factorial) + 1, by omega, ?_, by omega, fun j hj o Ω _ _ _ S hg hS hr => ?_⟩
  · have : B ≤ K := le_max_right _ _
    omega
  have hj' := lt j
  unfold ThetaSys.Big
  rw [hg, hS, hr, ← hN]
  have hk₀K : k₀ ≤ K := le_max_left _ _
  refine ⟨hk₀.trans (by exact_mod_cast (by omega : k₀ < N)), ?_, ?_⟩
  · rw [Nat.cast_mul (n ^ j)]
    exact mul_lt_mul_of_pos_right (hj₀.trans (by exact_mod_cast (by omega : j₀ < n ^ j)))
      (by exact_mod_cast (by omega : 0 < N))
  · exact lt_of_lt_of_le (by omega) (Nat.le_mul_of_pos_right _ (by omega))



theorem exists_setup_cov : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ l : ℕ, l.Prime → l ∣ n → ∀ j₀ : ℕ, ∃ (j : ℕ) (Y : Scheme.{0}) (q : Y ⟶ F.X), j₀ ≤ j ∧ IsFinite q ∧ Surjective q ∧ ∀ (K : Type) [Field K] (y' : Sp K ⟶ Y), ∃ (X₁ : Setup F W i) (yM : Sp K ⟶ X₁.M.Z), X₁.S.r * X₁.S.N = (l ^ j) ^ 2 ∧ yM ≫ X₁.π = y' ≫ q ≫ i ∧ ∀ a ∈ X₁.S.R, a ∈ X₁.M.O (yM (closedPoint K)) := by
  intro g hg n hn ho F Z z i _ hproj hZn hiz hden W hW hT l hl hln j₀
  have hlo : Odd l := Odd.of_dvd_nat ho hln
  obtain ⟨k, j₁, hk, -, hj₁, big⟩ := exists_big_ge (8 * g) l hl.two_le 0
  obtain ⟨κ, F', q, ⟨-, hζ, hfin, -, -⟩, ⟨hqs, hqfin, hqet, hqsurj, hq⟩, -⟩ :=
    GlobalTheory.SiegLevCover.exists_levelCover g n l (2 * (j₀ + j₁ + k)) F hg hn ho hl hln (by omega)
  refine ⟨j₀ + j₁ + k, F'.X, q, by omega, hqfin, hqsurj, fun K _ y' => ?_⟩
  have hl3 : 3 ≤ l := by
    have h2 := hl.two_le
    have : l ≠ 2 := fun e => by rw [e] at hlo; exact absurd hlo (by decide)
    omega
  have hk3 : 3 ≤ (l ^ (2 * (j₀ + j₁ + k))) ^ 2 :=
    le_trans (le_trans hl3 (Nat.le_self_pow (by omega) _)) (Nat.le_self_pow (by omega) _)
  have hko : Odd ((l ^ (2 * (j₀ + j₁ + k))) ^ 2) := hlo.pow.pow
  obtain ⟨bas, hbas⟩ := exists_isSharpBasis g W hW
  obtain ⟨a, w, w', hw, hw', hs⟩ := EighthPowerFactor.exists_matrices hW.2
  obtain ⟨b, t', hp', hsh'⟩ := exists_sharpOver_cover g n _ F F' κ q (by omega) hk3 hko hζ hqs hq W _ a w w' bas
    hW hbas hw hw' hs
  haveI := F.smooth
  haveI : Smooth F.s := SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) F.s
  haveI := F'.smooth
  haveI : Smooth F'.s := SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) F'.s
  obtain ⟨Ω, _, _, _, R, x, yR, V, f, hRfg, hfrac, hRic, hxs, hyR, hgen, hst, hV, hf, hfV⟩ :=
    chartAt n (n * (l ^ (2 * (j₀ + j₁ + k))) ^ 2) F.X F'.X Z F.s F'.s q i inferInstance (by omega)
      (Nat.mul_pos (by omega) (pow_pos (pow_pos hl.pos _) _)) inferInstance inferInstance hqfin hqet hqsurj K y'
  obtain ⟨t, ht⟩ := GlobalTheory.tObj_pull _ (8 * g) _ _ b F'.X (Sp R) F'.s (spMap (algebraMap _ R)) x t' hxs
  have hp : t.Prim w w' :=
    (GlobalTheory.shape_prim_pull_and_descend _ _ _ _ b (fun _ => 0) 0 w w' _ _ _ _ x t' t ht).2.1 hp'
  obtain ⟨ψ, hψ, hψL, -, -⟩ := ht
  have hsh : SharpOver F W t.pol (x ≫ q) := sharpOver_pullback _ _ _ _ F W _ _ t'.pol t.pol q x ψ hsh' hψ hψL
  have := t.ab.comm
  have hS : ZH.HypS t.A t.L := ⟨t.act w, t.act w', t.hom w, t.hom w', hp.1, hp.2.2, hp.2.1⟩
  have hu : IsUnit (l : cycAway (n * (l ^ (2 * (j₀ + j₁ + k))) ^ 2)) := isUnit_of_dvd_unit (Nat.cast_dvd_cast
    ((dvd_pow_self l (by omega : 2 * (j₀ + j₁ + k) ≠ 0)).trans (dvd_pow_self _ two_ne_zero))) b.unit
  haveI : NeZero ((l ^ (2 * (j₀ + j₁ + k))) ^ 2) := ⟨by have := hl.pos; positivity⟩
  obtain ⟨lev₀, -⟩ := GlobalTheory.ThetaSysOfObj.exists_level R t
  have e : (l ^ (2 * (j₀ + j₁ + k))) ^ 2 = (l ^ (2 * (j₀ + j₁)) * (l ^ k) ^ 2) ^ 2 := by ring
  obtain ⟨lev, -⟩ : ∃ lev : Out.Level t.pol ((l ^ (2 * (j₀ + j₁)) * (l ^ k) ^ 2) ^ 2)
      (unitOn (Units.map (algebraMap _ R).toMonoidHom b.ζ)), True := by
    rw [← e]; exact ⟨lev₀, trivial⟩
  obtain ⟨S, ρ, hR, φ, hreg, -, hNS, hrS, hgS, hpb, hL, -⟩ :=
    GlobalTheory.T.exists_thetaSystem_realisation_regular_at_prime _ Ω R hRfg hfrac (yR (IsLocalRing.closedPoint K)).asIdeal (yR (IsLocalRing.closedPoint K)).isPrime t.pol l k (2 * (j₀ + j₁))
      b.ζ hl hlo hk (by omega) hu hS lev
  haveI : IsDedekindDomain (cycAway n) := GlobalTheory.CycAwayReg.isDedekindDomain_cycAway _
  haveI : IsProper z := ((isProjOver_iff_isProper_and_exists_isAmpleLB z).1 hproj).1
  have hbase : spMap R.val.toRingHom ≫ x ≫ q ≫ F.s = spMap ((algebraMap _ Ω).comp κ) := by
    rw [hqs, ← Category.assoc x, hxs]
    simp only [spMap, ← Spec.map_comp]
    rfl
  have hp0 : (spMap R.val.toRingHom ≫ x ≫ q ≫ i) ≫ z = spMap ((algebraMap _ Ω).comp κ) := by
    simp only [Category.assoc, hiz]
    exact hbase
  obtain ⟨M, π, hMn, hπ, hcomp⟩ := GlobalTheory.T.exists_normal_model_normalisation_dedekind (cycAway n) _ Ω κ ((IsFinite.SpecMap_iff _).1 hfin) Z z
    inferInstance inferInstance inferInstance _ hp0 hst
  obtain ⟨φM, hφπ, hφreg⟩ := modelAt _ Ω M Z π hMn hπ R hfrac hRic V f hV hf (by rw [hcomp, hfV])
  have ef : spMap S.R.val.toRingHom ≫ spMap (Subalgebra.inclusion hR).toRingHom = spMap R.val.toRingHom :=
    (Spec.map_comp (CommRingCat.ofHom (Subalgebra.inclusion hR).toRingHom) (CommRingCat.ofHom S.R.val.toRingHom)).symm
  have hsharp : SharpOver F W ρ.P (spMap (Subalgebra.inclusion hR).toRingHom ≫ x ≫ q) :=
    sharpOver_pullback _ _ _ _ F W _ _ t.pol ρ.P (x ≫ q) _ φ hsh hpb hL
  refine ⟨Setup.mk _ Ω S ρ (big (2 * (j₀ + j₁)) (by omega) _ Ω S (hgS.trans ?_) hNS hrS)
    (spMap (Subalgebra.inclusion hR).toRingHom ≫ x ≫ q) hsharp
    (fun w => by rw [← Category.assoc, ef]; exact hgen w) M (GlobalTheory.IsNormalScheme.of_pred hMn) π hπ
    (by rw [hcomp]; simp only [Category.assoc]; rw [← Category.assoc (spMap S.R.val.toRingHom), ef]) hg hn ho z hproj (GlobalTheory.IsNormalScheme.of_pred hZn) inferInstance hiz hden
    hW hT κ (by rw [Category.assoc, ← Category.assoc (spMap S.R.val.toRingHom), ef]; exact hbase),
    yR ≫ φM, ?_, ?_, ?_⟩
  · rfl
  · show S.r * S.N = _
    rw [hrS, hNS]; ring
  · show (yR ≫ φM) ≫ π = _
    rw [Category.assoc, hφπ, hfV, ← Category.assoc, hyR]
  · intro a ha
    change a ∈ S.R at ha
    obtain ⟨a', b', hb', e⟩ := hreg a ha
    change a ∈ M.O ((yR ≫ φM) (IsLocalRing.closedPoint K))
    rw [e]
    exact hφreg _ a' b' hb'

end GlobalTheory.Poinc.SetupCov
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.Eq8.PeriodsEighth

theorem main : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X) c pr, SharpBy F W ρ.P u c pr → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.Over₀ M U₀ → ∀ (V : M.Z.Opens) (v : V.toScheme ⟶ F.X), (∀ x : Sp Ω ⟶ V.toScheme, x ≫ V.ι = M.pt → x ≫ v = spMap S.R.val.toRingHom ≫ u) → ∀ (f : Fin 8 → Fin 8 → (FinalForm.G ⟶ FinalForm.G)), (∀ a b, MatOn FinalForm pr a b (f a b)) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ M.Z) (D : DegPre R) (m : Fin 8 → Fin 8 → (D.X →+ D.X)) (T : Trait F) (ψ : R →+* T.V), ThroughU M V v (𝟙 F.X) T (spMap ψ ≫ ξ) → ∀ (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G'] (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Sp (FractionRing T.V))) (U' : Unif (maximalIdeal T.V) D' A' G') (gm : G'.left ⟶ FinalForm.G.left) (ι : D.X ≃+ D'.toPre.X), IsSemiAbelian G' → IsGrpPullback G' FinalForm.G (spMap ψ ≫ ξ) gm → LBIso U'.LG.L (FinalForm.L.L.pull gm) → CoordMap D D'.toPre ψ ι.toAddMonoidHom → (∀ a b, ∃ f' : G' ⟶ G', IsMonHom f' ∧ f'.left ≫ gm = gm ≫ (f a b).left ∧ ∀ m', EndChar U' f' m' → ∀ y, ι (m a b y) = m' (ι y)) → ∃ ρT : D.X ≃+ (Fin 8 → T.D.toPre.X), (∀ y r, PsiCoord D y r → 0 ≤ qW W T.β (ρT y) ∧ Associated (ψ r) (T.ϖ ^ (qW W T.β (ρT y)).toNat)) ∧ ∀ a b y, MatRel W a b (ρT y) (ρT (m a b y)) := by
  intro g n o _ ζ F W hW o' Ω _ _ _ _ S ρ u c pr hsh M U₀ EE FinalForm hov V v hv f hf R _ _ _ ξ D m T ψ hT G' _ _ D' A' U'
    gm ι hG hpb hL hco hm
  have hBV : GlobalTheory.Mum.Base T.V := ⟨⟨inferInstance, inferInstance, inferInstance, T.complete⟩, inferInstance⟩
  obtain ⟨ξ₀, h1, h2⟩ := hT
  obtain ⟨c', pr', hs', hmat⟩ := (GlobalTheory.T.thetaModel_open_abelian_eighthPower_with_bundle g n o ζ F W o' Ω S ρ u c pr hsh M U₀ EE FinalForm hov V v hv).2 T.V hBV G' hG
    D' A' U' (spMap ψ ≫ ξ) gm hpb hL ξ₀ h1
  have e0 : spMap (RingHom.id (FractionRing T.V)) ≫ T.y = ξ₀ ≫ v := by
    have : spMap (RingHom.id (FractionRing T.V)) = 𝟙 _ := Spec.map_id _
    rw [this, Category.id_comp, ← h2, Category.comp_id]
  have key : ∀ y₀ : Sp (FractionRing T.V) ⟶ F.X, spMap (RingHom.id (FractionRing T.V)) ≫ T.y = y₀ →
      ∀ c'' pr'', SharpBy F W A' y₀ c'' pr'' → ∃ e : D'.toPre.X ≃+ (Fin 8 → T.D.toPre.X),
      (∀ y r, PsiCoord D'.toPre y r → 0 ≤ qW W T.β (e y) ∧ Associated r (T.ϖ ^ (qW W T.β (e y)).toNat)) ∧
      ∀ (a b : Fin 8) (f : G' ⟶ G') (f₁ : A'.A ⟶ A'.A) (m : D'.toPre.X →+ D'.toPre.X), IsMonHom f →
        MatEnd pr'' a b f₁ → (Over.pullback (jK T.V)).map f ≫ U'.gen.hom = U'.gen.hom ≫ f₁ → EndChar U' f m →
        ∀ y, MatRel W a b (e y) (e (m y)) := by
    rintro _ rfl c'' pr'' hs''
    exact GlobalTheory.T.exists_eighthPowerTrait_lattice_equiv_localExt g n o ζ F W hW T T.V hBV inferInstance G' hG D' A' U' (RingHom.id _) (RingHom.id _)
      inferInstance (fun _ => rfl) c'' pr'' hs''
  obtain ⟨e, he1, he2⟩ := key _ e0 c' pr' hs'
  refine ⟨ι.trans e, fun y r hr => ?_, fun a b y => ?_⟩
  · obtain ⟨r', hr'⟩ := (GlobalTheory.PeriodFormCompare.exists_psiCoord_iff D'.toPre (ι y)).2
      (GlobalTheory.PeriodFormCompare.psiIn_top D' _)
    obtain ⟨h0, ha⟩ := he1 _ _ hr'
    exact ⟨h0, (hco y r r' hr hr').trans ha⟩
  · obtain ⟨f', hfm, hf', hmm⟩ := hm a b
    obtain ⟨m', hm'⟩ := endChar_exists_of_isMonHom T.V hBV G' hG D' A' U' f' hfm
    obtain ⟨f₁, hf₁, hgen⟩ := hmat a b (f a b) f' (hf a b) hf'
    have := he2 a b f' f₁ m' hfm hf₁ hgen hm' (ι y)
    rw [← hmm m' hm' y] at this
    exact this

end GlobalTheory.Poinc.Eq8.PeriodsEighth
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.tensorDegenerationData_torsion_isometry_onto : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det → ∀ T : Tens D.toPre D'.toPre W, ∀ (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ), (∀ a, (ρ a).transpose * (W + W.transpose) = (W + W.transpose) * ρ (H.bar a)) → W = (W + W.transpose) * ρ H.w0 → ∀ [Module (𝓞 E) D'.toPre.X] (o : letI := H.starRing; D'.toPre.OAct (𝓞 E)), (letI := H.starRing; T.IsAct o ρ) → (letI := H.starRing; TraceFormTwistIso D'.toPre o H.w0) → ∀ (Dm : Datum H) (g : ℕ) (e : Dm.La ≃+ (Fin r → (Fin g → ℤ) × (Fin g → ℤ))), g = D.toPre.P.g + Module.finrank ℤ D.toPre.X → (∀ (a : 𝓞 E) x i, e (a • x) i = ∑ j, ρ a i j • e x j) → (∀ x y, Dm.EF x y = ∑ i, ∑ j, (W + W.transpose) i j * ((e x i).1 ⬝ᵥ (e y j).2 - (e x i).2 ⬝ᵥ (e y j).1)) → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (ζ : ℕ → Fˣ), (∀ n, 0 < n → IsPrimitiveRoot (ζ n) n) → (∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n) → ∀ ev : ∀ n : ℕ, ((Fin g → ℤ) × (Fin g → ℤ)) → QkPt D.toPre F n, (∀ n, 0 < n → ∀ a b, QkAdd (ev n a) (ev n b) (ev n (a + b))) → (∀ n, 0 < n → ∀ a b, QkPt.Equiv D.toPre F (ev n a) (ev n b) ↔ ∃ e, a = b + n • e) → (∀ n, 0 < n → ∀ p, ∃ a, QkPt.Equiv D.toPre F (ev n a) p) → (∀ n m, 0 < n → 0 < m → ∀ a, ∃ q : QkPt D.toPre F n, q.y = (ev (n * m) a).y ∧ GtPtF.IsNsmul m (ev (n * m) a).g q.g ∧ QkPt.Equiv D.toPre F q (ev n a)) → (∀ n, 0 < n → ∀ a b, WeilQkIs D.toPre F n (ev n a) (ev n b) ((ζ n ^ (a.1 ⬝ᵥ b.2 - a.2 ⬝ᵥ b.1) : Fˣ) : F)) → ∃ I : TateIsoQ Dm D'.toPre o F, I.ζ = ζ := by
  first | exact @GlobalTheory.Mum.TensTor.tate_tens | exact GlobalTheory.Mum.TensTor.tate_tens | (intros; apply GlobalTheory.Mum.TensTor.tate_tens <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.recognition_degData_labels_at_every_trait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → OneTrait D.toPre A lab → GalEqN n lab → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), Function.Injective φ → IsLocalHom φ → ∀ (G' : Over (Sp W)) [GrpObj G'] [IsCommMonObj G'] (D' : DegData W (maximalIdeal W)) (A' : PolAV (Sp (FractionRing W))) (U' : Unif (maximalIdeal W) D' A' G') (a : A'.A.left ⟶ A.A.left), IsSemiAbelian G' → IsFib φ A A' a → ∃ hD : IsPullDeg φ D.toPre D'.toPre, ∀ j : ℕ, Induces lab φ U' hD a (n ^ j) := by
  first | exact @GlobalTheory.Mum.Recognition.pullDeg_induces | exact GlobalTheory.Mum.Recognition.pullDeg_induces | (intros; apply GlobalTheory.Mum.Recognition.pullDeg_induces <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

theorem _root_.GlobalTheory.T.thetaTerm_coefficient_sq_eq_monomial_subfield : ∀ (N₁ : ℕ), 2 ≤ N₁ → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁), D.PsiEven → D.TauBimult → ∀ (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D N₁ e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → ∀ (τ₀ : GlobalTheory.UChart.Gens D) (m N : ℕ) (s : Fin m ⊕ Fin N → V₁) (ε : Fin m ⊕ Fin N → LinearMap.BilinForm ℤ D.X), (∀ k, IsUnit (s (.inr k))) → GlobalTheory.UChart.TauIn D τ₀ (fun k => s (finSumFinEquiv.symm k)) (fun k => ε (finSumFinEquiv.symm k)) → (∀ mu, algebraMap V₁ (FractionRing V₁) (mo mu) ^ 2 = ∏ k, algebraMap V₁ (FractionRing V₁) (s (.inl k)) ^ ε (.inl k) (e mu) (e mu)) → ∀ (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V₁), GlobalTheory.UChart.FromBase D τ₀ ib → (∀ a, ev (ib a) ∈ k₀) → ∀ mu c, ∃ r ∈ k₀, ev (u mu c) ^ 2 = r * ∏ k, ev (s (.inr k)) ^ ε (.inr k) (e mu) (e mu) := by
  first | exact @GlobalTheory.USep.Coef.coef_sq_mem_monomial | exact GlobalTheory.USep.Coef.coef_sq_mem_monomial | (intros; apply GlobalTheory.USep.Coef.coef_sq_mem_monomial <;> assumption)
end
