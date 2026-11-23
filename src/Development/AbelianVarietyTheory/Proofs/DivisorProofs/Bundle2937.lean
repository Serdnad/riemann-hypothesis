module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle072
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CodimOneIntegralSubschemeDim
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1817
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RingKrullDimQuotientAddOneOfMemMinimalPrimesSup
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2808
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2809
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle107
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle088
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle134
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteRootsOfBimul
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle027
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VdmRec.CutSec

section General

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ArInt GlobalTheory.Cartier

theorem dim_closure_of_coheight_field {K : Type} [Field K] {X : Scheme.{0}} [IsIntegral X] (t : X ⟶ Spec (.of K))
    [LocallyOfFiniteType t] {n : ℕ} (hX : topologicalKrullDim X = (n + 1 : ℕ)) {w : X} (hw : Order.coheight w = 1) :
    topologicalKrullDim (closure ({w} : Set X)) = n := by
  have hgen : genericPoint X ∉ closure ({w} : Set X) := by
    intro h
    have e : w = genericPoint X :=
      ((genericPoint_specializes w).antisymm (specializes_iff_mem_closure.2 h)).eq.symm
    rw [e, Order.coheight_eq_zero.2 (fun y _ => genericPoint_specializes y)] at hw
    exact zero_ne_one hw
  have hX1 : topologicalKrullDim (Set.univ : Set X) = (n + 1 : ℕ) :=
    (topologicalKrullDim_eq_of_isEmbedding Topology.IsEmbedding.id Set.range_id).trans hX
  have hup : topologicalKrullDim (closure ({w} : Set X)) + 1 ≤ (n + 1 : ℕ) :=
    hX1 ▸ topologicalKrullDim_add_one_le isClosed_closure isClosed_univ
      fun x _ => ⟨genericPoint X, trivial, hgen, genericPoint_specializes x⟩
  refine le_antisymm (GlobalTheory.PullVanish.withBot_le_of_add_one_le hup) ?_
  obtain ⟨A, _, _, _, _, _, j, _, ⟨a, ha⟩, -, hA⟩ := exists_affine_chart_trdeg_eq t w
  obtain ⟨d, hd⟩ := exists_trdeg_eq_natCast K (A := A)
  have hdimX : topologicalKrullDim X ≤ (d : ℕ) := by
    refine topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_
    obtain ⟨B, _, _, _, _, _, j', _, ⟨b, rfl⟩, -, hB⟩ := exists_affine_chart_trdeg_eq t x
    refine ⟨Set.range j', j'.isOpenEmbedding.isOpen_range, ⟨b, rfl⟩, ?_⟩
    rw [topologicalKrullDim_eq_of_isEmbedding j'.isOpenEmbedding.isEmbedding rfl]
    exact ((PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim B).trans
      (ringKrullDim_eq_of_trdeg_eq K B (hB.trans (hA.symm.trans hd)))).le
  have hh : a.asIdeal.height = 1 := by
    rw [← hw, ← ha, coheight_apply_of_isOpenImmersion]
    exact idealHeight_eq_coheight (CommRingCat.of A) a
  have : a.asIdeal.IsPrime := a.isPrime
  have hF := height_add_ringKrullDim_quotient_of_finiteType K a.asIdeal
  rw [hh, ringKrullDim_eq_of_trdeg_eq K A hd] at hF
  have hlow : topologicalKrullDim (Set.range j ∩ closure {j a} : Set X) ≤
      topologicalKrullDim (closure ({w} : Set X)) := by
    rw [ha]
    exact (Topology.IsEmbedding.inclusion Set.inter_subset_right).isInducing.topologicalKrullDim_le
  rw [topologicalKrullDim_range_inter_closure_eq j a] at hlow
  refine le_trans ?_ hlow
  rw [hX, ← hF] at hdimX
  generalize ringKrullDim (A ⧸ a.asIdeal) = u at hdimX
  induction u using WithBot.recBotCoe with
  | bot => simp at hdimX
  | coe u =>
    induction u using ENat.recTopCoe with
    | top => exact_mod_cast le_top
    | coe u =>
      have : n + 1 ≤ 1 + u := by exact_mod_cast hdimX
      exact_mod_cast (by omega : n ≤ u)

theorem dim_closure_of_coheight {k : Type} [CommRing k] {X Z : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ} (hX : IsArithVar p D)
    (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] {n : ℕ} (hZ : topologicalKrullDim Z = (n + 1 : ℕ)) {w : Z}
    (hw : Order.coheight w = 1) : topologicalKrullDim (closure ({w} : Set Z)) = n := by
  obtain ⟨l, hl⟩ := CharP.exists Γ(Z, ⊤)
  rcases CharP.char_is_prime_or_zero Γ(Z, ⊤) l with hp | rfl
  · have : Fact l.Prime := ⟨hp⟩
    let := ZMod.algebra Γ(Z, ⊤) l
    obtain ⟨N, jN, _, hjN⟩ := hX.isProjOver
    have := isProper_str k N
    have : IsProper p := hjN ▸ inferInstance
    have : IsFinite (spMap (Int.castRingHom k)) :=
      (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 hX.finite)
    have e : strHom (ZMod l) Z ≫ spMap (Int.castRingHom (ZMod l)) = i ≫ p ≫ spMap (Int.castRingHom k) :=
      specZIsTerminal.hom_ext _ _
    have : LocallyOfFiniteType (strHom (ZMod l) Z ≫ spMap (Int.castRingHom (ZMod l))) := e ▸ inferInstance
    have : LocallyOfFiniteType (strHom (ZMod l) (X := Z)) := locallyOfFiniteType_of_comp _ (spMap (Int.castRingHom (ZMod l)))
    exact dim_closure_of_coheight_field (strHom (ZMod l) Z) hZ hw
  · have := CharP.charP_to_charZero Γ(Z, ⊤)
    have h := GlobalTheory.PrimeDivDim.dim_eq_of_coheight_eq_one k Z (i ≫ p) n (hX.of_isClosedImmersion i this hZ) _
      (redι (clo w)) (by rw [GlobalTheory.PullVanish.redι_genericPoint]; exact hw)
    exact (topologicalKrullDim_eq_of_isEmbedding (redι (clo w)).isClosedEmbedding.isEmbedding
      (range_redι _)).trans h

end General

section Cut

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ArInt GlobalTheory.Cartier

end Cut

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open GlobalTheory.VdmRec

end GlobalTheory.VdmRec.CutSec

end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points
open scoped ENNReal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernDescend

theorem chernIntegrableOn_descend : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k) (e : ℕ), IsArithVar q e → ∀ (Y' : Scheme.{0}) [IsIntegral Y'] (ρ : Y' ⟶ Y), IsArithVar (ρ ≫ q) e → ρ (genericPoint Y') = genericPoint Y → ρ.residueDegree (genericPoint Y') ≠ 0 → ∀ (N : HermLB q) (σ : k →+* ℂ) (U : Y.Opens) (f : CxPts q σ → ℝ), ContinuousOn f (ptsIn q σ U) → ((N.restr ρ).φ σ).ChernIntegrableOn e (ptsIn (ρ ≫ q) σ (ρ ⁻¹ᵁ U)) (fun y => f (PtsOver.map ρ rfl _ y)) → (N.φ σ).ChernIntegrableOn e (ptsIn q σ U) f := by
  intro k _ Y _ q e hY Y' _ ρ hY' hη hδ N σ U f hf hint
  obtain ⟨V, hVη, hV⟩ := GlobalTheory.T.exists_open_etaleChart_covering_complexPoints hY hY' ρ rfl hη hδ
  obtain ⟨hcard, hchart, hlift⟩ := hV σ
  have hFm : Measurable (PtsOver.map ρ (rfl : ρ ≫ q = ρ ≫ q) (spMap σ)) :=
    (PtsOver.continuous_map _ _ _).measurable
  have hpre : ∀ W : Y.Opens, PtsOver.map ρ (rfl : ρ ≫ q = ρ ≫ q) (spMap σ) ⁻¹' ptsIn q σ W =
      ptsIn (ρ ≫ q) σ (ρ ⁻¹ᵁ W) := by
    intro W
    ext z
    simp only [Set.mem_preimage, mem_ptsIn]
    rfl
  have hUm : MeasurableSet (ptsIn q σ U) := (isOpen_ptsIn U).measurableSet
  have hVm : MeasurableSet (ptsIn q σ V) := (isOpen_ptsIn V).measurableSet
  have h0 : ∀ ε : ℤˣ, (N.φ σ).chernPart e ε (ptsIn q σ V)ᶜ = 0 := by
    intro ε
    have h := GlobalTheory.T.chernPart_over_properClosed_eq_zero hY ((V : Y.Opens) : Set Y)ᶜ V.isOpen.isClosed_compl (by simp [hVη]) σ
      (N.φ σ) ε
    convert h using 2
    ext y
    simp [mem_ptsIn]
  have hmeas : ∀ ε : ℤˣ, (ρ.residueDegree (genericPoint Y') : ℝ≥0∞) •
      ((N.φ σ).chernPart e ε).restrict (ptsIn q σ U) =
      Measure.map (PtsOver.map ρ (rfl : ρ ≫ q = ρ ≫ q) (spMap σ))
        ((((N.φ σ).pull ρ rfl).chernPart e ε).restrict
          (PtsOver.map ρ (rfl : ρ ≫ q = ρ ≫ q) (spMap σ) ⁻¹' (ptsIn q σ U ∩ ptsIn q σ V))) := by
    intro ε
    ext A hA
    rw [Measure.smul_apply, Measure.restrict_apply hA, Measure.map_apply hFm hA,
      Measure.restrict_apply (hFm hA), ← Set.preimage_inter,
      GlobalTheory.T.chernPart_preimage_of_finite_liftedChartCovering hY hY' ρ rfl (N.φ σ) (N.cInf σ) ε (ptsIn q σ V) (isOpen_ptsIn V) _ hcard hchart
        hlift (fun c c' hc w hw => GlobalTheory.T.chernDensity_pullbackWeight_in_liftedChart ρ rfl (N.φ σ) (N.cInf σ) c c' hc w hw) _
        (hA.inter (hUm.inter hVm)) (fun x hx => hx.2.2), smul_eq_mul, ← Set.inter_assoc,
      measure_inter_conull (h0 ε)]
  have hδ1 : (1 : ℝ≥0∞) ≤ (ρ.residueDegree (genericPoint Y') : ℝ≥0∞) :=
    Nat.one_le_cast.2 (Nat.pos_of_ne_zero hδ)
  have key : ∀ ε : ℤˣ, IntegrableOn (fun y => f (PtsOver.map ρ rfl _ y))
      (ptsIn (ρ ≫ q) σ (ρ ⁻¹ᵁ U)) (((N.φ σ).pull ρ rfl).chernPart e ε) →
      IntegrableOn f (ptsIn q σ U) ((N.φ σ).chernPart e ε) := by
    intro ε h
    refine ⟨hf.aestronglyMeasurable hUm, ?_⟩
    have h1 := h.2
    unfold HasFiniteIntegral at h1 ⊢
    refine lt_of_le_of_lt ?_ h1
    calc ∫⁻ y, ‖f y‖ₑ ∂((N.φ σ).chernPart e ε).restrict (ptsIn q σ U)
        ≤ (ρ.residueDegree (genericPoint Y') : ℝ≥0∞) *
          ∫⁻ y, ‖f y‖ₑ ∂((N.φ σ).chernPart e ε).restrict (ptsIn q σ U) :=
          le_mul_of_one_le_left' hδ1
      _ = ∫⁻ y, ‖f y‖ₑ ∂Measure.map (PtsOver.map ρ (rfl : ρ ≫ q = ρ ≫ q) (spMap σ))
          ((((N.φ σ).pull ρ rfl).chernPart e ε).restrict
            (PtsOver.map ρ (rfl : ρ ≫ q = ρ ≫ q) (spMap σ) ⁻¹' (ptsIn q σ U ∩ ptsIn q σ V))) := by
          rw [← hmeas ε, lintegral_smul_measure, smul_eq_mul]
      _ ≤ ∫⁻ z, ‖f (PtsOver.map ρ (rfl : ρ ≫ q = ρ ≫ q) (spMap σ) z)‖ₑ
          ∂((((N.φ σ).pull ρ rfl).chernPart e ε).restrict
            (PtsOver.map ρ (rfl : ρ ≫ q = ρ ≫ q) (spMap σ) ⁻¹' (ptsIn q σ U ∩ ptsIn q σ V))) :=
          lintegral_map_le _ hFm.aemeasurable
      _ ≤ _ := by
          refine lintegral_mono' (Measure.restrict_mono ?_ le_rfl) le_rfl
          rw [← hpre U]
          exact Set.preimage_mono Set.inter_subset_left
  exact ⟨key 1 hint.1, key (-1) hint.2⟩

end GlobalTheory.ChernDescend

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc.TraitPullAct

theorem mono_spMap_toRat {o Ω F : Type} [CommRing o] [Field Ω] [Algebra o Ω] [Field F] [CharZero F] (R : Subalgebra o Ω)
    (s : Sp (ratHull R) ⟶ Sp F) : Mono (spMap (toRat R)) := by
  haveI : CharZero Ω :=
    (RingHom.charZero_iff ((ratHull R).val.toRingHom.comp (Spec.preimage s).hom).injective).1 inferInstance
  letI := (toRat R).toAlgebra
  haveI := isLocalization_ratHull R
  haveI : IsPreimmersion (spMap (toRat R)) :=
    IsPreimmersion.of_isLocalization (Algebra.algebraMapSubmonoid R (nonZeroDivisors ℤ))
  exact SurjectiveOnStalks.mono_of_injective (IsPreimmersion.isEmbedding _).injective

theorem exists_pull_univ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
    {Xo : Moduli Dw l} {c : Coeff l} (T : UTrait Xo c) :
    ∃ ψ : T.P.A.A.left ⟶ Xo.univ.t.G.left, IsGrpPullback T.P.A.A Xo.univ.t.G (T.y ≫ pullback.fst _ _) ψ ∧
      LBIso T.P.A.L (Xo.univ.t.PP.L.pull ψ) ∧
      ∀ a : 𝓞 E, (T.P.oA.act a).left ≫ ψ = ψ ≫ (Xo.univ.t.act.act a).left := by
  obtain ⟨tK, ⟨m₁⟩, ⟨m₂⟩⟩ := T.gen
  have hm := T.P.U.gen_hom
  haveI : IsMonHom T.P.U.gen.symm.hom := inferInstanceAs (IsMonHom T.P.U.gen.inv)
  have hgen : IsGrpPullback T.P.A.A T.t.G (jK T.V) (T.P.U.gen.inv.left ≫ pullback.fst T.t.G.hom (jK T.V)) :=
    ((isGrpPullback_of_iso T.P.U.gen.symm).comp (isGrpPullback_pullback T.t.G (jK T.V))).congr (Category.id_comp _) rfl
  obtain ⟨e, he, he₁⟩ := grpPullback_iso hgen m₁.cart
  haveI := he
  refine ⟨e.hom.left ≫ m₂.cm.F, ((isGrpPullback_of_iso e).comp m₂.cart).congr (Category.id_comp _) rfl, ?_, fun a => ?_⟩
  · have hext : LBIso (T.t.PP.L.pull (pullback.fst T.t.G.hom (jK T.V))) (T.P.A.L.pull T.P.U.gen.hom.left) := by
      obtain ⟨w, hw⟩ := T.P.U.ext
      have hb := T.P.bundle
      exact LBIso.symm (hb ▸ ⟨w, hw⟩)
    have s1 := GlobalTheory.TripleTheta.lbIso_inv T.P.U.gen hext
    have s2 := (GlobalTheory.GenSpread.lbIso_pull_pull T.t.PP.isLB (a := pullback.fst T.t.G.hom (jK T.V))
      T.P.U.gen.inv.left rfl).symm
    have s3 := GlobalTheory.GenSpread.lbIso_pull_of_lbIso (GlobalTheory.TripleTheta.lbIso_of_sabMap m₁) e.hom.left he₁.symm
    have s4 := GlobalTheory.GenSpread.lbIso_pull_of_lbIso (GlobalTheory.TripleTheta.lbIso_of_sabMap m₂) e.hom.left rfl
    exact LBIso.trans T.P.A.isLB (pull_isLB (pull_isLB T.t.PP.isLB _) _) (pull_isLB Xo.univ.t.PP.isLB _) s1
      (LBIso.trans (pull_isLB (pull_isLB T.t.PP.isLB _) _) (pull_isLB T.t.PP.isLB _) (pull_isLB Xo.univ.t.PP.isLB _) s2
      (LBIso.trans (pull_isLB T.t.PP.isLB _) (pull_isLB tK.PP.isLB _) (pull_isLB Xo.univ.t.PP.isLB _) (LBIso.symm s3) s4))
  · letI := H.starRing
    have h0 := T.P.lin.ext a
    have h1 : T.P.oA.act a ≫ T.P.U.gen.inv = T.P.U.gen.inv ≫ (Over.pullback (jK T.V)).map (T.t.act.act a) := by
      rw [Iso.comp_inv_eq, Category.assoc, eq_comm, Iso.inv_comp_eq]
      exact h0
    have h2 : ((Over.pullback (jK T.V)).map (T.t.act.act a)).left ≫ pullback.fst T.t.G.hom (jK T.V) =
        pullback.fst T.t.G.hom (jK T.V) ≫ (T.t.act.act a).left := pullback.lift_fst _ _ _
    have h3 : (T.P.oA.act a).left ≫ e.hom.left = e.hom.left ≫ (tK.act.act a).left := by
      apply m₁.cart.1.hom_ext
      · rw [Category.assoc, Category.assoc, m₁.act a, ← Category.assoc e.hom.left, he₁, ← Category.assoc,
          ← Over.comp_left, h1, Over.comp_left, Category.assoc, h2, Category.assoc]
      · rw [← Over.comp_left, ← Over.comp_left, Over.w, Over.w]
    rw [← Category.assoc, h3, Category.assoc, m₂.act a, Category.assoc]

theorem exists_pull_act : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (u' : Sp (ratHull S.R) ⟶ Xo.XF cf) (G : Over (Sp (ratHull S.R))) (_ : GrpObj G) (α : G.left ⟶ ρ.P.A.left) (β : G.left ⟶ Xo.univ.t.G.left), IsGrpPullback G ρ.P.A (spMap (toRat S.R)) α → IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β → LBIso (ρ.P.L.pull α) (Xo.univ.t.PP.L.pull β) → ∀ (T : UTrait Xo cf) (yK : ratHull S.R →+* FractionRing T.V), spMap yK ≫ u' = T.y → ∃ φ : T.P.A.A.left ⟶ ρ.P.A.left, IsGrpPullback T.P.A.A ρ.P.A (spMap (yK.comp (toRat S.R))) φ ∧ LBIso T.P.A.L (ρ.P.L.pull φ) ∧ ∀ (Y : Over (Sp (FractionRing T.V))) (x x' : Y ⟶ T.P.A.A) (w w' : Y.left ⟶ G.left) (a : 𝓞 E), w ≫ α = x.left ≫ φ → w' ≫ α = x'.left ≫ φ → w' ≫ β = w ≫ β ≫ (Xo.univ.t.act.act a).left → x' = x ≫ T.P.oA.act a := by
  intro E _ _ _ H Dw l Xo cf o Ω _ _ _ S ρ u' G _ α β hα hβ hL T yK hy
  obtain ⟨ψ, hψ, hψL, hψa⟩ := exists_pull_univ T
  have e₀ : T.y ≫ pullback.fst _ _ = spMap yK ≫ u' ≫ pullback.fst _ _ := by rw [← hy, Category.assoc]
  have w₀ : ψ ≫ Xo.univ.t.G.hom = (T.P.A.A.hom ≫ spMap yK) ≫ u' ≫ pullback.fst _ _ := by
    rw [Category.assoc, ← e₀]; exact hψ.1.w
  have e₁ := hβ.1.lift_fst _ _ w₀
  have hγ := hβ.cancel (hψ.congr e₀ e₁.symm) (hβ.1.lift_snd _ _ w₀)
  generalize hβ.1.lift _ _ w₀ = γ at e₁ hγ
  refine ⟨γ ≫ α, (hγ.comp hα).congr (by rw [← Spec.map_comp]; rfl) rfl, ?_, fun Y x x' w w' a hw hw' h => ?_⟩
  · exact LBIso.trans T.P.A.isLB (pull_isLB Xo.univ.t.PP.isLB _) (pull_isLB ρ.P.isLB _) hψL
      (GlobalTheory.GenSpread.lbIso_pull_comp γ rfl e₁.symm hL).symm
  · haveI := mono_spMap_toRat S.R (u' ≫ pullback.snd _ _)
    haveI : Mono α := ⟨fun f g hfg => hα.1.hom_ext hfg ((cancel_mono (spMap (toRat S.R))).1 (by
      rw [Category.assoc, Category.assoc, ← hα.1.w, ← Category.assoc, hfg, Category.assoc]))⟩
    obtain rfl : w = x.left ≫ γ := (cancel_mono α).1 (hw.trans (Category.assoc _ _ _).symm)
    obtain rfl : w' = x'.left ≫ γ := (cancel_mono α).1 (hw'.trans (Category.assoc _ _ _).symm)
    apply Over.OverMorphism.ext
    apply hψ.1.hom_ext
    · rw [Over.comp_left, Category.assoc, hψa a, ← e₁]
      simpa only [Category.assoc] using h
    · rw [Over.w, Over.w]

end GlobalTheory.UPoinc.TraitPullAct
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.Points GlobalTheory.ZM GlobalTheory.SiegelTor

namespace GlobalTheory.UPoinc

theorem rechart_at_uClassical_trait : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (p : ℕ) [Fact p.Prime] (z : X.M.Z) (ct : UCTrait X p z) (U : X.M.Z.Opens) (u' : Sp (ratHull (X.M.ringOn U)) ⟶ Xo.XF cf), IsAffineOpen U → (gPt p ≫ ct.y) (closedPoint (PadicAlgCl p)) ∈ U → spMap (ratHull (X.M.ringOn U)).val.toRingHom ≫ u' = X.uΩ → X.M.ringOn U ≤ X.M.O ((gPt p ≫ ct.y) (closedPoint (PadicAlgCl p))) ∧ ∃ y₁ : ratHull (X.M.ringOn U) →+* PadicAlgCl p, (∀ a : X.M.ringOn U, y₁ (toRat _ a) = X.M.val (gPt p ≫ ct.y) a) ∧ spMap y₁ ≫ u' = spMap ct.ι ≫ ct.T.y ∧ ∀ a : X.o₁, ‖y₁ (toRat _ (algebraMap X.o₁ (X.M.ringOn U) a))‖ ≤ 1 := by
  intro E _ _ _ H Dw hpq l Xo cf C X p _ z ct U u' hU hwU hu'
  haveI := X.ar.char
  set w := (gPt p ≫ ct.y) (closedPoint (PadicAlgCl p)) with hw
  have hne : (U : Set X.M.Z).Nonempty := ⟨w, hwU⟩
  have hle : X.M.ringOn U ≤ X.M.O w := RatModel.ringOn_le_O hwU
  have hsp : ∀ w', (gPt p ≫ ct.y) w' ⤳ w := fun w' => by
    rw [Subsingleton.elim w' (closedPoint (PadicAlgCl p))]
  let y₀ : X.M.ringOn U →+* PadicAlgCl p :=
    (RatModel.valHomOf (gPt p ≫ ct.y) w hsp).comp (Subalgebra.inclusion hle).toRingHom
  have hy₀ : ∀ a : X.M.ringOn U, y₀ a = X.M.val (gPt p ≫ ct.y) a := fun a => rfl
  obtain ⟨y₁, hy₁, -⟩ := existsUnique_ratLift (X.M.ringOn U) (K := PadicAlgCl p)
    (fun n hn => IsUnit.mk0 _ (Int.cast_ne_zero.2 hn)) y₀
  have hy₁' : ∀ a : X.M.ringOn U, y₁ (toRat _ a) = y₀ a := fun a => RingHom.congr_fun hy₁ a
  let e : Sp (X.M.ringOn U) ⟶ X.M.Z :=
    Spec.map (CommRingCat.ofHom (X.M.sectionsEquiv U hne).toRingHom) ≫ hU.fromSpec
  have he : ∀ {K : Type} [CommRing K] (φ : X.M.ringOn U →+* K), ⊤ ≤ (spMap φ ≫ e) ⁻¹ᵁ U ∧
      ∀ f, valR (spMap φ ≫ e) U f = φ (X.M.sectionsEquiv U hne f) := by
    intro K _ φ
    have e2 : spMap φ ≫ e = Spec.map (CommRingCat.ofHom (φ.comp (X.M.sectionsEquiv U hne).toRingHom)) ≫
        hU.fromSpec := by
      rw [← Category.assoc, ← Spec.map_comp]; rfl
    rw [e2]
    have hx := le_preimage_specMap_fromSpec hU (CommRingCat.ofHom (φ.comp (X.M.sectionsEquiv U hne).toRingHom))
    refine ⟨hx, fun f => ?_⟩
    rw [valR_eq _ U hx, valMap_specMap_fromSpec]
    rfl
  have hyU : ⊤ ≤ (gPt p ≫ ct.y) ⁻¹ᵁ U := (le_preimage_iff _ U).2 hwU
  have ha : spMap y₀ ≫ e = gPt p ≫ ct.y := by
    refine ext_of_valR hU (he y₀).1 hyU fun f => ?_
    rw [(he y₀).2, hy₀, RatModel.coe_sectionsEquiv, RatModel.val_valF ((top_le_preimage_iff _ _).1 hyU)]
    rfl
  have hgen : spMap (X.M.ringOn U).val.toRingHom ≫ e = X.M.pt := by
    refine ext_of_valR hU (he _).1 (X.M.top_le_preimage_pt hne) fun f => ?_
    rw [(he _).2]
    exact (RatModel.coe_sectionsEquiv U hne f).trans (valF_eq_valR _ _ _)
  have hdom : IsDominant (spMap (ratHull (X.M.ringOn U)).val.toRingHom) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 Subtype.val_injective]; exact bot_le)⟩
  haveI : IsProper C.z := ThetaDescent.isProper_of_isProjOver C.proj
  have hgen2 : spMap (ratHull (X.M.ringOn U)).val.toRingHom ≫ ((spMap (toRat _) ≫ e) ≫ X.π) =
      spMap (ratHull (X.M.ringOn U)).val.toRingHom ≫ (u' ≫ C.i) := by
    rw [← Category.assoc, ← Category.assoc, spMap_val_toRat, hgen, X.comp, ← Category.assoc _ u' C.i, hu']
    simp only [USetup.uΩ, Category.assoc]
  have hb : (spMap (toRat _) ≫ e) ≫ X.π = u' ≫ C.i :=
    ext_of_isDominant_of_isSeparated C.z
      (ext_of_isDominant (spMap (ratHull (X.M.ringOn U)).val.toRingHom) (by
        simp only [← Category.assoc] at hgen2 ⊢; rw [hgen2]))
      (spMap (ratHull (X.M.ringOn U)).val.toRingHom) hgen2
  haveI := C.isPreimmersion_i
  have hy01 : spMap y₁ ≫ spMap (toRat (X.M.ringOn U)) = spMap y₀ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hy₁]
  have hpt' : spMap y₁ ≫ u' = spMap ct.ι ≫ ct.T.y := by
    rw [← cancel_mono C.i, Category.assoc, ← hb, ← Category.assoc, ← Category.assoc, hy01, ha, Category.assoc,
      ct.comm, Category.assoc]
  let τ := Spec.preimage (ct.y ≫ X.M.s)
  have hσ : (gPt p ≫ ct.y) ≫ X.M.s = spMap ((OO p).subtype.comp τ.hom) := by
    rw [Category.assoc, ← Spec.map_preimage (ct.y ≫ X.M.s), ← Spec.map_comp]; rfl
  refine ⟨hle, y₁, fun a => (hy₁' a).trans (hy₀ a), hpt', fun a => ?_⟩
  rw [hy₁', hy₀]
  show ‖X.M.val (gPt p ≫ ct.y) (algebraMap X.o₁ X.Ω₁ a)‖ ≤ 1
  rw [RatModel.val_algebraMap hσ a]
  exact (mem_OO_iff _).1 (τ.hom a).2

end GlobalTheory.UPoinc
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

noncomputable section

namespace GlobalTheory.UPoinc.UTrait

theorem balanced_posDef_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : UTrait Xo c), T.be ∈ balForms H.bar T.P.D.toPre.X ∧ (∀ y, y ≠ 0 → 0 < T.be y y) ∧ Module.Finite (𝓞 E) T.P.D.toPre.X ∧ Module.Projective (𝓞 E) T.P.D.toPre.X ∧ ∃ n : ℕ, Nonempty (T.P.D.toPre.X ≃ₗ[ℤ] (Fin n → ℤ)) := by
  intro E _ _ _ H Dw l Xo c T
  haveI hf : Module.Finite (𝓞 E) T.P.D.toPre.X := Module.Finite.of_restrictScalars_finite ℤ _ _
  refine ⟨(balForms_eq_levelForms H T.P.D.toPre.X).ge T.lev, fun y hy => ?_, hf, ?_, _,
    ⟨(Module.finBasis ℤ T.P.D.toPre.X).equivFun⟩⟩
  · obtain ⟨i, hi⟩ := IsMonomial.exists_pos (maximalIdeal.isMaximal T.V).ne_top T.mono hy
    simpa using hi
  · exact GlobalTheory.Forms.projective_of_int (𝓞 E) _

end GlobalTheory.UPoinc.UTrait
end
end

section

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Models GlobalTheory.UPoinc GlobalTheory.ZH

namespace GlobalTheory.UPoinc

theorem isReduced_of_flat_isPreimmersion {X Y : Scheme.{0}} (f : X ⟶ Y) [Flat f] [IsPreimmersion f] [IsReduced Y] :
    IsReduced X := by
  haveI : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
    have hfl := Flat.stalkMap f x
    have hs := f.stalkMap_surjective x
    letI := (f.stalkMap x).hom.toAlgebra
    haveI : Module.Flat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := hfl
    haveI : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
      inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
    haveI := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := Y.presheaf.stalk (f x)) (B := X.presheaf.stalk x)
    have hi : Function.Injective (f.stalkMap x).hom :=
      FaithfulSMul.algebraMap_injective (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)
    exact isReduced_of_injective (RingEquiv.ofBijective _ ⟨hi, hs⟩).symm (RingEquiv.injective _)
  exact isReduced_of_isReduced_stalk X

theorem isIntegral_pullback_toRat : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [CharZero Ω] (M : RatModel o Ω) (U₀ : M.Z.Opens) (R : Subalgebra o Ω) (u₀ : U₀.toScheme ⟶ Sp R), (U₀ : Set M.Z).Nonempty → (∀ x : Sp Ω ⟶ U₀.toScheme, x ≫ U₀.ι = M.pt → x ≫ u₀ = spMap R.val.toRingHom) → IsIntegral (pullback u₀ (spMap (toRat R))) ∧ ∃ pt : Sp Ω ⟶ pullback u₀ (spMap (toRat R)), pt ≫ pullback.fst _ _ ≫ U₀.ι = M.pt ∧ Dense (Set.range pt) := by
  intro o Ω _ _ _ _ M U₀ R u₀ hne hgen
  haveI := M.integral
  letI := (toRat R).toAlgebra
  haveI := isLocalization_ratHull R
  haveI : IsPreimmersion (spMap (toRat R)) :=
    IsPreimmersion.of_isLocalization (Algebra.algebraMapSubmonoid R (nonZeroDivisors ℤ))
  haveI : Flat (spMap (toRat R)) := (HasRingHomProperty.Spec_iff (P := @Flat)).2
    (IsLocalization.flat (ratHull R) (Algebra.algebraMapSubmonoid R (nonZeroDivisors ℤ)))
  have hr : Set.range M.pt ⊆ Set.range U₀.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact M.top_le_preimage_pt hne (show w ∈ (⊤ : (Sp Ω).Opens) from trivial)
  have hx := IsOpenImmersion.lift_fac U₀.ι M.pt hr
  have w : IsOpenImmersion.lift U₀.ι M.pt hr ≫ u₀ = spMap (ratHull R).val.toRingHom ≫ spMap (toRat R) :=
    (hgen _ hx).trans (spMap_val_toRat R).symm
  let pt := pullback.lift _ _ w
  let j : pullback u₀ (spMap (toRat R)) ⟶ M.Z := pullback.fst _ _ ≫ U₀.ι
  have hpt : pt ≫ j = M.pt := by rw [← Category.assoc, pullback.lift_fst, hx]
  haveI : IsPreimmersion j := inferInstance
  haveI : Flat j := inferInstance
  haveI := isReduced_of_flat_isPreimmersion j
  have hj : ∀ y, j (pt y) = genericPoint M.Z := fun y => by
    rw [← Scheme.Hom.comp_apply, hpt]
    exact M.gen.le ⟨y, rfl⟩
  have hg : IsGenericPoint (pt default) Set.univ := by
    refine isGenericPoint_iff_specializes.2 fun z => ⟨fun _ => trivial, fun _ => ?_⟩
    rw [← j.isEmbedding.isInducing.specializes_iff, hj]
    exact genericPoint_specializes _
  haveI : IrreducibleSpace (pullback u₀ (spMap (toRat R)) :) :=
    (irreducibleSpace_def _).2 hg.isIrreducible
  refine ⟨isIntegral_of_irreducibleSpace_of_isReduced _, pt, hpt, ?_⟩
  exact Dense.mono (Set.singleton_subset_iff.2 ⟨default, rfl⟩) (dense_iff_closure_eq.2 hg)

end GlobalTheory.UPoinc
end
