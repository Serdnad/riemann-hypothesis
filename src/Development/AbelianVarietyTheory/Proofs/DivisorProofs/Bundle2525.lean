module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle061
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2485
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2347
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2486
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2517
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2342
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1467
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2375
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1372
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1647
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1831
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2227
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoversOfHalves
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfFiniteIndex
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle250
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle238
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle211
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle074
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2516
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.RegDom

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
open GlobalTheory.Discrepancy GlobalTheory.EtaleKlt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PairStep

theorem finite_test_divisors : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (η : RatForms p n) (m : ℕ) (G D₀ : CartierDiv X), η ≠ 0 → 0 < m → ∃ S : Set (DivOver p), S.Finite ∧ ∀ (x : X) (g f : X.functionFieldˣ) (c : ℚ), G.IsEqn x g → D₀.IsEqn x f → ((∀ E ∈ S, E.Through x → -1 < discrep E η m g - c * E.ord f) → ∀ E : DivOver p, E.Through x → -1 < discrep E η m g - c * E.ord f) ∧ ((∀ E ∈ S, E.Through x → -1 ≤ discrep E η m g - c * E.ord f) → ∀ E : DivOver p, E.Through x → -1 ≤ discrep E η m g - c * E.ord f) := by
  intro hP X _ _ p n hproj hn η m G D₀ hη hm
  haveI : LocallyOfFiniteType p := by
    obtain ⟨h1, -⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hproj
    infer_instance
  obtain ⟨Y, hYi, hYn, s, hsd, B, hsm, hprop, hbij, hfin, hη', hchart, hG, hD, hK⟩ :=
    GlobalTheory.T.exists_resolution_divisors_topForm_normalCrossings hP X p n hproj hn η G D₀ hη
  haveI := SmoothOfRelativeDimension.smooth n (s ≫ p)
  haveI : GlobalTheory.IsNormalScheme Y := isNormalScheme_of_smooth (s ≫ p)
  have hnY : topologicalKrullDim Y = n := GlobalTheory.NadelApp.topologicalKrullDim_eq_of_smooth Y (s ≫ p) n
  set S : Set (DivOver p) := ⋃ v ∈ {v : Y | v ∈ B ∧ Order.coheight v = 1},
    {E : DivOver p | ∀ f, f ∈ E.ring ↔ RegAt v (functionFieldMap s f)} with hSdef
  refine ⟨S, hfin.biUnion fun v _ => Set.Subsingleton.finite fun E hE E₂ hE₂ => ?_, ?_⟩
  · have hr : E.ring = E₂.ring := SetLike.ext fun f => (hE f).trans (hE₂ f).symm
    cases E; cases E₂
    cases hr
    rfl
  intro x g f c hg hf
  have hmq : (0 : ℚ) < m := by exact_mod_cast hm

  have core : ∀ E : DivOver p, E.Through x → ∃ (ι : Type) (_ : Fintype ι) (Es : ι → DivOver p) (t : ι → ℤ),
      (∀ j, Es j ∈ S ∧ (Es j).Through x ∧ 0 ≤ t j) ∧
      ((∀ j, t j = 0) → (1 : ℚ) ≤ 1 + (discrep E η m g - c * E.ord f)) ∧
      ((∃ j, t j ≠ 0) → ∑ j, (1 + (discrep (Es j) η m g - c * (Es j).ord f)) * (t j : ℚ) ≤
        1 + (discrep E η m g - c * E.ord f)) := by
    intro E hE
    obtain ⟨E', hE'⟩ := GlobalTheory.T.exists_primeDivisor_over_source_of_birational p s hbij E
    obtain ⟨y, hyx, hy⟩ := GlobalTheory.T.exists_centre_of_valuationSubring_proper_dominant s E'.ring x fun a ha => (hE' a).1 (hE a ha)
    obtain ⟨U, hyU, z, J, w, u, hc⟩ := hchart y
    have hgen := isFreeGen_formOf (gen_mem hyU) hc.frame
    set ω0 := formOf U (gen_mem hyU) (dOn (s ≫ p) z) with hω0
    have h0 : ω0 ≠ 0 := fun h =>
      one_ne_zero (hgen.1 (a₁ := 1) (a₂ := 0) (by simp [h]))
    obtain ⟨h, hh⟩ := hgen.2 (ratPull p s n η)
    have hh0 : h ≠ 0 := fun e => hη' (by simp [← hh, e])
    set H : Y.functionFieldˣ := Units.mk0 h hh0 with hH
    have hHη : ratPull p s n η = (H : Y.functionField) • ω0 := hh.symm

    have hgy : G.IsEqn (s y) g := by
      obtain ⟨V, hV, hgV⟩ := hg.exists_nhds
      exact hgV _ (hyx.mem_open V.isOpen hV)
    have hfy : D₀.IsEqn (s y) f := by
      obtain ⟨V, hV, hfV⟩ := hf.exists_nhds
      exact hfV _ (hyx.mem_open V.isOpen hV)

    have hoff : ∀ v, v ⤳ y → Order.coheight v = 1 → (∀ j : J, v ≠ w j) → v ∉ B := by
      intro v hv h1 hne hvB
      obtain ⟨j, hj, rfl⟩ := (hc.mem v hv h1).1 hvB
      exact hne ⟨j, hj⟩ rfl
    have hHv : ∀ v, v ⤳ y → Order.coheight v = 1 → (∀ j : J, v ≠ w j) →
        Scheme.ord (H : Y.functionField) v = 0 := by
      intro v hv h1 hne
      obtain ⟨F, hF⟩ := DivOver.exists_isAt_of_coheight_eq_one (p := s ≫ p) h1
      have e1 := hK v F h1 (hoff v hv h1 hne) hF
      change F.formOrd (ratPull p s n η) = 0 at e1
      rw [hHη, F.formOrd_smul hnY h0, DivOver.formOrd_formOf_eq_zero (hv.mem_open U.isOpen hyU) hF hc.frame,
        add_zero, hF.ord_eq] at e1
      exact e1
    have hM := fun φ hφ => GlobalTheory.T.primeDivisorOver_ord_eq_sum_adaptedMonomial E' y hy (ι := J) (fun j => w j) (fun j => u j)
      (fun a b e => Subtype.ext (hc.inj a.2 b.2 e)) (fun j => hc.spec j j.2) (fun j => hc.coheight j j.2)
      (fun j => hc.ord_self j j.2) (fun j v hv _ hne => hc.ord_other j j.2 v hv hne) φ hφ
    have hMH := hM H hHv
    have hMg := hM (fnPull s g) fun v hv h1 hne => hG y v g hv h1 (hoff v hv h1 hne) hgy
    have hMf := hM (fnPull s f) fun v hv h1 hne => hD y v f hv h1 (hoff v hv h1 hne) hfy

    have hFj : ∀ j : J, ∃ F : DivOver (s ≫ p), F.IsAt (w j) := fun j =>
      DivOver.exists_isAt_of_coheight_eq_one (hc.coheight j j.2)
    choose F hF using hFj
    have hEj : ∀ j : J, ∃ Ej : DivOver p, DivOver.Over s (F j) Ej := fun j => GlobalTheory.T.exists_primeDivisor_over_target_of_birational p s hbij (F j)
    choose Es hEs using hEj
    have hA := GlobalTheory.T.birational_primeDivisor_orders_functions_topForms p n hn s hbij E E' hE'
    have hAj := fun j => GlobalTheory.T.birational_primeDivisor_orders_functions_topForms p n hn s hbij (Es j) (F j) (hEs j)

    set t : J → ℤ := fun j => E'.ord (u j) with ht
    have htn : ∀ j, 0 ≤ t j := fun j => by
      refine (E'.ord_nonneg_iff _).2 (hy _ ?_)
      rw [hc.val j j.2]
      exact regAt_fnOf hyU _ _
    set Fo := E'.formOrd ω0 with hFo
    have hlog : ∑ j : J, t j - 1 ≤ Fo :=
      GlobalTheory.T.sum_ord_sub_one_le_ord_wedgeDifferentials hnY E' hyU hy z h0 (J := J) Subtype.val Subtype.val_injective (fun j => u j)
        fun j => hc.val j j.2
    have hnn : 0 ≤ Fo := DivOver.formOrd_formOf_nonneg hnY hyU hy (dOn (s ≫ p) z) h0
    have eFE : E.formOrd η = ∑ j : J, Scheme.ord (H : Y.functionField) (w j) * t j + Fo := by
      have hAform : E'.formOrd (ratPull p s n η) = E.formOrd η := hA.2 η hη
      rw [← hAform, hHη, E'.formOrd_smul hnY h0, hMH]
    have egE : E.ord g = ∑ j : J, Scheme.ord (fnPull s g : Y.functionField) (w j) * t j := by
      rw [← hA.1 g, hMg]
    have efE : E.ord f = ∑ j : J, Scheme.ord (fnPull s f : Y.functionField) (w j) * t j := by
      rw [← hA.1 f, hMf]
    have eFj : ∀ j, (Es j).formOrd η = Scheme.ord (H : Y.functionField) (w j) := fun j => by
      have hAform : (F j).formOrd (ratPull p s n η) = (Es j).formOrd η := (hAj j).2 η hη
      rw [← hAform, hHη, (F j).formOrd_smul hnY h0,
        DivOver.formOrd_formOf_eq_zero ((hc.spec j j.2).mem_open U.isOpen hyU) (hF j) hc.frame, add_zero,
        (hF j).ord_eq]
    have egj : ∀ j, (Es j).ord g = Scheme.ord (fnPull s g : Y.functionField) (w j) := fun j => by
      rw [← (hAj j).1 g, (hF j).ord_eq]
    have efj : ∀ j, (Es j).ord f = Scheme.ord (fnPull s f : Y.functionField) (w j) := fun j => by
      rw [← (hAj j).1 f, (hF j).ord_eq]
    have key : ∑ j : J, (1 + (discrep (Es j) η m g - c * (Es j).ord f)) * (t j : ℚ) =
        1 + (discrep E η m g - c * E.ord f) - (1 + Fo - ∑ j : J, (t j : ℚ)) := by
      simp only [discrep, eFE, egE, efE, eFj, egj, efj]
      push_cast
      rw [Finset.sum_div, Finset.mul_sum]
      have : ∀ j : J, (1 + ((Scheme.ord (H : Y.functionField) (w j) : ℚ) -
          (Scheme.ord (fnPull s g : Y.functionField) (w j) : ℚ) / m -
          c * (Scheme.ord (fnPull s f : Y.functionField) (w j) : ℚ))) * (t j : ℚ) =
          (t j : ℚ) + (Scheme.ord (H : Y.functionField) (w j) : ℚ) * t j -
          (Scheme.ord (fnPull s g : Y.functionField) (w j) : ℚ) * t j / m -
          c * ((Scheme.ord (fnPull s f : Y.functionField) (w j) : ℚ) * t j) := fun j => by ring
      rw [Finset.sum_congr rfl fun j _ => this j, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
        Finset.sum_add_distrib]
      ring
    refine ⟨J, inferInstance, Es, t, fun j => ⟨?_, ?_, htn j⟩, fun h0' => ?_, fun ⟨j0, hj0⟩ => ?_⟩
    · refine Set.mem_biUnion (x := w j) ⟨(hc.mem _ (hc.spec j j.2) (hc.coheight j j.2)).2 ⟨j, j.2, rfl⟩,
        hc.coheight j j.2⟩ fun a => (hEs j a).trans (hF j _)
    · intro a ha
      refine (hEs j a).2 ((hF j _).2 (regAt_of_specializes (hc.spec j j.2) ?_))
      exact GlobalTheory.Cartier.PullDominant.regAt_map s (regAt_of_specializes hyx ha)
    · have hs0 : ∑ j : J, (1 + (discrep (Es j) η m g - c * (Es j).ord f)) * (t j : ℚ) = 0 :=
        Finset.sum_eq_zero fun j _ => by rw [h0' j]; simp
      have ht0 : ∑ j : J, (t j : ℚ) = 0 := Finset.sum_eq_zero fun j _ => by rw [h0' j]; simp
      have : (0 : ℚ) ≤ Fo := by exact_mod_cast hnn
      linarith
    · have h1 : 1 ≤ ∑ j : J, t j := by
        have := Finset.single_le_sum (f := t) (fun j _ => htn j) (Finset.mem_univ j0)
        have : 1 ≤ t j0 := by have := htn j0; omega
        omega
      have h1q : (1 : ℚ) ≤ ∑ j : J, (t j : ℚ) := by exact_mod_cast h1
      have hlq : (∑ j : J, (t j : ℚ)) - 1 ≤ Fo := by exact_mod_cast hlog
      rw [key]
      linarith
  refine ⟨fun hS E hE => ?_, fun hS E hE => ?_⟩
  · obtain ⟨ι, _, Es, t, hEs, h0, h1⟩ := core E hE
    by_cases hall : ∀ j, t j = 0
    · have := h0 hall
      linarith
    · push_neg at hall
      have hpos : 0 < ∑ j, (1 + (discrep (Es j) η m g - c * (Es j).ord f)) * (t j : ℚ) := by
        obtain ⟨j0, hj0⟩ := hall
        refine Finset.sum_pos' (fun j _ => mul_nonneg ?_ ?_) ⟨j0, Finset.mem_univ _, mul_pos ?_ ?_⟩
        · have := hS (Es j) (hEs j).1 (hEs j).2.1; linarith
        · exact_mod_cast (hEs j).2.2
        · have := hS (Es j0) (hEs j0).1 (hEs j0).2.1; linarith
        · have : 0 < t j0 := lt_of_le_of_ne (hEs j0).2.2 (Ne.symm hj0)
          exact_mod_cast this
      have := h1 hall
      linarith
  · obtain ⟨ι, _, Es, t, hEs, h0, h1⟩ := core E hE
    by_cases hall : ∀ j, t j = 0
    · have := h0 hall
      linarith
    · push_neg at hall
      have hnn : 0 ≤ ∑ j, (1 + (discrep (Es j) η m g - c * (Es j).ord f)) * (t j : ℚ) := by
        refine Finset.sum_nonneg fun j _ => mul_nonneg ?_ ?_
        · have := hS (Es j) (hEs j).1 (hEs j).2.1; linarith
        · exact_mod_cast (hEs j).2.2
      have := h1 hall
      linarith

end GlobalTheory.PairStep
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PinnedDataGiven

theorem latEmb_iotaW {D : D7} (T : CoreJ D) (hT : LawsJ T) (i : Fin D.R.m) : LatEmb (Wc D i) (iotaW T i) := by
  have key : ∀ (V : HSp D) (_ : T.V ((i : ℕ) + 1) T.toCore.σ₀ = V) (hr : V.rank = D.R.r),
      LatEmb V (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota ((i : ℕ) + 1)) := by
    rintro V rfl hr
    obtain ⟨_, -, -, -, -, -, -, hemb, -⟩ := hT.adPin _ (inR i) _ T.toCore.good_σ₀
    exact hemb
  exact key _ (hT.spaceW _ (inR i) _ T.toCore.good_σ₀) (rank_Wc i)



theorem exists_pins_given : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) , R.toLevCh.Is A.μ0 → R.grp_chiW → R.IsFam → R.IsModels → R.thP_vP → Nonempty (FWTie T R κ v₀) → T.pb = R.C.P.pb → Finite T0 → QGuard R → ∀ i : Fin D.R.m, VStd D i → ∀ (lev : G → (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La), LevIs R i (iotaW T i) T.Q.l.M (Mfr T.Q.l) lev → ∀ (gramR : Matrix (Fin D.sp.X'.rank) (Fin D.sp.X'.rank) D.host.E) (c0R : VV D.what₂.LL (fun τ => Bridge.lamRdef (Ptw D) τ) →ₛₗ[D.what₂.embLL] R.cX.coef.W) (c0L : ∀ i : Fin D.R.m, VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).coef.W), Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ) (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L → ∃ O' : OMDat T.toCore R i T0 id, D.what₂.embLL.toRatAlgHom.fieldRange ≤ O'.c'.F ∧ O'.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O'.s0) ∧ O'.lev = lev ∧ CoefficientBaseChange R i O'.jL (inC O'.c') (c0L i) O'.c0' := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hL hchi hfam hmodels hvP hfw hpb hfin hG i hV lev hlev gramR c0R c0L htie
  obtain ⟨fw⟩ := id hfw
  have hT := fw.laws
  obtain ⟨pd, l₂, c₁, h1, h2, hc⟩ := GlobalTheory.TupleCover.exists_covers T R hT hL hpb hG i (Vc D i).rank
  choose Mφ hMφ hφ using fun t => GlobalTheory.T.exists_level_place_datum_over_number_field D G Pl0 T0 A _ R hL hvP i hV t _ (iotaW T i) (latEmb_iotaW T hT i)
  choose MB hMB hB using fun t => GlobalTheory.T.exists_numberField_heckeCharacter_sqrtNorm_values D G Pl0 T0 A _ R hL i t
  have := c₁.fin
  obtain ⟨c', hc'⟩ := GlobalTheory.TupleCover.exists_coeff_ge T.Q.l (c₁.F ⊔ ⨆ t, (Mφ t ⊔ MB t))
  have h3 : c₁.F ≤ c'.F := le_sup_left.trans hc'
  have h4 : ∀ t, Mφ t ⊔ MB t ≤ c'.F := fun t => ((le_iSup (fun t => Mφ t ⊔ MB t) t).trans le_sup_right).trans hc'
  have hle : T.Q.c.F ≤ c'.F := h1.trans h3
  have hLL := h2.trans h3
  obtain ⟨dδ, U₂, dict₂, xi, -, hcov, hhalf, hxi, hcxi, hmod, -⟩ := hc c' hle h3
  let jL : D.what₂.LL →+* c'.F := D.what₂.embLL.codRestrict c'.F fun x => hLL ⟨x, rfl⟩
  have hjL : (inC c').comp jL = D.what₂.embLL := RingHom.ext fun _ => rfl
  obtain ⟨c0', hc0, hplace⟩ := GlobalTheory.T.exists_coefficientMap_extension_rational_values D G Pl0 T0 A _ R hL hchi hfam hmodels gramR c0R c0L htie i c'.F jL (inC c') hjL
  obtain ⟨Cl, fCl, h, J', bad, Lh, gam, vol, La, Nc, hrep, hbad, hcl⟩ :=
    GlobalTheory.SplitReps.exists_repsR_repsCov R i (hL.βV i) hV c'.F (T.Q.Xo ((i : ℕ) + 1)) c' id dδ
  choose B hBis using fun t => hB t c'.F (le_sup_right.trans (h4 t)) (bad t) (hbad t).2.2.2.2
    fun PP hPP => (hrep t).1.2.1 PP (Or.inr hPP)
  have hodd : Odd ((T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q) := by
    obtain ⟨e1, e2, -⟩ := hT.pins.2.2.2 _ (inR i)
    have h5 := Formalism.L2.NTheta.odd_r D.R
    have h6 := i.2
    have h7 := D.R.m_add_three_le_k
    rw [e1, e2]
    convert h5 using 1
    simp only [Ranks.sigW, Ranks.r]
    omega
  choose epF hepF using fun t => (GlobalTheory.ClassTieCompare.exists_epIs_iff (n := (Vc D i).rank) (Dw := T.Q.Dw ((i : ℕ) + 1))
    (bad t) (B t)).2 fun L cc g d => GlobalTheory.T.law_of_squares_selfDual_splitLattice _ _ _ _ hodd L cc g.1 g.2.2 d.1 d.2
  obtain ⟨io, hw, hio⟩ := GlobalTheory.T.exists_harmonicCoefficientMap_at_weights D T.Q hT.pins κ fw.kap i c'
  choose φ hφis using fun t => hφ t c'.F (le_sup_left.trans (h4 t)) (hhalf t).2.2 (Mfr (dδ t).l₂) fun PP hPP c hc => by
    have hM : (dδ t).l₂.Mb ≤ PP.asIdeal := by
      rw [(hcov t).1.2.2.2.1]
      rcases hPP with hPP | hPP
      · rw [(hhalf t).1]
        exact Ideal.mul_le_left.trans (Ideal.prod_le_inf.trans (Finset.inf_le hPP))
      · exact Ideal.mul_le_right.trans ((hhalf t).2.1 PP hPP)
    obtain ⟨b, hb, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ T.Q.H.bar.surjective).1 hc
    refine ⟨b, hM hb, ?_⟩
    change _ = star ((T.Q.H.bar b : 𝓞 D.host.E) : D.host.E)
    rw [T.Q.H.bar_eq]
    exact (star_star _).symm
  choose thAd hth using fun t => GlobalTheory.T.exists_adelicSide_of_models D G Pl0 T0 A _ R hmodels i t _ _ c0' _ (h t) _ (hrep t).1.2.2.1
    (hrep t).1.2.2.2.2.2.1 (v₀ i (sg0 D A))
  have hact := fun c => GlobalTheory.T.levelAction_framedPoints_isAction D G Pl0 T0 A T R hL hT hpb i c lev hlev
  refine ⟨{ c' := c', hle := hle, jL := jL, hV := hT.spaceW _ (inR i) _ rfl, c0' := c0', lev := lev, dδ := dδ, Cl' := Cl,
            bad := bad, Lh := Lh, La := La, Nc := Nc, gam := gam, vol := vol, ep := fun t k => epF t (Lh t k), B := B,
            epF := epF, io := io, hw := hw, φ := φ,
            w := fun t _ q => (dδ t).eF.symm (phiHat (dδ t).c₂ (fun x => (dδ t).eF (φ t x)) q),
            U₂ := U₂, dict₂ := dict₂, xi := xi, thAd := thAd,
            Plc := fun t x => ∃ x₀, Place R i t (h t) c0' (jVx R i t x₀) x }, hLL,
    ⟨⟨hjL, hV, fw.hv₀ i _, ⟨gramR, c0R, c0L, htie, hc0⟩, hlev⟩,
    fun t => ⟨⟨h t, J' t, (hrep t).1, hplace t _ _, hth t, fun _ => Iff.rfl⟩, hBis t, hxi t, hφis t, hhalf t⟩,
    ⟨hact _, hact _⟩,
    hbad, hcl, fun t => ⟨fun _ => rfl, hepF t⟩, hio, fun t k q => AlgEquiv.apply_symm_apply _ _, hcov, hcxi, hmod⟩, rfl, hc0⟩

end GlobalTheory.PinnedDataGiven
end
end

section

open IsLocalRing TensorProduct

namespace GlobalTheory

theorem isReduced_of_isRegularRing (R : Type) [CommRing R] [IsRegularRing R] : IsReduced R :=
  isReduced_ofLocalizationMaximal R fun P _ => by
    haveI := ReciprocityTheory.AnForm.R.isDomain_of_isRegularLocalRing (R := Localization.AtPrime P)
    infer_instance

theorem tensor_map_injective_of_field (A M K L : Type) [CommRing A] [CommRing M] [Algebra A M]
    [Field K] [Field L] [Algebra A K] [Algebra A L] (ι : K →ₐ[A] L) :
    Function.Injective (Algebra.TensorProduct.map (AlgHom.id A M) ι) := by
  letI : Algebra K L := ι.toRingHom.toAlgebra
  haveI : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq fun a => (ι.commutes a).symm
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K L)
    (LinearMap.ker_eq_bot.mpr (algebraMap K L).injective)
  have hcomp : (r.restrictScalars A) ∘ₗ ι.toLinearMap = LinearMap.id := by
    ext k
    exact LinearMap.congr_fun hr k
  intro x y hxy
  have h := congrArg (LinearMap.lTensor M (r.restrictScalars A)) hxy
  have key : ∀ z : M ⊗[A] K,
      LinearMap.lTensor M (r.restrictScalars A) (Algebra.TensorProduct.map (AlgHom.id A M) ι z) = z := by
    intro z
    have : (LinearMap.lTensor M (r.restrictScalars A)) ∘ₗ (LinearMap.lTensor M ι.toLinearMap) =
        LinearMap.id := by
      rw [← LinearMap.lTensor_comp, hcomp, LinearMap.lTensor_id]
    have e : Algebra.TensorProduct.map (AlgHom.id A M) ι z = LinearMap.lTensor M ι.toLinearMap z := by
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp
      | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
    rw [e]
    exact LinearMap.congr_fun this z
  rwa [key, key] at h

end GlobalTheory

namespace GlobalTheory

theorem formalFibre_isReduced_of_field :
    ∀ (A L : Type) [CommRing A] [IsLocalRing A] [Algebra.EssFiniteType ℤ A] [Field L] [Algebra A L],
      IsReduced (AdicCompletion (maximalIdeal A) A ⊗[A] L) := by
  intro A L _ _ _ _ _
  classical
  refine ⟨fun x hx => ?_⟩
  obtain ⟨S, rfl⟩ := TensorProduct.exists_finset x
  set T : Subalgebra A L := Algebra.adjoin A ((S.image Prod.snd : Finset L) : Set L) with hT
  haveI : Algebra.FiniteType A T := (Subalgebra.fg_iff_finiteType T).mp (Subalgebra.fg_adjoin_finset _)
  let K := FractionRing T
  haveI : Algebra.EssFiniteType T K := Algebra.EssFiniteType.of_isLocalization K (nonZeroDivisors T)
  haveI : Algebra.EssFiniteType A K := Algebra.EssFiniteType.comp A T K
  have hinj : Function.Injective (IsScalarTower.toAlgHom T T L) := Subtype.val_injective
  let ι : K →ₐ[A] L := (IsFractionRing.liftAlgHom (K := K) hinj).restrictScalars A
  have hι : ∀ t : T, ι (algebraMap T K t) = t := fun t => by
    simp [ι, IsFractionRing.liftAlgHom_apply]
  have hmem : ∀ i ∈ S, i.2 ∈ T := fun i hi =>
    Algebra.subset_adjoin (by simpa using ⟨i.1, hi⟩)
  let y : AdicCompletion (maximalIdeal A) A ⊗[A] K :=
    ∑ i ∈ S.attach, i.1.1 ⊗ₜ[A] algebraMap T K ⟨i.1.2, hmem i.1 i.2⟩
  let Φ := Algebra.TensorProduct.map (AlgHom.id A (AdicCompletion (maximalIdeal A) A)) ι
  have hΦ : Φ y = ∑ i ∈ S, i.1 ⊗ₜ[A] i.2 := by

    simp only [y, map_sum, Φ, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hι]
    exact Finset.sum_attach S (fun i => i.1 ⊗ₜ[A] i.2)
  haveI : IsRegularRing (AdicCompletion (maximalIdeal A) A ⊗[A] K) :=
    formalFibre_isRegularRing_of_essFiniteType_int A K
  haveI := isReduced_of_isRegularRing (AdicCompletion (maximalIdeal A) A ⊗[A] K)
  obtain ⟨n, hn⟩ := hx
  have hy : IsNilpotent y := ⟨n, tensor_map_injective_of_field A _ K L ι (by rw [map_pow, map_zero, hΦ, hn])⟩
  rw [← hΦ, IsReduced.eq_zero y hy, map_zero]

end GlobalTheory
end
