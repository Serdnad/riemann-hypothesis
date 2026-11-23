module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle033
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1210
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1400
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1399
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle637
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle260
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1209
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle962
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnSourceIffOfDensity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1401
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1168
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle749
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1480
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle741
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle231
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1402
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1197
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1405
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle002
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
import ReciprocityTheory.AnalyticForms.PotentialTheory.MaMeasureB
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle041
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038

@[expose] public section

section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem closedPoint_mem_nonzeroLocus {K : Type} [Field K] {C : Scheme.{0}} [IsIntegral C] (x : Sp K ⟶ C)
    [IsDominant x] {L : LB C} {σ : L.Sec} (hσ : σ ≠ 0) : x (IsLocalRing.closedPoint K) ∈ Out.nonzeroLocus σ := by
  have h : ∃ i, σ.f i ≠ 0 := by
    by_contra h
    push Not at h
    apply hσ
    obtain ⟨f, hf⟩ := σ
    obtain rfl : f = fun _ => 0 := funext h
    rfl
  obtain ⟨i, hi⟩ := h
  have hne : ((C.basicOpen (σ.f i) : C.Opens) : Set C).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro e
    exact hi ((basicOpen_eq_bot_iff _).1 (Opens.ext e))
  obtain ⟨y, hy⟩ := x.denseRange.exists_mem_open (C.basicOpen (σ.f i)).isOpen hne
  obtain rfl : y = IsLocalRing.closedPoint K := Subsingleton.elim _ _
  exact Opens.mem_iSup.2 ⟨i, hy⟩

theorem deg_pos_of_integral {k K : Type} [Field k] [IsAlgClosed k] [Field K] [Algebra k K] {r : ℕ}
    {g : Place k K → Matrix (Fin r) (Fin r) K} (hg : admitted g) {f : K} (hf : f ≠ 0)
    (hfin : {v : Place k K | v.1 f ≠ 1}.Finite) (hsum : ∑ᶠ v : Place k K, ord v f = 0) {m : ℕ}
    (hle : ∀ v : Place k K, v.1 (f * (g v).det ^ m) ≤ 1) {w : Place k K} (hlt : w.1 (f * (g w).det ^ m) < 1) :
    0 < deg g := by
  have hne : ∀ v, f * (g v).det ^ m ≠ 0 := fun v => mul_ne_zero hf (pow_ne_zero _ (hg.1 v))
  have hadd : ∀ v : Place k K, ord v (f * (g v).det ^ m) = ord v f + m * ord v (g v).det := fun v => by
    rw [(ord_calculus k K v).1 _ _ hf (pow_ne_zero _ (hg.1 v)), ← (ord_calculus k K v).2.1 _ (hg.1 v), zpow_natCast]
  have f₁ : (Function.support fun v : Place k K => ord v f).Finite :=
    hfin.subset fun v hv e => hv (((ord_calculus k K v).2.2.2.1 _ hf).1 e)
  have f₂ : (Function.support fun v : Place k K => ord v (g v).det).Finite :=
    hg.2.subset fun v hv e => hv (((ord_calculus k K v).2.2.2.1 _ (hg.1 v)).1 e.2)
  have f₃ : (Function.support fun v : Place k K => (m : ℤ) * ord v (g v).det).Finite :=
    f₂.subset fun v hv e => hv (by simp only [e, mul_zero])
  have hs : ∑ᶠ v : Place k K, ord v (f * (g v).det ^ m) = m * deg g := by
    simp only [hadd]
    rw [finsum_add_distrib f₁ f₃, hsum, zero_add, deg, mul_finsum' _ _ f₂]
  have h0 : ∀ v : Place k K, 0 ≤ ord v (f * (g v).det ^ m) := fun v =>
    ((ord_calculus k K v).2.2.1 _ (hne v)).1 (hle v)
  have hw : 0 < ord w (f * (g w).det ^ m) :=
    (h0 w).lt_of_ne fun e => hlt.ne (((ord_calculus k K w).2.2.2.1 _ (hne w)).2 e.symm)
  have f₄ : (Function.support fun v : Place k K => ord v (f * (g v).det ^ m)).Finite := by
    refine (f₁.union f₃).subset fun v hv => ?_
    by_contra h
    simp only [Set.mem_union, Function.mem_support, not_or, not_not] at h
    exact hv (by simp only [hadd, h.1, h.2, add_zero])
  have hpos : 0 < (m : ℤ) * deg g := by
    rw [← hs]
    exact hw.trans_le (single_le_finsum w f₄ h0)
  by_contra h
  exact absurd hpos (not_lt.2 (mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg m) (not_lt.1 h)))

theorem interNum_det_nonpos_of_deg_nonpos : ∀ (k K : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  ∀ (W : C.Modules) (r : ℕ), IsVB W r → ∀ (V₀ : C.Opens) (s : Fin r → Γ(W, V₀)) (g : Place k K → Matrix (Fin r) (Fin r) K), (V₀ : Set C).Nonempty → IsFrame s → admitted g → (∀ v, LocFrame x s v (g v)) → deg g ≤ 0 → interNum k (GlobalTheory.structureModule C) ![det W r] ≤ 0 := by
  intro k K _ _ _ _ _ C _ x hx W r hW V₀ s g hV hs hg hloc hdeg
  by_contra hpos
  have := LieSemineg.isIntegral_curve hx.1.1 hx.1.2.2
  have := hx.2.1.1
  obtain ⟨m, σ, c, -, hσ, hc⟩ := GlobalTheory.T.exists_lineBundle_pow_section_vanishing_degree_pos k C hx.1 (det W r) hW.isLB_det (not_le.1 hpos)
  obtain ⟨w, b, hb, hbc⟩ := GlobalTheory.T.curve_closedPoint_isCentreOfPlace k K C x hx c fun e => hc (e ▸ closedPoint_mem_nonzeroLocus x hσ)
  obtain ⟨f, hf, H⟩ := GlobalTheory.T.detPowSection_rational_genericPoint k K C x hx W r hW V₀ s hV hs m σ hσ
  obtain ⟨hfin, hsum⟩ := GlobalTheory.T.functionField_finite_support_sum_order_eq_zero k K (GlobalTheory.T.isFunctionFieldOfOneVariable_of_genericPointOfCurve k K C x hx) f hf
  exact (deg_pos_of_integral hg hf hfin hsum (fun v => (H v _ (hloc v)).1)
    ((H w _ (hloc w)).2 b hb (hbc ▸ hc))).not_ge hdeg

end GlobalTheory.Nef
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.ClosFacts

theorem range_closι {X : Scheme.{0}} (z : X) : range (closι z) = closure {z} :=
  range_redι (Closeds.closure {z})

theorem isIntegral_clos {X : Scheme.{0}} (z : X) : IsIntegral (clos z) :=
  isIntegral_red (Z := Closeds.closure {z}) isIrreducible_singleton.closure

theorem clos_facts : ∀ (X : Scheme.{0}) (z : X), ∃ _ : IsIntegral (clos z), closι z (genericPoint (clos z)) = z ∧ topologicalKrullDim (clos z) = topologicalKrullDim (closure ({z} : Set X)) ∧ ∀ (Y : Scheme.{0}) [IsIntegral Y] (π : Y ⟶ X), π (genericPoint Y) = z → ∃ g : Y ⟶ clos z, g ≫ closι z = π ∧ g (genericPoint Y) = genericPoint (clos z) ∧ g.residueDegree (genericPoint Y) = π.residueDegree (genericPoint Y) ∧ (IsClosedImmersion π → IsIso g) := by
  intro X z
  have hI := isIntegral_clos z
  have hr := range_closι z
  have hi : closι z (genericPoint (clos z)) = z := by
    have h₁ := (genericPoint_spec (clos z)).image (closι z).continuous
    rw [image_univ, hr, closure_closure] at h₁
    exact h₁.eq isGenericPoint_closure
  refine ⟨hI, hi, (topologicalKrullDim_eq_of_isEmbedding (closι z).isClosedEmbedding.isEmbedding hr), ?_⟩
  intro Y _ π hπ
  have : Surjective (Limits.pullback.snd (closι z) π) := ⟨by
    rw [← Set.range_eq_univ, Scheme.Pullback.range_snd, hr, ← hπ]
    exact eq_univ_of_forall fun y => ((genericPoint_specializes y).map π.continuous).mem_closure⟩
  have := isIso_of_isClosedImmersion_of_surjective (Limits.pullback.snd (closι z) π)
  obtain ⟨g, rfl⟩ : ∃ g : Y ⟶ clos z, g ≫ closι z = π :=
    ⟨inv (Limits.pullback.snd (closι z) π) ≫ Limits.pullback.fst (closι z) π, by
      rw [Category.assoc, Limits.pullback.condition, IsIso.inv_hom_id_assoc]⟩
  have hg : g (genericPoint Y) = genericPoint (clos z) :=
    (closι z).isClosedEmbedding.injective (hπ.trans hi.symm)
  refine ⟨g, rfl, hg, ?_, fun hc => ?_⟩
  · rw [GlobalTheory.CurveDegreesCompare.residueDegree_comp, GlobalTheory.Published.residueDegree_of_isClosedImmersion (closι z), one_mul]
  · have : IsClosedImmersion g := IsClosedImmersion.of_comp_isClosedImmersion g (closι z)
    have : Surjective g := ⟨by
      rw [← Set.range_eq_univ]
      have h₁ := (genericPoint_spec Y).image g.continuous
      rw [image_univ, g.isClosedEmbedding.isClosed_range.closure_eq, hg] at h₁
      exact h₁.def.symm.trans (genericPoint_spec (clos z)).def⟩
    exact isIso_of_isClosedImmersion_of_surjective g

end GlobalTheory.ClosFacts
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V cHess)
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.FinChart

namespace GlobalTheory.Mix

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

theorem maDens_locPot_eq_dens (L : Fin D → MLine p σ) (c : AlgChart p σ D) {z : Fin D → ℂ}
    (hz : z ∈ c.finChart.target) :
    maDens (fun i y => (L i).φ.locPot.φ (c.finChart.symm z) (c.finChart.symm y)) z =
      dens L c (c.finChart.symm z) := by
  have hr : c.e (c.finChart.symm z) = toV D z := c.e.right_inv hz
  have hH (i) : hessC (fun y => (L i).φ.locPot.φ (c.finChart.symm z) (c.finChart.symm y)) z =
      ((2⁻¹ : ℝ) : ℂ) • c.hess (L i).φ (pick (L i).φ.isLB (c.finChart.symm z)) (c.finChart.symm z) := by
    have hd := (L i).cInf.contDiffAt c (c.finChart.map_target hz)
      (mem_pick (L i).φ.isLB (c.finChart.symm z))
    rw [hr] at hd
    have e : (fun y => (L i).φ.locPot.φ (c.finChart.symm z) (c.finChart.symm y)) = fun y => 2⁻¹ *
        ((fun v => (L i).φ.φ (pick (L i).φ.isLB (c.finChart.symm z)) (c.e.symm v)) ∘ toV D) y :=
      funext fun _ => div_eq_inv_mul _ _
    rw [e, hessC_const_mul', AlgChart.hess, hr, cHess_eq_hessC hd]
  have hτ (τ : Equiv.Perm (Fin D)) : (Matrix.of fun j l => (((2⁻¹ : ℝ) : ℂ) •
      c.hess (L (τ l)).φ (pick (L (τ l)).φ.isLB (c.finChart.symm z)) (c.finChart.symm z)) j l).det =
      (((2⁻¹ : ℝ) ^ D : ℝ) : ℂ) * (Matrix.of fun j l =>
      c.hess (L (τ l)).φ (pick (L (τ l)).φ.isLB (c.finChart.symm z)) (c.finChart.symm z) j l).det := by
    refine (Matrix.det_smul (Matrix.of fun j l => c.hess (L (τ l)).φ
      (pick (L (τ l)).φ.isLB (c.finChart.symm z)) (c.finChart.symm z) j l) ((2⁻¹ : ℝ) : ℂ)).trans ?_
    rw [Fintype.card_fin, Complex.ofReal_pow]
  have hf : (1 / (D.factorial : ℂ)) = ((1 / (D.factorial : ℝ) : ℝ) : ℂ) := by push_cast; rfl
  have h0 : (D.factorial : ℝ) ≠ 0 := by exact_mod_cast D.factorial_ne_zero
  have h2 : (2 / Real.pi) ^ D * (2⁻¹ : ℝ) ^ D = (Real.pi ^ D)⁻¹ := by
    rw [← mul_pow, ← inv_pow]
    congr 1
    ring
  simp only [maDens, hH, ReciprocityTheory.AnForm.A.mdisc_eq_sum_perm, hτ, dens]
  rw [← Finset.mul_sum, hf, Complex.re_ofReal_mul, Complex.re_ofReal_mul, ← h2]
  field_simp

variable {A : FinHolAtlas D (CxPts p σ)}

theorem locDens_locPot_eq_dens (L : Fin D → MLine p σ) (hA : IsAlgAtlas A) (j : Fin A.n)
    {z : Fin D → ℂ} (hz : z ∈ (A.chart j).target) : locDens A (fun i => (L i).φ.locPot) j z =
      dens L (hA.anRead.chart j) ((A.chart j).symm z) := by
  unfold locDens
  rw [hA.chart_eq j] at hz ⊢
  exact maDens_locPot_eq_dens L _ hz

theorem part_eq_lintegral_locDens [SecondCountableTopology (CxPts p σ)] (L : Fin D → MLine p σ)
    (hA : IsAlgAtlas A) (ε : ℤˣ) (j : Fin A.n) (S : Set (CxPts p σ)) (hS : MeasurableSet S)
    (hs : S ⊆ (A.chart j).source) : part L ε S =
      ∫⁻ y in (A.chart j).target ∩ (A.chart j).symm ⁻¹' S,
        ENNReal.ofReal (max ((ε : ℤ) * locDens A (fun i => (L i).φ.locPot) j y) 0) := by
  have hl (y) := locDens_locPot_eq_dens L hA j (z := y)
  generalize locDens A (fun i => (L i).φ.locPot) j = d at hl ⊢
  rw [hA.chart_eq j] at hs hl ⊢
  set c := hA.anRead.chart j
  have hm := measurableSet_image c.e hS hs
  rw [GlobalTheory.T.mixedChernFormSignedPartMeasure_chart_apply k X p σ D L ε c S hS hs,
    ← measurePreserving_toV.setLIntegral_comp_preimage_emb (toV D).toHomeomorph.measurableEmbedding]
  have e : c.e '' S = c.e.target ∩ c.e.symm ⁻¹' S := by
    rw [← c.e.image_source_inter_eq', inter_eq_right.2 (show S ⊆ c.e.source from hs)]
  rw [e] at hm ⊢
  refine setLIntegral_congr_fun (hm.preimage (toV D).continuous.measurable) fun y hy => ?_
  simp only [ENNReal.ofReal_max, ENNReal.ofReal_zero, zero_le, max_eq_left, hl y hy.1]
  rfl

theorem int_eq_mInt (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ)
    [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)] [SecondCountableTopology (CxPts p σ)] (D : ℕ)
    (A : FinHolAtlas D (CxPts p σ)) (hA : IsAlgAtlas A) (L : Fin D → MLine p σ)
    (g : CxPts p σ → ℝ) (hg : Measurable g) :
    (Intg L g ↔ MIntegrable A (fun i => (L i).φ.locPot) g) ∧
      (Intg L g → Mix.int L g = mInt A (fun i => (L i).φ.locPot) g) := by
  have hne : Nonempty (ChartPartition A) := existsPartition A
  set P := hne.some
  set d := locDens A fun i => (L i).φ.locPot with hd
  have hdc (j) : ContinuousOn (d j) (A.chart j).target := locDensCont A _
    (fun i => ((Weight.isCInf_iff_isSmooth hA.anRead).1 (L i).cInf).isPotential hA) j
  let w (ε : ℤˣ) (j) (y) : ℝ := max ((ε : ℤ) * d j y) 0
  have hw (ε j) : ContinuousOn (w ε j) (A.chart j).target :=
    (continuous_id.max continuous_const).comp_continuousOn (continuousOn_const.mul (hdc j))
  have hw0 (ε j) : ∀ y ∈ (A.chart j).target, 0 ≤ w ε j y := fun _ _ => le_max_right _ _
  have hsub (j y) : w 1 j y - w (-1) j y = d j y := by
    simpa [w] using max_zero_sub_max_neg_zero_eq_self (d j y)
  have habs (ε j y) : |w ε j y| ≤ |d j y| := by
    rw [abs_of_nonneg (le_max_right _ _)]
    refine max_le ((le_abs_self _).trans_eq ?_) (abs_nonneg _)
    rcases Int.units_eq_one_or ε with rfl | rfl <;> simp
  have back (hm : MIntegrable A (fun i => (L i).φ.locPot) g) (ε j) : IntegrableOn
      (fun y => P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * w ε j y)
      (A.chart j).target := by
    obtain ⟨hKc, hKs⟩ := image_closed_compact (A.chart j) (isClosed_tsupport (P.χ j))
      (P.tsupport_subset j)
    refine integrableOn_target_of_closed (A.chart j) (Z := tsupport (P.χ j))
      (fun y _ hy => by simp [image_eq_zero_of_notMem_tsupport hy]) ?_
    have hcc := (chi_comp_continuousOn P j).mono hKs
    refine Integrable.mono ((hm j _ hKs hKc).continuousOn_mul hcc hKc) ?_ (.of_forall fun y => ?_)
    · exact (((hcc.aemeasurable hKc.measurableSet).mul (hg.comp_aemeasurable
        (((A.chart j).continuousOn_symm.mono hKs).aemeasurable hKc.measurableSet))).mul
        (((hw ε j).mono hKs).aemeasurable hKc.measurableSet)).aestronglyMeasurable
    · simp only [Real.norm_eq_abs, abs_mul, ← mul_assoc]
      exact mul_le_mul_of_nonneg_left (habs ε j y) (by positivity)
  have pieces (hm : MIntegrable A (fun i => (L i).φ.locPot) g) (ε) :=
    integrable_of_pieces A P (hw ε) (hw0 ε) (part_eq_lintegral_locDens L hA ε) hg (back hm ε)
  have fwd (hi : Intg L g) : MIntegrable A (fun i => (L i).φ.locPot) g :=
    fun j K hK _ => by
    have key (ε) := (integrableOn_source_iff_of_density (A.chart j) (hw ε j) (hw0 ε j)
      (part_eq_lintegral_locDens L hA ε j) hg).1.1
    refine IntegrableOn.mono_set ?_ hK
    refine (Integrable.sub (key 1 hi.1.integrableOn) (key (-1) hi.2.integrableOn)).congr
      (.of_forall fun y => ?_)
    simp only [Pi.sub_apply, ← mul_sub, hsub, hd]
  refine ⟨⟨fwd, fun hm => ⟨(pieces hm 1).1, (pieces hm (-1)).1⟩⟩, fun hi => ?_⟩
  have hm := fwd hi
  have hmi : mInt A (fun i => (L i).φ.locPot) g = integralWith A hne.some (fun i => (L i).φ.locPot) g := by
    unfold mInt
    rw [dite_eq_left hne]
  rw [Mix.int, (pieces hm 1).2, (pieces hm (-1)).2,
    hmi, integralWith, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← integral_sub (back hm 1 j) (back hm (-1) j)]
  simp only [← mul_sub, hsub, hd, P]

end GlobalTheory.Mix
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace GlobalTheory.CoverDegProj

theorem etale_morphismRestrict {X Y : Scheme.{0}} (π : Y ⟶ X) (U : X.Opens) (hU : IsAffineOpen U)
    (hπU : IsAffineOpen (π ⁻¹ᵁ U)) (hét : (π.app U).hom.Etale) : Etale (π ∣_ U) := by
  haveI : IsAffine U := hU
  haveI : IsAffine (π ⁻¹ᵁ U) := hπU
  rw [HasRingHomProperty.iff_of_isAffine (P := @Etale), Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE,
    morphismRestrict_appLE]
  refine (Scheme.Hom.appLE_congr π _ (Scheme.Opens.ι_image_top U) (V' := π ⁻¹ᵁ U) ?_
    (fun φ => RingHom.Etale φ.hom)).2 ?_
  · rw [Scheme.Hom.preimage_top, Scheme.Opens.ι_image_top]
  · rw [← Scheme.Hom.app_eq_appLE]; exact hét

theorem etale_pullback_coords_of_etale {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k}
    (π : Y ⟶ X) (hπ : π ≫ p = q) (D : ℕ) (U : X.Opens) (hU : IsAffineOpen U)
    (hπU : IsAffineOpen (π ⁻¹ᵁ U)) (hét : (π.app U).hom.Etale) (W : X.Opens) (x : Fin D → Γ(X, W))
    (hW : IsAffineOpen W) (hx : (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p W) x).Etale)
    (z : Y) (hzU : π z ∈ U) (hzW : π z ∈ W) :
    ∃ V : Y.Opens, IsAffineOpen V ∧ z ∈ V ∧ ∃ h : V ≤ π ⁻¹ᵁ W,
      (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX q V) (fun a => (π.appLE W V h).hom (x a))).Etale := by
  subst hπ
  have hE := etale_morphismRestrict π U hU hπU hét
  obtain ⟨f, g, hfg, hz⟩ := exists_basicOpen_le_affine_inter hU hW (π z) ⟨hzU, hzW⟩
  have hW'U : X.basicOpen f ≤ U := X.basicOpen_le f
  have hW'W : X.basicOpen f ≤ W := hfg ▸ X.basicOpen_le g
  have hW' : IsAffineOpen (X.basicOpen f) := hU.basicOpen f
  have hV : IsAffineOpen (π ⁻¹ᵁ X.basicOpen f) := by
    rw [Scheme.Hom.preimage_basicOpen]; exact hπU.basicOpen _
  have hVU : π ⁻¹ᵁ X.basicOpen f ≤ π ⁻¹ᵁ U := fun y hy => hW'U hy
  have h : π ⁻¹ᵁ X.basicOpen f ≤ π ⁻¹ᵁ W := fun y hy => hW'W hy
  refine ⟨π ⁻¹ᵁ X.basicOpen f, hV, hz, h, ?_⟩

  have e1 : MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX (π ≫ p) (π ⁻¹ᵁ X.basicOpen f))
      (fun a => (π.appLE W _ h).hom (x a)) =
      (π.appLE W _ h).hom.comp (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p W) x) := by
    rw [MvPolynomial.comp_eval₂Hom, GlobalTheory.CoverDeg.algX_comp p π W _ h]
  rw [e1]
  refine RingHom.Etale.stableUnderComposition _ _ hx ?_

  have e2 : π.appLE W (π ⁻¹ᵁ X.basicOpen f) h =
      X.presheaf.map (homOfLE hW'W).op ≫ π.appLE (X.basicOpen f) (π ⁻¹ᵁ X.basicOpen f) le_rfl := by
    rw [Scheme.Hom.map_appLE]
  rw [e2, CommRingCat.hom_comp]
  refine RingHom.Etale.stableUnderComposition _ _ (GlobalTheory.CoverDeg.etale_map_basicOpen hW g _ hfg hW'W) ?_

  have ha : IsAffineOpen (U.ι ⁻¹ᵁ X.basicOpen f) :=
    hW'.preimage_of_isOpenImmersion U.ι (by rw [Scheme.Opens.opensRange_ι]; exact hW'U)
  have hb : IsAffineOpen ((π ⁻¹ᵁ U).ι ⁻¹ᵁ (π ⁻¹ᵁ X.basicOpen f)) :=
    hV.preimage_of_isOpenImmersion _ (by rw [Scheme.Opens.opensRange_ι]; exact hVU)
  have e3 : (π ⁻¹ᵁ U).ι ⁻¹ᵁ (π ⁻¹ᵁ X.basicOpen f) ≤ (π ∣_ U) ⁻¹ᵁ (U.ι ⁻¹ᵁ X.basicOpen f) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, morphismRestrict_ι]
  have := HasRingHomProperty.appLE @Etale (π ∣_ U) hE ⟨_, ha⟩ ⟨_, hb⟩ e3
  rw [morphismRestrict_appLE] at this
  refine (Scheme.Hom.appLE_congr π _ ?_ ?_ (fun φ => RingHom.Etale φ.hom)).1 this
  · rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]; exact inf_eq_right.2 hW'U
  · rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]; exact inf_eq_right.2 hVU

theorem exists_open_covering_charts : ∀ (F : Type) [Field F] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp F) (q : Y ⟶ Sp F) (σ : F →+* ℂ) (D : ℕ), IsProjOver p → IsProjOver q → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∃ U : X.Opens, genericPoint X ∈ U ∧ (∀ y ∈ ptsIn p σ U, (ptMap π hπ σ ⁻¹' {y}).encard = (π.residueDegree (genericPoint Y) : ℕ∞)) ∧ (∀ z : CxPts q σ, ptMap π hπ σ z ∈ ptsIn p σ U → ∀ c : AlgChart p σ D, ptMap π hπ σ z ∈ c.e.source → ∃ c' : AlgChart q σ D, z ∈ c'.e.source ∧ ∀ w ∈ c'.e.source, ptMap π hπ σ w ∈ c.e.source ∧ c'.e w = c.e (ptMap π hπ σ w)) := by
  intro k _ X Y _ _ p q σ D hpP hqP π hπ hη hδ
  haveI : CharZero k := RingHom.charZero σ
  obtain ⟨U, hU, hxU, hV, he, hf, hr⟩ :=
    GlobalTheory.GenFinEtField.exists_affine_finite_etale_free k X Y p q hpP hqP π hπ hη hδ
  refine ⟨U, hxU, fun y hy => ?_, fun z hz c hc => ?_⟩
  · rw [GlobalTheory.encard_fibre_eq_encard_ringHom π hπ U hU hV σ y hy]
    exact GlobalTheory.EtaleComplexPoints.encard_complexPoints_eq_rank (π.app U).hom _ he hf hr _
  · set y := PtsOver.map π hπ (spMap σ) z with hy
    have hyc : y ∈ ptsIn p σ c.U := c.source_subset hc
    have hpt : ∀ W : X.Opens, y ∈ ptsIn p σ W → π (z.1 (IsLocalRing.closedPoint ℂ)) ∈ W := by
      intro W hW
      have := mem_ptsIn.1 hW
      exact this
    obtain ⟨V, hVa, hzV, h, hVe⟩ := etale_pullback_coords_of_etale π hπ D U hU hV he c.U c.x c.affine c.etale _ (hpt U hz) (hpt c.U hyc)
    obtain ⟨c'', hc'', hU'', hx''⟩ := AlgChart.exists_of_etale (σ := σ) hVa _ hVe (mem_ptsIn.2 hzV)
    have key : ∀ w ∈ c''.e.source, w ∈ ptsIn q σ V ∧
        ∀ a, c''.e w a = ev q σ V ((π.appLE c.U V h).hom (c.x a)) w := by
      rcases c'' with ⟨e, U', aff, x', et, ss, ae, ho⟩
      dsimp only at hU'' hx'' ⊢
      subst hU''
      have hx : x' = fun a => (π.appLE c.U U' h).hom (c.x a) := hx''
      subst hx
      exact fun w hw => ⟨ss hw, ae w hw⟩
    have hS : IsOpen (c''.e.source ∩ PtsOver.map π hπ (spMap σ) ⁻¹' c.e.source) :=
      (PtsOver.continuous_map π hπ (spMap σ)).continuousOn.isOpen_inter_preimage c''.e.open_source
        c.e.open_source
    refine ⟨c''.restr _ hS, ⟨hc'', hc'', hc⟩, fun w hw => ⟨hw.2.2, ?_⟩⟩
    have hw' : w ∈ c''.e.source := hw.1
    obtain ⟨hwV, hwe⟩ := key w hw'
    ext a
    change c''.e w a = c.e (PtsOver.map π hπ (spMap σ) w) a
    rw [hwe a, c.apply_eq _ hw.2.2 a]
    exact valR_appLE w.1 π h hwV _

end GlobalTheory.CoverDegProj
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

theorem _root_.GlobalTheory.T.chernFormPowerIntegral_hermLineBundle_pow : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L : HermLB p) (n : ℕ) (w : ∀ σ, CxPts p σ → ℝ), chInt (L.pow n) D w = (n : ℝ) ^ D * chInt L D w := by
  first | exact @GlobalTheory.HSAmp.chInt_pow | exact GlobalTheory.HSAmp.chInt_pow | (intros; apply GlobalTheory.HSAmp.chInt_pow <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.smoothWeightedLineBundle_isometry_calculus : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (π : Y ⟶ X) (hπ : π ≫ p = q), (∀ A : MLine p σ, A.Isom A) ∧ (∀ A B : MLine p σ, A.Isom B → (A.pull π hπ).Isom (B.pull π hπ)) ∧ (∀ A B : MLine p σ, ((A.tens B).pull π hπ).Isom ((A.pull π hπ).tens (B.pull π hπ))) ∧ (∀ (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y), ((MLine.ofFun u hu).pull π hπ).Isom (MLine.ofFun (fun z => u (ptMap π hπ σ z)) fun z => (hu _).pull π hπ)) ∧ (∀ (A : MLine p σ) (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y), (A.addFn u hu).Isom (A.tens (MLine.ofFun u hu))) ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp k) (g : Z ⟶ Y) (hg : g ≫ q = r) (h : (g ≫ π) ≫ p = r) (A : MLine p σ), ((A.pull π hπ).pull g hg).Isom (A.pull (g ≫ π) h) := by
  first | exact @GlobalTheory.Mix.isom_calculus | exact GlobalTheory.Mix.isom_calculus | (intros; apply GlobalTheory.Mix.isom_calculus <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.exists_pullback_section_zeros_norm_multiplicities : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (π : Y ⟶ X) (hπ : π ≫ p = q) (M : MLine p σ) (s : M.B.Sec), ∃ s' : (M.pull π hπ).B.Sec, nonzeroLocus s' = π ⁻¹ᵁ nonzeroLocus s ∧ (∀ y, (M.pull π hπ).φ.nsq (secVal q σ s') y = M.φ.nsq (secVal p σ s) (ptMap π hπ σ y)) ∧ ∀ [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y] (hη : π (genericPoint Y) ⤳ genericPoint X) (hs : genericPoint X ∈ nonzeroLocus s) (hs' : genericPoint Y ∈ nonzeroLocus s') (w : Y) (i : M.B.ι), π w ∈ M.B.U i → (divOfSec (M.pull π hπ).φ.isLB s' hs').mult w = Scheme.ord (TrueGeo.SmallSec.fnMap π hη (ratOfSec s hs i : X.functionField)) w := by
  first | exact @GlobalTheory.Mix.exists_secPull_props | exact GlobalTheory.Mix.exists_secPull_props | (intros; apply GlobalTheory.Mix.exists_secPull_props <;> assumption)
end

section

open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.TowU


theorem _root_.GlobalTheory.T.exists_darbouxOperators_levi_and_double : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ] [DecidableEq κ], ∀ A : Matrix κ κ F, IsUnit A.det → ∃ (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (S' : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)), IsOp2 ψ (GlobalTheory.AdelicSvN.act (Matrix.fromBlocks A 0 0 (A⁻¹)ᵀ)) S S' := by
  first | exact @GlobalTheory.TowU.realised_levi2 | exact GlobalTheory.TowU.realised_levi2 | (intros; apply GlobalTheory.TowU.realised_levi2 <;> assumption)
end
