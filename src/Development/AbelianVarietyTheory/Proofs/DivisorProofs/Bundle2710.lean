module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2308
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle120
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1217
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle785
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1625
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineEtaleFiniteNbhdGeneric
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle774
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle991
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle598
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Convex.Contractible
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
public import Mathlib.Topology.Algebra.MvPolynomial
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle027
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle026
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
import Formalism.DegreeFormula.FlagDegFormula
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open MeasureTheory GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.Points
open scoped ENNReal

noncomputable section

namespace GlobalTheory.ChernNull

open Set CxPts
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

theorem exists_poly_dvd {k R : Type} [CommRing k] [IsDomain k] [CommRing R] [IsDomain R] {D : ℕ}
    (f : MvPolynomial (Fin D) k →+* R) (hf : f.Etale) (g : R) (hg : g ≠ 0) :
    ∃ Q : MvPolynomial (Fin D) k, Q ≠ 0 ∧ ∃ r : R, f Q = g * r := by
  letI := f.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin D) k) R := hf
  obtain ⟨Q, hQ, r, hr⟩ := (WeilIntegral.isAlgebraic_of_etale (MvPolynomial (Fin D) k) R g).exists_nonzero_dvd
    (mem_nonZeroDivisors_of_ne_zero hg)
  exact ⟨Q, hQ, r, hr⟩

theorem analyticAt_eval {D : ℕ} (P : MvPolynomial (Fin D) ℂ) (z : Fin D → ℂ) :
    AnalyticAt ℂ (fun w : Fin D → ℂ => MvPolynomial.eval w P) z := by
  induction P using MvPolynomial.induction_on
  next a =>
    simp only [MvPolynomial.eval_C]
    exact analyticAt_const
  next p q hp hq =>
    simp only [map_add (f := _)]
    exact hp.add hq
  next p i hp =>
    simp only [map_mul, MvPolynomial.eval_X]
    exact hp.mul ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin D => ℂ) i).analyticAt z)

theorem volume_poly_zero (D : ℕ) (P : MvPolynomial (Fin D) ℂ) (hP : P ≠ 0) :
    volume {v : ReciprocityTheory.L2DbarEstimates.V D | MvPolynomial.eval (fun a => v a) P = 0} = 0 := by
  obtain ⟨w, hw⟩ : ∃ w, MvPolynomial.eval w P ≠ 0 := by
    by_contra h
    push_neg at h
    exact hP (MvPolynomial.funext fun x => by simpa using h x)
  have h0 := ReciprocityTheory.AnForm.volume_zero_set_of_analyticOnNhd isOpen_univ isPreconnected_univ
    (fun z _ => analyticAt_eval P z) ⟨w, mem_univ _, hw⟩
  have hs : {z : Fin D → ℂ | z ∈ univ ∧ MvPolynomial.eval z P = 0} =
      {z : Fin D → ℂ | MvPolynomial.eval z P = 0} := by
    ext z
    simp
  have hT : MeasurableSet {z : Fin D → ℂ | MvPolynomial.eval z P = 0} :=
    (isClosed_eq (MvPolynomial.continuous_eval P) continuous_const).measurableSet
  rw [hs] at h0
  rw [← (volume_preserving_ofLp_complex (Fin D)).measure_preimage hT.nullMeasurableSet] at h0
  refine measure_mono_null (fun v hv => ?_) h0
  exact hv

theorem injective_of_arithVar {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ}
    (h : IsArithVar p D) (σ : k →+* ℂ) : Function.Injective σ := by
  have := h.isDomain
  have := h.finite
  have hk : RingHom.ker σ = ⊥ := Ideal.eq_bot_of_comap_eq_bot (R := ℤ) (by
    ext n
    simp [Ideal.mem_comap, RingHom.mem_ker])
  refine (injective_iff_map_eq_zero σ).2 fun a ha => ?_
  have : a ∈ RingHom.ker σ := ha
  rwa [hk, Ideal.mem_bot] at this

theorem exists_sec_vanish {X : Scheme.{0}} [IsIntegral X] {U : X.Opens} (hU : IsAffineOpen U)
    (hne : (U : Set X).Nonempty) {Z : Set X} (hZ : IsClosed Z) (hgen : genericPoint X ∉ Z) :
    ∃ g : Γ(X, U), g ≠ 0 ∧ ∀ z ∈ U, z ∈ Z → z ∉ X.basicOpen g := by
  have hgU : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).2 (by simpa using hne)
  let W : X.Opens := U ⊓ ⟨Zᶜ, hZ.isOpen_compl⟩
  obtain ⟨g, hgW, hgm⟩ := hU.exists_basicOpen_le (V := W) ⟨genericPoint X, ⟨hgU, hgen⟩⟩ hgU
  refine ⟨g, fun e => ?_, fun z _ hz hzg => (hgW hzg).2 hz⟩
  rw [e, X.basicOpen_zero] at hgm
  exact hgm

theorem chart_null {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    {D : ℕ} (h : IsArithVar p D) {Z : Set X} (hZ : IsClosed Z) (hgen : genericPoint X ∉ Z)
    (σ : k →+* ℂ) (c : AlgChart p σ D) :
    volume (c.e '' (c.e.source ∩ {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ Z})) = 0 := by
  rcases c.e.source.eq_empty_or_nonempty with hs | ⟨y0, hy0⟩
  · simp [hs]
  have hne : (c.U : Set X).Nonempty := ⟨_, mem_ptsIn.1 (c.source_subset hy0)⟩
  haveI : Nonempty c.U := ⟨⟨_, mem_ptsIn.1 (c.source_subset hy0)⟩⟩
  have := h.isDomain
  obtain ⟨g, hg0, hgZ⟩ := exists_sec_vanish c.affine hne hZ hgen
  obtain ⟨Q, hQ, r, hQr⟩ := exists_poly_dvd _ c.etale g hg0
  have hP : MvPolynomial.map σ Q ≠ 0 := fun e =>
    hQ (MvPolynomial.map_injective σ (injective_of_arithVar h σ) (by rw [e, map_zero]))
  refine measure_mono_null ?_ (volume_poly_zero D _ hP)
  rintro _ ⟨y, ⟨hys, hyZ⟩, rfl⟩
  have hyU := c.source_subset hys
  have hgy : ev p σ c.U g y = 0 := by
    by_contra hne'
    exact hgZ _ (mem_ptsIn.1 hyU) hyZ (mem_ptsIn.1 ((mem_ptsIn_basicOpen hyU g).2 hne'))
  have hcomp : (evHom hyU).comp (MvPolynomial.eval₂Hom (algX p c.U) c.x) =
      MvPolynomial.eval₂Hom σ (fun a => c.e y a) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun a => ?_)
    · simp [← ev_eq hyU, ev_algX hyU]
    · simp [← ev_eq hyU, c.apply_eq y hys]
  have := congrArg (fun F => F Q) hcomp
  simp only [RingHom.comp_apply] at this
  show MvPolynomial.eval (fun a => c.e y a) (MvPolynomial.map σ Q) = 0
  rw [MvPolynomial.eval_map, ← MvPolynomial.coe_eval₂Hom, ← this, hQr, map_mul, ← ev_eq hyU, hgy,
    zero_mul]

theorem chernPart_over_closed : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ}, IsArithVar p D → ∀ (Z : Set X), IsClosed Z → genericPoint X ∉ Z → ∀ (σ : k →+* ℂ) {B : LB X} (φ : Weight p σ B) (ε : ℤˣ), φ.chernPart D ε {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ Z} = 0 := by
  intro k _ X _ p D h Z hZ hgen σ B φ ε
  have hA : MeasurableSet {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ Z} := by
    have : {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ Z} =
        (ptsIn p σ ⟨Zᶜ, hZ.isOpen_compl⟩)ᶜ := by
      ext y
      simp [mem_ptsIn]
    rw [this]
    exact (isOpen_ptsIn _).measurableSet.compl
  exact GlueCoverNull.glueMeas_null _ _ hA fun c => chart_null h hZ hgen σ c

end GlobalTheory.ChernNull
end
end

section

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open MeasureTheory GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.Points
open scoped ENNReal

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CoverDeg

theorem exists_open_covering_charts : ∀ {k : Type} [CommRing k] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {D : ℕ}, IsArithVar p D → IsArithVar q D → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∃ U : X.Opens, genericPoint X ∈ U ∧ ∀ σ : k →+* ℂ, (∀ y ∈ ptsIn p σ U, (PtsOver.map π hπ (spMap σ)  ⁻¹' {y}).encard = (π.residueDegree (genericPoint Y) : ℕ∞)) ∧ (∀ y ∈ ptsIn p σ U, ∃ c : AlgChart p σ D, y ∈ c.e.source) ∧ (∀ z : CxPts q σ, PtsOver.map π hπ (spMap σ) z ∈ ptsIn p σ U → ∀ c : AlgChart p σ D, PtsOver.map π hπ (spMap σ) z ∈ c.e.source → ∃ c' : AlgChart q σ D, z ∈ c'.e.source ∧ ∀ w ∈ c'.e.source, PtsOver.map π hπ (spMap σ) w ∈ c.e.source ∧ c'.e w = c.e (PtsOver.map π hπ (spMap σ) w)) := by
  intro k _ X Y _ _ p q D hp hq π hπ hη hδ
  obtain ⟨U₁, hU₁, hx₁, ht⟩ := GlobalTheory.T.exists_affine_etale_coordinates_generic_point hp
  obtain ⟨U₂, hU₂, hx₂, hV₂, he₂, hf₂, hr₂⟩ := GlobalTheory.T.exists_affine_etale_finite_nbhd_generic hp hq π hπ hη hδ
  obtain ⟨U, hxU, hG⟩ := GlobalTheory.T.exists_basicOpen_etaleCoordinates_finiteFreeEtaleCover p π D _ _ U₁ U₂ hU₁ hx₁ ht hU₂ hx₂ hV₂ he₂ hf₂ hr₂
  refine ⟨U, hxU, fun σ => ⟨fun y hy => ?_, fun y hy => ?_, fun z hz c hc => ?_⟩⟩
  · rw [GlobalTheory.T.encard_complexPointFibre_eq_encard_ringHom_extensions π hπ U hG.1 hG.2.1 σ y hy]
    exact GlobalTheory.T.encard_complexPoints_finiteEtaleFree_eq_rank (π.app U).hom _ hG.2.2.2.1 hG.2.2.2.2.1 hG.2.2.2.2.2 _
  · obtain ⟨t, ht⟩ := hG.2.2.1
    obtain ⟨c, hc, -⟩ := AlgChart.exists_of_etale hG.1 t ht hy
    exact ⟨c, hc⟩
  · set y := PtsOver.map π hπ (spMap σ) z with hy
    have hyc : y ∈ ptsIn p σ c.U := c.source_subset hc
    have hpt : ∀ W : X.Opens, y ∈ ptsIn p σ W → π (z.1 (IsLocalRing.closedPoint ℂ)) ∈ W := by
      intro W hW
      have := mem_ptsIn.1 hW
      exact this
    obtain ⟨V, hV, hzV, h, hVe⟩ := GlobalTheory.T.exists_affine_etale_pullback_coordinates_goodCover π hπ D _ U hG c.U c.x c.affine c.etale _ (hpt U hz) (hpt c.U hyc)
    obtain ⟨c'', hc'', hU'', hx''⟩ := AlgChart.exists_of_etale (σ := σ) hV _ hVe (mem_ptsIn.2 hzV)
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

end GlobalTheory.CoverDeg
end
end

section

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open MeasureTheory GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.Points
open scoped ENNReal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverChern

open Set

section Cover

variable {n : ℕ} {A B ι κ : Type} [TopologicalSpace A] [TopologicalSpace B] [T2Space B]
  [SecondCountableTopology A] [SecondCountableTopology B] [MeasurableSpace A] [BorelSpace A]
  [MeasurableSpace B] [BorelSpace B]
  {e : ι → OpenPartialHomeomorph A (ReciprocityTheory.L2DbarEstimates.V n)} {ρ : ι → A → ℝ≥0∞}
  {e' : κ → OpenPartialHomeomorph B (ReciprocityTheory.L2DbarEstimates.V n)} {ρ' : κ → B → ℝ≥0∞} {m : B → A}

theorem exists_evenly_covered_on
    (hd : ∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) (ReciprocityTheory.L2DbarEstimates.Y.ovl e i j))
    (hρ : ∀ i j y, y ∈ (e i).source → y ∈ (e j).source →
      ρ i y = ENNReal.ofReal (‖transDet (e i) (e j) y‖ ^ 2) * ρ j y)
    (hd' : ∀ i j, DifferentiableOn ℂ (e' j ∘ (e' i).symm) (ReciprocityTheory.L2DbarEstimates.Y.ovl e' i j))
    (hρ' : ∀ i j y, y ∈ (e' i).source → y ∈ (e' j).source →
      ρ' i y = ENNReal.ofReal (‖transDet (e' i) (e' j) y‖ ^ 2) * ρ' j y)
    (hm : Continuous m) {U : Set A} (hU : IsOpen U) {d : ℕ}
    (hfib : ∀ x ∈ U, (m ⁻¹' {x}).encard = d)
    (hch : ∀ z, m z ∈ U → ∃ i j, z ∈ (e' j).source ∧ m z ∈ (e i).source ∧ ∀ w ∈ (e' j).source,
      m w ∈ (e i).source → e' j w = e i (m w) ∧ ρ' j w = ρ i (m w))
    {x : A} (hx : x ∈ U) :
    ∃ W : Set A, IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧ ∀ Q : Set A, MeasurableSet Q → Q ⊆ W →
      glueMeas e' ρ' (m ⁻¹' Q) = d * glueMeas e ρ Q := by
  classical
  have hfin : ∀ y ∈ U, (m ⁻¹' {y}).Finite := fun y hy => finite_of_encard_eq_coe (hfib y hy)
  have hcard : ∀ y (hy : y ∈ U), (hfin y hy).toFinset.card = d := fun y hy => by
    have h := hfib y hy
    rw [← (hfin y hy).coe_toFinset, encard_coe_eq_coe_finsetCard] at h
    exact_mod_cast h
  obtain ⟨V, hV, hVd⟩ := (hfin x hx).t2_separation
  have hFc := hcard x hx
  have hFm : ∀ z, z ∈ (hfin x hx).toFinset ↔ m z = x := fun z => by simp
  generalize (hfin x hx).toFinset = F at hFc hFm
  have hzF : ∀ z ∈ F, m z = x := fun z hz => (hFm z).1 hz
  have hzU : ∀ z ∈ F, m z ∈ U := fun z hz => by rwa [hzF z hz]
  have hsheet : ∀ z, z ∈ F → ∃ M : Set B, M ⊆ V z ∧ IsOpen M ∧ z ∈ M ∧ IsOpen (m '' M) ∧
      ∀ Q : Set A, MeasurableSet Q → Q ⊆ m '' M →
        glueMeas e' ρ' (M ∩ m ⁻¹' Q) = glueMeas e ρ Q := fun z hz =>
    GlueCover.exists_sheet hd hρ hd' hρ' hm (hch z (hzU z hz)) (hV z).2 (hV z).1
  choose! M hMV hMo hzM hMi hMQ using hsheet
  refine ⟨(⋂ z ∈ F, m '' M z) ∩ U, (isOpen_biInter_finset hMi).inter hU,
    ⟨mem_iInter₂.2 fun z hz => ⟨z, hzM z hz, hzF z hz⟩, hx⟩, inter_subset_right,
    fun Q hQ hQW => ?_⟩
  have hdisj : ∀ z₁ ∈ F, ∀ z₂ ∈ F, z₁ ≠ z₂ → Disjoint (M z₁) (M z₂) := fun z₁ h₁ z₂ h₂ hne =>
    Disjoint.mono (hMV z₁ h₁) (hMV z₂ h₂) (hVd (hzF z₁ h₁) (hzF z₂ h₂) hne)
  have key : m ⁻¹' Q = ⋃ z ∈ F, (M z ∩ m ⁻¹' Q) := by
    ext w
    constructor
    · intro hw
      have hWx := hQW hw
      have hpre : ∀ z ∈ F, ∃ z', z' ∈ M z ∧ m z' = m w := fun z hz => by
        obtain ⟨z', h₁, h₂⟩ := mem_iInter₂.1 hWx.1 z hz
        exact ⟨z', h₁, h₂⟩
      haveI : Nonempty B := ⟨w⟩
      choose! f hfM hfm using hpre
      have hinj : InjOn f F := fun z₁ h₁ z₂ h₂ h12 => by
        by_contra hne
        exact disjoint_left.1 (hdisj z₁ h₁ z₂ h₂ hne) (hfM z₁ h₁) (h12 ▸ hfM z₂ h₂)
      have hsub : F.image f ⊆ (hfin (m w) hWx.2).toFinset := fun v hv => by
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hv
        simpa using hfm z hz
      have heq := Finset.eq_of_subset_of_card_le hsub (by
        rw [Finset.card_image_of_injOn hinj, hcard _ hWx.2, hFc])
      have hwm : w ∈ F.image f := by
        rw [heq]
        simp
      obtain ⟨z, hz, hzw⟩ := Finset.mem_image.1 hwm
      exact mem_iUnion₂.2 ⟨z, hz, hzw ▸ hfM z hz, hw⟩
    · intro hw
      obtain ⟨z, _, _, h⟩ := mem_iUnion₂.1 hw
      exact h
  rw [key, measure_biUnion_finset
    (fun z₁ h₁ z₂ h₂ hne => Disjoint.mono inter_subset_left inter_subset_left
      (hdisj z₁ h₁ z₂ h₂ hne))
    (fun z hz => (hMo z hz).measurableSet.inter (hm.measurable hQ)),
    Finset.sum_congr rfl fun z hz => hMQ z hz Q hQ
      fun y hy => mem_iInter₂.1 (hQW hy).1 z hz,
    Finset.sum_const, nsmul_eq_mul, hFc]

theorem glueMeas_preimage_of_cover_on
    (hd : ∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) (ReciprocityTheory.L2DbarEstimates.Y.ovl e i j))
    (hρ : ∀ i j y, y ∈ (e i).source → y ∈ (e j).source →
      ρ i y = ENNReal.ofReal (‖transDet (e i) (e j) y‖ ^ 2) * ρ j y)
    (hd' : ∀ i j, DifferentiableOn ℂ (e' j ∘ (e' i).symm) (ReciprocityTheory.L2DbarEstimates.Y.ovl e' i j))
    (hρ' : ∀ i j y, y ∈ (e' i).source → y ∈ (e' j).source →
      ρ' i y = ENNReal.ofReal (‖transDet (e' i) (e' j) y‖ ^ 2) * ρ' j y)
    (hm : Continuous m) {U : Set A} (hU : IsOpen U) {d : ℕ}
    (hfib : ∀ x ∈ U, (m ⁻¹' {x}).encard = d)
    (hch : ∀ z, m z ∈ U → ∃ i j, z ∈ (e' j).source ∧ m z ∈ (e i).source ∧ ∀ w ∈ (e' j).source,
      m w ∈ (e i).source → e' j w = e i (m w) ∧ ρ' j w = ρ i (m w))
    {S : Set A} (hS : MeasurableSet S) (hSU : S ⊆ U) :
    glueMeas e' ρ' (m ⁻¹' S) = d * glueMeas e ρ S := by
  have hW : ∀ x : U, ∃ W : Set A, IsOpen W ∧ x.1 ∈ W ∧ W ⊆ U ∧
      ∀ Q : Set A, MeasurableSet Q → Q ⊆ W →
        glueMeas e' ρ' (m ⁻¹' Q) = d * glueMeas e ρ Q := fun x =>
    exists_evenly_covered_on hd hρ hd' hρ' hm hU hfib hch x.2
  choose W hWo hxW hWU hWQ using hW
  obtain ⟨C, hC, hCW⟩ := TopologicalSpace.isOpen_iUnion_countable W hWo
  haveI : Countable C := hC.to_subtype
  have key : (Measure.map m (glueMeas e' ρ')).restrict U =
      ((d : ℝ≥0∞) • glueMeas e ρ).restrict U := by
    refine Measure.ext_of_iUnion_eq_univ
      (s := fun o : Option C => o.elim Uᶜ fun c => W c.1) ?_ fun o => ?_
    · refine eq_univ_of_forall fun x => ?_
      by_cases hx : x ∈ U
      · have hmem : x ∈ ⋃ i ∈ C, W i := by
          rw [hCW]
          exact mem_iUnion.2 ⟨⟨x, hx⟩, hxW _⟩
        obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.1 hmem
        exact mem_iUnion.2 ⟨some ⟨c, hc⟩, hxc⟩
      · exact mem_iUnion.2 ⟨none, hx⟩
    · cases o with
      | none =>
        show ((Measure.map m (glueMeas e' ρ')).restrict U).restrict Uᶜ =
          (((d : ℝ≥0∞) • glueMeas e ρ).restrict U).restrict Uᶜ
        rw [Measure.restrict_restrict hU.measurableSet.compl,
          Measure.restrict_restrict hU.measurableSet.compl, compl_inter_self,
          Measure.restrict_empty, Measure.restrict_empty]
      | some c =>
        show ((Measure.map m (glueMeas e' ρ')).restrict U).restrict (W c.1) =
          (((d : ℝ≥0∞) • glueMeas e ρ).restrict U).restrict (W c.1)
        ext Q hQ
        have hQW := hQ.inter (hWo c.1).measurableSet
        have hQWU := hQW.inter hU.measurableSet
        rw [Measure.restrict_apply hQ, Measure.restrict_apply hQ, Measure.restrict_apply hQW,
          Measure.restrict_apply hQW, Measure.map_apply hm.measurable hQWU,
          hWQ c.1 _ hQWU fun y hy => hy.1.2, Measure.smul_apply, smul_eq_mul]
  have h := congrArg (fun μ : Measure A => μ S) key
  simp only [Measure.restrict_apply hS, inter_eq_left.2 hSU,
    Measure.map_apply hm.measurable hS, Measure.smul_apply, smul_eq_mul] at h
  exact h

end Cover

theorem chernPart_preimage_of_cover : ∀ {k : Type} [CommRing k] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {D : ℕ}, IsArithVar p D → IsArithVar q D → ∀ {σ : k →+* ℂ} (π : Y ⟶ X) (hπ : π ≫ p = q) {B : LB X} (φ : Weight p σ B), φ.IsCInf → ∀ (ε : ℤˣ) (U : Set (CxPts p σ)), IsOpen U → ∀ (n : ℕ), (∀ y ∈ U, (PtsOver.map π hπ (spMap σ)  ⁻¹' {y}).encard = (n : ℕ∞)) → (∀ y ∈ U, ∃ c : AlgChart p σ D, y ∈ c.e.source) → (∀ z : CxPts q σ, PtsOver.map π hπ (spMap σ) z ∈ U → ∀ c : AlgChart p σ D, PtsOver.map π hπ (spMap σ) z ∈ c.e.source → ∃ c' : AlgChart q σ D, z ∈ c'.e.source ∧ ∀ w ∈ c'.e.source, PtsOver.map π hπ (spMap σ) w ∈ c.e.source ∧ c'.e w = c.e (PtsOver.map π hπ (spMap σ) w)) → (∀ (c : AlgChart p σ D) (c' : AlgChart q σ D), (∀ w ∈ c'.e.source, PtsOver.map π hπ (spMap σ) w ∈ c.e.source ∧ c'.e w = c.e (PtsOver.map π hπ (spMap σ) w)) → ∀ w ∈ c'.e.source, c'.chernDens (φ.pull π hπ) w = c.chernDens φ (PtsOver.map π hπ (spMap σ) w)) → ∀ (S : Set (CxPts p σ)), MeasurableSet S → S ⊆ U → (φ.pull π hπ).chernPart D ε (PtsOver.map π hπ (spMap σ)  ⁻¹' S) = n * φ.chernPart D ε S := by
  intro k _ X Y _ _ p q D hp hq σ π hπ B φ hφ ε U hU n hfib hchart hlift hdens S hS hSU
  have := CxPts.t2Space_cxPts_of_isProjOver σ hq.isProjOver
  have := CxPts.secondCountableTopology_of_isProjOver (σ := σ) hp.isProjOver
  have := CxPts.secondCountableTopology_of_isProjOver (σ := σ) hq.isProjOver
  have hφ' := hφ.pull π hπ
  unfold Weight.chernPart
  refine glueMeas_preimage_of_cover_on (fun c c' => c.holo_trans c') (fun c c' y hy hy' => ?_)
    (fun c c' => c.holo_trans c') (fun c c' y hy hy' => ?_)
    (PtsOver.continuous_map π hπ _) hU hfib (fun z hz => ?_) hS hSU
  · rw [c.chernDens_trans c' hφ hy hy', mul_left_comm, ENNReal.ofReal_mul (sq_nonneg _)]
  · rw [c.chernDens_trans c' hφ' hy hy', mul_left_comm, ENNReal.ofReal_mul (sq_nonneg _)]
  · obtain ⟨c, hc⟩ := hchart _ hz
    obtain ⟨c', hz', hc'⟩ := hlift z hz c hc
    exact ⟨c, c', hz', hc, fun w hw _ => ⟨(hc' w hw).2, by rw [hdens c c' hc' w hw]⟩⟩

end GlobalTheory.CoverChern
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UTau0

section Bal

variable {R : Type} [CommRing R] {B : Over (Sp R)} [GrpObj B] [IsCommMonObj B] (M : RigLB B) (cub : CubicalStr B M)
  {O : Type} [CommRing O] [StarRing O] (act : RingAct B O) {X : Type} [AddCommGroup X] [Module O X]
  (c : X → (𝟙_ (Over (Sp R)) ⟶ B))

def BalTau (τ : ∀ y z : X, LB.Gen (LB.LinComb M.L (GlobalTheory.PolDeg.lamPts (c y) (c z)) GlobalTheory.PolDeg.negε)) : Prop :=
  (∀ y z, (τ y z).IsGen) ∧
  (∀ y y' z p J, Good M.L p J →
    val (τ (y + y') z) (𝟙 _) p J * cubV cub p J (c y) (c y') (c z) =
      val (τ y z) (𝟙 _) p J * val (τ y' z) (𝟙 _) p J) ∧
  (∀ y z z' p J, Good M.L p J →
    val (τ y (z + z')) (𝟙 _) p J * cubV cub p J (c z) (c z') (c y) =
      val (τ y z) (𝟙 _) p J * val (τ y z') (𝟙 _) p J) ∧
  (∀ (a : O) (u : LB.Gen (LB.LinComb M.L (rosatiφ B (act.act a) (act.act (star a))) rosatiε)), u.IsGen →
    LB.Gen.Corr M.L _ _ _ _ (LB.pullGen M.L _ _ u (zero2 B)) (LB.oneGen M.L) →
    ∀ y z p J, Good M.L p J →
      val (τ (a • y) z) (𝟙 _) p J * val u (lift (c y) (c z)).left p J = val (τ y (star a • z)) (𝟙 _) p J)

end Bal

section Psi

variable {R : Type} [CommRing R] [IsDomain R]

abbrev w0φ (D₀ : DegPre R) (f : D₀.P.A ⟶ D₀.P.A) : Fin 4 → (D₀.P.A.left ⟶ D₀.P.A.left) :=
  ![(padd D₀.P.A (𝟙 _) f).left, 𝟙 D₀.P.A.left, f.left, (toUnit D₀.P.A ≫ η[D₀.P.A]).left]

abbrev w0ε : Fin 4 → ℤ := ![1, -2, -1, 2]

def rigV (D₀ : DegPre R) (p : Sp R) (J : (Sp R ⟶ D₀.P.A.left) → D₀.P.L.ι) :=
  val (L := D₀.P.L) (φ := fun _ : PUnit => eSec D₀.P.A) (ε := fun _ => 1) D₀.rig (𝟙 _) p J

def tauV (D₀ : DegPre R)
    (ψ : ∀ y : D₀.X, LB.Gen (LB.LinComb D₀.P.L (K := PUnit) (fun _ => (D₀.c y).left) (fun _ => -1)))
    (p : Sp R) (J : (Sp R ⟶ D₀.P.A.left) → D₀.P.L.ι) (y z : D₀.X) :=
  val (ψ (y + z)) (𝟙 _) p J * (val (ψ y) (𝟙 _) p J)⁻¹ * (val (ψ z) (𝟙 _) p J)⁻¹ * (rigV D₀ p J)⁻¹

def RLaws (D₀ : DegPre R) {O : Type} [CommRing O] [StarRing O] [Module O D₀.X] (onB : D₀.P.OAct O) (w0 : O)
    (uw : LB.Gen (LB.LinComb D₀.P.L (w0φ D₀ (onB.act w0)) w0ε))
    (ψ : ∀ y : D₀.X, LB.Gen (LB.LinComb D₀.P.L (K := PUnit) (fun _ => (D₀.c y).left) (fun _ => -1))) : Prop :=
  (∀ y, (ψ y).IsGen) ∧
  (∀ y y' z p J, Good D₀.P.L p J →
    tauV D₀ ψ p J (y + y') z * cubV D₀.cub p J (D₀.c y) (D₀.c y') (D₀.c z) = tauV D₀ ψ p J y z * tauV D₀ ψ p J y' z) ∧
  (∀ y p J, Good D₀.P.L p J → val (ψ (-y)) (𝟙 _) p J * val D₀.sym (D₀.c y).left p J = val (ψ y) (𝟙 _) p J) ∧
  (∀ (a : O) (u : LB.Gen (LB.LinComb D₀.P.L (rosatiφ D₀.P.A (onB.act a) (onB.act (star a))) rosatiε)), u.IsGen →
    LB.Gen.Corr D₀.P.L _ _ _ _ (LB.pullGen D₀.P.L _ _ u (zero2 D₀.P.A)) (LB.oneGen D₀.P.L) →
    ∀ y z p J, Good D₀.P.L p J →
      tauV D₀ ψ p J (a • y) z * val u (lift (D₀.c y) (D₀.c z)).left p J = tauV D₀ ψ p J y (star a • z)) ∧
  (∀ y p J, Good D₀.P.L p J →
    tauV D₀ ψ p J y (w0 • y) * val uw (D₀.c y).left p J = val (ψ y) (𝟙 _) p J * rigV D₀ p J)

end Psi

end GlobalTheory.UTau0
end
end
