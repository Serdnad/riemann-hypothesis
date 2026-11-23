module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle061
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2461
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2532
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1371
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2460
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1441
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle031
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle037
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2431
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2852
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2912
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3152
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3013
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle056
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle065
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3153
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3144
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3154
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
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle070
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle077

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GeneralMember

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]

theorem regAt_functionFieldMap (q : Y ⟶ X) [IsDominant q] (y : Y) {f : X.functionField}
    (h : RegAt (q y) f) : RegAt y (functionFieldMap q f) := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨q.stalkMap y a, (functionFieldMap_algebraMap q y a).symm⟩

theorem unitAt_functionFieldMap (q : Y ⟶ X) [IsDominant q] (y : Y) {f : X.functionField}
    (h : UnitAt (q y) f) : UnitAt y (functionFieldMap q f) := by
  obtain ⟨a, ha, rfl⟩ := h
  exact ⟨q.stalkMap y a, ha.map _, (functionFieldMap_algebraMap q y a).symm⟩

theorem supp_nsmul_le (D : CartierDiv X) (r : ℕ) : (r • D).supp ≤ D.supp := by
  induction r with
  | zero => rw [zero_smul, CartierDiv.supp_eq_bot_iff.2 rfl]; exact bot_le
  | succ r ih => rw [succ_nsmul]; exact (CartierDiv.supp_add_le _ _).trans (sup_le ih le_rfl)

theorem functionFieldMap_mem_sections (q : Y ⟶ X) [IsDominant q] {A : CartierDiv X}
    {f : X.functionField} (h : f ∈ A.sections) : functionFieldMap q f ∈ (pullCart q A).sections := by
  refine CartierDiv.mem_sections.2 fun y => ?_
  obtain ⟨g, hg⟩ := A.exists_isEqn (q y)
  have h1 := hg.regularAt_iff.1 (CartierDiv.mem_sections.1 h (q y))
  refine ⟨fnPull q g, isEqn_pullCart q hg, ?_⟩
  have := regAt_functionFieldMap q y h1
  rwa [map_mul] at this

theorem generatesAt_pullCart (q : Y ⟶ X) [IsDominant q] {A : CartierDiv X} {y : Y}
    {f : X.functionField} (h : A.GeneratesAt (q y) f) :
    (pullCart q A).GeneratesAt y (functionFieldMap q f) := by
  obtain ⟨g, hg⟩ := A.exists_isEqn (q y)
  refine ⟨fnPull q g, isEqn_pullCart q hg, ?_⟩
  have := unitAt_functionFieldMap q y (hg.generatesAt_iff.1 h)
  rwa [map_mul] at this

variable [IsLocallyNoetherian X]

theorem isLogMult_add {p : X ⟶ Sp ℂ} {n : ℕ} {Δ : X → ℚ} {η : RatForms p n} {m m' b e : ℕ}
    {G D₀ : CartierDiv X} {a : ℚ} (hG : IsLogMult p n Δ η m G) (hm' : 0 < m') (he : 0 < e)
    (hab : a = b / e) :
    IsLogMult p n (Δ + a • qWeil D₀ m') η (m * (e * m')) ((e * m') • G + m • (b • D₀)) := by
  refine ⟨hG.ne_zero, Nat.mul_pos hG.pos (Nat.mul_pos he hm'), fun x g hg z hz E hE => ?_⟩
  obtain ⟨V, hV, hgV⟩ := hg.exists_nhds
  obtain ⟨g₁, hg₁⟩ := G.exists_isEqn z
  obtain ⟨d, hd⟩ := D₀.exists_isEqn z
  have h3 := ((hgV z (hz.mem_open V.isOpen hV)).mult_eq.symm.trans
    ((hg₁.nsmul (e * m')).add ((hd.nsmul b).nsmul m)).mult_eq)
  rw [← hE.ord_eq, ← hE.ord_eq, E.ord_mul, E.ord_pow, E.ord_pow, E.ord_pow] at h3
  have h4 := hG.eqn z g₁ hg₁ z specializes_rfl E hE
  have hd' := hd.mult_eq
  rw [← hE.ord_eq] at hd'
  have h1 : (m' : ℚ) ≠ 0 := by exact_mod_cast hm'.ne'
  have h2 : (e : ℚ) ≠ 0 := by exact_mod_cast he.ne'
  rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, qWeil, hd', h3, hab]
  push_cast
  rw [← h4]
  field_simp
  ring

end GlobalTheory.GeneralMember


open GlobalTheory.GeneralMember in
theorem GlobalTheory.PairStep.kltAt_add_general_member : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ D : X → ℚ) (m : ℕ) (G A : CartierDiv X) (ι : Type) [Fintype ι] (s : ι → X.functionField), 0 < m → IsLogCanonicalMultiple p n Δ m G → IsQCart D → (∀ i, s i ∈ A.sections) → ∃ Q : MvPolynomial ι ℂ, Q ≠ 0 ∧ ∀ u : ι → ℂ, MvPolynomial.eval u Q ≠ 0 → ∀ t : X.functionFieldˣ, (t : X.functionField) = ∑ i, Cartier.constFn p (u i) * s i → ∀ y : X, (∃ i, A.GeneratesAt y (s i)) → ∀ a c : ℚ, 0 ≤ a → c < 1 → KltAt p n (Δ + a • D) y → KltAt p n (Δ + a • D + c • qWeil (GlobalTheory.Cartier.CartierDiv.principal t + A) 1) y := by
  intro hP X _ _ _ p n hproj hn Δ D m G A ι _ s hm hG hD hs
  obtain ⟨η, hη⟩ := hG.exists_isLogMult hm
  obtain ⟨m', D₀, hm', -, rfl⟩ := hD
  obtain ⟨Y, hY, π, hπ, K, B, hres, hB⟩ :=
    GlobalTheory.T.exists_log_resolution hP ℂ X p n hproj hn η m G hη.ne_zero D₀.supp D₀.supp_ne_top
  haveI : IsNoetherian Y := isNoetherian_of_isProjOver hres.proj
  haveI := hres.smooth
  haveI : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hproj).1
  haveI : IsProper (π ≫ p) := ((isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hres.proj).1
  haveI : IsProper π := IsProper.of_comp π p
  obtain ⟨Q, hQ0, hQ⟩ := GlobalTheory.T.exists_bertini_poly_discrepancy_snc_boundary Y (π ≫ p) n hres.proj B hres.snc (pullCart π A) ι
    (fun i => functionFieldMap π (s i)) fun i => functionFieldMap_mem_sections π (hs i)
  refine ⟨Q, hQ0, fun u hu t ht y ⟨i, hi⟩ a c ha hc hklt => ?_⟩

  set b : ℕ := a.num.toNat with hb
  set e : ℕ := a.den with he
  have hepos : 0 < e := a.den_pos
  have hab : a = b / e := by
    have h0 : (0 : ℤ) ≤ a.num := Rat.num_nonneg.2 ha
    have h1 : ((a.num.toNat : ℕ) : ℚ) = (a.num : ℚ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg h0]
    rw [hb, he, h1]
    exact (Rat.num_div_den a).symm
  set m'' := m * (e * m') with hm''
  set G' := (e * m') • G + m • (b • D₀) with hG'
  have hm''pos : 0 < m'' := Nat.mul_pos hm (Nat.mul_pos hepos hm')
  have hmult : IsLogMult p n (Δ + a • qWeil D₀ m') η m'' G' := isLogMult_add hη hm' hepos hab

  have hΘ : pullCart π G' - m'' • K = (e * m') • (pullCart π G - m • K) + (m * b) • pullCart π D₀ := by
    have hn1 : ∀ (r : ℕ) (D : CartierDiv X), pullCart π (r • D) = r • pullCart π D :=
      fun r D => map_nsmul (pullCartHom π) r D
    rw [hG', pullCart_add, hn1, hn1, hn1, hm'']
    module
  have hsupp : (pullCart π G' - m'' • K).supp ≤ B := by
    rw [hΘ]
    refine (CartierDiv.supp_add_le _ _).trans (sup_le ((supp_nsmul_le _ _).trans hres.supp)
      ((supp_nsmul_le _ _).trans fun w hw => hB w ((GlobalTheory.T.cartierDivisorPullback_support_and_effective X Y π D₀).1 w hw)))
  have hres' : IsLogRes p n η m'' G' π K B := { hres with supp := hsupp }

  obtain ⟨g'', hg''⟩ := G'.exists_isEqn y
  have hL := hmult.eqn y g'' hg''
  obtain ⟨ya, hya⟩ := A.exists_isEqn y
  have hH : (CartierDiv.principal t + A).IsEqn y (t * ya) := (CartierDiv.isEqn_principal t y).add hya
  have hHz : ∀ z, z ⤳ y → ∀ E : DivOver p, E.IsAt z →
      qWeil (CartierDiv.principal t + A) 1 z = (E.ord (t * ya) : ℚ) / (1 : ℕ) := by
    intro z hz E hE
    obtain ⟨V, hV, hHV⟩ := hH.exists_nhds
    rw [qWeil, (hHV z (hz.mem_open V.isOpen hV)).mult_eq, ← hE.ord_eq]
  obtain ⟨m₂, g₂, hm₂, hL₂, hdisc⟩ := isLogEqn_add_smul X p n (Δ + a • qWeil D₀ m')
    (qWeil (CartierDiv.principal t + A) 1) η y m'' 1 g'' (t * ya) c hm''pos one_pos hL hHz
  rw [hL₂.kltAt_iff hn hη.ne_zero hm₂]
  intro E hE
  rw [hdisc]

  obtain ⟨E', hE'⟩ := GlobalTheory.T.exists_primeDivisor_over_source_birational ℂ X Y p π hres.bir E
  obtain ⟨y', rfl, hy'⟩ := GlobalTheory.T.divisor_center_proper_lift ℂ X Y p π hres.bir inferInstance E' E hE' y hE
  have hη' : EtaleKlt.ratPull p π n η ≠ 0 := fun h =>
    hη.ne_zero ((GlobalTheory.T.rationalTopFormPullback_bijective_birational ℂ X Y p π hres.bir n).1 (h.trans (map_zero _).symm))
  have hΘm : ∀ w, w ⤳ y' → (pullCart π G' - m'' • K).mult w < m'' := fun w hw =>
    ((GlobalTheory.T.log_resolution_multiplier_local ℂ X p n hproj hn _ η m'' G' Y π K B hmult hres' (π y')).1.1 hklt) w
      (hw.map π.continuous)
  have hΘe : (pullCart π G' - m'' • K + m'' • K).IsEqn y' (fnPull π g'') := by
    rw [sub_add_cancel]; exact isEqn_pullCart π hg''
  have ht' : ((fnPull π t : Y.functionFieldˣ) : Y.functionField) =
      ∑ i, Cartier.constFn (π ≫ p) (u i) * functionFieldMap π (s i) := by
    change functionFieldMap π (t : X.functionField) = _

    rw [ht, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, ← EtaleKlt.functionFieldMap_comp_constFn p π, RingHom.comp_apply]
  have hH' : (CartierDiv.principal (fnPull π t) + pullCart π A).IsEqn y' (fnPull π (t * ya)) := by
    rw [map_mul]; exact (CartierDiv.isEqn_principal _ y').add (isEqn_pullCart π hya)
  have key := hQ u hu (fnPull π t) ht' y' ⟨i, generatesAt_pullCart π hi⟩ (EtaleKlt.ratPull p π n η)
    K (pullCart π G' - m'' • K) m'' c (fnPull π g'') (fnPull π (t * ya)) hη' hres.div hm''pos
    hsupp hc hΘm hΘe hH' E' hy'
  have e1 := GlobalTheory.T.form_order_birational_pullback ℂ X Y p π hres.bir E' E hE' n η hη.ne_zero
  change E'.formOrd (EtaleKlt.ratPull p π n η) = E.formOrd η at e1
  have e2 := GlobalTheory.T.ord_functionField_pullback_primeDivisor_over ℂ X Y p π hres.bir E' E hE' g''
  have e3 := GlobalTheory.T.ord_functionField_pullback_primeDivisor_over ℂ X Y p π hres.bir E' E hE' (t * ya)
  simp only [discrep, e1, e2, e3] at key
  simpa [discrep] using key
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

theorem _root_.GlobalTheory.T.inductive_height_formula_rhs_transport_iso : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k), IsAmb p → IsAmb q → ∀ (g : Y ⟶ X) (hg : g ≫ p = q) (hη : g (genericPoint Y) = genericPoint X), IsIso g → ∀ e : ℕ, topologicalKrullDim X = (e + 1 : ℕ) → ∀ (h : X → ℝ) (L : Fin e → HermLB p) (M : HermLB p) (r : M.B.ι → X.functionFieldˣ) (hr : IsRatSec M.B r), recVal (fun w => h (g w)) (fun a => (L a).pull g hg) (M.pull g hg) (MultPull.isRatSec_pull_map g (hη ▸ specializes_rfl : g (genericPoint Y) ⤳ genericPoint X) hr) = recVal h L M hr := by
  exact @GlobalTheory.MixHt.transport
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

theorem _root_.GlobalTheory.T.arithmetic_curve_degree_independent_of_section : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsAmb q → topologicalKrullDim Y = (0 + 1 : ℕ) → ∀ (N : HermLB q) (L : Fin 0 → HermLB q) (r : N.B.ι → Y.functionFieldˣ) (hr : IsRatSec N.B r) (r' : N.B.ι → Y.functionFieldˣ) (hr' : IsRatSec N.B r'), recVal (fun z => Real.log (Nat.card (Y.residueField z))) L N hr = recVal (fun z => Real.log (Nat.card (Y.residueField z))) L N hr' := by
  first | exact @GlobalTheory.CurveIndep.main | exact GlobalTheory.CurveIndep.main | (intros; apply GlobalTheory.CurveIndep.main <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

theorem _root_.GlobalTheory.T.arithHeight_projectionFormula_inductiveStep : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D E : ℕ), IsArithVar p D → IsArithVar q E → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (L : HermLB p) (h : X → ℝ) (h' : Y → ℝ), L.IsArithHeight h → (L.pull π hπ).IsArithHeight h' → ∀ (y : Y) (e : ℕ), CharZero Γ(clo y, ⊤) → HasDim y (e + 1 + 1) → (∀ w : Y, HasDim w (e + 1) → h' w = (π.residueDegree w : ℝ) * h (π w)) → h' y = (π.residueDegree y : ℝ) * h (π y) := by
  first | exact @GlobalTheory.ProjStep.main | exact GlobalTheory.ProjStep.main | (intros; apply GlobalTheory.ProjStep.main <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

theorem _root_.GlobalTheory.T.arithHeight_projectionFormula_pointCurve : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D E : ℕ), IsArithVar p D → IsArithVar q E → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (L : HermLB p) (h : X → ℝ) (h' : Y → ℝ), L.IsArithHeight h → (L.pull π hπ).IsArithHeight h' → ∀ y : Y, CharZero Γ(clo y, ⊤) → HasDim y 1 → h' y = (π.residueDegree y : ℝ) * h (π y) := by
  first | exact @GlobalTheory.ProjCurve.main | exact GlobalTheory.ProjCurve.main | (intros; apply GlobalTheory.ProjCurve.main <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.archLogNormChernIntegrable_of_principalisation : GlobalTheory.Published.Principalisation → GlobalTheory.MixHt.ArchInteg := by
  first | exact @GlobalTheory.ArchIntegClosing.archInteg | exact GlobalTheory.ArchIntegClosing.archInteg | (intros; apply GlobalTheory.ArchIntegClosing.archInteg <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix

theorem side_bc_eq : ∀ (k K : Type) [CommRing k] [Field K] [Algebra k K] [IsFractionRing k K] (X G : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [IsIntegral G] [IsLocallyNoetherian G] (p : X ⟶ Sp k) (q : G ⟶ Sp K) (j : G ⟶ X) (hp : IsPullback j q p (spMap (algebraMap k K))) (τ : K →+* ℂ) (e : ℕ), IsArithVar p (e + 1) → ∀ (Δ : CartierDiv X) (Δ' : CartierDiv G), (∀ x, Δ'.mult x = Δ.mult (j x)) → ∀ (N : MLine p (τ.comp (algebraMap k K))) (L : Fin e → MLine p (τ.comp (algebraMap k K))) (f g : CxPts p (τ.comp (algebraMap k K)) → ℝ), side (N.bc hp.w τ) (fun i => (L i).bc hp.w τ) (fun y => f (bcPt hp.w τ y)) (fun y => g (bcPt hp.w τ y)) Δ' = side N L f g Δ := by
  intro k K _ _ _ _ X G _ _ _ _ p q j hp τ e hA Δ Δ' hΔ N L f g
  obtain ⟨_, _, _, _, _, hinj, _, hcoh, hemp⟩ := GlobalTheory.T.generic_fiber_arithmetic_variety_integral_projective k K X G p q j hp (e + 1) hA
  have hcons : (Fin.cons (N.bc hp.w τ) (fun i => (L i).bc hp.w τ) : Fin (e + 1) → MLine q τ) =
      fun i => ((Fin.cons N L : Fin (e + 1) → MLine p (τ.comp (algebraMap k K))) i).bc hp.w τ := by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> simp
  have h1 := ((GlobalTheory.T.mixedChernMeasure_integral_eq_genericFibre k K X G p q j hp τ (e + 1) hA (Fin.cons N L)).2 f).2
  have hzero : ∀ z : X, z ∉ Set.range j → cycInt L g z = 0 := by
    intro z hz
    haveI := hemp z hz (τ.comp (algebraMap k K))
    simp [cycInt, Mix.int, MeasureTheory.integral_of_isEmpty]
  unfold side
  rw [hcons, h1]
  congr 1
  calc ∑ᶠ x, (Δ'.mult x : ℝ) * cycInt (fun i => (L i).bc hp.w τ) (fun y => g (bcPt hp.w τ y)) x
      = ∑ᶠ x, (Δ.mult (j x) : ℝ) * cycInt L g (j x) := by
        refine finsum_congr fun x => ?_
        rw [hΔ]
        by_cases h : Δ.mult (j x) = 0
        · simp [h]
        · rw [GlobalTheory.T.horizontal_prime_divisor_integral_eq_generic_fibre k K X G p q j hp τ e hA L g x
            (by rw [← hcoh]; exact CartierDiv.coheight_eq_one_of_mult_ne_zero h)]
    _ = ∑ᶠ z ∈ Set.range j, (Δ.mult z : ℝ) * cycInt L g z := (finsum_mem_range (f := fun z => (Δ.mult z : ℝ) * cycInt L g z) hinj).symm
    _ = ∑ᶠ z, (Δ.mult z : ℝ) * cycInt L g z := by
        rw [finsum_mem_def]
        refine finsum_congr fun z => ?_
        by_cases hz : z ∈ Set.range j
        · simp [hz]
        · simp [hz, hzero z hz]

end GlobalTheory.Mix
end
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

theorem _root_.GlobalTheory.T.flagBundle_fibreIntegral_pullback_mul_fibreClass : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ, IsMetricOn E ⊤ H → ∀ α : (atlas X σ).Fld, (atlas X σ).IsForm α → (atlas Y σ).integral ((atlas X σ).pullback (atlas Y σ) (ptMap σ f hf) α * evalF (atlas Y σ) (grF E' (pullGram E H φ f hf)) (fibrePoint m)) = (atlas X σ).integral α := by
  first | exact @GlobalTheory.ChernCalc.fibre_integral | exact GlobalTheory.ChernCalc.fibre_integral | (intros; apply GlobalTheory.ChernCalc.fibre_integral <;> assumption)
end

section

open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical

theorem _root_.GlobalTheory.T.definiteCase_cuspForm_fibre_slope_ge_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (c₁ : ℝ), DefCase U ξ → Dom a n → FlatExistsAt U ξ c₁ → ∀ Z : Comp Xo c, FibreAt U ξ Z (wtZ a n) (defBound Dw a n c₁) := by
  first | exact @GlobalTheory.DefFibre.fibreAt_defCase | exact GlobalTheory.DefFibre.fibreAt_defCase | (intros; apply GlobalTheory.DefFibre.fibreAt_defCase <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.eighthPower_psiOrders_projectionLatticeCoordinates : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → IsDiscreteValuationRing R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (pr : Fin 8 → (A'.A ⟶ A.A)), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing R))) (y : Fin 8 → (T' ⟶ A.A)), ∃! z : T' ⟶ A'.A, ∀ a, z ≫ pr a = y a) → LBIso A'.L (LB.LinComb (abelian₂ A.A A.L) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (pG : Fin 8 → (G' ⟶ G)), (∀ v, IsMonHom (pG v)) → (∀ v, (Over.pullback (jK R)).map (pG v) ≫ U.gen.hom = U'.gen.hom ≫ pr v) → ∀ (c : Fin 8 → (D.toPre.X →+ D'.toPre.X)), (∀ v, TorMatch U U' (RingHom.id R) (pG v).left (c v)) → ∀ e : D'.toPre.X ≃+ (Fin 8 → D.toPre.X), (∀ y, ∑ v, c v (∑ u, (W + W.transpose) v u • e y u) = y) → ∀ (ϖ : R) (β : LinearMap.BilinForm ℤ D.toPre.X), (∀ a b, β a b = β b a) → (∀ a, 0 ≤ β a a) → (∀ a b' (x : (FractionRing R)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D.toPre a b' x → ∃ u : Rˣ, (x : FractionRing R) = algebraMap R (FractionRing R) (u : R) * algebraMap R (FractionRing R) ϖ ^ (β a b')) → ∀ y r, PsiCoord D'.toPre y r → 0 ≤ qW W β (e y) ∧ Associated r (ϖ ^ (qW W β (e y)).toNat) := by
  first | exact @GlobalTheory.Poinc.E8Lattice.main | exact GlobalTheory.Poinc.E8Lattice.main | (intros; apply GlobalTheory.Poinc.E8Lattice.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.eighth_power_endomorphism_lattice_adjoint : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → IsDiscreteValuationRing R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (pr : Fin 8 → (A'.A ⟶ A.A)), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing R))) (y : Fin 8 → (T' ⟶ A.A)), ∃! z : T' ⟶ A'.A, ∀ a, z ≫ pr a = y a) → LBIso A'.L (LB.LinComb (abelian₂ A.A A.L) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (pG : Fin 8 → (G' ⟶ G)), (∀ v, IsMonHom (pG v)) → (∀ v, (Over.pullback (jK R)).map (pG v) ≫ U.gen.hom = U'.gen.hom ≫ pr v) → ∀ (c : Fin 8 → (D.toPre.X →+ D'.toPre.X)), (∀ v, TorMatch U U' (RingHom.id R) (pG v).left (c v)) → ∀ e : D'.toPre.X ≃+ (Fin 8 → D.toPre.X), (∀ y, ∑ v, c v (∑ u, (W + W.transpose) v u • e y u) = y) → ∀ (a a' : Matrix (Fin 8) (Fin 8) ℤ), (W + W.transpose) * a' = a.transpose * (W + W.transpose) → ∀ E' : GlobalTheory.UT.EndU U'.toUnifPre, (∀ u, E'.aA ≫ pr u = (List.ofFn fun v => pr v ^ a' u v).prod) → ∀ y, e (E'.h y) = fun u => ∑ v, a u v • e y v := by
  first | exact @GlobalTheory.Poinc.E8Endomorphism.endU_lattice_adjoint | exact GlobalTheory.Poinc.E8Endomorphism.endU_lattice_adjoint | (intros; apply GlobalTheory.Poinc.E8Endomorphism.endU_lattice_adjoint <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_rescale_isPullDeg_generating_everywhere : ∀ {W V : Type} [CommRing W] [IsDomain W] [CommRing V] [IsDomain V] (θ₀ : W →+* V) (D₀ : DegPre W) (Q : DegPre V) (e : Q.X ≃+ D₀.X) (β : Q.P.A.left ⟶ D₀.P.A.left), (∀ y, PsiUnitOn D₀ y Set.univ) → IsGrpPullback Q.P.A D₀.P.A (spMap θ₀) β → LBIso Q.P.L (D₀.P.L.pull β) → (∀ y, (Q.c y).left ≫ β = spMap θ₀ ≫ (D₀.c (e y)).left) → ∃ (g : Q.X → (FractionRing V)ˣ) (hD : IsPullDeg θ₀ D₀ (GlobalTheory.PolDeg.rescale Q g)), (∀ y, hD.xe y = e y) ∧ hD.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf θ₀) = β ∧ hD.W = ⊤ := by
  first | exact @GlobalTheory.PreLiftData.exists_rescale_isPullDeg_top | exact GlobalTheory.PreLiftData.exists_rescale_isPullDeg_top | (intros; apply GlobalTheory.PreLiftData.exists_rescale_isPullDeg_top <;> assumption)
end
