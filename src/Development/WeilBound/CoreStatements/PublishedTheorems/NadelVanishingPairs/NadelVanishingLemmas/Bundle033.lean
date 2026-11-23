module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2461
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2460
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2431
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1441
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1322
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle025
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle029
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle031
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle032
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.LogResolutionMultiplierLocal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

namespace GlobalTheory.MultLoc

theorem isProper_of_isProjOver_nadel_vanishing {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R}
    (h : IsProjOver f) : IsProper f := by
  obtain ⟨N, i, hi, rfl⟩ := h
  have := isProper_str R N
  infer_instance

variable {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]

noncomputable def multHom (z : Y) : CartierDiv Y →+ ℤ :=
  AddMonoidHom.mk' (fun D => D.mult z) (fun D E => CartierDiv.mult_add D E z)

theorem mult_neg' (D : CartierDiv Y) (z : Y) : (-D).mult z = -D.mult z :=
  map_neg (multHom z) D

theorem mult_sub' (D E : CartierDiv Y) (z : Y) : (D - E).mult z = D.mult z - E.mult z :=
  map_sub (multHom z) D E

theorem mult_nsmul' (D : CartierDiv Y) (r : ℕ) (z : Y) : (r • D).mult z = r * D.mult z := by
  rw [← nsmul_eq_mul]; exact map_nsmul (multHom z) r D

end GlobalTheory.MultLoc


open GlobalTheory.MultLoc in
theorem GlobalTheory.Discrepancy.inMultAt_iff_regularAt_logRes : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → ∀ (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) (F : CartierDiv Y), η ≠ 0 → 0 < m → IsLogRes p n η m G s K B → (∀ z, F.mult z = (pullCart s G - m • K).mult z / (m : ℤ)) → ∀ (x : X) (u : X.functionFieldˣ), InMultAt p n η m G x u ↔ ∀ y : Y, s y = x → (-F).RegularAt y (functionFieldMap s (u : X.functionField)) := by
  intro k _ _ X _ p n hp η m G Y _ _ s _ K B F hη hm hres hF x u
  haveI : SmoothOfRelativeDimension n (s ≫ p) := hres.smooth
  haveI : Smooth (s ≫ p) := SmoothOfRelativeDimension.smooth n (s ≫ p)
  haveI : GlobalTheory.IsNormalScheme Y := GlobalTheory.isNormalScheme_of_smooth (s ≫ p)
  haveI : IsProper s := by
    haveI := isProper_of_isProjOver_nadel_vanishing hp
    haveI := isProper_of_isProjOver_nadel_vanishing hres.proj
    exact IsProper.of_comp s p
  set Γ := pullCart s G - m • K with hΓ
  set η' := EtaleKlt.ratPull p s n η with hη'def
  have hη' : η' ≠ 0 := fun h =>
    hη ((GlobalTheory.T.rationalTopFormPullback_bijective_birational k X Y p s hres.bir n).1 (h.trans (map_zero _).symm))
  have hdisc : ∀ (E' : DivOver (s ≫ p)) (E : DivOver p), DivOver.Over s E' E →
      ∀ g : X.functionFieldˣ, discrep E' η' m (fnPull s g) = discrep E η m g := by
    intro E' E hO g
    simp only [discrep, hη'def, GlobalTheory.BirOrd.formOrd_ratPull_of_over k X Y p s hres.bir E' E hO n η hη,
      GlobalTheory.T.ord_functionField_pullback_primeDivisor_over k X Y p s hres.bir E' E hO g]
  have hmq : (0 : ℚ) < m := by exact_mod_cast hm
  have hmz : (0 : ℤ) < m := by exact_mod_cast hm
  have eu : functionFieldMap s (u : X.functionField) = ((fnPull s u : Y.functionFieldˣ) : Y.functionField) := rfl
  constructor
  · intro hu y hy
    rw [eu, GlobalTheory.T.regularAt_iff_forall_specializes_ord_add_mult_nonneg Y (-F) y (fnPull s u)]
    intro z hz
    rw [mult_neg', hF z]
    by_cases hc : Order.coheight z = 1
    · obtain ⟨E', hE'⟩ : ∃ E' : DivOver (s ≫ p), E'.IsAt z :=
        DivOver.exists_isAt_of_coheight_eq_one hc
      obtain ⟨E, hO⟩ := GlobalTheory.T.exists_primeDivisor_over_target_birational k X Y p s hres.bir E'
      have hEx : E.Through x := hy ▸ GlobalTheory.T.primeDivisorCentre_through_image k X Y p s E' E hO y (hE'.through hz)
      obtain ⟨g, hg⟩ := G.exists_isEqn x
      have h1 := hu g hg E hEx
      have h2 : E.ord u = Scheme.ord ((fnPull s u : Y.functionFieldˣ) : Y.functionField) z := by
        rw [← GlobalTheory.T.ord_functionField_pullback_primeDivisor_over k X Y p s hres.bir E' E hO u, hE'.ord_eq]
      have hgy : (pullCart s G).IsEqn y (fnPull s g) := isEqn_pullCart s (by rw [hy]; exact hg)
      obtain ⟨V, hV, hgV⟩ := hgy.exists_nhds
      have h3 := GlobalTheory.T.discrepancy_formula_divisor k Y (s ≫ p) n η' hη' K (pullCart s G) m hm hres.div E' z
        (fnPull s g) hE' (hgV z (hz.mem_open V.isOpen hV))
      rw [hdisc E' E hO g, ← hΓ] at h3
      rw [h2, h3] at h1
      set o := Scheme.ord ((fnPull s u : Y.functionFieldˣ) : Y.functionField) z
      have h4 : ((Γ.mult z : ℤ) : ℚ) < ((((o + 1) * m : ℤ)) : ℚ) := by
        push_cast
        have h6 : ((Γ.mult z : ℤ) : ℚ) / m < o + 1 := by rw [neg_div] at h1; linarith
        rwa [div_lt_iff₀ hmq] at h6
      have h5 := Int.ediv_lt_of_lt_mul hmz (by exact_mod_cast h4)
      omega
    · have h0 : Γ.mult z = 0 := by
        by_contra h; exact hc (CartierDiv.coheight_eq_one_of_mult_ne_zero h)
      rw [Scheme.ord_eq_zero_of_coheight_neq_one hc, h0]
      simp
  · intro hR g hg E hE
    obtain ⟨E', hO⟩ := GlobalTheory.T.exists_primeDivisor_over_source_birational k X Y p s hres.bir E
    obtain ⟨y, hy, hE'y⟩ := GlobalTheory.T.divisor_center_proper_lift k X Y p s hres.bir inferInstance E' E hO x hE
    obtain ⟨f, hf⟩ := F.exists_isEqn y
    have hreg := hf.neg.regularAt_iff.1 (hR y hy)
    have hord : E'.ord f ≤ E'.ord (fnPull s u) := by
      have h0 : 0 ≤ E'.ord (fnPull s u * f⁻¹) := (E'.ord_nonneg_iff _).2 (hE'y _ hreg)
      rw [E'.ord_mul, E'.ord_inv] at h0
      omega
    set G' := pullCart s G - m • F with hG'
    have hg' : G'.IsEqn y (fnPull s g / f ^ m) :=
      (isEqn_pullCart s (by rw [hy]; exact hg)).sub (hf.nsmul m)
    have hmod : ∀ w, (G' - m • K).mult w = Γ.mult w % m := by
      intro w
      have e : G' - m • K = Γ - m • F := by rw [hG', hΓ]; abel
      rw [e, mult_sub', mult_nsmul', hF w, Int.emod_def]
    have hsupp : (G' - m • K).supp ≤ B := by
      intro w hw
      obtain ⟨z, hzw, hz0⟩ := ((GlobalTheory.T.cartier_divisor_mult_characterize Y (G' - m • K)).2.1 w).1 hw
      refine hres.supp (((GlobalTheory.T.cartier_divisor_mult_characterize Y Γ).2.1 w).2 ⟨z, hzw, fun h0 => hz0 ?_⟩)
      rw [hmod, h0, Int.zero_emod]
    have hcrit := (GlobalTheory.T.klt_of_snc_coefficients k Y (s ≫ p) n η' hη' K G' m B hm hres.div hres.snc hsupp y _ hg'
      E' hE'y).1 fun w _ => by rw [hmod]; exact Int.emod_lt_of_pos _ hmz
    have hd : discrep E' η' m (fnPull s g / f ^ m) = discrep E η m g + E'.ord f := by
      rw [← hdisc E' E hO g]
      simp only [discrep, div_eq_mul_inv, E'.ord_mul, E'.ord_inv, E'.ord_pow]
      push_cast
      field_simp
      ring
    rw [hd] at hcrit
    have h6 : (E'.ord f : ℚ) ≤ E.ord u := by
      rw [← GlobalTheory.T.ord_functionField_pullback_primeDivisor_over k X Y p s hres.bir E' E hO u]; exact_mod_cast hord
    linarith
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.canonical_divisor_birational_compare : ∀ (k : Type) [Field k] [CharZero k] (Y₀ Y₁ : Scheme.{0}) [IsIntegral Y₀] [IsIntegral Y₁] [IsLocallyNoetherian Y₀] [IsLocallyNoetherian Y₁] (q : Y₀ ⟶ Sp k) (n : ℕ) (t : Y₁ ⟶ Y₀) [IsDominant t] [SmoothOfRelativeDimension n q] [SmoothOfRelativeDimension n (t ≫ q)] (U : Y₀.Opens), (U : Set Y₀).Nonempty → IsIso (t ∣_ U) → ∀ (η : RatForms q n), η ≠ 0 → ∀ (K₀ : CartierDiv Y₀) (K₁ : CartierDiv Y₁), IsDivOfForm K₀ η → IsDivOfForm K₁ (EtaleKlt.ratPull q t n η) → ∀ y : Y₁, t y ∈ U → y ∉ (K₁ - pullCart t K₀).supp := by
  first | exact @_root_.GlobalTheory.Discrepancy.CanonIso.not_mem_supp_sub_pullCart | exact _root_.GlobalTheory.Discrepancy.CanonIso.not_mem_supp_sub_pullCart | (intros; apply _root_.GlobalTheory.Discrepancy.CanonIso.not_mem_supp_sub_pullCart <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.divisor_agreement_on_isomorphism : ∀ (k : Type) [Field k] [CharZero k] (Y₀ Y₁ : Scheme.{0}) [IsIntegral Y₀] [IsIntegral Y₁] [IsLocallyNoetherian Y₀] [IsLocallyNoetherian Y₁] (q : Y₀ ⟶ Sp k) (n : ℕ) (t : Y₁ ⟶ Y₀) [IsDominant t] [SmoothOfRelativeDimension n q] [SmoothOfRelativeDimension n (t ≫ q)], IsProjOver (t ≫ q) → ∀ (U : Y₀.Opens), IsIso (t ∣_ U) → ∀ H : CartierDiv Y₁, ∃ H₀ : CartierDiv Y₀, ∀ y : Y₁, t y ∈ U → y ∉ (H - pullCart t H₀).supp := by
  first | exact @_root_.GlobalTheory.PullDiv.exists_pullCart_agree | exact _root_.GlobalTheory.PullDiv.exists_pullCart_agree | (intros; apply _root_.GlobalTheory.PullDiv.exists_pullCart_agree <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.divisor_point_proper_lift : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (s : Y ⟶ X) [IsDominant s], Function.Bijective (functionFieldMap s) → IsProper s → ∀ (E' : DivOver (s ≫ p)) (E : DivOver p), DivOver.Over s E' E → ∀ z : X, E.IsAt z → ∃ w : Y, s w = z ∧ E'.IsAt w := by
  first | exact @_root_.GlobalTheory.Discrepancy.DivOver.isAt_lift | exact _root_.GlobalTheory.Discrepancy.DivOver.isAt_lift | (intros; apply _root_.GlobalTheory.Discrepancy.DivOver.isAt_lift <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.log_resolution_multiplier_local : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ : X → ℚ) (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y), IsLogMult p n Δ η m G → IsLogRes p n η m G s K B → ∀ x : X, (KltAt p n Δ x ↔ ∀ w : Y, s w ⤳ x → (pullCart s G - m • K).mult w < m) ∧ (LcAt p n Δ x ↔ ∀ w : Y, s w ⤳ x → (pullCart s G - m • K).mult w ≤ m) := by
  first | exact @_root_.GlobalTheory.Discrepancy.kltAt_lcAt_iff_of_isLogRes | exact _root_.GlobalTheory.Discrepancy.kltAt_lcAt_iff_of_isLogRes | (intros; apply _root_.GlobalTheory.Discrepancy.kltAt_lcAt_iff_of_isLogRes <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
namespace GlobalTheory.Discrepancy

theorem isOpen_setOf_forall_specializes_of_finite {X Y : Type} [TopologicalSpace X] (s : Y → X)
    (P : Y → Prop) (hP : {w | ¬ P w}.Finite) :
    IsOpen {x : X | ∀ w : Y, s w ⤳ x → P w} := by
  have h : {x : X | ∀ w : Y, s w ⤳ x → P w} = (⋃ w ∈ {w | ¬ P w}, closure {s w})ᶜ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_iUnion, not_exists,
      ← specializes_iff_mem_closure]
    exact ⟨fun h w hw hx => hw (h w hx), fun h w hx => by_contra fun hw => h w hw hx⟩
  rw [h]
  exact (hP.isClosed_biUnion fun w _ => isClosed_closure).isOpen_compl

theorem isOpen_kltAt_and_lcAt_of_isLogRes : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ : X → ℚ) (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y), IsLogMult p n Δ η m G → IsLogRes p n η m G s K B → IsOpen {x : X | KltAt p n Δ x} ∧ IsOpen {x : X | LcAt p n Δ x} := by
  intro k _ _ X _ _ _ p n hproj hn Δ η m G Y _ _ s _ K B hlm hres
  obtain ⟨N, i, hi, hpi⟩ := hres.proj
  haveI : QuasiCompact (s ≫ p) := hpi ▸ inferInstance
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (s ≫ p)
  have hfin := (pullCart s G - m • K).finite_support_mult
  have hm : (0 : ℤ) < m := by exact_mod_cast hlm.pos
  have hiff := kltAt_lcAt_iff_of_isLogRes k X p n hproj hn Δ η m G Y s K B hlm hres
  constructor
  · have : {x : X | KltAt p n Δ x} =
        {x : X | ∀ w : Y, s w ⤳ x → (pullCart s G - m • K).mult w < m} := by
      ext x
      exact (hiff x).1
    rw [this]
    refine isOpen_setOf_forall_specializes_of_finite _ _ (hfin.subset fun w hw => ?_)
    simp only [Set.mem_setOf_eq, not_lt] at hw
    simp only [Function.mem_support]
    omega
  · have : {x : X | LcAt p n Δ x} =
        {x : X | ∀ w : Y, s w ⤳ x → (pullCart s G - m • K).mult w ≤ m} := by
      ext x
      exact (hiff x).2
    rw [this]
    refine isOpen_setOf_forall_specializes_of_finite _ _ (hfin.subset fun w hw => ?_)
    simp only [Set.mem_setOf_eq, not_le] at hw
    simp only [Function.mem_support]
    omega

end GlobalTheory.Discrepancy
end
