module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle978
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2461
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2460
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1441
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle029
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.KltOfSncCoefficients
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2431
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

namespace GlobalTheory.Discrepancy

theorem regAt_of_regularAt_neg_roundDown : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ : X → ℚ) (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) (F : CartierDiv Y), (∀ z, 0 ≤ Δ z) → IsLogMult p n Δ η m G → IsLogRes p n η m G s K B → (∀ z, F.mult z = (pullCart s G - m • K).mult z / (m : ℤ)) → ∀ (x : X) (f : X.functionField), (∀ y : Y, s y ⤳ x → (-F).RegularAt y (functionFieldMap s f)) → RegAt x f := by
  intro k _ _ X _ _ _ p n hproj _ Δ η m G Y _ _ s _ K B F hΔ hmult hres hF x f hf
  haveI : IsProper p := GlobalTheory.CommonModel.isProper_of_isProjOver hproj
  haveI : IsProper (s ≫ p) := GlobalTheory.CommonModel.isProper_of_isProjOver hres.proj
  haveI : IsProper s := IsProper.of_comp s p
  haveI := hres.smooth
  by_cases hf0 : f = 0
  · subst hf0; exact regAt_zero x
  refine regAt_of_forall_coheight_eq_one fun z hzx hz1 => ?_
  obtain ⟨E, hE⟩ := DivOver.exists_isAt_of_coheight_eq_one (p := p) hz1
  obtain ⟨E', hE'E⟩ := GlobalTheory.T.exists_primeDivisor_over_source_birational k X Y p s hres.bir E
  obtain ⟨w, rfl, hE'⟩ := GlobalTheory.T.divisor_point_proper_lift k X Y p s hres.bir inferInstance E' E hE'E _ hE
  obtain ⟨g, hg⟩ := G.exists_isEqn (s w)
  have hg' := isEqn_pullCart s hg
  have hη' : EtaleKlt.ratPull p s n η ≠ 0 := fun h0 =>
    hmult.ne_zero ((GlobalTheory.T.rationalTopFormPullback_bijective_birational k X Y p s hres.bir n).1 (h0.trans (map_zero _).symm))
  have hd := GlobalTheory.T.discrepancy_formula_divisor k Y (s ≫ p) n (EtaleKlt.ratPull p s n η) hη' K (pullCart s G) m
    hmult.pos hres.div E' w (fnPull s g) hE' hg'
  have hd2 : discrep E' (EtaleKlt.ratPull p s n η) m (fnPull s g) = discrep E η m g := by
    simp only [discrep]
    have hform := GlobalTheory.T.form_order_birational_pullback k X Y p s hres.bir E' E hE'E n η hmult.ne_zero
    change E'.formOrd (EtaleKlt.ratPull p s n η) = E.formOrd η at hform
    rw [hform, GlobalTheory.T.ord_functionField_pullback_primeDivisor_over k X Y p s hres.bir E' E hE'E g]
  have hd3 := (hmult.eqn _ g hg).discrep_eq_neg hmult.pos (specializes_refl _) hE
  have hm : (0 : ℚ) < m := by exact_mod_cast hmult.pos
  have hnn : 0 ≤ (pullCart s G - m • K).mult w := by
    have e : ((pullCart s G - m • K).mult w : ℚ) / m = Δ (s w) := by
      rw [← hd2, hd] at hd3
      rw [neg_div] at hd3
      exact neg_injective hd3
    have h0 : (0 : ℚ) ≤ ((pullCart s G - m • K).mult w : ℚ) / m := e ▸ hΔ (s w)
    have := (div_nonneg_iff.1 h0)
    rcases this with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact_mod_cast h1
    · exact absurd h2 (not_le.2 hm)
  have hFn : 0 ≤ F.mult w := by
    rw [hF]; exact Int.ediv_nonneg hnn (by exact_mod_cast hmult.pos.le)
  obtain ⟨h, hh⟩ := F.exists_isEqn w
  have hreg := (hh.neg.regularAt_iff).1 (hf w hzx)
  set u : X.functionFieldˣ := Units.mk0 f hf0 with hu
  have hv : ((fnPull s u * h⁻¹ : Y.functionFieldˣ) : Y.functionField) =
      functionFieldMap s f * ((h⁻¹ : Y.functionFieldˣ) : Y.functionField) := by
    simp [hu, fnPull]
  have h1 : 0 ≤ E'.ord (fnPull s u * h⁻¹) :=
    (E'.ord_nonneg_iff _).2 (hv ▸ (hE' _).2 hreg)
  rw [E'.ord_mul, E'.ord_inv, GlobalTheory.T.ord_functionField_pullback_primeDivisor_over k X Y p s hres.bir E' E hE'E u, hE'.ord_eq h,
    ← hh.mult_eq] at h1
  have h2 : 0 ≤ E.ord u := by omega
  exact (hE f).1 ((E.ord_nonneg_iff u).1 h2)

end GlobalTheory.Discrepancy
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy

theorem inMultAt_one_iff_kltAt {k : Type} [Field k] [CharZero k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] {p : X ⟶ Sp k} {n : ℕ} (hp : IsProjOver p)
    (hn : topologicalKrullDim X = n) {Δ : X → ℚ} {η : RatForms p n} {m : ℕ} {G : CartierDiv X}
    (hM : IsLogMult p n Δ η m G) (y : X) : InMultAt p n η m G y 1 ↔ KltAt p n Δ y := by
  haveI : IsProper p := GlobalTheory.CommonModel.isProper_of_isProjOver hp
  have hkey : ∀ g, G.IsEqn y g → (KltAt p n Δ y ↔ ∀ (E : DivOver p), E.Through y → -1 < discrep E η m g) :=
    fun g hg => IsLogEqn.kltAt_iff hn hM.ne_zero hM.pos (hM.eqn y g hg)
  constructor
  · intro h
    obtain ⟨g, hg⟩ := G.exists_isEqn y
    rw [hkey g hg]
    intro E hE
    have h1 := h g hg E hE
    simpa [DivOver.ord_one] using h1
  · intro h g hg E hE
    have h1 := (hkey g hg).1 h E hE
    simpa [DivOver.ord_one] using h1

theorem one_mem_ideal_iff {k : Type} [Field k] [CharZero k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] {p : X ⟶ Sp k} {n : ℕ} (hp : IsProjOver p)
    (hn : topologicalKrullDim X = n) {Δ : X → ℚ} {η : RatForms p n} {m : ℕ} {G : CartierDiv X}
    (hM : IsLogMult p n Δ η m G) {J : X.IdealSheafData} (hJ : IsMultIdeal p n η m G J)
    (U : X.affineOpens) : (1 : Γ(X, U.1)) ∈ J.ideal U ↔ ∀ y ∈ U.1, KltAt p n Δ y := by
  rw [hJ U 1]
  constructor
  · intro h y hy
    exact (inMultAt_one_iff_kltAt hp hn hM y).1 (h y hy 1 (by simp))
  · intro h y hy u hu
    have : u = 1 := Units.ext (by simpa using hu)
    subst this
    exact (inMultAt_one_iff_kltAt hp hn hM y).2 (h y hy)

theorem mem_support_multIdeal_iff : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ : X → ℚ) (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y), IsLogMult p n Δ η m G → IsLogRes p n η m G s K B → ∀ J : X.IdealSheafData, IsMultIdeal p n η m G J → ∀ x : X, x ∈ J.support ↔ ¬ KltAt p n Δ x := by
  intro k _ _ X _ _ _ p n hp hn Δ η m G Y _ _ s _ K B hM hR J hJ x
  have hO := (isOpen_kltAt_and_lcAt_of_isLogRes k X p n hp hn Δ η m G Y s K B hM hR).1
  have hb : ∀ {U : X.Opens} {z : X}, z ∈ U → ∃ U' ∈ X.affineOpens, z ∈ U' ∧ U' ≤ U :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
  constructor
  · intro hx hk
    obtain ⟨V, hV, hxV, hVO⟩ := hb (show x ∈ (⟨_, hO⟩ : X.Opens) from hk)
    have h1 : (1 : Γ(X, V)) ∈ J.ideal ⟨V, hV⟩ :=
      (one_mem_ideal_iff hp hn hM hJ ⟨V, hV⟩).2 (fun y hy => hVO hy)
    have h2 := (Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨V, hV⟩) hxV).1 hx
    rw [Scheme.mem_zeroLocus_iff] at h2
    exact h2 1 h1 (by rw [Scheme.basicOpen_one]; exact hxV)
  · intro hnk
    by_contra hx
    obtain ⟨V, hV, hxV, -⟩ := hb (show x ∈ (⊤ : X.Opens) from trivial)
    have h2 : ¬ x ∈ X.zeroLocus (J.ideal ⟨V, hV⟩ : Set Γ(X, V)) := fun h =>
      hx ((Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨V, hV⟩) hxV).2 h)
    rw [Scheme.mem_zeroLocus_iff] at h2
    push_neg at h2
    obtain ⟨f, hf, hfx⟩ := h2
    rw [Scheme.mem_basicOpen X f x hxV] at hfx
    haveI : Nonempty V := ⟨⟨x, hxV⟩⟩
    have hgen : algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ V x hxV f) =
        X.germToFunctionField V f := by simp
    have hunit : IsUnit (X.germToFunctionField V f) := by
      rw [← hgen]
      exact hfx.map _
    have hmem := (hJ ⟨V, hV⟩ f).1 hf x hxV hunit.unit (by rw [IsUnit.unit_spec]; rfl)
    apply hnk
    rw [← inMultAt_one_iff_kltAt hp hn hM x]
    intro g hg E hE
    have h3 := hmem g hg E hE
    have h4 : E.ord hunit.unit = 0 :=
      DivOver.ord_eq_zero_of_unitAt hE _ ⟨_, hfx, by rw [IsUnit.unit_spec]; exact hgen⟩
    simpa [h4, DivOver.ord_one] using h3

end GlobalTheory.Discrepancy
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.log_resolution_multiplier_open : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ : X → ℚ) (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y), IsLogMult p n Δ η m G → IsLogRes p n η m G s K B → IsOpen {x : X | KltAt p n Δ x} ∧ IsOpen {x : X | LcAt p n Δ x} := by
  first | exact @_root_.GlobalTheory.Discrepancy.isOpen_kltAt_and_lcAt_of_isLogRes | exact _root_.GlobalTheory.Discrepancy.isOpen_kltAt_and_lcAt_of_isLogRes | (intros; apply _root_.GlobalTheory.Discrepancy.isOpen_kltAt_and_lcAt_of_isLogRes <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy

theorem isMultIdeal_iff_regularAt : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → ∀ (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) (F : CartierDiv Y), η ≠ 0 → 0 < m → IsLogRes p n η m G s K B → (∀ z, F.mult z = (pullCart s G - m • K).mult z / (m : ℤ)) → ∀ J : X.IdealSheafData, IsMultIdeal p n η m G J ↔ (∀ (U : X.affineOpens) (f : Γ(X, U.1)), f ∈ J.ideal U ↔ ∀ (y : Y) (hy : s y ∈ U.1), (-F).RegularAt y (functionFieldMap s (fnOf U.1 (gen_mem hy) f))) := by
  intro k _ _ X _ p n hproj η m G Y _ _ s _ K B F hη hm hres hF J
  have key := inMultAt_iff_regularAt_logRes k X p n hproj η m G Y s K B F hη hm hres hF
  unfold IsMultIdeal
  refine forall_congr' fun U => forall_congr' fun f => iff_congr Iff.rfl ?_
  constructor
  · intro H y hy
    by_cases h0 : fnOf U.1 (gen_mem hy) f = 0
    · rw [h0, map_zero]
      obtain ⟨g, hg⟩ := (-F).exists_isEqn y
      refine ⟨g, hg, ?_⟩
      rw [zero_mul]
      exact (regAt_zero (X := Y) (x := y))
    · have := (key (s y) (Units.mk0 _ h0)).1 (H (s y) hy _ rfl) y rfl
      simpa using this
  · intro H x hx u hu
    rw [key]
    rintro y rfl
    rw [hu]
    exact H y hx

end GlobalTheory.Discrepancy
end
