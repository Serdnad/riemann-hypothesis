module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2461
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle978
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2460
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1441
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2431
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle032
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2352
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2430
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2486
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2055
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2309
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1910
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2487
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
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Discrepancy.CoeffPlaces

variable {Z : Scheme.{0}} [IsIntegral Z]

theorem supp_neg_le' (D : CartierDiv Z) : (-D).supp ≤ D.supp := fun x hx h =>
  hx (by simpa using h.neg)

theorem supp_nsmul_le' (D : CartierDiv Z) (r : ℕ) : (r • D).supp ≤ D.supp := by
  induction r with
  | zero => rw [zero_smul, CartierDiv.supp_eq_bot_iff.2 rfl]; exact bot_le
  | succ r ih => rw [succ_nsmul]; exact (CartierDiv.supp_add_le _ _).trans (sup_le ih le_rfl)

variable [IsLocallyNoetherian Z]

theorem mult_zero'' (z : Z) : (0 : CartierDiv Z).mult z = 0 := by
  have h₀ := CartierDiv.mult_add (0 : CartierDiv Z) 0 z
  rw [add_zero] at h₀
  omega

theorem mult_nsmul''' (E : CartierDiv Z) (r : ℕ) (z : Z) : (r • E).mult z = r * E.mult z := by
  induction r with
  | zero => rw [zero_nsmul, mult_zero'']; simp
  | succ r ih => rw [succ_nsmul, CartierDiv.mult_add, ih]; push_cast; ring

theorem mult_sub'' (D E : CartierDiv Z) (z : Z) : (D - E).mult z = D.mult z - E.mult z := by
  have h := CartierDiv.mult_add (D - E) E z
  rw [sub_add_cancel] at h
  omega

theorem ord_nonneg_of_regAt' {f : Z.functionField} {z : Z} (hf : RegAt z f) (h0 : f ≠ 0) :
    0 ≤ Scheme.ord f z := by
  by_cases hz : Order.coheight z = 1
  · obtain ⟨a, rfl⟩ := hf
    have ha : a ≠ 0 := fun h => h0 (by rw [h, map_zero])
    rw [ord_algebraMap hz ha]
    exact Nat.cast_nonneg _
  · exact (Scheme.ord_eq_zero_of_coheight_neq_one hz _).ge

theorem regAt_functionFieldMap' {X : Scheme.{0}} [IsIntegral X] (q : Z ⟶ X) [IsDominant q] (y : Z)
    {f : X.functionField} (h : RegAt (q y) f) : RegAt y (functionFieldMap q f) := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨q.stalkMap y a, (functionFieldMap_algebraMap q y a).symm⟩

end GlobalTheory.Discrepancy.CoeffPlaces


open GlobalTheory.Discrepancy.CoeffPlaces in
theorem GlobalTheory.Discrepancy.neg_one_lt_discrep_add_ord_of_logRes : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (η : RatForms p n) (m : ℕ) (g f : X.functionFieldˣ) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) (y : X) (σ : Y), η ≠ 0 → 0 < m → IsLogRes p n η m (CartierDiv.principal g) s K B → (∀ y', s y' ∈ (CartierDiv.principal f).supp → y' ∈ B) → RegAt y (f : X.functionField) → Scheme.ord ((fnPull s f : Y.functionFieldˣ) : Y.functionField) σ = 1 → (pullCart s (CartierDiv.principal g) - m • K).mult σ = m → (∀ v : Y, v ≠ σ → s v ⤳ y → (pullCart s (CartierDiv.principal g) - m • K).mult v < m) → ∀ E : DivOver p, E.Through y → -1 < discrep E η m g + E.ord f := by
  intro X _ _ p n hproj _ η m g f Y _ _ s _ K B y σ hη hm hres hfB hfy hσ1 hσm hlt E hE
  haveI : IsProper p := GlobalTheory.CommonModel.isProper_of_isProjOver hproj
  haveI : IsProper (s ≫ p) := GlobalTheory.CommonModel.isProper_of_isProjOver hres.proj
  haveI : IsProper s := IsProper.of_comp s p
  haveI := hres.smooth
  obtain ⟨E', hE'E⟩ := GlobalTheory.T.exists_primeDivisor_over_source_birational ℂ X Y p s hres.bir E
  obtain ⟨y', rfl, hE'⟩ := GlobalTheory.T.divisor_center_proper_lift ℂ X Y p s hres.bir inferInstance E' E hE'E _ hE
  have hη' : EtaleKlt.ratPull p s n η ≠ 0 := fun h0 =>
    hη ((GlobalTheory.T.rationalTopFormPullback_bijective_birational ℂ X Y p s hres.bir n).1 (h0.trans (map_zero _).symm))
  set F := pullCart s (CartierDiv.principal f) with hFdef
  set G := pullCart s (CartierDiv.principal g) with hGdef
  have hFsupp : F.supp ≤ B := fun v hv => hfB v ((GlobalTheory.T.cartierDivisorPullback_support_and_effective X Y s _).1 v hv)
  have e : G - m • F - m • K = (G - m • K) + -(m • F) := by abel
  have hsupp : (G - m • F - m • K).supp ≤ B := by
    rw [e]
    exact (CartierDiv.supp_add_le _ _).trans
      (sup_le hres.supp ((supp_neg_le' _).trans ((supp_nsmul_le' _ _).trans hFsupp)))
  have hFm (w : Y) : F.mult w = Scheme.ord ((fnPull s f : Y.functionFieldˣ) : Y.functionField) w :=
    (isEqn_pullCart s (CartierDiv.isEqn_principal f (s w))).mult_eq
  have hEqn : (G - m • F).IsEqn y' (fnPull s g / fnPull s f ^ m) :=
    (isEqn_pullCart s (CartierDiv.isEqn_principal g (s y'))).sub
      ((isEqn_pullCart s (CartierDiv.isEqn_principal f (s y'))).nsmul m)
  have hmul (w : Y) : (G - m • F - m • K).mult w = (G - m • K).mult w - m * F.mult w := by
    rw [mult_sub'', mult_sub'', mult_sub'', mult_nsmul''', mult_nsmul''']; ring
  have hlt' : ∀ w, w ⤳ y' → (G - m • F - m • K).mult w < m := by
    intro w hw
    rw [hmul, hFm]
    by_cases hwσ : w = σ
    · subst hwσ
      rw [hσm, hσ1]
      simp only [mul_one, sub_self]
      exact_mod_cast hm
    · have hsw : s w ⤳ s y' := hw.map s.continuous
      have h0 : 0 ≤ Scheme.ord ((fnPull s f : Y.functionFieldˣ) : Y.functionField) w :=
        ord_nonneg_of_regAt' (regAt_functionFieldMap' s w (regAt_of_specializes hsw hfy))
          (Units.ne_zero _)
      have h1 := hlt w hwσ hsw
      have h2 : (0 : ℤ) ≤ m * Scheme.ord ((fnPull s f : Y.functionFieldˣ) : Y.functionField) w :=
        mul_nonneg (Int.natCast_nonneg m) h0
      linarith
  have hcrit := (GlobalTheory.T.klt_of_snc_coefficients ℂ Y (s ≫ p) n (EtaleKlt.ratPull p s n η) hη' K (G - m • F) m B hm
    hres.div hres.snc hsupp y' _ hEqn E' hE').1 hlt'
  have hd : discrep E' (EtaleKlt.ratPull p s n η) m (fnPull s g / fnPull s f ^ m) =
      discrep E η m g + E.ord f := by
    simp only [discrep]
    have hform := GlobalTheory.T.form_order_birational_pullback ℂ X Y p s hres.bir E' E hE'E n η hη
    change E'.formOrd (EtaleKlt.ratPull p s n η) = E.formOrd η at hform
    rw [hform, div_eq_mul_inv (fnPull s g), E'.ord_mul, E'.ord_inv,
      E'.ord_pow, GlobalTheory.T.ord_functionField_pullback_primeDivisor_over ℂ X Y p s hres.bir E' E hE'E g,
      GlobalTheory.T.ord_functionField_pullback_primeDivisor_over ℂ X Y p s hres.bir E' E hE'E f]
    have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
    push_cast
    field_simp
    ring
  rw [← hd]
  exact hcrit
end
end

section

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

namespace GlobalTheory.SiegelTheta

theorem transp {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a : GAd σ ((1 : E) • J.map σ)) :
    ∃ a' : UA σ J, (a' : GL (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = HA.mat (AF F) σ ((1 : E) • J.map σ) a := by
  have e := GlobalTheory.SiegelSet.ug_eq_hr (F := F) (J := J) hσ (c := (1 : E)) one_ne_zero
  refine ⟨⟨HA.mat (AF F) σ ((1 : E) • J.map σ) a, ?_⟩, rfl⟩
  have : HA.mat (AF F) σ ((1 : E) • J.map σ) a ∈ HR (AF F) σ ((1 : E) • J.map σ) := a.2
  rw [← e] at this
  exact this

theorem ht_bdd {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) {C₀ K : Set (GAd σ J)} (hC₀ : IsCompact C₀) (hK : IsCompact K) :
    ∃ B : ℝ, ∀ x ∈ C₀, ∀ k ∈ K, (heightGL F (HA.mat (AF F) σ J (x * k)) : ℝ) ≤ B := by
  have hc : Continuous fun q : GAd σ J × GAd σ J => (heightGL F (HA.mat (AF F) σ J (q.1 * q.2)) : ℝ) :=
    NNReal.continuous_coe.comp ((GlobalTheory.Grow.continuous_heightGL F).comp (continuous_subtype_val.comp (continuous_mul : Continuous fun p : GAd σ J × GAd σ J => p.1 * p.2)))
  obtain ⟨B, hB⟩ := ((hC₀.prod hK).image hc).bddAbove
  exact ⟨B, fun x hx k hk => hB ⟨(x, k), ⟨hx, hk⟩, rfl⟩⟩

end GlobalTheory.SiegelTheta

namespace GlobalTheory.SiegelTheta

theorem theta_le_seminorm_height_torus : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ) (hP : IsPair B M χX χW om r s r' s') (r₀ : ℕ) (Xf Yf : Matrix (Fin n) (Fin r₀) E),
    GlobalTheory.SiegelSet.IsWittFrame σ ((1 : E) • X.J.map σ) Xf Yf →
    ∀ (Ω C₀ : Set (GAd σ ((1 : E) • X.J.map σ))) (K : Subgroup (GAd σ ((1 : E) • X.J.map σ))) (c : ℝ),
      IsCompact Ω → IsCompact C₀ → IsCompact (K : Set (GAd σ ((1 : E) • X.J.map σ))) → 0 < c →
      (∀ p ∈ Ω, ∀ t ∈ GlobalTheory.SiegelSet.cone r₀ c, ∀ a, GlobalTheory.SiegelSet.IsTorusElt σ ((1 : E) • X.J.map σ) Xf Yf t a →
        a⁻¹ * p * a ∈ C₀) →
      ∀ φ ∈ SB (Fin n × Fin d → Af F), ∃ (N : ℕ) (C : ℝ) (T : Finset (ℕ × ℕ)),
        ∀ (f : SInf F (Fin n × Fin d)) (h : UA σ W.J) (g : UA σ X.J), ∀ p ∈ Ω, ∀ t ∈ GlobalTheory.SiegelSet.cone r₀ c, ∀ a,
          GlobalTheory.SiegelSet.IsTorusElt σ ((1 : E) • X.J.map σ) Xf Yf t a → ∀ k ∈ K,
          g.1 = HA.mat (AF F) σ ((1 : E) • X.J.map σ) (p * a * k) →
          ‖theta om (pureA F f φ) g h‖ ≤
            C * (T.sup (schwartzSeminormFamily ℂ (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ)) f *
              (ht h : ℝ) ^ N * ∏ i, t i ^ (Module.finrank ℚ F * d) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP r₀ Xf Yf hfr Ω C₀ K c hΩ hC₀ hK hc hconj φ hφ
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.SiegelSet.sigma_sigma hP.base.cm
  obtain ⟨Bd, hBd⟩ := ht_bdd ((1 : E) • X.J.map σ) hC₀ hK
  let I := {q : UA σ W.J × UA σ X.J × GAd σ ((1 : E) • X.J.map σ) × (Fin r₀ → ℝ) × GAd σ ((1 : E) • X.J.map σ) ×
      GAd σ ((1 : E) • X.J.map σ) // q.2.2.1 ∈ Ω ∧ q.2.2.2.1 ∈ GlobalTheory.SiegelSet.cone r₀ c ∧
      GlobalTheory.SiegelSet.IsTorusElt σ ((1 : E) • X.J.map σ) Xf Yf q.2.2.2.1 q.2.2.2.2.1 ∧ q.2.2.2.2.2 ∈ K ∧
      (q.2.1 : GL (Fin n) (AE F E)) = HA.mat (AF F) σ ((1 : E) • X.J.map σ) (q.2.2.1 * q.2.2.2.2.1 * q.2.2.2.2.2)}
  have hT := fun q : I => GlobalTheory.T.theta_kernel_continuous_functional F E σ B n d X W M χX χW om r s r' s' hP φ hφ q.1.2.1 q.1.1
  choose T hT using hT
  let P : I → ℝ := fun q => ∏ i, q.1.2.2.2.1 i ^ (Module.finrank ℚ F * d)
  have hP0 : ∀ q : I, 0 < P q := fun q => Finset.prod_pos fun i _ => pow_pos (q.2.2.1.1 i) _
  have hpt : ∀ f : SchwartzMap (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ, ∃ (N : ℕ) (C : ℝ), ∀ q : I,
      ‖((P q)⁻¹ • T q) f‖ ≤ C * (ht q.1.1 : ℝ) ^ N := by
    intro f
    obtain ⟨C₁, k₁, h₁⟩ := GlobalTheory.T.siegel_set_witt_frame_schwartz_bound F E σ B n d X W M χX χW om r s r' s' hP r₀ Xf Yf hfr c hc (pureA F f φ)
      (Submodule.subset_span ⟨f, φ, hφ, rfl⟩)
    refine ⟨k₁, |C₁| * (max Bd 0) ^ k₁, fun q => ?_⟩
    obtain ⟨⟨h, g, p, t, a, k⟩, hp, htc, ha, hk, hg⟩ := q
    obtain ⟨a', ha'⟩ := transp hσ X.J a
    have hy : ((a'⁻¹ * g : UA σ X.J) : GL (Fin n) (AE F E)) =
        HA.mat (AF F) σ ((1 : E) • X.J.map σ) ((a⁻¹ * p * a) * k) := by
      have : (a⁻¹ * p * a) * k = a⁻¹ * (p * a * k) := by group
      rw [this]
      change (a' : GL (Fin n) (AE F E))⁻¹ * (g : GL (Fin n) (AE F E)) = _
      rw [ha', hg]
      rfl
    have hty : (ht (a'⁻¹ * g) : ℝ) ≤ max Bd 0 := by
      refine le_trans ?_ (le_max_left _ _)
      show (heightGL F ((a'⁻¹ * g : UA σ X.J) : GL (Fin n) (AE F E)) : ℝ) ≤ Bd
      rw [hy]
      exact hBd _ (hconj p hp t htc a ha) k hk
    have hb := h₁ t htc a ha a' ha' (a'⁻¹ * g) h
    rw [mul_inv_cancel_left] at hb
    have hPq : 0 < ∏ i, t i ^ (Module.finrank ℚ F * d) := Finset.prod_pos fun i _ => pow_pos (htc.1 i) _
    show ‖((∏ i, t i ^ (Module.finrank ℚ F * d))⁻¹ • T _) f‖ ≤ _
    rw [ContinuousLinearMap.smul_apply, ← hT, norm_smul, Real.norm_of_nonneg (inv_pos.2 hPq).le]
    have h0 : (0 : ℝ) ≤ (ht h : ℝ) := NNReal.coe_nonneg _
    have hy0 : (0 : ℝ) ≤ (ht (a'⁻¹ * g) : ℝ) := NNReal.coe_nonneg _
    calc (∏ i, t i ^ (Module.finrank ℚ F * d))⁻¹ * ‖theta om (pureA F f φ) g h‖
        ≤ (∏ i, t i ^ (Module.finrank ℚ F * d))⁻¹ * (C₁ * ((ht (a'⁻¹ * g) : ℝ) * ht h) ^ k₁ *
            ∏ i, t i ^ (Module.finrank ℚ F * d)) := mul_le_mul_of_nonneg_left hb (inv_pos.2 hPq).le
      _ = C₁ * ((ht (a'⁻¹ * g) : ℝ) * ht h) ^ k₁ := by field_simp
      _ ≤ |C₁| * ((max Bd 0) * ht h) ^ k₁ :=
          mul_le_mul (le_abs_self _) (pow_le_pow_left₀ (mul_nonneg hy0 h0) (mul_le_mul_of_nonneg_right hty h0) _)
            (pow_nonneg (mul_nonneg hy0 h0) _) (abs_nonneg _)
      _ = |C₁| * (max Bd 0) ^ k₁ * (ht h : ℝ) ^ k₁ := by rw [mul_pow]; ring
  obtain ⟨N, C, S, hN⟩ := GlobalTheory.T.uniform_schwartz_seminorm_bound (Fin n × Fin d → mixedEmbedding.mixedSpace F) I (fun q => (P q)⁻¹ • T q)
    (fun q => (ht q.1.1 : ℝ)) (fun q => NNReal.coe_nonneg _) hpt
  refine ⟨N, C, S, fun f h g p hp t htc a ha k hk hg => ?_⟩
  let q : I := ⟨(h, g, p, t, a, k), hp, htc, ha, hk, hg⟩
  have e1 : theta om (pureA F f φ) g h = P q • ((P q)⁻¹ • T q f) := by
    rw [smul_smul, mul_inv_cancel₀ (hP0 q).ne', one_smul]
    exact hT q f
  have e2 := hN q f
  simp only [ContinuousLinearMap.smul_apply] at e2
  rw [e1, norm_smul, Real.norm_of_nonneg (hP0 q).le]
  calc P q * ‖(P q)⁻¹ • T q f‖ ≤ P q * (C * (S.sup (schwartzSeminormFamily ℂ _ ℂ)) f * (ht h : ℝ) ^ N) :=
        mul_le_mul_of_nonneg_left e2 (hP0 q).le
    _ = _ := by ring

end GlobalTheory.SiegelTheta
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm.CrysCmp

theorem exists_compatibleFormsCocycle_deRhamClass {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (c : FirstDeRham s) :
    ∃ (f₀ : Z1 (O (dp0 R) s)) (k₀ : (KK (dp0 R) s).Z1), k₀.1.1 = f₀.1 ∧ H1.mk _ f₀ = c := by
  obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
  have hb := (GlobalTheory.T.fnMap_pullbackBijective12_kk_and_res R ⊥ (dp0 R) X s X (𝟙 X)).1.1.2
  have hfe : ((f.1, fun _ ↦ PUnit.unit) : (Cx.single (KK (dp0 R) s).M0).T1) ∈ (Cx.single (KK (dp0 R) s).M0).Z1 := by
    refine AddMonoidHom.mem_ker.2 (Prod.ext ?_ (Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)))
    funext T T' T'' φ ψ
    change mp (O (dp0 R) s) ψ (f.1 _ _ φ) - f.1 _ _ (φ ≫ ψ) + f.1 _ _ ψ = 0
    rw [f.2 φ ψ]; abel
  obtain ⟨q, hq⟩ := hb (QuotientAddGroup.mk ⟨_, hfe⟩)
  obtain ⟨k₀, rfl⟩ := QuotientAddGroup.mk_surjective q
  have hq' := QuotientAddGroup.eq.1 ((QuotientAddGroup.map_mk _ _ _ _ k₀).symm.trans hq)
  rw [AddSubgroup.mem_addSubgroupOf] at hq'
  obtain ⟨g, hg⟩ := hq'
  have hk := AddMonoidHom.mem_ker.1 k₀.2
  let f₀ : Z1 (O (dp0 R) s) := ⟨k₀.1.1, fun T T' T'' φ ψ ↦ by
    have := congrFun (congrFun (congrFun (congrFun (congrFun (congrArg Prod.fst hk) T) T') T'') φ) ψ
    change mp (O (dp0 R) s) ψ (k₀.1.1 _ _ φ) - k₀.1.1 _ _ (φ ≫ ψ) + k₀.1.1 _ _ ψ = 0 at this
    change k₀.1.1 _ _ (φ ≫ ψ) = mp (O (dp0 R) s) ψ (k₀.1.1 _ _ φ) + k₀.1.1 _ _ ψ
    linear_combination (norm := abel1) -this⟩
  refine ⟨f₀, k₀, rfl, ?_⟩
  rw [H1.mk_eq_mk]
  refine ⟨-g, ?_⟩
  funext T T' φ
  have := congrFun (congrFun (congrFun (congrArg Prod.fst hg) T) T') φ
  change g T' - mp (O (dp0 R) s) φ (g T) = -(k₀.1.1 T T' φ) + f.1 T T' φ at this
  change -g T' - mp (O (dp0 R) s) φ (-g T) = k₀.1.1 T T' φ - f.1 T T' φ
  rw [map_neg]
  linear_combination (norm := abel1) -this

section Theta

variable {D : Data} (Λ : Lift D) (m : IsMor (dp0 D.R) D.s D.κ D.t (RingHom.id D.R) D.i)

def thAlg (U : AffOp D.X) : Sec D.s U.unop.1 →ₐ[D.R] (m.obj (Λ.L.obj U)).B :=
  { (Λ.e U : Sec D.s U.unop.1 →+* (Λ.L.obj U).B) with commutes' := fun r ↦ (Λ.e U).commutes r }

def theta (U : AffOp D.X) :
    Thick.triv (Sec D.s U.unop.1) (affPt D.s U.unop) (affPt_w D.s U.unop) ⟶ m.obj (Λ.L.obj U) :=
  Thick.trivHom (thAlg Λ m U) (Λ.pt U)

end Theta

theorem key4 {G : Type} [AddCommGroup G] (A B C E : G) (h : A + B = C + E) : E - A = B - C := by
  rw [sub_eq_sub_iff_add_eq_add, add_comm E C, ← h, add_comm]

theorem lift_rel1_pull1_cmp1 : ∀ (D : Data) (Λ : Lift D) (m : IsMor (dp0 D.R) D.s D.κ D.t (RingHom.id D.R) D.i) (c : FirstDeRham D.s), Λ.Rel1 (m.pull1 c) (cmp1 D.s c) := by
  intro D Λ m c
  obtain ⟨f₀, k₀, hk, rfl⟩ := exists_compatibleFormsCocycle_deRhamClass D.s c
  let k := (morMap m).z1 k₀
  let k' := ((KK D.κ D.t).resMap Λ.L).p1 k.1
  have hk' : k' ∈ ((KK D.κ D.t).res Λ.L).Z1 := (((KK D.κ D.t).resMap Λ.L).z1 k).2
  obtain ⟨w, hw, -⟩ := ((GlobalTheory.T.compatibleFormsCochains_eq_deRhamCochains_smoothLift).1 D Λ).1 k'
  have hwZ : w ∈ cechDeRhamTotalCocyclesOne (OAff D.s) := ((((GlobalTheory.T.compatibleFormsCochains_eq_deRhamCochains_smoothLift).1 D Λ).2.2 k' w hw).1.1 hk')
  refine ⟨k, m.coef.pullbackOneCocycle f₀, ⟨w, hwZ⟩, rfl, ?_, ?_, hw⟩

  · rw [comparison_mk, Hyp1.mk_eq_mk]
    refine ⟨fun U ↦ (Λ.e U).symm (ev f₀ (theta Λ m U)), Tot1.ext (fun U V a ↦ ?_) (fun U ↦ ?_)⟩
    · change (Λ.e V).symm (ev f₀ (theta Λ m V)) - Sec.res D.s (leOfHom a.unop) ((Λ.e U).symm (ev f₀ (theta Λ m U))) =
        w.1 U V a - (cmpZZ D.s f₀).1.1 U V a
      apply (Λ.e V).injective
      have h1 : Λ.e V (w.1 U V a) = ev f₀ (m.functor.map (Λ.L.map a)) := by
        refine (hw.1 U V a).symm.trans ?_
        change k₀.1.1 _ _ _ = _
        rw [hk]; rfl
      have h2 := Λ.nat a ((Λ.e U).symm (ev f₀ (theta Λ m U)))
      erw [AlgEquiv.apply_symm_apply] at h2
      have sq := ev_sq f₀ (theta Λ m U) (m.functor.map (Λ.L.map a))
          (Thick.trivHom (hx := affPt_w D.s U.unop) (T := Thick.triv _ _ (affPt_w D.s V.unop))
            (Sec.res D.s (leOfHom a.unop)) (affPt_res D.s (leOfHom a.unop))) (theta Λ m V)
          (by intro c; exact (Λ.nat a c).symm)
      rw [map_sub, map_sub, h1, cmpZZ_f]
      erw [AlgEquiv.apply_symm_apply]
      change _ - Λ.e V (mp (OAff D.s) a _) = _
      rw [h2]
      exact key4 _ _ _ _ sq
    · change KaehlerDifferential.D D.R (Sec D.s U.unop.1) ((Λ.e U).symm (ev f₀ (theta Λ m U))) =
        w.2 U - connForm f₀ (affPt D.s U.unop) (affPt_w D.s U.unop)
      have hrel : rel D.R (Λ.L.obj U).δ = ⊥ :=
        (GlobalTheory.T.divPowerCompatRel_filtration_twoSided_rel_eq_bot_of_base).2 D.R (Λ.L.obj U).B (Λ.L.obj U).J (Λ.L.obj U).δ D.I D.κ (Λ.L.obj U).dp (Λ.gen U).le
      have inj : ∀ x y : Ω[(Λ.L.obj U).B⁄D.R],
          (Submodule.Quotient.mk x : K1 D.R (Λ.L.obj U).δ) = Submodule.Quotient.mk y → x = y := by
        intro x y h
        rw [Submodule.Quotient.eq] at h
        have h' : ι1 (x - y) ∈ rel D.R (Λ.L.obj U).δ := h
        rw [hrel, Ideal.mem_bot, map_sub, sub_eq_zero] at h'
        exact (ExteriorAlgebra.ι_inj _ _ _).1 h'
      have hk0 := AddMonoidHom.mem_ker.1 k₀.2
      have hcoc := congrFun (congrFun (congrFun (congrArg (fun x ↦ x.2.1) hk0) _) _) (theta Λ m U)
      have hc := GlobalTheory.T.compatibleFormsCocycle_form_eq_connectionForm D.R D.X D.s k₀ f₀ hk (Sec D.s U.unop.1) (affPt D.s U.unop) (affPt_w D.s U.unop)
      have e1 : k₀.1.2 (m.obj (Λ.L.obj U)) = km1 (SemiHom.of_algHom (theta Λ m U).φ) (theta Λ m U).dp (k₀.1.2 _) +
          kd0 D.R (m.obj (Λ.L.obj U)).δ (ev f₀ (theta Λ m U)) := by
        have : k₀.1.2 (m.obj (Λ.L.obj U)) - km1 (SemiHom.of_algHom (theta Λ m U).φ) (theta Λ m U).dp (k₀.1.2 _) -
            kd0 D.R (m.obj (Λ.L.obj U)).δ (k₀.1.1 _ _ (theta Λ m U)) = 0 := hcoc
        rw [hk] at this
        exact sub_eq_zero.1 ((sub_sub _ _ _).symm.trans this)
      rw [hc, divPowerCompatOneFormMap_mk, divPowerCompatFunctionDifferential_apply, ← Submodule.Quotient.mk_add] at e1
      have e2 := hw.2 U
      change km1 (morSemi m (Λ.L.obj U)) (morDP m (Λ.L.obj U)) (k₀.1.2 (m.obj (Λ.L.obj U))) = _ at e2
      rw [e1] at e2
      erw [divPowerCompatOneFormMap_mk] at e2
      have e3 := inj _ _ e2
      have e3' : (Λ.semi U).m1 (w.2 U) = (Λ.semi U).m1 (connForm f₀ (affPt D.s U.unop) (affPt_w D.s U.unop)) +
          KaehlerDifferential.D D.R (Λ.L.obj U).B (ev f₀ (theta Λ m U)) := by
        rw [← e3, map_add (f := _)]
        congr 1
        · exact SemiHom.oneFormMap_comp_oneFormMap _ _ _ (fun _ ↦ rfl) _
        · exact SemiHom.m1_D _ _
      have semiInv : SemiHom (RingHom.id D.R) ((Λ.e U).symm : (Λ.L.obj U).B →+* Sec D.s U.unop.1) :=
        fun r b ↦ map_smul (Λ.e U).symm r b
      have linv : ∀ ω, semiInv.m1 ((Λ.semi U).m1 ω) = ω := fun ω ↦
        (SemiHom.oneFormMap_comp_oneFormMap (Λ.semi U) semiInv (SemiHom.of_algHom (AlgHom.id D.R (Sec D.s U.unop.1)))
          (fun b ↦ (Λ.e U).symm_apply_apply b) ω).trans (SemiHom.oneFormMap_eq_self_of_id _ (fun _ ↦ rfl) ω)
      have e5 := congrArg semiInv.m1 e3'
      rw [map_add (f := _), linv, linv] at e5
      rw [e5, add_sub_cancel_left]
      exact (SemiHom.m1_D semiInv _).symm
  · funext T T' φ
    change k₀.1.1 _ _ (m.functor.map φ) = f₀.1 _ _ (m.functor.map φ)
    rw [hk]

end GlobalTheory.PDForm.CrysCmp
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem isLocalizedModule_ratTensor (M : Type) [AddCommGroup M] :
    IsLocalizedModule (nonZeroDivisors ℤ) (TensorProduct.mk ℤ ℚ M 1) :=
  (isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ) ℚ _).2 (TensorProduct.isBaseChange ℤ M ℚ)

theorem toEnd0_apply {K : Type} [Field K] (A : AbVar K) (f : End A) :
    toEnd0 A f = TensorProduct.mk ℤ ℚ (End A) 1 f := rfl

theorem toEnd0_injective_and_fraction : ∀ (K : Type) [Field K] (A : AbVar K),
    Function.Injective (toEnd0 A) ∧ ∀ x : End0 A, ∃ (n : ℕ) (f : End A), 0 < n ∧ n • x = toEnd0 A f := by
  intro K _ A
  haveI := isLocalizedModule_ratTensor (End A)
  refine ⟨fun f g h => ?_, fun x => ?_⟩
  · rw [toEnd0_apply, toEnd0_apply] at h
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := nonZeroDivisors ℤ) h
    have hc0 : (c : ℤ) ≠ 0 := nonZeroDivisors.coe_ne_zero c
    have h1 : (c : ℤ) • (f - g) = 0 := by
      rw [smul_sub, sub_eq_zero]
      simpa [Submonoid.smul_def] using hc
    apply sub_eq_zero.1
    apply End.addEquiv.injective
    apply GlobalTheory.T.abVar_hom_eq_zero_of_nsmul_eq_zero K A A (c : ℤ) _ hc0
    have hh := congrArg (End.addEquiv (X := A)) h1
    rw [map_zsmul, map_zero] at hh
    exact hh
  · obtain ⟨⟨m, c⟩, hc⟩ := IsLocalizedModule.surj (nonZeroDivisors ℤ) (TensorProduct.mk ℤ ℚ (End A) 1) x
    have hc0 : (c : ℤ) ≠ 0 := nonZeroDivisors.coe_ne_zero c
    simp only [Submonoid.smul_def] at hc
    rcases Int.natAbs_eq (c : ℤ) with h | h
    · refine ⟨(c : ℤ).natAbs, m, Int.natAbs_pos.2 hc0, ?_⟩
      rw [toEnd0_apply, ← hc, ← natCast_zsmul, ← h]
    · refine ⟨(c : ℤ).natAbs, -m, Int.natAbs_pos.2 hc0, ?_⟩
      have h' : (((c : ℤ).natAbs : ℕ) : ℤ) = -(c : ℤ) := by omega
      rw [toEnd0_apply, map_neg, ← hc, ← natCast_zsmul, h', neg_smul]

end GlobalTheory.AV.AbVar
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw


theorem _root_.GlobalTheory.T.realPolynomialVector_reached_by_realDatum : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G)
    (e : Num G i j) (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
    (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (h : IsTripleOf W M t i j e Bs Γ X), IsTriple Bs Γ X om om' → ∀ n Φ τ τ', HasFlip B t ρ i j n Φ τ τ' →
    ∀ φ, IsFinPart Γ.M X.T φ → ∀ f₀, f₀ ≠ 0 → Γ.M.IsGauss Bs.ψ Bs.emb f₀ → IsDatumA W e Γ τ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ φ) →
    ∀ f ∈ Γ.M.Pol Bs.ψ Bs.emb, ∃ a, IsDatumA W e Γ (tensT W a τ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) := by
  first | exact @GlobalTheory.BigNZ.DatReal.datum_real | exact GlobalTheory.BigNZ.DatReal.datum_real | (intros; apply GlobalTheory.BigNZ.DatReal.datum_real <;> assumption)
end
