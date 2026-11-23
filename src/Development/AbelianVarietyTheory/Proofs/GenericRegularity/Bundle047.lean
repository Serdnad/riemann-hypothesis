module

public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle008
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle029
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsGenericComponentPointsOffMeagre
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle039
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle035
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle020
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle016
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle045
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle005
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle044
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle027
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle020
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle023
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle017
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle025
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifferentiableOnLeftInverse
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle050
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle021
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HostGeneratorPowFourTraceNormModEight
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle028
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle031
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle029
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TypeFnPeriodExistModuliNonempty
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle029
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle045
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle046
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle040
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.RegularCharts.Bundle001
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame

@[expose] public section

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg

theorem _root_.GlobalTheory.T.pointwiseNorm_bddAbove_iSup_eq_cuspForm_supNorm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ (xR : ℝ) (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ), 0 < xR → FnPin U xR fn → ∀ a n, Dom a n → ∀ f ∈ Formalism.L2.PjFree.cusp Xo c U a n, SupBdd Xo c fn a n f ∧ ∀ σ, supR Xo c fn σ a n f = Formalism.L2.PjFree.supC Xo c U xR (Formalism.L2.PjFree.goodOf c σ) a n f := by
  first | exact @GlobalTheory.FrameNorm.SupNorm.supBdd_and_supR_eq | exact GlobalTheory.FrameNorm.SupNorm.supBdd_and_supR_eq | (intros; apply GlobalTheory.FrameNorm.SupNorm.supBdd_and_supR_eq <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif GlobalTheory.FrameNorm
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.FrameNorm.Hol

theorem continuousOn_form {V : Type} [TopologicalSpace V] {g : ℕ} {B : Set V} (h τ : V → Matrix (Fin g) (Fin g) ℂ)
    (hh : ∀ i j, ContinuousOn (fun b => h b i j) B) (hτ : ∀ i j, ContinuousOn (fun b => τ b i j) B)
    (hp : ∀ b ∈ B, ((τ b).map Complex.im).PosDef) :
    ContinuousOn (fun b => ((τ b).map Complex.im).det) B ∧ ∀ i j, ContinuousOn (fun b =>
      ((h b)ᵀ * (((τ b).map Complex.im)⁻¹).map (fun x : ℝ => (x : ℂ)) * (h b).map (starRingEnd ℂ)) i j) B := by
  simp only [continuousOn_iff_continuous_restrict] at hh hτ ⊢
  have h1 : Continuous fun b : B => h b := continuous_matrix hh
  have h2 : Continuous fun b : B => (τ b).map Complex.im :=
    (continuous_matrix hτ : Continuous fun b : B => τ b).matrix_map Complex.continuous_im
  have h3 : Continuous fun b : B => ((τ b).map Complex.im)⁻¹ := by
    simp only [Matrix.inv_def, Ring.inverse_eq_inv']
    exact (h2.matrix_det.inv₀ fun b => (hp b b.2).det_pos.ne').smul h2.matrix_adjugate
  refine ⟨h2.matrix_det, fun i j => ?_⟩
  exact ((h1.matrix_transpose.matrix_mul (h3.matrix_map Complex.continuous_ofReal)).matrix_mul
    (h1.matrix_map Complex.continuous_conj)).matrix_elem i j

theorem exists_continuous_form_mean {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
    {σ : c.F →+* ℂ} {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ' ty) (k : Fin F.n)
    (hty : IsTypeFn H Dw.p Dw.q ty) {A : Type} [CommRing A] [Algebra c.F A] (yA : FrPt Xo c A) {m : ℕ}
    {B : Set (Fin m → ℂ)} (φ : (Fin m → ℂ) → (A →ₐ[c.F] CAt σ)) (y : (Fin m → ℂ) → FrPt Xo c (CAt σ))
    (P : (Fin m → ℂ) → ((F.Di k).La →+ (Fin g → ℂ))) (hB : IsOpen B)
    (hφ : ∀ a, DifferentiableOn ℂ (fun b => Formalism.L2.PjFree.toC (φ b a)) B) (hy : ∀ b ∈ B, FrMap (φ b) yA (y b))
    (hP : IsHolPeriods (F.Di k) ty B P) (hx : ∀ b ∈ B, (y b).x = F.u k (P b)) {b₀ : Fin m → ℂ} (hb₀ : b₀ ∈ B) :
    ∃ (B' : Set (Fin m → ℂ)) (Hm : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ) (μ : (Fin m → ℂ) → ℝ),
      IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ (∀ i j, ContinuousOn (fun b => Hm b i j) B') ∧ ContinuousOn μ B' ∧
      ∀ b ∈ B', (∀ v w, (hermForm (Hm b) (P b v) (P b w)).im = (F.Di k).EF v w) ∧
        AHMean F k (P b) (y b).x (y b).s (μ b) := by
  obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.1 hB b₀ hb₀
  obtain ⟨hg, -⟩ := (GlobalTheory.PeriodExists.typeFn_period_exist E H (F.Di k)).2.1 g ty
    (by rw [(F.sig k).1, (F.sig k).2]; exact hty)
  obtain ⟨bas, hbas, -⟩ := GlobalTheory.exists_symplectic_basis_adapted_mod_eight E H (F.Di k) g hg
  obtain ⟨hR1, hR2⟩ := GlobalTheory.RiemannRel.riemann_relations E H (F.Di k) g ty bas hbas
  have hP' : IsHolPeriods (F.Di k) ty (Metric.ball b₀ ε) P :=
    ⟨fun b hb => hP.1 b (hsub hb), fun v => (hP.2 v).mono hsub⟩
  choose! h τ hn hdet hsym hpos _ using fun b hb => hR1 _ (hP'.1 b hb)
  have hhol := hR2 m _ P h τ hP' hn
  obtain ⟨c₁, c₂, hc₁, hc₂, hθ⟩ := F.theta k m _ P bas (-1) h τ Metric.isOpen_ball
    (convex_ball b₀ ε).isPreconnected hP' (fun a b => by rw [hbas]; simp) (fun b hb => ⟨hpos b hb, hn b hb⟩)
  obtain ⟨t1, t2⟩ := GlobalTheory.ThetaHalf.thetaChar_holomorphic_ne_zero g c₁ c₂ hc₁ hc₂
  have t3 := t2 m _ h τ Metric.isOpen_ball (fun b hb => ⟨hsym b hb, hpos b hb⟩) hhol
  obtain ⟨fr, κ, hfr, hκ, hval⟩ := GlobalTheory.T.exists_holomorphicFactor_generator_thetaSection E H Dw l Xo c σ σ' g ty F k A yA m _ φ y P
    (fun b z => thetaChar (τ b) c₁ c₂ (h b *ᵥ z)) Metric.isOpen_ball
    (fun a => (hφ a).mono hsub) (fun b hb => hy b (hsub hb)) hP' (fun b hb => hx b (hsub hb))
    (fun z => DifferentiableOn.comp (f := fun b : Fin m → ℂ => ((b, z) : (Fin m → ℂ) × (Fin g → ℂ)))
      (g := fun bz : (Fin m → ℂ) × (Fin g → ℂ) => thetaChar (τ bz.1) c₁ c₂ (h bz.1 *ᵥ bz.2))
      t3 (by fun_prop) fun b hb => ⟨hb, trivial⟩)
    (fun b hb => by
      obtain ⟨-, w, hw⟩ := t1 _ (hsym b hb) (hpos b hb)
      obtain ⟨z, hz⟩ := Matrix.mulVec_surjective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 (hdet b hb)) w
      exact ⟨z, by rw [hz]; exact hw⟩) hθ
  obtain ⟨c1, c2⟩ := continuousOn_form h τ (fun i j => (hhol i j).1.continuousOn)
    (fun i j => (hhol i j).2.continuousOn) hpos
  refine ⟨Metric.ball b₀ ε, _, fun b => ‖κ b‖ ^ 2 * (Real.sqrt (2 ^ g * ((τ b).map Complex.im).det))⁻¹,
    Metric.isOpen_ball, Metric.mem_ball_self hε, hsub, c2, ?_, fun b hb => ⟨?_, ?_⟩⟩
  · refine (hκ.continuousOn.norm.pow 2).mul (ContinuousOn.inv₀ (continuousOn_const.mul c1).sqrt fun b hb => ?_)
    have := (hpos b hb).det_pos
    positivity
  · obtain ⟨Hm, -, -, hH⟩ := (hP'.1 b hb).2.2.2.2
    rw [← (GlobalTheory.RiemannForm.herm_eq_of_normalised E H _ g _ bas _ (h b) (τ b) Hm hbas (hP'.1 b hb) (hn b hb)
      ⟨hsym b hb, hpos b hb⟩ hH).1]
    exact hH
  · exact GlobalTheory.T.meanSquare_multiple_thetaSection_family E H Dw l Xo σ' g ty F k m _ P fr bas b (h b) (τ b) c₁ c₂ _ _ (κ b) hb (hP'.1 b hb) hbas (hdet b hb)
      (hsym b hb) (hpos b hb) (hn b hb) hc₁ hc₂ hfr (hx b (hsub hb)) (hval b hb).1 (hval b hb).2

end GlobalTheory.FrameNorm.Hol

theorem GlobalTheory.FrameNorm.fn_continuousOn_hol : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ (xR : ℝ) (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ), 0 < xR → FnPin U xR fn → ∀ σ, Formalism.L2.PjFree.GoodEmb c σ → ∀ (A : Type) [CommRing A] [Algebra c.F A] (yA : FrPt Xo c A) (m : ℕ) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → (A →ₐ[c.F] CAt σ)) (y : (Fin m → ℂ) → FrPt Xo c (CAt σ)), IsOpen B → (∀ a, DifferentiableOn ℂ (fun b => Formalism.L2.PjFree.toC (φ b a)) B) → (∀ b ∈ B, FrMap (φ b) yA (y b)) → ∀ i, ContinuousOn (fun b => |fn σ (y b) i|) B := by
  intro E _ _ _ H Dw l Xo c r U hU xR fn _ hpin σ hσ A _ _ yA m B φ y hB hφ hy i b₀ hb₀
  obtain ⟨hr, hty, hcov, -, -, g, e, F, ik, ψ, hef, hun⟩ := hU σ hσ
  obtain ⟨B₁, k, P, hB₁, hb₁, hs₁, hP, hyP⟩ := GlobalTheory.T.exists_holomorphic_periods_adapted E H Dw l Xo c σ g e F A yA m B φ y hB hφ hy b₀ hb₀
  obtain ⟨k₀, x₁, t₁, ht₁⟩ := hcov (y b₀)
  obtain ⟨P₁, hP₁, hP₁', hx₁, -⟩ := hun k₀ x₁
  obtain rfl : ik k₀ = k := F.disj _ _ _ _ hP₁' (hP.1 b₀ hb₁) (hx₁.symm.trans (ht₁.1.symm.trans (hyP b₀ hb₁).1))
  obtain ⟨d, hd, horth⟩ := GlobalTheory.T.period_eq_triangular_orthonormal_alt E H Dw l c σ g e _ r ((U σ).X k₀) (ψ k₀) hσ (F.sig _).1 (F.sig _).2 hr
    (hty k₀).1 (hty k₀).2 (hef k₀)
    (GlobalTheory.T.im_neg_of_frame_period_vector E H Dw l c σ g e _ r ((U σ).X k₀) (ψ k₀) hσ hr (hty k₀).1 (hty k₀).2 (hef k₀) x₁.1 x₁.2 P₁ hP₁ hP₁')
  obtain ⟨B₂, Hm, μ, hB₂, hb₂, hs₂, hHm, hμ, hAH⟩ := GlobalTheory.FrameNorm.Hol.exists_continuous_form_mean F (ik k₀)
    ((GlobalTheory.Relab.relab_good E H l c σ hσ).2.2.2 Dw g e) yA φ y P hB₁ (fun a => (hφ a).mono hs₁)
    (fun b hb => hy b (hs₁ hb)) hP (fun b hb => (hyP b hb).1) hb₁
  have key : ∀ b ∈ B₂, ∃ S : Matrix (Fin g) (Fin g) ℂ, (IsUnit S.det ∧
      (∀ j j', S j j' ≠ 0 → (e j).1 = (e j').1 ∧ ((e j).2 : ℕ) ≤ (e j').2) ∧
      Hm b = Sᵀ * ((Matrix.diagonal fun j => ((d j : ℝ) : ℂ)) * S.map (starRingEnd ℂ))) ∧
      (∀ j, |fn σ (y b) (some (e j))| = ‖S j j‖ * Real.sqrt (2 * Real.pi * xR)) ∧
      |fn σ (y b) none| = Real.sqrt (μ b) := by
    intro b hb
    have hp := hP.1 b (hs₂ hb)
    obtain ⟨x₀, hx₀, hunit, S, hS, hsupp, hper, hform⟩ := horth _ hp
    obtain ⟨P₀, hP₀, hP₀', hux, hud, hmean⟩ := hun k₀ ⟨x₀, hx₀⟩
    have hPS : ∀ a, P₀ a = S *ᵥ P b a := fun a => funext fun j => (hP₀ a j).trans (hper a j).symm
    obtain ⟨t, ht, htS⟩ := GlobalTheory.T.triangular_frame_change_of_triangular_period E H Dw l Xo c σ g e F _ (P b) P₀ S (y b) ((U σ).un k₀ ⟨x₀, hx₀⟩) hp hP₀' hPS hsupp
      (hyP b (hs₂ hb)).1 hux (hyP b (hs₂ hb)).2 hud
    have hfn := hpin.1 σ hσ k₀ ⟨x₀, hx₀⟩ hunit t (y b) ht
    refine ⟨S, ⟨hS, hsupp, ?_⟩, fun j => ?_, ?_⟩
    · refine GlobalTheory.UnitDet.eq_of_im_hermForm_eq _ hp.2.2.2.1 _ _ ?_
      rintro _ ⟨v, rfl⟩ _ ⟨w, rfl⟩
      rw [← GlobalTheory.UnitDet.hermForm_mulVec, hform, (hAH b hb).1]
    · rw [hfn, ← htS j]
      rfl
    · obtain ⟨hxx, -, pm, p1, p2, p3⟩ := ht
      have hbc : GlobalTheory.Frames.SecBC (RingHom.id ℂ) (Formalism.L2.PjFree.toC (t none : CAt σ)) ((U σ).un k₀ ⟨x₀, hx₀⟩).x (y b).x
          ((U σ).un k₀ ⟨x₀, hx₀⟩).s (y b).s := ⟨pm, p1, p2.trans (by rw [GlobalTheory.Frames.SecCalc.spMap_id']; exact (Category.comp_id _).symm), p3⟩
      have h1 := GlobalTheory.T.appellHumbertMeanSquare_eq_of_proportional_sections E H Dw l Xo _ g _ F _ P₀ (P b) S _ _ _ _ _ 1 (μ b) hP₀' hp hPS hux hxx hbc (hmean hunit)
        (hAH b hb).2
      rw [hfn, h1, mul_one, Real.sqrt_sq (norm_nonneg _)]
      exact mul_one _
  choose! S hS hlie hgen using key
  refine ContinuousAt.continuousWithinAt (ContinuousOn.continuousAt (s := B₂) ?_ (hB₂.mem_nhds hb₂))
  cases i with
  | none => exact hμ.sqrt.congr hgen
  | some s =>
    obtain ⟨j, rfl⟩ := e.surjective s
    refine ((GlobalTheory.T.continuousOn_norm_diag_of_triangular_factor g (E →+* ℂ) _ (fun j => (e j).1) (fun j => (e j).2) d B₂ S Hm (fun j j' h1 h2 => ?_) hd hHm hS
      j).mul continuousOn_const).congr fun b hb => hlie b hb j
    exact e.injective (Sigma.ext h1 ((Fin.heq_ext_iff (by rw [h1])).2 h2))
end

section

open NumberField Topology ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

theorem _root_.GlobalTheory.T.exists_genericComponentPoints_off_meagre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → ∀ (h : GenFrEx Xo c) (k : U.Comp), ∃ Z : Comp Xo c, ∃ S : ℕ → Set (Frame (U.X k).Ψ r), (∀ n, IsClosed (S n) ∧ interior (S n) = ∅) ∧ ∀ x : (U.X k).dom, (∀ n, x.1 ∉ S n) → ∃ (φ : Om Z →ₐ[c.F] CAt σ) (y' : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ), FrMap φ (genFr h Z) y' ∧ FrBor t (U.un k x) y' := by
  first | exact @GlobalTheory.GenericFrames.exists_comp_generic_off_meagre | exact GlobalTheory.GenericFrames.exists_comp_generic_off_meagre | (intros; apply GlobalTheory.GenericFrames.exists_comp_generic_off_meagre <;> assumption)
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

namespace GlobalTheory.FrameNorm.RecSup

theorem supBdd_and_supR_eq_supN : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j), ∀ (fn : ∀ σ : T.Q.c.F →+* ℂ, FrPt (T.Q.Xo j) T.Q.c (CAt σ) → Ix (T.Q.Dw j) → ℝ), GlobalTheory.FrameNorm.FnPin (fun σ => Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) (xiR D) fn → FnNe (T.Q.Xo j) T.Q.c fn ∧ (∀ (w : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j w), SupBdd (T.Q.Xo j) T.Q.c fn (wtA w) w.n F.1 ∧ ∀ sg, supR (T.Q.Xo j) T.Q.c fn sg (wtA w) w.n F.1 = (recB h.toLawsCore).supN j w sg F) ∧ ∀ (i : ℕ) (η : (recB h.toLawsCore).Cusp j (wEt D j i)), SupRLeRec h j fn i η := by
  intro D T h j hj fn hfn
  have hx : 0 < xiR D := (GlobalTheory.PinNum.xiR_pos_le_one D T.Q h.pins.1).1
  have hU : ∀ σ, Formalism.L2.PjFree.GoodEmb T.Q.c σ →
      Formalism.L2.PjFree.IsUnf (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) := fun σ hσ =>
    (Formalism.L2.PjFree.isUnf_ofPj _).2 (h.unf j hj σ ((Formalism.L2.PjFree.goodEmb_iff σ).1 hσ))
  have hmain : ∀ (w : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j w),
      SupBdd (T.Q.Xo j) T.Q.c fn (wtA w) w.n F.1 ∧
        ∀ sg, supR (T.Q.Xo j) T.Q.c fn sg (wtA w) w.n F.1 = (recB h.toLawsCore).supN j w sg F := by
    intro w F
    have hF : F.1 ∈ Formalism.L2.PjFree.cusp (T.Q.Xo j) T.Q.c (fun σ => Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) (wtA w) w.n :=
      cutR_le T.C j w F.2
    obtain ⟨h1, h2⟩ := GlobalTheory.FrameNorm.SupNorm.supBdd_and_supR_eq _ _ _ _ _ _ _ _ hU _ fn hx hfn _ _ (dom_wtA w) _ hF
    refine ⟨h1, fun sg => (h2 sg).trans ?_⟩
    show _ = cutN T.C T.Ns j w sg F
    unfold cutN
    rw [if_pos hj]
    rfl
  exact ⟨(GlobalTheory.FrameNorm.Comparison₂.ptNorm_eq_pnorm _ _ _ _ _ _ _ _ hU _ fn hx hfn).1, hmain,
    fun i η sg => ((hmain _ η).2 sg).le⟩

end GlobalTheory.FrameNorm.RecSup
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

theorem _root_.GlobalTheory.T.birational_of_formRatios_full_trdeg : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c), ∀ (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF), ((∀ Z : Comp (T.Q.Xo j) T.Q.c, ∃ k₀, evC hG Z ((G.w k₀ : (recB h.toLawsCore).Cusp j wL) : T.R j) ≠ 0 ∧ Algebra.trdeg T.Q.c.F (IntermediateField.adjoin T.Q.c.F (Set.range fun k => evC hG Z ((G.w k : (recB h.toLawsCore).Cusp j wL) : T.R j) / evC hG Z ((G.w k₀ : (recB h.toLawsCore).Cusp j wL) : T.R j))) = WeightFamilies.dimY D j) → BIRSt h j hj hG G) ∧ (BigAt h j hj hG G → BIRSt h j hj hG G) := by
  first | exact @GlobalTheory.Reg.birSt_of_ratios_trdeg | exact GlobalTheory.Reg.birSt_of_ratios_trdeg | (intros; apply GlobalTheory.Reg.birSt_of_ratios_trdeg <;> assumption)
end
