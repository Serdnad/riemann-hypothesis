module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle748
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle790
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle791
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle671
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle495
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle708
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle393
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle411
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle794
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle795
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.ExtremalEpi
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
public import Mathlib.RingTheory.Noetherian.Nilpotent
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.TsupportDbSubset
public import ReciprocityTheory.L2DbarEstimates.Localization.Bundle004
public import ReciprocityTheory.L2DbarEstimates.NormFibrations.Hormander
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle023
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle001
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle788

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh GlobalTheory.AbTan
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Pinch

theorem pinch_main : ∀ (R : Type) [CommRing R] (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M] [Module R M] [IsScalarTower R B M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] (β : TrivSqZeroExt R M →+* TrivSqZeroExt B M), IsSum β (algebraMap R B) id → ∀ (X : Scheme.{0}) (x : Sp R ⟶ X) (z : Sp (TrivSqZeroExt B M) ⟶ X), spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ z = spMap (algebraMap R B) ≫ x → ∃! z₀ : Sp (TrivSqZeroExt R M) ⟶ X, spMap (TrivSqZeroExt.fstHom R R M).toRingHom ≫ z₀ = x ∧ spMap β ≫ z₀ = z := by
  intro R _ B M _ _ _ _ _ _ _ _ _ _ β hβ X x z hxz
  let T := Sp (TrivSqZeroExt R M)
  let i : Sp R ⟶ T := spMap (TrivSqZeroExt.fstHom R R M).toRingHom
  let j : Sp (TrivSqZeroExt B M) ⟶ T := spMap β
  have hcov0 := fun q => exists_basicOpen_inl (M := M) x q
  have EO := GlobalTheory.T.trivSqZeroExt_pinch_exists_extend_basicOpen R B M β hβ X x z hxz
  have UO := GlobalTheory.T.trivSqZeroExt_pinch_basicOpen_morphism_unique R B M β hβ X x
  have RES : ∀ {Y' : Scheme.{0}} (f' : Y' ⟶ T) {V V' : T.Opens} (h : V' ≤ V) (g : V.toScheme ⟶ X) (w : Y' ⟶ X),
      f'.resLE V _ le_rfl ≫ g = (f' ⁻¹ᵁ V).ι ≫ w → f'.resLE V' _ le_rfl ≫ T.homOfLE h ≫ g = (f' ⁻¹ᵁ V').ι ≫ w := by
    intro Y' f' V V' h g w hg
    have e : f'.resLE V' _ le_rfl ≫ T.homOfLE h = Y'.homOfLE (f'.preimage_mono h) ≫ f'.resLE V _ le_rfl := by
      rw [← cancel_mono V.ι]
      simp only [Category.assoc, Scheme.homOfLE_ι, Scheme.Hom.resLE_comp_ι, Scheme.homOfLE_ι_assoc]
    rw [reassoc_of% e, hg, Scheme.homOfLE_ι_assoc]
  let Idx := {p : Γ(T, ⊤) × X.affineOpens // i ⁻¹ᵁ T.basicOpen p.1 ≤ x ⁻¹ᵁ p.2.1}
  have hcov : TopologicalSpace.IsOpenCover (fun p : Idx => T.basicOpen p.1.1) := by
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    intro q _
    obtain ⟨s, U, hq, hle⟩ := hcov0 q
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨(s, U), hle⟩, hq⟩
  let 𝒰 := T.openCoverOfIsOpenCover _ hcov
  choose g hg using fun p : Idx => EO p.1.1 p.1.2 p.2
  have hc : ∀ a b : Idx, pullback.fst (𝒰.f a) (𝒰.f b) ≫ g a = pullback.snd (𝒰.f a) (𝒰.f b) ≫ g b := by
    intro a b
    have hP := AlgebraicGeometry.isPullback_opens_inf (T.basicOpen a.1.1) (T.basicOpen b.1.1)
    change pullback.fst (T.basicOpen a.1.1).ι (T.basicOpen b.1.1).ι ≫ g a =
      pullback.snd (T.basicOpen a.1.1).ι (T.basicOpen b.1.1).ι ≫ g b
    rw [← cancel_epi hP.isoPullback.hom, IsPullback.isoPullback_hom_fst_assoc, IsPullback.isoPullback_hom_snd_assoc]
    refine UO _ (a.1.1 * b.1.1) (T.basicOpen_mul _ _).symm a.1.2 ((i.preimage_mono inf_le_left).trans a.2) _ _
      (RES i _ _ x (hg a).1) (RES i _ _ x (hg b).1) ?_
    rw [RES j _ _ z (hg a).2, RES j _ _ z (hg b).2]
  let z₀ := 𝒰.glueMorphisms g hc
  have hz₀ : ∀ a : Idx, (T.basicOpen a.1.1).ι ≫ z₀ = g a := fun a => 𝒰.ι_glueMorphisms g hc a
  have hi : i ≫ z₀ = x := by
    have hcovR : TopologicalSpace.IsOpenCover (fun p : Idx => i ⁻¹ᵁ T.basicOpen p.1.1) := by
      rw [TopologicalSpace.IsOpenCover, ← Scheme.Hom.preimage_iSup, hcov, Scheme.Hom.preimage_top]
    refine Scheme.Cover.hom_ext ((Sp R).openCoverOfIsOpenCover _ hcovR) _ _ fun a => ?_
    change (i ⁻¹ᵁ T.basicOpen a.1.1).ι ≫ i ≫ z₀ = (i ⁻¹ᵁ T.basicOpen a.1.1).ι ≫ x
    rw [← (hg a).1, ← hz₀ a, ← Category.assoc, ← Scheme.Hom.resLE_comp_ι i (le_rfl), Category.assoc]
  have hj : j ≫ z₀ = z := by
    have hcovA : TopologicalSpace.IsOpenCover (fun p : Idx => j ⁻¹ᵁ T.basicOpen p.1.1) := by
      rw [TopologicalSpace.IsOpenCover, ← Scheme.Hom.preimage_iSup, hcov, Scheme.Hom.preimage_top]
    refine Scheme.Cover.hom_ext ((Sp (TrivSqZeroExt B M)).openCoverOfIsOpenCover _ hcovA) _ _ fun a => ?_
    change (j ⁻¹ᵁ T.basicOpen a.1.1).ι ≫ j ≫ z₀ = (j ⁻¹ᵁ T.basicOpen a.1.1).ι ≫ z
    rw [← (hg a).2, ← hz₀ a, ← Category.assoc, ← Scheme.Hom.resLE_comp_ι j (le_rfl), Category.assoc]
  refine ⟨z₀, ⟨hi, hj⟩, fun z₁ ⟨h1, h2⟩ => ?_⟩
  refine Scheme.Cover.hom_ext 𝒰 _ _ fun a => ?_
  change (T.basicOpen a.1.1).ι ≫ z₁ = (T.basicOpen a.1.1).ι ≫ z₀
  rw [hz₀ a]
  refine UO _ a.1.1 rfl a.1.2 a.2 _ _ ?_ (hg a).1 ?_
  · rw [Scheme.Hom.resLE_comp_ι_assoc, h1]
  · rw [Scheme.Hom.resLE_comp_ι_assoc, h2, (hg a).2]

end GlobalTheory.Pinch
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem twEst_cancel {M : Type} [MeasurableSpace M] (μ : Measure M) (A B W S : M → ℝ≥0∞)
    (hS : Measurable S) (hpt : ∀ x, A x + W x ≤ B x + S x)
    (hBA : ∫⁻ x, B x ∂μ ≤ ∫⁻ x, A x ∂μ) (hB : ∫⁻ x, B x ∂μ ≠ ⊤) :
    ∫⁻ x, W x ∂μ ≤ ∫⁻ x, S x ∂μ := by
  have h1 : ∫⁻ x, A x ∂μ + ∫⁻ x, W x ∂μ ≤ ∫⁻ x, B x ∂μ + ∫⁻ x, S x ∂μ :=
    (le_lintegral_add A W).trans ((lintegral_mono hpt).trans_eq (lintegral_add_right _ hS))
  have h2 : ∫⁻ x, B x ∂μ + ∫⁻ x, W x ∂μ ≤ ∫⁻ x, B x ∂μ + ∫⁻ x, S x ∂μ :=
    (add_le_add hBA le_rfl).trans h1
  exact (ENNReal.add_le_add_iff_left hB).1 h2

theorem twEst_deriv_cut_zero (T : ℝ) (θ : ℝ → ℝ) (hθ : IsCut T θ) (s : ℝ)
    (hs : ¬ (-T - 1 ≤ s ∧ s ≤ -T + 1)) : deriv θ s = 0 := by
  obtain ⟨_, hθ1, hθ0, _, _⟩ := hθ
  rcases not_and_or.1 hs with h | h
  · push_neg at h
    have he : θ =ᶠ[𝓝 s] fun _ => (1 : ℝ) := by
      filter_upwards [Iio_mem_nhds h] with y hy using hθ1 y (le_of_lt hy)
    rw [he.deriv_eq]; simp
  · push_neg at h
    have he : θ =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
      filter_upwards [Ioi_mem_nhds h] with y hy using hθ0 y (le_of_lt hy)
    rw [he.deriv_eq]; simp

theorem twistedExtension_sqInt : ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M], ∀ (X : EtaleStein n M) (φ ψ : M → ℝ) (G : M → ℂ) (Ω : Set M) (δ T : ℝ) (θ : ℝ → ℝ), SmoothR n X.z φ → SmoothR n X.z ψ → (∀ x, ψ x ≤ 0) → 0 < δ → 300 ≤ T → IsCut T θ → (∀ α ∈ Set.Icc (1 : ℝ) (1 + δ), LeviNonneg n X.z (fun x => φ x + α * ψ x)) → IsOpen Ω → Measurable G → (∀ e : OpenPartialHomeomorph M (V n), IsChart n X.z e → DifferentiableOn ℂ (G ∘ e.symm) (e.target ∩ e.symm ⁻¹' Ω)) → (∀ x, δ * ψ x ≤ -T + 1 → x ∈ Ω) → wint n X.z (fun x => (θ (δ * ψ x) : ℂ) * G x) (fun x => φ x + ψ x) < ⊤ → ∃ F : M → ℂ, Holo n X.z F ∧ ∫⁻ x, ENNReal.ofReal (‖(θ (δ * ψ x) : ℂ) * G x - F x‖ ^ 2 * (wT T (δ * ψ x) * Real.exp (-(φ x + ψ x)))) ∂vol n X.z ≤ 30 * ∫⁻ x in {x | -T - 1 ≤ δ * ψ x ∧ δ * ψ x ≤ -T + 1}, ENNReal.ofReal (‖G x‖ ^ 2 * Real.exp (-(φ x + ψ x))) ∂vol n X.z := by
  intro n M _ _ _ _ _ X φ ψ G Ω δ T θ hφ hψ hψ0 hδ hT hθ hlevi hΩ hG hGh hΩsub hint
  have hz := X.isLocalHomeomorph
  obtain ⟨κ, hκ, ⟨C, hC⟩, hκ1, hκ2⟩ := GlobalTheory.T.exists_smooth_log_twist_inequalities T hT
  have hθ' := hθ
  obtain ⟨hθs, hθ1, hθ0, hθb, hθd⟩ := hθ'
  have hδψ : ∀ x, δ * ψ x ≤ 0 := fun x => mul_nonpos_of_nonneg_of_nonpos hδ.le (hψ0 x)
  have hk2 : ∀ x, 0 < deriv (deriv κ) (δ * ψ x) := fun x => (hκ1 _ (hδψ x)).2.2.1
  have h6 := GlobalTheory.T.leviForm_twisted_weight_lower_bound n M X.z φ ψ δ κ hz hφ hψ hψ0 hδ hκ
    (fun t ht => ⟨(hκ1 t ht).1, (hκ1 t ht).2.1⟩) hlevi
  have h7 := GlobalTheory.T.cutoff_holo_smooth_dbar_formula n M X ψ G Ω δ (-T + 1) θ hψ hθs (fun t ht => hθ0 t ht) hΩ hGh hΩsub
  have hψc : Continuous ψ := ReciprocityTheory.L2DbarEstimates.F.smoothReal_continuous n X.z hz ψ hψ
  have hφc : Continuous φ := ReciprocityTheory.L2DbarEstimates.F.smoothReal_continuous n X.z hz φ hφ
  have hψm : Measurable ψ := hψc.measurable
  have hφm : Measurable φ := hφc.measurable
  have hθm : Measurable θ := hθs.continuous.measurable
  have hdθ : Measurable (deriv θ) := measurable_deriv θ
  have hdk : Measurable (deriv (deriv κ)) := measurable_deriv _
  have hdk1 : Measurable (deriv κ) := measurable_deriv _
  have hκm : Measurable κ := hκ.continuous.measurable
  have hLevi : ∀ x ξ, deriv (deriv κ) (δ * ψ x) *
      (δ ^ 2 * ‖dbarDot n X.z (fun y => (ψ y : ℂ)) x ξ‖ ^ 2) ≤
      (Levi n X.z (fun y => (φ y + ψ y) + κ (δ * ψ y)) x ξ).re := fun x ξ => (h6.2 x ξ).2
  have hLnn : ∀ x ξ, 0 ≤ (Levi n X.z (fun y => (φ y + ψ y) + κ (δ * ψ y)) x ξ).re := by
    intro x ξ
    exact le_trans (mul_nonneg (hk2 x).le (by positivity)) (hLevi x ξ)
  obtain ⟨⟨F, hF⟩, hbd⟩ := ReciprocityTheory.L2DbarEstimates.tw n M X (fun x => φ x + ψ x) (fun x => κ (δ * ψ x))
    (fun x => (θ (δ * ψ x) : ℂ) * G x)
    (fun x => deriv θ (δ * ψ x) ^ 2 * ‖G x‖ ^ 2 / deriv (deriv κ) (δ * ψ x))
    (fun x => deriv κ (δ * ψ x) ^ 2 / deriv (deriv κ) (δ * ψ x))
    (SmoothR.add n X.z φ ψ hφ hψ) h6.1 ⟨C, fun x => hC _ (hδψ x)⟩ hLnn h7.1 hint
    (by fun_prop) (by fun_prop)
    (fun x => div_nonneg (by positivity) (hk2 x).le)
    (fun x => div_nonneg (by positivity) (hk2 x).le)
    (fun x => (div_le_one (hk2 x)).2 (hκ1 _ (hδψ x)).2.2.2.1)
    (by
      intro x ξ
      rw [(h7.2 x ξ)]
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc (|deriv θ (δ * ψ x)| * |δ| * ‖G x‖ * ‖dbarDot n X.z (fun y => (ψ y : ℂ)) x ξ‖) ^ 2
          = deriv θ (δ * ψ x) ^ 2 * ‖G x‖ ^ 2 / deriv (deriv κ) (δ * ψ x) *
            (deriv (deriv κ) (δ * ψ x) *
              (δ ^ 2 * ‖dbarDot n X.z (fun y => (ψ y : ℂ)) x ξ‖ ^ 2)) := by
            simp only [mul_pow, sq_abs]
            field_simp [(hk2 x).ne']
        _ ≤ _ := mul_le_mul_of_nonneg_left (hLevi x ξ) (div_nonneg (by positivity) (hk2 x).le))
    (by
      intro x ξ
      rw [(h6.2 x ξ).1]
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc (|deriv κ (δ * ψ x)| * |δ| * ‖dbarDot n X.z (fun y => (ψ y : ℂ)) x ξ‖) ^ 2
          = deriv κ (δ * ψ x) ^ 2 / deriv (deriv κ) (δ * ψ x) *
            (deriv (deriv κ) (δ * ψ x) *
              (δ ^ 2 * ‖dbarDot n X.z (fun y => (ψ y : ℂ)) x ξ‖ ^ 2)) := by
            simp only [mul_pow, sq_abs]
            field_simp [(hk2 x).ne']
        _ ≤ _ := mul_le_mul_of_nonneg_left (hLevi x ξ) (div_nonneg (by positivity) (hk2 x).le))
  refine ⟨F, hF.1, ?_⟩
  have hB := hbd F hF
  beta_reduce at hB
  have hsh : MeasurableSet {x | -T - 1 ≤ δ * ψ x ∧ δ * ψ x ≤ -T + 1} := by
    have h1 : Measurable (fun x => δ * ψ x) := by fun_prop
    exact (measurableSet_le measurable_const h1).inter (measurableSet_le h1 measurable_const)
  have hw : ∀ s, 0 ≤ wT T s := fun s => by unfold wT; positivity
  have hfin : ∫⁻ x, ENNReal.ofReal (‖(θ (δ * ψ x) : ℂ) * G x - F x‖ ^ 2 *
      Real.exp (κ (δ * ψ x) - (φ x + ψ x))) ∂vol n X.z ≠ ⊤ := by
    have hF0 : ∫⁻ x, ENNReal.ofReal (‖(θ (δ * ψ x) : ℂ) * G x‖ ^ 2 *
        Real.exp (-(φ x + ψ x))) ∂vol n X.z < ⊤ := hint
    have hF1 : ∫⁻ x, ENNReal.ofReal (‖F x‖ ^ 2 * Real.exp (-(φ x + ψ x))) ∂vol n X.z < ⊤ :=
      hF.2.1
    refine ne_of_lt (lt_of_le_of_lt (lintegral_mono (g := fun x =>
      ENNReal.ofReal (2 * Real.exp C) *
        (ENNReal.ofReal (‖(θ (δ * ψ x) : ℂ) * G x‖ ^ 2 * Real.exp (-(φ x + ψ x))) +
          ENNReal.ofReal (‖F x‖ ^ 2 * Real.exp (-(φ x + ψ x))))) ?_) ?_)
    · intro x
      beta_reduce
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have hu : ‖(θ (δ * ψ x) : ℂ) * G x - F x‖ ^ 2 ≤
          2 * (‖(θ (δ * ψ x) : ℂ) * G x‖ ^ 2 + ‖F x‖ ^ 2) := by
        have h0 := norm_sub_le ((θ (δ * ψ x) : ℂ) * G x) (F x)
        have h1 := pow_le_pow_left₀ (norm_nonneg _) h0 2
        nlinarith [sq_nonneg (‖(θ (δ * ψ x) : ℂ) * G x‖ - ‖F x‖)]
      have hk : Real.exp (κ (δ * ψ x)) ≤ Real.exp C :=
        Real.exp_le_exp.2 (le_trans (le_abs_self _) (hC _ (hδψ x)))
      have he : Real.exp (κ (δ * ψ x) - (φ x + ψ x)) =
          Real.exp (κ (δ * ψ x)) * Real.exp (-(φ x + ψ x)) := by
        rw [sub_eq_add_neg, Real.exp_add]
      rw [he]
      have hpos := Real.exp_pos (-(φ x + ψ x))
      calc ‖(θ (δ * ψ x) : ℂ) * G x - F x‖ ^ 2 *
            (Real.exp (κ (δ * ψ x)) * Real.exp (-(φ x + ψ x)))
          ≤ (2 * (‖(θ (δ * ψ x) : ℂ) * G x‖ ^ 2 + ‖F x‖ ^ 2)) *
            (Real.exp C * Real.exp (-(φ x + ψ x))) :=
            mul_le_mul hu (mul_le_mul_of_nonneg_right hk hpos.le) (by positivity) (by positivity)
        _ = _ := by ring
    · rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left (by fun_prop)]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.2 ⟨hF0, hF1⟩)
  have hcan := twEst_cancel (vol n X.z)
    (fun x => ENNReal.ofReal ((Real.sqrt (deriv θ (δ * ψ x) ^ 2 * ‖G x‖ ^ 2 /
        deriv (deriv κ) (δ * ψ x)) + ‖(θ (δ * ψ x) : ℂ) * G x - F x‖ *
        Real.sqrt (deriv κ (δ * ψ x) ^ 2 / deriv (deriv κ) (δ * ψ x))) ^ 2 *
        Real.exp (κ (δ * ψ x) - (φ x + ψ x))))
    (fun x => ENNReal.ofReal (‖(θ (δ * ψ x) : ℂ) * G x - F x‖ ^ 2 *
        Real.exp (κ (δ * ψ x) - (φ x + ψ x))))
    (fun x => ENNReal.ofReal (‖(θ (δ * ψ x) : ℂ) * G x - F x‖ ^ 2 * (wT T (δ * ψ x) / 8) *
        Real.exp (-(φ x + ψ x))))
    (Set.indicator {x | -T - 1 ≤ δ * ψ x ∧ δ * ψ x ≤ -T + 1}
      (fun x => ENNReal.ofReal (15 / 4 * (‖G x‖ ^ 2 * Real.exp (-(φ x + ψ x))))))
    ((by fun_prop : Measurable (fun x =>
      ENNReal.ofReal (15 / 4 * (‖G x‖ ^ 2 * Real.exp (-(φ x + ψ x)))))).indicator hsh)
    (by
      intro x
      beta_reduce
      have h8 := GlobalTheory.T.sq_sqrt_add_mul_le_of_twisted_absorption T (δ * ψ x) ‖(θ (δ * ψ x) : ℂ) * G x - F x‖ ‖G x‖
        (deriv θ (δ * ψ x)) (deriv κ (δ * ψ x)) (deriv (deriv κ) (δ * ψ x))
        (Real.exp (κ (δ * ψ x))) (norm_nonneg _) (norm_nonneg _) (hk2 x) (Real.exp_pos _)
        (hθd _) (hκ1 _ (hδψ x)).2.2.2.2 (fun h => hκ2 _ h.1 h.2)
        (fun h => twEst_deriv_cut_zero T θ hθ _ h)
      have he : Real.exp (κ (δ * ψ x) - (φ x + ψ x)) =
          Real.exp (κ (δ * ψ x)) * Real.exp (-(φ x + ψ x)) := by
        rw [sub_eq_add_neg, Real.exp_add]
      have hp := Real.exp_pos (-(φ x + ψ x))
      have hreal := mul_le_mul_of_nonneg_right h8 hp.le
      have hwx := hw (δ * ψ x)
      rw [he]
      by_cases hx : -T - 1 ≤ δ * ψ x ∧ δ * ψ x ≤ -T + 1
      · rw [Set.indicator_of_mem (show x ∈ {x | -T - 1 ≤ δ * ψ x ∧ δ * ψ x ≤ -T + 1} from hx),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        rw [if_pos hx] at hreal
        linear_combination hreal
      · rw [Set.indicator_of_notMem (show x ∉ {x | -T - 1 ≤ δ * ψ x ∧ δ * ψ x ≤ -T + 1} from hx),
          ← ENNReal.ofReal_add (by positivity) (by positivity), add_zero]
        apply ENNReal.ofReal_le_ofReal
        rw [if_neg hx] at hreal
        linear_combination hreal)
    hB hfin
  have hLHS : ∫⁻ x, ENNReal.ofReal (‖(θ (δ * ψ x) : ℂ) * G x - F x‖ ^ 2 *
      (wT T (δ * ψ x) * Real.exp (-(φ x + ψ x)))) ∂vol n X.z =
      ENNReal.ofReal 8 * ∫⁻ x, ENNReal.ofReal (‖(θ (δ * ψ x) : ℂ) * G x - F x‖ ^ 2 *
        (wT T (δ * ψ x) / 8) * Real.exp (-(φ x + ψ x))) ∂vol n X.z := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr (fun x => ?_)
    rw [← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    ring
  have hRHS : ∫⁻ x, Set.indicator {x | -T - 1 ≤ δ * ψ x ∧ δ * ψ x ≤ -T + 1}
      (fun x => ENNReal.ofReal (15 / 4 * (‖G x‖ ^ 2 * Real.exp (-(φ x + ψ x))))) x ∂vol n X.z =
      ENNReal.ofReal (15 / 4) * ∫⁻ x in {x | -T - 1 ≤ δ * ψ x ∧ δ * ψ x ≤ -T + 1},
        ENNReal.ofReal (‖G x‖ ^ 2 * Real.exp (-(φ x + ψ x))) ∂vol n X.z := by
    rw [lintegral_indicator hsh, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr (fun x => ?_)
    rw [ENNReal.ofReal_mul (by norm_num)]
  rw [hLHS]
  calc ENNReal.ofReal 8 * ∫⁻ x, ENNReal.ofReal (‖(θ (δ * ψ x) : ℂ) * G x - F x‖ ^ 2 *
        (wT T (δ * ψ x) / 8) * Real.exp (-(φ x + ψ x))) ∂vol n X.z
      ≤ ENNReal.ofReal 8 * ∫⁻ x, Set.indicator {x | -T - 1 ≤ δ * ψ x ∧ δ * ψ x ≤ -T + 1}
        (fun x => ENNReal.ofReal (15 / 4 * (‖G x‖ ^ 2 * Real.exp (-(φ x + ψ x))))) x
          ∂vol n X.z := by gcongr
    _ = _ := by
      rw [hRHS, ← mul_assoc, ← ENNReal.ofReal_mul (by norm_num)]
      norm_num

end GlobalTheory
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.PDivGroup

theorem surjective_of_cotangentPullback_surjective_nilAug {k A B : Type} [Field k] [CommRing A] [CommRing B]
    [Bialgebra k A] [Bialgebra k B] [Module.Finite k A] (f : B →ₐc[k] A)
    (hA : ∀ a ∈ augIdeal k A, IsNilpotent a) (hf : Function.Surjective (cotMap f)) :
    Function.Surjective f := by
  set I := augIdeal k A with hIdef
  set J := augIdeal k B with hJdef
  have hfJ : ∀ b ∈ J, f b ∈ I := by
    intro b hb
    have hb' : counit (R := k) b = 0 := hb
    show counit (R := k) (f b) = 0
    rw [CoalgHomClass.counit_comp_apply]; exact hb'

  have step1 : ∀ x ∈ I, ∃ b ∈ J, x - f b ∈ I ^ 2 := by
    intro x hx
    obtain ⟨c, hc⟩ := hf (AugCot.d (counitAlgHom k A) x)
    obtain ⟨b0, rfl⟩ := AugCot.d_surjective _ c
    rw [cotMap_d] at hc
    set b := b0 - algebraMap k B (counit b0) with hb
    have hbJ : b ∈ J := by
      show counit (R := k) b = 0
      simp [hb]
    have hdb : AugCot.d (counitAlgHom k A) (f b) = AugCot.d (counitAlgHom k A) (f b0) := by
      rw [hb, map_sub, AlgHomClass.commutes, map_sub, AugCot.d_algebraMap, sub_zero]
    refine ⟨b, hbJ, ?_⟩
    have h1 : AugCot.d (counitAlgHom k A) (x - f b) = 0 := by
      rw [map_sub, hdb, ← hc, sub_self]
    have hmem : x - f b ∈ I := I.sub_mem hx (hfJ b hbJ)
    rw [AugCot.d_of_mem _ hmem, Ideal.toCotangent_eq_zero] at h1
    exact h1

  have step2 : ∀ m : ℕ, ∀ y ∈ I ^ (m + 1), ∃ b ∈ J ^ (m + 1), y - f b ∈ I ^ (m + 2) := by
    intro m
    induction m with
    | zero =>
      intro y hy
      rw [zero_add, pow_one] at hy
      obtain ⟨b, hb, h⟩ := step1 y hy
      exact ⟨b, by rwa [zero_add, pow_one], h⟩
    | succ m ih =>
      intro y hy
      rw [pow_succ'] at hy
      refine Submodule.mul_induction_on hy ?_ ?_
      · intro x hx z hz
        obtain ⟨b1, hb1, hu⟩ := step1 x hx
        obtain ⟨b2, hb2, hv⟩ := ih z hz
        have hfb1 : f b1 ∈ I := hfJ b1 hb1
        have hfb2 : f b2 ∈ I ^ (m + 1) := by
          have : f b2 = z - (z - f b2) := by ring
          rw [this]
          exact (I ^ (m + 1)).sub_mem hz (Ideal.pow_le_pow_right (by omega) hv)
        refine ⟨b1 * b2, ?_, ?_⟩
        · rw [pow_succ']; exact Ideal.mul_mem_mul hb1 hb2
        · set u := x - f b1
          set v := z - f b2
          have hx' : x = f b1 + u := by simp [u]
          have hz' : z = f b2 + v := by simp [v]
          have : x * z - f (b1 * b2) = f b1 * v + u * f b2 + u * v := by
            rw [hx', hz', map_mul]; ring
          rw [this]
          refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_
          · rw [show m + 1 + 2 = 1 + (m + 2) by omega, pow_add, pow_one]
            exact Ideal.mul_mem_mul hfb1 hv
          · rw [show m + 1 + 2 = 2 + (m + 1) by omega, pow_add]
            exact Ideal.mul_mem_mul hu hfb2
          · rw [show m + 1 + 2 = 1 + (m + 2) by omega, pow_add, pow_one]
            exact Ideal.mul_mem_mul (Ideal.pow_le_self (by norm_num) hu) hv
      · rintro y1 y2 ⟨b1, hb1, h1⟩ ⟨b2, hb2, h2⟩
        refine ⟨b1 + b2, Ideal.add_mem _ hb1 hb2, ?_⟩
        have : y1 + y2 - f (b1 + b2) = (y1 - f b1) + (y2 - f b2) := by rw [map_add (f := _)]; ring
        rw [this]; exact Ideal.add_mem _ h1 h2
  have step3 : ∀ m : ℕ, ∀ x ∈ I, ∃ b : B, x - f b ∈ I ^ (m + 1) := by
    intro m
    induction m with
    | zero => intro x hx; exact ⟨0, by rw [map_zero, sub_zero, zero_add, pow_one]; exact hx⟩
    | succ m ih =>
      intro x hx
      obtain ⟨b, hb⟩ := ih x hx
      obtain ⟨b', -, hb'⟩ := step2 m _ hb
      refine ⟨b + b', ?_⟩
      have : x - f (b + b') = x - f b - f b' := by rw [map_add (f := _)]; ring
      rw [this]; exact hb'

  haveI : IsNoetherianRing A := IsNoetherianRing.of_finite k A
  have hnil : IsNilpotent I := by
    refine (Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian I)).2 ?_
    intro a ha
    exact (mem_nilradical).2 (hA a ha)
  obtain ⟨N, hN⟩ := hnil
  have hI : ∀ x ∈ I, ∃ b : B, f b = x := by
    intro x hx
    obtain ⟨b, hb⟩ := step3 N x hx
    have : x - f b ∈ I ^ N := Ideal.pow_le_pow_right (by omega) hb
    rw [hN] at this
    exact ⟨b, (sub_eq_zero.1 ((Submodule.mem_bot _).1 this)).symm⟩
  intro a
  have ha : a - algebraMap k A (counit a) ∈ I := by
    show counit (R := k) (a - algebraMap k A (counit a)) = 0
    simp
  obtain ⟨b, hb⟩ := hI _ ha
  refine ⟨b + algebraMap k B (counit a), ?_⟩
  rw [map_add (f := _), AlgHomClass.commutes, hb, sub_add_cancel]

theorem app_surjective_of_omegaMap_surjective : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (G H : PDivGroup p k) (q : G ⟶ H), G.IsConn → Function.Surjective (omegaMap G H q) → ∀ n, Function.Surjective (q.app n) := by
  intro p _ k _ _ G H q hG hq n
  refine surjective_of_cotangentPullback_surjective_nilAug (q.app n) (hG n) fun w => ?_
  obtain ⟨v, rfl⟩ := G.omegaLevel_surjective n w
  obtain ⟨u, rfl⟩ := hq v
  exact ⟨u.1 n, rfl⟩

end GlobalTheory.PDivGroup
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.isLatticeQuotientCorrespondence_of_torsionTransport : ∀ (K : Type) [Field K] [NumberField K] (ι : K →+* ℂ) (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), TorsTransport ι g t Λ₀ Λ₁ Ω₀ Ω₁ → IsTr ι Λ₀ Λ₁ (Tr t) := by
  first | exact @GlobalTheory.WpFam.TrIs.main | exact GlobalTheory.WpFam.TrIs.main | (intros; apply GlobalTheory.WpFam.TrIs.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.ringActionOnGroupScheme_intCombination_eq_prod_zpow : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (O : Type) [Ring O] (act : O → (A ⟶ A)), IsRAct A act → ∀ (r : ℕ) (e : Fin r → O) (c : Fin r → ℤ), act (∑ k, c k • e k) = ∏ k, act (e k) ^ c k := by
  first | (exact @GlobalTheory.ActSum.act_sum_zsmul) | (exact GlobalTheory.ActSum.act_sum_zsmul) | (intros; apply GlobalTheory.ActSum.act_sum_zsmul  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.groupScheme_ringAction_iff_endomorphism_relations : ∀ (O : Type) [Ring O] (r : ℕ) (e : Fin r → O), Submodule.span ℤ (Set.range e) = ⊤ → ∃ (m : ℕ) (N : Fin m → Fin r → ℤ) (c1 : Fin r → ℤ) (cm : Fin r → Fin r → Fin r → ℤ), ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (f : Fin r → (A ⟶ A)), (∀ k, IsMonHom (f k)) → ((∃ act : O → (A ⟶ A), IsRAct A act ∧ ∀ k, act (e k) = f k) ↔ ((∀ j, ∏ k, f k ^ N j k = 1) ∧ ∏ k, f k ^ c1 k = 𝟙 A ∧ ∀ i j, f i ≫ f j = ∏ k, f k ^ cm i j k)) := by
  first | exact @GlobalTheory.ActRel.ringAct_iff_relations | exact GlobalTheory.ActRel.ringAct_iff_relations | (intros; apply GlobalTheory.ActRel.ringAct_iff_relations <;> assumption)
end
