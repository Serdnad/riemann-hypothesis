module

public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle073
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1868
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfCoefficientsSeparatingCharactersEqZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalSymplecticPointsSelfAnnihilator
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle336
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Dimension.Basic
public import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaFixedProd

theorem setIntegral_add_right {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] (Γ : AddSubgroup G) [Countable Γ]
    (μ : Measure G) [μ.IsAddHaarMeasure] {𝓕 : Set G} (h𝓕 : IsAddFundamentalDomain Γ 𝓕 μ) (h : G → ℂ)
    (hper : ∀ γ ∈ Γ, ∀ x, h (γ + x) = h x) (l : G) :
    ∫ x in 𝓕, h (x + l) ∂μ = ∫ x in 𝓕, h x ∂μ := by
  have hs : IsAddFundamentalDomain Γ ((fun x => x - l) ⁻¹' 𝓕) μ :=
    h𝓕.preimage_of_equiv (measurePreserving_sub_right μ l).quasiMeasurePreserving (e := id) Function.bijective_id
      (fun g x => by
        show (g +ᵥ x) - l = g +ᵥ (x - l)
        simp only [AddSubgroup.vadd_def, vadd_eq_add]
        abel)
  have e1 : ∫ x in 𝓕, h (x + l) ∂μ = ∫ y in (fun x => x - l) ⁻¹' 𝓕, h y ∂μ := by
    rw [← (measurePreserving_add_right μ l).setIntegral_preimage_emb (measurableEmbedding_addRight l) h]
    congr 2
    ext x
    simp
  rw [e1]
  exact hs.setIntegral_eq h𝓕 fun g x => hper g g.2 x

theorem prod_eq_of_fixed : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ (N : AddSubgroup (WO S T)) (M : Module.End ℂ (WO S T → ℂ)), (∀ f, IsThetaFunO ψ S T f → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f) → IsThetaFunO ψ S T (M f) ∧ ∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u (M f) = M f) → (∀ w f, IsThetaFunO ψ S T f → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f) → (∀ l ∈ N, l.map (infPart D) = 0 → ψ (symplO S T w l) = 1) → M (heisO ψ S T w f) = heisO ψ S T w (M f)) → (∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∀ f, IsThetaFunO ψ S T f → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f) → ∫⁻ w in 𝓕, ‖M f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ) → ∀ f g, IsThetaFunO ψ S T f → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f) → IsThetaFunO ψ S T g → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u g = g) → ∀ x, M f x * star (M g x) = f x * star (g x) := by
  intro D ψ S T hψ N M hMV hc hn f g hf hfN hg hgN x
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : Countable (ratL T S) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  obtain ⟨μ, 𝓕, hμ, h𝓕, -⟩ :=
    (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WO S T) (ratL T S) K hK hKc).1
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (G := WO S T) (ratL T S) hK hKc μ h𝓕⟩
  obtain ⟨l1, l2, -, l4, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D S T
  have hth := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1
  have hcomp := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).2.1
  let Θ : Submodule ℂ (WO S T → ℂ) :=
    { carrier := {f | IsThetaFunO ψ S T f ∧ ∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f}
      add_mem' := fun {a b} ha hb => ⟨GlobalTheory.WeilVacMove.isTheta_add ha.1 hb.1, fun u hu h0 => by
        funext w
        have e1 := congrFun (ha.2 u hu h0) w
        have e2 := congrFun (hb.2 u hu h0) w
        simp only [heisO, Pi.add_apply] at e1 e2 ⊢
        rw [mul_add, e1, e2]⟩
      zero_mem' := ⟨GlobalTheory.WeilVacMove.isTheta_zero, fun u _ _ => by funext w; simp [heisO]⟩
      smul_mem' := fun c a ha => ⟨GlobalTheory.WeilVacMove.isTheta_smul c ha.1, fun u hu h0 => by
        funext w
        have e1 := congrFun (ha.2 u hu h0) w
        simp only [heisO, Pi.smul_apply, smul_eq_mul] at e1 ⊢
        rw [mul_left_comm, e1]⟩ }
  have hb : ∀ a ∈ Θ, ∃ C : ℝ, ∀ w, ‖a w‖ ≤ C := fun a ha => by
    have hp : ∀ γ ∈ ratL T S, ∀ w, ‖a (γ + w)‖ = ‖a w‖ := by
      rintro _ ⟨γ, rfl⟩ w
      exact (congrArg norm (ha.1.quasi γ w)).trans (by rw [norm_mul, hψ.1.2.1, one_mul])
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn ha.1.cont.continuousOn
    refine ⟨C, fun w => ?_⟩
    obtain ⟨γ, hγ, h⟩ := hKc w
    rw [← hp γ hγ w]
    exact hC _ h
  have hMΘ : ∀ a ∈ Θ, M a ∈ Θ := fun a ha => hMV a ha.1 ha.2
  have hpol : ∀ a a', a ∈ Θ → a' ∈ Θ → ∫ w in 𝓕, M a w * star (M a' w) ∂μ = ∫ w in 𝓕, a w * star (a' w) ∂μ :=
    fun a a' ha ha' => GlobalTheory.Mem.LiftPolar.integral_mul_star_eq (μ.restrict 𝓕) Θ (fun b hb => hb.1.cont.measurable) hb M
      hMΘ (fun b hb => hn μ 𝓕 hμ h𝓕 b hb.1 hb.2) a a' ha ha'
  have hint : ∀ a a', IsThetaFunO ψ S T a → IsThetaFunO ψ S T a' →
      Integrable (fun w => a w * star (a' w)) (μ.restrict 𝓕) := fun a a' ha ha' => by
    have hcont : Continuous fun w => a w * star (a' w) := ha.cont.mul ha'.cont.star
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
    refine Integrable.of_bound hcont.aestronglyMeasurable C (Filter.Eventually.of_forall fun w => ?_)
    obtain ⟨γ, hγ, h⟩ := hKc w
    rw [← GlobalTheory.ThetaSchur.prod_periodic hψ ha ha' hγ w]
    exact hC _ h
  have hfix : ∀ a a', a ∈ Θ → a' ∈ Θ → ∀ l ∈ N, l.map (infPart D) = 0 → ∀ w,
      a (w + l) * star (a' (w + l)) = a w * star (a' w) := fun a a' ha ha' l hl h0 w => by
    have e1 := congrFun (ha.2 l hl h0) w
    have e2 := congrFun (ha'.2 l hl h0) w
    simp only [heisO] at e1 e2
    rw [← e1, ← e2, star_mul']
    linear_combination -(a (w + l) * star (a' (w + l))) * GlobalTheory.ThetaSchur.mul_star_psi hψ (symplOH S T w l)
  have hfΘ : f ∈ Θ := ⟨hf, hfN⟩
  have hgΘ : g ∈ Θ := ⟨hg, hgN⟩
  have hadd : ∀ y z γ : WO S T, ψ (symplO S T (y + z) γ) = ψ (symplO S T y γ) * ψ (symplO S T z γ) := fun y z γ => by
    simp only [← l4, l1, AddChar.map_add_eq_mul]
    ring
  have key := GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero (WO S T) (ratL T S) K hK hKc (ratL T S)
    (fun γ x => ψ (symplO S T x γ))
    (fun γ => by
      have : Continuous fun x : WO S T => symplOH S T x (γ : WO S T) :=
        GlobalTheory.WeilVacMove.continuous_symplOH S T continuous_id' continuous_const
      simp only [← l4]
      exact hψ.1.1.comp (this.add this))
    (fun γ x y => hadd x y γ)
    (fun γ γ' x => by
      simp only [← l4, AddSubgroup.coe_add, l2, AddChar.map_add_eq_mul]
      ring)
    (fun x => by
      simp only [← l4, AddSubgroup.coe_zero, GlobalTheory.WeilVacMove.symplOH_zero_right, add_zero, AddChar.map_zero_eq_one])
    (fun γ x => hψ.1.2.1 _)
    (fun x => by
      rw [← GlobalTheory.RatAnnih.ratL_annihilator D ψ hψ S T x]
      exact ⟨fun h γ hγ => h ⟨γ, hγ⟩, fun h γ => h γ γ.2⟩)
    μ 𝓕 hμ h𝓕 (fun x => M f x * star (M g x) - f x * star (g x))
    (((hMΘ f hfΘ).1.cont.mul (hMΘ g hgΘ).1.cont.star).sub (hf.cont.mul hg.cont.star))
    (fun γ hγ x => by
      rw [GlobalTheory.ThetaSchur.prod_periodic hψ hf hg hγ,
        GlobalTheory.ThetaSchur.prod_periodic hψ (hMΘ f hfΘ).1 (hMΘ g hgΘ).1 hγ])
    (fun γ => by
      show ∫ x in 𝓕, ψ (symplO S T x γ) * (M f x * star (M g x) - f x * star (g x)) ∂μ = 0
      by_cases hγ : ∀ l ∈ N, l.map (infPart D) = 0 → ψ (symplO S T (γ : WO S T) l) = 1
      · have hγf : heisO ψ S T γ f ∈ Θ := ⟨hth _ f hf, fun u hu h0 => by
          funext w
          have a1 := congrFun (hcomp u γ f) w
          have a2 := congrFun (hcomp γ u f) w
          rw [hfN u hu h0, add_comm (γ : WO S T) u] at a2
          simp only [Pi.smul_apply, smul_eq_mul] at a1 a2
          rw [a1, a2]
          congr 1
          have h1 := hγ u hu h0
          rw [← l4, AddChar.map_add_eq_mul] at h1
          rw [GlobalTheory.WeilVacMove.symplOH_skew S T (γ : WO S T) u]
          have h2 : ψ (-symplOH S T (γ : WO S T) u) * ψ (symplOH S T (γ : WO S T) u) = 1 := by
            rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
          linear_combination (-ψ (-symplOH S T (γ : WO S T) u)) * h1 + ψ (symplOH S T (γ : WO S T) u) * h2⟩
        have e : (fun x => ψ (symplO S T x γ) * (M f x * star (M g x) - f x * star (g x))) = fun x =>
            M (heisO ψ S T γ f) x * star (M g x) - heisO ψ S T γ f x * star (g x) := by
          funext x
          rw [hc _ f hf hfN hγ, GlobalTheory.ThetaSchur.heisO_rat hf γ.2, GlobalTheory.ThetaSchur.heisO_rat (hMΘ f hfΘ).1 γ.2]
          ring
        rw [e, integral_sub (hint _ _ (hMΘ _ hγf).1 (hMΘ g hgΘ).1) (hint _ _ hγf.1 hg), hpol _ _ hγf hgΘ, sub_self]
      · push_neg at hγ
        obtain ⟨l, hl, h0, hne⟩ := hγ
        have hper : ∀ δ ∈ ratL T S, ∀ x, (fun x => ψ (symplO S T x γ) * (M f x * star (M g x) - f x * star (g x)))
            (δ + x) = (fun x => ψ (symplO S T x γ) * (M f x * star (M g x) - f x * star (g x))) x := by
          intro δ hδ x
          simp only
          rw [hadd, (GlobalTheory.RatAnnih.ratL_annihilator D ψ hψ S T δ).2 hδ γ γ.2, one_mul,
            GlobalTheory.ThetaSchur.prod_periodic hψ hf hg hδ,
            GlobalTheory.ThetaSchur.prod_periodic hψ (hMΘ f hfΘ).1 (hMΘ g hgΘ).1 hδ]
        have htr := GlobalTheory.ThetaFixedProd.setIntegral_add_right (G := WO S T) (ratL T S) μ h𝓕
          (fun x => ψ (symplO S T x γ) * (M f x * star (M g x) - f x * star (g x))) hper l
        simp only [hadd, hfix _ _ (hMΘ f hfΘ) (hMΘ g hgΘ) l hl h0, hfix _ _ hfΘ hgΘ l hl h0] at htr
        have hsk : symplO S T l γ = -symplO S T (γ : WO S T) l := by
          rw [← l4, ← l4, GlobalTheory.WeilVacMove.symplOH_skew S T (γ : WO S T) l]
          abel
        have hc1 : ψ (symplO S T l γ) ≠ 1 := fun h1 => by
          apply hne
          rw [hsk] at h1
          have h2 : ψ (symplO S T (γ : WO S T) l) * ψ (-symplO S T (γ : WO S T) l) = 1 := by
            rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
          rw [h1, mul_one] at h2
          exact h2
        have e2 : (fun x => ψ (symplO S T x γ) * ψ (symplO S T l γ) * (M f x * star (M g x) - f x * star (g x))) =
            fun x => ψ (symplO S T l γ) * (ψ (symplO S T x γ) * (M f x * star (M g x) - f x * star (g x))) := by
          funext x
          ring
        rw [e2, integral_const_mul] at htr
        have h3 : (ψ (symplO S T l γ) - 1) *
            ∫ x in 𝓕, ψ (symplO S T x γ) * (M f x * star (M g x) - f x * star (g x)) ∂μ = 0 := by
          linear_combination htr
        exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hc1))
  exact sub_eq_zero.1 (congrFun key x)

end GlobalTheory.ThetaFixedProd

end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaMove

open GlobalTheory.SplitHecke

variable {D : D7} {S T : HSp D}

theorem act_add (g : GA D S) (h : GA D T) (x y : WO S T) :
    actO S T g h (x + y) = actO S T g h x + actO S T g h y := map_add (actAdd S T g h) x y

theorem act_nsmul (g : GA D S) (h : GA D T) (k : ℕ) (x : WO S T) :
    actO S T g h (k • x) = k • actO S T g h x := map_nsmul (actAdd S T g h) k x

theorem act_act_inv (g : GA D S) (h : GA D T) (u : WO S T) : actO S T g h (actO S T g⁻¹ h⁻¹ u) = u := by
  have := actO_inv_actO g⁻¹ h⁻¹ u
  rwa [inv_inv, inv_inv] at this

theorem isHalf_of_act {e : AE D} (g : GA D S) (h : GA D T) {u : WO S T} (hu : IsHalf e (actO S T g h u)) :
    IsHalf e u := by
  have := isHalf_actO g⁻¹ h⁻¹ hu
  rwa [actO_inv_actO] at this

theorem isSBHalf_comp {e : AE D} {Λ : AddSubgroup (WO S T)} (g : GA D S) (h : GA D T)
    (hΛ : ∀ u, u ∈ Λ ↔ actO S T g h u ∈ Λ) {Ψ : WO S T → ℂ} (hΨ : IsSBHalf e Λ Ψ) :
    IsSBHalf e Λ fun t => Ψ (actO S T g h t) := by
  obtain ⟨h1, k, hk, h2, h3⟩ := hΨ
  refine ⟨fun t ht => isHalf_of_act g h (h1 _ ht), k, hk, fun u hu hu' t => ?_, fun t ht => ?_⟩
  · show Ψ _ = Ψ _
    rw [act_add, act_nsmul]
    exact h2 _ ((hΛ u).1 hu) (isHalf_actO g h hu') _
  · rw [hΛ, act_nsmul]
    exact h3 _ ht

theorem halfInd_act {e : AE D} {Λ : AddSubgroup (WO S T)} (g : GA D S) (h : GA D T)
    (hΛ : ∀ u, u ∈ Λ ↔ actO S T g h u ∈ Λ) (t : WO S T) :
    halfInd e Λ (actO S T g h t) = halfInd e Λ t := by
  unfold halfInd
  have : (actO S T g h t ∈ Λ ∧ IsHalf e (actO S T g h t)) ↔ (t ∈ Λ ∧ IsHalf e t) :=
    and_congr (hΛ t).symm ⟨isHalf_of_act g h, isHalf_actO g h⟩
  by_cases ht : t ∈ Λ ∧ IsHalf e t
  · rw [if_pos ht, if_pos (this.2 ht)]
  · rw [if_neg ht, if_neg (fun hh => ht (this.1 hh))]

theorem heisO_smul' (ψ : AddChar (AF D.host.F) ℂ) (w : WO S T) (c : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T w (c • f) = c • heisO ψ S T w f := by
  funext t
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem om_theta_eq_smul : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (e : AE D) (Λ : AddSubgroup (WO S T)) (f₀ Φ f : WO S T → ℂ), (∀ Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ), IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Tm → ∀ Ψ, IsSBHalf e Λ Ψ → IsThetaFunO ψ S T (Tm Ψ)) → IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Φ f → ∀ (g : GA D S) (h : GA D T), (∀ u, u ∈ Λ ↔ actO S T g h u ∈ Λ) → ∀ c c' : ℂ, c ≠ 0 → om (g, h) f₀ = c • f₀ → (∀ x, Φ (actO S T g⁻¹ h⁻¹ x) = c' * Φ x) → om (g, h) f = (c * c') • f := by
  intro D ψ S T χS χT om hom e Λ f₀ Φ f hth hΘ g h hΛ c c' hc hf₀ hΦ
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hΘ
  let Tm' : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) :=
    c⁻¹ • (om (g, h) ∘ₗ Tm ∘ₗ LinearMap.funLeft ℂ ℂ (actO S T g h))
  have hT' : ∀ Ψ, Tm' Ψ = c⁻¹ • om (g, h) (Tm fun t => Ψ (actO S T g h t)) := fun Ψ => rfl
  have hP : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Tm' := by
    refine ⟨fun Ψ hΨ x hx => ?_, fun Ψ hΨ y hy => ?_, ?_⟩
    · have hΨ' := isSBHalf_comp g h hΛ hΨ
      have h1 := hTm.trans _ hΨ' _ (isHalf_actO g⁻¹ h⁻¹ hx)
      simp only [act_add, act_act_inv] at h1
      rw [hT', hT', h1, hom.om_heis _ _ _ _ (hth Tm hTm _ hΨ'), act_act_inv, heisO_smul']
    · have hΨ' := isSBHalf_comp g h hΛ hΨ
      have h1 := hTm.modul _ hΨ' _ (isHalf_actO g⁻¹ h⁻¹ hy)
      have h2 : ∀ t, symplO S T t (actO S T g⁻¹ h⁻¹ y) = symplO S T (actO S T g h t) y := fun t => by
        rw [← symplO_actO S T g h, act_act_inv]
      simp only [h2] at h1
      rw [hT', hT', h1, hom.om_heis _ _ _ _ (hth Tm hTm _ hΨ'), act_act_inv, heisO_smul']
    · have h1 := hTm.vac
      rw [one_smul] at h1 ⊢
      have h2 : (fun t => halfInd e Λ (actO S T g h t)) = halfInd e Λ := funext (halfInd_act g h hΛ)
      rw [hT', h2, h1, hf₀, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have e1 : f = Tm Φ := hall Tm hTm
  have e2 : f = Tm' Φ := hall Tm' hP
  have e3 : Φ = c' • fun t => Φ (actO S T g h t) := by
    funext t
    have := hΦ (actO S T g h t)
    rw [actO_inv_actO] at this
    exact this
  rw [hT'] at e2
  have e4 : om (g, h) (Tm fun t => Φ (actO S T g h t)) = c • f := by
    rw [e2, smul_smul, mul_inv_cancel₀ hc, one_smul]
  calc om (g, h) f = om (g, h) (Tm (c' • fun t => Φ (actO S T g h t))) := by rw [← e3, ← e1]
    _ = (c * c') • f := by rw [map_smul, map_smul, e4, smul_smul, mul_comm]

end GlobalTheory.ThetaMove

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.TripleAssembly.Transport

theorem exists_factor {V Q P : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup Q] [Module ℂ Q]
    [AddCommGroup P] [Module ℂ P] (T : V →ₗ[ℂ] Q) (S : Submodule ℂ V) (hT : ∀ Φ ∈ S, T Φ = 0 → Φ = 0)
    (pD : V →ₗ[ℂ] P) : ∃ q : Q →ₗ[ℂ] P, ∀ Ψ ∈ S, q (T Ψ) = pD Ψ := by
  have hinj : Function.Injective (T ∘ₗ S.subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    exact Subtype.ext (hT x.1 x.2 hx)
  let eq := LinearEquiv.ofInjective (T ∘ₗ S.subtype) hinj
  obtain ⟨g, hg⟩ := LinearMap.exists_extend ((pD ∘ₗ S.subtype) ∘ₗ eq.symm.toLinearMap)
  refine ⟨g, fun Ψ hΨ => ?_⟩
  have h1 : g (T Ψ) = (g ∘ₗ (LinearMap.range (T ∘ₗ S.subtype)).subtype) (eq ⟨Ψ, hΨ⟩) := rfl
  rw [h1, hg]
  simp

end GlobalTheory.TripleAssembly.Transport

end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

namespace GlobalTheory

open Polynomial

theorem dixmier_aeval_injective {V : Type} [AddCommGroup V] [Module ℂ V] (T : Module.End ℂ V)
    (hT : ∀ c : ℂ, Function.Injective ⇑(T - c • (1 : Module.End ℂ V))) (p : ℂ[X]) (hp : p ≠ 0) :
    Function.Injective (aeval T p) := by
  have hs := C_leadingCoeff_mul_prod_multiset_X_sub_C (p := p) IsAlgClosed.card_roots_eq_natDegree
  have hlin : ∀ a : ℂ, aeval T (X - C a) = T - a • 1 := by
    intro a; simp [Algebra.algebraMap_eq_smul_one]
  have key : ∀ m : Multiset ℂ, Function.Injective (aeval T (m.map fun a => X - C a).prod) := by
    intro m
    induction m using Multiset.induction_on with
    | empty =>
      simp only [Multiset.map_zero, Multiset.prod_zero, map_one, Module.End.one_eq_id, LinearMap.id_coe]
      exact Function.injective_id
    | cons a m ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, map_mul, Module.End.mul_eq_comp, LinearMap.coe_comp]
      refine Function.Injective.comp ?_ ih
      rw [hlin]; exact hT a
  rw [← hs, map_mul, Module.End.mul_eq_comp, LinearMap.coe_comp]
  refine Function.Injective.comp ?_ (key _)
  rw [aeval_C, Algebra.algebraMap_eq_smul_one]
  intro x y hxy
  simp only [LinearMap.smul_apply, Module.End.one_apply] at hxy
  exact smul_right_injective V (leadingCoeff_ne_zero.mpr hp) hxy

theorem dixmier_commutant_scalar (ι V : Type) [AddCommGroup V] [Module ℂ V] (ρ : ι → Module.End ℂ V)
    (hrank : Module.rank ℂ V ≤ Cardinal.aleph0)
    (hirr : ∀ N : Submodule ℂ V, (∀ i, ∀ x ∈ N, ρ i x ∈ N) → N = ⊥ ∨ N = ⊤)
    (T : Module.End ℂ V) (hT : ∀ i, T * ρ i = ρ i * T) : ∃ c : ℂ, T = c • 1 := by
  by_contra hne
  push_neg at hne
  have hcomm : ∀ c : ℂ, ∀ i, (T - c • 1) * ρ i = ρ i * (T - c • 1) := by
    intro c i; rw [sub_mul, mul_sub, hT i, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  have hinj : ∀ c : ℂ, Function.Injective ⇑(T - c • (1 : Module.End ℂ V)) := by
    intro c
    rw [← LinearMap.ker_eq_bot]
    rcases hirr (LinearMap.ker (T - c • 1)) (fun i x hx => by
      rw [LinearMap.mem_ker] at hx ⊢
      rw [← Module.End.mul_apply, hcomm c i, Module.End.mul_apply, hx, map_zero]) with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp (LinearMap.ker_eq_top.mp h)) (hne c)
  obtain ⟨v₀, hv₀⟩ : ∃ v : V, v ≠ 0 := by
    by_contra h; push_neg at h
    exact hne 0 (LinearMap.ext fun v => (h _).trans (h _).symm)
  have hsurj : ∀ c : ℂ, Function.Surjective ⇑(T - c • (1 : Module.End ℂ V)) := by
    intro c
    rw [← LinearMap.range_eq_top]
    rcases hirr (LinearMap.range (T - c • 1)) (fun i x hx => by
      obtain ⟨y, rfl⟩ := hx
      exact ⟨ρ i y, by rw [← Module.End.mul_apply, hcomm c i, Module.End.mul_apply]⟩) with h | h
    · exfalso
      have h1 : (T - c • 1) v₀ ∈ LinearMap.range (T - c • 1) := LinearMap.mem_range_self _ _
      rw [h, Submodule.mem_bot] at h1
      exact hv₀ (hinj c (by rw [h1, map_zero]))
    · exact h
  let S : ℂ → V ≃ₗ[ℂ] V := fun c => LinearEquiv.ofBijective (T - c • 1) ⟨hinj c, hsurj c⟩
  let w : ℂ → V := fun c => (S c).symm v₀
  have hw : ∀ c, (T - c • (1 : Module.End ℂ V)) (w c) = v₀ := fun c => (S c).apply_symm_apply v₀
  have hlin : ∀ a : ℂ, aeval T (X - C a) = T - a • 1 := by
    intro a; simp [Algebra.algebraMap_eq_smul_one]
  have hli : LinearIndependent ℂ w := by
    rw [linearIndependent_iff']
    intro s g hsum i hi
    let q : ℂ → ℂ[X] := fun c => ∏ d ∈ s.erase c, (X - C d)
    have hq : ∀ c ∈ s, aeval T (∏ d ∈ s, (X - C d)) (w c) = aeval T (q c) v₀ := by
      intro c hc
      rw [← Finset.mul_prod_erase s _ hc, mul_comm, map_mul, Module.End.mul_apply, hlin, hw]
    have h0 : aeval T (∑ c ∈ s, g c • q c) v₀ = 0 := by
      have h2 := congrArg (aeval T (∏ d ∈ s, (X - C d))) hsum

      rw [map_zero, map_sum] at h2

      rw [map_sum, LinearMap.sum_apply, ← h2]
      refine Finset.sum_congr rfl fun c hc => ?_
      rw [LinearMap.map_smul, hq c hc, map_smul, LinearMap.smul_apply]
    have hp0 : ∑ c ∈ s, g c • q c = 0 := by
      by_contra hp
      exact hv₀ (dixmier_aeval_injective T hinj _ hp (by rw [h0, map_zero]))
    have h3 := congrArg (Polynomial.eval i) hp0
    rw [eval_finsetSum, Finset.sum_eq_single i] at h3
    · simp only [eval_smul, q, eval_prod, eval_sub, eval_X, eval_C, smul_eq_mul, eval_zero] at h3
      rcases mul_eq_zero.mp h3 with h | h
      · exact h
      · exfalso
        rw [Finset.prod_eq_zero_iff] at h
        obtain ⟨d, hd, hd0⟩ := h
        exact (Finset.ne_of_mem_erase hd) (sub_eq_zero.mp hd0).symm
    · intro c hc hci
      simp only [eval_smul, q, eval_prod, eval_sub, eval_X, eval_C, smul_eq_mul]
      rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hci, hi⟩) (sub_self i), mul_zero]
    · intro h; exact absurd hi h
  have h4 := hli.cardinal_le_rank
  rw [Cardinal.mk_complex] at h4
  exact absurd (h4.trans hrank) (not_le.mpr Cardinal.aleph0_lt_continuum)

end GlobalTheory
end
