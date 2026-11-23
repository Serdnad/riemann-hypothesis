module

import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle116
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.CpRegPhRegOfNonneg
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle101
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameChangeUnderFieldMap
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GenericBlockMatrixIsBlockDiag
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle031
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagonalMinorVanishing
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle012
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.FiniteEtaleSurjectiveOfPullback
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SheetCoverOfArithmeticVariety
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle107
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle032
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle095
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle043
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle110
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle109
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle097
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle021
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentModulusMatrix
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle088
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle102
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle103
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle090
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

namespace GlobalTheory.CompanionTheory.Ar.Cusp

theorem tendstoUniformlyOn_regWeight_of_isTied :
    ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing J)) (n : ℕ) (M : CxModel P n) (Xo : Set ((Σ k, J k) → ℂ)) (A : HermLine J) (S : LogLogRegularisationSetting M Xo A), S.IsTied → ∀ K' ⊆ S.R.Yo, IsCompact K' → TendstoUniformlyOn S.regWeight S.R.ph (𝓝[>] 0) K' := by
  apply GlobalTheory.CompanionTheory.Ar.Giv.Mix.tendstoUniformlyOn_regWeight_of_isCompact_subset_Yo <;> assumption

end GlobalTheory.CompanionTheory.Ar.Cusp
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.PlVanish

theorem cols_ne_empty {N j : ℕ} (hj : j ≤ N) (i : Fin N) : stepCols N j i ≠ ∅ := by
  intro e
  have hi := i.2
  by_cases h : (i : ℕ) + 1 ≤ j
  · have : (⟨N - j, by omega⟩ : Fin N) ∈ stepCols N j i := by
      simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_pos h]
      omega
    simp [e] at this
  · have : (⟨0, by omega⟩ : Fin N) ∈ stepCols N j i := by
      simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_neg h]
      omega
    simp [e] at this

theorem minor_one_ne {N : ℕ} {I J : Finset (Fin N)} (h : I ≠ J) :
    minorIJ (1 : Matrix (Fin N) (Fin N) ℂ) I J = 0 := by
  apply GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.FV.minorIJ_one_ne <;> assumption

theorem minor_one_same {N : ℕ} (I : Finset (Fin N)) :
    minorIJ (1 : Matrix (Fin N) (Fin N) ℂ) I I = 1 := by
  unfold minorIJ
  rw [dif_pos rfl, Matrix.submatrix_one _ (I.orderEmbOfFin rfl).injective, Matrix.det_one]

theorem det_submatrix_eq_zero {N : ℕ} (C : Matrix (Fin N) (Fin N) ℂ) (S : Finset (Fin N))
    (f : Fin S.card → Fin N) (hf : Function.Injective f)
    (h0 : minorIJ C (Finset.univ.image f) S = 0) :
    (C.submatrix f (S.orderEmbOfFin rfl)).det = 0 :=
  _root_.UpperTheory.Reformulated.B.MinorDeterminants.main C S f hf h0

theorem minor_quot {N j : ℕ} (hj : j ≤ N) (i : Fin N) {h₁ h₂ : Matrix (Fin N) (Fin N) ℂ} {α β : ℂ}
    (hb₁ : IsBlockDiag j h₁) (hb₂ : IsBlockDiag j h₂) (hd : h₁.det ≠ 0)
    (hp : ∀ I, IsStepRows N j i I → α * minorIJ h₁ I (stepCols N j i) = β * minorIJ h₂ I (stepCols N j i))
    (I : Finset (Fin N)) :
    β * minorIJ (h₁⁻¹ * h₂) I (stepCols N j i) =
      α * minorIJ (1 : Matrix (Fin N) (Fin N) ℂ) I (stepCols N j i) := by
  obtain ⟨cb, off, -, -⟩ := GlobalTheory.CompanionTheory.Ar.PB.MinorCalc.minors_main ℂ N j i hj
  have hne := cols_ne_empty hj i
  have hall : ∀ J, α * minorIJ h₁ J (stepCols N j i) = β * minorIJ h₂ J (stepCols N j i) := fun J => by
    by_cases hJ : IsStepRows N j i J
    · exact hp J hJ
    · rw [(off h₁ J hb₁ hJ).resolve_right hne, (off h₂ J hb₂ hJ).resolve_right hne, mul_zero, mul_zero]
  have e1 : minorIJ (1 : Matrix (Fin N) (Fin N) ℂ) I (stepCols N j i) =
      minorIJ (h₁⁻¹ * h₁) I (stepCols N j i) := by
    rw [Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hd)]
  rw [e1, cb, cb, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun J _ => ?_
  linear_combination (-minorIJ h₁⁻¹ I J) * hall J

theorem quot_vanish : ∀ (N j : ℕ) (i : Fin N) (h₁ h₂ : Matrix (Fin N) (Fin N) ℂ) (α β : ℂ), j ≤ N →
    IsBlockDiag j h₁ → IsBlockDiag j h₂ → h₁.det ≠ 0 → α ≠ 0 → β ≠ 0 →
    (∀ I, IsStepRows N j i I → α * minorIJ h₁ I (stepCols N j i) = β * minorIJ h₂ I (stepCols N j i)) →
    ∀ r c, c ∈ stepCols N j i → r ∉ stepCols N j i → (h₁⁻¹ * h₂) r c = 0 := by
  intro N j i h₁ h₂ α β hj hb₁ hb₂ hd hα hβ hp r c hc hr
  have hq := minor_quot hj i hb₁ hb₂ hd hp
  set S := stepCols N j i with hS
  set C := h₁⁻¹ * h₂ with hC
  let e := S.orderEmbOfFin rfl
  obtain ⟨t, ht⟩ : ∃ t, e t = c := by
    have h2 : c ∈ Set.range e := by
      rw [Finset.range_orderEmbOfFin]
      exact hc
    exact h2
  let D : Matrix (Fin S.card) (Fin S.card) ℂ := C.submatrix e e
  have hD : D.det ≠ 0 := by
    have h1 := hq S
    rw [minor_one_same, mul_one] at h1
    have h2 : minorIJ C S S = D.det := dif_pos rfl
    rw [← h2]
    intro h0
    rw [h0, mul_zero] at h1
    exact hα h1.symm
  let v : Fin S.card → ℂ := fun s => C r (e s)
  have hrow : ∀ u, (D.updateRow u v).det = 0 := fun u => by
    let f : Fin S.card → Fin N := Function.update e u r
    have hmem : ∀ s, e s ∈ S := fun s => Finset.orderEmbOfFin_mem _ _ _
    have hf : Function.Injective f := fun a b hab => by
      by_cases ha : a = u
      · by_cases hb : b = u
        · rw [ha, hb]
        · subst ha
          simp only [f, Function.update_self, Function.update_of_ne hb] at hab
          exact absurd (hab ▸ hmem b) hr
      · by_cases hb : b = u
        · subst hb
          simp only [f, Function.update_self, Function.update_of_ne ha] at hab
          exact absurd (hab ▸ hmem a) hr
        · simp only [f, Function.update_of_ne ha, Function.update_of_ne hb] at hab
          exact e.injective hab
    have hI : Finset.univ.image f ≠ S := fun h => hr (by
      rw [← h]
      exact Finset.mem_image.2 ⟨u, Finset.mem_univ _, Function.update_self _ _ _⟩)
    have h0 : minorIJ C (Finset.univ.image f) S = 0 := by
      have h1 := hq (Finset.univ.image f)
      rw [minor_one_ne hI, mul_zero] at h1
      exact (mul_eq_zero.1 h1).resolve_left hβ
    have h2 := det_submatrix_eq_zero C S f hf h0
    have e2 : D.updateRow u v = C.submatrix f e := by
      ext a b
      by_cases ha : a = u
      · subst ha
        simp [f, D, v, Matrix.updateRow_self]
      · simp [f, D, Matrix.updateRow_ne ha, Function.update_of_ne ha]
    rw [e2]
    exact h2
  have hcr : Dᵀ.cramer v = 0 := by
    funext u
    rw [Matrix.cramer_transpose_apply]
    exact hrow u
  have h3 := Matrix.mulVec_cramer Dᵀ v
  rw [hcr, Matrix.mulVec_zero, Matrix.det_transpose] at h3
  have h4 : D.det * v t = 0 := by
    have := congrFun h3 t
    simpa using this.symm
  have h5 : v t = 0 := (mul_eq_zero.1 h4).resolve_left hD
  rw [← ht]
  exact h5

end GlobalTheory.CompanionTheory.Ar.PB.PlVanish
end
end

section

open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder


theorem _root_.GlobalTheory.CompanionTheory.Relay.isArithVar_of_snc_model : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (x : (Σ k, J k) → Ω) (n : ℕ) (bd : Ideal (MRing J)), 1 ≤ n → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, x ⟨k, c' k⟩) → Cmp.IsSncModel x n bd → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal x) (n + 1) := by
  first | exact @PositivityTheory.Xgp.t_c_bm_exists_arith | exact PositivityTheory.Xgp.t_c_bm_exists_arith
end

section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

theorem _root_.GlobalTheory.T.hodgeCpt_lattice_base_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (x : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S x) (τ : CMType H) (X' : Scheme.{0}) (G : Type) [Field G] [Algebra Ω G] (ξ' : Spec (CommRingCat.of G) ⟶ X') (pr : X' ⟶ 𝔐.X) (Li' : Type) [AddCommGroup Li'] [Module G Li'] (j : 𝔐.Li →+ Li') (bO : Module.Basis (Fin D.q) Ω (Module.Dual Ω (𝔐.Vgen (.inr τ)))) (v : Fin D.q → 𝔐.Vgen (.inr τ)) (u : Matrix (Fin D.q) (Fin D.q) G), IsExtOver (algebraMap Ω G) j → GlobalTheory.CompanionTheory.Ar.Dominates ξ' 𝔐.ξ pr (algebraMap Ω G) → (∀ a b, bO a (v b) = if a = b then 1 else 0) → (∀ a, u a a = 1) → (∀ a b, a < b → u a b = 0) → ((omBundle 𝔐 τ).pull ξ' pr (TensorProduct.mk Ω G (Module.Dual Ω (𝔐.Vgen (.inr τ))) 1).toAddMonoidHom).IsFlagVBOn Set.univ (fun k => ∑ l, u l k • TensorProduct.mk Ω G (Module.Dual Ω (𝔐.Vgen (.inr τ))) 1 (bO l)) → ((𝔐.V (.inr τ)).pull ξ' pr j).IsFlagVBOn Set.univ (fun k => colFrame (fun a => j (v a)) uᵀ⁻¹ k.rev) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl.flags_dual_of_flags_pull | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl.flags_dual_of_flags_pull | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl.flags_dual_of_flags_pull <;> assumption)
end

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace

theorem _root_.GlobalTheory.T.sheet_cover_of_arithmetic_variety : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MRing J)) (n nc : ℕ) (Bd : Set ((Σ k, J k) → ℂ)) (χ : Fin nc → GroundTheory.Heights₂.Heights.LowerBoundFree.SncChart P n Bd) (V B : ℕ → Set (Fin n → ℂ)) (γ : ℕ → (Fin n → ℂ) → (Σ k, J k) → ℂ) (A : HermLine J) (G : ((Σ k, J k) → ℂ) → ℝ), IsArithVar P (n + 1) → (∀ z ∈ mcPts P, ∃ a, ∃ t : Fin n → ℂ, ‖t‖ ≤ 1 / 2 ∧ z ∈ torusSat {(χ a).γ t}) → IsSheetCover χ V B γ → (∀ m, ContDiffOn ℝ 2 (fun t => Real.log (A.h (γ m t))) (V m)) → (∀ w ∈ mcPts P \ Bd, ∀ w' ∈ torusSat {w}, G w' = G w) → (∀ m, IntegrableOn (fun t => G (γ m t) * maDensity (fun (_ : Fin n) t' => Real.log (A.h (γ m t'))) t) (B m)) → Summable (fun m => ∫ t in B m, |G (γ m t) * maDensity (fun (_ : Fin n) t' => Real.log (A.h (γ m t'))) t|) → ptsIntegral (e := n) P (fun _ z => Real.log (A.h z)) G = ∑' m, ∫ t in B m, G (γ m t) * maDensity (fun (_ : Fin n) t' => Real.log (A.h (γ m t'))) t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.ptsIntegral_sheets | exact GlobalTheory.CompanionTheory.Ar.Cusp.ptsIntegral_sheets | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.ptsIntegral_sheets <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem _root_.GlobalTheory.T.hodge_metric_frame_properties : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D), (∀ z ∈ mcPts (mCoordIdeal D.y), Nonempty (MuFrameAt Hd z)) ∧ (∀ z ∈ D.Xo, ∀ d : MuFrameAt Hd z, 0 < d.norm ∧ (muLine Hd).h z = d.norm) ∧ LogHom D Hd.aMu (phMu Hd) ∧ ConjOff D (phMu Hd) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.hodge_metric_frame_properties | exact GlobalTheory.CompanionTheory.Relay.hodge_metric_frame_properties | (intros; apply GlobalTheory.CompanionTheory.Relay.hodge_metric_frame_properties <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun


theorem _root_.GlobalTheory.T.exists_local_twist_trivialization : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type) (x : κ → Ω) (L : Lat ξ E) (m r n : ℕ) (V : Submodule Ω E) (φ : Fin n → Module.Dual Ω E) (cb : Fin r → E), IsTwistGen ξ x L m φ → L.IsVB r V → LinearIndependent Ω cb → Submodule.span Ω (Set.range cb) = V → ∀ (p : Cpt ξ) (c : κ), InChart ξ x c p → ∃ (T : Matrix (Fin r) (Fin r) Ω) (C : Matrix (Fin r) (Fin n) Ω), IsUnit T.det ∧ L.IsFrameAt (colFrame cb T) p ∧ (∀ a b, ((Matrix.of fun a b => φ a (cb b)) * T) a b / x c ^ m ∈ regAt ξ p) ∧ (∀ a b, C a b ∈ regAt ξ p) ∧ ∀ a b, ∑ k, C a k * (((Matrix.of fun a b => φ a (cb b)) * T) k b / x c ^ m) = if a = b then 1 else 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.RootsBase.frame_values | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.RootsBase.frame_values | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.RootsBase.frame_values <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

namespace GlobalTheory.CompanionTheory.Ar.PB.FrameTrans

theorem colFrame_injective {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] {r : ℕ} {e : Fin r → V}
    (he : LinearIndependent Ω e) {T T' : Matrix (Fin r) (Fin r) Ω} (h : colFrame e T = colFrame e T') : T = T' := by
  ext a b
  have hb := congrFun h b
  simp only [colFrame] at hb
  have h0 := Fintype.linearIndependent_iff.1 he (fun a => T a b - T' a b)
    (by simp only [sub_smul, Finset.sum_sub_distrib]; exact sub_eq_zero.2 hb) a
  exact sub_eq_zero.1 h0

theorem linearIndependent_colFrame {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] {r : ℕ} {w : Fin r → V}
    (hw : LinearIndependent Ω w) {g : Matrix (Fin r) (Fin r) Ω} (hg : IsUnit g.det) :
    LinearIndependent Ω (colFrame w g) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hsum : ∑ a, (g.mulVec c a) • w a = 0 := by
    rw [← hc]
    simp only [colFrame, Matrix.mulVec, dotProduct, Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [_root_.mul_comm]
  have h0 : g.mulVec c = 0 := funext (Fintype.linearIndependent_iff.1 hw _ hsum)
  have hc0 : c = 0 := Matrix.eq_zero_of_mulVec_eq_zero hg.ne_zero h0
  intro i
  rw [hc0]
  rfl

theorem exists_regular_coeff {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type}
    [AddCommGroup E] [Module Ω E] {p : Cpt ξ} {r : ℕ} {e : Fin r → E} {v : E}
    (h : v ∈ Submodule.span (regAt ξ p) (Set.range e)) :
    ∃ c : Fin r → Ω, (∀ a, c a ∈ regAt ξ p) ∧ v = ∑ a, c a • e a := by
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h
  exact ⟨fun k => (a k : Ω), fun k => (a k).2, ha.symm⟩

theorem exists_triangular {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] {r : ℕ} {b b₀ : Fin r → V}
    (hF : ∀ i, flagStep Ω b i = flagStep Ω b₀ i) :
    ∃ U : Matrix (Fin r) (Fin r) Ω, U.BlockTriangular id ∧ b = colFrame b₀ U := by
  have hex : ∀ l : Fin r, ∃ f : Fin r → Ω, (∀ k : Fin r, ¬ (k : ℕ) < (l : ℕ) + 1 → f k = 0) ∧
      b l = ∑ k, f k • b₀ k := by
    intro l
    have h1 : b l ∈ flagStep Ω b₀ ((l : ℕ) + 1) := by
      rw [← hF]
      exact Submodule.subset_span ⟨l, Nat.lt_succ_self _, rfl⟩
    obtain ⟨f, hf, hs⟩ := (Finsupp.mem_span_image_iff_linearCombination Ω).1 h1
    refine ⟨f, fun k hk => (Finsupp.mem_supported' Ω f).1 hf k hk, ?_⟩
    rw [← hs, Finsupp.linearCombination_apply]
    exact Finsupp.sum_fintype f (fun i a => a • b₀ i) (fun k => zero_smul Ω _)
  choose f hf0 hf using hex
  refine ⟨fun k l => f l k, ?_, ?_⟩
  · intro i j hij
    have hij' : j < i := hij
    refine hf0 j i ?_
    have : (j : ℕ) < i := hij'
    omega
  · funext l
    exact hf l

theorem sub_diag_mem {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] {r : ℕ} (b₀ : Fin r → V)
    {U : Matrix (Fin r) (Fin r) Ω} (hU : U.BlockTriangular id) (l : Fin r) :
    colFrame b₀ U l - U l l • b₀ l ∈ flagStep Ω b₀ l := by
  have h : colFrame b₀ U l - U l l • b₀ l = ∑ a ∈ Finset.univ.erase l, U a l • b₀ a := by
    rw [colFrame, ← Finset.add_sum_erase _ _ (Finset.mem_univ l), add_sub_cancel_left]
  rw [h]
  refine Submodule.sum_mem _ fun a ha => ?_
  have hne : a ≠ l := Finset.ne_of_mem_erase ha
  by_cases hlt : (a : ℕ) < l
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, hlt, rfl⟩)
  · have hla : l < a := lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hne)
    rw [hU hla, zero_smul]
    exact zero_mem _

theorem exists_adapted : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (r : ℕ) (w : Fin r → E) (P g : Matrix (Fin r) (Fin r) Ω) (p : Cpt ξ), LinearIndependent Ω w → IsUnit g.det → L.IsFrameAt (colFrame w P) p → L.IsFlagVBOn Set.univ (colFrame w g) → ∃ U Rm Rm' : Matrix (Fin r) (Fin r) Ω, U.BlockTriangular id ∧ (∀ a b, Rm a b ∈ regAt ξ p) ∧ (∀ a b, Rm' a b ∈ regAt ξ p) ∧ Rm * Rm' = 1 ∧ g * U = P * Rm ∧ ∀ l, (L.gr (colFrame w g) l).IsGenAt p (U l l) := by
  intro X Ω _ ξ E _ _ L r w P g p hw hg he hFl
  obtain ⟨V, hV, b, hbF, hbL⟩ := hFl p (Set.mem_univ p)
  have hb : L.IsFrameAt b p := hbL p (Set.mem_univ p) hV
  have hb₀ := linearIndependent_colFrame hw hg
  obtain ⟨U, hU, hbU⟩ := exists_triangular hbF
  have hexR : ∀ l : Fin r, ∃ c : Fin r → Ω, (∀ a, c a ∈ regAt ξ p) ∧ b l = ∑ a, c a • colFrame w P a := by
    intro l
    refine exists_regular_coeff ?_
    rw [← he.2, hb.2]
    exact Submodule.subset_span ⟨l, rfl⟩
  have hexR' : ∀ l : Fin r, ∃ c : Fin r → Ω, (∀ a, c a ∈ regAt ξ p) ∧ colFrame w P l = ∑ a, c a • b a := by
    intro l
    refine exists_regular_coeff ?_
    rw [← hb.2, he.2]
    exact Submodule.subset_span ⟨l, rfl⟩
  choose c hc hcs using hexR
  choose c' hc' hcs' using hexR'
  obtain ⟨Rm, hRm, hbR⟩ : ∃ Rm : Matrix (Fin r) (Fin r) Ω, (∀ a l, Rm a l ∈ regAt ξ p) ∧
      b = colFrame (colFrame w P) Rm := ⟨fun a l => c l a, fun a l => hc l a, funext hcs⟩
  obtain ⟨Rm', hRm', heR⟩ : ∃ Rm' : Matrix (Fin r) (Fin r) Ω, (∀ a l, Rm' a l ∈ regAt ξ p) ∧
      colFrame w P = colFrame b Rm' := ⟨fun a l => c' l a, fun a l => hc' l a, funext hcs'⟩
  refine ⟨U, Rm, Rm', hU, hRm, hRm', ?_, ?_, ?_⟩
  · refine colFrame_injective he.1 ?_
    rw [colFrame_mul, ← hbR, ← heR, colFrame_one]
  · refine colFrame_injective hw ?_
    rw [colFrame_mul, colFrame_mul, ← hbU, ← hbR]
  · intro l
    refine FlagGrGen.gr_isGenAt X Ω ξ E L r (colFrame w g) b p l (U l l) hb₀ hbF hb ?_
    rw [hbU]
    exact sub_diag_mem _ hU l

end GlobalTheory.CompanionTheory.Ar.PB.FrameTrans
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

theorem _root_.GlobalTheory.T.holomorphic_frame_metric_near_point : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (V : Set X) (y₀ : X) (zb : X → (Σ k, baseIdx ι M.blk k) → ℂ) (Hm : X → Matrix (Fin N) (Fin N) ℂ) (F : FrameData ι Ψ N M.Ω M.blk) (τ : Ψ) (a : Fin N), IsOpen V → y₀ ∈ V → (∀ q, A.HoloOn V fun w => zb w q) → (∀ w ∈ V, zb w ∈ mcPts (mCoordIdeal M.x)) → (∀ w ∈ V, M.GoodAt F (mCoordIdeal (zb w))) → (∀ r s, A.HoloOn V fun w => Hm w r s) → (∀ w ∈ V, IsBlockDiag j (Hm w) ∧ (Hm w).det ≠ 0) → ∃ V' : Set X, IsOpen V' ∧ y₀ ∈ V' ∧ V' ⊆ V ∧ A.HoloOn V' (fun w => ∏ i : Fin N, (if IsProperStep N j i then 1 else valAt M.x (F.υ (τ, i)) (zb w) * (if (i : ℕ) + 1 = j then (if (a : ℕ) < j then minorIJ (Hm w) (wIdx N j) (wIdx N j) else 1) else minorIJ (Hm w) (omIdx N j) (omIdx N j))) ^ xiCoef τ a (τ, i)) ∧ ∀ w ∈ V', (∏ i : Fin N, (if IsProperStep N j i then 1 else valAt M.x (F.υ (τ, i)) (zb w) * (if (i : ℕ) + 1 = j then (if (a : ℕ) < j then minorIJ (Hm w) (wIdx N j) (wIdx N j) else 1) else minorIJ (Hm w) (omIdx N j) (omIdx N j))) ^ xiCoef τ a (τ, i)) ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Factor.improper_factor | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Factor.improper_factor | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Factor.improper_factor <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

theorem _root_.GlobalTheory.T.elementary_twist_minor_other_steps : ∀ (N j : ℕ) (a b ca cb : Fin N), j ≤ N → (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (h : Matrix (Fin N) (Fin N) ℂ) (t : ℂ) (i : Fin N), i ≠ a → ∀ I, minorIJ (h * (1 + Matrix.single cb ca t)) I (stepCols N j i) = minorIJ h I (stepCols N j i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.TransvOther.minorIJ_other_step | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.TransvOther.minorIJ_other_step | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.TransvOther.minorIJ_other_step <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

theorem _root_.GlobalTheory.T.flag_dimension_index_equiv : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j n d : ℕ), j ≤ N → d + 1 = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) → Nonempty (Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin (d + 2)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.ChartCount.nonempty_paramEquiv | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.ChartCount.nonempty_paramEquiv | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.ChartCount.nonempty_paramEquiv <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan


theorem _root_.GlobalTheory.T.LU_twist_refactorization : ∀ (N j : ℕ) (a ca cb : Fin N) (L U : Matrix (Fin N) (Fin N) ℂ) (t' : ℂ), j ≤ N → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ((ca : ℕ) < N - j ↔ (cb : ℕ) < N - j) → IsBlockDiag j L → IsLowerUni L → IsBlockDiag j U → U.BlockTriangular id → (∀ c, U c c ≠ 0) → minorIJ (L * U * (1 + Matrix.single cb ca t')) (stepCols N j a) (stepCols N j a) ≠ 0 → ∃ (t : ℂ) (V : Matrix (Fin N) (Fin N) ℂ), IsBlockDiag j V ∧ V.BlockTriangular id ∧ (∀ c ∈ stepCols N j a, V c c ≠ 0) ∧ U * (1 + Matrix.single cb ca t') = (1 + Matrix.single cb ca t) * V := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.Transv.main | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.Transv.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.Transv.main <;> assumption)
end
