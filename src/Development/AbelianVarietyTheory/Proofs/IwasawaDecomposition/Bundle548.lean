module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle414
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle140
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle540
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle538
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle541
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing

@[expose] public section

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

namespace GlobalTheory.AntisymmChern

theorem antisymm_eq_chernRoots_mul_rootDiscr : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (Q : MvPolynomial (Root m) ℝ), ∃ R : MvPolynomial (ι × ℕ) ℝ, antisymm Q = chernRoots m R * rootDiscr m := by
  intro ι _ m Q
  classical
  obtain ⟨S, hS⟩ : rootDiscr m ∣ antisymm Q := GlobalTheory.T.flagRelativeTangentTopChern_dvd_of_differences_dvd ι m (antisymm Q) fun τ i j hij =>
    GlobalTheory.T.X_sub_X_dvd_of_rename_swap_eq_neg (⟨τ, i⟩ : Root m) ⟨τ, j⟩ (by simp [hij.ne]) _ (GlobalTheory.T.weylAntisymmetrization_rename_swap_neg ι m Q τ i j hij.ne)
  have hsym : ∀ w : ∀ τ, Equiv.Perm (Fin (m τ)), rename (Equiv.sigmaCongrRight w) S = S := by
    intro w
    have h1 := GlobalTheory.T.weylAntisymmetrization_rename_block_perm_sign ι m Q w
    rw [hS, map_mul, GlobalTheory.T.flagRelativeTangentTopChern_rename_block_perm ι m w, smul_mul_assoc] at h1
    have hs : ((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) ≠ 0 := Units.ne_zero _
    exact mul_left_cancel₀ (GlobalTheory.T.flagRelativeTangentTopChern_ne_zero ι m) (smul_right_injective _ hs h1)
  obtain ⟨R, hR⟩ := GlobalTheory.T.symmetric_poly_chern_roots ι m S hsym
  exact ⟨R, by rw [hS, hR, mul_comm]⟩

end GlobalTheory.AntisymmChern
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3.StepUniq


open Classical in
theorem eq_zero_of_vanish_it : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Pins R F cG → Holds R F → ∀ (t : T) (k : ℕ), k + 1 < D.R.m → ∀ u : MMap (R.MY k), Formalism.IndefR.Eqv.ContAt (R.MY k) u → (∀ φ w, PiTensorProduct.lift u (R.ItY k φ w) = 0) → u = 0 := by
  intro hDS hHC D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hP hH t k hk u hc hv
  have hB := hP.char.base
  have hCh : R.toRealDat.IsChain := RealDat.chain_of_weak hB.chain hH.aux.ex
  have hok := GlobalTheory.Chain.StepVac.stepsOK D G Pl0 T A3.A Ks R.toRealDat hB.lev hB.models.inf hCh.ωY hCh.ωX hCh.vY hCh.vX
  obtain ⟨hw, hvv⟩ := hok.1 t ⟨k, by omega⟩ hk
  have hIt := hCh.ItY t k hk
  have hle := GlobalTheory.ItOnto.kfinSpan_le_span_it hDS hHC D _ _ _ _ (R.MY k) (R.MY (k + 1)) R.θ R.ψ _ _
    (R.ωY t k) (R.vY t k) (R.ItY k) hB.models.inf hw hvv hIt
  have hx : ∀ x, (LinearMap.proj x : (GA D (Yc D k) → ℂ) →ₗ[ℂ] ℂ) ∘ₗ PiTensorProduct.lift u = 0 := by
    intro x
    refine GlobalTheory.Core.Mi.eq_zero_of_sepCont hHC D _ _ (R.MY k) _ ?_ ?_
    · intro τ v
      obtain ⟨ℓ, hℓ, he⟩ := hc τ v x
      refine ⟨ℓ, hℓ, fun w => ?_⟩
      rw [he w]
      simp [PiTensorProduct.lift.tprod]
    · intro v hv'
      have hmem := hle (Submodule.subset_span ⟨v, fun τ => Submodule.subset_span (hv' τ), rfl⟩)
      have hker : Submodule.span ℂ {w | ∃ P, ∃ y ∈ Submodule.span ℂ {w | ∃ v, (∀ τ, ((v τ : (R.MY (k + 1)).sm τ) :
          (R.MY (k + 1)).H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin (R.MY (k + 1)) τ) ∧ w = PiTensorProduct.tprod ℂ v},
            w = (R.ItY k P) y} ≤ LinearMap.ker ((LinearMap.proj x : (GA D (Yc D k) → ℂ) →ₗ[ℂ] ℂ) ∘ₗ
              PiTensorProduct.lift u) := by
        rw [Submodule.span_le]
        rintro _ ⟨P, y, -, rfl⟩
        simp [hv P y]
      exact hker hmem
  have h0 : PiTensorProduct.lift u = 0 := by
    ext v x
    have := congrArg (fun Λ => Λ (PiTensorProduct.tprod ℂ v)) (hx x)
    simpa using this
  have : u = PiTensorProduct.lift.symm (PiTensorProduct.lift u) := by simp
  rw [this, h0, map_zero]

end GlobalTheory.Mem.R3.StepUniq
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
open MonoidalCategory CartesianMonoidalCategory MonObj


theorem _root_.GlobalTheory.T.derivatives_separate_lieBasis_coeffs_cartesian : ∀ {S : Type} [CommRing S] {X : Scheme.{0}} {x : Sp S ⟶ X} {G : Over X} {G' : Over (Sp S)} [GrpObj G] [GrpObj G'] [IsCommMonObj G'] {φ : G'.left ⟶ G.left}, IsGrpPullback G' G x φ → ∀ {n : ℕ} (v : Fin n → (epsR S ⟶ G')), IsLieBasis v → ∀ {V : G.left.Opens}, IsAffineOpen V → ⊤ ≤ ((η[G']).left ≫ φ) ⁻¹ᵁ V → ∀ (b : Fin n → S), (∀ f : Γ(G.left, V), ∑ k, b k * (valR ((v k).left ≫ φ) V f).snd = 0) → b = 0 := by
  first | exact @GlobalTheory.ArcLieCoord.sep | exact GlobalTheory.ArcLieCoord.sep | (intros; apply GlobalTheory.ArcLieCoord.sep <;> assumption)
end
