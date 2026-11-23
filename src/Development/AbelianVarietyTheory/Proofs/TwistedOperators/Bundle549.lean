module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfOrthogonalTranslates
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle513
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsPureTensors
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.KTypeExtension
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ChainParSucc
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle535
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle299
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSphericalOperatorsRowsNormalEigenspaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle238
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle205
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle164
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle322
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle534
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle136
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle374
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle536
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle005
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.FibrePushforward
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsPointedOfIsHkIsog
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle411

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PureTensorExists

theorem existsUnique_isPure : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (x : Place D → WO S T → ℂ), IsRestricted ψ θ S T sS sT ΛS ΛT f₀ x → ∃! f, IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f := by
  intro D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hC x hx
  classical
  have hstd : IsStdChar D ψ (-1) := GlobalTheory.PlaceTensor.base_std hB
  have hf0 : IsThetaFunO ψ S T f₀ := GlobalTheory.PlaceTensor.base_theta hB

  have build : ∀ (s : Finset (Place D)) (y : Place D → WO S T → ℂ),
      IsRestricted ψ θ S T sS sT ΛS ΛT f₀ y → (∀ p, y p ≠ f₀ → p ∈ s) →
        ∃ f, IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ y f := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro y _ hy
      have hconst : y = fun _ => f₀ := by
        funext p
        by_contra hne
        exact absurd (hy p hne) (by simp)
      subst hconst
      exact ⟨f₀, (GlobalTheory.T.isPureTensor_base_vector_and_local_factor D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hC).1⟩
    · intro q s _ ih y hyR hy

      have hres : IsRestricted ψ θ S T sS sT ΛS ΛT f₀ (Function.update y q f₀) := by
        refine ⟨fun p => ?_, ?_⟩
        · by_cases hpq : p = q
          · subst hpq
            simpa using GlobalTheory.PlaceTensor.base_isLocal hB p
          · simpa [Function.update_apply, hpq] using hyR.1 p
        · refine hyR.2.subset fun p hp => ?_
          by_cases hpq : p = q
          · subst hpq
            simp at hp
          · simpa [Function.update_apply, hpq] using hp
      have hsub : ∀ p, Function.update y q f₀ p ≠ f₀ → p ∈ s := by
        intro p hp
        by_cases hpq : p = q
        · subst hpq
          simp at hp
        · have hp' : y p ≠ f₀ := by simpa [Function.update_apply, hpq] using hp
          rcases Finset.mem_insert.1 (hy p hp') with h | h
          · exact absurd h hpq
          · exact h
      obtain ⟨f, hf⟩ := ih (Function.update y q f₀) hres hsub
      obtain ⟨f', hf', -⟩ := GlobalTheory.T.pureTensor_update_factor_from_base_vector D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hC
        (Function.update y q f₀) y f q hf (by simp)
        (fun p hp => (Function.update_of_ne hp f₀ y).symm) (hyR.1 q)
      exact ⟨f', hf'⟩
  obtain ⟨f, hf⟩ := build hx.2.toFinset x hx (fun p hp => by simpa using hp)
  refine ⟨f, hf, fun g hg => ?_⟩

  obtain ⟨hHaar, hFD, -⟩ := id hC
  have hfT : IsThetaFunO ψ S T f := hf.2.1
  have hgT : IsThetaFunO ψ S T g := hg.2.1
  have hIP := GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 hstd hC
  have hd : IsThetaFunO ψ S T (g - f) := GlobalTheory.WeilVacMove.isTheta_sub hgT hfT
  have hz : g - f = 0 := by
    refine GlobalTheory.HeisTotal.eq_zero_of_orthogonal_translates D ψ hstd S T f₀ (g - f) hf0
      (GlobalTheory.PlaceTensor.base_ne_zero hB) hd μ 𝓕 hHaar hFD fun w => ?_
    have hw : IsThetaFunO ψ S T (heisO ψ S T w f₀) :=
      (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hstd S T).1 w f₀ hf0
    have e1 : ipO μ 𝓕 g (heisO ψ S T w f₀) = ipO μ 𝓕 f (heisO ψ S T w f₀) := by
      rw [(hg.2.2 w).2, (hf.2.2 w).2]
    have e2 : ipO μ 𝓕 (heisO ψ S T w f₀) g = ipO μ 𝓕 (heisO ψ S T w f₀) f := by
      rw [(hIP g _ hgT hw).2.1, (hIP f _ hfT hw).2.1, e1]
    have e3 := ((hIP (g - f) _ hd hw).2.2.2.1 f hfT).2
    rw [sub_add_cancel] at e3
    have e4 : ipO μ 𝓕 (heisO ψ S T w f₀) (g - f) = 0 := by
      linear_combination e2 - e3
    exact e4
  exact sub_eq_zero.1 hz

end GlobalTheory.PureTensorExists
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.fockVectors_pureTensors : ∀ D : D7, FockPure D := by
  first | exact @GlobalTheory.FockPureTensor.fockPure | exact GlobalTheory.FockPureTensor.fockPure | (intros; apply GlobalTheory.FockPureTensor.fockPure <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.gkMapCuspForms_extends_to_smoothVectors : GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.GKExtension D := by
  first | exact @GlobalTheory.GKExtensionToSmoothVectors.gkExtension | exact GlobalTheory.GKExtensionToSmoothVectors.gkExtension | (intros; apply GlobalTheory.GKExtensionToSmoothVectors.gkExtension <;> assumption)
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

theorem _root_.GlobalTheory.T.exists_testFamilies_projectedTranslationOperators : ∀ (D : D7) (V : HSp D) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V), U.u ∉ T.S → ∀ (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)), (∀ v, (μf v).IsHaarMeasure) → (∀ᶠ v in cofinite, μf v (Kv V v) = 1) → ∀ ν, IsFinMeas V μf ν → ∃ e, IsFinFamily D.sp.cm.sig V.gram (frameLat V) e ∧ (∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), GlobalTheory.PRep.IsSmooth σ → ∀ P, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ (finFn V e) P → P ∘ₗ P = P ∧ (HasTypeVec T σ → P ≠ 0)) ∧ ∀ g : GfC V, ∃ ff, IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff ∧ (∀ k ∈ U.frame.iwahori, ∀ x, ff U.u (k * x) = ff U.u x) ∧ (∀ t ∈ strictTorus V.rank U.ϖ, IsTestFin T U μf (Function.update ff U.u (U.frame.cosetFn t)) ∧ SphRest T U (Function.update ff U.u (U.frame.cosetFn t))) ∧ ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), GlobalTheory.PRep.IsSmooth σ → ∀ P, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ (finFn V e) P → GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ (finFn V ff) (P ∘ₗ σ g ∘ₗ P) := by
  first | exact @GlobalTheory.TestFamTr.test_families | exact GlobalTheory.TestFamTr.test_families | (intros; apply GlobalTheory.TestFamTr.test_families <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.congruenceSubgroup_level_member_clauses : ∀ (D : D7) (c : GlobalTheory.EvenOnto.Com D) (s : GlobalTheory.EvenOnto.PiLocalization₂ D) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → (∀ P : HeightOneSpectrum (𝓞 D.host.E), 𝔪 ≤ P.asIdeal → P.under (𝓞 D.host.F) ∈ c.S) → IsSelfDualC s.V s.Λ → s.J = Lev.levA s.V (congLev D.sp.cm s.V.gram s.Λ 𝔪) → s.J ≤ GfC s.V ∧ (∃ U : Subgroup (GA D s.V), IsOpen (U : Set (GA D s.V)) ∧ ∀ k ∈ U, k ∈ GfC s.V → k ∈ s.J) ∧ (∀ k ∈ s.J, ∀ v, GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v k ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram s.Λ v) ∧ (∀ k ∈ GfC s.V, k ∈ GlobalTheory.EvenOnto.intOff c s → (∀ v ∈ c.S, GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v k = 1) → k ∈ s.J) ∧ SphOff (s.J : Set (GA D s.V)) 1 c.S ∧ ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) e f, OffS D c.S P → IsPrimeIdem P e f → ∀ k ∈ s.J, ∃ k₁ ∈ s.J, ∃ k₂ ∈ s.J, SuppF s.V f k₁ ∧ SuppF s.V (1 - f) k₂ ∧ k = k₁ * k₂ := by
  first | exact @GlobalTheory.CongMember.congLev_clauses | exact GlobalTheory.CongMember.congLev_clauses | (intros; apply GlobalTheory.CongMember.congLev_clauses <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.Hk3.LabDetRows

open GlobalTheory.Hk3 GlobalTheory.Hk3.LabDet

theorem dual_eq_of_split : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ SF, GlobalTheory.Hk3.IsSF R SF → ∀ (c c' : Pl D.host.E → List ℤ → ℂ), GlobalTheory.Hk3.EEc R SF c ≠ ⊥ → GlobalTheory.Hk3.EEc R SF c' ≠ ⊥ → (∀ P, GlobalTheory.Hk3.Good R A.μ0 P → Formalism.DivisionValues.conjPl P ≠ P → ∀ k ≤ (Yc D 0).rank, c P (dualLab (splitLab (Yc D 0).rank k)) = c' P (dualLab (splitLab (Yc D 0).rank k))) → ∀ P, GlobalTheory.Hk3.Good R A.μ0 P → Formalism.DivisionValues.conjPl P ≠ P → ∀ d, GlobalTheory.Hk3.IsLab (Yc D 0) P d → c P (dualLab d) = c' P (dualLab d) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC SF hSF c c' hc hc' hs P hP hcP
  obtain ⟨-, hgood, hoff, -⟩ := GlobalTheory.T.theta_lift_levels_good_primes_properties R F hC.lev
  obtain ⟨n, hβ⟩ := hC.lev.βY 0 (by have := D.R.two_le_m; omega)
  have hlev := fun (P : Pl D.host.E) (hP : Good R A.μ0 P) =>
    GlobalTheory.T.level_operators_at_prime_off_level_datum (Yc D 0) (R.βY 0) (R.ΛY 0) ((D.host.g 0 * D.host.g 1) ^ n) (R.dat0 R.triv) hβ P
      (by
        rw [Nat.cast_pow]
        exact fun h => (hgood A.μ0 P hP).1 (P.isPrime.mem_of_pow_mem _ h))
      (by
        intro PP hPP
        refine hP PP (hPP.imp id ?_)
        intro h
        exact absurd h (Finset.notMem_empty _))
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc
  obtain ⟨x', hx', hx0'⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc'
  have inj : Function.Injective R.HE.e := hC.models.HE.1
  have hu : R.HE.e x ≠ 0 := fun h => hx0 (inj (by rw [h, map_zero]))
  have hu' : R.HE.e x' ≠ 0 := fun h => hx0' (inj (by rw [h, map_zero]))
  have hp := (LabDet.mem_partFull _ _ _ _ _ _ _).1 (Submodule.mem_comap.1 hx)
  have hp' := (LabDet.mem_partFull _ _ _ _ _ _ _).1 (Submodule.mem_comap.1 hx')
  have hP' : Good R A.μ0 (Formalism.DivisionValues.conjPl P) := (hgood _ P hP).2.1
  have hcc : Formalism.DivisionValues.conjPl (Formalism.DivisionValues.conjPl P) = P := Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl P
  exact eq_of_split (rRep (R.MY 0)) P hcP _ _ hu hu'
    (fun k hk => mult_lev _ _ _ _ _ hp.1 k ((hlev P hP).1 k hk).1 ((hlev P hP).1 k hk).2)
    (fun k hk => mult_lev _ _ _ _ _ hp'.1 k ((hlev P hP).1 k hk).1 ((hlev P hP).1 k hk).2)
    (fun d => c P (dualLab d)) (fun d => c' P (dualLab d))
    (fun d => c (Formalism.DivisionValues.conjPl P) (dualLab d)) (fun d => c' (Formalism.DivisionValues.conjPl P) (dualLab d))
    (fun d hd => by
      rw [opOf_single, sum_rRep]
      exact hp.2 _ _ _ (((hlev P hP).2.1 SF d _).2 ⟨(hoff SF hSF P).2 hP, sphOp_rep hd⟩))
    (fun d hd => by
      rw [opOf_single, sum_rRep]
      exact hp'.2 _ _ _ (((hlev P hP).2.1 SF d _).2 ⟨(hoff SF hSF P).2 hP, sphOp_rep hd⟩))
    (fun d hd => by
      rw [opOf_single, sum_rRep]
      exact hp.2 _ _ _ (((hlev _ hP').2.1 SF d _).2 ⟨(hoff SF hSF _).2 hP', sphOp_rep hd⟩))
    (fun d hd => by
      rw [opOf_single, sum_rRep]
      exact hp'.2 _ _ _ (((hlev _ hP').2.1 SF d _).2 ⟨(hoff SF hSF _).2 hP', sphOp_rep hd⟩))
    (hs P hP hcP) (hs _ hP' (by rw [hcc]; exact fun h => hcP h.symm))

end GlobalTheory.Hk3.LabDetRows

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Hk3.SplitLabels

open GlobalTheory.Hk3 GlobalTheory.Hk3.LabDet

theorem evC_single_lab {D : D7} (V : HSp D) (P : Pl D.host.E) (a : List ℤ → ℂ) (d : List ℤ) (hd : IsLab V P d) :
    evC V P a (Finsupp.single d 1) = a d := by
  unfold evC
  rw [Finsupp.sum_single_index (by simp), if_pos hd, one_mul]

theorem eq_of_split_vec : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (t : T) (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ R.HE.H), (∀ P, GlobalTheory.Hk3.Good R t P → ∀ c x, R.HE.e (h P c x) = postOn (R.MY 0) (GlobalTheory.Hk3.hk (Yc D 0) P c) (R.HE.e x)) → ∀ P, GlobalTheory.Hk3.Good R t P → Formalism.DivisionValues.conjPl P ≠ P → ∀ (c : Pl D.host.E → List ℤ → ℂ) (x w : R.HE.H), x ≠ 0 → (∀ P', GlobalTheory.Hk3.Good R t P' → ∀ cc, h P' cc x = GlobalTheory.Hk3.evC (Yc D 0) P' (fun d => c P' (dualLab d)) cc • x) → (∀ k ≤ (Yc D 0).rank, h P (Finsupp.single (splitLab (Yc D 0).rank k) 1) w = GlobalTheory.Hk3.evC (Yc D 0) P (fun d => c P (dualLab d)) (Finsupp.single (splitLab (Yc D 0).rank k) 1) • w ∧ h (Formalism.DivisionValues.conjPl P) (Finsupp.single (splitLab (Yc D 0).rank k) 1) w = GlobalTheory.Hk3.evC (Yc D 0) (Formalism.DivisionValues.conjPl P) (fun d => c (Formalism.DivisionValues.conjPl P) (dualLab d)) (Finsupp.single (splitLab (Yc D 0).rank k) 1) • w) → ∀ d, GlobalTheory.Hk3.IsLab (Yc D 0) P d → h P (Finsupp.single d 1) w = c P (dualLab d) • w := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC t h hh P hP hcP c x w hx0 hxe hw d hd
  obtain ⟨-, hgood, -, -⟩ := GlobalTheory.T.theta_lift_levels_good_primes_properties R F hC.lev
  have hPA : Good R A.μ0 P := (hgood t P hP).2.2
  have hPc : Good R t (Formalism.DivisionValues.conjPl P) := (hgood t P hP).2.1
  obtain ⟨n, hβ⟩ := hC.lev.βY 0 (lt_of_lt_of_le two_pos D.R.two_le_m)
  have hlev := GlobalTheory.T.level_operators_at_prime_off_level_datum (Yc D 0) (R.βY 0) (R.ΛY 0) _ (R.dat0 R.triv) hβ P
    (by rw [Nat.cast_pow]; exact fun hm => (hgood _ P hPA).1 (P.isPrime.mem_of_pow_mem n hm))
    (fun PP hPP => hPA PP (hPP.imp id fun h => absurd h (Finset.notMem_empty _)))
  have inj : Function.Injective R.HE.e := hC.models.HE.1
  have hmem : ∀ y, R.HE.e y ∈ Mult R.θ (R.MY 0) (levG _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) :=
    fun y => goodPart_le _ _ _ _ _ (hC.models.HE.2.1 ▸ LinearMap.mem_range_self _ y)
  have hfix : ∀ y, ∀ k ∈ hyp (Yc D 0) P, rRep (R.MY 0) k (R.HE.e y) = R.HE.e y := fun y k hk =>
    mult_lev _ _ _ _ _ (hmem y) k (hlev.1 k hk).1 (hlev.1 k hk).2
  have hop : ∀ P', Good R t P' → ∀ e y, opOf (rRep (R.MY 0)) P' (Finsupp.single e 1) (R.HE.e y) =
      R.HE.e (h P' (Finsupp.single e 1) y) := by
    intro P' hP' e y
    rw [opOf_single, sum_rRep, hh P' hP', GlobalTheory.Hk3.OpsRows.hk_single]
    rfl
  have hu : R.HE.e x ≠ 0 := fun h0 => hx0 (inj (by rw [h0, map_zero]))
  obtain ⟨a, ha, hae⟩ := GlobalTheory.SplitGen.gen_split (Yc D 0) P hcP (MMap (R.MY 0)) (rRep (R.MY 0)) d
  obtain ⟨l, h1, h2⟩ := adjoin_common _ (R.HE.e x) (R.HE.e w) (by
    rintro y ⟨k, hk, rfl | rfl⟩
    · refine ⟨evC (Yc D 0) P (fun d => c P (dualLab d)) (Finsupp.single (splitLab (Yc D 0).rank k) 1), ?_, ?_⟩
      · rw [hop P hP, hxe P hP, map_smul]
      · rw [hop P hP, (hw k hk).1, map_smul]
    · have hc := (GlobalTheory.T.sphericalHecke_conjPlace_eq_dualLabel (Yc D 0) P).2.2 (Finsupp.single (splitLab (Yc D 0).rank k) 1) _ (rRep (R.MY 0))
      have hdc : dualC (Finsupp.single (splitLab (Yc D 0).rank k) 1) =
          Finsupp.single (dualLab (splitLab (Yc D 0).rank k)) 1 := by
        unfold dualC
        rw [Finsupp.mapDomain_single]
      rw [hdc] at hc
      rw [← hc _ (hfix x), ← hc _ (hfix w)]
      refine ⟨evC (Yc D 0) (Formalism.DivisionValues.conjPl P) (fun d => c (Formalism.DivisionValues.conjPl P) (dualLab d))
        (Finsupp.single (splitLab (Yc D 0).rank k) 1), ?_, ?_⟩
      · rw [hop _ hPc, hxe _ hPc, map_smul]
      · rw [hop _ hPc, (hw k hk).2, map_smul]) a ha
  rw [hae _ (hfix x), hop P hP, hxe P hP, evC_single_lab _ _ _ _ hd, map_smul] at h1
  have hl : l = c P (dualLab d) := (smul_left_injective ℂ hu h1).symm
  rw [hae _ (hfix w), hop P hP, hl, ← map_smul] at h2
  exact inj h2

end GlobalTheory.Hk3.SplitLabels

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

theorem _root_.GlobalTheory.T.exists_equiv_heckeKernelScheme_points_heckeKernels : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (P : Ideal (𝓞 E)) (p i : ℕ) (Z : KerScheme Xo P p i), admitted l P p → ∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ Xo.X), ∃ e : {w : Sp k ⟶ Z.Hk // w ≫ Z.π₁ = y} ≃ {C : Subgroup (Over.mk y ⟶ Xo.univ.t.G) // Xo.univ.t.HeckeKer (Over.mk y) Dw P p i C}, ∀ w C, Z.Carries w.1 y C ↔ C = (e w).1 := by
  first | exact @GlobalTheory.HeckeEx.exists_equiv_carries | exact GlobalTheory.HeckeEx.exists_equiv_carries | (intros; apply GlobalTheory.HeckeEx.exists_equiv_carries <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.cuspMultiplicity_mem_sphericalEigenPart_of_value_params : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, MetEx D → ForStage D fun c _ s => ∀ (u : s.CC c) w B, PiLocalization₂.val u w ≠ 0 → ParFun c s (PiLocalization₂.val u w) B → ∃ e : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ, PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) ∈ partFull c.θ s.M (s.J : Set (GA D s.V)) 1 c.S e := by
  first | exact @GlobalTheory.EvenOnto.ValPart.valPart_mem | exact GlobalTheory.EvenOnto.ValPart.valPart_mem | (intros; apply GlobalTheory.EvenOnto.ValPart.valPart_mem <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.evenRankThetaChainLift_surjective_of_adjoint_nonzero : ∀ D : D7, FinDim D → MetEx D → EigSpan D → ParIndep D → ParBound D → StepUp D → OntoAll D := by
  first | exact @GlobalTheory.EvenOnto.ontoAll_of | exact GlobalTheory.EvenOnto.ontoAll_of | (intros; apply GlobalTheory.EvenOnto.ontoAll_of <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.evenThetaStep_semilocalZeta_ne_zero_of_real : ∀ D : D7, MetEx D → RealZeta D → ZetaNe D := by
  first | exact @GlobalTheory.EvenOnto.ZetaNeProof.zetaNe_of_real | exact GlobalTheory.EvenOnto.ZetaNeProof.zetaNe_of_real | (intros; apply GlobalTheory.EvenOnto.ZetaNeProof.zetaNe_of_real <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.evenRankChain_eigenPart_has_parameters : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, ForStage D fun c _ s => ∀ (u : s.CC c) (e : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ), PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) ∈ partFull c.θ s.M (s.J : Set (GA D s.V)) 1 c.S e → (u ≠ 0 → ∃ B, IsPar u B) ∧ ∀ w B, PiLocalization₂.val u w ≠ 0 → ParFun c s (PiLocalization₂.val u w) B → IsPar u B := by
  first | exact @GlobalTheory.EvenOnto.partPar | exact GlobalTheory.EvenOnto.partPar | (intros; apply GlobalTheory.EvenOnto.partPar <;> assumption)
end
