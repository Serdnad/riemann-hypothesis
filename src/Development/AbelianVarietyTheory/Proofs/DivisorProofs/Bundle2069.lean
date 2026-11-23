module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1874
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1989
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1968
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralPointsIndicatorIsVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1770
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1902
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1944
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHyperbolicPlaneSplitHermitianLatticeSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenContinuousInverse
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1897
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2021
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2022
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle250
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVacuumTransverseLagrangianLocalField
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1781
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle077
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle266
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1898
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1991
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1910
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFinsetSelfDualClassesHerm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2035
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal

noncomputable section

namespace GlobalTheory.ThK.ModelLocInt

open scoped Classical
open Filter GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem incM_one (m : ℕ) : incM F (1 : Matrix (Fin m) (Fin m) E) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem heis_loc {B : Base F E} {M M₁ : Model σ X W} (hM : M.IsGood B.ψ) (hM₁ : M₁.IsGood B.ψ)
    {e : Fn F n d →ₗ[ℂ] Fn F n d} (he : IsEv B M M₁ 1 1 ∅ e)
    (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d))
    (ev : ∀ v : Pl (F := F), ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d → Fv F v) → ℂ) (hei : ei ≠ 0)
    (hvm : ∀ v, ev v (M.vac v) = M₁.vac v ∧ (SB _).map (ev v) = SB _)
    (hloc : ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) →
      e (pure f φ) = pure (ei f) fun v => ev v (φ v))
    (v : Pl (F := F)) (z : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (φ : (Fin n × Fin d → Fv F v) → ℂ) (hφ : φ ∈ SB _)
    (φ₁ : (Fin n × Fin d → Fv F v) → ℂ) (hφ₁ : φ₁ ∈ SB _) (hA : Acts (evFin F v) (M.co.rho B.ψ z) φ φ₁)
    (χ₁ : (Fin n × Fin d → Fv F v) → ℂ) (hA₁ : Acts (evFin F v) (M₁.co.rho B.ψ z) (ev v φ) χ₁) :
    ev v φ₁ = χ₁ := by
  have hpre : ∀ w, ∃ ψ ∈ SB (Fin n × Fin d → Fv F w), ev w ψ = GlobalTheory.ThK.EvUniq.LocFin.ind w := fun w => by
    have h := GlobalTheory.StdVacuum.indicator_mem_SB (κ := Fin n × Fin d) w
    rw [← (hvm w).2] at h
    obtain ⟨ψ, hψ, e⟩ := Submodule.mem_map.mp h
    exact ⟨ψ, hψ, e⟩
  let ψs : ∀ w : Pl (F := F), (Fin n × Fin d → Fv F w) → ℂ := fun w =>
    if M₁.vac w = GlobalTheory.ThK.EvUniq.LocFin.ind w then M.vac w else (hpre w).choose
  have hψSB : ∀ w, ψs w ∈ SB _ := fun w => by
    by_cases h : M₁.vac w = GlobalTheory.ThK.EvUniq.LocFin.ind w
    · simp only [ψs, if_pos h]; exact (hM.vac w).1
    · simp only [ψs, if_neg h]; exact (hpre w).choose_spec.1
  have hψev : ∀ w, ev w (ψs w) = GlobalTheory.ThK.EvUniq.LocFin.ind w := fun w => by
    by_cases h : M₁.vac w = GlobalTheory.ThK.EvUniq.LocFin.ind w
    · simp only [ψs, if_pos h]; rw [(hvm w).1, h]
    · simp only [ψs, if_neg h]; exact (hpre w).choose_spec.2
  have hψM : ∀ᶠ w in cofinite, ψs w = M.vac w := by
    filter_upwards [hM₁.std] with w hw
    simp only [ψs, if_pos hw]
  have hψind : ∀ᶠ w in cofinite, ψs w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := by
    filter_upwards [hψM, hM.std] with w h1 h2
    rw [h1, h2]
  obtain ⟨f, hf⟩ : ∃ f, ei f ≠ 0 := by
    obtain ⟨f, hf⟩ := DFunLike.ne_iff.mp hei
    exact ⟨f, by simpa using hf⟩
  have hind : ∀ᶠ w in cofinite, (GlobalTheory.ThK.EvUniq.LocFin.ind (κ := Fin n × Fin d) w) =
      Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := Eventually.of_forall fun _ => rfl
  obtain ⟨ρ, hρ, hρt⟩ := GlobalTheory.PureFactor.exists_rest_factor v f ψs hψind
  obtain ⟨ρ₁, hρ₁, hρt₁⟩ := GlobalTheory.PureFactor.exists_rest_factor v (ei f) _ hind
  have hRest : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), Rest (evFin F v) φ ρ := fun φ hφ => by
    refine ⟨hρ, ?_⟩
    rw [hρt φ]
    refine GlobalTheory.TensUniq.pure_mem_schA f _ (fun w => ?_) (GlobalTheory.PureFactor.update_eventually ψs v φ hψind)
    by_cases hw : w = v
    · subst hw; rw [Function.update_self]; exact hφ
    · rw [Function.update_of_ne hw]; exact hψSB w
  have hRest₁ : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), Rest (evFin F v) φ ρ₁ := fun φ hφ => by
    refine ⟨hρ₁, ?_⟩
    rw [hρt₁ φ]
    refine GlobalTheory.TensUniq.pure_mem_schA (ei f) _ (fun w => ?_) (GlobalTheory.PureFactor.update_eventually _ v φ hind)
    by_cases hw : w = v
    · subst hw; rw [Function.update_self]; exact hφ
    · rw [Function.update_of_ne hw]; exact GlobalTheory.StdVacuum.indicator_mem_SB w
  have key : ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      e (tens (evFin F v) φ ρ) = tens (evFin F v) (ev v φ) ρ₁ := fun φ hφ => by
    rw [hρt φ, hρt₁ (ev v φ)]
    have hSB : ∀ w, Function.update ψs v φ w ∈ SB _ := fun w => by
      by_cases hw : w = v
      · subst hw; rw [Function.update_self]; exact hφ
      · rw [Function.update_of_ne hw]; exact hψSB w
    have hcof : ∀ᶠ w in cofinite, Function.update ψs v φ w = M.vac w := by
      filter_upwards [hψM, eventually_cofinite_ne v] with w h1 h2
      rw [Function.update_of_ne h2, h1]
    rw [hloc f _ hSB hcof]
    congr 1
    funext w
    by_cases hw : w = v
    · subst hw; rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hw, Function.update_of_ne hw, hψev w]
  have canc := GlobalTheory.ThK.EvUniq.LocFin.cancel v (ei f) hf ρ₁ hρ₁ hρt₁
  have h1 := he.Heisenberg₂ z _ (hRest φ hφ).2
  rw [incM_one, incM_one, Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one] at h1
  rw [hA ρ (hRest φ hφ), key φ₁ hφ₁, key φ hφ] at h1
  have hevφ : ev v φ ∈ SB _ := by
    rw [← (hvm v).2]
    exact Submodule.mem_map_of_mem hφ
  rw [hA₁ ρ₁ (hRest₁ _ hevφ)] at h1
  exact canc _ _ h1

def ptAt (M : Model σ X W) (v : Pl (F := F)) (w : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)) :
    Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
  M.co.e.symm (fun k => GlobalTheory.LatVac.liftV v (w.1 k), fun k => GlobalTheory.LatVac.liftV v (w.2 k))

theorem at_ptAt (M : Model σ X W) (v : Pl (F := F)) (w : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)) :
    At (evFin F v) (ptAt M v w) := by
  intro a ha
  unfold ptAt
  rw [← LinearEquiv.map_smul, ← M.co.e.symm.map_zero]
  congr 1
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
  · exact GlobalTheory.LatVac.at_liftV v _ a ha
  · exact GlobalTheory.LatVac.at_liftV v _ a ha

theorem locCo_ptAt (M : Model σ X W) (v : Pl (F := F)) (w : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)) :
    GlobalTheory.LatVac.locCo M.co v (ptAt M v w) = w := by
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;>
    simp [ptAt, GlobalTheory.LatVac.locCo, GlobalTheory.LatVac.evFin_liftV]

end GlobalTheory.ThK.ModelLocInt


open GlobalTheory.ThK.ModelLocInt in
theorem GlobalTheory.ThK.ModelLocInt.exists_loc_schr : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d,
    IsEv B M M₁ 1 1 ∅ e →
    ∀ (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d))
      (ev : ∀ v : Pl (F := F), ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d → Fv F v) → ℂ), ei ≠ 0 →
      (∀ v, ev v (M.vac v) = M₁.vac v ∧ (SB _).map (ev v) = SB _) →
      (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
        e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
      ∀ (v : Pl (F := F)) [Invertible (2 : Fv F v)], ∃ ψv : AddChar (Fv F v) ℂ, Continuous ψv ∧ ψv ≠ 1 ∧
        ∃ A : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) → (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v),
          ∀ w, ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ev v (schr ψv w φ) = schr ψv (A w) (ev v φ) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP M₁ hM₁ e he ei ev hei hvm hloc v _
  obtain rfl : ‹Invertible (2 : Fv F v)› = GlobalTheory.VacAny.invTwoV v := Subsingleton.elim _ _
  have hψe : GlobalTheory.LatVac.psiAt B.ψ v = GlobalTheory.VacAny.psiV B.ψ v :=
    by
    ext t
    exact (GlobalTheory.LatVac.psiAt_apply B.ψ v t).trans (GlobalTheory.VacAny.psiV_eq_psiLoc B.ψ v t).symm
  have hψc : Continuous (GlobalTheory.LatVac.psiAt B.ψ v) := by
    rw [hψe]; exact GlobalTheory.VacAny.continuous_psiV hP.base.std.1 v
  refine ⟨GlobalTheory.LatVac.psiAt B.ψ v, hψc, by rw [hψe]; exact GlobalTheory.PsiNontriv.psiV_ne_one B.ψ hP.base.std v,
    fun w => GlobalTheory.LatVac.locCo M₁.co v (ptAt M v w), fun w φ hφ => ?_⟩
  have hA := GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v (ptAt M v w) (at_ptAt M v w) φ
  rw [locCo_ptAt] at hA
  have hA₁ := GlobalTheory.VacBridge.rho_acts_locCo M₁.co B.ψ v (ptAt M v w) (at_ptAt M v w) (ev v φ)
  exact heis_loc hP.good hM₁ he ei ev hei hvm hloc v (ptAt M v w) φ hφ _
    (GlobalTheory.SchrSBFin.schr_mem_SB v _ hψc w φ hφ) hA _ hA₁
end
end

section

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.exists_hyperbolicPlane_split_hermitianLatticeSpace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (n n₁ : ℕ), n = n₁ + 2 → 1 ≤ n₁ → ∀ (Y : Spc F E n) (r s : ℕ), 1 ≤ r → 1 ≤ s →
    Y.IsHerm σ B r s → ∀ i₀ i₁ : ℕ, i₀ < i₁ → i₁ < n → ∃ (Y' : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁),
      (GlobalTheory.ThK.reS Y Y').IsHerm σ B r s ∧ Y₁.IsHerm σ B (r - 1) (s - 1) ∧ H.IsAdapted σ B (GlobalTheory.ThK.reS Y Y') Y₁ i₀ i₁ := by
  first | exact @GlobalTheory.KTowerPlane.exists_hyperbolic_split | exact GlobalTheory.KTowerPlane.exists_hyperbolic_split | (intros; apply GlobalTheory.KTowerPlane.exists_hyperbolic_split <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal


theorem _root_.GlobalTheory.T.weil_eigen_continuous_inverse : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d,
    IsEv B M M₁ 1 1 ∅ e →
    ∀ (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d))
      (ev : ∀ v : Pl (F := F), ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d → Fv F v) → ℂ), ei ≠ 0 →
      (∀ v, ev v (M.vac v) = M₁.vac v ∧ (SB _).map (ev v) = SB _) →
      (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
        e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
      ∀ [Invertible (2 : mixedEmbedding.mixedSpace F)], ∃ ψ : AddChar (mixedEmbedding.mixedSpace F) ℂ,
        (∀ a, ψ a = Complex.exp (-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) a : ℝ))) ∧
        ∃ A : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F) →
            (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F),
          ∀ w (f g : SInf F (Fin n × Fin d)), (g : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) = schr ψ w f →
            (ei g : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) = schr ψ (A w) (ei f) := by
  first | exact @GlobalTheory.ArchIntertw.ei_schr | exact GlobalTheory.ArchIntertw.ei_schr | (intros; apply GlobalTheory.ArchIntertw.ei_schr <;> assumption)
end

section

open scoped Pointwise nonZeroDivisors
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section
namespace GlobalTheory.FunObj.EigUnit

theorem conj_smul_smul (D : D7) (I : Ideal (𝓞 D.host.E)) : D.host.conj • D.host.conj • I = I := by
  have h2 : D.host.conj * D.host.conj = 1 := AlgEquiv.ext fun x => VacMove.conj_conj D x
  rw [smul_smul, h2, one_smul]

theorem conj_smul_mul (D : D7) (I J : Ideal (𝓞 D.host.E)) :
    D.host.conj • (I * J) = D.host.conj • I * D.host.conj • J := by
  simp only [Ideal.pointwise_smul_def, Ideal.map_mul]

theorem conj_smul_mono (D : D7) {I J : Ideal (𝓞 D.host.E)} (h : I ≤ J) : D.host.conj • I ≤ D.host.conj • J := by
  simp only [Ideal.pointwise_smul_def]; exact Ideal.map_mono h

theorem coprime_rep (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (h𝔪 : 𝔪 ≠ ⊥) :
    ∃ 𝔫 : Ideal (𝓞 D.host.E), 𝔫 ≠ ⊥ ∧ IsCoprime 𝔫 (D.host.conj • 𝔫) ∧
      𝔪 * D.host.conj • 𝔫 = 𝔫 * D.host.conj • 𝔪 := by
  induction 𝔪 using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl h𝔪
  | h₂ x hx =>
    rw [Ideal.isUnit_iff] at hx
    subst hx
    exact ⟨⊤, top_ne_bot, by rw [Ideal.isCoprime_iff_sup_eq]; exact top_sup_eq _, rfl⟩
  | h₃ x p hx hp ih =>
    obtain ⟨n, hn, hcop, hxn⟩ := ih hx
    have hpb : p ≠ ⊥ := hp.ne_zero
    have hpP : p.IsPrime := Ideal.isPrime_of_prime hp
    have hpM : p.IsMaximal := hpP.isMaximal hpb
    have hsb : D.host.conj • p ≠ ⊥ := GlobalTheory.BotPairSmall.conj_smul_ne_bot D hpb
    have hsM : (D.host.conj • p).IsMaximal := (Ideal.IsPrime.smul D.host.conj).isMaximal hsb
    by_cases hfix : D.host.conj • p = p
    · refine ⟨n, hn, hcop, ?_⟩
      rw [conj_smul_mul, hfix, mul_assoc, hxn]
      ring
    by_cases hdiv : n ≤ D.host.conj • p
    · obtain ⟨n', rfl⟩ := Ideal.dvd_iff_le.2 hdiv
      refine ⟨n', fun h0 => hn (by rw [h0, Ideal.mul_bot]), ?_, ?_⟩
      · rw [conj_smul_mul] at hcop
        exact (hcop.of_mul_left_right).of_mul_right_right
      · simp only [conj_smul_mul, conj_smul_smul] at hxn ⊢
        calc p * x * D.host.conj • n' = x * p * D.host.conj • n' := by ring
          _ = D.host.conj • p * n' * D.host.conj • x := by rw [mul_assoc, hxn]
          _ = n' * (D.host.conj • p * D.host.conj • x) := by ring
    · refine ⟨p * n, mul_ne_zero hpb hn, ?_, ?_⟩
      · have hnot : ¬ D.host.conj • n ≤ p := fun h => hdiv (by
          have := conj_smul_mono D h
          rwa [conj_smul_smul] at this)
        have c1 : IsCoprime p (D.host.conj • p) := by
          rw [Ideal.isCoprime_iff_sup_eq]
          by_contra hne
          have h3 : p = p ⊔ D.host.conj • p := hpM.eq_of_le hne le_sup_left
          exact hfix (hsM.eq_of_le hpM.ne_top (le_sup_right.trans h3.ge))
        have c2 : IsCoprime p (D.host.conj • n) := by
          rw [Ideal.isCoprime_iff_sup_eq]
          by_contra hne
          have h3 : p = p ⊔ D.host.conj • n := hpM.eq_of_le hne le_sup_left
          exact hnot (le_sup_right.trans h3.ge)
        have c3 : IsCoprime n (D.host.conj • p) := by
          rw [Ideal.isCoprime_iff_sup_eq, sup_comm]
          by_contra hne
          have h3 : D.host.conj • p = D.host.conj • p ⊔ n := hsM.eq_of_le hne le_sup_left
          exact hdiv (le_sup_right.trans h3.ge)
        rw [conj_smul_mul]
        exact IsCoprime.mul_left (IsCoprime.mul_right c1 c2) (IsCoprime.mul_right c3 hcop)
      · rw [conj_smul_mul, conj_smul_mul]
        calc p * x * (D.host.conj • p * D.host.conj • n) = p * D.host.conj • p * (x * D.host.conj • n) := by ring
          _ = p * D.host.conj • p * (n * D.host.conj • x) := by rw [hxn]
          _ = p * n * (D.host.conj • p * D.host.conj • x) := by ring

theorem zeroAt_zero' (D : D7) (q : ℕ) : ZeroAt D q 0 :=
  fun _ => ⟨1, one_pos, Nat.coprime_one_left q, 0, zero_mem _, by simp⟩

theorem suppSplit_one' (D : D7) (N : ℕ) : SuppSplit D ((1 : GA D N) : GL (Fin N) (AE D)) :=
  fun q _ _ i j => by rw [OneMemClass.coe_one, Units.val_one, sub_self]; exact zeroAt_zero' D q

theorem skewLat_eq (D : D7) {𝔪 𝔫 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) (h𝔫 : 𝔫 ≠ ⊥)
    (h : 𝔪 * D.host.conj • 𝔫 = 𝔫 * D.host.conj • 𝔪) (N : ℕ) : skewLat D 𝔪 N = skewLat D 𝔫 N := by
  have e : ((𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) /
      ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)) =
      ((𝔫 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) /
      ((D.host.conj • 𝔫 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)) := by
    rw [div_eq_div_iff (FractionalIdeal.coeIdeal_ne_zero.2 (GlobalTheory.BotPairSmall.conj_smul_ne_bot D h𝔪))
      (FractionalIdeal.coeIdeal_ne_zero.2 (GlobalTheory.BotPairSmall.conj_smul_ne_bot D h𝔫)), ← FractionalIdeal.coeIdeal_mul,
      ← FractionalIdeal.coeIdeal_mul, h]
  unfold skewLat
  rw [e]

theorem eig_unit : ∀ (D : D7) (δ : ℂ), Crv D ⊤ δ → ∀ {a d : ℕ} (e0 : VC D a d → ℂ), e0 ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d) → ∀ (W : WeilO D ⊤ δ a d e0) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∀ (r : GA D a), r ∈ intG D a → ∀ c : ℂ, W.Om r 1 e0 = c • e0 → W.Om r 1 (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0) = c • Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0 := by
  intro D δ hc a d e0 he W 𝔪 h𝔪 r hr c hrc
  have h1 := (GlobalTheory.InducedType.induced_type D).1
  have hT := VacMove.vac_TT h1 hc he
  obtain ⟨𝔫, h𝔫, hcop, hmn⟩ := coprime_rep D 𝔪 h𝔪
  rw [skewLat_eq D h𝔪 h𝔫 hmn d]
  obtain ⟨g', x', hg's, hg'm, hx'q, hx'd⟩ := GlobalTheory.T.exists_splitSupported_unitary_moving_to_selfDualSkewLattice D 𝔫 h𝔫 hcop d
  have hJ : W.Om 1 g' e0 = ((W.chV.f x' ^ W.ep * W.chV'.f 1 ^ W.ep' : ℂˣ) : ℂ) •
      Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔫 d)) e0 := by
    rw [W.split 1 g' 1 x' (stdL D a) (skewLat D 𝔫 d) (suppSplit_one' D a) hg's
      (fun q hq hi => ⟨by simpa using zeroAt_zero' D q, hx'q q hq hi⟩) (by simp) hx'd (VacMove.moves_one D a) hg'm]
    rfl
  have hc0 : ((W.chV.f x' ^ W.ep * W.chV'.f 1 ^ W.ep' : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hJe : Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔫 d)) e0 =
      ((W.chV.f x' ^ W.ep * W.chV'.f 1 ^ W.ep' : ℂˣ) : ℂ)⁻¹ • W.Om 1 g' e0 := by
    rw [hJ, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have e1 := W.mul r 1 1 g' e0 hT
  have e2 := W.mul 1 r g' 1 e0 hT
  rw [mul_one, one_mul] at e1
  rw [one_mul, mul_one, hrc, W.smul _ _ _ _ hT] at e2
  rw [hJe, W.smul _ _ _ _ (W.maps 1 g' e0 hT), ← e1, e2, smul_comm]

end GlobalTheory.FunObj.EigUnit
end
end

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open GlobalTheory.FunObj.SqNum GlobalTheory.NormSum


theorem _root_.GlobalTheory.T.exists_maxLevel_unitary_congr_mod_ideal : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → 𝔪 ⊔ D.host.conj • 𝔪 = ⊤ → ∀ (N : ℕ)
    (g : Matrix (Fin N) (Fin N) (𝓞 D.host.E)), IsUnit (g.map (Ideal.Quotient.mk 𝔪)).det →
      ∃ k : GA D N, k ∈ intG D N ∧ ∀ i j : Fin N,
        ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j - inc D ((g i j : 𝓞 D.host.E) : D.host.E) ∈ hatId D 𝔪 := by
  first | exact @GlobalTheory.MaxLevelLift.exists_intG_cong | exact GlobalTheory.MaxLevelLift.exists_intG_cong | (intros; apply GlobalTheory.MaxLevelLift.exists_intG_cong <;> assumption)
end

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)


theorem _root_.GlobalTheory.T.exists_idempotent_powerLimit_congruentOne : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∀ y ∈ OhE D, y - 1 ∈ hatId D 𝔪 → ∃ g ∈ OhE D, y * g * (y * g) = y * g ∧ y * g - 1 ∈ hatId D 𝔪 := by
  first | exact @GlobalTheory.PowIdem.exists_idem | exact GlobalTheory.PowIdem.exists_idem | (intros; apply GlobalTheory.PowIdem.exists_idem <;> assumption)
end

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)


theorem _root_.GlobalTheory.T.skewIdealLattice_point_rational_normKills : ∀ (D : D7) (δ : ℂ), Crv D ⊤ δ → ∀ (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∀ {a d : ℕ}, ∀ y ∈ (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)), ∃ z : Matrix (Fin d) (Fin a) D.host.E, y = pt D (tor0 D ⊤ δ) δ z ∧ Ideal.absNorm 𝔪 • pt D (tor0 D ⊤ δ) δ z ∈ (La0 D (tor0 D ⊤ δ) a d) := by
  first | exact @GlobalTheory.FunObj.StdDatum.SkewPoints.points | exact GlobalTheory.FunObj.StdDatum.SkewPoints.points | (intros; apply GlobalTheory.FunObj.StdDatum.SkewPoints.points <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
open GlobalTheory.PureMatch GlobalTheory.SquareFlipReach ValuativeRel


theorem _root_.GlobalTheory.T.schwartzBruhat_blockScaled_hasLatticeDepth : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (A' C : Type) [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C] (ϖ : kˣ) (P : Finset C) (Ψ : Matrix A' C k → ℂ),
    Ψ ∈ GlobalTheory.WeilM.SB (Matrix A' C k) → IsUnif ϖ → ∃ M : ℕ, ∀ n, 2 * M ≤ n →
      HasDepth ϖ n (blockLat ϖ n P) (fun Y => Ψ (Y * diagonal (fun col => if col ∈ P then ((ϖ ^ M : kˣ) : k) else (((ϖ ^ M)⁻¹ : kˣ) : k)))) := by
  first | exact @GlobalTheory.PurityDepth.hasDepth_scaled | exact GlobalTheory.PurityDepth.hasDepth_scaled | (intros; apply GlobalTheory.PurityDepth.hasDepth_scaled <;> assumption)
end

section

open ValuativeRel Matrix

theorem _root_.GlobalTheory.T.exists_vacuum_transverseLagrangian_localField : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    [Invertible (2 : k)] {κ : Type} [Fintype κ] {n d : ℕ} (ψ0 : AddChar k ℂ), Continuous ψ0 →
    (∀ x : k, (∀ y ∈ 𝒪[k], ψ0 (x * y) = 1) ↔ x ∈ 𝒪[k]) →
    ∀ (wT wM : Matrix (Fin n) (Fin d) k →+ (κ → k) × (κ → k)),
    (∀ Y Y', (wT Y).1 ⬝ᵥ (wT Y').2 - (wT Y').1 ⬝ᵥ (wT Y).2 = 0) →
    (∀ z z', (wM z).1 ⬝ᵥ (wM z').2 - (wM z').1 ⬝ᵥ (wM z).2 = 0) →
    (∀ Y z, (wT Y).1 ⬝ᵥ (wM z).2 - (wM z).1 ⬝ᵥ (wT Y).2 = ∑ i, ∑ j, Y i j * z i j) →
    (∀ w, ∃ Y z, wT Y + wM z = w) →
    ∃ f₀ ∈ GlobalTheory.WeilM.SB (κ → k), f₀ ≠ 0 ∧
      (∀ u : Matrix (Fin n) (Fin d) k, (∀ r q, u r q ∈ 𝒪[k]) → GlobalTheory.WeilM.schr ψ0 (wT u) f₀ = f₀) ∧
      (∀ z : Matrix (Fin n) (Fin d) k, (∀ r q, z r q ∈ 𝒪[k]) → GlobalTheory.WeilM.schr ψ0 (wM z) f₀ = f₀) := by
  first | exact @GlobalTheory.LagVac.exists_vacuum | exact GlobalTheory.LagVac.exists_vacuum | (intros; apply GlobalTheory.LagVac.exists_vacuum <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport

namespace GlobalTheory.FrameTransport

theorem exists_finG_eq : ∀ {D : D7} (V : HSp D) (M : GL (Fin V.rank) (Lev.EAf D)), M ∈ UA D.sp.cm V.gram →
    ∃ g : GfC V, finG V g = M := by
  intro D V M hM
  obtain ⟨g0, hg0⟩ := GlobalTheory.FunObj.UA_le_range_finE V hM
  obtain ⟨k, k1, k2⟩ := GlobalTheory.UnitarySplit.ga_glue V 1 (finHom V g0) (one_mem _) (GlobalTheory.UnitarySplit.finHom_mem V g0)
  refine ⟨⟨k, MonoidHom.mem_ker.2 k1⟩, ?_⟩
  rw [← hg0]
  change Formalism.UG.bc (Lev.swapAE D) (finHom V k) = Formalism.UG.bc (Lev.swapAE D) (finHom V g0)
  rw [k2]

end GlobalTheory.FrameTransport

end
end
