module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle900
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1990
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle950
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1968
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralPointsIndicatorIsVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1770
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1191
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdicIntegersCompact.IsCompactAdicCompletionIntegers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntAFSmulMemLatOF
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle664
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1602
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1609
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle026
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1993
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1940
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

noncomputable section

open NumberField
open scoped Pointwise

namespace GlobalTheory.VacRead.SelfDual

open GlobalTheory.InertSign (IntE hE)

theorem intE_iff {D : Formalism.BasicNotions.D7} {e : D.host.E} : IntE D e ↔ e ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := Iff.rfl

theorem intE_gen (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E) (hn : (Ideal.absNorm cc : D.host.E) ≠ 0)
    (hs : GlobalTheory.NormExact.IsScale D cc r) {α₁ α₂ γ₁ γ₂ : D.host.E} (hα₁ : α₁ ∈ cE D cc) (hα₂ : α₂ ∈ cE D cc)
    (hγ₁ : γ₁ ∈ cE D D.host.ccK) (hγ₂ : γ₂ ∈ cE D D.host.ccK) :
    IntE D (r * D.host.conj α₁ * γ₁ / (Ideal.absNorm cc : D.host.E) *
      D.host.conj (r * D.host.conj α₂ * γ₂ / (Ideal.absNorm cc : D.host.E))) := by
  obtain ⟨o₁, h₁⟩ := (GlobalTheory.T.idealExtend_conj_mul_eq_absNorm D cc).1 α₁ hα₁ α₂ hα₂
  obtain ⟨o₂, h₂⟩ := (GlobalTheory.T.idealExtend_conj_mul_eq_absNorm D D.host.ccK).1 γ₂ hγ₂ γ₁ hγ₁
  unfold GlobalTheory.NormExact.IsScale at hs
  refine ⟨o₁ * o₂, ?_⟩
  simp only [map_div₀, map_mul, map_natCast, GlobalTheory.InertSign.conj_conj]
  change (o₁ : D.host.E) * (o₂ : D.host.E) = _
  field_simp
  linear_combination (exp := 1) (-(r * D.host.conj r) * (D.host.conj γ₂ * γ₁)) * h₁ +
    (-(r * D.host.conj r) * (Ideal.absNorm cc : D.host.E) * (o₁ : D.host.E)) * h₂ +
    (-((Ideal.absNorm cc : D.host.E) * (o₁ : D.host.E) * (o₂ : D.host.E))) * hs

def pairSpan (D : Formalism.BasicNotions.D7) (J : Submodule (𝓞 D.host.E) D.host.E) : Submodule (𝓞 D.host.E) D.host.E :=
  Submodule.span (𝓞 D.host.E) {t | ∃ u ∈ J, ∃ x ∈ J, t = u * D.host.conj x}

theorem conj_smul (D : Formalism.BasicNotions.D7) (c : 𝓞 D.host.E) (x : D.host.E) :
    D.host.conj (c • x) = D.host.conj (c : D.host.E) * D.host.conj x := by
  rw [Algebra.smul_def, map_mul]

theorem intE_coe (D : Formalism.BasicNotions.D7) (c : 𝓞 D.host.E) : IntE D (c : D.host.E) := ⟨c, rfl⟩

theorem intE_mul_conj (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E) (hn : (Ideal.absNorm cc : D.host.E) ≠ 0)
    (hs : GlobalTheory.NormExact.IsScale D cc r) {u x : D.host.E} (hu : u ∈ bInv D cc r) (hx : x ∈ bInv D cc r) :
    IntE D (u * D.host.conj x) := by
  unfold bInv at hu hx
  induction hu using Submodule.span_induction generalizing x with
  | mem g hg =>
    obtain ⟨α₁, hα₁, γ₁, hγ₁, rfl⟩ := hg
    induction hx using Submodule.span_induction with
    | mem g' hg' =>
      obtain ⟨α₂, hα₂, γ₂, hγ₂, rfl⟩ := hg'
      exact intE_gen D cc r hn hs hα₁ hα₂ hγ₁ hγ₂
    | zero => rw [map_zero, mul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add (f := _), mul_add]; exact add_mem hy hz
    | smul c y _ hy =>
      rw [conj_smul, mul_left_comm]
      exact mul_mem (GlobalTheory.InertSign.IntE.conj (intE_coe D c)) hy
  | zero => rw [zero_mul]; exact zero_mem _
  | add y z _ _ hy hz => rw [add_mul]; exact add_mem (hy hx) (hz hx)
  | smul c y _ hy =>
    rw [Algebra.smul_def, mul_assoc]
    exact mul_mem (intE_coe D c) (hy hx)

theorem one_mem_pairSpan (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E)
    (hn : (Ideal.absNorm cc : D.host.E) ≠ 0) (hs : GlobalTheory.NormExact.IsScale D cc r) :
    (1 : D.host.E) ∈ pairSpan D (bInv D cc r) := by
  have h₁ := (GlobalTheory.T.idealExtend_conj_mul_eq_absNorm D cc).2
  have h₂ := (GlobalTheory.T.idealExtend_conj_mul_eq_absNorm D D.host.ccK).2
  have hm := Submodule.mul_mem_mul h₁ h₂
  rw [Submodule.span_mul_span] at hm
  set c : D.host.E := r * D.host.conj r / (Ideal.absNorm cc : D.host.E) ^ 2 with hc
  have hle : Submodule.span (𝓞 D.host.E) ({t | ∃ α ∈ cE D cc, ∃ β ∈ cE D cc, t = D.host.conj α * β} *
      {t | ∃ α ∈ cE D D.host.ccK, ∃ β ∈ cE D D.host.ccK, t = D.host.conj α * β}) ≤
      (pairSpan D (bInv D cc r)).comap (LinearMap.mulLeft (𝓞 D.host.E) c) := by
    rw [Submodule.span_le]
    rintro _ ⟨_, ⟨α, hα, β, hβ, rfl⟩, _, ⟨γ, hγ, ε, hε, rfl⟩, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulLeft_apply]
    refine Submodule.subset_span ⟨r * D.host.conj α * ε / (Ideal.absNorm cc : D.host.E), ?_,
      r * D.host.conj β * γ / (Ideal.absNorm cc : D.host.E), ?_, ?_⟩
    · unfold bInv; exact Submodule.subset_span ⟨α, hα, ε, hε, rfl⟩
    · unfold bInv; exact Submodule.subset_span ⟨β, hβ, γ, hγ, rfl⟩
    · simp only [map_div₀, map_mul, map_natCast, GlobalTheory.InertSign.conj_conj, hc]
      field_simp
  have h := hle hm
  simp only [Submodule.mem_comap, LinearMap.mulLeft_apply] at h
  convert h using 1
  unfold GlobalTheory.NormExact.IsScale at hs
  rw [hc]
  field_simp
  linear_combination -hs

theorem mem_of_dual (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E)
    (hn : (Ideal.absNorm cc : D.host.E) ≠ 0) (hs : GlobalTheory.NormExact.IsScale D cc r) {y : D.host.E}
    (hy : ∀ x ∈ bInv D cc r, IntE D (y * D.host.conj x)) : y ∈ bInv D cc r := by
  have hle : pairSpan D (bInv D cc r) ≤ (bInv D cc r).comap (LinearMap.mulLeft (𝓞 D.host.E) y) := by
    unfold pairSpan
    rw [Submodule.span_le]
    rintro _ ⟨u, hu, x, hx, rfl⟩
    obtain ⟨o, ho⟩ := hy x hx
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulLeft_apply]
    have : y * (u * D.host.conj x) = o • u := by rw [Algebra.smul_def, ho]; ring
    rw [this]
    exact Submodule.smul_mem _ o hu
  have h := hle (one_mem_pairSpan D cc r hn hs)
  simpa only [Submodule.mem_comap, LinearMap.mulLeft_apply, mul_one] using h

theorem exists_ne_zero (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E)
    (hn : (Ideal.absNorm cc : D.host.E) ≠ 0) (hs : GlobalTheory.NormExact.IsScale D cc r) :
    ∃ x ∈ bInv D cc r, x ≠ 0 := by
  by_contra hne
  push_neg at hne
  have hle : pairSpan D (bInv D cc r) ≤ ⊥ := by
    unfold pairSpan
    rw [Submodule.span_le]
    rintro _ ⟨u, hu, x, hx, rfl⟩
    simp [hne u hu]
  have h := hle (one_mem_pairSpan D cc r hn hs)
  rw [Submodule.mem_bot] at h
  exact one_ne_zero h

theorem lsB_sd (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E) (a : ℕ) (hcc : cc ≠ ⊥)
    (hs : GlobalTheory.NormExact.IsScale D cc r) : Formalism.MainNotions.StandardLatticesGL3.SD D (lsB D cc r a) := by
  have hn : (Ideal.absNorm cc : D.host.E) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr hcc)
  have hsingle : ∀ (i : Fin a) (u : D.host.E), u ∈ bInv D cc r → (Pi.single i u : Fin a → D.host.E) ∈ lsB D cc r a := by
    intro i u hu
    rw [mem_lsB]
    intro j
    by_cases hj : j = i
    · subst hj; simpa using hu
    · simp only [Pi.single_apply, hj, if_false]; exact zero_mem _
  rw [GlobalTheory.InertSign.sd_iff]
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨x₀, hx₀, hne⟩ := exists_ne_zero D cc r hn hs
    have hcne : D.host.conj x₀ ≠ 0 := (map_ne_zero_iff _ D.host.conj.injective).mpr hne
    let M := Submodule.span (𝓞 D.host.E)
      (Set.range fun i : Fin a => (Pi.single i (D.host.conj x₀)⁻¹ : Fin a → D.host.E))
    have hM : M.FG := Submodule.fg_span (Set.finite_range _)
    haveI := isNoetherian_of_fg_of_noetherian M hM
    refine Submodule.FG.of_le_of_isNoetherian (T := M) ?_
    intro y hy
    rw [mem_lsB] at hy
    rw [pi_eq_sum_univ' y]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨o, ho⟩ := intE_mul_conj D cc r hn hs (hy i) hx₀
    have he : y i • (Pi.single i (1 : D.host.E) : Fin a → D.host.E) = o • Pi.single i (D.host.conj x₀)⁻¹ := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, Algebra.smul_def, ho]
        field_simp
      · simp [Pi.single_apply, hj]
    rw [he]
    exact Submodule.smul_mem _ o (Submodule.subset_span ⟨i, rfl⟩)
  · rw [eq_top_iff]
    intro v _
    have he : ∀ i : Fin a, (Pi.single i (1 : D.host.E) : Fin a → D.host.E) ∈
        Submodule.span D.host.E (lsB D cc r a : Set (Fin a → D.host.E)) := by
      intro i
      have key : ∀ t ∈ pairSpan D (bInv D cc r), t • (Pi.single i (1 : D.host.E) : Fin a → D.host.E) ∈
          Submodule.span D.host.E (lsB D cc r a : Set (Fin a → D.host.E)) := by
        intro t ht
        unfold pairSpan at ht
        induction ht using Submodule.span_induction with
        | mem g hg =>
          obtain ⟨u, hu, x, hx, rfl⟩ := hg
          have hg' : (u * D.host.conj x) • (Pi.single i (1 : D.host.E) : Fin a → D.host.E) =
              D.host.conj x • Pi.single i u := by
            funext j
            by_cases hj : j = i
            · subst hj; simp [mul_comm]
            · simp [Pi.single_apply, hj]
          rw [hg']
          exact Submodule.smul_mem _ _ (Submodule.subset_span (hsingle i u hu))
        | zero => rw [zero_smul]; exact zero_mem _
        | add s t _ _ hs' ht' => rw [add_smul]; exact add_mem hs' ht'
        | smul c t _ ht' => rw [smul_assoc]; exact Submodule.smul_of_tower_mem _ c ht'
      simpa using key 1 (one_mem_pairSpan D cc r hn hs)
    rw [pi_eq_sum_univ' v]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (he i)
  · intro y
    rw [mem_lsB]
    constructor
    · intro hy x hx
      rw [mem_lsB] at hx
      rw [intE_iff]
      unfold hE
      exact Subring.sum_mem _ fun i _ => intE_mul_conj D cc r hn hs (hy i) (hx i)
    · intro h i
      refine mem_of_dual D cc r hn hs fun x hx => ?_
      have h' := h (Pi.single i x) (hsingle i x hx)
      unfold hE at h'
      rwa [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp),
        Pi.single_eq_same] at h'

end GlobalTheory.VacRead.SelfDual

theorem GlobalTheory.VacRead.lsB_selfDual : ∀ (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E) (a : ℕ), cc ≠ ⊥ →
    GlobalTheory.NormExact.IsScale D cc r → Formalism.MainNotions.StandardLatticesGL3.SD D (GlobalTheory.VacRead.lsB D cc r a) :=
  fun D cc r a hcc hs => GlobalTheory.VacRead.SelfDual.lsB_sd D cc r a hcc hs
end
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LatVac
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open MeasureTheory

noncomputable section

namespace GlobalTheory.DiagTens

attribute [local instance] GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele
  GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField
  GlobalTheory.DiagForm.measAf GlobalTheory.DiagForm.borelAf

theorem finprod_indicator {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (y : κ → FiniteAdeleRing (𝓞 F) F) :
    (∏ᶠ w : Pl (F := F), Set.indicator {x : κ → Fv F w | ∀ i, x i ∈ w.adicCompletionIntegers F} (1 : (κ → Fv F w) → ℂ)
      (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (y i))) =
    (Set.univ.pi fun _ : κ => {x : FiniteAdeleRing (𝓞 F) F | ∀ w : Pl (F := F), x w ∈ w.adicCompletionIntegers F}).indicator
      (fun _ => (1 : ℂ)) y := by
  by_cases h : ∀ i (w : Pl (F := F)), y i w ∈ w.adicCompletionIntegers F
  · rw [Set.indicator_of_mem (show y ∈ (Set.univ.pi fun _ : κ => {x : FiniteAdeleRing (𝓞 F) F | ∀ w : Pl (F := F), x w ∈ w.adicCompletionIntegers F}) from Set.mem_univ_pi.2 fun i => h i)]
    refine finprod_eq_one_of_forall_eq_one fun w => ?_
    rw [Set.indicator_of_mem (show (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (y i)) ∈
      {x : κ → Fv F w | ∀ i, x i ∈ w.adicCompletionIntegers F} from fun i => h i w)]
    rfl
  · rw [Set.indicator_of_notMem (show y ∉ (Set.univ.pi fun _ : κ => {x : FiniteAdeleRing (𝓞 F) F | ∀ w : Pl (F := F), x w ∈ w.adicCompletionIntegers F}) from fun hy => h fun i => Set.mem_univ_pi.1 hy i)]
    push_neg at h
    obtain ⟨i₀, w₀, hw₀⟩ := h
    have hfin : (Function.mulSupport fun w : Pl F => Set.indicator
        {x : κ → Fv F w | ∀ i, x i ∈ w.adicCompletionIntegers F} (1 : (κ → Fv F w) → ℂ)
        (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (y i))).Finite := by
      have hx : ∀ᶠ w in Filter.cofinite, ∀ i, (y i) w ∈ w.adicCompletionIntegers F := by
        rw [Filter.eventually_all]
        intro i
        exact (y i).2
      refine Set.Finite.subset (Filter.eventually_cofinite.1 hx) ?_
      intro w hw hw'
      apply hw
      show Set.indicator _ _ _ = _
      rw [Set.indicator_of_mem (show (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (y i)) ∈
        {x : κ → Fv F w | ∀ i, x i ∈ w.adicCompletionIntegers F} from hw')]
      rfl
    refine finprod_eq_zero _ w₀ ?_ hfin
    exact Set.indicator_of_notMem (show (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w₀ (y i)) ∉
      {x : κ → Fv F w₀ | ∀ i, x i ∈ w₀.adicCompletionIntegers F} from fun hy => hw₀ (hy i₀)) _

theorem lDiag_box_tens_ne : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (v : Pl (F := F)), ∃ φ₀ ∈ SB (κ → Fv F v), boxFun φ₀ φ₀ ∈ SB (κ ⊕ κ → Fv F v) ∧
    ∃ R R' : (κ → AF F) → ℂ, (∀ φ ∈ SB (κ → Fv F v), Rest (evFin F v) φ R ∧ Rest (evFin F v) φ R') ∧
      GlobalTheory.DiagForm.lDiag F κ (boxFun (tens (evFin F v) φ₀ R) (tens (evFin F v) φ₀ R')) ≠ 0 := by
  intro F _ _ κ _ v
  classical
  obtain ⟨hO, hK⟩ := PI.IntAdCpctOpenWork.main F
  set O := {x : FiniteAdeleRing (𝓞 F) F | ∀ w : HeightOneSpectrum (𝓞 F), x w ∈ w.adicCompletionIntegers F} with hOdef
  let b : ContDiffBump (0 : κ → mixedEmbedding.mixedSpace F) := ⟨1, 2, one_pos, one_lt_two⟩
  have hc : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) := b.hasCompactSupport.comp_left Complex.ofReal_zero
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fun x => ((b x : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp b.contDiff
  let f : SInf F κ := hc.toSchwartzMap hd
  have hf : ∀ x, f x = ((b x : ℝ) : ℂ) := fun x => rfl
  let φs : ∀ w : Pl (F := F), (κ → Fv F w) → ℂ := fun w => Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1
  have hstd : ∀ᶠ w in Filter.cofinite, φs w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 :=
    Filter.Eventually.of_forall fun _ => rfl
  obtain ⟨r, hr, hrt⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φs hstd
  have hRest : ∀ φ ∈ SB (κ → Fv F v), Rest (evFin F v) φ r := fun φ hφ => ⟨hr, by
    rw [hrt φ]
    refine GlobalTheory.TensUniq.pure_mem_schA f _ (fun w => ?_) (GlobalTheory.PureFactor.update_eventually φs v φ hstd)
    by_cases hw : w = v
    · subst hw; rw [Function.update_self]; exact hφ
    · rw [Function.update_of_ne hw]; exact GlobalTheory.StdVacuum.indicator_mem_SB w⟩
  have h0 : φs v ∈ SB (κ → Fv F v) := GlobalTheory.StdVacuum.indicator_mem_SB v
  refine ⟨φs v, h0, ?_, r, r, fun φ hφ => ⟨hRest φ hφ, hRest φ hφ⟩, ?_⟩
  · have e : boxFun (φs v) (φs v) = Set.indicator {x : κ ⊕ κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
      funext x
      simp only [boxFun, φs, Set.indicator_apply, Set.mem_setOf_eq, Function.comp_apply, Sum.forall, Pi.one_apply]
      split_ifs <;> simp_all
    rw [e]; exact GlobalTheory.StdVacuum.indicator_mem_SB v
  · set V : Set (GlobalTheory.DiagForm.Vf F κ) := Set.univ.pi fun _ => O with hVdef
    set g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ := V.indicator fun _ => (1 : ℂ) with hgdef
    have hΦ : tens (evFin F v) (φs v) r = pureA F f g := by
      rw [hrt, Function.update_eq_self]
      funext x
      show f _ * _ = f _ * _
      congr 1
      exact finprod_indicator _
    have hΦs : tens (evFin F v) (φs v) r ∈ schA F κ := (hRest _ h0).2
    have hbox := GlobalTheory.SchwartzBox.boxFun_mem_schA F κ κ _ hΦs _ hΦs
    have hint := GlobalTheory.DiagForm.integrable_resD hbox
    have hres : GlobalTheory.DiagForm.resD F κ (boxFun (tens (evFin F v) (φs v) r) (tens (evFin F v) (φs v) r)) =
        fun p => ((b (GlobalTheory.DiagForm.eI F κ p.1) * b (GlobalTheory.DiagForm.eI F κ p.1) : ℝ) : ℂ) * (g p.2 * g p.2) := by
      rw [hΦ]
      funext p
      show pureA F f g _ * pureA F f g _ = _
      have e1 : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((GlobalTheory.DiagForm.glue p) i).1) =
          GlobalTheory.DiagForm.eI F κ p.1 := by
        funext i
        exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply _
      have e2 : (fun i => ((GlobalTheory.DiagForm.glue p) i).2) = p.2 := rfl
      simp only [pureA, Function.comp_def, Sum.elim_inl, Sum.elim_inr]
      rw [e1, e2, hf]
      push_cast
      ring
    rw [GlobalTheory.DiagForm.lDiag, LinearMap.comp_apply, GlobalTheory.DiagForm.Lext_apply _ hint, hres, GlobalTheory.DiagForm.mu,
      integral_prod_mul (fun u => ((b (GlobalTheory.DiagForm.eI F κ u) * b (GlobalTheory.DiagForm.eI F κ u) : ℝ) : ℂ))
        (fun y => g y * g y)]
    have h0O : (0 : FiniteAdeleRing (𝓞 F) F) ∈ O := fun w => (w.adicCompletionIntegers F).zero_mem
    have hVo : IsOpen V := isOpen_set_pi Set.finite_univ fun _ _ => hO
    have hVc : IsCompact V := isCompact_univ_pi fun _ => hK
    have hgg : (fun y => g y * g y) = V.indicator fun _ => (1 : ℂ) := by
      funext y
      simp only [hgdef, Set.indicator_apply]
      split_ifs <;> simp
    have hc2 : (∫ y, g y * g y ∂(Measure.addHaar : Measure (GlobalTheory.DiagForm.Vf F κ))) ≠ 0 := by
      rw [hgg, integral_indicator_const _ hVo.measurableSet]
      have hpos : 0 < (Measure.addHaar : Measure (GlobalTheory.DiagForm.Vf F κ)) V := hVo.measure_pos _ ⟨0, fun i _ => h0O⟩
      have hfin : (Measure.addHaar : Measure (GlobalTheory.DiagForm.Vf F κ)) V < ⊤ := hVc.measure_lt_top
      have : 0 < (Measure.addHaar : Measure (GlobalTheory.DiagForm.Vf F κ)).real V := ENNReal.toReal_pos hpos.ne' hfin.ne
      simpa using this.ne'
    have hc1 : (∫ u, ((b (GlobalTheory.DiagForm.eI F κ u) * b (GlobalTheory.DiagForm.eI F κ u) : ℝ) : ℂ)
        ∂(volume : Measure (GlobalTheory.DiagForm.Vi F κ))) ≠ 0 := by
      rw [integral_complex_ofReal]
      have hcs1 : HasCompactSupport fun u : GlobalTheory.DiagForm.Vi F κ => b (GlobalTheory.DiagForm.eI F κ u) :=
        b.hasCompactSupport.comp_homeomorph (GlobalTheory.DiagForm.eI F κ).toHomeomorph
      have hcs : HasCompactSupport fun u : GlobalTheory.DiagForm.Vi F κ =>
          b (GlobalTheory.DiagForm.eI F κ u) * b (GlobalTheory.DiagForm.eI F κ u) := hcs1.mul_right
      have hcont : Continuous fun u : GlobalTheory.DiagForm.Vi F κ =>
          b (GlobalTheory.DiagForm.eI F κ u) * b (GlobalTheory.DiagForm.eI F κ u) :=
        (b.continuous.comp (GlobalTheory.DiagForm.eI F κ).continuous).mul (b.continuous.comp (GlobalTheory.DiagForm.eI F κ).continuous)
      have hpos := hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero
        (μ := (volume : Measure (GlobalTheory.DiagForm.Vi F κ))) (x := 0) hcs (fun u => mul_nonneg b.nonneg b.nonneg) (by
          simp only [map_zero]
          rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)]
          norm_num)
      exact_mod_cast hpos.ne'
    exact mul_ne_zero hc1 hc2

end GlobalTheory.DiagTens
end
end

section

open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil

noncomputable section

namespace GlobalTheory.FinLatUnitF

open GlobalTheory.FinLatF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}

theorem hOF_actOF (hS : IsHermND σ JS) (g : GAF σ JS) (h : GAF σ JT) (x y : WOF F E nS nT) :
    hOF σ JS JT (actOF σ JS JT g h x) (actOF σ JS JT g h y) = hOF σ JS JT x y := by
  have h1 : JS⁻¹.map (incAF F E) * JS.map (incAF F E) = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hS.2)]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  exact GlobalTheory.SymplOInv.sum_unitary (cAF σ) (JT.map (incAF F E)) (mtF σ JT h) (JS⁻¹.map (incAF F E))
    (JS.map (incAF F E)) (mtF σ JS g⁻¹) h1 h.2 (g⁻¹).2 x y

theorem gamFF_rhoFF (hS : IsHermND σ JS) (ξ₀ : E) (ψ : AddChar (AF F) ℂ) (p : GAF σ JS × GAF σ JT)
    (x y : XFF F E nS nT) :
    gamFF σ JS JT ξ₀ ψ (rhoFF σ JS JT p x) (rhoFF σ JS JT p y) = gamFF σ JS JT ξ₀ ψ x y := by
  unfold gamFF
  rw [coe_rhoFF, coe_rhoFF]
  unfold symplOF
  rw [hOF_actOF hS]

theorem sigma_sigma (hcm : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  let τ : E →+* ℂ := Classical.arbitrary _
  apply τ.injective
  rw [hcm.2.2.2 τ, hcm.2.2.2 τ, star_star]

theorem lintegral_sq_Om : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (hc : GlobalTheory.FinLatF.HeisClosedF σ JS JT ξ₀ B.ψ) (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) (w : 𝓞 E)
        (lam : ℕ →* ℂ) (Om : GAF σ JS × GAF σ JT →* Module.End ℂ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ)),
        GlobalTheory.FinLatF.IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om →
        ∀ (μ : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), μ.IsAddHaarMeasure →
          IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 μ → ∀ p f,
            ∫⁻ w in 𝓕, ‖(Om p f : WOF F E nS nT → ℂ) w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖(f : WOF F E nS nT → ℂ) w‖ₑ ^ 2 ∂μ := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ0 hξ hc Λ w lam Om h μ 𝓕 hμ h𝓕 p f
  have hσ : ∀ x, σ (σ x) = x := sigma_sigma hB.cm
  have hn : ∀ a, ‖B.ψ a‖ = 1 := GlobalTheory.StdCharWeilDatum.norm_psi hB.std
  obtain ⟨Bf, hB1, hB2⟩ := GlobalTheory.T.exists_heisenbergInvariant_thetaMeanSquare_form F E σ B hB nS nT JS JT hS hT ξ₀ hξ0 hξ
    (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ) (fun _ hf => hf) μ 𝓕 hμ h𝓕
  rw [hB2, hB2, GlobalTheory.T.invariantForm_normalizedHeisenbergIntertwiner (isHeis_opFF hσ hS hT hξ hc h.hw) (fun x y => hn _) lam h.good _ h.sd h.span
    (rhoFF σ JS JT p) (gamFF_rhoFF hS ξ₀ B.ψ p) (h.sd' p) (h.fin p) (Om p) (h.op p) (h.vac p) Bf]
  intro x u v
  have h1 : ∀ u : GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ, opFF hc w x u =
      phaseF σ JS JT ξ₀ B.ψ w x • (⟨heisOF σ JS JT ξ₀ B.ψ x u, hc x u u.2⟩ : GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ) :=
    fun u => rfl
  have h2 : phaseF σ JS JT ξ₀ B.ψ w x * (starRingEnd ℂ) (phaseF σ JS JT ξ₀ B.ψ w x) = 1 := by
    rw [Complex.mul_conj', show ‖phaseF σ JS JT ξ₀ B.ψ w x‖ = 1 from hn _]; simp
  rw [h1, h1, Bf.map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_smul, h2, one_smul]
  exact hB1 x u v _ _ rfl rfl

end GlobalTheory.FinLatUnitF

end
end

section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.substitution_maximalMinorProduct_eq_sum_cauchyBinet : ∀ (D : D7) {a d : ℕ} {m : D.what₂.Tau → ℕ} (K : D.what₂.Tau → Matrix (Fin d) (Fin d) ℂ) (T : Tup D a d m), GlobalTheory.CompactHowe.substF K (fun _ => (1 : Matrix (Fin a) (Fin a) ℂ)) (minorPol D T) = ∑ T' : Tup D a d m, (∏ τ, ∏ r, (Matrix.of fun i i' : Fin a => K τ ((T' τ r).1 i') ((T τ r).1 i)).det) • minorPol D T' := by
  first | exact @GlobalTheory.NormDict.substF_minorPol_eq_sum | exact GlobalTheory.NormDict.substF_minorPol_eq_sum | (intros; apply GlobalTheory.NormDict.substF_minorPol_eq_sum <;> assumption)
end
