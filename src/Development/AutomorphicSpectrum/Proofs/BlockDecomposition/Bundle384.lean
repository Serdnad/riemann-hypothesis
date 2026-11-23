module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle082
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle084
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle133
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle285
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle317
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatMatrixTranslationModulationIrreduc
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenEvaluationInduced
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle354
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle379
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle316
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle006
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle173
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle380
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle378
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle110
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle381
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle382
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle286

@[expose] public section

section

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped Matrix

theorem zetaR_nonneg (K : Type) [Field K] [NumberField K] (r : ℝ) : 0 ≤ zetaR K r :=
  tsum_nonneg fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _

theorem step {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (m : ℕ) (s : ℝ) (hs : (m : ℝ) + 1 < s)
    (ih : Summable (fun x : hermE σ m ⧸ hermO σ m => (delta (Quotient.out x).1 : ℝ) ^ (-(s - 1)))) :
    Summable (fun x : hermE σ (m + 1) ⧸ hermO σ (m + 1) =>
      (delta (Quotient.out x).1 : ℝ) ^ (-s)) := by
  obtain ⟨C, hC, hD⟩ := GlobalTheory.T.delta_block_series_zeta_bound F E σ hσ
  obtain ⟨ι, hinj, hι⟩ := GlobalTheory.T.delta_block_quotient_injection F E σ hσ m
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hs1 : 1 < s := by linarith
  set G : (hermE σ m ⧸ hermO σ m) × ((Fin m → E) ⧸ intVec E m) × FQ F → ℝ := fun p =>
    (delta (blk σ (Quotient.out p.1).1 (Quotient.out p.2.1)
      (algebraMap F E ((Quotient.out p.2.2 : Fin 1 → F) 0))) : ℝ) ^ (-s) with hG
  have hG0 : 0 ≤ G := fun p => Real.rpow_nonneg (Nat.cast_nonneg _) _
  set r : ℝ := 2 * s - 1 - m with hr
  have hr1 : 1 < r := by rw [hr]; linarith
  have hexp : 1 - 2 * s = -((m : ℝ) + r) := by rw [hr]; ring

  have hin : ∀ (x : hermE σ m ⧸ hermO σ m) (U : (Fin m → E) ⧸ intVec E m),
      Summable (fun D : FQ F => G (x, U, D)) ∧
      ∑' D : FQ F, G (x, U, D) ≤ C * zetaR F (2 * s - 1) * (delta (Quotient.out x).1 : ℝ) ^ (-s) *
        (Ideal.absNorm (tor (Quotient.out x).1 (Quotient.out U)) : ℝ) ^ (-((m : ℝ) + r)) := by
    intro x U
    have := hD m (Quotient.out x).1 (Quotient.out x).2 (Quotient.out U) s hs1
    rw [hexp] at this
    exact this
  set A : ℝ := C * zetaR F (2 * s - 1) with hA
  have hA0 : 0 ≤ A := mul_nonneg hC.le (zetaR_nonneg _ _)
  have hmid : ∀ x : hermE σ m ⧸ hermO σ m,
      Summable (fun q : ((Fin m → E) ⧸ intVec E m) × FQ F => G (x, q)) ∧
      ∑' q : ((Fin m → E) ⧸ intVec E m) × FQ F, G (x, q) ≤
        A * zetaR E r * (delta (Quotient.out x).1 : ℝ) ^ (-(s - 1)) := by
    intro x
    obtain ⟨hU, hUle⟩ := GlobalTheory.T.torsion_sum_zeta_bound_delta E m (Quotient.out x).1 r hr1
    have hδ : (0 : ℝ) < delta (Quotient.out x).1 :=
      Nat.cast_pos.mpr (Nat.pos_of_ne_zero (GlobalTheory.T.delta_eq_lattice_index E m _).1)
    set B : ℝ := A * (delta (Quotient.out x).1 : ℝ) ^ (-s) with hB
    have hB0 : 0 ≤ B := mul_nonneg hA0 (Real.rpow_nonneg hδ.le _)
    have hsum : Summable (fun U : (Fin m → E) ⧸ intVec E m => ∑' D : FQ F, G (x, U, D)) :=
      Summable.of_nonneg_of_le (fun U => tsum_nonneg fun D => hG0 _) (fun U => (hin x U).2)
        (hU.mul_left B)
    have hS : Summable (fun q : ((Fin m → E) ⧸ intVec E m) × FQ F => G (x, q)) :=
      (summable_prod_of_nonneg (fun q => hG0 (x, q))).mpr ⟨fun U => (hin x U).1, hsum⟩
    refine ⟨hS, ?_⟩
    rw [hS.tsum_prod' (fun U => (hin x U).1)]
    calc ∑' U : (Fin m → E) ⧸ intVec E m, ∑' D : FQ F, G (x, U, D)
        ≤ ∑' U : (Fin m → E) ⧸ intVec E m, B *
            (Ideal.absNorm (tor (Quotient.out x).1 (Quotient.out U)) : ℝ) ^ (-((m : ℝ) + r)) :=
          hsum.tsum_le_tsum (fun U => (hin x U).2) (hU.mul_left B)
      _ = B * ∑' U : (Fin m → E) ⧸ intVec E m,
            (Ideal.absNorm (tor (Quotient.out x).1 (Quotient.out U)) : ℝ) ^ (-((m : ℝ) + r)) :=
          tsum_mul_left
      _ ≤ B * (delta (Quotient.out x).1 * zetaR E r) := mul_le_mul_of_nonneg_left hUle hB0
      _ = A * zetaR E r * (delta (Quotient.out x).1 : ℝ) ^ (-(s - 1)) := by
          have : (delta (Quotient.out x).1 : ℝ) ^ (-(s - 1)) =
              (delta (Quotient.out x).1 : ℝ) ^ (-s) * delta (Quotient.out x).1 := by
            rw [show -(s - 1) = -s + 1 by ring, Real.rpow_add hδ, Real.rpow_one]
          rw [this, hB]
          ring
  have hGs : Summable G := by
    refine (summable_prod_of_nonneg hG0).mpr ⟨fun x => (hmid x).1, ?_⟩
    exact Summable.of_nonneg_of_le (fun x => tsum_nonneg fun q => hG0 _) (fun x => (hmid x).2)
      (ih.mul_left _)
  refine (hGs.comp_injective hinj).congr fun x => ?_
  simp only [Function.comp, hG, hι x]

theorem summable_delta_rpow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (s : ℝ), (n : ℝ) < s →
    Summable (fun x : hermE σ n ⧸ hermO σ n => (delta (Quotient.out x).1 : ℝ) ^ (-s)) := by
  intro F E _ _ _ _ _ σ hσ n
  induction n with
  | zero =>
    intro s _
    haveI : Subsingleton (hermE σ 0) := ⟨fun a b => Subtype.ext (Matrix.ext fun i => i.elim0)⟩
    haveI : Subsingleton (hermE σ 0 ⧸ hermO σ 0) := QuotientAddGroup.mk_surjective.subsingleton
    exact Summable.of_finite
  | succ n ih =>
    intro s hs
    push_cast at hs
    exact step σ hσ n s hs (ih (s - 1) (by linarith))

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
end
end

section

open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

namespace GlobalTheory.CompanionTheory.LinRec

lemma eq_zero_of_natDegree_eq_zero {p : ℂ[X]} (hp : p.Monic) (hd : p.natDegree = 0)
    {u : ℕ → ℂ} (hu : aeval shift p u = 0) : u = 0 := by
  have hp1 : p = 1 := by
    have h1 : p.coeff 0 = 1 := by
      have h2 := hp.coeff_natDegree
      rwa [hd] at h2
    rw [eq_C_of_natDegree_eq_zero hd, h1, C_1]
  subst hp1
  simpa using hu

theorem uniform_aeval (D : ℕ) (κ' κ : ℝ) (hκ : κ' < κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ℂ[X], p.Monic → p.natDegree ≤ D →
      (∀ z, p.IsRoot z → ‖z‖ ≤ Real.exp κ') → ∀ (u : ℕ → ℂ) (M : ℝ), aeval shift p u = 0 →
      (∀ j < p.natDegree, ‖u j‖ ≤ M) → 0 ≤ M →
      ∀ i : ℕ, ‖u i‖ ≤ C * Real.exp (κ * i) * M := by
  have hδ : 0 < Real.exp κ - Real.exp κ' := sub_pos.2 (Real.exp_lt_exp.2 hκ)
  induction D with
  | zero =>
    refine ⟨0, le_rfl, fun p hp hd _ u M hu _ _ i => ?_⟩
    have hu0 := eq_zero_of_natDegree_eq_zero hp (Nat.le_zero.1 hd) hu
    simp [hu0]
  | succ D ih =>
    obtain ⟨C', hC', hB⟩ := ih
    have hE' : 0 < Real.exp κ' := Real.exp_pos _
    have hc : 0 ≤ C' * (1 + Real.exp κ') := by positivity
    have hC0 : 0 ≤ 1 + C' * (1 + Real.exp κ') / (Real.exp κ - Real.exp κ') := by positivity
    refine ⟨_, hC0, fun p hp hd hr u M hu hM hM0 i => ?_⟩
    by_cases hd0 : p.natDegree = 0
    · have hu0 := eq_zero_of_natDegree_eq_zero hp hd0 hu
      have : 0 ≤ (1 + C' * (1 + Real.exp κ') / (Real.exp κ - Real.exp κ')) *
          Real.exp (κ * i) * M := by positivity
      simpa [hu0] using this
    obtain ⟨z, hz⟩ : ∃ z, p.IsRoot z := IsAlgClosed.exists_root p (by
      intro h0
      exact hd0 (natDegree_eq_zero_iff_degree_le_zero.2 h0.le))
    have hzle := hr z hz
    have hzlt : ‖z‖ < Real.exp κ := hzle.trans_lt (Real.exp_lt_exp.2 hκ)
    obtain ⟨q, rfl⟩ := dvd_iff_isRoot.2 hz
    have hq : q.Monic := (monic_X_sub_C z).of_mul_monic_left hp
    have hqd : ((X - C z) * q).natDegree = q.natDegree + 1 := by
      rw [(monic_X_sub_C z).natDegree_mul hq, natDegree_X_sub_C]
      omega
    have hv : ∀ i : ℕ, ‖u (i + 1) - z * u i‖ ≤
        C' * (1 + Real.exp κ') * Real.exp (κ * i) * M := by
      intro i
      have hb := hB q hq (by omega)
        (fun w hw => hr w (by
          have hw' : eval w q = 0 := hw
          simp [IsRoot, hw']))
        (fun i => u (i + 1) - z * u i) ((1 + Real.exp κ') * M) (aeval_diff q z u hu)
        (fun j hj => ?_) (by positivity) i
      · calc ‖u (i + 1) - z * u i‖ ≤ C' * Real.exp (κ * i) * ((1 + Real.exp κ') * M) := hb
          _ = _ := by ring
      · calc ‖u (j + 1) - z * u j‖ ≤ ‖u (j + 1)‖ + ‖z * u j‖ := norm_sub_le _ _
          _ = ‖u (j + 1)‖ + ‖z‖ * ‖u j‖ := by rw [norm_mul]
          _ ≤ M + Real.exp κ' * M := add_le_add (hM _ (by omega))
              (mul_le_mul hzle (hM _ (by omega)) (norm_nonneg _) hE'.le)
          _ = _ := by ring
    have hg := geom_step z κ _ M hzlt hc hM0 u (hM 0 (by omega)) hv i
    refine hg.trans ?_
    have hdiv : C' * (1 + Real.exp κ') / (Real.exp κ - ‖z‖) ≤
        C' * (1 + Real.exp κ') / (Real.exp κ - Real.exp κ') :=
      div_le_div_of_nonneg_left hc hδ (by linarith)
    have hEM : 0 ≤ Real.exp (κ * i) * M := by positivity
    calc _ = (1 + C' * (1 + Real.exp κ') / (Real.exp κ - ‖z‖)) * (Real.exp (κ * i) * M) := by ring
      _ ≤ (1 + C' * (1 + Real.exp κ') / (Real.exp κ - Real.exp κ')) * (Real.exp (κ * i) * M) :=
        mul_le_mul_of_nonneg_right (by linarith) hEM
      _ = _ := by ring

theorem uniformRecBound :
    ∀ (D : ℕ) (κ' κ : ℝ), κ' < κ → ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ℂ[X], p.Monic → p.natDegree ≤ D →
  (∀ z, p.IsRoot z → ‖z‖ ≤ Real.exp κ') → ∀ (u : ℕ → ℂ) (M : ℝ),
  (∀ i, ∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j * u (i + j) = 0) → (∀ j < p.natDegree, ‖u j‖ ≤ M) → 0 ≤ M →
  ∀ i : ℕ, ‖u i‖ ≤ C * Real.exp (κ * i) * M := by
  intro D κ' κ hκ
  obtain ⟨C, hC, h⟩ := uniform_aeval D κ' κ hκ
  refine ⟨C, hC, fun p hp hd hr u M hu hM hM0 i => h p hp hd hr u M ?_ hM hM0 i⟩
  funext i
  rw [aeval_shift]
  exact hu i

end GlobalTheory.CompanionTheory.LinRec
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.TwFibre

theorem twisted_fibre_isLocallyConstant_hasCompactSupport : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (f : XS τ σ) (y : Mir k ((i + 1) + t + 1)), IsLocallyConstant (fun d : Fin (t + 1) → k => (((Circle.toUnits (ψ (d (Fin.last t))))⁻¹ : ℂˣ) : ℂ) • evX f (dEmb k i t d * y)) ∧ HasCompactSupport (fun d : Fin (t + 1) → k => (((Circle.toUnits (ψ (d (Fin.last t))))⁻¹ : ℂˣ) : ℂ) • evX f (dEmb k i t d * y)) := by
  intro k _ _ _ _ i t ψ hψ τ σ f y
  obtain ⟨hl, hc⟩ := GlobalTheory.T.locally_constant_compact_support_unipotent k i t τ σ f y
  refine ⟨?_, ?_⟩
  · have h1 : IsLocallyConstant (fun d : Fin (t + 1) → k => ψ (d (Fin.last t))) :=
      (GlobalTheory.IrredSB.char_isLocallyConstant ψ hψ).comp_continuous (continuous_apply _)
    have h2 : IsLocallyConstant (fun d : Fin (t + 1) → k =>
        (((Circle.toUnits (ψ (d (Fin.last t))))⁻¹ : ℂˣ) : ℂ)) :=
      h1.comp (fun z : Circle => (((Circle.toUnits z)⁻¹ : ℂˣ) : ℂ))
    exact IsLocallyConstant.comp₂ h2 hl (fun a b => a • b)
  · refine hc.mono fun d hd h0 => hd ?_
    have h0' : evX f (dEmb k i t d * y) = 0 := h0
    show (_ : ℂ) • evX f (dEmb k i t d * y) = 0
    rw [h0', smul_zero]

end GlobalTheory.CompanionTheory.BZPhiPG.TwFibre
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.Lin

open GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.Rodier.SmIntEl

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem muD_add {W : Type} [AddCommGroup W] [Module ℂ W] (n : ℕ) {φ₁ φ₂ : (Fin n → k) → W}
    (l₁ : IsLocallyConstant φ₁) (c₁ : HasCompactSupport φ₁)
    (l₂ : IsLocallyConstant φ₂) (c₂ : HasCompactSupport φ₂) :
    @smInt _ _ (borel _) _ _ (muD k n) (φ₁ + φ₂) =
      @smInt _ _ (borel _) _ _ (muD k n) φ₁ + @smInt _ _ (borel _) _ _ (muD k n) φ₂ := by
  letI : MeasurableSpace (Fin n → k) := borel _
  haveI : BorelSpace (Fin n → k) := ⟨rfl⟩
  haveI : MeasureTheory.IsFiniteMeasureOnCompacts (muD k n) := by
    unfold muD
    infer_instance
  exact smInt_add (muD k n) l₁ c₁ l₂ c₂

theorem muD_smul {W : Type} [AddCommGroup W] [Module ℂ W] (n : ℕ) (c : ℂ) {φ : (Fin n → k) → W}
    (l : IsLocallyConstant φ) (h : HasCompactSupport φ) :
    @smInt _ _ (borel _) _ _ (muD k n) (c • φ) = c • @smInt _ _ (borel _) _ _ (muD k n) φ := by
  letI : MeasurableSpace (Fin n → k) := borel _
  haveI : BorelSpace (Fin n → k) := ⟨rfl⟩
  haveI : MeasureTheory.IsFiniteMeasureOnCompacts (muD k n) := by
    unfold muD
    infer_instance
  have e : (⇑(c • LinearMap.id : W →ₗ[ℂ] W) ∘ φ) = c • φ := rfl
  rw [← e, smInt_linear (muD k n) (c • LinearMap.id : W →ₗ[ℂ] W) l h]
  rfl

variable {i t : ℕ} {τ : MRep k (i + 1)} {σ : GRep k (t + 1)}

def tw (ψ : AddChar k Circle) (f : XS τ σ) (y : Mir k ((i + 1) + t + 1)) : (Fin (t + 1) → k) → τ.V ⊗[ℂ] σ.V :=
  fun d => (((Circle.toUnits (ψ (d (Fin.last t))))⁻¹ : ℂˣ) : ℂ) • evX f (dEmb k i t d * y)

theorem tw_add (ψ : AddChar k Circle) (f g : XS τ σ) (y : Mir k ((i + 1) + t + 1)) :
    tw ψ (f + g) y = tw ψ f y + tw ψ g y :=
  funext fun _ => smul_add _ _ _

theorem tw_smul (ψ : AddChar k Circle) (c : ℂ) (f : XS τ σ) (y : Mir k ((i + 1) + t + 1)) :
    tw ψ (c • f) y = c • tw ψ f y :=
  funext fun d => by
    show (_ : ℂ) • (c • evX f _) = c • ((_ : ℂ) • evX f _)
    exact smul_comm _ _ _

theorem tw_lc (ψ : AddChar k Circle) (hψ : Continuous ψ) (f : XS τ σ) (y : Mir k ((i + 1) + t + 1)) :
    IsLocallyConstant (tw ψ f y) := by
  have h1 : IsLocallyConstant (fun d : Fin (t + 1) → k => ψ (d (Fin.last t))) :=
    (GlobalTheory.IrredSB.char_isLocallyConstant ψ hψ).comp_continuous (continuous_apply _)
  have h2 : IsLocallyConstant (fun d : Fin (t + 1) → k =>
      (((Circle.toUnits (ψ (d (Fin.last t))))⁻¹ : ℂˣ) : ℂ)) :=
    h1.comp (fun z : Circle => (((Circle.toUnits z)⁻¹ : ℂˣ) : ℂ))
  exact IsLocallyConstant.comp₂ h2 (GlobalTheory.T.locally_constant_compact_support_unipotent k i t τ σ f y).1 (fun a b => a • b)

theorem tw_cs (ψ : AddChar k Circle) (f : XS τ σ) (y : Mir k ((i + 1) + t + 1)) :
    HasCompactSupport (tw ψ f y) := by
  refine (GlobalTheory.T.locally_constant_compact_support_unipotent k i t τ σ f y).2.mono fun d hd h0 => hd ?_
  have h0' : evX f (dEmb k i t d * y) = 0 := h0
  show (_ : ℂ) • evX f (dEmb k i t d * y) = 0
  rw [h0', smul_zero]

theorem intO_add (f g : XS τ σ) (y : Mir k ((i + 1) + t + 1)) :
    intO (f + g) y = intO f y + intO g y :=
  muD_add (t + 1) (GlobalTheory.T.locally_constant_compact_support_unipotent k i t τ σ f y).1 (GlobalTheory.T.locally_constant_compact_support_unipotent k i t τ σ f y).2
    (GlobalTheory.T.locally_constant_compact_support_unipotent k i t τ σ g y).1 (GlobalTheory.T.locally_constant_compact_support_unipotent k i t τ σ g y).2

theorem intO_smul (c : ℂ) (f : XS τ σ) (y : Mir k ((i + 1) + t + 1)) :
    intO (c • f) y = c • intO f y :=
  muD_smul (t + 1) c (GlobalTheory.T.locally_constant_compact_support_unipotent k i t τ σ f y).1 (GlobalTheory.T.locally_constant_compact_support_unipotent k i t τ σ f y).2

theorem intC_add (ψ : AddChar k Circle) (hψ : Continuous ψ) (f g : XS τ σ) (y : Mir k ((i + 1) + t + 1)) :
    intC ψ (f + g) y = intC ψ f y + intC ψ g y :=
  (congrArg (@smInt _ _ (borel _) _ _ (muD k (t + 1))) (tw_add ψ f g y)).trans
    (muD_add (t + 1) (tw_lc ψ hψ f y) (tw_cs ψ f y) (tw_lc ψ hψ g y) (tw_cs ψ g y))

theorem intC_smul (ψ : AddChar k Circle) (hψ : Continuous ψ) (c : ℂ) (f : XS τ σ) (y : Mir k ((i + 1) + t + 1)) :
    intC ψ (c • f) y = c • intC ψ f y :=
  (congrArg (@smInt _ _ (borel _) _ _ (muD k (t + 1))) (tw_smul ψ c f y)).trans
    (muD_smul (t + 1) c (tw_lc ψ hψ f y) (tw_cs ψ f y))

theorem scaled_add {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] (T : A →ₗ[ℂ] B) (u : ℂ)
    {a b c : A} (h : a = b + c) : u • T a = u • T b + u • T c := by
  rw [h, map_add (f := _), smul_add]

theorem scaled_smul {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] (T : A →ₗ[ℂ] B) (u c : ℂ)
    {a b : A} (h : a = c • b) : u • T a = c • u • T b := by
  rw [h, map_smul, smul_comm]

theorem eC_eO_linear : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (f g : XS τ σ) (c : ℂ),
    eC ψ (f + g) = eC ψ f + eC ψ g ∧ eC ψ (c • f) = c • eC ψ f ∧ eO ψ (f + g) = eO ψ f + eO ψ g ∧ eO ψ (c • f) = c • eO ψ f := by
  intro k _ _ _ _ i t ψ hψ τ σ _ _ f g c
  refine ⟨funext fun m => ?_, funext fun m => ?_, funext fun m => ?_, funext fun m => ?_⟩
  · exact scaled_add (qC τ σ) _ (intC_add ψ hψ f g _)
  · exact scaled_smul (qC τ σ) _ c (intC_smul ψ hψ c f _)
  · exact scaled_add (qO τ σ ψ) _ (intO_add f g _)
  · exact scaled_smul (qO τ σ ψ) _ c (intO_smul c f _)

end GlobalTheory.CompanionTheory.BZPhiPG.Lin

end
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

theorem _root_.GlobalTheory.T.open_evaluation_induced : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (f : XS τ σ) (hf : ∀ x ∈ Cl k i t, evX f x = 0),
  ∃ y : cIndSpace (HPG k i (t + 1)) (sigO τ σ ψ), (y : smoothPart (ind (HPG k i (t + 1)) (sigO τ σ ψ))).1.1 = eO ψ f := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.MemO.eO_mem | exact GlobalTheory.CompanionTheory.BZPhiPG.MemO.eO_mem | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.MemO.eO_mem <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

theorem _root_.GlobalTheory.T.fibre_integral_support_subgroup : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W) [MeasurableSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k)) (c : kˣ) (K₁ : Subgroup (GL (Fin (i + t)) k)) (hK : K₁ ≤ GlobalTheory.SplitWeil.KO k (Fin (i + t))) (b : cIndSpace (HPG k i t) (hRep τ σ)), (∀ p : Mir k (i + t), (¬ ∃ h : HPG k i t, ∃ β ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK, p = (h : Mir k (i + t)) * β) → b.1.1.1 p = 0) → ∀ g : GL (Fin (i + t)) k, (¬ ∃ q : Qp k i t, ∃ b' ∈ K₁, g = (q : GL (Fin (i + t)) k) * b') → fibInt μ b g = 0 := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.FibOffQ.main | exact GlobalTheory.CompanionTheory.BZPsiPG.FibOffQ.main | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.FibOffQ.main <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

theorem _root_.GlobalTheory.T.fibre_integral_vanishing_subgroup : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W) (c : kˣ) (K₁ : Subgroup (GL (Fin (i + t)) k)) (hK : K₁ ≤ GlobalTheory.SplitWeil.KO k (Fin (i + t))) (z : V ⊗[ℂ] W) (b : cIndSpace (HPG k i t) (hRep τ σ)), (∀ (h : HPG k i t) (β : Mir k (i + t)), β ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK → b.1.1.1 ((h : Mir k (i + t)) * β) = hRep τ σ h z) → (∀ p : Mir k (i + t), (¬ ∃ h : HPG k i t, ∃ β ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK, p = (h : Mir k (i + t)) * β) → b.1.1.1 p = 0) → fibV b 1 = (GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.latt t c : Set (Fin t → k)).indicator (fun _ => z) := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.fibV_one_bump | exact GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.fibV_one_bump | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.fibV_one_bump <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)

theorem _root_.GlobalTheory.T.local_frame_derivation_compat : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [Smooth q] (s : ℕ) {V V' : X.Opens} (hVV : V ≤ V'), IsAffineOpen V' → ∀ {d : ℕ} (c : Coord q V d),
    letI := (strV q V).toAlgebra
    ∀ (D : Fin d → Derivation K Γ(X, V) Γ(X, V)), (∀ k j, D k (c.t j) = if k = j then 1 else 0) →
    ∀ (E : Frame (sP (KS q s {V})) d) (ε : Γ(X, V) ≃+* (sP (KS q s {V})).A.obj E.D), IsLoc q s c.t E ε →
    ∀ (σ : ∀ T, E.D ⟶ T) (m : ℕ) (r : ℤ), r = m → m + 1 ≤ s → ∀ (ξ : HQ (KS q s {V'}) r (r + 1) m) (y : Idx m d → Γ(X, V)),
      CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {V}) r) (sFil (KS q s {V}) (r + 1)) (fun u => ∑ I : Idx m d, E.form σ I.1 (ε (y I)) u) (resKS q s hVV _ _ _ ξ) →
      ∀ I, y I ∈ jacSpan hVV (RingHom.id _) (fun k => D k) I.1 := by
  first | exact @GlobalTheory.CompanionTheory.ConeLocal.coef_mem_jacSpan | exact GlobalTheory.CompanionTheory.ConeLocal.coef_mem_jacSpan | (intros; apply GlobalTheory.CompanionTheory.ConeLocal.coef_mem_jacSpan <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.affine_graded_cohomology_vanishing : KH.LocGr → KH.LocVan → KH.PolyTf → KH.GlobSerreSt → KH.GlobVanSt → ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [Smooth q]
    (V : X.Opens) (hV : IsAffineOpen V) (s r j : ℕ), r < s → j ≠ r → Subsingleton (HQ (KS q s {V}) r ((r : ℤ) + 1) j) := by
  first | exact @GlobalTheory.CompanionTheory.GrForm.gr_aff | exact GlobalTheory.CompanionTheory.GrForm.gr_aff | (intros; apply GlobalTheory.CompanionTheory.GrForm.gr_aff <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.thickening_filtration_isFil : ∀ {b : Base} (L : b.Fun), IsFil (thP L) (thFil L) := by
  first | exact @GlobalTheory.CompanionTheory.DPFil.isFil_thFil | exact GlobalTheory.CompanionTheory.DPFil.isFil_thFil | (intros; apply GlobalTheory.CompanionTheory.DPFil.isFil_thFil <;> assumption)
end

section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

theorem _root_.GlobalTheory.T.segment_rep_central_character_formula : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Γ : Segment k) (y : IrrGL (k := k)), IsLSeg Γ y.rep → ∀ (t : kˣ) (c : ℂ), Zl.ScalarBy Γ.first t c → Zl.ScalarBy y t (c ^ Γ.len * ((absPow k (Γ.first.1 : ℂ) t : ℂˣ) : ℂ) ^ (Γ.len * (Γ.len - 1) / 2)) := by
  first | exact @GlobalTheory.CompanionTheory.SegScalar.scalarBy_of_isLSeg | exact GlobalTheory.CompanionTheory.SegScalar.scalarBy_of_isLSeg | (intros; apply GlobalTheory.CompanionTheory.SegScalar.scalarBy_of_isLSeg <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

theorem _root_.GlobalTheory.T.langlands_factors_dual_reverse_ordered : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → LSegDual k → ∀ (𝔪 : Multiset (Segment k)) {h : ℕ} (x : Fin h → IrrGL (k := k)), LFactors 𝔪 x → ∃ Γ : Fin h → Segment k, IsRevOrdered Γ ∧ ∀ i, IsLSeg (Γ i) (dualCl (x i)).rep := by
  first | exact @GlobalTheory.CompanionTheory.DualForms.exists_revOrdered_dual | exact GlobalTheory.CompanionTheory.DualForms.exists_revOrdered_dual | (intros; apply GlobalTheory.CompanionTheory.DualForms.exists_revOrdered_dual <;> assumption)
end
