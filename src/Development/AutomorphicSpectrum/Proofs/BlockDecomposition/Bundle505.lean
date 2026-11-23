module

public import Formalism.RealPlaceAnalysis.Bundle001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiExistsStatement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.DisintegrationDensityContinuous
public import GroundTheory.IdeleRoots.ConstantFrames.GaugeExistence.QdetSub
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Topology.Instances.Matrix
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle054
public import Mathlib.FieldTheory.Separable
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle479
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.Normed
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Bundle005
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PRVComponents.TensorActionLieRelations
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.SingleMulJmComm
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Bundle004
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle472
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle018
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle452
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle002
import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle475
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLoc
public import Formalism.RealPlaceAnalysis.Bundle002
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneMemGoodCT
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.GenSpace
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Vandermonde
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulEqOfRangeLe
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.WedgeSub
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.QuotVanish
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.InvTransposeGLInvTransposeGL

@[expose] public section

section

noncomputable section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

namespace GlobalTheory.CompanionTheory.RealCount.Extremal

variable {n : ℕ}

def permM (w : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => if i = w j then 1 else 0

theorem permM_conjTranspose (w : Equiv.Perm (Fin n)) : (permM w)ᴴ = permM w⁻¹ := by
  ext i j
  simp only [permM, Matrix.conjTranspose_apply, Matrix.of_apply]
  by_cases h : j = w i
  · have h2 : i = w⁻¹ j := by subst h; simp
    rw [if_pos h, if_pos h2]; simp
  · have h2 : ¬ i = w⁻¹ j := fun e => h (by rw [e]; simp)
    rw [if_neg h, if_neg h2]; simp

theorem permM_mul_single (w : Equiv.Perm (Fin n)) (c d : Fin n) :
    permM w * Matrix.single c d (1 : ℂ) = Matrix.single (w c) d 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.single_apply, permM, Matrix.of_apply]
  rw [Finset.sum_eq_single c]
  · by_cases h1 : i = w c <;> by_cases h2 : d = j
    · simp [h1, h2]
    · simp [h1, h2]
    · simp [h2, h1, Ne.symm h1]
    · simp [h1, h2, Ne.symm h1]
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

theorem single_mul_permM (v : Equiv.Perm (Fin n)) (c d : Fin n) :
    Matrix.single c d (1 : ℂ) * permM v = Matrix.single c (v⁻¹ d) 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.single_apply, permM, Matrix.of_apply]
  rw [Finset.sum_eq_single d]
  · by_cases h1 : c = i
    · by_cases h2 : d = v j
      · subst h1 h2; simp
      · subst h1
        have h3 : ¬ v.symm d = j := fun e => h2 (by rw [← e]; simp)
        simp [h2, h3]
    · simp [h1]
  · intro b _ hb
    rw [if_neg (fun q => hb q.2.symm)]; simp
  · simp

theorem permM_single (w : Equiv.Perm (Fin n)) (c d : Fin n) :
    permM w * Matrix.single c d (1 : ℂ) * (permM w)ᴴ = Matrix.single (w c) (w d) 1 := by
  rw [permM_conjTranspose, permM_mul_single, single_mul_permM, inv_inv]

theorem permM_mul (w v : Equiv.Perm (Fin n)) : permM w * permM v = permM (w * v) := by
  ext i j
  simp only [Matrix.mul_apply, permM, Matrix.of_apply]
  rw [Finset.sum_eq_single (v j)]
  · have e : (w * v) j = w (v j) := rfl
    by_cases h : i = w (v j)
    · rw [if_pos h, if_pos rfl, if_pos (h.trans e.symm)]; simp
    · rw [if_neg h, zero_mul, if_neg (fun q => h (q.trans e))]
  · intro b _ hb
    rw [if_neg hb]; simp
  · simp

theorem permM_one : permM (1 : Equiv.Perm (Fin n)) = 1 := by
  ext i j
  simp only [permM, Matrix.of_apply, Matrix.one_apply]
  have e : (1 : Equiv.Perm (Fin n)) j = j := rfl
  by_cases h : i = j
  · rw [if_pos (h.trans e.symm), if_pos h]
  · rw [if_neg (fun q => h (q.trans e)), if_neg h]

theorem Jm_true : ReciprocityTheory.ChartRestriction.DS.Jm (fun _ : Fin n => true) = 1 := by
  simp [ReciprocityTheory.ChartRestriction.DS.Jm]

def permU (w : Equiv.Perm (Fin n)) : (Matrix (Fin n) (Fin n) ℂ)ˣ where
  val := permM w
  inv := permM w⁻¹
  val_inv := by rw [permM_mul, mul_inv_cancel, permM_one]
  inv_val := by rw [permM_mul, inv_mul_cancel, permM_one]

theorem permM_unitary (w : Equiv.Perm (Fin n)) : permM w ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, permM_conjTranspose, permM_mul,
    mul_inv_cancel, permM_one]

def permK (w : Equiv.Perm (Fin n)) : ReciprocityTheory.ChartRestriction.DS.S7.KG (fun _ : Fin n => true) :=
  ⟨⟨permU w, by
      show (permM w)ᴴ * ReciprocityTheory.ChartRestriction.DS.Jm (fun _ : Fin n => true) * permM w = _
      rw [Jm_true, Matrix.mul_one, permM_conjTranspose, permM_mul, inv_mul_cancel, permM_one]⟩,
    by
      show permM w ∈ ReciprocityTheory.ChartRestriction.DS.Kset (fun _ : Fin n => true)
      refine ⟨permM_unitary w, ?_⟩
      rw [Jm_true, Matrix.mul_one, Matrix.one_mul]⟩

theorem toMK_permK (w : Equiv.Perm (Fin n)) : ReciprocityTheory.ChartRestriction.DS.S7.toMK (permK w) = permM w := rfl

theorem conj_single {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : ReciprocityTheory.ChartRestriction.DS.S7.KType ε Λ)
    (k : ReciprocityTheory.ChartRestriction.DS.S7.KG ε) {c d : Fin n} (h : ε c = ε d) :
    T.op k * T.dτ (Matrix.single c d 1) * star (T.op k) =
      T.dτ (ReciprocityTheory.ChartRestriction.DS.S7.toMK k * Matrix.single c d 1 * star (ReciprocityTheory.ChartRestriction.DS.S7.toMK k)) := by
  have h1 := ReciprocityTheory.ChartRestriction.DS.HW.KType.conj_dτ T k (ReciprocityTheory.ChartRestriction.DS.HW.inK_hermitian_unit h)
  have h2 := ReciprocityTheory.ChartRestriction.DS.HW.KType.conj_dτ T k (ReciprocityTheory.ChartRestriction.DS.HW.inK_skew_hermitian_unit h)
  rw [ReciprocityTheory.ChartRestriction.DS.HW.single_eq_kp c d, map_add (f := _), map_smul, mul_add, add_mul, mul_smul_comm, smul_mul_assoc,
    h1, h2, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, map_add, map_smul]

theorem unit_translate {Λ : Fin n → ℝ} (T : ReciprocityTheory.ChartRestriction.DS.S7.KType (fun _ : Fin n => true) Λ)
    (w : Equiv.Perm (Fin n)) (c d : Fin n) (v : T.V) :
    T.dτ (Matrix.single (w c) (w d) 1) (T.op (permK w) v) = T.op (permK w) (T.dτ (Matrix.single c d 1) v) := by
  have h := conj_single T (permK w) (c := c) (d := d) rfl
  rw [toMK_permK, Matrix.star_eq_conjTranspose, permM_single] at h
  rw [← h]
  have hu : star (T.op (permK w)) * T.op (permK w) = 1 := Unitary.coe_star_mul_self _
  have e : T.op (permK w) * T.dτ (Matrix.single c d 1) * star (T.op (permK w)) * T.op (permK w) =
      T.op (permK w) * T.dτ (Matrix.single c d 1) := by
    rw [mul_assoc _ (star _), hu, mul_one]
  exact congrArg (fun F : T.V →L[ℂ] T.V => F v) e

theorem extremal_module : ∀ {n : ℕ} (κ : Fin n → ℝ), Antitone κ → ∀ s : ℝ, (∀ a, ∃ m : ℤ, κ a - s = m) →
    ∀ w : Equiv.Perm (Fin n),
    ∃ (Z : Type) (_ : NormedAddCommGroup Z) (_ : InnerProductSpace ℂ Z) (_ : FiniteDimensional ℂ Z)
      (E : Fin n → Fin n → Module.End ℂ Z) (u a : Z),
      Formalism.REAL.GlRel E ∧ (∀ x y (f g : Z), ⟪E x y f, g⟫_ℂ = ⟪f, E y x g⟫_ℂ) ∧ u ≠ 0 ∧
      Formalism.REAL.KHighest (fun _ => true) E κ u ∧
      (∀ W : Submodule ℂ Z, (∀ x y, ∀ f ∈ W, E x y f ∈ W) → u ∈ W → W = ⊤) ∧ a ≠ 0 ∧
      (∀ x, E (w x) (w x) a = ((κ x : ℝ) : ℂ) • a) ∧ ∀ x y, x < y → E (w x) (w y) a = 0 := by
  intro n κ hκ s hs w
  obtain ⟨T⟩ := ReciprocityTheory.ChartRestriction.DS.HW.kType_exists_of_dom (fun _ : Fin n => true) (fun a => κ a - s) hs
    (fun a b hab _ => sub_le_sub_right (hκ hab.le) s)
  set F := ReciprocityTheory.ChartRestriction.DS.HW.kunits T with hF
  set E := ReciprocityTheory.ChartRestriction.DS.HW.endomorphismFamilyShift F (fun _ => s) with hE
  have hEval : ∀ x y (f : T.V), E x y f = T.dτ (Matrix.single x y 1) f + (if x = y then ((s : ℝ) : ℂ) else 0) • f := by
    intro x y f
    simp only [hE, hF, ReciprocityTheory.ChartRestriction.DS.HW.endomorphismFamilyShift, ReciprocityTheory.ChartRestriction.DS.HW.kunits, LinearMap.add_apply,
      LinearMap.smul_apply, Module.End.one_apply, ContinuousLinearMap.coe_coe]
  have hrel : Formalism.REAL.KRel (fun _ : Fin n => true) E :=
    ReciprocityTheory.ChartRestriction.DS.HW.ext1Shift_kRel (ReciprocityTheory.ChartRestriction.DS.HW.KType.kRel T) (fun _ _ _ => rfl)
  have huni : Formalism.REAL.KUnit (fun _ : Fin n => true) E :=
    ReciprocityTheory.ChartRestriction.DS.HW.ext1Shift_kUnit (ReciprocityTheory.ChartRestriction.DS.HW.KType.kUnit T) _
  have hhigh : Formalism.REAL.KHighest (fun _ => true) E κ T.w := by
    have h := ReciprocityTheory.ChartRestriction.DS.HW.ext1Shift_kHighest (t := fun _ => s) (ReciprocityTheory.ChartRestriction.DS.HW.KType.kHighest_w T)
    have e : (fun a => κ a - s) + (fun _ => s) = κ := by
      funext a
      simp
    rwa [e] at h
  have hw0 := ReciprocityTheory.ChartRestriction.DS.HW.KType.w_ne_zero T
  set k := permK w with hk
  refine ⟨T.V, inferInstance, inferInstance, inferInstance, E, T.w, T.op k T.w, fun a b c d => hrel a b c d rfl rfl,
    fun x y => huni x y rfl, hw0, hhigh, ?_, ?_, ?_, ?_⟩
  · intro W hW hu
    have hW' : ∀ a b, (fun _ : Fin n => true) a = (fun _ : Fin n => true) b → ∀ v ∈ W,
        T.dτ (Matrix.single a b 1) v ∈ W := by
      intro a b _ v hv
      have h1 := hW a b v hv
      rw [hEval] at h1
      exact (W.add_mem_iff_left (W.smul_mem _ hv)).1 h1
    rcases ReciprocityTheory.ChartRestriction.DS.HW.KType.dτ_irred T W hW' with h | h
    · rw [h, Submodule.mem_bot] at hu
      exact absurd hu hw0
    · exact h
  · intro h0
    have hu : star (T.op k) * T.op k = 1 := Unitary.coe_star_mul_self _
    have := congrArg (fun G : T.V →L[ℂ] T.V => G T.w) hu
    simp only [ContinuousLinearMap.mul_apply, h0, map_zero] at this
    exact hw0 this.symm
  · intro x
    rw [hEval, unit_translate, T.w_wt x, if_pos rfl, map_smul, ← add_smul]
    congr 1
    push_cast
    ring
  · intro x y hxy
    have hne : w x ≠ w y := fun e => (ne_of_lt hxy) (w.injective e)
    rw [hEval, unit_translate, T.w_hw x y hxy rfl, if_neg hne]
    simp

end GlobalTheory.CompanionTheory.RealCount.Extremal
end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.FibreJointOpen

theorem continuousOn_fibre_integral_of_subset : ∀ (V X Y : Type) [TopologicalSpace V] [LocallyCompactSpace V] [T2Space V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace X] [LocallyCompactSpace X] [MeasurableSpace X] (μ : Measure V) (ν : Measure X) (f : V → Y) (ι : X → Y) (U : Set V), IsOpen U → ∀ (B : Set X), IsOpen B → ∀ fib : X → Measure V, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν B fib → ∀ (P : Type) [TopologicalSpace P] (W : Set P) (Φ : P → V → ℝ), ContinuousOn (fun p : P × V => Φ p.1 p.2) (W ×ˢ Set.univ) → IsOpen W → ∀ C : Set V, IsCompact C → C ⊆ U → (∀ p ∈ W, ∀ v, v ∉ C → Φ p v = 0) → ContinuousOn (fun q : P × X => ∫ v, Φ q.1 v ∂(fib q.2)) (W ×ˢ B) := by
  intro V X Y _ _ _ _ _ _ _ _ μ ν f ι U hU B hB fib hF P _ W Φ hΦ hW C hC hCU hsupp
  obtain ⟨-, -, h3⟩ := hF

  have hAt : ∀ p ∈ W, ∀ v, ContinuousAt (fun p : P × V => Φ p.1 p.2) (p, v) := fun p hp v =>
    hΦ.continuousAt ((hW.prod isOpen_univ).mem_nhds ⟨hp, Set.mem_univ v⟩)
  have hslice : ∀ p ∈ W, Continuous (Φ p) := fun p hp =>
    continuous_iff_continuousAt.2 fun v =>
      ContinuousAt.comp (f := fun v : V => (p, v)) (g := fun p : P × V => Φ p.1 p.2)
        (hAt p hp v) (by fun_prop)
  have hcs : ∀ p ∈ W, HasCompactSupport (Φ p) := fun p hp =>
    HasCompactSupport.intro hC (hsupp p hp)
  have hts : ∀ p ∈ W, tsupport (Φ p) ⊆ U := fun p hp => by
    refine (closure_minimal ?_ hC.isClosed).trans hCU
    intro v hv
    by_contra hvC
    exact hv (hsupp p hp v hvC)
  have hint : ∀ p ∈ W, ∀ b ∈ B, Integrable (Φ p) (fib b) := fun p hp b hb =>
    (h3 (Φ p) (hslice p hp) (hcs p hp) (hts p hp)).1 b hb

  have hbd : ∀ D : Set X, IsCompact D → D ⊆ B → ∃ c : ℝ≥0, ∀ b ∈ D, fib b C ≤ c := by
    intro D hD hDB
    obtain ⟨φ, hc, hcs', hs, h0, -, hone⟩ := GlobalTheory.CompanionTheory.SW.FibreFam.exists_bump hC hU hCU
    obtain ⟨hi, hco⟩ := h3 φ hc hcs' hs
    obtain ⟨M, hM⟩ := hD.exists_bound_of_continuousOn (hco.mono hDB)
    refine ⟨M.toNNReal, fun b hb => ?_⟩
    calc fib b C ≤ ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib b) :=
          GlobalTheory.CompanionTheory.SW.FibreFam.le_lintegral_bump _ hC h0 hone
      _ = ENNReal.ofReal (∫ v, φ v ∂(fib b)) :=
          (ofReal_integral_eq_lintegral_ofReal (hi b (hDB hb))
            (Filter.Eventually.of_forall h0)).symm
      _ ≤ ENNReal.ofReal M := ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hM b hb))
      _ = (M.toNNReal : ℝ≥0∞) := rfl
  rintro ⟨p₀, b₀⟩ ⟨hp₀, hb₀⟩
  simp only [Set.mem_prod] at hp₀ hb₀ ⊢
  refine ContinuousAt.continuousWithinAt ?_
  obtain ⟨D, hDn, hDB, hDc⟩ := local_compact_nhds (hB.mem_nhds hb₀)
  obtain ⟨c, hc⟩ := hbd D hDc hDB
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  set δ : ℝ := ε / (2 * ((c : ℝ) + 1)) with hδ
  have hc0 : (0 : ℝ) ≤ c := c.2
  have hδ0 : 0 < δ := by positivity

  have htube : ∀ᶠ p in 𝓝 p₀, ∀ v ∈ C, |Φ p v - Φ p₀ v| < δ := by
    refine hC.eventually_forall_of_forall_eventually fun v _ => ?_
    have h1 : ContinuousAt (fun z : P × V => Φ z.1 z.2 - Φ p₀ z.2) (p₀, v) :=
      (hAt p₀ hp₀ v).sub
        (ContinuousAt.comp (f := fun z : P × V => z.2) (g := Φ p₀)
          (hslice p₀ hp₀).continuousAt continuousAt_snd)
    have h2 : Filter.Tendsto (fun z : P × V => Φ z.1 z.2 - Φ p₀ z.2) (𝓝 (p₀, v)) (𝓝 0) := by
      have h3 := h1.tendsto
      simp only [sub_self] at h3
      exact h3
    have h4 := (Metric.tendsto_nhds.1 h2) δ hδ0
    filter_upwards [h4] with z hz
    simpa [Real.dist_eq] using hz
  have hb : ∀ᶠ b in 𝓝 b₀,
      |∫ v, Φ p₀ v ∂(fib b) - ∫ v, Φ p₀ v ∂(fib b₀)| < ε / 2 := by
    have h1 := (((h3 (Φ p₀) (hslice p₀ hp₀) (hcs p₀ hp₀) (hts p₀ hp₀)).2).continuousAt
      (hB.mem_nhds hb₀)).tendsto
    have h2 := (Metric.tendsto_nhds.1 h1) (ε / 2) (by positivity)
    filter_upwards [h2] with b hb
    simpa [Real.dist_eq] using hb
  rw [nhds_prod_eq]
  have hp : ∀ᶠ p in 𝓝 p₀, p ∈ W ∧ ∀ v ∈ C, |Φ p v - Φ p₀ v| < δ :=
    Filter.Eventually.and (hW.mem_nhds hp₀) htube
  have hbb : ∀ᶠ b in 𝓝 b₀, b ∈ D ∧
      |∫ v, Φ p₀ v ∂(fib b) - ∫ v, Φ p₀ v ∂(fib b₀)| < ε / 2 := Filter.Eventually.and hDn hb
  filter_upwards [hp.prod_mk hbb] with q hq
  obtain ⟨⟨hqW, hqt⟩, hqD, hqb⟩ := hq
  obtain ⟨p, b⟩ := q
  simp only at hqW hqt hqD hqb ⊢
  have hbB : b ∈ B := hDB hqD
  have hfin : fib b C < ∞ := (hc b hqD).trans_lt ENNReal.coe_lt_top
  have hdiff : ∫ v, Φ p v ∂(fib b) - ∫ v, Φ p₀ v ∂(fib b)
      = ∫ v in C, (Φ p v - Φ p₀ v) ∂(fib b) := by
    rw [← integral_sub (hint p hqW b hbB) (hint p₀ hp₀ b hbB)]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun v hv => ?_).symm
    rw [hsupp p hqW v hv, hsupp p₀ hp₀ v hv, sub_zero]
  have hreal : (fib b).real C ≤ c := by
    have := ENNReal.toReal_mono ENNReal.coe_ne_top (hc b hqD)
    simpa [Measure.real] using this
  have hle : |∫ v, Φ p v ∂(fib b) - ∫ v, Φ p₀ v ∂(fib b)| ≤ δ * (c : ℝ) := by
    rw [hdiff, ← Real.norm_eq_abs]
    have h5 : ‖∫ v in C, (Φ p v - Φ p₀ v) ∂(fib b)‖ ≤ δ * (fib b).real C :=
      norm_setIntegral_le_of_norm_le_const (C := δ) hfin fun v hv => by
        rw [Real.norm_eq_abs]; exact (hqt v hv).le
    exact h5.trans (mul_le_mul_of_nonneg_left hreal hδ0.le)
  have hδc : δ * (c : ℝ) ≤ ε / 2 := by
    rw [hδ, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  rw [Real.dist_eq]
  calc |∫ v, Φ p v ∂(fib b) - ∫ v, Φ p₀ v ∂(fib b₀)|
      = |(∫ v, Φ p v ∂(fib b) - ∫ v, Φ p₀ v ∂(fib b))
          + (∫ v, Φ p₀ v ∂(fib b) - ∫ v, Φ p₀ v ∂(fib b₀))| := by congr 1; ring
    _ ≤ _ := abs_add_le _ _
    _ < ε := by linarith

end GlobalTheory.CompanionTheory.SW.FibreJointOpen
end

section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin

namespace GlobalTheory.CompanionTheory.CTFin.QdetCoeff

theorem coeff_mem_span_values {M : Type*} [AddCommGroup M] [Module ℂ M] (n : ℕ) (a : ℕ → M)
    (f : ℂ → M) (hf : ∀ u : ℂ, f u = ∑ k ∈ Finset.range (n + 1), u ^ k • a k) (k : ℕ) (hk : k ≤ n) :
    a k ∈ Submodule.span ℂ (Set.range f) := by
  set v : Fin (n + 1) → ℂ := fun i => ((i : ℕ) : ℂ) with hv
  have hinj : Function.Injective v := by
    intro i j h
    simp only [hv, Nat.cast_inj] at h
    exact Fin.ext h
  set V := Matrix.vandermonde v
  have hdet : IsUnit V.det := (Matrix.det_vandermonde_ne_zero_iff.mpr hinj).isUnit
  have hWV : V⁻¹ * V = 1 := Matrix.nonsing_inv_mul V hdet
  set k' : Fin (n + 1) := ⟨k, by omega⟩
  have key : ∑ i : Fin (n + 1), V⁻¹ k' i • f (v i) = a k := by
    simp_rw [hf, Finset.sum_range (fun j => _ • a j), Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul]
    have : ∀ j : Fin (n + 1), ∑ i, V⁻¹ k' i * v i ^ (j : ℕ) = (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) k' j := by
      intro j
      rw [← hWV, Matrix.mul_apply]
      rfl
    simp_rw [this, Matrix.one_apply, ite_smul, one_smul, zero_smul]
    rw [Finset.sum_ite_eq]
    simp [k']
  rw [← key]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨v i, rfl⟩)


open Polynomial GroundTheory.BlockD.FourierDecayAlt.GaugeExists in
theorem qdet_eq_sum_coeff {A : Type} [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A) (w : ℂ) :
    Formalism.REAL.qdet E w = ∑ j ∈ Finset.range (n + 1), w ^ j • (qdetPoly E).coeff j := by
  rw [← evU_qdetPoly E w, evU_apply, eval₂_eq_sum_range' _ (Nat.lt_succ_of_le (natDegree_qdetPoly_le E))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [RingHom.id_apply, ← map_pow, Algebra.smul_def, Algebra.commutes]

open Polynomial GroundTheory.BlockD.FourierDecayAlt.GaugeExists in
theorem qdetPoly_coeff_top {A : Type} [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A) :
    (qdetPoly E).coeff n = 1 := by
  rw [coeff_qdetPoly_top E n (by omega), (prod_linear n _).2.1]

theorem qdet_shift_coeff : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (X : Fin n → Fin n → A) (c : ℂ),
    ∃ a : ℕ → A, a n = 1 ∧ (∀ k, a k ∈ Submodule.span ℂ (Set.range fun u : ℂ => Formalism.REAL.qdet X (u + c))) ∧
      ∀ u : ℂ, Formalism.REAL.qdet X (u + c) = ∑ k ∈ Finset.range (n + 1), u ^ k • a k := by
  intro A _ _ n X c
  set b : ℕ → A := fun j => (GroundTheory.BlockD.FourierDecayAlt.GaugeExists.qdetPoly X).coeff j with hb
  set a : ℕ → A := fun k => ∑ j ∈ Finset.range (n + 1), (c ^ (j - k) * (Nat.choose j k : ℂ)) • b j with ha
  have hexp : ∀ u : ℂ, Formalism.REAL.qdet X (u + c) = ∑ k ∈ Finset.range (n + 1), u ^ k • a k := by
    intro u
    rw [qdet_eq_sum_coeff]
    have hj : ∀ j ∈ Finset.range (n + 1), (u + c) ^ j =
        ∑ m ∈ Finset.range (n + 1), u ^ m * (c ^ (j - m) * (Nat.choose j m : ℂ)) := by
      intro j hj
      rw [add_pow]
      have hsub : Finset.range (j + 1) ⊆ Finset.range (n + 1) := by
        have hj' := Finset.mem_range.mp hj
        intro m hm
        have hm' := Finset.mem_range.mp hm
        exact Finset.mem_range.mpr (by omega)
      rw [← Finset.sum_subset hsub]
      · exact Finset.sum_congr rfl fun m _ => by ring
      · intro m _ hm
        simp only [Finset.mem_range, not_lt] at hm
        rw [Nat.choose_eq_zero_of_lt (by omega)]
        simp
    rw [Finset.sum_congr rfl fun j hjm => by rw [hj j hjm]]
    simp_rw [ha, Finset.sum_smul, Finset.smul_sum, smul_smul]
    exact Finset.sum_comm
  refine ⟨a, ?_, ?_, hexp⟩
  · simp only [ha]
    rw [Finset.sum_eq_single n]
    · simp [hb, qdetPoly_coeff_top]
    · intro j hj hjn
      simp only [Finset.mem_range] at hj
      rw [Nat.choose_eq_zero_of_lt (by omega)]
      simp
    · intro h; simp at h
  · intro k
    by_cases hk : k ≤ n
    · exact coeff_mem_span_values n a _ hexp k hk
    · have : a k = 0 := by
        simp only [ha]
        refine Finset.sum_eq_zero fun j hj => ?_
        simp only [Finset.mem_range] at hj
        rw [Nat.choose_eq_zero_of_lt (by omega)]
        simp
      rw [this]; exact Submodule.zero_mem _

end GlobalTheory.CompanionTheory.CTFin.QdetCoeff
end

section

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.exists_haar_unitary_group : ∀ (n : ℕ) [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)] [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)], ∃ κ : Measure (Matrix.unitaryGroup (Fin n) ℂ), IsFiniteMeasure κ ∧ κ.IsMulRightInvariant ∧ κ.IsOpenPosMeasure := by
  first | exact @GlobalTheory.CompanionTheory.ModelS.exists_rightInvariant_measure_unitaryGroup | exact GlobalTheory.CompanionTheory.ModelS.exists_rightInvariant_measure_unitaryGroup | (intros; apply GlobalTheory.CompanionTheory.ModelS.exists_rightInvariant_measure_unitaryGroup <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise

theorem _root_.GlobalTheory.T.exists_cyclic_vector_of_separable : ∀ (K : Type) [Field K] (n : ℕ) (γ : Matrix (Fin n) (Fin n) K), γ.charpoly.Separable → ∃ v : Fin n → K, ∀ y : Fin n → K, ∃ h : K[X], y = aeval γ h *ᵥ v := by
  first | exact @GlobalTheory.CompanionTheory.TorusCh.CyclicVector.exists_cyclic_vector | exact GlobalTheory.CompanionTheory.TorusCh.CyclicVector.exists_cyclic_vector | (intros; apply GlobalTheory.CompanionTheory.TorusCh.CyclicVector.exists_cyclic_vector <;> assumption)
end
