module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle111
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle127
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormPosOfIsUnit
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
public import Formalism.PeriodIntegrals.Bundle004
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle047
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle128
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicLeviEmbeddingHomomorphismProperties
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicStabilizerRadicalStructure
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingMulVec
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle125
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle123
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaDecompComplexifiedMaxCompact
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Integral.Pi
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MemConfTOfDetNeZero
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.PointLattice

section General

variable {E A n : Type} [Field E] [CommRing A] [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
theorem latUnip_map_mulVec (ι : E →+* A) (M : Matrix n n E) (y : n → E) :
    (fun i => ι ((M *ᵥ y) i)) = M.map ι *ᵥ fun i => ι (y i) := by
  funext i
  exact RingHom.map_mulVec ι M y i

theorem latUnip_conj_pow (X Y G : Matrix n n A) (h : X * Y = 1) (m : ℕ) :
    (Y * G * X - 1) ^ m * Y = Y * (G - 1) ^ m := by
  have h1 : (Y * G * X - 1) * Y = Y * (G - 1) := by
    rw [sub_mul, one_mul, mul_assoc (Y * G), h, mul_one, mul_sub, mul_one]
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, mul_assoc, h1, ← mul_assoc, ih, mul_assoc, ← pow_succ]

end General

theorem lamX_unipMod : ∀ (I : AutInst) (x a : I.GA) (γ : GL (Fin I.n) I.E) (l : ℕ), 1 ≤ l → I.fmat a.2 = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)) → (x⁻¹ * a * x).2 ∈ I.Kset → I.UnipMod l (x⁻¹ * a * x).2 → (∀ y ∈ lamX I x, (γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ y ∈ lamX I x) ∧ ∀ y ∈ lamX I x, ∃ z ∈ lamX I x, (((γ : Matrix (Fin I.n) (Fin I.n) I.E) - 1) ^ I.n) *ᵥ y = (l : I.E) • z := by
  intro I x a γ l hl hfa hk hu
  have hK : ∀ w, w ∈ I.Lf ↔ I.fmat (x⁻¹ * a * x).2 *ᵥ w ∈ I.Lf := hk
  have hmem : ∀ y, y ∈ lamX I x ↔
      I.fmat x.2⁻¹ *ᵥ (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (y i)) ∈ I.Lf := (lamX_selfDual I x).1
  have hconj : I.fmat (x⁻¹ * a * x).2 = I.fmat x.2⁻¹ * I.fmat a.2 * I.fmat x.2 := rfl
  have hXY : I.fmat x.2 * I.fmat x.2⁻¹ = 1 := by
    show I.fmat (x.2 * x.2⁻¹) = 1
    rw [mul_inv_cancel]
    rfl
  have key : ∀ y, I.fmat x.2⁻¹ *ᵥ (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (((γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ y) i)) =
      I.fmat (x⁻¹ * a * x).2 *ᵥ (I.fmat x.2⁻¹ *ᵥ fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (y i)) := by
    intro y
    rw [latUnip_map_mulVec (Formalism.UG.inclE (F := I.F) (Af I.F)) (γ : Matrix (Fin I.n) (Fin I.n) I.E) y, ← hfa, hconj, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, mul_assoc (I.fmat x.2⁻¹ * I.fmat a.2), hXY, mul_one]
  refine ⟨fun y hy => ?_, fun y hy => ?_⟩
  · rw [hmem, key]
    exact (hK _).1 ((hmem y).1 hy)
  · obtain ⟨w, hw, hwe⟩ := hu _ ((hmem y).1 hy)
    have hl0 : (l : I.E) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    refine ⟨(l : I.E)⁻¹ • ((((γ : Matrix (Fin I.n) (Fin I.n) I.E) - 1) ^ I.n) *ᵥ y), ?_, ?_⟩
    · rw [hmem]
      have hpow : (((γ : Matrix (Fin I.n) (Fin I.n) I.E) - 1) ^ I.n).map (Formalism.UG.inclE (F := I.F) (Af I.F)) = (I.fmat a.2 - 1) ^ I.n := by
        rw [hfa, ← RingHom.mapMatrix_apply, map_pow, map_sub, map_one, RingHom.mapMatrix_apply]
      have hcp := latUnip_conj_pow (I.fmat x.2) (I.fmat x.2⁻¹) (I.fmat a.2) hXY I.n
      have e1 : (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (((l : I.E)⁻¹ • ((((γ : Matrix (Fin I.n) (Fin I.n) I.E) - 1) ^ I.n) *ᵥ y)) i)) =
          Formalism.UG.inclE (F := I.F) (Af I.F) ((l : I.E)⁻¹) • fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (((((γ : Matrix (Fin I.n) (Fin I.n) I.E) - 1) ^ I.n) *ᵥ y) i) := by
        funext i
        simp only [Pi.smul_apply, smul_eq_mul, map_mul]
      have e2 : I.fmat x.2⁻¹ *ᵥ (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (((((γ : Matrix (Fin I.n) (Fin I.n) I.E) - 1) ^ I.n) *ᵥ y) i)) =
          (l : TensorProduct I.F I.E (Af I.F)) • w := by
        rw [latUnip_map_mulVec (Formalism.UG.inclE (F := I.F) (Af I.F)) (((γ : Matrix (Fin I.n) (Fin I.n) I.E) - 1) ^ I.n) y, hpow, Matrix.mulVec_mulVec, ← hcp,
          ← Matrix.mulVec_mulVec, ← hconj, hwe]
      rw [e1, Matrix.mulVec_smul, e2, smul_smul, ← map_natCast (Formalism.UG.inclE (F := I.F) (Af I.F)) l, ← map_mul,
        inv_mul_cancel₀ hl0, map_one, one_smul]
      exact hw
    · rw [smul_smul, mul_inv_cancel₀ hl0, one_smul]

end GlobalTheory.PointLattice
end
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.Count.CartanSize

open GlobalTheory.Count.Cartan

theorem cartan_size : ∀ (n : ℕ) (ε : Fin n → Bool), Continuous (fun g : UJ ε => dHS (uMat g)) ∧ (∀ g : UJ ε, 0 ≤ dHS (uMat g) ∧ dOp (uMat g) ≤ dHS (uMat g)) ∧ (∀ g : UJ ε, ∃ k ∈ Kset ε, ∃ X, inP ε X ∧ uMat g = k * NormedSpace.exp X ∧ dHS (uMat g) = Real.sqrt (hs X)) ∧ (rkR ε = 0 → ∀ g : UJ ε, dHS (uMat g) = 0) := by
  intro n ε
  have hU : ∀ g : UJ ε, Formalism.REAL.inUJ ε (uMat g) := fun g => g.2
  have hnn : ∀ g : Matrix (Fin n) (Fin n) ℂ, 0 ≤ dHS g := fun g => Real.sqrt_nonneg _
  obtain ⟨-, hB, -, hC, -⟩ := GlobalTheory.Count.Cartan.cartan_distances n ε
  refine ⟨hC, ?_, ?_, ?_⟩
  · intro g
    refine ⟨hnn _, ?_⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [GlobalTheory.Dec.dOp_fin_zero]
      exact hnn _
    · obtain ⟨h0, -, -, h2, -⟩ := hB g g (by omega)
      have h1 : (1 : ℝ) ≤ Real.sqrt 2 := by
        rw [show (1 : ℝ) = Real.sqrt 1 by simp]
        exact Real.sqrt_le_sqrt (by norm_num)
      nlinarith
  · intro g
    exact ⟨uMat g * NormedSpace.exp (-Formalism.REAL.polarLog (uMat g)), Formalism.REAL.mul_exp_neg_polarLog_mem_compact (hU g),
      Formalism.REAL.polarLog (uMat g), Formalism.REAL.polarLog_mem_hermitian_part (hU g), Formalism.REAL.polar_decomposition_eq,
      GlobalTheory.Count.Cartan.dHS_eq_log (hU g)⟩
  · intro hr g
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [dHS]
    · obtain ⟨-, -, -, -, h3⟩ := hB g g (by omega)
      simp only [hr, Nat.cast_zero, mul_zero, Real.sqrt_zero, zero_mul] at h3
      exact le_antisymm h3 (hnn _)

end GlobalTheory.Count.CartanSize
end
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.SnMass
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.SnMass.QuotUniq

theorem lintegral_le {k r : ℕ} {R : Set (Mat k r)} {μG μR ν ν' : Measure (Mt k r)}
    (hR : IsClosedSub k r R) (hG : IsHaarOn (GG k r) μG) (hμ : IsHaarOn R μR) (hU : IsUnimod R μR)
    (hν : IsQuotMeas μG μR ν) (hν' : IsQuotMeas μG μR ν') (F : Mt k r → ℝ≥0∞) (hF : Measurable F)
    (hFi : ∀ ρ ∈ R, ∀ x, Matrix.of x ∈ GG k r → F (lmulM ρ x) = F x) :
    ∫⁻ x, F x ∂ν ≤ ∫⁻ x, F x ∂ν' := by
  obtain ⟨-, -, φ, hφ, h⟩ := GlobalTheory.Amp.CutQuot.cut_quotient k r R μG μR ν hR hG hμ hU hν
  obtain ⟨h1, -, -⟩ := GlobalTheory.Amp.CutQuot.cut_quotient k r R μG μR ν' hR hG hμ hU hν'
  have h1' : ∀ᵐ x ∂ν', Matrix.of x ∈ GG k r := h1
  have hae : ∀ᵐ s ∂μR, Matrix.of s ∈ R := hμ.2.2.1
  have hW' : ∀ f : Mt k r → ℝ≥0∞, Measurable f →
      ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, f (lmulM (Matrix.of s) x) ∂μR) ∂ν' := hν'
  have hTm := (GlobalTheory.Amp.CutQuot.continuous_act k r).measurable
  rw [h F hF hFi, hW' (fun x => φ x * F x) (hφ.1.mul hF)]
  refine lintegral_mono_ae ?_
  filter_upwards [h1'] with x hx
  have hTx : Measurable fun s : Mt k r => lmulM (Matrix.of s) x :=
    hTm.comp (measurable_id.prodMk measurable_const)
  have h2 : ∫⁻ s, φ (lmulM (Matrix.of s) x) * F (lmulM (Matrix.of s) x) ∂μR =
      ∫⁻ s, φ (lmulM (Matrix.of s) x) * F x ∂μR := by
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with s hs
    rw [hFi _ hs x hx]
  rw [h2, lintegral_mul_const (F x) (f := fun s => φ (lmulM (Matrix.of s) x)) (hφ.1.comp hTx)]
  exact mul_le_of_le_one_left zero_le (hφ.2 x hx)

theorem quot_uniq : ∀ (k r : ℕ) (R : Set (Mat k r)) (μG μR ν ν' : Measure (Mt k r)), IsClosedSub k r R → IsHaarOn (GG k r) μG → IsHaarOn R μR → IsUnimod R μR → IsQuotMeas μG μR ν → IsQuotMeas μG μR ν' → ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] (F : Mat k r → V), ContinuousOn F (GG k r) → (∀ ρ ∈ R, ∀ x ∈ GG k r, F (ρ * x) = F x) → (Integrable (fun x : Mt k r => F (Matrix.of x)) ν ↔ Integrable (fun x : Mt k r => F (Matrix.of x)) ν') ∧ ∫ x, F (Matrix.of x) ∂ν = ∫ x, F (Matrix.of x) ∂ν' := by
  intro k r R μG μR ν ν' hR hG hμ hU hν hν' V _ _ _ F hF hFi
  classical
  borelize V
  set S : Set (Mt k r) := {x | Matrix.of x ∈ GG k r} with hS
  have hSm : MeasurableSet S := GlobalTheory.Amp.CutQuot.measurable_G k r
  have hFc : ContinuousOn (fun x : Mt k r => F (Matrix.of x)) S := hF
  set F' : Mt k r → V := S.piecewise (fun x : Mt k r => F (Matrix.of x)) (fun _ => 0) with hF'
  have hF'm : Measurable F' := hFc.measurable_piecewise continuousOn_const hSm
  have hsep : TopologicalSpace.IsSeparable (Set.range F') := by
    have h1 : TopologicalSpace.IsSeparable ((fun x : Mt k r => F (Matrix.of x)) '' S) :=
      hFc.isSeparable_image (TopologicalSpace.IsSeparable.of_separableSpace S)
    refine (h1.union (Set.finite_singleton (0 : V)).isSeparable).mono ?_
    rintro _ ⟨x, rfl⟩
    by_cases hx : x ∈ S
    · exact Or.inl ⟨x, hx, by rw [hF', Set.piecewise_eq_of_mem _ _ _ hx]⟩
    · exact Or.inr (by rw [hF', Set.piecewise_eq_of_notMem _ _ _ hx]; rfl)
  have hinv : ∀ ρ ∈ R, ∀ x : Mt k r, Matrix.of x ∈ GG k r → F' (lmulM ρ x) = F' x := by
    intro ρ hρ x hx
    have hx' : lmulM ρ x ∈ S := (GlobalTheory.Amp.CutQuot.mul_mem_iff (hR.1 hρ) (Matrix.of x)).2 hx
    rw [hF', Set.piecewise_eq_of_mem _ _ _ hx', Set.piecewise_eq_of_mem _ _ _ (show x ∈ S from hx)]
    exact hFi ρ hρ _ hx
  have hm : MeasurableSpace.comap F' inferInstance ≤ (inferInstance : MeasurableSpace (Mt k r)) :=
    hF'm.comap_le
  have hsm : StronglyMeasurable[MeasurableSpace.comap F' inferInstance] F' :=
    (@stronglyMeasurable_iff_measurable_separable _ _ _ (MeasurableSpace.comap F' inferInstance)
      _ _ _ _).2 ⟨comap_measurable F', hsep⟩
  have htrim : ν.trim hm = ν'.trim hm := by
    refine @Measure.ext _ (MeasurableSpace.comap F' inferInstance) _ _ fun A hA => ?_
    rw [trim_measurableSet_eq hm hA, trim_measurableSet_eq hm hA]
    have hAm : MeasurableSet A := hm A hA
    obtain ⟨B, -, rfl⟩ := hA
    have hi : ∀ ρ ∈ R, ∀ x : Mt k r, Matrix.of x ∈ GG k r →
        (F' ⁻¹' B).indicator (1 : Mt k r → ℝ≥0∞) (lmulM ρ x) = (F' ⁻¹' B).indicator 1 x := by
      intro ρ hρ x hx
      simp only [Set.indicator, Set.mem_preimage, hinv ρ hρ x hx, Pi.one_apply]
    rw [← lintegral_indicator_one hAm, ← lintegral_indicator_one hAm]
    exact le_antisymm (lintegral_le hR hG hμ hU hν hν' _ (measurable_one.indicator hAm) hi)
      (lintegral_le hR hG hμ hU hν' hν _ (measurable_one.indicator hAm) hi)
  have hae : ∀ ν₀ : Measure (Mt k r), IsQuotMeas μG μR ν₀ →
      (fun x : Mt k r => F (Matrix.of x)) =ᵐ[ν₀] F' := by
    intro ν₀ h
    have h1 : ∀ᵐ x ∂ν₀, x ∈ S := (GlobalTheory.Amp.CutQuot.cut_quotient k r R μG μR ν₀ hR hG hμ hU h).1
    filter_upwards [h1] with x hx
    rw [hF', Set.piecewise_eq_of_mem _ _ _ hx]
  rw [integrable_congr (hae ν hν), integrable_congr (hae ν' hν'), integral_congr_ae (hae ν hν),
    integral_congr_ae (hae ν' hν'), integral_trim hm hsm, integral_trim hm hsm, htrim]
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, rfl⟩
  · exact integrable_of_integrable_trim hm (htrim ▸ h.trim hm hsm)
  · exact integrable_of_integrable_trim hm (htrim.symm ▸ h.trim hm hsm)

end GlobalTheory.SnMass.QuotUniq
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

theorem hpk_ne_zero (k r : ℕ) : Hpk k r ≠ 0 := by
  intro h
  have := congrFun (congrFun h ⟨r, by omega⟩) ⟨r, by omega⟩
  simp only [Hpk, Matrix.zero_apply] at this
  split_ifs at this <;> first | omega | norm_num at this | skip
  all_goals simp_all

theorem isMatGroup_of_isClosedSub {k r : ℕ} {S : Set (Mat k r)} (hS : IsClosedSub k r S) :
    PI.IsMatGroup S := by
  obtain ⟨hU, hc, h1, hm, hi⟩ := hS
  refine ⟨hc, h1, hm, fun a ha => ⟨hi a ha, ?_⟩⟩
  by_cases hd : IsUnit a.det
  · exact Matrix.mul_nonsing_inv a hd
  · exfalso
    have h0 : a⁻¹ = 0 := Matrix.nonsing_inv_apply_not_isUnit a hd
    have hmem := hU (hi a ha)
    rw [h0] at hmem
    have : (0 : Mat k r)ᴴ * Hpk k r * 0 = Hpk k r := hmem
    simp at this
    exact hpk_ne_zero k r this.symm

theorem haarOn_unique : ∀ (k r : ℕ) (S : Set (Mat k r)) (μ μ' : Measure (Mt k r)), IsClosedSub k r S →
    IsHaarOn S μ → IsHaarOn S μ' → ∃ c : ENNReal, 0 < c ∧ c < ⊤ ∧ μ' = c • μ := by
  intro k r S μ μ' hS hμ hμ'
  exact (GlobalTheory.MatHaar.haar_unique_locFinite_openPos (2 * r + k + 1) S μ (isMatGroup_of_isClosedSub hS) hμ).1 μ' hμ'

end GlobalTheory.SgInf
end

section

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.SgInf

variable {k r : ℕ}

theorem Hpk_ne_zero' (k r : ℕ) : Hpk k r ≠ 0 := by
  intro h
  have h1 : Hpk k r ⟨r + k, by omega⟩ ⟨r + k, by omega⟩ = -1 := by
    simp [Hpk]
  rw [h] at h1
  simp at h1

theorem IsClosedSub.mul_inv {S : Set (Mat k r)} (hS : IsClosedSub k r S) {a : Mat k r} (ha : a ∈ S) :
    a * a⁻¹ = 1 := by
  by_cases hd : IsUnit a.det
  · exact Matrix.mul_nonsing_inv a hd
  · exfalso
    have h0 : a⁻¹ = 0 := Matrix.nonsing_inv_apply_not_isUnit a hd
    have hm : a⁻¹ ∈ GG k r := hS.1 (hS.2.2.2.2 a ha)
    rw [h0] at hm
    have : (0 : Mat k r)ᴴ * Hpk k r * 0 = Hpk k r := hm
    simp at this
    exact Hpk_ne_zero' k r this.symm

theorem IsClosedSub.isMatGroup {S : Set (Mat k r)} (hS : IsClosedSub k r S) : PI.IsMatGroup S :=
  ⟨hS.2.1, hS.2.2.1, hS.2.2.2.1, fun a ha => ⟨hS.2.2.2.2 a ha, hS.mul_inv ha⟩⟩

theorem haarOn_locFinite_openPos :
    ∀ (k r : ℕ) (S : Set (Mat k r)) (μ : Measure (Mt k r)), IsClosedSub k r S → IsHaarOn S μ →
      (∀ C : Set (Mt k r), IsCompact C → μ C < ⊤) ∧
      (∀ U : Set (Mt k r), IsOpen U → (∃ x ∈ U, Matrix.of x ∈ S) → 0 < μ U) := by
  intro k r S μ hS hμ
  have hμ' : PI.IsHaarOnM S μ := hμ
  obtain ⟨-, hK, hU⟩ := GlobalTheory.MatHaar.haar_unique_locFinite_openPos _ S μ hS.isMatGroup hμ'
  refine ⟨fun C hC => ?_, hU⟩
  have hA : IsClosed {x : Mt k r | Matrix.of x ∈ S} := hS.2.1
  have h1 : μ C ≤ μ (C ∩ {x : Mt k r | Matrix.of x ∈ S}) + μ (C \ {x : Mt k r | Matrix.of x ∈ S}) :=
    measure_le_inter_add_sdiff μ C _
  have h2 : μ (C \ {x : Mt k r | Matrix.of x ∈ S}) = 0 :=
    measure_mono_null (fun x hx => hx.2) hμ.2.2.1
  have h3 : μ (C ∩ {x : Mt k r | Matrix.of x ∈ S}) < ⊤ :=
    hK _ (hC.inter_right hA) (fun x hx => hx.2)
  rw [h2, add_zero] at h1
  exact lt_of_le_of_lt h1 h3

end GlobalTheory.SgInf
end
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.cutoff_computes_besselQuotientIntegral : ∀ (k r : ℕ) (R : Set (Mat k r)) (μG μR ν : Measure (Mt k r)), IsClosedSub k r R → IsHaarOn (GG k r) μG → IsHaarOn R μR → IsUnimod R μR → IsQuotMeas μG μR ν → ν {x | Matrix.of x ∉ GG k r} = 0 ∧ (∀ A : Set (Mt k r), MeasurableSet A → (∀ ρ ∈ R, ∀ x, Matrix.of x ∈ GG k r → (lmulM ρ x ∈ A ↔ x ∈ A)) → μG A = 0 → ν A = 0) ∧ ∃ φ, SubCut (GG k r) μR φ ∧ ∀ F : Mt k r → ℝ≥0∞, Measurable F → (∀ ρ ∈ R, ∀ x, Matrix.of x ∈ GG k r → F (lmulM ρ x) = F x) → ∫⁻ x, F x ∂ν = ∫⁻ x, φ x * F x ∂μG := by
  first | exact @GlobalTheory.Amp.CutQuot.cut_quotient | exact GlobalTheory.Amp.CutQuot.cut_quotient | (intros; apply GlobalTheory.Amp.CutQuot.cut_quotient <;> assumption)
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.isotropicLeviEmbedding_homomorphism_properties : ∀ k r : ℕ, (∀ u u' : Matrix (Fin r) (Fin r) ℂ, IsUnit u.det → IsUnit u'.det → uEmb k r (u * u') = uEmb k r u * uEmb k r u') ∧ uEmb k r 1 = 1 ∧ (∀ u : Matrix (Fin r) (Fin r) ℂ, IsUnit u.det → uEmb k r u ∈ GG k r ∧ (uEmb k r u)⁻¹ = uEmb k r u⁻¹ ∧ (∀ b : Fin r, uEmb k r u *ᵥ bvec (eI k r b) = ∑ a, u a b • bvec (eI k r a)) ∧ (∀ b : Fin r, uEmb k r u *ᵥ bvec (esI k r b) = ∑ a, star (u⁻¹ b a) • bvec (esI k r a)) ∧ ∀ w, inWb k r w → uEmb k r u *ᵥ w = w) ∧ (∀ x : UT r → ℂ, (upper x).det = 1 ∧ uEmb k r (upper x) ∈ Nset k r) := by
  first | exact @GlobalTheory.Amp.UEmb.uEmb_hom | exact GlobalTheory.Amp.UEmb.uEmb_hom | (intros; apply GlobalTheory.Amp.UEmb.uEmb_hom <;> assumption)
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.isotropicStabilizerRadical_structure : ∀ k r : ℕ, (∀ (B : Fin r → Fin (k + 1) → ℂ) (S : Matrix (Fin r) (Fin r) ℂ), (∀ a : Fin r, pEl k r B S *ᵥ bvec (eI k r a) = bvec (eI k r a)) ∧ (∀ j : Fin (k + 1), pEl k r B S *ᵥ bvec (wI k r j) = bvec (wI k r j) - ∑ b, herm (Hb k) (bvec j) (B b) • bvec (eI k r b)) ∧ (∀ b : Fin r, pEl k r B S *ᵥ bvec (esI k r b) = bvec (esI k r b) + (∑ j, B b j • bvec (wI k r j)) + ∑ a, (S a b - herm (Hb k) (B b) (B a) / 2) • bvec (eI k r a)) ∧ (Sᴴ = -S → pEl k r B S ∈ Nset k r ∧ (pEl k r B S)⁻¹ = pEl k r (-B) (-S))) ∧ (∀ (s : UT r → ℂ) (t : Fin r → ℝ), (skewM s t)ᴴ = -skewM s t) ∧ (∀ S : Matrix (Fin r) (Fin r) ℂ, Sᴴ = -S → ∃! p : (UT r → ℂ) × (Fin r → ℝ), S = skewM p.1 p.2) ∧ (∀ B B' (S S' : Matrix (Fin r) (Fin r) ℂ), pEl k r B S * pEl k r B' S' = pEl k r (B + B') (S + S' + Matrix.of fun a b => (herm (Hb k) (B b) (B' a) - herm (Hb k) (B' b) (B a)) / 2)) ∧ ∀ m ∈ UH (Hb k), mEmb k r m ∈ GG k r ∧ (mEmb k r m)⁻¹ = mEmb k r m⁻¹ := by
  first | exact @GlobalTheory.Amp.Rad.radical | exact GlobalTheory.Amp.Rad.radical | (intros; apply GlobalTheory.Amp.Rad.radical <;> assumption)
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.GramVol

theorem vol_gram_codim_three : ∀ (k r : ℕ), 1 ≤ r → 2 * r + 6 ≤ k → ∀ m ∈ UH (Hb k), ∀ P₀ : Submodule ℂ (EuclideanSpace ℂ (Fin (k + 1))), (Module.finrank ℂ P₀ = k - 2 ∨ Module.finrank ℂ P₀ = k - 1) → volume {B : Fin r → Fin (k + 1) → ℂ | gramProj P₀ (fun b => m⁻¹ *ᵥ B b) = 0} = 0 ∧ ∀ R' y : ℝ, 1 ≤ R' → 0 < y → volume {B : Fin r → Fin (k + 1) → ℂ | (∀ b, eucl (m⁻¹ *ᵥ B b) ≤ R') ∧ y < gramProj P₀ (fun b => m⁻¹ *ᵥ B b) ∧ gramProj P₀ (fun b => m⁻¹ *ᵥ B b) ≤ 2 * y} ≤ ENNReal.ofReal ((Real.pi * R' ^ 2) ^ (3 * r) * 4 * R' ^ (2 * r ^ 2 + 2 * r) * Real.pi ^ (r ^ 2) * (Real.pi * Real.exp 1 / ((k - 2 - r : ℕ) : ℝ)) ^ (r * (k - 2 - r)) * (2 * y) ^ (2 * (k - 2 - r))) := by
  intro k j _ hjk m hm P hP0
  have hP : k - 2 ≤ Module.finrank ℂ P := by omega
  obtain ⟨d, rfl⟩ : ∃ d, k = d + 2 := ⟨k - 2, by omega⟩
  have hd : d + 2 - 2 = d := by omega
  rw [hd] at hP ⊢
  have key := vol_le d 3 j (by omega) m⁻¹ (norm_det_inv_eq_one hm) P hP
  obtain ⟨s, hs⟩ : ∃ s, d = j + s := ⟨d - j, by omega⟩
  have hs1 : 1 ≤ s := by omega
  have hs2 : d - j = s := by omega
  rw [hs2] at key ⊢
  refine ⟨?_, fun M y hM hy => ?_⟩
  · have hz : ∀ N : ℕ, volume {B : Fin j → Fin (d + 2 + 1) → ℂ | (∀ b, eucl (m⁻¹ *ᵥ B b) ≤ (N : ℝ) + 1) ∧
        gramProj P (fun b => m⁻¹ *ᵥ B b) ≤ 0} = 0 := fun N => by
      have := key ((N : ℝ) + 1) 0 (by positivity) le_rfl
      rw [zero_pow (by omega)] at this
      simpa using this
    refine measure_mono_null ?_ (measure_iUnion_null hz)
    intro B hB
    obtain ⟨N, hN⟩ := exists_nat_ge (∑ b, eucl (m⁻¹ *ᵥ B b))
    refine Set.mem_iUnion.2 ⟨N, fun b => ?_, le_of_eq hB⟩
    have : eucl (m⁻¹ *ᵥ B b) ≤ ∑ b, eucl (m⁻¹ *ᵥ B b) :=
      Finset.single_le_sum (f := fun b => eucl (m⁻¹ *ᵥ B b)) (fun _ _ => Real.sqrt_nonneg _) (Finset.mem_univ b)
    linarith
  · refine le_trans (measure_mono fun B hB => ?_)
      (le_trans (key M (2 * y) (by positivity) (by positivity)) (ENNReal.ofReal_le_ofReal ?_))
    · exact ⟨hB.1, hB.2.2⟩
    have hpi := Real.pi_pos
    have h1 : (1 / (s.factorial : ℝ)) ^ j ≤ ((Real.exp 1 / s) ^ s) ^ j :=
      pow_le_pow_left₀ (by positivity) (inv_factorial_le s hs1) j
    have h2 : M ^ (2 * j ^ 2) ≤ 4 * M ^ (2 * j ^ 2 + 2 * j) := by
      have h3 : M ^ (2 * j ^ 2) ≤ M ^ (2 * j ^ 2 + 2 * j) := pow_le_pow_right₀ hM (Nat.le_add_right _ _)
      have h4 : 0 ≤ M ^ (2 * j ^ 2 + 2 * j) := by positivity
      linarith
    calc _ = (Real.pi * M ^ 2) ^ (3 * j) * M ^ (2 * j ^ 2) * Real.pi ^ (j ^ 2) *
          (Real.pi ^ (j * s) * (1 / (s.factorial : ℝ)) ^ j) * (2 * y) ^ (2 * s) := by
          rw [hs, mul_add j j s, pow_add, ← sq j, one_div, inv_pow, div_eq_mul_inv]; ring
      _ ≤ (Real.pi * M ^ 2) ^ (3 * j) * (4 * M ^ (2 * j ^ 2 + 2 * j)) * Real.pi ^ (j ^ 2) *
          (Real.pi ^ (j * s) * ((Real.exp 1 / s) ^ s) ^ j) * (2 * y) ^ (2 * s) := by gcongr
      _ = _ := by
          rw [← pow_mul (Real.exp 1 / s), mul_comm s j, ← mul_pow, mul_div_assoc, mul_assoc _ (4 : ℝ)]

end GlobalTheory.Amp.GramVol
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.Dec

theorem isFdegG_tensor (B : RowsAut) (d : InfinitePlace B.I.F → ℝ)
    (hU : ∀ v, IsURepOn (UJset (B.I.ε v)) (B.σ v)) (hF : ∀ v, IsFdeg (muG (B.I.ε v)) (B.σ v) (d v)) :
    IsFdegG (muInf B.I) B.σs (∏ v, d v) := by
  have hd : 0 < ∏ v, d v := Finset.prod_pos fun v _ => (hF v).1
  obtain ⟨hi, hs, hdense⟩ := B.tens_spec
  refine isFdegG_of_total B.I.Ginf (muInf B.I) B.Hs B.σs (∏ v, d v) (Set.range B.tens)
    (GlobalTheory.HilbTensorUnitary.isURep_rows B hU) hd hdense ?_
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ _ ⟨x', rfl⟩ _ ⟨y', rfl⟩

  have hfun : (fun g : B.I.Ginf => ⟪B.tens y, B.σs g (B.tens x)⟫_ℂ * star ⟪B.tens y', B.σs g (B.tens x')⟫_ℂ) =
      fun g => ∏ v, (coefOn (B.σ v) (x v) (y v) (g v) * star (coefOn (B.σ v) (x' v) (y' v) (g v))) := by
    funext g
    rw [hs, hs, hi, hi, star_prod, ← Finset.prod_mul_distrib]
    rfl
  have hloc := fun v => (hF v).2 (x v) (y v) (x' v) (y' v)
  rw [hfun]
  unfold muInf
  refine ⟨Integrable.fintype_prod_dep fun v => (hloc v).1, ?_⟩
  refine (integral_fintype_prod_eq_prod (μ := fun v => muG (B.I.ε v))
    (fun v g => coefOn (B.σ v) (x v) (y v) g * star (coefOn (B.σ v) (x' v) (y' v) g))).trans ?_
  rw [Finset.prod_congr rfl fun v _ => (hloc v).2, hi, hi, Finset.prod_div_distrib, Finset.prod_mul_distrib]
  push_cast
  rfl

theorem tensorRep : TensorRep := by
  intro B d hB
  have hU : ∀ v, IsURepOn (UJset (B.I.ε v)) (B.σ v) := fun v => (hB v).2.1.2.2.1
  have hF : ∀ v, IsFdeg (muG (B.I.ε v)) (B.σ v) (d v) := fun v => (hB v).2.2.2
  have hG := isFdegG_tensor B d hU hF
  obtain ⟨hi, hs, -⟩ := B.tens_spec
  refine ⟨GlobalTheory.HilbTensorUnitary.isURep_rows B hU, (isIrr_and_dense_of_isFdegG _ _ _ _ _ hG).1, hG, ?_, ?_⟩
  ·
    have h1 : ⟪B.tens B.w, B.tens B.w⟫_ℂ = 1 := by
      rw [hi]
      refine Finset.prod_eq_one fun v _ => ?_
      rw [inner_self_eq_norm_sq_to_K, (hB v).2.2.1.1]
      simp
    have h2 : ‖B.tens B.w‖ ^ 2 = 1 := by
      rw [← inner_self_eq_norm_sq (𝕜 := ℂ), h1]
      simp
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h2
  · intro g
    rw [hs, hi]
    rfl

end GlobalTheory.Dec
end

section

open GlobalTheory.Dec

theorem _root_.GlobalTheory.T.iwasawa_decomp_complexifiedMaxCompact : IwasawaKC := by
  first | exact @GlobalTheory.Dec.iwasawaKC | exact GlobalTheory.Dec.iwasawaKC | (intros; apply GlobalTheory.Dec.iwasawaKC <;> assumption)
end

end

section

@[expose] public section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.SnMass
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.integral_eq_of_quotientMeasures_besselUnitary : ∀ (k r : ℕ) (R : Set (Mat k r)) (μG μR ν ν' : Measure (Mt k r)), IsClosedSub k r R → IsHaarOn (GG k r) μG → IsHaarOn R μR → IsUnimod R μR → IsQuotMeas μG μR ν → IsQuotMeas μG μR ν' → ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] (F : Mat k r → V), ContinuousOn F (GG k r) → (∀ ρ ∈ R, ∀ x ∈ GG k r, F (ρ * x) = F x) → (Integrable (fun x : Mt k r => F (Matrix.of x)) ν ↔ Integrable (fun x : Mt k r => F (Matrix.of x)) ν') ∧ ∫ x, F (Matrix.of x) ∂ν = ∫ x, F (Matrix.of x) ∂ν' := by
  first | exact @GlobalTheory.SnMass.QuotUniq.quot_uniq | exact GlobalTheory.SnMass.QuotUniq.quot_uniq | (intros; apply GlobalTheory.SnMass.QuotUniq.quot_uniq <;> assumption)

end
end
