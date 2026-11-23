module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle015
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle045
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle057
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle060
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle061
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle062
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasFlagDepthAtLeastOfFreeEntriesVanish
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

theorem _root_.GlobalTheory.T.scaledSkewLattice_fundamentalDomain_of_imaginaryParts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (I : FractionalIdeal (𝓞 E)⁰ E), (∀ x ∈ I, σ x ∈ I) → ∀ (θ : 𝓞 E), (θ : E) + σ θ = 1 → ∀ (c : ℝ), 0 < c → ∀ (D : Set (InfinitePlace E → ℝ)) (m : ℝ≥0∞), MeasurableSet D → (∀ y, ∃! l, l ∈ {b | ∃ x ∈ I, imV x = b} ∧ y + l ∈ D) → volume D = m → HasDom volume (skewLat (σ : E →+* E) I c : Set (InfinitePlace E → ℝ)) (ENNReal.ofReal ((2 * c) ^ Fintype.card (InfinitePlace E)) * m) := by
  first | exact @GlobalTheory.SnMass.SkewDom.skewDom | exact GlobalTheory.SnMass.SkewDom.skewDom | (intros; apply GlobalTheory.SnMass.SkewDom.skewDom <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

theorem _root_.GlobalTheory.T.re_antidiagonal_entry_eq_zero_of_flagDepth : ∀ (k r : ℕ) (x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a : Fin r), x ∈ Nset k r → Dep k r (2 * r - 2 * a.val) (x - 1) → (x (eI k r a) (esI k r a)).re = 0 := by
  first | exact @GlobalTheory.SnMass.VolN.re_corner_eq_zero | exact GlobalTheory.SnMass.VolN.re_corner_eq_zero | (intros; apply GlobalTheory.SnMass.VolN.re_corner_eq_zero <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

theorem _root_.GlobalTheory.T.unipotentBlockEntries_mul_of_hasFlagDepthAtLeast : ∀ (k r : ℕ) (g x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (d : ℕ), Dep k r d (g - 1) → Dep k r 1 (x - 1) → ∀ β : Bk r, degB r β ≤ d → cM k r β (Matrix.of.symm (g * x)) = cM k r β (Matrix.of.symm x) + cM k r β (Matrix.of.symm g) := by
  first | exact @GlobalTheory.SnMass.VolN.cM_mul_of_dep | exact GlobalTheory.SnMass.VolN.cM_mul_of_dep | (intros; apply GlobalTheory.SnMass.VolN.cM_mul_of_dep <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

theorem _root_.GlobalTheory.T.flagUnipotent_block_upper_unitriangular : ∀ (k r : ℕ) (x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ), x ∈ Nset k r → Dep k r 1 (x - 1) := by
  first | exact @GlobalTheory.SnMass.VolN.DepOne.dep_one | exact GlobalTheory.SnMass.VolN.DepOne.dep_one | (intros; apply GlobalTheory.SnMass.VolN.DepOne.dep_one <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

theorem _root_.GlobalTheory.T.integralUnipotent_mem_modelUnipotentAtPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ γ ∈ GN (σ : E →+* E) J Λ P, ∀ w, gM A γ w ∈ Nset k r := by
  first | exact @GlobalTheory.SnMass.VolN.gM_mem_Nset | exact GlobalTheory.SnMass.VolN.gM_mem_Nset | (intros; apply GlobalTheory.SnMass.VolN.gM_mem_Nset <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

theorem _root_.GlobalTheory.T.unipotentRadical_blockCovolumes_prod : ∀ (d : ℝ) (f k r : ℕ) (s : Fin r → ℝ), 0 < d → (∀ a, 0 < s a) → (2 : ℝ) ^ (f * (r * (r - 1) + r * (k + 1))) * ((∏ p : UTr r, (2⁻¹ : ℝ) ^ f * d ^ (1 - 2 * ((r - p.1.1.val : ℕ) : ℝ) + 2 * ((r - p.1.2.val : ℕ) : ℝ)) * (s p.1.1 / s p.1.2) ^ (2 * f)) * (∏ a : Fin r, ((2⁻¹ : ℝ) ^ f * d ^ (1 - 2 * ((r - a.val : ℕ) : ℝ)) * s a ^ (2 * f)) ^ (k + 1)) * (∏ p : UTr r, (2⁻¹ : ℝ) ^ f * d ^ (1 - 2 * ((r - p.1.1.val : ℕ) : ℝ) - 2 * ((r - p.1.2.val : ℕ) : ℝ)) * (s p.1.1 * s p.1.2) ^ (2 * f)) * ∏ a : Fin r, d ^ (1 / 2 - 2 * ((r - a.val : ℕ) : ℝ)) * (s a ^ 2) ^ f) = d ^ (-(((k : ℝ) + 1) * (r : ℝ) ^ 2) - 4 * ((r : ℝ) ^ 3 - r) / 3 - 3 * (r : ℝ) / 2) * (∏ a : Fin r, s a ^ (4 * (r - (a : ℕ)) + 2 * k)) ^ f := by
  first | exact @GlobalTheory.SnMass.VolN.covol_blocks_prod | exact GlobalTheory.SnMass.VolN.covol_blocks_prod | (intros; apply GlobalTheory.SnMass.VolN.covol_blocks_prod <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

theorem _root_.GlobalTheory.T.integralUnipotentRadical_forms_unit_subgroup : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → (∃ G : Subgroup (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E)ˣ, ∀ u : (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E)ˣ, u ∈ G ↔ (u : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) ∈ GN (σ : E →+* E) J Λ P) ∧ ∀ γ ∈ GN (σ : E →+* E) J Λ P, IsUnit γ := by
  first | exact @GlobalTheory.SnMass.VolN.gN_subgroup | exact GlobalTheory.SnMass.VolN.gN_subgroup | (intros; apply GlobalTheory.SnMass.VolN.gN_subgroup <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

theorem _root_.GlobalTheory.T.rowIsometry_entries_in_modelCoordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ (a : Fin r) (y : Fin (2 * r + k + 1) → E) (t : E) (w : InfinitePlace E) (i j : Fin (2 * r + k + 1)), gM A (rowE (σ : E →+* E) J (fun i => P i a.castSucc) y t) w i j = (if i = j then 1 else 0) + (if j = esI k r a then (s a : ℂ) * (((A w).mulVec fun l => w.embedding (y l)) i + (if i = eI k r a then (s a : ℂ) * w.embedding t else 0)) else 0) - (if i = eI k r a then (s a : ℂ) * herm (Hpk k r) (bvec j) ((A w).mulVec fun l => w.embedding (y l)) else 0) := by
  first | exact @GlobalTheory.SnMass.VolN.rowE_entries | exact GlobalTheory.SnMass.VolN.rowE_entries | (intros; apply GlobalTheory.SnMass.VolN.rowE_entries <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

theorem _root_.GlobalTheory.T.unipotentModelAction_isAction_and_faithful : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → (∀ x, actM A 1 x = x) ∧ (∀ γ γ' x, actM A (γ * γ') x = actM A γ (actM A γ' x)) ∧ ∀ γ, (∀ w, gM A γ w = 1) → γ = 1 := by
  first | exact @GlobalTheory.SnMass.VolN.actLaws | exact GlobalTheory.SnMass.VolN.actLaws | (intros; apply GlobalTheory.SnMass.VolN.actLaws <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

theorem _root_.GlobalTheory.T.integralUnipotent_corner_entry_mem_idealLattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ γ ∈ GN (σ : E →+* E) J Λ P, ∀ p : UTr r, (fun w => gM A γ w (eI k r p.1.1) (esI k r p.1.2)) ∈ ideLat (dInv E (r - p.1.1.val) * dInv E (r - p.1.2.val)) (s p.1.1 * s p.1.2) := by
  first | exact @GlobalTheory.SnMass.VolN.corner_entry_mem_ideLat | exact GlobalTheory.SnMass.VolN.corner_entry_mem_ideLat | (intros; apply GlobalTheory.SnMass.VolN.corner_entry_mem_ideLat <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

theorem _root_.GlobalTheory.T.integralUnipotent_entry_mem_inverseDifferentLattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ γ ∈ GN (σ : E →+* E) J Λ P, ∀ p : UTr r, (fun w => gM A γ w (eI k r p.1.1) (eI k r p.1.2)) ∈ ideLat (dInv E (r - p.1.1.val) * (dInv E (r - p.1.2.val))⁻¹) (s p.1.1 / s p.1.2) := by
  first | exact @GlobalTheory.SnMass.VolN.gM_entry_mem_ideLat | exact GlobalTheory.SnMass.VolN.gM_entry_mem_ideLat | (intros; apply GlobalTheory.SnMass.VolN.gM_entry_mem_ideLat <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

theorem _root_.GlobalTheory.T.hasFlagDepthAtLeast_of_free_entries_vanish : ∀ (k r : ℕ) (x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (d : ℕ), x ∈ Nset k r → (∀ β : Bk r, degB r β < d → cM k r β (Matrix.of.symm x) = 0) → Dep k r d (x - 1) := by
  first | exact @GlobalTheory.SnMass.VolN.dep_of_free_coords | exact GlobalTheory.SnMass.VolN.dep_of_free_coords | (intros; apply GlobalTheory.SnMass.VolN.dep_of_free_coords <;> assumption)
end
