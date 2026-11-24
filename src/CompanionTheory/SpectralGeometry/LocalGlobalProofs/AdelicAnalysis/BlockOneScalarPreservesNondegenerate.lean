module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StageData
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HyperbolicAndBlockOneNondegenerate

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂

theorem det_blockOne_eq_mul {K : Type} [CommRing K] {M : ℕ} (t : K) (A : Matrix (Fin M) (Fin M) K) :
    (blockOne t A).det = t * A.det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  have hsub : (Matrix.of (Fin.cons (Fin.cons t fun _ ↦ 0) fun i ↦ Fin.cons 0 (A i)) :
      Matrix (Fin (M + 1)) (Fin (M + 1)) K).submatrix Fin.succ Fin.succ = A := by
    ext i j
    simp
  simp [blockOne, hsub]

theorem isHermND_blockOne_algebraMap : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ t : F, t ≠ 0 → IsHermND σ (blockOne (algebraMap F E t) J) := by
  intros; apply _root_.GlobalTheory.CompanionTheory.SW.BlockForm.isHermND_blockOne <;> assumption

end GlobalTheory.CompanionTheory.SW.PiLocalization₂
