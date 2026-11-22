import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EagonNorthcottIntegral.YHom
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EagonNorthcottIntegral.DivisionPartitionTotal

noncomputable section

namespace PI.EagonNorthcottZ

open MvPolynomial

private def mon {D : ℕ} (α : Fin D → ℕ) : Fin D ⊕ Fin D →₀ ℕ := ∑ i, Finsupp.single (Sum.inr i) (α i)

private def yp {D : ℕ} (α : Fin D → ℕ) : P D := ∏ i, ys i ^ α i

private lemma mon_inl {D : ℕ} (α : Fin D → ℕ) (i : Fin D) : mon α (Sum.inl i) = 0 := by
  classical
  simp [mon, Finsupp.finsetSum_apply]

private lemma yp_eq {D : ℕ} (α : Fin D → ℕ) : yp α = monomial (mon α) (1 : ℤ) := by
  rw [yp, mon, monomial_sum_one]
  simp [ys, X_pow_eq_monomial]

private lemma noX_iff {D : ℕ} (f : P D) : NoX f ↔ ∃ g, rename Sum.inr g = f := Iff.rfl

private lemma yhom_smul {D a : ℕ} (c : ℤ) {f : P D} (hf : YHom a f) : YHom a (c • f) :=
  fun m hm => hf m (support_smul hm)

private lemma K_add {D : ℕ} (t : Fin D → P D) (ω η : W D) : K t (ω + η) = K t ω + K t η := by
  funext J
  simp [K, mul_add, Finset.sum_add_distrib]

private lemma K_smul {D : ℕ} (t : Fin D → P D) (c : ℤ) (ω : W D) : K t (c • ω) = c • K t ω := by
  funext J
  simp only [K, Pi.smul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_smul_comm]

private lemma isZL_iff {D a j : ℕ} (ω : W D) : IsZL a j ω ↔
    (((∀ J, J.card ≠ j → ω J = 0) ∧ ∀ J, YHom a (ω J)) ∧ K ys ω = 0) ∧ ∀ J, NoX (ω J) := Iff.rfl

private def G (D a : ℕ) : Set (W D) :=
  Set.range fun p : Finset (Fin D) × {α // α ∈ Finset.piAntidiag (Finset.univ : Finset (Fin D)) a} =>
    (Pi.single p.1 (yp p.2.1) : W D)

end PI.EagonNorthcottZ
