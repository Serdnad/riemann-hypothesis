import Mathlib

noncomputable section

namespace UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl

def IsIntP : {p : ℕ} →
  [inst : Fact (Nat.Prime p)] → ℂ_[p] → Prop :=
fun {p} [Fact (Nat.Prime p)] x => ‖x‖ ≤ 1

theorem aux2 : ∀ {p : ℕ} [inst : Fact (Nat.Prime p)],
  IsTopologicalDivisionRing (PadicAlgCl p) := by
  intro p inst
  exact Valued.isTopologicalDivisionRing

theorem aux3 : ∀ {p : ℕ} [inst : Fact (Nat.Prime p)],
  CompletableTopField (PadicAlgCl p) := by
  intro p inst
  exact NormedField.instCompletableTopField

theorem aux4 : ∀ {p : ℕ} [inst : Fact (Nat.Prime p)],
  IsUniformAddGroup (PadicAlgCl p) := by
  intro p inst
  exact Valued.toIsUniformAddGroup

def IntegralMv.{u_1} : {σ : Type u_1} →
  {p : ℕ} → [inst : Fact (Nat.Prime p)] → MvPowerSeries σ ℂ_[p] → Prop :=
fun {σ} {p} [Fact (Nat.Prime p)] F => ∀ (n : σ →₀ ℕ), IsIntP ((MvPowerSeries.coeff n) F)

theorem intMv_X.{u_1} : ∀ {p : ℕ}
  [inst : Fact (Nat.Prime p)] {σ : Type u_1} (i : σ), IntegralMv (p := p) (MvPowerSeries.X i) := by
  intro p inst σ i n
  classical
  change ‖(MvPowerSeries.coeff n (MvPowerSeries.X i : MvPowerSeries σ ℂ_[p]) : ℂ_[p])‖ ≤ 1
  rw [MvPowerSeries.coeff_X]
  split_ifs
  · exact norm_one.le
  · rw [norm_zero]
    exact zero_le_one

end UpperTheory.Reformulated.B.IntegralPolynomialOverPadicAlgCl
