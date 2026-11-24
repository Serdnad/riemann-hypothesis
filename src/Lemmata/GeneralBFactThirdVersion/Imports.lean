module

public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.NumberTheory.NumberField.Basic
import Lemmata.GeneralBFactAltForm.Imports
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

@[expose] public section

namespace Bl.general_b_fact_third_version

open NumberField in
theorem goal1 {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V]
    [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
    (Λ : Submodule (𝓞 E) V) (hΛ : Submodule.IsFullLattice E Λ) (v : V) :
    ∃ m : ℕ, m ≠ 0 ∧ (m : E) • v ∈ Λ := by
  obtain ⟨d, hd, hdv⟩ :=
    Bl.general_b_fact_alt_form.goal1 (F := E) Λ (x := v) (by simp [hΛ.span_eq_top])
  let I : Ideal (𝓞 E) := Ideal.span {d}
  have hI : I ≠ ⊥ := by simpa only [I, ne_eq, Ideal.span_singleton_eq_bot] using hd
  have hnorm : I.absNorm ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr hI
  obtain ⟨a, ha⟩ := (Ideal.mem_span_singleton' (y := d)).mp (Ideal.absNorm_mem I)
  refine ⟨I.absNorm, hnorm, ?_⟩
  rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul (𝓞 E), ← ha, mul_smul]
  exact Λ.smul_mem a hdv

end Bl.general_b_fact_third_version
