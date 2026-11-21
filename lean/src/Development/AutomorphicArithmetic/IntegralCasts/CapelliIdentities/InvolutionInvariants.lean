import Mathlib

/-!
For each signature matrix, right-translation invariance of Haar measure on its
indefinite unitary group implies invariance under inversion.
-/

open Matrix MeasureTheory MeasureTheory.Measure

noncomputable section

namespace UpperTheory.Reformulated.B.InvolutionInvariants

def Jm {n : ℕ} (ε : Fin n → Bool) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun a ↦ if ε a then 1 else -1

def inUJ {n : ℕ} (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  gᴴ * Jm ε * g = Jm ε

private theorem units_preserve_mul {A : Type*} [Monoid A] [StarMul A] {a : A} {g h : Aˣ}
    (hg : star (g : A) * a * g = a) (hh : star (h : A) * a * h = a) :
    star (↑(g * h) : A) * a * ↑(g * h) = a := calc
  _ = star (h : A) * (star (g : A) * a * g) * h := by
    simp only [Units.val_mul, star_mul, mul_assoc]
  _ = a := by rw [hg, hh]

private theorem units_preserve_inv {A : Type*} [Monoid A] [StarMul A] {a : A} {g : Aˣ}
    (hg : star (g : A) * a * g = a) : star (↑g⁻¹ : A) * a * ↑g⁻¹ = a := calc
  _ = star (↑g⁻¹ : A) * (star (g : A) * a * g) * ↑g⁻¹ := by rw [hg]
  _ = star (↑(g * g⁻¹) : A) * a * ↑(g * g⁻¹) := by
    simp only [Units.val_mul, star_mul, mul_assoc]
  _ = a := by simp

theorem aux3 {n : ℕ} (ε : Fin n → Bool) {g h : (Matrix (Fin n) (Fin n) ℂ)ˣ} :
    g ∈ Set.ofPred (fun u ↦ inUJ ε u.val) → h ∈ Set.ofPred (fun u ↦ inUJ ε u.val) →
      g * h ∈ Set.ofPred (fun u ↦ inUJ ε u.val) :=
  units_preserve_mul

theorem aux4 {n : ℕ} (ε : Fin n → Bool) :
    ((1 : (Matrix (Fin n) (Fin n) ℂ)ˣ).val)ᴴ * Jm ε * (1 : (Matrix (Fin n) (Fin n) ℂ)ˣ).val =
      Jm ε := by simp

theorem aux5 {n : ℕ} (ε : Fin n → Bool) {g : (Matrix (Fin n) (Fin n) ℂ)ˣ} :
    g ∈ Set.ofPred (fun u ↦ inUJ ε u.val) → g⁻¹ ∈ Set.ofPred (fun u ↦ inUJ ε u.val) :=
  units_preserve_inv

def UJ {n : ℕ} (ε : Fin n → Bool) : Subgroup (Matrix (Fin n) (Fin n) ℂ)ˣ where
  carrier := Set.ofPred fun g ↦ inUJ ε g.val
  mul_mem' := aux3 ε
  one_mem' := aux4 ε
  inv_mem' := aux5 ε

@[reducible] def instMeasurableSpaceUJ (n : ℕ) (ε : Fin n → Bool) : MeasurableSpace (UJ ε) :=
  borel _

attribute [local instance] instMeasurableSpaceUJ

theorem aux8 {n : ℕ} (ε : Fin n → Bool) : IsTopologicalGroup (UJ ε) := inferInstance

theorem aux9 (n : ℕ) (ε : Fin n → Bool) : BorelSpace (UJ ε) := ⟨rfl⟩

theorem isClosed_UJ {n : ℕ} (ε : Fin n → Bool) :
    IsClosed (UJ ε : Set (Matrix (Fin n) (Fin n) ℂ)ˣ) :=
  isClosed_eq (f := fun g : (Matrix (Fin n) (Fin n) ℂ)ˣ => g.valᴴ * Jm ε * g.val)
    ((Units.continuous_val.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
      Units.continuous_val) continuous_const

theorem laurent_T_neg_one_mul_T_one (n : ℕ) (ε : Fin n → Bool) : LocallyCompactSpace (UJ ε) := by
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  exact (isClosed_UJ ε).locallyCompactSpace

def muG {n : ℕ} (ε : Fin n → Bool) : Measure (UJ ε) :=
  @Measure.haar (UJ ε) _ _ (aux8 ε) (instMeasurableSpaceUJ n ε) (aux9 n ε)
    (laurent_T_neg_one_mul_T_one n ε)

theorem muG_isHaarMeasure {n : ℕ} (ε : Fin n → Bool) : (muG ε).IsHaarMeasure := by
  have := aux8 ε
  have := aux9 n ε
  have := laurent_T_neg_one_mul_T_one n ε
  unfold muG
  infer_instance

def Unimodular : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (g : UJ ε), Measure.map (fun x => x * g) (muG ε) = muG ε

def InvInvariant : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool), Measure.map (fun x : UJ ε => x⁻¹) (muG ε) = muG ε

/-- Inversion exchanges left and right Haar measure. For a bi-invariant measure,
its scalar factor squares to one by involutivity. -/
private theorem inv_eq_of_isMulRightInvariant {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] [μ.Regular] : μ.inv = μ := by
  have ⟨c, hc⟩ : ∃ c : ENNReal, μ.inv = c • μ :=
    ⟨_, isMulLeftInvariant_eq_smul_of_regular μ.inv μ⟩
  have K : TopologicalSpace.PositiveCompacts G := Classical.arbitrary _
  have hK : μ K ≠ 0 := (measure_pos_of_nonempty_interior _ K.interior_nonempty).ne'
  have hK' : μ K ≠ ⊤ := K.isCompact.measure_lt_top.ne
  have h : μ.inv.inv = c ^ 2 • μ := by
    rw [Measure.inv_def μ.inv, hc, Measure.map_smul, ← Measure.inv_def, hc, smul_smul, pow_two]
  have h' : c ^ 2 * μ K = 1 ^ 2 * μ K := by
    rw [← smul_eq_mul, ← Measure.smul_apply, ← h, Measure.inv_inv, one_pow, one_mul]
  rw [show c = 1 from (ENNReal.pow_right_strictMono two_ne_zero).injective
    ((ENNReal.mul_left_inj hK hK').1 h'), one_smul] at hc
  exact hc

theorem invInvariant_of : Unimodular → InvInvariant := by
  intro h n ε
  have := aux8 ε
  have := aux9 n ε
  have := laurent_T_neg_one_mul_T_one n ε
  have : (muG ε).IsMulRightInvariant := ⟨h n ε⟩
  have := muG_isHaarMeasure ε
  have : (muG ε).Regular := regular_haarMeasure
  exact inv_eq_of_isMulRightInvariant (muG ε)

end UpperTheory.Reformulated.B.InvolutionInvariants
