module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle018
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.UnitaryThreeReflectionRight
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle005
public import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart

@[expose] public section

section

open Matrix UpperTheory.V

private theorem diagonal_on_subgroup_from_equations {Γ k : Type} [Group Γ] [Field k] (H : Subgroup Γ) (W : Γ →* GL (Fin 2) k)
    (Ψ : Γ →* kˣ) (a b c d : k) (hdet : a * d - b * c ≠ 0)
    (h : ∀ g ∈ H, a * W g 0 0 + b * W g 1 0 = (Ψ g : k) * a ∧ a * W g 0 1 + b * W g 1 1 = (Ψ g : k) * b ∧
      c * W g 0 0 + d * W g 1 0 = (Ψ g : k)⁻¹ * c ∧ c * W g 0 1 + d * W g 1 1 = (Ψ g : k)⁻¹ * d) :
    Af.IsDiagOn W H ![Ψ, Ψ⁻¹] := by
  have hd : Matrix.det !![a, b; c, d] ≠ 0 := by rwa [Matrix.det_fin_two_of]
  obtain ⟨P, hP⟩ : ∃ P : GL (Fin 2) k, (P : Matrix (Fin 2) (Fin 2) k) = !![a, b; c, d] :=
    ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd, rfl⟩
  refine ⟨P, fun t ht => ?_⟩
  have hPW : !![a, b; c, d] * (W t : Matrix (Fin 2) (Fin 2) k) =
      Matrix.diagonal (fun i => ((![Ψ, Ψ⁻¹] i t : kˣ) : k)) * !![a, b; c, d] := by
    obtain ⟨h1, h2, h3, h4⟩ := h t ht
    ext i j
    fin_cases i <;> fin_cases j
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination h1
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination h2
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination h3
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination h4
  rw [Units.val_mul, Units.val_mul, hP, hPW, Matrix.mul_assoc, ← hP, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, Matrix.mul_one]

theorem UpperTheory.diagonal_on_subgroup_of_conjugate :
    ∀ {Γ k : Type} [Group Γ] [Field k] (H : Subgroup Γ) (W : Γ →* GL (Fin 2) k) (Ψ : Γ →* kˣ) (M : GL (Fin 3) k), (∀ g ∈ H, (M : Matrix (Fin 3) (Fin 3) k) * !![W g 0 0, 0, W g 0 1; 0, 1, 0; W g 1 0, 0, W g 1 1] = Matrix.diagonal ![(Ψ g : k), 1, (((Ψ g)⁻¹ : kˣ) : k)] * (M : Matrix (Fin 3) (Fin 3) k)) → Af.IsDiagOn W H ![Ψ, Ψ⁻¹] := by
  intro Γ k _ _ H W Ψ M hM
  have hMi : ((M⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) * (M : Matrix (Fin 3) (Fin 3) k) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  by_cases htriv : ∀ g ∈ H, Ψ g = 1
  · refine ⟨1, fun t ht => ?_⟩
    have e := hM t ht
    have hD : Matrix.diagonal ![(Ψ t : k), 1, (((Ψ t)⁻¹ : kˣ) : k)] = 1 := by
      rw [htriv t ht]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    rw [hD, Matrix.one_mul] at e
    have hB : !![W t 0 0, 0, W t 0 1; 0, 1, 0; W t 1 0, 0, W t 1 1] = (1 : Matrix (Fin 3) (Fin 3) k) := by
      calc _ = ((M⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *
            ((M : Matrix (Fin 3) (Fin 3) k) * !![W t 0 0, 0, W t 0 1; 0, 1, 0; W t 1 0, 0, W t 1 1]) := by
            rw [← Matrix.mul_assoc, hMi, Matrix.one_mul]
        _ = 1 := by rw [e, hMi]
    have b00 := congrFun (congrFun hB 0) 0
    have b02 := congrFun (congrFun hB 0) 2
    have b20 := congrFun (congrFun hB 2) 0
    have b22 := congrFun (congrFun hB 2) 2
    simp at b00 b02 b20 b22
    rw [one_mul, inv_one, mul_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [htriv t ht, b00, b02, b20, b22]
  · push_neg at htriv
    obtain ⟨g0, hg0, hne⟩ := htriv
    have e0 := hM g0 hg0
    have x01 : (M : Matrix (Fin 3) (Fin 3) k) 0 1 = (Ψ g0 : k) * (M : Matrix (Fin 3) (Fin 3) k) 0 1 := by
      have := congrFun (congrFun e0 0) 1
      simpa [Matrix.mul_apply, Fin.sum_univ_three] using this
    have x21 : (M : Matrix (Fin 3) (Fin 3) k) 2 1 =
        (((Ψ g0)⁻¹ : kˣ) : k) * (M : Matrix (Fin 3) (Fin 3) k) 2 1 := by
      have := congrFun (congrFun e0 2) 1
      simpa [Matrix.mul_apply, Fin.sum_univ_three] using this
    have m01 : (M : Matrix (Fin 3) (Fin 3) k) 0 1 = 0 := by
      have : (M : Matrix (Fin 3) (Fin 3) k) 0 1 * (1 - (Ψ g0 : k)) = 0 := by linear_combination x01
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd (Units.val_eq_one.mp (sub_eq_zero.mp h).symm) hne
    have m21 : (M : Matrix (Fin 3) (Fin 3) k) 2 1 = 0 := by
      have : (M : Matrix (Fin 3) (Fin 3) k) 2 1 * (1 - (((Ψ g0)⁻¹ : kˣ) : k)) = 0 := by
        linear_combination x21
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd (inv_eq_one.mp (Units.val_eq_one.mp (sub_eq_zero.mp h).symm)) hne
    have hdetM : (M : Matrix (Fin 3) (Fin 3) k).det ≠ 0 := by
      intro h0
      have := congrArg Matrix.det hMi
      rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at this
      exact zero_ne_one this
    have hdet : (M : Matrix (Fin 3) (Fin 3) k) 0 0 * (M : Matrix (Fin 3) (Fin 3) k) 2 2 -
        (M : Matrix (Fin 3) (Fin 3) k) 0 2 * (M : Matrix (Fin 3) (Fin 3) k) 2 0 ≠ 0 := by
      intro h0
      apply hdetM
      rw [Matrix.det_fin_three, m01, m21]
      linear_combination (M : Matrix (Fin 3) (Fin 3) k) 1 1 * h0
    refine diagonal_on_subgroup_from_equations H W Ψ _ _ _ _ hdet fun g hg => ⟨?_, ?_, ?_, ?_⟩
    · have := congrFun (congrFun (hM g hg) 0) 0
      simpa [Matrix.mul_apply, Fin.sum_univ_three] using this
    · have := congrFun (congrFun (hM g hg) 0) 2
      simpa [Matrix.mul_apply, Fin.sum_univ_three] using this
    · have := congrFun (congrFun (hM g hg) 2) 0
      simpa [Matrix.mul_apply, Fin.sum_univ_three] using this
    · have := congrFun (congrFun (hM g hg) 2) 2
      simpa [Matrix.mul_apply, Fin.sum_univ_three] using this
end

section

open Matrix UpperTheory.V

private theorem UpperTheory.exists_gl2_first_column {k : Type} [Field k] (v : Fin 2 → k) (hv : v ≠ 0) :
    ∃ h : GL (Fin 2) k, ∀ i, (h : Matrix (Fin 2) (Fin 2) k) i 0 = v i := by
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := by
      intro h1
      apply hv
      funext i
      fin_cases i <;> simp [h0, h1]
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![v 0, 1; v 1, 0] (by simp [Matrix.det_fin_two, h1]), ?_⟩
    intro i
    fin_cases i <;> rfl
  · refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![v 0, 0; v 1, 1] (by simp [Matrix.det_fin_two, h0]), ?_⟩
    intro i
    fin_cases i <;> rfl

private theorem UpperTheory.upper_triangular_characters {Γ k : Type} [Group Γ] [Field k] (D I : Subgroup Γ)
    (r : Γ →* Matrix (Fin 2) (Fin 2) k) (Ψ : Γ →* kˣ)
    (hn : ∀ d ∈ D, ∀ s ∈ I, d⁻¹ * s * d ∈ I)
    (h00 : ∀ s ∈ I, r s 0 0 = Ψ s) (h10 : ∀ s ∈ I, r s 1 0 = 0)
    (hdet : ∀ s ∈ I, (r s).det = 1) (hex : ∃ s ∈ I, (Ψ s : k) ^ 2 ≠ 1) :
    ∃ κ : Fin 2 → ↥D →* kˣ, (∀ s : ↥D, (∀ i j, j < i → r s i j = 0) ∧ ∀ i, r s i i = (κ i s : k)) ∧
      ∀ s : ↥D, (s : Γ) ∈ I → κ 0 s = Ψ s ∧ κ 1 s = (Ψ s)⁻¹ := by
  have r11 : ∀ s ∈ I, r s 1 1 = ((Ψ s)⁻¹ : kˣ) := by
    intro s hs
    have hd := hdet s hs
    rw [Matrix.det_fin_two, h00 s hs, h10 s hs, mul_zero, sub_zero] at hd
    rw [Units.val_inv_eq_inv_val]
    exact eq_inv_of_mul_eq_one_right hd
  obtain ⟨s0, hs0, ha⟩ := hex
  have hane : (Ψ s0 : k) - (Ψ s0 : k)⁻¹ ≠ 0 := by
    intro h
    apply ha
    rw [sub_eq_zero] at h
    calc (Ψ s0 : k) ^ 2 = (Ψ s0 : k) * (Ψ s0 : k)⁻¹ := by rw [sq]; nth_rewrite 2 [h]; rfl
      _ = 1 := mul_inv_cancel₀ (Ψ s0).ne_zero
  have low : ∀ d ∈ D, r d 1 0 = 0 := by
    intro d hd
    have ht : d⁻¹ * s0 * d ∈ I := hn d hd s0 hs0
    have hΨ : Ψ (d⁻¹ * s0 * d) = Ψ s0 := by
      rw [map_mul, map_mul, map_inv, mul_comm, ← mul_assoc, mul_inv_cancel, one_mul]
    have hm : r s0 * r d = r d * r (d⁻¹ * s0 * d) := by
      rw [← map_mul, ← map_mul]
      congr 1
      group
    have key := congrArg (fun M => M 1 0) hm
    simp only [Matrix.mul_apply, Fin.sum_univ_two] at key
    rw [h10 s0 hs0, r11 s0 hs0, h10 _ ht, h00 _ ht, hΨ, Units.val_inv_eq_inv_val] at key
    have : r d 1 0 * ((Ψ s0 : k) - (Ψ s0 : k)⁻¹) = 0 := by
      rw [mul_sub]
      linear_combination -key
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h hane
  have diag : ∀ d ∈ D, ∀ e ∈ D, ∀ i, r (d * e) i i = r d i i * r e i i := by
    intro d hd e he i
    rw [map_mul, Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i
    · simp [low e he]
    · simp [low d hd]
  let f : Fin 2 → ↥D →* k := fun i =>
    { toFun := fun d => r d i i
      map_one' := by simp
      map_mul' := fun d e => diag _ d.2 _ e.2 i }
  refine ⟨fun i => (f i).toHomUnits, ?_, ?_⟩
  · intro s
    refine ⟨?_, fun i => rfl⟩
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd hij (by decide)
    · exact absurd hij (by decide)
    · exact low s s.2
    · exact absurd hij (by decide)
  · intro s hs
    constructor
    · ext
      exact h00 _ hs
    · ext
      exact r11 _ hs

theorem UpperTheory.exists_isFlagOn_of_eigenvector_normal_subgroup :
    ∀ {Γ k : Type} [Group Γ] [Field k] (D I : Subgroup Γ) (W : Γ →* GL (Fin 2) k) (Ψ : Γ →* kˣ) (v : Fin 2 → k), (∀ d ∈ D, ∀ s ∈ I, d⁻¹ * s * d ∈ I) → v ≠ 0 → (∀ s ∈ I, (W s : Matrix (Fin 2) (Fin 2) k) *ᵥ v = (Ψ s : k) • v) → (∀ s ∈ I, (W s : Matrix (Fin 2) (Fin 2) k).det = 1) → (∃ s ∈ I, (Ψ s : k) ^ 2 ≠ 1) → ∃ κ : Fin 2 → ↥D →* kˣ, Af.IsFlagOn W D κ ∧ ∀ s : ↥D, (s : Γ) ∈ I → κ 0 s = Ψ s ∧ κ 1 s = (Ψ s)⁻¹ := by
  intro Γ k _ _ D I W Ψ v hn hv heig hdet hex
  obtain ⟨h, hh⟩ := UpperTheory.exists_gl2_first_column v hv
  have hcol : (h : Matrix (Fin 2) (Fin 2) k) *ᵥ Pi.single 0 1 = v := by
    rw [Matrix.mulVec_single_one]
    funext i
    exact hh i
  have hinv : ((h⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) * (h : Matrix (Fin 2) (Fin 2) k) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  let r : Γ →* Matrix (Fin 2) (Fin 2) k := (Units.coeHom _).comp ((MulAut.conj h⁻¹).toMonoidHom.comp W)
  have hr2 : ∀ s, r s = ((h⁻¹ * W s * h⁻¹⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) := fun s => rfl
  have hr : ∀ s, r s = ((h⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) * (W s : Matrix (Fin 2) (Fin 2) k) * (h : Matrix (Fin 2) (Fin 2) k) := by
    intro s
    rw [hr2, inv_inv, Units.val_mul, Units.val_mul]
  have hcol' : ∀ s ∈ I, r s *ᵥ Pi.single 0 1 = (Ψ s : k) • (Pi.single 0 1 : Fin 2 → k) := by
    intro s hs
    rw [hr, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hcol, heig s hs, Matrix.mulVec_smul, ← hcol,
      Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  have h00 : ∀ s ∈ I, r s 0 0 = Ψ s := by
    intro s hs
    have := congrFun (hcol' s hs) 0
    simpa [Matrix.mulVec_single_one] using this
  have h10 : ∀ s ∈ I, r s 1 0 = 0 := by
    intro s hs
    have := congrFun (hcol' s hs) 1
    simpa [Matrix.mulVec_single_one] using this
  have hdet' : ∀ s ∈ I, (r s).det = 1 := by
    intro s hs
    rw [hr, Matrix.det_mul, Matrix.det_mul, hdet s hs, mul_one, ← Matrix.det_mul, hinv, Matrix.det_one]
  obtain ⟨κ, hκ, hI⟩ := UpperTheory.upper_triangular_characters D I r Ψ hn h00 h10 hdet' hex
  exact ⟨κ, ⟨h⁻¹, hκ⟩, hI⟩
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem left_conj {R : Type} [CommRing R] {m : ℕ} (x y : GG (m := m) (R := R))
    (h1 : x.mat = 1) (h2 : x.right = -1) (h3 : y.right = 1) :
    (x * y * x⁻¹).left = theta y.left := by
  have hl : x.left = 1 := Units.ext h1
  simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right, SemidirectProduct.inv_left,
    hl, h2, h3, inv_one, mul_one, one_mul, sgnAct_neg_one, map_one]

private theorem pairing_theta {R : Type} [CommRing R] {m : ℕ} (a : GL (Fin m) R) :
    (a : Matrix (Fin m) (Fin m) R)ᵀ * Jmat R m * (theta a : GL (Fin m) R) = Jmat R m := by
  rw [theta_val, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc _ (Jmat R m) (Jmat R m), Jmat_mul_Jmat,
    Matrix.mul_one, ← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one,
    Matrix.one_mul]

private theorem cont_hom {Γ M : Type} [Group Γ] [TopologicalSpace Γ] [ContinuousInv Γ] [Monoid M] [TopologicalSpace M]
    (f : Γ →* Mˣ) (h : Continuous fun g => (f g : M)) : Continuous f := by
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  simp only [← map_inv]
  exact h.comp continuous_inv

private theorem irr_tw {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (ρ : Γ →* GL (Fin n) k) (χ : Γ →* kˣ) :
    (Af.tw ρ χ⁻¹).comp χ.ker.subtype = ρ.comp χ.ker.subtype := by
  refine MonoidHom.ext fun s => Units.ext ?_
  have hs : χ s = 1 := s.2
  show (Af.tw ρ χ⁻¹ s : Matrix (Fin n) (Fin n) k) = ρ s
  rw [Af.tw_val, MonoidHom.inv_apply, hs, inv_one, Units.val_one, one_smul]
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg
open IsLocalRing Matrix Formalism.MainNotions.N GlobalTheory.GalOfCusp

namespace UpperTheory.V.U3

abbrev CharCont {O Γ : Type} [CommRing O] [IsLocalRing O] [Group Γ] [TopologicalSpace Γ] (Ψ : Γ →* Oˣ) : Prop :=
  ∀ n : ℤ, AdicCont (maximalIdeal O) fun g => ((Ψ g ^ n : Oˣ) : O)

structure Dat (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K] [Algebra K Ω]
    {l : ℕ} [Fact l.Prime] (c : Coef l) {N : ℕ} [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) where
  gd : GD Ω K l e ψ
  η : G ℚ Ω →* ℤˣ
  η_ker : η.ker = galOf ℚ K Ω
  cc : G ℚ Ω
  conj : ∃ φ : Ω →+* ℂ, ∀ x, φ (cc x) = starRingEnd ℂ (φ x)
  j : Ω →+* Om l
  ι : GQ l →* G ℚ Ω
  ι_cont : Continuous ι
  ι_spec : ∀ σ x, σ (j x) = j (ι σ x)
  Kv : FinExt l
  Kv_spec : ∀ g, η (ι g) = 1 ↔ g ∈ GK Kv
  η_unr : ∀ g ∈ Loc.Iq l, η (ι g) = 1
  τ_open : IsOpen (((Chr.dirG ℚ Ω (comp l ψ)).comp ι).ker : Set (GQ l))
  Ψ_cont : CharCont (Chr.Psi l e (Chr.dirG ℚ Ω ψ))
  Ψ_I : ∀ g ∈ Loc.Iq l, Chr.Psi l e (Chr.dirG ℚ Ω ψ) (ι g) =
    Loc.cycA l l c.O g ^ e * Chr.dirG ℚ Ω (comp l ψ) (ι g)

namespace Dat

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
  {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ)

abbrev Ψ (_ : Dat Ω K c e ψ) : G ℚ Ω →* c.Oˣ := Chr.Psi l e (Chr.dirG ℚ Ω ψ)

def ΨQ : G ℚ Ω →* (PadicAlgCl l)ˣ := (Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom).comp D.Ψ

abbrev loc : Loc.Dat3 l c.O where
  η := D.η.comp D.ι
  Ψ := D.Ψ.comp D.ι
  τ := (Chr.dirG ℚ Ω (comp l ψ)).comp D.ι
  e := e
  Kv := D.Kv
  odd := D.gd.l_odd
  e_pos := D.gd.e_pos
  η_ker := D.Kv_spec
  η_unr := D.η_unr
  τ_open := D.τ_open
  Ψ_cont n := by
    have h := (D.Ψ_cont 1 n).comp_continuous D.ι_cont
    simp only [zpow_one] at h
    exact h
  Ψ_I := D.Ψ_I

def Kill : Set (G ℚ Ω) :=
  {g | ∃ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 ∧ g ∈ Ine (F := ℚ) A ∧ rbar c.O D.η D.Ψ g = 1}

abbrev ULoc : Type 1 := Univ (GCond.noCondition c.O (D.η.comp D.ι) (D.Ψ.comp D.ι))

abbrev Ring (U : D.ULoc) (g₁ : G ℚ Ω) : Type 1 := SRing D.Kill D.ι_cont U (D.loc.It U) D.cc g₁

abbrev Marked (g₁ : G ℚ Ω) : Prop := Marks D.η D.Ψ D.cc g₁

def rhoK {κ : Type} [CommRing κ] (r : G ℚ Ω →* GG (m := 3) (R := κ)) (hr : HasMult D.η r) : G K Ω →* GL (Fin 3) κ :=
  (glPart D.η r hr).comp ((galEmb ℚ K Ω).codRestrict D.η.ker fun s => D.η_ker ▸ galEmb_mem ℚ K Ω s)

theorem rhoK_apply {κ : Type} [CommRing κ] (r : G ℚ Ω →* GG (m := 3) (R := κ)) (hr : HasMult D.η r) (s : G K Ω) :
    D.rhoK r hr s = (r (galEmb ℚ K Ω s)).left := rfl

structure IsPt (U : D.ULoc) (g₁ : G ℚ Ω) (r : G ℚ Ω →* GG (m := 3) (R := PadicAlgCl l)) : Prop where
  mult : HasMult D.η r
  cont : Continuous (mats r)
  int : ∀ g a b, ‖(r g).mat a b‖ ≤ 1
  red : ∀ g a b, ‖(r g).mat a b - (r0 D.η D.ΨQ g).mat a b‖ < 1
  norm : Normalised D.cc g₁ r
  kill : ∀ g ∈ D.Kill, r g = 1
  loc : ∃ f : U.R →ₐ[c.O] PadicAlgCl l, IsLocPt f ∧ D.loc.It U ≤ RingHom.ker f ∧ push f U.r.hom = r.comp D.ι

def IsExt {κ : Type} [CommRing κ] (r : G ℚ Ω →* GG (m := 3) (R := κ)) (W : G ℚ Ω →* GL (Fin 2) κ) : Prop :=
  (∀ g ∈ D.η.ker, (W g : Matrix (Fin 2) (Fin 2) κ) = corner (r g).mat) ∧ (W D.cc : Matrix (Fin 2) (Fin 2) κ).trace = 0

def IsAutI [IsCMField K] (ι : Qbar l ≃+* ℂ) (r : G ℚ Ω →* GG (m := 3) (R := PadicAlgCl l)) (hr : HasMult D.η r) : Prop :=
  Af.IsAutCsd ι (Af.tw (D.rhoK r hr) (cycBar K Ω l)⁻¹)

def IsModular (_ : Dat Ω K c e ψ) (ι : Qbar l ≃+* ℂ) (W : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l)) : Prop :=
  ∃ f : Af.Newform (2 * e + 1), f.Att ι (Af.tw W (cycBar ℚ Ω l ^ (-(e : ℤ))))

end Dat

end UpperTheory.V.U3

end
end
