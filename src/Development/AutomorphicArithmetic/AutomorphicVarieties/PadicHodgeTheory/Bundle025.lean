module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module Topology UpperTheory.V.Loc UpperTheory.V.U3

private def triGL {B : Type} [CommRing B] (t : Fin 3 → Bˣ) (x y z : B) : GL (Fin 3) B where
  val := triM t x y z
  inv := !![((t 0)⁻¹ : Bˣ), -x * ((t 0)⁻¹ : Bˣ), (x * y - z) * ((t 0)⁻¹ : Bˣ);
    0, ((t 1)⁻¹ : Bˣ), -y * ((t 1)⁻¹ : Bˣ); 0, 0, ((t 2)⁻¹ : Bˣ)]
  val_inv := by
    have h0 := (t 0).mul_inv
    have h1 := (t 1).mul_inv
    have h2 := (t 2).mul_inv
    ext i j
    fin_cases i <;> fin_cases j <;> simp [triM, Matrix.mul_apply, Fin.sum_univ_three, -Units.mul_inv, -Units.inv_mul] <;>
      first
        | assumption
        | linear_combination (-x) * h0
        | linear_combination (x * y - z) * h0 - x * y * h1
        | linear_combination (-y) * h1
  inv_val := by
    have h0 := (t 0).inv_mul
    have h1 := (t 1).inv_mul
    have h2 := (t 2).inv_mul
    ext i j
    fin_cases i <;> fin_cases j <;> simp [triM, Matrix.mul_apply, Fin.sum_univ_three, -Units.mul_inv, -Units.inv_mul] <;>
      first
        | assumption
        | ring

private theorem triGL_val {B : Type} [CommRing B] (t : Fin 3 → Bˣ) (x y z : B) :
    (triGL t x y z : Matrix (Fin 3) (Fin 3) B) = triM t x y z := rfl

private theorem triGL_congr {B : Type} [CommRing B] {t s : Fin 3 → Bˣ} {x y z x' y' z' : B}
    (ht : t = s) (hx : x = x') (hy : y = y') (hz : z = z') : triGL t x y z = triGL s x' y' z' := by
  subst ht hx hy hz
  rfl

private theorem theta_triGL {B : Type} [CommRing B] (t : Fin 3 → Bˣ) (x y z : B) :
    theta (triGL t x y z) = triGL (fun i => (t i.rev)⁻¹) (-y) (-x) (x * y - z) := by
  apply Units.ext
  rw [theta_val, triGL_val]
  have hinv : ((triGL t x y z)⁻¹ : GL (Fin 3) B).val =
      !![(((t 0)⁻¹ : Bˣ) : B), -x * (((t 0)⁻¹ : Bˣ) : B), (x * y - z) * (((t 0)⁻¹ : Bˣ) : B);
        0, (((t 1)⁻¹ : Bˣ) : B), -y * (((t 1)⁻¹ : Bˣ) : B); 0, 0, (((t 2)⁻¹ : Bˣ) : B)] := rfl
  rw [hinv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Jmat, triM, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, Fin.rev] <;> ring

private theorem triGL_mul {B : Type} [CommRing B] (t s : Fin 3 → Bˣ) (x y z x' y' z' : B) :
    triGL t x y z * triGL s x' y' z' = triGL (fun i => t i * s i)
      (x + ((t 0 / t 1 : Bˣ) : B) * x') (y + ((t 1 / t 2 : Bˣ) : B) * y')
      (z + ((t 0 / t 2 : Bˣ) : B) * z' + x * (((t 1 / t 2 : Bˣ) : B) * y')) := by
  apply Units.ext
  rw [Units.val_mul, triGL_val, triGL_val, triGL_val]
  have h1 := (t 1).inv_mul
  have h2 := (t 2).inv_mul
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, triM, div_eq_mul_inv, -Units.mul_inv, -Units.inv_mul] <;>
    first
      | linear_combination (-((t 0 : B) * x' * s 1)) * h1
      | linear_combination (-((t 1 : B) * y' * s 2)) * h2
      | linear_combination (-((t 0 : B) * z' * s 2 + x * t 1 * y' * s 2)) * h2

theorem UpperTheory.exists_unipotent_from_torus_coords :
    ∀ {G B : Type} [Group G] [CommRing B] {η : G →* ℤˣ} (T : Tor η B) (h : B), 2 * h = 1 →
      ∀ (β : G → B × B) (γ : G → B), (∀ g g', β (g * g') = β g + T.M1 g (β g')) →
        T.IsGam h β γ → ∃ u : G →* GG (m := 3) (R := B), T.Coord h β γ u := by
  intro G B _ _ η T h hh β γ hβ hγ
  let F : G → GG (m := 3) (R := B) := fun g =>
    ⟨triGL (T.t g) (β g).1 (β g).2 (γ g + h * (β g).1 * (β g).2), η g⟩
  have hmul : ∀ g g' : G, F (g * g') = F g * F g' := by
    intro g g'
    have hab : (((T.t g 0 / T.t g 2 : Bˣ)) : B) =
        ((T.t g 0 / T.t g 1 : Bˣ) : B) * ((T.t g 1 / T.t g 2 : Bˣ) : B) := by
      rw [← Units.val_mul, div_mul_div_cancel]
    have hb := hβ g g'
    have hc := hγ g g'
    apply SemidirectProduct.ext
    · simp only [F, SemidirectProduct.mul_left]
      rcases Int.units_eq_one_or (η g) with he | he
      · rw [he, sgnAct_one, triGL_mul]
        rw [Tor.adjointSuperdiagRep_apply, if_pos he] at hb
        rw [Tor.adjointSuperdiagRep_apply, if_pos he, Tor.χ2_apply, he] at hc
        apply triGL_congr
        · funext i
          rw [T.mul, if_pos he]
        · rw [hb]; rfl
        · rw [hb]; rfl
        · rw [hc, hb, hab]
          simp only [omg, Prod.fst_add, Prod.snd_add, Units.val_one, Int.cast_one, one_mul]
          linear_combination ((β g).1 * ((T.t g 1 / T.t g 2 : Bˣ) : B) * (β g').2) * hh
      · have hne : η g ≠ 1 := by rw [he]; decide
        rw [he, sgnAct_neg_one, theta_triGL, triGL_mul]
        rw [Tor.adjointSuperdiagRep_apply, if_neg hne] at hb
        rw [Tor.adjointSuperdiagRep_apply, if_neg hne, Tor.χ2_apply, he] at hc
        apply triGL_congr
        · funext i
          rw [T.mul, if_neg hne]
        · rw [hb]
          simp only [Prod.fst_add]
          ring
        · rw [hb]
          simp only [Prod.snd_add]
          ring
        · rw [hc, hb, hab]
          simp only [omg, Prod.fst_add, Prod.snd_add, Units.val_neg, Units.val_one, Int.cast_neg,
            Int.cast_one]
          linear_combination (((T.t g 0 / T.t g 1 : Bˣ) : B) * ((T.t g 1 / T.t g 2 : Bˣ) : B) *
            (β g').1 * (β g').2 - ((T.t g 1 / T.t g 2 : Bˣ) : B) * (β g).1 * (β g').1) * hh
    · simp only [F, SemidirectProduct.mul_right, map_mul]
  refine ⟨MonoidHom.mk' F hmul, ?_⟩
  exact Tor.Coord.mk (fun g => rfl) (fun g => rfl)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module Topology UpperTheory.V.Loc UpperTheory.V.U3

section

variable {B : Type} [CommRing B]

private theorem triM_mul (t s : Fin 3 → Bˣ) (x y z x' y' z' : B) :
    triM t x y z * triM s x' y' z' =
      triM (fun i => t i * s i) (x + ((t 0 / t 1 : Bˣ) : B) * x') (y + ((t 1 / t 2 : Bˣ) : B) * y')
        (z + x * (((t 1 / t 2 : Bˣ) : B) * y') + ((t 0 / t 2 : Bˣ) : B) * z') := by
  have h1 := Units.inv_mul (t 1)
  have h2 := Units.inv_mul (t 2)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [triM, Matrix.mul_apply, Fin.sum_univ_three, div_eq_mul_inv] <;>
    first
    | ring1
    | linear_combination (-((t 0 : B) * x' * (s 1 : B))) * h1
    | linear_combination (-((t 0 : B) * z' * (s 2 : B)) - (s 2 : B) * x * (t 1 : B) * y') * h2
    | linear_combination (-((t 1 : B) * y' * (s 2 : B))) * h2

private theorem triM_inj {t s : Fin 3 → Bˣ} {x y z x' y' z' : B} (h : triM t x y z = triM s x' y' z') :
    t = s ∧ x = x' ∧ y = y' ∧ z = z' := by
  have e : ∀ i j, triM t x y z i j = triM s x' y' z' i j := fun i j => by rw [h]
  have a0 := e 0 0
  have a1 := e 1 1
  have a2 := e 2 2
  have b1 := e 0 1
  have b2 := e 1 2
  have b3 := e 0 2
  simp [triM] at a0 a1 a2 b1 b2 b3
  have ht : t = s := by
    funext i
    fin_cases i
    · exact Units.ext a0
    · exact Units.ext a1
    · exact Units.ext a2
  subst ht
  refine ⟨rfl, ?_, ?_, ?_⟩
  · simpa using congrArg (· * ((t 1)⁻¹ : Bˣ).val) b1
  · simpa using congrArg (· * ((t 2)⁻¹ : Bˣ).val) b2
  · simpa using congrArg (· * ((t 2)⁻¹ : Bˣ).val) b3

private theorem theta_triM {A : GL (Fin 3) B} {t : Fin 3 → Bˣ} {x y z : B}
    (h : (A : Matrix (Fin 3) (Fin 3) B) = triM t x y z) :
    (theta A : Matrix (Fin 3) (Fin 3) B) = triM (fun i => (t i.rev)⁻¹) (-y) (-x) (x * y - z) := by
  have h1 := Units.inv_mul (t 1)
  have h2 := Units.inv_mul (t 2)
  have key : triM (fun i => (t i.rev)⁻¹) (-y) (-x) (x * y - z) * ((theta A)⁻¹ : GL (Fin 3) B) = 1 := by
    rw [theta_inv_val, h]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [triM, Jmat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, Fin.rev] <;>
      first
      | linear_combination y * h2
      | linear_combination z * h2 - x * y * h1
      | linear_combination x * h1
  calc (theta A : Matrix (Fin 3) (Fin 3) B)
      = 1 * (theta A : Matrix (Fin 3) (Fin 3) B) := (one_mul _).symm
    _ = triM (fun i => (t i.rev)⁻¹) (-y) (-x) (x * y - z) * ((theta A)⁻¹ : GL (Fin 3) B) *
          (theta A : Matrix (Fin 3) (Fin 3) B) := by rw [key]
    _ = triM (fun i => (t i.rev)⁻¹) (-y) (-x) (x * y - z) := by
      rw [mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]

private theorem exists_triM (A : GL (Fin 3) B)
    (h : ∀ a b, wt a b < 0 → (A : Matrix (Fin 3) (Fin 3) B) a b = 0) :
    ∃ (t : Fin 3 → Bˣ) (x y z : B), (A : Matrix (Fin 3) (Fin 3) B) = triM t x y z := by
  have z10 := h 1 0 (by decide)
  have z20 := h 2 0 (by decide)
  have z21 := h 2 1 (by decide)
  have hd : IsUnit (A : Matrix (Fin 3) (Fin 3) B).det := Matrix.isUnits_det_units A
  rw [Matrix.det_fin_three, z10, z20, z21] at hd
  simp only [mul_zero, zero_mul, sub_zero, add_zero, zero_sub, neg_zero, IsUnit.mul_iff] at hd
  obtain ⟨⟨h0, h1⟩, h2⟩ := hd
  refine ⟨![h0.unit, h1.unit, h2.unit], (A : Matrix (Fin 3) (Fin 3) B) 0 1 * ↑h1.unit⁻¹,
    (A : Matrix (Fin 3) (Fin 3) B) 1 2 * ↑h2.unit⁻¹, (A : Matrix (Fin 3) (Fin 3) B) 0 2 * ↑h2.unit⁻¹, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [triM, z10, z20, z21, mul_assoc]

end

theorem UpperTheory.exists_torus_coords_of_unipotent :
    ∀ {G B : Type} [Group G] [CommRing B] {η : G →* ℤˣ} (h : B),
      2 * h = 1 → ∀ u : G →* GG (m := 3) (R := B), HasMult η u →
        (∀ g a b, wt a b < 0 → (u g).mat a b = 0) →
        ∃ (T : Tor η B) (β : G → B × B) (γ : G → B),
          T.Coord h β γ u ∧ (∀ g g', β (g * g') = β g + T.M1 g (β g')) ∧ T.IsGam h β γ := by
  intro G B _ _ η h h2 u hm hu
  have ex : ∀ g, ∃ (t : Fin 3 → Bˣ) (x y z : B), (u g).mat = triM t x y z :=
    fun g => exists_triM (u g).left (hu g)
  choose t x y z hA using ex
  have step : ∀ g g', ∃ (t' : Fin 3 → Bˣ) (x' y' z' : B),
      (u (g * g')).mat = triM (t g) (x g) (y g) (z g) * triM t' x' y' z' ∧
      ((η g = 1 ∧ t' = t g' ∧ x' = x g' ∧ y' = y g' ∧ z' = z g') ∨
       (η g = -1 ∧ t' = (fun i => (t g' i.rev)⁻¹) ∧ x' = -y g' ∧ y' = -x g' ∧ z' = x g' * y g' - z g')) := by
    intro g g'
    have hmul : (u (g * g')).mat = (u g).mat * (((sgnAct 3 B) (u g).right) (u g').left : Matrix (Fin 3) (Fin 3) B) := by
      rw [map_mul]
      show (((u g * u g').left : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B) = _
      rw [SemidirectProduct.mul_left, Units.val_mul]
      rfl
    rw [hm g] at hmul
    rcases Int.units_eq_one_or (η g) with e | e
    · rw [e, sgnAct_one] at hmul
      exact ⟨_, _, _, _, by rw [hmul, hA g]; exact congrArg _ (hA g'), Or.inl ⟨e, rfl, rfl, rfl, rfl⟩⟩
    · rw [e, sgnAct_neg_one] at hmul
      exact ⟨_, _, _, _, by rw [hmul, hA g]; exact congrArg _ (theta_triM (hA g')), Or.inr ⟨e, rfl, rfl, rfl, rfl⟩⟩
  have hne : (-1 : ℤˣ) ≠ 1 := by decide
  have hab : ∀ g, ((t g 0 / t g 1 : Bˣ) : B) * ((t g 1 / t g 2 : Bˣ) : B) = ((t g 0 / t g 2 : Bˣ) : B) := by
    intro g
    rw [← Units.val_mul, div_mul_div_cancel]
  refine ⟨⟨t, ?_⟩, fun g => (x g, y g), fun g => z g - h * x g * y g, ⟨hm, fun g => ?_⟩, ?_, ?_⟩
  · intro g g' i
    obtain ⟨t', x', y', z', he, hc⟩ := step g g'
    rw [triM_mul, hA (g * g')] at he
    obtain ⟨ht, -, -, -⟩ := triM_inj he
    rcases hc with ⟨e, rfl, -, -, -⟩ | ⟨e, rfl, -, -, -⟩
    · rw [ht]
      simp [e]
    · rw [ht]
      simp [e, hne]
  · rw [hA g]
    congr 1
    ring
  · intro g g'
    obtain ⟨t', x', y', z', he, hc⟩ := step g g'
    rw [triM_mul, hA (g * g')] at he
    obtain ⟨-, hx, hy, -⟩ := triM_inj he
    rcases hc with ⟨e, -, rfl, rfl, -⟩ | ⟨e, -, rfl, rfl, -⟩
    · ext <;> simp [Tor.adjointSuperdiagRep_apply, e, hx, hy]
    · ext <;> simp [Tor.adjointSuperdiagRep_apply, e, hne, hx, hy]
  · intro g g'
    obtain ⟨t', x', y', z', he, hc⟩ := step g g'
    rw [triM_mul, hA (g * g')] at he
    obtain ⟨-, hx, hy, hz⟩ := triM_inj he
    have hg := hab g
    simp only [Tor.χ2_apply, Tor.adjointSuperdiagRep_apply, omg]
    rcases hc with ⟨e, -, rfl, rfl, rfl⟩ | ⟨e, -, rfl, rfl, rfl⟩
    · simp only [e, if_true]
      rw [hx, hy, hz]
      push_cast
      linear_combination (-(x g * ((t g 1 / t g 2 : Bˣ) : B) * y g')) * h2 - (h * x g' * y g') * hg
    · simp only [e, hne, if_false]
      rw [hx, hy, hz]
      push_cast
      linear_combination (((t g 1 / t g 2 : Bˣ) : B) * x g * x g' - ((t g 0 / t g 2 : Bˣ) : B) * x g' * y g') * h2 - (h * x g' * y g') * hg
end
