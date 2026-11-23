module

public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open Matrix

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

open Formalism.MainNotions.S Formalism.BasicNotions

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

theorem hT_swap (x y : S.V) : S.hT y x = star (S.hT x y) := by
  have h := S.herm.eq x y
  simpa [starRingEnd_apply] using h.symm

theorem brS_add_left (x x' y : S.V) : brS S (x + x') y = brS S x y + brS S x' y := by
  simp [brS]

theorem brS_smul_left (c : E) (x y : S.V) : brS S (c • x) y = c * brS S x y := by
  simp [brS]

theorem brS_sum_left {ι : Type*} (s : Finset ι) (c : ι → E) (x : ι → S.V) (y : S.V) :
    brS S (∑ i ∈ s, c i • x i) y = ∑ i ∈ s, c i * brS S (x i) y := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [brS, map_sum]

theorem brS_add_right (x y y' : S.V) : brS S x (y + y') = brS S x y + brS S x y' := by
  simp [brS]

theorem brS_smul_right (c : E) (x y : S.V) : brS S x (c • y) = star c * brS S x y := by
  simp [brS, starRingEnd_apply]

theorem brS_sum_right {ι : Type*} (s : Finset ι) (c : ι → E) (x : S.V) (y : ι → S.V) :
    brS S x (∑ i ∈ s, c i • y i) = ∑ i ∈ s, star (c i) * brS S x (y i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [brS, map_sum, starRingEnd_apply]

theorem brS_swap (x y : S.V) : brS S y x = star (brS S x y) := by
  exact hT_swap y x

theorem brS_fvec (F : FlagG S r T) (c b : Fin (r + 1)) :
    brS S (F.fvec c) (F.fvec b) = if c = Fin.last r ∧ b = Fin.last r then -T else 0 := by
  unfold brS
  induction c using Fin.lastCases with
  | last =>
    induction b using Fin.lastCases with
    | last => simp [FlagG.fvec, F.z_norm]
    | cast j => simp [FlagG.fvec, F.z_orth, Fin.castSucc_ne_last]
  | cast i =>
    induction b using Fin.lastCases with
    | last => simp [FlagG.fvec, hT_swap, F.z_orth]
    | cast j => simp [FlagG.fvec, F.e_iso, Fin.castSucc_ne_last]

variable (F : FlagG S r T) (F' : FlagG S r T')

def omp : S.V := ∑ b, (Zhat F F').adjugate b (Fin.last r) • F'.fvec b

theorem brS_omp_fvec (a : Fin (r + 1)) :
    brS S (omp F F') (F.fvec a) = if a = Fin.last r then (Zhat F F').det else 0 := by
  unfold omp
  rw [brS_sum_left]
  have h := congrFun (congrFun (Matrix.mul_adjugate (Zhat F F')) a) (Fin.last r)
  rw [Matrix.mul_apply] at h
  have h2 : ∀ b, (Zhat F F').adjugate b (Fin.last r) * brS S (F'.fvec b) (F.fvec a)
      = Zhat F F' a b * (Zhat F F').adjugate b (Fin.last r) := fun b => by
    rw [mul_comm]; rfl
  simp_rw [h2, h, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> simp

theorem brS_omp_e (a : Fin r) : brS S (omp F F') (F.e a) = 0 := by
  have h : F.e a = F.fvec (Fin.castSucc a) := by simp [FlagG.fvec]
  rw [h, brS_omp_fvec]
  simp [Fin.castSucc_ne_last]

theorem det_eq_Dl : (Zhat F F').det = Dl F F' (r + 1) := by
  unfold Dl leadMinorE
  rw [dite_eq_left le_rfl]
  congr 1

theorem pairing_omegaPrime_z : brS S (omp F F') F.z = Dl F F' (r + 1) := by
  have h : F.z = F.fvec (Fin.last r) := by simp [FlagG.fvec]
  rw [h, brS_omp_fvec, if_pos rfl, det_eq_Dl]

theorem adj_last_eq_Dl : (Zhat F F').adjugate (Fin.last r) (Fin.last r) = Dl F F' r := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  unfold Dl leadMinorE
  rw [dite_eq_left (Nat.le_succ r), Fin.succAbove_last]
  have hp : ((-1 : E) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ))) = 1 := by
    rw [← two_mul, pow_mul]; simp
  rw [hp, one_mul]
  congr 1

theorem brS_omp_f' (b : Fin (r + 1)) :
    brS S (omp F F') (F'.fvec b) = if b = Fin.last r then (Zhat F F').adjugate (Fin.last r) (Fin.last r) * -T' else 0 := by
  unfold omp
  rw [brS_sum_left]
  simp_rw [brS_fvec F']
  by_cases hb : b = Fin.last r
  · subst hb; simp
  · simp [hb]

theorem brS_omp_omp : brS S (omp F F') (omp F F') = -T' * (Dl F F' r * star (Dl F F' r)) := by
  nth_rewrite 2 [omp]
  rw [brS_sum_right]
  simp_rw [brS_omp_f']
  simp [adj_last_eq_Dl]
  ring

def yv : S.V := T • omp F F' + Dl F F' (r + 1) • F.z

theorem brS_yv_e (a : Fin r) : brS S (yv F F') (F.e a) = 0 := by
  unfold yv
  rw [brS_add_left, brS_smul_left, brS_smul_left, brS_omp_e]
  simp [brS, F.z_orth]

theorem pairing_yVector_z : brS S (yv F F') F.z = 0 := by
  unfold yv
  rw [brS_add_left, brS_smul_left, brS_smul_left, pairing_omegaPrime_z]
  simp [brS, F.z_norm]
  ring

theorem brS_yv_yv (hT : star T = T) : brS S (yv F F') (yv F F') = T * Gflag F F' := by
  have hz : brS S F.z (yv F F') = 0 := by rw [brS_swap, pairing_yVector_z, star_zero]
  have ho : brS S (omp F F') (yv F F') = T * brS S (omp F F') (omp F F') + star (Dl F F' (r + 1)) * Dl F F' (r + 1) := by
    unfold yv
    rw [brS_add_right, brS_smul_right, brS_smul_right, pairing_omegaPrime_z, hT]
  conv_lhs => rw [show yv F F' = T • omp F F' + Dl F F' (r + 1) • F.z from rfl]
  rw [brS_add_left, brS_smul_left, brS_smul_left, ← show yv F F' = T • omp F F' + Dl F F' (r + 1) • F.z from rfl, hz, ho, brS_omp_omp]
  unfold Gflag
  ring

end Formalism.L2.SG.NGCut.NormalVectorPairings
end
end

section

noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section Cut

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

def MMo (H : HermSp M V) {r : ℕ} (t : Term V M r) : Submodule M.L.O V :=
  Submodule.span M.L.O (Set.range (H.MMfam t))

def MMsharp (H : HermSp M V) {r : ℕ} (t : Term V M r) : Submodule M.L.O V where
  carrier := {u | u ∈ Submodule.span E (Set.range (H.MMfam t)) ∧ ∀ m ∈ MMo H t, H.h u m ∈ M.L.O}
  add_mem' := fun {a b} ha hb => ⟨Submodule.add_mem _ ha.1 hb.1, fun m hm => by
    rw [H.h_add_left]; exact M.L.O.add_mem (ha.2 m hm) (hb.2 m hm)⟩
  zero_mem' := ⟨Submodule.zero_mem _, fun m _ => by rw [H.h_zero_left]; exact M.L.O.zero_mem⟩
  smul_mem' := fun c u hu => ⟨by rw [Subring.smul_def]; exact Submodule.smul_mem _ _ hu.1, fun m hm => by
    rw [Subring.smul_def, H.h_smul_left]; exact M.L.O.mul_mem c.2 (hu.2 m hm)⟩

abbrev DDt (H : HermSp M V) {r : ℕ} (t : Term V M r) : Type :=
  ↥(MMsharp H t) ⧸ (MMo H t).comap (MMsharp H t).subtype

def ddMk (H : HermSp M V) {r : ℕ} (t : Term V M r) (u : ↥(MMsharp H t)) : DDt H t :=
  Submodule.Quotient.mk u

def IsomD (H : HermSp M V) {r : ℕ} (t₁ t₂ : Term V M r) (θ : DDt H t₁ ≃ₗ[M.L.O] DDt H t₂) : Prop :=
  ∀ (x y : ↥(MMsharp H t₁)) (x₂ y₂ : ↥(MMsharp H t₂)), θ (ddMk H t₁ x) = ddMk H t₂ x₂ →
    θ (ddMk H t₁ y) = ddMk H t₂ y₂ → H.h x₂ y₂ - H.h x y ∈ M.L.O

def Gam (H : HermSp M V) {r : ℕ} (t : Term V M r) : Set (DDt H t × H.Wb t.f) :=
  {p | ∃ (u : ↥(MMsharp H t)) (hu : (u : V) ∈ H.perp (H.X t.f)), p = (ddMk H t u, H.mkW t.f ⟨u, hu⟩)}

def Gam' (H : HermSp M V) {r : ℕ} (t : Term V M r) : Set (DDt H t × H.Wb t.f') :=
  {p | ∃ (u : ↥(MMsharp H t)) (hu : (u : V) ∈ H.perp (H.X t.f')), p = (ddMk H t u, H.mkW t.f' ⟨u, hu⟩)}

def GamR (H : HermSp M V) {r : ℕ} (t : Term V M r) (c : E) :
    Set (DDt H t × DDt H t × H.Wb t.f × H.Wb t.f') :=
  {p | ∃ (u u' u'' : ↥(MMsharp H t)) (hu : (u : V) ∈ H.perp (H.X t.f)) (hu' : (u' : V) ∈ H.perp (H.X t.f')),
    (u : V) - u' = c • (u'' : V) ∧
      p = (ddMk H t u, ddMk H t u'', H.mkW t.f ⟨u, hu⟩, H.mkW t.f' ⟨u', hu'⟩)}

def MMInt (H : HermSp M V) {r : ℕ} (t : Term V M r) : Prop :=
  ∀ m ∈ MMo H t, ∀ m' ∈ MMo H t, H.h m m' ∈ M.L.O

def Theta (H : HermSp M V) {r : ℕ} (t₁ t₂ : Term V M r) (φ : H.Wb t₁.f ≃ₗ[E] H.Wb t₂.f)
    (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb t₂.f') : Set (DDt H t₁ ≃ₗ[M.L.O] DDt H t₂) :=
  {θ | IsUnit (H.Dl t₂.f t₂.f' (r + 1)) ∧ MMInt H t₂ ∧ IsomD H t₁ t₂ θ ∧
    (M.split = none →
      (fun p => (θ p.1, φ p.2)) '' Gam H t₁ = Gam H t₂ ∧ (fun p => (θ p.1, φ' p.2)) '' Gam' H t₁ = Gam' H t₂) ∧
    (∀ g : SplitG M.L, M.split = some g →
      (fun p => (θ p.1, θ p.2.1, φ p.2.2.1, φ' p.2.2.2)) '' GamR H t₁ (algebraMap F E (g.q : F)) =
        GamR H t₂ (algebraMap F E (g.q : F)))}

def LocalCountHypotheses (H : HermSp M V) {r : ℕ} (t₁ : Term V M r) (f₂ f₂' : Fin (r + 1) → V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂') : Prop :=
  H.IsGeneric t₁ ∧ Formalism.MainNotions.ThinScalesBound.FrameK H f₂ t₁.T ∧ Formalism.MainNotions.ThinScalesBound.FrameK H f₂' t₁.T' ∧
    H.Ident t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ φ φ' ∧
    H.SendsTo φ.toLinearMap 1 1 (t₁.f (Fin.last r)) (f₂ (Fin.last r)) ∧
    H.SendsTo φ'.toLinearMap 1 1 (t₁.f' (Fin.last r)) (f₂' (Fin.last r))

end Cut

section Props

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

def LatSide (M : Model F E) (r n : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  ∀ (t₁ : Term V M r) (f₂ f₂' : Fin (r + 1) → V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂'), LocalCountHypotheses H t₁ f₂ f₂' φ φ' →
    Nat.card {Λ₂ : Submodule M.L.O V | H.IsGeneric ⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩ ∧
        H.Respects t₁ ⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩ φ φ'} =
      Nat.card (Theta H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ φ φ')

def ModSide0 (M : Model F E) (r n : ℕ) (mode : Bool) : Prop :=
  (M.split.isSome = mode) →
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  ∀ (t₁ : Term V M r) (f₂ f₂' : Fin (r + 1) → V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂'), LocalCountHypotheses H t₁ f₂ f₂' φ φ' →
    H.Dl t₁.f t₁.f' r = 0 →
    ∀ (Z₁ Z₂ : M.Mat (r + 1)), Z₁.Z.map M.R.subtype = H.ZZplus t₁ →
      Z₂.Z.map M.R.subtype = HermSp.ZZplusOf M (H.Zhat f₂ f₂') t₁.T t₁.T' →
      Nat.card (Theta H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ φ φ') = M.nIso Z₁ Z₂

def ModSideU (M : Model F E) (r n : ℕ) (mode : Bool) : Prop :=
  (M.split.isSome = mode) →
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  ∀ (t₁ : Term V M r) (f₂ f₂' : Fin (r + 1) → V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂'), LocalCountHypotheses H t₁ f₂ f₂' φ φ' →
    IsUnit (H.Dl t₁.f t₁.f' r) →
    ∀ (Y₁ Y₂ : M.Mat r) (be₁ be₂ al₁ al₂ : Fin r → M.R),
      (∀ a b : Fin r, (Y₁.Z a b : E) = H.ZZplus t₁ a.castSucc b.castSucc ∧
        (Y₂.Z a b : E) = HermSp.ZZplusOf M (H.Zhat f₂ f₂') t₁.T t₁.T' a.castSucc b.castSucc) →
      (∀ a : Fin r, (be₁ a : E) = H.ZZplus t₁ a.castSucc (Fin.last r) ∧
        (be₂ a : E) = HermSp.ZZplusOf M (H.Zhat f₂ f₂') t₁.T t₁.T' a.castSucc (Fin.last r) ∧
        (al₁ a : E) = H.ZZplus t₁ (Fin.last r) a.castSucc ∧
        (al₂ a : E) = HermSp.ZZplusOf M (H.Zhat f₂ f₂') t₁.T t₁.T' (Fin.last r) a.castSucc) →
      Nat.card (Theta H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ φ φ') = M.nIsoBA Y₁ Y₂ be₁ be₂ al₁ al₂

end Props

end Formalism.L2.SG.LsDatumA
end
end
