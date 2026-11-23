module

public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import CompanionTheory.AutomorphicTheory.ThetaDilations.Nuabs
public import Mathlib.MeasureTheory.Group.Measure
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle003
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Matrix HeckeCharacterZeroLocus.SiegelWeilU

namespace GlobalTheory.CompanionTheory.SW.UnitRep

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem hform_add_left (σ : A →+* A) (J : Matrix n n A) (x x' y : n → A) :
    hform σ J (x + x') y = hform σ J x y + hform σ J x' y := by
  simp only [hform, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem hform_add_right (σ : A →+* A) (J : Matrix n n A) (x y y' : n → A) :
    hform σ J x (y + y') = hform σ J x y + hform σ J x y' := by
  simp only [hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hform_smul_left' (σ : A →+* A) (J : Matrix n n A) (a : A) (x y : n → A) :
    hform σ J (a • x) y = σ a * hform σ J x y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

theorem hform_smul_right' (σ : A →+* A) (J : Matrix n n A) (a : A) (x y : n → A) :
    hform σ J x (a • y) = a * hform σ J x y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hform_single_single (σ : A →+* A) (J : Matrix n n A) (i j : n) :
    hform σ J (Pi.single i 1) (Pi.single j 1) = J i j := by
  rw [hform, Finset.sum_eq_single i, Finset.sum_eq_single j]
  · simp
  · intro b _ hb; simp [Pi.single_eq_of_ne hb]
  · simp
  · intro b _ hb; simp [Pi.single_eq_of_ne hb]
  · simp

theorem hform_self_fixed (σ : A →+* A) (hσ : ∀ y, σ (σ y) = y) (J : Matrix n n A)
    (hJ : ∀ i j, σ (J j i) = J i j) (x : n → A) : σ (hform σ J x x) = hform σ J x x := by

  simp only [hform, map_sum, map_mul, hσ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ i j]; ring

theorem hform_self_congr (σ : A →+* A) (J : Matrix n n A) (P : Ideal A) (x z : n → A)
    (h₁ : ∀ i, z i - x i ∈ P) (h₂ : ∀ i, σ (z i - x i) ∈ P) :
    hform σ J z z - hform σ J x x ∈ P := by
  have e₁ : ∀ i, Ideal.Quotient.mk P (z i) = Ideal.Quotient.mk P (x i) := fun i =>
    Ideal.Quotient.eq.2 (h₁ i)
  have e₂ : ∀ i, Ideal.Quotient.mk P (σ (z i)) = Ideal.Quotient.mk P (σ (x i)) := fun i =>
    Ideal.Quotient.eq.2 (by simpa only [map_sub] using h₂ i)
  refine Ideal.Quotient.eq.1 ?_

  simp only [hform, map_sum, map_mul, e₁, e₂]

theorem exists_hform_not_mem (σ : A →+* A) (hσ : ∀ y, σ (σ y) = y) (h2 : IsUnit (2 : A))
    (hδ : ∃ δ : A, IsUnit δ ∧ σ δ = -δ) (m : ℕ) (J : Matrix (Fin (m + 1)) (Fin (m + 1)) A)
    (hdet : IsUnit J.det) (P : Ideal A) (hP : P.IsMaximal) :
    ∃ y, hform σ J y y ∉ P := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨δ, hδu, hδσ⟩ := hδ
  have hpol : ∀ x y, hform σ J x y + hform σ J y x ∈ P := fun x y => by
    have h := hcon (x + y)
    rw [hform_add_left, hform_add_right, hform_add_right] at h
    have h' := P.sub_mem (P.sub_mem h (hcon x)) (hcon y)
    convert h' using 1
    ring
  have hpol' : ∀ x y, δ * (hform σ J x y - hform σ J y x) ∈ P := fun x y => by
    have h := hpol x (δ • y)
    rw [hform_smul_right', hform_smul_left', hδσ] at h
    convert h using 1
    ring
  have hall : ∀ x y, hform σ J x y ∈ P := fun x y => by
    have h₁ : hform σ J x y - hform σ J y x ∈ P :=
      (Ideal.unit_mul_mem_iff_mem P hδu).1 (hpol' x y)
    have h₂ : 2 * hform σ J x y ∈ P := by
      convert P.add_mem (hpol x y) h₁ using 1
      ring
    exact (Ideal.unit_mul_mem_iff_mem P h2).1 h₂
  have hJ0 : (Ideal.Quotient.mk P).mapMatrix J = 0 := by
    ext i j
    have h := hall (Pi.single i 1) (Pi.single j 1)
    rw [hform_single_single] at h
    simpa using Ideal.Quotient.eq_zero_iff_mem.2 h
  have hd : J.det ∈ P := by
    refine Ideal.Quotient.eq_zero_iff_mem.1 ?_
    rw [RingHom.map_det, hJ0, Matrix.det_zero]
  exact hP.ne_top (Ideal.eq_top_of_isUnit_mem P hd hdet)

theorem comap_isMaximal (σ : A →+* A) (hσ : ∀ y, σ (σ y) = y) (P : Ideal A) (hP : P.IsMaximal) :
    (P.comap σ).IsMaximal :=
  Ideal.comap_isMaximal_of_surjective σ (fun y => ⟨σ y, hσ y⟩)

theorem isCoprime_of_mem_not_mem {P Q : Ideal A} (hP : P.IsMaximal) (hQ : Q.IsMaximal) {a : A}
    (ha : a ∈ P) (ha' : a ∉ Q) : IsCoprime P Q := by
  rw [Ideal.isCoprime_iff_sup_eq]
  refine hP.coprime_of_ne hQ ?_
  rintro rfl
  exact ha' ha

theorem exists_good_on_finset [Finite (MaximalSpectrum A)] (σ : A →+* A) (hσ : ∀ y, σ (σ y) = y)
    (h2 : IsUnit (2 : A)) (hδ : ∃ δ : A, IsUnit δ ∧ σ δ = -δ) (m : ℕ)
    (J : Matrix (Fin (m + 1)) (Fin (m + 1)) A) (hJ : ∀ i j, σ (J j i) = J i j)
    (hdet : IsUnit J.det) (T : Finset (MaximalSpectrum A)) :
    ∃ x, ∀ p ∈ T, hform σ J x x ∉ p.asIdeal := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert q T _ ih =>
    obtain ⟨x, hx⟩ := ih
    by_cases hxq : hform σ J x x ∈ q.asIdeal
    swap
    · refine ⟨x, fun p hp => ?_⟩
      rcases Finset.mem_insert.1 hp with rfl | hp
      · exact hxq
      · exact hx p hp
    obtain ⟨y, hy⟩ := exists_hform_not_mem σ hσ h2 hδ m J hdet q.asIdeal q.isMaximal
    have hfix := hform_self_fixed σ hσ J hJ x
    have hmemc : ∀ {P : Ideal A}, hform σ J x x ∈ P → hform σ J x x ∈ P.comap σ := fun h => by
      rw [Ideal.mem_comap, hfix]; exact h
    have hnotc : ∀ {P : Ideal A}, hform σ J x x ∉ P → hform σ J x x ∉ P.comap σ := fun h h' => by
      rw [Ideal.mem_comap, hfix] at h'; exact h h'
    have hqm := q.isMaximal
    have hqc := comap_isMaximal σ hσ q.asIdeal q.isMaximal
    have hL : ∀ {Q : Ideal A}, Q.IsMaximal → hform σ J x x ∉ Q →
        IsCoprime (q.asIdeal * q.asIdeal.comap σ) Q := fun hQ hn =>
      IsCoprime.mul_left (isCoprime_of_mem_not_mem hqm hQ hxq hn)
        (isCoprime_of_mem_not_mem hqc hQ (hmemc hxq) hn)
    have hK₁ : IsCoprime (q.asIdeal * q.asIdeal.comap σ) (⨅ p ∈ T, p.asIdeal) :=
      Ideal.isCoprime_biInf fun p hp => hL p.isMaximal (hx p hp)
    have hK₂ : IsCoprime (q.asIdeal * q.asIdeal.comap σ) (⨅ p ∈ T, p.asIdeal.comap σ) :=
      Ideal.isCoprime_biInf fun p hp =>
        hL (comap_isMaximal σ hσ _ p.isMaximal) (hnotc (hx p hp))
    obtain ⟨u, hu, c, hc, huc⟩ := Ideal.isCoprime_iff_exists.1 (hK₁.mul_right hK₂)
    have hc₁ : ∀ p ∈ T, c ∈ p.asIdeal := fun p hp =>
      (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 (Ideal.mul_le_left hc) p) hp
    have hc₂ : ∀ p ∈ T, σ c ∈ p.asIdeal := fun p hp =>
      Ideal.mem_comap.1 ((Submodule.mem_iInf _).1
        ((Submodule.mem_iInf _).1 (Ideal.mul_le_right hc) p) hp)
    have hu₁ : u ∈ q.asIdeal := Ideal.mul_le_right (I := q.asIdeal.comap σ) (by rwa [mul_comm] at hu)
    have hu₂ : σ u ∈ q.asIdeal := Ideal.mem_comap.1 (Ideal.mul_le_left (J := q.asIdeal) (by rwa [mul_comm] at hu))
    refine ⟨u • x + c • y, fun p hp => ?_⟩
    have hu' : u = 1 - c := by rw [← huc]; ring
    rcases Finset.mem_insert.1 hp with rfl | hp
    · intro hz
      refine hy ?_
      have h := hform_self_congr σ J p.asIdeal y (u • x + c • y)
        (fun i => ?_) (fun i => ?_)
      · simpa using p.asIdeal.sub_mem hz h
      · have : (u • x + c • y) i - y i = u * (x i - y i) := by
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hu']; ring
        rw [this]
        exact p.asIdeal.mul_mem_right _ hu₁
      · have : (u • x + c • y) i - y i = u * (x i - y i) := by
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hu']; ring
        rw [this, map_mul]
        exact p.asIdeal.mul_mem_right _ hu₂
    · intro hz
      refine hx p hp ?_
      have h := hform_self_congr σ J p.asIdeal x (u • x + c • y)
        (fun i => ?_) (fun i => ?_)
      · simpa using p.asIdeal.sub_mem hz h
      · have : (u • x + c • y) i - x i = c * (y i - x i) := by
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hu']; ring
        rw [this]
        exact p.asIdeal.mul_mem_right _ (hc₁ p hp)
      · have : (u • x + c • y) i - x i = c * (y i - x i) := by
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hu']; ring
        rw [this, map_mul]
        exact p.asIdeal.mul_mem_right _ (hc₂ p hp)

theorem exists_isUnit_hform : ∀ (A : Type) [CommRing A] [Finite (MaximalSpectrum A)] (σ : A →+* A),
    (∀ y, σ (σ y) = y) → IsUnit (2 : A) → (∃ δ : A, IsUnit δ ∧ σ δ = -δ) →
    ∀ (m : ℕ) (J : Matrix (Fin (m + 1)) (Fin (m + 1)) A), (∀ i j, σ (J j i) = J i j) →
    IsUnit J.det → ∃ x, IsUnit (HeckeCharacterZeroLocus.SiegelWeilU.hform σ J x x) := by
  intro A _ _ σ hσ h2 hδ m J hJ hdet
  have := Fintype.ofFinite (MaximalSpectrum A)
  obtain ⟨x, hx⟩ := exists_good_on_finset σ hσ h2 hδ m J hJ hdet Finset.univ
  refine ⟨x, ?_⟩
  by_contra hnu
  obtain ⟨P, hP, hmem⟩ := exists_max_ideal_of_mem_nonunits hnu
  exact hx ⟨P, hP⟩ (Finset.mem_univ _) hmem

end GlobalTheory.CompanionTheory.SW.UnitRep
end

section

open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.QuasiRefl

open HeckeCharacterZeroLocus.SiegelWeilU

section Form

variable {A : Type} [CommRing A] {n : Type} [Fintype n] {σ : A →+* A} {J : Matrix n n A}

theorem hform_eq_dot (x y : n → A) : hform σ J x y = (σ ∘ x) ⬝ᵥ J *ᵥ y := by
  simp [hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem comp_mulVec' (P : Matrix n n A) (x : n → A) : σ ∘ (P *ᵥ x) = P.map σ *ᵥ (σ ∘ x) := by
  funext i
  simp [mulVec, dotProduct]

theorem hform_mulVec' (P Q : Matrix n n A) (x y : n → A) :
    hform σ J (P *ᵥ x) (Q *ᵥ y) = hform σ (cT σ P * J * Q) x y := by
  rw [hform_eq_dot, hform_eq_dot, comp_mulVec', cT, ← mulVec_mulVec, ← mulVec_mulVec,
    dotProduct_mulVec _ (_ᵀ), vecMul_transpose]

theorem hform_sub_left (x d y : n → A) (c : A) :
    hform σ J (x - c • d) y = hform σ J x y - σ c * hform σ J d y := by
  simp [hform, Finset.mul_sum, sub_mul, mul_assoc]

theorem hform_sub_right (x d y : n → A) (c : A) :
    hform σ J x (y - c • d) = hform σ J x y - c * hform σ J x d := by
  simp [hform, Finset.mul_sum, mul_sub, mul_left_comm]

theorem hform_smul_right' (d y : n → A) (c : A) :
    hform σ J y (c • d) = c * hform σ J y d := by
  simp [hform, Finset.mul_sum, mul_left_comm]

theorem hform_conj_symm (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j) (x y : n → A) :
    σ (hform σ J x y) = hform σ J y x := by

  simp only [hform, map_sum, map_mul, hσ, hJ]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end Form

section Refl

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {σ : A →+* A}
  {J : Matrix n n A}

def qrMat (σ : A →+* A) (J : Matrix n n A) (d : n → A) (c : A) : Matrix n n A :=
  1 - c • vecMulVec d ((σ ∘ d) ᵥ* J)

theorem qrMat_mulVec (d : n → A) (c : A) (z : n → A) :
    qrMat σ J d c *ᵥ z = z - (c * hform σ J d z) • d := by
  rw [qrMat, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, hform_eq_dot, dotProduct_mulVec]
  funext i
  simp [mul_comm, mul_left_comm]

theorem ext_mulVec' {P Q : Matrix n n A} (h : ∀ z, P *ᵥ z = Q *ᵥ z) : P = Q := by
  ext i j
  simpa using congrFun (h (Pi.single j 1)) i

theorem qrMat_mul (d : n → A) {c c' : A} (hc : c + c' = c * c' * hform σ J d d) :
    qrMat σ J d c * qrMat σ J d c' = 1 := ext_mulVec' fun z => by
  rw [← mulVec_mulVec, qrMat_mulVec, qrMat_mulVec, hform_sub_right, one_mulVec]
  funext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (-hform σ J d z * d i) * hc

theorem hform_single' (i j : n) :
    hform σ J (Pi.single i 1) (Pi.single j 1) = J i j := by
  have : σ ∘ (Pi.single i 1 : n → A) = Pi.single i 1 := by
    funext k
    by_cases h : k = i <;> simp [h]
  rw [hform_eq_dot, this]
  simp

theorem qrMat_isometry (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j) (d : n → A) (c : A)
    (hc : c + σ c = c * σ c * hform σ J d d) :
    cT σ (qrMat σ J d c) * J * qrMat σ J d c = J := by
  ext i j
  rw [← hform_single' (σ := σ) (J := _ * J * _) i j, ← hform_mulVec', qrMat_mulVec, qrMat_mulVec,
    hform_sub_left, hform_sub_right, hform_sub_right, map_mul, hform_conj_symm hσ hJ,
    hform_single']
  linear_combination
    (-hform σ J (Pi.single i 1) d * hform σ J d (Pi.single j 1)) * hc

def qr (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j) (d : n → A) (c : A)
    (hc : c + σ c = c * σ c * hform σ J d d) : UJ σ J :=
  ⟨⟨qrMat σ J d c, qrMat σ J d (σ c), qrMat_mul d hc,
    qrMat_mul d (by linear_combination hc)⟩, qrMat_isometry hσ hJ d c hc⟩

end Refl

theorem exists_unitary_carry (A : Type) [CommRing A] (σ : A →+* A) (hσ : ∀ y, σ (σ y) = y) (M : ℕ)
    (J : Matrix (Fin M) (Fin M) A) (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin M → A) (ε : A)
    (hxy : hform σ J x x = hform σ J y y) (hβ : IsUnit (hform σ J x x)) (hε : ε * σ ε = 1)
    (hu : IsUnit (hform σ J x x - σ ε * hform σ J y x)) :
    ∃ g ∈ UJ σ J, (g : Matrix (Fin M) (Fin M) A) *ᵥ x = y ∧
      ∀ z, hform σ J x z = 0 → hform σ J y z = 0 → (g : Matrix (Fin M) (Fin M) A) *ᵥ z = z := by
  obtain ⟨bi, hb⟩ := hβ.exists_right_inv
  obtain ⟨ui, hui⟩ := hu.exists_right_inv
  set β := hform σ J x x with hβdef
  set w := hform σ J y x with hw
  have hyy : hform σ J y y = β := hxy.symm
  have hxyw : hform σ J x y = σ w := by rw [hw, hform_conj_symm hσ hJ]
  have hσβ : σ β = β := hform_conj_symm hσ hJ x x
  have hσε : σ (σ ε) = ε := hσ ε
  have hσb : σ bi = bi := by
    have h1 : β * σ bi = 1 := by
      have := congrArg σ hb
      rwa [map_mul, hσβ, map_one] at this
    linear_combination bi * h1 - σ bi * hb
  have hσui : (β - ε * σ w) * σ ui = 1 := by
    have := congrArg σ hui
    rwa [map_mul, map_sub, map_mul, hσβ, hσε, map_one] at this
  set d : Fin M → A := x - ε • y with hd
  have hdx : hform σ J d x = β - σ ε * w := hform_sub_left x y x ε
  have hdy : hform σ J d y = σ w - σ ε * β := by
    rw [hd, hform_sub_left, hxyw, hyy]
  have hdd : hform σ J d d = (β - σ ε * w) + (β - ε * σ w) + (ε * σ ε - 1) * β := by
    rw [hform_sub_right, hdx, hdy]
    ring
  have hc₁ : (1 - σ ε) * bi + σ ((1 - σ ε) * bi)
      = (1 - σ ε) * bi * σ ((1 - σ ε) * bi) * hform σ J y y := by
    rw [map_mul, map_sub, map_one, hσε, hσb, hyy]
    linear_combination (-(1 - ε - σ ε + ε * σ ε) * bi) * hb + (-bi) * hε
  have hc₂ : ui + σ ui = ui * σ ui * hform σ J d d := by
    rw [hdd, hε]
    linear_combination (-σ ui) * hui + (-ui) * hσui
  refine ⟨((qr hσ hJ y _ hc₁ * qr hσ hJ d ui hc₂ : UJ σ J) : GL (Fin M) A), SetLike.coe_mem _, ?_, ?_⟩
  · have h2 : qrMat σ J d ui *ᵥ x = ε • y := by
      rw [qrMat_mulVec, hdx, mul_comm ui, hui, one_smul, hd]
      simp
    have h3 : qrMat σ J y ((1 - σ ε) * bi) *ᵥ (ε • y) = y := by
      rw [qrMat_mulVec, hform_smul_right', hyy]
      funext i
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination ((1 - σ ε) * ε * y i) * (-hb) + (y i) * hε
    show (qrMat σ J y ((1 - σ ε) * bi) * qrMat σ J d ui) *ᵥ x = y
    rw [← mulVec_mulVec, h2, h3]
  · intro z hxz hyz
    have hdz : hform σ J d z = 0 := by
      rw [hd, hform_sub_left, hxz, hyz]
      simp
    show (qrMat σ J y ((1 - σ ε) * bi) * qrMat σ J d ui) *ᵥ z = z
    have h2 : qrMat σ J d ui *ᵥ z = z := by
      rw [qrMat_mulVec, hdz, mul_zero, zero_smul, sub_zero]
    rw [← mulVec_mulVec, h2, qrMat_mulVec, hyz, mul_zero, zero_smul, sub_zero]

end GlobalTheory.CompanionTheory.SW.QuasiRefl
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.BB

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

section Coord

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def cv (R : Type) [CommRing R] [Algebra F R] {d M : ℕ} (b : Module.Basis (Fin d) F E)
    (x : Fin M → R ⊗[F] E) : Fin M × Fin d → R :=
  fun p => (Algebra.TensorProduct.basis R b).repr (x p.1) p.2

def gmat (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {d M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin d) F E) (h : HA R σ J) :
    Matrix (Fin M × Fin d) (Fin M × Fin d) R :=
  fun p q => (Algebra.TensorProduct.basis R b).repr
    ((HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) p.1 q.1 * inclR R (b q.2)) p.2

def ofF {d M : ℕ} (b : Module.Basis (Fin d) F E) (x : Fin M × Fin d → F) : Fin 1 → Fin M → E :=
  fun _ i => ∑ k, x (i, k) • b k

end Coord

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def gfin (σ : E →ₐ[F] E) {d M : ℕ} (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin d) F E)
    (h : HA (AF F) σ J) : Matrix (Fin M × Fin d) (Fin M × Fin d) (Af F) :=
  (gmat (AF F) σ J b h⁻¹).map (sndA F)

def ginf (e : Ainf F ≃+* (InfinitePlace F → ℝ)) (σ : E →ₐ[F] E) {d M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin d) F E) (h : HA (AF F) σ J)
    (w : InfinitePlace F) : Matrix (Fin M × Fin d) (Fin M × Fin d) ℝ :=
  (gmat (AF F) σ J b h⁻¹).map fun t => e (fstA F t) w

def xw (e : Ainf F ≃+* (InfinitePlace F → ℝ)) {d M : ℕ} (b : Module.Basis (Fin d) F E)
    (X : Fin 1 → Fin M → Ainf F ⊗[F] E) (w : InfinitePlace F) : Fin M × Fin d → ℝ :=
  fun p => e (cv (Ainf F) b (X 0) p) w

def gaussQ (e : Ainf F ≃+* (InfinitePlace F → ℝ)) {d M : ℕ} (b : Module.Basis (Fin d) F E)
    (Pm : InfinitePlace F → Matrix (Fin M × Fin d) (Fin M × Fin d) ℝ)
    (X : Fin 1 → Fin M → Ainf F ⊗[F] E) : ℝ :=
  Real.exp (-Real.pi * ∑ w, xw e b X w ⬝ᵥ (Pm w *ᵥ xw e b X w))

def prH {G : Type} [MeasurableSpace G] (μ : Measure G) (𝓕 : Set G) : Measure G :=
  (μ 𝓕)⁻¹ • μ.restrict 𝓕

end Adelic

end GlobalTheory.CompanionTheory.SW.BB
end
end

section

open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.Adelic

theorem unfold_coset_sum_fundamentalDomain : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] (Γ Γ' : Subgroup G) [Countable Γ], Γ' ≤ Γ → ∀ 𝓕 : Set G, IsFundamentalDomain Γ 𝓕 μ → ∀ (Q : Type) (r : Q → G), (∀ q, r q ∈ Γ) → (∀ γ ∈ Γ, ∃! q, γ * (r q)⁻¹ ∈ Γ') → ∃ 𝓕' : Set G, IsFundamentalDomain Γ' 𝓕' μ ∧ ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ h in 𝓕, ∑' q, f (r q * h) ∂μ = ∫⁻ h in 𝓕', f h ∂μ :=
  CompanionTheory.PlacePermOperatorBicommutantSpan.unf

end GlobalTheory.CompanionTheory.Adelic
end

section

open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.Adelic

theorem integral_fundamentalDomain_le_siegel : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (P : Subgroup G) (ν : Measure G) [SFinite ν], (∀ p ∈ P, ν.map (fun g => p * g) = ν) → (∀ U ∈ 𝓝 (1 : G), ν U ≠ 0) → ∀ C : Set G, IsCompact C → ∃ (C' : Set G) (K : ℝ≥0∞), IsCompact C' ∧ K < ⊤ ∧ ∀ (Γ : Subgroup G) [Countable Γ], Γ ≤ P → ∀ 𝓕 : Set G, IsFundamentalDomain Γ 𝓕 μ → ∀ S : Set G, MeasurableSet S → (∀ᵐ p ∂ν, ∃ γ ∈ Γ, γ * p ∈ S) → ∀ f g : G → ℝ≥0∞, Measurable f → Measurable g → (∀ γ ∈ Γ, ∀ x, f (γ * x) = f x) → (∀ x, f x ≠ 0 → ∃ p ∈ P, ∃ c ∈ C, x = p * c) → (∀ p ∈ S, ∀ c ∈ C', f (p * c) ≤ g p) → ∫⁻ x in 𝓕, f x ∂μ ≤ K * ∫⁻ p in S, g p ∂ν := by
  first | exact CompanionTheory.PlacePermOperatorBicommutantSpan.cover | exact @CompanionTheory.PlacePermOperatorBicommutantSpan.cover

end GlobalTheory.CompanionTheory.Adelic
end

section

open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

theorem _root_.GlobalTheory.T.haar_modular_character_of_continuous_action : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] [IsTopologicalAddGroup V] (μ : Measure V) [μ.IsAddHaarMeasure] (Q : Type) [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [DistribMulAction Q V] [ContinuousSMul Q V], ∃ χ : Q →* ℝ≥0, Continuous χ ∧ ∀ q : Q, μ.map (fun v => q • v) = χ q • μ := by
  first | exact @GlobalTheory.CompanionTheory.SW.exists_continuous_modulus_of_continuous_action | exact GlobalTheory.CompanionTheory.SW.exists_continuous_modulus_of_continuous_action | (intros; apply GlobalTheory.CompanionTheory.SW.exists_continuous_modulus_of_continuous_action <;> assumption)
end
