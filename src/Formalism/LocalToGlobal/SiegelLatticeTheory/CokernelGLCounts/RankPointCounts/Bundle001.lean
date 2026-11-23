module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.RingTheory.DedekindDomain.Basic

@[expose] public section

section

noncomputable section

open MeasureTheory

namespace Formalism.L2.SG.NGCut.SplitEmbedding

section Tri

variable {P : Type} [Fintype P] [DecidableEq P] {α : P → Type} [∀ p, AddCommGroup (α p)]
  (h : P → ℕ) (B : ∀ p, (∀ q, α q) → (∀ q, α q) → α p)
  (hBd : ∀ p (x x' y y' : ∀ q, α q), (∀ q, h q < h p → x q = x' q ∧ y q = y' q) → B p x y = B p x' y')
  (A : ∀ p, AddSubgroup (α p)) (F : ∀ p, Set (α p)) (hFd : ∀ p (v : α p), ∃! a : A p, (a : α p) + v ∈ F p)

def mlaw (x y : ∀ q, α q) : ∀ p, α p := fun p => x p + y p + B p x y

end Tri

end Formalism.L2.SG.NGCut.SplitEmbedding
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.ProdEApprox

section Mono

variable {A : Type*} [CommRing A] {n : ℕ}

def mono (σ : Fin n → Fin n) (ν : Fin n → A) : Matrix (Fin n) (Fin n) A :=
  Matrix.of fun a b => if b = σ a then ν a else 0

theorem mono_mul (σ : Fin n → Fin n) (ν : Fin n → A) (X : Matrix (Fin n) (Fin n) A) (i j : Fin n) :
    (mono σ ν * X) i j = ν i * X (σ i) j := by
  simp [mono, Matrix.mul_apply, ite_mul]

variable {σ : Fin n → Fin n} (hσ : ∀ a, σ (σ a) = a) (ν : Fin n → A)
include hσ

theorem mul_mono (X : Matrix (Fin n) (Fin n) A) (i j : Fin n) : (X * mono σ ν) i j = X i (σ j) * ν (σ j) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (σ j)]
  · simp [mono, hσ]
  · intro b _ hb
    have hj : j ≠ σ b := fun h => hb (by rw [h, hσ])
    simp [mono, hj]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem fix_entry {l c : Matrix (Fin n) (Fin n) A} (h : l * mono σ ν = mono σ ν * c) (i j : Fin n) :
    l i j * ν j = ν i * c (σ i) (σ j) := by
  have e := congrFun (congrFun h i) (σ j)
  rw [mul_mono hσ, mono_mul, hσ] at e
  exact e

theorem fix_pat (hν : ∀ a, IsUnit (ν a)) {l c : Matrix (Fin n) (Fin n) A} (hc : ∀ i j, j < i → c i j = 0)
    (h : l * mono σ ν = mono σ ν * c) (i j : Fin n) (hij : σ j < σ i) : l i j = 0 := by
  have e := fix_entry hσ ν h i j
  rw [hc _ _ hij, mul_zero] at e
  exact (hν j).mul_left_eq_zero.mp e


omit hσ in
def cOf (σ : Fin n → Fin n) (ν : Fin n → A) (l : Matrix (Fin n) (Fin n) A) : Matrix (Fin n) (Fin n) A :=
  Matrix.of fun a b => Ring.inverse (ν (σ a)) * l (σ a) (σ b) * ν (σ b)

theorem fix_cOf (hν : ∀ a, IsUnit (ν a)) (l : Matrix (Fin n) (Fin n) A) :
    l * mono σ ν = mono σ ν * cOf σ ν l := by
  ext i j
  rw [mul_mono hσ, mono_mul]
  simp only [cOf, Matrix.of_apply, hσ]
  rw [← mul_assoc, ← mul_assoc, Ring.mul_inverse_cancel _ (hν i), one_mul]

theorem cOf_up (l : Matrix (Fin n) (Fin n) A) (hl : ∀ i, l i i = 1) (hpat : ∀ i j, σ j < σ i → l i j = 0)
    (hν : ∀ a, IsUnit (ν a)) : (∀ a, cOf σ ν l a a = 1) ∧ ∀ a b, b < a → cOf σ ν l a b = 0 := by
  refine ⟨fun a => ?_, fun a b hab => ?_⟩
  · simp only [cOf, Matrix.of_apply, hl, mul_one]
    exact Ring.inverse_mul_cancel _ (hν _)
  · simp only [cOf, Matrix.of_apply]
    rw [hpat (σ a) (σ b) (by rw [hσ, hσ]; exact hab), mul_zero, zero_mul]

end Mono

end Formalism.L2.SG.Pf.ProdEApprox
end
end

section

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.CountAb

variable {G 𝒳 : Type} [Group G] [MulAction G 𝒳]

section

variable (W : 𝒳) (S N' K : Subgroup G) (π : G →* G) (g : G)

structure Data : Prop where
  stab : ∀ x : G, x • W = W ↔ x ∈ S
  mem : ∀ x, π x ∈ S
  id : ∀ s ∈ S, π s = s
  ker : ∀ x, x ∈ N' ↔ π x = 1
  kπ : ∀ k ∈ K, π k ∈ K

def cell (x : G) : G := x * (π x)⁻¹

theorem π_π (hD : Data W S N' K π) (x : G) : π (π x) = π x := hD.id _ (hD.mem x)

theorem cell_mem (hD : Data W S N' K π) (x : G) : cell π x ∈ N' := by
  rw [hD.ker, cell, map_mul, map_inv, π_π W S N' K π hD, mul_inv_cancel]

theorem cell_smul (hD : Data W S N' K π) (x : G) : cell π x • W = x • W := by
  rw [cell, mul_smul, (hD.stab _).mpr (S.inv_mem (hD.mem x))]

def Cells : Set G := {x | x ∈ N' ∧ ∃ k ∈ K, x • W = k • (g • W)}

def cellRel : Setoid (Cells W N' K g) where
  r x y := (y : G) * (x : G)⁻¹ ∈ K ⊓ N'
  iseqv := ⟨fun x => by simp [(K ⊓ N').one_mem], fun {x y} h => by
      have := (K ⊓ N').inv_mem h; simpa [mul_inv_rev] using this,
    fun {x y z} h1 h2 => by
      have := (K ⊓ N').mul_mem h2 h1; simpa [mul_assoc] using this⟩

def Hs : Subgroup G := K ⊓ MulAction.stabilizer G (g • W)

def toCell (hD : Data W S N' K π) (k : K) : Cells W N' K g :=
  ⟨cell π ((k : G) * g), cell_mem W S N' K π hD _, k, k.2, by rw [cell_smul W S N' K π hD, mul_smul]⟩

theorem toCell_surj (hD : Data W S N' K π) : Function.Surjective (toCell W S N' K π g hD) := by
  rintro ⟨c, hcN, k, hk, hc⟩
  refine ⟨⟨k, hk⟩, Subtype.ext ?_⟩
  show cell π (k * g) = c
  have hs : (k * g)⁻¹ * c ∈ S := by
    rw [← hD.stab, mul_smul, hc, ← mul_smul k g W, inv_smul_smul]
  obtain ⟨s, hsS, hc'⟩ : ∃ s ∈ S, c = k * g * s := ⟨_, hs, by group⟩
  have hπc : π c = 1 := (hD.ker c).mp hcN
  have hπ : π (k * g) = s⁻¹ := by
    rw [hc', map_mul, hD.id s hsS] at hπc
    exact eq_inv_of_mul_eq_one_left hπc
  rw [cell, hπ, inv_inv, ← hc']

end

end Formalism.L2.SG.Pf.CountAb
end
end

section

noncomputable section

open Matrix

namespace Formalism.L2.SG.Pf.UkEmb

variable {n k : ℕ}

def Wm (wf : Fin k → Fin n → ℂ) : Matrix (Fin n) (Fin k) ℂ := Matrix.of fun i a => wf a i

def smat (J : Matrix (Fin n) (Fin n) ℂ) (wf : Fin k → Fin n → ℂ) (G : Matrix (Fin k) (Fin k) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  1 + Wm wf * (G - 1) * (Wm wf)ᴴ * J

theorem entry (wf : Fin k → Fin n → ℂ) (M : Matrix (Fin n) (Fin n) ℂ) (a b : Fin k) :
    ((Wm wf)ᴴ * M * Wm wf) a b = star (wf a) ⬝ᵥ (M *ᵥ wf b) := by
  first
  | (rw [Matrix.mul_assoc]; rfl)
  | (simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Wm, Matrix.of_apply, dotProduct,
        Matrix.mulVec, Pi.star_apply, Finset.sum_mul, Finset.mul_sum]
     rw [Finset.sum_comm]
     exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)

private theorem conjTranspose_Wm_mulVec_apply (wf : Fin k → Fin n → ℂ) (y : Fin n → ℂ) (a : Fin k) :
    ((Wm wf)ᴴ *ᵥ y) a = star (wf a) ⬝ᵥ y := by
  first
  | rfl
  | simp [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Wm]

private theorem conjTranspose_mul_J_one_add_mul_eq_one_add (J : Matrix (Fin n) (Fin n) ℂ) (F : Matrix (Fin n) (Fin k) ℂ)
    (D : Matrix (Fin k) (Fin k) ℂ) (hF : Fᴴ * J * F = 1) :
    Fᴴ * (J * (1 + F * D * Fᴴ * J)) * F = 1 + D := by
  have key : ∀ {m : Type} [Fintype m] (X : Matrix (Fin k) m ℂ), Fᴴ * (J * (F * X)) = X := by
    intro m _ X
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hF, Matrix.one_mul]
  have key2 : Fᴴ * (J * F) = 1 := by rw [← Matrix.mul_assoc, hF]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, key, key2]

private theorem conjTranspose_one_add_mul_J_mul_eq_J (J : Matrix (Fin n) (Fin n) ℂ) (F : Matrix (Fin n) (Fin k) ℂ)
    (D : Matrix (Fin k) (Fin k) ℂ) (hJh : Jᴴ = J) (hF : Fᴴ * J * F = 1) (hD : D + Dᴴ + Dᴴ * D = 0) :
    (1 + F * D * Fᴴ * J)ᴴ * J * (1 + F * D * Fᴴ * J) = J := by
  have key : ∀ {m : Type} [Fintype m] (X : Matrix (Fin k) m ℂ), Fᴴ * (J * (F * X)) = X := by
    intro m _ X
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hF, Matrix.one_mul]
  have h0 : J * (F * ((D + Dᴴ + Dᴴ * D) * (Fᴴ * J))) = 0 := by
    rw [hD]; simp
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc] at h0
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hJh]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, key]
  rw [← sub_eq_zero, ← h0]
  abel

private theorem sub_one_add_conjTranspose_defect_eq_zero_of_unitary (G : Matrix (Fin k) (Fin k) ℂ) (hG : Gᴴ * G = 1) :
    (G - 1) + (G - 1)ᴴ + (G - 1)ᴴ * (G - 1) = 0 := by
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one]
  have e : (Gᴴ - 1) * (G - 1) = Gᴴ * G - Gᴴ - G + 1 := by
    first
    | noncomm_ring
    | (simp only [sub_mul, mul_sub, Matrix.one_mul, Matrix.mul_one]; abel)
  rw [e, hG]
  abel

variable (J : Matrix (Fin n) (Fin n) ℂ) (wf : Fin k → Fin n → ℂ)
  (hon : ∀ a b, star (wf a) ⬝ᵥ (J *ᵥ wf b) = if a = b then 1 else 0)

include hon in
theorem ortho : (Wm wf)ᴴ * J * Wm wf = 1 := by
  ext a b
  rw [entry, hon, Matrix.one_apply]

include hon in
theorem smat_unitary (hJh : Jᴴ = J) (G : Matrix (Fin k) (Fin k) ℂ) (hG : Gᴴ * G = 1) :
    (smat J wf G)ᴴ * J * smat J wf G = J := by
  unfold smat
  exact conjTranspose_one_add_mul_J_mul_eq_J J (Wm wf) (G - 1) hJh
    (ortho J wf hon) (sub_one_add_conjTranspose_defect_eq_zero_of_unitary G hG)

include hon in
theorem smat_fix (G : Matrix (Fin k) (Fin k) ℂ) (x : Fin n → ℂ) (hx : ∀ a, star (wf a) ⬝ᵥ (J *ᵥ x) = 0) :
    smat J wf G *ᵥ x = x := by
  have hz : (Wm wf)ᴴ *ᵥ (J *ᵥ x) = 0 := by
    funext a
    rw [conjTranspose_Wm_mulVec_apply, hx a, Pi.zero_apply]
  unfold smat
  rw [Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hz,
    Matrix.mulVec_zero, add_zero]

include hon in
theorem smat_mat (G : Matrix (Fin k) (Fin k) ℂ) (a b : Fin k) :
    star (wf a) ⬝ᵥ (J *ᵥ (smat J wf G *ᵥ wf b)) = G a b := by
  have hM : (Wm wf)ᴴ * (J * smat J wf G) * Wm wf = G := by
    unfold smat
    rw [conjTranspose_mul_J_one_add_mul_eq_one_add J (Wm wf) (G - 1) (ortho J wf hon)]
    abel
  rw [Matrix.mulVec_mulVec, ← entry, hM]


theorem smat_inv (hJ2 : J * J = 1) (hJh : Jᴴ = J) (G : Matrix (Fin k) (Fin k) ℂ) (hG : Gᴴ * G = 1)
    (hon : ∀ a b, star (wf a) ⬝ᵥ (J *ᵥ wf b) = if a = b then 1 else 0) :
    (J * (smat J wf G)ᴴ * J) * smat J wf G = 1 := by
  have h := smat_unitary J wf hon hJh G hG
  calc (J * (smat J wf G)ᴴ * J) * smat J wf G
      = J * ((smat J wf G)ᴴ * J * smat J wf G) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h, hJ2]

end Formalism.L2.SG.Pf.UkEmb
end
end

section

noncomputable section

open scoped Classical
open MeasureTheory NumberField NumberField.mixedEmbedding

namespace Formalism.L2.SG.NGCut.SplitEmbedding

section Covol

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  (σ : ι ≃ {w : InfinitePlace K // w.IsComplex}) (cj : ι → Prop) [DecidablePred cj]

def phiMap (x : mixedSpace K) : ι → ℂ := fun i => if cj i then (starRingEnd ℂ) (x.2 (σ i)) else x.2 (σ i)

theorem phiMap_add (x y : mixedSpace K) : phiMap σ cj (x + y) = phiMap σ cj x + phiMap σ cj y := by
  funext i
  by_cases h : cj i <;> simp [phiMap, h]

theorem phiMap_mp [IsEmpty {w : InfinitePlace K // w.IsReal}] :
    MeasurePreserving (phiMap σ cj) volume volume := by
  have hu : (volume : Measure ({w : InfinitePlace K // w.IsReal} → ℝ)) Set.univ = 1 := by
    first
    | (rw [volume_pi, Measure.pi_of_empty]; simp)
    | (rw [volume_pi, Measure.pi_univ]; simp)
    | simp [volume_pi, Measure.pi_univ]
    | (erw [Measure.pi_univ]; simp)
  have h1 : MeasurePreserving (Prod.snd : mixedSpace K → ({w : InfinitePlace K // w.IsComplex} → ℂ))
      volume volume := by
    refine ⟨measurable_snd, ?_⟩
    rw [Measure.volume_eq_prod, Measure.map_snd_prod]
    first
    | rw [hu, one_smul]
    | simp only [hu, one_smul]
    | (convert one_smul ENNReal (volume : Measure ({w : InfinitePlace K // w.IsComplex} → ℂ)); exact hu)
  have h2 : MeasurePreserving (fun (y : {w : InfinitePlace K // w.IsComplex} → ℂ) (i : ι) => y (σ i))
      volume volume :=
    MeasurePreserving.symm _
      (measurePreserving_piCongrLeft (fun _ : {w : InfinitePlace K // w.IsComplex} => (volume : Measure ℂ)) σ)
  have hc : MeasurePreserving (starRingEnd ℂ) (volume : Measure ℂ) volume := by
    have := Complex.conjLIE.measurePreserving
    convert this using 2
    all_goals first | rfl | (funext z; simp) | (ext z; simp)
  have h3 : MeasurePreserving (fun (z : ι → ℂ) (i : ι) => if cj i then starRingEnd ℂ (z i) else z i)
      (Measure.pi fun _ => (volume : Measure ℂ)) (Measure.pi fun _ => (volume : Measure ℂ)) := by
    refine measurePreserving_pi (fun _ => (volume : Measure ℂ)) (fun _ => (volume : Measure ℂ))
      (f := fun i c => if cj i then starRingEnd ℂ c else c) (fun i => ?_)
    by_cases h : cj i
    · first
      | (simp only [if_pos h]; exact hc)
      | simpa [h] using hc
    · first
      | (simp only [if_neg h]; exact MeasurePreserving.id _)
      | simp [h, MeasurePreserving.id]
  first
  | exact h3.comp (h2.comp h1)
  | (rw [volume_pi]; exact h3.comp (h2.comp h1))

end Covol

end Formalism.L2.SG.NGCut.SplitEmbedding
end
end

section

noncomputable section

open IsDedekindDomain

namespace Formalism.L2.SG.Pf.ProdEApprox

section DedekindLFunctions

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {n : ℕ}

end DedekindLFunctions

section Ent

variable {A : Type*} [CommRing A] {n : ℕ}

def EntIn (J : AddSubgroup A) (X : Matrix (Fin n) (Fin n) A) : Prop := ∀ i j, X i j ∈ J

theorem entIn_mul {J1 J2 J3 : AddSubgroup A} (h : ∀ x ∈ J1, ∀ y ∈ J2, x * y ∈ J3)
    {X Y : Matrix (Fin n) (Fin n) A} (hX : EntIn J1 X) (hY : EntIn J2 Y) : EntIn J3 (X * Y) := by
  intro i j
  rw [Matrix.mul_apply]
  exact sum_mem fun k _ => h _ (hX i k) _ (hY k j)

theorem entIn_add {J : AddSubgroup A} {X Y : Matrix (Fin n) (Fin n) A} (hX : EntIn J X) (hY : EntIn J Y) :
    EntIn J (X + Y) :=
  fun i j => J.add_mem (hX i j) (hY i j)

theorem entIn_neg {J : AddSubgroup A} {X : Matrix (Fin n) (Fin n) A} (hX : EntIn J X) : EntIn J (-X) :=
  fun i j => J.neg_mem (hX i j)

theorem pow_apply_eq_zero (f : Fin n → ℕ) {X : Matrix (Fin n) (Fin n) A} (hX : ∀ i j, f i ≤ f j → X i j = 0)
    (m : ℕ) : ∀ i j, f i < f j + m → (X ^ m) i j = 0 := by
  induction m with
  | zero =>
    intro i j h
    rw [pow_zero, Matrix.one_apply_ne]
    rintro rfl
    omega
  | succ m ih =>
    intro i j h
    rw [pow_succ, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : f i < f k + m
    · rw [ih i k hk, zero_mul]
    · rw [hX k j (by omega), mul_zero]

theorem pow_eq_zero_of (f : Fin n → ℕ) (hf : ∀ i, f i < n) {X : Matrix (Fin n) (Fin n) A}
    (hX : ∀ i j, f i ≤ f j → X i j = 0) : X ^ n = 0 := by
  ext i j
  have := hf i
  exact pow_apply_eq_zero f hX n i j (by omega)

theorem entIn_negpow {J : AddSubgroup A} (hJ : ∀ x ∈ J, ∀ y ∈ J, x * y ∈ J) {X : Matrix (Fin n) (Fin n) A}
    (hX : EntIn J X) (m : ℕ) : EntIn J ((-X) ^ (m + 1)) := by
  induction m with
  | zero => rw [zero_add, pow_one]; exact entIn_neg hX
  | succ m ih => rw [pow_succ]; exact entIn_mul hJ ih (entIn_neg hX)

theorem inv_sub_one (f : Fin n → ℕ) (hf : ∀ i, f i < n) {J : AddSubgroup A} (hJ : ∀ x ∈ J, ∀ y ∈ J, x * y ∈ J)
    (x : GL (Fin n) A) (hlow : ∀ i j, f i ≤ f j → ((x : Matrix (Fin n) (Fin n) A) - 1) i j = 0)
    (hx : EntIn J ((x : Matrix (Fin n) (Fin n) A) - 1)) :
    EntIn J (((x⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) - 1) ∧
      ∀ i j, f i ≤ f j → (((x⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) - 1) i j = 0 := by
  set X := (x : Matrix (Fin n) (Fin n) A) - 1 with hXdef
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨fun i => i.elim0, fun i => i.elim0⟩
  have hnX : ∀ i j, f i ≤ f j → (-X) i j = 0 := fun i j h => by rw [Matrix.neg_apply, hlow i j h, neg_zero]
  have hpow : (-X) ^ n = 0 := pow_eq_zero_of f hf hnX

  have hxS : (x : Matrix (Fin n) (Fin n) A) * ∑ i ∈ Finset.range n, (-X) ^ i = 1 := by
    have e : (x : Matrix (Fin n) (Fin n) A) = 1 - (-X) := by rw [sub_neg_eq_add, hXdef, add_sub_cancel]
    rw [e, mul_neg_geom_sum, hpow, sub_zero]
  have hinv : ((x⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) = ∑ i ∈ Finset.range n, (-X) ^ i := by
    calc ((x⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)
        = ((x⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) *
          ((x : Matrix (Fin n) (Fin n) A) * ∑ i ∈ Finset.range n, (-X) ^ i) := by rw [hxS, mul_one]
      _ = ∑ i ∈ Finset.range n, (-X) ^ i := by
          rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hY : ((x⁻¹ : GL (Fin (k + 1)) A) : Matrix (Fin (k + 1)) (Fin (k + 1)) A) - 1 =
      ∑ i ∈ Finset.range k, (-X) ^ (i + 1) := by
    rw [hinv, Finset.sum_range_succ', pow_zero, add_sub_cancel_right]
  rw [hY]
  refine ⟨fun i j => ?_, fun i j h => ?_⟩
  · rw [Matrix.sum_apply]
    exact sum_mem fun m _ => entIn_negpow hJ hx m i j
  · rw [Matrix.sum_apply]
    exact Finset.sum_eq_zero fun m _ => pow_apply_eq_zero f hnX (m + 1) i j (by omega)

end Ent

end Formalism.L2.SG.Pf.ProdEApprox
end
end
