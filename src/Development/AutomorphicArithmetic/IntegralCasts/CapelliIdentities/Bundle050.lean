module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Geometry.Manifold.StructureGroupoid

@[expose] public section

section

noncomputable def UpperTheory.Reformulated.B.H71.wt1 :
    Fin (3 : ℕ) → ℤ :=
    fun (i : Fin (3 : ℕ)) ↦ (1 : ℤ) - (↑(↑i : ℕ) : ℤ)

theorem UpperTheory.Reformulated.B.H71.aux2.{u_1} :
    ∀ {R : Type u_1} [inst : CommRing R] (t : Rˣ),
      ((Matrix.diagonal fun (i : Fin (3 : ℕ)) ↦ (↑(t ^ UpperTheory.Reformulated.B.H71.wt1 i) : R)) *
          Matrix.diagonal fun (i : Fin (3 : ℕ)) ↦ (↑(t ^ UpperTheory.Reformulated.B.H71.wt1 i)⁻¹ : R)) =
        (1 : Matrix (Fin (3 : ℕ)) (Fin (3 : ℕ)) R) := by
  intro R _ t
  rw [Matrix.diagonal_mul_diagonal]
  simp only [Units.mul_inv, Matrix.diagonal_one]

theorem UpperTheory.Reformulated.B.H71.aux3.{u_1} :
    ∀ {R : Type u_1} [inst : CommRing R] (t : Rˣ),
      ((Matrix.diagonal fun (i : Fin (3 : ℕ)) ↦ (↑(t ^ UpperTheory.Reformulated.B.H71.wt1 i)⁻¹ : R)) *
          Matrix.diagonal fun (i : Fin (3 : ℕ)) ↦ (↑(t ^ UpperTheory.Reformulated.B.H71.wt1 i) : R)) =
        (1 : Matrix (Fin (3 : ℕ)) (Fin (3 : ℕ)) R) := by
  intro R _ t
  rw [Matrix.diagonal_mul_diagonal]
  simp only [Units.inv_mul, Matrix.diagonal_one]

noncomputable def UpperTheory.Reformulated.B.H71.torGL.{u_1} :
    {R : Type u_1} → [inst : CommRing R] → Rˣ → GL (Fin (3 : ℕ)) R :=
    fun {R : Type u_1} [CommRing R] (t : Rˣ) ↦
      { val := Matrix.diagonal fun (i : Fin (3 : ℕ)) ↦ (↑(t ^ UpperTheory.Reformulated.B.H71.wt1 i) : R),
        inv := Matrix.diagonal fun (i : Fin (3 : ℕ)) ↦ (↑(t ^ UpperTheory.Reformulated.B.H71.wt1 i)⁻¹ : R),
        val_inv := UpperTheory.Reformulated.B.H71.aux2 t, inv_val := UpperTheory.Reformulated.B.H71.aux3 t : (Matrix (Fin (3 : ℕ)) (Fin (3 : ℕ)) R)ˣ }

theorem UpperTheory.Reformulated.B.H71.aux5.{u_1} :
    ∀ (R : Type u_1) [inst : CommRing R], UpperTheory.Reformulated.B.H71.torGL (1 : Rˣ) = (1 : GL (Fin (3 : ℕ)) R) := by
  intro R _
  apply Units.ext
  change Matrix.diagonal (fun i : Fin 3 ↦ (↑((1 : Rˣ) ^ UpperTheory.Reformulated.B.H71.wt1 i) : R)) = 1
  simp only [one_zpow, Units.val_one, Matrix.diagonal_one]

theorem UpperTheory.Reformulated.B.H71.aux6.{u_1} :
    ∀ (R : Type u_1) [inst : CommRing R] (s t : Rˣ),
      UpperTheory.Reformulated.B.H71.torGL (s * t) = UpperTheory.Reformulated.B.H71.torGL s * UpperTheory.Reformulated.B.H71.torGL t := by
  intro R _ s t
  apply Units.ext
  change Matrix.diagonal (fun i : Fin 3 ↦ (↑((s * t) ^ UpperTheory.Reformulated.B.H71.wt1 i) : R)) =
    Matrix.diagonal (fun i : Fin 3 ↦ (↑(s ^ UpperTheory.Reformulated.B.H71.wt1 i) : R)) *
      Matrix.diagonal (fun i : Fin 3 ↦ (↑(t ^ UpperTheory.Reformulated.B.H71.wt1 i) : R))
  rw [Matrix.diagonal_mul_diagonal]
  simp only [mul_zpow, Units.val_mul]

noncomputable def UpperTheory.Reformulated.B.H71.tor.{u_1} :
    (R : Type u_1) → [inst : CommRing R] → Rˣ →* GL (Fin (3 : ℕ)) R :=
    fun (R : Type u_1) [CommRing R] ↦
      { toFun := UpperTheory.Reformulated.B.H71.torGL, map_one' := UpperTheory.Reformulated.B.H71.aux5 R, map_mul' := UpperTheory.Reformulated.B.H71.aux6 R :
        Rˣ →* GL (Fin (3 : ℕ)) R }

theorem UpperTheory.Reformulated.B.H71.map_tor :
    ∀ {A B : Type} [inst : CommRing A] [inst_1 : CommRing B] (f : A →+* B) (t : Aˣ),
      (Matrix.GeneralLinearGroup.map f : GL (Fin (3 : ℕ)) A → GL (Fin (3 : ℕ)) B)
          ((UpperTheory.Reformulated.B.H71.tor A : Aˣ → GL (Fin (3 : ℕ)) A) t) =
        (UpperTheory.Reformulated.B.H71.tor B : Bˣ → GL (Fin (3 : ℕ)) B) ((Units.map (↑f : A →* B) : Aˣ → Bˣ) t) := by
  intro A B _ _ f t
  apply Units.ext
  change (Matrix.diagonal (fun i : Fin 3 ↦ (↑(t ^ UpperTheory.Reformulated.B.H71.wt1 i) : A))).map f =
    Matrix.diagonal (fun i : Fin 3 ↦ (↑((Units.map (f : A →* B) t) ^ UpperTheory.Reformulated.B.H71.wt1 i) : B))
  rw [Matrix.diagonal_map (map_zero f)]
  congr 1
  funext i
  rw [← map_zpow, Units.coe_map]
  rfl
end

section

noncomputable def UpperTheory.Reformulated.B.Ua5.MatIrr.{u_1, u_2} :
    {G : Type u_1} →
      [inst : Group G] → {R : Type u_2} → [CommRing R] → {m : ℕ} → Subgroup G → (G → Matrix (Fin m) (Fin m) R) → Prop :=
    fun {G : Type u_1} [Group G] {R : Type u_2} [CommRing R] {m : ℕ} (H : Subgroup G) (a : G → Matrix (Fin m) (Fin m) R) ↦
      ∀ (W : Submodule R (Fin m → R)), (∀ g ∈ H, ∀ v ∈ W, (a g).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤

theorem UpperTheory.Reformulated.B.Ua5.matIrr_conj :
    ∀ {G R : Type} [inst : Group G] [inst_1 : CommRing R] {m : ℕ} {U : Subgroup G} {a a' : G → Matrix (Fin m) (Fin m) R}
      (h : GL (Fin m) R),
      (∀ g ∈ U, a g = (↑h⁻¹ : Matrix (Fin m) (Fin m) R) * a' g * (↑h : Matrix (Fin m) (Fin m) R)) →
        UpperTheory.Reformulated.B.Ua5.MatIrr U a → UpperTheory.Reformulated.B.Ua5.MatIrr U a' := by
  intro G R _ _ m U a a' h hconj hirr W hW
  have hcancel : ∀ w : Fin m → R,
      (↑h : Matrix (Fin m) (Fin m) R).mulVec ((↑h⁻¹ : Matrix (Fin m) (Fin m) R).mulVec w) = w := by
    intro w
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hmem : ∀ v : Fin m → R,
      v ∈ W.comap (Matrix.mulVecLin (↑h : Matrix (Fin m) (Fin m) R)) ↔
        (↑h : Matrix (Fin m) (Fin m) R).mulVec v ∈ W := fun v => Iff.rfl
  have hinv : ∀ g ∈ U, ∀ v ∈ W.comap (Matrix.mulVecLin (↑h : Matrix (Fin m) (Fin m) R)),
      (a g).mulVec v ∈ W.comap (Matrix.mulVecLin (↑h : Matrix (Fin m) (Fin m) R)) := by
    intro g hg v hv
    rw [hmem] at hv ⊢
    rw [hconj g hg, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hcancel]
    exact hW g hg _ hv
  rcases hirr _ hinv with hbot | htop
  · left
    rw [eq_bot_iff]
    intro w hw
    have h1 : (↑h⁻¹ : Matrix (Fin m) (Fin m) R).mulVec w ∈
        W.comap (Matrix.mulVecLin (↑h : Matrix (Fin m) (Fin m) R)) := by
      rw [hmem, hcancel]
      exact hw
    rw [hbot, Submodule.mem_bot] at h1
    rw [Submodule.mem_bot, ← hcancel w, h1, Matrix.mulVec_zero]
  · right
    rw [eq_top_iff]
    intro w _
    have h1 : (↑h⁻¹ : Matrix (Fin m) (Fin m) R).mulVec w ∈
        W.comap (Matrix.mulVecLin (↑h : Matrix (Fin m) (Fin m) R)) := by
      rw [htop]
      exact Submodule.mem_top
    rwa [hmem, hcancel] at h1
end

section

namespace UpperTheory.Reformulated.B.NormalizedMatrixSpan

@[reducible] noncomputable def Mat (C : Type) (N : ℕ) : Type := Matrix (Fin N) (Fin N) C

noncomputable def Normd {C : Type} [Field C] {N : ℕ} {Γ : Type} [Group Γ] (ρ : Γ →* GL (Fin N) C)
    (A : Subalgebra C (Mat C N)) : Prop :=
  ∀ g : Γ, ∀ a ∈ A,
    (ρ g : Matrix (Fin N) (Fin N) C) * a * (ρ g⁻¹ : Matrix (Fin N) (Fin N) C) ∈ A

noncomputable def gens {Γ C : Type} [Group Γ] [Field C] {N : ℕ} (ρ : Γ →* GL (Fin N) C)
    (A : Subalgebra C (Mat C N)) : Set (Mat C N) :=
  {x : Mat C N | ∃ a ∈ A, ∃ g : Γ, x = a * (ρ g : Matrix (Fin N) (Fin N) C)}

theorem span_mul {Γ C : Type} [Group Γ] [Field C] {N : ℕ} (ρ : Γ →* GL (Fin N) C)
    (A : Subalgebra C (Mat C N)) (hA : Normd ρ A) (x y : Mat C N)
    (hx : x ∈ Submodule.span C (gens ρ A)) (hy : y ∈ Submodule.span C (gens ρ A)) :
    x * y ∈ Submodule.span C (gens ρ A) := by
  have h := Submodule.mul_mem_mul hx hy
  rw [Submodule.span_mul_span] at h
  refine Submodule.span_mono ?_ h
  rintro _ ⟨_, ⟨a, ha, g, rfl⟩, _, ⟨b, hb, k, rfl⟩, rfl⟩
  refine ⟨a * ((ρ g : Matrix (Fin N) (Fin N) C) * b * (ρ g⁻¹ : Matrix (Fin N) (Fin N) C)),
    A.mul_mem ha (hA g b hb), g * k, ?_⟩
  have e : (ρ g⁻¹ : Matrix (Fin N) (Fin N) C) * (ρ (g * k) : Matrix (Fin N) (Fin N) C)
      = (ρ k : Matrix (Fin N) (Fin N) C) := by
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel_left]
  simp only [mul_assoc, e]

end UpperTheory.Reformulated.B.NormalizedMatrixSpan
end

section

@[reducible] noncomputable def UpperTheory.Reformulated.B.StronglyIrreducible.gm :
    {G R : Type} → [inst : Group G] → [inst_1 : CommRing R] → {n : ℕ} → (G →* GL (Fin n) R) → G → Matrix (Fin n) (Fin n) R :=
    fun {G R : Type} [Group G] [CommRing R] {n : ℕ} (r : G →* GL (Fin n) R) (g : G) ↦
      (↑((r : G → GL (Fin n) R) g) : Matrix (Fin n) (Fin n) R)

noncomputable def UpperTheory.Reformulated.B.StronglyIrreducible.StrongIrr :
    {G κ : Type} → [inst : Group G] → [inst_1 : Field κ] → {n : ℕ} → (G →* GL (Fin n) κ) → Prop :=
    fun {G κ : Type} [Group G] [Field κ] {n : ℕ} (r : G →* GL (Fin n) κ) ↦
      ∀ (W : Submodule κ (Fin n → κ)) (S : Subgroup G),
        S.FiniteIndex → (∀ (g : G), g ∈ S ↔ ∀ v ∈ W, (UpperTheory.Reformulated.B.StronglyIrreducible.gm r g).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤

theorem UpperTheory.Reformulated.B.StronglyIrreducible.strongIrr_conj :
    ∀ {G κ : Type} [inst : Group G] [inst_1 : Field κ] {n : ℕ} (r : G →* GL (Fin n) κ),
      UpperTheory.Reformulated.B.StronglyIrreducible.StrongIrr r →
        ∀ (P : GL (Fin n) κ),
          UpperTheory.Reformulated.B.StronglyIrreducible.StrongIrr
            ((MulEquiv.toMonoidHom ((MulAut.conj : GL (Fin n) κ → MulAut (GL (Fin n) κ)) P⁻¹)).comp r) := by
  intro G κ _ _ n r h P W S hS hW
  have h1 : ∀ v : Fin n → κ, ((P⁻¹ : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ).mulVec
      ((P : Matrix (Fin n) (Fin n) κ).mulVec v) = v := by
    intro v
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have h2 : ∀ v : Fin n → κ, (P : Matrix (Fin n) (Fin n) κ).mulVec
      (((P⁻¹ : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ).mulVec v) = v := by
    intro v
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have h3 : ∀ (g : G) (v : Fin n → κ),
      (UpperTheory.Reformulated.B.StronglyIrreducible.gm ((MulEquiv.toMonoidHom
        ((MulAut.conj : GL (Fin n) κ → MulAut (GL (Fin n) κ)) P⁻¹)).comp r) g).mulVec v
      = ((P⁻¹ : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ).mulVec
        ((UpperTheory.Reformulated.B.StronglyIrreducible.gm r g).mulVec ((P : Matrix (Fin n) (Fin n) κ).mulVec v)) := by
    intro g v
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    change (((P⁻¹ * r g * P⁻¹⁻¹ : GL (Fin n) κ)) : Matrix (Fin n) (Fin n) κ).mulVec v = _
    rw [inv_inv, Units.val_mul, Units.val_mul]
  have hmem : ∀ v : Fin n → κ,
      v ∈ W.comap (Matrix.mulVecLin ((P⁻¹ : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ)) ↔
        ((P⁻¹ : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ).mulVec v ∈ W := fun v => Iff.rfl
  have key := h (W.comap (Matrix.mulVecLin ((P⁻¹ : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ)))
    S hS (by
      intro g
      rw [hW g]
      constructor
      · intro hg v hv
        have := hg _ ((hmem v).1 hv)
        rw [h3, h2] at this
        exact (hmem _).2 this
      · intro hg v hv
        rw [h3]
        apply (hmem _).1
        apply hg
        rw [hmem, h1]
        exact hv)
  rcases key with key | key
  · left
    rw [eq_bot_iff]
    intro v hv
    have hv' : (P : Matrix (Fin n) (Fin n) κ).mulVec v ∈
        W.comap (Matrix.mulVecLin ((P⁻¹ : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ)) := by
      rw [hmem, h1]
      exact hv
    rw [key, Submodule.mem_bot] at hv'
    rw [Submodule.mem_bot, ← h1 v, hv', Matrix.mulVec_zero]
  · right
    rw [eq_top_iff]
    intro v _
    rw [← h1 v]
    apply (hmem _).1
    rw [key]
    exact Submodule.mem_top
end

section

private lemma liftUnitri {R K : Type} [CommRing R] [CommRing K] (f : R →+* K) (I : Ideal R) {n : ℕ}
    (h : GL (Fin n) K) (a : Fin n → Fin n → R)
    (ha : ∀ i j, f (a i j) = (h : Matrix (Fin n) (Fin n) K) i j)
    (hlow : ∀ i j, j < i → a i j = 0) (hd : ∀ i, a i i = 1)
    (hI : ∀ i j, i < j → a i j ∈ I) :
    h ∈ Subgroup.map (Matrix.GeneralLinearGroup.map f)
      (Matrix.GeneralLinearGroup.map (n := Fin n) (Ideal.Quotient.mk I)).ker := by
  have hdet : (Matrix.of a).det = 1 := by
    rw [Matrix.det_of_upperTriangular (M := Matrix.of a) (fun i j hij => hlow i j hij)]
    simp [hd]
  let H : GL (Fin n) R := Matrix.GeneralLinearGroup.mk'' (Matrix.of a) (by rw [hdet]; exact isUnit_one)
  refine ⟨H, ?_, ?_⟩
  · rw [SetLike.mem_coe, MonoidHom.mem_ker]
    ext i j
    rcases lt_trichotomy i j with hij | rfl | hij
    · have : Ideal.Quotient.mk I (a i j) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (hI i j hij)
      simpa [H, Matrix.one_apply, hij.ne] using this
    · simp [H, hd]
    · simp [H, hlow i j hij, Matrix.one_apply, hij.ne']
  · ext i j
    simp [H, ha]

theorem UpperTheory.diagonal_conjugate_mem :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ} (ϖ : kˣ), ValuativeRel.valuation k (ϖ : k) < 1 →
        ∀ (c : ℕ) (z g : GL (Fin n) k),
        (z : Matrix (Fin n) (Fin n) k) = Matrix.diagonal (fun i : Fin n => ((ϖ ^ ((n : ℤ) - 1 - ((i : ℕ) : ℤ)) : kˣ) : k)) →
        g ∈ (Matrix.GeneralLinearGroup.map (n := Fin n) (algebraMap (↥(ValuativeRel.valuation k).integer) k)).range →
        (g : Matrix (Fin n) (Fin n) k).BlockTriangular id → (∀ i, (g : Matrix (Fin n) (Fin n) k) i i = 1) →
        z ^ c * g * (z ^ c)⁻¹ ∈ Subgroup.map (Matrix.GeneralLinearGroup.map (algebraMap (↥(ValuativeRel.valuation k).integer) k))
          (Matrix.GeneralLinearGroup.map (n := Fin n)
            (Ideal.Quotient.mk (IsLocalRing.maximalIdeal ↥(ValuativeRel.valuation k).integer ^ c))).ker := by
  intro k _ _ _ _ n ϖ hϖ c z g hz hg hb hd
  obtain ⟨g0, hg0⟩ := hg
  have hg0' : ∀ i j, algebraMap (↥(ValuativeRel.valuation k).integer) k ((g0 : Matrix (Fin n) (Fin n) _) i j)
      = (g : Matrix (Fin n) (Fin n) k) i j := by
    intro i j
    rw [← hg0]
    simp
  let p : ↥(ValuativeRel.valuation k).integer := ⟨(ϖ : k), hϖ.le⟩
  have hp : p ∈ IsLocalRing.maximalIdeal ↥(ValuativeRel.valuation k).integer := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    obtain ⟨q, hq⟩ := hu.exists_right_inv
    have h1 : ValuativeRel.valuation k ((p * q : ↥(ValuativeRel.valuation k).integer) : k) = 1 := by
      rw [hq]; simp
    have h2 : ValuativeRel.valuation k ((q : ↥(ValuativeRel.valuation k).integer) : k) ≤ 1 := q.2
    rw [Subring.coe_mul, map_mul] at h1
    have h3 : ValuativeRel.valuation k (ϖ : k) * ValuativeRel.valuation k ((q : ↥(ValuativeRel.valuation k).integer) : k) < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_right' h2) hϖ
    exact absurd h1 h3.ne
  let t : Fin n → kˣ := fun i => ϖ ^ ((n : ℤ) - 1 - ((i : ℕ) : ℤ))
  have hz1 : ((z ^ c : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)
      = Matrix.diagonal (fun i => (((t i) ^ c : kˣ) : k)) := by
    rw [Units.val_pow_eq_pow_val, hz, Matrix.diagonal_pow]
    congr 1
  have hz2 : (((z ^ c)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)
      = Matrix.diagonal (fun i => ((((t i) ^ c)⁻¹ : kˣ) : k)) := by
    apply Units.inv_eq_of_mul_eq_one_right
    rw [hz1, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext i
    rw [← Units.val_mul]
    simp
  have hent : ∀ i j, ((z ^ c * g * (z ^ c)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j
      = (((t i) ^ c : kˣ) : k) * (g : Matrix (Fin n) (Fin n) k) i j * ((((t j) ^ c)⁻¹ : kˣ) : k) := by
    intro i j
    rw [Units.val_mul, Units.val_mul, hz2, hz1, Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hpow : ∀ i j : Fin n, i < j →
      (((t i) ^ c : kˣ) : k) * ((((t j) ^ c)⁻¹ : kˣ) : k) = (ϖ : k) ^ (((j : ℕ) - (i : ℕ)) * c) := by
    intro i j hij
    rw [← Units.val_mul, ← Units.val_pow_eq_pow_val]
    congr 1
    have hle : (i : ℕ) ≤ (j : ℕ) := hij.le
    simp only [t]
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_neg, ← zpow_add]
    congr 1
    push_cast [Nat.cast_sub hle]
    ring
  refine liftUnitri _ _ _
    (fun i j => if i < j then p ^ (((j : ℕ) - (i : ℕ)) * c) * (g0 : Matrix (Fin n) (Fin n) _) i j
      else if i = j then 1 else 0) ?_ ?_ ?_ ?_
  · intro i j
    rw [hent]
    rcases lt_trichotomy i j with hij | rfl | hij
    · rw [if_pos hij, map_mul, hg0', map_pow, mul_right_comm, hpow i j hij]
      rfl
    · rw [if_neg (lt_irrefl _), if_pos rfl, hd, map_one, mul_one, ← Units.val_mul]
      simp
    · rw [if_neg hij.not_gt, if_neg hij.ne', hb hij]
      simp
  · intro i j hij
    rw [if_neg hij.not_gt, if_neg hij.ne']
  · intro i
    simp
  · intro i j hij
    rw [if_pos hij]
    apply Ideal.mul_mem_right
    have hpos : (j : ℕ) - (i : ℕ) ≠ 0 := by
      have : (i : ℕ) < (j : ℕ) := hij
      omega
    rw [pow_mul]
    exact Ideal.pow_mem_pow (Ideal.pow_mem_of_mem _ hp _ (Nat.pos_of_ne_zero hpos)) c
end

section

open scoped IntermediateField TensorProduct Matrix Pointwise NumberField Topology ContDiff NNReal ENNReal Polynomial DirectSum BigOperators InnerProductSpace Manifold

noncomputable def UpperTheory.Reformulated.B.IwahoriEntryBound.latK :
    (L : Type) → [inst : Field L] → [Valued L (WithZero (Multiplicative ℤ))] → (n : ℕ) → ℕ → Set (Fin n → L) :=
    fun (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (n k : ℕ) ↦
      {x : Fin n → L |
        ∀ (i : Fin n),
          if (↑i : ℕ) < k then (Valued.v : L → WithZero (Multiplicative ℤ)) (x i) ≤ (1 : WithZero (Multiplicative ℤ))
          else (Valued.v : L → WithZero (Multiplicative ℤ)) (x i) < (1 : WithZero (Multiplicative ℤ))}

noncomputable def UpperTheory.Reformulated.B.IwahoriEntryBound.IwGL :
    (L : Type) → [inst : Field L] → [Valued L (WithZero (Multiplicative ℤ))] → (n : ℕ) → Subgroup (GL (Fin n) L) :=
    fun (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (n : ℕ) ↦
      ⨅ (k : Fin (n + (1 : ℕ))),
        Subgroup.comap Matrix.GeneralLinearGroup.toLin.toMonoidHom
          (MulAction.stabilizer (LinearMap.GeneralLinearGroup L (Fin n → L)) (UpperTheory.Reformulated.B.IwahoriEntryBound.latK L n (↑k : ℕ)))

namespace UpperTheory.Reformulated.B.IwahoriEntryBound.Helpers

private lemma entry_bound {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}
    {h : GL (Fin n) L} (hh : h ∈ UpperTheory.Reformulated.B.IwahoriEntryBound.IwGL L n) (i j : Fin n) :
    (Valued.v ((h : Matrix (Fin n) (Fin n) L) i j) ≤ 1) ∧
    ((j : ℕ) < (i : ℕ) → Valued.v ((h : Matrix (Fin n) (Fin n) L) i j) < 1) := by
  classical
  have hk := (Subgroup.mem_iInf.mp hh) ⟨(j : ℕ) + 1, by omega⟩
  rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff] at hk
  have hx : (Pi.single j (1 : L) : Fin n → L) ∈ UpperTheory.Reformulated.B.IwahoriEntryBound.latK L n ((j : ℕ) + 1) := by
    intro t
    by_cases ht : t = j
    · subst ht
      simp
    · have : Pi.single (M := fun _ => L) j (1 : L) t = 0 := Pi.single_eq_of_ne ht _
      split_ifs <;> simp [this]
  have hy := Set.smul_mem_smul_set (a := (Matrix.GeneralLinearGroup.toLin.toMonoidHom h)) hx
  have hk' : Matrix.GeneralLinearGroup.toLin.toMonoidHom h • UpperTheory.Reformulated.B.IwahoriEntryBound.latK L n ((j : ℕ) + 1)
      = UpperTheory.Reformulated.B.IwahoriEntryBound.latK L n ((j : ℕ) + 1) := hk
  rw [hk'] at hy
  have key : (Matrix.GeneralLinearGroup.toLin.toMonoidHom h) • (Pi.single j (1 : L) : Fin n → L)
      = (h : Matrix (Fin n) (Fin n) L) *ᵥ Pi.single j 1 := by
    rfl
  rw [key] at hy
  have e : ((h : Matrix (Fin n) (Fin n) L) *ᵥ Pi.single j 1) i = (h : Matrix (Fin n) (Fin n) L) i j := by
    simp [Matrix.mulVec_single_one]
  have hi := hy i
  rw [e] at hi
  constructor
  · split_ifs at hi with hc
    · exact hi
    · exact hi.le
  · intro hlt
    rw [if_neg (by omega)] at hi
    exact hi

end UpperTheory.Reformulated.B.IwahoriEntryBound.Helpers

open UpperTheory.Reformulated.B.IwahoriEntryBound.Helpers in
theorem UpperTheory.Reformulated.B.IwahoriEntryBound.main :
    ∀ {L : Type} [inst : Field L] [inst_1 : Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} {g : GL (Fin n) L},
      g ∈ UpperTheory.Reformulated.B.IwahoriEntryBound.IwGL L n →
        ∀ (i : Fin n),
          (Valued.v : L → WithZero (Multiplicative ℤ)) ((↑g : Matrix (Fin n) (Fin n) L) i i) =
            (1 : WithZero (Multiplicative ℤ)) := by
  intro L _ _ n g hg i
  classical
  have hg' : g⁻¹ ∈ UpperTheory.Reformulated.B.IwahoriEntryBound.IwGL L n := inv_mem hg
  have hprod : ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (g : Matrix (Fin n) (Fin n) L) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hii := congrFun (congrFun hprod i) i
  rw [Matrix.mul_apply, Matrix.one_apply_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hii
  set a := ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i * (g : Matrix (Fin n) (Fin n) L) i i with ha
  have hrest : Valued.v (∑ j ∈ Finset.univ.erase i,
      ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j * (g : Matrix (Fin n) (Fin n) L) j i) < 1 := by
    apply Valuation.map_sum_lt _ one_ne_zero
    intro j hj
    have hne : j ≠ i := Finset.ne_of_mem_erase hj
    rw [Valuation.map_mul]
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
    ·
      have h1 := (entry_bound hg' i j).2 hlt
      have h2 := (entry_bound hg j i).1
      calc _ ≤ Valued.v (((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j) * 1 := by gcongr
        _ = _ := mul_one _
        _ < 1 := h1
    · have h1 := (entry_bound hg' i j).1
      have h2 := (entry_bound hg j i).2 hlt
      calc _ ≤ 1 * Valued.v ((g : Matrix (Fin n) (Fin n) L) j i) := by gcongr
        _ = _ := one_mul _
        _ < 1 := h2
  have hva : 1 ≤ Valued.v a := by
    by_contra hc
    push Not at hc
    have := Valuation.map_add_lt _ hc hrest
    rw [hii, Valuation.map_one] at this
    exact lt_irrefl _ this
  have hgi := (entry_bound hg i i).1
  have hinv := (entry_bound hg' i i).1
  apply le_antisymm hgi
  calc (1 : WithZero (Multiplicative ℤ)) ≤ Valued.v a := hva
    _ = _ := Valuation.map_mul _ _ _
    _ ≤ 1 * Valued.v ((g : Matrix (Fin n) (Fin n) L) i i) := by gcongr
    _ = _ := one_mul _
end
