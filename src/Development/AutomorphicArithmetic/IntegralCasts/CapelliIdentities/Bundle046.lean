module

public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Localization.Integral

@[expose] public section

section

universe u_1 u_3

namespace UpperTheory.Reformulated.B.AntidiagonalTranspose

noncomputable def Jmat (R : Type u_1) [CommRing R] (m : ℕ) : Matrix (Fin m) (Fin m) R :=
  fun i j ↦ if j = i.rev then (1 : R) else (0 : R)

theorem aux2 {R : Type u_1} [CommRing R] (m : ℕ) :
    Jmat R m * Jmat R m = (1 : Matrix (Fin m) (Fin m) R) := by
  ext i j
  simp only [Matrix.mul_apply, Jmat, Matrix.one_apply]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, Fin.rev_rev]
  by_cases h : i = j
  · simp [h]
  · simp [h, Ne.symm h]

noncomputable def Jgl (R : Type u_1) [CommRing R] (m : ℕ) : GL (Fin m) R :=
  { val := Jmat R m, inv := Jmat R m, val_inv := aux2 m, inv_val := aux2 m :
    (Matrix (Fin m) (Fin m) R)ˣ }

theorem aux4 {n : Type} [Fintype n] [DecidableEq n] {R : Type u_1} [CommRing R] (g : GL n R) :
    (↑g⁻¹ : Matrix n n R).transpose * (↑g : Matrix n n R).transpose = (1 : Matrix n n R) := by
  rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]

theorem aux5 {n : Type} [Fintype n] [DecidableEq n] {R : Type u_1} [CommRing R] (g : GL n R) :
    (↑g : Matrix n n R).transpose * (↑g⁻¹ : Matrix n n R).transpose = (1 : Matrix n n R) := by
  rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]

noncomputable def trInv {n : Type} [Fintype n] [DecidableEq n] {R : Type u_1} [CommRing R]
    (g : GL n R) : GL n R :=
  { val := (↑g⁻¹ : Matrix n n R).transpose, inv := (↑g : Matrix n n R).transpose,
    val_inv := aux4 g, inv_val := aux5 g : (Matrix n n R)ˣ }

noncomputable def theta {m : ℕ} {R : Type u_1} [CommRing R] (g : GL (Fin m) R) : GL (Fin m) R :=
  Jgl R m * trInv g * Jgl R m

private theorem Jmat_transpose {R : Type u_1} [CommRing R] (m : ℕ) :
    (Jmat R m).transpose = Jmat R m := by
  ext i j
  simp only [Matrix.transpose_apply, Jmat]
  have : (i = j.rev) ↔ (j = i.rev) := by
    constructor
    · rintro rfl; simp
    · rintro rfl; simp
  simp [this]

private theorem Jgl_mul_self {R : Type u_1} [CommRing R] (m : ℕ) : Jgl R m * Jgl R m = 1 :=
  Units.ext (aux2 m)

private theorem Jgl_inv {R : Type u_1} [CommRing R] (m : ℕ) : (Jgl R m)⁻¹ = Jgl R m :=
  inv_eq_of_mul_eq_one_left (Jgl_mul_self m)

private theorem trInv_mul {n : Type} [Fintype n] [DecidableEq n] {R : Type u_1} [CommRing R]
    (g h : GL n R) : trInv (g * h) = trInv g * trInv h := by
  apply Units.ext
  change (((g * h)⁻¹ : GL n R) : Matrix n n R).transpose =
    (↑g⁻¹ : Matrix n n R).transpose * (↑h⁻¹ : Matrix n n R).transpose
  rw [mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

private theorem trInv_trInv {n : Type} [Fintype n] [DecidableEq n] {R : Type u_1} [CommRing R]
    (g : GL n R) : trInv (trInv g) = g := by
  apply Units.ext
  change (↑(trInv g)⁻¹ : Matrix n n R).transpose = ↑g
  change ((↑g : Matrix n n R).transpose).transpose = ↑g
  exact Matrix.transpose_transpose _

private theorem trInv_Jgl {R : Type u_1} [CommRing R] (m : ℕ) : trInv (Jgl R m) = Jgl R m := by
  apply Units.ext
  change (((Jgl R m)⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R).transpose = Jmat R m
  rw [Jgl_inv]
  exact Jmat_transpose m

theorem aux8 {m : ℕ} {R : Type u_1} [CommRing R] (g : GL (Fin m) R) : theta (theta g) = g := by
  have hJ := Jgl_mul_self (R := R) m
  simp only [theta, trInv_mul, trInv_trInv, trInv_Jgl]
  calc _ = (Jgl R m * Jgl R m) * g * (Jgl R m * Jgl R m) * (Jgl R m * Jgl R m) := by
        simp only [hJ, mul_one, one_mul]
        simp only [mul_assoc, hJ, mul_one]
        simp only [← mul_assoc, hJ, one_mul]
    _ = g := by simp [hJ]

theorem aux9 {m : ℕ} {R : Type u_1} [CommRing R] (g h : GL (Fin m) R) :
    theta (g * h) = theta g * theta h := by
  have hJ := Jgl_mul_self (R := R) m
  simp only [theta, trInv_mul]
  calc _ = Jgl R m * trInv g * 1 * trInv h * Jgl R m := by simp only [mul_one, mul_assoc]
    _ = _ := by rw [← hJ]; simp only [mul_assoc]

noncomputable def thetaAut (m : ℕ) (R : Type u_1) [CommRing R] : MulAut (GL (Fin m) R) :=
  { toFun := theta, invFun := theta, left_inv := aux8, right_inv := aux8, map_mul' := aux9 :
    GL (Fin m) R ≃* GL (Fin m) R }

private theorem thetaAut_sq (m : ℕ) (R : Type u_1) [CommRing R] :
    thetaAut m R * thetaAut m R = 1 := by
  ext1 g
  exact aux8 g

theorem aux11 (m : ℕ) (R : Type u_1) [CommRing R] :
    (if (1 : ℤˣ) = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else thetaAut m R) =
      (1 : MulAut (GL (Fin m) R)) :=
  if_pos rfl

theorem aux12 (m : ℕ) (R : Type u_1) [CommRing R] (s t : ℤˣ) :
    (if s * t = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else thetaAut m R) =
      (if s = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else thetaAut m R) *
        if t = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else thetaAut m R := by
  rcases Int.units_eq_one_or s with rfl | rfl <;> rcases Int.units_eq_one_or t with rfl | rfl
  · simp
  · simp
  · simp
  · simp [thetaAut_sq]

noncomputable def sgnAct (m : ℕ) (R : Type u_1) [CommRing R] : ℤˣ →* MulAut (GL (Fin m) R) :=
  { toFun := fun (s : ℤˣ) ↦ if s = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else thetaAut m R,
    map_one' := aux11 m R, map_mul' := aux12 m R : ℤˣ →* MulAut (GL (Fin m) R) }

@[reducible] noncomputable def GG (m : ℕ) (R : Type u_1) [CommRing R] : Type u_1 :=
  GL (Fin m) R ⋊[sgnAct m R] ℤˣ

@[reducible] noncomputable def ofGL {m : ℕ} {R : Type u_1} [CommRing R] : GL (Fin m) R →* GG m R :=
  SemidirectProduct.inl

noncomputable def conjBy {m : ℕ} {R : Type u_1} [CommRing R] {G : Type u_3} [Group G]
    (h : GL (Fin m) R) (r : G →* GG m R) : G →* GG m R :=
  (MulAut.conj (ofGL h : GG m R)).toMonoidHom.comp r

theorem conj_right {G R : Type} [Group G] [CommRing R] {m : ℕ} (h : GL (Fin m) R)
    (r : G →* GG m R) (g : G) : (conjBy h r g).right = (r g).right := by
  simp [conjBy, MulAut.conj_apply]

end UpperTheory.Reformulated.B.AntidiagonalTranspose
end

section

universe u_1 u_3

namespace UpperTheory.Reformulated.B.ThetaInvolution

noncomputable def Jmat (R : Type u_1) [CommRing R] (m : ℕ) : Matrix (Fin m) (Fin m) R :=
  fun i j ↦ if j = i.rev then (1 : R) else (0 : R)

theorem aux2 {R : Type u_1} [CommRing R] (m : ℕ) :
    Jmat R m * Jmat R m = (1 : Matrix (Fin m) (Fin m) R) := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single i.rev]
  · simp only [Jmat, Matrix.one_apply, if_true, one_mul, Fin.rev_rev]
    by_cases h : i = j
    · subst h; simp
    · rw [if_neg (fun e => h e.symm), if_neg h]
  · intro k _ hk
    simp [Jmat, hk]
  · intro h; exact absurd (Finset.mem_univ _) h

noncomputable def Jgl (R : Type u_1) [CommRing R] (m : ℕ) : GL (Fin m) R :=
  { val := Jmat R m, inv := Jmat R m, val_inv := aux2 m, inv_val := aux2 m :
    (Matrix (Fin m) (Fin m) R)ˣ }

theorem aux4 {n : Type} [Fintype n] [DecidableEq n] {R : Type u_1} [CommRing R] (g : GL n R) :
    (↑g⁻¹ : Matrix n n R).transpose * (↑g : Matrix n n R).transpose = (1 : Matrix n n R) := by
  rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one]

theorem aux5 {n : Type} [Fintype n] [DecidableEq n] {R : Type u_1} [CommRing R] (g : GL n R) :
    (↑g : Matrix n n R).transpose * (↑g⁻¹ : Matrix n n R).transpose = (1 : Matrix n n R) := by
  rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one]

noncomputable def trInv {n : Type} [Fintype n] [DecidableEq n] {R : Type u_1} [CommRing R]
    (g : GL n R) : GL n R :=
  { val := (↑g⁻¹ : Matrix n n R).transpose, inv := (↑g : Matrix n n R).transpose,
    val_inv := aux4 g, inv_val := aux5 g : (Matrix n n R)ˣ }

noncomputable def theta {m : ℕ} {R : Type u_1} [CommRing R] (g : GL (Fin m) R) : GL (Fin m) R :=
  Jgl R m * trInv g * Jgl R m

private theorem Jgl_mul_self (R : Type u_1) [CommRing R] (m : ℕ) : Jgl R m * Jgl R m = 1 :=
  Units.ext (aux2 m)

private theorem trInv_mul {n : Type} [Fintype n] [DecidableEq n] {R : Type u_1} [CommRing R]
    (g h : GL n R) : trInv (g * h) = trInv g * trInv h := by
  apply Units.ext
  change (((g * h)⁻¹ : GL n R) : Matrix n n R).transpose =
    ((g⁻¹ : GL n R) : Matrix n n R).transpose * ((h⁻¹ : GL n R) : Matrix n n R).transpose
  rw [mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

private theorem trInv_trInv {n : Type} [Fintype n] [DecidableEq n] {R : Type u_1} [CommRing R]
    (g : GL n R) : trInv (trInv g) = g := by
  apply Units.ext
  change (g : Matrix n n R).transpose.transpose = (g : Matrix n n R)
  exact Matrix.transpose_transpose _

private theorem trInv_Jgl (R : Type u_1) [CommRing R] (m : ℕ) : trInv (Jgl R m) = Jgl R m := by
  apply Units.ext
  change (Jmat R m).transpose = Jmat R m
  ext i j
  simp only [Matrix.transpose_apply, Jmat]
  by_cases h : j = i.rev
  · rw [if_pos h, if_pos (by rw [h, Fin.rev_rev])]
  · rw [if_neg h, if_neg (fun e => h (by rw [e, Fin.rev_rev]))]

theorem aux8 {m : ℕ} {R : Type u_1} [CommRing R] (g : GL (Fin m) R) : theta (theta g) = g := by
  have hJ := Jgl_mul_self R m
  simp only [theta, trInv_mul, trInv_trInv, trInv_Jgl]
  calc _ = (Jgl R m * Jgl R m) * g * (Jgl R m * Jgl R m) := by simp only [mul_assoc]
    _ = g := by rw [hJ, one_mul, mul_one]

theorem aux9 {m : ℕ} {R : Type u_1} [CommRing R] (g h : GL (Fin m) R) :
    theta (g * h) = theta g * theta h := by
  have hJ := Jgl_mul_self R m
  simp only [theta, trInv_mul]
  calc _ = Jgl R m * trInv g * 1 * trInv h * Jgl R m := by rw [mul_one]; simp only [mul_assoc]
    _ = _ := by rw [← hJ]; simp only [mul_assoc]

noncomputable def thetaAut (m : ℕ) (R : Type u_1) [CommRing R] : MulAut (GL (Fin m) R) :=
  { toFun := theta, invFun := theta, left_inv := aux8, right_inv := aux8, map_mul' := aux9 :
    GL (Fin m) R ≃* GL (Fin m) R }

theorem aux11 (m : ℕ) (R : Type u_1) [CommRing R] :
    (if (1 : ℤˣ) = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else thetaAut m R) =
      (1 : MulAut (GL (Fin m) R)) :=
  if_pos rfl

private theorem thetaAut_mul_self (m : ℕ) (R : Type u_1) [CommRing R] :
    thetaAut m R * thetaAut m R = 1 :=
  MulEquiv.ext (fun g => aux8 g)

theorem aux12 (m : ℕ) (R : Type u_1) [CommRing R] (s t : ℤˣ) :
    (if s * t = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else thetaAut m R) =
      (if s = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else thetaAut m R) *
        if t = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else thetaAut m R := by
  have hn : (-1 : ℤˣ) ≠ 1 := by decide
  rcases Int.units_eq_one_or s with rfl | rfl <;> rcases Int.units_eq_one_or t with rfl | rfl
  · simp
  · simp [hn]
  · simp [hn]
  · simp [hn, thetaAut_mul_self]

noncomputable def sgnAct (m : ℕ) (R : Type u_1) [CommRing R] : ℤˣ →* MulAut (GL (Fin m) R) :=
  { toFun := fun (s : ℤˣ) ↦ if s = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else thetaAut m R,
    map_one' := aux11 m R, map_mul' := aux12 m R : ℤˣ →* MulAut (GL (Fin m) R) }

@[reducible] noncomputable def GG (m : ℕ) (R : Type u_1) [CommRing R] : Type u_1 :=
  GL (Fin m) R ⋊[sgnAct m R] ℤˣ

@[reducible] noncomputable def ofGL {m : ℕ} {R : Type u_1} [CommRing R] : GL (Fin m) R →* GG m R :=
  SemidirectProduct.inl

noncomputable def conjBy {m : ℕ} {R : Type u_1} [CommRing R] {G : Type u_3} [Group G]
    (h : GL (Fin m) R) (r : G →* GG m R) : G →* GG m R :=
  (MulAut.conj (ofGL h : GG m R)).toMonoidHom.comp r

theorem conjBy_conjBy {C D : Type} [CommRing C] [Group D] (h h' : GL (Fin (3 : ℕ)) C)
    (r : D →* GG (3 : ℕ) C) : conjBy (h * h')⁻¹ (conjBy h r) = conjBy h'⁻¹ r := by
  ext1 x
  have e1 : (ofGL (h * h')⁻¹ : GG 3 C) = (ofGL h * ofGL h')⁻¹ := by rw [map_inv, map_mul]
  have e2 : (ofGL h'⁻¹ : GG 3 C) = (ofGL h')⁻¹ := map_inv _ _
  change MulAut.conj (ofGL (h * h')⁻¹) (MulAut.conj (ofGL h) (r x)) = MulAut.conj (ofGL h'⁻¹) (r x)
  rw [e1, e2]
  generalize (ofGL h : GG 3 C) = a
  generalize (ofGL h' : GG 3 C) = b
  generalize r x = y
  simp only [MulAut.conj_apply]
  group

end UpperTheory.Reformulated.B.ThetaInvolution
end

section

theorem UpperTheory.Reformulated.B.Ud9.exists_indep_of_sat :
    ∀ {R E : Type} [inst : CommRing R] [IsDomain R] [IsNoetherianRing R]
    [inst_3 : AddCommGroup E] [inst_4 : _root_.Module R E] [Module.Finite R E] [Module.IsTorsionFree R E] (T : Set E)
    (F : Submodule R E),
    (∀ (x : E), x ∈ F ↔ ∃ (a : R), a ≠ (0 : R) ∧ a • x ∈ Submodule.span R T) →
      ∃ (f : Fin (Module.finrank R ↥F) → E), (∀ (j : Fin (Module.finrank R ↥F)), f j ∈ T) ∧ LinearIndependent R f := by
  intro R E _ _ _ _ _ _ _ T F hF
  obtain ⟨I, hI, hmax⟩ := exists_maximal_linearIndepOn R (Subtype.val : T → E)
  set S : Submodule R E := Submodule.span R ((Subtype.val : T → E) '' I) with hS
  have hT : ∀ y ∈ Submodule.span R T, ∃ b : R, b ≠ 0 ∧ b • y ∈ S := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      by_cases h : (⟨x, hx⟩ : T) ∈ I
      · exact ⟨1, one_ne_zero, by
          rw [one_smul]; exact Submodule.subset_span ⟨⟨x, hx⟩, h, rfl⟩⟩
      · exact hmax ⟨x, hx⟩ h
    | zero => exact ⟨1, one_ne_zero, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, hax⟩ := hx
      obtain ⟨b, hb, hby⟩ := hy
      refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
      rw [smul_add]
      refine S.add_mem ?_ ?_
      · rw [mul_comm, mul_smul]; exact S.smul_mem _ hax
      · rw [mul_smul]; exact S.smul_mem _ hby
    | smul c x _ hx =>
      obtain ⟨a, ha, hax⟩ := hx
      refine ⟨a, ha, ?_⟩
      rw [smul_comm]; exact S.smul_mem _ hax
  let N : Submodule R F := S.comap F.subtype
  have h0 : Module.rank R (F ⧸ N) = 0 := by
    rw [rank_eq_zero_iff]
    intro q
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective N q
    obtain ⟨a, ha, hax⟩ := (hF x).1 x.2
    obtain ⟨b, hb, hbx⟩ := hT _ hax
    refine ⟨b * a, mul_ne_zero hb ha, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    change (b * a) • (x : E) ∈ S
    rwa [mul_smul]
  have h1 : Module.rank R F = Module.rank R N := by
    rw [← rank_quotient_add_rank_of_isDomain N, h0, zero_add]
  have h2 : Module.rank R N ≤ Module.rank R S := by
    let g : N →ₗ[R] S := (F.subtype.comp N.subtype).codRestrict S (fun x => x.2)
    refine LinearMap.rank_le_of_injective g ?_
    intro x y hxy
    have h : ((g x : S) : E) = ((g y : S) : E) := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext h)
  have h3 : Module.rank R S ≤ Cardinal.mk I :=
    (rank_span_le _).trans Cardinal.mk_image_le
  have h4 : Cardinal.mk (Fin (Module.finrank R F)) ≤ Cardinal.mk I := by
    rw [Cardinal.mk_fin, Module.finrank_eq_rank, h1]
    exact h2.trans h3
  obtain ⟨e⟩ := (Cardinal.le_def _ _).1 h4
  exact ⟨fun j => ((e j : T) : E), fun j => (e j : T).2, LinearIndependent.comp hI e e.injective⟩
end

section

theorem UpperTheory.Reformulated.B.InterpolationPointsOfFinrankBound.pick :
    ∀ {k D : Type} [inst : Field k] (P : Set D) {p0 : D},
    p0 ∈ P →
      ∀ (W : Submodule k (D → k)),
        (∀ (f : D → k), f ∈ W ↔ ∀ p ∈ P, f p = (0 : k)) →
          ∀ (n : ℕ) (Y : Submodule k (D → k)) [FiniteDimensional k ↥Y],
            Module.finrank k ↥Y ≤ n + Module.finrank k ↥(Y ⊓ W) →
              ∃ (u : Fin n → D), (∀ (a : Fin n), u a ∈ P) ∧ ∀ f ∈ Y, (∀ (a : Fin n), f (u a) = (0 : k)) → f ∈ W := by
  intro k D _ P p0 hp0 W hW n
  induction n with
  | zero =>
    intro Y _ h
    refine ⟨fun _ => p0, fun _ => hp0, fun f hf _ => ?_⟩
    have heq : Y ⊓ W = Y :=
      Submodule.eq_of_le_of_finrank_le inf_le_left (by simpa using h)
    rw [← heq] at hf
    exact hf.2
  | succ n ih =>
    intro Y _ h
    by_cases hYW : Y ≤ W
    · exact ⟨fun _ => p0, fun _ => hp0, fun f hf _ => hYW hf⟩
    · obtain ⟨g, hgY, hgW⟩ := SetLike.not_le_iff_exists.mp hYW
      rw [hW] at hgW
      simp only [not_forall] at hgW
      obtain ⟨p, hp, hgp⟩ := hgW
      let K : Submodule k (D → k) := LinearMap.ker (LinearMap.proj p : (D → k) →ₗ[k] k)
      have hK : ∀ f : D → k, f ∈ K ↔ f p = 0 := fun f => LinearMap.mem_ker
      have hWK : W ≤ K := fun f hf => (hK f).2 ((hW f).1 hf p hp)
      haveI : FiniteDimensional k ↥(Y ⊓ K) := Submodule.finiteDimensional_of_le inf_le_left
      have hlt : Y ⊓ K < Y := by
        refine lt_of_le_of_ne inf_le_left fun he => hgp ?_
        rw [← he] at hgY
        exact (hK g).1 hgY.2
      have hrank := Submodule.finrank_lt_finrank_of_lt hlt
      have hinf : (Y ⊓ K) ⊓ W = Y ⊓ W := by
        rw [inf_assoc, inf_eq_right.2 hWK]
      obtain ⟨u, hu, hu'⟩ := ih (Y ⊓ K) (by rw [hinf]; omega)
      refine ⟨Fin.cons p u, fun a => ?_, fun f hf hz => ?_⟩
      · refine Fin.cases ?_ (fun i => ?_) a
        · simpa using hp
        · simpa using hu i
      · refine hu' f ⟨hf, (hK f).2 ?_⟩ fun a => ?_
        · simpa using hz 0
        · simpa using hz a.succ
end

section

private theorem UpperTheory.pow_mul_isIntegral {l : ℕ} [Fact l.Prime] {K : Type} [Field K]
    [Algebra ℚ_[l] K] [Algebra ℤ_[l] K] [IsScalarTower ℤ_[l] ℚ_[l] K]
    [FiniteDimensional ℚ_[l] K] (c : K) :
    ∃ n : ℕ, IsIntegral ℤ_[l] ((l : K) ^ n * c) := by
  have h1 : IsAlgebraic ℚ_[l] c := Algebra.IsAlgebraic.isAlgebraic c
  have h2 : IsAlgebraic ℤ_[l] c :=
    (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] K).mpr h1
  obtain ⟨y, hy, hint⟩ := h2.exists_integral_multiple
  refine ⟨y.valuation, ?_⟩
  have hspec := PadicInt.unitCoeff_spec hy
  set u := PadicInt.unitCoeff hy
  have h3 : ((l : ℤ_[l]) ^ y.valuation) = (↑u⁻¹ : ℤ_[l]) * y := by
    rw [Units.eq_inv_mul_iff_mul_eq]
    exact hspec.symm
  have h4 : (l : K) ^ y.valuation * c = (↑u⁻¹ : ℤ_[l]) • (y • c) := by
    rw [← mul_smul, ← h3, Algebra.smul_def, map_pow, map_natCast]
  rw [h4]
  exact hint.smul _

theorem UpperTheory.exists_pow_smul_mem_alt :
    ∀ {l : ℕ} [Fact l.Prime] {K : Type} [Field K] [Algebra ℚ_[l] K] [Algebra ℤ_[l] K] [IsScalarTower ℤ_[l] ℚ_[l] K] [FiniteDimensional ℚ_[l] K] {O : Type} [CommRing O] [Algebra O K] {V : Type} [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] (T : Submodule O V), (∀ c : K, IsIntegral ℤ_[l] c → ∃ o : O, algebraMap O K o = c) → Submodule.span K (T : Set V) = ⊤ → ∀ v : V, ∃ n : ℕ, (l : K) ^ n • v ∈ T := by
  intro l _ K _ _ _ _ _ O _ _ V _ _ _ _ T hO hT v
  have hpow : ∀ (m : ℕ) (w : V), w ∈ T → (l : K) ^ m • w ∈ T := by
    intro m w hw
    have h : (l : K) ^ m = algebraMap O K ((l : O) ^ m) := by
      rw [map_pow, map_natCast]
    rw [h, algebraMap_smul]
    exact T.smul_mem _ hw
  have hv : v ∈ Submodule.span K (T : Set V) := hT ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨0, by simpa using hx⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a + b, ?_⟩
    rw [smul_add]
    refine T.add_mem ?_ ?_
    · rw [add_comm, pow_add, mul_smul]
      exact hpow _ _ ha
    · rw [pow_add, mul_smul]
      exact hpow _ _ hb
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨n, hn⟩ := UpperTheory.pow_mul_isIntegral (l := l) c
    obtain ⟨o, ho⟩ := hO _ hn
    refine ⟨n + a, ?_⟩
    have h : (l : K) ^ (n + a) • c • x = o • ((l : K) ^ a • x) := by
      rw [← algebraMap_smul K o, ho, smul_smul, smul_smul]
      congr 1
      ring
    rw [h]
    exact T.smul_mem _ ha
end
