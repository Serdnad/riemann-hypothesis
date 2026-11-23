module

public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.LinearAlgebra.Matrix.Block
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

section

noncomputable def UpperTheory.Reformulated.B.SignActionTheta.Jmat.{u_1} :
    (R : Type u_1) → [CommRing R] → (m : ℕ) → Matrix (Fin m) (Fin m) R :=
    fun (R : Type u_1) [CommRing R] (m : ℕ) (i j : Fin m) ↦ if j = i.rev then (1 : R) else (0 : R)

theorem UpperTheory.Reformulated.B.SignActionTheta.aux2.{u_1} :
    ∀ {R : Type u_1} [inst : CommRing R] (m : ℕ),
      UpperTheory.Reformulated.B.SignActionTheta.Jmat R m * UpperTheory.Reformulated.B.SignActionTheta.Jmat R m = (1 : Matrix (Fin m) (Fin m) R) := by
  intro R _ m
  ext i j
  simp only [UpperTheory.Reformulated.B.SignActionTheta.Jmat, Matrix.mul_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Fin.rev_rev, Matrix.one_apply]
  simp only [eq_comm]

noncomputable def UpperTheory.Reformulated.B.SignActionTheta.Jgl.{u_1} :
    (R : Type u_1) → [inst : CommRing R] → (m : ℕ) → GL (Fin m) R :=
    fun (R : Type u_1) [CommRing R] (m : ℕ) ↦
      { val := UpperTheory.Reformulated.B.SignActionTheta.Jmat R m, inv := UpperTheory.Reformulated.B.SignActionTheta.Jmat R m, val_inv := UpperTheory.Reformulated.B.SignActionTheta.aux2 m,
        inv_val := UpperTheory.Reformulated.B.SignActionTheta.aux2 m : (Matrix (Fin m) (Fin m) R)ˣ }

theorem UpperTheory.Reformulated.B.SignActionTheta.aux4.{u_1} :
    ∀ {n : Type} [inst : Fintype n] [inst_1 : DecidableEq n] {R : Type u_1} [inst_2 : CommRing R] (g : GL n R),
      (↑g⁻¹ : Matrix n n R).transpose * (↑g : Matrix n n R).transpose = (1 : Matrix n n R) := by
  intro n _ _ R _ g
  rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]

theorem UpperTheory.Reformulated.B.SignActionTheta.aux5.{u_1} :
    ∀ {n : Type} [inst : Fintype n] [inst_1 : DecidableEq n] {R : Type u_1} [inst_2 : CommRing R] (g : GL n R),
      (↑g : Matrix n n R).transpose * (↑g⁻¹ : Matrix n n R).transpose = (1 : Matrix n n R) := by
  intro n _ _ R _ g
  rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]

noncomputable def UpperTheory.Reformulated.B.SignActionTheta.trInv.{u_1} :
    {n : Type} → [inst : Fintype n] → [inst_1 : DecidableEq n] → {R : Type u_1} → [inst_2 : CommRing R] → GL n R → GL n R :=
    fun {n : Type} [Fintype n] [DecidableEq n] {R : Type u_1} [CommRing R] (g : GL n R) ↦
      { val := (↑g⁻¹ : Matrix n n R).transpose, inv := (↑g : Matrix n n R).transpose, val_inv := UpperTheory.Reformulated.B.SignActionTheta.aux4 g,
        inv_val := UpperTheory.Reformulated.B.SignActionTheta.aux5 g : (Matrix n n R)ˣ }

noncomputable def UpperTheory.Reformulated.B.SignActionTheta.theta.{u_1} :
    {m : ℕ} → {R : Type u_1} → [inst : CommRing R] → GL (Fin m) R → GL (Fin m) R :=
    fun {m : ℕ} {R : Type u_1} [CommRing R] (g : GL (Fin m) R) ↦
      UpperTheory.Reformulated.B.SignActionTheta.Jgl R m * UpperTheory.Reformulated.B.SignActionTheta.trInv g * UpperTheory.Reformulated.B.SignActionTheta.Jgl R m

private theorem UpperTheory.Reformulated.B.SignActionTheta.J_mul_J {m : ℕ} {R : Type*} [CommRing R] :
    UpperTheory.Reformulated.B.SignActionTheta.Jgl R m * UpperTheory.Reformulated.B.SignActionTheta.Jgl R m = 1 :=
  Units.ext (UpperTheory.Reformulated.B.SignActionTheta.aux2 m)

private theorem UpperTheory.Reformulated.B.SignActionTheta.trInv_mul {n : Type} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    (g h : GL n R) :
    UpperTheory.Reformulated.B.SignActionTheta.trInv (g * h) = UpperTheory.Reformulated.B.SignActionTheta.trInv g * UpperTheory.Reformulated.B.SignActionTheta.trInv h := by
  apply Units.ext
  change (↑(g * h)⁻¹ : Matrix n n R).transpose =
    (↑g⁻¹ : Matrix n n R).transpose * (↑h⁻¹ : Matrix n n R).transpose
  rw [mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

private theorem UpperTheory.Reformulated.B.SignActionTheta.trInv_trInv {n : Type} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    (g : GL n R) : UpperTheory.Reformulated.B.SignActionTheta.trInv (UpperTheory.Reformulated.B.SignActionTheta.trInv g) = g :=
  Units.ext (Matrix.transpose_transpose (↑g : Matrix n n R))

private theorem UpperTheory.Reformulated.B.SignActionTheta.trInv_J {m : ℕ} {R : Type*} [CommRing R] :
    UpperTheory.Reformulated.B.SignActionTheta.trInv (UpperTheory.Reformulated.B.SignActionTheta.Jgl R m) = UpperTheory.Reformulated.B.SignActionTheta.Jgl R m := by
  apply Units.ext
  change (UpperTheory.Reformulated.B.SignActionTheta.Jmat R m).transpose = UpperTheory.Reformulated.B.SignActionTheta.Jmat R m
  ext i j
  simp only [Matrix.transpose_apply, UpperTheory.Reformulated.B.SignActionTheta.Jmat]
  refine if_congr ⟨fun h => ?_, fun h => ?_⟩ rfl rfl <;> rw [h, Fin.rev_rev]

theorem UpperTheory.Reformulated.B.SignActionTheta.aux8.{u_1} :
    ∀ {m : ℕ} {R : Type u_1} [inst : CommRing R] (g : GL (Fin m) R), UpperTheory.Reformulated.B.SignActionTheta.theta (UpperTheory.Reformulated.B.SignActionTheta.theta g) = g := by
  intro m R _ g
  unfold UpperTheory.Reformulated.B.SignActionTheta.theta
  rw [UpperTheory.Reformulated.B.SignActionTheta.trInv_mul, UpperTheory.Reformulated.B.SignActionTheta.trInv_mul, UpperTheory.Reformulated.B.SignActionTheta.trInv_trInv,
    UpperTheory.Reformulated.B.SignActionTheta.trInv_J]
  simp only [← mul_assoc]
  rw [UpperTheory.Reformulated.B.SignActionTheta.J_mul_J, one_mul, mul_assoc, UpperTheory.Reformulated.B.SignActionTheta.J_mul_J, mul_one]

theorem UpperTheory.Reformulated.B.SignActionTheta.aux9.{u_1} :
    ∀ {m : ℕ} {R : Type u_1} [inst : CommRing R] (g h : GL (Fin m) R),
      UpperTheory.Reformulated.B.SignActionTheta.theta (g * h) = UpperTheory.Reformulated.B.SignActionTheta.theta g * UpperTheory.Reformulated.B.SignActionTheta.theta h := by
  intro m R _ g h
  unfold UpperTheory.Reformulated.B.SignActionTheta.theta
  rw [UpperTheory.Reformulated.B.SignActionTheta.trInv_mul]
  simp only [mul_assoc]
  rw [← mul_assoc (UpperTheory.Reformulated.B.SignActionTheta.Jgl R m) (UpperTheory.Reformulated.B.SignActionTheta.Jgl R m) (UpperTheory.Reformulated.B.SignActionTheta.trInv h * _),
    UpperTheory.Reformulated.B.SignActionTheta.J_mul_J, one_mul]

noncomputable def UpperTheory.Reformulated.B.SignActionTheta.thetaAut.{u_1} :
    (m : ℕ) → (R : Type u_1) → [inst : CommRing R] → MulAut (GL (Fin m) R) :=
    fun (m : ℕ) (R : Type u_1) [CommRing R] ↦
      { toFun := UpperTheory.Reformulated.B.SignActionTheta.theta, invFun := UpperTheory.Reformulated.B.SignActionTheta.theta, left_inv := UpperTheory.Reformulated.B.SignActionTheta.aux8,
        right_inv := UpperTheory.Reformulated.B.SignActionTheta.aux8, map_mul' := UpperTheory.Reformulated.B.SignActionTheta.aux9 : GL (Fin m) R ≃* GL (Fin m) R }

theorem UpperTheory.Reformulated.B.SignActionTheta.aux11.{u_1} :
    ∀ (m : ℕ) (R : Type u_1) [inst : CommRing R],
      (if (1 : ℤˣ) = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.SignActionTheta.thetaAut m R) =
        (1 : MulAut (GL (Fin m) R)) := by
  intro m R _
  exact if_pos rfl

theorem UpperTheory.Reformulated.B.SignActionTheta.aux12.{u_1} :
    ∀ (m : ℕ) (R : Type u_1) [inst : CommRing R] (s t : ℤˣ),
      (if s * t = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.SignActionTheta.thetaAut m R) =
        (if s = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.SignActionTheta.thetaAut m R) *
          if t = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.SignActionTheta.thetaAut m R := by
  intro m R _ s t
  have hne : (-1 : ℤˣ) ≠ 1 := by decide
  rcases Int.units_eq_one_or s with rfl | rfl <;> rcases Int.units_eq_one_or t with rfl | rfl
  · simp
  · simp
  · simp
  · rw [if_pos (by simp), if_neg hne]
    ext1 g
    exact (UpperTheory.Reformulated.B.SignActionTheta.aux8 g).symm

noncomputable def UpperTheory.Reformulated.B.SignActionTheta.sgnAct.{u_1} :
    (m : ℕ) → (R : Type u_1) → [inst : CommRing R] → ℤˣ →* MulAut (GL (Fin m) R) :=
    fun (m : ℕ) (R : Type u_1) [CommRing R] ↦
      { toFun := fun (s : ℤˣ) ↦ if s = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.SignActionTheta.thetaAut m R,
        map_one' := UpperTheory.Reformulated.B.SignActionTheta.aux11 m R, map_mul' := UpperTheory.Reformulated.B.SignActionTheta.aux12 m R : ℤˣ →* MulAut (GL (Fin m) R) }

@[reducible] noncomputable def UpperTheory.Reformulated.B.SignActionTheta.GG.{u_1} :
    ℕ → (R : Type u_1) → [CommRing R] → Type u_1 :=
    fun (m : ℕ) (R : Type u_1) [CommRing R] ↦ GL (Fin m) R ⋊[UpperTheory.Reformulated.B.SignActionTheta.sgnAct m R] ℤˣ

private theorem UpperTheory.Reformulated.B.SignActionTheta.map_theta {m : ℕ} {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (g : GL (Fin m) R) :
    Matrix.GeneralLinearGroup.map f (UpperTheory.Reformulated.B.SignActionTheta.theta g) =
      UpperTheory.Reformulated.B.SignActionTheta.theta (Matrix.GeneralLinearGroup.map f g) := by
  have hJ : Matrix.GeneralLinearGroup.map f (UpperTheory.Reformulated.B.SignActionTheta.Jgl R m) = UpperTheory.Reformulated.B.SignActionTheta.Jgl S m := by
    ext i j
    change f (UpperTheory.Reformulated.B.SignActionTheta.Jmat R m i j) = UpperTheory.Reformulated.B.SignActionTheta.Jmat S m i j
    unfold UpperTheory.Reformulated.B.SignActionTheta.Jmat
    split_ifs <;> simp
  have hT : Matrix.GeneralLinearGroup.map f (UpperTheory.Reformulated.B.SignActionTheta.trInv g) =
      UpperTheory.Reformulated.B.SignActionTheta.trInv (Matrix.GeneralLinearGroup.map f g) := by
    ext i j
    rfl
  unfold UpperTheory.Reformulated.B.SignActionTheta.theta
  rw [map_mul, map_mul, hJ, hT]

theorem UpperTheory.Reformulated.B.SignActionTheta.sign_action_map_comm.{u_1, u_2} :
    ∀ {m : ℕ} {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] (f : R →+* S) (s : ℤˣ),
      (Matrix.GeneralLinearGroup.map f).comp
          (MulEquiv.toMonoidHom ((UpperTheory.Reformulated.B.SignActionTheta.sgnAct m R : ℤˣ → MulAut (GL (Fin m) R)) s)) =
        (MulEquiv.toMonoidHom
              ((UpperTheory.Reformulated.B.SignActionTheta.sgnAct m S : ℤˣ → MulAut (GL (Fin m) S)) ((MonoidHom.id ℤˣ : ℤˣ → ℤˣ) s))).comp
          (Matrix.GeneralLinearGroup.map f) := by
  intro m R S _ _ f s
  have hne : (-1 : ℤˣ) ≠ 1 := by decide
  rcases Int.units_eq_one_or s with rfl | rfl
  · ext1 g
    simp
  · have h1 : UpperTheory.Reformulated.B.SignActionTheta.sgnAct m R (-1) = UpperTheory.Reformulated.B.SignActionTheta.thetaAut m R :=
      if_neg (t := (1 : MulAut (GL (Fin m) R))) hne
    have h2 : UpperTheory.Reformulated.B.SignActionTheta.sgnAct m S (-1) = UpperTheory.Reformulated.B.SignActionTheta.thetaAut m S :=
      if_neg (t := (1 : MulAut (GL (Fin m) S))) hne
    rw [MonoidHom.id_apply, h1, h2]
    refine MonoidHom.ext fun g => ?_
    exact UpperTheory.Reformulated.B.SignActionTheta.map_theta f g

noncomputable def UpperTheory.Reformulated.B.SignActionTheta.map.{u_1, u_2} :
    {m : ℕ} →
      {R : Type u_1} →
        {S : Type u_2} →
          [inst : CommRing R] → [inst_1 : CommRing S] → (R →+* S) → UpperTheory.Reformulated.B.SignActionTheta.GG m R →* UpperTheory.Reformulated.B.SignActionTheta.GG m S :=
    fun {m : ℕ} {R : Type u_1} {S : Type u_2} [CommRing R] [CommRing S] (f : R →+* S) ↦
      SemidirectProduct.map (Matrix.GeneralLinearGroup.map f) (MonoidHom.id ℤˣ) (UpperTheory.Reformulated.B.SignActionTheta.sign_action_map_comm f)

@[reducible] noncomputable def UpperTheory.Reformulated.B.SignActionTheta.ofGL.{u_1} :
    {m : ℕ} → {R : Type u_1} → [inst : CommRing R] → GL (Fin m) R →* UpperTheory.Reformulated.B.SignActionTheta.GG m R :=
    fun {m : ℕ} {R : Type u_1} [CommRing R] ↦ SemidirectProduct.inl

noncomputable def UpperTheory.Reformulated.B.SignActionTheta.conjBy.{u_1, u_3} :
    {m : ℕ} →
      {R : Type u_1} →
        [inst : CommRing R] →
          {G : Type u_3} → [inst_1 : Group G] → GL (Fin m) R → (G →* UpperTheory.Reformulated.B.SignActionTheta.GG m R) → G →* UpperTheory.Reformulated.B.SignActionTheta.GG m R :=
    fun {m : ℕ} {R : Type u_1} [CommRing R] {G : Type u_3} [Group G] (h : GL (Fin m) R) (r : G →* UpperTheory.Reformulated.B.SignActionTheta.GG m R) ↦
      (MulEquiv.toMonoidHom
            ((MulAut.conj : UpperTheory.Reformulated.B.SignActionTheta.GG m R → MulAut (UpperTheory.Reformulated.B.SignActionTheta.GG m R))
              ((UpperTheory.Reformulated.B.SignActionTheta.ofGL : GL (Fin m) R → UpperTheory.Reformulated.B.SignActionTheta.GG m R) h))).comp
        r

theorem UpperTheory.Reformulated.B.SignActionTheta.map_conjBy :
    ∀ {G R S : Type} [inst : Group G] [inst_1 : CommRing R] [inst_2 : CommRing S] {m : ℕ} (f : R →+* S) (h : GL (Fin m) R)
      (r : G →* UpperTheory.Reformulated.B.SignActionTheta.GG m R),
      (UpperTheory.Reformulated.B.SignActionTheta.map f).comp (UpperTheory.Reformulated.B.SignActionTheta.conjBy h r) =
        UpperTheory.Reformulated.B.SignActionTheta.conjBy ((Matrix.GeneralLinearGroup.map f : GL (Fin m) R → GL (Fin m) S) h)
          ((UpperTheory.Reformulated.B.SignActionTheta.map f).comp r) := by
  intro G R S _ _ _ m f h r
  refine MonoidHom.ext fun x => ?_
  have hi : UpperTheory.Reformulated.B.SignActionTheta.map f (UpperTheory.Reformulated.B.SignActionTheta.ofGL h) =
      UpperTheory.Reformulated.B.SignActionTheta.ofGL (Matrix.GeneralLinearGroup.map f h) :=
    SemidirectProduct.map_inl _ _ _ h
  change UpperTheory.Reformulated.B.SignActionTheta.map f (UpperTheory.Reformulated.B.SignActionTheta.ofGL h * r x * (UpperTheory.Reformulated.B.SignActionTheta.ofGL h)⁻¹) =
    UpperTheory.Reformulated.B.SignActionTheta.ofGL (Matrix.GeneralLinearGroup.map f h) * UpperTheory.Reformulated.B.SignActionTheta.map f (r x) *
      (UpperTheory.Reformulated.B.SignActionTheta.ofGL (Matrix.GeneralLinearGroup.map f h))⁻¹
  rw [map_mul, map_mul, map_inv, hi]
end

section

noncomputable def UpperTheory.Reformulated.B.TransposeInverseTheta.Jmat.{u_1} :
    (R : Type u_1) → [CommRing R] → (m : ℕ) → Matrix (Fin m) (Fin m) R :=
    fun (R : Type u_1) [CommRing R] (m : ℕ) (i j : Fin m) ↦ if j = i.rev then (1 : R) else (0 : R)

theorem UpperTheory.Reformulated.B.TransposeInverseTheta.aux2.{u_1} :
    ∀ {R : Type u_1} [inst : CommRing R] (m : ℕ),
      UpperTheory.Reformulated.B.TransposeInverseTheta.Jmat R m * UpperTheory.Reformulated.B.TransposeInverseTheta.Jmat R m = (1 : Matrix (Fin m) (Fin m) R) := by
  intro R _ m
  ext i j
  simp only [Matrix.mul_apply, UpperTheory.Reformulated.B.TransposeInverseTheta.Jmat, Matrix.one_apply]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, Fin.rev_rev]
  simp only [eq_comm]

noncomputable def UpperTheory.Reformulated.B.TransposeInverseTheta.Jgl.{u_1} :
    (R : Type u_1) → [inst : CommRing R] → (m : ℕ) → GL (Fin m) R :=
    fun (R : Type u_1) [CommRing R] (m : ℕ) ↦
      { val := UpperTheory.Reformulated.B.TransposeInverseTheta.Jmat R m, inv := UpperTheory.Reformulated.B.TransposeInverseTheta.Jmat R m, val_inv := UpperTheory.Reformulated.B.TransposeInverseTheta.aux2 m,
        inv_val := UpperTheory.Reformulated.B.TransposeInverseTheta.aux2 m : (Matrix (Fin m) (Fin m) R)ˣ }

theorem UpperTheory.Reformulated.B.TransposeInverseTheta.aux4.{u_1} :
    ∀ {n : Type} [inst : Fintype n] [inst_1 : DecidableEq n] {R : Type u_1} [inst_2 : CommRing R] (g : GL n R),
      (↑g⁻¹ : Matrix n n R).transpose * (↑g : Matrix n n R).transpose = (1 : Matrix n n R) := by
  intro n _ _ R _ g
  rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]

theorem UpperTheory.Reformulated.B.TransposeInverseTheta.aux5.{u_1} :
    ∀ {n : Type} [inst : Fintype n] [inst_1 : DecidableEq n] {R : Type u_1} [inst_2 : CommRing R] (g : GL n R),
      (↑g : Matrix n n R).transpose * (↑g⁻¹ : Matrix n n R).transpose = (1 : Matrix n n R) := by
  intro n _ _ R _ g
  rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]

noncomputable def UpperTheory.Reformulated.B.TransposeInverseTheta.trInv.{u_1} :
    {n : Type} → [inst : Fintype n] → [inst_1 : DecidableEq n] → {R : Type u_1} → [inst_2 : CommRing R] → GL n R → GL n R :=
    fun {n : Type} [Fintype n] [DecidableEq n] {R : Type u_1} [CommRing R] (g : GL n R) ↦
      { val := (↑g⁻¹ : Matrix n n R).transpose, inv := (↑g : Matrix n n R).transpose, val_inv := UpperTheory.Reformulated.B.TransposeInverseTheta.aux4 g,
        inv_val := UpperTheory.Reformulated.B.TransposeInverseTheta.aux5 g : (Matrix n n R)ˣ }

noncomputable def UpperTheory.Reformulated.B.TransposeInverseTheta.theta.{u_1} :
    {m : ℕ} → {R : Type u_1} → [inst : CommRing R] → GL (Fin m) R → GL (Fin m) R :=
    fun {m : ℕ} {R : Type u_1} [CommRing R] (g : GL (Fin m) R) ↦
      UpperTheory.Reformulated.B.TransposeInverseTheta.Jgl R m * UpperTheory.Reformulated.B.TransposeInverseTheta.trInv g * UpperTheory.Reformulated.B.TransposeInverseTheta.Jgl R m

private theorem UpperTheory.Reformulated.B.TransposeInverseTheta.trInv_mul {n : Type} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    (g h : GL n R) :
    UpperTheory.Reformulated.B.TransposeInverseTheta.trInv (g * h) = UpperTheory.Reformulated.B.TransposeInverseTheta.trInv g * UpperTheory.Reformulated.B.TransposeInverseTheta.trInv h := by
  apply Units.ext
  change (↑(g * h)⁻¹ : Matrix n n R).transpose = (↑g⁻¹ : Matrix n n R).transpose * (↑h⁻¹ : Matrix n n R).transpose
  rw [mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

private theorem UpperTheory.Reformulated.B.TransposeInverseTheta.trInv_trInv {n : Type} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    (g : GL n R) : UpperTheory.Reformulated.B.TransposeInverseTheta.trInv (UpperTheory.Reformulated.B.TransposeInverseTheta.trInv g) = g := by
  apply Units.ext
  change (↑g : Matrix n n R).transpose.transpose = ↑g
  rw [Matrix.transpose_transpose]

private theorem UpperTheory.Reformulated.B.TransposeInverseTheta.Jgl_mul_self {m : ℕ} {R : Type*} [CommRing R] :
    UpperTheory.Reformulated.B.TransposeInverseTheta.Jgl R m * UpperTheory.Reformulated.B.TransposeInverseTheta.Jgl R m = 1 :=
  Units.ext (UpperTheory.Reformulated.B.TransposeInverseTheta.aux2 m)

private theorem UpperTheory.Reformulated.B.TransposeInverseTheta.trInv_Jgl {m : ℕ} {R : Type*} [CommRing R] :
    UpperTheory.Reformulated.B.TransposeInverseTheta.trInv (UpperTheory.Reformulated.B.TransposeInverseTheta.Jgl R m) = UpperTheory.Reformulated.B.TransposeInverseTheta.Jgl R m := by
  apply Units.ext
  change (UpperTheory.Reformulated.B.TransposeInverseTheta.Jmat R m).transpose = UpperTheory.Reformulated.B.TransposeInverseTheta.Jmat R m
  ext i j
  simp only [Matrix.transpose_apply, UpperTheory.Reformulated.B.TransposeInverseTheta.Jmat]
  by_cases h : j = i.rev
  · have h' : i = j.rev := by rw [h, Fin.rev_rev]
    simp [h, ← h']
  · have h' : ¬ i = j.rev := fun e => h (by rw [e, Fin.rev_rev])
    simp [h, h']

theorem UpperTheory.Reformulated.B.TransposeInverseTheta.aux8.{u_1} :
    ∀ {m : ℕ} {R : Type u_1} [inst : CommRing R] (g : GL (Fin m) R), UpperTheory.Reformulated.B.TransposeInverseTheta.theta (UpperTheory.Reformulated.B.TransposeInverseTheta.theta g) = g := by
  intro m R _ g
  have hJ := UpperTheory.Reformulated.B.TransposeInverseTheta.Jgl_mul_self (m := m) (R := R)
  simp only [UpperTheory.Reformulated.B.TransposeInverseTheta.theta, UpperTheory.Reformulated.B.TransposeInverseTheta.trInv_mul, UpperTheory.Reformulated.B.TransposeInverseTheta.trInv_trInv,
    UpperTheory.Reformulated.B.TransposeInverseTheta.trInv_Jgl]
  calc _ = (UpperTheory.Reformulated.B.TransposeInverseTheta.Jgl R m * UpperTheory.Reformulated.B.TransposeInverseTheta.Jgl R m) * g *
        (UpperTheory.Reformulated.B.TransposeInverseTheta.Jgl R m * UpperTheory.Reformulated.B.TransposeInverseTheta.Jgl R m) := by simp only [mul_assoc]
    _ = g := by rw [hJ, one_mul, mul_one]

theorem UpperTheory.Reformulated.B.TransposeInverseTheta.aux9.{u_1} :
    ∀ {m : ℕ} {R : Type u_1} [inst : CommRing R] (g h : GL (Fin m) R),
      UpperTheory.Reformulated.B.TransposeInverseTheta.theta (g * h) = UpperTheory.Reformulated.B.TransposeInverseTheta.theta g * UpperTheory.Reformulated.B.TransposeInverseTheta.theta h := by
  intro m R _ g h
  have hJ := UpperTheory.Reformulated.B.TransposeInverseTheta.Jgl_mul_self (m := m) (R := R)
  simp only [UpperTheory.Reformulated.B.TransposeInverseTheta.theta, UpperTheory.Reformulated.B.TransposeInverseTheta.trInv_mul]
  calc _ = UpperTheory.Reformulated.B.TransposeInverseTheta.Jgl R m * UpperTheory.Reformulated.B.TransposeInverseTheta.trInv g * 1 * UpperTheory.Reformulated.B.TransposeInverseTheta.trInv h *
        UpperTheory.Reformulated.B.TransposeInverseTheta.Jgl R m := by simp only [mul_assoc, one_mul]
    _ = _ := by rw [← hJ]; simp only [mul_assoc]

noncomputable def UpperTheory.Reformulated.B.TransposeInverseTheta.thetaAut.{u_1} :
    (m : ℕ) → (R : Type u_1) → [inst : CommRing R] → MulAut (GL (Fin m) R) :=
    fun (m : ℕ) (R : Type u_1) [CommRing R] ↦
      { toFun := UpperTheory.Reformulated.B.TransposeInverseTheta.theta, invFun := UpperTheory.Reformulated.B.TransposeInverseTheta.theta, left_inv := UpperTheory.Reformulated.B.TransposeInverseTheta.aux8,
        right_inv := UpperTheory.Reformulated.B.TransposeInverseTheta.aux8, map_mul' := UpperTheory.Reformulated.B.TransposeInverseTheta.aux9 : GL (Fin m) R ≃* GL (Fin m) R }

theorem UpperTheory.Reformulated.B.TransposeInverseTheta.aux11.{u_1} :
    ∀ (m : ℕ) (R : Type u_1) [inst : CommRing R],
      (if (1 : ℤˣ) = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.TransposeInverseTheta.thetaAut m R) =
        (1 : MulAut (GL (Fin m) R)) := by
  intro m R _
  exact if_pos rfl

private theorem UpperTheory.Reformulated.B.TransposeInverseTheta.thetaAut_mul_self (m : ℕ) (R : Type*) [CommRing R] :
    UpperTheory.Reformulated.B.TransposeInverseTheta.thetaAut m R * UpperTheory.Reformulated.B.TransposeInverseTheta.thetaAut m R = 1 := by
  ext1 g
  exact UpperTheory.Reformulated.B.TransposeInverseTheta.aux8 g

theorem UpperTheory.Reformulated.B.TransposeInverseTheta.aux12.{u_1} :
    ∀ (m : ℕ) (R : Type u_1) [inst : CommRing R] (s t : ℤˣ),
      (if s * t = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.TransposeInverseTheta.thetaAut m R) =
        (if s = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.TransposeInverseTheta.thetaAut m R) *
          if t = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.TransposeInverseTheta.thetaAut m R := by
  intro m R _ s t
  have hne : (-1 : ℤˣ) ≠ 1 := by decide
  rcases Int.units_eq_one_or s with rfl | rfl <;> rcases Int.units_eq_one_or t with rfl | rfl
  · simp
  · simp [hne]
  · simp [hne]
  · simp [hne, UpperTheory.Reformulated.B.TransposeInverseTheta.thetaAut_mul_self]

noncomputable def UpperTheory.Reformulated.B.TransposeInverseTheta.sgnAct.{u_1} :
    (m : ℕ) → (R : Type u_1) → [inst : CommRing R] → ℤˣ →* MulAut (GL (Fin m) R) :=
    fun (m : ℕ) (R : Type u_1) [CommRing R] ↦
      { toFun := fun (s : ℤˣ) ↦ if s = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.TransposeInverseTheta.thetaAut m R,
        map_one' := UpperTheory.Reformulated.B.TransposeInverseTheta.aux11 m R, map_mul' := UpperTheory.Reformulated.B.TransposeInverseTheta.aux12 m R : ℤˣ →* MulAut (GL (Fin m) R) }

@[reducible] noncomputable def UpperTheory.Reformulated.B.TransposeInverseTheta.GG.{u_1} :
    ℕ → (R : Type u_1) → [CommRing R] → Type u_1 :=
    fun (m : ℕ) (R : Type u_1) [CommRing R] ↦ GL (Fin m) R ⋊[UpperTheory.Reformulated.B.TransposeInverseTheta.sgnAct m R] ℤˣ

@[reducible] noncomputable def UpperTheory.Reformulated.B.TransposeInverseTheta.ofGL.{u_1} :
    {m : ℕ} → {R : Type u_1} → [inst : CommRing R] → GL (Fin m) R →* UpperTheory.Reformulated.B.TransposeInverseTheta.GG m R :=
    fun {m : ℕ} {R : Type u_1} [CommRing R] ↦ SemidirectProduct.inl

noncomputable def UpperTheory.Reformulated.B.TransposeInverseTheta.conjBy.{u_1, u_3} :
    {m : ℕ} →
      {R : Type u_1} →
        [inst : CommRing R] →
          {G : Type u_3} → [inst_1 : Group G] → GL (Fin m) R → (G →* UpperTheory.Reformulated.B.TransposeInverseTheta.GG m R) → G →* UpperTheory.Reformulated.B.TransposeInverseTheta.GG m R :=
    fun {m : ℕ} {R : Type u_1} [CommRing R] {G : Type u_3} [Group G] (h : GL (Fin m) R) (r : G →* UpperTheory.Reformulated.B.TransposeInverseTheta.GG m R) ↦
      (MulEquiv.toMonoidHom
            ((MulAut.conj : UpperTheory.Reformulated.B.TransposeInverseTheta.GG m R → MulAut (UpperTheory.Reformulated.B.TransposeInverseTheta.GG m R))
              ((UpperTheory.Reformulated.B.TransposeInverseTheta.ofGL : GL (Fin m) R → UpperTheory.Reformulated.B.TransposeInverseTheta.GG m R) h))).comp
        r

theorem UpperTheory.Reformulated.B.TransposeInverseTheta.conj_left :
    ∀ {G R : Type} [inst : Group G] [inst_1 : CommRing R] {m : ℕ} (h : GL (Fin m) R) (r : G →* UpperTheory.Reformulated.B.TransposeInverseTheta.GG m R)
      (g : G),
      ((UpperTheory.Reformulated.B.TransposeInverseTheta.conjBy h r : G → UpperTheory.Reformulated.B.TransposeInverseTheta.GG m R) g).left =
        h * ((r : G → UpperTheory.Reformulated.B.TransposeInverseTheta.GG m R) g).left *
          ((UpperTheory.Reformulated.B.TransposeInverseTheta.sgnAct m R : ℤˣ → MulAut (GL (Fin m) R)) ((r : G → UpperTheory.Reformulated.B.TransposeInverseTheta.GG m R) g).right :
              GL (Fin m) R → GL (Fin m) R)
            h⁻¹ := by
  intro G R _ _ m h r g
  have e : (UpperTheory.Reformulated.B.TransposeInverseTheta.conjBy h r) g =
      SemidirectProduct.inl h * r g * (SemidirectProduct.inl h)⁻¹ := rfl
  rw [e, ← map_inv, SemidirectProduct.mul_left, SemidirectProduct.mul_left]
  simp [mul_assoc]
end

section

theorem UpperTheory.Reformulated.B.Ra1.ab_eval :
    ∀ {k X : Type} [inst : Field k] [Inhabited X] (r : ℕ)
    (H : Submodule k (X → k)),
    Module.Finite k ↥H →
      Module.finrank k ↥H ≤ r → ∃ (t : Fin r → X), ∀ φ ∈ H, (∀ (a : Fin r), φ (t a) = (0 : k)) → φ = (0 : X → k) := by
  intro k X inst _ r
  induction r with
  | zero =>
    intro H hfin hr
    have hH : H = ⊥ := Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hr)
    refine ⟨fun _ => default, fun φ hφ _ => ?_⟩
    rw [hH] at hφ
    exact (Submodule.mem_bot k).mp hφ
  | succ n ih =>
    intro H hfin hr
    by_cases h : ∀ φ ∈ H, φ = 0
    · exact ⟨fun _ => default, fun φ hφ _ => h φ hφ⟩
    · have h' : ∃ ψ ∈ H, ∃ x, ψ x ≠ 0 := by
        by_contra hc
        apply h
        intro φ hφ
        funext x
        by_contra hx
        exact hc ⟨φ, hφ, x, hx⟩
      obtain ⟨ψ, hψ, x, hx⟩ := h'
      let K : Submodule k (X → k) :=
        H ⊓ LinearMap.ker (LinearMap.proj (R := k) (φ := fun _ : X => k) x)
      have hle : K ≤ H := inf_le_left
      have hlt : K < H := by
        refine lt_of_le_of_ne hle ?_
        intro he
        have hK : ψ ∈ K := he ▸ hψ
        exact hx hK.2
      have hKfin : Module.Finite k ↥K := Submodule.finiteDimensional_of_le hle
      have hrank : Module.finrank k ↥K < Module.finrank k ↥H :=
        Submodule.finrank_lt_finrank_of_lt hlt
      obtain ⟨t, ht⟩ := ih K hKfin (by omega)
      refine ⟨Fin.cons x t, fun φ hφ h0 => ?_⟩
      exact ht φ ⟨hφ, h0 0⟩ (fun a => h0 a.succ)
end

section

theorem UpperTheory.Reformulated.B.Qk9.tri_diag :
    ∀ {R : Type} [inst : CommRing R] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) R),
    A.BlockTriangular id → B.BlockTriangular id → ∀ (i : Fin n), (A * B) i i = A i i * B i i := by
  intro R _ n A B hA hB i
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i ?_ ?_
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with h | h
    · rw [hA (show id j < id i from h), zero_mul]
    · rw [hB (show id i < id j from h), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h
end
