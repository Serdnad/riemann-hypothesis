module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.NumberTheory.NumberField.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Basic.Real.ConjExponents
public import Mathlib.MeasureTheory.Integral.MeanInequalities

@[expose] public section

section

namespace UpperTheory.Reformulated.B.P6.BlockTriangularLevi

open scoped Sigma DFunLike EquivLike Equiv Matrix CommSemiring CommRing Membership Set Preorder PartialOrder SemilatticeInf Lattice DistribLattice MulZeroClass Units Semiring HMul MulOne MulOneClass Monoid DivInvMonoid Group OfNat One Inv InvOneClass DivInvOneMonoid DivisionMonoid Subgroup Submonoid Subsemigroup Subtype SetLike MulZeroOneClass MonoidHom OneHom Pi PUnit Fin Finset HAdd AddMonoidWithOne AddGroupWithOne Ring DivisionRing Field CommGroup Circle DivisionSemiring Semifield Complex SeminormedRing SeminormedCommRing NormedCommRing NormedField AddChar Zero HSub

noncomputable def GlobalTheory.SmGL.blk :
    {α n : Type} → {m : α → Type} → (a : α) × m a ≃ n → n → α :=
  fun {α n : Type} {m : α → Type} (e : (a : α) × m a ≃ n) (i : n) ↦ Sigma.fst (β := fun (a : α) ↦ m a) (DFunLike.coe (β := fun (x_h1 : n) ↦ (a : α) × m a) e.symm i)

theorem blockIndex_sigma_equiv {α n : Type} {m : α → Type} (e : (a : α) × m a ≃ n) (a : α) (i : m a) :
    GlobalTheory.SmGL.blk (m := m) e (e ⟨a, i⟩) = a := by
  show (e.symm (e ⟨a, i⟩)).1 = a
  rw [Equiv.symm_apply_apply]

theorem blockTriangular_mul_submatrix {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
    [∀ a, Fintype (m a)] [Fintype n] (e : (a : α) × m a ≃ n) (a : α) (X Y : Matrix n n R)
    (hX : X.BlockTriangular (GlobalTheory.SmGL.blk (m := m) e))
    (hY : Y.BlockTriangular (GlobalTheory.SmGL.blk (m := m) e)) :
    (X * Y).submatrix (fun i : m a => e ⟨a, i⟩) (fun i : m a => e ⟨a, i⟩)
      = X.submatrix (fun i : m a => e ⟨a, i⟩) (fun i : m a => e ⟨a, i⟩)
        * Y.submatrix (fun i : m a => e ⟨a, i⟩) (fun i : m a => e ⟨a, i⟩) := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  rw [← e.sum_comp, Fintype.sum_sigma, Finset.sum_eq_single a]
  · intro b _ hb
    apply Finset.sum_eq_zero
    intro l _
    rcases lt_or_gt_of_ne hb with h | h
    · have h' : GlobalTheory.SmGL.blk (m := m) e (e ⟨b, l⟩) < GlobalTheory.SmGL.blk (m := m) e (e ⟨a, i⟩) := by
        rw [blockIndex_sigma_equiv, blockIndex_sigma_equiv]; exact h
      rw [hX h', zero_mul]
    · have h' : GlobalTheory.SmGL.blk (m := m) e (e ⟨a, j⟩) < GlobalTheory.SmGL.blk (m := m) e (e ⟨b, l⟩) := by
        rw [blockIndex_sigma_equiv, blockIndex_sigma_equiv]; exact h
      rw [hY h', mul_zero]
  · intro h
    exact absurd (Finset.mem_univ a) h

theorem GlobalTheory.SmGL.parab_obl_1 :
    ∀ (R : Type) [inst_h0 : CommRing R] {α n : Type} {m : α → Type} [inst_h2 : LinearOrder α] [inst_h3 : Fintype n] [inst_h4 : DecidableEq n] (e : (a : α) × m a ≃ n) {x y : GL n R}, Membership.mem (γ := Set (GL n R)) {g : GL n R | g.val.BlockTriangular (GlobalTheory.SmGL.blk (m := m) e)} x → Membership.mem (γ := Set (GL n R)) {g : GL n R | g.val.BlockTriangular (GlobalTheory.SmGL.blk (m := m) e)} y → Membership.mem (γ := Set (GL n R)) {g : GL n R | g.val.BlockTriangular (GlobalTheory.SmGL.blk (m := m) e)} (x * y) := by
  intro R _ α n m _ _ _ e x y hx hy
  show ((x * y : GL n R) : Matrix n n R).BlockTriangular _
  rw [Units.val_mul]
  exact Matrix.BlockTriangular.mul hx hy

theorem GlobalTheory.SmGL.parab_obl_2 :
    ∀ (R : Type) [inst_h0 : CommRing R] {α n : Type} {m : α → Type} [inst_h2 : LinearOrder α] [inst_h3 : Fintype n] [inst_h4 : DecidableEq n] (e : (a : α) × m a ≃ n), Membership.mem (γ := Set (GL n R)) {g : GL n R | g.val.BlockTriangular (GlobalTheory.SmGL.blk (m := m) e)} (OfNat.ofNat (nat_lit 1)) := by
  intro R _ α n m _ _ _ e
  show ((1 : GL n R) : Matrix n n R).BlockTriangular _
  rw [Units.val_one]
  exact Matrix.blockTriangular_one

theorem GlobalTheory.SmGL.parab_obl_3 :
    ∀ (R : Type) [inst_h0 : CommRing R] {α n : Type} {m : α → Type} [inst_h2 : LinearOrder α] [inst_h3 : Fintype n] [inst_h4 : DecidableEq n] (e : (a : α) × m a ≃ n) {x : GL n R}, Membership.mem (γ := Set (GL n R)) {g : GL n R | g.val.BlockTriangular (GlobalTheory.SmGL.blk (m := m) e)} x → Membership.mem (γ := Set (GL n R)) {g : GL n R | g.val.BlockTriangular (GlobalTheory.SmGL.blk (m := m) e)} x⁻¹ := by
  intro R _ α n m _ _ _ e x hx
  show ((x⁻¹ : GL n R) : Matrix n n R).BlockTriangular _
  rw [Matrix.coe_units_inv]
  haveI : Invertible (x : Matrix n n R) := x.invertible
  exact Matrix.blockTriangular_inv_of_blockTriangular hx

noncomputable def GlobalTheory.SmGL.parab :
    (R : Type) → [inst_h0 : CommRing R] → {α n : Type} → {m : α → Type} → [inst_h2 : LinearOrder α] → [inst_h3 : Fintype n] → [inst_h4 : DecidableEq n] → (a : α) × m a ≃ n → Subgroup (GL n R) :=
  fun (R : Type) {inst_h0 : CommRing R} {α n : Type} {m : α → Type} {inst_h2 : LinearOrder α} {inst_h3 : Fintype n} {inst_h4 : DecidableEq n} (e : (a : α) × m a ≃ n) ↦ { carrier := {g : GL n R | g.val.BlockTriangular (GlobalTheory.SmGL.blk (m := m) e)}, mul_mem' := @GlobalTheory.SmGL.parab_obl_1 R inst_h0 α n m inst_h2 inst_h3 inst_h4 e, one_mem' := GlobalTheory.SmGL.parab_obl_2 R (m := m) e, inv_mem' := @GlobalTheory.SmGL.parab_obl_3 R inst_h0 α n m inst_h2 inst_h3 inst_h4 e }

@[reducible] noncomputable def GlobalTheory.SmGL.Levi :
    (R : Type) → [inst_h0 : CommRing R] → {α : Type} → (m : α → Type) → [inst_h2 : (a : α) → Fintype (m a)] → [inst_h3 : (a : α) → DecidableEq (m a)] → Type :=
  fun (R : Type) {inst_f0 : CommRing R} {α : Type} (m : α → Type) {inst_f1 : (a : α) → Fintype (m a)} {inst_f2 : (a : α) → DecidableEq (m a)} ↦ (a : α) → GL (m a) R

theorem GlobalTheory.SmGL.diagBlock_obl_1 :
    ∀ (R : Type) [inst_h0 : CommRing R] {α n : Type} {m : α → Type} [inst_h2 : LinearOrder α] [inst_h3 : (a : α) → Fintype (m a)] [inst_h4 : (a : α) → DecidableEq (m a)] [inst_h5 : Fintype n] [inst_h6 : DecidableEq n] (e : (a : α) × m a ≃ n) (a : α), Eq (α := Matrix (m a) (m a) R) (Matrix.submatrix (m := n) (n := n) (Units.val (Subtype.val (p := fun (x : GL n R) ↦ Membership.mem (γ := Subgroup (GL n R)) (GlobalTheory.SmGL.parab R (m := m) e) x) (OfNat.ofNat (nat_lit 1)))) (fun (i : m a) ↦ DFunLike.coe (β := fun (x_h7 : (a : α) × m a) ↦ n) e (Sigma.mk (β := fun (a : α) ↦ m a) a i)) fun (i : m a) ↦ DFunLike.coe (β := fun (x_h8 : (a : α) × m a) ↦ n) e (Sigma.mk (β := fun (a : α) ↦ m a) a i)) (OfNat.ofNat (nat_lit 1)) := by
  intro R _ α n m _ _ _ _ _ e a
  show ((1 : GL n R) : Matrix n n R).submatrix _ _ = 1
  rw [Units.val_one]
  exact Matrix.submatrix_one _ (e.injective.comp sigma_mk_injective)

theorem GlobalTheory.SmGL.diagBlock_obl_2 :
    ∀ (R : Type) [inst_h0 : CommRing R] {α n : Type} {m : α → Type} [inst_h2 : Fintype α] [inst_h3 : LinearOrder α] [inst_h4 : (a : α) → Fintype (m a)] [inst_h5 : (a : α) → DecidableEq (m a)] [inst_h6 : Fintype n] [inst_h7 : DecidableEq n] (e : (a : α) × m a ≃ n) (a : α) (x y : ↥(GlobalTheory.SmGL.parab R (m := m) e)), ((x * y).val (p := fun (x : GL n R) ↦ Membership.mem (γ := Subgroup (GL n R)) (GlobalTheory.SmGL.parab R (m := m) e) x).val.submatrix (fun (i : m a) ↦ DFunLike.coe (β := fun (x_h8 : (a : α) × m a) ↦ n) e (Sigma.mk (β := fun (a : α) ↦ m a) a i)) fun (i : m a) ↦ DFunLike.coe (β := fun (x_h9 : (a : α) × m a) ↦ n) e (Sigma.mk (β := fun (a : α) ↦ m a) a i)) = HMul.hMul (α := Matrix (m a) (m a) R) (x.val (p := fun (x : GL n R) ↦ Membership.mem (γ := Subgroup (GL n R)) (GlobalTheory.SmGL.parab R (m := m) e) x).val.submatrix (fun (i : m a) ↦ DFunLike.coe (β := fun (x_h10 : (a : α) × m a) ↦ n) e (Sigma.mk (β := fun (a : α) ↦ m a) a i)) fun (i : m a) ↦ DFunLike.coe (β := fun (x_h11 : (a : α) × m a) ↦ n) e (Sigma.mk (β := fun (a : α) ↦ m a) a i)) (y.val (p := fun (x : GL n R) ↦ Membership.mem (γ := Subgroup (GL n R)) (GlobalTheory.SmGL.parab R (m := m) e) x).val.submatrix (fun (i : m a) ↦ DFunLike.coe (β := fun (x_h12 : (a : α) × m a) ↦ n) e (Sigma.mk (β := fun (a : α) ↦ m a) a i)) fun (i : m a) ↦ DFunLike.coe (β := fun (x_h13 : (a : α) × m a) ↦ n) e (Sigma.mk (β := fun (a : α) ↦ m a) a i)) := by
  intro R _ α n m _ _ _ _ _ _ e a x y
  have hx : ((x : GL n R) : Matrix n n R).BlockTriangular (GlobalTheory.SmGL.blk (m := m) e) := x.2
  have hy : ((y : GL n R) : Matrix n n R).BlockTriangular (GlobalTheory.SmGL.blk (m := m) e) := y.2
  have key := blockTriangular_mul_submatrix e a _ _ hx hy
  exact key

noncomputable def GlobalTheory.SmGL.diagBlock :
    (R : Type) → [inst_h0 : CommRing R] → {α n : Type} → {m : α → Type} → [inst_h2 : Fintype α] → [inst_h3 : LinearOrder α] → [inst_h4 : (a : α) → Fintype (m a)] → [inst_h5 : (a : α) → DecidableEq (m a)] → [inst_h6 : Fintype n] → [inst_h7 : DecidableEq n] → (e : (a : α) × m a ≃ n) → (a : α) → ↥(GlobalTheory.SmGL.parab R (m := m) e) →* Matrix (m a) (m a) R :=
  fun (R : Type) {inst_f3 : CommRing R} {α n : Type} {m : α → Type} {inst_f4 : Fintype α} {inst_f5 : LinearOrder α} {inst_f6 : (a : α) → Fintype (m a)} {inst_f7 : (a : α) → DecidableEq (m a)} {inst_f8 : Fintype n} {inst_f9 : DecidableEq n} (e : (a : α) × m a ≃ n) (a : α) ↦ { toFun := fun (p : ↥(GlobalTheory.SmGL.parab R (m := m) e)) ↦ p.val (p := fun (x : GL n R) ↦ Membership.mem (γ := Subgroup (GL n R)) (GlobalTheory.SmGL.parab R (m := m) e) x).val.submatrix (fun (i : m a) ↦ DFunLike.coe (β := fun (x_h8 : (a : α) × m a) ↦ n) e (Sigma.mk (β := fun (a : α) ↦ m a) a i)) fun (i : m a) ↦ DFunLike.coe (β := fun (x_h9 : (a : α) × m a) ↦ n) e (Sigma.mk (β := fun (a : α) ↦ m a) a i), map_one' := GlobalTheory.SmGL.diagBlock_obl_1 R (m := m) e a, map_mul' := GlobalTheory.SmGL.diagBlock_obl_2 R (m := m) e a }

noncomputable def GlobalTheory.SmGL.leviProj :
    (R : Type) → [inst_h0 : CommRing R] → {α n : Type} → {m : α → Type} → [inst_h2 : Fintype α] → [inst_h3 : LinearOrder α] → [inst_h4 : (a : α) → Fintype (m a)] → [inst_h5 : (a : α) → DecidableEq (m a)] → [inst_h6 : Fintype n] → [inst_h7 : DecidableEq n] → (e : (a : α) × m a ≃ n) → ↥(GlobalTheory.SmGL.parab R (m := m) e) →* GlobalTheory.SmGL.Levi R m :=
  fun (R : Type) {inst_f10 : CommRing R} {α n : Type} {m : α → Type} {inst_f11 : Fintype α} {inst_f12 : LinearOrder α} {inst_f13 : (a : α) → Fintype (m a)} {inst_f14 : (a : α) → DecidableEq (m a)} {inst_f15 : Fintype n} {inst_f16 : DecidableEq n} (e : (a : α) × m a ≃ n) ↦ MonoidHom.pi (f := fun (a : α) ↦ GL (m a) R) fun (a : α) ↦ MonoidHom.toHomUnits (GlobalTheory.SmGL.diagBlock R (m := m) e a)

noncomputable def GlobalTheory.SmGL.unipRad :
    (R : Type) → [inst_h0 : CommRing R] → {α n : Type} → {m : α → Type} → [inst_h2 : Fintype α] → [inst_h3 : LinearOrder α] → [inst_h4 : (a : α) → Fintype (m a)] → [inst_h5 : (a : α) → DecidableEq (m a)] → [inst_h6 : Fintype n] → [inst_h7 : DecidableEq n] → (a : α) × m a ≃ n → Subgroup (GL n R) :=
  fun (R : Type) {inst_f17 : CommRing R} {α n : Type} {m : α → Type} {inst_f18 : Fintype α} {inst_f19 : LinearOrder α} {inst_f20 : (a : α) → Fintype (m a)} {inst_f21 : (a : α) → DecidableEq (m a)} {inst_f22 : Fintype n} {inst_f23 : DecidableEq n} (e : (a : α) × m a ≃ n) ↦ Subgroup.map (G := ↥(GlobalTheory.SmGL.parab R (m := m) e)) (Subgroup.subtype (GlobalTheory.SmGL.parab R (m := m) e)) (MonoidHom.ker (GlobalTheory.SmGL.leviProj R (m := m) e))

noncomputable def GlobalTheory.SmGL.points :
    (n : Type) → (_ : n) × Unit ≃ n :=
  fun (n : Type) ↦ Equiv.sigmaUnique n fun (x_h0 : n) ↦ Unit

noncomputable def GlobalTheory.SmGL.unipB :
    (R : Type) → [inst_h0 : CommRing R] → (n : Type) → [inst_h1 : Fintype n] → [inst_h2 : DecidableEq n] → [inst_h3 : LinearOrder n] → Subgroup (GL n R) :=
  fun (R : Type) {inst_f24 : CommRing R} (n : Type) {inst_f25 : Fintype n} {inst_f26 : DecidableEq n} {inst_f27 : LinearOrder n} ↦ GlobalTheory.SmGL.unipRad R (m := fun (a : n) ↦ Unit) (GlobalTheory.SmGL.points n)

noncomputable def GlobalTheory.Whittaker.superDiag :
    {R : Type} → [inst_h0 : CommRing R] → {n : ℕ} → GL (Fin n) R → R :=
  fun {R : Type} {inst_f28 : CommRing R} {n : ℕ} (g : GL (Fin n) R) ↦ ∑ i : Fin n, ∑ j : Fin n with j.val = i.val + OfNat.ofNat (nat_lit 1), g.val i j

noncomputable def DiscreteGroups.sglob.LConv.IsWhitTest :
    {k : Type} → [inst_h0 : Field k] → [inst_h1 : TopologicalSpace k] → {m : ℕ} → AddChar k Circle → (GL (Fin m) k → ℂ) → Prop :=
  fun {k : Type} {inst_f29 : Field k} {inst_f30 : TopologicalSpace k} {m : ℕ} (ψ : AddChar k Circle) (f : GL (Fin m) k → ℂ) ↦ (∀ (u : GL (Fin m) k), Membership.mem (γ := Subgroup (GL (Fin m) k)) (GlobalTheory.SmGL.unipB k (Fin m)) u → ∀ (g : GL (Fin m) k), f (u * g) = Subtype.val (p := fun (x : ℂ) ↦ Membership.mem (γ := Submonoid ℂ) (Submonoid.unitSphere ℂ) x) (DFunLike.coe (β := fun (x_h4 : k) ↦ Circle) ψ (GlobalTheory.Whittaker.superDiag u)) * f g) ∧ IsLocallyConstant f ∧ ∃ (C : Set (GL (Fin m) k)), IsCompact C ∧ ∀ (g : GL (Fin m) k), f g ≠ OfNat.ofNat (nat_lit 0) → ∃ (u : GL (Fin m) k), Membership.mem (γ := Subgroup (GL (Fin m) k)) (GlobalTheory.SmGL.unipB k (Fin m)) u ∧ ∃ c ∈ C, g = u * c

theorem DiscreteGroups.sglob.LConv.IsWhitTest.sub :
    ∀ {k : Type} [inst_h0 : Field k] [inst_h1 : TopologicalSpace k] {m : ℕ} {ψ : AddChar k Circle} {f f' : GL (Fin m) k → ℂ}, DiscreteGroups.sglob.LConv.IsWhitTest ψ f → DiscreteGroups.sglob.LConv.IsWhitTest ψ f' → DiscreteGroups.sglob.LConv.IsWhitTest (m := m) ψ fun (g : GL (Fin m) k) ↦ f g - f' g := by
  intro k _ _ m ψ f f' hf hf'
  unfold DiscreteGroups.sglob.LConv.IsWhitTest at hf hf' ⊢
  obtain ⟨h1, h2, C, hC, h3⟩ := hf
  obtain ⟨h1', h2', C', hC', h3'⟩ := hf'
  refine ⟨?_, h2.sub h2', C ∪ C', hC.union hC', ?_⟩
  · intro u hu g
    beta_reduce
    rw [h1 u hu g, h1' u hu g, mul_sub]
  · intro g hg
    beta_reduce at hg
    by_cases hfg : f g = 0
    · have hfg' : f' g ≠ 0 := by
        intro h
        apply hg
        rw [hfg, h, sub_zero]
      obtain ⟨u, hu, c, hc, rfl⟩ := h3' g hfg'
      exact ⟨u, hu, c, Set.mem_union_right _ hc, rfl⟩
    · obtain ⟨u, hu, c, hc, rfl⟩ := h3 g hfg
      exact ⟨u, hu, c, Set.mem_union_left _ hc, rfl⟩

end UpperTheory.Reformulated.B.P6.BlockTriangularLevi
end

section

namespace UpperTheory.Reformulated.B.P6.r24a

theorem quadratic_form_smul_re {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Q : V →L[ℝ] V →L[ℝ] ℂ) (c : ℝ) (x : V) :
    (Q (c • x) (c • x)).re = c ^ 2 * (Q x x).re := by
  simp only [map_smul, ContinuousLinearMap.smul_apply, Complex.smul_re, smul_eq_mul]
  ring

theorem inv_norm_smul_mem_sphere {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (x : V) (hx : x ≠ 0) : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : V) 1 := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']

theorem PositivityTheory.Rg.Sw.Glob.GCSchH.coercive_of_pos :
    ∀ {V : Type} [inst : NormedAddCommGroup V] [inst_1 : NormedSpace ℝ V] [FiniteDimensional ℝ V] (Q : V →L[ℝ] V →L[ℝ] ℂ), (∀ (x : V), x ≠ OfNat.ofNat (nat_lit 0) → OfNat.ofNat (nat_lit 0) < (DFunLike.coe (DFunLike.coe Q x) x).re) → ∃ (κ : ℝ), OfNat.ofNat (nat_lit 0) < κ ∧ ∀ (x : V), κ * ‖x‖ ^ OfNat.ofNat (nat_lit 2) ≤ (DFunLike.coe (DFunLike.coe Q x) x).re := by
  intro V _ _ _ Q hQ
  have hcont : Continuous fun x : V => (Q x x).re :=
    Complex.continuous_re.comp (Q.continuous.clm_apply continuous_id)
  by_cases hne : (Metric.sphere (0 : V) 1).Nonempty
  · obtain ⟨x0, hx0, hmin⟩ :=
      (isCompact_sphere (0 : V) 1).exists_isMinOn hne hcont.continuousOn
    have hx0ne : x0 ≠ 0 := by
      intro h
      rw [h, mem_sphere_zero_iff_norm, norm_zero] at hx0
      exact zero_ne_one hx0
    refine ⟨(Q x0 x0).re, hQ x0 hx0ne, fun x => ?_⟩
    by_cases hx : x = 0
    · subst hx
      simp
    · have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
      obtain ⟨y, hyd⟩ : ∃ y : V, y = ‖x‖⁻¹ • x := ⟨_, rfl⟩
      have hy : y ∈ Metric.sphere (0 : V) 1 := hyd ▸ inv_norm_smul_mem_sphere x hx
      have h1 : (Q x0 x0).re ≤ (Q y y).re := hmin hy
      have h2 : ‖x‖ • y = x := by
        rw [hyd, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
      have h3 : (Q x x).re = ‖x‖ ^ 2 * (Q y y).re := by
        have := quadratic_form_smul_re Q ‖x‖ y
        rw [h2] at this
        exact this
      rw [h3, mul_comm (‖x‖ ^ 2)]
      exact mul_le_mul_of_nonneg_right h1 (by positivity)
  · refine ⟨1, one_pos, fun x => ?_⟩
    have hx : x = 0 := by
      by_contra hx
      exact hne ⟨_, inv_norm_smul_mem_sphere x hx⟩
    subst hx
    simp

end UpperTheory.Reformulated.B.P6.r24a
end

section

namespace UpperTheory.Reformulated.B.P6.r22b

theorem one_add_pow_mul_exp_neg_le_of_mul_le (K : ℕ) {a β s : ℝ} (ha : 0 < a) (hKa : (K : ℝ) * a ≤ β) (hs : 0 ≤ s) :
    (1 + s) ^ K * Real.exp (-β * s) ≤ (1 + 1 / a) ^ K := by
  have e : 1 / a * (a * s) = s := by
    rw [← mul_assoc, one_div_mul_cancel ha.ne', one_mul]
  have has : 0 ≤ a * s := mul_nonneg ha.le hs
  have hia : 0 < 1 / a := one_div_pos.mpr ha
  have h1 : 1 + s ≤ (1 + 1 / a) * (1 + a * s) := by
    calc 1 + s ≤ 1 + a * s + 1 / a + 1 / a * (a * s) := by rw [e]; linarith
      _ = (1 + 1 / a) * (1 + a * s) := by ring
  have h2 : 1 + a * s ≤ Real.exp (a * s) := by
    linarith [Real.add_one_le_exp (a * s)]
  have h3 : (1 + s) ^ K ≤ (1 + 1 / a) ^ K * Real.exp (a * s) ^ K := by
    rw [← mul_pow]
    have h4 : 1 + s ≤ (1 + 1 / a) * Real.exp (a * s) :=
      le_trans h1 (mul_le_mul_of_nonneg_left h2 (by linarith))
    exact pow_le_pow_left₀ (by linarith) h4 K
  have h5 : Real.exp (a * s) ^ K * Real.exp (-β * s) ≤ 1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    rw [Real.exp_le_one_iff]
    have : (K : ℝ) * (a * s) = ((K : ℝ) * a) * s := by ring
    rw [this]
    nlinarith [mul_le_mul_of_nonneg_right hKa hs]
  have hc : 0 ≤ (1 + 1 / a) ^ K := pow_nonneg (by linarith) K
  have hE : 0 ≤ Real.exp (-β * s) := (Real.exp_pos _).le
  calc (1 + s) ^ K * Real.exp (-β * s)
      ≤ (1 + 1 / a) ^ K * Real.exp (a * s) ^ K * Real.exp (-β * s) :=
        mul_le_mul_of_nonneg_right h3 hE
    _ = (1 + 1 / a) ^ K * (Real.exp (a * s) ^ K * Real.exp (-β * s)) := by ring
    _ ≤ (1 + 1 / a) ^ K * 1 := mul_le_mul_of_nonneg_left h5 hc
    _ = (1 + 1 / a) ^ K := mul_one _

theorem PositivityTheory.Rg.Sw.FFTSteps.SecondLineEstimates.pow_mul_exp_le :
    ∀ (K : ℕ) {β : ℝ}, OfNat.ofNat (nat_lit 0) < β → ∃ (M : ℝ), ∀ (s : ℝ), OfNat.ofNat (nat_lit 0) ≤ s → (OfNat.ofNat (nat_lit 1) + s) ^ K * Real.exp (-β * s) ≤ M := by
  intro K β hβ
  have hK : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  have ha : 0 < β / ((K : ℝ) + 1) := div_pos hβ hK
  have hKa : (K : ℝ) * (β / ((K : ℝ) + 1)) ≤ β := by
    have e : ((K : ℝ) + 1) * (β / ((K : ℝ) + 1)) = β := by field_simp
    have : (K : ℝ) * (β / ((K : ℝ) + 1)) ≤ ((K : ℝ) + 1) * (β / ((K : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_right (by linarith) ha.le
    linarith
  exact ⟨_, fun s hs => one_add_pow_mul_exp_neg_le_of_mul_le K ha hKa hs⟩

end UpperTheory.Reformulated.B.P6.r22b
end

section

namespace UpperTheory.Reformulated.B.P6.r23b

theorem pow_mul_exp_le_half_exp (N : ℕ) (a : ℝ) (ha : 0 < a) :
    ∃ (C : ℝ), 0 ≤ C ∧ ∀ (x : ℝ), 0 ≤ x →
      (1 + x) ^ N * Real.exp (-(a * x)) ≤ C * Real.exp (-(a / 2 * x)) := by
  refine ⟨(2 / a) ^ N * (N.factorial : ℝ) * Real.exp (a / 2), by positivity, ?_⟩
  intro x hx
  have hy : 0 ≤ a / 2 * (1 + x) := by positivity
  have h1 : (a / 2 * (1 + x)) ^ N / (N.factorial : ℝ) ≤ Real.exp (a / 2 * (1 + x)) := Real.pow_div_factorial_le_exp (x := a / 2 * (1 + x)) (n := N) hy
  have hf : (0 : ℝ) < (N.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos N
  have h1' : (a / 2 * (1 + x)) ^ N ≤ Real.exp (a / 2 * (1 + x)) * (N.factorial : ℝ) :=
    (div_le_iff₀ hf).mp h1
  have h2 : (1 + x) ^ N = (2 / a) ^ N * (a / 2 * (1 + x)) ^ N := by
    rw [← mul_pow]
    congr 1
    field_simp
  have hp : (0 : ℝ) ≤ (2 / a) ^ N := by positivity
  have h3 : (1 + x) ^ N ≤ (2 / a) ^ N * (N.factorial : ℝ) * Real.exp (a / 2 * (1 + x)) := by
    rw [h2]
    have := mul_le_mul_of_nonneg_left h1' hp
    linarith [this]
  have h4 : Real.exp (a / 2 * (1 + x)) * Real.exp (-(a * x)) =
      Real.exp (a / 2) * Real.exp (-(a / 2 * x)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc (1 + x) ^ N * Real.exp (-(a * x))
      ≤ ((2 / a) ^ N * (N.factorial : ℝ) * Real.exp (a / 2 * (1 + x))) * Real.exp (-(a * x)) :=
        mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
    _ = (2 / a) ^ N * (N.factorial : ℝ) * (Real.exp (a / 2 * (1 + x)) * Real.exp (-(a * x))) := by ring
    _ = (2 / a) ^ N * (N.factorial : ℝ) * Real.exp (a / 2) * Real.exp (-(a / 2 * x)) := by
        rw [h4]; ring

theorem PositivityTheory.Rg.Sw.Glob.DCalcDH.poly_exp :
    ∀ (N : ℕ) (a : ℝ), OfNat.ofNat (nat_lit 0) < a → ∃ (C : ℝ), OfNat.ofNat (nat_lit 0) ≤ C ∧ ∀ (x : ℝ), OfNat.ofNat (nat_lit 0) ≤ x → (OfNat.ofNat (nat_lit 1) + x) ^ N * Real.exp (-(a * x)) ≤ C * Real.exp (-(a / OfNat.ofNat (nat_lit 2) * x)) := by
  intro N a ha
  exact pow_mul_exp_le_half_exp N a ha

end UpperTheory.Reformulated.B.P6.r23b
end

section

namespace UpperTheory.Reformulated.B.P6.r96a

open scoped MeasureTheory ENNReal LE HPow NPow Monoid Semiring CommSemiring HMul Distrib OfNat

theorem ennreal_sqrt_mul_sqrt (x : ENNReal) : x ^ (1/2 : ℝ) * x ^ (1/2 : ℝ) = x := by
  calc x ^ (1/2 : ℝ) * x ^ (1/2 : ℝ) = (x ^ (1/2 : ℝ)) ^ (2:ℕ) := (sq _).symm
    _ = (x ^ (1/2 : ℝ)) ^ ((2:ℕ):ℝ) := (ENNReal.rpow_natCast _ _).symm
    _ = x := by rw [← ENNReal.rpow_mul]; norm_num

theorem ennreal_sqrt_sq (x : ENNReal) : (x ^ (1/2 : ℝ)) ^ 2 = x := by
  rw [sq]; exact ennreal_sqrt_mul_sqrt x

theorem ennreal_rpow_two_eq_sq (x : ENNReal) : x ^ (2:ℝ) = x ^ 2 := by
  rw [← ENNReal.rpow_natCast]; norm_num

theorem GlobalTheory.CompanionTheory.Conc.WeightedCauchySchwarzLintegral.sq_lintegral_mul_le.{u_1} :
    ∀ {X : Type u_1} [inst_h0 : MeasurableSpace X] (ν : MeasureTheory.Measure X) {a b : X → ENNReal}, Measurable a → Measurable b → HPow.hPow (β := ℕ) (∫⁻ (w : X), a w * b w ∂ν) (OfNat.ofNat (nat_lit 2)) ≤ (∫⁻ (w : X), a w ∂ν) * ∫⁻ (w : X), a w * HPow.hPow (β := ℕ) (b w) (OfNat.ofNat (nat_lit 2)) ∂ν := by
  intro X _ ν a b ha hb
  have hf : AEMeasurable (fun w => a w ^ (1/2:ℝ)) ν := (ha.pow_const _).aemeasurable
  have hg : AEMeasurable (fun w => a w ^ (1/2:ℝ) * b w) ν := ((ha.pow_const _).mul hb).aemeasurable
  have key := ENNReal.lintegral_mul_le_Lp_mul_Lq ν (p := 2) (q := 2)
    Real.HolderConjugate.two_two hf hg
  have key2 : ∫⁻ w, a w * b w ∂ν ≤
      (∫⁻ w, a w ∂ν) ^ (1/(2:ℝ)) * (∫⁻ w, a w * b w ^ 2 ∂ν) ^ (1/(2:ℝ)) := by
    have h1 : ∫⁻ w, a w * b w ∂ν
        = ∫⁻ w, ((fun w => a w ^ (1/2:ℝ)) * (fun w => a w ^ (1/2:ℝ) * b w)) w ∂ν := by
      apply MeasureTheory.lintegral_congr
      intro w
      simp only [Pi.mul_apply]
      rw [← mul_assoc, ennreal_sqrt_mul_sqrt]
    have h2 : ∫⁻ w, a w ∂ν = ∫⁻ w, (a w ^ (1/2:ℝ)) ^ (2:ℝ) ∂ν := by
      apply MeasureTheory.lintegral_congr
      intro w
      rw [ennreal_rpow_two_eq_sq, ennreal_sqrt_sq]
    have h3 : ∫⁻ w, a w * b w ^ 2 ∂ν = ∫⁻ w, (a w ^ (1/2:ℝ) * b w) ^ (2:ℝ) ∂ν := by
      apply MeasureTheory.lintegral_congr
      intro w
      rw [ennreal_rpow_two_eq_sq, mul_pow, ennreal_sqrt_sq]
    rw [h1, h2, h3]
    exact key
  calc (∫⁻ w, a w * b w ∂ν) ^ 2
      ≤ ((∫⁻ w, a w ∂ν) ^ (1/(2:ℝ)) * (∫⁻ w, a w * b w ^ 2 ∂ν) ^ (1/(2:ℝ))) ^ 2 := by
        gcongr
    _ = (∫⁻ w, a w ∂ν) * ∫⁻ w, a w * b w ^ 2 ∂ν := by
        rw [mul_pow, ennreal_sqrt_sq, ennreal_sqrt_sq]

end UpperTheory.Reformulated.B.P6.r96a
end

section

namespace UpperTheory.Reformulated.B.P6.r03a

theorem integer_smul_eq_algebraMap_smul {K : Type} [Field K] [NumberField K] {n : ℕ}
    (r : NumberField.RingOfIntegers K) (x : Fin n → K) :
    r • x = (algebraMap (NumberField.RingOfIntegers K) K r) • x :=
  (algebraMap_smul K r x).symm

theorem GlobalTheory.CompanionTheory.Adelic.SatLine.exists_smul_mem :
    ∀ {K : Type} [inst : Field K] [NumberField K] {n : ℕ} (M : Submodule (NumberField.RingOfIntegers K) (Fin n → K)) {x : Fin n → K}, x ∈ Submodule.span K (SetLike.coe M) → ∃ (c : NumberField.RingOfIntegers K), c ≠ OfNat.ofNat (nat_lit 0) ∧ c • x ∈ M := by
  intro K _ _ n M x hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hy⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact M.zero_mem⟩
  | add y z _ _ hy hz =>
    obtain ⟨c1, hc1, h1⟩ := hy
    obtain ⟨c2, hc2, h2⟩ := hz
    refine ⟨c1 * c2, mul_ne_zero hc1 hc2, ?_⟩
    have e : (c1 * c2) • (y + z) = c2 • (c1 • y) + c1 • (c2 • z) := by
      rw [smul_add, mul_smul c1 c2 z, mul_comm c1 c2, mul_smul c2 c1 y]
    rw [e]
    exact M.add_mem (M.smul_mem c2 h1) (M.smul_mem c1 h2)
  | smul a y _ hy =>
    obtain ⟨c, hc, h⟩ := hy
    obtain ⟨⟨p, q⟩, hpq⟩ := IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers K)) a
    refine ⟨(q : NumberField.RingOfIntegers K) * c, mul_ne_zero (nonZeroDivisors.ne_zero q.2) hc, ?_⟩
    have hpq' : a * algebraMap (NumberField.RingOfIntegers K) K (q : NumberField.RingOfIntegers K)
        = algebraMap (NumberField.RingOfIntegers K) K p := hpq
    have e : ((q : NumberField.RingOfIntegers K) * c) • (a • y) = p • (c • y) := by
      rw [integer_smul_eq_algebraMap_smul ((q : NumberField.RingOfIntegers K) * c) (a • y), integer_smul_eq_algebraMap_smul p (c • y),
        integer_smul_eq_algebraMap_smul c y, smul_smul, smul_smul, map_mul, ← hpq']
      congr 1
      ring
    rw [e]
    exact M.smul_mem p h

end UpperTheory.Reformulated.B.P6.r03a
end
