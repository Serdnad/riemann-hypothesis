module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Algebra.Lie.UniversalEnveloping
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.Algebra.Module.LinearMap.Defs
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Topology.Constructions
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.LinearAlgebra.Isomorphisms

@[expose] public section

section

noncomputable def UpperTheory.Reformulated.B.DaGva8.prodE :
    {G₁ G₂ : Type} →
      [inst : Group G₁] →
        [inst_1 : TopologicalSpace G₁] →
          [inst_2 : Group G₂] →
            [inst_3 : TopologicalSpace G₂] → (T₁ : Subgroup G₁) → (T₂ : Subgroup G₂) → ↥T₁ × ↥T₂ ≃ₜ* ↥(T₁.prod T₂) :=
  fun {_ _} _ _ _ _ T₁ T₂ =>
    { toFun := fun x => ⟨(x.1.1, x.2.1), x.1.2, x.2.2⟩
      invFun := fun y => (⟨y.1.1, y.2.1⟩, ⟨y.1.2, y.2.2⟩)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      continuous_toFun :=
        ((continuous_subtype_val.comp continuous_fst).prodMk
          (continuous_subtype_val.comp continuous_snd)).subtype_mk _
      continuous_invFun :=
        ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
          ((continuous_snd.comp continuous_subtype_val).subtype_mk _) }
end

section

theorem UpperTheory.Reformulated.B.LocallyConstantOfKernelCapelliIdentities.locConst_of_ker :
    ∀ {G M : Type} [inst : Group G]
    [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] [inst_3 : Group M] (χ : G →* M),
    IsOpen (↑χ.ker : Set G) → IsLocallyConstant (⇑χ : G → M) := by
  intro G M _ _ _ _ χ h
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y => x⁻¹ * y) ⁻¹' (↑χ.ker : Set G),
    h.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · simp [MonoidHom.mem_ker]
  · intro y hy
    have hy' : χ (x⁻¹ * y) = 1 := MonoidHom.mem_ker.mp hy
    rw [map_mul, map_inv] at hy'
    exact (inv_mul_eq_one.mp hy').symm
end

section

theorem UpperTheory.Reformulated.B.LocallyConstantFunctions.locConst :
    ∀ {Γ A : Type} [inst : Group Γ] [inst_1 : TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [inst_3 : Group A] (ψ : Γ →* A), IsOpen (↑ψ.ker : Set Γ) → IsLocallyConstant (⇑ψ : Γ → A) := by
  intro Γ A _ _ _ _ ψ h
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y => x⁻¹ * y) ⁻¹' (↑ψ.ker : Set Γ),
    h.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · simp [MonoidHom.mem_ker]
  · intro y hy
    have hk : ψ (x⁻¹ * y) = 1 := MonoidHom.mem_ker.mp hy
    rw [map_mul, map_inv, inv_mul_eq_one] at hk
    exact hk.symm
end

section

theorem UpperTheory.Reformulated.B.LocallyConstantMaps.locConst :
    ∀ {Γ A : Type} [inst : Group Γ] [inst_1 : TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [inst_3 : Group A] (ψ : Γ →* A), IsOpen (↑ψ.ker : Set Γ) → IsLocallyConstant (⇑ψ : Γ → A) := by
  intro Γ A _ _ _ _ ψ h
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y => x⁻¹ * y) ⁻¹' (↑ψ.ker : Set Γ),
    h.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · simp [MonoidHom.mem_ker]
  · intro y hy
    have hy' : ψ (x⁻¹ * y) = 1 := MonoidHom.mem_ker.mp hy
    rw [map_mul, map_inv, inv_mul_eq_one] at hy'
    exact hy'.symm
end

section

theorem UpperTheory.Reformulated.B.LocallyConstantOfKernel.lc_of_ker :
    ∀ {Γ C : Type} [inst : Group Γ]
    [inst_1 : TopologicalSpace Γ] [IsTopologicalGroup Γ] [inst_3 : Group C] (η : Γ →* C),
    IsOpen (↑η.ker : Set Γ) → IsLocallyConstant (⇑η : Γ → C) := by
  intro Γ C _ _ _ _ η h
  refine (IsLocallyConstant.iff_exists_open _).2 fun x => ?_
  refine ⟨(fun y => x⁻¹ * y) ⁻¹' (η.ker : Set Γ),
    h.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · change x⁻¹ * x ∈ η.ker
    simp [MonoidHom.mem_ker]
  · intro y hy
    have hy' : η (x⁻¹ * y) = 1 := hy
    rw [map_mul, map_inv] at hy'
    exact (inv_mul_eq_one.mp hy').symm
end

section

theorem UpperTheory.Reformulated.B.LocallyConstantOfOpen.ho_locConst :
    ∀ {Γ A : Type} [inst : Group Γ] [inst_1 : TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [inst_3 : Group A] (ψ : Γ →* A), IsOpen (↑ψ.ker : Set Γ) → IsLocallyConstant (⇑ψ : Γ → A) := by
  intro Γ A _ _ _ _ ψ h
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y => x⁻¹ * y) ⁻¹' (ψ.ker : Set Γ),
    h.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · change x⁻¹ * x ∈ ψ.ker
    simp [MonoidHom.mem_ker]
  · intro y hy
    have hy' : ψ (x⁻¹ * y) = 1 := hy
    rw [map_mul, map_inv, inv_mul_eq_one] at hy'
    exact hy'.symm
end

section

theorem UpperTheory.Reformulated.B.LocallyConstantOfOpenSet.lc_of_open :
    ∀ {G H : Type} [inst : Group G] [inst_1 : TopologicalSpace G]
    [IsTopologicalGroup G] [inst_3 : Group H] (f : G →* H), IsOpen (↑f.ker : Set G) → IsLocallyConstant (⇑f : G → H) := by
  intro G H _ _ _ _ f hk
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hc : Continuous fun y : G => x⁻¹ * y := continuous_const.mul continuous_id
  have ho : IsOpen ((fun y : G => x⁻¹ * y) ⁻¹' (f.ker : Set G)) := hk.preimage hc
  have hx : x ∈ (fun y : G => x⁻¹ * y) ⁻¹' (f.ker : Set G) := by
    simp [Set.mem_preimage, MonoidHom.mem_ker]
  filter_upwards [ho.mem_nhds hx] with y hy
  have h1 : f (x⁻¹ * y) = 1 := MonoidHom.mem_ker.mp hy
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1.symm
end

section

theorem UpperTheory.Reformulated.B.LocallyConstantOpenPreimage.lc_of_open :
    ∀ {Γ A : Type} [inst : Group Γ] [inst_1 : TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [inst_3 : Group A] (ψ : Γ →* A), IsOpen (↑ψ.ker : Set Γ) → IsLocallyConstant (⇑ψ : Γ → A) := by
  intro Γ A _ _ _ _ ψ h
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y => x⁻¹ * y) ⁻¹' (ψ.ker : Set Γ),
    h.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · simp [MonoidHom.mem_ker]
  · intro y hy
    have hk : ψ (x⁻¹ * y) = 1 := MonoidHom.mem_ker.mp hy
    rw [map_mul, map_inv] at hk
    exact (inv_mul_eq_one.mp hk).symm
end

section

namespace UpperTheory.Reformulated.B.Qi43

theorem pb_mem {B C : Type} [Group B] [Group C] (J : B →* C) (UQ : Subgroup C)
    (hc : ∀ u ∈ UQ, ∀ g : B, Commute u (J g)) (K : Subgroup B) (x : C) :
    x ∈ UQ ⊔ Subgroup.map J K ↔ ∃ u ∈ UQ, ∃ k ∈ K, x = u * J k := by
  constructor
  · intro hx
    rw [Subgroup.sup_eq_closure] at hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with hy | hy
      · exact ⟨y, hy, 1, K.one_mem, by simp⟩
      · obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hy
        exact ⟨1, UQ.one_mem, k, hk, by simp⟩
    | one => exact ⟨1, UQ.one_mem, 1, K.one_mem, by simp⟩
    | mul y z _ _ hy hz =>
      obtain ⟨u, hu, k, hk, rfl⟩ := hy
      obtain ⟨v, hv, l, hl, rfl⟩ := hz
      refine ⟨u * v, UQ.mul_mem hu hv, k * l, K.mul_mem hk hl, ?_⟩
      rw [map_mul, mul_assoc, ← mul_assoc (J k), ← (hc v hv k).eq]
      simp only [mul_assoc]
    | inv y _ hy =>
      obtain ⟨u, hu, k, hk, rfl⟩ := hy
      refine ⟨u⁻¹, UQ.inv_mem hu, k⁻¹, K.inv_mem hk, ?_⟩
      rw [(hc u hu k).eq, mul_inv_rev, map_inv]
  · rintro ⟨u, hu, k, hk, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hu)
      (Subgroup.mem_sup_right (Subgroup.mem_map_of_mem J hk))

end UpperTheory.Reformulated.B.Qi43
end

section

namespace UpperTheory.Reformulated.B.Qk36

@[reducible] noncomputable def gl : ℕ → Type :=
  fun n => Matrix (Fin n) (Fin n) ℂ

@[reducible] noncomputable def U : ℕ → Type :=
  fun n => by
    letI : LieRing (gl n) := LieRing.ofAssociativeRing
    letI : LieAlgebra ℂ (gl n) := LieAlgebra.ofAssociativeAlgebra
    exact UniversalEnvelopingAlgebra ℂ (gl n)

noncomputable def E : {n : ℕ} → Fin n × Fin n → gl n :=
  fun {n} a => Matrix.single a.1 a.2 1

noncomputable def e : {n : ℕ} → Fin n × Fin n → U n :=
  fun {n} a => by
    letI : LieRing (gl n) := LieRing.ofAssociativeRing
    letI : LieAlgebra ℂ (gl n) := LieAlgebra.ofAssociativeAlgebra
    exact UniversalEnvelopingAlgebra.ι ℂ (E a)

noncomputable def capelliMatrix : {n : ℕ} →
  Matrix (Fin n) (Fin n) (U n) :=
  fun {n} i j => e (i, j)

private theorem commutator_matrix_pow {R : Type*} [Ring R] {n : Nat}
    (M : Matrix (Fin n) (Fin n) R) (x : R) (a b : Fin n)
    (h : ∀ c d, x * M c d - M c d * x
      = (if b = c then M a d else 0) - (if d = a then M c b else 0))
    (k : Nat) (c d : Fin n) :
    x * (M ^ k) c d - (M ^ k) c d * x
      = (if b = c then (M ^ k) a d else 0) - (if d = a then (M ^ k) c b else 0) := by
  induction k generalizing d with
  | zero =>
    simp only [pow_zero, Matrix.one_apply, mul_ite, ite_mul, mul_one, one_mul, mul_zero, zero_mul,
      sub_self]
    by_cases h1 : b = c <;> by_cases h2 : d = a <;> simp [h1, h2, eq_comm (a := a), eq_comm (a := c)]
  | succ k ih =>
    have key : ∀ j, x * ((M ^ k) c j * M j d) - (M ^ k) c j * M j d * x
        = ((if b = c then (M ^ k) a j else 0) - (if j = a then (M ^ k) c b else 0)) * M j d
          + (M ^ k) c j * ((if b = j then M a d else 0) - (if d = a then M j b else 0)) := by
      intro j
      rw [← ih j, ← h j d]
      noncomm_ring
    simp only [pow_succ, Matrix.mul_apply]
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib,
      Finset.sum_congr rfl (fun j _ => key j)]
    simp only [sub_mul, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, ite_mul, mul_ite,
      zero_mul, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    by_cases h1 : b = c <;> by_cases h2 : d = a <;>
      simp only [h1, h2, if_true, if_false, Finset.sum_const_zero] <;> abel

private theorem E_comm {n : Nat} (a b c d : Fin n) :
    E (a, b) * E (c, d)
        - E (c, d) * E (a, b)
      = (if b = c then E (a, d) else 0)
        - (if d = a then E (c, b) else 0) := by
  have h : ∀ p q r s : Fin n, E (p, q) * E (r, s)
      = if q = r then E (p, s) else 0 := by
    intro p q r s
    unfold E
    split_ifs with hqr
    · subst hqr
      simp
    · exact Matrix.single_mul_single_of_ne _ _ _ _ hqr _
  rw [h, h]

private theorem e_comm {n : Nat} (a b c d : Fin n) :
    e (a, b) * e (c, d)
        - e (c, d) * e (a, b)
      = (if b = c then e (a, d) else 0)
        - (if d = a then e (c, b) else 0) := by
  letI : LieRing (gl n) := LieRing.ofAssociativeRing
  letI : LieRing (U n) := LieRing.ofAssociativeRing
  unfold e
  rw [← LieRing.of_associative_ring_bracket, ← LieHom.map_lie,
    LieRing.of_associative_ring_bracket, E_comm, map_sub]
  congr 1 <;> split_ifs <;> first | rfl | exact map_zero _

theorem e_mul_sub_mul_capelliMatrix_pow : ∀ {n : ℕ} (a b : Fin n) (k : ℕ) (c d : Fin n),
  e (a, b) * (capelliMatrix ^ k) c d -
      (capelliMatrix ^ k) c d * e (a, b) =
    (if b = c then (capelliMatrix ^ k) a d else 0) -
      if d = a then (capelliMatrix ^ k) c b else 0 := by
  intro n a b k c d
  exact commutator_matrix_pow capelliMatrix _ a b
    (fun c d => e_comm a b c d) k c d

end UpperTheory.Reformulated.B.Qk36
end

section

theorem UpperTheory.Reformulated.B.ExistsSmulMemOfIsLattice₂.dual_lattice_denom :
    ∀ {A : Type} [inst : CommRing A]
    [IsDomain A] {F V : Type} [inst_2 : Field F] [inst_3 : Algebra A F] [IsFractionRing A F] [inst_5 : AddCommGroup V]
    [inst_6 : _root_.Module F V] [inst_7 : _root_.Module A V] [inst_8 : IsScalarTower A F V] (Y : Submodule A V),
    Submodule.IsFullLattice F Y → ∀ (z : V), ∃ (a : A), a ≠ (0 : A) ∧ a • z ∈ Y := by
  intro A _ _ F V _ _ _ _ _ _ _ Y hY z
  have hz : z ∈ Submodule.span F (Y : Set V) := by
    rw [hY.span_eq_top]; exact Submodule.mem_top
  induction hz using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine Y.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact Y.smul_mem b hax
    · rw [mul_smul]; exact Y.smul_mem a hby
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨⟨d, hd⟩, n, hn⟩ := IsLocalization.exists_integer_multiple (nonZeroDivisors A) c
    refine ⟨a * d, mul_ne_zero ha (nonZeroDivisors.ne_zero hd), ?_⟩
    have h : (a * d) • c • x = n • a • x := by
      rw [mul_smul, ← smul_assoc d c x]
      have h2 : d • c = algebraMap A F n := hn.symm
      rw [h2, algebraMap_smul, smul_comm]
    rw [h]
    exact Y.smul_mem n hax
end

section

theorem UpperTheory.Reformulated.B.Qf12.lift_ex :
    ∀ {A M Q Q' : Type} [inst : CommRing A] [inst_1 : AddCommGroup M]
    [inst_2 : AddCommGroup Q] [inst_3 : AddCommGroup Q'] [inst_4 : _root_.Module A M] [inst_5 : _root_.Module A Q]
    [inst_6 : _root_.Module A Q'] (π : M →ₗ[A] Q),
    Function.Surjective (⇑π : M → Q) →
      ∀ (g : M →ₗ[A] Q'),
        (∀ (m : M), (π : M → Q) m = (0 : Q) → (g : M → Q') m = (0 : Q')) →
          ∃ (q : Q →ₗ[A] Q'), ∀ (m : M), (q : Q → Q') ((π : M → Q) m) = (g : M → Q') m := by
  intro A M Q Q' _ _ _ _ _ _ _ π hπ g hg
  have hle : LinearMap.ker π ≤ LinearMap.ker g := fun m hm =>
    LinearMap.mem_ker.mpr (hg m (LinearMap.mem_ker.mp hm))
  refine ⟨((LinearMap.ker π).liftQ g hle).comp
    (π.quotKerEquivOfSurjective hπ).symm.toLinearMap, fun m => ?_⟩
  have h : (π.quotKerEquivOfSurjective hπ).symm (π m) = Submodule.Quotient.mk m := by
    rw [LinearEquiv.symm_apply_eq]
    rfl
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, h, Submodule.liftQ_apply]
end
