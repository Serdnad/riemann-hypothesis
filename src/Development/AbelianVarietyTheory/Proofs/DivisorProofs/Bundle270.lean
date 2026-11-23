module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle159
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PtOrderProdSub

@[expose] public section

section

set_option autoImplicit false

open CategoryTheory GlobalTheory.CxCoh

namespace GlobalTheory.CxCoh.QAtFormal

universe u

variable {C : Type u} [Category.{0} C] (K : Cx C)

theorem qAt_ident (T : C) : K.QAt (𝟙 T) := by
  refine ⟨fun x _ h => ?_, fun y hy => ⟨y, hy, ?_⟩, fun x y _ h => ⟨y, ?_⟩, fun y hy => ⟨y, 0, hy, ?_⟩,
    fun x y _ h => ⟨y, ?_⟩, fun y hy => ⟨y, 0, hy, ?_⟩⟩
  · rwa [K.M0.map_id] at h
  · exact K.M0.map_id T y
  · rw [K.M1.map_id] at h; exact h.symm
  · rw [K.M1.map_id, map_zero, add_zero]
  · rw [K.M2.map_id] at h; exact h.symm
  · rw [K.M2.map_id, map_zero, add_zero]

theorem qAt_comp {T T' T'' : C} (a : T ⟶ T') (b : T' ⟶ T'') (ha : K.QAt a) (hb : K.QAt b) :
    K.QAt (a ≫ b) := by
  refine ⟨fun x hx h => ?_, fun y hy => ?_, fun x y hx h => ?_, fun y hy => ?_,
    fun x y hx h => ?_, fun y hy => ?_⟩
  · rw [K.M0.map_comp] at h
    exact ha.inj0 x hx (hb.inj0 _ (by rw [K.diffZero_natural, hx, map_zero]) h)
  · obtain ⟨x', hx', rfl⟩ := hb.surj0 y hy
    obtain ⟨x, hx, rfl⟩ := ha.surj0 x' hx'
    exact ⟨x, hx, K.M0.map_comp a b x⟩
  · rw [K.M1.map_comp] at h
    obtain ⟨w', hw'⟩ := hb.inj1 _ y (by rw [K.diffOne_natural, hx, map_zero]) h
    exact ha.inj1 x w' hx hw'.symm
  · obtain ⟨x', w', hx', rfl⟩ := hb.surj1 y hy
    obtain ⟨x, w, hx, rfl⟩ := ha.surj1 x' hx'
    refine ⟨x, K.M0.map b w + w', hx, ?_⟩
    simp only [map_add (f := _), K.M1.map_comp, K.diffZero_natural]
    abel
  · rw [K.M2.map_comp] at h
    obtain ⟨w', hw'⟩ := hb.inj2 _ y (by rw [K.diffTwo_natural, hx, map_zero]) h
    exact ha.inj2 x w' hx hw'.symm
  · obtain ⟨x', w', hx', rfl⟩ := hb.surj2 y hy
    obtain ⟨x, w, hx, rfl⟩ := ha.surj2 x' hx'
    refine ⟨x, K.M1.map b w + w', hx, ?_⟩
    simp only [map_add (f := _), K.M2.map_comp, K.diffOne_natural]
    abel

theorem qAt_of_comp_retract {T T' T'' : C} (a : T ⟶ T') (b : T' ⟶ T'') (c : T'' ⟶ T')
    (hbc : b ≫ c = 𝟙 T') (h : K.QAt (a ≫ b)) : K.QAt a := by
  have e0 : ∀ y, K.M0.map c (K.M0.map b y) = y := fun y => by
    rw [← K.M0.map_comp, hbc, K.M0.map_id]
  have e1 : ∀ y, K.M1.map c (K.M1.map b y) = y := fun y => by
    rw [← K.M1.map_comp, hbc, K.M1.map_id]
  have e2 : ∀ y, K.M2.map c (K.M2.map b y) = y := fun y => by
    rw [← K.M2.map_comp, hbc, K.M2.map_id]
  refine ⟨fun x hx hax => ?_, fun y hy => ?_, fun x y hx hxy => ?_, fun y hy => ?_,
    fun x y hx hxy => ?_, fun y hy => ?_⟩
  · exact h.inj0 x hx (by rw [K.M0.map_comp, hax, map_zero])
  · obtain ⟨x, hx, hxy⟩ := h.surj0 (K.M0.map b y) (by rw [K.diffZero_natural, hy, map_zero])
    refine ⟨x, hx, ?_⟩
    rw [K.M0.map_comp] at hxy
    simpa only [e0] using congrArg (K.M0.map c) hxy
  · exact h.inj1 x (K.M0.map b y) hx (by rw [K.M1.map_comp, hxy, K.diffZero_natural])
  · obtain ⟨x, w, hx, hw⟩ := h.surj1 (K.M1.map b y) (by rw [K.diffOne_natural, hy, map_zero])
    refine ⟨x, K.M0.map c w, hx, ?_⟩
    have := congrArg (K.M1.map c) hw
    rw [map_add (f := _), K.M1.map_comp, e1, e1, ← K.diffZero_natural] at this
    exact this
  · exact h.inj2 x (K.M1.map b y) hx (by rw [K.M2.map_comp, hxy, K.diffOne_natural])
  · obtain ⟨x, w, hx, hw⟩ := h.surj2 (K.M2.map b y) (by rw [K.diffTwo_natural, hy, map_zero])
    refine ⟨x, K.M1.map c w, hx, ?_⟩
    have := congrArg (K.M2.map c) hw
    rw [map_add (f := _), K.M2.map_comp, e2, e2, ← K.diffOne_natural] at this
    exact this

theorem qAt_of_isIso {T T' : C} (a : T ⟶ T') [IsIso a] : K.QAt a :=
  qAt_of_comp_retract K a (inv a) a (IsIso.inv_hom_id a) (by rw [IsIso.hom_inv_id]; exact qAt_ident K T)

theorem qAt_formal : ∀ (C : Type 1) [Category.{0} C] (K : Cx C),
    (∀ (T T' : C) (a : T ⟶ T') [IsIso a], K.QAt a) ∧
    (∀ (T T' T'' : C) (a : T ⟶ T') (b : T' ⟶ T''), K.QAt a → K.QAt b → K.QAt (a ≫ b)) ∧
    ∀ (T T' T'' : C) (a : T ⟶ T') (b : T' ⟶ T'') (c : T'' ⟶ T'), b ≫ c = 𝟙 T' → K.QAt (a ≫ b) → K.QAt a :=
  fun _ _ K => ⟨fun _ _ a _ => qAt_of_isIso K a, fun _ _ _ a b => qAt_comp K a b,
    fun _ _ _ a b c => qAt_of_comp_retract K a b c⟩

end GlobalTheory.CxCoh.QAtFormal
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace GlobalTheory.CxCoh

namespace CxMap

universe a b

variable {C : Type a} [Category.{0} C] {C' : Type b} [Category.{0} C'] {K : Cx C} {K' : Cx C'}

theorem h0_eq_of_joined (m m' : CxMap K K') (θ : m.G ⟶ m'.G) (hj : m.Joined m' θ) (c : K.H0) :
    m.h0 c = m'.h0 c := by
  obtain ⟨g, hg⟩ := c
  have hg' : K.D0 g = 0 := hg
  have hc : ∀ T T' (φ : T ⟶ T'), g T' = K.M0.map φ (g T) := fun T T' φ => by
    have h := congrArg (fun c => c.1 T T' φ) hg'
    change g T' - K.M0.map φ (g T) = 0 at h
    exact sub_eq_zero.mp h
  apply Subtype.ext
  funext T
  change m.a0 T (g _) = m'.a0 T (g _)
  rw [hc _ _ (θ.app T), hj.e0]

theorem p1_eq_add_D0_of_joined_of_cocycle (m m' : CxMap K K') (θ : m.G ⟶ m'.G) (hj : m.Joined m' θ) (c : K.T1)
    (hc : K.D1 c = 0) :
    m'.p1 c = m.p1 c + K'.D0 (fun T => m'.a0 T (c.1 _ _ (θ.app T))) := by
  have e1 : ∀ A A' A'' (α : A ⟶ A') (β : A' ⟶ A''),
      c.1 A A'' (α ≫ β) = K.M0.map β (c.1 A A' α) + c.1 A' A'' β := by
    intro A A' A'' α β
    have h := congrArg (fun x => x.1 A A' A'' α β) hc
    change K.M0.map β (c.1 A A' α) - c.1 A A'' (α ≫ β) + c.1 A' A'' β = 0 at h
    linear_combination (norm := abel1) -h
  have e2 : ∀ A A' (α : A ⟶ A'), c.2 A' = K.M1.map α (c.2 A) + K.d0 A' (c.1 A A' α) := by
    intro A A' α
    have h := congrArg (fun x => x.2.1 A A' α) hc
    change c.2 A' - K.M1.map α (c.2 A) - K.d0 A' (c.1 A A' α) = 0 at h
    linear_combination (norm := abel1) h
  refine Prod.ext ?_ ?_
  · funext T T' φ
    change m'.a0 T' (c.1 _ _ (m'.G.map φ)) = m.a0 T' (c.1 _ _ (m.G.map φ)) +
      (m'.a0 T' (c.1 _ _ (θ.app T')) - K'.M0.map φ (m'.a0 T (c.1 _ _ (θ.app T))))
    have k1 := e1 _ _ _ (m.G.map φ) (θ.app T')
    have k2 := e1 _ _ _ (θ.app T) (m'.G.map φ)
    rw [θ.naturality φ] at k1
    have k := congrArg (m'.a0 T') (k1.symm.trans k2)
    rw [map_add (f := _), map_add (f := _), hj.e0, m'.compDegreeZero_natural] at k
    linear_combination (norm := abel1) -k
  · funext T
    change m'.a1 T (c.2 _) = m.a1 T (c.2 _) + K'.d0 T (m'.a0 T (c.1 _ _ (θ.app T)))
    rw [e2 _ _ (θ.app T), map_add (f := _), hj.e1, m'.comp_commutes_diffZero]

theorem h1_eq_of_joined (m m' : CxMap K K') (θ : m.G ⟶ m'.G) (hj : m.Joined m' θ) (c : K.H1) :
    m.h1 c = m'.h1 c := by
  obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientAddGroup.mk_surjective c
  change (QuotientAddGroup.mk (m.z1 ⟨x, hx⟩) : K'.H1) = QuotientAddGroup.mk (m'.z1 ⟨x, hx⟩)
  rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
  refine ⟨fun T => m'.a0 T (x.1 _ _ (θ.app T)), ?_⟩
  have h := p1_eq_add_D0_of_joined_of_cocycle m m' θ hj x (AddMonoidHom.mem_ker.mp hx)
  change _ = -(m.p1 x) + m'.p1 x
  rw [h]; abel

end CxMap

theorem joinedOne_cohomology.{a, b} : JoinedOne.{a, b} := fun m m' θ hj =>
  ⟨CxMap.h0_eq_of_joined m m' θ hj, CxMap.h1_eq_of_joined m m' θ hj⟩

theorem joinedOne_inst : JoinedOne.{1, 1} ∧ JoinedOne.{1, 0} ∧ JoinedOne.{0, 0} :=
  ⟨joinedOne_cohomology, joinedOne_cohomology, joinedOne_cohomology⟩

end GlobalTheory.CxCoh
end
end

section

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.LowU

noncomputable section

variable {C : Type} [Field C]

def intSubring (v : AddValuation C (WithTop ℝ)) : Subring C where
  carrier := {x | 0 ≤ v x}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, AddValuation.map_mul] at *
    exact add_nonneg ha hb
  one_mem' := by simp [AddValuation.map_one]
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    exact le_trans (le_min ha hb) (v.map_add a b)
  zero_mem' := by simp [AddValuation.map_zero]
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq, AddValuation.map_neg] at *
    exact ha

theorem isIntV_iff (v : AddValuation C (WithTop ℝ)) (x : C) : IsIntV v x ↔ x ∈ intSubring v :=
  Iff.rfl

theorem int_of_le (v : AddValuation C (WithTop ℝ)) {a b : C} (hb : b ≠ 0)
    (h : v b ≤ v (a * b)) : IsIntV v a := by
  show 0 ≤ v a
  rw [AddValuation.map_mul] at h
  have hb' : v b ≠ ⊤ := fun h' => hb ((AddValuation.top_iff v).1 h')
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 hb'
  rcases eq_or_ne (v a) ⊤ with ha | ha
  · rw [ha]; exact le_top
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 ha
  rw [← hr, ← hs, ← WithTop.coe_add, WithTop.coe_le_coe] at h
  rw [← hs]
  exact_mod_cast (by linarith : (0 : ℝ) ≤ s)

end

end GlobalTheory.LowU

namespace GlobalTheory.LowU

noncomputable section

variable {C : Type} [Field C]

def Reduces (v : AddValuation C (WithTop ℝ)) {i n : ℕ} (M : Matrix (Fin i) (Fin n) C) : Prop :=
  ∃ (g : Matrix (Fin i) (Fin i) C) (cr : ℕ), cr ≤ i ∧ cr ≤ n ∧ (∀ a b, IsIntV v (g a b)) ∧
    v g.det = 0 ∧ ∀ a : Fin i, cr ≤ a.val → ∀ e, (g * M) a e = 0

theorem pivot_step (v : AddValuation C (WithTop ℝ)) {i' n : ℕ}
    (ih : ∀ M' : Matrix (Fin i') (Fin n) C, Reduces v M')
    (M : Matrix (Fin (i' + 1)) (Fin (n + 1)) C) (h0 : M 0 0 ≠ 0)
    (hmin : ∀ b, v (M 0 0) ≤ v (M b 0)) : Reduces v M := by
  have hq : ∀ c : Fin i', IsIntV v (M c.succ 0 / M 0 0) := fun c =>
    int_of_le v h0 (by rw [div_mul_cancel₀ _ h0]; exact hmin c.succ)
  obtain ⟨g', cr', hc1, hc2, hint, hdet, hz⟩ :=
    ih (Matrix.of fun c e' => M c.succ e'.succ - M c.succ 0 / M 0 0 * M 0 e'.succ)
  have hw : ∀ a'', IsIntV v (-∑ c, g' a'' c * (M c.succ 0 / M 0 0)) := fun a'' =>
    (isIntV_iff v _).2 (neg_mem (Subring.sum_mem _ fun c _ =>
      mul_mem ((isIntV_iff v _).1 (hint a'' c)) ((isIntV_iff v _).1 (hq c))))
  refine ⟨Matrix.of fun a b => Fin.cases (motive := fun _ => C)
      (Fin.cases (motive := fun _ => C) 1 (fun _ => 0) b)
      (fun a'' => Fin.cases (motive := fun _ => C) (-∑ c, g' a'' c * (M c.succ 0 / M 0 0))
        (fun b'' => g' a'' b'') b) a,
    cr' + 1, by omega, by omega, ?_, ?_, ?_⟩
  · intro a b
    cases a using Fin.cases <;> cases b using Fin.cases <;>
      simp only [Matrix.of_apply, Fin.cases_zero, Fin.cases_succ]
    · simp [IsIntV]
    · simp [IsIntV]
    · exact hw _
    · exact hint _ _
  · have hsub : (Matrix.of fun a b => Fin.cases (motive := fun _ => C)
        (Fin.cases (motive := fun _ => C) 1 (fun _ => 0) b)
        (fun a'' => Fin.cases (motive := fun _ => C) (-∑ c, g' a'' c * (M c.succ 0 / M 0 0))
          (fun b'' => g' a'' b'') b) a).submatrix Fin.succ Fin.succ = g' := by
      ext a b
      simp
    rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
    simp only [Matrix.of_apply, Fin.cases_zero, Fin.cases_succ, Fin.succAbove_zero, hsub,
      mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero, one_mul]
    exact hdet
  · intro a ha e
    obtain ⟨a'', rfl⟩ := Fin.exists_succ_eq.2 (show a ≠ 0 by rintro rfl; simp at ha)
    have ha' : cr' ≤ a''.val := by rw [Fin.val_succ] at ha; omega
    rw [Matrix.mul_apply, Fin.sum_univ_succ]
    simp only [Matrix.of_apply, Fin.cases_zero, Fin.cases_succ]
    cases e using Fin.cases with
    | zero =>
      rw [neg_mul, Finset.sum_mul, neg_add_eq_zero]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [mul_assoc, div_mul_cancel₀ _ h0]
    | succ e' =>
      have h1 := hz a'' ha' e'
      simp only [Matrix.mul_apply, Matrix.of_apply, mul_sub, Finset.sum_sub_distrib] at h1
      have e1 : ∑ c, g' a'' c * (M c.succ 0 / M 0 0 * M 0 e'.succ) =
          (∑ c, g' a'' c * (M c.succ 0 / M 0 0)) * M 0 e'.succ := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun c _ => by ring
      rw [e1] at h1
      linear_combination h1

end

end GlobalTheory.LowU

namespace GlobalTheory.LowU

noncomputable section

variable {C : Type} [Field C]

theorem one_int (v : AddValuation C (WithTop ℝ)) {i : ℕ} (a b : Fin i) :
    IsIntV v ((1 : Matrix (Fin i) (Fin i) C) a b) := by
  show 0 ≤ v _
  by_cases h : a = b
  · subst h
    simp
  · simp [Matrix.one_apply_ne h]

theorem reduces_all (v : AddValuation C (WithTop ℝ)) :
    ∀ (n i : ℕ) (M : Matrix (Fin i) (Fin n) C), Reduces v M := by
  intro n
  induction n with
  | zero =>
    intro i M
    exact ⟨1, 0, Nat.zero_le _, le_rfl, one_int v, by simp, fun a _ e => e.elim0⟩
  | succ n ih =>
    intro i M
    cases i with
    | zero => exact ⟨1, 0, le_rfl, Nat.zero_le _, one_int v, by simp, fun a _ => a.elim0⟩
    | succ i' =>
      obtain ⟨b0, -, hb0⟩ :=
        Finset.univ.exists_min_image (fun b => v (M b 0)) Finset.univ_nonempty
      by_cases h0 : M b0 0 = 0
      · have hcol : ∀ b, M b 0 = 0 := fun b => by
          have hb := hb0 b (Finset.mem_univ _)
          rw [h0, AddValuation.map_zero, top_le_iff] at hb
          exact (AddValuation.top_iff v).1 hb
        obtain ⟨g, cr, h1, h2, hint, hdet, hz⟩ := ih (i' + 1) (Matrix.of fun a e => M a e.succ)
        refine ⟨g, cr, h1, by omega, hint, hdet, fun a ha e => ?_⟩
        cases e using Fin.cases with
        | zero => simp [Matrix.mul_apply, hcol]
        | succ e' => simpa [Matrix.mul_apply] using hz a ha e'
      · obtain ⟨g1, cr, h1, h2, hint, hdet, hz⟩ := pivot_step v (ih i')
          (M.submatrix (Equiv.swap 0 b0) id) (by simpa using h0)
          (fun b => by simpa using hb0 _ (Finset.mem_univ _))
        refine ⟨g1.submatrix id (Equiv.swap 0 b0), cr, h1, h2, fun a b => hint _ _, ?_,
          fun a ha e => ?_⟩
        · rw [Matrix.det_permute', AddValuation.map_mul, hdet, add_zero]
          rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap (0 : Fin (i' + 1)) b0)) with
            h | h <;> simp [h]
        · have key : ∑ b, g1 a (Equiv.swap 0 b0 b) * M b e =
              ∑ b, g1 a b * M (Equiv.swap 0 b0 b) e := by
            rw [← Equiv.sum_comp (Equiv.swap 0 b0) (fun b => g1 a b * M (Equiv.swap 0 b0 b) e)]
            simp [Equiv.swap_apply_self]
          simpa [Matrix.mul_apply, key] using hz a ha e

end

end GlobalTheory.LowU

theorem GlobalTheory.LowU.adapted_basis : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ))
    (i d : ℕ) (u : Fin i → Fin d → C) (S : Finset (Fin d)), IsSatFrame v u →
    ∃ (g : Matrix (Fin i) (Fin i) C) (cr : ℕ), cr ≤ i ∧ cr ≤ S.card ∧ (∀ a b, IsIntV v (g a b)) ∧
      v g.det = 0 ∧ ∀ a : Fin i, cr ≤ a.val → ∀ e ∈ S, ∑ a', g a a' * u a' e = 0 := by
  intro C _ _ v i d u S _
  obtain ⟨g, cr, h1, h2, hint, hdet, hz⟩ := GlobalTheory.LowU.reduces_all v S.card i
    (Matrix.of fun a k => u a (S.equivFin.symm k))
  refine ⟨g, cr, h1, h2, hint, hdet, fun a ha e he => ?_⟩
  simpa [Matrix.mul_apply] using hz a ha (S.equivFin ⟨e, he⟩)
end

section

open MvPowerSeries ReciprocityTheory.PGsh GlobalTheory.FGDepth

namespace GlobalTheory.FGDepth

theorem exists_lipschitz_eval {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {ι : Type}
    (Q : MvPolynomial ι C) :
    ∃ K : ℝ, (∀ a : ι → C, (∀ i, IsIntV v (a i)) →
        ((-K : ℝ) : WithTop ℝ) ≤ v (MvPolynomial.eval a Q)) ∧
      ∀ (M : ℝ) (a a' : ι → C), (∀ i, IsIntV v (a i)) → (∀ i, IsIntV v (a' i)) →
        (∀ i, ((M : ℝ) : WithTop ℝ) ≤ v (a i - a' i)) →
        ((M - K : ℝ) : WithTop ℝ) ≤ v (MvPolynomial.eval a Q - MvPolynomial.eval a' Q) := by
  induction Q using MvPolynomial.induction_on with
  | C c =>
    by_cases hc : v c = ⊤
    · exact ⟨0, fun a _ => by simp [hc], fun M a a' _ _ _ => by simp⟩
    · obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hc
      exact ⟨-r, fun a _ => by simp [hr], fun M a a' _ _ _ => by simp⟩
  | add p q hp hq =>
    obtain ⟨K₁, h₁, h₁'⟩ := hp
    obtain ⟨K₂, h₂, h₂'⟩ := hq
    refine ⟨max K₁ K₂, fun a ha => ?_, fun M a a' ha ha' hM => ?_⟩
    · rw [map_add (f := _)]
      refine v.map_le_add (le_trans ?_ (h₁ a ha)) (le_trans ?_ (h₂ a ha))
      · exact WithTop.coe_le_coe.mpr (neg_le_neg (le_max_left _ _))
      · exact WithTop.coe_le_coe.mpr (neg_le_neg (le_max_right _ _))
    · rw [map_add (f := _), map_add (f := _), add_sub_add_comm]
      refine v.map_le_add (le_trans ?_ (h₁' M a a' ha ha' hM))
        (le_trans ?_ (h₂' M a a' ha ha' hM))
      · exact WithTop.coe_le_coe.mpr (sub_le_sub_left (le_max_left _ _) _)
      · exact WithTop.coe_le_coe.mpr (sub_le_sub_left (le_max_right _ _) _)
  | mul_X p i hp =>
    obtain ⟨K, h, h'⟩ := hp
    refine ⟨K, fun a ha => ?_, fun M a a' ha ha' hM => ?_⟩
    · rw [map_mul, MvPolynomial.eval_X, v.map_mul]
      exact le_add_of_le_of_nonneg (h a ha) (ha i)
    · rw [map_mul, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_X]
      have e : MvPolynomial.eval a p * a i - MvPolynomial.eval a' p * a' i =
          (MvPolynomial.eval a p - MvPolynomial.eval a' p) * a i +
            MvPolynomial.eval a' p * (a i - a' i) := by ring
      rw [e]
      refine v.map_le_add ?_ ?_
      · rw [v.map_mul]
        exact le_add_of_le_of_nonneg (h' M a a' ha ha' hM) (ha i)
      · rw [v.map_mul]
        have e2 : ((M - K : ℝ) : WithTop ℝ) = ((-K : ℝ) : WithTop ℝ) + ((M : ℝ) : WithTop ℝ) := by
          rw [← WithTop.coe_add]; congr 1; ring
        rw [e2]
        exact add_le_add (h a' ha') (hM i)

theorem exists_poly_derivAt0_subst {C : Type} [Field C] {σ Λ : Type} [Fintype σ] [Fintype Λ]
    (P : MvPolynomial Λ C) (Z : MvPowerSeries σ C) :
    ∃ Q : MvPolynomial (σ × Λ) C, ∀ a : σ → Λ → C,
      derivAt0 P (MvPowerSeries.subst
        (fun s => ∑ l, a s l • (MvPowerSeries.X l : MvPowerSeries Λ C)) Z) =
      MvPolynomial.eval (fun x : σ × Λ => a x.1 x.2) Q := by
  let u : σ → MvPowerSeries Λ (MvPolynomial (σ × Λ) C) :=
    fun s => ∑ l, (MvPolynomial.X (s, l) : MvPolynomial (σ × Λ) C) • MvPowerSeries.X l
  have hu : HasSubst u := hasSubst_of_constantCoeff_zero fun s => by simp [u]
  let Zu : MvPowerSeries Λ (MvPolynomial (σ × Λ) C) :=
    subst u (MvPowerSeries.map (MvPolynomial.C : C →+* MvPolynomial (σ × Λ) C) Z)
  refine ⟨∑ α ∈ P.support, MvPolynomial.C (P.coeff α * mfact α) * coeff α Zu, fun a => ?_⟩
  have key : MvPowerSeries.map (MvPolynomial.eval (fun x : σ × Λ => a x.1 x.2)) Zu =
      MvPowerSeries.subst (fun s => ∑ l, a s l • (MvPowerSeries.X l : MvPowerSeries Λ C)) Z := by
    rw [MvPowerSeries.map_subst hu]
    congr 1
    · funext s
      simp [u, MvPowerSeries.smul_eq_C_mul]
    · ext d
      simp

  rw [← key, derivAt0, map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [map_mul, MvPolynomial.eval_C, coeff_map]

theorem derivAt0_subst_linear_lipschitz :
    ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (σ Λ : Type) [Fintype σ] [Fintype Λ] (P : MvPolynomial Λ C) (Z : MvPowerSeries σ C), ∃ K : ℝ, ∀ (M : ℝ) (a a' : σ → Λ → C), (∀ s l, IsIntV v (a s l)) → (∀ s l, IsIntV v (a' s l)) → (∀ s l, ((M : ℝ) : WithTop ℝ) ≤ v (a s l - a' s l)) → ((M - K : ℝ) : WithTop ℝ) ≤ v (derivAt0 P (MvPowerSeries.subst (fun s => ∑ l, a s l • (MvPowerSeries.X l : MvPowerSeries Λ C)) Z) - derivAt0 P (MvPowerSeries.subst (fun s => ∑ l, a' s l • (MvPowerSeries.X l : MvPowerSeries Λ C)) Z)) := by
  intro C _ v σ Λ _ _ P Z
  obtain ⟨Q, hQ⟩ := exists_poly_derivAt0_subst P Z
  obtain ⟨K, -, hK⟩ := exists_lipschitz_eval v Q
  refine ⟨K, fun M a a' ha ha' hM => ?_⟩
  rw [hQ, hQ]
  exact hK M _ _ (fun x => ha x.1 x.2) (fun x => ha' x.1 x.2) (fun x => hM x.1 x.2)

end GlobalTheory.FGDepth
end

section

open GlobalTheory.OrbitUnfold GlobalTheory.OrbitUnfold.ConjSelf

theorem _root_.GlobalTheory.T.finite_support_stabilizerWeightedPairTerm : ∀ {Γ Y : Type} [Group Γ] [MulAction Γ Y] (F : Y → Γ → ℂ), (∀ (η : Γ) (y : Y) (γ : Γ), F (η • y) (η * γ * η⁻¹) = F y γ) → (∀ y : Y, (Function.support (F y)).Finite) → {o : MulAction.orbitRel.Quotient Γ Y | ∃ γ, F (Quotient.out o) γ ≠ 0}.Finite → (Function.support (fun o : MulAction.orbitRel.Quotient Γ (Y × ConjSelf Γ) => pairTerm F (Quotient.out o))).Finite := by
  first | exact @GlobalTheory.OrbitUnfold.finite_support_pairTerm | exact GlobalTheory.OrbitUnfold.finite_support_pairTerm | (intros; apply GlobalTheory.OrbitUnfold.finite_support_pairTerm <;> assumption)
end
