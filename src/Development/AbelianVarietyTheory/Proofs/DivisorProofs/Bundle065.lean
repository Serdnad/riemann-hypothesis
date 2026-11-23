module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Matrix.PEquiv
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Tactic.Continuity
public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Multilinear.Basic
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
public import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

section

open MeasureTheory Matrix

namespace GlobalTheory.DetFactor

variable {k : Type} [Field k] {m : ℕ}

noncomputable def diagGL (n : ℕ) : (Fin n → kˣ) →* GL (Fin n) k :=
  (Units.map (diagonalRingHom (Fin n) k).toMonoidHom).comp MulEquiv.piUnits.symm.toMonoidHom

theorem diagGL_val {n : ℕ} (d : Fin n → kˣ) : ((diagGL n d : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = diagonal (fun i => (d i : k)) := rfl

noncomputable def toGL {n : ℕ} (M : Matrix (Fin n) (Fin n) k) (h : M.det ≠ 0) : GL (Fin n) k :=
  nonsingInvUnit M (isUnit_iff_ne_zero.mpr h)

@[simp] theorem toGL_val {n : ℕ} (M : Matrix (Fin n) (Fin n) k) (h : M.det ≠ 0) :
    ((toGL M h : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = M := rfl

theorem conj_transvection {n : ℕ} {i j : Fin n} (hij : i ≠ j) (t : k) :
    diagonal (fun l => if l = i then (2 : k) else 1) * transvection i j t
      = transvection i j (2 * t) * diagonal (fun l => if l = i then (2 : k) else 1) := by
  ext a b
  simp only [transvection, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, diagonal_mul, mul_diagonal]
  by_cases ha : a = i <;> by_cases hb : b = j <;> by_cases hbi : b = i <;> by_cases hab : a = b <;>
    simp_all [single, one_apply, eq_comm] <;> ring

theorem det_diag2_ne {n : ℕ} (h2 : (2 : k) ≠ 0) (i : Fin n) :
    (diagonal (fun l => if l = i then (2 : k) else 1)).det ≠ 0 := by
  rw [det_diagonal, Finset.prod_ne_zero_iff]
  intro l _
  split_ifs <;> simp [h2]

theorem det_transvection_ne {n : ℕ} {i j : Fin n} (hij : i ≠ j) (t : k) :
    (transvection i j t).det ≠ 0 := by
  rw [det_transvection_of_ne _ _ hij]; exact one_ne_zero

theorem map_transvection_eq_one (h2 : (2 : k) ≠ 0) {n : ℕ} (c : GL (Fin n) k →* ℂˣ) {i j : Fin n}
    (hij : i ≠ j) (t : k) : c (toGL (transvection i j t) (det_transvection_ne hij t)) = 1 := by
  set D := toGL _ (det_diag2_ne h2 i)
  have h1 : D * toGL (transvection i j t) (det_transvection_ne hij t)
      = toGL (transvection i j (2 * t)) (det_transvection_ne hij _) * D := by
    apply Units.ext; simp only [Units.val_mul, toGL_val, D]; exact conj_transvection hij t
  have h3 : toGL (transvection i j t) (det_transvection_ne hij t) * toGL (transvection i j t) (det_transvection_ne hij t)
      = toGL (transvection i j (2 * t)) (det_transvection_ne hij _) := by
    apply Units.ext; simp only [Units.val_mul, toGL_val]; rw [transvection_mul_transvection_same (h := hij), two_mul]
  have e1 := congrArg c h1
  have e3 := congrArg c h3
  rw [map_mul, map_mul, mul_comm (c D)] at e1
  have e1' := mul_right_cancel e1
  rw [map_mul, ← e1'] at e3
  exact (mul_eq_left.mp e3)

theorem det_perm_ne {n : ℕ} (σ : Equiv.Perm (Fin n)) : (σ.toPEquiv.toMatrix : Matrix (Fin n) (Fin n) k).det ≠ 0 := by
  have := det_permutation (R := k) σ
  simp only [Equiv.Perm.permMatrix] at this
  rw [this]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

theorem map_diagGL_perm {n : ℕ} (c : GL (Fin n) k →* ℂˣ) (σ : Equiv.Perm (Fin n)) (d : Fin n → kˣ) :
    c (diagGL n (d ∘ σ)) = c (diagGL n d) := by
  set P := toGL _ (det_perm_ne (k := k) σ)
  have h1 : P * diagGL n d = diagGL n (d ∘ σ) * P := by
    apply Units.ext
    simp only [Units.val_mul, toGL_val, P, diagGL_val]
    rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
    ext a b
    simp [diagonal_apply, Equiv.eq_symm_apply]
  have e := congrArg c h1
  rw [map_mul, map_mul, mul_comm (c P)] at e
  exact (mul_right_cancel e).symm

theorem map_diagGL_eq (c : GL (Fin (m + 1)) k →* ℂˣ) (d : Fin (m + 1) → kˣ) :
    c (diagGL (m + 1) d) = (c.comp (diagGL (m + 1))).comp (MonoidHom.mulSingle (fun _ => kˣ) 0) (∏ i, d i) := by
  have hs : ∀ i (x : kˣ), c (diagGL (m + 1) (Pi.mulSingle i x)) = c (diagGL (m + 1) (Pi.mulSingle 0 x)) := by
    intro i x
    rw [← map_diagGL_perm c (Equiv.swap 0 i) (Pi.mulSingle i x)]
    congr 2
    simp [Pi.mulSingle_comp_equiv]
  have e : c (diagGL (m + 1) d) = (c.comp (diagGL (m + 1))) (∏ i, Pi.mulSingle i (d i)) := by
    rw [Finset.univ_prod_mulSingle]; rfl
  rw [e, map_prod, map_prod]
  simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.mulSingle_apply]
  exact Finset.prod_congr rfl (fun i _ => hs i (d i))

theorem factors_through_det (h2 : (2 : k) ≠ 0) {n : ℕ} (c : GL (Fin n) k →* ℂˣ) :
    ∃ χ : kˣ →* ℂˣ, ∀ g, c g = χ (Matrix.GeneralLinearGroup.det g) := by
  cases n with
  | zero =>
    refine ⟨1, fun g => ?_⟩
    have : g = 1 := Units.ext (Matrix.ext fun i _ => i.elim0)
    simp [this]
  | succ m =>
    refine ⟨(c.comp (diagGL (m + 1))).comp (MonoidHom.mulSingle (fun _ => kˣ) 0), fun g => ?_⟩
    set χ := (c.comp (diagGL (m + 1))).comp (MonoidHom.mulSingle (fun _ => kˣ) 0)
    let P : Matrix (Fin (m + 1)) (Fin (m + 1)) k → Prop := fun M =>
      ∀ u : GL (Fin (m + 1)) k, (u : Matrix _ _ k) = M → c u = χ (Matrix.GeneralLinearGroup.det u)
    have hg : Matrix.det (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) ≠ 0 := (Matrix.isUnits_det_units g).ne_zero
    refine diagonal_transvection_induction_of_det_ne_zero P (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) hg ?_ ?_ ?_ g rfl
    · intro D hD u hu
      have hD' : ∀ i, D i ≠ 0 := by
        intro i; rw [det_diagonal] at hD; exact Finset.prod_ne_zero_iff.mp hD i (Finset.mem_univ i)
      have hu' : u = diagGL (m + 1) (fun i => Units.mk0 (D i) (hD' i)) := by
        apply Units.ext; rw [hu, diagGL_val]; rfl
      have hdet : Matrix.GeneralLinearGroup.det u = ∏ i, Units.mk0 (D i) (hD' i) := by
        apply Units.ext; simp [hu, det_diagonal]
      rw [hdet, hu', map_diagGL_eq]
    · intro t u hu
      have hu' : u = toGL (transvection t.i t.j t.c) (det_transvection_ne t.hij t.c) := Units.ext hu
      have hdet : Matrix.GeneralLinearGroup.det u = 1 := by
        apply Units.ext; simp [hu, TransvectionStruct.toMatrix, det_transvection_of_ne _ _ t.hij]
      rw [hdet, map_one, hu']
      exact map_transvection_eq_one h2 c t.hij t.c
    · intro A B hA hB PA PB u hu
      have hu' : u = toGL A hA * toGL B hB := Units.ext (by simp [hu])
      rw [hu', map_mul, map_mul, PA _ rfl, PB _ rfl, ← map_mul]

end GlobalTheory.DetFactor

theorem GlobalTheory.ghom_factors_through_det : ∀ {k : Type} [Field k], (2 : k) ≠ 0 → ∀ {n : ℕ} (c : GL (Fin n) k →* ℂˣ),
    ∃ χ : kˣ →* ℂˣ, ∀ g, c g = χ (Matrix.GeneralLinearGroup.det g) :=
  by intro k _ h2 n c; exact GlobalTheory.DetFactor.factors_through_det h2 c
end

section

open scoped Pointwise

namespace GlobalTheory.DCIndex

variable {A : Type} [Group A]

theorem normal_of_comm (hc : ∀ a b : A, a * b = b * a) (V : Subgroup A) : V.Normal :=
  ⟨fun n hn g => by rw [hc g n, mul_inv_cancel_right]; exact hn⟩

theorem mem_sup_iff (hc : ∀ a b : A, a * b = b * a) (P Q : Subgroup A) {x : A} :
    x ∈ P ⊔ Q ↔ ∃ p ∈ P, ∃ q ∈ Q, p * q = x := by
  haveI : Q.Normal := normal_of_comm hc Q
  rw [← SetLike.mem_coe, Subgroup.mul_normal, Set.mem_mul]
  simp only [SetLike.mem_coe]

theorem card_quot_eq_index (hc : ∀ a b : A, a * b = b * a) (P V : Subgroup A) :
    Nat.card (DoubleCoset.Quotient (P : Set A) (V : Set A)) = (P ⊔ V).index := by
  rw [Subgroup.index]
  apply Nat.card_congr
  refine Quotient.congr (Equiv.refl A) ?_
  intro x y
  simp only [Equiv.refl_apply]
  rw [DoubleCoset.rel_iff, QuotientGroup.leftRel_apply, mem_sup_iff hc]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨a, ha, b, hb, ?_⟩
    rw [hc a x, mul_assoc, inv_mul_cancel_left]
  · rintro ⟨a, ha, b, hb, h⟩
    refine ⟨a, ha, b, hb, ?_⟩
    rw [hc a x, mul_assoc, h, mul_inv_cancel_left]

theorem relIndex_split (hc : ∀ a b : A, a * b = b * a) (h u c : Subgroup A) (huc : u ≤ c) :
    u.relIndex c = (h ⊓ u).relIndex (h ⊓ c) * (h ⊔ u).relIndex (h ⊔ c) := by
  haveI : u.Normal := normal_of_comm hc u
  haveI : (h ⊔ u).Normal := normal_of_comm hc (h ⊔ u)
  have hM : (h ⊔ u) ⊓ c = (h ⊓ c) ⊔ u := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 hx
      obtain ⟨p, hp, q, hq, rfl⟩ := (mem_sup_iff hc h u).1 hx1
      have hpc : p ∈ c := by
        have := c.mul_mem hx2 (c.inv_mem (huc hq))
        rwa [mul_inv_cancel_right] at this
      exact (mem_sup_iff hc _ _).2 ⟨p, Subgroup.mem_inf.2 ⟨hp, hpc⟩, q, hq, rfl⟩
    · exact sup_le (inf_le_inf_right c le_sup_left) (le_inf le_sup_right huc)
  have e1 := Subgroup.relIndex_mul_relIndex (H := u) (K := (h ⊔ u) ⊓ c) (L := c)
    (le_inf le_sup_right huc) inf_le_right
  have e2 : ((h ⊔ u) ⊓ c).relIndex c = (h ⊔ u).relIndex (h ⊔ c) := by
    rw [Subgroup.inf_relIndex_right, ← Subgroup.relIndex_sup_right (H := c) (K := h ⊔ u)]
    congr 1
    apply le_antisymm
    · exact sup_le le_sup_right (sup_le le_sup_left (huc.trans le_sup_right))
    · exact sup_le (le_sup_left.trans le_sup_right) le_sup_left
  have e3 : u.relIndex ((h ⊔ u) ⊓ c) = (h ⊓ u).relIndex (h ⊓ c) := by
    rw [hM, Subgroup.relIndex_sup_right, ← Subgroup.inf_relIndex_right (H := u) (K := h ⊓ c)]
    congr 1
    apply le_antisymm
    · exact le_inf (inf_le_right.trans inf_le_left) inf_le_left
    · exact le_inf inf_le_right (inf_le_inf_left h huc)
  rw [← e1, e2, e3]

theorem card_split (h u c : Subgroup A) (huc : u ≤ c) :
    (h ⊓ u).relIndex (h ⊓ c) * Nat.card (h ⊓ u : Subgroup A) = Nat.card (h ⊓ c : Subgroup A) := by
  have hle : h ⊓ u ≤ h ⊓ c := inf_le_inf_left h huc
  have := Subgroup.card_mul_index ((h ⊓ u).subgroupOf (h ⊓ c))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at this
  rw [Subgroup.relIndex, mul_comm, this]

end GlobalTheory.DCIndex

namespace GlobalTheory.DCIndex

theorem card_inf_subgroupOf {G : Type} [Group G] (T H U : Subgroup G) (hUT : U ≤ T) :
    Nat.card (H.subgroupOf T ⊓ U.subgroupOf T : Subgroup T) = Nat.card (H ⊓ U : Subgroup G) := by
  have he : H.subgroupOf T ⊓ U.subgroupOf T = (H ⊓ U).subgroupOf T := by
    ext x; simp [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  rw [he]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right.trans hUT)).toEquiv

theorem index_identity : ∀ {G : Type} [Group G] (T H U C : Subgroup G), (∀ a ∈ T, ∀ b ∈ T, a * b = b * a) → U ≤ C → C ≤ T → U.relIndex C ≠ 0 → (Nat.card (DoubleCoset.Quotient ((H.subgroupOf T : Subgroup T) : Set T) ((U.subgroupOf T : Subgroup T) : Set T)) : ℂ) / (Nat.card (H ⊓ U : Subgroup G) : ℂ) = (U.relIndex C : ℂ) * (Nat.card (DoubleCoset.Quotient ((H.subgroupOf T : Subgroup T) : Set T) ((C.subgroupOf T : Subgroup T) : Set T)) : ℂ) / (Nat.card (H ⊓ C : Subgroup G) : ℂ) := by
  intro G _ T H U C hcomm hUC hCT hne
  have hc : ∀ a b : T, a * b = b * a := fun a b => Subtype.ext (hcomm a a.2 b b.2)
  have hu'c' : U.subgroupOf T ≤ C.subgroupOf T := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hUC hx
  have hrel : (U.subgroupOf T).relIndex (C.subgroupOf T) = U.relIndex C :=
    Subgroup.relIndex_subgroupOf hCT
  rw [card_quot_eq_index hc, card_quot_eq_index hc, ← card_inf_subgroupOf T H U (hUC.trans hCT),
    ← card_inf_subgroupOf T H C hCT, ← hrel]
  rw [← hrel] at hne
  have hU := (Subgroup.relIndex_mul_index
    (sup_le_sup_left hu'c' (H.subgroupOf T))).symm
  have hsplit := relIndex_split hc (H.subgroupOf T) _ _ hu'c'
  have hcard := card_split (H.subgroupOf T) _ _ hu'c'
  rw [hU, hsplit, ← hcard]
  rw [hsplit] at hne
  have hs : (((H.subgroupOf T ⊓ U.subgroupOf T).relIndex (H.subgroupOf T ⊓ C.subgroupOf T) : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 (left_ne_zero_of_mul hne)
  push_cast
  rw [mul_assoc, mul_div_mul_left _ _ hs]

end GlobalTheory.DCIndex
end

section

open MulAction

namespace GlobalTheory.OrbitMass

variable {G H D : Type} [Group G] [Group H] [MulAction G D] [MulAction H D]

def toG (ι : H →* G) (hc : ∀ (h : H) (d : D), ι h • d = h • d) :
    orbitRel.Quotient H D → orbitRel.Quotient G D :=
  Quotient.map' id (fun a b hab => by
    change a ∈ orbit H b at hab
    change a ∈ orbit G b
    obtain ⟨h, rfl⟩ := hab
    exact ⟨ι h, hc h b⟩)

def toCoset (ι : H →* G) (hc : ∀ (h : H) (d : D), ι h • d = h • d) (x : D) :
    G ⧸ ι.range → orbitRel.Quotient H D :=
  fun ω => Quotient.liftOn' ω (fun g => (Quotient.mk'' (g⁻¹ • x) : orbitRel.Quotient H D)) (by
    intro g₁ g₂ hg
    rw [QuotientGroup.leftRel_apply, MonoidHom.mem_range] at hg
    obtain ⟨h, hh⟩ := hg
    apply Quotient.sound'
    change g₁⁻¹ • x ∈ orbit H (g₂⁻¹ • x)
    refine ⟨h, ?_⟩
    change h • g₂⁻¹ • x = g₁⁻¹ • x
    rw [← hc, smul_smul, hh, mul_inv_cancel_right])

theorem toCoset_mk (ι : H →* G) (hc : ∀ (h : H) (d : D), ι h • d = h • d) (x : D) (g : G) :
    toCoset ι hc x (g : G ⧸ ι.range) = Quotient.mk'' (g⁻¹ • x) := rfl

theorem toCoset_eq_iff (ι : H →* G) (hc : ∀ (h : H) (d : D), ι h • d = h • d) (x : D) (a g : G) :
    toCoset ι hc x (g : G ⧸ ι.range) = Quotient.mk'' (a⁻¹ • x) ↔
      (g : G ⧸ ι.range) ∈ orbit (stabilizer G x) (a : G ⧸ ι.range) := by
  rw [toCoset_mk, Quotient.eq'']
  change g⁻¹ • x ∈ orbit H (a⁻¹ • x) ↔ _
  rw [mem_orbit_iff, mem_orbit_iff]
  constructor
  · rintro ⟨h, hh⟩
    refine ⟨⟨g * ι h * a⁻¹, ?_⟩, ?_⟩
    · rw [mem_stabilizer_iff, mul_smul, mul_smul, hc, hh, smul_inv_smul]
    · change ((g * ι h * a⁻¹ : G) • (a : G ⧸ ι.range)) = g
      rw [MulAction.Quotient.smul_mk, QuotientGroup.eq]
      exact ⟨h⁻¹, by simp [mul_assoc]⟩
  · rintro ⟨⟨s, hs⟩, hsa⟩
    change ((s : G) • (a : G ⧸ ι.range)) = g at hsa
    rw [MulAction.Quotient.smul_mk, QuotientGroup.eq, MonoidHom.mem_range] at hsa
    obtain ⟨k, hk⟩ := hsa
    have hg : g = s * a * ι k := by rw [hk, smul_eq_mul, mul_inv_cancel_left]
    subst hg
    have hs' : s⁻¹ • x = x := by rw [inv_smul_eq_iff]; exact (mem_stabilizer_iff.mp hs).symm
    refine ⟨k⁻¹, ?_⟩
    rw [← hc, map_inv, mul_inv_rev, mul_inv_rev, mul_smul, mul_smul, hs']

theorem card_stab (ι : H →* G) (hinj : Function.Injective ι)
    (hc : ∀ (h : H) (d : D), ι h • d = h • d) (x : D) (a : G) :
    Nat.card (stabilizer (stabilizer G x) (a : G ⧸ ι.range)) =
      Nat.card (stabilizer H (a⁻¹ • x)) := by
  symm
  refine Nat.card_eq_of_bijective
    (fun h => ⟨⟨a * ι h.1 * a⁻¹, by
      rw [mem_stabilizer_iff, mul_smul, mul_smul, hc, mem_stabilizer_iff.mp h.2, smul_inv_smul]⟩,
      by
        rw [mem_stabilizer_iff]
        change ((a * ι h.1 * a⁻¹ : G) • (a : G ⧸ ι.range)) = a
        rw [MulAction.Quotient.smul_mk, QuotientGroup.eq]
        exact ⟨h.1⁻¹, by simp [mul_assoc]⟩⟩) ⟨?_, ?_⟩
  · intro h₁ h₂ he
    have e : a * ι h₁.1 * a⁻¹ = a * ι h₂.1 * a⁻¹ := congrArg (fun s => ((s.1 : stabilizer G x) : G)) he
    exact Subtype.ext (hinj (mul_left_cancel (mul_right_cancel e)))
  · rintro ⟨⟨s, hs⟩, hsa⟩
    rw [mem_stabilizer_iff] at hsa
    change ((s : G) • (a : G ⧸ ι.range)) = a at hsa
    rw [MulAction.Quotient.smul_mk, QuotientGroup.eq, MonoidHom.mem_range] at hsa
    obtain ⟨k, hk⟩ := hsa
    have e : ι k⁻¹ = a⁻¹ * s * a := by
      rw [map_inv, hk, smul_eq_mul]; group
    refine ⟨⟨k⁻¹, ?_⟩, ?_⟩
    · rw [mem_stabilizer_iff, ← hc, e, mul_smul, mul_smul, smul_inv_smul, mem_stabilizer_iff.mp hs]
    · apply Subtype.ext; apply Subtype.ext
      change a * ι k⁻¹ * a⁻¹ = s
      rw [e]; group

theorem toG_mk (ι : H →* G) (hc : ∀ (h : H) (d : D), ι h • d = h • d) (y : D) :
    toG ι hc (Quotient.mk'' y) = Quotient.mk'' y := rfl

theorem sum_fiber (ι : H →* G) (hinj : Function.Injective ι)
    (hc : ∀ (h : H) (d : D), ι h • d = h • d) [ι.range.FiniteIndex]
    (c' : orbitRel.Quotient G D) [Finite (stabilizer G (Quotient.out c'))]
    [Fintype (orbitRel.Quotient H D)] [DecidableEq (orbitRel.Quotient G D)] :
    ∑ c ∈ Finset.univ.filter (fun c => toG ι hc c = c'),
        ((Nat.card (stabilizer H (Quotient.out c)) : ℂ))⁻¹
      = (ι.range.index : ℂ) / Nat.card (stabilizer G (Quotient.out c')) := by
  classical
  set x := Quotient.out c' with hx
  haveI : Fintype (G ⧸ ι.range) := Fintype.ofFinite _
  have hS0 : 0 < Nat.card (stabilizer G x) := Nat.card_pos
  have hidx : (ι.range.index : ℂ) / Nat.card (stabilizer G x) =
      ∑ _ω : G ⧸ ι.range, ((Nat.card (stabilizer G x) : ℂ))⁻¹ := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Subgroup.index_eq_card,
      Nat.card_eq_fintype_card, div_eq_mul_inv]
  rw [hidx, ← Finset.sum_fiberwise Finset.univ (toCoset ι hc x), Finset.sum_filter]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Finset.sum_const, nsmul_eq_mul]
  split_ifs with hcx
  · have hmem : Quotient.out c ∈ orbit G x := by
      have h1 : (Quotient.mk'' (Quotient.out c) : orbitRel.Quotient G D) = Quotient.mk'' x := by
        rw [← toG_mk ι hc, Quotient.out_eq', hcx, hx, Quotient.out_eq']
      exact Quotient.exact' h1
    obtain ⟨b, hb⟩ := hmem
    have hy : (b⁻¹)⁻¹ • x = Quotient.out c := by rw [inv_inv]; exact hb
    have hfib : (Finset.univ.filter (fun ω => toCoset ι hc x ω = c)) =
        (orbit (stabilizer G x) ((b⁻¹ : G) : G ⧸ ι.range)).toFinset := by
      ext ω
      induction ω using QuotientGroup.induction_on with
      | H g =>
        rw [Finset.mem_filter, Set.mem_toFinset, ← toCoset_eq_iff ι hc x b⁻¹ g, hy,
          Quotient.out_eq']
        simp
    have hcard := Subgroup.card_mul_index (stabilizer (stabilizer G x) ((b⁻¹ : G) : G ⧸ ι.range))
    rw [index_stabilizer, card_stab ι hinj hc x b⁻¹, hy] at hcard
    rw [hfib, ← Set.ncard_eq_toFinset_card']
    have hm0 : Nat.card (stabilizer H (Quotient.out c)) ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hcard; omega
    have hn0 : (orbit (stabilizer G x) ((b⁻¹ : G) : G ⧸ ι.range)).ncard ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hcard; omega
    rw [← hcard]
    push_cast
    field_simp
  · rw [Finset.card_eq_zero.mpr, Nat.cast_zero, zero_mul]
    rw [Finset.filter_eq_empty_iff]
    intro ω _ hω
    apply hcx
    rw [← hω]
    induction ω using QuotientGroup.induction_on with
    | H g =>
      rw [toCoset_mk, toG_mk, hx]
      conv_rhs => rw [← Quotient.out_eq' c']
      exact Quotient.sound' ⟨g⁻¹, rfl⟩

theorem mass_formula : ∀ {G H D : Type} [Group G] [Group H] [MulAction G D] [MulAction H D] (ι : H →* G), Function.Injective ι → (∀ (h : H) (d : D), ι h • d = h • d) → ι.range.FiniteIndex → (∀ d : D, Finite (MulAction.stabilizer G d)) → ∀ [Fintype (MulAction.orbitRel.Quotient G D)] [Fintype (MulAction.orbitRel.Quotient H D)] (f : D → ℂ), (∀ (g : G) (d : D), f (g • d) = f d) → ∑ c : MulAction.orbitRel.Quotient H D, ((Nat.card (MulAction.stabilizer H (Quotient.out c)) : ℂ))⁻¹ * f (Quotient.out c) = (ι.range.index : ℂ) * ∑ c : MulAction.orbitRel.Quotient G D, ((Nat.card (MulAction.stabilizer G (Quotient.out c)) : ℂ))⁻¹ * f (Quotient.out c) := by
  intro G H D _ _ _ _ ι hinj hc hfi hfin _ _ f hf
  classical
  rw [← Finset.sum_fiberwise Finset.univ (toG ι hc)
    (fun c => ((Nat.card (MulAction.stabilizer H (Quotient.out c)) : ℂ))⁻¹ * f (Quotient.out c)),
    Finset.mul_sum]
  refine Finset.sum_congr rfl (fun c' _ => ?_)
  have hconst : ∀ c ∈ Finset.univ.filter (fun c => toG ι hc c = c'),
      ((Nat.card (MulAction.stabilizer H (Quotient.out c)) : ℂ))⁻¹ * f (Quotient.out c) =
      ((Nat.card (MulAction.stabilizer H (Quotient.out c)) : ℂ))⁻¹ * f (Quotient.out c') := by
    intro c hc'
    rw [Finset.mem_filter] at hc'
    have h1 : (Quotient.mk'' (Quotient.out c) : orbitRel.Quotient G D) = Quotient.mk'' (Quotient.out c') := by
      rw [← toG_mk ι hc, Quotient.out_eq', hc'.2, Quotient.out_eq']
    obtain ⟨g, hg⟩ := (Quotient.exact' h1 : Quotient.out c ∈ orbit G (Quotient.out c'))
    rw [← hg]
    change _ * f (g • Quotient.out c') = _
    rw [hf]
  haveI := hfin (Quotient.out c')
  rw [Finset.sum_congr rfl hconst, ← Finset.sum_mul, sum_fiber ι hinj hc c', div_eq_mul_inv, mul_assoc]

end GlobalTheory.OrbitMass
end

section

namespace GlobalTheory.MultilinearSpanImage

theorem multilinear_mem_span_image_partial {ι : Type} [Fintype ι] [DecidableEq ι] {M : ι → Type}
    [(i : ι) → AddCommGroup (M i)] [(i : ι) → Module ℂ (M i)] {N : Type} [AddCommGroup N]
    [Module ℂ N] (Φ : MultilinearMap (RingHom.id ℂ) M N) (s : (i : ι) → Set (M i)) (t : Finset ι) :
    ∀ f : (i : ι) → M i, (∀ i ∈ t, f i ∈ Submodule.span ℂ (s i)) → (∀ i, i ∉ t → f i ∈ s i) →
      Φ f ∈ Submodule.span ℂ {y : N | ∃ g : (i : ι) → M i, (∀ i, g i ∈ s i) ∧ y = Φ g} := by
  refine Finset.induction_on t ?_ ?_
  · intro f _ h
    exact Submodule.subset_span ⟨f, fun i => h i (by simp), rfl⟩
  · intro a t ha ih f h1 h2
    have key : ∀ x ∈ Submodule.span ℂ (s a), Φ (Function.update f a x) ∈
        Submodule.span ℂ {y : N | ∃ g : (i : ι) → M i, (∀ i, g i ∈ s i) ∧ y = Φ g} := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        apply ih
        · intro i hi
          have hne : i ≠ a := by rintro rfl; exact ha hi
          simpa [hne] using h1 i (Finset.mem_insert_of_mem hi)
        · intro i hi
          by_cases h : i = a
          · subst h; simpa using hx
          · simpa [h] using h2 i (by simp [h, hi])
      | zero => rw [Φ.map_update_zero]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [Φ.map_update_add]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx => rw [Φ.map_update_smul]; exact Submodule.smul_mem _ c hx
    have := key (f a) (h1 a (Finset.mem_insert_self a t))
    simpa using this

theorem multilinear_apply_mem_span_image {ι : Type} [Fintype ι] [DecidableEq ι] {M : ι → Type}
    [inst : (i : ι) → AddCommGroup (M i)] [inst_1 : (i : ι) → Module ℂ (M i)] {N : Type}
    [inst_2 : AddCommGroup N] [inst_3 : Module ℂ N] (Φ : MultilinearMap (RingHom.id ℂ) M N)
    (s : (i : ι) → Set (M i)) (f : (i : ι) → M i) (hf : ∀ (i : ι), f i ∈ Submodule.span ℂ (s i)) :
    (Φ : ((i : ι) → M i) → N) f ∈ Submodule.span ℂ
      {y : N | ∃ (g : (i : ι) → M i), (∀ (i : ι), g i ∈ s i) ∧ y = (Φ : ((i : ι) → M i) → N) g} :=
  multilinear_mem_span_image_partial Φ s Finset.univ f (fun i _ => hf i) (fun i hi => absurd (Finset.mem_univ i) hi)

end GlobalTheory.MultilinearSpanImage
end
