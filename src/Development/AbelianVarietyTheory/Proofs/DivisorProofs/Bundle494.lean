module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle445
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle333
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle332
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle483
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle446
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle447
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective

@[expose] public section

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

noncomputable section

namespace GlobalTheory.Shin

theorem deg_map_const_fst (m : ℕ) (e : ℕ → ℕ) (L : List ℕ) :
    deg (L.map fun i => (m, e i)) = m * L.length := by
  induction L with
  | nil => simp [deg]
  | cons a L ih =>
    simp only [deg, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    rw [ih]; ring

theorem pair_prod_split {F : Type} [Field F] [Fintype F] {a b : ℕ} (α : GL (Fin a) F → ℂ)
    (β : GL (Fin b) F → ℂ) (r : ℕ → F[X] → ℂ) (hr : ∀ j, IsAdditive (r j)) (T : Finset ℕ) :
    ∑ᶠ x : GL (Fin a) F, ∑ᶠ y : GL (Fin b) F, α x * β y *
      star ((fun P => ∏ j ∈ T, r j P) (Matrix.charpoly (x : Matrix (Fin a) (Fin a) F) *
        Matrix.charpoly (y : Matrix (Fin b) (Fin b) F))) =
    ∑ U ∈ T.powerset, (∑ᶠ x : GL (Fin a) F, α x * star (∏ j ∈ U, r j (Matrix.charpoly (x : Matrix (Fin a) (Fin a) F)))) *
      (∑ᶠ y : GL (Fin b) F, β y * star (chG (fun P => ∏ j ∈ T \ U, r j P) b y)) := by
  simp only [finsum_eq_sum_of_fintype, chG]
  have e1 : ∀ (x : GL (Fin a) F) (y : GL (Fin b) F),
      ∏ j ∈ T, r j (Matrix.charpoly (x : Matrix (Fin a) (Fin a) F) * Matrix.charpoly (y : Matrix (Fin b) (Fin b) F)) =
      ∑ U ∈ T.powerset, (∏ j ∈ U, r j (Matrix.charpoly (x : Matrix (Fin a) (Fin a) F))) *
        ∏ j ∈ T \ U, r j (Matrix.charpoly (y : Matrix (Fin b) (Fin b) F)) := by
    intro x y
    rw [← Finset.prod_add]
    exact Finset.prod_congr rfl fun j _ => hr j _ _ (Matrix.charpoly_monic _) (Matrix.charpoly_monic _)
  simp only [e1, star_sum, star_mul', Finset.mul_sum, Finset.sum_mul]
  conv_lhs => arg 2; ext x; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun U _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem sum_powerset_single (i : ℕ) (S T : Finset ℕ) (hiS : i ∉ S) (hT : T.card ≤ S.card + 1)
    (f g : Finset ℕ → ℂ) (A B : ℂ) (hf0 : f ∅ = 0) (hf1 : ∀ j ∈ T, f {j} = if i = j then A else 0)
    (hg : ∀ U ∈ T.powerset, U ≠ ∅ → g U = if T \ U = S then B else 0) :
    ∑ U ∈ T.powerset, f U * g U = if T = insert i S then A * B else 0 := by
  have hz : ∀ U ∈ T.powerset, U ≠ {i} → f U * g U = 0 := by
    intro U hU hUi
    by_cases h0 : U = ∅
    · rw [h0, hf0, zero_mul]
    rw [hg U hU h0]
    split_ifs with hc
    · have hsub : U ⊆ T := Finset.mem_powerset.1 hU
      have h1 := Finset.card_sdiff_add_card_eq_card hsub
      rw [hc] at h1
      have hpos : 0 < U.card := Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 h0)
      have hU1 : U.card = 1 := by omega
      obtain ⟨j, rfl⟩ := Finset.card_eq_one.1 hU1
      have hjT : j ∈ T := hsub (Finset.mem_singleton_self j)
      rw [hf1 j hjT, if_neg (fun h => hUi (by rw [h])), zero_mul]
    · rw [mul_zero]
  by_cases hiT : i ∈ T
  · have hmem : {i} ∈ T.powerset := Finset.mem_powerset.2 (Finset.singleton_subset_iff.2 hiT)
    rw [Finset.sum_eq_single_of_mem {i} hmem hz, hf1 i hiT, if_pos rfl,
      hg {i} hmem (Finset.singleton_ne_empty i)]
    have hiff : (T \ {i} = S) ↔ T = insert i S := by
      constructor
      · intro h
        rw [← h, Finset.sdiff_singleton_eq_erase, Finset.insert_erase hiT]
      · intro h
        rw [h, Finset.sdiff_singleton_eq_erase, Finset.erase_insert hiS]
    by_cases hc : T = insert i S
    · rw [if_pos (hiff.2 hc), if_pos hc]
    · rw [if_neg (fun h => hc (hiff.1 h)), if_neg hc, mul_zero]
  · rw [Finset.sum_eq_zero fun U hU => hz U hU (fun h => hiT (by
      rw [h] at hU; exact Finset.singleton_subset_iff.1 (Finset.mem_powerset.1 hU)))]
    rw [if_neg (fun h => hiT (by rw [h]; exact Finset.mem_insert_self i S))]

theorem pair_J_prod_rootSum : ∀ (F : Type) [Field F] [Finite F], ∀ (θ : AlgebraicClosure F →* ℂ) (m : ℕ) (e : ℕ → ℕ) (ε : ℤ), (∀ i, ∑ᶠ x, cusp θ m (e i) x = 0) → ∀ N : ℕ, (∀ i j, i < N → j < N → ∑ᶠ x, cusp θ m (e i) x * star (chG (rootSum θ (e j)) m x) = if i = j then (ε : ℂ) * (Nat.card (GL (Fin m) F) : ℂ) else 0) → ∀ (L : List ℕ) (T : Finset ℕ), L.Nodup → (∀ i ∈ L, i < N) → (∀ j ∈ T, j < N) → T.card ≤ L.length → ∀ n, n = m * L.length → ∑ᶠ x, J θ (L.map fun i => (m, e i)) n x * star (chG (fun P => ∏ j ∈ T, rootSum θ (e j) P) n x) = if T = L.toFinset then (ε : ℂ) ^ L.length * (Nat.card (GL (Fin n) F) : ℂ) else 0 := by
  intro F _ _ θ m e ε h1 N h2 L
  induction L with
  | nil =>
    intro T _ _ _ hT n hn
    have hT0 : T = ∅ := Finset.card_eq_zero.1 (by simpa using hT)
    subst hT0
    simp only [List.length_nil, mul_zero] at hn
    subst hn
    haveI : Subsingleton (GL (Fin 0) F) := ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩
    haveI : Unique (GL (Fin 0) F) := ⟨⟨1⟩, fun a => Subsingleton.elim _ _⟩
    simp [J_nil, chG, finsum_unique]
  | cons i L ih =>
    intro T hnd hLN hTN hT n hn
    haveI : Fintype F := Fintype.ofFinite F
    have hiS : i ∉ L.toFinset := by simpa using (List.nodup_cons.1 hnd).1
    have hnd' : L.Nodup := (List.nodup_cons.1 hnd).2
    have hb := deg_map_const_fst m e L
    have hn' : n = m + deg (L.map fun i => (m, e i)) := by rw [hn, hb, List.length_cons]; ring
    have hmass := GlobalTheory.T.pairing_harishChandraInduction_charpolyFunction F m (deg (L.map fun i => (m, e i))) n hn' (cusp θ m (e i))
      (J θ (L.map fun i => (m, e i)) (deg (L.map fun i => (m, e i)))) (fun P => ∏ j ∈ T, rootSum θ (e j) P)
    have hs := pair_prod_split (cusp θ m (e i))
      (J θ (L.map fun i => (m, e i)) (deg (L.map fun i => (m, e i))))
      (fun j => rootSum θ (e j)) (fun j => (rootSum_isAdditive_and_pow_X_sub_one F θ (e j)).1) T
    have hiN : i < N := hLN i (List.mem_cons_self ..)
    have hsum := sum_powerset_single i L.toFinset T hiS
      (by rw [List.toFinset_card_of_nodup hnd']; simpa using hT)
      (fun U => ∑ᶠ x : GL (Fin m) F, cusp θ m (e i) x *
        star (∏ j ∈ U, rootSum θ (e j) (Matrix.charpoly (x : Matrix (Fin m) (Fin m) F))))
      (fun U => ∑ᶠ y : GL (Fin (deg (L.map fun i => (m, e i)))) F,
        J θ (L.map fun i => (m, e i)) (deg (L.map fun i => (m, e i))) y *
          star (chG (fun P => ∏ j ∈ T \ U, rootSum θ (e j) P) (deg (L.map fun i => (m, e i))) y))
      ((ε : ℂ) * Nat.card (GL (Fin m) F))
      ((ε : ℂ) ^ L.length * Nat.card (GL (Fin (deg (L.map fun i => (m, e i)))) F))
      (by simpa using h1 i)
      (fun j hj => by simpa [chG] using h2 i j hiN (hTN j hj))
      (fun U hU hU0 => by
        have hsub := Finset.mem_powerset.1 hU
        have hc := Finset.card_sdiff_add_card_eq_card hsub
        have hpos : 0 < U.card := Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 hU0)
        simp only [List.length_cons] at hT
        exact ih (T \ U) hnd' (fun k hk => hLN k (List.mem_cons_of_mem _ hk))
          (fun k hk => hTN k (Finset.mem_sdiff.1 hk).1) (by omega) _ hb)
    beta_reduce at hmass hs hsum
    rw [hs, hsum] at hmass
    have hG : ((Nat.card (GL (Fin m) F) : ℂ) *
        (Nat.card (GL (Fin (deg (L.map fun i => (m, e i)))) F) : ℂ)) ≠ 0 := by
      apply mul_ne_zero <;> exact_mod_cast Nat.card_pos.ne'
    apply mul_left_cancel₀ hG
    refine hmass.trans ?_
    rw [List.toFinset_cons, List.length_cons]
    split_ifs <;> ring

end GlobalTheory.Shin

end
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.lift_all_preserves_degree_and_regularity : ∀ (q l : ℕ) (L : List (ℕ × ℕ)), 2 ≤ q → l.Prime → (∀ p ∈ L, 0 < p.1 ∧ Reg q p.1 p.2) → deg (liftAll q l L) = deg L ∧ ∀ p ∈ liftAll q l L, 0 < p.1 ∧ Reg (q ^ l) p.1 p.2 := by
  first | (exact @GlobalTheory.liftAll_deg_reg) | (exact GlobalTheory.liftAll_deg_reg) | (intros; apply GlobalTheory.liftAll_deg_reg <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin.ListProd

variable {F : Type} [Field F]

theorem deg_cons' (p : ℕ × ℕ) (L : List (ℕ × ℕ)) : deg (p :: L) = p.1 + deg L := by
  simp [deg]

theorem deg_append' (L L' : List (ℕ × ℕ)) : deg (L ++ L') = deg L + deg L' := by
  simp [deg]

theorem deg_perm' {L L' : List (ℕ × ℕ)} (h : L.Perm L') : deg L = deg L' :=
  (h.map Prod.fst).sum_eq

theorem hc_congr_right (a b b' : ℕ) (hb : b = b') (α : GL (Fin a) F → ℂ)
    (β : (m : ℕ) → GL (Fin m) F → ℂ) (n : ℕ) :
    hc a b α (β b) n = hc a b' α (β b') n := by
  subst hb
  rfl

theorem hc_congr_left (a a' b : ℕ) (ha : a = a') (α : (m : ℕ) → GL (Fin m) F → ℂ)
    (β : GL (Fin b) F → ℂ) (n : ℕ) :
    hc a b (α a) β n = hc a' b (α a') β n := by
  subst ha
  rfl

variable [Finite F]

theorem isCl_cusp (θ : AlgebraicClosure F →* ℂ) (m k : ℕ) : IsCl (cusp θ m k) := by

  have h := ((GlobalTheory.T.twistedHarishChandraInductionGL_isTwistedClassFunction F (RingHom.id F) 0 0 m (fun _ => 0) (fun _ => 0)).2.2 (rootSum θ k)).1
  intro x y
  simp only [cusp]
  rw [h x y]

theorem isCl_J (θ : AlgebraicClosure F →* ℂ) (L : List (ℕ × ℕ)) (n : ℕ) : IsCl (J θ L n) := by
  cases L with
  | nil =>
    rw [J_nil]
    intro x y
    rfl
  | cons p L =>
    rw [J_cons]
    exact (GlobalTheory.T.twistedHarishChandraInductionGL_isTwistedClassFunction F (RingHom.id F) _ _ n _ _).2.1

theorem J_append (θ : AlgebraicClosure F →* ℂ) (L L' : List (ℕ × ℕ)) (n : ℕ) (hn : n = deg L + deg L') :
    J θ (L ++ L') n = hc (deg L) (deg L') (J θ L (deg L)) (J θ L' (deg L')) n := by
  induction L generalizing n with
  | nil =>

    have h0 : deg ([] : List (ℕ × ℕ)) = 0 := rfl
    have hn' : n = deg L' := by rw [hn, h0, Nat.zero_add]
    subst hn'
    change J θ L' (deg L') = hc 0 (deg L') (J θ [] 0) (J θ L' (deg L')) (deg L')
    rw [J_nil]
    exact ((GlobalTheory.T.harishChandraInductionGL_one_left_right_unit F (deg L') (J θ L' (deg L')) (isCl_J θ L' _)).1).symm
  | cons p L ih =>

    rw [List.cons_append, J_cons, ih (deg (L ++ L')) (deg_append' L L'), J_cons]
    refine (hc_congr_right p.1 _ _ (deg_append' L L') (cusp θ p.1 p.2)
      (fun m => hc (deg L) (deg L') (J θ L (deg L)) (J θ L' (deg L')) m) n).trans ?_
    refine Eq.trans ?_ (hc_congr_left _ _ (deg L') (deg_cons' p L).symm
      (fun m => hc p.1 (deg L) (cusp θ p.1 p.2) (J θ L (deg L)) m) (J θ L' (deg L')) n)
    have hn' : n = p.1 + deg L + deg L' := by rw [hn, deg_cons']
    exact (GlobalTheory.T.harishChandraInductionGL_assoc F p.1 (deg L) (deg L') n (cusp θ p.1 p.2) (J θ L (deg L)) (J θ L' (deg L'))
      (isCl_cusp θ _ _) (isCl_J θ L _) (isCl_J θ L' _) hn').symm

theorem J_perm (θ : AlgebraicClosure F →* ℂ) (L L' : List (ℕ × ℕ)) (n : ℕ) (hn : n = deg L) (h : L.Perm L') :
    J θ L n = J θ L' n := by
  revert n
  induction h with
  | nil => intro n _; rfl
  | cons p h ih =>
    rename_i l₁ l₂
    intro n _
    rw [J_cons, J_cons, ih (deg l₁) rfl]
    exact hc_congr_right p.1 _ _ (deg_perm' h) (cusp θ p.1 p.2) (J θ l₂) n
  | swap q p l =>

    intro n hn
    rw [J_cons, J_cons, J_cons, J_cons]
    have hcp := isCl_cusp θ p.1 p.2
    have hcq := isCl_cusp θ q.1 q.2
    have hl := isCl_J θ l (deg l)
    have e1 : n = p.1 + q.1 + deg l := by rw [hn, deg_cons', deg_cons', Nat.add_assoc]
    have e2 : n = q.1 + p.1 + deg l := by rw [e1, Nat.add_comm p.1 q.1]
    refine (hc_congr_right p.1 _ _ (deg_cons' q l) (cusp θ p.1 p.2)
      (fun m => hc q.1 (deg l) (cusp θ q.1 q.2) (J θ l (deg l)) m) n).trans ?_
    refine Eq.trans ?_ (hc_congr_right q.1 _ _ (deg_cons' p l).symm (cusp θ q.1 q.2)
      (fun m => hc p.1 (deg l) (cusp θ p.1 p.2) (J θ l (deg l)) m) n)
    rw [← GlobalTheory.T.harishChandraInductionGL_assoc F p.1 q.1 (deg l) n _ _ _ hcp hcq hl e1,
      ← GlobalTheory.T.harishChandraInductionGL_assoc F q.1 p.1 (deg l) n _ _ _ hcq hcp hl e2,
      GlobalTheory.T.harishChandraInductionGL_comm F p.1 q.1 (p.1 + q.1) _ _ hcp hcq rfl]
    exact hc_congr_left _ _ (deg l) (Nat.add_comm p.1 q.1)
      (fun m => hc q.1 p.1 (cusp θ q.1 q.2) (cusp θ p.1 p.2) m) (J θ l (deg l)) n
  | trans h₁ _ ih₁ ih₂ =>
    intro n hn
    exact (ih₁ n hn).trans (ih₂ n (hn.trans (deg_perm' h₁)))

end GlobalTheory.Shin.ListProd


open GlobalTheory.Shin.ListProd in
theorem GlobalTheory.Shin.J_list_props : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ),
    (∀ L n, IsCl (J θ L n)) ∧
    (∀ (L L' : List (ℕ × ℕ)) (n : ℕ), n = deg L + deg L' →
      J θ (L ++ L') n = hc (deg L) (deg L') (J θ L (deg L)) (J θ L' (deg L')) n) ∧
    ∀ (L L' : List (ℕ × ℕ)) (n : ℕ), n = deg L → L.Perm L' → J θ L n = J θ L' n := by
  intro F _ _ θ
  exact ⟨fun L n => isCl_J θ L n, fun L L' n hn => J_append θ L L' n hn,
    fun L L' n hn h => J_perm θ L L' n hn h⟩
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin.ConjDesc

noncomputable section

theorem smul_of_X {F : Type} [Field F] {M N : Type} [AddCommGroup M] [Module F M] [Module F[X] M]
    [IsScalarTower F F[X] M] [AddCommGroup N] [Module F N] [Module F[X] N] [IsScalarTower F F[X] N]
    (e : M ≃ₗ[F] N) (h : ∀ m, e ((X : F[X]) • m) = (X : F[X]) • e m) (p : F[X]) (m : M) :
    e (p • m) = p • e m := by
  revert m
  induction p using Polynomial.induction_on with
  | C a =>
    intro m
    rw [← Polynomial.algebraMap_eq, algebraMap_smul, algebraMap_smul]
    exact e.map_smul a m
  | add p q hp hq =>
    intro m
    rw [add_smul, add_smul, map_add (f := _), hp, hq]
  | monomial k a ih =>
    intro m
    rw [pow_succ, ← mul_assoc, mul_smul (C a * X ^ k) X m, ih, h, ← mul_smul]

def equivOfX {F : Type} [Field F] {M N : Type} [AddCommGroup M] [Module F M] [Module F[X] M]
    [IsScalarTower F F[X] M] [AddCommGroup N] [Module F N] [Module F[X] N] [IsScalarTower F F[X] N]
    (e : M ≃ₗ[F] N) (h : ∀ m, e ((X : F[X]) • m) = (X : F[X]) • e m) : M ≃ₗ[F[X]] N :=
  { e with
    map_smul' := fun p m => smul_of_X e h p m }

def swapE (F : Type) [Field F] (a b : ℕ) : (Fin a → Fin b → F) ≃ₗ[F] (Fin b → Fin a → F) :=
  { Equiv.piComm (fun (_ : Fin a) (_ : Fin b) => F) with map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

def coordE {F F' : Type} [Field F] [Field F'] [Algebra F F'] {l : ℕ} (b : Module.Basis (Fin l) F F') (n : ℕ) :
    (Fin n → F') ≃ₗ[F] (Fin l → Fin n → F) :=
  (LinearEquiv.piCongrRight fun _ : Fin n => b.equivFun).trans (swapE F n l)

theorem coordE_apply {F F' : Type} [Field F] [Field F'] [Algebra F F'] {l : ℕ} (b : Module.Basis (Fin l) F F') (n : ℕ)
    (v : Fin n → F') (k : Fin l) (i : Fin n) : coordE b n v k i = b.equivFun (v i) k := rfl

theorem coordE_mulVec {F F' : Type} [Field F] [Field F'] [Algebra F F'] {l : ℕ} (b : Module.Basis (Fin l) F F') (n : ℕ)
    (A : Matrix (Fin n) (Fin n) F) (v : Fin n → F') :
    coordE b n (Matrix.mulVec (A.map (algebraMap F F')) v) = fun k => Matrix.mulVec A (coordE b n v k) := by
  funext k i
  rw [coordE_apply]

  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, ← Algebra.smul_def, map_sum, map_smul,
  Finset.sum_apply, Pi.smul_apply, smul_eq_mul, coordE_apply]

end

end GlobalTheory.Shin.ConjDesc

namespace GlobalTheory.Shin


open ConjDesc in
theorem isConj_of_isConj_incl : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (n : ℕ)
    (γ γ' : GL (Fin n) F), IsConj (incl F F' n γ) (incl F F' n γ') → IsConj γ γ' := by
  intro F F' _ _ _ _ n γ γ' hc
  obtain ⟨c, hc⟩ := isConj_iff.mp hc
  have hcA : (c : Matrix (Fin n) (Fin n) F') * ((γ : Matrix (Fin n) (Fin n) F).map (algebraMap F F')) =
      ((γ' : Matrix (Fin n) (Fin n) F).map (algebraMap F F')) * (c : Matrix (Fin n) (Fin n) F') := by
    have h2 : c * incl F F' n γ = incl F F' n γ' * c := by rw [← hc]; group
    exact congrArg (fun x : GL (Fin n) F' => (x : Matrix (Fin n) (Fin n) F')) h2
  haveI : Finite F := Finite.of_injective _ (algebraMap F F').injective
  haveI : FiniteDimensional F F' := inferInstance
  have hl : 0 < Module.finrank F F' := Module.finrank_pos
  let b := Module.finBasis F F'
  let f := Matrix.toLin' (γ : Matrix (Fin n) (Fin n) F)
  let g := Matrix.toLin' (γ' : Matrix (Fin n) (Fin n) F)
  let Fc : (Fin n → F') ≃ₗ[F] (Fin n → F') :=
    (LinearEquiv.ofLinear (Matrix.toLin' (c : Matrix (Fin n) (Fin n) F'))
      (Matrix.toLin' ((c⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F'))
      (by rw [← Matrix.toLin'_mul, Units.mul_inv, Matrix.toLin'_one])
      (by rw [← Matrix.toLin'_mul, Units.inv_mul, Matrix.toLin'_one])).restrictScalars F
  have hFc : ∀ w, Fc w = Matrix.mulVec (c : Matrix (Fin n) (Fin n) F') w := fun w => rfl
  let core : (Fin (Module.finrank F F') → Fin n → F) ≃ₗ[F] (Fin (Module.finrank F F') → Fin n → F) :=
    (coordE b n).symm.trans (Fc.trans (coordE b n))
  have hcore : ∀ x, core (fun k => f (x k)) = fun k => g (core x k) := by
    intro x
    obtain ⟨v, rfl⟩ := (coordE b n).surjective x
    have h1 : (fun k => f (coordE b n v k)) =
        coordE b n (Matrix.mulVec ((γ : Matrix (Fin n) (Fin n) F).map (algebraMap F F')) v) := by
      rw [coordE_mulVec]; rfl
    rw [h1]
    show coordE b n (Fc ((coordE b n).symm (coordE b n
        (Matrix.mulVec ((γ : Matrix (Fin n) (Fin n) F).map (algebraMap F F')) v)))) =
      fun k => g (coordE b n (Fc ((coordE b n).symm (coordE b n v))) k)
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, hFc, hFc, Matrix.mulVec_mulVec, hcA,
      ← Matrix.mulVec_mulVec, coordE_mulVec]
    rfl
  let Θ : (Fin (Module.finrank F F') → Module.AEval' f) ≃ₗ[F] (Fin (Module.finrank F F') → Module.AEval' g) :=
    (LinearEquiv.piCongrRight fun _ => (Module.AEval'.of f).symm).trans
      (core.trans (LinearEquiv.piCongrRight fun _ => Module.AEval'.of g))
  have hΘ : ∀ x, Θ ((X : F[X]) • x) = (X : F[X]) • Θ x := by
    intro x
    have h3 : (fun k => (Module.AEval'.of f).symm (((X : F[X]) • x) k)) =
        fun k => f ((Module.AEval'.of f).symm (x k)) :=
      funext fun k => Module.AEval'.of_symm_X_smul f (x k)
    funext k
    show Module.AEval'.of g (core (fun k => (Module.AEval'.of f).symm (((X : F[X]) • x) k)) k) =
      (X : F[X]) • Module.AEval'.of g (core (fun k => (Module.AEval'.of f).symm (x k)) k)
    rw [h3, hcore, Module.AEval'.X_smul_of]
  haveI : Finite (Module.AEval' f) := Finite.of_equiv _ (Module.AEval'.of f).toEquiv
  haveI : Finite (Module.AEval' g) := Finite.of_equiv _ (Module.AEval'.of g).toEquiv
  obtain ⟨ψ⟩ := GlobalTheory.T.nonempty_linearEquiv_of_pi_fin_pow_finite F[X] (Module.AEval' f) (Module.AEval' g) (Module.finrank F F') hl
    ⟨equivOfX Θ hΘ⟩
  let e : (Fin n → F) ≃ₗ[F] (Fin n → F) :=
    (Module.AEval'.of f).trans ((ψ.restrictScalars F).trans (Module.AEval'.of g).symm)
  have he : ∀ v, e (f v) = g (e v) := by
    intro v
    have h1 : Module.AEval'.of f (f v) = (X : F[X]) • Module.AEval'.of f v :=
      (Module.AEval'.X_smul_of f v).symm
    simp only [e, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply, h1, map_smul]
    exact Module.AEval'.of_symm_X_smul g _
  let P : GL (Fin n) F := ⟨LinearMap.toMatrix' e.toLinearMap, LinearMap.toMatrix' e.symm.toLinearMap,
    by rw [← LinearMap.toMatrix'_comp]; simp, by rw [← LinearMap.toMatrix'_comp]; simp⟩
  refine isConj_iff.mpr ⟨P, ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  apply Units.ext
  have h4 : e.toLinearMap ∘ₗ f = g ∘ₗ e.toLinearMap := LinearMap.ext he
  have h5 := congrArg LinearMap.toMatrix' h4
  rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp] at h5
  simpa [P, f, g, LinearMap.toMatrix'_toLin'] using h5

end GlobalTheory.Shin
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.exists_cofiltered_limit_affine_etale_of_isStalk' : ∀ (S : Scheme.{0}) (O : Type) [CommRing O] (s : Spec (CommRingCat.of O) ⟶ S), IsStalk O s → ∃ (I : Type) (_ : SmallCategory I) (_ : IsCofiltered I) (G : I ⥤ Over S) (π : (Functor.const I).obj (Over.mk s) ⟶ G), Nonempty (IsLimit (Cone.mk _ π)) ∧ ∀ i, IsAffine (G.obj i).left ∧ Etale (G.obj i).hom := by
  first | (exact @GlobalTheory.EtC.exists_cofiltered_limit_affine_etale_of_isStalk) | (exact GlobalTheory.EtC.exists_cofiltered_limit_affine_etale_of_isStalk) | (intros; apply GlobalTheory.EtC.exists_cofiltered_limit_affine_etale_of_isStalk  <;> assumption)
end

section

open CategoryTheory Coalgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.HTPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.projective_rankAtStalk_of_const_fibreDim : ∀ (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] (M : Type) [AddCommGroup M] [Module O M] [Module.Finite O M] (n : ℕ), (∀ q : PrimeSpectrum O, fibreDim M q = n) → Module.Projective O M ∧ ∀ q : PrimeSpectrum O, Module.rankAtStalk M q = n := by
  first | exact @GlobalTheory.ConstFibreFree.projective_and_rankAtStalk_of_fibreDim | exact GlobalTheory.ConstFibreFree.projective_and_rankAtStalk_of_fibreDim | (intros; apply GlobalTheory.ConstFibreFree.projective_and_rankAtStalk_of_fibreDim <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.baseChange_cechNerveAugmentation_iso : ∀ (S W V : Scheme.{0}) (r : W ⟶ S) (f : V ⟶ W) (U : Over S), ∃ (e₁ : cech (pullback.snd f (pullback.fst r U.hom)) ≅ (bc (cechAug f ≫ sch.map r)).obj U) (e₂ : sch.obj (pullback r U.hom) ≅ (bc (sch.map r)).obj U), e₁.hom ≫ (bcMap (cechAug f) (sch.map r)).app U = cechAug _ ≫ e₂.hom := by
  first | (exact @GlobalTheory.EtC.bc_cechAug_iso) | (exact GlobalTheory.EtC.bc_cechAug_iso) | (intros; apply GlobalTheory.EtC.bc_cechAug_iso  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.exists_etaleFaithfullyFlat_refining_etale_surjection : ∀ (A : CommRingCat.{0}) (V : Scheme.{0}) (f : V ⟶ Spec A), Etale f → Surjective f → ∃ (B : CommRingCat.{0}) (g : A ⟶ B) (h : Spec B ⟶ V), EtFF g ∧ h ≫ f = Spec.map g := by
  first | (exact @GlobalTheory.EtC.exists_etFF_refine_of_etale_surjective) | (exact GlobalTheory.EtC.exists_etFF_refine_of_etale_surjective) | (intros; apply GlobalTheory.EtC.exists_etFF_refine_of_etale_surjective  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.sheafSection_eq_zero_at_stage_of_filtered_colimit : ∀ (R : Type) [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) (F : Shv R) (η : M ⟶ onRings F), PreservesFilteredColimitsOfSize.{0, 0} M → (∀ (A : CommRingCat.{0}) (x : (onRings F).obj A), ∃ (ι : Type) (_ : Finite ι) (B : ι → CommRingCat.{0}) (g : ∀ i, A ⟶ B i) (m : ∀ i, M.obj (B i)), (∀ i, (g i).hom.Etale) ∧ (∀ p : Spec A, ∃ i v, Spec.map (g i) v = p) ∧ ∀ i, (η.app (B i)).hom (m i) = ((onRings F).map (g i)).hom x) → (∀ (A : CommRingCat.{0}) (m : M.obj A), (η.app A).hom m = 0 → ∃ (ι : Type) (_ : Finite ι) (B : ι → CommRingCat.{0}) (g : ∀ i, A ⟶ B i), (∀ i, (g i).hom.Etale) ∧ (∀ p : Spec A, ∃ i v, Spec.map (g i) v = p) ∧ ∀ i, (M.map (g i)).hom m = 0) → ∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ (j : J) (y : (onRings F).obj (D.obj j)), ((onRings F).map (c.ι.app j)).hom y = 0 → ∃ (k : J) (f : j ⟶ k), ((onRings F).map (D.map f)).hom y = 0 := by
  first | (exact @GlobalTheory.EtC.FilteredSections.eq_zero_at_stage_of_map_colimit_eq_zero) | (exact GlobalTheory.EtC.FilteredSections.eq_zero_at_stage_of_map_colimit_eq_zero) | (intros; apply GlobalTheory.EtC.FilteredSections.eq_zero_at_stage_of_map_colimit_eq_zero  <;> assumption)
end
