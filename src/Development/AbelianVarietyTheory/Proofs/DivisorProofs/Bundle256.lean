module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle005
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle155
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam.Act

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
theorem _root_.GlobalTheory.WpFam.Act.redGL_mul (N : ℕ) (γ δ : SL(2, ℤ)) :
    _root_.GlobalTheory.WpFam.redGL N (γ * δ) = _root_.GlobalTheory.WpFam.redGL N γ * _root_.GlobalTheory.WpFam.redGL N δ := by
  unfold _root_.GlobalTheory.WpFam.redGL
  simp [map_mul]

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
theorem _root_.GlobalTheory.WpFam.Act.redGL_one (N : ℕ) : _root_.GlobalTheory.WpFam.redGL N 1 = 1 := by
  unfold _root_.GlobalTheory.WpFam.redGL
  simp

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
theorem _root_.GlobalTheory.WpFam.Act.vmul_vmul {N : ℕ} (x : Fin 2 → ZMod N) (α β : GL (Fin 2) (ZMod N)) :
    _root_.GlobalTheory.WpFam.vmul (_root_.GlobalTheory.WpFam.vmul x α) β = _root_.GlobalTheory.WpFam.vmul x (α * β) := by
  unfold _root_.GlobalTheory.WpFam.vmul
  simp [Matrix.vecMul_vecMul]

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
theorem _root_.GlobalTheory.WpFam.Act.vmul_one {N : ℕ} (x : Fin 2 → ZMod N) : _root_.GlobalTheory.WpFam.vmul x 1 = x := by
  unfold _root_.GlobalTheory.WpFam.vmul
  simp

theorem isRAct_gact (N : ℕ) (D : GL (Fin 2) (ZMod N)) : IsRAct (gact N D) := by
  constructor
  · intro x; simp [gact, redGL_one]
  · intro x γ δ; simp only [gact, redGL_mul]; group


open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
theorem _root_.GlobalTheory.WpFam.Act.rightActions : ∀ (N : ℕ), _root_.GlobalTheory.QFam.IsRAct (_root_.GlobalTheory.WpFam.vact N) ∧ (∀ D, _root_.GlobalTheory.QFam.IsRAct (_root_.GlobalTheory.WpFam.gact N D)) ∧ (∀ (x : Fin 2 → ZMod N) α β, _root_.GlobalTheory.WpFam.vmul (_root_.GlobalTheory.WpFam.vmul x α) β = _root_.GlobalTheory.WpFam.vmul x (α * β)) ∧ (∀ x : Fin 2 → ZMod N, _root_.GlobalTheory.WpFam.vmul x 1 = x) ∧ (∀ (x : Fin 2 → ZMod N) α, _root_.GlobalTheory.WpFam.vmul x α = 0 ↔ x = 0) ∧ (∀ (M : ℕ) (x : Fin 2 → ZMod N) α, _root_.GlobalTheory.WpFam.vmul (M • x) α = M • _root_.GlobalTheory.WpFam.vmul x α) ∧ (∀ (x : Fin 2 → ZMod N) (a : (ZMod N)ˣ), _root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a) = ![x 0, (a : ZMod N) * x 1]) ∧ (∀ γ δ, _root_.GlobalTheory.WpFam.redGL N (γ * δ) = _root_.GlobalTheory.WpFam.redGL N γ * _root_.GlobalTheory.WpFam.redGL N δ) ∧ _root_.GlobalTheory.WpFam.redGL N 1 = 1 := by
  intro N
  refine ⟨?_, ?_, _root_.GlobalTheory.WpFam.Act.vmul_vmul, _root_.GlobalTheory.WpFam.Act.vmul_one, ?_, ?_, ?_,
    _root_.GlobalTheory.WpFam.Act.redGL_mul N, _root_.GlobalTheory.WpFam.Act.redGL_one N⟩
  · refine ⟨fun x => ?_, fun x γ δ => ?_⟩
    · unfold _root_.GlobalTheory.WpFam.vact
      rw [_root_.GlobalTheory.WpFam.Act.redGL_one, _root_.GlobalTheory.WpFam.Act.vmul_one]
    · unfold _root_.GlobalTheory.WpFam.vact
      rw [_root_.GlobalTheory.WpFam.Act.vmul_vmul, _root_.GlobalTheory.WpFam.Act.redGL_mul]
  · intro D
    refine ⟨fun α => ?_, fun α γ δ => ?_⟩
    · unfold _root_.GlobalTheory.WpFam.gact
      rw [_root_.GlobalTheory.WpFam.Act.redGL_one]
      group
    · unfold _root_.GlobalTheory.WpFam.gact
      rw [_root_.GlobalTheory.WpFam.Act.redGL_mul]
      group
  · intro x α
    constructor
    · intro h
      have key := congrArg (fun y => _root_.GlobalTheory.WpFam.vmul y α⁻¹) h
      simp only [_root_.GlobalTheory.WpFam.Act.vmul_vmul, mul_inv_cancel, _root_.GlobalTheory.WpFam.Act.vmul_one] at key
      rw [key]
      unfold _root_.GlobalTheory.WpFam.vmul
      simp
    · rintro rfl
      unfold _root_.GlobalTheory.WpFam.vmul
      simp
  · intro M x α
    unfold _root_.GlobalTheory.WpFam.vmul
    rw [Matrix.smul_vecMul]
  · intro x a
    unfold _root_.GlobalTheory.WpFam.vmul _root_.GlobalTheory.WpFam.dg
    ext i
    fin_cases i <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, mul_comm]

end GlobalTheory.WpFam.Act
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin.IndIso

theorem sum_dite_mem {G M : Type} [Group G] [Fintype G] [AddCommMonoid M] (H : Subgroup G)
    (f : H → M) : ∑ z : G, (if h : z ∈ H then f ⟨z, h⟩ else 0) = ∑ h : H, f h := by
  rw [← Fintype.sum_subtype_add_sum_subtype (fun z => z ∈ H)]
  have h2 : ∑ i : {x // ¬ x ∈ H}, (if h : (i : G) ∈ H then f ⟨i, h⟩ else 0) = 0 :=
    Finset.sum_eq_zero fun i _ => dif_neg i.2
  rw [h2, add_zero]
  exact Fintype.sum_congr _ _ fun i => dif_pos i.2

theorem star_ext_zero {G : Type} [Group G] (H : Subgroup G) (c : H → ℂ) (z : G) :
    star (ext0 H c z) = ext0 H (fun h => star (c h)) z := by
  unfold ext0; split_ifs <;> simp

theorem reidx {G M : Type} [Group G] [Fintype G] [AddCommMonoid M] [Module ℂ M] (H : Subgroup G)
    (a b : G) (c : H → ℂ) (T : G → M) :
    ∑ x : G, ext0 H c (a * x * b) • T x = ∑ h : H, c h • T (a⁻¹ * h * b⁻¹) := by
  rw [Fintype.sum_equiv ((Equiv.mulLeft a).trans (Equiv.mulRight b)) _
    (fun z => ext0 H c z • T (a⁻¹ * z * b⁻¹)) (fun x => by simp [mul_assoc])]
  rw [← sum_dite_mem H (fun h => c h • T (a⁻¹ * h * b⁻¹))]
  refine Fintype.sum_congr _ _ fun z => ?_
  unfold ext0; split_ifs <;> simp

end GlobalTheory.Shin.IndIso

namespace GlobalTheory.Shin.IndIso

theorem kills_ind : ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G) (τ : G → G) (φ Y : H → ℂ), Kills φ Y →
    Kills (fun x => (Nat.card H : ℂ)⁻¹ * ∑ᶠ y : G, ext0 H φ (y⁻¹ * x * τ y)) (ind H Y) := by
  intro G _ _ H τ φ Y hK V _ _ _ ρ hρ
  letI : Fintype G := Fintype.ofFinite G
  have hHc : (Nat.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hGc : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'

  have hres : ∑ᶠ h : H, star (Y h) * LinearMap.trace ℂ V ((ρ.comp H.subtype) h) = 0 := by
    rw [finsum_eq_sum_of_fintype]
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
    simp only [ind, finsum_eq_sum_of_fintype, star_mul', star_inv₀, star_natCast, star_sum, star_ext_zero] at hρ
    simp only [mul_assoc, ← Finset.mul_sum] at hρ
    have hρ' := (mul_eq_zero.mp hρ).resolve_left (inv_ne_zero hHc)
    have trc : ∀ g x : G, LinearMap.trace ℂ V (ρ (g * (x * g⁻¹))) = LinearMap.trace ℂ V (ρ x) := by
      intro g x
      rw [map_mul ρ, map_mul ρ, LinearMap.trace_mul_comm, mul_assoc, ← map_mul ρ, ← map_mul ρ]
      simp
    simp only [Finset.sum_mul] at hρ'
    rw [Finset.sum_comm] at hρ'
    have key : ∀ g : G, ∑ x : G, ext0 H (fun h => star (Y h)) (g⁻¹ * (x * g)) * LinearMap.trace ℂ V (ρ x)
        = ∑ h : H, star (Y h) * LinearMap.trace ℂ V (ρ h) := by
      intro g
      have := reidx (M := ℂ) H g⁻¹ g (fun h => star (Y h)) (fun x => LinearMap.trace ℂ V (ρ x))
      simp only [smul_eq_mul, inv_inv, mul_assoc] at this
      rw [this]
      exact Fintype.sum_congr _ _ fun h => by rw [trc]
    simp only [key, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hρ'
    rw [← Nat.card_eq_fintype_card] at hρ'
    exact (mul_eq_zero.mp hρ').resolve_left hGc
  have hk := hK V (ρ.comp H.subtype) hres
  rw [finsum_eq_sum_of_fintype] at hk
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype] at hk

  rw [finsum_eq_sum_of_fintype]
  simp only [finsum_eq_sum_of_fintype, star_mul', star_inv₀, star_natCast, star_sum, star_ext_zero, mul_smul,
    Finset.sum_smul]
  rw [← Finset.smul_sum, Finset.sum_comm]
  have key2 : ∀ y : G, ∑ x : G, ext0 H (fun h => star (φ h)) (y⁻¹ * x * τ y) • ρ x = 0 := by
    intro y
    rw [reidx H y⁻¹ (τ y) (fun h => star (φ h)) (fun x => ρ x)]
    simp only [inv_inv, map_mul]
    have : ∑ h : H, star (φ h) • (ρ y * ρ h * ρ (τ y)⁻¹) = ρ y * (∑ h : H, star (φ h) • ρ h) * ρ (τ y)⁻¹ := by
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Fintype.sum_congr _ _ fun h => ?_
      rw [mul_smul_comm, smul_mul_assoc]
    rw [this, hk, mul_zero, zero_mul]
  simp only [key2, Finset.sum_const_zero, smul_zero]

end GlobalTheory.Shin.IndIso
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

noncomputable section

namespace GlobalTheory.Shin.TensorInd

section Paths

variable {n : Type} [Fintype n] [DecidableEq n]

theorem trace_reindex_eq {m : Type} [Fintype m] (e : n ≃ m) (A : Matrix n n ℂ) :
    Matrix.trace (Matrix.reindex e e A) = Matrix.trace A := by
  simp only [Matrix.trace, Matrix.diag, Matrix.reindex_apply, Matrix.submatrix_apply]
  exact Fintype.sum_equiv e.symm _ _ (fun _ => rfl)

theorem path_sum : ∀ (k : ℕ) (B : ℕ → Matrix n n ℂ) (a c : n),
    ∑ w : Fin k → n, ∏ i : Fin (k + 1),
      B i ((Fin.cons a (Fin.snoc w c : Fin (k + 1) → n) : Fin (k + 2) → n) i.castSucc)
        ((Fin.cons a (Fin.snoc w c : Fin (k + 1) → n) : Fin (k + 2) → n) i.succ)
      = ((List.range (k + 1)).map B).prod a c := by
  intro k
  induction k with
  | zero =>
    intro B a c
    simp [Fin.snoc]
  | succ k ih =>
    intro B a c
    rw [List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map, Matrix.mul_apply]
    rw [← (Fin.consEquiv fun _ => n).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [← ih (B ∘ Nat.succ) x c, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    have hc : (Fin.consEquiv fun _ => n) (x, w) = Fin.cons x w := rfl
    rw [Fin.prod_univ_succ, hc, ← Fin.cons_snoc_eq_snoc_cons]
    simp only [Fin.cons_zero, Fin.castSucc_zero, Fin.cons_succ, ← Fin.succ_castSucc, Function.comp_apply,
      Fin.val_succ, Fin.val_zero, Nat.succ_eq_add_one]

theorem cyc_sum (k : ℕ) (B : ℕ → Matrix n n ℂ) :
    ∑ w : Fin (k + 1) → n, ∏ i : Fin (k + 1), B i (w i) (w (i + 1))
      = Matrix.trace ((List.range (k + 1)).map B).prod := by
  rw [← (Fin.consEquiv fun _ => n).sum_comp, Fintype.sum_prod_type]
  simp only [Matrix.trace, Matrix.diag]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← path_sum k B a a]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  refine Finset.prod_congr rfl (fun i _ => ?_)
  have hc : (Fin.consEquiv fun _ => n) (a, w) = Fin.cons a w := rfl
  have h1 : (Fin.cons a w : Fin (k + 1) → n) i
      = (Fin.cons a (Fin.snoc w a : Fin (k + 1) → n) : Fin (k + 2) → n) i.castSucc := by
    cases i using Fin.cases with
    | zero => simp
    | succ j => rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ, Fin.snoc_castSucc]
  have h2 : (Fin.cons a w : Fin (k + 1) → n) (i + 1)
      = (Fin.cons a (Fin.snoc w a : Fin (k + 1) → n) : Fin (k + 2) → n) i.succ := by
    rw [Fin.cons_succ]
    cases i using Fin.lastCases with
    | last => rw [Fin.last_add_one, Fin.snoc_last, Fin.cons_zero]
    | cast j => rw [Fin.coeSucc_eq_succ, Fin.cons_succ, Fin.snoc_castSucc]
  rw [hc, h1, h2]

end Paths

section Rep

variable {G Γ : Type} [Group G] [Group Γ] [Fintype Γ] {d : ℕ}

def ker (ρ : G →* GL (Fin d) ℂ) (φ : Γ →* MulAut G) (g : G) (r : Γ) :
    Matrix (Γ → Fin d) (Γ → Fin d) ℂ :=
  fun u v => ∏ t, (ρ (φ t g) : Matrix (Fin d) (Fin d) ℂ) (u t) (v (t * r))

theorem ker_one (ρ : G →* GL (Fin d) ℂ) (φ : Γ →* MulAut G) : ker ρ φ 1 1 = 1 := by
  ext u v
  simp only [ker, map_one, Units.val_one, mul_one]
  by_cases h : u = v
  · subst h
    simp
  · obtain ⟨t, ht⟩ := Function.ne_iff.1 h
    rw [Matrix.one_apply_ne h]
    exact Finset.prod_eq_zero (Finset.mem_univ t) (Matrix.one_apply_ne ht)

theorem ker_mul (ρ : G →* GL (Fin d) ℂ) (φ : Γ →* MulAut G) (g₁ g₂ : G) (r₁ r₂ : Γ) :
    ker ρ φ g₁ r₁ * ker ρ φ g₂ r₂ = ker ρ φ (g₁ * φ r₁ g₂) (r₁ * r₂) := by
  ext u v
  simp only [Matrix.mul_apply, ker]
  have hre : ∀ w : Γ → Fin d, ∏ t, (ρ (φ t g₂) : Matrix (Fin d) (Fin d) ℂ) (w t) (v (t * r₂))
      = ∏ t, (ρ (φ (t * r₁) g₂) : Matrix (Fin d) (Fin d) ℂ) (w (t * r₁)) (v (t * r₁ * r₂)) :=
    fun w => (Fintype.prod_equiv (Equiv.mulRight r₁) _ _ (fun t => rfl)).symm
  simp_rw [hre, ← Finset.prod_mul_distrib]
  rw [← (Equiv.arrowCongr (Equiv.mulRight r₁) (Equiv.refl (Fin d))).sum_comp]
  simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply, Equiv.coe_mulRight,
    Equiv.mulRight_symm, mul_inv_cancel_right, id]
  refine (Fintype.prod_sum (fun t (j : Fin d) =>
    (ρ (φ t g₁) : Matrix (Fin d) (Fin d) ℂ) (u t) j *
      (ρ (φ (t * r₁) g₂) : Matrix (Fin d) (Fin d) ℂ) j (v (t * r₁ * r₂)))).symm.trans ?_
  refine Finset.prod_congr rfl (fun t _ => ?_)
  rw [map_mul (φ t), ← MulAut.mul_apply, ← map_mul φ, map_mul ρ, Units.val_mul, Matrix.mul_apply, mul_assoc]

def tensRep (ρ : G →* GL (Fin d) ℂ) (φ : Γ →* MulAut G) : G ⋊[φ] Γ →* Matrix (Γ → Fin d) (Γ → Fin d) ℂ where
  toFun x := ker ρ φ x.left x.right
  map_one' := by simpa using ker_one ρ φ
  map_mul' x y := by rw [ker_mul]; simp

theorem trace_ker_one (ρ : G →* GL (Fin d) ℂ) (φ : Γ →* MulAut G) (g : G) :
    Matrix.trace (ker ρ φ g 1) = ∏ t, Matrix.trace (ρ (φ t g) : Matrix (Fin d) (Fin d) ℂ) := by
  simp only [Matrix.trace, Matrix.diag, ker, mul_one]
  rw [Fintype.prod_sum]

end Rep

end GlobalTheory.Shin.TensorInd

namespace GlobalTheory.Shin.TensorInd

variable {G Γ : Type} [Group G] [Group Γ] [Fintype Γ] {d : ℕ}

theorem trace_ker_gen (ρ : G →* GL (Fin d) ℂ) (φ : Γ →* MulAut G) (s : Γ)
    (hs : ∀ t : Γ, t ∈ Subgroup.zpowers s) (δ : G) :
    Matrix.trace (ker ρ φ δ s) = Matrix.trace (((List.range (Nat.card Γ)).map
      fun i => (ρ (φ (s ^ i) δ) : Matrix (Fin d) (Fin d) ℂ)).prod) := by
  have hl : orderOf s = Nat.card Γ := orderOf_eq_card_of_forall_mem_zpowers hs
  obtain ⟨k, hk⟩ : ∃ k, Nat.card Γ = k + 1 :=
    Nat.exists_eq_succ_of_ne_zero (Nat.card_pos (α := Γ)).ne'
  rw [hk] at hl ⊢
  have hinj : Function.Injective (fun i : Fin (k + 1) => s ^ (i : ℕ)) := by
    intro i j hij
    have := pow_injOn_Iio_orderOf (x := s) (by rw [hl]; exact i.2) (by rw [hl]; exact j.2) hij
    exact Fin.ext this
  have hbij : Function.Bijective (fun i : Fin (k + 1) => s ^ (i : ℕ)) := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hinj, ?_⟩
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, hk]
  let e : Fin (k + 1) ≃ Γ := Equiv.ofBijective _ hbij
  have he : ∀ i : Fin (k + 1), e i * s = e (i + 1) := by
    intro i
    show s ^ (i : ℕ) * s = s ^ ((i + 1 : Fin (k + 1)) : ℕ)
    have hv : ((i + 1 : Fin (k + 1)) : ℕ) = ((i : ℕ) + 1) % orderOf s := by
      rw [hl, Fin.val_add_one]
      split_ifs with h
      · subst h; simp
      · rw [Nat.mod_eq_of_lt]
        have := Fin.val_lt_last h
        omega
    rw [hv, pow_mod_orderOf, pow_succ]
  rw [← cyc_sum k (fun i => (ρ (φ (s ^ i) δ) : Matrix (Fin d) (Fin d) ℂ))]
  simp only [Matrix.trace, Matrix.diag, ker]
  rw [← (Equiv.arrowCongr e (Equiv.refl (Fin d))).sum_comp]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [← e.prod_comp]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply, id, he, Equiv.symm_apply_apply]
  rfl

theorem exists_tensorInduction_char : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (∀ t : Γ, t ∈ Subgroup.zpowers s) → ∀ χ : G → ℂ, IsChar ℂ ℂ χ → ∃ X : G ⋊[φ] Γ → ℂ, IsChar ℂ ℂ X ∧ (∀ g, X (inl g) = ∏ t : Γ, χ (φ t g)) ∧ ∀ δ, X (inl δ * inr s) = χ (nrmG φ s (Nat.card Γ) δ) := by
  intro G Γ _ _ _ _ φ s hs χ hχ
  obtain ⟨d, ρ, hρ⟩ := (matrixChar_iff_isChar G χ).2 hχ
  let e := Fintype.equivFin (Γ → Fin d)
  let R : G ⋊[φ] Γ →* GL (Fin (Fintype.card (Γ → Fin d))) ℂ := MonoidHom.toHomUnits
    (((Matrix.reindexAlgEquiv ℂ ℂ e).toMulEquiv.toMonoidHom).comp (tensRep ρ φ))
  refine ⟨fun x => Matrix.trace (tensRep ρ φ x), ?_, ?_, ?_⟩
  · refine (matrixChar_iff_isChar _ _).1 ⟨_, R, fun x => ?_⟩
    show _ = Matrix.trace (Matrix.reindexAlgEquiv ℂ ℂ e (tensRep ρ φ x))
    rw [Matrix.reindexAlgEquiv_apply, trace_reindex_eq]
  · intro g
    show Matrix.trace (ker ρ φ (inl g).left (inl g).right) = _
    rw [left_inl, right_inl, trace_ker_one]
    exact Finset.prod_congr rfl (fun t _ => (hρ _).symm)
  · intro δ
    show Matrix.trace (ker ρ φ (inl δ * inr s).left (inl δ * inr s).right) = _
    have h1 : (inl δ * inr s : G ⋊[φ] Γ).left = δ := by simp
    have h2 : (inl δ * inr s : G ⋊[φ] Γ).right = s := by simp
    rw [h1, h2, trace_ker_gen ρ φ s hs δ, hρ, nrmG]
    congr 1
    have hm := map_list_prod ((Units.coeHom (Matrix (Fin d) (Fin d) ℂ)).comp ρ)
      ((List.range (Nat.card Γ)).map fun i => φ (s ^ i) δ)
    rw [List.map_map] at hm
    exact hm.symm

end GlobalTheory.Shin.TensorInd
end
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam.AddCharZMod

theorem ch_eq (N : ℕ) [NeZero N] (j : ZMod N) : ch N j = ZMod.stdAddChar j := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  rfl

theorem main : ∀ (N : ℕ) [NeZero N], (∀ n : ℤ, ch N (n : ZMod N) = Complex.exp (2 * Real.pi * Complex.I * n / N)) ∧ (∀ i j, ch N (i + j) = ch N i * ch N j) ∧ ch N 0 = 1 ∧ (∀ j, ch N j = 1 ↔ j = 0) ∧ (∀ (m : ℕ) j, ch N ((m : ZMod N) * j) = ch N j ^ m) ∧ (∀ j, ch N (-j) = (ch N j)⁻¹) ∧ (∀ j, ‖ch N j‖ = 1) ∧ (∀ j, IsIntegral ℤ (ch N j)) := by
  intro N _
  have hpow : ∀ (m : ℕ) (j : ZMod N), ch N ((m : ZMod N) * j) = ch N j ^ m := by
    intro m j
    rw [ch_eq, ch_eq, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]
  have hadd : ∀ i j, ch N (i + j) = ch N i * ch N j := by
    intro i j
    rw [ch_eq, ch_eq, ch_eq]
    exact AddChar.map_add_eq_mul _ i j
  have hzero : ch N 0 = 1 := by
    rw [ch_eq]
    exact AddChar.map_zero_eq_one _
  refine ⟨fun n => ?_, hadd, hzero, fun j => ?_, hpow, fun j => ?_, fun j => ?_, fun j => ?_⟩
  · rw [ch_eq]
    exact ZMod.stdAddChar_coe n
  · rw [ch_eq, ← (ZMod.stdAddChar (N := N)).map_zero_eq_one, ZMod.injective_stdAddChar.eq_iff]
  · have h : ch N (-j) * ch N j = 1 := by
      rw [← hadd, neg_add_cancel, hzero]
    exact eq_inv_of_mul_eq_one_left h
  · rw [ch_eq, ZMod.stdAddChar_apply]
    exact Circle.norm_coe _
  · have h : ch N j ^ N = 1 := by
      rw [← hpow, ZMod.natCast_self, zero_mul, hzero]
    refine IsIntegral.of_pow (Nat.pos_of_neZero N) ?_
    rw [h]
    exact isIntegral_one

end GlobalTheory.WpFam.AddCharZMod
end

section

open NumberField Matrix GlobalTheory.AdLat GlobalTheory.UCls

noncomputable section
namespace GlobalTheory
open IsDedekindDomain
open scoped TensorProduct

theorem isTA_det_of_isUA {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {r : ℕ}
    (c : E ≃ₐ[F] E) (G : Matrix (Fin r) (Fin r) E) (g : Matrix (Fin r) (Fin r) (RA F E))
    (hG : G.det ≠ 0) (hg : IsUA c G g) : IsTA c g.det := by
  set σ := sg (FiniteAdeleRing (𝓞 F) F) c with hσ
  set G' : Matrix (Fin r) (Fin r) (RA F E) := G.map (Algebra.TensorProduct.includeRight : E →ₐ[F] RA F E) with hG'
  have hM : gᵀ * G' * g.map σ = G' := by
    ext a b
    have h := hg.2 (Pi.single a 1) (Pi.single b 1)
    simp only [hermA, Matrix.mulVec_single_one] at h
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    convert h using 1
    · rfl
    · simp [G', Pi.single_apply, apply_ite σ]
  have hdet := congrArg Matrix.det hM
  have hs : (g.map σ).det = σ g.det := by
    rw [show g.map σ = (σ : RA F E →+* RA F E).mapMatrix g from rfl, ← RingHom.map_det]; rfl
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hs] at hdet
  have hG'det : G'.det = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ G.det := by
    rw [hG', show G.map (Algebra.TensorProduct.includeRight : E →ₐ[F] RA F E) =
      ((Algebra.TensorProduct.includeRight : E →ₐ[F] RA F E) : E →+* RA F E).mapMatrix G from rfl,
      ← RingHom.map_det]; rfl
  have hu : IsUnit G'.det := by
    rw [hG'det]
    refine IsUnit.of_mul_eq_one ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ G.det⁻¹) ?_
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_inv_cancel₀ hG]
    rfl
  unfold IsTA
  have : g.det * σ g.det * G'.det = 1 * G'.det := by
    rw [one_mul]; convert hdet using 1; ring
  exact hu.mul_right_cancel this

theorem unitary_det_isTA : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (g : Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)), G.det ≠ 0 → IsUA (IsCMField.complexConj E) G g → IsTA (IsCMField.complexConj E) g.det :=
  fun _ _ _ _ _ _ _ hG hg => isTA_det_of_isUA _ _ _ hG hg

end GlobalTheory
end
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

theorem _root_.GlobalTheory.T.comma_descent_injective : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), (∀ (T : C) (x : (F).obj T), (∀ t (u : T ⟶ G.obj t), mp (F) u x = 0) → x = 0) → (∀ (T : C) (s : ∀ t, (T ⟶ G.obj t) → (F).obj (G.obj t)), (∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), s t' (u ≫ G.map a) = mp (F) (G.map a) (s t u)) → ∃ x : (F).obj T, ∀ t u, mp (F) u x = s t u) → (∀ (T : C) (y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → (F).obj (G.obj t')), (∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), y t t'' u (a ≫ b) = mp (F) (G.map b) (y t t' u a) + y t' t'' (u ≫ G.map a) b) → ∃ g : ∀ t, (T ⟶ G.obj t) → (F).obj (G.obj t), ∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), g t' (u ≫ G.map a) - mp (F) (G.map a) (g t u) = y t t' u a) → Function.Injective (CoefMap.restrict F G).pull2 := by
  first | exact @GlobalTheory.CatCoh.pull2_restrict_injective_of_comma | exact GlobalTheory.CatCoh.pull2_restrict_injective_of_comma | (intros; apply GlobalTheory.CatCoh.pull2_restrict_injective_of_comma <;> assumption)
end
