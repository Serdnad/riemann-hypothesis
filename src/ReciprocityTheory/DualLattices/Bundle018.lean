module

public import ReciprocityTheory.DualLattices.Bundle012
public import Mathlib.GroupTheory.GroupAction.Ring
public import ReciprocityTheory.DualLattices.Bundle006
import Mathlib.Algebra.Module.StablyFree.Basic
public import ReciprocityTheory.DualLattices.Bundle013
public import ReciprocityTheory.DualLattices.Bundle014
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import ReciprocityTheory.DualLattices.ColengthSqBlockVandermonde
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Module.Projective
import ReciprocityTheory.DualLattices.Bundle002

@[expose] public section

section

noncomputable section

open TensorProduct

namespace ReciprocityTheory.PGsh

universe u

structure ATowerL (R₀ : Type u) [CommRing R₀] (p : ℕ) extends ATower R₀ p where
  r' : ∀ n, LHom (R' (n + 1)) (R' n)
  r : ∀ n, LHom (R (n + 1)) (R n)
  r_π : ∀ n (x : (R' (n + 1) : Type u)), (r n).1 ((π (n + 1)).1 x) = (π n).1 ((r' n).1 x)
  r_q : ∀ n (x : (O : Type u)), (r n).1 ((q (n + 1)).1 x) = (q n).1 x
  r'_ξ : ∀ n, (r' n).1 (ξ (n + 1)) = ξ n
  complete : ∀ x : ∀ n, (R n : Type u), (∀ n, (r n).1 (x (n + 1)) = x n) →
    ∃ a : (O : Type u), ∀ n, (q n).1 a = x n

variable {R₀ : Type u} [CommRing R₀]

structure DualTower {p : ℕ} (Tw : ATowerL R₀ p) where
  Dp : ∀ n, DualPair (Tw.R n)
  d : ∀ n, LHom (Dp (n + 1)).D (Dp n).D
  d_π : ∀ n (x : ((Dp (n + 1)).D : Type u)), (Dp n).π.1 ((d n).1 x) = (Tw.r n).1 ((Dp (n + 1)).π.1 x)
  d_σ : ∀ n (x : (Tw.R (n + 1) : Type u)), (d n).1 ((Dp (n + 1)).σ.1 x) = (Dp n).σ.1 ((Tw.r n).1 x)
  d_η : ∀ n, (d n).1 (Dp (n + 1)).η = (Dp n).η

def LimStatement (B : BX R₀) {p : ℕ} (Tw : ATowerL R₀ p) (Dt : DualTower Tw) : Prop :=
  ∀ (ι : Type) (τ : ι → ℕ → B.G Tw.O),
    (∀ i n, (p ^ (n + 1)) • τ i n = 0) → (∀ i n, τ i n = p • τ i (n + 1)) →
    ∃ (ht : ι → B.gg →ₗ[R₀] (Tw.O : Type u)) (bt : ι → B.gg ⊗[R₀] (Tw.O : Type u)),
      (∀ i n, B.IsHeight (Dt.Dp n) (p ^ (n + 1)) (B.map (Tw.q n) (τ i n))
        ((Tw.q n).1.toLinearMap ∘ₗ ht i)) ∧
      (∀ i n, ∃ (th : B.G (Tw.R' n)) (w : B.gg ⊗[R₀] (Tw.R' n : Type u)),
        B.map (Tw.π n) th = B.map (Tw.q n) (τ i n) ∧
        (p ^ (n + 1)) • th = B.tg (Tw.π n) (Tw.sqZero n)
          (TensorProduct.map LinearMap.id (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) w) ∧
        LinearMap.lTensor B.gg (Tw.π n).1.toLinearMap w =
          LinearMap.lTensor B.gg (Tw.q n).1.toLinearMap (bt i))

def HtLinStatement (B : BX R₀) {p : ℕ} (Tw : ATower R₀ p) (Dp : ∀ n, DualPair (Tw.R n)) : Prop :=
  ∀ (ι : Type) [Fintype ι] (τ : ι → ℕ → B.G Tw.O) (ht : ι → B.gg →ₗ[R₀] (Tw.O : Type u))
    (a : ι → ℕ → ℤ) (α : ι → (Tw.O : Type u)),
    (∀ i n, (p ^ (n + 1)) • τ i n = 0) →
    (∀ i n, B.IsHeight (Dp n) (p ^ (n + 1)) (B.map (Tw.q n) (τ i n))
      ((Tw.q n).1.toLinearMap ∘ₗ ht i)) →
    (∀ i n, (Tw.q n).1 (α i) = a i n) →
    ∀ n, B.IsHeight (Dp n) (p ^ (n + 1)) (B.map (Tw.q n) (∑ i, a i n • τ i n))
      ((Tw.q n).1.toLinearMap ∘ₗ ∑ i, α i • ht i)

end ReciprocityTheory.PGsh
end
end

section

noncomputable section

open TensorProduct

namespace ReciprocityTheory.PGsh

universe u

variable {R₀ : Type u} [CommRing R₀]

lemma BX.ev_map (B : BX R₀) {R S : LAlg R₀} (f : (R : Type u) →ₐ[R₀] (S : Type u))
    (h : B.gg →ₗ[R₀] (R : Type u)) (v : B.gg ⊗[R₀] (R : Type u)) :
    f (B.ev h v) = B.ev (f.toLinearMap ∘ₗ h) (LinearMap.lTensor B.gg f.toLinearMap v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp [BX.ev]
  | tmul g r => simp [BX.ev]
  | add a b ha hb =>
    simp only [BX.ev, map_add (f := _)] at ha hb ⊢
    rw [ha, hb]

private lemma one_add_pow_of_sq {S : Type*} [CommRing S] (a : S) (ha : a * a = 0) (k : ℕ) :
    (1 + a) ^ k = 1 + k * a := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih]
    push_cast
    linear_combination (k : S) * ha

theorem b4 (B : BX R₀) (hB1 : PairingPropertiesStatement B) (hB3 : TangentPairingStatement B) {p : ℕ}
    (Tw : ATower R₀ p) : NsetExpInjectiveSurjective B Tw := by
  intro Dp ι τ E ht bt h1 h2 h3 i j
  apply sub_eq_zero.mp
  apply Tw.sep
  intro n
  obtain ⟨k, hk, hpair⟩ := h1 i j n
  obtain ⟨thi, wi, hmi, hNi, hwi⟩ := h3 i n
  obtain ⟨thj, wj, hmj, hNj, hwj⟩ := h3 j n
  have hsurjL : Function.Surjective (Tw.π n).1.toLinearMap := Tw.surj n
  obtain ⟨hsi, hsi_spec⟩ := Module.projective_lifting_property (Tw.π n).1.toLinearMap
    ((Tw.q n).1.toLinearMap ∘ₗ ht i) hsurjL
  obtain ⟨hsj, hsj_spec⟩ := Module.projective_lifting_property (Tw.π n).1.toLinearMap
    ((Tw.q n).1.toLinearMap ∘ₗ ht j) hsurjL
  obtain ⟨-, -, -, -, -, -, hnat, -⟩ := hB1
  have hpq := hnat _ _ (Tw.q n) _ _ _ _ hpair
  rw [← hmi, ← hmj] at hpq
  have hB3' := hB3 (Tw.R' n) (Tw.R n) (Tw.π n) (Tw.ξ n) (Dp n) (p ^ (n + 1)) (Tw.surj n)
    (Tw.ker_eq n) (Tw.ξ_sq n) (Tw.ann n) (Tw.char n) thi thj
    (TensorProduct.map LinearMap.id (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) wi)
    (TensorProduct.map LinearMap.id (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) wj)
    hsi hsj (Tw.zh n ^ k) _ hNi hNj
    (by rw [hmi, hsi_spec]; exact h2 i n) (by rw [hmj, hsj_spec]; exact h2 j n) hpq
    (Units.ext (by simp [Tw.ζ_spec]))
  have hev : ∀ (h : B.gg →ₗ[R₀] (Tw.R' n : Type u)) (w : B.gg ⊗[R₀] (Tw.R' n : Type u)),
      B.evK (Tw.π n) h (TensorProduct.map LinearMap.id (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) w) =
        Tw.ξ n * B.ev h w := by
    intro h w
    induction w using TensorProduct.induction_on with
    | zero => simp [BX.evK, BX.ev]
    | tmul g r =>
      simp [BX.evK, BX.ev, ξmul]
      ring
    | add a b ha hb =>
      simp only [BX.evK, BX.ev, map_add (f := _)] at ha hb ⊢
      rw [ha, hb, mul_add]
  rw [hev, hev] at hB3'
  have hpow : ((Tw.zh n ^ k : (Tw.R' n : Type u)ˣ) : (Tw.R' n : Type u)) ^ (p ^ (n + 1)) =
      1 + (k : (Tw.R' n : Type u)) * (Tw.cp n * Tw.ξ n) := by
    rw [Units.val_pow_eq_pow_val, pow_right_comm, Tw.zh_pow n]
    apply one_add_pow_of_sq
    calc Tw.cp n * Tw.ξ n * (Tw.cp n * Tw.ξ n) = Tw.cp n * Tw.cp n * (Tw.ξ n * Tw.ξ n) := by ring
      _ = 0 := by rw [Tw.ξ_sq n, mul_zero]
  have hξ : ((k : (Tw.R' n : Type u)) * Tw.cp n - (B.ev hsj wi - B.ev hsi wj)) * Tw.ξ n = 0 := by
    have hh := hB3'.symm.trans hpow
    linear_combination -hh
  have hmem := Tw.ann n _ hξ
  rw [← Tw.ker_eq n, RingHom.mem_ker] at hmem
  have e1 : (Tw.π n).1 (B.ev hsj wi) = (Tw.q n).1 (B.ev (ht j) (bt i)) := by
    rw [BX.ev_map B (Tw.π n).1 hsj wi, hsj_spec, hwi, ← BX.ev_map B (Tw.q n).1 (ht j) (bt i)]
  have e2 : (Tw.π n).1 (B.ev hsi wj) = (Tw.q n).1 (B.ev (ht i) (bt j)) := by
    rw [BX.ev_map B (Tw.π n).1 hsi wj, hsi_spec, hwj, ← BX.ev_map B (Tw.q n).1 (ht i) (bt j)]
  simp only [map_sub, map_mul, map_natCast, Tw.cp_spec, e1, e2] at hmem
  rw [map_sub, map_sub, map_mul, hk]
  linear_combination hmem

end ReciprocityTheory.PGsh
end
end

section

noncomputable section

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

section Transport

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
variable {X Y : Type} [AddCommGroup X] [Fintype X] [DecidableEq X]
  [AddCommGroup Y] [Fintype Y] [DecidableEq Y]

abbrev pbE (e : X ≃+ Y) : (Y → C) ≃ₗ[R] (X → C) := LinearEquiv.funCongrLeft R C e.toEquiv

lemma pbE_apply (e : X ≃+ Y) (f : Y → C) (x : X) : pbE (C := C) (R := R) e f x = f (e x) := rfl

lemma pbE_symm_apply (e : X ≃+ Y) (f : X → C) (y : Y) :
    (pbE (C := C) (R := R) e).symm f y = f (e.symm y) := by
  rfl

lemma det_sub (e : X ≃+ Y) (B : Matrix Y Y C) : (B.submatrix e e).det = B.det :=
  Matrix.det_submatrix_equiv_self e.toEquiv B

lemma map_cols (e : X ≃+ Y) (B : Matrix Y Y C) :
    (Submodule.span R (Set.range fun j y => B y j)).map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C)) =
      Submodule.span R (Set.range fun j x => (B.submatrix e e) x j) := by
  rw [Submodule.map_span, ← Set.range_comp]
  have h : (fun j x => (B.submatrix e e) x j) =
      ((pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C)) ∘ fun j y => B y j) ∘ e := by
    funext j x
    rfl
  rw [h, e.surjective.range_comp]

lemma hasColen_map (v : Valuation C NNReal) (e : X ≃+ Y) (M : Submodule R (Y → C)) (c : NNReal)
    (h : HasColen R v M c) : HasColen R v (M.map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C))) c := by
  obtain ⟨B, hM, hc⟩ := h
  exact ⟨B.submatrix e e, by rw [hM, map_cols], by rw [det_sub, hc]⟩

lemma map_pbE_symm (e : X ≃+ Y) (M : Submodule R (Y → C)) :
    (M.map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C))).map (pbE (C := C) (R := R) e.symm : (X → C) →ₗ[R] (Y → C)) = M := by
  rw [← Submodule.map_comp]
  have h : ((pbE (C := C) (R := R) e.symm : (X → C) →ₗ[R] (Y → C)).comp
      (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C))) = LinearMap.id := by
    refine LinearMap.ext fun f => funext fun y => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, pbE_apply, LinearMap.id_apply,
      AddEquiv.apply_symm_apply]
  rw [h, Submodule.map_id]

def hopfPull (e : X ≃+ Y) (A : HopfOrder (C := C) R Y) : HopfOrder (C := C) R X where
  carrier := A.carrier.map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C))
  lat := by
    obtain ⟨B, hB, hA⟩ := A.lat
    exact ⟨B.submatrix e e, by rwa [det_sub], by rw [hA, map_cols]⟩
  le_int := by
    intro f hf
    rw [Submodule.mem_map_equiv] at hf
    have h := A.le_int hf
    intro x
    obtain ⟨r, hr⟩ := h (e x)
    exact ⟨r, by rw [hr, pbE_symm_apply, AddEquiv.symm_apply_apply]⟩
  one_mem := by
    rw [Submodule.mem_map_equiv]
    convert A.one_mem using 1
    funext y
    simp [pbE_symm_apply]
  mul_mem := fun f g hf hg => by
    rw [Submodule.mem_map_equiv] at hf hg ⊢
    convert A.mul_mem _ _ hf hg using 1
    funext y
    simp only [pbE_symm_apply, Pi.mul_apply]
  comul := by
    intro f hf
    rw [Submodule.mem_map_equiv] at hf
    set g := (pbE (C := C) (R := R) e).symm f with hg
    have hfg : f = pbE (C := C) (R := R) e g := by rw [hg, LinearEquiv.apply_symm_apply]
    let pb2 : (Y × Y → C) →ₗ[R] (X × X → C) :=
      LinearMap.funLeft R C (fun q : X × X => (e q.1, e q.2))
    have h1 : addPull R X f = pb2 (addPull R Y g) := by
      funext q
      rw [hfg]
      simp only [addPull, pb2, LinearMap.funLeft_apply, pbE_apply, map_add (f := _)]
    rw [h1]
    have h2 := A.comul g hf
    have h3 : (tensorSpan R A.carrier).map pb2 ≤ tensorSpan R (A.carrier.map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C))) := by
      rw [tensorSpan, Submodule.map_span_le]
      rintro F ⟨g1, hg1, h1', hh1, rfl⟩
      exact Submodule.subset_span ⟨pbE (C := C) (R := R) e g1, Submodule.mem_map_of_mem hg1,
        pbE (C := C) (R := R) e h1', Submodule.mem_map_of_mem hh1, rfl⟩
    exact h3 (Submodule.mem_map_of_mem h2)
  antipode := fun f hf => by
    rw [Submodule.mem_map_equiv] at hf ⊢
    convert A.antipode _ hf using 1
    funext y
    simp only [pbE_symm_apply, map_neg]

private theorem pbE_symm_pow (e : X ≃+ Y) (f : X → C) (n : ℕ) :
    (pbE (C := C) (R := R) e).symm (f ^ n) = ((pbE (C := C) (R := R) e).symm f) ^ n := by
  funext y
  simp only [pbE_symm_apply, Pi.pow_apply]

lemma mem_augIdeal_pull (e : X ≃+ Y) (A : HopfOrder (C := C) R Y) (f : X → C) :
    f ∈ augIdeal (hopfPull e A).carrier ↔ (pbE (C := C) (R := R) e).symm f ∈ augIdeal A.carrier := by
  rw [show (hopfPull e A).carrier =
      A.carrier.map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C)) from rfl]
  simp only [ReciprocityTheory.PGsh.L2.augIdeal, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.proj_apply,
    Submodule.mem_map_equiv, pbE_symm_apply, map_zero]

end Transport

lemma pow_mem_aug {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {X : Type}
    [AddCommGroup X] [Fintype X] [DecidableEq X] (A : HopfOrder (C := C) R X) {x : X → C}
    (hx : x ∈ augIdeal A.carrier) : ∀ k : ℕ, x ^ (k + 1) ∈ augIdeal A.carrier := by
  intro k
  simp only [ReciprocityTheory.PGsh.L2.augIdeal, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.proj_apply] at hx ⊢
  refine ⟨?_, by rw [Pi.pow_apply, hx.2, zero_pow (Nat.succ_ne_zero k)]⟩
  induction k with
  | zero => rw [zero_add, pow_one]; exact hx.1
  | succ k ih => rw [pow_succ]; exact A.mul_mem _ _ ih hx.1

theorem primeHopfOrder_of_addEquiv (hU3 : PrimeHopfOrderStatement) (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C]
    [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C]
    (hv : v.Integers R) (hp : v (p : C) < 1) {K : Type} [AddCommGroup K] [Fintype K]
    [DecidableEq K] (e : ZMod p ≃+ K) (AK : HopfOrder (C := C) R K) :
    ∃ (xK : K → C) (δ : R) (x1 : C), xK ∈ augIdeal AK.carrier ∧
      xK ^ p = (fun a => algebraMap R C δ * xK a) ∧ v (algebraMap R C δ) = v x1 ^ (p - 1) ∧
      (∀ f ∈ augIdeal AK.carrier, ∃ r : R,
        f - r • xK ∈ augIdeal AK.carrier * augIdeal AK.carrier) ∧
      HasColen R v AK.carrier (v x1 ^ (p * (p - 1) / 2)) := by
  obtain ⟨x, _, δ, hx, hx0, -, -, -, hxp, hδ, -, haug, -, hcol⟩ :=
    hU3 p C v R hv hp (hopfPull e AK)
  have hxa : x ∈ ReciprocityTheory.PGsh.L2.augIdeal (hopfPull e AK).carrier := by
    simp only [ReciprocityTheory.PGsh.L2.augIdeal, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.proj_apply]
    exact ⟨hx, hx0⟩
  have hxK := (mem_augIdeal_pull e AK x).1 hxa
  refine ⟨(pbE (C := C) (R := R) e).symm x, δ, x 1, hxK, ?_, hδ, ?_, ?_⟩
  · funext k
    have h := congrFun hxp (e.symm k)
    simp only [Pi.pow_apply] at h ⊢
    rw [pbE_symm_apply]
    exact h
  · have key : ∀ F ∈ Submodule.span R {y | ∃ j : ℕ, 1 ≤ j ∧ j < p ∧ y = x ^ j},
        ∃ r : R, (pbE (C := C) (R := R) e).symm F - r • (pbE (C := C) (R := R) e).symm x ∈
          ReciprocityTheory.PGsh.L2.augIdeal AK.carrier * ReciprocityTheory.PGsh.L2.augIdeal AK.carrier := by
      intro F hF
      induction hF using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨j, hj1, -, rfl⟩ := hy
        rcases Nat.lt_or_ge j 2 with hj | hj
        · obtain rfl : j = 1 := by omega
          refine ⟨1, ?_⟩
          rw [pow_one, one_smul, sub_self]
          exact zero_mem _
        · obtain ⟨m, rfl⟩ : ∃ m, j = m + 2 := ⟨j - 2, by omega⟩
          refine ⟨0, ?_⟩
          rw [zero_smul, sub_zero, pbE_symm_pow, show m + 2 = (m + 1) + 1 from rfl, pow_succ]
          exact Submodule.mul_mem_mul (pow_mem_aug AK hxK m) hxK
      | zero =>
        refine ⟨0, ?_⟩
        rw [map_zero, zero_smul, sub_zero]
        exact zero_mem _
      | add a b _ _ ha hb =>
        obtain ⟨r1, h1⟩ := ha
        obtain ⟨r2, h2⟩ := hb
        refine ⟨r1 + r2, ?_⟩
        convert add_mem h1 h2 using 1
        rw [map_add (f := _), add_smul]
        abel
      | smul c a _ ha =>
        obtain ⟨r1, h1⟩ := ha
        refine ⟨c * r1, ?_⟩
        convert Submodule.smul_mem _ c h1 using 1
        rw [map_smul, smul_sub, mul_smul]
    intro f hf
    have hF : pbE (C := C) (R := R) e f ∈
        ReciprocityTheory.PGsh.L2.augIdeal (hopfPull e AK).carrier := by
      rw [mem_augIdeal_pull, LinearEquiv.symm_apply_apply]
      exact hf
    rw [haug] at hF
    obtain ⟨r, hr⟩ := key _ hF
    rw [LinearEquiv.symm_apply_apply] at hr
    exact ⟨r, hr⟩
  · have hc := hasColen_map v e.symm _ _ hcol
    rwa [show (hopfPull e AK).carrier =
        AK.carrier.map (pbE (C := C) (R := R) e : (K → C) →ₗ[R] (ZMod p → C)) from rfl,
      map_pbE_symm] at hc

end ReciprocityTheory.PGsh.Up
end
end

section

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

def qE {R : Type} [CommRing R] {g m : ℕ} (εL : Fin m → Matrix (Fin g) (Fin g) R) (i j : Fin m) :
    Submodule R (Fin g ⊕ Fin g → R) :=
  (LinearMap.range (Matrix.mulVecLin (εL j)ᵀ)).comap (LinearMap.funLeft R R Sum.inl) ⊓
    (LinearMap.range (Matrix.mulVecLin (εL i))).comap (LinearMap.funLeft R R Sum.inr)

abbrev xModE {R : Type} [CommRing R] {g m : ℕ} (Ht Bt : Matrix (Fin g) (Ix g) R)
    (εT : Fin m → Matrix (Ix g) (Ix g) R) (εL : Fin m → Matrix (Fin g) (Fin g) R)
    (π : Equiv.Perm (Fin m)) (i : Fin m) :=
  qE εL i (π i) ⧸
    ((LinearMap.range (Matrix.mulVecLin (εT i))).map (Matrix.mulVecLin (fromRows Ht Bt))).comap
      (qE εL i (π i)).subtype

def LenIdStatement : Prop :=
  ∀ (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C],
    v.Integers R → ∀ (g m : ℕ) (Ht Bt : Matrix (Fin g) (Ix g) R) (E : Matrix (Ix g) (Ix g) R)
    (cp : R), cp ≠ 0 → IsUnit E.det → Btᵀ * Ht - Htᵀ * Bt = cp • E →
    ∀ (εT : Fin m → Matrix (Ix g) (Ix g) R) (εL : Fin m → Matrix (Fin g) (Fin g) R)
    (π : Equiv.Perm (Fin m)), (∀ i, π (π i) = i) →
    (∀ i j, εT i * εT j = if i = j then εT i else 0) → ∑ i, εT i = 1 →
    (∀ i j, εL i * εL j = if i = j then εL i else 0) → ∑ i, εL i = 1 →
    (∀ i, Ht * εT i = (εL (π i))ᵀ * Ht) → (∀ i, Bt * εT i = εL i * Bt) →
    (∀ i, (εT i)ᵀ * E = E * εT (π i)) →
    ∀ (i : Fin m) (d : ℕ), Nonempty (LinearMap.range (Matrix.mulVecLin (εL i)) ≃ₗ[R] (Fin d → R)) →
    ∀ c₁ c₂ : NNReal, HasLen v R (cokE Ht εT εL i (π i)) c₁ →
      HasLen v R (cokE Ht εT εL (π i) i) c₂ →
      ∃ X : NNReal, HasLen v R (xModE Ht Bt εT εL π i) X ∧ X * c₁ = v (algebraMap R C cp) ^ d * c₂

end ReciprocityTheory.PGsh.Up
end
end

section

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

variable {C : Type} [Field C] {v : Valuation C NNReal}

def phiMap {n s h : ℕ} (A : Fin n → Matrix (Fin s) (Fin h) C) (w : Fin n × Fin h → C) :
    Fin n × Fin s → C := fun y => ∑ l, A y.1 y.2 l * w (y.1, l)

lemma sumLat_inv_mulVec {n s : ℕ} (Mτ : Fin n → Lat v (Fin s)) (w : Fin n × Fin s → C)
    (τ : Fin n) (i : Fin s) :
    ((sumLat Mτ).B⁻¹ *ᵥ w) (τ, i) = ((Mτ τ).B⁻¹ *ᵥ fun j => w (τ, j)) i := by
  classical
  unfold sumLat
  simp only
  have hinv : (reindex (Equiv.prodComm (Fin s) (Fin n)) (Equiv.prodComm (Fin s) (Fin n))
      (blockDiagonal fun τ ↦ (Mτ τ).B))⁻¹ =
      reindex (Equiv.prodComm (Fin s) (Fin n)) (Equiv.prodComm (Fin s) (Fin n))
        (blockDiagonal fun τ ↦ (Mτ τ).B⁻¹) := by
    refine Matrix.inv_eq_left_inv ?_
    simp only [Matrix.reindex_apply]
    rw [Matrix.submatrix_mul_equiv, ← Matrix.blockDiagonal_mul]
    have h1 : (fun τ ↦ (Mτ τ).B⁻¹ * (Mτ τ).B) = 1 :=
      funext fun τ ↦ Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (Mτ τ).det_ne)
    rw [h1, Matrix.blockDiagonal_one, Matrix.submatrix_one_equiv]
  rw [hinv]
  simp only [Matrix.mulVec, dotProduct, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.prodComm_symm, Equiv.prodComm_apply, Prod.swap_prod_mk, Matrix.blockDiagonal_apply,
    Fintype.sum_prod_type, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]

lemma v_mulVec_le {m k : Type} [Fintype k] (P : Matrix m k C) (x : k → C)
    (hP : ∀ i j, v (P i j) ≤ 1) (hx : ∀ j, v (x j) ≤ 1) (i : m) : v ((P *ᵥ x) i) ≤ 1 := by
  simp only [Matrix.mulVec, dotProduct]
  refine v.map_sum_le fun j _ ↦ ?_
  rw [map_mul]
  exact mul_le_one₀ (hP i j) (zero_le) (hx j)

theorem polyVec_mem {n h : ℕ} {a : Fin n → C} (F : Lat v (Fin n × Fin h))
    (hF : F.B = freeMat a h) (p : Polynomial C) (hp : ∀ k, v (p.coeff k) ≤ 1)
    (hdeg : p.natDegree < n) (u : Fin h → C) (hu : ∀ l, v (u l) ≤ 1) :
    (fun y : Fin n × Fin h => p.eval (a y.1) * u y.2) ∈ F.pts := by
  classical
  refine ⟨fun y ↦ p.coeff (y.1 : ℕ) * u y.2, ?_, ?_⟩
  · intro j
    rw [map_mul]
    exact mul_le_one₀ (hp _) (zero_le) (hu _)
  · funext y
    rw [hF]
    simp only [Matrix.mulVec, dotProduct, freeMat, Matrix.of_apply, Fintype.sum_prod_type,
      ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [Polynomial.eval_eq_sum_range' hdeg, Finset.sum_mul, ← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun k _ ↦ by ring

end ReciprocityTheory.PGsh.Up
end
end
