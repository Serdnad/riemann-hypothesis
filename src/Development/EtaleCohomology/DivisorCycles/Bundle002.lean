module

public import Development.EtaleCohomology.DivisorCycles.OpenCoset
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle015
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Univ
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Matrix

namespace LateralTheory.DivDb.TangentFieldExtension
open LateralTheory.DivDb

variable {C : Type} [Field C] {N : ℕ}

theorem ev_DX (Y x : Mat C N) (f : MP C N) : ev x (DX Y f) = dAt f x (Y * x) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [dAt, ev, DX, MvPolynomial.derivation_C]
  | add f g hf hg =>
    rw [map_add (f := _), ev, map_add (f := _), ← ev, ← ev, hf, hg]
    simp only [dAt, map_add (f := _), ev, add_mul, Finset.sum_add_distrib]
  | mul_X f q hf =>
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    simp only [ev, map_add (f := _), map_mul] at hf ⊢
    rw [hf]

    simp only [DX, MvPolynomial.mkDerivation_X, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
    dAt, ev, Derivation.leibniz, smul_eq_mul, map_add, map_mul, MvPolynomial.pderiv_X, add_mul,
    Finset.sum_add_distrib, Matrix.mul_apply]
    congr 1
    · simp [Pi.single_apply, apply_ite (MvPolynomial.eval _)]
    · rw [Finset.mul_sum]; simp only [mul_assoc]

theorem TanField_of (hChain : Chain) : TanField := by
  intro C _ N S Y
  constructor
  · intro hY f hf s hs
    obtain ⟨f', hev, hd⟩ := hChain C N N (LinearMap.mulRight C s) f
    have hf' : f' ∈ Van (S : Set (Mat C N)) := fun x hx => by
      rw [hev, LinearMap.mulRight_apply]; exact hf _ (S.mul_mem hx hs)
    have h1 : dAt f' 1 Y = 0 := hY f' hf'
    rw [hd] at h1
    simp only [LinearMap.mulRight_apply, one_mul] at h1
    show ev s (DX Y f) = 0
    rw [ev_DX]; exact h1
  · intro h f hf
    have h1 : ev 1 (DX Y f) = 0 := h f hf 1 S.one_mem
    rw [ev_DX, mul_one] at h1
    exact h1

end LateralTheory.DivDb.TangentFieldExtension
end

section

open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb.SpecLiePf
open LateralTheory.DivDb

theorem SpecLie_of (hS : SpecPt) : SpecLie := by
  intro Γ K K' _ _ _ _ _ N n ρ X e hX hL hR
  classical
  let x : (Fin N × Fin N) ⊕ Fin n → K' := Sum.elim (fun p => X p.1 p.2) e
  let gAB : Finset (Fin n) → Finset (Fin n) → MvPolynomial ((Fin N × Fin N) ⊕ Fin n) K := fun A B =>
    MvPolynomial.C (B.card : K) * ∑ i ∈ A, MvPolynomial.X (Sum.inr i) -
      MvPolynomial.C (A.card : K) * ∑ i ∈ B, MvPolynomial.X (Sum.inr i)
  let G : Set (MvPolynomial ((Fin N × Fin N) ⊕ Fin n) K) :=
    {g | ∃ A B : Finset (Fin n), A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧ g = gAB A B}
  have hGf : G.Finite :=
    (Set.finite_range (fun AB : Finset (Fin n) × Finset (Fin n) => gAB AB.1 AB.2)).subset
      (by rintro g ⟨A, B, -, -, -, rfl⟩; exact ⟨(A, B), rfl⟩)
  have haG : ∀ g ∈ G, MvPolynomial.aeval x g ≠ 0 := by
    rintro g ⟨A, B, hA, hB, hAB, rfl⟩

    simp only [gAB, map_sub, map_mul, map_sum, MvPolynomial.aeval_X, x, Sum.elim_inr, map_natCast]
    exact sub_ne_zero.mpr (hL A B hA hB hAB)
  obtain ⟨y, hy, hyG⟩ := hS K K' _ x G hGf haG
  refine ⟨Matrix.of fun a b => y (Sum.inl (a, b)), fun i => y (Sum.inr i), ?_, ?_, ?_⟩
  · change ∀ f ∈ Van (img ρ ⊤ : Set (Mat K N)), dAt f 1 _ = 0
    intro f hf
    have hf' : ∀ g : Γ, MvPolynomial.eval (fun p : Fin N × Fin N => (ρ g : Matrix (Fin N) (Fin N) K) p.1 p.2) f = 0 :=
      fun g => hf _ ⟨g, trivial, rfl⟩
    have h0 := hX f hf'
    let L : MvPolynomial ((Fin N × Fin N) ⊕ Fin n) K := ∑ p : Fin N × Fin N,
      MvPolynomial.C (MvPolynomial.eval (fun q : Fin N × Fin N => (1 : Matrix (Fin N) (Fin N) K) q.1 q.2)
        (MvPolynomial.pderiv p f)) * MvPolynomial.X (Sum.inl p)
    have hxL : MvPolynomial.aeval x L = 0 := by

      simpa only [L, map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X, x, Sum.elim_inl] using h0
    have h1 := hy L hxL

    simpa only [L, dAt, ev, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, Matrix.of_apply] using h1
  · intro A B hA hB hAB
    have h1 := hyG _ ⟨A, B, hA, hB, hAB, rfl⟩

    simp only [gAB, map_sub, map_mul, map_sum, MvPolynomial.eval_C, MvPolynomial.eval_X] at h1
    exact sub_ne_zero.mp h1
  · intro i
    let M : Matrix (Fin N) (Fin N) (MvPolynomial ((Fin N × Fin N) ⊕ Fin n) K) :=
      Matrix.scalar (Fin N) (MvPolynomial.X (Sum.inr i)) - Matrix.of (fun a b => MvPolynomial.X (Sum.inl (a, b)))
    have hx : MvPolynomial.aeval x M.det = 0 := by
      have e1 : MvPolynomial.aeval x M.det = ((MvPolynomial.aeval x).toRingHom.mapMatrix M).det := by
        rw [← RingHom.map_det]; rfl
      have e2 : (MvPolynomial.aeval x).toRingHom.mapMatrix M = Matrix.scalar (Fin N) (e i) - X := by
        ext a b
        by_cases h : a = b
        · subst h; simp [M, x]
        · simp [M, x, h]
      rw [e1, e2, ← Matrix.eval_charpoly]; exact hR i
    have h1 := hy _ hx
    have e1 : MvPolynomial.eval y M.det = ((MvPolynomial.eval y).mapMatrix M).det := by
      rw [← RingHom.map_det]
    have e2 : (MvPolynomial.eval y).mapMatrix M =
        Matrix.scalar (Fin N) (y (Sum.inr i)) - Matrix.of (fun a b => y (Sum.inl (a, b))) := by
      ext a b
      by_cases h : a = b
      · subst h; simp [M]
      · simp [M, h]
    rw [e1, e2] at h1
    change Polynomial.eval (y (Sum.inr i)) (Matrix.charpoly (Matrix.of fun a b => y (Sum.inl (a, b)))) = 0
    rw [Matrix.eval_charpoly]; exact h1

end LateralTheory.DivDb.SpecLiePf
end

section

open Matrix

namespace LateralTheory.DivDb.EnvStab₂
open LateralTheory.DivDb

variable {Γ C : Type} [Group Γ] [Field C] {N : ℕ}

theorem ev_X (x : Mat C N) (q : Fin N × Fin N) : ev x (MvPolynomial.X q) = x q.1 q.2 := by
  simp [ev]

theorem mem_img (ρ : Γ →* GL (Fin N) C) (h : Γ) : ((ρ h : GL (Fin N) C) : Mat C N) ∈ (img ρ ⊤ : Set (Mat C N)) := by
  simp only [img, SetLike.mem_coe, Submonoid.mem_map]
  exact ⟨h, by simp, rfl⟩

theorem img_cases (ρ : Γ →* GL (Fin N) C) {x : Mat C N} (hx : x ∈ (img ρ ⊤ : Set (Mat C N))) :
    ∃ h : Γ, ((ρ h : GL (Fin N) C) : Mat C N) = x := by
  simp only [img, SetLike.mem_coe, Submonoid.mem_map] at hx
  obtain ⟨h, _, rfl⟩ := hx
  exact ⟨h, rfl⟩

theorem coe_mul_inv (ρ : Γ →* GL (Fin N) C) (g : Γ) :
    ((ρ g : GL (Fin N) C) : Mat C N) * ((ρ g⁻¹ : GL (Fin N) C) : Mat C N) = 1 := by
  rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]

theorem coe_inv_mul (ρ : Γ →* GL (Fin N) C) (g : Γ) :
    ((ρ g⁻¹ : GL (Fin N) C) : Mat C N) * ((ρ g : GL (Fin N) C) : Mat C N) = 1 := by
  rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]

def conjL (G G' : Mat C N) : Mat C N →ₗ[C] Mat C N where
  toFun x := G * x * G'
  map_add' x y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c x := by simp

theorem lie_conj (hC : Chain) (ρ : Γ →* GL (Fin N) C) (g : Γ) (Y : Mat C N) (hY : Y ∈ lie ρ) :
    ((ρ g : GL (Fin N) C) : Mat C N) * Y * ((ρ g⁻¹ : GL (Fin N) C) : Mat C N) ∈ lie ρ := by
  intro f hf
  obtain ⟨f', hev, hd⟩ := hC C N N (conjL (ρ g : Mat C N) (ρ g⁻¹ : Mat C N)) f
  have hf' : f' ∈ Van (img ρ ⊤ : Set (Mat C N)) := by
    intro x hx
    obtain ⟨h, rfl⟩ := img_cases ρ hx
    rw [hev]
    apply hf
    have : conjL (C := C) (N := N) (ρ g : Mat C N) (ρ g⁻¹ : Mat C N) (ρ h : Mat C N)
        = ((ρ (g * h * g⁻¹) : GL (Fin N) C) : Mat C N) := by
      simp [conjL, map_mul, Units.val_mul]
    rw [this]; exact mem_img ρ _
  have h1 : conjL (C := C) (N := N) (ρ g : Mat C N) (ρ g⁻¹ : Mat C N) 1 = 1 := by
    simp only [conjL, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mul_one]; exact coe_mul_inv ρ g
  have := hd 1 Y
  rw [h1] at this
  show dAt f 1 (conjL (C := C) (N := N) (ρ g : Mat C N) (ρ g⁻¹ : Mat C N) Y) = 0
  rw [← this]
  exact hY f' hf'

theorem normd (hC : Chain) (ρ : Γ →* GL (Fin N) C) : Normd ρ (env ρ) := by
  intro g a ha
  induction ha using Algebra.adjoin_induction with
  | mem x hx => exact Algebra.subset_adjoin (lie_conj hC ρ g x hx)
  | algebraMap r =>
    rw [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, coe_mul_inv]
    exact Subalgebra.smul_mem _ (Subalgebra.one_mem _) r
  | add x y _ _ hx hy =>
    rw [Matrix.mul_add, Matrix.add_mul]; exact Subalgebra.add_mem _ hx hy
  | mul x y _ _ hx hy =>
    have : ((ρ g : GL (Fin N) C) : Mat C N) * (x * y) * ((ρ g⁻¹ : GL (Fin N) C) : Mat C N)
        = (((ρ g : GL (Fin N) C) : Mat C N) * x * ((ρ g⁻¹ : GL (Fin N) C) : Mat C N)) *
          (((ρ g : GL (Fin N) C) : Mat C N) * y * ((ρ g⁻¹ : GL (Fin N) C) : Mat C N)) := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc ((ρ g⁻¹ : GL (Fin N) C) : Mat C N), coe_inv_mul, Matrix.one_mul]
    rw [this]; exact Subalgebra.mul_mem _ hx hy

def lamL (ℓ : Module.Dual C (Fin N → C)) (v : Fin N → C) : Mat C N →ₗ[C] Mat C 1 where
  toFun x := Matrix.of fun _ _ => ℓ (x *ᵥ v)
  map_add' x y := by ext; simp [Matrix.add_mulVec]
  map_smul' c x := by ext; simp [Matrix.smul_mulVec]

theorem lie_keeps (hC : Chain) (ρ : Γ →* GL (Fin N) C) (W : Submodule C (Fin N → C))
    (hW : ∀ g, ∀ v ∈ W, ((ρ g : GL (Fin N) C) : Mat C N) *ᵥ v ∈ W) (Y : Mat C N) (hY : Y ∈ lie ρ)
    (v : Fin N → C) (hv : v ∈ W) : Y *ᵥ v ∈ W := by
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro ℓ hℓ
  rw [Submodule.mem_dualAnnihilator] at hℓ
  obtain ⟨f', hev, hd⟩ := hC C N 1 (lamL ℓ v) (MvPolynomial.X (0, 0))
  have hf' : f' ∈ Van (img ρ ⊤ : Set (Mat C N)) := by
    intro x hx
    obtain ⟨h, rfl⟩ := img_cases ρ hx
    rw [hev, ev_X]
    simp only [lamL, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply]
    exact hℓ _ (hW h v hv)
  have h0 := hY f' hf'
  rw [hd] at h0
  simpa [dAt, lamL, ev, MvPolynomial.pderiv_X, Fintype.sum_unique, Pi.single_apply, Prod.ext_iff, Fin.fin_one_eq_zero] using h0

theorem keeps (hC : Chain) (ρ : Γ →* GL (Fin N) C) : Keeps ρ (env ρ) := by
  intro W hW a ha
  induction ha using Algebra.adjoin_induction with
  | mem x hx => exact fun v hv => lie_keeps hC ρ W hW x hx v hv
  | algebraMap r =>
    intro v hv
    rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]
    exact W.smul_mem r hv
  | add x y _ _ hx hy =>
    intro v hv; rw [Matrix.add_mulVec]; exact W.add_mem (hx v hv) (hy v hv)
  | mul x y _ _ hx hy =>
    intro v hv; rw [← Matrix.mulVec_mulVec]; exact hx _ (hy v hv)

end LateralTheory.DivDb.EnvStab₂

namespace LateralTheory.DivDb

theorem EnvStab_of (hC : Chain) : EnvStab := fun _ _ _ _ _ ρ =>
  ⟨EnvStab₂.normd hC ρ, EnvStab₂.keeps hC ρ⟩

end LateralTheory.DivDb
end

section

open Matrix
namespace LateralTheory.DivDb.UnipotentPartTrivial
open LateralTheory.DivDb

theorem pow_vanish {C : Type} [Field C] {N : ℕ} (E : Mat C N) (h : E * E = 0) (k : ℕ) (hk : 2 ≤ k) :
    E ^ k = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [pow_add, sq, h, zero_mul]

theorem series_eq {C : Type} [Field C] {N : ℕ} (E : Mat C N) (h : E * E = 0) (p : Fin N × Fin N) :
    PowerSeries.mk (fun k => ((k.factorial : C)⁻¹ • E ^ k) p.1 p.2)
      = ((Polynomial.C ((1 : Mat C N) p.1 p.2) + Polynomial.X * Polynomial.C (E p.1 p.2) : Polynomial C) :
          PowerSeries C) := by
  ext k
  rw [PowerSeries.coeff_mk, Polynomial.coeff_coe]
  rcases k with _ | _ | k
  · simp
  · simp
  · rw [pow_vanish E h _ (by omega)]
    simp

theorem Unip_of (h : ExpVan) : Unip := by
  intro C _ _ N S E hE hEE f hf
  have h0 := h C N S E hE f hf
  let g : Fin N × Fin N → Polynomial C := fun p =>
    Polynomial.C ((1 : Mat C N) p.1 p.2) + Polynomial.X * Polynomial.C (E p.1 p.2)
  have h1 : MvPolynomial.aeval g f = 0 := by
    apply Polynomial.coe_injective
    rw [Polynomial.coe_zero]
    have hc := congrArg (fun φ => φ f)
      (MvPolynomial.comp_aeval (R := C) g (Polynomial.coeToPowerSeries.algHom C))
    simp only [AlgHom.comp_apply] at hc
    simp only [Polynomial.coeToPowerSeries.algHom_apply, PowerSeries.map_id, Algebra.algebraMap_self] at hc
    simp only [id] at hc
    have hs : (fun p : Fin N × Fin N => PowerSeries.mk (fun k => ((k.factorial : C)⁻¹ • E ^ k) p.1 p.2))
        = fun i => ((g i : Polynomial C) : PowerSeries C) := funext (series_eq E hEE)
    rw [hs] at h0
    exact hc.trans h0
  have h2 := congrArg (fun q => Polynomial.aeval (1 : C) q) h1
  simp only [map_zero] at h2
  have hc := congrArg (fun φ => φ f) (MvPolynomial.comp_aeval (R := C) g (Polynomial.aeval (1 : C)))
  simp only [AlgHom.comp_apply] at hc
  rw [hc] at h2
  have h3 : (fun p : Fin N × Fin N => Polynomial.aeval (1 : C) (g p)) = fun p => (1 + E) p.1 p.2 := by
    funext p; simp [g]
  rw [h3] at h2
  unfold ev
  exact h2

end LateralTheory.DivDb.UnipotentPartTrivial
end

section

open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb

def Proj : Prop := ∀ (C : Type) [Field C] (N n : ℕ) (X : Mat C N) (e : Fin n → C), Function.Injective e → Deg n X →
  (∀ i, X.charpoly.IsRoot (e i)) →
  ∃ p : Fin n → Mat C N, Sys p ∧ X = ∑ i, e i • p i ∧ ∀ i, p i ∈ Algebra.adjoin C ({X} : Set (Mat C N))

def Grade : Prop := ∀ (C : Type) [Field C] [CharZero C] (N n : ℕ) (p : Fin n → Mat C N) (e : Fin n → C)
  (g : Submodule C (Mat C N)), Sys p → IsLac e →
  (∀ Y ∈ g, (∑ i, e i • p i) * Y - Y * (∑ i, e i • p i) ∈ g) → ∀ Y ∈ g, ∀ i j, i ≠ j → p i * Y * p j ∈ g

def CycleCount : Prop := ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (N n : ℕ) (p : Fin n → Mat C N)
  (y : Mat C N) (π : Equiv.Perm (Fin n)), Sys p → IsUnit y → (∀ j, y * p j = p (π j) * y) → Deg n y → Disj y π p →
  HasEig n y ∧ ∀ i, π i = i → ∃ c : C, y * p i = c • p i

def DiagScalar : Prop := ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (N n : ℕ) (p : Fin n → Mat C N)
  (e : Fin n → C) (Y : Mat C N), Sys p → Function.Injective e → (∀ i, Y * p i = p i * Y) →
  (∀ s : C, Deg n (s • Y + ∑ i, e i • p i)) → ∀ i, ∃ c : C, Y * p i = c • p i

def AlgStruct : Prop := ∀ (C : Type) [Field C] (N n : ℕ) (p : Fin n → Mat C N) (g : Submodule C (Mat C N)), Sys p →
  (∀ Y ∈ g, ∀ Z ∈ g, Y * Z - Z * Y ∈ g) → (∀ Y ∈ g, ∀ i j, i ≠ j → p i * Y * p j ∈ g) →
  (∀ Y ∈ g, (∀ i, Y * p i = p i * Y) → ∀ i, ∃ c : C, Y * p i = c • p i) →
  ∀ a ∈ Algebra.adjoin C (g : Set (Mat C N)),
    (∀ i j, i ≠ j → p i * a * p j ∈ g) ∧ ∀ i, ∃ c : C, p i * a * p i = c • p i

def Semis : Prop := ∀ (Γ C : Type) [Group Γ] [Field C] (N : ℕ) (ρ : Γ →* GL (Fin N) C) (A : Subalgebra C (Mat C N)),
  IsSSMat ρ → Normd ρ A → Keeps ρ A → NoNil A

def MatrixUnits₂ : Prop := ∀ (C : Type) [Field C] (N n : ℕ) (A : Subalgebra C (Mat C N)) (p : Fin n → Mat C N),
  Sys p → Corner A p → NoNil A → ∃ E, MUnits A p E

def IdemConj : Prop := ∀ (C : Type) [Field C] [CharZero C] (N n : ℕ) (A : Subalgebra C (Mat C N))
  (p q : Fin n → Mat C N), Sys p → Corner A p → Sys q → Corner A q → NoNil A →
  ∃ v ∈ A, IsUnit v ∧ ∃ π : Equiv.Perm (Fin n), (∀ j, v * p j = q (π j) * v) ∧
    ∀ i, (∃ a ∈ A, q i * a * p i ≠ 0) → π i = i

def UnitFactorization : Prop := ∀ (C : Type) [Field C] (N n : ℕ) (A : Subalgebra C (Mat C N)) (p : Fin n → Mat C N)
  (E : Fin n → Fin n → Mat C N), Sys p → MUnits A p E → ∀ v ∈ A, IsUnit v →
  ∃ u ∈ Tv A p, ∃ d : Fin n → C, (∀ j, d j ≠ 0) ∧ v = u * ∑ j, d j • p j

def GenSpec : Prop := ∀ (C : Type) [Field C] (N n : ℕ) (p : Fin n → Mat C N) (x : Mat C N) (π : Equiv.Perm (Fin n)),
  Sys p → IsUnit x → (∀ j, x * p j = p (π j) * x) → ∃ B : Set C, B.Finite ∧ ∀ τ : Fin n → C, (∀ j, τ j ≠ 0) →
    MulLac τ B → Disj (x * ∑ j, τ j • p j) π p

def Struct : Prop := ∀ (Γ C : Type) [Group Γ] [Field C] [IsAlgClosed C] [CharZero C] (N n : ℕ)
  (ρ : Γ →* GL (Fin N) C) (X : Mat C N) (e : Fin n → C), IsSSMat ρ → (∀ g, Deg n (ρ g : Mat C N)) → X ∈ lie ρ →
  IsLac e → (∀ i, X.charpoly.IsRoot (e i)) → ∃ p, Good ρ e p

def Key : Prop := ∀ (Γ C : Type) [Group Γ] [Field C] [IsAlgClosed C] [CharZero C] (N n : ℕ)
  (ρ : Γ →* GL (Fin N) C) (e : Fin n → C) (p : Fin n → Mat C N), (∀ g, Deg n (ρ g : Mat C N)) → IsLac e → Good ρ e p →
  ∀ U : Subgroup Γ, U.Normal → U.FiniteIndex → ∀ g,
    (∃ m ∈ Zcl (img ρ U : Set (Mat C N)), HasEig n ((ρ g : Mat C N) * m)) ∧
    ∀ i, (∃ a ∈ env ρ, p i * a * (ρ g : Mat C N) * p i ≠ 0) → ∃ w ∈ env ρ, p i * (ρ g : Mat C N) = p i * w

def BigCorner : Prop := ∀ (Γ C : Type) [Group Γ] [Field C] (N n : ℕ) (ρ : Γ →* GL (Fin N) C)
  (A : Subalgebra C (Mat C N)) (p : Fin n → Mat C N), Corner A p → Normd ρ A → Keeps ρ A →
  (∀ g i, (∃ a ∈ A, p i * a * (ρ g : Mat C N) * p i ≠ 0) → ∃ w ∈ A, p i * (ρ g : Mat C N) = p i * w) →
  ∃ R : Subalgebra C (Mat C N), (∀ g, (ρ g : Mat C N) ∈ R) ∧ Corner R p ∧ Normd ρ R ∧ Keeps ρ R

def Rep : Prop := ∀ (Γ C : Type) [Group Γ] [Field C] (N n : ℕ) (ρ : Γ →* GL (Fin N) C) (R : Subalgebra C (Mat C N))
  (p : Fin n → Mat C N) (E : Fin n → Fin n → Mat C N), Sys p → MUnits R p E → (∀ g, (ρ g : Mat C N) ∈ R) →
  ∃ r A B, Sub (n := n) ρ r A B

def DenseAlg : Prop := ∀ (Γ C : Type) [Group Γ] [Field C] [CharZero C] (N n : ℕ) (ρ : Γ →* GL (Fin N) C)
  (r : Γ →* GL (Fin n) C) A B, Sub ρ r A B → ∀ (U : Subgroup Γ) (g : Γ), ∀ m ∈ Zcl (img ρ U : Set (Mat C N)),
  HasEig n ((ρ g : Mat C N) * m) → ∃ u ∈ U, (r (g * u) : Mat C n).charpoly.Separable

def DegAll : Prop := ∀ (Γ K : Type) [Group Γ] [TopologicalSpace Γ] [Field K] [TopologicalSpace K]
  [IsTopologicalRing K] [T2Space K] (N n : ℕ) (ρ : Γ →* GL (Fin N) K), Continuous (fun g => (ρ g : Mat K N)) →
  ∀ S : Set Γ, Dense S → (∀ s ∈ S, Deg n (ρ s : Mat K N)) → ∀ g, Deg n (ρ g : Mat K N)

def FinSub : Prop := ∀ (Γ K : Type) [Group Γ] [Field K] (N n : ℕ) (ρ : Γ →* GL (Fin N) K) (r : Γ →* GL (Fin n) K) A B,
  Sub ρ r A B → IsSSMat ρ → IsSSMat r ∧ A.rank = n ∧ (∀ g, (r g : Mat K n) = B * (ρ g : Mat K N) * A) ∧
  ∀ g (q : Polynomial K), Polynomial.aeval (ρ g : Mat K N) q = 0 ↔ Polynomial.aeval (r g : Mat K n) q = 0

def FinEmbed : Prop := ∀ (Γ K : Type) [Group Γ] [Field K] (N n : ℕ) (ρ : Γ →* GL (Fin N) K) (r : Γ →* GL (Fin n) K) A B,
  Sub ρ r A B → IsSSMat ρ → IsSSMat r →
  ∃ (k : ℕ) (T : Fin k → Matrix (Fin n) (Fin N) K) (T' : Fin k → Matrix (Fin N) (Fin n) K),
    (∀ j g, T j * (ρ g : Mat K N) = (r g : Mat K n) * T j) ∧ (∀ j g, (ρ g : Mat K N) * T' j = T' j * (r g : Mat K n)) ∧
    ∑ j, T' j * T j = 1

def FinDense : Prop := ∀ (Γ K : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
  [Field K] [CharZero K] [TopologicalSpace K] [IsTopologicalRing K] [T2Space K] (n : ℕ) (r : Γ →* GL (Fin n) K),
  Continuous (fun g => (r g : Mat K n)) →
  (∀ U : Subgroup Γ, U.Normal → U.FiniteIndex → ∀ g, ∃ u ∈ U, (r (g * u) : Mat K n).charpoly.Separable) →
  IsOpen {g | (r g : Mat K n).charpoly.Separable} ∧ Dense {g | (r g : Mat K n).charpoly.Separable}

def FinPoly : Prop := ∀ (K : Type) [Field K] [IsAlgClosed K] (n : ℕ) (x : Mat K n) (P : Polynomial K), P.Monic →
  P.natDegree = n → Polynomial.aeval x P = 0 → (x.charpoly.Separable → x.charpoly = P) ∧
  (ProdGen n P → x.det = (-1) ^ n * P.coeff 0 → x.charpoly = P)

end LateralTheory.DivDb
end

section

open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div

namespace LateralTheory.DivDb.OpenCosetPf
open LateralTheory.DivDb

theorem main (hChain : Chain) : OpenCoset :=
  _root_.UpperTheory.Reformulated.B.Qn18.main hChain

end LateralTheory.DivDb.OpenCosetPf

namespace LateralTheory.DivDb
theorem OpenCoset_of (hChain : Chain) : OpenCoset := OpenCosetPf.main hChain
end LateralTheory.DivDb
end

section

open Matrix Polynomial
namespace LateralTheory.DivDb.SepPolyProof

noncomputable def disc (C : Type) [Field C] (n : ℕ) : MvPolynomial (Fin n × Fin n) C :=
  resultant (charpoly.univ C (Fin n)) (derivative (charpoly.univ C (Fin n))) n (n - 1)

theorem univ_map_ev {C : Type} [Field C] {n : ℕ} (x : Mat C n) :
    (charpoly.univ C (Fin n)).map (MvPolynomial.eval (fun p : Fin n × Fin n => x p.1 p.2)) = x.charpoly := by
  have h := charpoly.univ_map_eval₂Hom (Fin n) (RingHom.id C) (fun p : Fin n × Fin n => x p.1 p.2)
  have hx : (Matrix.of (fun p : Fin n × Fin n => x p.1 p.2).curry) = x := by ext i j; rfl
  rw [hx] at h
  exact h

theorem ev_disc {C : Type} [Field C] [CharZero C] {n : ℕ} (x : Mat C n) :
    ev x (disc C n) = resultant x.charpoly (derivative x.charpoly) := by
  unfold ev disc
  rw [← resultant_map_map, ← derivative_map, univ_map_ev]
  have h1 : x.charpoly.natDegree = n := by simpa using charpoly_natDegree_eq_dim x
  rw [natDegree_derivative, h1]

end LateralTheory.DivDb.SepPolyProof

namespace LateralTheory.DivDb
open LateralTheory.DivDb.SepPolyProof in
theorem SepPoly_of : SepPoly := by
  intro C _ _ n
  refine ⟨disc C n, fun x => ?_⟩
  rw [ev_disc, Ne, resultant_eq_zero_iff]
  have h0 : x.charpoly ≠ 0 := (charpoly_monic x).ne_zero
  simp only [ne_eq, h0, not_false_eq_true, true_or, true_and, not_not]
  rfl
end LateralTheory.DivDb
end
