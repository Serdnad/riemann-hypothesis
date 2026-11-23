module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle798
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle809
public import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle810
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006

@[expose] public section

section

noncomputable section

namespace GlobalTheory.FinGL.LeviWh

open GlobalTheory.FinGL Formalism.L2.DIV Module

section Mat

variable {F : Type} [Field F] {r : ℕ} {k : Fin r} {H U : Matrix (Fin r) (Fin r) F}

theorem corner_row (hH : ∀ i j, H i j ≠ (1 : Matrix (Fin r) (Fin r) F) i j → i < k ∧ j < k)
    (N : Matrix (Fin r) (Fin r) F) {i : Fin r} (hi : ¬ i < k) (j : Fin r) : (H * N) i j = N i j := by
  have : (H * N) i j = ((1 : Matrix (Fin r) (Fin r) F) * N) i j := by
    rw [Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    have : H i m = (1 : Matrix (Fin r) (Fin r) F) i m := by
      by_contra hne
      exact hi (hH i m hne).1
    rw [this]
  rw [this, one_mul]

theorem corner_nil_mul (hH : ∀ i j, H i j ≠ (1 : Matrix (Fin r) (Fin r) F) i j → i < k ∧ j < k)
    (hU : ∀ i j : Fin r, j.val < k.val → U i j = (1 : Matrix (Fin r) (Fin r) F) i j) :
    (U - 1) * H = U - 1 := by
  conv_rhs => rw [← mul_one (U - 1)]
  ext i j
  rw [Matrix.mul_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  by_cases hm : m < k
  · rw [Matrix.sub_apply, hU i m hm, sub_self, zero_mul, zero_mul]
  · have : H m j = (1 : Matrix (Fin r) (Fin r) F) m j := by
      by_contra hne
      exact hm (hH m j hne).1
    rw [this]

end Mat

variable {F : Type} [Field F] {r : ℕ}

theorem corner_conj_val {k : Fin r} (h u : GL (Fin r) F)
    (hH : ∀ i j, (h : Matrix (Fin r) (Fin r) F) i j ≠ (1 : Matrix (Fin r) (Fin r) F) i j → i < k ∧ j < k)
    (hU : ∀ i j : Fin r, j.val < k.val → (u : Matrix (Fin r) (Fin r) F) i j = (1 : Matrix (Fin r) (Fin r) F) i j) :
    ((h * u * h⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) =
      1 + (h : Matrix (Fin r) (Fin r) F) * ((u : Matrix (Fin r) (Fin r) F) - 1) := by
  rw [Units.val_mul, Units.mul_inv_eq_iff_eq_mul, add_mul, mul_assoc, corner_nil_mul hH hU, Units.val_mul,
    mul_sub, one_mul, mul_one, add_sub_cancel]

theorem corner_conj {k : Fin r} (h u : GL (Fin r) F)
    (hH : ∀ i j, (h : Matrix (Fin r) (Fin r) F) i j ≠ (1 : Matrix (Fin r) (Fin r) F) i j → i < k ∧ j < k)
    (hU : ∀ i j : Fin r, j.val < k.val → (u : Matrix (Fin r) (Fin r) F) i j = (1 : Matrix (Fin r) (Fin r) F) i j) :
    (∀ i j : Fin r, ¬ i < k → ((h * u * h⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j =
      (u : Matrix (Fin r) (Fin r) F) i j) ∧
    (∀ i j : Fin r, j.val < k.val → ((h * u * h⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j =
      (1 : Matrix (Fin r) (Fin r) F) i j) ∧
    (∀ i : Fin r, ((h * u * h⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i k =
      ((h : Matrix (Fin r) (Fin r) F) * (u : Matrix (Fin r) (Fin r) F)) i k) := by
  rw [corner_conj_val h u hH hU]
  refine ⟨fun i j hi => ?_, fun i j hj => ?_, fun i => ?_⟩
  · rw [Matrix.add_apply, corner_row hH _ hi, Matrix.sub_apply, add_sub_cancel]
  · rw [Matrix.add_apply, Matrix.mul_apply, Finset.sum_eq_zero, add_zero]
    intro m _
    rw [Matrix.sub_apply, hU m j hj, sub_self, mul_zero]
  · have : (h : Matrix (Fin r) (Fin r) F) i k = (1 : Matrix (Fin r) (Fin r) F) i k := by
      by_contra hne
      exact lt_irrefl _ (hH i k hne).2
    rw [mul_sub, mul_one, Matrix.add_apply, Matrix.sub_apply, this, add_sub_cancel]

theorem eig_colChar_vecMul_ne_bot (F : Type) [Field F] (ψ : AddChar F ℂ) (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V) (k : Fin r) (l : Fin r → F)
    (h : blockTri (κ := F) b)
    (hH : ∀ i j, ((h : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j ≠ (1 : Matrix (Fin r) (Fin r) F) i j →
      i < k ∧ j < k)
    (hne : eig σ (colSet F b k.val) (colChar ψ b k l) ≠ ⊥) :
    eig σ (colSet F b k.val)
      (colChar ψ b k (Matrix.vecMul l ((h : GL (Fin r) F) : Matrix (Fin r) (Fin r) F))) ≠ ⊥ := by
  rw [Submodule.ne_bot_iff] at hne ⊢
  obtain ⟨v, hv, hv0⟩ := hne
  rw [mem_eig] at hv
  refine ⟨σ h⁻¹ v, ?_, fun h0 => hv0 ?_⟩
  · rw [mem_eig]
    rintro u ⟨hu, hU⟩
    obtain ⟨c1, c2, c3⟩ := corner_conj (h : GL (Fin r) F) (u : GL (Fin r) F) hH hU
    have hc : ((h * u * h⁻¹ : blockTri (κ := F) b) : GL (Fin r) F) =
        (h : GL (Fin r) F) * (u : GL (Fin r) F) * (h : GL (Fin r) F)⁻¹ := rfl
    have hmem : h * u * h⁻¹ ∈ colSet F b k.val := by
      refine ⟨?_, ?_⟩
      · rw [hc]
        refine ⟨fun i j hij => ?_, fun i => ?_⟩
        · have hij' : j < i := hij
          by_cases hj : j < k
          · rw [c2 i j hj, Matrix.one_apply_ne (ne_of_gt hij')]
          · rw [c1 i j (fun hi => hj (hij'.trans hi)), unip_lower hu hij']
        · by_cases hi : i < k
          · rw [c2 i i hi, Matrix.one_apply_eq]
          · rw [c1 i i hi, unip_diag hu]
      · rw [hc]; exact c2
    have hχ : colChar ψ b k l (h * u * h⁻¹) =
        colChar ψ b k (Matrix.vecMul l ((h : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)) u := by
      unfold colChar
      rw [hc]
      congr 2
      · simp only [c3]
        have := congrFun (Matrix.vecMul_vecMul l ((h : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)
          ((u : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)) k
        exact this.symm
      · unfold edgeSum
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        split_ifs with hij
        · refine c1 i j fun hi => ?_
          have h1 : j.val = i.val + 1 := hij.1.1
          have h2 : k.val < j.val := hij.2
          have h3 : i.val < k.val := hi
          omega
        · rfl
    have e : σ u (σ h⁻¹ v) = σ h⁻¹ (σ (h * u * h⁻¹) v) := by
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
      congr 2
      group
    rw [e, hv _ hmem, map_smul, hχ]
  · have : σ h (σ h⁻¹ v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [← this, h0, map_zero]

end GlobalTheory.FinGL.LeviWh
end
end

section

open GlobalTheory.LogDerProj

set_option autoImplicit false

namespace GlobalTheory.LogDerProj

theorem exists_pow_smul_eq_res : ∀ {k R S : Type} [Field k] [CommRing R] [CommRing S] [Algebra R S] (f : R)
    [IsLocalization.Away f S] (φ : k →+* R), φ.FiniteType → ∀ (J : Ideal R)
    (n : (logSub ((algebraMap R S).comp φ) (J.map (algebraMap R S))).restrictScalars R),
    ∃ x : logSub φ J × Submonoid.powers f, x.2 • n = res (S := S) f φ J x.1 := by
  intro k R S _ _ _ _ f _ φ hφ J n
  letI : Algebra k R := φ.toAlgebra
  haveI : Algebra.FiniteType k R := hφ
  haveI : Algebra.FinitePresentation k R := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  letI : Algebra k S := ((algebraMap R S).comp φ).toAlgebra
  haveI : IsScalarTower k R S := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hn0 : ∀ c : k, n.1 (algebraMap R S (φ c)) = 0 := fun c => n.2.1 c
  have hnJ : ∀ y ∈ J.map (algebraMap R S), n.1 y ∈ J.map (algebraMap R S) := n.2.2
  let gl : R →ₗ[k] S :=
    { toFun := fun r => n.1 (algebraMap R S r)
      map_add' := fun a b => by simp
      map_smul' := fun c r => by
        rw [RingHom.id_apply, Algebra.smul_def, map_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
        show _ = algebraMap R S (φ c) * _
        rw [show algebraMap k R c = φ c from rfl, hn0, mul_zero, add_zero] }
  let g : Derivation k R S := Derivation.mk' gl fun a b => by
    show n.1 (algebraMap R S (a * b)) = a • n.1 (algebraMap R S b) + b • n.1 (algebraMap R S a)
    rw [map_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul, Algebra.smul_def, Algebra.smul_def]
  have hg : ∀ r, g r = n.1 (algebraMap R S r) := fun r => rfl
  obtain ⟨h, s, hs⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule (Submonoid.powers f)
    (Algebra.linearMap R S) g.liftKaehlerDifferential
  let D' : Derivation k R R := h.compDer (KaehlerDifferential.D k R)
  have hD' : ∀ r, algebraMap R S (D' r) = algebraMap R S s * n.1 (algebraMap R S r) := by
    intro r
    have := congrArg (fun L : Ω[R⁄k] →ₗ[R] S => L (KaehlerDifferential.D k R r)) hs
    simp only [LinearMap.coe_comp, Function.comp_apply, Algebra.linearMap_apply, LinearMap.smul_apply,
      Derivation.liftKaehlerDifferential_comp_D] at this
    rw [Submonoid.smul_def, Algebra.smul_def] at this
    rw [← hg]
    exact this
  have hJfg : J.FG := IsNoetherian.noetherian J
  obtain ⟨T, hT⟩ := hJfg
  have hex : ∀ t : T, ∃ m : Submonoid.powers f, (m : R) * D' t ∈ J := by
    intro t
    have ht : (t : R) ∈ J := hT ▸ Ideal.subset_span t.2
    have h1 : algebraMap R S (D' t) ∈ J.map (algebraMap R S) := by
      rw [hD']
      exact Ideal.mul_mem_left _ _ (hnJ _ (Ideal.mem_map_of_mem _ ht))
    obtain ⟨m, hm, hmJ⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers f) S J _).1 h1
    exact ⟨⟨m, hm⟩, hmJ⟩
  choose c hc using hex
  let m : Submonoid.powers f := ∏ t, c t
  have hmT : ∀ t ∈ T, (m : R) * D' t ∈ J := by
    intro t ht
    have hdvd : (c ⟨t, ht⟩ : R) ∣ (m : R) := by
      show (c ⟨t, ht⟩ : R) ∣ ((∏ t, c t : Submonoid.powers f) : R)
      change (c ⟨t, ht⟩ : R) ∣ (Submonoid.subtype (Submonoid.powers f)) (∏ t, c t)
      rw [map_prod]
      exact Finset.dvd_prod_of_mem _ (Finset.mem_univ _)
    obtain ⟨q, hq⟩ := hdvd
    rw [hq, mul_comm _ q, mul_assoc]
    exact Ideal.mul_mem_left _ _ (hc ⟨t, ht⟩)
  let D : Derivation ℤ R R := (m : R) • D'.restrictScalars ℤ
  have hDapp : ∀ r, D r = (m : R) * D' r := fun r => rfl
  have hDmem : D ∈ logSub φ J := by
    refine ⟨fun a => ?_, fun y hy => ?_⟩
    · rw [hDapp, show φ a = algebraMap k R a from rfl, D'.map_algebraMap, mul_zero]
    · rw [← hT] at hy
      induction hy using Submodule.span_induction with
      | mem x hx => rw [hDapp]; exact hmT x hx
      | zero => rw [map_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | smul a x hx' hx =>
        rw [smul_eq_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
        have hxJ : x ∈ J := by rw [← hT]; exact hx'
        exact add_mem (Ideal.mul_mem_left _ _ hx) (Ideal.mul_mem_right _ _ hxJ)
  refine ⟨(⟨D, hDmem⟩, m * s), ?_⟩
  apply Subtype.ext
  refine der_ext f _ _ fun r => ?_
  rw [res_apply, hDapp]
  show ((m * s : Submonoid.powers f) : R) • n.1 (algebraMap R S r) = _
  rw [Algebra.smul_def, Submonoid.coe_mul, map_mul, map_mul, hD', mul_assoc]

end GlobalTheory.LogDerProj
end

section

open GlobalTheory.LogDerProj

noncomputable section
set_option autoImplicit false

namespace GlobalTheory.LogDerProj

theorem exists_pow_smul_eq_of_res_eq {k R S : Type} [Field k] [CommRing R] [CommRing S] [Algebra R S] (f : R)
    [IsLocalization.Away f S] (φ : k →+* R) (hφ : φ.FiniteType) (J : Ideal R) (D₁ D₂ : logSub φ J)
    (h : res (S := S) f φ J D₁ = res (S := S) f φ J D₂) : ∃ c : Submonoid.powers f, c • D₁ = c • D₂ := by
  classical
  set E : Derivation ℤ R R := D₁.1 - D₂.1 with hE
  have hloc : ∀ r, ∃ m : Submonoid.powers f, (m : R) * E r = 0 := by
    intro r
    have h1 := congrArg (fun D => D.1 (algebraMap R S r)) h
    simp only [res_apply] at h1
    have h2 : algebraMap R S (E r) = 0 := by
      rw [hE, Derivation.sub_apply, map_sub, h1, sub_self]
    exact (IsLocalization.map_eq_zero_iff (Submonoid.powers f) S _).1 h2
  choose m hm using hloc
  letI := φ.toAlgebra
  have hft : Algebra.FiniteType k R := hφ
  obtain ⟨s, hs⟩ := hft.out
  let c : Submonoid.powers f := ∏ x ∈ s, m x
  have hcs : ∀ x ∈ s, (c : R) * E x = 0 := by
    intro x hx
    have : (c : R) = (∏ y ∈ s.erase x, m y : Submonoid.powers f) * m x := by
      simp only [c]
      rw [← Submonoid.coe_mul, ← Finset.prod_erase_mul s m hx]
    rw [this, mul_assoc, hm x, mul_zero]
  have hall : ∀ r, (c : R) * E r = 0 := by
    intro r
    have hr : r ∈ Algebra.adjoin k (s : Set R) := by rw [hs]; trivial
    induction hr using Algebra.adjoin_induction with
    | mem x hx => exact hcs x hx
    | algebraMap a =>
      have e1 : D₁.1 (φ a) = 0 := D₁.2.1 a
      have e2 : D₂.1 (φ a) = 0 := D₂.2.1 a
      show (c : R) * E (φ a) = 0
      rw [hE, Derivation.sub_apply, e1, e2, sub_self, mul_zero]
    | add x y _ _ hx hy => rw [map_add (f := _), mul_add, hx, hy, add_zero]
    | mul x y _ _ hx hy =>
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, mul_add]
      calc (c : R) * (x * E y) + (c : R) * (y * E x) = x * ((c : R) * E y) + y * ((c : R) * E x) := by ring
        _ = 0 := by rw [hx, hy, mul_zero, mul_zero, add_zero]
  refine ⟨c, ?_⟩
  apply Subtype.ext
  ext r
  rw [Submonoid.smul_def, Submonoid.smul_def]
  show ((c : R) • D₁.1) r = ((c : R) • D₂.1) r
  rw [Derivation.smul_apply, Derivation.smul_apply, smul_eq_mul, smul_eq_mul, ← sub_eq_zero, ← mul_sub]
  have := hall r
  rwa [hE, Derivation.sub_apply] at this

end GlobalTheory.LogDerProj
end
end

section

open Classical MvPolynomial

noncomputable section
namespace GlobalTheory.MinorFrame
open scoped Matrix
variable {ι : Type} [Fintype ι]

theorem eval_minorAt_frame {a d : ℕ} (x₀ : Var ι d a → ℂ) (τ : ι) (s : Fin a → Fin d) :
    eval x₀ (minorAt τ s) = ((Matrix.of fun (r : Fin d) (i : Fin a) => x₀ (τ, r, i)).submatrix s id).det := by
  unfold minorAt
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp

theorem rsub_frame_X {a d : ℕ} (x₀ : Var ι d a → ℂ) (τ : ι) (i j : Fin a) :
    rsub (frameMat x₀)ᴴ (X (τ, i, j)) = ∑ r : Fin d, C (star (x₀ (τ, r, i))) * (X (τ, r, j) : Pol ι d a) := by
  rw [rsub_X, Fintype.sum_prod_type, Finset.sum_eq_single τ]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_eq_single j]
    · simp [frameMat, Matrix.conjTranspose_apply]
    · intro b _ hb; simp [frameMat, Matrix.conjTranspose_apply, Ne.symm hb]
    · simp
  · intro b _ hb
    refine Finset.sum_eq_zero fun w _ => ?_
    simp [frameMat, Matrix.conjTranspose_apply, Ne.symm hb]
  · simp

end GlobalTheory.MinorFrame

noncomputable section
namespace GlobalTheory.MinorFrame
open scoped Matrix
variable {ι : Type} [Fintype ι]

theorem rsub_frame_det {a d : ℕ} (x₀ : Var ι d a → ℂ) (τ : ι) :
    rsub (frameMat x₀)ᴴ ((Matrix.of fun i j : Fin a => (X (τ, i, j) : MvPolynomial (ι × Fin a × Fin a) ℂ)).det) =
      ∑ s : {s : Fin a → Fin d // StrictMono s}, C (star (eval x₀ (minorAt τ s.1))) * minorAt τ s.1 := by
  rw [AlgHom.map_det]
  set A : Matrix (Fin d) (Fin a) ℂ := Matrix.of fun (r : Fin d) (i : Fin a) => x₀ (τ, r, i) with hA
  have hM : (rsub (frameMat x₀)ᴴ : MvPolynomial (ι × Fin a × Fin a) ℂ →ₐ[ℂ] Pol ι d a).mapMatrix
      (Matrix.of fun i j : Fin a => (X (τ, i, j) : MvPolynomial (ι × Fin a × Fin a) ℂ)) =
      (Aᴴ.map (C : ℂ →+* Pol ι d a)) * xMat τ d a := by
    ext i j
    simp [rsub_frame_X, xMat, Matrix.mul_apply, hA, Matrix.conjTranspose_apply]
  rw [hM, det_mul_eq_sum_sm]
  refine Finset.sum_congr rfl fun s _ => ?_
  congr 1
  · rw [eval_minorAt_frame, ← hA, Matrix.submatrix_map, ← Matrix.det_conjTranspose, Matrix.conjTranspose_submatrix]
    exact (RingHom.map_det _ _).symm

theorem rsub_frame_detG {a d : ℕ} (n : ι → ℕ) (x₀ : Var ι d a → ℂ) :
    rsub (frameMat x₀).conjTranspose (detG a n) =
      ∑ T : Tup ι a d n, star (eval x₀ (prodMinors T)) • prodMinors T := by
  unfold detG
  simp only [map_prod, map_pow, rsub_frame_det]
  rw [Finset.prod_congr rfl fun τ _ => (Fin.prod_const (n τ) _).symm]
  rw [Finset.prod_congr rfl fun τ _ => Fintype.prod_sum _, Fintype.prod_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  unfold prodMinors
  simp only [map_prod, star_prod, smul_eq_C_mul, Finset.prod_mul_distrib]

end GlobalTheory.MinorFrame

namespace GlobalTheory.MinorFrame

theorem rsub_frame_detG_eq_sum : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (n : ι → ℕ) (x₀ : Var ι d a → ℂ),
    rsub (frameMat x₀).conjTranspose (detG a n) =
      ∑ T : Tup ι a d n, star (MvPolynomial.eval x₀ (prodMinors T)) • prodMinors T :=
  fun _ _ n x₀ => rsub_frame_detG n x₀

end GlobalTheory.MinorFrame
end
end
end

section

noncomputable section

open MvPolynomial Matrix Formalism.L2.DIV

namespace GlobalTheory.MinorFrame

variable {σ σ' : Type} [Fintype σ] [Fintype σ']

theorem constantCoeff_rsub (M : Matrix σ' σ ℂ) (g : MvPolynomial σ ℂ) :
    constantCoeff (rsub M g) = constantCoeff g := by
  have : (constantCoeff : MvPolynomial σ' ℂ →+* ℂ).comp (rsub M).toRingHom = constantCoeff := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp
    · intro i; simp [rsub_X]
  exact congrArg (fun φ : MvPolynomial σ ℂ →+* ℂ => φ g) this

theorem pderiv_rsub [DecidableEq σ] [DecidableEq σ'] (M : Matrix σ' σ ℂ) (s : σ') (g : MvPolynomial σ ℂ) :
    pderiv s (rsub M g) = ∑ w, C (M s w) * rsub M (pderiv w g) := by
  induction g using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p k hp =>
    have hX : pderiv s (rsub M (X k)) = C (M s k) := by

      rw [rsub_X, map_sum, Finset.sum_eq_single s]
      · simp [pderiv_X]
      · intro b _ hb
        rw [Derivation.leibniz, pderiv_C, pderiv_X_of_ne hb]
        simp
      · simp
    rw [map_mul, Derivation.leibniz, hX, hp, smul_eq_mul, smul_eq_mul]
    simp_rw [Derivation.leibniz, smul_eq_mul, map_add (f := _), map_mul, mul_add, Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_eq_single k]
      · rw [pderiv_X_self, map_one]; ring
      · intro b _ hb
        rw [pderiv_X_of_ne hb.symm]
        simp
      · simp
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring

theorem fockL_rsub_adj (M : Matrix σ' σ ℂ) (F : MvPolynomial σ ℂ) (F' : MvPolynomial σ' ℂ) :
    fockL (rsub M F) F' = fockL F (rsub Mᴴ F') := by
  classical
  induction F using MvPolynomial.induction_on generalizing F' with
  | C a => rw [algHom_C, algebraMap_eq, fockL_C_left, fockL_C_left, constantCoeff_rsub]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, hp, hq]
  | mul_X p v hp =>
    have e1 : rsub M (p * X v) = ∑ w, M w v • (X w * rsub M p) := by
      rw [map_mul, rsub_X, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_eq_C_mul]; ring

    rw [e1, map_sum, LinearMap.sum_apply]
    simp_rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, fockL_X_pderiv, hp]

    rw [mul_comm p, fockL_X_pderiv, pderiv_rsub, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← smul_eq_C_mul, map_smul, Matrix.conjTranspose_apply, starRingEnd_apply]

theorem fockS_rsub_adj : ∀ {σ σ' : Type} [Fintype σ] [Fintype σ'] (M : Matrix σ' σ ℂ) (F : MvPolynomial σ ℂ)
    (F' : MvPolynomial σ' ℂ), Formalism.L2.DIV.fockS (GlobalTheory.MinorFrame.rsub M F) F' =
      Formalism.L2.DIV.fockS F (GlobalTheory.MinorFrame.rsub M.conjTranspose F') := by
  intro σ σ' _ _ M F F'
  exact fockL_rsub_adj M F F'

end GlobalTheory.MinorFrame

end
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.contDiffAt_psi_chart_of_not_mem_zeroSet : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (L : La) (s : Fin n → ι → Y → ℂ), (∀ k, A.IsSec L (s k)) → ∀ y, y ∉ A.zeroSet s → ∀ i, y ∈ (A.chart i).source → ContDiffAt ℝ ∞ (psi A L s ∘ (A.chart i).symm) (A.chart i y) := by
  first | exact @GlobalTheory.OTY.contDiffAt_psi_of_notMem_zeroSet | exact GlobalTheory.OTY.contDiffAt_psi_of_notMem_zeroSet | (intros; apply GlobalTheory.OTY.contDiffAt_psi_of_notMem_zeroSet <;> assumption)
end
