module

public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.ClifMod
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.RealTrOfAll

@[expose] public section

section

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private theorem sl2Core {V : Type} [AddCommGroup V] [Module ℂ V] (E G A B : Module.End ℂ V)
    (S : Submodule ℂ V) (hfin : FiniteDimensional ℂ S)
    (hEG : ∀ v, E (G v) = G (E v) + A v - B v)
    (hAG : ∀ v, A (G v) = G (A v) - G v)
    (hBG : ∀ v, B (G v) = G (B v) + G v)
    (hS : ∀ v ∈ S, G v ∈ S) (α β : ℂ) (x : V) (hxS : x ∈ S) (hx : x ≠ 0)
    (hA : A x = α • x) (hB : B x = β • x) (hE : E x = 0) :
    ∃ m : ℕ, α - β = (m : ℂ) := by
  classical
  let v : ℕ → V := fun k => (G ^ k) x
  have hv0 : v 0 = x := by simp [v]
  have hv : ∀ k, v (k + 1) = G (v k) := by
    intro k
    simp [v, pow_succ', Module.End.mul_apply]
  have hvS : ∀ k, v k ∈ S := by
    intro k
    induction k with
    | zero => simpa [hv0] using hxS
    | succ k ih => rw [hv]; exact hS _ ih
  have hAk : ∀ k : ℕ, A (v k) = (α - k) • v k := by
    intro k
    induction k with
    | zero => simp [hv0, hA]
    | succ k ih =>
      rw [hv, hAG, ih, map_smul]
      push_cast
      module
  have hBk : ∀ k : ℕ, B (v k) = (β + k) • v k := by
    intro k
    induction k with
    | zero => simp [hv0, hB]
    | succ k ih =>
      rw [hv, hBG, ih, map_smul]
      push_cast
      module
  have hEk : ∀ k : ℕ, E (v (k + 1)) = (((k : ℂ) + 1) * (α - β - k)) • v k := by
    intro k
    induction k with
    | zero =>
      rw [hv, hEG, hv0, hE, hA, hB, map_zero]
      push_cast
      module
    | succ k ih =>
      rw [hv (k + 1), hEG, ih, map_smul, ← hv, hAk, hBk]
      push_cast
      module
  have hex : ∃ k, v k = 0 := by
    by_contra hne
    push_neg at hne
    have hli : LinearIndependent ℂ v := by
      apply Module.End.eigenvectors_linearIndependent' A (fun k : ℕ => α - k)
      · intro i j hij
        have : (i : ℂ) = j := by simpa using hij
        exact_mod_cast this
      · intro i
        rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
        exact ⟨hAk i, hne i⟩
    let w : ℕ → S := fun k => ⟨v k, hvS k⟩
    have hliw : LinearIndependent ℂ w := by
      apply LinearIndependent.of_comp S.subtype
      exact hli
    have : Finite ℕ := hliw.finite
    exact not_finite ℕ
  have hk : v (Nat.find hex) = 0 := Nat.find_spec hex
  have hk0 : Nat.find hex ≠ 0 := by
    intro h0
    apply hx
    rw [← hv0, ← h0]
    exact hk
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  have hvm : v m ≠ 0 := Nat.find_min hex (by omega)
  have hvm1 : v (m + 1) = 0 := by
    rw [show m + 1 = Nat.find hex by omega]
    exact hk
  have h := hEk m
  rw [hvm1, map_zero] at h
  have hc : ((m : ℂ) + 1) * (α - β - m) = 0 := by
    by_contra hc
    exact hvm ((smul_eq_zero.mp h.symm).resolve_left hc)
  have hm1 : (m : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  refine ⟨m, ?_⟩
  have := (mul_eq_zero.mp hc).resolve_left hm1
  linear_combination this

theorem UpperTheory.RealTr.hwDom :
    ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (F : Fin n → Fin n → Module.End ℂ V), UF F → ∀ S : Submodule ℂ V, FiniteDimensional ℂ S → Stb F S → ∀ (ν : Wt n), ∀ x ∈ S, x ≠ 0 → x ∈ hw F ν → Dom ν := by
  intro n V _ _ F hUF S hfin hStb ν x hxS hx hxw
  have hk : KHighest (fun _ => true) F ν x := hxw
  have hgl : GlRel F := hUF.gl
  intro a b hab
  have hne : a ≠ b := ne_of_lt hab
  have hEG : ∀ v, F a b (F b a v) = F b a (F a b v) + F a a v - F b b v := by
    intro v
    have h := LinearMap.congr_fun (hgl a b b a) v
    simp only [if_true, LinearMap.sub_apply, Module.End.mul_apply] at h
    rw [← sub_eq_zero]
    rw [← sub_eq_zero] at h
    convert h using 1
    abel
  have hAG : ∀ v, F a a (F b a v) = F b a (F a a v) - F b a v := by
    intro v
    have h := LinearMap.congr_fun (hgl a a b a) v
    simp only [if_neg hne, if_true, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.zero_apply] at h
    rw [← sub_eq_zero]
    rw [← sub_eq_zero] at h
    convert h using 1
    abel
  have hBG : ∀ v, F b b (F b a v) = F b a (F b b v) + F b a v := by
    intro v
    have h := LinearMap.congr_fun (hgl b b b a) v
    simp only [if_neg hne, if_neg hne.symm, if_true, LinearMap.sub_apply, Module.End.mul_apply,
      LinearMap.zero_apply] at h
    rw [← sub_eq_zero]
    rw [← sub_eq_zero] at h
    convert h using 1
    abel
  have hS : ∀ v ∈ S, F b a v ∈ S := fun v hv => hStb b a v hv
  obtain ⟨m, hm⟩ := sl2Core (F a b) (F b a) (F a a) (F b b) S hfin hEG hAG hBG hS
    (ν a : ℂ) (ν b : ℂ) x hxS hx (hk.1 a) (hk.1 b) (hk.2 a b hab rfl)
  refine ⟨m, ?_⟩
  apply Complex.ofReal_injective
  push_cast
  exact hm
end
end

section

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private theorem evT_ex' {n : ℕ} (θ x : Wt n) :
    evT θ (ex x) = Complex.exp (Complex.I * ∑ a, (θ a : ℂ) * (x a : ℂ)) := by
  simp [evT, ex, AddMonoidAlgebra.lift_single]

private theorem evT_alt' {n : ℕ} (θ x : Wt n) :
    evT θ (alt x) = (Matrix.of fun a b : Fin n => Complex.exp (Complex.I * ((θ a : ℂ) * (x b : ℂ)))).det := by
  rw [← Matrix.det_transpose, Matrix.det_apply]

  simp only [alt, map_sum, map_smul, evT_ex', smul_eq_mul, sg, Matrix.transpose_apply, Matrix.of_apply]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← Complex.exp_sum, Units.smul_def, zsmul_eq_mul, Finset.mul_sum]
  rfl

private theorem den_ne {n : ℕ} (z : Fin n → ℂ) (hz : Function.Injective z) :
    (Matrix.of fun i j : Fin n => z i ^ (n - 1 - (j : ℕ))).det ≠ 0 := by
  have e : (Matrix.of fun i j : Fin n => z i ^ (n - 1 - (j : ℕ))) =
      (Matrix.vandermonde z).submatrix id Fin.revPerm := by
    ext i j
    simp only [Matrix.of_apply, Matrix.submatrix_apply, id, Matrix.vandermonde_apply, Fin.revPerm_apply, Fin.val_rev]
    congr 1
    omega
  rw [e, Matrix.det_permute']
  refine mul_ne_zero ?_ (Matrix.det_vandermonde_ne_zero_iff.mpr hz)
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n))) with h | h <;> simp [h]

private theorem first' {n : ℕ} (lam : Fin n → ℤ) (θ : Wt n) (z : Fin n → ℂ)
    (hz : ∀ a, z a = Complex.exp (Complex.I * θ a)) (hinj : Function.Injective z) :
    weylChar lam z * evT θ (alt (rhoV n)) = evT θ (alt ((fun a => (lam a : ℝ)) + rhoV n)) := by
  set c : Fin n → ℂ := fun a => Complex.exp (Complex.I * (θ a : ℂ) * ((1 - (n : ℂ)) / 2)) with hc
  have hcast : ∀ b : Fin n, (((n - 1 - (b : ℕ) : ℕ) : ℂ)) = (n : ℂ) - 1 - ((b : ℕ) : ℂ) := by
    intro b
    have := b.isLt
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    simp
  have hD : evT θ (alt (rhoV n)) =
      (∏ a, c a) * (Matrix.of fun i j : Fin n => z i ^ (n - 1 - (j : ℕ))).det := by
    rw [evT_alt', ← Matrix.det_mul_column]
    congr 1
    ext a b
    simp only [Matrix.of_apply, hz a, rhoV, c]
    rw [← Complex.exp_nat_mul, ← Complex.exp_add, hcast b]
    congr 1
    push_cast
    ring
  have hA : evT θ (alt ((fun a => (lam a : ℝ)) + rhoV n)) =
      (∏ a, c a) * (Matrix.of fun i j : Fin n => z i ^ (lam j + ((n - 1 - (j : ℕ) : ℕ) : ℤ))).det := by
    rw [evT_alt', ← Matrix.det_mul_column]
    congr 1
    ext a b
    simp only [Matrix.of_apply, hz a, rhoV, c, Pi.add_apply]
    rw [← Complex.exp_int_mul, ← Complex.exp_add]
    congr 1
    push_cast
    rw [hcast b]
    ring
  rw [hD, hA, weylChar]
  have hden := den_ne z hinj
  field_simp

theorem UpperTheory.RealTr.weylEv :
    ∀ (n : ℕ) (lam : Fin n → ℤ) (θ : Wt n) (z : Fin n → ℂ), (∀ a, z a = Complex.exp (Complex.I * θ a)) →
      (Function.Injective z → weylChar lam z * evT θ (alt (rhoV n)) = evT θ (alt ((fun a => (lam a : ℝ)) + rhoV n))) ∧
      ((Function.Injective fun a => z a ^ 2) → weylChar lam (fun a => z a ^ 2) * evT θ (alt ((2 : ℝ) • rhoV n)) = evT θ (alt (twoL lam))) ∧
      ∏ a, ∏ b, (1 + z a / z b) = evT θ (∏ a, ∏ b, (1 + ex (rt a b))) ∧
      ∀ y : Fin n → ℂ, conj (weylChar lam fun a => conj (y a)) = weylChar lam y := by
  intro n lam θ z hz
  refine ⟨first' lam θ z hz, ?_, ?_, ?_⟩
  · intro hinj2
    have h := first' lam ((2 : ℝ) • θ) (fun a => z a ^ 2) (fun a => by
      rw [hz a, ← Complex.exp_nat_mul]
      congr 1
      simp only [Pi.smul_apply, smul_eq_mul]
      push_cast
      ring) hinj2
    have e1 : evT θ (alt ((2 : ℝ) • rhoV n)) = evT ((2 : ℝ) • θ) (alt (rhoV n)) := by
      rw [evT_alt', evT_alt']
      congr 1
      ext a b
      simp only [Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
      congr 1
      push_cast
      ring
    have e2 : evT θ (alt (twoL lam)) = evT ((2 : ℝ) • θ) (alt ((fun a => (lam a : ℝ)) + rhoV n)) := by
      rw [evT_alt', evT_alt']
      congr 1
      ext a b
      simp only [Matrix.of_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply, twoL]
      congr 1
      push_cast
      ring
    rw [e1, e2]
    exact h
  · simp only [map_prod, map_add (f := _), map_one, evT_ex']
    refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun b _ => ?_
    congr 1
    rw [hz a, hz b, ← Complex.exp_sub]
    congr 1
    simp only [rt, Pi.sub_apply, Complex.ofReal_sub, mul_sub, Finset.sum_sub_distrib, Pi.single_apply,
      apply_ite (fun r : ℝ => (r : ℂ)), Complex.ofReal_one, Complex.ofReal_zero, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · intro y
    simp only [weylChar, map_div₀, RingHom.map_det, RingHom.mapMatrix_apply]
    congr 1 <;> congr 1 <;> ext i j <;> simp [map_zpow₀]
end
end

section

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private theorem wsp_orth {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {F : Fin n → Fin n → Module.End ℂ V} (hF : UF F) {μ ν : Wt n} (h : μ ≠ ν) {x y : V}
    (hx : x ∈ wsp F μ) (hy : y ∈ wsp F ν) : ⟪x, y⟫_ℂ = 0 := by
  obtain ⟨a, ha⟩ := Function.ne_iff.1 h
  have h1 := hF.unit a a x y
  have hx' : F a a x = (μ a : ℂ) • x := hx a
  have hy' : F a a y = (ν a : ℂ) • y := hy a
  rw [hx', hy', inner_smul_left, inner_smul_right, Complex.conj_ofReal] at h1
  have h2 : ((μ a : ℂ) - (ν a : ℂ)) * ⟪x, y⟫_ℂ = 0 := by rw [sub_mul, h1, sub_self]
  have h3 : (μ a : ℂ) - (ν a : ℂ) ≠ 0 := by
    rw [sub_ne_zero]
    exact fun e => ha (Complex.ofReal_injective e)
  exact (mul_eq_zero.1 h2).resolve_left h3

theorem UpperTheory.RealTr.wtDec :
    ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (F : Fin n → Fin n → Module.End ℂ V), UF F → ∀ S : Submodule ℂ V, FiniteDimensional ℂ S → Stb F S → ∃ s : Finset (Wt n), (∀ μ ∉ s, wsp F μ ⊓ S = ⊥) ∧ (⨆ μ ∈ s, wsp F μ ⊓ S) = S ∧ iSupIndep fun μ => wsp F μ ⊓ S := by
  intro n V _ _ F hF S hSfin hS
  have hind : iSupIndep fun μ => wsp F μ ⊓ S := by
    refine OrthogonalFamily.independent (OrthogonalFamily.of_pairwise fun μ ν hne => ?_)
    show (wsp F μ ⊓ S) ⟂ (wsp F ν ⊓ S)
    rw [Submodule.isOrtho_iff_inner_eq]
    intro x hx y hy
    exact wsp_orth hF hne hx.1 hy.1
  let T : Fin n → Module.End ℂ S := fun a => (F a a).restrict (fun x hx => hS a a x hx)
  have hT : ∀ a, (T a).IsSymmetric := by
    intro a x y
    rw [Submodule.coe_inner, Submodule.coe_inner]
    exact hF.unit a a x y
  have hcomm : Pairwise fun a b => Commute (T a) (T b) := by
    intro a b hab
    have h0 : F a a * F b b = F b b * F a a := by
      have := hF.gl a a b b
      rw [if_neg hab, if_neg (Ne.symm hab), sub_zero, sub_eq_zero] at this
      exact this
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    show F a a (F b b (x : V)) = F b b (F a a (x : V))
    exact LinearMap.congr_fun h0 (x : V)
  have htop := LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hT hcomm
  have hkey : ∀ χ : Fin n → ℂ, ∀ v : S, v ∈ (⨅ i, Module.End.eigenspace (T i) (χ i)) →
      (v : V) ∈ wsp F (fun i => (χ i).re) ⊓ S := by
    intro χ v hv
    refine ⟨?_, v.2⟩
    show ∀ i, F i i (v : V) = (((χ i).re : ℝ) : ℂ) • (v : V)
    intro i
    have hvi : T i v = χ i • v := Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hv i)
    by_cases h0 : v = 0
    · subst h0
      simp
    · have hre : (((χ i).re : ℝ) : ℂ) = χ i := by
        have hs := hT i v v
        rw [hvi, inner_smul_left, inner_smul_right] at hs
        have hvv : ⟪v, v⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr h0
        exact Complex.conj_eq_iff_re.mp (mul_right_cancel₀ hvv hs)
      rw [hre]
      exact congrArg Subtype.val hvi
  have hspan : S ≤ ⨆ μ : Wt n, wsp F μ ⊓ S := by
    have hle : Submodule.map S.subtype (⨆ χ : Fin n → ℂ, ⨅ i, Module.End.eigenspace (T i) (χ i))
        ≤ ⨆ μ : Wt n, wsp F μ ⊓ S := by
      rw [Submodule.map_iSup]
      refine iSup_le fun χ => ?_
      rintro _ ⟨v, hv, rfl⟩
      exact le_iSup (fun μ : Wt n => wsp F μ ⊓ S) (fun i => (χ i).re) (hkey χ v hv)
    rw [htop, Submodule.map_top, Submodule.range_subtype] at hle
    exact hle
  have hfin : Set.Finite {μ : Wt n | wsp F μ ⊓ S ≠ ⊥} := by
    let W' : Wt n → Submodule ℂ S := fun μ => (wsp F μ).comap S.subtype
    have hind' : iSupIndep W' := by
      refine OrthogonalFamily.independent (OrthogonalFamily.of_pairwise fun μ ν hne => ?_)
      show W' μ ⟂ W' ν
      rw [Submodule.isOrtho_iff_inner_eq]
      intro x hx y hy
      rw [Submodule.coe_inner]
      exact wsp_orth hF hne hx hy
    haveI := hind'.fintypeNeBotOfFiniteDimensional
    refine (Set.finite_range (fun i : {μ // W' μ ≠ ⊥} => (i : Wt n))).subset ?_
    intro μ hμ
    refine ⟨⟨μ, fun h => hμ ?_⟩, rfl⟩
    rw [inf_comm, ← Submodule.map_comap_subtype]
    change Submodule.map S.subtype (W' μ) = ⊥
    rw [h, Submodule.map_bot]
  refine ⟨hfin.toFinset, ?_, ?_, hind⟩
  · intro μ hμ
    by_contra h
    exact hμ (hfin.mem_toFinset.mpr h)
  · apply le_antisymm
    · exact iSup₂_le fun μ _ => inf_le_right
    · refine hspan.trans (iSup_le fun μ => ?_)
      by_cases h : wsp F μ ⊓ S = ⊥
      · rw [h]
        exact bot_le
      · exact le_iSup₂_of_le μ (hfin.mem_toFinset.mpr h) le_rfl
end
end
