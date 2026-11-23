module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1514
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PerCApply

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem exists_pos_form {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (h1 : sigPosH hA = 1) :
    ∃ w : Fin n → ℂ, 0 < (star w ⬝ᵥ (A *ᵥ w)).re := by
  have hne : Nonempty {i : Fin n // 0 < hA.eigenvalues i} := by
    apply Fintype.card_pos_iff.1
    unfold sigPosH at h1
    omega
  obtain ⟨i, hi⟩ := hne
  refine ⟨(hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ Pi.single i 1, ?_⟩
  rw [GlobalTheory.SignatureOneForms.form_re_eq_sum hA]
  have hU : star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ
      ((hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ Pi.single i 1) = Pi.single i 1 := by
    rw [Matrix.mulVec_mulVec, Unitary.coe_star_mul_self, Matrix.one_mulVec]
  rw [hU, Finset.sum_eq_single i]
  · simpa using hi
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem UpperTheory.Gal.W2.sigB_of :
    UpperTheory.Gal.W2.SigB := by
  intro p _ G B v
  obtain ⟨hH, hdet, Z, hZ⟩ := GlobalTheory.LKCx.herm_laws p G v B.β B.sym B.trivR
  have hZi : (Z : Matrix (Fin G.n) (Fin G.n) ℂ) * ((Z⁻¹ : GL (Fin G.n) ℂ) : Matrix (Fin G.n) (Fin G.n) ℂ) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hiZ : ((Z⁻¹ : GL (Fin G.n) ℂ) : Matrix (Fin G.n) (Fin G.n) ℂ) * (Z : Matrix (Fin G.n) (Fin G.n) ℂ) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have key : ∀ x y : Fin G.n → ℂ, hv (GlobalTheory.LKCx.herm G v B.β) x y =
      star ((Z : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ y) ⬝ᵥ
        (G.gram v *ᵥ ((Z : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ x)) := by
    intro x y
    unfold hv
    rw [hZ, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_assoc]
  have hinj : ∀ x : Fin G.n → ℂ, x ≠ 0 → (Z : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ x ≠ 0 := by
    intro x hx h0
    apply hx
    have h2 := congrArg (fun w => ((Z⁻¹ : GL (Fin G.n) ℂ) : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ w) h0
    simpa [Matrix.mulVec_mulVec, hiZ] using h2
  refine ⟨hH, fun h1 => ⟨?_, ?_⟩, fun h1 => ?_⟩
  · obtain ⟨w, hw⟩ := exists_pos_form (G.gram_herm v) h1
    refine ⟨((Z⁻¹ : GL (Fin G.n) ℂ) : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ w, ?_⟩
    rw [key, Matrix.mulVec_mulVec, hZi, Matrix.one_mulVec]
    exact hw
  · intro z x hz hx hxz
    rw [key] at hz hxz ⊢
    exact GlobalTheory.re_form_neg_of_orth_of_sigPosH_eq_one (G.gram v) (G.gram_herm v) (G.gram_det v) h1 _ _ hz hxz (hinj x hx)
  · have h0 : sigPosH (G.gram_herm v) = 0 := by
      rcases G.sig v with h | h
      · exact absurd h.1 h1
      · exact h.1
    intro x hx
    rw [key]
    exact GlobalTheory.herm_negDef_of_sigPosH_eq_zero (G.gram v) (G.gram_herm v) (G.gram_det v) h0 _ (hinj x hx)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem nsmul_canc {V : Type} [AddCommGroup V] [Module ℚ V] {a : ℕ} (ha : a ≠ 0) {x y : V}
    (h : a • x = a • y) : x = y := by
  have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast ha
  have h' : (a : ℚ) • x = (a : ℚ) • y := by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]; exact h
  exact (smul_right_injective V ha') h'

private theorem ext_lin {Λ V V' : Type} [AddCommGroup Λ] [AddCommGroup V] [AddCommGroup V'] [Module ℚ V]
    [Module ℚ V'] (j : Λ →+ V) (hj : Function.Injective j)
    (hs : ∀ v, ∃ (m : ℕ) (u : Λ), m ≠ 0 ∧ m • v = j u) (f : Λ →+ V') :
    ∃ A : V →ₗ[ℚ] V', ∀ u, A (j u) = f u := by
  choose m u hm hu using hs
  let g : V → V' := fun v => ((m v : ℚ))⁻¹ • f (u v)
  have hg : ∀ v, m v • g v = f (u v) := by
    intro v
    have h0 : (m v : ℚ) ≠ 0 := by exact_mod_cast hm v
    rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, mul_inv_cancel₀ h0, one_smul]
  have key : ∀ (a : ℕ) (x : Λ) (v : V), a ≠ 0 → a • v = j x → a • g v = f x := by
    intro a x v ha hx
    have e : m v • x = a • u v := by
      apply hj
      rw [map_nsmul, map_nsmul, ← hx, ← hu v, smul_comm]
    apply nsmul_canc (hm v)
    rw [smul_comm, hg, ← map_nsmul, ← map_nsmul, e]
  have hadd : ∀ v₁ v₂, g (v₁ + v₂) = g v₁ + g v₂ := by
    intro v₁ v₂
    have h12 : m v₁ * m v₂ ≠ 0 := mul_ne_zero (hm _) (hm _)
    apply nsmul_canc h12
    rw [key (m v₁ * m v₂) (m v₂ • u v₁ + m v₁ • u v₂) (v₁ + v₂) h12 ?_]
    · rw [map_add (f := _), map_nsmul, map_nsmul, smul_add, ← hg v₁, ← hg v₂, smul_smul, smul_smul, mul_comm (m v₂),
        mul_comm (m v₁) (m v₂)]
    · rw [map_add (f := _), map_nsmul, map_nsmul, ← hu v₁, ← hu v₂, smul_add, smul_smul, smul_smul, mul_comm (m v₂)]
  refine ⟨(AddMonoidHom.mk' g hadd).toRatLinearMap, fun x => ?_⟩
  show g (j x) = f x
  have h1 : (1 : ℕ) • g (j x) = f x := key 1 x (j x) one_ne_zero (one_nsmul _)
  simpa using h1

theorem UpperTheory.Gal.W2.latForm_of :
    UpperTheory.Gal.W2.LatForm := by
  intro p _ D G L β β' D' D'' j j'' hP hP'' w m hm hw
  obtain ⟨hj, hjO, hjs, s₀, hs₀, hjF⟩ := hP
  obtain ⟨hj2, hjO2, hjs2, s₂, hs₂, hjF2⟩ := hP''
  obtain ⟨A, hA⟩ := ext_lin j'' hj2 hjs2 (j.comp w.toAddMonoidHom)
  replace hA : ∀ u, A (j'' u) = j (w u) := hA
  haveI := D.finLa
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hAinj : Function.Injective A := by
    refine (injective_iff_map_eq_zero A).2 fun v hv => ?_
    obtain ⟨a, u, ha, hu⟩ := hjs2 v
    have h1 : j (w u) = 0 := by rw [← hA, ← hu, map_nsmul, hv, smul_zero]
    have h2 : w u = 0 := hj (by rw [h1, map_zero])
    have h3 : u = 0 := by
      refine D''.nondeg u fun u' => ?_
      have := hw u u'
      rw [h2] at this
      simp only [map_zero, LinearMap.zero_apply] at this
      rcases mul_eq_zero.1 this.symm with h | h
      · exact absurd h hm.ne'
      · exact h
    apply nsmul_canc ha
    rw [hu, h3, map_zero, smul_zero]
  let Ae := LinearEquiv.ofInjectiveEndo A hAinj
  let B : Module.End ℚ (VQ D) := (Ae.symm : VQ D →ₗ[ℚ] VQ D)
  have hAB : A * B = 1 := LinearEquiv.ofInjectiveEndo_right_inv A hAinj
  have hBA : B * A = 1 := LinearEquiv.ofInjectiveEndo_left_inv A hAinj
  have hcomm : ∀ b, A * actQ D b = actQ D b * A := by
    intro b
    refine LinearMap.ext fun v => ?_
    obtain ⟨a, u, ha, hu⟩ := hjs2 v
    apply nsmul_canc ha
    show a • A (actQ D b v) = a • actQ D b (A v)
    calc a • A (actQ D b v) = A (actQ D b (a • v)) := by rw [map_nsmul, map_nsmul]
      _ = A (j'' (b • u)) := by rw [hu, hjO2]
      _ = j (w (b • u)) := hA _
      _ = j (b • w u) := by rw [map_smul]
      _ = actQ D b (j (w u)) := hjO _ _
      _ = actQ D b (A (a • v)) := by rw [hu, hA]
      _ = a • actQ D b (A v) := by rw [map_nsmul, map_nsmul]
  have hBcomm : ∀ b, B * actQ D b = actQ D b * B := by
    intro b
    calc B * actQ D b = B * actQ D b * (A * B) := by rw [hAB, _root_.mul_one]
      _ = B * (actQ D b * A) * B := by simp only [_root_.mul_assoc]
      _ = B * (A * actQ D b) * B := by rw [hcomm]
      _ = (B * A) * actQ D b * B := by simp only [_root_.mul_assoc]
      _ = actQ D b * B := by rw [hBA, _root_.one_mul]
  obtain ⟨x, hx⟩ := (L.rep_range A).2 hcomm
  obtain ⟨x', hx'⟩ := (L.rep_range B).2 hBcomm
  have hxx' : x * x' = 1 := L.rep_inj (by rw [map_mul, hx, hx', hAB, map_one])
  have hx'x : x' * x = 1 := L.rep_inj (by rw [map_mul, hx, hx', hBA, map_one])
  let y : G.Cˣ := ⟨x, x', hxx', hx'x⟩
  have hform : ∀ v v', s₀ * D.EF.baseChange ℚ (L.rep ((β⁻¹ : G.Cˣ) : G.C) (A v)) (A v') =
      (m : ℚ) * s₂ * D.EF.baseChange ℚ (L.rep ((β'⁻¹ : G.Cˣ) : G.C) v) v' := by
    intro v v'
    obtain ⟨a, u, ha, hu⟩ := hjs2 v
    obtain ⟨b, u', hb, hu'⟩ := hjs2 v'
    have e1 := hjF (w u) (w u')
    have e2 := hjF2 u u'
    have e3 : ((D'.EF (w u) (w u') : ℤ) : ℚ) = (m : ℚ) * (D''.EF u u' : ℤ) := by
      rw [hw u u']; push_cast; ring
    unfold formB at e1 e2
    rw [← hA, ← hA, ← hu, ← hu', map_nsmul, map_nsmul, map_nsmul] at e1
    rw [← hu, ← hu', map_nsmul] at e2
    simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul] at e1 e2
    have hab : (a : ℚ) * b ≠ 0 := mul_ne_zero (by exact_mod_cast ha) (by exact_mod_cast hb)
    apply mul_left_cancel₀ hab
    linear_combination -e1 + e3 + (m : ℚ) * e2
  have hnd : ∀ a : VQ D, (∀ v, D.EF.baseChange ℚ a v = 0) → a = 0 := by
    intro a ha
    obtain ⟨c, u, hc, hu⟩ := hjs (L.rep (β : G.C) a)
    have hinv : ∀ z : VQ D, L.rep ((β⁻¹ : G.Cˣ) : G.C) (L.rep (β : G.C) z) = z := by
      intro z
      rw [← Module.End.mul_apply, ← map_mul, Units.inv_mul, map_one, Module.End.one_apply]
    have hu0 : u = 0 := by
      refine D'.nondeg u fun u' => ?_
      have e := hjF u u'
      unfold formB at e
      rw [← hu, map_nsmul, hinv] at e
      simp only [map_nsmul, LinearMap.smul_apply, ha, smul_zero, mul_zero] at e
      exact_mod_cast e
    have h0 : c • L.rep (β : G.C) a = c • (0 : VQ D) := by rw [hu, hu0, map_zero, smul_zero]
    have := nsmul_canc hc h0
    rw [← hinv a, this, map_zero]
  set r : ℚ := (m : ℚ) * s₂ / s₀ with hr
  have hr0 : 0 < r := by
    have : (0 : ℚ) < m := by exact_mod_cast hm
    positivity
  have hs₀' : s₀ ≠ 0 := hs₀.ne'
  have hshsh : sh G (sh G x) = x := G.star_star x
  have hkey : sh G x * ((β⁻¹ : G.Cˣ) : G.C) * x = algebraMap ℚ G.C r * ((β'⁻¹ : G.Cˣ) : G.C) := by
    apply L.rep_inj
    refine LinearMap.ext fun v => ?_
    rw [← sub_eq_zero]
    refine hnd _ fun v' => ?_
    have e := hform v v'
    have e2 := L.adj (sh G x) (L.rep ((β⁻¹ : G.Cˣ) : G.C) (A v)) v'
    rw [hshsh, hx] at e2
    simp only [map_mul, Module.End.mul_apply, hx, AlgHom.commutes, Module.algebraMap_end_apply,
      map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [e2, hr]
    field_simp
    linear_combination e
  refine ⟨y, Units.mk0 r hr0.ne', hr0, ?_, fun u => ?_⟩
  · show x * (β' : G.C) * sh G x = algebraMap ℚ G.C r * (β : G.C)
    have h1 : x * (β' : G.C) * sh G x * (((β⁻¹ : G.Cˣ) : G.C) * x) = r • x := by
      calc x * (β' : G.C) * sh G x * (((β⁻¹ : G.Cˣ) : G.C) * x)
          = x * (β' : G.C) * (sh G x * ((β⁻¹ : G.Cˣ) : G.C) * x) := by simp only [_root_.mul_assoc]
        _ = r • (x * ((β' : G.C) * ((β'⁻¹ : G.Cˣ) : G.C))) := by
            rw [hkey, ← Algebra.smul_def, mul_smul_comm, _root_.mul_assoc]
        _ = r • x := by rw [Units.mul_inv, _root_.mul_one]
    calc x * (β' : G.C) * sh G x
        = x * (β' : G.C) * sh G x * (((β⁻¹ : G.Cˣ) : G.C) * (x * x') * (β : G.C)) := by
          rw [hxx', _root_.mul_one, Units.inv_mul, _root_.mul_one]
      _ = x * (β' : G.C) * sh G x * (((β⁻¹ : G.Cˣ) : G.C) * x) * (x' * (β : G.C)) := by
          simp only [_root_.mul_assoc]
      _ = r • (x * x' * (β : G.C)) := by rw [h1, smul_mul_assoc, _root_.mul_assoc]
      _ = algebraMap ℚ G.C r * (β : G.C) := by rw [hxx', _root_.one_mul, Algebra.smul_def]
  · show j (w u) = L.rep x (j'' u)
    rw [hx, hA]
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical

namespace UpperTheory.Gal.W2

private theorem formB_add_left {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (β : G.Cˣ)
    (a b c : VQ D) : formB L β (a + b) c = formB L β a c + formB L β b c := by
  simp only [formB, map_add (f := _), LinearMap.add_apply]

private theorem formB_nsmul_left {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (β : G.Cˣ)
    (n : ℕ) (a c : VQ D) : formB L β (n • a) c = n * formB L β a c := by
  simp only [formB, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]

private theorem formB_add_right {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (β : G.Cˣ)
    (a b c : VQ D) : formB L β a (b + c) = formB L β a b + formB L β a c := by
  simp only [formB, map_add (f := _)]

private theorem formB_nsmul_right {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (β : G.Cˣ)
    (n : ℕ) (a c : VQ D) : formB L β a (n • c) = n * formB L β a c := by
  simp only [formB, map_nsmul, nsmul_eq_mul]

private theorem formB_zsmul_right {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (β : G.Cˣ)
    (n : ℤ) (a c : VQ D) : formB L β a (n • c) = n * formB L β a c := by
  simp only [formB, map_zsmul, zsmul_eq_mul]

private theorem den_dvd_of_mul_eq_int (q : ℚ) (n : ℕ) (z : ℤ) (h : (n : ℚ) * q = z) : q.den ∣ n := by
  have h1 : (n : ℤ) * q.num = z * q.den := by
    have h2 : (q.num : ℚ) = q * q.den := (Rat.mul_den_eq_num q).symm
    have h3 : (((n : ℤ) * q.num : ℤ) : ℚ) = ((z * q.den : ℤ) : ℚ) := by
      push_cast
      rw [h2, ← _root_.mul_assoc, h]
    exact_mod_cast h3
  have h3 : (q.den : ℤ) ∣ n * q.num := ⟨z, by rw [h1]; ring⟩
  have h4 : IsCoprime (q.den : ℤ) q.num := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
    exact q.reduced
  exact Int.natCast_dvd_natCast.1 (h4.dvd_of_dvd_mul_right h3)

theorem placeLoc_of : PlaceLoc := by
  intro p _ D G L β D' j hP hH
  obtain ⟨-, hact, hspan, s0, hs0, hform⟩ := hP
  obtain ⟨E₁, hE, e, he, hperf⟩ := hH
  have hE1 : ∀ u u', (E₁ u u' : ℚ) = (s0 / 2) * formB L β (j u) (j u') := by
    intro u u'
    have h := hform u u'
    rw [hE] at h
    simp only [LinearMap.smul_apply, smul_eq_mul] at h
    push_cast at h
    linarith
  obtain ⟨S, hS⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ D'.La).FG)
  have hcl0 : AddSubgroup.closure (S : Set D'.La) = ⊤ := by
    rw [eq_top_iff]
    intro u _
    have hu : u ∈ Submodule.span ℤ (S : Set D'.La) := hS ▸ Submodule.mem_top
    induction hu using Submodule.span_induction with
    | mem x hx => exact AddSubgroup.subset_closure hx
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem (hx trivial) (hy trivial)
    | smul a x _ hx => exact zsmul_mem (hx trivial) a
  have hcl : AddSubgroup.closure ((S.image j : Finset (VQ D)) : Set (VQ D)) = j.range := by
    rw [Finset.coe_image, ← AddMonoidHom.map_closure, hcl0, AddMonoidHom.range_eq_map]
  let M : AddSubgroup (VQ D) :=
    { carrier := {w | ∃ (m : ℕ) (u : D'.La), m.Coprime p ∧ m • w = j u}
      add_mem' := by
        rintro a b ⟨m, u, hm, hu⟩ ⟨m', u', hm', hu'⟩
        refine ⟨m * m', m' • u + m • u', hm.mul_left hm', ?_⟩
        rw [map_add (f := _), map_nsmul, map_nsmul, ← hu, ← hu', smul_add, smul_smul, smul_smul, mul_comm m' m]
      zero_mem' := ⟨1, 0, Nat.coprime_one_left p, by simp⟩
      neg_mem' := by
        rintro a ⟨m, u, hm, hu⟩
        exact ⟨m, -u, hm, by rw [map_neg, ← hu, smul_neg]⟩ }
  have hM : ∀ w, w ∈ M ↔ ∃ (m : ℕ) (u : D'.La), m.Coprime p ∧ m • w = j u := fun w => Iff.rfl
  refine ⟨M, ⟨?_, S.image j, ?_, ?_⟩, ⟨s0 / 2, by positivity, ?_⟩, fun w => (hM w).symm⟩
  · rintro c w ⟨m, u, hm, h⟩
    exact ⟨m, c • u, hm, by rw [hact, ← h, map_nsmul]⟩
  · rw [eq_top_iff]
    intro w _
    obtain ⟨m, u, hm, h⟩ := hspan w
    have hu : j u ∈ AddSubgroup.closure ((S.image j : Finset (VQ D)) : Set (VQ D)) := hcl ▸ ⟨u, rfl⟩
    have hu' : j u ∈ Submodule.span ℚ ((S.image j : Finset (VQ D)) : Set (VQ D)) :=
      (AddSubgroup.closure_le (Submodule.span ℚ ((S.image j : Finset (VQ D)) : Set (VQ D))).toAddSubgroup).2
        Submodule.subset_span hu
    have hw : w = (m : ℚ)⁻¹ • j u := by
      rw [← h, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hm), one_smul]
    rw [hw]
    exact Submodule.smul_mem _ _ hu'
  · intro w
    rw [hcl]
    constructor
    · rintro ⟨m, u, hm, h⟩
      exact ⟨m, hm, ⟨u, h.symm⟩⟩
    · rintro ⟨m, hm, u, h⟩
      exact ⟨m, u, hm, h.symm⟩
  · intro w
    constructor
    · rintro ⟨m, a, hm, ha⟩ u ⟨m', b, hm', hb⟩
      have key : ((m * m' : ℕ) : ℚ) * (s0 / 2 * formB L β w u) = (E₁ a b : ℤ) := by
        rw [hE1, ← ha, ← hb, formB_nsmul_left, formB_nsmul_right]
        push_cast
        ring
      exact Nat.Coprime.coprime_dvd_left (den_dvd_of_mul_eq_int _ _ _ key) (hm.mul_left hm')
    · intro h
      have hden : ∀ x : D'.La, (s0 / 2 * formB L β w (j x)).den.Coprime p := fun x =>
        h (j x) ⟨1, x, Nat.coprime_one_left p, one_smul _ _⟩
      let m : ℕ := ∏ x ∈ S, (s0 / 2 * formB L β w (j x)).den
      have hm : m.Coprime p := Nat.Coprime.prod_left fun x _ => hden x
      have hint : ∀ u : D'.La, ∃ z : ℤ, (z : ℚ) = m * (s0 / 2 * formB L β w (j u)) := by
        intro u
        have hu : u ∈ Submodule.span ℤ (S : Set D'.La) := hS ▸ Submodule.mem_top
        induction hu using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem (fun x => (s0 / 2 * formB L β w (j x)).den) hx
          refine ⟨r * (s0 / 2 * formB L β w (j x)).num, ?_⟩
          have h2 := Rat.mul_den_eq_num (s0 / 2 * formB L β w (j x))
          change (((r : ℤ) * (s0 / 2 * formB L β w (j x)).num : ℤ) : ℚ) = ((∏ x ∈ S, (s0 / 2 * formB L β w (j x)).den : ℕ) : ℚ) * _
          rw [hr]
          push_cast
          rw [← h2]
          ring
        | zero =>
          refine ⟨0, ?_⟩
          have h0 : formB L β w (j 0) = 0 := by
            have := formB_nsmul_right L β 0 w (0 : VQ D)
            simpa using this
          rw [h0]
          simp
        | add x y _ _ hx hy =>
          obtain ⟨a, ha⟩ := hx
          obtain ⟨b, hb⟩ := hy
          refine ⟨a + b, ?_⟩
          rw [map_add (f := _), formB_add_right]
          push_cast
          rw [ha, hb]
          ring
        | smul a x _ hx =>
          obtain ⟨b, hb⟩ := hx
          refine ⟨a * b, ?_⟩
          rw [map_zsmul, formB_zsmul_right]
          push_cast
          rw [hb]
          ring
      choose c hc using hint
      let f : D'.La →ₗ[ℤ] ℤ := AddMonoidHom.toIntLinearMap (AddMonoidHom.mk' c (fun a b => by
        have h3 : ((c (a + b) : ℤ) : ℚ) = ((c a + c b : ℤ) : ℚ) := by
          push_cast
          rw [hc, hc, hc, map_add (f := _), formB_add_right]
          ring
        exact_mod_cast h3))
      obtain ⟨x, hx⟩ := hperf f
      obtain ⟨z, hz⟩ : ∃ z, z + j x = (e * m) • w := ⟨(e * m) • w - j x, sub_add_cancel _ _⟩
      have hs : s0 / 2 ≠ 0 := by positivity
      have hzero : ∀ u, formB L β z (j u) = 0 := by
        intro u
        have h1 : E₁ x u = e • c u := by
          have := LinearMap.congr_fun hx u
          simpa [f] using this
        have h2 : (E₁ x u : ℚ) = e * (m * (s0 / 2 * formB L β w (j u))) := by
          rw [h1, ← hc]
          push_cast
          simp
        rw [hE1] at h2
        have h3 : formB L β (z + j x) (j u) = ((e * m : ℕ) : ℚ) * formB L β w (j u) := by
          rw [hz, formB_nsmul_left]
        rw [formB_add_left] at h3
        have h4 : s0 / 2 * formB L β z (j u) = 0 := by
          have h5 : s0 / 2 * (formB L β z (j u) + formB L β (j x) (j u)) =
              s0 / 2 * (((e * m : ℕ) : ℚ) * formB L β w (j u)) := by rw [h3]
          push_cast at h5
          linarith
        exact (mul_eq_zero.1 h4).resolve_left hs
      obtain ⟨k, u₁, hk, hu₁⟩ := hspan z
      have hEF : ∀ u, D'.EF u₁ u = 0 := by
        intro u
        have h1 := hform u₁ u
        rw [← hu₁, formB_nsmul_left, hzero u] at h1
        simpa using h1
      have hu₀ : u₁ = 0 := D'.nondeg _ hEF
      have hz0 : z = 0 := by
        rw [hu₀, map_zero, ← Nat.cast_smul_eq_nsmul ℚ] at hu₁
        exact (smul_eq_zero.1 hu₁).resolve_left (by exact_mod_cast hk)
      refine ⟨e * m, x, he.mul_left hm, ?_⟩
      rw [← hz, hz0, zero_add]

end UpperTheory.Gal.W2
end
end
