module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle008
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle010
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq

@[expose] public section

section

noncomputable section

open IsDedekindDomain NumberField ValuativeRel

namespace Formalism.L2.SG.Pf.ProdEApprox

section Close2

open Formalism.MainNotions.S.Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  {p : HeightOneSpectrum (𝓞 F)} {L : LocAt F E sig p} {n : ℕ}

theorem entIn_sandwich {P Q X : Matrix (Fin n) (Fin n) L.Ep} {sP sQ c : L.Fp}
    (hP : ∀ i j, algebraMap L.Fp L.Ep sP * P i j ∈ L.O) (hQ : ∀ i j, algebraMap L.Fp L.Ep sQ * Q i j ∈ L.O)
    (hX : EntIn (latS L (sP * (sQ * c))) X) : EntIn (latS L c) (P * X * Q) :=
  entIn_mul_right hQ (entIn_mul_left hP hX)

theorem smul_sandwich (e : L.Ep) (P X Q : Matrix (Fin n) (Fin n) L.Ep) : P * (e • X) * Q = e • (P * X * Q) := by
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem close (ex ey : L.Ep) (hex : ex ∈ L.O) (hey : ey ∈ L.O) (hxx : ex * ex = ex) (hyy : ey * ey = ey)
    (hsum : ex + ey = 1) (hxy : ex * ey = 0)
    (N Ni Δ Δi Γ Γi : Matrix (Fin n) (Fin n) L.Ep) (hN : N * Ni = 1) (hN' : Ni * N = 1) (hΔ : Δ * Δi = 1)
    (hΓ : Γ * Γi = 1) (hΓ' : Γi * Γ = 1) (h1 h2 : GL (Fin n) L.Ep)
    (hh : (h1 : Matrix (Fin n) (Fin n) L.Ep) * N * (h2 : Matrix (Fin n) (Fin n) L.Ep) = N) (c : L.Fp) (hc0 : c ≠ 0) (hc : c ∈ 𝒪[L.Fp]) :
    ∃ c' : L.Fp, c' ≠ 0 ∧ c' ∈ 𝒪[L.Fp] ∧ ∀ (l ρ : GL (Fin n) L.Ep) (G : Matrix (Fin n) (Fin n) L.Ep),
      (∀ i j, i ≤ j → (((h1⁻¹ * l : GL (Fin n) L.Ep) : Matrix (Fin n) (Fin n) L.Ep) - 1) i j = 0) →
      (∀ i j, j ≤ i → (((ρ * h2⁻¹ : GL (Fin n) L.Ep) : Matrix (Fin n) (Fin n) L.Ep) - 1) i j = 0) →
      (l : Matrix (Fin n) (Fin n) L.Ep) * N * (ρ : Matrix (Fin n) (Fin n) L.Ep) = N →
      ex • (l : Matrix (Fin n) (Fin n) L.Ep) = ex • (Δ * G * Δi) →
      ey • (ρ : Matrix (Fin n) (Fin n) L.Ep) = ey • (Γi * G.transpose * Γ) →
      EntIn (latS L c') (G - (ex • (Δi * (h1 : Matrix (Fin n) (Fin n) L.Ep) * Δ) +
        ey • (Γ * (h2 : Matrix (Fin n) (Fin n) L.Ep) * Γi).transpose)) →
      EntIn (latS L c) (((h1⁻¹ * l : GL (Fin n) L.Ep) : Matrix (Fin n) (Fin n) L.Ep) - 1) ∧
        EntIn (latS L c) (((ρ * h2⁻¹ : GL (Fin n) L.Ep) : Matrix (Fin n) (Fin n) L.Ep) - 1) := by
  obtain ⟨sN, hsN0, hsNO, hsN⟩ := bounded_mat (L := L) N
  obtain ⟨sNi, hsNi0, hsNiO, hsNi⟩ := bounded_mat (L := L) Ni
  obtain ⟨sA, hsA0, hsAO, hsA⟩ := bounded_mat (L := L) (((h1⁻¹ : GL (Fin n) L.Ep) : Matrix (Fin n) (Fin n) L.Ep) * Δ)
  obtain ⟨sB, hsB0, hsBO, hsB⟩ := bounded_mat (L := L) Δi
  obtain ⟨sC, hsC0, hsCO, hsC⟩ := bounded_mat (L := L) Γi
  obtain ⟨sD, hsD0, hsDO, hsD⟩ := bounded_mat (L := L) (Γ * ((h2⁻¹ : GL (Fin n) L.Ep) : Matrix (Fin n) (Fin n) L.Ep))
  set c1 := sNi * (sN * c) with hc1
  have hc1O : c1 ∈ 𝒪[L.Fp] := Subring.mul_mem _ hsNiO (Subring.mul_mem _ hsNO hc)
  have hc10 : c1 ≠ 0 := mul_ne_zero hsNi0 (mul_ne_zero hsN0 hc0)
  refine ⟨sA * (sB * (sC * (sD * c1))), mul_ne_zero hsA0 (mul_ne_zero hsB0 (mul_ne_zero hsC0 (mul_ne_zero hsD0 hc10))),
    Subring.mul_mem _ hsAO (Subring.mul_mem _ hsBO (Subring.mul_mem _ hsCO (Subring.mul_mem _ hsDO hc1O))), ?_⟩
  intro l ρ G hk1 hk2 hlN hlx hρy hG
  set h1i := ((h1⁻¹ : GL (Fin n) L.Ep) : Matrix (Fin n) (Fin n) L.Ep) with hh1i
  set h2i := ((h2⁻¹ : GL (Fin n) L.Ep) : Matrix (Fin n) (Fin n) L.Ep) with hh2i
  set τ := ex • (Δi * (h1 : Matrix (Fin n) (Fin n) L.Ep) * Δ) + ey • (Γ * (h2 : Matrix (Fin n) (Fin n) L.Ep) * Γi).transpose
    with hτ
  set D := G - τ with hD
  have h11 : h1i * h1 = 1 := by rw [hh1i, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h22 : (h2 : Matrix (Fin n) (Fin n) L.Ep) * h2i = 1 := by rw [hh2i, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hk1v : ((h1⁻¹ * l : GL (Fin n) L.Ep) : Matrix (Fin n) (Fin n) L.Ep) = h1i * l := Units.val_mul _ _
  have hk2v : ((ρ * h2⁻¹ : GL (Fin n) L.Ep) : Matrix (Fin n) (Fin n) L.Ep) = ρ * h2i := Units.val_mul _ _
  have hτx : ex • τ = ex • (Δi * (h1 : Matrix (Fin n) (Fin n) L.Ep) * Δ) := by
    rw [hτ, smul_add, smul_smul, smul_smul, hxx, hxy, zero_smul, add_zero]
  have hτy : ey • τ.transpose = ey • (Γ * (h2 : Matrix (Fin n) (Fin n) L.Ep) * Γi) := by
    rw [hτ, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul, Matrix.transpose_transpose, smul_add,
      smul_smul, smul_smul, hyy, mul_comm ey ex, hxy, zero_smul, zero_add]

  have E1 : ex • (h1i * l - 1) = (h1i * Δ) * (ex • D) * Δi := by
    have a1 : (h1i * Δ) * (ex • D) * Δi = h1i * (Δ * (ex • G) * Δi) - h1i * (Δ * (ex • τ) * Δi) := by
      rw [hD, smul_sub, Matrix.mul_sub, Matrix.sub_mul]
      simp only [Matrix.mul_assoc]
    have a2 : Δ * (ex • G) * Δi = ex • (l : Matrix (Fin n) (Fin n) L.Ep) := by rw [smul_sandwich, hlx]
    have a3 : Δ * (ex • τ) * Δi = ex • (h1 : Matrix (Fin n) (Fin n) L.Ep) := by
      rw [hτx, smul_sandwich]
      congr 1
      rw [show Δ * (Δi * (h1 : Matrix (Fin n) (Fin n) L.Ep) * Δ) * Δi = (Δ * Δi) * h1 * (Δ * Δi) by
        simp only [Matrix.mul_assoc], hΔ, Matrix.one_mul, Matrix.mul_one]
    rw [a1, a2, a3, Matrix.mul_smul, Matrix.mul_smul, h11, smul_sub]
  have E2 : ey • (ρ * h2i - 1) = Γi * (ey • D).transpose * (Γ * h2i) := by
    have b1 : Γi * (ey • D).transpose * (Γ * h2i) =
        (Γi * (ey • G.transpose) * Γ) * h2i - (Γi * (ey • τ.transpose) * Γ) * h2i := by
      rw [hD, smul_sub, Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_smul, Matrix.mul_sub,
        Matrix.sub_mul]
      simp only [Matrix.mul_assoc]
    have b2 : Γi * (ey • G.transpose) * Γ = ey • (ρ : Matrix (Fin n) (Fin n) L.Ep) := by rw [smul_sandwich, hρy]
    have b3 : Γi * (ey • τ.transpose) * Γ = ey • (h2 : Matrix (Fin n) (Fin n) L.Ep) := by
      rw [hτy, smul_sandwich]
      congr 1
      rw [show Γi * (Γ * (h2 : Matrix (Fin n) (Fin n) L.Ep) * Γi) * Γ = (Γi * Γ) * h2 * (Γi * Γ) by
        simp only [Matrix.mul_assoc], hΓ', Matrix.one_mul, Matrix.mul_one]
    rw [b1, b2, b3, Matrix.smul_mul, Matrix.smul_mul, h22, smul_sub]

  have hexJ : ∀ {c'' : L.Fp}, ∀ x ∈ latS L c'', ex * x ∈ latS L c'' := fun x hx => O_mul_latS hex hx
  have heyJ : ∀ {c'' : L.Fp}, ∀ x ∈ latS L c'', ey * x ∈ latS L c'' := fun x hx => O_mul_latS hey hx
  have hD1 : EntIn (latS L (sA * (sB * c1))) (ex • D) :=
    entIn_smul ex (fun x hx => hexJ x hx)
      (entIn_latS_of_eq (t := sC * sD) (by ring) (Subring.mul_mem _ hsCO hsDO) hG)
  have X1 : EntIn (latS L c1) (ex • (h1i * (l : Matrix (Fin n) (Fin n) L.Ep) - 1)) := by rw [E1]; exact entIn_sandwich hsA hsB hD1
  have hD2 : EntIn (latS L (sC * (sD * c1))) (ey • D).transpose :=
    entIn_transpose (entIn_smul ey (fun x hx => heyJ x hx)
      (entIn_latS_of_eq (t := sA * sB) (by ring) (Subring.mul_mem _ hsAO hsBO) hG))
  have Y2 : EntIn (latS L c1) (ey • ((ρ : Matrix (Fin n) (Fin n) L.Ep) * h2i - 1)) := by rw [E2]; exact entIn_sandwich hsC hsD hD2

  set k1 : GL (Fin n) L.Ep := h1⁻¹ * l with hk1d
  set k2 : GL (Fin n) L.Ep := ρ * h2⁻¹ with hk2d
  set k1i := ((k1⁻¹ : GL (Fin n) L.Ep) : Matrix (Fin n) (Fin n) L.Ep) with hk1id
  set k2i := ((k2⁻¹ : GL (Fin n) L.Ep) : Matrix (Fin n) (Fin n) L.Ep) with hk2id
  have R : (k1 : Matrix (Fin n) (Fin n) L.Ep) * N * (k2 : Matrix (Fin n) (Fin n) L.Ep) = N := by
    rw [hk1v, hk2v]
    calc h1i * (l : Matrix (Fin n) (Fin n) L.Ep) * N * ((ρ : Matrix (Fin n) (Fin n) L.Ep) * h2i) =
          h1i * ((l : Matrix (Fin n) (Fin n) L.Ep) * N * (ρ : Matrix (Fin n) (Fin n) L.Ep)) * h2i := by
          simp only [Matrix.mul_assoc]
      _ = h1i * ((h1 : Matrix (Fin n) (Fin n) L.Ep) * N * (h2 : Matrix (Fin n) (Fin n) L.Ep)) * h2i := by
          rw [hlN, hh]
      _ = (h1i * h1) * N * ((h2 : Matrix (Fin n) (Fin n) L.Ep) * h2i) := by simp only [Matrix.mul_assoc]
      _ = N := by rw [h11, h22, Matrix.one_mul, Matrix.mul_one]
  have hk1i : k1i * (k1 : Matrix (Fin n) (Fin n) L.Ep) = 1 := by
    rw [hk1id, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hk2i : (k2 : Matrix (Fin n) (Fin n) L.Ep) * k2i = 1 := by
    rw [hk2id, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have S2 : (k2 : Matrix (Fin n) (Fin n) L.Ep) = Ni * k1i * N := by
    calc (k2 : Matrix (Fin n) (Fin n) L.Ep) = Ni * (k1i * ((k1 : Matrix (Fin n) (Fin n) L.Ep) * N * k2)) := by
          rw [show k1i * ((k1 : Matrix (Fin n) (Fin n) L.Ep) * N * k2) = (k1i * k1) * N * k2 by
            simp only [Matrix.mul_assoc], hk1i, Matrix.one_mul, ← Matrix.mul_assoc, hN', Matrix.one_mul]
      _ = Ni * k1i * N := by rw [R, Matrix.mul_assoc]
  have S1 : (k1 : Matrix (Fin n) (Fin n) L.Ep) = N * k2i * Ni := by
    calc (k1 : Matrix (Fin n) (Fin n) L.Ep) = (((k1 : Matrix (Fin n) (Fin n) L.Ep) * N * k2) * k2i) * Ni := by
          rw [show ((k1 : Matrix (Fin n) (Fin n) L.Ep) * N * k2) * k2i = k1 * N * (k2 * k2i) by
            simp only [Matrix.mul_assoc], hk2i, Matrix.mul_one, Matrix.mul_assoc, hN, Matrix.mul_one]
      _ = N * k2i * Ni := by rw [R]
  have F1 : ex • ((k2 : Matrix (Fin n) (Fin n) L.Ep) - 1) = Ni * (ex • (k1i - 1)) * N := by
    rw [smul_sandwich, S2, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hN']
  have F2 : ey • ((k1 : Matrix (Fin n) (Fin n) L.Ep) - 1) = N * (ey • (k2i - 1)) * Ni := by
    rw [smul_sandwich, S1, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hN]

  have hJ : ∀ x ∈ latS L c1, ∀ y ∈ latS L c1, x * y ∈ latS L c1 := fun x hx y hy => latS_mul_self hc1O hx hy
  have I1 : EntIn (latS L c1) (ex • (k1i - 1)) := by
    refine proj_inv (fun i => i.val) (fun i => i.isLt) hJ ex hxx k1 (fun i j h => hk1 i j (Fin.le_def.2 h)) ?_
    rw [hk1v]; exact X1
  have I2 : EntIn (latS L c1) (ey • (k2i - 1)) := by
    refine proj_inv (fun i => n - 1 - i.val) (fun i => by have := i.isLt; omega) hJ ey hyy k2
      (fun i j h => hk2 i j (Fin.le_def.2 (by have := i.isLt; have := j.isLt; omega))) ?_
    rw [hk2v]; exact Y2
  have G1 : EntIn (latS L c) (ex • ((k2 : Matrix (Fin n) (Fin n) L.Ep) - 1)) := by
    rw [F1]; exact entIn_sandwich hsNi hsN I1
  have G2 : EntIn (latS L c) (ey • ((k1 : Matrix (Fin n) (Fin n) L.Ep) - 1)) := by
    rw [F2]
    exact entIn_sandwich hsN hsNi (entIn_latS_of_eq (t := 1) (by rw [hc1]; ring) (Subring.one_mem _) I2)
  have hsplit : ∀ X : Matrix (Fin n) (Fin n) L.Ep, X = ex • X + ey • X := fun X => by
    rw [← add_smul, hsum, one_smul]
  refine ⟨?_, ?_⟩
  · show EntIn (latS L c) ((k1 : Matrix (Fin n) (Fin n) L.Ep) - 1)
    rw [hsplit ((k1 : Matrix (Fin n) (Fin n) L.Ep) - 1)]
    refine entIn_add ?_ G2
    rw [hk1v]
    exact entIn_latS_of_eq (t := sNi * sN) (by rw [hc1]; ring) (Subring.mul_mem _ hsNiO hsNO) X1
  · show EntIn (latS L c) ((k2 : Matrix (Fin n) (Fin n) L.Ep) - 1)
    rw [hsplit ((k2 : Matrix (Fin n) (Fin n) L.Ep) - 1)]
    refine entIn_add G1 ?_
    rw [hk2v]
    exact entIn_latS_of_eq (t := sNi * sN) (by rw [hc1]; ring) (Subring.mul_mem _ hsNiO hsNO) Y2

end Close2

end Formalism.L2.SG.Pf.ProdEApprox
end
end

section

noncomputable section

open MeasureTheory

namespace Formalism.L2.SG.NGCut.SplitEmbedding

theorem box_fundX {ι P : Type} [Fintype P] [DecidableEq P] (h : P → ℕ) (BX : P → (P → ℂ) → (P → ℂ) → ℂ)
    (hBd : ∀ p (x x' y y' : P → ℂ), (∀ q, h q < h p → x q = x' q ∧ y q = y' q) → BX p x y = BX p x' y')
    (τ : P → (ι → P → ℂ) → (ι → ℂ))
    (hτ : ∀ p (x x' : ι → P → ℂ), (∀ q, h q < h p → ∀ v, x v q = x' v q) → τ p x = τ p x')
    (A : P → AddSubgroup (ι → ℂ)) (F : P → Set (ι → ℂ)) (hFd : ∀ p (v : ι → ℂ), ∃! a : A p, (a : ι → ℂ) + v ∈ F p)
    (x : ι → P → ℂ) :
    ∃! γ : ι → P → ℂ, (∀ p, (fun v => γ v p) - τ p γ ∈ A p) ∧
      lawX BX γ x ∈ {y : ι → P → ℂ | ∀ p, (fun v => y v p) ∈ F p} := by
  classical
  let w : P → (ι → P → ℂ) → (ι → ℂ) := fun p γ => τ p γ + fun v => x v p + BX p (γ v) (x v)
  let c : P → (ι → P → ℂ) → (ι → ℂ) := fun p γ =>
    ((hFd p (w p γ)).exists.choose : ι → ℂ) + τ p γ
  have hloc : ∀ p (γ γ' : ι → P → ℂ), (∀ q, h q < h p → ∀ v, γ v q = γ' v q) → c p γ = c p γ' := by
    intro p γ γ' hg
    have h1 : τ p γ = τ p γ' := hτ p γ γ' hg
    have h2 : w p γ = w p γ' := by
      show (τ p γ + fun v => x v p + BX p (γ v) (x v)) = τ p γ' + fun v => x v p + BX p (γ' v) (x v)
      rw [h1]
      congr 1
      funext v
      rw [hBd p (γ v) (γ' v) (x v) (x v) (fun q hq => ⟨hg q hq v, rfl⟩)]
    have hch : ∀ u u' : ι → ℂ, u = u' →
        ((hFd p u).exists.choose : ι → ℂ) = ((hFd p u').exists.choose : ι → ℂ) := by
      rintro u _ rfl
      rfl
    show ((hFd p (w p γ)).exists.choose : ι → ℂ) + τ p γ = ((hFd p (w p γ')).exists.choose : ι → ℂ) + τ p γ'
    rw [h1, hch _ _ h2]
  have key : ∀ p (γ : ι → P → ℂ), ((fun v => γ v p) - τ p γ ∈ A p ∧ (fun v => lawX BX γ x v p) ∈ F p) ↔
      (fun v => γ v p) = c p γ := by
    intro p γ
    obtain ⟨a, ha, huniq⟩ := hFd p (w p γ)
    have hc : c p γ = (a : ι → ℂ) + τ p γ := by
      show ((hFd p (w p γ)).exists.choose : ι → ℂ) + τ p γ = (a : ι → ℂ) + τ p γ
      rw [huniq _ (hFd p (w p γ)).exists.choose_spec]
    have hlaw : (fun v => lawX BX γ x v p) = ((fun v => γ v p) - τ p γ) + w p γ := by
      funext v
      simp only [lawX, w, Pi.add_apply, Pi.sub_apply]
      ring
    rw [hc, hlaw]
    constructor
    · rintro ⟨hA, hF⟩
      have e := congrArg Subtype.val (huniq ⟨_, hA⟩ hF)
      simp only at e
      rw [← e]
      abel
    · intro hg
      rw [hg, add_sub_cancel_right]
      exact ⟨a.2, ha⟩
  let Φ : (ι → P → ℂ) → (ι → P → ℂ) := fun γ v p => c p γ v
  have hit : ∀ k (γ γ' : ι → P → ℂ), ∀ p, h p < k → ∀ v, (Φ^[k] γ) v p = (Φ^[k] γ') v p := by
    intro k
    induction k with
    | zero => intro γ γ' p hp; exact absurd hp (Nat.not_lt_zero _)
    | succ k ih =>
      intro γ γ' p hp v
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      show c p (Φ^[k] γ) v = c p (Φ^[k] γ') v
      rw [hloc p _ _ (fun q hq v => ih γ γ' q (by omega) v)]
  have hN : ∀ p, h p < Finset.univ.sup h + 1 := fun p =>
    Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ p))
  have hcond : ∀ γ : ι → P → ℂ, ((∀ p, (fun v => γ v p) - τ p γ ∈ A p) ∧
      lawX BX γ x ∈ {y : ι → P → ℂ | ∀ p, (fun v => y v p) ∈ F p}) ↔ Φ γ = γ := by
    intro γ
    rw [Set.mem_setOf_eq, ← forall_and, forall_congr' (fun p => key p γ)]
    constructor
    · intro H
      funext v p
      exact (congrFun (H p) v).symm
    · intro H p
      funext v
      exact (congrFun (congrFun H v) p).symm
  refine ⟨Φ^[Finset.univ.sup h + 1] 0, (hcond _).2 ?_, fun γ hγ => ?_⟩
  · rw [← Function.iterate_succ_apply' Φ _ 0, Function.iterate_succ_apply]
    funext v p
    exact hit _ (Φ 0) 0 p (hN p) v
  · have e1 : Φ^[Finset.univ.sup h + 1] γ = γ := Function.iterate_fixed ((hcond γ).1 hγ) _
    funext v p
    calc γ v p = (Φ^[Finset.univ.sup h + 1] γ) v p := by rw [e1]
      _ = _ := hit _ γ 0 p (hN p) v

end Formalism.L2.SG.NGCut.SplitEmbedding
end
end
