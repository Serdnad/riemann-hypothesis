module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
public import Development.AbelianVarietyTheory.Definitions.Divisors.CechDeRhamCoefMapOneFormsRestrictAlongFunctor
public import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle261
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration

@[expose] public section

section

open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology
open Filter

namespace GlobalTheory.QSA

theorem exists_nrm_one_re_sq_ne_one : ∀ (K : Type) [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K] [T2Space K], (2 : K) ≠ 0 → (𝓝[≠] (0 : K)).NeBot → ∀ a b : K, a ≠ 0 → ∀ g : ℍ[K, a, b], nrm g = 1 → ∀ W : Set ℍ[K, a, b], W ∈ 𝓝 g → ∃ g' : ℍ[K, a, b], nrm g' = 1 ∧ g'.re ^ 2 ≠ 1 ∧ W ∈ 𝓝 g' := by
  intro K _ _ _ _ h2 hne a b ha g hg W hW
  by_cases hre : g.re ^ 2 = 1
  swap
  · exact ⟨g, hg, hre, hW⟩
  have hs0 : g.re ≠ 0 := by
    intro h
    rw [h] at hre
    simp at hre
  let X0 : K → K := fun τ => (1 + a * τ ^ 2) / (1 - a * τ ^ 2)
  let X1 : K → K := fun τ => 2 * τ / (1 - a * τ ^ 2)
  let x : K → ℍ[K, a, b] := fun τ => ⟨X0 τ, X1 τ, 0, 0⟩
  have hD : Tendsto (fun τ : K => 1 - a * τ ^ 2) (𝓝 0) (𝓝 1) := by
    have : Continuous (fun τ : K => 1 - a * τ ^ 2) := by fun_prop
    simpa using this.tendsto 0
  have hx0 : Tendsto X0 (𝓝 0) (𝓝 1) := by
    have h1 : Continuous (fun τ : K => 1 + a * τ ^ 2) := by fun_prop
    have := (h1.tendsto 0).div hD one_ne_zero
    simpa [Pi.div_def] using this
  have hx1 : Tendsto X1 (𝓝 0) (𝓝 0) := by
    have h1 : Continuous (fun τ : K => 2 * τ) := by fun_prop
    have := (h1.tendsto 0).div hD one_ne_zero
    simpa [Pi.div_def] using this
  have key : ∀ c d : K, Tendsto (fun τ => c * X0 τ + d * X1 τ) (𝓝 0) (𝓝 c) := by
    intro c d
    simpa using (hx0.const_mul c).add (hx1.const_mul d)
  have hf : Tendsto (fun τ => g * x τ) (𝓝 0) (𝓝 g) := by
    rw [(Topology.IsInducing.induced coords).tendsto_nhds_iff, tendsto_pi_nhds]
    intro i
    fin_cases i
    · refine (key g.re (a * g.imI)).congr fun τ => ?_
      simp [coords, x]
    · refine (key g.imI g.re).congr fun τ => ?_
      simp [coords, x, add_comm]
    · refine (key g.imJ (-(a * g.imK))).congr fun τ => ?_
      simp [coords, x, sub_eq_add_neg]
    · refine (key g.imK (-g.imJ)).congr fun τ => ?_
      simp [coords, x, add_comm]
  have e1 : ∀ᶠ τ in 𝓝[≠] (0 : K), τ ≠ 0 := self_mem_nhdsWithin
  have e2 : ∀ᶠ τ in 𝓝[≠] (0 : K), 1 - a * τ ^ 2 ≠ 0 :=
    (hD.eventually_ne one_ne_zero).filter_mono nhdsWithin_le_nhds
  have e3 : ∀ᶠ τ in 𝓝[≠] (0 : K), g.re + a * τ * g.imI ≠ 0 := by
    have h1 : Continuous (fun τ : K => g.re + a * τ * g.imI) := by fun_prop
    exact ((h1.tendsto 0).eventually_ne (by simpa using hs0)).filter_mono nhdsWithin_le_nhds
  have e4 : ∀ᶠ τ in 𝓝[≠] (0 : K), g.re * τ + g.imI ≠ 0 := by
    by_cases hI : g.imI = 0
    · filter_upwards [e1] with τ hτ
      simpa [hI] using ⟨hs0, hτ⟩
    · have h1 : Continuous (fun τ : K => g.re * τ + g.imI) := by fun_prop
      exact ((h1.tendsto 0).eventually_ne (by simpa using hI)).filter_mono nhdsWithin_le_nhds
  have e5 : ∀ᶠ τ in 𝓝[≠] (0 : K), g * x τ ∈ interior W :=
    (hf.eventually (interior_mem_nhds.2 hW)).filter_mono nhdsWithin_le_nhds
  obtain ⟨τ, h1, h2', h3, h4, h5⟩ := (e1.and (e2.and (e3.and (e4.and e5)))).exists
  refine ⟨g * x τ, ?_, ?_, mem_interior_iff_mem_nhds.1 h5⟩
  · rw [nrm_mul, hg, one_mul]
    simp only [nrm, x, X0, X1]
    field_simp
    ring
  · have hr : (g * x τ).re = g.re * X0 τ + a * g.imI * X1 τ := by simp [x]
    rw [hr]
    intro h
    have hm : g.re * X0 τ + a * g.imI * X1 τ - g.re
        = 2 * a * τ * (g.re * τ + g.imI) / (1 - a * τ ^ 2) := by
      simp only [X0, X1]
      field_simp
      ring
    have hp : g.re * X0 τ + a * g.imI * X1 τ + g.re
        = 2 * (g.re + a * τ * g.imI) / (1 - a * τ ^ 2) := by
      simp only [X0, X1]
      field_simp
      ring
    have hz : (g.re * X0 τ + a * g.imI * X1 τ - g.re) * (g.re * X0 τ + a * g.imI * X1 τ + g.re) = 0 := by
      linear_combination h - hre
    rw [hm, hp] at hz
    exact mul_ne_zero (div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h2 ha) h1) h4) h2')
      (div_ne_zero (mul_ne_zero h2 h3) h2') hz

end GlobalTheory.QSA
end

section

noncomputable section

open Matrix
open scoped Quaternion

namespace GlobalTheory.PlaneSU

open Formalism.UG

section Emb

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

def emb (A : Matrix n (Fin 2) R) (B : Matrix (Fin 2) n R) (X : Matrix (Fin 2) (Fin 2) R) : Matrix n n R :=
  1 + A * (X - 1) * B

theorem emb_one (A : Matrix n (Fin 2) R) (B : Matrix (Fin 2) n R) : emb A B 1 = 1 := by
  simp [emb]

theorem emb_mul {A : Matrix n (Fin 2) R} {B : Matrix (Fin 2) n R} (hBA : B * A = 1)
    (X Y : Matrix (Fin 2) (Fin 2) R) : emb A B (X * Y) = emb A B X * emb A B Y := by
  have e1 : X * Y - 1 = (X - 1) + (Y - 1) + (X - 1) * (Y - 1) := by noncomm_ring
  have e2 : A * (X - 1) * B * (A * (Y - 1) * B) = A * ((X - 1) * (Y - 1)) * B := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc B A, hBA, Matrix.one_mul]
  unfold emb
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, e2, e1,
    Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul]
  abel

theorem det_emb {A : Matrix n (Fin 2) R} {B : Matrix (Fin 2) n R} (hBA : B * A = 1)
    (X : Matrix (Fin 2) (Fin 2) R) : (emb A B X).det = X.det := by
  unfold emb
  rw [Matrix.mul_assoc, Matrix.det_one_add_mul_comm, Matrix.mul_assoc, hBA, Matrix.mul_one, add_sub_cancel]

theorem emb_map {S : Type} [CommRing S] (f : R →+* S) (A : Matrix n (Fin 2) R) (B : Matrix (Fin 2) n R)
    (X : Matrix (Fin 2) (Fin 2) R) : (emb A B X).map f = emb (A.map f) (B.map f) (X.map f) := by
  simp [emb, Matrix.map_mul, Matrix.map_add (f := _), Matrix.map_sub, Matrix.map_one]

theorem cT_add (c : R →+* R) {m p : Type} (P Q : Matrix m p R) : cT c (P + Q) = cT c P + cT c Q := by
  ext i j; simp [cT]

theorem cT_sub (c : R →+* R) {m p : Type} (P Q : Matrix m p R) : cT c (P - Q) = cT c P - cT c Q := by
  ext i j; simp [cT]

theorem emb_unitary (c : R →+* R) {A : Matrix n (Fin 2) R} {B : Matrix (Fin 2) n R} {J : Matrix n n R}
    {H X : Matrix (Fin 2) (Fin 2) R} (hBA : B * A = 1) (h1 : cT c A * J = H * B) (h2 : J * A = cT c B * H)
    (hX : cT c X * H * X = H) : cT c (emb A B X) * J * emb A B X = J := by
  have hc : cT c (emb A B X) = 1 + cT c B * (cT c X - 1) * cT c A := by
    unfold emb
    rw [cT_add, cT_one, cT_mul, cT_mul, cT_sub, cT_one, Matrix.mul_assoc]
  set P := X - 1 with hP
  set P' := cT c X - 1 with hP'
  have key : H * P + P' * H + P' * H * P = 0 := by
    rw [hP, hP']
    calc H * (X - 1) + (cT c X - 1) * H + (cT c X - 1) * H * (X - 1) = cT c X * H * X - H := by noncomm_ring
      _ = 0 := by rw [hX, sub_self]
  have h1' : ∀ Z : Matrix n n R, cT c A * (J * Z) = H * (B * Z) := fun Z => by
    rw [← Matrix.mul_assoc, h1, Matrix.mul_assoc]
  have h1'' : ∀ {k : Type} [Fintype k] (Z : Matrix n k R), cT c A * (J * Z) = H * (B * Z) := fun Z => by
    rw [← Matrix.mul_assoc, h1, Matrix.mul_assoc]
  have h2' : ∀ {k : Type} (Z : Matrix (Fin 2) k R), J * (A * Z) = cT c B * (H * Z) := fun Z => by
    rw [← Matrix.mul_assoc, h2, Matrix.mul_assoc]
  have hBA' : ∀ {k : Type} (Z : Matrix (Fin 2) k R), B * (A * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, hBA, Matrix.one_mul]
  rw [hc]
  unfold emb
  rw [← hP]
  have e : (1 + cT c B * P' * cT c A) * J * (1 + A * P * B) =
      J + cT c B * ((H * P + P' * H + P' * H * P) * B) := by
    have hAB' : ∀ {k : Type} (Z : Matrix (Fin 2) k R), cT c A * (cT c B * Z) = Z := fun Z => by
      rw [← Matrix.mul_assoc, ← cT_mul, hBA, cT_one, Matrix.one_mul]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc, h1, h1'', h2', hBA', hAB']
    abel
  rw [e, key, Matrix.zero_mul, Matrix.mul_zero, add_zero]

end Emb

section Quat

variable {S T : Type} [CommRing S] [CommRing T]

def qm (ι : S →+* T) (θ : T) {a b : S} (x : ℍ[S, a, b]) : Matrix (Fin 2) (Fin 2) T :=
  !![ι x.re + ι x.imI * θ, ι b * (ι x.imJ + ι x.imK * θ); ι x.imJ - ι x.imK * θ, ι x.re - ι x.imI * θ]

variable (ι : S →+* T) (θ : T) {a b : S}

theorem qm_one : qm ι θ (1 : ℍ[S, a, b]) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [qm]

theorem qm_sub (x y : ℍ[S, a, b]) : qm ι θ (x - y) = qm ι θ x - qm ι θ y := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [qm] <;> ring

theorem qm_smul (r : S) (x : ℍ[S, a, b]) : qm ι θ (r • x) = ι r • qm ι θ x := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [qm] <;> ring

theorem qm_mul (hθ : θ * θ = ι a) (x y : ℍ[S, a, b]) : qm ι θ (x * y) = qm ι θ x * qm ι θ y := by
  ext i j
  have hθ2 : θ ^ 2 = ι a := by rw [sq, hθ]
  fin_cases i <;> fin_cases j <;> simp [qm, Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf <;> simp only [hθ2] <;> ring

theorem det_qm (hθ : θ * θ = ι a) (x : ℍ[S, a, b]) : (qm ι θ x).det = ι (GlobalTheory.QSA.nrm x) := by
  have hθ2 : θ ^ 2 = ι a := by rw [sq, hθ]
  simp [qm, Matrix.det_fin_two, GlobalTheory.QSA.nrm]
  ring_nf
  simp only [hθ2]
  ring

theorem qm_unitary (c : T →+* T) (hc : ∀ s, c (ι s) = ι s) (hcθ : c θ = -θ) (hθ : θ * θ = ι a)
    {h₁ h₂ : T} (hb : ι b * h₁ = -h₂) {x : ℍ[S, a, b]} (hx : GlobalTheory.QSA.nrm x = 1) :
    cT c (qm ι θ x) * Matrix.diagonal ![h₁, h₂] * qm ι θ x = Matrix.diagonal ![h₁, h₂] := by
  have hθ2 : θ ^ 2 = ι a := by rw [sq, hθ]
  have hn : ι x.re ^ 2 - ι a * ι x.imI ^ 2 - ι b * ι x.imJ ^ 2 + ι a * ι b * ι x.imK ^ 2 = 1 := by
    have := congrArg ι hx
    simp only [GlobalTheory.QSA.nrm, map_sub, map_add (f := _), map_mul, map_pow, map_one] at this
    exact this
  have hh2 : h₂ = -(ι b * h₁) := by rw [hb, neg_neg]
  subst hh2
  ext i j
  fin_cases i <;> fin_cases j
  · simp [cT, qm, Matrix.mul_apply, Fin.sum_univ_two, hc, hcθ]
    ring_nf; simp only [hθ2]; linear_combination h₁ * hn
  · simp [cT, qm, Matrix.mul_apply, Fin.sum_univ_two, hc, hcθ]
    ring_nf
  · simp [cT, qm, Matrix.mul_apply, Fin.sum_univ_two, hc, hcθ]
    ring_nf
  · simp [cT, qm, Matrix.mul_apply, Fin.sum_univ_two, hc, hcθ]
    ring_nf; simp only [hθ2]; linear_combination (-(ι b * h₁)) * hn

end Quat

section Plane

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F E : Type} [Field F] [Field E] [Algebra F E] {M : ℕ}

def planeA (e₁ e₂ : Fin M → E) : Matrix (Fin M) (Fin 2) E := Matrix.of fun i k => ![e₁, e₂] k i

def planeH (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (e₁ e₂ : Fin M → E) : Matrix (Fin 2) (Fin 2) E :=
  Matrix.diagonal ![hE σ J e₁ e₁, hE σ J e₂ e₂]

def planeB (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (e₁ e₂ : Fin M → E) : Matrix (Fin 2) (Fin M) E :=
  Matrix.diagonal ![(hE σ J e₁ e₁)⁻¹, (hE σ J e₂ e₂)⁻¹] * cT (σ : E →+* E) (planeA e₁ e₂) * J

end Plane

end GlobalTheory.PlaneSU
end
end

section

noncomputable section

namespace GlobalTheory.MatrixHomBijective

variable {F : Type} [Field F] [CharZero F]

theorem rep_of_sq {a b s t : F} (ha : a ≠ 0) (ht : t ≠ 0) (h : s ^ 2 = a * t ^ 2) :
    ∃ p q : F, b = p ^ 2 - a * q ^ 2 := by
  have hs : s ≠ 0 := by
    rintro rfl
    have : a * t ^ 2 ≠ 0 := mul_ne_zero ha (pow_ne_zero 2 ht)
    exact this (by rw [← h]; ring)
  have ha' : a = s ^ 2 / t ^ 2 := by
    rw [h]; field_simp
  refine ⟨(b + 1) / 2, (b - 1) * t / (2 * s), ?_⟩
  rw [ha']
  field_simp
  ring

theorem rep_of_isotropic {a b : F} (ha : a ≠ 0) (x : QuaternionAlgebra F a 0 b) (hx : x ≠ 0)
    (hn : GlobalTheory.QSA.nrm x = 0) : ∃ p q : F, b = p ^ 2 - a * q ^ 2 := by
  obtain ⟨x0, x1, x2, x3⟩ := x
  simp only [GlobalTheory.QSA.nrm] at hn
  by_cases hd : x2 ^ 2 - a * x3 ^ 2 = 0
  · by_cases h3 : x3 = 0
    · subst h3
      have h2 : x2 = 0 := by
        have : x2 ^ 2 = 0 := by linear_combination hd
        exact pow_eq_zero_iff (two_ne_zero) |>.1 this
      subst h2
      have h1 : x1 ≠ 0 := by
        rintro rfl
        have : x0 ^ 2 = 0 := by linear_combination hn
        have h0 : x0 = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 this
        subst h0
        exact hx rfl
      exact rep_of_sq (s := x0) ha h1 (by linear_combination hn)
    · exact rep_of_sq (s := x2) ha h3 (by linear_combination hd)
  · refine ⟨(x0 * x2 - a * x1 * x3) / (x2 ^ 2 - a * x3 ^ 2),
      (x1 * x2 - x0 * x3) / (x2 ^ 2 - a * x3 ^ 2), ?_⟩
    obtain ⟨d, hdd⟩ : ∃ d, d = x2 ^ 2 - a * x3 ^ 2 := ⟨_, rfl⟩
    rw [← hdd] at hd ⊢
    have key : b * d ^ 2 = (x0 * x2 - a * x1 * x3) ^ 2 - a * (x1 * x2 - x0 * x3) ^ 2 := by
      rw [hdd]
      linear_combination (-(x2 ^ 2 - a * x3 ^ 2)) * hn
    field_simp
    linear_combination key

def mat {a b : F} (p q : F) (x : QuaternionAlgebra F a 0 b) : Matrix (Fin 2) (Fin 2) F :=
  !![x.re + p * x.imJ + a * q * x.imK, a * x.imI - a * q * x.imJ - a * p * x.imK;
    x.imI + q * x.imJ + p * x.imK, x.re - p * x.imJ - a * q * x.imK]

def hom {a b : F} (p q : F) (h : b = p ^ 2 - a * q ^ 2) :
    QuaternionAlgebra F a 0 b →ₐ[F] Matrix (Fin 2) (Fin 2) F where
  toFun := mat p q
  map_one' := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [mat]
  map_mul' x y := by
    subst h
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  map_zero' := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [mat]
  map_add' x y := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mat] <;> ring
  commutes' r := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [mat, QuaternionAlgebra.algebraMap_eq, Matrix.algebraMap_matrix_apply]

theorem mat_bijective {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) (p q : F) (h : b = p ^ 2 - a * q ^ 2) :
    Function.Bijective (mat (a := a) (b := b) p q) := by
  constructor
  · intro x y hxy
    have e00 := congrFun (congrFun hxy 0) 0
    have e01 := congrFun (congrFun hxy 0) 1
    have e10 := congrFun (congrFun hxy 1) 0
    have e11 := congrFun (congrFun hxy 1) 1
    simp only [mat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] at e00 e01 e10 e11
    have two : (2 : F) ≠ 0 := two_ne_zero
    ext
    · apply mul_left_cancel₀ two
      linear_combination e00 + e11
    · apply mul_left_cancel₀ (mul_ne_zero two ha)
      linear_combination e01 + a * e10
    · apply mul_left_cancel₀ (mul_ne_zero two hb)
      linear_combination p * (e00 - e11) - q * (a * e10 - e01) + 2 * (x.imJ - y.imJ) * h
    · apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero two ha) hb)
      linear_combination p * (a * e10 - e01) - a * q * (e00 - e11) + 2 * a * (x.imK - y.imK) * h
  · intro M
    refine ⟨⟨(M 0 0 + M 1 1) / 2, (M 0 1 / a + M 1 0) / 2,
      (p * (M 0 0 - M 1 1) - q * (a * M 1 0 - M 0 1)) / (2 * b),
      (p * (a * M 1 0 - M 0 1) - a * q * (M 0 0 - M 1 1)) / (2 * a * b)⟩, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mat] <;> field_simp <;> rw [h] <;> ring

theorem det_mat {a b : F} (p q : F) (h : b = p ^ 2 - a * q ^ 2) (x : QuaternionAlgebra F a 0 b) :
    (mat p q x).det = GlobalTheory.QSA.nrm x := by
  subst h
  simp only [mat, Matrix.det_fin_two_of, GlobalTheory.QSA.nrm]
  ring

theorem split_of_isotropic (F : Type) [Field F] [NumberField F] (a b : F) (ha : a ≠ 0) (hb : b ≠ 0)
    (hx : ∃ x : QuaternionAlgebra F a 0 b, x ≠ 0 ∧ GlobalTheory.QSA.nrm x = 0) :
    ∃ φ : QuaternionAlgebra F a 0 b ≃ₐ[F] Matrix (Fin 2) (Fin 2) F,
      ∀ x, Matrix.det (φ x) = GlobalTheory.QSA.nrm x := by
  obtain ⟨x, hx, hn⟩ := hx
  obtain ⟨p, q, h⟩ := rep_of_isotropic ha x hx hn
  exact ⟨AlgEquiv.ofBijective (hom p q h) (mat_bijective ha hb p q h), fun y => det_mat p q h y⟩

end GlobalTheory.MatrixHomBijective
end
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechDR

theorem pullHyp1_restrict_injective {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type}
    [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C)
    (h1 : Function.Injective (CoefMap.restrict F G).pull1)
    (h0 : ∀ g' : ∀ t, F.obj (G.obj t), (∀ ⦃t t' : C'⦄ (a : t ⟶ t'), g' t' = mp F (G.map a) (g' t)) →
      ∃ g : C0 F, (∀ ⦃T T' : C⦄ (φ : T ⟶ T'), g T' = mp F φ (g T)) ∧ ∀ t, g (G.obj t) = g' t)
    (hf : Function.Injective (pullGlob1 (CoefMap.restrict F G))) :
    Function.Injective (pullHyp1 (CoefMap.restrict F G)) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨x, rfl⟩ := Hyp1.mk_surjective F c
  have ht : toO F (Hyp1.mk F x) = 0 := h1 (by rw [← toO_pullHyp1, hc, map_zero, map_zero])
  rw [pullHyp1_mk, Hyp1.mk_eq_zero] at hc
  obtain ⟨g, hg'⟩ := hc
  obtain ⟨g', rfl⟩ : ∃ g' : ∀ t, F.obj (G.obj t), (g' : Tot0 (G ⋙ F)) = g := ⟨g, rfl⟩
  have hf' : ∀ ⦃t t' : C'⦄ (a : t ⟶ t'), g' t' - mp F (G.map a) (g' t) = x.1.1 _ _ (G.map a) :=
    fun t t' a ↦ congrArg (fun y : Tot1 (G ⋙ F) ↦ y.1 t t' a) hg'
  have hω : ∀ t, D R _ (g' t) = x.1.2 (G.obj t) := fun t ↦
    (congrArg (fun y : Tot1 (G ⋙ F) ↦ y.2 t) hg').trans (cechDeRhamCoefMapOneForms_restrictAlongFunctor F G t _)
  rw [toO_mk, H1.mk_eq_zero] at ht
  obtain ⟨g₀, hg₀⟩ := ht
  have hg0 : ∀ (T T' : C) (φ : T ⟶ T'), g₀ T' - mp F φ (g₀ T) = x.1.1 T T' φ := fun T T' φ ↦
    congrFun (congrFun (congrFun hg₀ T) T') φ
  obtain ⟨h, hh, hhG⟩ := h0 (fun t ↦ g' t - g₀ (G.obj t)) (fun t t' a ↦ by
    have e1 := hf' a
    have e2 := hg0 _ _ (G.map a)
    rw [map_sub]
    linear_combination e1 - e2)
  let θ : Glob1 F := ⟨fun T ↦ x.1.2 T - D R _ (g₀ T), fun T T' φ ↦ by
    show x.1.2 T' - D R _ (g₀ T') = p1 F φ (x.1.2 T - D R _ (g₀ T))
    rw [map_sub, p1_D, cechDeRhamTotalCocyclesOne.conn x φ, ← hg0 T T' φ, map_sub]; abel⟩
  let ψ : Glob1 F := ⟨fun T ↦ D R _ (h T), fun T T' φ ↦ by
    show D R _ (h T') = p1 F φ (D R _ (h T))
    rw [p1_D, ← hh φ]⟩
  have hθψ : θ = ψ := hf (Subtype.ext (funext fun t ↦ by
    change q1 (CoefMap.restrict F G) t (θ.1 (G.obj t)) = q1 (CoefMap.restrict F G) t (ψ.1 (G.obj t))
    rw [cechDeRhamCoefMapOneForms_restrictAlongFunctor, cechDeRhamCoefMapOneForms_restrictAlongFunctor]
    show x.1.2 (G.obj t) - D R _ (g₀ (G.obj t)) = D R _ (h (G.obj t))
    rw [hhG, map_sub, hω]))
  refine Hyp1.mk_eq_zero.2 ⟨g₀ + h, Tot1.ext (fun T T' φ ↦ ?_) fun T ↦ ?_⟩
  · rw [dTot0_f]
    simp only [Pi.add_apply, map_add (f := _)]
    linear_combination hh φ + hg0 T T' φ
  · have e : x.1.2 T - D R _ (g₀ T) = D R _ (h T) := congrArg (fun ω : Glob1 F ↦ ω.1 T) hθψ
    rw [dTot0_ω, Pi.add_apply, map_add (f := _), ← e]
    abel

end GlobalTheory.CechDR
end
end

section

open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace

theorem _root_.GlobalTheory.T.parameter_function_eq_zero_of_composable : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F), K.Rich → ∀ (l m : Λ) (p : Hol F.V), (∀ (k k' k'' : K.K), K.le l k' k → K.le m k'' k' → K.cst k'' p = 0) → p = 0 := by
  first | exact @GlobalTheory.AnPer.Charts.eq_zero_of_cst_composable | exact GlobalTheory.AnPer.Charts.eq_zero_of_cst_composable | (intros; apply GlobalTheory.AnPer.Charts.eq_zero_of_cst_composable <;> assumption)
end

section

open Filter Topology TopologicalSpace CategoryTheory GlobalTheory.AnPer GlobalTheory.CatCoh GlobalTheory.Cris TensorProduct

theorem _root_.GlobalTheory.T.const_biadditive_coboundary_symmetric : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F), (∀ c : C1 K.Oc, (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = 0 → ψ.deg = 0 → c T T'' (φ ≫ ψ) = mp K.Oc ψ (c T T' φ) + c T' T'' ψ) → ∃ γ : C0 K.Oc, ∀ (T T' : K.Obj) (φ : T ⟶ T'), φ.deg = 0 → c T T' φ = d0 K.Oc γ T T' φ) → (∀ γ : C0 K.Oc, (∀ (T T' : K.Obj) (φ : T ⟶ T'), φ.deg = 0 → mp K.Oc φ (γ T) = γ T') → ∃ r : Hol F.V, ∀ T, γ T = algebraMap (Hol F.V) (K.Oc.obj T) r) → (∀ l k', ∃ k, K.le l k' k ∧ K.le (-l) k k') → K.Rich → ∀ (β : Λ →+ Λ →+ Hol F.V) (c : C1 K.Oc), (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), d1 K.Oc c T T' T'' φ ψ = algebraMap (Hol F.V) (K.Oc.obj T'') (β φ.deg ψ.deg)) → ∀ l m, β l m = β m l := by
  first | exact @GlobalTheory.AnPer.const_biadditive_coboundary_symm | exact GlobalTheory.AnPer.const_biadditive_coboundary_symm | (intros; apply GlobalTheory.AnPer.const_biadditive_coboundary_symm <;> assumption)
end
