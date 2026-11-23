module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle234
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle222
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle226
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle074
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle073
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle071
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle122
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle239
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle240
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle230
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle216
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryHeckeCharacterValues
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsDual
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle080
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle215
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle077
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators Pointwise

namespace GlobalTheory.CompletedLattice

variable (D : D7)

theorem moves_one (N : ℕ) : Moves D ((1 : GA D N) : GL (Fin N) (AE D)) (stdL D N) := by
  obtain ⟨Lt, h1, h2, -⟩ := GlobalTheory.NormSum.exists_lattice_of_adelic_point D N
  rw [← h2]
  exact (h1 1).1

theorem pt_injective (cc : Ideal (𝓞 D.host.K)) {δ : ℂ} (hδ : δ ≠ 0) {N N' : ℕ}
    {z z' : Matrix (Fin N') (Fin N) D.host.E}
    (h : pt D (tor0 D cc δ) δ z = pt D (tor0 D cc δ) δ z') : z = z' := by
  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm 1⟩
  refine Matrix.ext fun i j => ?_
  have h1 : δ * embT D τ (z i j) = δ * embT D τ (z' i j) := congrFun (congrFun (congrFun h τ) i) j
  exact (embT D τ).injective (mul_left_cancel₀ hδ h1)

theorem exists_mul_IhE_mem (cc : Ideal (𝓞 D.host.K)) :
    ∃ m : ℕ, 0 < m ∧ ∀ y ∈ IhE D cc, (m : AE D) * y ∈ OhE D := by
  have hb : D.host.𝔟 ≠ ⊥ := by
    intro h
    have h1 := D.host.𝔟_spec.1
    rw [h, Ideal.bot_mul] at h1
    exact differentIdeal_ne_bot h1
  have hB : ((D.host.𝔟 : Ideal (𝓞 D.host.E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 := by
    rwa [Ne, FractionalIdeal.coeIdeal_eq_zero]
  refine ⟨Ideal.absNorm D.host.𝔟, Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff]), fun y hy => ?_⟩
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨c, -, a, ha, s, hs, rfl⟩ := hy
    rw [FractionalIdeal.mem_coe] at ha
    unfold Host.AA0 at ha
    rw [FractionalIdeal.mem_inv_iff hB] at ha
    have h1 := ha _ (FractionalIdeal.mem_coeIdeal_of_mem _ (Ideal.absNorm_mem D.host.𝔟))
    obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1 h1
    rw [map_natCast] at hr
    have h2 : inc D (r : D.host.E) ∈ OhE D := (AdLattice.incl_mem_iff (F := ℚ) _).2 ⟨r, rfl⟩
    have h3 : inc D ((c : D.host.K) : D.host.E) ∈ OhE D :=
      (AdLattice.incl_mem_iff (F := ℚ) _).2 ⟨algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c, rfl⟩
    have h4 : (Ideal.absNorm D.host.𝔟 : AE D) * (inc D ((((c : D.host.K) : D.host.E)) * a) * s) =
        inc D ((c : D.host.K) : D.host.E) * (inc D (r : D.host.E) * s) := by
      have : (r : D.host.E) = a * (Ideal.absNorm D.host.𝔟 : D.host.E) := hr
      rw [this, map_mul, map_mul, map_natCast]
      ring
    rw [h4]
    exact mul_mem h3 (mul_mem h2 hs)
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [mul_neg]; exact neg_mem hx

theorem completed_lattice : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ), (∀ z : Matrix (Fin N') (Fin N) D.host.E, z.map (inc D) ∈ latA D cc N N' ↔ pt D (tor0 D cc δ) δ z ∈ La0 D (tor0 D cc δ) N N') ∧ (∀ x ∈ La0 D (tor0 D cc δ) N N', ∃ z, x = pt D (tor0 D cc δ) δ z) ∧ (∀ (ζ : XA D N N') (m : ℕ), 0 < m → ∃ z : Matrix (Fin N') (Fin N) D.host.E, ∃ a ∈ latA D cc N N', z.map (inc D) = ζ + m • a) ∧ (∀ ζ : XA D N N', ∃ m : ℕ, 0 < m ∧ m • ζ ∈ latA D cc N N') ∧ (∃ m : ℕ, 0 < m ∧ ∀ y ∈ IhE D cc, (m : AE D) * y ∈ OhE D) ∧ (∃ m : ℕ, 0 < m ∧ ∀ s ∈ OhE D, (m : AE D) * s ∈ IhE D cc) := by
  intro D hg cc δ hc N N'
  have hcc : cc ≠ ⊥ := hc.1.1
  have hδ : δ ≠ 0 := (GlobalTheory.CurveLattice.lattice_of_curve D hg cc δ hc).2.1
  have hn : 0 < Ideal.absNorm cc := Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
  have hA := GlobalTheory.NormSum.exists_pt_of_mem_La_moved D hg cc δ hcc N N' 1 1 _ _ (moves_one D N) (moves_one D N')
  have hB := GlobalTheory.NormSum.pt_mem_La_of_adelic D hg cc δ hcc N N' 1 1 _ _ (moves_one D N) (moves_one D N')
  simp only [OneMemClass.coe_one, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one] at hA hB
  refine ⟨fun z => ⟨fun h => hB z h, fun h => ?_⟩, fun x hx => ?_, fun ζ m hm => ?_, fun ζ => ?_,
    exists_mul_IhE_mem D cc, _, hn, GlobalTheory.AdelicApprox.absNorm_mul_mem_IhE D cc⟩
  · obtain ⟨z', h1, h2⟩ := hA _ h
    rw [pt_injective D cc hδ h1]
    exact h2
  · obtain ⟨z, h1, -⟩ := hA x hx
    exact ⟨z, h1⟩
  · choose e t ht h using fun (i : Fin N') (j : Fin N) => (GlobalTheory.AdelicApprox.approx_mod_ideal D cc hcc).1 (ζ i j) m hm
    refine ⟨Matrix.of e, Matrix.of t, ht, ?_⟩
    ext i j
    rw [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, nsmul_eq_mul, Matrix.of_apply, Matrix.of_apply, ← h]
    ring
  · choose n hn0 h using fun k : Fin N' × Fin N => GlobalTheory.AdelicApprox.exists_denom D (ζ k.1 k.2)
    refine ⟨Ideal.absNorm cc * ∏ k, n k, Nat.mul_pos hn (Finset.prod_pos fun k _ => hn0 k), fun i j => ?_⟩
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem n (Finset.mem_univ (i, j))
    have h1 := GlobalTheory.AdelicApprox.absNorm_mul_mem_IhE D cc _ (mul_mem (natCast_mem (OhE D) c) (h (i, j)))
    rw [Matrix.smul_apply, nsmul_eq_mul, hc]
    convert h1 using 1
    push_cast
    ring

end GlobalTheory.CompletedLattice
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil.WdCocycle

section General

variable {D : D7} {T : Tor D} {N N' : ℕ}

theorem hf_add_left (x y z : VC D N N') : Hf D T (x + y) z = Hf D T x z + Hf D T y z := by
  simp only [Hf, Pi.add_apply, add_mul, Finset.sum_add_distrib, add_div]

theorem hf_add_right (x y z : VC D N N') : Hf D T x (y + z) = Hf D T x y + Hf D T x z := by
  simp only [Hf, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib, add_div]

theorem hf_conj (x z : VC D N N') : Hf D T z x = (starRingEnd ℂ) (Hf D T x z) := by

  simp only [Hf, map_div₀, map_sum, map_mul, Complex.conj_conj, Complex.conj_ofReal]
  congr 1
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

theorem wd_wd (x y : VC D N N') (F : VC D N N' → ℂ) :
    Wd D T x (Wd D T y F) = ee (-(w0 D * Hf D T x y).im) • Wd D T (x + y) F := by
  funext z
  have h1 : Hf D T x y = ((Hf D T x y).re : ℂ) + ((Hf D T x y).im : ℂ) * Complex.I := (Complex.re_add_im _).symm
  have h2 : Hf D T y x = ((Hf D T x y).re : ℂ) - ((Hf D T x y).im : ℂ) * Complex.I := by
    rw [hf_conj x y]
    apply Complex.ext <;> simp
  have h3 : (Hf D T y x).re = (Hf D T x y).re := by
    rw [hf_conj x y, Complex.conj_re]
  have h4 : (w0 D * Hf D T x y).im = ((Hf D T x y).im + Real.sqrt D.host.d * (Hf D T x y).re) / 2 := by
    have : w0 D = ((1 / 2 : ℝ) : ℂ) + ((Real.sqrt D.host.d / 2 : ℝ) : ℂ) * Complex.I := by
      rw [w0]; push_cast; ring
    rw [this]
    simp only [Complex.mul_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  have key : ee (qH D T x / 2) * ee (qH D T y / 2) *
      Complex.exp (-(Real.pi : ℂ) * Hf D T (z + x) y - (Real.pi : ℂ) * Hf D T y y / 2) *
      Complex.exp (-(Real.pi : ℂ) * Hf D T z x - (Real.pi : ℂ) * Hf D T x x / 2) =
      ee (-(w0 D * Hf D T x y).im) * ee (qH D T (x + y) / 2) *
      Complex.exp (-(Real.pi : ℂ) * Hf D T z (x + y) - (Real.pi : ℂ) * Hf D T (x + y) (x + y) / 2) := by
    simp only [ee, ← Complex.exp_add, qH]
    congr 1
    rw [h4]
    simp only [hf_add_left, hf_add_right, Complex.add_re, h3]
    rw [h2]
    generalize (Hf D T x y).re = a at h1 ⊢
    generalize (Hf D T x y).im = b at h1 ⊢
    rw [h1]
    push_cast
    ring
  simp only [Wd, U, wdPh, Pi.smul_apply, smul_eq_mul]
  rw [add_assoc z x y]
  linear_combination F (z + (x + y)) * key

end General

variable {D : D7}

theorem emb_conj (φ : D.host.E →+* ℂ) (x : D.host.E) : φ (D.host.conj x) = starRingEnd ℂ (φ x) :=
  D.host.conjE_apply φ x

theorem hf_pt (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (z y : Matrix (Fin N') (Fin N) D.host.E) :
    Hf D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) (pt D (tor0 D cc δ) δ y) =
      ((‖δ‖ ^ 2 / area (lamOf D cc δ) : ℝ) : ℂ) * ∑ τ, embT D τ (∑ i, ∑ j, z i j * D.host.conj (y i j)) := by
  have h : δ * starRingEnd ℂ δ = (‖δ‖ : ℂ) ^ 2 := Complex.mul_conj' δ

  simp only [Hf, pt, embV, tor0, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, emb_conj]
  push_cast
  rw [← h, div_mul_eq_mul_div]
  congr 1
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

theorem pt_add (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (z y : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ (z + y) = pt D (tor0 D cc δ) δ z + pt D (tor0 D cc δ) δ y := by
  funext τ i j
  simp only [pt, embV, tor0, Pi.smul_apply, Pi.add_apply, Matrix.add_apply, smul_eq_mul, map_add (f := _), mul_add]

theorem wd_cocycle : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∃ w : 𝓞 D.host.E, w + sgO D w = 1 ∧ ∀ (N N' : ℕ) (z y : Matrix (Fin N') (Fin N) D.host.E), ee (-(Hf D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) (pt D (tor0 D cc δ) δ y)).im) = psi0 D cc δ (∑ i, ∑ j, z i j * D.host.conj (y i j)) ∧ pt D (tor0 D cc δ) δ (z + y) = pt D (tor0 D cc δ) δ z + pt D (tor0 D cc δ) δ y ∧ ∀ F, Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) (Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ y) F) = psi0 D cc δ (∑ i, ∑ j, (w : D.host.E) * z i j * D.host.conj (y i j)) • Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z + y)) F := by
  intro D hg cc δ _
  obtain ⟨a, ha⟩ := exists_integer_map_eq_w0 D
  let w : 𝓞 D.host.E := algebraMap (𝓞 D.host.K) (𝓞 D.host.E) a
  have hw : (w : D.host.E) = ((a : D.host.K) : D.host.E) := rfl
  have hτ : ∀ τ, embT D τ (w : D.host.E) = w0 D := fun τ => by
    rw [hw, ← ha]
    exact hg.1 τ _
  refine ⟨w, ?_, fun N N' z y => ⟨?_, pt_add cc δ z y, fun F => ?_⟩⟩
  · apply RingOfIntegers.ext
    apply D.host.φ₀.injective
    change D.host.φ₀ ((w : D.host.E) + D.host.conj (w : D.host.E)) = D.host.φ₀ 1
    rw [map_add (f := _), emb_conj, hw, ha, map_one, w0]
    simp only [map_div₀, map_add (f := _), map_mul, map_one, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
    ring
  · rw [hf_pt, psi0, Complex.im_ofReal_mul]
  · rw [wd_wd, pt_add, hf_pt, psi0]
    congr 3
    rw [mul_left_comm, Complex.im_ofReal_mul, Finset.mul_sum]
    congr 2
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [← hτ τ, ← map_mul]
    simp only [Finset.mul_sum, mul_assoc]

end GlobalTheory.FinWeil.WdCocycle
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil.AdelicChar

theorem ee_add (s t : ℝ) : ee (s + t) = ee s * ee t := by
  rw [ee, ee, ee, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem ee_int (k : ℤ) : ee k = 1 := by
  rw [ee, mul_comm]
  exact_mod_cast Complex.exp_int_mul_two_pi_mul_I k

variable (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ)

theorem cmTraceAdditiveCharacter_add (a b : D.host.E) : psi0 D cc δ (a + b) = psi0 D cc δ a * psi0 D cc δ b := by
  rw [psi0, psi0, psi0, ← ee_add]
  congr 1
  simp only [map_add (f := _), Finset.sum_add_distrib, Complex.add_im]
  ring

theorem cmTraceAdditiveCharacter_zero : psi0 D cc δ 0 = 1 := by simp [psi0, ee]

theorem embT_conj (τ : D.what₂.Tau) (a : D.host.E) :
    embT D τ (D.host.conj a) = (starRingEnd ℂ) (embT D τ a) := by
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  have h : D.host.conj a = IsCMField.complexConj D.host.E a := by
    apply D.host.φ₀.injective
    rw [IsCMField.complexEmbedding_complexConj]
    exact D.host.toHostAx.conjE_apply _ a
  rw [h, IsCMField.complexEmbedding_complexConj]

theorem cmTraceAdditiveCharacter_add_conj (a : D.host.E) : psi0 D cc δ (a + D.host.conj a) = 1 := by
  have : (∑ τ, embT D τ (a + D.host.conj a)).im = 0 := by
    simp [Complex.im_sum, embT_conj]
  rw [psi0, this]
  simp [ee]

theorem im_div_area (hcc : cc ≠ ⊥) (hδ : δ ≠ 0) {x y : ℂ} (hx : x ∈ lamOf D cc δ) (hy : y ∈ lamOf D cc δ) :
    ∃ k : ℤ, (x * (starRingEnd ℂ) y).im / area (lamOf D cc δ) = k := by
  obtain ⟨a, τ, ha, -, h⟩ := GlobalTheory.CurveLattice.exists_tau D cc hcc
  have hda : δ * a ≠ 0 := mul_ne_zero hδ ha
  rw [GlobalTheory.CurveLattice.area_of_tau hda (h δ)]
  obtain ⟨m, n, rfl⟩ := (h δ x).1 hx
  obtain ⟨m', n', rfl⟩ := (h δ y).1 hy
  refine ⟨m * n' - n * m', ?_⟩
  have hp : 0 < ‖δ * a‖ ^ 2 * τ.im := by
    have := norm_pos_iff.2 hda
    have := τ.im_pos
    positivity
  rw [div_eq_iff hp.ne']
  generalize δ * a = b
  simp [Complex.sq_norm, Complex.normSq_apply]
  ring

theorem cmTraceAdditiveCharacter_trivial_multiple_integers (hg : admG1 D) (hc : Crv D cc δ) :
    ∃ m : ℕ, 0 < m ∧ ∀ r : D.host.E, IsIntegral ℤ r → psi0 D cc δ ((m : D.host.E) * r) = 1 := by
  have hδ : δ ≠ 0 := (GlobalTheory.CurveLattice.lattice_of_curve D hg cc δ hc).2.1
  have hcc := hc.1.1
  set n := Ideal.absNorm cc with hn
  have hn0 : n ≠ 0 := by simpa [hn, Ideal.absNorm_eq_zero_iff] using hcc
  refine ⟨n * n, by positivity, fun r hr => ?_⟩
  let t : 𝓞 D.host.K := ⟨Algebra.trace D.host.K D.host.E r, Algebra.isIntegral_trace hr⟩
  have hnc : (n : 𝓞 D.host.K) ∈ cc := Ideal.absNorm_mem cc
  obtain ⟨k, hk⟩ := im_div_area D cc δ hcc hδ
    ((GlobalTheory.CurveLattice.mem_lamOf D cc δ _).2 ⟨_, cc.mul_mem_right t hnc, rfl⟩)
    ((GlobalTheory.CurveLattice.mem_lamOf D cc δ _).2 ⟨_, hnc, rfl⟩)
  rw [psi0, ← ee_int (-k)]
  congr 1
  have h1 : ∑ τ, embT D τ (((n * n : ℕ) : D.host.E) * r) =
      (n : ℂ) * n * D.host.φ₀ ((t : D.host.K) : D.host.E) := by
    have := hg.2 r
    simp only [map_mul, map_natCast, ← Finset.mul_sum, this, Nat.cast_mul]
    rfl
  have h2 : D.host.φ₀ (((n * t : 𝓞 D.host.K) : D.host.K) : D.host.E) =
      (n : ℂ) * D.host.φ₀ ((t : D.host.K) : D.host.E) := by simp
  have h3 : D.host.φ₀ ((((n : ℕ) : 𝓞 D.host.K) : D.host.K) : D.host.E) = (n : ℂ) := by simp
  rw [h2, h3] at hk
  rw [h1, Int.cast_neg, ← hk]
  generalize D.host.φ₀ ((t : D.host.K) : D.host.E) = z
  simp [Complex.sq_norm, Complex.normSq_apply]
  ring

theorem exists_rat (m : ℕ) (hm : 0 < m) (y : AE D) :
    ∃ e : D.host.E, ∃ s ∈ OhE D, y = inc D e + (m : AE D) * s := by
  obtain ⟨n, hn, hy⟩ := GlobalTheory.HeckeVal.exists_denom D y
  obtain ⟨r, -, w, hw, e⟩ := GlobalTheory.HeckeVal.exists_approx D (n * m) (Nat.mul_pos hn hm) _ hy
  have h1 : inc D ((n : D.host.E)⁻¹) * (n : AE D) = 1 := by
    rw [← map_natCast (inc D), ← map_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hn.ne'), map_one]
  refine ⟨(n : D.host.E)⁻¹ * r, w, hw, ?_⟩
  rw [map_mul]
  push_cast at e
  linear_combination inc D ((n : D.host.E)⁻¹) * e + ((m : AE D) * w - y) * h1

theorem exists_psi : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∃ ψ : AE D → ℂ, IsPsi D cc δ ψ := by
  intro D hg cc δ hc
  obtain ⟨m, hm, hint⟩ := cmTraceAdditiveCharacter_trivial_multiple_integers D cc δ hg hc
  choose e s hs he using exists_rat D m hm
  have key : ∀ (y : AE D) (a : D.host.E) (w : AE D), w ∈ OhE D → y = inc D a + (m : AE D) * w →
      psi0 D cc δ (e y) = psi0 D cc δ a := by
    intro y a w hw h
    have hm' : (m : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
    have h1 : inc D ((m : D.host.E)⁻¹) * (m : AE D) = 1 := by
      rw [← map_natCast (inc D), ← map_mul, inv_mul_cancel₀ hm', map_one]
    have h2 : inc D ((m : D.host.E)⁻¹ * (e y - a)) = w - s y := by
      rw [map_mul, map_sub]
      linear_combination inc D ((m : D.host.E)⁻¹) * (h - he y) + (w - s y) * h1
    have h3 := hint _ ((GlobalTheory.HeckeVal.inc_mem_iff D _).1 (h2 ▸ sub_mem hw (hs y)))
    rw [mul_inv_cancel_left₀ hm'] at h3
    rw [show e y = a + (e y - a) by ring, cmTraceAdditiveCharacter_add, h3, mul_one]
  refine ⟨fun y => psi0 D cc δ (e y), fun x y => ?_, ?_, fun a => ?_, fun y => ?_, m, hm, fun w hw => ?_⟩
  · rw [← cmTraceAdditiveCharacter_add]
    refine key _ _ _ (add_mem (hs x) (hs y)) ?_
    rw [map_add (f := _)]
    linear_combination he x + he y
  · exact (key 0 0 0 (zero_mem _) (by simp)).trans (cmTraceAdditiveCharacter_zero D cc δ)
  · exact key _ a 0 (zero_mem _) (by simp)
  · have hw : sgA D (s y) ∈ OhE D := Formalism.UG.P.csDual_sig_mem _ (hs y)
    refine (key _ (e y + D.host.conj (e y)) _ (add_mem (hs y) hw) ?_).trans (cmTraceAdditiveCharacter_add_conj D cc δ _)
    have h := congrArg (sgA D) (he y)
    rw [map_add (f := _), map_mul, map_natCast, GlobalTheory.NormSum.PtsMem.sgA_inc] at h
    rw [map_add (f := _)]
    linear_combination he y + h
  · exact (key _ 0 w hw (by simp)).trans (cmTraceAdditiveCharacter_zero D cc δ)

end GlobalTheory.FinWeil.AdelicChar
end

section

open UpperHalfPlane Filter GlobalTheory.OddFrame
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory.OddFrame

theorem neg_one_not_mem_Gamma1 {N : ℕ} (hN : 5 ≤ N) : (-1 : SL(2, ℤ)) ∉ CongruenceSubgroup.Gamma1 N := by
  intro h
  rw [CongruenceSubgroup.Gamma1_mem] at h
  have h1 : ((2 : ℕ) : ZMod N) = 0 := by
    have := h.1
    simp at this
    push_cast
    linear_combination -this
  rw [ZMod.natCast_eq_zero_iff] at h1
  have := Nat.le_of_dvd (by norm_num) h1
  omega

theorem neg_one_mem_Gamma {M : ℕ} (h0 : 0 < M) (hM : M < 3) : (-1 : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma M := by
  rw [CongruenceSubgroup.Gamma_mem]
  interval_cases M <;> simp <;> decide

theorem exists_frame (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (hM : 0 < M) (hΓ : CongruenceSubgroup.Gamma M ≤ Γ)
    (h1 : (-1 : SL(2, ℤ)) ∉ Γ) {r : ℕ} {s : Fin r → SL(2, ℤ)} (hs : IsReps Γ s) :
    ∃ (w : Fin r → ℤ) (F G : Fin r → ℍ → ℂ), (∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j)) ∧
      (∀ τ, (evM s w F τ).det ≠ 0) ∧ (∀ j, IsCF Γ (12 - w j) (G j)) ∧
      ∀ τ, (evM s (fun j => 12 - w j) G τ).det ≠ 0 := by
  have hfi := finiteIndex_of_Gamma_le hM hΓ
  have hM3 : 3 ≤ M := by
    by_contra h
    exact h1 (hΓ (neg_one_mem_Gamma hM (by omega)))
  obtain ⟨τ₀, hτ₀⟩ := GlobalTheory.T.exists_point_slashEvaluations_independent_gamma M hM (GlobalTheory.T.exists_eisenstein_slash_ne_outside_gamma M hM3)
  obtain ⟨w₀, F₀, hF₀, hd₀⟩ := GlobalTheory.T.exists_odd_weight_frame_det_ne_zero M Γ r s τ₀ hM hΓ h1 hs hτ₀
  obtain ⟨w, F, hF, -, hred⟩ := GlobalTheory.T.exists_oddFrame_not_reducesToSmallerOddWeight Γ r s w₀ F₀ hfi hF₀ ⟨τ₀, hd₀⟩
  have hdet : ∀ τ, (evM s w F τ).det ≠ 0 := fun τ h => hred (GlobalTheory.T.reduces_of_det_evM_eq_zero' Γ r s w F τ hs hF h)
  have hlead : (leadM M s w F).det ≠ 0 := fun h => hred (GlobalTheory.T.reducesToSmallerOddWeight_of_leadingCoeffMatrix_det_zero M Γ r s w F hM hΓ hs hF h)
  obtain ⟨U, hU1, hU2⟩ := GlobalTheory.T.exists_tendsto_slashEvaluationMatrix_mul M Γ r s w F hM hΓ hs hF hlead
  obtain ⟨G, hG, hGd⟩ := GlobalTheory.T.exists_dual_oddFrame_cuspForms Γ r s w F h1 hs hF hdet (GlobalTheory.T.tendsto_smul_inv_of_mul_tendsto_invertible_matrix r _ U _ _ hlead hU1 hU2)
  exact ⟨w, F, G, hF, hdet, hG, hGd⟩

theorem levelOne_pair (k j : ℤ) (hk : Odd k) (hj : Odd j) :
    2 * k - 2 + 4 * (if k % 3 = 0 then 1 else if k % 3 = 2 then -1 else 0) * (3 * (if (3 : ℤ) ∣ j then 1 else 0) - 1)
      ≤ 12 * ((Module.finrank ℂ (ModularForm 𝒮ℒ (k - j)) : ℤ) +
        (Module.finrank ℂ (ModularForm 𝒮ℒ (k - (12 - j))) : ℤ)) := by
  have ha := GlobalTheory.T.levelOne_twelve_mul_finrank_modularForm_lower_bound (k - j) (hk.sub_odd hj)
  have hb := GlobalTheory.T.levelOne_twelve_mul_finrank_modularForm_lower_bound (k - (12 - j)) (hk.sub_odd (Even.sub_odd (by decide) hj))
  rw [Int.odd_iff] at hk hj
  generalize (Module.finrank ℂ (ModularForm 𝒮ℒ (k - j)) : ℤ) = a at *
  generalize (Module.finrank ℂ (ModularForm 𝒮ℒ (k - (12 - j))) : ℤ) = b at *
  have e4 : ((if (k - j) % 4 = 0 then 1 else -1) : ℤ) + (if (k - (12 - j)) % 4 = 0 then 1 else -1) = 0 := by
    split_ifs <;> omega
  have e3 : ((if (k - j) % 6 = 0 then 1 else if (k - j) % 6 = 2 then -1 else 0) : ℤ) +
      (if (k - (12 - j)) % 6 = 0 then 1 else if (k - (12 - j)) % 6 = 2 then -1 else 0) =
      (if k % 3 = 0 then 1 else if k % 3 = 2 then -1 else 0) * (3 * (if (3 : ℤ) ∣ j then 1 else 0) - 1) := by
    split_ifs <;> omega
  rw [mul_assoc, ← e3]
  linarith

theorem dim_lower_bound : ∀ (N M : ℕ) (Γ : Subgroup SL(2, ℤ)) (k : ℕ), 5 ≤ N → 0 < M →
    CongruenceSubgroup.Gamma M ≤ Γ → Γ ≤ CongruenceSubgroup.Gamma1 N → Odd k → 3 ≤ k →
    FiniteDimensional ℂ (ModularForm Γ (k : ℤ)) ∧ FiniteDimensional ℂ (CuspForm Γ (k : ℤ)) ∧
      (k - 1) * Γ.index ≤
        12 * (Module.finrank ℂ (ModularForm Γ (k : ℤ)) + Module.finrank ℂ (CuspForm Γ (k : ℤ))) := by
  intro N M Γ k hN hM hΓ hΓ1 hk hk3
  obtain ⟨hfM, hfS⟩ := GlobalTheory.T.finiteDimensional_modularForm_cuspForm_of_gamma_le M Γ k hM hΓ
  refine ⟨hfM, hfS, ?_⟩
  have hfi := finiteIndex_of_Gamma_le hM hΓ
  have h1 : (-1 : SL(2, ℤ)) ∉ Γ := fun h => neg_one_not_mem_Gamma1 hN (hΓ1 h)
  obtain ⟨r, s, hs, hr⟩ := GlobalTheory.T.exists_plusMinusCosetRepresentatives_two_mul_card Γ hfi h1
  obtain ⟨w, F, G, hF, hd, hG, hGd⟩ := exists_frame M Γ hM hΓ h1 hs
  have hcM := GlobalTheory.T.sum_finrank_levelOne_le_finrank_of_frame Γ r s w F k hfi hfM (fun j => (hF j).2) hd
  have hcS := GlobalTheory.T.sum_finrank_levelOne_le_finrank_cuspForm_of_frame Γ r s (fun j => 12 - w j) G k hfi hfS hG hGd
  have h3 := GlobalTheory.T.three_mul_card_oddFrame_weights_dvd_three N Γ r s w F hN hΓ1 hs hF (hd _)
  have hkz : Odd (k : ℤ) := by exact_mod_cast hk
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun j _ => levelOne_pair k (w j) hkz (hF j).1
  have h3' : ∑ j, (3 * (if (3 : ℤ) ∣ w j then (1 : ℤ) else 0) - 1) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    have : (3 : ℤ) * ((Finset.univ.filter fun j => (3 : ℤ) ∣ w j).card : ℤ) = r := by exact_mod_cast h3
    omega
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, h3', ← Finset.mul_sum, Finset.sum_add_distrib] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_zero, add_zero] at hsum
  have hcM' : ∑ j, (Module.finrank ℂ (ModularForm 𝒮ℒ ((k : ℤ) - w j)) : ℤ) ≤
      Module.finrank ℂ (ModularForm Γ (k : ℤ)) := by exact_mod_cast hcM
  have hcS' : ∑ j, (Module.finrank ℂ (ModularForm 𝒮ℒ ((k : ℤ) - (12 - w j))) : ℤ) ≤
      Module.finrank ℂ (CuspForm Γ (k : ℤ)) := by exact_mod_cast hcS
  rw [← hr]
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  zify
  simp only [Nat.add_sub_cancel]
  push_cast at hsum hcM' hcS' ⊢
  nlinarith

end GlobalTheory.OddFrame
end
