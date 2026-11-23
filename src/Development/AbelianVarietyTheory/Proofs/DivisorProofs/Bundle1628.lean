module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1576
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1594
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogIdealMulSpanMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBoundedPolesGlobalData
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.IrreducibleOfIrreducibleMap
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LeadingCoeffNonnegOfEventuallyEvalNat
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChowFormIntExistsAndChowFormExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle401
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RingKrullDimQuotientAddOneOfMemMinimalPrimesSup
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1579
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1581
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Univ
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
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
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle016
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle031
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle046
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective

@[expose] public section

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid.CentPos

theorem eq_smul_of_eigen {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (Z : GL (Fin n) ℂ) (lam : Fin n → ℂ)
    (hlam : Function.Injective lam) (hZ : M * (Z : Matrix (Fin n) (Fin n) ℂ) = (Z : Matrix (Fin n) (Fin n) ℂ) * diagonal lam)
    (μ : ℂ) (u w : Fin n → ℂ) (hu : M *ᵥ u = μ • u) (hw : M *ᵥ w = μ • w) (hu0 : u ≠ 0) :
    ∃ l : ℂ, w = l • u := by
  set Zm : Matrix (Fin n) (Fin n) ℂ := (Z : Matrix (Fin n) (Fin n) ℂ)
  set Zi : Matrix (Fin n) (Fin n) ℂ := ((Z⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)
  have h1 : Zi * Zm = 1 := by simp [Zi, Zm, ← Units.val_mul]
  have h2 : Zm * Zi = 1 := by simp [Zi, Zm, ← Units.val_mul]
  have hD : Zi * M = diagonal lam * Zi := by
    calc Zi * M = Zi * (M * Zm) * Zi := by rw [Matrix.mul_assoc, Matrix.mul_assoc, h2, Matrix.mul_one]
      _ = Zi * (Zm * diagonal lam) * Zi := by rw [hZ]
      _ = diagonal lam * Zi := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hcoord : ∀ a : Fin n → ℂ, M *ᵥ a = μ • a → ∀ j, lam j * (Zi *ᵥ a) j = μ * (Zi *ᵥ a) j := by
    intro a ha j
    have e : diagonal lam *ᵥ (Zi *ᵥ a) = μ • (Zi *ᵥ a) := by
      rw [mulVec_mulVec, ← hD, ← mulVec_mulVec, ha, mulVec_smul]
    have := congrFun e j
    rwa [mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at this
  have hback : ∀ a : Fin n → ℂ, Zm *ᵥ (Zi *ᵥ a) = a := by
    intro a; rw [mulVec_mulVec, h2, one_mulVec]
  set u' := Zi *ᵥ u
  set w' := Zi *ᵥ w
  have hu'0 : u' ≠ 0 := by
    intro h; apply hu0; rw [← hback u]; show Zm *ᵥ u' = 0; rw [h, mulVec_zero]
  obtain ⟨i0, hi0⟩ : ∃ i0, u' i0 ≠ 0 := by
    by_contra h; push_neg at h; exact hu'0 (funext h)
  have hlam0 : lam i0 = μ := mul_right_cancel₀ hi0 (hcoord u hu i0)
  refine ⟨w' i0 / u' i0, ?_⟩
  have hw' : w' = (w' i0 / u' i0) • u' := by
    funext j
    rw [Pi.smul_apply, smul_eq_mul]
    by_cases hj : j = i0
    · subst hj; field_simp
    · have hne : lam j - μ ≠ 0 := by
        intro h; apply hj; apply hlam; rw [hlam0]; exact sub_eq_zero.1 h
      have hu0j : u' j = 0 := by
        have := hcoord u hu j
        have h' : (lam j - μ) * u' j = 0 := by rw [sub_mul]; exact sub_eq_zero.2 this
        exact (mul_eq_zero.1 h').resolve_left hne
      have hw0j : w' j = 0 := by
        have := hcoord w hw j
        have h' : (lam j - μ) * w' j = 0 := by rw [sub_mul]; exact sub_eq_zero.2 this
        exact (mul_eq_zero.1 h').resolve_left hne
      rw [hu0j, hw0j, mul_zero]
  calc w = Zm *ᵥ w' := (hback w).symm
    _ = Zm *ᵥ ((w' i0 / u' i0) • u') := by rw [← hw']
    _ = (w' i0 / u' i0) • u := by rw [mulVec_smul, hback u]

theorem cent_form_law {p : ℕ} [Fact p.Prime] (G : HTGroup p) (P : Pair G) (v : InfinitePlace G.F)
    (y : G.Cˣ × ℚˣ) (hy : y ∈ P.cent) :
    (G.psi v (y.1 : G.C))ᴴ * (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) * G.psi v (y.1 : G.C) =
      (((y.2 : ℚˣ) : ℚ) : ℂ) • (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) := by
  have hsim : (y.1 : G.C) * P.β * sh G y.1 = algebraMap ℚ G.C (y.2 : ℚ) * P.β := hy.2
  have hgu : IsUnit (G.gram v).det := isUnit_iff_ne_zero.mpr (G.gram_det v)
  have hgg : G.gram v * (G.gram v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hgu
  have hgg' : (G.gram v)⁻¹ * G.gram v = 1 := Matrix.nonsing_inv_mul _ hgu
  have hH : ∀ x : G.C, (G.psi v x)ᴴ = G.gram v * G.psi v (sh G x) * (G.gram v)⁻¹ := by
    intro x
    have e : G.psi v (sh G x) = (G.gram v)⁻¹ * (G.psi v x)ᴴ * G.gram v := G.psi_star v x
    rw [e, ← mul_assoc, ← mul_assoc, hgg, one_mul, mul_assoc, hgg, mul_one]
  have hu : sh G (y.1 : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C) * y.1 =
      algebraMap ℚ G.C (y.2 : ℚ) * ((P.β⁻¹ : G.Cˣ) : G.C) := by
    apply (Units.mul_right_inj (y.1 * P.β)).mp
    rw [Units.val_mul, ← Algebra.smul_def]
    calc (y.1 : G.C) * P.β * (sh G (y.1 : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C) * y.1)
        = ((y.1 : G.C) * P.β * sh G (y.1 : G.C)) * ((P.β⁻¹ : G.Cˣ) : G.C) * y.1 := by
          simp only [mul_assoc]
      _ = (y.2 : ℚ) • ((P.β : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C) * y.1) := by
          rw [hsim, ← Algebra.smul_def]; simp only [smul_mul_assoc]
      _ = (y.2 : ℚ) • ((y.1 : G.C) * P.β * ((P.β⁻¹ : G.Cˣ) : G.C)) := by
          rw [Units.mul_inv, one_mul, mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [mul_smul_comm, mul_assoc]
  rw [hH]
  calc G.gram v * G.psi v (sh G (y.1 : G.C)) * (G.gram v)⁻¹ * (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) *
        G.psi v (y.1 : G.C)
      = G.gram v * (G.psi v (sh G (y.1 : G.C)) * ((G.gram v)⁻¹ * G.gram v) *
          G.psi v ((P.β⁻¹ : G.Cˣ) : G.C) * G.psi v (y.1 : G.C)) := by simp only [mul_assoc]
    _ = G.gram v * G.psi v (sh G (y.1 : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C) * y.1) := by
        rw [hgg', mul_one, map_mul, map_mul]
    _ = G.gram v * (((y.2 : ℚˣ) : ℚ) • G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) := by
        rw [hu, map_mul, RingHom.map_rat_algebraMap, ← Algebra.smul_def]
    _ = _ := by rw [mul_smul_comm, Rat.cast_smul_eq_qsmul]

end GlobalTheory.LKMid.CentPos

namespace GlobalTheory.LKMid


open GlobalTheory.LKMid.CentPos in
theorem cent_sim_pos : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (μ : ℂ), G.a = 1 → P.Mark μ →
    ∀ y ∈ P.cent, 0 < ((y.2 : ℚˣ) : ℚ) := by
  intro p _ G P μ _ hm y hy
  obtain ⟨v, -, x, hx, hpos⟩ := hm
  set H := G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C) with hHdef
  set M := G.psi v (P.γ : G.C) with hMdef
  set Y := G.psi v (y.1 : G.C) with hYdef
  have hc : (y.1 : G.C) * P.γ = P.γ * y.1 := by
    have := congrArg Units.val hy.1; simpa using this
  have hMY : M * Y = Y * M := by rw [hMdef, hYdef, ← map_mul, ← map_mul, hc]
  have hform : Yᴴ * H * Y = (((y.2 : ℚˣ) : ℚ) : ℂ) • H := cent_form_law G P v y hy
  obtain ⟨Z, lam, hinj, -, hZ⟩ := psi_eigenbasis p G P v
  have hx0 : x ≠ 0 := by rintro rfl; simp at hpos
  have hYx : M *ᵥ (Y *ᵥ x) = μ • (Y *ᵥ x) := by
    rw [mulVec_mulVec, hMY, ← mulVec_mulVec, hx, mulVec_smul]
  obtain ⟨l, hl⟩ := eq_smul_of_eigen M Z lam hinj hZ μ x (Y *ᵥ x) hx hYx hx0
  have key : star (Y *ᵥ x) ⬝ᵥ (H *ᵥ (Y *ᵥ x)) = star x ⬝ᵥ ((Yᴴ * H * Y) *ᵥ x) := by
    rw [star_mulVec, mulVec_mulVec, dotProduct_mulVec, dotProduct_mulVec, vecMul_vecMul]
    simp only [hHdef, Matrix.mul_assoc]
  rw [hform, hl] at key
  simp only [Matrix.smul_mulVec, mulVec_smul, star_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul] at key
  set q := star x ⬝ᵥ (H *ᵥ x) with hq
  have hq0 : q ≠ 0 := by intro h; rw [h] at hpos; simp at hpos
  have hs : star l * l = (((y.2 : ℚˣ) : ℚ) : ℂ) := by
    rw [← mul_assoc] at key; have := mul_right_cancel₀ hq0 key; rw [mul_comm] at this; exact this
  have hsre : ((((y.2 : ℚˣ) : ℚ) : ℂ)).re = ((y.2 : ℚˣ) : ℚ) := by simp
  have hnn : (0 : ℝ) ≤ (((y.2 : ℚˣ) : ℚ) : ℝ) := by
    have : (star l * l).re = Complex.normSq l := by
      rw [mul_comm, Complex.star_def, Complex.mul_conj]; simp
    rw [hs] at this
    have h2 : ((((y.2 : ℚˣ) : ℚ) : ℂ)).re = (((y.2 : ℚˣ) : ℚ) : ℝ) := by simp
    rw [← h2, this]; exact Complex.normSq_nonneg l
  have hnn' : (0 : ℚ) ≤ ((y.2 : ℚˣ) : ℚ) := by exact_mod_cast hnn
  exact lt_of_le_of_ne hnn' (Ne.symm (y.2.ne_zero))

end GlobalTheory.LKMid
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.marked_similitude_pair_minpoly_roots_normSq_eq : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (μ : ℂ), G.a = 1 → P.Mark μ → ∀ (φ : G.F →+* ℂ) (z : ℂ), P.pol.eval₂ φ z = 0 → ‖z‖ ^ 2 = ((P.c : ℚ) : ℝ) := by
  first | (exact @GlobalTheory.LKMid.MarkEll.mark_ell) | (exact GlobalTheory.LKMid.MarkEll.mark_ell) | (intros; apply GlobalTheory.LKMid.MarkEll.mark_ell  <;> assumption)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid

theorem Pair.mark_norm_sq : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (μ : ℂ), P.Mark μ →
    ‖μ‖ ^ 2 = ((P.c : ℚ) : ℝ) := by
  intro p _ G P μ hμ
  obtain ⟨v, _, x, hx, hpos⟩ := hμ
  obtain ⟨_, _, hlaw⟩ := GlobalTheory.T.similitudePair_hermitianForm_invertible_similitude p G P v
  set H := G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C) with hH
  set A := G.psi v (P.γ : G.C) with hA
  set q : ℂ := star x ⬝ᵥ (H *ᵥ x) with hq
  have hq0 : q ≠ 0 := by
    intro h0; rw [h0] at hpos; simp at hpos
  have key : star x ⬝ᵥ ((Aᴴ * H * A) *ᵥ x) = (star μ * μ) * q := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, hx, dotProduct_mulVec, ← star_mulVec, hx, mulVec_smul, star_smul,
      smul_dotProduct, dotProduct_smul, hq]
    simp only [smul_eq_mul]; ring
  rw [hlaw, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at key
  have hc : star μ * μ = ((P.c : ℚ) : ℂ) := by
    have := mul_right_cancel₀ hq0 key.symm
    exact this
  have h2 : ((‖μ‖ ^ 2 : ℝ) : ℂ) = ((((P.c : ℚ) : ℝ)) : ℂ) := by
    rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
    push_cast
    exact hc
  exact_mod_cast h2

end GlobalTheory.LKMid
end

section

open Matrix GlobalTheory.LKRes GlobalTheory.LKMid
open scoped TensorProduct

theorem _root_.GlobalTheory.T.twisted_conj_of_twistedNorm_eq_GL_one_unramified : ∀ (p : ℕ) [Fact p.Prime] (r : ℕ), 0 < r → ∀ δ δ' : GL (Fin 1) (Qr p r), nrmG (GlobalTheory.LKLoc.sig p (Q0 p) 1 r) r δ = nrmG (GlobalTheory.LKLoc.sig p (Q0 p) 1 r) r δ' → ∃ h : GL (Fin 1) (Qr p r), δ' = h⁻¹ * δ * GlobalTheory.LKLoc.sig p (Q0 p) 1 r h := by
  first | (exact @GlobalTheory.LKMid.exists_sig_twisted_conj_of_nrmG_eq) | (exact GlobalTheory.LKMid.exists_sig_twisted_conj_of_nrmG_eq) | (intros; apply GlobalTheory.LKMid.exists_sig_twisted_conj_of_nrmG_eq  <;> assumption)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory

theorem nrm_exact : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), (∀ (r : ℕ) (γ : Gp G) (δ z : Gr G r), 0 < r →
    IsNrm G r γ δ z → IsNrm G r γ (z * δ * (sigG G r z)⁻¹) 1) ∧ ∀ γ : Gp G, IsNrm G 1 γ (inclG G 1 γ) 1 := by
  intro p _ G
  refine ⟨fun r γ δ z hr h => ?_, fun γ => ?_⟩
  · unfold IsNrm at h ⊢
    have e := (GlobalTheory.T.twistedNormProductIterate_twistedConj (sigG G r) r δ z⁻¹).1
    have hit := (GlobalTheory.T.hermitianTripleFrobeniusTwist_order_fixed_points p G r hr).1 z⁻¹
    rw [inv_inv] at e
    rw [← map_inv, e, h, hit]
    group
  · unfold IsNrm nrmG
    simp
end GlobalTheory
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section
namespace GlobalTheory.AwayPDen

theorem continuous_charpoly_coeff {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (n i : ℕ) :
    Continuous fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i := by
  have h : (fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i) =
      fun M => MvPolynomial.eval (fun ij : Fin n × Fin n => M ij.1 ij.2)
        ((Matrix.charpoly.univ K (Fin n)).coeff i) := by
    funext M
    exact (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id K) (fun ij : Fin n × Fin n => M ij.1 ij.2) i).symm
  rw [h]
  exact (MvPolynomial.continuous_eval _).comp
    (continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))

theorem charpoly_den_bounded : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (Ω : Set G.GAf), IsCompact Ω → ∃ D : ℕ, 0 < D ∧ ∀ (g : G.GAf) (y : G.C) (x : (AfP p ⊗[ℚ] G.C)ˣ), g ∈ Ω → (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : AfP p ⊗[ℚ] G.C) = (x : AfP p ⊗[ℚ] G.C) * inC G (AfP p) y * ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C)) → ∀ i, ∃ k : ℕ, ∃ a : ℤ, ((D * p ^ k : ℕ) : ℚ) * (LinearMap.mulLeft ℚ y).charpoly.coeff i = a := by
  intro p _ G Ω hΩ
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  haveI : IsModuleTopology (AfP p) (AfP p ⊗[ℚ] G.C) := ⟨rfl⟩
  set d := Module.finrank ℚ G.C
  let φ : G.GAf → AfP p ⊗[ℚ] G.C := fun g => ((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : AfP p ⊗[ℚ] G.C)
  have hφ : Continuous φ := Units.continuous_val.comp (continuous_fst.comp continuous_subtype_val)
  let F : ℕ → AfP p ⊗[ℚ] G.C → AfP p := fun i a => (LevelExists.mulMatAlg (AfP p) G.C a).charpoly.coeff i
  have hF : ∀ i, Continuous (F i) := fun i =>
    (continuous_charpoly_coeff d i).comp
      (IsModuleTopology.continuous_of_linearMap (LevelExists.mulMatAlg (AfP p) G.C).toLinearMap)
  let S : Set (AfP p) := ⋃ i ∈ Finset.range (d + 1), (F i ∘ φ) '' Ω
  have hS : IsCompact S := (Finset.range (d + 1)).isCompact_biUnion fun i _ => hΩ.image ((hF i).comp hφ)
  obtain ⟨D, hD0, hD⟩ := GlobalTheory.T.exists_common_pos_denominator_of_isCompact_finiteAdeleAway p S hS
  refine ⟨D, hD0, fun g y x hg hx i => ?_⟩
  by_cases hi : i ≤ d
  · have hmem : F i (φ g) ∈ S :=
      Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_range.2 (Nat.lt_succ_of_le hi))) ⟨g, hg, rfl⟩
    have hval : F i (φ g) = algebraMap ℚ (AfP p) ((LinearMap.mulLeft ℚ y).charpoly.coeff i) := by
      show (LevelExists.mulMatAlg (AfP p) G.C (φ g)).charpoly.coeff i = _
      rw [show φ g = _ from hx]
      have := GlobalTheory.T.charpoly_tensorLeftMul_conj_one_tmul (AfP p) G.C x y
      simp only [inC] at *
      rw [show ((Algebra.TensorProduct.includeRight : G.C →ₐ[ℚ] AfP p ⊗[ℚ] G.C) : G.C →+* AfP p ⊗[ℚ] G.C) y = 1 ⊗ₜ[ℚ] y from rfl]
      rw [this, Polynomial.coeff_map]
    have h2 := hD _ hmem
    rw [hval] at h2
    have h3 : algebraMap ℚ (AfP p) ((D : ℚ) * (LinearMap.mulLeft ℚ y).charpoly.coeff i) ∈ LevelExists.intAfP p := by
      rw [map_mul, map_natCast]; exact h2
    obtain ⟨k, a, ha⟩ := GlobalTheory.T.exists_primePow_mul_eq_int_of_integral_finiteAdeleAway p _ h3
    exact ⟨k, a, by rw [← ha]; push_cast; ring⟩
  · refine ⟨0, 0, ?_⟩
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [LinearMap.charpoly_natDegree]; omega)]
    simp

end GlobalTheory.AwayPDen
end
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.bounded_coordinates_p_power_denominator : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (B : ℝ), ∃ e : ℕ, ∀ c : G.C, (∀ (w : Fin G.m) (a b : Fin G.n), ‖((G.rho w c a b : G.Fw w) : PadicAlgCl p)‖ ≤ B ∧ ‖((G.rho w (sh G c) a b : G.Fw w) : PadicAlgCl p)‖ ≤ B) → ∀ i, ∃ (k : ℤ) (m : ℕ), ¬ p ∣ m ∧ (Module.finBasis ℚ G.C).repr c i * (p : ℚ) ^ e = k / m := by
  first | (exact @GlobalTheory.CoordP.coord_bound) | (exact GlobalTheory.CoordP.coord_bound) | (intros; apply GlobalTheory.CoordP.coord_bound <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

namespace GlobalTheory.HSCore

theorem nef_big_baseChange : ∀ (F : Type) [Field F] [NumberField F] (X : Data F) (E : Type) [Field E] [NumberField E] [Algebra F E], IsNef F X.LA → IsBig F X.LA → IsNef E (X.baseChange E).LA ∧ IsBig E (X.baseChange E).LA := by
  intro F _ _ X E _ _ _ hn hb
  exact ⟨GlobalTheory.HilbertSamuel.Geo.isNef_baseChange X.toGeo E hn, GlobalTheory.HilbertSamuel.Geo.isBig_baseChange X.toGeo E hb⟩

end GlobalTheory.HSCore
end

section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

namespace GlobalTheory.HSShort

theorem nef_big_second_baseChange : ∀ (F : Type) [Field F] [NumberField F] (X : Data F) (E : Type) [Field E] [NumberField E] [Algebra F E], IsNef F X.L₂ → IsBig F X.L₂ → IsNef E (X.baseChange E).L₂ ∧ IsBig E (X.baseChange E).L₂ := by
  intro F _ _ X E _ _ _ hn hb
  exact ⟨PosBaseChange.isNef_baseChange (X.toGeo.isPullback_fst E) X.geom.alg.variety.proj hn,
    PosBaseChange.isBig_baseChange (X.toGeo.isPullback_fst E) X.geom.alg.variety.proj hb⟩

end GlobalTheory.HSShort
end

section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

set_option autoImplicit false

namespace GlobalTheory.HSElim

attribute [local instance] MvPolynomial.gradedAlgebra

theorem aeval_eq_zero_of_point {F K : Type} [Field F] [Field K] [Algebra F K] [IsAlgClosure F K]
    {N e δ : ℕ} {P : Ideal (MvPolynomial (Fin N) F)} {f : MvPolynomial (Fin (e + 1) × Fin N) F}
    (hf : IsChowFormInt P e δ f) (s : Fin (e + 1) → Fin N → K) (y : Fin N → K) (hy : y ≠ 0)
    (hyP : ∀ a ∈ P, aeval y a = 0) (hs : ∀ i, ∑ j, s i j * y j = 0) :
    aeval (fun p : Fin (e + 1) × Fin N => s p.1 p.2) f = 0 := by
  let φ : K ≃ₐ[F] AlgebraicClosure F := IsAlgClosure.equiv F K (AlgebraicClosure F)
  have hmap : ∀ {σ : Type} (x : σ → K) (a : MvPolynomial σ F),
      aeval (fun i => φ (x i)) a = φ (aeval x a) := fun x a =>
    (AlgHom.congr_fun (MvPolynomial.comp_aeval (f := x) (φ : K →ₐ[F] AlgebraicClosure F)) a).symm
  have key : aeval (fun p : Fin (e + 1) × Fin N => φ (s p.1 p.2)) f = 0 := by
    refine (hf.zero_iff _).2 ⟨fun j => φ (y j), ?_, fun a ha => ?_, fun i => ?_⟩
    · intro h
      apply hy
      funext j
      have := congrFun h j
      simpa using this
    · rw [hmap, hyP a ha, map_zero]
    · have := congrArg φ (hs i)

      simpa [map_sum, map_mul] using this
  rw [hmap (fun p : Fin (e + 1) × Fin N => s p.1 p.2)] at key
  simpa using key

theorem exists_elim_form : ∀ (F : Type) [Field F] [CharZero F] (D N d : ℕ)
    (I : Ideal (MvPolynomial (Fin N) F)) (g : MvPolynomial (Fin N) F), 1 ≤ D → I.IsPrime →
    (∀ a ∈ I, ∀ n : ℕ, homogeneousComponent n a ∈ I) →
    ringKrullDim (MvPolynomial (Fin N) F ⧸ I) = (D + 1 : ℕ) → g.IsHomogeneous d → g ∉ I →
    ∃ Q : MvPolynomial (Fin D × Fin N) F, Q ≠ 0 ∧ Q.totalDegree ≤ D * d * hilbertDegree I ∧
      ∀ (K : Type) [Field K] [Algebra F K] [IsAlgClosure F K] (s : Fin D → Fin N → K)
        (y : Fin N → K), y ≠ 0 → (∀ a ∈ I, aeval y a = 0) → aeval y g = 0 →
        (∀ i, ∑ j, s i j * y j = 0) → aeval (fun p : Fin D × Fin N => s p.1 p.2) Q = 0 := by
  intro F _ _ D N d I g hD hp hcomp hdim hg hgI
  obtain ⟨e, rfl⟩ : ∃ e, D = e + 1 := ⟨D - 1, by omega⟩
  have hIh := GlobalTheory.ChowExists.isHomogeneous_of_component hcomp
  obtain ⟨f0, hf0⟩ := GlobalTheory.ChowExists.exists_isChowFormInt hp hIh hdim
  obtain ⟨i0, hi0⟩ := GlobalTheory.ChowExists.exists_X_notMem hf0
  have hJh := isHomogeneous_sup_span_singleton hIh hg
  have hex : ∀ P ∈ (finite_projComponents (I ⊔ Ideal.span {g})).toFinset,
      ∃ f : MvPolynomial (Fin (e + 1) × Fin N) F, IsChowFormInt P e (hilbertDegree P) f := by
    intro P hP
    rw [Set.Finite.mem_toFinset] at hP
    have hPp := hP.1.1.1
    obtain ⟨e', h1, h2⟩ := ringKrullDim_of_mem_projComponents_sup hIh hdim hg hgI hP
    obtain rfl : e = e' := by omega
    exact GlobalTheory.ChowExists.exists_isChowFormInt hPp (isHomogeneous_of_mem_projComponents hJh hP) h2
  choose! f hf using hex
  refine ⟨∏ P ∈ (finite_projComponents (I ⊔ Ideal.span {g})).toFinset, f P, ?_, ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.2 fun P hP => (hf P hP).ne_zero
  · refine (totalDegree_finsetProd _ _).trans ?_
    have h1 : ∑ P ∈ (finite_projComponents (I ⊔ Ideal.span {g})).toFinset, (f P).totalDegree =
        (e + 1) * projSetDegree (I ⊔ Ideal.span {g}) := by
      rw [projSetDegree, Finset.mul_sum]
      exact Finset.sum_congr rfl fun P hP => GlobalTheory.ChowSection.totalDegree_of_isChowFormInt (hf P hP)
    rw [h1, mul_assoc]
    exact Nat.mul_le_mul_left _ (projSetDegree_sup_le_of_isPrime hIh hi0 hg hgI)
  · intro K _ _ _ s y hy hyI hyg hs
    rw [map_prod]
    let Jy : Ideal (MvPolynomial (Fin N) F) := RingHom.ker (aeval y : MvPolynomial (Fin N) F →ₐ[F] K)
    have hJy : I ⊔ Ideal.span {g} ≤ Jy := sup_le (fun a ha => (RingHom.mem_ker).2 (hyI a ha))
      ((Ideal.span_singleton_le_iff_mem _).2 ((RingHom.mem_ker).2 hyg))
    have : Jy.IsPrime := RingHom.ker_isPrime _
    obtain ⟨P, hPmin, hPle⟩ := Ideal.exists_minimalPrimes_le hJy
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hy
    have hPc : P ∈ projComponents (I ⊔ Ideal.span {g}) :=
      ⟨hPmin, i, fun h => hi (by simpa using (RingHom.mem_ker).1 (hPle h))⟩
    have hPf : P ∈ (finite_projComponents (I ⊔ Ideal.span {g})).toFinset :=
      (Set.Finite.mem_toFinset _).2 hPc
    exact Finset.prod_eq_zero hPf (aeval_eq_zero_of_point (hf P hPf) s y hy
      (fun a ha => (RingHom.mem_ker).1 (hPle ha)) hs)

end GlobalTheory.HSElim
end

section

open Matrix GlobalTheory.LKTrip

theorem _root_.GlobalTheory.T.exists_posDef_majorant_of_positiveIndex_one : ∀ {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian), H.det ≠ 0 → sigPosH hH = 1 → ∀ z : Fin n → ℂ, 0 < (star z ⬝ᵥ H *ᵥ z).re → ∃ P : Matrix (Fin n) (Fin n) ℂ, P.IsHermitian ∧ (∀ x : Fin n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ P *ᵥ x).re) ∧ ∀ (Y : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) (c : ℂ), 0 < s → Yᴴ * H * Y = (s : ℂ) • H → Y *ᵥ z = c • z → Yᴴ * P * Y = (s : ℂ) • P := by
  first | (exact @GlobalTheory.exists_posDef_majorant_of_sigPosH_eq_one) | (exact GlobalTheory.exists_posDef_majorant_of_sigPosH_eq_one) | (intros; apply GlobalTheory.exists_posDef_majorant_of_sigPosH_eq_one  <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isPerfectPair_of_geometric_fibres : ∀ (R : Type) [CommRing R] (M N : Type 1) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M] [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Projective R N] (φ : Module.Dual R M →ₗ[R] Module.Dual R N →ₗ[R] R), (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra R Ω], ∃ (M' N' : Type 1) (_ : AddCommGroup M') (_ : Module Ω M') (_ : AddCommGroup N') (_ : Module Ω N') (f : M →ₛₗ[algebraMap R Ω] M') (f' : N →ₛₗ[algebraMap R Ω] N') (φ' : Module.Dual Ω M' →ₗ[Ω] Module.Dual Ω N' →ₗ[Ω] Ω), Function.Bijective (liftSemi f) ∧ Function.Bijective (liftSemi f') ∧ φ'.IsPerfPair ∧ ∀ (x : Module.Dual R M) (x' : Module.Dual Ω M') (y : Module.Dual R N) (y' : Module.Dual Ω N'), (∀ c, x' (f c) = algebraMap R Ω (x c)) → (∀ c, y' (f' c) = algebraMap R Ω (y c)) → φ' x' y' = algebraMap R Ω (φ x y)) → φ.IsPerfPair := by
  first | exact @GlobalTheory.PairFibres.isPerfPair_of_fibres₂ | exact GlobalTheory.PairFibres.isPerfPair_of_fibres₂ | (intros; apply GlobalTheory.PairFibres.isPerfPair_of_fibres₂ <;> assumption)
end
