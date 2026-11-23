module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualOrthAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle415
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle416
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle417
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.MonoBes

variable {D : D7}

theorem colMul_pX {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (i : Fin ρ) (y : Fin S.rank → AE D) :
    GlobalTheory.FinPl.colMul d.jX i ((d.pX *ᵥ y) i) = rat (fun k l => d.e k i * d.qX i l) *ᵥ y := by
  funext k
  simp only [GlobalTheory.FinPl.colMul, HypDec.jX, HypDec.pX, rat, mulVec, dotProduct, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  show (incA D) (d.qX i l) * y l * (incA D) (d.e k i) = (incA D) (d.e k i * d.qX i l) * y l
  rw [map_mul]
  ring

theorem colMul_pY {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (i : Fin ρ) (y : Fin S.rank → AE D) :
    GlobalTheory.FinPl.colMul d.jY i ((d.pY *ᵥ y) i) = rat (fun k l => d.e' k i * d.qY i l) *ᵥ y := by
  funext k
  simp only [GlobalTheory.FinPl.colMul, HypDec.jY, HypDec.pY, rat, mulVec, dotProduct, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  show (incA D) (d.qY i l) * y l * (incA D) (d.e' k i) = (incA D) (d.e' k i * d.qY i l) * y l
  rw [map_mul]
  ring

theorem mulVec_eq_sum_colMul {m n : ℕ} (x : Mx D m n) (w : Fin n → AE D) :
    x *ᵥ w = ∑ i, GlobalTheory.FinPl.colMul x i (w i) := by
  funext k
  simp only [mulVec, dotProduct, GlobalTheory.FinPl.colMul, Finset.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem mulVec_eq_sum_col {m n : ℕ} (x : Matrix (Fin m) (Fin n) D.host.E) (w : Fin n → D.host.E) :
    x *ᵥ w = ∑ i, fun k => x k i * w i := by
  funext k
  simp only [mulVec, dotProduct, Finset.sum_apply]

theorem rank_one_mulVec {m n k : ℕ} (a : Matrix (Fin m) (Fin k) D.host.E) (b : Matrix (Fin k) (Fin n) D.host.E)
    (i : Fin k) (x : Fin n → D.host.E) : (fun r l => a r i * b i l) *ᵥ x = fun r => a r i * (b *ᵥ x) i := by
  funext r
  simp only [mulVec, dotProduct, Finset.mul_sum, mul_assoc]

theorem monoAt_of_proj {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (L : Lat S)
    (hX : ∀ i, ∀ x ∈ L, (fun k => d.e k i * (d.qX *ᵥ x) i) ∈ L)
    (hY : ∀ i, ∀ x ∈ L, (fun k => d.e' k i * (d.qY *ᵥ x) i) ∈ L) (v : GlobalTheory.FinPl.Pl D) :
    MonoAt d L (L.comap ((Matrix.mulVecLin d.i₀).restrictScalars (𝓞 D.host.E))) v := by
  have h0 : ∀ x ∈ L, d.i₀ *ᵥ (d.q0 *ᵥ x) ∈ L := by
    intro x hx
    have e : d.i₀ *ᵥ (d.q0 *ᵥ x) = x - d.e *ᵥ (d.qX *ᵥ x) - d.e' *ᵥ (d.qY *ᵥ x) := by
      have := congrArg (· *ᵥ x) d.sum_eq_one_rat
      simp only [add_mulVec, one_mulVec, ← mulVec_mulVec] at this
      rw [sub_sub, eq_sub_iff_add_eq]
      calc _ = d.e *ᵥ (d.qX *ᵥ x) + d.i₀ *ᵥ (d.q0 *ᵥ x) + d.e' *ᵥ (d.qY *ᵥ x) := by abel
        _ = x := this
    rw [e, mulVec_eq_sum_col d.e, mulVec_eq_sum_col d.e']
    exact L.sub_mem (L.sub_mem hx (L.sum_mem fun i _ => hX i x hx)) (L.sum_mem fun i _ => hY i x hx)
  intro y
  constructor
  · intro hy
    refine ⟨fun i => ?_, fun i => ?_, ?_⟩
    · rw [colMul_pX]; exact GlobalTheory.OrthSumLat.rat_mulVec_mem_latV _ (fun x hx => by rw [rank_one_mulVec]; exact hX i x hx) hy
    · rw [colMul_pY]; exact GlobalTheory.OrthSumLat.rat_mulVec_mem_latV _ (fun x hx => by rw [rank_one_mulVec]; exact hY i x hx) hy
    · exact GlobalTheory.OrthSumLat.rat_mulVec_mem_latV d.q0 h0 hy
  · rintro ⟨h1, h2, h3⟩
    have e : y = d.jX *ᵥ (d.pX *ᵥ y) + d.j0 *ᵥ (d.p0 *ᵥ y) + d.jY *ᵥ (d.pY *ᵥ y) := by
      have h : d.jX * d.pX + d.j0 * d.p0 + d.jY * d.pY = 1 := by
        have h := congrArg rat d.sum_eq_one_rat
        rw [rat_add, rat_add, rat_one] at h
        simpa only [HypDec.jX, HypDec.j0, HypDec.jY,
          HypDec.pX, HypDec.p0, HypDec.pY, rat, Matrix.map_mul] using h
      have := congrArg (· *ᵥ y) h
      simp only [add_mulVec, one_mulVec, ← mulVec_mulVec] at this
      exact this.symm
    rw [e, mulVec_eq_sum_colMul d.jX, mulVec_eq_sum_colMul d.jY]
    refine add_mem (add_mem (AddSubgroup.sum_mem _ fun i _ => h1 i) ?_) (AddSubgroup.sum_mem _ fun i _ => h2 i)
    exact GlobalTheory.OrthSumLat.rat_mulVec_mem_latV d.i₀ (fun x hx => hx) h3

section SlopeTestRemainingChoices

variable {A B B₀ : HSp D} {c ρ : ℕ}

theorem antiDiagonalEpsilonGram_mulVec_of_rev_ne (ε : D.host.E) (u : Fin c → D.host.E) (j : Fin c) (hj : j.rev ≠ j) :
    (antiDiagonalSignGramMatrix c ε *ᵥ u) j = u j.rev := by
  simp only [mulVec, dotProduct, antiDiagonalSignGramMatrix]
  rw [Finset.sum_eq_single j.rev]
  · rw [if_pos (by simp only [Fin.val_rev]; omega), if_neg (Ne.symm hj), one_mul]
  · intro b _ hb
    rw [if_neg, zero_mul]
    intro h
    apply hb
    ext
    simp only [Fin.val_rev]
    omega
  · intro h; exact absurd (Finset.mem_univ _) h

theorem mulVec_single_apply {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (j : Fin n) (x : D.host.E) (k : Fin m) :
    (M *ᵥ Pi.single j x) k = M k j * x := by
  simp [mulVec, dotProduct, Pi.single_apply]

theorem auxiliaryVectors_pairing_eq_antiDiagonal_gram (a : HermitianOrthogonalExtensionData A B c (-1)) (y : Fin A.rank → D.host.E) (u : Fin c → D.host.E) :
    (a.aᴴ * B.gram) *ᵥ (frameMat B A a.ι *ᵥ y + a.a *ᵥ u) = antiDiagonalSignGramMatrix c (-1) *ᵥ u := by
  have hG : B.gramᴴ = B.gram := Matrix.ext fun i j => B.herm.eq _ _
  have h1 : a.aᴴ * B.gram * frameMat B A a.ι = 0 := by
    have h := congrArg Matrix.conjTranspose a.perp
    change ((frameMat B A a.ι)ᴴ * B.gram * a.a)ᴴ = 0ᴴ at h
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hG, Matrix.conjTranspose_zero,
      Matrix.mul_assoc] using h
  have h2 : a.aᴴ * B.gram * a.a = antiDiagonalSignGramMatrix c (-1) := a.gram
  rw [mulVec_add, mulVec_mulVec, mulVec_mulVec, h1, h2, zero_mulVec, zero_add]

theorem proj_mem (a : HermitianOrthogonalExtensionData A B c (-1)) (d : HypDec B B₀ ρ) (hd : IsAuxiliaryVectorWittDec a d) (Λ : Lat A)
    (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :
    (∀ i, ∀ x ∈ a.lat Λ 𝔟, (fun k => d.e k i * (d.qX *ᵥ x) i) ∈ a.lat Λ 𝔟) ∧
      (∀ i, ∀ x ∈ a.lat Λ 𝔟, (fun k => d.e' k i * (d.qY *ᵥ x) i) ∈ a.lat Λ 𝔟) := by
  obtain ⟨hc, he, s, he'⟩ := hd
  have hrev : ∀ i : Fin ρ, (Fin.castLE (by omega) i : Fin c).rev ≠ Fin.castLE (by omega) i := by
    intro i h
    have := congrArg Fin.val h
    simp only [Fin.val_rev, Fin.val_castLE] at this
    have := i.2
    omega
  have qX_eq : ∀ x (i : Fin ρ),
      (d.qX *ᵥ x) i = star (s i) * ((a.aᴴ * B.gram) *ᵥ x) (Fin.castLE (by omega) i : Fin c).rev := by
    intro x i
    rw [HypDec.qX, he', ← mulVec_mulVec, ← mulVec_mulVec]
    simp only [mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [conjTranspose_apply, colsOf, star_mul']
    ring_nf
  have qY_eq : ∀ x (i : Fin ρ),
      (d.qY *ᵥ x) i = star ((-D.host.xi0) ^ (i.1 + 1)) * ((a.aᴴ * B.gram) *ᵥ x) (Fin.castLE (by omega) i : Fin c) := by
    intro x i
    rw [HypDec.qY, he, ← mulVec_mulVec, ← mulVec_mulVec]
    simp only [mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [conjTranspose_apply, colsOf, star_mul']
    ring_nf
  have scal : ∀ i : Fin ρ, star (s i) * (-D.host.xi0) ^ (i.1 + 1) = 1 := by
    intro i
    have h1 : (fun k => d.e k i) =
        frameMat B A a.ι *ᵥ 0 + a.a *ᵥ Pi.single (Fin.castLE (by omega) i : Fin c) ((-D.host.xi0) ^ (i.1 + 1)) := by
      funext k
      show _ = (frameMat B A a.ι *ᵥ 0 + a.a *ᵥ _) k
      rw [he, mulVec_zero, zero_add, mulVec_single_apply]
      simp only [colsOf]
      ring
    have h2 : (d.e'ᴴ * B.gram * d.e) i i = (d.qX *ᵥ fun k => d.e k i) i := rfl
    have h3 := congrFun (congrFun d.e'e i) i
    rw [h2, h1, qX_eq, auxiliaryVectors_pairing_eq_antiDiagonal_gram, antiDiagonalEpsilonGram_mulVec_of_rev_ne _ _ _ (by rw [Fin.rev_rev]; exact (hrev i).symm), Fin.rev_rev, Pi.single_eq_same,
      Matrix.one_apply_eq] at h3
    exact h3
  refine ⟨fun i x hx => ?_, fun i x hx => ?_⟩
  · obtain ⟨y, hy, u, hu, rfl⟩ := hx
    refine ⟨0, Λ.zero_mem, Pi.single (Fin.castLE (by omega) i : Fin c) (u (Fin.castLE (by omega) i)), fun p => ?_, ?_⟩
    · by_cases hp : p = Fin.castLE (by omega) i
      · subst hp; rw [Pi.single_eq_same]; exact hu _
      · rw [Pi.single_eq_of_ne hp]; exact (𝔟 p).zero_mem
    · funext k
      show _ = (frameMat B A a.ι *ᵥ 0 + a.a *ᵥ _) k
      rw [qX_eq, auxiliaryVectors_pairing_eq_antiDiagonal_gram, antiDiagonalEpsilonGram_mulVec_of_rev_ne _ _ _ (by rw [Fin.rev_rev]; exact (hrev i).symm), Fin.rev_rev, mulVec_zero,
        zero_add, mulVec_single_apply, he]
      simp only [colsOf]
      linear_combination (a.a k (Fin.castLE (by omega) i) * u (Fin.castLE (by omega) i)) * scal i
  · obtain ⟨y, hy, u, hu, rfl⟩ := hx
    refine ⟨0, Λ.zero_mem, Pi.single (Fin.castLE (by omega) i : Fin c).rev (u (Fin.castLE (by omega) i : Fin c).rev),
      fun p => ?_, ?_⟩
    · by_cases hp : p = (Fin.castLE (by omega) i : Fin c).rev
      · subst hp; rw [Pi.single_eq_same]; exact hu _
      · rw [Pi.single_eq_of_ne hp]; exact (𝔟 p).zero_mem
    · have hs : s i * star ((-D.host.xi0) ^ (i.1 + 1)) = 1 := by
        have := congrArg star (scal i)
        rw [star_mul', star_star, star_one] at this
        exact this
      funext k
      show _ = (frameMat B A a.ι *ᵥ 0 + a.a *ᵥ _) k
      rw [qY_eq, auxiliaryVectors_pairing_eq_antiDiagonal_gram, antiDiagonalEpsilonGram_mulVec_of_rev_ne _ _ _ (hrev i), mulVec_zero, zero_add, mulVec_single_apply, he']
      simp only [colsOf]
      linear_combination (a.a k (Fin.castLE (by omega) i : Fin c).rev * u (Fin.castLE (by omega) i : Fin c).rev) * hs

end SlopeTestRemainingChoices

theorem monoAt_bes : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (F : GlobalTheory.Asc.Frames G), Std F → ∀ (ρ : ℕ) (h : 2 * ρ + 2 ≤ D.R.m) (v : GlobalTheory.FinPl.Pl D), MonoAt (F.dB ρ h) (G.Λ (.grid (2 * ρ + 2) 0)) (lat0 F ρ h) v := by
  intro D T L sc G F hF ρ h v
  have hL : G.Λ (.grid (2 * ρ + 2) 0) = (G.colDec (2 * ρ + 2) (by omega) h).lat (G.Λ (.core (2 * ρ + 2)))
      (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1)) := G.sp.colLat _ _ h
  obtain ⟨hX, hY⟩ := proj_mem (G.colDec (2 * ρ + 2) (by omega) h) (F.dB ρ h) (hF.hB ρ h) (G.Λ (.core (2 * ρ + 2)))
    (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1))
  rw [← hL] at hX hY
  exact monoAt_of_proj (F.dB ρ h) _ hX hY v

end GlobalTheory.MonoBes

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.isSelfDual_besselCoreVertexLattice : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (F : GlobalTheory.Asc.Frames G), Std F → ∀ (ρ : ℕ) (h : 2 * ρ + 2 ≤ D.R.m), IsSelfDualC (F.V₀ ρ) (lat0 F ρ h) := by
  first | exact @GlobalTheory.AscFin.isSelfDualC_lat0 | exact GlobalTheory.AscFin.isSelfDualC_lat0 | (intros; apply GlobalTheory.AscFin.isSelfDualC_lat0 <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.proj_X_preserves_embedding_lattice : ∀ {D : D7} {A B B₀ : HSp D} {c ρ : ℕ} (a : HermitianOrthogonalExtensionData A B c (-1)) (d : HypDec B B₀ ρ), IsAuxiliaryVectorWittDec a d → ∀ (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (v : Fin B.rank → D.host.E), v ∈ a.lat Λ 𝔟 → (d.e * d.qX) *ᵥ v ∈ a.lat Λ 𝔟 := by
  first | exact @GlobalTheory.projX_embedding_lattice | exact GlobalTheory.projX_embedding_lattice | (intros; apply GlobalTheory.projX_embedding_lattice <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin




theorem _root_.GlobalTheory.T.auxiliaryWittIsotropicCoordinate_eq_pairing : ∀ {D : D7} {A B B₀ : HSp D} {c ρ : ℕ} (a : HermitianOrthogonalExtensionData A B c (-1)) (d : HypDec B B₀ ρ), c = 2 * ρ → IsAuxiliaryVectorWittDec a d → ∀ (i : Fin ρ) (hi : 2 * ρ - 1 - i.1 < c) (x : Fin B.rank → AE D), incA D ((-D.host.xi0) ^ (i.1 + 1)) * (d.pX *ᵥ x) i = ∑ k, ∑ l, cA D (incA D (a.a k ⟨2 * ρ - 1 - i.1, hi⟩)) * incA D (B.gram k l) * x l := by
  first | exact @GlobalTheory.AscFin.incA_neg_xi0_pow_mul_pX_mulVec_eq_sum | exact GlobalTheory.AscFin.incA_neg_xi0_pow_mul_pX_mulVec_eq_sum | (intros; apply GlobalTheory.AscFin.incA_neg_xi0_pow_mul_pX_mulVec_eq_sum <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel

theorem _root_.GlobalTheory.T.besselStep_basePoint_scaled_coordinates : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m), ∀ v ∈ G.pl.S0, ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : GlobalTheory.FinPl.SplitPt D k) (β : GlobalTheory.FinPl.Frame p (G.V (.grid (2 * (σ + 1) + 1) 0)) (Fin (G.V (.grid (2 * (σ + 1) + 1) 0)).rank)) (ϖ : 𝒪[k])
    (κ : Fin (2 * (σ + 1) + 1 - 1) → Fin (G.V (.grid (2 * (σ + 1) + 1) 0)).rank),
  p.v = v →
  Formalism.L2.NTheta.IsIdemAt p.e (G.pl.w v) →
  β.IsLat (G.Λ (.grid (2 * (σ + 1) + 1) 0)) (Submodule.pi Set.univ fun _ => (1 : Submodule 𝒪[k] k)) →
  Irreducible ϖ →
  Function.Injective κ →
  (∀ r i, β.b i (κ r) = (ϖ : k) ^ (G.pl.depth sc v * (r.1 + 1)) * p.pr (incA D ((G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a i r))) →
  (∀ j, j ∉ Set.range κ → ∀ r, ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a * (G.V (.grid (2 * (σ + 1) + 1) 0)).gram).map
      (fun c => p.pr (incA D c)) * β.b) r j = 0) →
  ∃ s t : Fin (σ + 1) → k, (∀ q, s q • (β.b' *ᵥ fun i => p.pr (xZero (F.dJ (σ + 1) h) i q)) = Pi.single (κ ⟨q.1, by omega⟩) 1) ∧
    (∀ q, t q • ((fun i => p.pr (cA D (xZero (F.dJ (σ + 1) h) i q))) ᵥ*
    ((G.V (.grid (2 * (σ + 1) + 1) 0)).gram.map (fun c => p.pr (incA D c)) * β.b)) = Pi.single (κ ⟨2 * (σ + 1) - 1 - q.1, by omega⟩) 1) := by
  first | exact @GlobalTheory.FrameZero.xclauses | exact GlobalTheory.FrameZero.xclauses | (intros; apply GlobalTheory.FrameZero.xclauses <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.besselStep_coreComponent_mem_depthLatticeGridCore : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ u ∈ (pcBF W F ρ h).Γ₀, ((F.oB ρ h).resS (G.V (.core (2 * ρ + 1))) u).1 ∈ latCore G (2 * ρ + 1) := by
  first | exact @GlobalTheory.AscFin.pcBF_core_mem_latCore | exact GlobalTheory.AscFin.pcBF_core_mem_latCore | (intros; apply GlobalTheory.AscFin.pcBF_core_mem_latCore <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.proj_Y_preserves_embedding_lattice : ∀ {D : D7} {A B B₀ : HSp D} {c ρ : ℕ} (a : HermitianOrthogonalExtensionData A B c (-1)) (d : HypDec B B₀ ρ), IsAuxiliaryVectorWittDec a d → ∀ (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (v : Fin B.rank → D.host.E), v ∈ a.lat Λ 𝔟 → (d.e' * d.qY) *ᵥ v ∈ a.lat Λ 𝔟 := by
  first | exact @GlobalTheory.AscFin.projY_mem_lat | exact GlobalTheory.AscFin.projY_mem_lat | (intros; apply GlobalTheory.AscFin.projY_mem_lat <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.exists_unitriangularStabilizer_of_principal_move : ∀ {D : D7} (W : HSp D) {ρ : ℕ} (x : Mx D W.rank ρ) (Q : GlobalTheory.FinPl.Pl D → Prop) (g k : GA D W) (u : UX D ρ), g ∈ grpAt W Q → k ∈ grpAt W Q → MxOff Q (mt W k ⬝ x - mt W g⁻¹ ⬝ (x ⬝ u.1.1)) → ∃ r ∈ Rgrp W x, r ∈ grpAt W Q ∧ g = r * k⁻¹ := by
  first | exact @GlobalTheory.PrincipalMove.exists_move | exact GlobalTheory.PrincipalMove.exists_move | (intros; apply GlobalTheory.PrincipalMove.exists_move <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.flatMapNonvanishingCondition_localise : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (p : Pieces V₀ W W₀ ρ σ) (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ) (P : GlobalTheory.FinPl.Pl D → Prop) (h₁ h₂ : GA D W), h₁ ∈ grpAt W P → h₂ ∈ grpOff W P → Cond dW p x y ψ (fun _ => True) (h₁ * h₂) → Cond dW p x y ψ P h₁ := by
  first | exact @GlobalTheory.AscFin.cond_loc | exact GlobalTheory.AscFin.cond_loc | (intros; apply GlobalTheory.AscFin.cond_loc <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.isSelfDual_standardFrame_lineLattice : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (F : GlobalTheory.Asc.Frames G), Std F → IsSelfDualC (negSp F.Lz) (Submodule.span (𝓞 D.host.E) {F.ζ 0}) := by
  first | exact @GlobalTheory.AscFin.isSelfDualC_line | exact GlobalTheory.AscFin.isSelfDualC_line | (intros; apply GlobalTheory.AscFin.isSelfDualC_line <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.isotropic_condition_last_torus_diagonal_integral : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ ρ) (p : Pieces V₀ W W₀ ρ ρ) (z : Fin V₀.rank → D.host.E) (LV : Lat V) (LV₀ : Lat V₀) (LW : Lat W) (LW₀ : Lat W₀) (v : GlobalTheory.FinPl.Pl D), GoodAt dV dW (xZero dW) ψ LV LV₀ LW LW₀ v → StdAt dV dW p LV LW v → (0 < ρ → ∀ a ∈ idAt D (· = v), dW.incAdj V₀ (a • yZero V₀ ρ z) ∈ latO V₀ W (LV₀ : Set _) (LW : Set _) (· = v) ↔ a ∈ intAt D (· = v)) → ∀ t : GL (Fin ρ) (AE D), (∀ i j, i ≠ j → t.1 i j = 0) → dW.levi t ∈ grpAt W (· = v) → (∀ ξ ∈ p.B₁, ∀ ξ' : Mx D ρ V₀.rank, MxAt (· = v) ξ → mt W (dW.levi t) ⬝ dW.incX V₀ ξ = dW.incX V₀ ξ' → ψ (symplO V₀ W (dW.incAdj V₀ (yZero V₀ ρ z)) (dW.incX V₀ ξ')) = ψ (symplO V₀ W (dW.incAdj V₀ (yZero V₀ ρ z)) (dW.incX V₀ ξ))) → ∀ i : Fin ρ, i.1 + 1 = ρ → t.1 i i - 1 ∈ intAt D (· = v) := by
  first | exact @GlobalTheory.AscFin.IsoDiag.last_diag_int_iso | exact GlobalTheory.AscFin.IsoDiag.last_diag_int_iso | (intros; apply GlobalTheory.AscFin.IsoDiag.last_diag_int_iso <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.of_mul_trivialAtPlaces_subset : ∀ {D : D7} {V₀ W W₀ : HSp D} {ρ σ : ℕ} (dW : HypDec W W₀ σ) (p : Pieces V₀ W W₀ ρ σ) (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ) (ψ : AddChar (AF D.host.F) ℂ) (P Q : GlobalTheory.FinPl.Pl D → Prop) (g₁ g₂ : GA D W), (∀ v, Q v → P v) → g₁ ∈ grpAt W Q → g₂ ∈ grpOff W Q → g₁ * g₂ = g₂ * g₁ → Cond dW p x y ψ P (g₁ * g₂) → Cond dW p x y ψ Q g₁ := by
  first | exact @GlobalTheory.AscFin.Cond.of_mul_grpOff | exact GlobalTheory.AscFin.Cond.of_mul_grpOff | (intros; apply GlobalTheory.AscFin.Cond.of_mul_grpOff <;> assumption)
end
