module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
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

namespace GlobalTheory.AscFin

variable {D : D7}

theorem colsOf_eq_mul {n c k : ℕ} (a : Matrix (Fin n) (Fin c) D.host.E) (f : Fin k → Fin c) (s : Fin k → D.host.E) :
    colsOf a f s = a * Matrix.of (fun q p => if q = f p then s p else 0) := by
  ext i p
  simp only [colsOf, Matrix.mul_apply, Matrix.of_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact mul_comm _ _

theorem antiDiagonalGram_neg_one_castLE_row {c ρ : ℕ} (h : 2 * ρ ≤ c) (p : Fin ρ) (r : Fin c) :
    antiDiagonalSignGramMatrix c (-1 : D.host.E) (Fin.castLE (by omega) p) r = if r = (Fin.castLE (by omega) p : Fin c).rev then 1 else 0 := by
  have := p.2; have := r.2
  unfold antiDiagonalSignGramMatrix
  simp only [Fin.ext_iff, Fin.val_rev, Fin.val_castLE]
  split_ifs <;> first | rfl | omega

theorem projY_mem_lat : ∀ {D : D7} {A B B₀ : HSp D} {c ρ : ℕ} (a : HermitianOrthogonalExtensionData A B c (-1)) (d : HypDec B B₀ ρ), IsAuxiliaryVectorWittDec a d → ∀ (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (v : Fin B.rank → D.host.E), v ∈ a.lat Λ 𝔟 → (d.e' * d.qY) *ᵥ v ∈ a.lat Λ 𝔟 := by
  intro D A B B₀ c ρ a d ⟨h, he, s, he'⟩ Λ 𝔟 v ⟨y, hy, u, hu, hv⟩
  subst hv
  set f : Fin ρ → Fin c := Fin.castLE (by omega) with hf
  set t : Fin ρ → D.host.E := fun p => (-D.host.xi0) ^ (p.1 + 1) with ht
  set Pe : Matrix (Fin c) (Fin ρ) D.host.E := Matrix.of (fun q p => if q = f p then t p else 0) with hPe
  set Pe' : Matrix (Fin c) (Fin ρ) D.host.E := Matrix.of (fun q p => if q = (f p).rev then s p else 0) with hPe'
  have hE : d.e = a.a * Pe := by rw [he, colsOf_eq_mul]
  have hE' : d.e' = a.a * Pe' := by rw [he', colsOf_eq_mul]
  have hG : B.gramᴴ = B.gram := GlobalTheory.MixModel.gram_conjTranspose B
  have hperp : (frameMat B A a.ι)ᴴ * B.gram * a.a = 0 := a.perp
  have hgram : a.aᴴ * B.gram * a.a = antiDiagonalSignGramMatrix c (-1) := a.gram
  have hperp' : a.aᴴ * B.gram * frameMat B A a.ι = 0 := by
    have := congrArg Matrix.conjTranspose hperp
    rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hG, conjTranspose_zero, ← Matrix.mul_assoc] at this
  have hQF : d.qY * frameMat B A a.ι = 0 := by
    rw [HypDec.qY, hE, conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc a.aᴴ, hperp', Matrix.mul_zero]
  have hQA : d.qY * a.a = Matrix.of (fun p r => if r = (f p).rev then star (t p) else 0) := by
    rw [HypDec.qY, hE, conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc a.aᴴ, hgram]
    ext p r
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hPe, Matrix.of_apply, apply_ite star, star_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, hf, antiDiagonalGram_neg_one_castLE_row h, mul_ite, mul_one, mul_zero]
  have hS : ∀ p, s p * star (t p) = 1 := by
    intro p
    have h1 : d.eᴴ * B.gram * d.e' = 1 := by
      have := congrArg Matrix.conjTranspose d.e'e
      rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hG, conjTranspose_one, ← Matrix.mul_assoc] at this
    have h2 : (d.qY * a.a * Pe') p p = 1 := by
      rw [Matrix.mul_assoc, ← hE', HypDec.qY, h1, Matrix.one_apply_eq]
    rw [hQA] at h2
    simp only [Matrix.mul_apply, hPe', Matrix.of_apply, ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,
      Finset.mem_univ, if_true] at h2
    rw [mul_comm]; exact h2
  refine ⟨0, Λ.zero_mem, fun q => ∑ p, if q = (f p).rev then u q else 0, fun q => ?_, ?_⟩
  · refine Submodule.sum_mem _ fun p _ => ?_
    split_ifs
    · exact hu q
    · exact Submodule.zero_mem _
  · rw [mulVec_zero, zero_add, ← mulVec_mulVec, mulVec_add, mulVec_mulVec, mulVec_mulVec, hQF, zero_mulVec, zero_add,
      mulVec_mulVec, hQA, hE', Matrix.mul_assoc, ← mulVec_mulVec]
    apply congrArg (fun x => a.a *ᵥ x)
    ext q
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, hPe', Matrix.of_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hq : q = (f p).rev
    · subst hq
      simp only [if_true, mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, hS p, one_mul]
    · simp only [hq, if_false, zero_mul, Finset.sum_const_zero]

end GlobalTheory.AscFin
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
open ValuativeRel

namespace GlobalTheory.FrameZero

theorem vecMul_row {E k ι : Type} [Field E] [Field k] [Fintype ι] {n c : ℕ} (φ : E →+* k) (σ : E →+* E)
    (a : Matrix (Fin n) (Fin c) E) (g : Matrix (Fin n) (Fin n) E) (b : Matrix (Fin n) ι k) (q : Fin c) (m : ι) :
    ((fun i => φ (σ (a i q))) ᵥ* (g.map φ * b)) m = ((Formalism.UG.cT σ a * g).map φ * b) q m := by

  simp only [Matrix.vecMul, dotProduct, Matrix.mul_apply, Matrix.map_apply, Formalism.UG.cT, Matrix.transpose_apply,
  map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring
private theorem mulVec_col_eq_single_of_mul_eq_one {k m n : Type} [Field k] [Fintype m] [DecidableEq n] (b : Matrix m n k)
    (b' : Matrix n m k) (hb : b' * b = 1) (j : n) : (b' *ᵥ fun i => b i j) = Pi.single j 1 := by
  funext i
  show ∑ l, b' i l * b l j = _
  rw [← Matrix.mul_apply, hb, Matrix.one_apply, Pi.single_apply]
private theorem cA_incA_eq_incA_sig (D : D7) (x : D.host.E) :
    cA D (incA D x) = incA D ((D.sp.cm.sig : D.host.E →+* D.host.E) x) := rfl
end GlobalTheory.FrameZero

theorem GlobalTheory.FrameZero.xclauses : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m), ∀ v ∈ G.pl.S0, ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
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
  unfold GlobalTheory.AscFin.OnStd All
  intro D _ T L μ0 _ sc G _ M _ F hF σ h v _ k _ _ _ _ p β ϖ κ _ _ _ hirr hinj hb hperp
  obtain ⟨h2, he, -⟩ := hF.hJ (σ + 1) h
  have hϖ : (ϖ : k) ≠ 0 := fun h0 => hirr.ne_zero (Subtype.ext h0)
  have hx0 : p.pr (incA D (-D.host.xi0)) ≠ 0 :=
    (map_ne_zero (p.pr.comp (incA D))).mpr (neg_ne_zero.mpr cmHost_imaginaryGenerator_ne_zero)
  have hx1 : p.pr (incA D ((D.sp.cm.sig : D.host.E →+* D.host.E) (-D.host.xi0))) ≠ 0 :=
    (map_ne_zero (p.pr.comp (incA D))).mpr ((map_ne_zero _).mpr (neg_ne_zero.mpr cmHost_imaginaryGenerator_ne_zero))
  have hx : ∀ i (q : Fin (σ + 1)), xZero (F.dJ (σ + 1) h) i q = incA D ((-D.host.xi0) ^ (q.1 + 1) *
      (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a i ⟨q.1, by omega⟩) := by
    intro i q
    show incA D ((F.dJ (σ + 1) h).e i q) = _
    rw [he]
    rfl
  refine ⟨fun q => (p.pr (incA D (-D.host.xi0)) ^ (q.1 + 1) *
      ((ϖ : k) ^ (G.pl.depth sc v * (q.1 + 1)))⁻¹)⁻¹,
    fun q => (p.pr (incA D ((D.sp.cm.sig : D.host.E →+* D.host.E) (-D.host.xi0))) ^ (q.1 + 1) *
      (ϖ : k) ^ (G.pl.depth sc v * (2 * (σ + 1) - 1 - q.1 + 1)))⁻¹, ?_, ?_⟩
  · intro q
    have hcol : (fun i => p.pr (xZero (F.dJ (σ + 1) h) i q)) =
        (p.pr (incA D (-D.host.xi0)) ^ (q.1 + 1) * ((ϖ : k) ^ (G.pl.depth sc v * (q.1 + 1)))⁻¹) •
          fun i => β.b i (κ ⟨q.1, by omega⟩) := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [hb, hx, map_mul, map_mul, map_pow, map_pow, mul_assoc, inv_mul_cancel_left₀ (pow_ne_zero _ hϖ)]
    dsimp only
    rw [hcol, Matrix.mulVec_smul, mulVec_col_eq_single_of_mul_eq_one _ _ β.b'b, smul_smul,
      inv_mul_cancel₀ (mul_ne_zero (pow_ne_zero _ hx0) (inv_ne_zero (pow_ne_zero _ hϖ))), one_smul]
  · intro q
    have hrow : (fun i => p.pr (cA D (xZero (F.dJ (σ + 1) h) i q))) =
        p.pr (incA D ((D.sp.cm.sig : D.host.E →+* D.host.E) (-D.host.xi0))) ^ (q.1 + 1) •
          fun i => (p.pr.comp (incA D)) ((D.sp.cm.sig : D.host.E →+* D.host.E)
            ((G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a i ⟨q.1, by omega⟩)) := by
      funext i
      rw [hx, cA_incA_eq_incA_sig]
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_pow, RingHom.comp_apply]
    have key : ∀ r : Fin (2 * (σ + 1) + 1 - 1), ∑ j, p.pr (incA D ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E)
          (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a * (G.V (.grid (2 * (σ + 1) + 1) 0)).gram)
            ⟨q.1, by omega⟩ j)) * ((ϖ : k) ^ (G.pl.depth sc v * (r.1 + 1)) *
          p.pr (incA D ((G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a j r))) =
        (ϖ : k) ^ (G.pl.depth sc v * (r.1 + 1)) * p.pr (incA D ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E)
          (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a * (G.V (.grid (2 * (σ + 1) + 1) 0)).gram *
          (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a) ⟨q.1, by omega⟩ r)) := by
      intro r

      rw [Matrix.mul_apply, map_sum, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, map_mul]
      ring
    have hN : ((fun i => (p.pr.comp (incA D)) ((D.sp.cm.sig : D.host.E →+* D.host.E)
          ((G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a i ⟨q.1, by omega⟩))) ᵥ*
          ((G.V (.grid (2 * (σ + 1) + 1) 0)).gram.map (fun c => p.pr (incA D c)) * β.b)) =
        (ϖ : k) ^ (G.pl.depth sc v * (2 * (σ + 1) - 1 - q.1 + 1)) •
          Pi.single (κ ⟨2 * (σ + 1) - 1 - q.1, by omega⟩) 1 := by
      funext m
      refine (GlobalTheory.FrameZero.vecMul_row (p.pr.comp (incA D)) (D.sp.cm.sig : D.host.E →+* D.host.E)
        (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a (G.V (.grid (2 * (σ + 1) + 1) 0)).gram β.b
        ⟨q.1, by omega⟩ m).trans ?_
      by_cases hm : m ∈ Set.range κ
      · obtain ⟨r, rfl⟩ := hm
        rw [Matrix.mul_apply]
        simp only [hb, Matrix.map_apply, RingHom.comp_apply]
        rw [key, (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).gram, antiDiagonalSignGramMatrix]
        split_ifs with h1 h3
        · exfalso
          have h4 := congrArg Fin.val h3
          simp only at h1 h4
          omega
        · have hrv : r.1 = 2 * (σ + 1) - 1 - q.1 := by simp only at h1; omega
          rw [map_one, map_one, mul_one, Pi.smul_apply, Pi.single_apply,
            if_pos (congrArg κ (Fin.ext hrv)), smul_eq_mul, mul_one, hrv]
        · rw [map_zero, map_zero, mul_zero, Pi.smul_apply, Pi.single_apply, if_neg, smul_zero]
          intro hk
          have h4 := congrArg Fin.val (hinj hk)
          simp only at h1 h4
          omega
      · rw [Pi.smul_apply, Pi.single_apply, if_neg (fun e => hm ⟨_, e.symm⟩), smul_zero]
        exact hperp m hm _
    dsimp only
    rw [hrow, Matrix.smul_vecMul, hN, smul_smul, smul_smul, mul_assoc,
      inv_mul_cancel₀ (mul_ne_zero (pow_ne_zero _ hx1) (pow_ne_zero _ hϖ)), one_smul]
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin



noncomputable section

namespace GlobalTheory.AscFin

theorem coeff_monic_poly_sum {K R : Type} [CommRing K] [CommRing R] (φ : K →+* R) {n : ℕ} (u s : K) (h : s * u = 1)
    (b : Fin n → K) (G : Matrix (Fin n) (Fin n) K) (x : Fin n → R) :
    φ u * ∑ l, φ (∑ k, (s * b k) * G k l) * x l = ∑ k, ∑ l, φ (b k) * φ (G k l) * x l := by
  have hus : φ u * φ s = 1 := by rw [← map_mul, mul_comm, h, map_one]

  simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  linear_combination (φ (b k) * φ (G k l) * x l) * hus

private theorem cT_sig_eq_conjTranspose' {D : D7} {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) M = Mᴴ := rfl

private theorem cA_incA_apply_eq_incA_star {D : D7} (e : D.host.E) : cA D (incA D e) = incA D (star e) := rfl

theorem incA_neg_xi0_pow_mul_pX_mulVec_eq_sum : ∀ {D : D7} {A B B₀ : HSp D} {c ρ : ℕ} (a : HermitianOrthogonalExtensionData A B c (-1)) (d : HypDec B B₀ ρ), c = 2 * ρ → IsAuxiliaryVectorWittDec a d → ∀ (i : Fin ρ) (hi : 2 * ρ - 1 - i.1 < c) (x : Fin B.rank → AE D), incA D ((-D.host.xi0) ^ (i.1 + 1)) * (d.pX *ᵥ x) i = ∑ k, ∑ l, cA D (incA D (a.a k ⟨2 * ρ - 1 - i.1, hi⟩)) * incA D (B.gram k l) * x l := by
  intro D A B B₀ c ρ a d hc hA i hi x
  obtain ⟨h2, he, s, he'⟩ := hA
  have hle : ρ ≤ c := by omega
  have hj : ∀ hle : ρ ≤ c, (Fin.castLE hle i).rev = (⟨2 * ρ - 1 - i.1, hi⟩ : Fin c) := fun hle => by
    ext
    simp only [Fin.val_rev, Fin.coe_castLE]
    omega
  have g1 := congrFun (congrFun a.gram ⟨2 * ρ - 1 - i.1, hi⟩) (Fin.castLE hle i)
  have g2 := congrFun (congrFun d.e'e i) i
  rw [he, he'] at g2
  simp only [antiDiagonalSignGramMatrix, cT_sig_eq_conjTranspose', Matrix.mul_apply, Matrix.conjTranspose_apply, colsOf, star_mul', Matrix.one_apply_eq, hj,
    Fin.coe_castLE] at g1 g2
  rw [if_pos (by omega), if_neg (fun h => by have := congrArg Fin.val h; simp only [Fin.coe_castLE] at this; omega)] at g1
  have g3 : ∑ l, (∑ k, star (s i) * star (a.a k ⟨2 * ρ - 1 - i.1, hi⟩) * HSpace.gram B k l) *
      ((-D.host.xi0) ^ (i.1 + 1) * a.a l (Fin.castLE hle i)) =
      star (s i) * (-D.host.xi0) ^ (i.1 + 1) *
        ∑ l, (∑ k, star (a.a k ⟨2 * ρ - 1 - i.1, hi⟩) * HSpace.gram B k l) * a.a l (Fin.castLE hle i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [mul_assoc (star (s i)), ← Finset.mul_sum]
    ring
  have key : star (s i) * (-D.host.xi0) ^ (i.1 + 1) = 1 := by
    linear_combination g2 - g3 - (star (s i) * (-D.host.xi0) ^ (i.1 + 1)) * g1
  simp only [HypDec.pX, HypDec.qX, GlobalTheory.MixModel.rat, Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, he', colsOf, star_mul', hj, cA_incA_apply_eq_incA_star]
  exact coeff_monic_poly_sum (incA D) _ _ key (fun k => star (a.a k ⟨2 * ρ - 1 - i.1, hi⟩)) (HSpace.gram B) x

end GlobalTheory.AscFin

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

noncomputable section

namespace GlobalTheory.LatSandwich

variable {D : D7}

theorem incA_eq (e : D.host.E) : incA D e = (1 : AF D.host.F) ⊗ₜ[D.host.F] e := rfl

theorem rat_mul_tmul_mul {k l m n : ℕ} (A : Matrix (Fin k) (Fin l) D.host.E) (X : Matrix (Fin l) (Fin m) D.host.E)
    (B : Matrix (Fin m) (Fin n) D.host.E) (p : AF D.host.F) :
    rat A ⬝ (Matrix.of fun i j => p ⊗ₜ[D.host.F] X i j : Mx D l m) ⬝ rat B =
      Matrix.of fun i j => p ⊗ₜ[D.host.F] (A * X * B) i j := by
  ext i j
  simp only [Matrix.mul_apply, rat, Matrix.map_apply, Matrix.of_apply, incA_eq, Finset.sum_mul,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, ← TensorProduct.tmul_sum]

theorem sandwich_hatMx {k l m n : ℕ} {M : Submodule (𝓞 D.host.E) (Matrix (Fin l) (Fin m) D.host.E)}
    {M' : Submodule (𝓞 D.host.E) (Matrix (Fin k) (Fin n) D.host.E)} (A : Matrix (Fin k) (Fin l) D.host.E)
    (B : Matrix (Fin m) (Fin n) D.host.E) (h : ∀ x ∈ M, A * x * B ∈ M') {z : Mx D l m} (hz : z ∈ hatMx M) :
    rat A ⬝ z ⬝ rat B ∈ hatMx M' := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, x, hx, rfl⟩ := hw
    rw [rat_mul_tmul_mul]
    exact AddSubgroup.subset_closure ⟨α, hα, _, h x hx, rfl⟩
  | zero => rw [Matrix.mul_zero, Matrix.zero_mul]; exact zero_mem _
  | add a b _ _ ha hb => rw [Matrix.mul_add, Matrix.add_mul]; exact add_mem ha hb
  | neg a _ ha => rw [Matrix.mul_neg, Matrix.neg_mul]; exact neg_mem ha

theorem sandwich_homLat {k l m n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin m → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin l → D.host.E)} {Λ₂ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ₂' : Submodule (𝓞 D.host.E) (Fin k → D.host.E)} (A : Matrix (Fin k) (Fin l) D.host.E)
    (B : Matrix (Fin m) (Fin n) D.host.E) (hA : ∀ t ∈ Λ', A *ᵥ t ∈ Λ₂') (hB : ∀ y ∈ Λ₂, B *ᵥ y ∈ Λ)
    (𝔪 : Ideal (𝓞 D.host.E)) : ∀ x ∈ 𝔪 • homLat Λ Λ', A * x * B ∈ 𝔪 • homLat Λ₂ Λ₂' := by
  intro x hx
  refine Submodule.smul_induction_on hx (fun r hr x hx => ?_) (fun x y hx hy => ?_)
  · have e : A * (r • x) * B = r • (A * x * B) := by
      rw [Matrix.mul_smul, Matrix.smul_mul]
    rw [e]
    refine Submodule.smul_mem_smul hr fun y hy => ?_
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact hA _ (hx _ (hB y hy))
  · rw [Matrix.mul_add, Matrix.add_mul]; exact add_mem hx hy

theorem sandwich_entry {k l m n : ℕ} (A : Matrix (Fin k) (Fin l) D.host.E) (B : Matrix (Fin m) (Fin n) D.host.E)
    (a : D.host.E) (t : Fin l → D.host.E) (r : Fin m → D.host.E) (i : Fin k) (j : Fin n) :
    (A * Matrix.of (fun i j => a * t i * r j) * B) i j = a * (A *ᵥ t) i * ∑ m, r m * B m j := by
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem sandwich_latO {S T S' T' : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {LS' : Set (Fin S'.rank → D.host.E)} {LT' : Set (Fin T'.rank → D.host.E)} (A : Matrix (Fin T'.rank) (Fin T.rank) D.host.E)
    (B : Matrix (Fin S.rank) (Fin S'.rank) D.host.E) (hA : ∀ t ∈ LT, A *ᵥ t ∈ LT')
    (hB : ∀ s ∈ LS, ∃ s' ∈ LS', ∀ j, ∑ k, star (s' k) * S'.gram k j = ∑ m, (∑ k, star (s k) * S.gram k m) * B m j)
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) {w : WO S T} (hw : w ∈ latO S T LS LT P) :
    (rat A ⬝ w ⬝ rat B : WO S' T') ∈ latO S' T' LS' LT' P := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hw
    obtain ⟨s', hs', e⟩ := hB s hs
    have e1 : (Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) : WO S T) =
        Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F]
          (Matrix.of (fun i j => a * t i * ∑ k, star (s k) * S.gram k j) : Matrix (Fin T.rank) (Fin S.rank) D.host.E) i j := rfl
    rw [e1, rat_mul_tmul_mul]
    refine AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s', hs', A *ᵥ t, hA t ht, ?_⟩
    ext i j
    simp only [Matrix.of_apply]
    rw [sandwich_entry, e j]
  | zero => rw [Matrix.mul_zero, Matrix.zero_mul]; exact zero_mem _
  | add a b _ _ ha hb => rw [Matrix.mul_add, Matrix.add_mul]; exact add_mem ha hb
  | neg a _ ha => rw [Matrix.mul_neg, Matrix.neg_mul]; exact neg_mem ha

theorem orthogonalSumAuxiliaryVectors_frame_mulVec_mem_lattice {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)
    {M : Matrix (Fin B.rank) (Fin A.rank) D.host.E} (hM : M = frameMat B A d.ι) {y : Fin A.rank → D.host.E} (hy : y ∈ Λ) :
    M *ᵥ y ∈ d.lat Λ 𝔟 :=
  ⟨y, hy, 0, fun p => (𝔟 p).val.zero_mem, by rw [hM, Matrix.mulVec_zero, add_zero]⟩

theorem orthogonalSumAuxiliaryVectors_projection_mem_lattice {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)
    {M : Matrix (Fin B.rank) (Fin A.rank) D.host.E} (hM : M = frameMat B A d.ι) (hiso : Mᴴ * B.gram * M = A.gram)
    {x : Fin B.rank → D.host.E} (hx : x ∈ d.lat Λ 𝔟) : (A.gram⁻¹ * (Mᴴ * B.gram)) *ᵥ x ∈ Λ := by
  obtain ⟨y, hy, u, -, rfl⟩ := hx
  have h1 : A.gram⁻¹ * (Mᴴ * B.gram) * M = 1 := by
    rw [Matrix.mul_assoc, hiso, Matrix.nonsing_inv_mul _ (gram_isUnit_det A)]
  have h2 : A.gram⁻¹ * (Mᴴ * B.gram) * d.a = 0 := by
    have := d.perp
    rw [cT_sig, ← hM] at this
    rw [Matrix.mul_assoc, this, Matrix.mul_zero]
  rw [← hM, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h1, h2, Matrix.one_mulVec,
    Matrix.zero_mulVec, add_zero]
  exact hy

theorem proj_form {A B : HSp D} (M : Matrix (Fin B.rank) (Fin A.rank) D.host.E) (s : Fin B.rank → D.host.E) (j : Fin A.rank) :
    ∑ k, star (((A.gram⁻¹ * (Mᴴ * B.gram)) *ᵥ s) k) * A.gram k j = ∑ m, (∑ k, star (s k) * B.gram k m) * M m j := by
  have e1 : (A.gram⁻¹ * (Mᴴ * B.gram))ᴴ * A.gram = B.gram * M := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, gram_conjTranspose,
      gram_conjTranspose, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (gram_isUnit_det A),
      Matrix.mul_one]
  have e2 : (fun j => ∑ k, star (((A.gram⁻¹ * (Mᴴ * B.gram)) *ᵥ s) k) * A.gram k j) =
      star ((A.gram⁻¹ * (Mᴴ * B.gram)) *ᵥ s) ᵥ* A.gram := by
    funext j; simp only [Matrix.vecMul, dotProduct, Pi.star_apply]
  have e3 : (fun j => ∑ m, (∑ k, star (s k) * B.gram k m) * M m j) = (star s ᵥ* B.gram) ᵥ* M := by
    funext j; simp only [Matrix.vecMul, dotProduct, Pi.star_apply]
  have key : star ((A.gram⁻¹ * (Mᴴ * B.gram)) *ᵥ s) ᵥ* A.gram = (star s ᵥ* B.gram) ᵥ* M := by
    rw [Matrix.star_mulVec, Matrix.vecMul_vecMul, e1, ← Matrix.vecMul_vecMul]
  exact congrFun (e2.trans (key.trans e3.symm)) j

end GlobalTheory.LatSandwich

namespace GlobalTheory.AscFin

open GlobalTheory.LatSandwich

theorem pcBF_core_mem_latCore : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ u ∈ (pcBF W F ρ h).Γ₀,
    ((F.oB ρ h).resS (G.V (.core (2 * ρ + 1))) u).1 ∈ latCore G (2 * ρ + 1) := by
  intro D hoff T L μ0 hL sc G W M hM F hF ρ h u hu
  simp only [pcBF, piecesOf, AddSubgroup.mem_comap, AddMonoidHom.coe_comp, Function.comp_apply] at hu
  rw [OrthDec.resS_apply]

  have key : rat (F.dJ ρ h).q0 ⬝ (F.dB ρ h).ext0 _ ((F.dJ ρ h).inc0 _ u) ⬝ rat ((F.dB ρ h).i₀ * (F.oB ρ h).iA) =
      u ⬝ (F.oB ρ h).jA := by
    rw [rat_mul, HypDec.matrixExtendByZero_apply, HypDec.wittDecomp_inclAnisotropicHom_apply]
    change (F.dJ ρ h).p0 ⬝ ((F.dJ ρ h).j0 ⬝ u ⬝ (F.dB ρ h).p0) ⬝ ((F.dB ρ h).j0 ⬝ (F.oB ρ h).jA) = _
    simp only [← Matrix.mul_assoc]
    rw [HypDec.p0_j0, Matrix.one_mul, Matrix.mul_assoc u, HypDec.p0_j0, Matrix.mul_one]
  rw [← key]

  have lat1 : G.Λ (.grid (2 * ρ + 1) 0) = (G.colDec (2 * ρ + 1) (by omega) (by omega)).lat (G.Λ (.core (2 * ρ + 1)))
      (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1)) := G.sp.colLat (2 * ρ + 1) (by omega) (by omega)
  have lat2 : G.Λ (.grid (2 * ρ + 2) 0) = (G.colDec (2 * ρ + 2) (by omega) h).lat (G.Λ (.core (2 * ρ + 2)))
      (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1)) := G.sp.colLat (2 * ρ + 2) (by omega) h
  have iso2 : ((F.dB ρ h).i₀ * (F.oB ρ h).iA)ᴴ * (G.V (.grid (2 * ρ + 2) 0)).gram * ((F.dB ρ h).i₀ * (F.oB ρ h).iA) =
      (G.V (.core (2 * ρ + 2))).gram := by
    rw [Matrix.conjTranspose_mul]
    calc _ = (F.oB ρ h).iAᴴ * ((F.dB ρ h).i₀ᴴ * (G.V (.grid (2 * ρ + 2) 0)).gram * (F.dB ρ h).i₀) * (F.oB ρ h).iA := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [(F.dB ρ h).iso, (F.oB ρ h).isoA]

  have hA : ∀ t ∈ G.Λ (.grid (2 * ρ + 1) 0), (F.dJ ρ h).q0 *ᵥ t ∈ G.Λ (.core (2 * ρ + 1)) := fun t ht =>
    orthogonalSumAuxiliaryVectors_projection_mem_lattice _ _ _ (hF.aJ ρ h) (F.dJ ρ h).iso (lat1 ▸ ht)

  have hB1 : ∀ y ∈ G.Λ (.core (2 * ρ + 2)), ((F.dB ρ h).i₀ * (F.oB ρ h).iA) *ᵥ y ∈ G.Λ (.grid (2 * ρ + 2) 0) :=
    fun y hy => lat2 ▸ orthogonalSumAuxiliaryVectors_frame_mulVec_mem_lattice _ _ _ (hF.aB ρ h) hy

  have hB : ∀ s ∈ (G.Λ (.grid (2 * ρ + 2) 0) : Set (Fin (negSp (G.V (.grid (2 * ρ + 2) 0))).rank → D.host.E)),
      ∃ s' ∈ (G.Λ (.core (2 * ρ + 2)) : Set (Fin (negSp (G.V (.core (2 * ρ + 2)))).rank → D.host.E)), ∀ j,
        ∑ k, star (s' k) * (negSp (G.V (.core (2 * ρ + 2)))).gram k j =
          ∑ m, (∑ k, star (s k) * (negSp (G.V (.grid (2 * ρ + 2) 0))).gram k m) * ((F.dB ρ h).i₀ * (F.oB ρ h).iA) m j := by
    intro s hs
    rw [SetLike.mem_coe, lat2] at hs
    refine ⟨_, orthogonalSumAuxiliaryVectors_projection_mem_lattice _ _ _ (hF.aB ρ h) iso2 hs, fun j => ?_⟩
    simp only [negSp_gram, Matrix.neg_apply, mul_neg, Finset.sum_neg_distrib, neg_mul]
    rw [proj_form]
  have hu1 : (F.dB ρ h).ext0 _ ((F.dJ ρ h).inc0 _ u) ∈ latO (negSp (G.V (.grid (2 * ρ + 2) 0))) (G.V (.grid (2 * ρ + 1) 0))
      (G.Λ (.grid (2 * ρ + 2) 0) : Set _) (G.Λ (.grid (2 * ρ + 1) 0) : Set _) (fun _ => True) := hu.1
  have hu2 : ∀ e : AE D, IsIdemSum e G.pl.W0 → e • (F.dB ρ h).ext0 _ ((F.dJ ρ h).inc0 _ u) ∈
      hatMx (G.modul • homLat (G.Λ (.grid (2 * ρ + 2) 0)) (G.Λ (.grid (2 * ρ + 1) 0))) := hu.2
  refine ⟨?_, fun e he => ?_⟩
  · have h1 := sandwich_latO (S' := negSp (G.V (.core (2 * ρ + 2)))) (T' := G.V (.core (2 * ρ + 1)))
      (LS' := (G.Λ (.core (2 * ρ + 2)) : Set _)) (LT' := (G.Λ (.core (2 * ρ + 1)) : Set _)) _ _ hA hB _ hu1
    exact h1
  · have h2 := sandwich_hatMx _ _ (sandwich_homLat _ _ hA hB1 G.modul) (hu2 e he)
    rw [Matrix.mul_smul, Matrix.smul_mul] at h2
    exact h2

end GlobalTheory.AscFin
end
end
