module

public import Formalism.LocalToGlobal.KernelLattices.Bundle001
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.KerEntHyp
public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
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
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC

theorem cTw_eq_mul (B : Base) :
    ((B.R.m * (B.R.t + 1) / 2 : ℕ) : ℤ) = (B.R.m : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ) := by
  obtain ⟨b, hb⟩ := B.R.t_odd
  have h2 : B.R.t + 1 = 2 * (b + 1) := by omega
  rw [h2, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2), Nat.mul_left_comm,
    Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  push_cast
  ring

theorem trueWeight_lastStep_trueColumns {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)
    (τ : (I.rec7 l Z).what₂.Tau) : Formalism.MainNotions.product_first_zeroth_parts.lamTr (I.rec7 l Z) u τ = B.wts.lamTrue u B.R.m τ := by
  have h := cTw_eq_mul B
  show Formalism.MainNotions.product_first_zeroth_parts.wSh (Examples₂.lamOf (B.hcW u τ) B.R.m) (Formalism.MainNotions.product_first_zeroth_parts.cTw B.R) =
    Formalism.L2.Col.shiftW (Examples₂.lamOf (B.hcW u τ) B.R.m) (-((B.R.m : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ)))
  unfold Formalism.MainNotions.product_first_zeroth_parts.wSh Formalism.L2.Col.shiftW Formalism.MainNotions.product_first_zeroth_parts.cTw
  congr 1
  funext i
  rw [h]
  ring

theorem trueRowWeight_trueColumns {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)
    (τ : (I.rec7 l Z).what₂.Tau) : Formalism.MainNotions.product_first_zeroth_parts.sgTr (I.rec7 l Z) u τ = B.wts.sgTrue τ := by
  have h := cTw_eq_mul B
  show Formalism.MainNotions.product_first_zeroth_parts.wSh (B.wts.row τ).sg (Formalism.MainNotions.product_first_zeroth_parts.cTw B.R) =
    Formalism.L2.Col.shiftW (B.wts.row τ).sg (-((B.R.m : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ)))
  unfold Formalism.MainNotions.product_first_zeroth_parts.wSh Formalism.L2.Col.shiftW Formalism.MainNotions.product_first_zeroth_parts.cTw
  congr 1
  funext i
  rw [h]
  ring

end GlobalTheory.Mem.Col2.TC

namespace GlobalTheory.Mem.Col2.TC

theorem branchingNorm_identity_trueColumns_members {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) :
    BeOnTie (I.rec7 l Z) u := by
  intro τ
  have e1 := trueWeight_lastStep_trueColumns I l Z u τ
  have e2 := trueRowWeight_trueColumns I l Z u τ
  have n1 : (Formalism.MainNotions.product_first_zeroth_parts.lamTr (I.rec7 l Z) u τ).natW = (((I.rec7 l Z).fm u).lam (I.rec7 l Z).R.m τ).natW :=
    Formalism.MainNotions.product_first_zeroth_parts.natW_wSh _ _
  have n2 : (Formalism.MainNotions.product_first_zeroth_parts.sgTr (I.rec7 l Z) u τ).natW = (((I.rec7 l Z).fm u).sg τ).natW := Formalism.MainNotions.product_first_zeroth_parts.natW_wSh _ _
  show fockOpNorm (B.wts.lamTrue u B.R.m τ) (B.wts.sgTrue τ)
      (GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance.brOne ℂ (N_m_succ B.R) (B.wts.lamTrue u B.R.m τ) (B.wts.sgTrue τ)) =
    fockOpNorm (((I.rec7 l Z).fm u).lam (I.rec7 l Z).R.m τ) (((I.rec7 l Z).fm u).sg τ)
      (Formalism.L2.Ker.brOne ℂ (Formalism.MainNotions.product_first_zeroth_parts.Nm_succ (I.rec7 l Z).R).symm (Formalism.MainNotions.product_first_zeroth_parts.lamTr (I.rec7 l Z) u τ)
        (Formalism.MainNotions.product_first_zeroth_parts.sgTr (I.rec7 l Z) u τ))
  rw [e1, e2] at *
  exact fockOpNorm_congr _ n1 n2

theorem beOnTie_true : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws)
    (Z : TC.Later B (I.cols l)), ∀ u, BeOnTie (I.rec7 l Z) u :=
  fun I _ _ l Z u => branchingNorm_identity_trueColumns_members I l Z u

end GlobalTheory.Mem.Col2.TC
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.KerForm

open Classical

theorem frInv_leftInv {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} (O : GL3Theta.LiftObj D C) {i : ℕ}
    (hi : i ≤ D.R.m) (Q : MvPolynomial (GL3Theta.FrV D (D.R.N i)) ℂ) : frInv O i (frPoly O i Q) = Q := by
  have hs : frInv O i ∘ₗ frPoly O i = LinearMap.id :=
    Classical.epsilon_spec (p := fun g => g ∘ₗ frPoly O i = LinearMap.id)
      (LinearMap.exists_leftInverse_of_injective _ (LinearMap.ker_eq_bot.2 (Formalism.L2.Ker.frobenius_poly_injective D u C O i hi)))
  exact LinearMap.congr_fun hs Q

theorem sharp_evC (D : D7) (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)) (u : D.what₂.Word) (μ : D.what₂.Tup) (i : ℕ) (hi : i < D.R.m)
    (v : ValQ O u μ i) :
    (D.chTw u μ).sharp i (evC O u μ i v) = frPoly (O u μ) i
      (MvPolynomial.map D.what₂.embLL (srcPol u μ i (secC O u μ i v : MvPolynomial (GL3Theta.FrV D (D.R.N i)) D.what₂.LL))) := by
  funext y
  rw [evC_sec]
  show (∏ τ, ((D.chTw u μ).de i y τ) ^ ((D.chTw u μ).sSharp i τ)) * ((∏ τ, ((D.chTw u μ).de i y τ) ^ (-(twB D u μ i τ))) *
    GL3Theta.evFr D (MvPolynomial.map D.what₂.embLL (secC O u μ i v : MvPolynomial (GL3Theta.FrV D (D.R.N i)) D.what₂.LL)) ((O u μ).frm i y)) = _
  show _ = GL3Theta.evFr D _ ((O u μ).frm i y)
  unfold srcPol GL3Theta.evFr
  rw [map_mul, map_mul, map_prod, map_prod, ← mul_assoc, ← Finset.prod_mul_distrib, mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_pow, map_pow, eval_detP, ← (O u μ).frm_de i hi.le y τ, ← zpow_add₀ ((D.chTw u μ).de_ne i y τ), ← zpow_natCast,
    Int.toNat_of_nonneg (sub_nonneg.2 (twLe D u μ i hi τ)), sub_eq_add_neg]

theorem complex_kform : ∀ (D : D7) (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)) (u : D.what₂.Word) (μ : D.what₂.Tup) (i : ℕ) (hi : i < D.R.m)
    (hU : UnfIsAll (O u μ) i) (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)) (v : ValQ O u μ i) (v' : ValQ O u μ (i + 1))
    (h : evC O u μ (i + 1) v' = (D.chTw u μ).Kmap i c c' (evC O u μ i v)), MvPolynomial.map D.what₂.embLL (secC O u μ (i + 1) v' : MvPolynomial (GL3Theta.FrV D (D.R.N (i + 1))) D.what₂.LL) =
      MvPolynomial.C (((GL3Theta.rhoOf D (O u μ).mt i ((O u μ).dt i c) : ℂˣ) : ℂ) * ((GL3Theta.rhoOf' D (O u μ).mt i ((O u μ).dt (i + 1) c') : ℂˣ) : ℂ)) *
        jetMap (jetC (O u μ).dgen ((O u μ).Th i c c')) (fun _ => 0)
          (MvPolynomial.map D.what₂.embLL (srcPol u μ i (secC O u μ i v : MvPolynomial (GL3Theta.FrV D (D.R.N i)) D.what₂.LL))) := by
  intro D O u μ i hi hU c c' v v' h
  set Q := MvPolynomial.map D.what₂.embLL (srcPol u μ i (secC O u μ i v : MvPolynomial (GL3Theta.FrV D (D.R.N i)) D.what₂.LL)) with hQ
  set Q' := MvPolynomial.map D.what₂.embLL (secC O u μ (i + 1) v' : MvPolynomial (GL3Theta.FrV D (D.R.N (i + 1))) D.what₂.LL) with hQ'
  set ρ : ℂ := ((GL3Theta.rhoOf D (O u μ).mt i ((O u μ).dt i c) : ℂˣ) : ℂ) * ((GL3Theta.rhoOf' D (O u μ).mt i ((O u μ).dt (i + 1) c') : ℂˣ) : ℂ) with hρ
  have hunf : (D.chTw u μ).unf i c c' (frPoly (O u μ) i Q) =
      frPoly (O u μ) (i + 1) (jetMap (ι := D.what₂.Tau) (jetC (O u μ).dgen ((O u μ).Th i c c')) (fun _ => 0) Q) := by
    rw [hU c c' Q]
    unfold unfC
    rw [LinearMap.comp_apply, LinearMap.comp_apply, frInv_leftInv (O u μ) hi.le]
  have hrho : (D.chTw u μ).rhoDet i c * (D.chTw u μ).rhoDet' i c' = ρ := by
    rw [((O u μ).c13 i hi).1 c, ((O u μ).c13 i hi).2 c']
  apply Formalism.L2.Ker.frobenius_poly_injective D u (D.chTw u μ) (O u μ) (i + 1) hi
  funext y'
  have h1 := congrFun h y'
  rw [ColumnChain.Kmap, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.comp_apply, sharp_evC D O u μ i hi v, hunf, hrho] at h1
  rw [evC_sec] at h1
  change (∏ τ, ((D.chTw u μ).de (i + 1) y' τ) ^ (-((D.chTw u μ).sDiv i τ))) * GL3Theta.evFr D Q' ((O u μ).frm (i + 1) y') =
    ρ * ((∏ τ, ((D.chTw u μ).de (i + 1) y' τ) ^ ((D.chTw u μ).sDiv i τ))⁻¹ *
      frPoly (O u μ) (i + 1) (jetMap (ι := D.what₂.Tau) (jetC (O u μ).dgen ((O u μ).Th i c c')) (fun _ => 0) Q) y') at h1
  have hne : (∏ τ, ((D.chTw u μ).de (i + 1) y' τ) ^ ((D.chTw u μ).sDiv i τ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ ((D.chTw u μ).de_ne (i + 1) y' τ)
  have hinv : (∏ τ, ((D.chTw u μ).de (i + 1) y' τ) ^ (-((D.chTw u μ).sDiv i τ))) =
      (∏ τ, ((D.chTw u μ).de (i + 1) y' τ) ^ ((D.chTw u μ).sDiv i τ))⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun τ _ => zpow_neg _ _
  rw [hinv] at h1
  have h2 : GL3Theta.evFr D Q' ((O u μ).frm (i + 1) y') =
      ρ * frPoly (O u μ) (i + 1) (jetMap (ι := D.what₂.Tau) (jetC (O u μ).dgen ((O u μ).Th i c c')) (fun _ => 0) Q) y' := by
    have := inv_ne_zero hne
    apply mul_left_cancel₀ this
    rw [h1]; ring
  show GL3Theta.evFr D Q' ((O u μ).frm (i + 1) y') = GL3Theta.evFr D _ ((O u μ).frm (i + 1) y')
  rw [h2]
  simp [frPoly, GL3Theta.evFr]

end GlobalTheory.Mem.KerForm

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.WtHomog

open MvPolynomial

theorem coeff_aeval_diag {K : Type} [Field K] {σ : Type} (c : σ → K) (Q : MvPolynomial σ K)
    (e : σ →₀ ℕ) :
    AddMonoidAlgebra.coeff (aeval (fun v => C (c v) * X v) Q : MvPolynomial σ K) e
      = (e.prod fun v k => c v ^ k) * AddMonoidAlgebra.coeff Q e := by
  classical
  induction Q using MvPolynomial.induction_on' generalizing e with
  | monomial u a =>
    have h : (aeval (fun v => C (c v) * X v) (monomial u a) : MvPolynomial σ K)
        = monomial u ((u.prod fun v k => c v ^ k) * a) := by
      rw [aeval_monomial]
      simp only [mul_pow, Finsupp.prod_mul, ← map_pow]
      rw [show (u.prod fun v k => (C (c v ^ k) : MvPolynomial σ K))
            = C (u.prod fun v k => c v ^ k) from (map_finsuppProd C _ _).symm]
      rw [show (u.prod fun v k => (X v : MvPolynomial σ K) ^ k) = monomial u 1 from
        (monomial_eq (s := u) (a := (1 : K))).symm ▸ by simp]
      rw [algebraMap_eq, ← mul_assoc, ← C_mul, C_mul_monomial]
      simp [mul_comm]
    rw [h, coeff_monomial, coeff_monomial]
    by_cases hue : u = e
    · subst hue; simp
    · simp [hue]
  | add p q hp hq =>
    rw [map_add (f := _), MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, mul_add]

theorem deg_eq_of_mem_wtPol : ∀ {K : Type} [Field K] [CharZero K] {ι : Type} [Fintype ι] {n : ℕ} (ν : ι → Fin n → ℕ)
    (Q : MvPolynomial (ι × Fin n × Fin n) K) (hQ : Q ∈ WtPol K ν), ∀ e ∈ Q.support, ∀ τ, ∑ α, ∑ s, e (τ, α, s) = ∑ r, ν τ r := by
  intro K _ _ ι _ n ν Q hQ e he τ
  classical
  set c : ι → K := fun σ => if σ = τ then 2 else 1 with hc
  set β : ι → Matrix (Fin n) (Fin n) K := fun σ => c σ • (1 : Matrix (Fin n) (Fin n) K) with hβ
  have hc0 : ∀ σ, c σ ≠ 0 := by
    intro σ; simp only [hc]; split_ifs <;> norm_num
  have hbor : IsBor β := by
    intro σ
    refine ⟨fun r s hsr => ?_, fun r => ?_⟩
    · simp [hβ, Matrix.one_apply, (ne_of_lt hsr).symm]
    · simpa [hβ] using hc0 σ
  have hsub : colSub β = aeval (fun v : ι × Fin n × Fin n => C (c v.1) * X v) := by
    unfold colSub
    congr 1
    funext v
    obtain ⟨σ, α, s⟩ := v
    simp only [hβ, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single s]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  have hw := hQ β hbor
  rw [hsub] at hw
  have hcoef := congrArg (AddMonoidAlgebra.coeff · e) hw
  rw [coeff_aeval_diag, MvPolynomial.coeff_smul] at hcoef
  have hne : AddMonoidAlgebra.coeff Q e ≠ 0 := mem_support_iff.mp he
  have hL : (e.prod fun v k => c v.1 ^ k) = (2 : K) ^ (∑ α, ∑ s, e (τ, α, s)) := by
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type,
      Finset.prod_eq_single τ]
    · rw [Fintype.prod_prod_type]
      simp only [hc, if_true, Finset.prod_pow_eq_pow_sum]
    · intro σ _ hσ
      simp [hc, hσ]
    · simp
  have hR : (∏ σ, ∏ r, β σ r r ^ ν σ r) = (2 : K) ^ (∑ r, ν τ r) := by
    rw [Finset.prod_eq_single τ]
    · simp [hβ, hc, Finset.prod_pow_eq_pow_sum]
    · intro σ _ hσ
      simp [hβ, hc, hσ]
    · simp
  rw [hL, hR, smul_eq_mul] at hcoef
  have heq := mul_right_cancel₀ hne hcoef
  have h2 : ((2 : ℕ) ^ (∑ α, ∑ s, e (τ, α, s))) = (2 : ℕ) ^ (∑ r, ν τ r) := by
    exact_mod_cast heq
  exact Nat.pow_right_injective (le_refl 2) h2

end GlobalTheory.Mem.WtHomog
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.JetTransport

open MvPolynomial Finsupp

variable {ι : Type} [Fintype ι] {a b : ℕ}


open Classical in
noncomputable def wD (ι : Type) (a b : ℕ) : ((ι × Fin b × Fin b) ⊕ DVar ι a b) → (ι → ℕ) :=
  Sum.elim 0 fun x => Pi.single x.1 1


open Classical in
noncomputable def wF (ι : Type) (a : ℕ) : (ι × Fin a × Fin a) → (ι → ℕ) := fun v => Pi.single v.1 1

lemma weight_wF (e : (ι × Fin a × Fin a) →₀ ℕ) (τ : ι) :
    weight (wF ι a) e τ = ∑ α, ∑ s, e (τ, α, s) := by
  classical
  rw [weight_apply, Finsupp.sum_fintype _ _ (by intro; simp)]
  simp [wF, Finset.sum_apply, Pi.single_apply, Fintype.sum_prod_type]
  rw [Fintype.sum_eq_single τ (fun x hx => by simp [Ne.symm hx])]
  simp

lemma weight_wD (u : ((ι × Fin b × Fin b) ⊕ DVar ι a b) →₀ ℕ) (τ : ι) :
    weight (wD ι a b) u τ = ∑ β, ∑ α, u (Sum.inr (τ, β, α)) := by
  classical
  rw [weight_apply, Finsupp.sum_fintype _ _ (by intro; simp)]
  simp [wD, Finset.sum_apply, Pi.single_apply, Fintype.sum_prod_type, Fintype.sum_sum_type]
  rw [Fintype.sum_eq_single τ (fun x hx => by simp [Ne.symm hx])]
  simp

lemma jetMap_zero {K : Type} [Field K] (J : (DVar ι a b →₀ ℕ) → K) (P : Formalism.L2.DIV.Pol K ι a) :
    jetMap J (fun _ => 0) P = jetLin J (subD K ι a b P) := by
  simp [jetMap]

lemma jetLin_monomial {K : Type} [Field K] (J : (DVar ι a b →₀ ℕ) → K)
    (u : ((ι × Fin b × Fin b) ⊕ DVar ι a b) →₀ ℕ) (c : K) :
    jetLin J (monomial u c) = monomial (u.comapDomain Sum.inl Sum.inl_injective.injOn)
      (c * J (u.comapDomain Sum.inr Sum.inr_injective.injOn)) := by
  have : (monomial u c : MvPolynomial _ K) = c • basisMonomials _ K u := by
    rw [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  rw [this]
  unfold jetLin
  rw [LinearMap.map_smul, Module.Basis.constr_basis, smul_monomial, smul_eq_mul]

lemma jetLin_map {K K' : Type} [Field K] [Field K'] (f : K →+* K') (J : (DVar ι a b →₀ ℕ) → K)
    (Q : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K) :
    jetLin (f ∘ J) (map f Q) = map f (jetLin J Q) := by
  induction Q using MvPolynomial.induction_on' with
  | monomial u c => simp [jetLin_monomial, map_monomial]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]

lemma subD_map {K K' : Type} [Field K] [Field K'] (f : K →+* K') (P : Formalism.L2.DIV.Pol K ι a) :
    subD K' ι a b (map f P) = map f (subD K ι a b P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [subD]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    rw [map_mul, map_X, map_mul, hp, map_mul, map_mul]
    congr 1
    simp only [subD, aeval_X]
    split_ifs <;> simp [map_sum]

lemma subD_X_hom {K : Type} [Field K] (v : ι × Fin a × Fin a) :
    IsWeightedHomogeneous (wD ι a b) (subD K ι a b (X v)) (wF ι a v) := by
  simp only [subD, aeval_X]
  split_ifs with h
  · apply IsWeightedHomogeneous.sum
    intro β _
    have := (isWeightedHomogeneous_X K (wD ι a b) (Sum.inl (v.1, β, (⟨v.2.2.1, h⟩ : Fin b)))).mul
      (isWeightedHomogeneous_X K (wD ι a b) (Sum.inr (v.1, β, v.2.1)))
    simpa [wD, wF] using this
  · exact isWeightedHomogeneous_zero _ _ _

lemma subD_hom {K : Type} [Field K] (P : Formalism.L2.DIV.Pol K ι a) (n : ι → ℕ)
    (hP : IsWeightedHomogeneous (wF ι a) P n) :
    IsWeightedHomogeneous (wD ι a b) (subD K ι a b P) n := by

  rw [P.as_sum, map_sum]
  apply IsWeightedHomogeneous.sum
  intro e he
  have hw : weight (wF ι a) e = n := hP (MvPolynomial.mem_support_iff.mp he)
  rw [subD, aeval_monomial, algebraMap_eq]
  apply IsWeightedHomogeneous.C_mul
  rw [← hw, weight_apply]
  apply IsWeightedHomogeneous.prod
  intro v _
  simpa only [subD, aeval_X] using (subD_X_hom (b := b) (K := K) v).pow (e v)

lemma jetLin_congr {K : Type} [Field K] (J₁ J₂ : (DVar ι a b →₀ ℕ) → K) (n : ι → ℕ)
    (Q : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K) (hQ : IsWeightedHomogeneous (wD ι a b) Q n)
    (hJ : ∀ m : DVar ι a b →₀ ℕ, (∀ τ, ∑ β, ∑ α, m (τ, β, α) = n τ) → J₁ m = J₂ m) :
    jetLin J₁ Q = jetLin J₂ Q := by

  rw [Q.as_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [jetLin_monomial, jetLin_monomial, hJ]
  intro τ
  have hw := congrFun (hQ (MvPolynomial.mem_support_iff.mp hu)) τ
  rw [weight_wD] at hw
  simpa [Finsupp.comapDomain_apply] using hw

end GlobalTheory.JetTransport

theorem GlobalTheory.jetMapTransport : ∀ (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {a b : ℕ}
    (J : (DVar D.what₂.Tau a b →₀ ℕ) → ℂ) (J' : (DVar D.what₂.Tau a b →₀ ℕ) → ℂ_[p]) (n : D.what₂.Tau → ℕ) (r : Qbar)
    (A : MvPolynomial (GL3Theta.FrV D b) Qbar) (P : MvPolynomial (GL3Theta.FrV D a) Qbar)
    (hJ : ∀ m : DVar D.what₂.Tau a b →₀ ℕ, (∀ τ, ∑ β, ∑ α, m (τ, β, α) = n τ) → ∃ x : Qbar, (x : ℂ) = J m ∧ lam x = J' m)
    (hP : ∀ e ∈ P.support, ∀ τ, ∑ α, ∑ s, e (τ, α, s) = n τ)
    (h : MvPolynomial.map (algebraMap Qbar ℂ) A = MvPolynomial.C (r : ℂ) * jetMap J (fun _ => 0) (MvPolynomial.map (algebraMap Qbar ℂ) P)), MvPolynomial.map lam A = MvPolynomial.C (lam r) * jetMap J' (fun _ => 0) (MvPolynomial.map lam P) := by
  intro D p _ lam a b J J' n r A P hJ hP h
  classical
  let x : (DVar D.what₂.Tau a b →₀ ℕ) → Qbar := fun m =>
    if hm : ∀ τ, ∑ β, ∑ α, m (τ, β, α) = n τ then (hJ m hm).choose else 0
  have hx1 : ∀ m : DVar D.what₂.Tau a b →₀ ℕ, (∀ τ, ∑ β, ∑ α, m (τ, β, α) = n τ) →
      J m = (algebraMap Qbar ℂ ∘ x) m := by
    intro m hm
    simp only [x, Function.comp_apply, dif_pos hm]
    exact (hJ m hm).choose_spec.1.symm
  have hx2 : ∀ m : DVar D.what₂.Tau a b →₀ ℕ, (∀ τ, ∑ β, ∑ α, m (τ, β, α) = n τ) →
      J' m = (lam ∘ x) m := by
    intro m hm
    simp only [x, Function.comp_apply, dif_pos hm]
    exact (hJ m hm).choose_spec.2.symm
  have hPw : ∀ {K : Type} [Field K] (f : Qbar →+* K),
      MvPolynomial.IsWeightedHomogeneous (GlobalTheory.JetTransport.wF D.what₂.Tau a) (MvPolynomial.map f P) n := by
    intro K _ f d hd
    funext τ
    rw [GlobalTheory.JetTransport.weight_wF]
    refine hP d (MvPolynomial.mem_support_iff.mpr fun h0 => hd ?_) τ
    rw [MvPolynomial.coeff_map, h0, map_zero]
  have key : ∀ {K : Type} [Field K] (f : Qbar →+* K) (JK : (DVar D.what₂.Tau a b →₀ ℕ) → K),
      (∀ m : DVar D.what₂.Tau a b →₀ ℕ, (∀ τ, ∑ β, ∑ α, m (τ, β, α) = n τ) → JK m = (f ∘ x) m) →
      jetMap JK (fun _ => 0) (MvPolynomial.map f P) = MvPolynomial.map f (jetMap x (fun _ => 0) P) := by
    intro K _ f JK hJK
    rw [GlobalTheory.JetTransport.jetMap_zero, GlobalTheory.JetTransport.jetMap_zero, ← GlobalTheory.JetTransport.jetLin_map,
      ← GlobalTheory.JetTransport.subD_map]
    exact GlobalTheory.JetTransport.jetLin_congr _ _ n _ (GlobalTheory.JetTransport.subD_hom _ n (hPw f)) hJK
  have hA : A = MvPolynomial.C r * jetMap x (fun _ => 0) P := by
    apply MvPolynomial.map_injective (algebraMap Qbar ℂ) (algebraMap Qbar ℂ).injective
    rw [h, key (algebraMap Qbar ℂ) J hx1, map_mul, MvPolynomial.map_C]
    rfl
  rw [hA, map_mul, MvPolynomial.map_C, key lam J' hx2]
end
