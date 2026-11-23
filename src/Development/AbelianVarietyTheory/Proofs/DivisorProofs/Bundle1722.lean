module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnramifiedLocalSituationOfEmbedding
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Monotonicity.Lemmas
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PtCoeffSingleSubst
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.TangentEqLcZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.BiextCoeffSecondLinear
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv.CoeffCont

open MvPowerSeries

theorem coe_le_add {a b : WithTop ℝ} {x y : ℝ} (ha : (x : WithTop ℝ) ≤ a) (hb : (y : WithTop ℝ) ≤ b) :
    ((x + y : ℝ) : WithTop ℝ) ≤ a + b := by
  rw [WithTop.coe_add]; exact add_le_add ha hb

theorem poly_bound {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {κ : Type} (Q : MvPolynomial κ C) :
    ∃ K : ℝ, ∀ (N : ℝ) (s s' : κ → C), (∀ k, (0 : WithTop ℝ) ≤ v (s k)) → (∀ k, (0 : WithTop ℝ) ≤ v (s' k)) →
      (∀ k, ((N : ℝ) : WithTop ℝ) ≤ v (s k - s' k)) →
      ((N - K : ℝ) : WithTop ℝ) ≤ v (MvPolynomial.eval s Q - MvPolynomial.eval s' Q) ∧
      ((-K : ℝ) : WithTop ℝ) ≤ v (MvPolynomial.eval s Q) := by
  induction Q using MvPolynomial.induction_on
  · rename_i c
    by_cases ht : v c = ⊤
    · refine ⟨0, fun N s s' _ _ _ => ?_⟩
      simp only [MvPolynomial.eval_C, sub_self, AddValuation.map_zero, ht, le_top, and_self]
    · obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp ht
      refine ⟨-r, fun N s s' _ _ _ => ?_⟩
      simp only [MvPolynomial.eval_C, sub_self, AddValuation.map_zero, ← hr, le_top, neg_neg, le_refl, and_self]
  · rename_i p q hp hq
    obtain ⟨K₁, h₁⟩ := hp
    obtain ⟨K₂, h₂⟩ := hq
    refine ⟨max K₁ K₂, fun N s s' hs hs' hss => ?_⟩
    obtain ⟨a₁, b₁⟩ := h₁ N s s' hs hs' hss
    obtain ⟨a₂, b₂⟩ := h₂ N s s' hs hs' hss
    rw [map_add (MvPolynomial.eval s), map_add (MvPolynomial.eval s')]
    constructor
    · have e : MvPolynomial.eval s p + MvPolynomial.eval s q - (MvPolynomial.eval s' p + MvPolynomial.eval s' q) =
          (MvPolynomial.eval s p - MvPolynomial.eval s' p) + (MvPolynomial.eval s q - MvPolynomial.eval s' q) := by ring
      rw [e]
      refine le_trans (le_min ?_ ?_) (v.map_add _ _)
      · exact le_trans (WithTop.coe_le_coe.mpr (by linarith [le_max_left K₁ K₂])) a₁
      · exact le_trans (WithTop.coe_le_coe.mpr (by linarith [le_max_right K₁ K₂])) a₂
    · refine le_trans (le_min ?_ ?_) (v.map_add _ _)
      · exact le_trans (WithTop.coe_le_coe.mpr (by linarith [le_max_left K₁ K₂])) b₁
      · exact le_trans (WithTop.coe_le_coe.mpr (by linarith [le_max_right K₁ K₂])) b₂
  · rename_i p k hp
    obtain ⟨K, h⟩ := hp
    refine ⟨K, fun N s s' hs hs' hss => ?_⟩
    obtain ⟨a, b⟩ := h N s s' hs hs' hss
    rw [map_mul (MvPolynomial.eval s), map_mul (MvPolynomial.eval s'), MvPolynomial.eval_X, MvPolynomial.eval_X]
    constructor
    · have e : MvPolynomial.eval s p * s k - MvPolynomial.eval s' p * s' k =
          (MvPolynomial.eval s p - MvPolynomial.eval s' p) * s k + MvPolynomial.eval s' p * (s k - s' k) := by ring
      rw [e]
      refine le_trans (le_min ?_ ?_) (v.map_add _ _)
      · rw [v.map_mul]
        have := coe_le_add (y := 0) a (hs k)
        rwa [add_zero] at this
      · rw [v.map_mul]
        have := coe_le_add (h N s' s' hs' hs' (fun k => by rw [sub_self, v.map_zero]; exact le_top)).2 (hss k)
        have e2 : (-K + N : ℝ) = N - K := by ring
        rw [e2] at this
        exact this
    · rw [v.map_mul]
      have := coe_le_add (y := 0) b (hs k)
      rwa [add_zero] at this

theorem coeff_subst_eq_eval {C : Type} [Field C] {τ σ ι : Type} [Fintype τ] [Fintype ι]
    (W : MvPowerSeries τ C) (g : ι → MvPowerSeries σ C) (hg : ∀ i, constantCoeff (g i) = 0) (α : σ →₀ ℕ) :
    ∃ Q : MvPolynomial (τ × ι) C, ∀ s : τ → ι → C,
      coeff α (subst (fun q => ∑ i, s q i • g i) W : MvPowerSeries σ C) =
        MvPolynomial.eval (fun x => s x.1 x.2) Q := by
  classical
  let G : ι → MvPowerSeries σ (MvPolynomial (τ × ι) C) := fun i => (g i).map MvPolynomial.C
  let a : τ → MvPowerSeries σ (MvPolynomial (τ × ι) C) :=
    fun q => ∑ i, (MvPolynomial.X (q, i) : MvPolynomial (τ × ι) C) • G i
  have hG : ∀ i, constantCoeff (G i) = 0 := fun i => by simp [G, hg]
  have ha : HasSubst a := hasSubst_of_constantCoeff_zero (fun q => by simp [a, hG])
  refine ⟨coeff α (subst a (W.map (MvPolynomial.C : C →+* MvPolynomial (τ × ι) C)) :
    MvPowerSeries σ (MvPolynomial (τ × ι) C)), fun s => ?_⟩
  have h1 := congrArg (coeff α) (map_subst ha (h := MvPolynomial.eval (fun x : τ × ι => s x.1 x.2))
    (W.map (MvPolynomial.C : C →+* MvPolynomial (τ × ι) C)))
  rw [coeff_map] at h1
  have hW : (W.map (MvPolynomial.C : C →+* MvPolynomial (τ × ι) C)).map
      (MvPolynomial.eval (fun x : τ × ι => s x.1 x.2)) = W := by
    ext n; simp [coeff_map]
  have hA : (fun q => (a q).map (MvPolynomial.eval (fun x : τ × ι => s x.1 x.2))) =
      fun q => ∑ i, s q i • g i := by
    funext q; ext n; simp [a, G, coeff_map, map_sum]
  rw [h1, hW, hA]

end GlobalTheory.IsoTriv.CoeffCont

namespace GlobalTheory.IsoTriv

open MvPowerSeries

theorem contSt_holds : ContSt := by
  intro C _ v τ σ ι _ _ _ W g hg α
  obtain ⟨Q, hQ⟩ := CoeffCont.coeff_subst_eq_eval W g hg α
  obtain ⟨K, hK⟩ := CoeffCont.poly_bound v Q
  refine ⟨⌈K⌉₊, fun s s' hs hs' hss => ?_⟩
  rw [hQ, hQ]
  have h := (hK (⌈K⌉₊ : ℝ) (fun x => s x.1 x.2) (fun x => s' x.1 x.2) (fun x => hs _ _) (fun x => hs' _ _)
    (fun x => hss _ _)).1
  show (0 : WithTop ℝ) ≤ _
  refine le_trans ?_ h
  rw [← WithTop.coe_zero, WithTop.coe_le_coe]
  linarith [Nat.le_ceil K]

end GlobalTheory.IsoTriv
end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv

open MvPowerSeries ReciprocityTheory.PGsh

section Unit

variable {C : Type} [Field C] [CharZero C] {σ : Type}

theorem expU_add (s t : MvPowerSeries σ C) (hs : constantCoeff s = 0) (ht : constantCoeff t = 0) :
    PowerSeries.subst (s + t) (PowerSeries.exp C) =
      PowerSeries.subst s (PowerSeries.exp C) * PowerSeries.subst t (PowerSeries.exp C) := by
  have hst : MvPowerSeries.HasSubst ![s, t] :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (by intro i; fin_cases i <;> simp [hs, ht])
  have comp : ∀ p : MvPowerSeries (Fin 2) C, constantCoeff p = 0 →
      MvPowerSeries.subst ![s, t] (PowerSeries.subst p (PowerSeries.exp C)) =
        PowerSeries.subst (MvPowerSeries.subst ![s, t] p) (PowerSeries.exp C) := by
    intro p hp
    unfold PowerSeries.subst
    rw [MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero hp).const hst]
  have H := congrArg (MvPowerSeries.subst ![s, t]) (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_subst_add_two_vars C)
  rw [MvPowerSeries.subst_mul hst, comp _ (by simp), comp _ (by simp), comp _ (by simp),
    MvPowerSeries.subst_add hst, MvPowerSeries.subst_X hst, MvPowerSeries.subst_X hst] at H
  simpa using H

theorem cc_expU (s : MvPowerSeries σ C) (hs : constantCoeff s = 0) :
    constantCoeff (PowerSeries.subst s (PowerSeries.exp C)) = 1 := by
  rw [PowerSeries.constantCoeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hs), finsum_eq_single _ 0]
  · simp
  · intro e he
    simp [map_pow, hs, zero_pow he]

theorem expU_zero : PowerSeries.subst (0 : MvPowerSeries σ C) (PowerSeries.exp C) = 1 := by
  have h := expU_add (0 : MvPowerSeries σ C) 0 (by simp) (by simp)
  rw [add_zero] at h
  have hu : IsUnit (PowerSeries.subst (0 : MvPowerSeries σ C) (PowerSeries.exp C)) := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff, cc_expU _ (by simp)]
    exact isUnit_one
  exact hu.mul_left_cancel (by rw [mul_one]; exact h.symm)

omit [CharZero C] in
theorem inv_int (v : AddValuation C (WithTop ℝ)) (U : MvPowerSeries σ C) (hU : MvIsInt v U)
    (h1 : constantCoeff U = 1) : ∃ U', MvIsInt v U' ∧ U * U' = 1 := by
  set S := ReciprocityTheory.ChartRestriction.G.Sh.PTb.intRing v
  let U' : MvPowerSeries σ S := fun α => ⟨coeff α U, hU α⟩
  have hU' : map S.subtype U' = U := by ext α; rfl
  have hc : constantCoeff U' = ((1 : Sˣ) : S) := by
    apply Subtype.ext
    change coeff 0 U = 1
    rw [coeff_zero_eq_constantCoeff_apply, h1]
  refine ⟨map S.subtype (invOfUnit U' 1), fun α => ?_, ?_⟩
  · rw [coeff_map]; exact (coeff α (invOfUnit U' 1)).2
  · rw [← hU', ← map_mul, mul_invOfUnit U' 1 hc, map_one]

theorem unitSt : UnitSt := by
  intro C _ _ v σ _
  have hexp0 := expU_zero (C := C) (σ := σ)
  refine ⟨⟨by simp, ?_⟩, ?_, ?_, fun s t hs ht => expU_add s t hs ht, fun s hs => cc_expU s hs,
    fun U hU h1 => inv_int v U hU h1⟩
  · rw [hexp0]; exact Subring.one_mem (ReciprocityTheory.ChartRestriction.G.Sh.ptIntSer v σ)
  · rintro s t ⟨hs0, hs⟩ ⟨ht0, ht⟩
    refine ⟨by simp [hs0, ht0], ?_⟩
    rw [expU_add s t hs0 ht0]
    exact Subring.mul_mem (ReciprocityTheory.ChartRestriction.G.Sh.ptIntSer v σ) hs ht
  · rintro s ⟨hs0, hs⟩
    have hn0 : constantCoeff (-s) = 0 := by simp [hs0]
    refine ⟨hn0, ?_⟩
    obtain ⟨U', hU', hm⟩ := inv_int v _ hs (cc_expU s hs0)
    have e : PowerSeries.subst (-s) (PowerSeries.exp C) * PowerSeries.subst s (PowerSeries.exp C) = 1 := by
      rw [← expU_add _ _ hn0 hs0, neg_add_cancel, hexp0]
    have : PowerSeries.subst (-s) (PowerSeries.exp C) = U' := by
      calc PowerSeries.subst (-s) (PowerSeries.exp C)
          = PowerSeries.subst (-s) (PowerSeries.exp C) * (PowerSeries.subst s (PowerSeries.exp C) * U') := by
            rw [hm, mul_one]
        _ = U' := by rw [← mul_assoc, e, one_mul]
    rw [this]; exact hU'

end Unit

end GlobalTheory.IsoTriv
end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv

open NumberField IsDedekindDomain MvPowerSeries
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.LawLog GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns

section NabAux

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}


open Classical in
def colCoef {k : Type} [Field k] {n : ℕ} (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → k) (cx : Lt1 Dw → ℕ)
    (lam : Let cx) (ℓ : LtN Dw n) : k :=
  ∑ j : Fin n, if ℓ = ⟨lam.1.1.1.1, Fin.castLE (rk_le _) lam.2, j⟩ then B lam.1.1.1 lam.1.2 j else 0

theorem sum_colCoef_smul {k : Type} [Field k] {n : ℕ} (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → k) (cx : Lt1 Dw → ℕ)
    (lam : Let cx) {M : Type} [AddCommGroup M] [Module k M] (x : LtN Dw n → M) :
    ∑ ℓ, colCoef B cx lam ℓ • x ℓ =
      ∑ j : Fin n, B lam.1.1.1 lam.1.2 j • x ⟨lam.1.1.1.1, Fin.castLE (rk_le _) lam.2, j⟩ := by
  classical
  simp only [colCoef, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single (⟨lam.1.1.1.1, Fin.castLE (rk_le _) lam.2, j⟩ : LtN Dw n)]
  · rw [if_pos rfl]
  · intro b _ hb
    rw [if_neg hb, zero_smul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem polyP_eq_aeval {k : Type} [Field k] {n : ℕ} (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → k) (cx : Lt1 Dw → ℕ) :
    polyP B cx = MvPolynomial.aeval (fun lam : Let cx => ∑ ℓ, MvPolynomial.C (colCoef B cx lam ℓ) *
      (MvPolynomial.X ℓ : MvPolynomial (LtN Dw n) k)) (polyH k cx) := by
  classical
  unfold polyP polyH
  rw [map_prod, ← Finset.prod_filter_of_ne (p := fun f => cx f ≠ 0)
    (fun f _ hf h0 => hf (by rw [h0, pow_zero])),
    Finset.prod_subtype (p := fun f => cx f ≠ 0) (F := inferInstance) _ (by simp)]
  refine Finset.prod_congr rfl fun f _ => ?_
  rw [MvPolynomial.aeval_rename, detPow, map_pow, AlgHom.map_det, ← Matrix.det_transpose]
  congr 2
  ext1 a b
  simp only [GlobalTheory.CombMinor.cMat, Matrix.transpose_apply, Matrix.of_apply, AlgHom.mapMatrix_apply, Matrix.map_apply,
    MvPolynomial.aeval_X, Function.comp_apply, MvPolynomial.C_mul']
  rw [sum_colCoef_smul]

theorem map_polyP {k k' : Type} [Field k] [Field k'] (φ : k →+* k') {n : ℕ}
    (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → k) (cx : Lt1 Dw → ℕ) :
    MvPolynomial.map φ (polyP B cx) = polyP (fun f b j => φ (B f b j)) cx := by
  unfold polyP
  rw [map_prod]
  refine Finset.prod_congr rfl fun f _ => ?_
  rw [map_pow, RingHom.map_det]
  congr 2
  ext1 a b
  simp [GlobalTheory.CombMinor.cMat]

theorem subst_colCoef_expPt {k : Type} [Field k] {v : AddValuation k (WithTop ℝ)} {d n : ℕ} (G : LogFGL v d)
    (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → k) (cx : Lt1 Dw → ℕ) (u : Lt1 Dw → Fin d → k) (Φ : PS k n d) :
    subst (fun ℓ : LtN Dw n => ∑ lam : Let cx, colCoef B cx lam ℓ • (X lam : MvPowerSeries (Let cx) k))
      (subst (fun q : Fin n × Fin d => expPt G (fun e => ∑ ℓ : LtN Dw n,
        (if ℓ.2.2 = q.1 then u ⟨ℓ.1, ℓ.2.1⟩ e else 0) • (X ℓ : MvPowerSeries (LtN Dw n) k)) q.2) Φ) =
    subst (fun q : Fin n × Fin d => expPt G (fun e => ∑ lam : Let cx,
      (B lam.1.1.1 lam.1.2 q.1 * u ⟨lam.1.1.1.1, Fin.castLE (rk_le _) lam.2⟩ e) •
        (X lam : MvPowerSeries (Let cx) k)) q.2) Φ := by
  have ht : HasSubst (fun ℓ : LtN Dw n => ∑ lam : Let cx, colCoef B cx lam ℓ •
      (X lam : MvPowerSeries (Let cx) k)) := hasSubst_of_constantCoeff_zero (by simp)
  have hw : ∀ (j : Fin n) (e : Fin d), constantCoeff (∑ ℓ : LtN Dw n,
      (if ℓ.2.2 = j then u ⟨ℓ.1, ℓ.2.1⟩ e else 0) • (X ℓ : MvPowerSeries (LtN Dw n) k)) = 0 := by
    intro j e

    rw [map_sum]
    exact Finset.sum_eq_zero fun ℓ _ => by rw [constantCoeff_smul, constantCoeff_X, smul_zero]
  have hs : HasSubst (fun q : Fin n × Fin d => expPt G (fun e => ∑ ℓ : LtN Dw n,
      (if ℓ.2.2 = q.1 then u ⟨ℓ.1, ℓ.2.1⟩ e else 0) • (X ℓ : MvPowerSeries (LtN Dw n) k)) q.2) :=
    hasSubst_of_constantCoeff_zero fun q => cc_expPt G (hw q.1) q.2
  refine (subst_comp_subst_apply hs ht Φ).trans (congrArg (fun s => subst s Φ) (funext fun q => ?_))
  refine (subst_expPt G ht (hw q.1) q.2).trans (congrArg (fun s => expPt G s q.2) (funext fun e => ?_))

  simp only [← coe_substAlgHom ht, map_sum, map_smul]
  simp only [coe_substAlgHom, subst_X ht, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun lam _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  have h := sum_colCoef_smul B cx lam
    (fun ℓ : LtN Dw n => if ℓ.2.2 = q.1 then u ⟨ℓ.1, ℓ.2.1⟩ e else 0)
  simp only [smul_eq_mul] at h
  rw [Finset.sum_congr rfl fun ℓ _ => mul_comm _ _, h]
  simp

end NabAux

theorem nabSt_of : InvDerSt → LinSt → FrameSt → NabSt := by
  intro hI hL hF E _ _ _ H Dw l Xo c _ T io y Ch p _ X cx n B k g
  let _ := io.toAlgebra
  let _ : Algebra T.Fr X.C := X.ιF.toAlgebra
  have hfr := (hF X.C (vX_vp X) (chD Ch.ch) T.Fr (𝓞 E) Ch.ch.B (isIntFB_chart Ch X) _ (gauge_chart Ch X) H.w0 n).2.1 k
  have hinv := hI X.C (vX_vp X) (chD Ch.ch) (lawX Ch X) (fgl Ch X).F_int n (LtN Dw n) (fun ℓ => ℓ.2.2)
    (fun ℓ => lieVec Ch X ⟨ℓ.1, ℓ.2.1⟩) (MvPolynomial.map X.ιF (polyT B cx)) (g * frameX Ch X n ^ k)
  have hP : MvPolynomial.map X.ιF (polyT B cx) = polyP (fun f b j => jX X (B f b j)) cx := map_polyP _ _ _
  unfold nabX nabValN
  rw [hfr]
  refine Eq.trans hinv ?_
  rw [hP, polyP_eq_aeval, hL]
  exact congrArg (derivAt0 (polyH X.C cx))
    (subst_colCoef_expPt (fgl Ch X) (fun f b j => jX X (B f b j)) cx (lieVec Ch X) (g * frameX Ch X n ^ k))

end GlobalTheory.IsoTriv
end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv.HermRead

open MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.TB (dAct)

section Lin

variable {C : Type} [Field C] {d : ℕ} {σ : Type}

theorem mv_sum (A : Matrix (Fin d) (Fin d) C) {β : Type} (s : Finset β) (x : β → Fin d → MvPowerSeries σ C) :
    mv A (∑ b ∈ s, x b) = ∑ b ∈ s, mv A (x b) := by
  funext e
  simp only [mv, Finset.sum_apply, Finset.smul_sum]
  exact Finset.sum_comm

theorem mv_mv (A A' : Matrix (Fin d) (Fin d) C) (w : Fin d → MvPowerSeries σ C) :
    mv A (mv A' w) = mv (A * A') w := by
  funext e
  simp only [mv, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
  exact Finset.sum_comm

theorem add_mv (A A' : Matrix (Fin d) (Fin d) C) (w : Fin d → MvPowerSeries σ C) :
    mv (A + A') w = mv A w + mv A' w := by
  funext e
  simp only [mv, Matrix.add_apply, add_smul, Finset.sum_add_distrib, Pi.add_apply]

end Lin

theorem map_sum_of_additive {M Q : Type} [AddCommMonoid M] [AddCommGroup Q] (p : M → Prop) (h0 : p 0)
    (hp : ∀ x y, p x → p y → p (x + y)) (f : M → Q) (hf : ∀ x y, p x → p y → f (x + y) = f x + f y)
    {β : Type} (s : Finset β) (x : β → M) (hx : ∀ b, p (x b)) :
    p (∑ b ∈ s, x b) ∧ f (∑ b ∈ s, x b) = ∑ b ∈ s, f (x b) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by simpa using h0, ?_⟩
    have := hf 0 0 h0 h0
    rw [add_zero] at this
    simpa using this
  | insert b s hb ih =>
    rw [Finset.sum_insert hb, Finset.sum_insert hb]
    exact ⟨hp _ _ (hx b) ih.1, by rw [hf _ _ (hx b) ih.1, ih.2]⟩

theorem finSt_of (hAdd : AddSt) (hAct : ActSt) (hUnit : UnitSt) (hBi : BiaddSt) : FinSt := by
  intro C _ _ v d R _ _ O _ _ B hB h hg σ _ κ _ w hw w0 n a ι _ e t ht
  obtain ⟨hU0, hUadd, hUneg, -⟩ := hUnit C v σ
  obtain ⟨hI0, -, hIadd⟩ := hAdd C v d (fglOf hB) σ
  have hIact := fun c => (hAct C v d R O B hB σ c).2
  have hbi := hBi C v d R O B hB h hg σ
  let U : AddSubgroup (MvPowerSeries σ C) :=
    { carrier := {s | LogUnit v s}
      add_mem' := fun {s t} hs ht => hUadd s t hs ht
      zero_mem' := hU0
      neg_mem' := fun {s} hs => hUneg s hs }
  let π := QuotientAddGroup.mk' U
  have key : ∀ s, π s = 0 ↔ LogUnit v s := fun s => QuotientAddGroup.eq_zero_iff s
  have h1 : ∀ z, IntLog (fglOf hB) z → ∀ x y, IntLog (fglOf hB) x → IntLog (fglOf hB) y →
      π (pairSer (fglOf hB) h (x + y) z) = π (pairSer (fglOf hB) h x z) + π (pairSer (fglOf hB) h y z) := by
    intro z hz x y hx hy
    have := (key _).2 (hbi x y z hx hy hz).2.1
    rw [map_sub, map_add (f := _), sub_eq_zero] at this
    exact this.symm
  have h2 : ∀ z, IntLog (fglOf hB) z → ∀ x y, IntLog (fglOf hB) x → IntLog (fglOf hB) y →
      π (pairSer (fglOf hB) h z (x + y)) = π (pairSer (fglOf hB) h z x) + π (pairSer (fglOf hB) h z y) := by
    intro z hz x y hx hy
    have := (key _).2 (hbi x y z hx hy hz).2.2.1
    rw [map_sub, map_add (f := _), sub_eq_zero] at this
    exact this.symm
  have h3 : ∀ (c : O) x z, IntLog (fglOf hB) x → IntLog (fglOf hB) z →
      π (pairSer (fglOf hB) h (mv (dAct C B c) x) z) =
        π (pairSer (fglOf hB) h x (mv (dAct C B (star c)) z)) := by
    intro c x z hx hz
    have := (key _).2 ((hbi x x z hx hx hz).2.2.2 c)
    rwa [map_sub, sub_eq_zero] at this
  let F : κ → κ → O →+ MvPowerSeries σ C ⧸ U := fun b b' =>
    AddMonoidHom.mk' (fun c => π (pairSer (fglOf hB) h (w b) (mv (dAct C B c) (w b')))) fun c c' => by
      rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.dAct_add, add_mv]
      exact h2 _ (hw b) _ _ (hIact _ _ (hw b')) (hIact _ _ (hw b'))
  have hF : ∀ b b' c, F b b' c = π (pairSer (fglOf hB) h (w b) (mv (dAct C B c) (w b'))) := fun _ _ _ => rfl
  have hj : ∀ j, π (pairSer (fglOf hB) h (∑ b, mv (dAct C B (a b j)) (w b))
      (mv (dAct C B w0) (∑ b, mv (dAct C B (a b j)) (w b)))) =
        ∑ b, ∑ b', F b b' (star (a b j) * a b' j * w0) := by
    intro j
    have hy : IntLog (fglOf hB) (∑ b, mv (dAct C B (a b j)) (w b)) :=
      (map_sum_of_additive (IntLog (fglOf hB)) hI0 hIadd (fun _ => (0 : ℤ)) (by simp) Finset.univ _
        fun b => hIact _ _ (hw b)).1
    have hz := hIact w0 _ hy
    generalize hzz : mv (dAct C B w0) (∑ b, mv (dAct C B (a b j)) (w b)) = z at hz
    refine (map_sum_of_additive (IntLog (fglOf hB)) hI0 hIadd (fun x => π (pairSer (fglOf hB) h x z)) (h1 _ hz)
      Finset.univ _ fun b => hIact (a b j) _ (hw b)).2.trans (Finset.sum_congr rfl fun b _ => ?_)
    rw [h3 _ _ _ (hw b) hz, ← hzz, mv_mv, mv_sum, ← ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.dAct_mul]
    refine (map_sum_of_additive (IntLog (fglOf hB)) hI0 hIadd (fun x => π (pairSer (fglOf hB) h (w b) x))
      (h2 _ (hw b)) Finset.univ _ fun b' => hIact _ _ (hIact _ _ (hw b'))).2.trans
      (Finset.sum_congr rfl fun b' _ => ?_)
    rw [hF, mv_mv, ← ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.dAct_mul, mul_right_comm]

  rw [← key, map_sub, sub_eq_zero, map_sum, Finset.sum_congr rfl fun j _ => hj j, Finset.sum_comm, map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_

  rw [Finset.sum_comm, map_sum]
  refine Finset.sum_congr rfl fun b' _ => ?_

  rw [← map_sum, ← Finset.sum_mul, ht, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, Int.cast_smul_eq_zsmul, map_zsmul, hF]

end GlobalTheory.IsoTriv.HermRead
end
end

section

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace

theorem _root_.GlobalTheory.T.exists_unramifiedLocalSituation_of_embedding : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (H : LocHW l P) (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω], l ≠ 2 → ¬ (l : ℤ) ∣ NumberField.discr E → ∀ (σ : Equiv.Perm (E →+* PadicAlgCl l)), GlobalTheory.ExpFrame.IsFrobPerm σ → ∀ LL : FinExt l, (∃ ζ : ↥LL.1, IsPrimitiveRoot ζ l) → (∀ (τ : E →+* PadicAlgCl l) (x : E), τ x ∈ LL.1) → ∀ i₀ : E →+* PadicAlgCl l, ∃ (K : FinExt l) (hA : CaseA K LL) (ι : ↥(GK K) →* (Ω ≃ₐ[E] Ω)) (κ : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → (E →+* PadicAlgCl l)), Function.Injective κ ∧ (∀ i, κ (i - 1) = σ (κ i)) ∧ i₀ ∈ Set.range κ ∧ ∀ (n : ℕ) (r : (Ω ≃ₐ[E] Ω) →* GL (Fin n) ↥(OL LL)) (J : (E →+* PadicAlgCl l) → Multiset ℤ), GlobalTheory.ExpFrame.CrysWith ((Matrix.GeneralLinearGroup.map (toOm LL)).comp r) J → MatGood P (H.W K 1 LL hA.2.2).emb (r.comp ι) (fun i => J (κ i)) := by
  first | exact @GlobalTheory.PlaceLetters.exists_place | exact GlobalTheory.PlaceLetters.exists_place | (intros; apply GlobalTheory.PlaceLetters.exists_place <;> assumption)
end

end

section

@[expose] public section

open GlobalTheory.IsoTriv

theorem _root_.GlobalTheory.T.gaugeHermitianCombination_of_steps : AddSt → ActSt → UnitSt → BiaddSt → FinSt := by
  first | exact @GlobalTheory.IsoTriv.HermRead.finSt_of | exact GlobalTheory.IsoTriv.HermRead.finSt_of | (intros; apply GlobalTheory.IsoTriv.HermRead.finSt_of <;> assumption)

end
end

section

@[expose] public section

open GlobalTheory.IsoTriv

theorem _root_.GlobalTheory.T.logIntegralUnitsSubgroupExpHom_proof : UnitSt := by
  first | exact @GlobalTheory.IsoTriv.unitSt | exact GlobalTheory.IsoTriv.unitSt | (intros; apply GlobalTheory.IsoTriv.unitSt <;> assumption)

end
end

section

@[expose] public section

open GlobalTheory.IsoTriv

theorem _root_.GlobalTheory.T.nablaOperatorFrameSeries_of_steps : InvDerSt → LinSt → FrameSt → NabSt := by
  first | exact @GlobalTheory.IsoTriv.nabSt_of | exact GlobalTheory.IsoTriv.nabSt_of | (intros; apply GlobalTheory.IsoTriv.nabSt_of <;> assumption)

end
end

section

@[expose] public section

open GlobalTheory.IsoTriv

theorem _root_.GlobalTheory.T.seriesCoeffUniformlyContinuousInCoeffs_proof : ContSt := by
  first | exact @GlobalTheory.IsoTriv.contSt_holds | exact GlobalTheory.IsoTriv.contSt_holds | (intros; apply GlobalTheory.IsoTriv.contSt_holds <;> assumption)

end
end
