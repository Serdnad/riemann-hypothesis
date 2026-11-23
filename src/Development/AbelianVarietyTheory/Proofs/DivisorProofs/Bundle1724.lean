module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralInvariantDerivationLog
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormEqNegOne
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AutomorphicFormsFiniteIdeal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle280
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1687
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle007
public import CompanionTheory.AutomorphicTheory.PadicUnitaryWeights.DixmierMalliavin.DixmierMalliavinFactorisationHolds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle002
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle048
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.InvDer

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.LawLog GlobalTheory.FactorDepth
  GlobalTheory.IsoTriv

section Two

variable {K : Type} [Field K] [CharZero K] {d : ℕ}

theorem subst_secondBlockZero_twoPointVariables {ι : Type} (Y : Fin d → MvPowerSeries ι K) (hY : ∀ i, constantCoeff (Y i) = 0)
    (f : PS K 2 d) :
    subst Y (subst (GlobalTheory.LogJacobian.substSecondBlockZero (C := K) d) (subst (twoVars K d) f : MvPowerSeries (Fin d ⊕ Fin d) K) :
        MvPowerSeries (Fin d) K) =
      subst (fun q : Fin 2 × Fin d => if q.1 = 0 then Y q.2 else 0) f := by
  have hYs : HasSubst Y := hasSubst_of_constantCoeff_zero hY
  have hA := GlobalTheory.LogJacobian.hasSubst_substSecondBlockZero (C := K) d
  have hB : HasSubst (fun q : Fin 2 × Fin d => subst (GlobalTheory.LogJacobian.substSecondBlockZero (C := K) d) (twoVars K d q)) :=
    hasSubst_of_constantCoeff_zero fun q =>
      constantCoeff_subst_eq_zero hA (GlobalTheory.LogJacobian.constantCoeff_substSecondBlockZero d) (cc_twoVars q)
  rw [subst_comp_subst_apply hs_twoVars hA, subst_comp_subst_apply hB hYs]
  congr 1
  funext q
  rw [twoVars, subst_X hA]
  split_ifs with h
  · simp [GlobalTheory.LogJacobian.substSecondBlockZero, subst_X hYs]
  · simp only [GlobalTheory.LogJacobian.substSecondBlockZero, Sum.elim_inr]
    rw [← coe_substAlgHom hYs, map_zero]

theorem pderiv_inr_twoVars (k : Fin d) (f : PS K 2 d) :
    pderiv (Sum.inr k) (subst (twoVars K d) f) = subst (twoVars K d) (pderiv ((1 : Fin 2), k) f) := by
  classical
  rw [ReciprocityTheory.ChartRestriction.G.TB.LogPf.pderiv_subst cc_twoVars, Finset.sum_eq_single ((1 : Fin 2), k)]
  · simp [twoVars]
  · intro q _ hq
    obtain ⟨a, i⟩ := q
    fin_cases a
    · simp [twoVars]
    · have : i ≠ k := fun h => hq (by simp [h])
      simp [twoVars, this]
  · simp

end Two

section Main

variable {K : Type} [Field K] [CharZero K] {v : AddValuation K (WithTop ℝ)} {d n : ℕ} {ι : Type}

theorem subst_jacEntry (F : FGLaw K d) (hF : ∀ a, MvIsInt v (subst (twoVars K d) (F.F a)))
    (Y : Fin d → MvPowerSeries ι K) (hY : ∀ i, constantCoeff (Y i) = 0) (k j : Fin d) :
    subst Y (GlobalTheory.LogJacobian.jacEntry (logFGLOf v F hF) k j) =
      subst (fun q : Fin 2 × Fin d => if q.1 = 0 then Y q.2 else 0) (pderiv ((1 : Fin 2), k) (F.F j)) := by
  rw [← subst_secondBlockZero_twoPointVariables Y hY, ← pderiv_inr_twoVars]
  rfl


omit [CharZero K] in
theorem subst_ev_pt_zero [Finite ι] (T : Fin n × Fin d → MvPowerSeries ι K) (hT : ∀ q, constantCoeff (T q) = 0)
    (b : Fin n) (g : PS K 2 d) :
    subst T (ev (n := n) ![pt K d b, 0] g) =
      subst (fun q : Fin 2 × Fin d => if q.1 = 0 then T (b, q.2) else 0) g := by
  have hTs : HasSubst T := hasSubst_of_constantCoeff_zero hT
  have h2 : HasSubst (fun p : Fin 2 × Fin d => (![pt K d b, 0] : Fin 2 → Pt K n d) p.1 p.2) :=
    hasSubst_of_constantCoeff_zero fun p => by
      obtain ⟨j, i⟩ := p
      fin_cases j <;> simp [pt]
  unfold ev
  rw [subst_comp_subst_apply h2 hTs]
  congr 1
  funext p
  obtain ⟨j, i⟩ := p
  fin_cases j
  · simp [pt, subst_X hTs]
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, Pi.zero_apply, one_ne_zero, ite_false]
    rw [← coe_substAlgHom hTs, map_zero]


omit [CharZero K] in
theorem constantCoeff_subst_self {σ : Type} [Finite σ] (T : σ → MvPowerSeries ι K)
    (hT : ∀ q, constantCoeff (T q) = 0) (f : MvPowerSeries σ K) :
    constantCoeff (subst T f : MvPowerSeries ι K) = constantCoeff f := by
  have hs : HasSubst T := hasSubst_of_constantCoeff_zero hT
  have h0 : constantCoeff (subst T (f - (constantCoeff f) • 1) : MvPowerSeries ι K) = 0 :=
    constantCoeff_subst_eq_zero hs hT (by simp)
  rw [← coe_substAlgHom hs, map_sub, map_smul, map_one, coe_substAlgHom hs] at h0
  simpa [sub_eq_zero] using h0

variable [Fintype ι]

def logLin (cp : ι → Fin n) (u : ι → Fin d → K) (b : Fin n) : Fin d → MvPowerSeries ι K :=
  fun e => ∑ l, (if cp l = b then u l e else 0) • (X l : MvPowerSeries ι K)

omit [CharZero K] in
theorem cc_logLin (cp : ι → Fin n) (u : ι → Fin d → K) (b : Fin n) (e : Fin d) :
    constantCoeff (logLin cp u b e) = 0 := by

  simp only [logLin, map_sum, constantCoeff_smul, constantCoeff_X, smul_zero, Finset.sum_const_zero]

omit [CharZero K] in
theorem pderiv_logLin (cp : ι → Fin n) (u : ι → Fin d → K) (b : Fin n) (e : Fin d) (l : ι) :
    pderiv l (logLin cp u b e) = if cp l = b then C (u l e) else 0 := by
  classical
  unfold logLin

  rw [map_sum, Finset.sum_eq_single l]
  · rw [Derivation.map_smul, pderiv_X_self, smul_eq_C_mul, mul_one]
    split_ifs <;> simp
  · intro l' _ hl
    rw [Derivation.map_smul, pderiv_X_of_ne hl, smul_zero]
  · simp

theorem pderiv_subst_expPt (F : FGLaw K d) (hF : ∀ a, MvIsInt v (subst (twoVars K d) (F.F a)))
    (cp : ι → Fin n) (u : ι → Fin d → K) (l : ι) (Φ : PS K n d) :
    subst (fun q : Fin n × Fin d => expPt (logFGLOf v F hF) (logLin cp u q.1) q.2) (DofN F.F (cp l) (u l) Φ) =
      pderiv l (subst (fun q : Fin n × Fin d => expPt (logFGLOf v F hF) (logLin cp u q.1) q.2) Φ) := by
  classical
  set G := logFGLOf v F hF with hG
  set T : Fin n × Fin d → MvPowerSeries ι K := fun q => expPt G (logLin cp u q.1) q.2 with hTdef
  have hT : ∀ q, constantCoeff (T q) = 0 := fun q => cc_expPt G (cc_logLin cp u q.1) q.2
  have hTs : HasSubst T := hasSubst_of_constantCoeff_zero hT
  have key : ∀ b j, pderiv l (T (b, j)) = if cp l = b then
      ∑ i : Fin d, C (u l i) * subst T (ev (n := n) ![pt K d b, 0] (pderiv ((1 : Fin 2), i) (F.F j))) else 0 := by
    intro b j
    have h1 : pderiv l (T (b, j)) = ∑ i, subst (logLin cp u b) (pderiv i (expOf G j)) *
        pderiv l (logLin cp u b i) :=
      ReciprocityTheory.ChartRestriction.G.TB.LogPf.pderiv_subst (cc_logLin cp u b) (expOf G j) l
    have h2 : ∀ i, subst (logLin cp u b) (pderiv i (expOf G j)) =
        subst T (ev (n := n) ![pt K d b, 0] (pderiv ((1 : Fin 2), i) (F.F j))) := by
      intro i
      rw [GlobalTheory.LogJacobian.pderiv_expOf, subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (isExp_expOf G).1)
        (hasSubst_of_constantCoeff_zero (cc_logLin cp u b)), subst_ev_pt_zero T hT]
      exact subst_jacEntry F hF (fun e => T (b, e)) (fun e => hT (b, e)) i j
    rw [h1]
    simp only [h2, pderiv_logLin]
    split_ifs
    · exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    · simp
  rw [ReciprocityTheory.ChartRestriction.G.TB.LogPf.pderiv_subst hT, Fintype.sum_prod_type, Finset.sum_eq_single (cp l)]
  · unfold DofN
    simp only [key, ite_true]

    rw [← coe_substAlgHom hTs, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_

    rw [map_mul, map_sum, mul_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, coe_substAlgHom hTs, subst_C]
  · intro b _ hb
    simp [key, Ne.symm hb]
  · simp

end Main

theorem invDer : InvDerSt := by
  intro K _ _ v d F hF n ι _ cp u P Φ
  classical
  show _ = derivAt0 P (subst (fun q : Fin n × Fin d => expPt (logFGLOf v F hF) (logLin cp u q.1) q.2) Φ)
  have hk := pderiv_subst_expPt F hF cp u
  set T : Fin n × Fin d → MvPowerSeries ι K := fun q => expPt (logFGLOf v F hF) (logLin cp u q.1) q.2
  have hT : ∀ q, constantCoeff (T q) = 0 := fun q => cc_expPt _ (cc_logLin cp u q.1) q.2
  have hit : ∀ (l : ι) (c : ℕ) (g : PS K n d),
      subst T ((DofN F.F (cp l) (u l))^[c] g) = (pderiv l)^[c] (subst T g : MvPowerSeries ι K) := by
    intro l c
    induction c with
    | zero => intro g; rfl
    | succ c ih => intro g; rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, hk]
  have hfold : ∀ (m : ι →₀ ℕ) (L : List ι),
      subst T (L.foldr (fun l g => (DofN F.F (cp l) (u l))^[m l] g) Φ) =
        L.foldr (fun l g => (pderiv l)^[m l] g) (subst T Φ : MvPowerSeries ι K) := by
    intro m L
    induction L with
    | nil => rfl
    | cons a L ih => rw [List.foldr_cons, List.foldr_cons, hit, ih]
  unfold DpolyN derivAt0

  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, constantCoeff_C, mul_assoc, ← constantCoeff_subst_self T hT]
  congr 1
  unfold DmonN
  rw [hfold, ← coeff_zero_eq_constantCoeff_apply,
    ReciprocityTheory.ChartRestriction.G.TB.MV.coeff_fold (fun l : ι => l) (fun _ _ h => h) m _ _ (Finset.nodup_toList _) 0,
    Finset.sum_map_toList, Finset.prod_map_toList]
  have h1 : (∑ l, m l • Finsupp.single l 1 : ι →₀ ℕ) = m := by
    simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    exact Finsupp.univ_sum_single m
  have h2 : (mfact m : K) = ∏ l, ((m l).factorial : K) := Finsupp.prod_fintype _ _ (by simp)
  simp only [zero_add, Finsupp.coe_zero, Pi.zero_apply, Nat.one_ascFactorial]
  rw [h1, h2, mul_comm]

end GlobalTheory.InvDer
end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv

open NumberField IsDedekindDomain MvPowerSeries
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.LawLog GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns

theorem mv_sum_smul_X {C : Type} [Field C] {d : ℕ} {σ : Type} [Fintype σ] (A : Matrix (Fin d) (Fin d) C)
    (s : σ → C) (g : σ → Fin d → C) (e : Fin d) :
    mv A (fun e' => ∑ ℓ, (s ℓ * g ℓ e') • (MvPowerSeries.X ℓ : MvPowerSeries σ C)) e =
      ∑ ℓ, (s ℓ * A.mulVec (g ℓ) e) • (MvPowerSeries.X ℓ : MvPowerSeries σ C) := by
  simp only [mv, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ℓ _ => Finset.sum_congr rfl fun e' _ => ?_
  rw [mul_left_comm]

theorem subst_expPt_sum_mv {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d n : ℕ} {σ κ : Type} [Fintype κ]
    (G : LogFGL v d) (w : Fin n → Fin d → MvPowerSeries σ C) (hw : ∀ j e, constantCoeff (w j e) = 0)
    (r : κ → Fin n) (A : κ → Matrix (Fin d) (Fin d) C) (i : Fin d) :
    subst (fun q : Fin n × Fin d => expPt G (w q.1) q.2)
        (expPt G (∑ b, mv (A b) (lgPt G fun e => (MvPowerSeries.X (r b, e) : MvPowerSeries (Fin n × Fin d) C))) i) =
      expPt G (fun e => ∑ b, mv (A b) (w (r b)) e) i := by
  have ht : HasSubst (fun q : Fin n × Fin d => expPt G (w q.1) q.2) :=
    hasSubst_of_constantCoeff_zero fun q => cc_expPt G (hw q.1) q.2
  have hl : ∀ b e, constantCoeff
      (lgPt G (fun e => (MvPowerSeries.X (r b, e) : MvPowerSeries (Fin n × Fin d) C)) e) = 0 :=
    fun b => cc_lgPt G (by simp)

  rw [subst_expPt G ht (fun e => by
  rw [Finset.sum_apply, map_sum]; exact Finset.sum_eq_zero fun b _ => cc_mv _ (hl b) e)]
  congr 1
  funext e

  rw [Finset.sum_apply, ← coe_substAlgHom ht, map_sum, coe_substAlgHom]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [subst_mv ht]
  congr 1
  funext e'
  rw [subst_lgPt G ht (by simp)]
  simp only [subst_X ht]
  exact congrFun (lgPt_expPt G (hw (r b))) e'

theorem retrSt_of : LimActSt → LimPtSt → InvSt → RetrSt := by
  intro hAct hPt hInv E _ _ _ H Dw l Xo c _ hstar T io y Ch p _ X cx n B hB
  classical
  obtain ⟨blk, hblk⟩ := hB
  have key : ∀ f : {f : Lt1 Dw // cx f ≠ 0}, ∃ ρf : Fin (rk f.1) → Fin (chD Ch.ch) → PS X.C n (chD Ch.ch),
      (∀ β i, constantCoeff (ρf β i) = 0) ∧ (∀ β i, MvIsInt (vX_vp X) (ρf β i)) ∧
      ∀ β i, subst (colPt Ch X cx B) (ρf β i) = expH Ch X cx ⟨⟨f, β⟩, i⟩ := by
    intro f
    obtain ⟨hS, ⟨r, hr⟩, hx⟩ := hblk f
    obtain ⟨φ, hφ⟩ := GlobalTheory.IsoCols.exists_lift T (io.comp (embK c f.1.1))
    have inj := IsFractionRing.injective T.V T.Fr
    have hp0 : (p : T.V) ≠ 0 := fun h => by
      have h1 := congrArg (jX X) h
      rw [map_natCast, map_zero] at h1
      exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast h1)
    have hM : ∀ b b' (N : ℕ), ∃ a z,
        φ a = (Matrix.of fun b b' => B f.1 b (r b')) b b' + φ (p : 𝓞 E) ^ N * z := fun b b' N => by
      obtain ⟨x, -, hx2, -⟩ := hx N
      obtain ⟨z, hz⟩ := hx2 b (r b')
      exact ⟨x b (r b'), z, inj (by rw [hφ, map_natCast φ]; exact hz)⟩
    obtain ⟨M', hMM', hM'⟩ := hInv (𝓞 E) T.V φ (p : 𝓞 E) (by rw [map_natCast]; exact hp0)
      (by rw [map_natCast]; exact not_isUnit_p X) (rk f.1) _ hr hM
    obtain ⟨ε, hε⟩ := hAct E H Dw l Xo c hstar T io y Ch p X f.1.1
    choose x z hxz using hM'
    choose A hA1 hA2 using fun β' β => hε (M' β' β) (x β' β) fun N =>
      ⟨z β' β N, by rw [← map_natCast φ p, ← hxz, hφ]; rfl⟩
    have hint : ∀ β, IntLog (fgl Ch X) (∑ β', mv (A β' β)
        (lgPt (fgl Ch X) fun e => (MvPowerSeries.X (r β', e) : PS X.C n (chD Ch.ch)))) := fun β => by
      letI := io.toAlgebra
      letI : Algebra T.Fr X.C := X.ιF.toAlgebra
      exact hPt X.C (vX_vp X) _ T.Fr (𝓞 E) Ch.ch.B (isIntFB_chart Ch X) _ (Fin (rk f.1)) _
        (fun β' => intLog_lgPt_X (fgl Ch X) fun e => (r β', e)) (fun β' => A β' β)
        (fun N β' => ε N * x β' β N) fun N β' => hA1 β' β N
    have hz : ∀ f' : {f : Lt1 Dw // cx f ≠ 0}, f' ≠ f → ∀ b β', B f'.1 b (r β') = 0 := fun f' hf b β' => by
      refine (hblk f').1 b _ fun ⟨j', hj'⟩ => ?_
      by_cases hm : r β' ∈ Set.range fun j => blk ⟨f, j⟩
      · obtain ⟨j, hj⟩ := hm
        exact hf (congrArg Sigma.fst (blk.injective (hj'.trans hj.symm)))
      · rw [Matrix.det_eq_zero_of_column_eq_zero β' fun b => hS b _ hm] at hr
        exact not_isUnit_zero hr
    refine ⟨fun β => expPt (fgl Ch X) _, fun β => cc_expPt _ (hint β).1, fun β => (hint β).2, fun β i => ?_⟩
    refine (subst_expPt_sum_mv (fgl Ch X) (fun j e => ∑ ℓ : Let cx,
      (jX X (B ℓ.1.1.1 ℓ.1.2 j) * frame Ch X ℓ.1.1.1 ℓ.2 e) • (MvPowerSeries.X ℓ : MvPowerSeries (Let cx) X.C))
      (fun j e => by simp) r (fun β' => A β' β) i).trans ?_
    show expPt _ _ i = expPt (fgl Ch X) (fun e => ∑ a, frame Ch X f.1 a e •
      (MvPowerSeries.X ⟨⟨f, β⟩, a⟩ : MvPowerSeries (Let cx) X.C)) i
    congr 1
    funext e
    simp_rw [mv_sum_smul_X]
    have hc : ∀ (b : Fin (rk f.1)) (a : Fin (rk f.1)),
        ∑ β', jX X (B f.1 b (r β')) * (A β' β).mulVec (frame Ch X f.1 a) e =
          if b = β then frame Ch X f.1 a e else 0 := fun b a => by
      have h1 := congrArg (jX X) (congrFun (congrFun hMM' b) β)

      rw [Matrix.mul_apply, map_sum, Matrix.one_apply] at h1
      simp only [frame, hA2, Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← Finset.sum_mul, ← map_mul]
      rw [show ∑ β', jX X (B f.1 b (r β') * M' β' β) = _ from h1]
      split_ifs <;> simp
    rw [Finset.sum_comm, Fintype.sum_sigma, Finset.sum_eq_single (⟨f, β⟩ : Col cx)]
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_smul, hc, if_pos rfl]
    · rintro ⟨f', b⟩ - hne
      refine Finset.sum_eq_zero fun a _ => ?_
      rw [← Finset.sum_smul]
      by_cases hf : f' = f
      · subst hf
        rw [hc, if_neg fun h => hne (by rw [show b = β from h]), zero_smul]
      · simp [hz f' hf]
    · exact fun h => absurd (Finset.mem_univ _) h
  choose ρf h1 h2 h3 using key
  exact ⟨fun q => ρf q.1.1 q.1.2 q.2, fun q => h1 _ _ _, fun q => h2 _ _ _, fun q => h3 _ _ _⟩

end GlobalTheory.IsoTriv
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies
open scoped TensorProduct

namespace GlobalTheory.CentralOps

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}


open Classical in
def lieRep (R : RealPoints θ V) : GlobalTheory.AutFinLit.LieC V →ₗ⁅ℂ⁆ Module.End ℂ (SmF θ V) :=
  DirectSum.toLieAlgebra _ (fun τ => (envRep R τ).toLieHom.comp (UniversalEnvelopingAlgebra.ι ℂ)) fun τ τ' h x y => by
    change (envRep R τ (UniversalEnvelopingAlgebra.ι ℂ x)) * envRep R τ' (UniversalEnvelopingAlgebra.ι ℂ y) -
      envRep R τ' (UniversalEnvelopingAlgebra.ι ℂ y) * envRep R τ (UniversalEnvelopingAlgebra.ι ℂ x) = 0
    rw [(envRep_comm R h _ _).eq, sub_self]

def envRepAll (R : RealPoints θ V) : GlobalTheory.AutFinLit.Env V →ₐ[ℂ] Module.End ℂ (SmF θ V) :=
  UniversalEnvelopingAlgebra.lift ℂ (lieRep R)


open Classical in
def envIncl (V : HSp D) (τ : D.what₂.Tau) : EnvAt V τ →ₐ[ℂ] GlobalTheory.AutFinLit.Env V :=
  UniversalEnvelopingAlgebra.lift ℂ ((UniversalEnvelopingAlgebra.ι ℂ).comp
    (DirectSum.lieAlgebraOf ℂ D.what₂.Tau (fun τ => ℂ ⊗[ℝ] LieAt V τ) τ))

open Classical in
theorem envIncl_ι (τ : D.what₂.Tau) (x : ℂ ⊗[ℝ] LieAt V τ) :
    envIncl V τ (UniversalEnvelopingAlgebra.ι ℂ x) =
      UniversalEnvelopingAlgebra.ι ℂ (DirectSum.of (fun τ => ℂ ⊗[ℝ] LieAt V τ) τ x) := by
  simp [envIncl]

theorem envRepAll_envIncl (R : RealPoints θ V) (τ : D.what₂.Tau) (u : EnvAt V τ) :
    envRepAll R (envIncl V τ u) = envRep R τ u := by
  classical
  have : (envRepAll R).comp (envIncl V τ) = envRep R τ := by
    apply UniversalEnvelopingAlgebra.hom_ext
    refine LieHom.ext fun x => ?_
    change envRepAll R (envIncl V τ (UniversalEnvelopingAlgebra.ι ℂ x)) = envRep R τ (UniversalEnvelopingAlgebra.ι ℂ x)
    rw [envIncl_ι, envRepAll, UniversalEnvelopingAlgebra.lift_ι_apply, lieRep]
    exact DirectSum.toModule_lof ℂ (M := fun τ => ℂ ⊗[ℝ] LieAt V τ) τ x
  exact congrArg (fun f : EnvAt V τ →ₐ[ℂ] _ => f u) this

end GlobalTheory.CentralOps
end
end

section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdTh.SerAll


open NumberField Matrix Complex MeasureTheory IsDedekindDomain in
open scoped TensorProduct Classical ComplexConjugate in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar in
theorem _root_.GlobalTheory.AdTh.SerAll.lieFac_eq_pow {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) {x : ℝ} (hx : 0 < x)
    (a : (E →+* ℂ) × ℕ → ℕ) :
    _root_.Formalism.L2.Pj.lieFac Dw x a = (Real.sqrt (2 * Real.pi * x))⁻¹ ^ _root_.GlobalTheory.PtId.degW Dw a := by
  have hy : 0 < 2 * Real.pi * x := by positivity
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hy.le, ← Real.rpow_natCast, ← Real.rpow_mul hy.le,
    Real.rpow_def_of_pos hy]
  unfold _root_.Formalism.L2.Pj.lieFac _root_.GlobalTheory.PtId.degW
  congr 1
  push_cast
  ring


end GlobalTheory.AdTh.SerAll
end
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

theorem _root_.GlobalTheory.T.adaptedFullFlag_frame_change_diagonal_units : ∀ (F : Type) [Field F] (X : Var F) (ι : Type) (m : ι → ℕ) (E : Fr (ratOf X) m m) (B : Mat m X.Fn),
    B ∈ E.S (genericPoint X.X) → ∀ (z : X.X) (A A' : Mat m X.Fn), A ∈ E.S z → A' ∈ E.S z → ∀ x : Root m,
      UnitAt z ((A' * A⁻¹) x.1 x.2 x.2) ∧ (B * A⁻¹) x.1 x.2 x.2 = (B * A'⁻¹) x.1 x.2 x.2 * (A' * A⁻¹) x.1 x.2 x.2 := by
  first | exact @GlobalTheory.FlagChange.diag_unitAt_and_mul | exact GlobalTheory.FlagChange.diag_unitAt_and_mul | (intros; apply GlobalTheory.FlagChange.diag_unitAt_and_mul <;> assumption)
end

section

namespace GlobalTheory

theorem dixmierMalliavinFactorisation_fromLibrary : GlobalTheory.Published.DixmierMalliavinFactorisation :=
  CompanionTheory.DM.dixmierMalliavinFactorisation_holds

end GlobalTheory
end

end

section

@[expose] public section

open GlobalTheory.IsoTriv

theorem _root_.GlobalTheory.T.columnInclusionRetraction_of_limitSteps : LimActSt → LimPtSt → InvSt → RetrSt := by
  first | exact @GlobalTheory.IsoTriv.retrSt_of | exact GlobalTheory.IsoTriv.retrSt_of | (intros; apply GlobalTheory.IsoTriv.retrSt_of <;> assumption)

end
end

section

@[expose] public section

open GlobalTheory.IsoTriv

theorem _root_.GlobalTheory.T.invariantDerivationEqPartialLogCoords_proof : InvDerSt := by
  first | exact @GlobalTheory.InvDer.invDer | exact GlobalTheory.InvDer.invDer | (intros; apply GlobalTheory.InvDer.invDer <;> assumption)

end
end
