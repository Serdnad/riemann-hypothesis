module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiCongrLeftUpdate
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle264
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle142
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicTransportMeasureSecond
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicTransportMeasureThird
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle078
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralInvOfSupport
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle463

@[expose] public section

section

open Formalism.MainNotions.S Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix Formalism.IndefR Formalism.IndefR.Datum GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct ContDiff

noncomputable section

namespace GlobalTheory.ConjRowRepModels



theorem exists_contRep_models : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → GapHyp D → R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → SeeAt R F X h t → ∀ (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (Formalism.MainNotions.S.uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → ∀ u : (MP R).Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) ψ := by
  intro _ _ _ _ D G' _ _ Pl0 T A Ks _ _ _ R F X h t hE _ _ hθ _ _ c hc Φ hΦ u
  obtain ⟨_, _, _, _, _, -, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (D.sp.Y 0)
  obtain ⟨hf, -, hat, -⟩ := GlobalTheory.Core.Mi.SeeReal.realSplit_of_idE D X h R.θ hθ hE
  obtain ⟨-, hcomm, g, hg, hfix⟩ := GlobalTheory.IdemProj.re_orth_proj X.B
  have := X.B.sf
  have := X.B.haar
  let T : GA D (D.sp.Y 0) ≃* X.B.I.GA := (iotaX X h).toMulEquiv
  have hT : Continuous T := (iotaX X h).continuous
  have hT' : Continuous T.symm := (iotaX X h).symm.continuous
  obtain ⟨μ, ρ, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :=
    GlobalTheory.TensRep.exists_transport X.B.I X.B.μf X.B.fund X.B.fund_spec X.B.R X.B.R_spec T hT hT'
  obtain ⟨U, hU, hUg⟩ := h11 g hg
  have hA : Φ ∈ X.B.I.HomS X.B.σs X.B.μf X.B.fund X.B.R := by
    obtain ⟨A, hA, rfl⟩ := hΦ
    intro g
    show (X.B.Re.comp A).comp (X.B.σs g) = (X.B.R (g, 1)).comp (X.B.Re.comp A)
    rw [ContinuousLinearMap.comp_assoc, hA g, ← ContinuousLinearMap.comp_assoc, hcomm g,
      ContinuousLinearMap.comp_assoc]
  have hlev : ∀ k ∈ X.B.I.Kg g, ∀ w, X.B.R (1, k) (Φ w) = Φ w := by
    obtain ⟨A, -, rfl⟩ := hΦ
    intro k hk w
    exact congrArg (fun C : L2X X →L[ℂ] L2X X => C (A w)) (hfix k hk)
  obtain ⟨m, hm, -⟩ := GlobalTheory.exists_continuousMultilinearMap_of_inner_prod (H := X.B.H) X.B.tens
    X.B.tens_spec.1 X.B.tens_spec.2.2
  let C : (∀ τ, (MP R).H τ) → ∀ v, X.B.H v := fun y => Equiv.piCongrLeft X.B.H X.pl.symm (fun τ => c τ (y τ))
  have hC : ∀ y τ, C y (X.pl.symm τ) = c τ (y τ) := fun y τ => Equiv.piCongrLeft_apply_apply _ _ _ _
  have hCd : ContDiff ℝ ∞ C := by
    refine contDiff_pi.2 fun v => ?_
    obtain ⟨τ, rfl⟩ := X.pl.symm.surjective v
    simp only [hC]
    exact (GlobalTheory.ConjRowRep.contDiff_anti (c τ)).comp (contDiff_pi.1 contDiff_id τ)
  let F : (∀ τ, (MP R).H τ) → L2X X := fun y => Φ (X.B.tens (C y))
  have hF : ContDiff ℝ ∞ F := by
    have e : F = fun y => (Φ.compContinuousMultilinearMap m) (C y) := by
      funext y
      show Φ (X.B.tens (C y)) = Φ (m (C y))
      rw [hm]
    rw [e]
    exact (((Φ.compContinuousMultilinearMap m).contDiff (n := ∞)).restrict_scalars ℝ).comp hCd
  have hsm := GlobalTheory.ConjRowRep.smooth_of_contDiff R.θ (MP R) ρ F hF (fun τ a ha y => by
    obtain ⟨q1, q2, -⟩ := hat τ a ha
    rw [h3]
    refine GlobalTheory.TensRep.hom_tens X.B.I X.B.tens_spec hA q1 _ _ fun v => ?_
    obtain ⟨τ', rfl⟩ := X.pl.symm.surjective v
    rw [hC, hC]
    by_cases e : τ' = τ
    · subst e
      rw [Function.update_self]
      exact hc _ a ha _
    · rw [Function.update_of_ne e]
      have q : (iotaX X h (atTau R.θ (D.sp.Y 0) τ a)).1 (X.pl.symm τ') = 1 := q2 _ (X.pl.symm.injective.ne e)
      rw [q]
      have : X.B.σ (X.pl.symm τ') 1 = 1 := (X.ds _).2.2.1.1.1
      show _ = X.B.σ (X.pl.symm τ') 1 _
      rw [this]
      rfl) u
  obtain ⟨R', L, -, hR, -⟩ := GlobalTheory.TensRep.exists_adelic_rep (ι := fun v x => X.B.I.ext v (T x)) hθ h1 h2 h5 h6 h7
    h8 h9 hU
  obtain ⟨p1, p2⟩ := hR _ hsm (fun k hk hk' => by
    rw [h3]
    have e : T k = (1, (T k).2) := Prod.ext ((hf k).1 hk') rfl
    rw [e]
    exact hlev _ (hUg k hk) _)
  refine ⟨fun x => R' (F fun τ => (u τ : (MP R).H τ)) (T.symm x),
    GlobalTheory.RepSmooth.isContRep_of_ae X.B (p1.comp hT') (fun γ hγ x => ?_) ?_⟩
  · have e : (fun x => R' (F fun τ => (u τ : (MP R).H τ)) (T.symm γ * x)) = R' (F fun τ => (u τ : (MP R).H τ)) :=
      ((p1.comp (continuous_const_mul _)).ae_eq_iff_eq μ p1).1
        (Filter.EventuallyEq.trans
          (((measurePreserving_mul_left μ _).quasiMeasurePreserving.ae p2).mono fun _ hy => hy.symm)
          ((h10 (T.symm γ) (by rw [T.apply_symm_apply]; exact hγ) _).trans p2))
    rw [map_mul]
    exact congrFun e _
  · filter_upwards [h4 _ p2] with x hx
    rw [← hx, T.apply_symm_apply]
    rfl

end GlobalTheory.ConjRowRepModels

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.DenseGL

variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))

theorem approx (x : P.adicCompletion E) (M : ℤ) :
    ∃ e : E, Valued.v (x - algebraMap E (P.adicCompletion E) e) ≤ WithZero.exp (-M) := by
  have hd := HeightOneSpectrum.denseRange_algebraMap (K := E) P
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer (K := E) P
  set c : P.adicCompletion E := algebraMap E (P.adicCompletion E) (π ^ M.toNat) with hc
  have hvc : Valued.v c = WithZero.exp (-(M.toNat : ℤ)) := by
    have hv : ∀ k : E, Valued.v (algebraMap E (P.adicCompletion E) k) = P.valuation E k :=
      fun k => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P k
    rw [hc, hv, map_pow, hπ,
      ← WithZero.exp_nsmul]
    congr 1
    simp
  have hc0 : Valued.v c ≠ 0 := by rw [hvc]; exact WithZero.exp_ne_zero
  have hN : {y : P.adicCompletion E | Valued.v (x - y) < Valued.v c} ∈ nhds x := by
    have ho := (Valued.isOpen_ball (P.adicCompletion E) (Valued.v.restrict c)).preimage
      (continuous_const.sub continuous_id : Continuous fun y : P.adicCompletion E => x - y)
    simp only [Set.preimage_ofPred_eq, Valuation.restrict_lt_iff] at ho
    refine ho.mem_nhds ?_
    show Valued.v (x - x) < _
    rw [sub_self, map_zero]
    exact zero_lt_iff.2 hc0
  obtain ⟨e, he⟩ := hd.mem_nhds hN
  refine ⟨e, le_of_lt (lt_of_lt_of_le he ?_)⟩
  rw [hvc, WithZero.exp_le_exp]
  have := Int.self_le_toNat M
  omega

theorem bound {n : ℕ} (B : Matrix (Fin n) (Fin n) (P.adicCompletion E)) :
    ∃ L : ℕ, ∀ r k, Valued.v (B r k) ≤ WithZero.exp (L : ℤ) := by
  obtain ⟨c, hc⟩ := Finite.bddAbove_range (fun p : Fin n × Fin n => Valued.v (B p.1 p.2))
  refine ⟨(WithZero.log (max c 1)).toNat, fun r k => ?_⟩
  have h1 : Valued.v (B r k) ≤ max c 1 := (hc ⟨(r, k), rfl⟩).trans (le_max_left _ _)
  have h0 : max c 1 ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
  refine h1.trans ?_
  rw [← WithZero.exp_log h0, WithZero.exp_le_exp, WithZero.log_exp]
  exact Int.self_le_toNat _

end GlobalTheory.DenseGL

namespace GlobalTheory.DenseGL

variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))

def smallIdeal : Ideal (P.adicCompletionIntegers E) where
  carrier := {x | Valued.v (x : P.adicCompletion E) < 1}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Subring.coe_add] at *
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ha hb)
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq, smul_eq_mul] at *
    have hc : Valued.v (c : P.adicCompletion E) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 c.2
    rw [show ((c * x : P.adicCompletionIntegers E) : P.adicCompletion E) = c * x from rfl, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' hc) hx

theorem one_add_small {n : ℕ} (X : Matrix (Fin n) (Fin n) (P.adicCompletion E))
    (hX : ∀ r s, Valued.v (X r s) < 1) :
    Valued.v (1 + X).det = 1 ∧ ∀ r s, Valued.v ((1 + X)⁻¹ r s) ≤ 1 := by
  set O := P.adicCompletionIntegers E
  have hmem : ∀ r s, X r s ∈ O := fun r s =>
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hX r s).le
  let X' : Matrix (Fin n) (Fin n) O := fun r s => ⟨X r s, hmem r s⟩
  have hmap : O.subtype.mapMatrix (1 + X') = 1 + X := by
    rw [map_add (f := _), map_one]; rfl
  have hq : (Ideal.Quotient.mk (smallIdeal P)).mapMatrix (1 + X') = 1 := by
    rw [map_add (f := _), map_one, add_eq_left]
    ext r s
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hX r s)
  have hd : (1 + X').det - 1 ∈ smallIdeal P := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, RingHom.map_det, hq, Matrix.det_one, map_one,
      sub_self]
  have hdet : Valued.v (1 + X).det = 1 := by
    rw [← hmap, ← RingHom.map_det]
    have h1 : (O.subtype (1 + X').det) = 1 + (((1 + X').det - 1 : O) : P.adicCompletion E) := by
      simp [O]
    rw [h1]
    exact Valuation.map_one_add_of_lt _ hd
  refine ⟨hdet, fun r s => ?_⟩
  have hdet0 : (1 + X).det ≠ 0 := fun h => by rw [h, map_zero] at hdet; exact zero_ne_one hdet
  rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀, hdet,
    inv_one, one_mul, ← hmap, ← RingHom.map_adjugate]
  exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 ((1 + X').adjugate r s).2

end GlobalTheory.DenseGL

namespace GlobalTheory.DenseGL

theorem entry_le {n : ℕ} {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] (B C : Matrix (Fin n) (Fin n) K)
    (a b : WithZero (Multiplicative ℤ)) (hB : ∀ r k, Valued.v (B r k) ≤ a) (hC : ∀ k s, Valued.v (C k s) ≤ b) (r s : Fin n) :
    Valued.v ((B * C) r s) ≤ a * b := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun k _ => ?_
  rw [map_mul]
  exact mul_le_mul' (hB r k) (hC k s)

theorem dense_two_sided : ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (n N : ℕ) (A : GL (Fin n) (P.adicCompletion E)), ∃ γ : GL (Fin n) E, ∀ r s, Valued.v (((A⁻¹).1 * γ.1.map (algebraMap E (P.adicCompletion E)) - 1) r s) ≤ WithZero.exp (-(N : ℤ)) ∧ Valued.v (((γ⁻¹).1.map (algebraMap E (P.adicCompletion E)) * A.1 - 1) r s) ≤ WithZero.exp (-(N : ℤ)) := by
  intro E _ _ P n N A
  set f := algebraMap E (P.adicCompletion E)
  set B := (A⁻¹).1 with hBdef
  have hBA : B * A.1 = 1 := Units.inv_mul A
  obtain ⟨L, hL⟩ := bound P B
  choose C hC using fun r s => approx P (A.1 r s) ((N : ℤ) + 1 + L)
  let Cm : Matrix (Fin n) (Fin n) E := Matrix.of C
  set C' := Cm.map f with hC'
  set X := B * C' - 1 with hXdef
  have hXe : X = B * (C' - A.1) := by rw [Matrix.mul_sub, hBA]
  have hsmall : ∀ r s, Valued.v (X r s) ≤ WithZero.exp (-((N : ℤ) + 1)) := by
    intro r s
    rw [hXe]
    refine (entry_le B (C' - A.1) _ (WithZero.exp (-((N : ℤ) + 1 + L))) hL (fun k s => ?_) r s).trans (le_of_eq ?_)
    · show Valued.v (f (C k s) - A.1 k s) ≤ _
      rw [Valuation.map_sub_swap]
      exact hC k s
    · rw [← WithZero.exp_add]; congr 1; ring
  have hN1 : WithZero.exp (-((N : ℤ) + 1)) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have hNN : WithZero.exp (-((N : ℤ) + 1)) ≤ WithZero.exp (-(N : ℤ)) := by
    rw [WithZero.exp_le_exp]; omega
  have hX1 : ∀ r s, Valued.v (X r s) < 1 := fun r s => (hsmall r s).trans_lt hN1
  obtain ⟨hdet, hint⟩ := one_add_small P X hX1
  have hY : 1 + X = B * C' := by rw [hXdef]; abel
  have hCdet : Cm.det ≠ 0 := by
    intro h0
    have : (1 + X).det = 0 := by
      rw [hY, Matrix.det_mul, hC', ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero,
        mul_zero]
    rw [this, map_zero] at hdet
    exact zero_ne_one hdet
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero Cm hCdet, fun r s => ⟨?_, ?_⟩⟩
  · exact (hsmall r s).trans hNN
  · set γ := Matrix.GeneralLinearGroup.mkOfDetNeZero Cm hCdet
    have hγ : γ.1 = Cm := rfl
    set D := (γ⁻¹).1.map f
    have hCD : C' * D = 1 := by
      rw [hC', ← hγ, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero f) (map_one f)]
    have hYZ : (1 + X) * (D * A.1) = 1 := by
      rw [hY, Matrix.mul_assoc, ← Matrix.mul_assoc C', hCD, Matrix.one_mul, hBA]
    have hZ : D * A.1 = (1 + X)⁻¹ := (Matrix.inv_eq_right_inv hYZ).symm
    have hZY : (D * A.1) * (1 + X) = 1 := by
      rw [hZ]; exact Matrix.nonsing_inv_mul _ (by
        refine isUnit_iff_ne_zero.2 fun h => ?_; rw [h, map_zero] at hdet; exact zero_ne_one hdet)
    have hdiff : D * A.1 - 1 = -((D * A.1) * X) := by
      rw [Matrix.mul_add, Matrix.mul_one] at hZY
      rw [← hZY]; abel
    rw [hdiff, Matrix.neg_apply, Valuation.map_neg]
    refine (entry_le _ X 1 _ (by rw [hZ]; exact hint) hsmall r s).trans ?_
    rw [one_mul]; exact hNN

end GlobalTheory.DenseGL
end
