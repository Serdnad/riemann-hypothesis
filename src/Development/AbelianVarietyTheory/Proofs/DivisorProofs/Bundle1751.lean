module

public import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle050
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle579
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle625
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle481
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle152
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactHaarRightInvariantInst
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.KoszulLowersPower
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousAdeleNorm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle093
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle208
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeEmbeddingMemUnitGroup
import Formalism.HarderNarasimhan.ShiftInvariance
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1713
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero

@[expose] public section

section

noncomputable section

open MeasureTheory MvPolynomial GlobalTheory.OpTrace
open Formalism.REAL (UJ KG toM toMK muK)
open GlobalTheory.PsCo.Pc1
open scoped InnerProductSpace ComplexConjugate

namespace GlobalTheory.PsCo.Pc3.RangeSh

variable {n : ℕ}

def evK (ε : Fin n → Bool) : Poly n →ₗ[ℂ] (KG ε → ℂ) where
  toFun P k := ev (toMK k) P
  map_add' P Q := by funext k; simp
  map_smul' c P := by funext k; simp [ev, smul_eval]

def polyK (ε : Fin n → Bool) (d : ℕ) : Submodule ℂ (KG ε → ℂ) :=
  (restrictTotalDegree _ ℂ d).map (evK ε)

instance (ε : Fin n → Bool) (d : ℕ) : FiniteDimensional ℂ (polyK ε d) := by
  unfold polyK; infer_instance

theorem mem_polyK {ε : Fin n → Bool} {d : ℕ} {F : KG ε → ℂ} :
    F ∈ polyK ε d ↔ ∃ P : Poly n, P.totalDegree ≤ d ∧ ∀ k, F k = ev (toMK k) P := by
  constructor
  · rintro ⟨P, hP, rfl⟩
    exact ⟨P, (mem_restrictTotalDegree _ _ _).1 hP, fun _ => rfl⟩
  · rintro ⟨P, hP, h⟩
    refine Submodule.mem_map.2 ⟨P, (mem_restrictTotalDegree _ _ _).2 hP, ?_⟩
    funext k
    rw [h k]
    rfl

theorem ev_conjTranspose (P : Poly n) :
    ∃ Q : Poly n, Q.totalDegree ≤ P.totalDegree ∧ ∀ A : Mat n, ev A.conjTranspose P = ev A Q := by
  refine ⟨rename (Sum.elim (fun x => Sum.inr x.swap) (fun x => Sum.inl x.swap)) P, totalDegree_rename_le _ _,
    fun A => ?_⟩
  rw [ev, ev, eval_rename]
  congr 2
  funext v
  rcases v with x | x <;> simp

theorem conj_ev (P : Poly n) :
    ∃ Q : Poly n, Q.totalDegree ≤ P.totalDegree ∧ ∀ A : Mat n, conj (ev A P) = ev A Q := by
  refine ⟨rename Sum.swap (map (starRingEnd ℂ) P), (totalDegree_rename_le _ _).trans ?_, fun A => ?_⟩
  · exact Finset.sup_mono (support_map_subset _ _)
  · induction P using MvPolynomial.induction_on with
    | C a => simp [ev]
    | add p q hp hq => simp only [map_add (f := _), hp, hq]
    | mul_X p v hp =>
      simp only [map_mul, hp]
      rcases v with x | x <;> simp [ev]

theorem ev_mul (a b : Mat n) (P : Poly n) :
    ∃ Q : Poly n, Q.totalDegree ≤ P.totalDegree ∧ ∀ g : Mat n, ev (a * g * b) P = ev g Q :=
  GlobalTheory.PolyEntryMul.main n a b P

theorem toMK_inv {ε : Fin n → Bool} (k : KG ε) : toM ((k : UJ ε)⁻¹) = (toMK k).conjTranspose := by
  have h1 : toMK k * star (toMK k) = 1 := Unitary.mul_star_self_of_mem k.2.1
  exact Units.inv_eq_of_mul_eq_one_right h1

theorem rM_inv (ε : Fin n → Bool) (k k' : KG ε) (g : UJ ε) :
    rM ε (toM ((k : UJ ε) * g * (k' : UJ ε))) = rM ε (toM g) :=
  (GlobalTheory.offDiagBlockNorm_cont_inv n ε).2 k k' g

theorem shape_cc {ε : Fin n → Bool} {d : ℕ} {φ : Mat n → ℂ} (hφ : φ ∈ ShapeM ε d) :
    Continuous (fun g : UJ ε => φ (toM g)) ∧ HasCompactSupport (fun g : UJ ε => φ (toM g)) := by
  induction hφ using Submodule.span_induction with
  | mem φ h =>
    obtain ⟨H, P, ⟨hH, R, hR⟩, -, rfl⟩ := h
    have hM : Continuous fun g : UJ ε => toM g := Units.continuous_val.comp continuous_subtype_val
    refine ⟨?_, ?_⟩
    · have hr : Continuous fun g : UJ ε => rM ε (toM g) := (GlobalTheory.offDiagBlockNorm_cont_inv n ε).1
      have hent : Continuous fun g : UJ ε =>
          (Sum.elim (fun x => toM g x.1 x.2) (fun x => star (toM g x.1 x.2)) :
            (Fin n × Fin n) ⊕ (Fin n × Fin n) → ℂ) := by
        refine continuous_pi fun i => ?_
        rcases i with x | x
        · exact (continuous_apply x.2).comp ((continuous_apply x.1).comp hM)
        · exact continuous_star.comp ((continuous_apply x.2).comp ((continuous_apply x.1).comp hM))
      exact (Complex.continuous_ofReal.comp (hH.continuous.comp hr)).mul
        ((MvPolynomial.continuous_eval P).comp hent)
    · refine HasCompactSupport.intro (GlobalTheory.T.isCompact_pseudoUnitary_offDiag_norm_sublevel n ε R) fun g hg => ?_
      have h : R ≤ rM ε (toM g) := (not_le.1 hg).le
      simp [bas, hR _ h]
  | zero => exact ⟨continuous_const, HasCompactSupport.zero⟩
  | add φ ψ _ _ h1 h2 => exact ⟨h1.1.add h2.1, h1.2.add h2.2⟩
  | smul c φ _ h => exact ⟨h.1.const_smul c, h.2.smul_left (f := fun _ => c)⟩

theorem shape_left {ε : Fin n → Bool} {d : ℕ} {φ : Mat n → ℂ} (hφ : φ ∈ ShapeM ε d) (g : UJ ε) :
    (fun k : KG ε => φ (toM ((k : UJ ε)⁻¹ * g))) ∈ polyK ε d := by
  induction hφ using Submodule.span_induction with
  | mem φ h =>
    obtain ⟨H, P, -, hP, rfl⟩ := h
    obtain ⟨Q, hQ, hQe⟩ := ev_mul 1 (toM g) P
    obtain ⟨S, hS, hSe⟩ := ev_conjTranspose Q
    have hm : (fun k : KG ε => ev (toMK k) S) ∈ polyK ε d :=
      mem_polyK.2 ⟨S, hS.trans (hQ.trans hP), fun _ => rfl⟩
    convert (polyK ε d).smul_mem (H (rM ε (toM g)) : ℂ) hm using 1
    funext k
    have h1 : rM ε (toM ((k : UJ ε)⁻¹ * g)) = rM ε (toM g) := by
      simpa using rM_inv ε k⁻¹ 1 g
    have h2 : toM ((k : UJ ε)⁻¹ * g) = 1 * (toMK k).conjTranspose * toM g := by
      rw [Matrix.one_mul, ← toMK_inv]; rfl
    simp only [bas, Pi.smul_apply, smul_eq_mul]
    rw [h1, h2, hQe, hSe]
  | zero => exact (polyK ε d).zero_mem
  | add φ ψ _ _ h1 h2 => exact (polyK ε d).add_mem h1 h2
  | smul c φ _ h => exact (polyK ε d).smul_mem c h

theorem shape_right {ε : Fin n → Bool} {d : ℕ} {φ : Mat n → ℂ} (hφ : φ ∈ ShapeM ε d) (g : UJ ε) :
    (fun k : KG ε => φ (toM (g * (k : UJ ε)))) ∈ polyK ε d := by
  induction hφ using Submodule.span_induction with
  | mem φ h =>
    obtain ⟨H, P, -, hP, rfl⟩ := h
    obtain ⟨Q, hQ, hQe⟩ := ev_mul (toM g) 1 P
    have hm : (fun k : KG ε => ev (toMK k) Q) ∈ polyK ε d :=
      mem_polyK.2 ⟨Q, hQ.trans hP, fun _ => rfl⟩
    convert (polyK ε d).smul_mem (H (rM ε (toM g)) : ℂ) hm using 1
    funext k
    have h1 : rM ε (toM (g * (k : UJ ε))) = rM ε (toM g) := by
      simpa using rM_inv ε 1 k g
    have h2 : toM (g * (k : UJ ε)) = toM g * toMK k * 1 := by
      rw [Matrix.mul_one]; rfl
    simp only [bas, Pi.smul_apply, smul_eq_mul]
    rw [h1, h2, hQe]
  | zero => exact (polyK ε d).zero_mem
  | add φ ψ _ _ h1 h2 => exact (polyK ε d).add_mem h1 h2
  | smul c φ _ h => exact (polyK ε d).smul_mem c h

theorem conj_mem {ε : Fin n → Bool} {d : ℕ} {F : KG ε → ℂ} (hF : F ∈ polyK ε d) :
    (fun k => conj (F k)) ∈ polyK ε d := by
  obtain ⟨P, hP, h⟩ := mem_polyK.1 hF
  obtain ⟨Q, hQ, hQe⟩ := conj_ev P
  exact mem_polyK.2 ⟨Q, hQ.trans hP, fun k => by rw [h, hQe]⟩

end GlobalTheory.PsCo.Pc3.RangeSh

namespace GlobalTheory.PsCo.Pc3

open RangeSh

theorem rangeShape : RangeShape := by
  intro n ε μ _ U _ _ _ π hπ d φ hφ
  haveI := GlobalTheory.unitarySigns_haar_isMulRightInvariant n ε μ
  obtain ⟨hc, hs⟩ := shape_cc hφ
  set f : UJ ε → ℂ := fun g => φ (toM g) with hf
  have hT : IsRepOp π μ f (repOp π μ f) := hπ.isRepOp hc hs
  have hin : ∀ a b : U, ⟪a, repOp π μ f b⟫_ℂ = ∫ g, f g * ⟪a, π g b⟫_ℂ ∂μ := by
    intro a b
    rw [(hT b).2, ← integral_inner (hT b).1]
    simp only [inner_smul_right]
  have hco : ∀ a b : U, Continuous fun g => ⟪a, π g b⟫_ℂ :=
    fun a b => continuous_const.inner (hπ.continuous_apply b)
  refine ⟨hT, fun u => ⟨fun l => mem_polyK.1 ?_, fun l => mem_polyK.1 ?_⟩⟩
  · have key := GlobalTheory.Pc3.RS.integral_mem μ (polyK ε d) (fun g k => ⟪l, π g u⟫_ℂ * f ((k : UJ ε)⁻¹ * g))
      (fun g => (polyK ε d).smul_mem ⟪l, π g u⟫_ℂ (shape_left hφ g))
      (fun k => ((hco l u).mul (hc.comp (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport
        (hs.comp_homeomorph (Homeomorph.mulLeft ((k : UJ ε)⁻¹))).mul_left)
    convert key using 1
    funext k
    have e1 : ⟪l, π k (repOp π μ f u)⟫_ℂ = ⟪π (k : UJ ε)⁻¹ l, repOp π μ f u⟫_ℂ := by
      rw [hπ.inner_apply_left, inv_inv]
    rw [e1, hin, ← integral_mul_left_eq_self (fun g => ⟪l, π g u⟫_ℂ * f ((k : UJ ε)⁻¹ * g)) (k : UJ ε)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [hπ.inner_apply_left, inv_inv, inv_mul_cancel_left, map_mul, ContinuousLinearMap.mul_apply]
    ring
  · have key := GlobalTheory.Pc3.RS.integral_mem μ (polyK ε d) (fun g k => ⟪u, π g l⟫_ℂ * f (g * (k : UJ ε)))
      (fun g => (polyK ε d).smul_mem ⟪u, π g l⟫_ℂ (shape_right hφ g))
      (fun k => ((hco u l).mul (hc.comp (continuous_id.mul continuous_const))).integrable_of_hasCompactSupport
        (hs.comp_homeomorph (Homeomorph.mulRight (k : UJ ε))).mul_left)
    convert conj_mem key using 1
    funext k
    have e1 : ⟪l, π k (ContinuousLinearMap.adjoint (repOp π μ f) u)⟫_ℂ =
        conj ⟪u, repOp π μ f (π (k : UJ ε)⁻¹ l)⟫_ℂ := by
      rw [inner_conj_symm, ← ContinuousLinearMap.adjoint_inner_right, hπ.inner_apply_left, inv_inv]
    rw [e1, hin, ← integral_mul_right_eq_self (fun g => ⟪u, π g l⟫_ℂ * f (g * (k : UJ ε))) (k : UJ ε)⁻¹]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [inv_mul_cancel_right, map_mul, ContinuousLinearMap.mul_apply]
    ring

end GlobalTheory.PsCo.Pc3

end
end

section

noncomputable section

open MeasureTheory MvPolynomial
open Formalism.REAL (UJ KG toM toMK muK)
open GlobalTheory.PsCo.Pc1
open scoped InnerProductSpace

namespace GlobalTheory.PsCo.Pc3.RK

def linT (n : ℕ) : (Fin n × Fin n) ⊕ (Fin n × Fin n) → MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) (Poly n)
  | Sum.inl x => ∑ l, X (Sum.inr (l, x.1)) * C (X (Sum.inl (l, x.2)))
  | Sum.inr x => ∑ l, X (Sum.inl (l, x.1)) * C (X (Sum.inr (l, x.2)))

def TT (n : ℕ) : Poly n →ₐ[ℂ] MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) (Poly n) := aeval (linT n)

theorem TT_deg {n : ℕ} (P : Poly n) : (TT n P).totalDegree ≤ P.totalDegree := by
  first
  | exact @_root_.GlobalTheory.TotalDegreeBounds.main
  | exact _root_.GlobalTheory.TotalDegreeBounds.main
  | (apply _root_.GlobalTheory.TotalDegreeBounds.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.TotalDegreeBounds.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TotalDegreeBounds.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TotalDegreeBounds.main ..)

theorem ev_conjT_mul {n : ℕ} (A M : Mat n) (P : Poly n) :
    ev (A.conjTranspose * M) P =
      eval (Sum.elim (fun x => A x.1 x.2) (fun x => star (A x.1 x.2))) (map (ev M) (TT n P)) := by
  have h : (ev (A.conjTranspose * M) : Poly n →+* ℂ) =
      (eval (Sum.elim (fun x => A x.1 x.2) (fun x => star (A x.1 x.2)))).comp
        ((map (ev M)).comp (TT n).toRingHom) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun v => ?_)
    · simp [ev, TT, MvPolynomial.algebraMap_eq]
    · rcases v with x | x
      · simp [ev, TT, linT, Matrix.mul_apply]
      · simp [ev, TT, linT, Matrix.mul_apply]
  exact congrArg (fun f : Poly n →+* ℂ => f P) h

theorem eval_map_eq {n : ℕ} (x : (Fin n × Fin n) ⊕ (Fin n × Fin n) → ℂ) (f : Poly n →+* ℂ)
    (p : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) (Poly n)) :
    eval x (map f p) = ∑ s ∈ p.support, f (AddMonoidAlgebra.coeff p s) * eval x (monomial s 1) := by
  conv_lhs => rw [p.as_sum]

  simp only [map_sum, map_monomial, eval_monomial, one_mul]

end GlobalTheory.PsCo.Pc3.RK

namespace GlobalTheory.PsCo.Pc3

open RK

theorem rangeK : RangeK := by
  classical
  intro n ε U _ _ _ π hπ P
  have hemb : Topology.IsEmbedding (fun k : KG ε => toMK k) :=
    (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  have hφc : Continuous fun k : KG ε => toMK k := hemb.continuous
  have hevc : ∀ Q : Poly n, Continuous fun k : KG ε => ev (toMK k) Q := by
    intro Q
    have hent : Continuous fun k : KG ε =>
        (Sum.elim (fun x => toMK k x.1 x.2) (fun x => star (toMK k x.1 x.2)) :
          (Fin n × Fin n) ⊕ (Fin n × Fin n) → ℂ) := by
      refine continuous_pi fun i => ?_
      rcases i with x | x
      · exact (continuous_apply x.2).comp ((continuous_apply x.1).comp hφc)
      · exact continuous_star.comp ((continuous_apply x.2).comp ((continuous_apply x.1).comp hφc))
    exact (MvPolynomial.continuous_eval Q).comp hent
  have horb : ∀ v : U, Continuous fun k : KG ε => π k v :=
    fun v => (hπ.continuous_apply v).comp continuous_subtype_val
  have hint : ∀ (Q : Poly n) (v : U), Integrable (fun k : KG ε => ev (toMK k) Q • π k v) (muK ε) :=
    fun Q v => ((hevc Q).smul (horb v)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hintC : ∀ g : KG ε → ℂ, Continuous g → Integrable g (muK ε) :=
    fun g hg => hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  obtain ⟨M, hM⟩ := (isCompact_univ.image (hevc P)).isBounded.exists_norm_le
  have hMb : ∀ k : KG ε, ‖ev (toMK k) P‖ ≤ M := fun k => hM _ ⟨k, Set.mem_univ _, rfl⟩
  let Bl : U →ₗ[ℂ] U :=
    { toFun := fun v => ∫ k, ev (toMK k) P • π k v ∂(muK ε)
      map_add' := fun v w => by
        simp only [map_add (f := _), smul_add]
        exact integral_add (hint P v) (hint P w)
      map_smul' := fun c v => by
        simp only [map_smul, RingHom.id_apply]
        rw [← integral_smul]
        exact integral_congr_ae (Filter.Eventually.of_forall fun k => smul_comm _ _ _) }
  let B : U →L[ℂ] U := Bl.mkContinuous (M * ((muK ε) Set.univ).toReal) fun v => by
    change ‖∫ k, ev (toMK k) P • π k v ∂(muK ε)‖ ≤ _
    have := norm_integral_le_of_norm_le_const (μ := muK ε) (C := M * ‖v‖)
      (f := fun k : KG ε => ev (toMK k) P • π k v) (Filter.Eventually.of_forall fun k => by
        rw [norm_smul, hπ.norm_apply]
        exact mul_le_mul_of_nonneg_right (hMb k) (norm_nonneg v))
    calc _ ≤ M * ‖v‖ * ((muK ε) Set.univ).toReal := this
      _ = M * ((muK ε) Set.univ).toReal * ‖v‖ := by ring
  refine ⟨B, fun v => ⟨hint P v, rfl⟩, fun u l => ?_⟩
  set p := TT n P with hp
  let f : KG ε → ℂ := fun k => ⟪l, π k u⟫_ℂ
  have hfc : Continuous f := continuous_const.inner (horb u)
  let c : _ → ℂ := fun s => ∫ k, ev (toMK k) (AddMonoidAlgebra.coeff p s) * f k ∂(muK ε)
  refine ⟨∑ s ∈ p.support, C (c s) * monomial s 1, ?_, fun k₀ => ?_⟩
  · refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun s hs => ?_)
    rw [C_mul_monomial, mul_one]
    exact (totalDegree_monomial_le _ _).trans ((le_totalDegree hs).trans (TT_deg P))
  · have hginv : toMK k₀⁻¹ = star (toMK k₀) := by
      have h1 : toMK k₀ * star (toMK k₀) = 1 := Unitary.mul_star_self_of_mem k₀.2.1
      calc toMK k₀⁻¹ = toMK k₀⁻¹ * (toMK k₀ * star (toMK k₀)) := by rw [h1, Matrix.mul_one]
        _ = star (toMK k₀) := by
          rw [← Matrix.mul_assoc]
          change toMK (k₀⁻¹ * k₀) * _ = _
          rw [inv_mul_cancel]
          exact Matrix.one_mul _
    have e1 : π k₀ (B u) = ∫ k, ev (toMK (k₀⁻¹ * k)) P • π k u ∂(muK ε) := by
      change π k₀ (∫ k, ev (toMK k) P • π k u ∂(muK ε)) = _
      rw [← (π k₀).integral_comp_comm (hint P u)]
      have e2 : ∫ k, π k₀ (ev (toMK k) P • π k u) ∂(muK ε) =
          ∫ k, (fun k' : KG ε => ev (toMK (k₀⁻¹ * k')) P • π (k' : UJ ε) u) (k₀ * k) ∂(muK ε) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
        simp only [map_smul, inv_mul_cancel_left, Subgroup.coe_mul, map_mul, ContinuousLinearMap.mul_apply]
      rw [e2, integral_mul_left_eq_self (fun k' : KG ε => ev (toMK (k₀⁻¹ * k')) P • π (k' : UJ ε) u) k₀]
    have hexp : ∀ k : KG ε, ev (toMK (k₀⁻¹ * k)) P =
        ∑ s ∈ p.support, ev (toMK k) (AddMonoidAlgebra.coeff p s) * ev (toMK k₀) (monomial s 1) := by
      intro k
      change ev (toMK k₀⁻¹ * toMK k) P = _
      rw [hginv, show star (toMK k₀) = (toMK k₀).conjTranspose from rfl, ev_conjT_mul, eval_map_eq]
      rfl
    have hint2 : ∀ s, Integrable (fun k : KG ε => ev (toMK k) (AddMonoidAlgebra.coeff p s) * f k) (muK ε) :=
      fun s => hintC _ ((hevc _).mul hfc)
    have hint3 : Integrable (fun k : KG ε => ev (toMK (k₀⁻¹ * k)) P • π k u) (muK ε) :=
      (((hevc P).comp (continuous_const.mul continuous_id)).smul (horb u)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    calc ⟪l, π k₀ (B u)⟫_ℂ = ∫ k, ⟪l, ev (toMK (k₀⁻¹ * k)) P • π k u⟫_ℂ ∂(muK ε) := by
          rw [e1, integral_inner hint3]
      _ = ∫ k, ∑ s ∈ p.support, ev (toMK k₀) (monomial s 1) * (ev (toMK k) (AddMonoidAlgebra.coeff p s) * f k) ∂(muK ε) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
          simp only [inner_smul_right, hexp k, Finset.sum_mul]
          refine Finset.sum_congr rfl fun s _ => ?_
          ring
      _ = ∑ s ∈ p.support, ev (toMK k₀) (monomial s 1) * c s := by
          rw [integral_finsetSum _ fun s _ => (hint2 s).const_mul _]
          exact Finset.sum_congr rfl fun s _ => integral_const_mul _ _
      _ = ev (toMK k₀) (∑ s ∈ p.support, C (c s) * monomial s 1) := by

          simp only [map_sum, map_mul, ev, eval_C]
          exact Finset.sum_congr rfl fun s _ => mul_comm _ _

end GlobalTheory.PsCo.Pc3
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.EtaFinUnit

theorem quadChar_finPartI_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ b : Neutral.B1.Ideles (maximalRealSubfield E),
    b ∈ GlobalTheory.Mem.Chr.unitIdl (maximalRealSubfield E) → (GlobalTheory.GalOfCusp.quadChar E).1 (GlobalTheory.Mem.Chr.finPartI _ b) = 1 := by
  intro E _ _ _ hU b hb
  have hs : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), ∃ w : HeightOneSpectrum (𝓞 E),
      w.under (𝓞 (maximalRealSubfield E)) = v := fun v => by
    haveI := v.isPrime
    obtain ⟨⟨P, hP, hP'⟩⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 E)))
    exact ⟨⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩, HeightOneSpectrum.ext hP'.over.symm⟩
  refine GlobalTheory.Mem.LocTriv.eq_one_of_local (maximalRealSubfield E) (GlobalTheory.GalOfCusp.quadChar E).1
    (GlobalTheory.GalOfCusp.quadChar E).2.1 (GlobalTheory.Mem.Chr.finPartI (maximalRealSubfield E) b)
    (GlobalTheory.Mem.Chr.finPartI_mem_unitIdl.2 hb) (fun w => by rw [GlobalTheory.Mem.Chr.finPartI_fst]; rfl) ?_
  intro v x hx
  rw [GlobalTheory.Mem.Chr.finPartI_snd] at hx
  have hxu : Valued.v (x : v.adicCompletion (maximalRealSubfield E)) = 1 := by rw [hx]; exact hb v
  obtain ⟨w, rfl⟩ := hs v
  exact GlobalTheory.QuadCharUnr.quadChar_unrAt_of_isUnramifiedAt E w (hU w) x hxu

end GlobalTheory.EtaFinUnit
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions GlobalTheory.AllWt GlobalTheory.FlatLine

noncomputable section

namespace GlobalTheory.RestrictNorm

theorem hasGram_comp {K V W : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [AddCommGroup W]
    [Module K W] (N : (K →+* ℂ) → V → ℝ) (φ : W →ₗ[K] V) (hφ : Function.Injective φ) {n : ℕ}
    (b : Module.Basis (Fin n) K V) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (hG : IsGram b X N) :
    HasGram (fun σ (x : W) => N σ (φ x)) := by
  haveI : Module.Finite K V := Module.Finite.of_basis b
  let e : W ≃ₗ[K] LinearMap.range φ := LinearEquiv.ofInjective φ hφ
  let c := Module.finBasis K (LinearMap.range φ)
  obtain ⟨Y, hY, hn⟩ := GlobalTheory.Mem.DivInhab.exists_frames_restrict b X (fun v => (hG v).1) (LinearMap.range φ) c
  refine IsGram.hasGram (b := c.map e.symm) (X := Y) fun v => ⟨hY v, fun x => ?_⟩
  have h1 : Formalism.HermitianLatticesTheory.normAt (c.map e.symm) Y v x = Formalism.HermitianLatticesTheory.normAt c Y v (e x) := by
    have hv : Formalism.HermitianLatticesTheory.vecAt (c.map e.symm) v x = Formalism.HermitianLatticesTheory.vecAt c v (e x) := by
      funext i
      simp only [Formalism.HermitianLatticesTheory.vecAt, Module.Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_symm]
    unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.fcoord
    rw [hv]
  rw [h1, hn, (hG v).2]
  rfl

theorem restrict_deg : ∀ (K V : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (W : Type) [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (N : (K →+* ℂ) → V → ℝ) (φ : W →ₗ[K] V), Function.Injective φ → HasGram N → HasGram (fun σ (x : W) => N σ (φ x)) ∧ ∀ L : Submodule (𝓞 K) W, L.FG → Formalism.HN.rkK (L.map (φ.restrictScalars (𝓞 K))) = Formalism.HN.rkK L ∧ deg N (L.map (φ.restrictScalars (𝓞 K))) = deg (fun σ (x : W) => N σ (φ x)) L := by
  intro K V _ _ _ _ _ _ _ W _ _ _ _ N φ hφ hN
  obtain ⟨⟨n, ⟨b, X⟩, hG⟩⟩ := hN
  have hN' := hasGram_comp N φ hφ b X hG
  refine ⟨hN', fun L hL => ?_⟩
  obtain ⟨⟨m, ⟨c, Y⟩, hG'⟩⟩ := hN'
  letI : StarRing K := starRingOfComm
  have hr := Formalism.HN.rerealize K W (Fin m) V (Fin n) c Y b X φ (fun v => (hG' v).1) (fun v => (hG v).1) hφ
    (fun v x => by rw [(hG v).2, (hG' v).2]) L hL
  have hrk : Formalism.HN.rkK (L.map (φ.restrictScalars (𝓞 K))) = Formalism.HN.rkK L := by
    unfold Formalism.HN.rkK
    have hs : Submodule.span K ((L.map (φ.restrictScalars (𝓞 K)) : Submodule (𝓞 K) V) : Set V) =
        (Submodule.span K (L : Set W)).map φ := by
      rw [Submodule.map_coe, ← Submodule.span_image]
      rfl
    rw [hs]
    exact (Submodule.equivMapOfInjective φ hφ _).finrank_eq.symm
  refine ⟨hrk, ?_⟩
  unfold GlobalTheory.AllWt.deg GlobalTheory.AllWt.slope
  rw [hrk, slope_sq_eq hG (hL.map _), slope_sq_eq hG' hL]
  unfold Formalism.HN.muDef
  rw [hr.2.2.1]

end GlobalTheory.RestrictNorm
end
end

section

open NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict
open GlobalTheory.SW hiding Level
open scoped ComplexConjugate Classical

theorem _root_.GlobalTheory.T.exists_levelOne_theta_ne_zero_on_ideal_half_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsSympl X bas → ∀ (w : E) (L : Lt E r), SelfD X L → ∀ x ∈ X.dom, ∀ (𝔪 : Ideal (𝓞 E)) (M : ℕ), 2 ≤ M → 𝔪 * conjI 𝔪 = Ideal.span {(M : 𝓞 E)} → ∀ ϑ : (Fin g → ℂ) → ℂ, IsTheta1 X bas idx w x L ϑ → ϑ ≠ 0 → ∃ u ∈ 𝔪 • L, ϑ (pv X idx x ((M : E)⁻¹ • u)) ≠ 0 := by
  first | exact @GlobalTheory.Dict.ThetaHalf.exists_ne_zero_on_half | exact GlobalTheory.Dict.ThetaHalf.exists_ne_zero_on_half | (intros; apply GlobalTheory.Dict.ThetaHalf.exists_ne_zero_on_half <;> assumption)
end
