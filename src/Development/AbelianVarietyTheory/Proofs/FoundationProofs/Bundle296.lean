module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle133
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
public import Formalism.BranchSandwichDivisors.Bundle001
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle006
public import Mathlib.RepresentationTheory.Irreducible
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle289
public import Formalism.BranchSandwichDivisors.DivFromPassageAndNorm
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FinalC
public import Formalism.BranchSandwichDivisors.BranchIsometryProofs.BranchScale
import Formalism.GradedWeylDivisibility.FinalB
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle014
public import Formalism.LocalRingCardinality.DataCD
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LamBallULe
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DatumCurveIntegralUnitDiscModel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.Star.Int
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
public import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.CartanCoshPower
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StarMulOfMemKc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle096
import Formalism.LocalRingCardinality.DataTheta
import Formalism.SharpRestriction.Divisibility.SchurIrreducible

@[expose] public section

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.TwoAdicFirst

theorem cont_coe : Continuous fun z : ℤ_[2] => algebraMap ℚ_[2] ℂ_[2] (z : ℚ_[2]) := by
  fun_prop

theorem coe_mem_closure (z : ℤ_[2]) :
    algebraMap ℚ_[2] ℂ_[2] (z : ℚ_[2]) ∈ closure (Set.range (Nat.cast : ℕ → ℂ_[2])) := by
  refine map_mem_closure (f := fun z : ℤ_[2] => algebraMap ℚ_[2] ℂ_[2] (z : ℚ_[2])) cont_coe
    (PadicInt.denseRange_natCast z) ?_
  rintro _ ⟨n, rfl⟩
  exact ⟨n, by simp⟩

theorem exists_root (k : ℕ) : ∃ z : ℤ_[2], z ^ 2 - z + 2 * (k : ℤ_[2]) = 0 := by
  let F : Polynomial ℤ_[2] := Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (2 * (k : ℤ_[2]))
  have h0 : F.eval 0 = 2 * (k : ℤ_[2]) := by simp [F]
  have h1 : F.derivative.eval 0 = -1 := by simp [F]
  have hn : ‖F.eval 0‖ < ‖F.derivative.eval 0‖ ^ 2 := by
    rw [h0, h1, norm_neg, norm_one, one_pow, norm_mul]
    have h2 : ‖(2 : ℤ_[2])‖ < 1 := by
      have := PadicInt.norm_p (p := 2)
      norm_num at this
      rw [this]; norm_num
    have hk : ‖(k : ℤ_[2])‖ ≤ 1 := PadicInt.norm_le_one _
    nlinarith [norm_nonneg (k : ℤ_[2]), norm_nonneg (2 : ℤ_[2])]
  obtain ⟨z, hz, -⟩ := hensels_lemma hn
  refine ⟨z, ?_⟩
  simpa [F] using hz

open GlobalTheory.CompletedBasis

theorem sq_neg_mem (d : ℕ) (hd : d % 8 = 7) {s : ℂ_[2]} (hs : s ^ 2 = -(d : ℂ_[2])) :
    s ∈ (algebraMap ℚ_[2] ℂ_[2]).fieldRange := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, d + 1 = 8 * k := ⟨(d + 1) / 8, by omega⟩
  obtain ⟨z, hz⟩ := exists_root k
  let φ : ℤ_[2] →+* ℂ_[2] := (algebraMap ℚ_[2] ℂ_[2]).comp PadicInt.Coe.ringHom
  set u : ℂ_[2] := φ (2 * z - 1) with hu
  have hz' : φ z ^ 2 - φ z + 2 * (k : ℂ_[2]) = 0 := by
    have := congrArg φ hz
    simpa only [map_add (f := _), map_sub, map_mul, map_pow, map_ofNat, map_natCast, map_zero] using this
  have hk' : (d : ℂ_[2]) + 1 = 8 * (k : ℂ_[2]) := by exact_mod_cast hk
  have hu2 : u ^ 2 = -(d : ℂ_[2]) := by
    rw [hu]
    simp only [map_sub, map_mul, map_ofNat, map_one]
    linear_combination 4 * hz' + hk'
  have h : (s - u) * (s + u) = 0 := by linear_combination hs - hu2
  rcases mul_eq_zero.1 h with h | h
  · exact ⟨_, (sub_eq_zero.1 h).symm⟩
  · refine ⟨-(PadicInt.Coe.ringHom (2 * z - 1)), ?_⟩
    rw [map_neg]
    change -u = s
    linear_combination -h

variable (D : D7) (lam : Qbar →+* ℂ_[2])

theorem rhoBase_mem_of_K (x : D.host.K) : rhoBase D lam (x : D.host.E) ∈ (algebraMap ℚ_[2] ℂ_[2]).fieldRange := by
  let S : Subfield D.host.E := ((algebraMap ℚ_[2] ℂ_[2]).fieldRange).comap (rhoBase D lam)
  let F : IntermediateField ℚ D.host.E := S.toIntermediateField fun q => by
    refine ⟨(q : ℚ_[2]), ?_⟩
    change _ = rhoBase D lam (algebraMap ℚ D.host.E q)
    rw [eq_ratCast, map_ratCast, map_ratCast]
  have hd16 : D.host.d % 16 = 7 := D.host.hyp.2.2.2.1
  have hb : D.host.sqd ∈ F := by
    change rhoBase D lam (D.host.sqd) ∈ (algebraMap ℚ_[2] ℂ_[2]).fieldRange
    refine sq_neg_mem D.host.d (by omega) ?_
    rw [← map_pow, D.host.sqd_sq, map_neg, map_natCast]
  have hle : D.host.K ≤ F := IntermediateField.adjoin_simple_le_iff.2 hb
  exact hle x.2

theorem rhoK_mem (a : 𝓞 D.host.K) :
    rhoK D lam (a : D.host.K) ∈ closure (Set.range (Nat.cast : ℕ → ℂ_[2])) := by
  obtain ⟨q, hq⟩ := rhoBase_mem_of_K D lam (a : D.host.K)
  have hq' : algebraMap ℚ_[2] ℂ_[2] q = rhoK D lam (a : D.host.K) := hq
  have hn : ‖q‖ ≤ 1 := by
    have := norm_le_one_of_mem (rhoK D lam) (mem_intClosure (rhoK D lam) a)
    rwa [← hq', norm_algebraMap'] at this
  have := coe_mem_closure ⟨q, hn⟩
  rwa [show ((⟨q, hn⟩ : ℤ_[2]) : ℚ_[2]) = q from rfl, hq'] at this

theorem fst_mem_closure_natCast :
    ∀ (D : D7) (lam : Qbar →+* ℂ_[2]), ∀ α ∈ GL3Theta.OKp D lam,
      α.1 ∈ closure (Set.range (Nat.cast : ℕ → ℂ_[2])) := by
  intro D lam α hα
  have h1 : α.1 ∈ (intClosure (rhoK D lam) : Set ℂ_[2]) := by
    rw [← fst_image_OKp]
    exact ⟨α, hα, rfl⟩
  rw [coe_intClosure] at h1
  refine closure_minimal ?_ isClosed_closure h1
  rintro _ ⟨a, rfl⟩
  exact rhoK_mem D lam a

end GlobalTheory.TwoAdicFirst
end

section

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching
open Formalism.MainNotions.PrimeDegreeVariant (embGL Interlace)
open scoped DirectSum

namespace GlobalTheory.Branching

theorem initMinor_ne_zero_of_strictMono {r n s : ℕ} (I : Fin s → Fin r) (hs : s ≤ n) (hI : StrictMono I) :
    initMinor ℂ I hs ≠ 0 := by
  intro h0
  have := (colLexInitMinor ℂ r n s I hs hI).2
  rw [h0] at this
  simp at this

theorem xiB_ne_zero {n : ℕ} (lam sg : Fin n → ℕ) : Formalism.BranchingDeterminantCap.xiB ℂ lam sg ≠ 0 := by
  unfold Formalism.BranchingDeterminantCap.xiB
  refine Finset.prod_ne_zero_iff.2 fun i _ => mul_ne_zero (pow_ne_zero _ ?_) (pow_ne_zero _ ?_)
  · refine initMinor_ne_zero_of_strictMono _ _ fun p q hpq => ?_
    exact hpq
  · refine initMinor_ne_zero_of_strictMono _ _ fun p q hpq => ?_
    have h1 := p.2
    have h2 := q.2
    have h3 := i.2
    rw [Fin.lt_def] at hpq ⊢
    simp only [Formalism.BranchingDeterminantCap.rowsB]
    split_ifs <;> simp <;> omega

theorem det_embGL {n : ℕ} (g : GL (Fin n) ℂ) :
    Matrix.GeneralLinearGroup.det (embGL ℂ n (n + 1) rfl g) = Matrix.GeneralLinearGroup.det g := by
  apply Units.ext
  have e : (embGL ℂ n (n + 1) rfl g : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) =
      (Matrix.fromBlocks (g : Matrix (Fin n) (Fin n) ℂ) 0 0 (1 : Matrix (Fin 1) (Fin 1) ℂ)).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm := rfl
  simp only [Matrix.GeneralLinearGroup.val_det_apply]
  rw [e, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
  simp

theorem transpose_embGL {n : ℕ} (g : GL (Fin n) ℂ) :
    (embGL ℂ n (n + 1) rfl g : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ).transpose =
      Formalism.BranchingDeterminantCap.extM ℂ (g : Matrix (Fin n) (Fin n) ℂ).transpose := by
  ext a b
  rw [Matrix.transpose_apply, embGL_apply]
  simp only [Formalism.BranchingDeterminantCap.extM, Matrix.of_apply, Matrix.transpose_apply]
  by_cases h : a.val < n ∧ b.val < n
  · rw [dite_eq_left h, dite_eq_left h.symm]
  · rw [dite_eq_right h, dite_eq_right (fun h' => h h'.symm)]
    simp only [eq_comm]

theorem exists_intertwining_ne_zero : ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (mu : DomWeight n), Interlace h lam mu → ∃ φ : (smallRep (MonoidHom.id (GL (Fin n) ℂ)) mu).IntertwiningMap (resRep (MonoidHom.id (GL (Fin n) ℂ)) h lam), φ ≠ 0 := by
  intro n N h lam mu hI
  subst h
  set c : ℕ := (mu.detShift - lam.detShift).toNat with hcdef
  have hls : lam.detShift = lam.w (Fin.last n) := by
    simp [DomWeight.detShift, Fin.last]
  have hlow : ∀ i, lam.detShift ≤ lam.w i := fun i => hls ▸ lam.anti (Fin.le_last i)
  have hc : 0 < n → (c : ℤ) = mu.detShift - lam.detShift := by
    intro hn
    have h1 := (hI ⟨n - 1, by omega⟩).2
    have h2 := hlow ⟨n - 1 + 1, by omega⟩
    have h3 : mu.detShift = mu.w ⟨n - 1, by omega⟩ := by simp [DomWeight.detShift, hn]
    simp only at h1
    omega
  have hmlow : ∀ i, mu.detShift ≤ mu.w i := fun i => by
    have hn : 0 < n := i.pos
    have h3 : mu.detShift = mu.w ⟨n - 1, by omega⟩ := by simp [DomWeight.detShift, hn]
    rw [h3]
    refine mu.anti ?_
    have := i.2
    rw [Fin.le_def]
    simp only
    omega
  have hsg : ∀ i, ((mu.natW i + c : ℕ) : ℤ) = mu.w i - lam.detShift := fun i => by
    have h1 := hc i.pos
    have h2 := hmlow i
    simp only [DomWeight.natW]
    omega
  have hlz : ∀ a, Formalism.BranchingDeterminantCap.lamZ (fun i : Fin n => lam.natW i.castSucc) a = lam.w a - lam.detShift := fun a => by
    have h2 := hlow a
    unfold Formalism.BranchingDeterminantCap.lamZ
    split_ifs with ha
    · have : (⟨a.val, ha⟩ : Fin n).castSucc = a := rfl
      simp only [DomWeight.natW, this]
      omega
    · have : a = Fin.last n := Fin.ext (by have := a.2; simp; omega)
      rw [hls, this]; simp
  have hI' : Formalism.BranchingDeterminantCap.Interlace (Formalism.BranchingDeterminantCap.lamZ (fun i : Fin n => lam.natW i.castSucc))
      (fun i => ((mu.natW i + c : ℕ) : ℤ)) := by
    intro i
    simp only [hsg, hlz]
    have h1 : mu.w i ≤ lam.w i.castSucc := (hI i).1
    have h2 : lam.w i.succ ≤ mu.w i := (hI i).2
    constructor <;> omega
  obtain ⟨io, hmem, heq, hhw, -⟩ := Formalism.BranchingDeterminantCap.branchMap ℂ n (fun i : Fin n => lam.natW i.castSucc)
    (fun i => mu.natW i + c) hI'
  obtain ⟨dm, de, dh⟩ := GlobalTheory.Branching.genericDet_pow_mul n c mu.natW
  obtain ⟨am, ae⟩ := GlobalTheory.Branching.AddColumn.add_column (n + 1) n lam.natW (by simp [DomWeight.natW, hls])
  have ha : Antitone mu.natW := fun i j hij => by
    have := mu.anti hij
    simp only [DomWeight.natW]
    omega
  let D : nablaSq ℂ n mu →ₗ[ℂ] dualWeyl ℂ n n (fun i => mu.natW i + c) :=
    { toFun := fun f => ⟨lpMinor ℂ n le_rfl le_rfl ^ c * f, dm f f.2⟩
      map_add' := fun f f' => Subtype.ext (by simp [mul_add])
      map_smul' := fun a f => Subtype.ext (by simp) }
  let L : nablaSq ℂ n mu →ₗ[ℂ] nablaSq ℂ (n + 1) lam :=
    { toFun := fun f => ⟨rename (Prod.map id Fin.castSucc) (io (D f)), am _ (hmem _)⟩
      map_add' := fun f f' => Subtype.ext (by simp)
      map_smul' := fun a f => Subtype.ext (by simp) }
  have hdet : ∀ g : GL (Fin n) ℂ, detPow ℂ n g mu.detShift =
      detPow ℂ n g lam.detShift * (g : Matrix (Fin n) (Fin n) ℂ).det ^ c := by
    intro g
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have : Matrix.GeneralLinearGroup.det g = 1 := Units.ext (by simp)
      simp [detPow, this]
    · have : mu.detShift = lam.detShift + c := by have := hc hn; omega
      rw [this, detPow, detPow, zpow_add, zpow_natCast]
      simp
  have hL : ∀ (g : GL (Fin n) ℂ) (f : nablaSq ℂ n mu),
      L (sqRep ℂ n mu g f) = sqRep ℂ (n + 1) lam (embGL ℂ n (n + 1) rfl g) (L f) := by
    intro g f
    apply Subtype.ext
    have hd0 : detPow ℂ n g lam.detShift ≠ 0 := Units.ne_zero _
    have h1 : io ((detPow ℂ n g lam.detShift)⁻¹ • D (sqRep ℂ n mu g f)) =
        rowAct ℂ (Formalism.BranchingDeterminantCap.extM ℂ (g : Matrix (Fin n) (Fin n) ℂ).transpose) (io (D f)) := by
      apply heq
      change (detPow ℂ n g lam.detShift)⁻¹ • (lpMinor ℂ n le_rfl le_rfl ^ c * sqAct ℂ n mu g f) =
        rowAct ℂ (g : Matrix (Fin n) (Fin n) ℂ).transpose
          (lpMinor ℂ n le_rfl le_rfl ^ c * (f : MvPolynomial (Fin n × Fin n) ℂ))
      rw [de, sqAct, hdet, Matrix.det_transpose, mul_smul_comm, smul_smul, ← mul_assoc,
        inv_mul_cancel₀ hd0, one_mul]
    have h2 : detPow ℂ (n + 1) (embGL ℂ n (n + 1) rfl g) lam.detShift = detPow ℂ n g lam.detShift := by
      rw [detPow, detPow, det_embGL]
    change rename (Prod.map id Fin.castSucc) (io (D (sqRep ℂ n mu g f))) =
      sqAct ℂ (n + 1) lam (embGL ℂ n (n + 1) rfl g) (rename (Prod.map id Fin.castSucc) (io (D f)))
    rw [sqAct, transpose_embGL, ae, ← h1, h2, map_smul, map_smul, smul_smul, mul_inv_cancel₀ hd0, one_smul]
  refine ⟨⟨L, fun g => LinearMap.ext fun f => hL g f⟩, fun h0 => ?_⟩
  have h1 : L ⟨_, hwMem ℂ n n le_rfl _ ha⟩ = 0 := by
    have := congrArg (fun φ => φ.toLinearMap ⟨_, hwMem ℂ n n le_rfl _ ha⟩) h0
    exact this
  have h2 : rename (Prod.map id Fin.castSucc : Fin (n + 1) × Fin n → Fin (n + 1) × Fin (n + 1))
      (io (D ⟨_, hwMem ℂ n n le_rfl _ ha⟩)) = 0 := congrArg Subtype.val h1
  rw [hhw _ (dh ha)] at h2
  have hinj : Function.Injective
      (Prod.map id Fin.castSucc : Fin (n + 1) × Fin n → Fin (n + 1) × Fin (n + 1)) :=
    Function.injective_id.prodMap (Fin.castSucc_injective n)
  have h3 := rename_injective _ hinj (h2.trans (map_zero _).symm)
  rcases smul_eq_zero.1 h3 with h4 | h4
  · exact (Formalism.BranchingDeterminantCap.capConst n _ _ hI').1 (by exact_mod_cast h4)
  · exact xiB_ne_zero _ _ h4

end GlobalTheory.Branching
end

section

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching
open Formalism.MainNotions.PrimeDegreeVariant (embGL Interlace)
open scoped DirectSum

namespace GlobalTheory.Branching

theorem rowAct_mem_of_unitary_stable {n k : ℕ} (M : Submodule ℂ (MvPolynomial (Fin n × Fin k) ℂ))
    (hM : ∀ u ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ f ∈ M, rowAct ℂ u f ∈ M)
    (g : Matrix (Fin n) (Fin n) ℂ) (f : MvPolynomial (Fin n × Fin k) ℂ) (hf : f ∈ M) : rowAct ℂ g f ∈ M := by
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro l hl
  obtain ⟨P, hP⟩ := exists_poly_rowAct_coef n k f l
  have h0 : P = 0 := eq_zero_of_vanish_unitaryGroup n P fun u hu => by
    rw [← hP]
    exact (Submodule.mem_dualAnnihilator l).1 hl _ (hM u hu f hf)
  rw [hP, h0, map_zero]

theorem rowDivClosed_of_rowAct_stable {n k : ℕ} (M : Submodule ℂ (MvPolynomial (Fin n × Fin k) ℂ))
    (hM : ∀ (g : Matrix (Fin n) (Fin n) ℂ), ∀ f ∈ M, rowAct ℂ g f ∈ M) : RowDivClosed M := by
  intro a b j p hp
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro l hl
  set N := (rowGen ℂ a b p).natDegree + j + 1 with hN
  have h1 : (rowGen ℂ a b p).natDegree < N := by omega
  have hk : j ∈ Finset.range N := Finset.mem_range.mpr (by omega)
  set P : Polynomial ℂ := ∑ i ∈ Finset.range N, Polynomial.monomial i (l (rowDiv ℂ a b i p)) with hP
  have hP0 : P = 0 := by
    apply Polynomial.funext
    intro c
    simp only [hP, Polynomial.eval_finsetSum, Polynomial.eval_monomial, Polynomial.eval_zero]
    have e := (Submodule.mem_dualAnnihilator l).1 hl _ (hM (lfockq_mat a b c) p hp)

    rw [← lfockq_eval_rowGen, lfockq_eval_C _ N h1, map_sum] at e
    rw [← e]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← smul_eq_C_mul, map_smul, smul_eq_mul, mul_comm]
    rfl
  have := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p j) hP0
  simp only [hP, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Finsupp.single_apply, Finset.sum_ite_eq',
    if_pos hk, Polynomial.coeff_zero] at this
  exact this

theorem height_rowDiv_le {n k : ℕ} (H : ℤ) (a b : Fin n) (j : ℕ) (f : MvPolynomial (Fin n × Fin k) ℂ)
    (hf : ∀ d ∈ f.support, Finsupp.weight (lhwinHt n k) d ≤ H) :
    ∀ d ∈ (rowDiv ℂ a b j f).support, Finsupp.weight (lhwinHt n k) d ≤ H + j * ((a.val : ℤ) - b.val) := by
  intro e he
  have hs : rowDiv ℂ a b j f = ∑ d ∈ f.support, (rowGen ℂ a b (monomial d (AddMonoidAlgebra.coeff f d))).coeff j := by
    unfold rowDiv
    conv_lhs => rw [f.as_sum]

    rw [map_sum, Polynomial.finsetSum_coeff]
  rw [mem_support_iff, hs, coeff_sum] at he
  obtain ⟨d, hd, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero he
  have h1 := lhwinShift_rowGen_monomial ℂ a b d (AddMonoidAlgebra.coeff f d) j hne
  have h2 := hf d hd
  omega

theorem exists_killed_of_rowDivClosed {n k : ℕ} (M : Submodule ℂ (MvPolynomial (Fin n × Fin k) ℂ))
    (hM : RowDivClosed M) (hne : M ≠ ⊥) :
    ∃ v ∈ M, v ≠ 0 ∧ ∀ a b : Fin n, a < b → ∀ j : ℕ, 1 ≤ j → rowDiv ℂ a b j v = 0 := by
  classical
  have hex : ∃ N : ℕ, ∃ v ∈ M, v ≠ 0 ∧ ∀ d ∈ v.support, Finsupp.weight (lhwinHt n k) d ≤ (N : ℤ) := by
    obtain ⟨f, hfM, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    refine ⟨f.support.sup fun d => (Finsupp.weight (lhwinHt n k) d).toNat, f, hfM, hf0, fun d hd => ?_⟩
    have := Finset.le_sup (f := fun d => (Finsupp.weight (lhwinHt n k) d).toNat) hd
    have h2 : ((Finsupp.weight (lhwinHt n k) d).toNat : ℤ) ≤ _ := Int.ofNat_le.2 this
    exact (Int.self_le_toNat _).trans h2
  obtain ⟨v, hvM, hv0, hvH⟩ := Nat.find_spec hex
  refine ⟨v, hvM, hv0, fun a b hab j hj => ?_⟩
  by_contra hne'
  have hH := height_rowDiv_le _ a b j v hvH
  obtain ⟨d, hd⟩ := ne_zero_iff.mp hne'
  have hnn := (lhwin_weight_nonneg d).trans (hH d (mem_support_iff.2 hd))
  have hab' : (a.val : ℤ) < b.val := by exact_mod_cast (Fin.lt_def.mp hab)
  have hk' : (1 : ℤ) ≤ j := by exact_mod_cast hj
  have hlt : ((Nat.find hex : ℕ) : ℤ) + j * ((a.val : ℤ) - b.val) < (Nat.find hex : ℕ) := by
    nlinarith
  have hmin := Nat.find_min hex (m := (((Nat.find hex : ℕ) : ℤ) + j * ((a.val : ℤ) - b.val)).toNat)
    (by omega)
  apply hmin
  refine ⟨_, hM a b j v hvM, hne', ?_⟩
  rw [Int.toNat_of_nonneg hnn]
  exact hH

theorem dualWeyl_le_of_rowDivClosed {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν)
    (M : Submodule ℂ (MvPolynomial (Fin r × Fin n) ℂ)) (hle : M ≤ dualWeyl ℂ r n ν) (hM : RowDivClosed M)
    (hne : M ≠ ⊥) : dualWeyl ℂ r n ν ≤ M := by
  obtain ⟨v, hvM, hv0, hkill⟩ := exists_killed_of_rowDivClosed M hM hne
  obtain ⟨c, hc⟩ := hwLine ℂ r n hn ν hν v (hle hvM) hkill
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hv0 (by simpa using hc)
  have e : hw ℂ hn ν = c⁻¹ • v := by
    rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have hhw : hw ℂ hn ν ∈ M := e ▸ M.smul_mem _ hvM
  refine (Formalism.BranchingDeterminantCap.bs_dual_le_weyl hn ν hν).trans ?_
  unfold weyl
  rw [Submodule.span_le]
  rintro _ ⟨w, rfl⟩
  induction w with
  | nil => exact hhw
  | cons x w ih => exact hM _ _ _ _ ih

theorem isIrreducible_smallRep_unitary (n : ℕ) (mu : DomWeight n) :
    (smallRep (unitaryIncl n) mu).IsIrreducible := by
  have hnt : Nontrivial (Subrepresentation (smallRep (unitaryIncl n) mu)) :=
    ⟨⊥, ⊤, fun e => bot_ne_top (congrArg Subrepresentation.toSubmodule e)⟩
  refine ⟨fun S => ?_⟩
  by_cases hS : S.toSubmodule = ⊥
  · exact Or.inl (Subrepresentation.ext hS)
  refine Or.inr (Subrepresentation.ext ?_)
  let M : Submodule ℂ (MvPolynomial (Fin n × Fin n) ℂ) := S.toSubmodule.map (nablaSq ℂ n mu).subtype
  have hU : ∀ u ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ f ∈ M, rowAct ℂ u f ∈ M := by
    rintro u hu _ ⟨f, hf, rfl⟩
    let t : Matrix.unitaryGroup (Fin n) ℂ := Matrix.UnitaryGroup.transpose ⟨u, hu⟩
    have h1 : (smallRep (unitaryIncl n) mu t f : MvPolynomial (Fin n × Fin n) ℂ) ∈ M :=
      ⟨_, S.apply_mem_toSubmodule t hf, rfl⟩
    have h2 : (smallRep (unitaryIncl n) mu t f : MvPolynomial (Fin n × Fin n) ℂ) =
        detPow ℂ n (unitaryIncl n t) mu.detShift • rowAct ℂ u f := rfl
    rw [h2] at h1
    exact (M.smul_mem_iff (Units.ne_zero _)).1 h1
  have hcl := rowDivClosed_of_rowAct_stable M (rowAct_mem_of_unitary_stable M hU)
  have hne : M ≠ ⊥ := fun e => hS (Submodule.map_injective_of_injective (nablaSq ℂ n mu).injective_subtype
    (e.trans (Submodule.map_bot _).symm))
  have hle := dualWeyl_le_of_rowDivClosed le_rfl mu.natW (factNatW n mu).1 M
    (Submodule.map_subtype_le (nablaSq ℂ n mu) _) hcl hne
  refine eq_top_iff.2 fun f _ => ?_
  obtain ⟨g, hg, e⟩ := hle f.2
  rwa [← Subtype.ext e]

end GlobalTheory.Branching
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower GlobalTheory.CartanInt Matrix MeasureTheory

theorem _root_.GlobalTheory.T.lam_ballU_le_ofReal_pow : ∀ (p q : ℕ) (lam : Measure (lieU p q)), IsOmegaLeb lam → ∀ r : ℝ, 0 < r → lam (ballU p q r) ≤ ENNReal.ofReal ((18 / 5 * r / ((p + q : ℕ) : ℝ)) ^ ((p + q) ^ 2)) := by
  first | exact @GlobalTheory.CartanInt.LamBall.lam_ballU_le | exact GlobalTheory.CartanInt.LamBall.lam_ballU_le | (intros; apply GlobalTheory.CartanInt.LamBall.lam_ballU_le <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.datum_curve_integral_unitDisc_model : ∀ D : D7, GL3Theta.modelEx D := by
  first | exact @GlobalTheory.UnitModel.modelEx_holds | exact GlobalTheory.UnitModel.modelEx_holds | (intros; apply GlobalTheory.UnitModel.modelEx_holds <;> assumption)
end
