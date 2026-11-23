module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitaryReductionPolynomialHeightBound
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle171
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle078
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle018
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.MemIntegersOfMemIntAd
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle579
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1446
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1589
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.NumberTheory.SelbergSieve
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle032
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

noncomputable section



namespace GlobalTheory.LatMatch

theorem exists_nat_mul_intAf' {F : Type} [Field F] [NumberField F] (t : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) :
    ∃ m : ℕ, 0 < m ∧ (m : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) * t ∈ intAf F := by
  obtain ⟨m, hm, h⟩ := Formalism.L2.SG.Pf.Tau.TraceIntegralityAlt.exists_nat_mul_intAd t
  exact ⟨m, hm, fun v => h v⟩


theorem exists_nat_smul_intAE {D : D7} (w : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :
    ∃ k : ℕ, 0 < k ∧ k • w ∈ intAE D := by
  induction w using TensorProduct.induction_on with
  | zero => exact ⟨1, one_pos, by rw [smul_zero]; exact zero_mem _⟩
  | tmul β z =>
    obtain ⟨m, hm, hβ⟩ := exists_nat_mul_intAf' β
    obtain ⟨M, hM, o, ho⟩ := Formalism.L2.SG.Pf.Tau.TraceIntegralityAlt.exists_nat_mul_mem z
    refine ⟨m * M, Nat.mul_pos hm hM, ?_⟩
    have e : (m * M) • (β ⊗ₜ[D.host.F] z) = ((m : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) * β) ⊗ₜ[D.host.F] ((o : 𝓞 D.host.E) : D.host.E) := by
      have ho' : ((o : 𝓞 D.host.E) : D.host.E) = (M : D.host.E) * z := ho
      rw [ho', mul_smul, ← TensorProduct.tmul_smul, TensorProduct.smul_tmul', nsmul_eq_mul, nsmul_eq_mul]
    rw [e]
    exact AddSubgroup.subset_closure ⟨_, hβ, o, rfl⟩
  | add w w' h h' =>
    obtain ⟨k, hk, m⟩ := h
    obtain ⟨k', hk', m'⟩ := h'
    refine ⟨k * k', Nat.mul_pos hk hk', ?_⟩
    have e : (k * k') • (w + w') = k' • (k • w) + k • (k' • w') := by
      rw [smul_add, ← mul_smul, ← mul_smul, mul_comm k' k]
    rw [e]
    exact add_mem (nsmul_mem m k') (nsmul_mem m' k)

theorem exists_nat_smul_single {D : D7} (V : HSp D) :
    ∃ b : ℕ, 0 < b ∧ ∀ j : Fin V.rank, (Pi.single j (b : D.host.E) : Fin V.rank → D.host.E) ∈ GlobalTheory.Member.latC V := by
  classical
  have hspan := (GlobalTheory.Member.latHat_eq_hat_and_gram D V).2.2.2.1
  have key : ∀ v : Fin V.rank → D.host.E, ∃ m : ℕ, 0 < m ∧ (m : D.host.E) • v ∈ GlobalTheory.Member.latC V := by
    intro v
    have hv : v ∈ Submodule.span D.host.E (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) := by
      rw [hspan]; trivial
    induction hv using Submodule.span_induction with
    | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
    | zero => exact ⟨1, one_pos, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨m, hm, hmx⟩ := hx
      obtain ⟨k, hk, hky⟩ := hy
      refine ⟨m * k, Nat.mul_pos hm hk, ?_⟩
      have e : ((m * k : ℕ) : D.host.E) • (x + y) = k • ((m : D.host.E) • x) + m • ((k : D.host.E) • y) := by
        simp only [smul_add, Nat.cast_mul, ← Nat.cast_smul_eq_nsmul D.host.E, smul_smul]
        rw [mul_comm (k : D.host.E) (m : D.host.E)]
      rw [e]
      exact add_mem (Submodule.smul_of_tower_mem _ k hmx) (Submodule.smul_of_tower_mem _ m hky)
    | smul c x _ hx =>
      obtain ⟨m, hm, hmx⟩ := hx
      obtain ⟨d, hd, hdc⟩ := GlobalTheory.SmoothForms.Reduce.exists_nat_integral (fun _ : Unit => c)
      refine ⟨d * m, Nat.mul_pos hd hm, ?_⟩
      have e : ((d * m : ℕ) : D.host.E) • (c • x) = (⟨(d : D.host.E) * c, (mem_integralClosure_iff _ _).2 (hdc ())⟩ : 𝓞 D.host.E) • ((m : D.host.E) • x) := by
        funext i
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [Algebra.smul_def]
        change (((d * m : ℕ) : D.host.E)) * (c * x i) = ((d : D.host.E) * c) * ((m : D.host.E) * x i)
        push_cast
        ring
      rw [e]
      exact (GlobalTheory.Member.latC V).smul_mem _ hmx
  choose m hm hmv using fun j : Fin V.rank => key (Pi.single j 1)
  refine ⟨∏ j, m j, Finset.prod_pos fun j _ => hm j, fun j => ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
  have : (Pi.single j (((∏ i ∈ Finset.univ.erase j, m i) * m j : ℕ) : D.host.E) : Fin V.rank → D.host.E) =
      (∏ i ∈ Finset.univ.erase j, m i) • ((m j : D.host.E) • Pi.single j 1) := by
    funext i
    rcases eq_or_ne i j with rfl | h
    · simp
    · simp [Pi.single_apply, h]
  rw [this]
  exact Submodule.smul_of_tower_mem _ _ (hmv j)

theorem mul_mem_intAE' (D : D7) {x y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D) (hy : y ∈ intAE D) :
    x * y ∈ intAE D := by
  refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intAE D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, v, rfl⟩
    refine AddSubgroup.subset_closure ⟨a * b, fun w => ?_, u * v, ?_⟩
    · rw [map_mul]; exact mul_mem (ha w) (hb w)
    · rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl
  · intro x _; rw [zero_mul]; exact zero_mem _
  · intro x _; rw [mul_zero]; exact zero_mem _
  · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
  · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
  · intro x y _ _ h; rw [neg_mul]; exact neg_mem h
  · intro x y _ _ h; rw [mul_neg]; exact neg_mem h

theorem mulVec_lamHat_bound : ∀ {D : D7} (V V' : HSp D) (X : Matrix (Fin V'.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)), ∃ N : ℕ, 0 < N ∧ ∀ y ∈ Formalism.L2.NTheta.LamHat V, ((N : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • X.mulVec y ∈ Formalism.L2.NTheta.LamHat V' := by
  intro D V V' X
  classical
  obtain ⟨m, hm, hden⟩ := GlobalTheory.SmoothForms.Reduce.den_hat (D := D) (GlobalTheory.Member.latC V)
    (GlobalTheory.Member.latHat_eq_hat_and_gram D V).2.2.1
  choose k hk hkX using fun p : Fin V'.rank × Fin V.rank => exists_nat_smul_intAE (D := D) (X p.1 p.2)
  have hc : 0 < ∏ p, k p := Finset.prod_pos fun p _ => hk p
  have hcX : ∀ j i, (∏ p, k p) • X j i ∈ intAE D := by
    intro j i
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (j, i)), mul_smul]
    exact nsmul_mem (hkX (j, i)) _
  obtain ⟨b, hb, hbs⟩ := exists_nat_smul_single V'
  refine ⟨b * ((∏ p, k p) * m), Nat.mul_pos hb (Nat.mul_pos hc hm), fun y hy => ?_⟩
  have hy' : ∀ i, m • y i ∈ intAE D := hden y (by rw [← GlobalTheory.LatDual.lamHat_eq_hat]; exact hy)
  have hw : ∀ j, ((∏ p, k p) * m) • X.mulVec y j ∈ intAE D := by
    intro j
    simp only [Matrix.mulVec, dotProduct, Finset.smul_sum]
    refine sum_mem fun i _ => ?_
    have := mul_mem_intAE' D (hcX j i) (hy' i)
    convert this using 1
    simp only [nsmul_eq_mul]
    push_cast
    ring
  have hV' : ∀ w : Fin V'.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E, (∀ j, w j ∈ intAE D) →
      (fun j => (b : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) * w j) ∈ Formalism.L2.NTheta.LamHat V' := by
    intro w hw
    have e : (fun j => (b : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) * w j) = ∑ l, (fun j => w l *
        ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (Pi.single l (b : D.host.E) : Fin V'.rank → D.host.E) j)) := by
      funext j
      rw [Finset.sum_apply, Finset.sum_eq_single j]
      · rw [Pi.single_eq_same, ← Algebra.TensorProduct.natCast_def', mul_comm]
      · intro l _ hl
        rw [Pi.single_eq_of_ne (Ne.symm hl), TensorProduct.tmul_zero, mul_zero]
      · intro h; exact absurd (Finset.mem_univ j) h
    rw [e]
    refine sum_mem fun l _ => GlobalTheory.LatDual.smul_mem_lamHat V' _ (hw l) _ ?_
    refine AddSubgroup.subset_closure ⟨1, fun v => by rw [map_one]; exact one_mem _, _, ?_, rfl⟩
    have h := (GlobalTheory.Member.mem_latC V' _).1 (hbs l)
    rw [Module.Basis.equivFun_symm_apply] at h
    exact h
  have := hV' _ hw
  convert this using 1
  funext j
  simp only [Pi.smul_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_mul]
  ring

end GlobalTheory.LatMatch
end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.TorusHeight

open scoped Matrix.Norms.L2Operator

theorem opNorm_le_of_shape {n q : ℕ} (X Y' : Matrix (Fin n) (Fin q) ℂ) (Y X' : Matrix (Fin q) (Fin n) ℂ)
    (d d' : Fin q → ℂ) {s : ℝ} (hs : 0 ≤ s) (hd : ∀ i, ‖d i‖ ≤ s) (hd' : ∀ i, ‖d' i‖ ≤ s) :
    (opNorm (1 + X * Matrix.diagonal d * Y + Y' * Matrix.diagonal d' * X') : ℝ) ≤
      1 + (‖X‖ * ‖Y‖ + ‖Y'‖ * ‖X'‖) * s := by
  have e : ∀ M : Matrix (Fin n) (Fin n) ℂ, (opNorm M : ℝ) = ‖M‖ := fun M => by
    rw [opNorm, coe_nnNorm]; exact (Matrix.l2_opNorm_def M).symm
  rw [e]
  have h1 : ‖(1 : Matrix (Fin n) (Fin n) ℂ)‖ ≤ 1 := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun _ => by simp
  have hD : ‖Matrix.diagonal d‖ ≤ s := by
    rw [Matrix.l2_opNorm_diagonal]; exact (pi_norm_le_iff_of_nonneg hs).2 hd
  have hD' : ‖Matrix.diagonal d'‖ ≤ s := by
    rw [Matrix.l2_opNorm_diagonal]; exact (pi_norm_le_iff_of_nonneg hs).2 hd'
  have h2 : ‖X * Matrix.diagonal d * Y‖ ≤ ‖X‖ * s * ‖Y‖ :=
    (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right
      ((Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_left hD (norm_nonneg _))) (norm_nonneg _))
  have h3 : ‖Y' * Matrix.diagonal d' * X'‖ ≤ ‖Y'‖ * s * ‖X'‖ :=
    (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right
      ((Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_left hD' (norm_nonneg _))) (norm_nonneg _))
  calc _ ≤ ‖(1 : Matrix (Fin n) (Fin n) ℂ)‖ + ‖X * Matrix.diagonal d * Y‖ + ‖Y' * Matrix.diagonal d' * X'‖ :=
        norm_add₃_le
    _ ≤ 1 + ‖X‖ * s * ‖Y‖ + ‖Y'‖ * s * ‖X'‖ := by linarith
    _ = _ := by ring

theorem le_prod_of_forall_le {q : ℕ} {c : ℝ} (hc : 0 < c) (t : Fin q → ℝ) (ht : ∀ i, c ≤ t i) (k : Fin q) :
    t k * (min 1 c) ^ (q - 1) ≤ ∏ i, t i := by
  have hm : 0 < min 1 c := lt_min one_pos hc
  rw [← Finset.mul_prod_erase Finset.univ t (Finset.mem_univ k)]
  have hk : 0 ≤ t k := hc.le.trans (ht k)
  refine mul_le_mul_of_nonneg_left ?_ hk
  have := Finset.prod_le_prod₀ (s := Finset.univ.erase k) (f := fun _ => min 1 c) (g := t) (fun _ _ => hm.le)
    (fun i _ => (min_le_right _ _).trans (ht i))
  simpa [Finset.prod_const, Finset.card_erase_of_mem, Finset.card_univ, Fintype.card_fin] using this

theorem norm_ofReal_sub_one (x : ℝ) : ‖(x : ℂ) - 1‖ = |x - 1| := by
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

theorem norm_ofReal_inv_sub_one (x : ℝ) : ‖(x : ℂ)⁻¹ - 1‖ = |x⁻¹ - 1| := by
  rw [← Complex.ofReal_inv, norm_ofReal_sub_one]

theorem height_torus_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (q : ℕ) (Xf Yf : Matrix (Fin n) (Fin q) E) (c : ℝ), 0 < c →
    ∃ (C : ℝ) (A : ℕ), ∀ (t : Fin q → ℝ), (∀ i, c ≤ t i) → ∀ a : GAd σ J, a ∈ infPts σ J →
      (∀ (w : InfinitePlace F) (τ : EmbOver E w),
        GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) = (1 + (Xf).map τ.1 * Matrix.diagonal (fun i => ((t i : ℝ) : ℂ) - 1) * (Formalism.UG.cT (σ : E →+* E) Yf * J).map τ.1 +
          (Yf).map τ.1 * Matrix.diagonal (fun i => ((t i : ℝ) : ℂ)⁻¹ - 1) * (Formalism.UG.cT (σ : E →+* E) Xf * J).map τ.1) ∧
        GlobalTheory.Orb.archMat σ J τ (projArch σ J w a⁻¹) = (1 + (Xf).map τ.1 * Matrix.diagonal (fun i => (((fun i => (t i)⁻¹) i : ℝ) : ℂ) - 1) * (Formalism.UG.cT (σ : E →+* E) Yf * J).map τ.1 +
          (Yf).map τ.1 * Matrix.diagonal (fun i => (((fun i => (t i)⁻¹) i : ℝ) : ℂ)⁻¹ - 1) * (Formalism.UG.cT (σ : E →+* E) Xf * J).map τ.1)) →
      (height σ J a : ℝ) ≤ C * (1 + ∏ i, t i) ^ A := by
  intro F E _ _ _ _ _ σ hcm n J q Xf Yf c hc
  classical
  have hm : 0 < min 1 c := lt_min one_pos hc
  set c0 : ℝ := ((min 1 c) ^ (q - 1))⁻¹ + c⁻¹ + 1 with hc0
  have hc0' : 1 ≤ c0 := by
    have : 0 ≤ ((min 1 c) ^ (q - 1))⁻¹ := inv_nonneg.2 (pow_nonneg hm.le _)
    have : 0 ≤ c⁻¹ := inv_nonneg.2 hc.le
    linarith
  let τ0 : ∀ w : InfinitePlace F, EmbOver E w := fun w => Classical.arbitrary _
  let K : InfinitePlace F → ℝ := fun w =>
    ‖(Xf).map (τ0 w).1‖ * ‖(Formalism.UG.cT (σ : E →+* E) Yf * J).map (τ0 w).1‖ +
      ‖(Yf).map (τ0 w).1‖ * ‖(Formalism.UG.cT (σ : E →+* E) Xf * J).map (τ0 w).1‖
  have hK : ∀ w, 0 ≤ K w := fun w => by positivity
  refine ⟨∏ w, (1 + K w * c0), Fintype.card (InfinitePlace F), fun t ht a ha hA => ?_⟩
  set P := ∏ i, t i with hP'
  have hP : 0 ≤ P := Finset.prod_nonneg fun i _ => hc.le.trans (ht i)
  have hs : 0 ≤ c0 * (1 + P) := by positivity
  have hs1 : ∀ k, |t k - 1| ≤ c0 * (1 + P) := fun k => by
    have htk : 0 ≤ t k := hc.le.trans (ht k)
    have h1 := le_prod_of_forall_le hc t ht k
    have hpow : 0 < (min 1 c) ^ (q - 1) := pow_pos hm _
    have h2 : t k ≤ ((min 1 c) ^ (q - 1))⁻¹ * P := by
      rw [← div_eq_inv_mul, le_div_iff₀ hpow]; exact h1
    have h3 : |t k - 1| ≤ t k + 1 := by
      rw [abs_le]; constructor <;> linarith
    have h4 : ((min 1 c) ^ (q - 1))⁻¹ * P ≤ c0 * P := by
      apply mul_le_mul_of_nonneg_right _ hP
      have : 0 ≤ c⁻¹ := inv_nonneg.2 hc.le
      linarith
    nlinarith
  have hs2 : ∀ k, |(t k)⁻¹ - 1| ≤ c0 * (1 + P) := fun k => by
    have htk : 0 < t k := hc.trans_le (ht k)
    have h1 : (t k)⁻¹ ≤ c⁻¹ := inv_anti₀ hc (ht k)
    have h0 : 0 ≤ (t k)⁻¹ := inv_nonneg.2 htk.le
    have h3 : |(t k)⁻¹ - 1| ≤ (t k)⁻¹ + 1 := by
      rw [abs_le]; constructor <;> linarith
    have : 0 ≤ ((min 1 c) ^ (q - 1))⁻¹ := inv_nonneg.2 (pow_nonneg hm.le _)
    nlinarith

  have hfin : ∀ v, htFin F v (matHom _ σ J (proj σ J v a)) = 1 := fun v => by
    rw [mem_infPts_iff_forall.1 ha v, map_one]
    exact htOf_eq_one.2 ⟨by simpa using normFin_one_le (E := E) F v, by simpa using normFin_one_le (E := E) F v⟩

  have hinf : ∀ w, (htInf F w (matHom _ σ J (projArch σ J w a)) : ℝ) ≤ (1 + K w * c0) * (1 + P) := by
    intro w
    obtain ⟨h1, h2⟩ := hA w (τ0 w)
    have e1 : normInf F w ((matHom _ σ J (projArch σ J w a) : GL (Fin n) (w.Completion ⊗[F] E)) :
        Matrix (Fin n) (Fin n) (w.Completion ⊗[F] E)) = opNorm (GlobalTheory.Orb.archMat σ J (τ0 w) (projArch σ J w a)) :=
      normInf_eq_opNorm hcm (τ0 w) _
    have e2 : normInf F w (((matHom _ σ J (projArch σ J w a))⁻¹ : GL (Fin n) (w.Completion ⊗[F] E)) :
        Matrix (Fin n) (Fin n) (w.Completion ⊗[F] E)) =
        opNorm (GlobalTheory.Orb.archMat σ J (τ0 w) (projArch σ J w a⁻¹)) := by
      rw [← map_inv, ← map_inv]; exact normInf_eq_opNorm hcm (τ0 w) _
    have B1 : (opNorm (GlobalTheory.Orb.archMat σ J (τ0 w) (projArch σ J w a)) : ℝ) ≤ 1 + K w * (c0 * (1 + P)) := by
      rw [h1]
      refine (opNorm_le_of_shape _ _ _ _ _ _ hs (fun i => ?_) (fun i => ?_)).trans le_rfl
      · rw [norm_ofReal_sub_one]; exact hs1 i
      · rw [norm_ofReal_inv_sub_one]; exact hs2 i
    have B2 : (opNorm (GlobalTheory.Orb.archMat σ J (τ0 w) (projArch σ J w a⁻¹)) : ℝ) ≤ 1 + K w * (c0 * (1 + P)) := by
      rw [h2]
      refine (opNorm_le_of_shape _ _ _ _ _ _ hs (fun i => ?_) (fun i => ?_)).trans le_rfl
      · rw [norm_ofReal_sub_one]; exact hs2 i
      · rw [norm_ofReal_inv_sub_one, inv_inv]; exact hs1 i
    have hfin' : (1 + K w * (c0 * (1 + P))) ≤ (1 + K w * c0) * (1 + P) := by
      have := hK w; nlinarith
    have hone : (1 : ℝ) ≤ (1 + K w * c0) * (1 + P) := by
      have := hK w; nlinarith
    simp only [htInf, htOf, NNReal.coe_max, NNReal.coe_one]
    rw [e1, e2]
    exact max_le hone (max_le (B1.trans hfin') (B2.trans hfin'))
  have hh : (height σ J a : ℝ) = ∏ w, (htInf F w (matHom _ σ J (projArch σ J w a)) : ℝ) := by
    rw [height_eq]
    simp only [hfin, finprod_one, mul_one, NNReal.coe_prod]
  rw [hh]
  calc _ ≤ ∏ w, ((1 + K w * c0) * (1 + P)) :=
        Finset.prod_le_prod₀ (fun _ _ => NNReal.coe_nonneg _) (fun w _ => hinf w)
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

end GlobalTheory.TorusHeight
end
end

section

open MeasureTheory Matrix GlobalTheory.Orb
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)
open scoped ContDiff

namespace GlobalTheory.CutoffPoly

theorem contDiff_entry {n : ℕ} (i j : Fin n) : ContDiff ℝ ∞ (fun M : Fin n → Fin n → ℂ => M i j) :=
  (contDiff_apply ℝ (fun _ => ℂ) j).comp (contDiff_apply ℝ (fun _ => (Fin n → ℂ)) i)

theorem contDiff_eval {X σ : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (c : σ → X → ℂ)
    (hc : ∀ s, ContDiff ℝ ∞ (c s)) (P : MvPolynomial σ ℂ) :
    ContDiff ℝ ∞ (fun x => MvPolynomial.eval (fun s => c s x) P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using contDiff_const
  | add p q hp hq => simpa using hp.add hq
  | mul_X p s hp => simpa using hp.mul (hc s)

theorem cutoff_mul_poly_mem_ccMat : ∀ (n : ℕ) (ε : Fin n → Bool) (F : ℝ → ℝ) (R : ℝ), ContDiff ℝ ∞ F → (∀ x, R ≤ x → F x = 0) → ∀ P : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ, (fun g : UJ ε => ((F (∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖(toM g) z.1.1 z.1.2‖ ^ 2) : ℝ) : ℂ) * MvPolynomial.eval (Sum.elim (fun z : Fin n × Fin n => (toM g) z.1 z.2) (fun z : Fin n × Fin n => star ((toM g) z.1 z.2))) P) ∈ CcMat (ujMat ε) := by
  intro n ε F R hF hR P
  refine mem_ccSmooth.2 ⟨?_, fun M : Fin n → Fin n → ℂ =>
    ((F (∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖M z.1.1 z.1.2‖ ^ 2) : ℝ) : ℂ) *
      MvPolynomial.eval (fun s => Sum.elim (fun (z : Fin n × Fin n) (M : Fin n → Fin n → ℂ) => M z.1 z.2)
        (fun (z : Fin n × Fin n) (M : Fin n → Fin n → ℂ) => star (M z.1 z.2)) s M) P, ?_, ?_⟩
  · refine HasCompactSupport.intro (GlobalTheory.T.isCompact_pseudoUnitary_offDiag_norm_sublevel n ε R) fun g hg => ?_
    have h : R ≤ ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖(toM g) z.1.1 z.1.2‖ ^ 2 :=
      (not_le.1 hg).le
    rw [hR _ h]; simp
  · refine ContDiff.mul (Complex.ofRealCLM.contDiff.comp (hF.comp ?_)) (contDiff_eval _ ?_ P)
    · exact ContDiff.sum fun z _ => (contDiff_norm_sq ℂ).comp (contDiff_entry _ _)
    · rintro (z | z)
      · exact contDiff_entry _ _
      · exact Complex.conjCLE.contDiff.comp (contDiff_entry z.1 z.2)
  · intro g
    congr 3
    funext s
    rcases s with z | z <;> rfl

end GlobalTheory.CutoffPoly
end

section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

noncomputable section

namespace GlobalTheory.LFun.SatConj

open ComplexConjugate

theorem esymm_map_conj (s : Multiset ℂ) (j : ℕ) : (s.map (starRingEnd ℂ)).esymm j = conj (s.esymm j) := by
  simp only [Multiset.esymm, Multiset.powersetCard_map, Multiset.map_map, map_multiset_sum]
  congr 1
  refine Multiset.map_congr rfl fun t _ => ?_
  simp [map_multiset_prod]

theorem conj_satEig (q n : ℕ) (B : Multiset ℂˣ) (j : ℕ) :
    conj (GlobalTheory.LFun.satEig q n B j) = GlobalTheory.LFun.satEig q n (B.map star) j := by
  have hz : conj (((j : ℂ) * ((n : ℂ) - j)) / 2) = ((j : ℂ) * ((n : ℂ) - j)) / 2 := by
    rw [map_div₀, map_mul, map_sub, Complex.conj_natCast, Complex.conj_natCast, map_ofNat]
  have harg : (q : ℂ).arg ≠ Real.pi := by
    rw [Complex.natCast_arg]; exact Real.pi_pos.ne
  have hp : conj ((q : ℂ) ^ (((j : ℂ) * ((n : ℂ) - j)) / 2)) = (q : ℂ) ^ (((j : ℂ) * ((n : ℂ) - j)) / 2) := by
    have := Complex.conj_cpow (q : ℂ) (((j : ℂ) * ((n : ℂ) - j)) / 2) harg
    rw [hz, Complex.conj_natCast] at this
    exact this.symm
  have hm : ((B.map star).map fun b : ℂˣ => (b : ℂ)) = (B.map fun b : ℂˣ => (b : ℂ)).map (starRingEnd ℂ) := by
    simp only [Multiset.map_map]
    refine Multiset.map_congr rfl fun b _ => ?_
    simp [Units.coe_star]
  rw [GlobalTheory.LFun.satEig, GlobalTheory.LFun.satEig, map_mul, hp, hm, esymm_map_conj]

theorem conj_Tj {L : Type} [Field L] (n : ℕ) (O : Subring L) (ϖ : L) (j : ℕ) (g : GL (Fin n) L) :
    conj (Formalism.UG.Tj ℂ n O ϖ j g) = Formalism.UG.Tj ℂ n O ϖ j g := by
  classical
  unfold Formalism.UG.Tj
  rw [Set.indicator_apply]
  split_ifs <;> simp

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V}
  {ρ' : Representation ℂ (GL (Fin n) (w.adicCompletion E)) W}

theorem isSatVecGL_conj (J : V ≃ₗ⋆[ℂ] W) (hJ : ∀ g x, ρ' g (J x) = J (ρ g x)) {x : V} {B : Multiset ℂˣ}
    (h : GlobalTheory.LFun.IsSatVecGL w ρ x B) : GlobalTheory.LFun.IsSatVecGL w ρ' (J x) (B.map star) := by
  obtain ⟨h0, hfix, hcard, hT⟩ := h
  refine ⟨fun e => h0 (J.map_eq_zero_iff.1 e), GlobalTheory.LGrp.mem_fixed.2 fun k hk => by
    rw [hJ, GlobalTheory.LGrp.mem_fixed.1 hfix k hk], by simp [hcard], fun ϖ hϖ j hj => ?_⟩
  have hfin := GlobalTheory.LFun.finite_heckeVec (Formalism.UG.Final.GLintComm E w n) (GlobalTheory.LFun.Tj_mem_hecke hϖ j) ρ x
  have e1 : GlobalTheory.LFun.heckeVec ρ' (GlobalTheory.LFun.KGL w (n := n)) (Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j) (J x) =
      J (GlobalTheory.LFun.heckeVec ρ (GlobalTheory.LFun.KGL w (n := n)) (Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j) x) := by
    rw [GlobalTheory.LFun.heckeVec, GlobalTheory.LFun.heckeVec]
    refine (finsum_congr fun c => ?_).trans
      (AddMonoidHom.map_finsum (J.toLinearMap.toAddMonoidHom) hfin).symm
    simp [hJ, conj_Tj]
  rw [e1, hT ϖ hϖ j hj, LinearEquiv.map_smulₛₗ, conj_satEig]

end GlobalTheory.LFun.SatConj


open GlobalTheory.LFun.SatConj in
theorem GlobalTheory.LFun.hasSatGL_of_conjIntertwiner : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (ρ' : Representation ℂ (GL (Fin n) (w.adicCompletion E)) W) (J : V ≃ₗ⋆[ℂ] W), (∀ g x, ρ' g (J x) = J (ρ g x)) → ∀ B : Multiset ℂˣ, GlobalTheory.LFun.HasSatGL w ρ B → GlobalTheory.LFun.HasSatGL w ρ' (B.map star) := by
  intro E _ _ w n V W _ _ _ _ ρ ρ' J hJ B hB
  have hJs : ∀ g y, ρ g (J.symm y) = J.symm (ρ' g y) := fun g y => by
    apply J.injective
    rw [← hJ, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  obtain ⟨x, hx⟩ := hB.exists_vec
  refine ⟨(Submodule.ne_bot_iff _).2 ⟨J x, (isSatVecGL_conj J hJ hx).2.1, (isSatVecGL_conj J hJ hx).1⟩,
    fun y hy h0 => ?_⟩
  have hy' : J.symm y ∈ GlobalTheory.PRep.fixed ρ (GlobalTheory.LFun.KGL w (n := n)) := GlobalTheory.LGrp.mem_fixed.2 fun k hk => by
    rw [hJs, GlobalTheory.LGrp.mem_fixed.1 hy k hk]
  have := isSatVecGL_conj J hJ (hB.2 _ hy' fun e => h0 (by simpa using congrArg J e))
  rwa [LinearEquiv.apply_symm_apply] at this
end
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.finiteDimensional_eigen_intertwiners : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ (W : Submodule ℂ (Sm E a)) (hW : ∀ k, ∀ w ∈ W, cptRep E a k w ∈ W), FiniteDimensional ℂ W → ∀ (c : (E →+* ℂ) → ℂ → ℂ) (N : Submodule ℂ (W →ₗ[ℂ] Sm E a)), N ≤ maps L W hW → (∀ T ∈ N, ∀ τ u, cap τ u ∘ₗ T = c τ u • T) → FiniteDimensional ℂ N := by
  first | exact @GlobalTheory.AutGrowth.finiteDimensional_capEigen_maps | exact GlobalTheory.AutGrowth.finiteDimensional_capEigen_maps | (intros; apply GlobalTheory.AutGrowth.finiteDimensional_capEigen_maps <;> assumption)
end
