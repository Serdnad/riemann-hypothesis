module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle156
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1231
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1232
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1233
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1339
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1752
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1679
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle364
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle337
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1735
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle639
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle547
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1759
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle651
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle701
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle140
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtSchrodingerLinePureTensorZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle876
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1758
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1763
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonemptyCompactDualHaar
import Formalism.PadicSubsetSums.StableGradedCounts.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb

noncomputable section

namespace GlobalTheory.InertUnitOrb

theorem isIntegral_iff_of_mulVec {K : UQ} (B : InvAlg K) {n : ℕ} (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)) (a : B.A)
    (M : Matrix (Fin n) (Fin n) K.E) (h : ∀ y, ψ (a * y) = M *ᵥ ψ y) : IsIntegral K.O a ↔ IsIntegral K.O M := by
  let b : Module.Basis (Fin n) K.E B.A := Module.Basis.ofEquivFun ψ
  let φ : B.A →ₐ[K.O] Matrix (Fin n) (Fin n) K.E := (Algebra.leftMulMatrix b).restrictScalars K.O
  have hinj : Function.Injective φ := Algebra.leftMulMatrix_injective b
  have hφ : φ a = M := by
    ext i j
    change Algebra.leftMulMatrix b a i j = M i j
    rw [Algebra.leftMulMatrix_eq_repr_mul, ← Module.Basis.equivFun_apply, Module.Basis.equivFun_ofEquivFun, h]
    simp [b, Module.Basis.coe_ofEquivFun, Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [← hφ]
  exact (isIntegral_algHom_iff φ hinj).symm

theorem cptPart_iff_intUnits_of_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ (x : B.Aˣ) (γ : UL n w), IsModel B ((((γ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) x ψ → B.P.Separable → ∀ τ : twCent (MonoidHom.id (UL n w)) γ ≃* B.T, (∀ (t : twCent (MonoidHom.id (UL n w)) γ) (y : B.A), ψ (((τ t : B.Aˣ) : B.A) * y) = (((((t : UL n w) : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) *ᵥ ψ y) → ∀ t : twCent (MonoidHom.id (UL n w)) γ, ((t : UL n w) ∈ cptPart (twCent (MonoidHom.id (UL n w)) γ) ↔ ((τ t : B.Aˣ)) ∈ intUnits K.O B.A) := by
  intro E _ _ _ hE w hw K e he hint n B ψ x γ hmod hsep τ hτ t
  have hcont := (GlobalTheory.ConjAtPlace.main E hE w).1
  have hcl : IsClosed ((UL n w : Subgroup (GLw n w)) : Set (GLw n w)) := by
    unfold UL; rw [if_neg hw]
    have : ((UJ (cj w) (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) : Subgroup _) : Set (GLw n w)) =
        (fun g : GLw n w => cT (cj w) (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * 1 *
          (g : Matrix (Fin n) (Fin n) (w.adicCompletion E))) ⁻¹' {1} := rfl
    rw [this]
    refine IsClosed.preimage ?_ isClosed_singleton
    unfold cT
    exact (((Units.continuous_val.matrix_map hcont).matrix_transpose).matrix_mul continuous_const).matrix_mul
      Units.continuous_val
  have hmat : ∀ (g : GLw n w) (k : ℕ) i j,
      e ((((g : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) ^ k) i j) =
        ((g ^ k : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j := by
    intro g k i j
    have : ((g : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) ^ k =
        ((g ^ k : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm := by
      rw [Units.val_pow_eq_pow_val]
      exact (map_pow (e.symm.toRingHom.mapMatrix) _ k).symm
    rw [this, Matrix.map_apply, RingEquiv.apply_symm_apply]
  have key : ∀ s : twCent (MonoidHom.id (UL n w)) γ,
      IsCompact (closure (Subgroup.zpowers (s : UL n w) : Set (UL n w))) ↔ (τ s : B.Aˣ) ∈ intUnits K.O B.A := by
    intro s
    have hinv : ((τ s : B.Aˣ))⁻¹ = ((τ s⁻¹ : B.T) : B.Aˣ) := by rw [map_inv, Subgroup.coe_inv]
    have hI1 : IsIntegral K.O ((τ s : B.Aˣ) : B.A) ↔ ∃ m : ℤ, ∀ k : ℕ, ∀ i j,
        Valued.v (((((s : UL n w) : GLw n w) ^ k : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤
          WithZero.exp m := by
      rw [isIntegral_iff_of_mulVec B ψ _ _ (hτ s), GlobalTheory.T.isIntegral_matrix_iff_bounded_powers K e hint n]
      simp only [hmat]
    have hI2 : IsIntegral K.O ((((τ s : B.Aˣ))⁻¹ : B.Aˣ) : B.A) ↔ ∃ m : ℤ, ∀ k : ℕ, ∀ i j,
        Valued.v (((((s : UL n w) : GLw n w)⁻¹ ^ k : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤
          WithZero.exp m := by
      rw [hinv, isIntegral_iff_of_mulVec B ψ _ _ (hτ s⁻¹), GlobalTheory.T.isIntegral_matrix_iff_bounded_powers K e hint n]
      simp only [hmat, Subgroup.coe_inv]
    rw [GlobalTheory.T.isCompact_closure_zpowers_iff_bounded_entries w n (UL n w) hcl (s : UL n w)]
    show _ ↔ IsIntegral K.O _ ∧ IsIntegral K.O _
    rw [hI1, hI2]
    simp only [SubgroupClass.coe_zpow]
    constructor
    · rintro ⟨m, hm⟩
      refine ⟨⟨m, fun k i j => ?_⟩, ⟨m, fun k i j => ?_⟩⟩
      · have := hm (k : ℤ) i j
        rwa [zpow_natCast] at this
      · have := hm (-(k : ℤ)) i j
        rwa [_root_.zpow_neg, zpow_natCast, ← inv_pow] at this
    · rintro ⟨⟨m1, h1⟩, ⟨m2, h2⟩⟩
      refine ⟨max m1 m2, fun k i j => ?_⟩
      rcases Int.eq_nat_or_neg k with ⟨l, rfl | rfl⟩
      · rw [zpow_natCast]
        exact (h1 l i j).trans (WithZero.exp_le_exp.2 (le_max_left _ _))
      · rw [_root_.zpow_neg, zpow_natCast, ← inv_pow]
        exact (h2 l i j).trans (WithZero.exp_le_exp.2 (le_max_right _ _))
  let H' : Subgroup (UL n w) := ((intUnits K.O B.A).comap (B.T.subtype.comp τ.toMonoidHom)).map
    (twCent (MonoidHom.id (UL n w)) γ).subtype
  constructor
  · intro ht
    have hle : cptPart (twCent (MonoidHom.id (UL n w)) γ) ≤ H' := by
      rw [cptPart, Subgroup.closure_le]
      rintro u ⟨hu, hc⟩
      exact ⟨⟨u, hu⟩, (key ⟨u, hu⟩).1 hc, rfl⟩
    obtain ⟨t₀, ht₀, he₀⟩ := hle ht
    have : t₀ = t := Subtype.ext he₀
    subst this
    exact ht₀
  · intro ht
    exact Subgroup.subset_closure ⟨t.2, (key t).2 ht⟩

end GlobalTheory.InertUnitOrb
end
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovTop.VolUp.LowBall

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem exists_lam (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r)
    (hx : ∀ τ, (mat x τ).det ≠ 0) :
    ∃ lam : Measure (realLie Ψ G), lam.IsAddHaarMeasure ∧ lam.map Subtype.val = riemLie Ψ G x := by
  set W := (realLie Ψ G).comap (fromFrame x)
  let Φ : W →ₗ[ℝ] realLie Ψ G :=
    ((fromFrame x).comp W.subtype).codRestrict (realLie Ψ G) (fun v => v.2)
  have key2 : ∀ τ (A : Matrix (Fin r) (Fin r) ℂ),
      mat x τ * ((mat x τ)⁻¹ * A * mat x τ) * (mat x τ)⁻¹ = A := fun τ A => by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ (hx τ).isUnit,
      Matrix.mul_nonsing_inv_cancel_left _ _ (hx τ).isUnit]
  have hsurj : Function.Surjective Φ := by
    intro X
    let Y : EuclideanSpace ℂ (Ψ × Fin r × Fin r) := WithLp.toLp 2 (fun p : Ψ × Fin r × Fin r =>
      ((mat x p.1)⁻¹ * Matrix.of (X.1 p.1) * mat x p.1) p.2.1 p.2.2)
    have hY : fromFrame x Y = X.1 := by
      funext τ
      have e : Matrix.of (fun a b => Y (τ, a, b)) = (mat x τ)⁻¹ * Matrix.of (X.1 τ) * mat x τ := by
        ext a b; simp [Y]
      change (mat x τ * Matrix.of _ * (mat x τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) = X.1 τ
      rw [e, key2]; rfl
    exact ⟨⟨Y, show fromFrame x Y ∈ realLie Ψ G by rw [hY]; exact X.2⟩, Subtype.ext hY⟩
  have key1 : ∀ τ (A : Matrix (Fin r) (Fin r) ℂ),
      (mat x τ)⁻¹ * (mat x τ * A * (mat x τ)⁻¹) * mat x τ = A := fun τ A => by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_right _ _ (hx τ).isUnit,
      Matrix.nonsing_inv_mul_cancel_left _ _ (hx τ).isUnit]
  have hinj : Function.Injective Φ := by
    intro Y Z h
    have h' : fromFrame x Y.1 = fromFrame x Z.1 := congrArg Subtype.val h
    have hτ : ∀ τ, Matrix.of (fun a b => Y.1 (τ, a, b)) = Matrix.of (fun a b => Z.1 (τ, a, b)) := by
      intro τ
      have h1 : mat x τ * Matrix.of (fun a b => Y.1 (τ, a, b)) * (mat x τ)⁻¹ =
          mat x τ * Matrix.of (fun a b => Z.1 (τ, a, b)) * (mat x τ)⁻¹ := congrFun h' τ
      rw [← key1 τ (Matrix.of (fun a b => Y.1 (τ, a, b))), h1, key1]
    refine Subtype.ext (PiLp.ext fun p => ?_)
    obtain ⟨τ, a, b⟩ := p
    exact congrFun (congrFun (hτ τ) a) b
  let φ : W ≃L[ℝ] realLie Ψ G := (LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩).toContinuousLinearEquiv
  refine ⟨(stdOrthonormalBasis ℝ W).toBasis.addHaar.map φ, φ.isAddHaarMeasure_map _, ?_⟩
  rw [Measure.map_map measurable_subtype_coe φ.continuous.measurable]
  rfl

theorem exists_conj_bound (Ψ : Finset (E →+* ℂ)) (x : Frame Ψ r) (hx : ∀ τ, (mat x τ).det ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (X : Ψ → Fin r → Fin r → ℂ), 0 ≤ t →
      (∀ τ a b, ‖((mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ) a b‖ ≤ t) → ‖X‖ ≤ C * t := by
  let L : (Ψ → Fin r → Fin r → ℂ) →ₗ[ℝ] (Ψ → Fin r → Fin r → ℂ) :=
    { toFun := fun Y τ => (mat x τ * Matrix.of (Y τ) * (mat x τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ)
      map_add' := fun Y Z => by
        funext τ
        change mat x τ * (Matrix.of (Y τ) + Matrix.of (Z τ)) * (mat x τ)⁻¹ = _
        rw [Matrix.mul_add, Matrix.add_mul]; rfl
      map_smul' := fun c Y => by
        funext τ
        change mat x τ * ((c : ℂ) • Matrix.of (Y τ)) * (mat x τ)⁻¹ = _
        rw [Matrix.mul_smul, Matrix.smul_mul]; rfl }
  let Lc := LinearMap.toContinuousLinearMap L
  refine ⟨‖Lc‖ + 1, by positivity, fun t X ht hX => ?_⟩
  let Y : Ψ → Fin r → Fin r → ℂ := fun τ => ((mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ : Matrix (Fin r) (Fin r) ℂ)
  have hLY : Lc Y = X := by
    funext τ
    change mat x τ * ((mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ) * (mat x τ)⁻¹ = Matrix.of (X τ)
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ (hx τ).isUnit,
      Matrix.mul_nonsing_inv_cancel_left _ _ (hx τ).isUnit]
  have hY : ‖Y‖ ≤ t := by
    refine (pi_norm_le_iff_of_nonneg ht).2 fun τ => (pi_norm_le_iff_of_nonneg ht).2 fun a =>
      (pi_norm_le_iff_of_nonneg ht).2 fun b => hX τ a b
  calc ‖X‖ = ‖Lc Y‖ := by rw [hLY]
    _ ≤ ‖Lc‖ * ‖Y‖ := Lc.le_opNorm Y
    _ ≤ ‖Lc‖ * t := by gcongr
    _ ≤ (‖Lc‖ + 1) * t := by nlinarith

section Exp

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem exists_exp_bound (n : Type) [Fintype n] [DecidableEq n] :
    ∃ δ : ℝ, 0 < δ ∧ ∀ Y : Matrix n n ℂ, ‖Y‖ < δ → ‖NormedSpace.exp Y - 1‖ ≤ 2 * ‖Y‖ := by
  have h := (hasFDerivAt_iff_isLittleO_nhds_zero.1
    (GlobalTheory.CompactDualExists.exp_strict (n := n)).hasFDerivAt).def (zero_lt_one' ℝ)
  obtain ⟨δ, hδ, hh⟩ := Metric.eventually_nhds_iff.1 h
  refine ⟨δ, hδ, fun Y hY => ?_⟩
  have := hh (y := Y) (by rwa [dist_zero_right])
  simp only [zero_add, NormedSpace.exp_zero, one_mul] at this
  have this : ‖NormedSpace.exp Y - 1 - Y‖ ≤ ‖Y‖ := this
  calc ‖NormedSpace.exp Y - 1‖ = ‖Y + (NormedSpace.exp Y - 1 - Y)‖ := by congr 1; abel
    _ ≤ ‖Y‖ + ‖NormedSpace.exp Y - 1 - Y‖ := norm_add_le _ _
    _ ≤ 2 * ‖Y‖ := by linarith

theorem exists_exp_entry (n : Type) [Fintype n] [DecidableEq n] :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (ε : ℝ) (Y : Matrix n n ℂ), 0 < ε → ε < δ → (∀ a b, ‖Y a b‖ < ε / 2) →
      ∀ a b, ‖(NormedSpace.exp Y - 1) a b‖ < ε := by
  obtain ⟨δ, hδ, h⟩ := exists_exp_bound n
  refine ⟨δ, hδ, fun ε Y hε hεδ hY a b => ?_⟩
  have hYn : ‖Y‖ < ε / 2 := (Matrix.norm_lt_iff (by positivity)).2 hY
  calc ‖(NormedSpace.exp Y - 1) a b‖ ≤ ‖NormedSpace.exp Y - 1‖ := Matrix.norm_entry_le_entrywise_sup_norm _
    _ ≤ 2 * ‖Y‖ := h Y (by linarith)
    _ < ε := by linarith

end Exp

theorem riemHaar_frBall_ge : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ))
    (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r), 1 ≤ r → G.det ≠ 0 → (∀ τ, (mat x τ).det ≠ 0) →
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ENNReal.ofReal ((ε / (2 * ((Ψ.card : ℝ) * (r : ℝ) ^ 2))) ^ (Ψ.card * (r ^ 2 - 1)) / 2) ≤
        riemHaar Ψ G x (frBall Ψ G x ε) := by
  intro E _ _ _ r Ψ G x hr hG hx
  obtain ⟨lam, hlam, hmap⟩ := exists_lam Ψ G x hx
  obtain ⟨δ, hδ, hlow⟩ := GlobalTheory.T.lieHaar_le_two_mul_tangentNormalizedHaar E r Ψ G hG lam
  obtain ⟨C, hC, hconj⟩ := exists_conj_bound Ψ x hx
  obtain ⟨δ', hδ', hexp⟩ := exists_exp_entry (Fin r)
  refine ⟨min 2 (min δ' (δ / C)), lt_min two_pos (lt_min hδ' (div_pos hδ hC)), fun ε hε hε₀ => ?_⟩
  have hε2 : ε < 2 := lt_of_lt_of_le hε₀ (min_le_left _ _)
  have hεδ' : ε < δ' := lt_of_lt_of_le hε₀ ((min_le_right _ _).trans (min_le_left _ _))
  have hεC : ε < δ / C := lt_of_lt_of_le hε₀ ((min_le_right _ _).trans (min_le_right _ _))
  set S : Set (Ψ → Fin r → Fin r → ℂ) :=
    {X | ∀ τ a b, ‖((mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ) a b‖ < ε / 2} with hS
  have hcont : ∀ τ a b, Continuous (fun X : Ψ → Fin r → Fin r → ℂ =>
      ((mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ) a b) := by
    intro τ a b
    exact ((continuous_const.matrix_mul (continuous_apply τ)).matrix_mul continuous_const).matrix_elem a b
  have hSm : MeasurableSet S := by
    simp only [hS, Set.setOf_forall]
    exact MeasurableSet.iInter fun τ => MeasurableSet.iInter fun a => MeasurableSet.iInter fun b =>
      measurableSet_lt (hcont τ a b).norm.measurable measurable_const
  set s : Set (realLie Ψ G) := Subtype.val ⁻¹' S with hs
  have hsm : MeasurableSet s := measurable_subtype_coe hSm
  have h1 : ENNReal.ofReal ((ε / 2 / ((Ψ.card : ℝ) * (r : ℝ) ^ 2)) ^ (Ψ.card * (r ^ 2 - 1))) ≤ lam s := by
    have := GlobalTheory.T.riemannianLieMeasure_frameBox_ge E r Ψ G x hr hG hx (ε / 2) (by positivity) (by linarith)
    rw [← hmap, Measure.map_apply measurable_subtype_coe hSm] at this
    exact this
  have hball : s ⊆ Metric.ball 0 δ := by
    intro X hX
    rw [mem_ball_zero_iff]
    have h := hconj (ε / 2) X.1 (by positivity) fun τ a b => (hX τ a b).le
    have hCε : C * ε < δ := by rw [lt_div_iff₀ hC] at hεC; linarith
    calc ‖X‖ = ‖X.1‖ := rfl
      _ ≤ C * (ε / 2) := h
      _ < δ := by nlinarith
  have himg : GlobalTheory.SUVol.DensOne.chartExp Ψ G hG '' s ⊆ frBall Ψ G x ε := by
    rintro _ ⟨X, hX, rfl⟩ τ a b
    change ‖((mat x τ)⁻¹ * NormedSpace.exp (Matrix.of (X.1 τ)) * mat x τ - 1) a b‖ < ε
    rw [← Matrix.exp_conj' _ _ ((Matrix.isUnit_iff_isUnit_det _).2 (hx τ).isUnit)]
    exact hexp ε _ hε hεδ' (hX τ) a b
  have h2 := hlow s hsm hball
  have h3 : tangentHaar (realSU Ψ G) (lam.map Subtype.val) (GlobalTheory.SUVol.DensOne.chartExp Ψ G hG '' s) ≤
      riemHaar Ψ G x (frBall Ψ G x ε) := by
    rw [hmap]; exact measure_mono himg
  have e : ε / (2 * ((Ψ.card : ℝ) * (r : ℝ) ^ 2)) = ε / 2 / ((Ψ.card : ℝ) * (r : ℝ) ^ 2) := by rw [div_div]
  rw [e, ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_ofNat]
  refine ENNReal.div_le_of_le_mul ?_
  calc _ ≤ lam s := h1
    _ ≤ 2 * tangentHaar (realSU Ψ G) (lam.map Subtype.val) (GlobalTheory.SUVol.DensOne.chartExp Ψ G hG '' s) := h2
    _ ≤ 2 * riemHaar Ψ G x (frBall Ψ G x ε) := by gcongr
    _ = riemHaar Ψ G x (frBall Ψ G x ε) * 2 := mul_comm _ _

end GlobalTheory.CovTop.VolUp.LowBall
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC

attribute [-instance] CategoryTheory.Limits.hasPullbackHorizPaste

theorem qcqsOver_sch {X S : Scheme.{0}} (r : X ⟶ S) [QuasiCompact r] [QuasiSeparated r] : QcqsOver (sch.map r) :=
  fun _ => ⟨X, r, Iso.refl _, inferInstance, inferInstance, by simp [sch]⟩

theorem isPullback_sch_comp {Y X S T : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) (s : T ⟶ S) :
    IsPullback (sch.map (pullback.fst (f ≫ p) s)) (sch.map (pullback.snd (f ≫ p) s)) (sch.map f ≫ sch.map p) (sch.map s) := by
  have h := (IsPullback.of_hasPullback (f ≫ p) s).map sch
  rw [Functor.map_comp] at h
  exact h

set_option synthInstance.maxHeartbeats 200000

theorem bcMap_app_fst {E E' : Spc} {S : Scheme.{0}} (α : E ⟶ E') (p : E' ⟶ sch.obj S) (U : Over S) :
    (bcMap α p).app U ≫ (pullback.fst p (sch.map U.hom) : (bc p).obj U ⟶ E') = pullback.fst (α ≫ p) (sch.map U.hom) ≫ α :=
  pullback.lift_fst _ _ _

theorem bcMap_app_snd {E E' : Spc} {S : Scheme.{0}} (α : E ⟶ E') (p : E' ⟶ sch.obj S) (U : Over S) :
    (bcMap α p).app U ≫ (pullback.snd p (sch.map U.hom) : (bc p).obj U ⟶ _) = pullback.snd (α ≫ p) (sch.map U.hom) :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

theorem bcMap_sch_square {Y X S T : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) (s : T ⟶ S) :
    (isPullback_sch_comp f p s).isoPullback.hom ≫ (bcMap (sch.map f) (sch.map p)).app (Over.mk s) =
      sch.map (pullback.map (f ≫ p) s p s f (𝟙 _) (𝟙 _) (by simp) (by simp)) ≫
        ((IsPullback.of_hasPullback p s).map sch).isoPullback.hom := by
  let P1 := isPullback_sch_comp f p s
  let P2 := (IsPullback.of_hasPullback p s).map sch
  apply pullback.hom_ext
  · have l : (P1.isoPullback.hom ≫ (bcMap (sch.map f) (sch.map p)).app (Over.mk s)) ≫ pullback.fst (sch.map p) (sch.map s) =
        sch.map (pullback.fst (f ≫ p) s) ≫ sch.map f := by
      refine (Category.assoc _ _ _).trans ?_
      erw [bcMap_app_fst]
      rw [← Category.assoc]
      exact congrArg (· ≫ sch.map f) P1.isoPullback_hom_fst
    have r : (sch.map (pullback.map (f ≫ p) s p s f (𝟙 _) (𝟙 _) (by simp) (by simp)) ≫ P2.isoPullback.hom) ≫
        pullback.fst (sch.map p) (sch.map s) = sch.map (pullback.fst (f ≫ p) s) ≫ sch.map f := by
      rw [Category.assoc, IsPullback.isoPullback_hom_fst, ← Functor.map_comp, ← Functor.map_comp, pullback.lift_fst]
    exact l.trans r.symm
  · have l : (P1.isoPullback.hom ≫ (bcMap (sch.map f) (sch.map p)).app (Over.mk s)) ≫ pullback.snd (sch.map p) (sch.map s) =
        sch.map (pullback.snd (f ≫ p) s) := by
      refine (Category.assoc _ _ _).trans ?_
      erw [bcMap_app_snd]
      exact P1.isoPullback_hom_snd
    have r : (sch.map (pullback.map (f ≫ p) s p s f (𝟙 _) (𝟙 _) (by simp) (by simp)) ≫ P2.isoPullback.hom) ≫
        pullback.snd (sch.map p) (sch.map s) = sch.map (pullback.snd (f ≫ p) s) := by
      rw [Category.assoc, IsPullback.isoPullback_hom_snd, ← Functor.map_comp]
      exact congrArg sch.map ((pullback.lift_snd _ _ _).trans (Category.comp_id _))
    exact l.trans r.symm

theorem eqv_sch_of_stalks : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (Y X S : Scheme.{0}) (f : Y ⟶ X) (p : X ⟶ S) [QuasiCompact p] [QuasiSeparated p] [QuasiCompact f] [QuasiSeparated f], (∀ (O : Type) [CommRing O] (s : Spec (CommRingCat.of O) ⟶ S), IsStalk O s → Eqv R (sch.map (pullback.map (f ≫ p) s p s f (𝟙 _) (𝟙 _) (by simp) (by simp))) F) → Eqv R (sch.map f) F := by
  intro R _ F hF Y X S f p _ _ _ _ hst
  refine GlobalTheory.T.equiv_of_stalkwise_base_change R F S (sch.obj Y) (sch.obj X) (sch.map f) (sch.map p) hF ?_ (qcqsOver_sch p) ?_
  · rw [← Functor.map_comp]; exact qcqsOver_sch (f ≫ p)
  · intro O _ s hs
    have hb := eqv_basic R F
    have hsq := bcMap_sch_square f p s
    have h1 := hb.1 _ _ (isPullback_sch_comp f p s).isoPullback.hom inferInstance
    have h2 := (hb.2.1 _ _ _ _ _).1 (hst O s hs) (hb.1 _ _ ((IsPullback.of_hasPullback p s).map sch).isoPullback.hom inferInstance)
    rw [← hsq] at h2
    exact (hb.2.1 _ _ _ _ _).2.1 h1 h2

end GlobalTheory.EtC
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieLin

theorem _root_.GlobalTheory.T.kottwitzLieConditionModule_iff_ideal_le_ker : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (B : Type) [CommRing B]
  (βB : R →+* B) (n : ℕ) (M : 𝓞 D.F →+* Matrix (Fin n) (Fin n) B) (T : Type) [CommRing T] (f : B →+* T),
    LieMod (matAct M f) D.ω (f (βB b.ρ)) (fun i => (f.comp βB).comp (b.t i)) ↔ lieIdeal b βB M ≤ RingHom.ker f := by
  first | exact @GlobalTheory.UPel.HT.LieLin.lieMod_matAct_iff_lieIdeal_le_ker | exact GlobalTheory.UPel.HT.LieLin.lieMod_matAct_iff_lieIdeal_le_ker | (intros; apply GlobalTheory.UPel.HT.LieLin.lieMod_matAct_iff_lieIdeal_le_ker <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

namespace GlobalTheory.ThetaTransform

noncomputable def finEmbSnd (F : Type) [Field F] [NumberField F] (N : ℕ) : (Fin N → Af F) →+ VA F N where
  toFun v := (0, fun i => pairA F 0 (v i))
  map_zero' := rfl
  map_add' v w := by
    refine Prod.ext (add_zero _).symm ?_
    funext i
    exact Prod.ext (add_zero _).symm rfl

theorem continuous_finEmbSnd (F : Type) [Field F] [NumberField F] (N : ℕ) : Continuous (finEmbSnd F N) :=
  continuous_const.prodMk (continuous_pi fun i => continuous_const.prodMk (continuous_apply i))

theorem dotProduct_finEmbSnd {F : Type} [Field F] [NumberField F] {N : ℕ} (x : Fin N → AF F) (v : Fin N → Af F) :
    x ⬝ᵥ (finEmbSnd F N v).2 = pairA F 0 (Bd (Af F) (half F N) (fin x) v) := by
  have h : Bd (Af F) (half F N) (fin x) v = ∑ i, fin x i * v i := by
    simp [Bd, half]
  rw [h]
  refine Prod.ext ?_ ?_
  · change fstA F (∑ i, x i * pairA F 0 (v i)) = 0

    rw [map_sum]
    exact Finset.sum_eq_zero fun i _ => by rw [map_mul]; exact mul_zero _
  · change sndA F (∑ i, x i * pairA F 0 (v i)) = _

    rw [map_sum]
    rfl

theorem invV_level_support : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)), Ctx ψ lam ν (half F N) → ∀ 𝓓 : Set (Fin N → AF F), IsAddFundamentalDomain (ratSub F N) 𝓓 (muV N ν) → muV N ν 𝓓 = 1 → ∀ f : VA F N → ℂ, QuasiV ψ f → LevelV ψ f → (∃ U : AddSubgroup (Fin N → AF F), IsOpen (U : Set (Fin N → AF F)) ∧ ∀ u ∈ U, inf u = 0 → ∀ x, invV ψ ν 𝓓 f (x + u) = invV ψ ν 𝓓 f x) ∧ ∃ K : Set (Fin N → Af F), IsCompact K ∧ ∀ x, invV ψ ν 𝓓 f x ≠ 0 → fin x ∈ K := by
  intro F _ _ N _ ψ lam ν hc 𝓓 hD _ f hq hl
  obtain ⟨U, hU, hf⟩ := hl
  have h0 : inf (0 : Fin N → AF F) = 0 := rfl
  refine ⟨⟨U.comap (AddMonoidHom.inl (Fin N → AF F) (Fin N → AF F)),
    hU.preimage (f := fun u : Fin N → AF F => ((u, 0) : VA F N)) (continuous_id.prodMk continuous_const), ?_⟩, ?_⟩
  · intro u hu hi x
    rw [← invV_heisV_fst, hf (u, 0) hu hi h0]
  · refine ⟨_, (GlobalTheory.T.finiteAdeleVector_annihilators_compact_open_basis F N ψ lam ν (half F N) hc).1 (U.comap (finEmbSnd F N))
      (hU.preimage (continuous_finEmbSnd F N)), fun x hx v hv => ?_⟩
    have h1 := invV_heisV_snd hc.2.2.2.1 hD hq (finEmbSnd F N v).2 x
    rw [show ((0 : Fin N → AF F), (finEmbSnd F N v).2) = finEmbSnd F N v from rfl, hf _ hv h0 rfl,
      dotProduct_finEmbSnd] at h1
    exact mul_right_cancel₀ hx (h1.symm.trans (one_mul _).symm)

end GlobalTheory.ThetaTransform
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

theorem _root_.GlobalTheory.T.hasDerivAt_schrodingerLine_pureTensor_zero : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ), IsTotallyReal F → IsCharAF F ψ → ∀ M : ℝ →+ VA F N, IsRealLine M → ∀ (f : SchwartzMap (Fin N → mixedEmbedding.mixedSpace F) ℂ) (g : (Fin N → FiniteAdeleRing (𝓞 F) F) → ℂ), g ∈ GlobalTheory.WeilM.SB (Fin N → FiniteAdeleRing (𝓞 F) F) → ∃ f' : SchwartzMap (Fin N → mixedEmbedding.mixedSpace F) ℂ, ∀ z : Fin N → AF F, HasDerivAt (fun s : ℝ => GlobalTheory.WeilM.schr ψ (M s) (GlobalTheory.WeilM.pureA F f g) z) (GlobalTheory.WeilM.pureA F f' g z) 0 := by
  first | exact @GlobalTheory.Adopt.hasDerivAt_schrodingerLine_pureTensor_zero | exact GlobalTheory.Adopt.hasDerivAt_schrodingerLine_pureTensor_zero | (intros; apply GlobalTheory.Adopt.hasDerivAt_schrodingerLine_pureTensor_zero <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

theorem _root_.GlobalTheory.T.exists_appellHumbertFrame_of_complexExponential : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (M : LB A.left), M.IsLB → ∀ (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)), IsExp (𝟙 (Sp ℂ)) e → ∃ (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), (∀ z, u.ex z = e z) ∧ GlobalTheory.TorusRM.IsFactorAH u Hm χ := by
  first | exact @GlobalTheory.ExpUnifAH.exists_unif_isFactorAH_of_isExp | exact GlobalTheory.ExpUnifAH.exists_unif_isFactorAH_of_isExp | (intros; apply GlobalTheory.ExpUnifAH.exists_unif_isFactorAH_of_isExp <;> assumption)
end
