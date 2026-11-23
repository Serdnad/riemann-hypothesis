module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle781
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle925
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle114
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle203
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1345
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle201
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle008
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle204
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle170
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle178
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle205
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle196
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle014
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCoverKFinitePairingOfRealIntertwiner
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle206
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModelsAreCoverSeries
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
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
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle013
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

noncomputable section

open Classical MeasureTheory MvPolynomial

namespace GlobalTheory.MinorFrame.AvgCore

variable {ι : Type} [Fintype ι] {a d : ℕ}

theorem continuous_colSub_mul (Λ : Pol ι d a →ₗ[ℂ] ℂ) (P : Pol ι d a) : ∀ Q : Pol ι d a,
    Continuous (fun G : ι → Fin a → Fin a → ℂ => Λ (colSub (fun τ => Matrix.of (G τ)) P * Q)) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    intro Q
    have h : ∀ G : ι → Fin a → Fin a → ℂ, colSub (d := d) (fun τ => Matrix.of (G τ)) (C c) = C c := by
      intro G; simp [colSub, MvPolynomial.algebraMap_eq]
    simp only [h]
    exact continuous_const
  | add p q hp hq =>
    intro Q
    simp only [map_add (f := _), add_mul]
    exact (hp Q).add (hq Q)
  | mul_X p y hp =>
    intro Q
    have h : ∀ G : ι → Fin a → Fin a → ℂ, Λ (colSub (fun τ => Matrix.of (G τ)) (p * X y) * Q) =
        ∑ j' : Fin a, G y.1 j' y.2.2 * Λ (colSub (fun τ => Matrix.of (G τ)) p * (X (y.1, y.2.1, j') * Q)) := by
      intro G
      have hX : colSub (d := d) (fun τ => Matrix.of (G τ)) (X y) =
          ∑ j' : Fin a, C (G y.1 j' y.2.2) * X (y.1, y.2.1, j') := by
        simp [colSub]

      rw [map_mul (colSub (fun τ => Matrix.of (G τ))) p (X y), hX, Finset.mul_sum, Finset.sum_mul, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show colSub (fun τ => Matrix.of (G τ)) p * (C (G y.1 j y.2.2) * X (y.1, y.2.1, j)) * Q =
          C (G y.1 j y.2.2) * (colSub (fun τ => Matrix.of (G τ)) p * (X (y.1, y.2.1, j) * Q)) by ring,
        ← smul_eq_C_mul, map_smul, smul_eq_mul]
    simp only [h]
    refine continuous_finsetSum _ fun j _ => ?_
    exact Continuous.mul (by fun_prop) (hp _)

theorem norm_det_unitary (u : Matrix.unitaryGroup (Fin a) ℂ) : ‖(u : Matrix (Fin a) (Fin a) ℂ).det‖ = 1 := by
  exact CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary u.2)

theorem integrable_avg {K : Type} [Group K] [MeasurableSpace K] (ν : Measure K) [IsFiniteMeasure ν]
    (ρ : K →* (ι → Matrix.unitaryGroup (Fin a) ℂ))
    (hmeas : ∀ τ i j, Measurable fun g => (ρ g τ : Matrix (Fin a) (Fin a) ℂ) i j) (z : ι → ℤ)
    (Λ : Pol ι d a →ₗ[ℂ] ℂ) (P : Pol ι d a) :
    Integrable (fun g => (∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (z τ)) *
      Λ (colSub (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) P)) ν := by
  let F : (ι → Fin a → Fin a → ℂ) → ℂ := fun G => Λ (colSub (fun τ => Matrix.of (G τ)) P)
  have hF : Continuous F := by simpa [F] using continuous_colSub_mul Λ P 1
  let e : K → (ι → Fin a → Fin a → ℂ) := fun g τ i j => (ρ g τ : Matrix (Fin a) (Fin a) ℂ) i j
  have he : Measurable e := Measurable.of_eval fun τ => Measurable.of_eval fun i =>
    Measurable.of_eval fun j => hmeas τ i j
  have hFe : ∀ g, Λ (colSub (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) P) = F (e g) := fun g => rfl
  have hdetc : ∀ τ, Continuous fun G : ι → Fin a → Fin a → ℂ => (Matrix.of (G τ)).det :=
    fun τ => Continuous.matrix_det (continuous_apply τ)
  have hdete : ∀ g τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det = (Matrix.of (e g τ)).det := fun g τ => rfl
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ι → Fin a → Fin a → ℂ) 1).exists_bound_of_continuousOn hF.continuousOn
  have hball : ∀ g, e g ∈ Metric.closedBall (0 : ι → Fin a → Fin a → ℂ) 1 := by
    intro g
    rw [mem_closedBall_zero_iff]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun τ => (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i =>
      (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => entry_norm_bound_of_unitary (ρ g τ).2 i j
  refine Integrable.of_bound ?_ C (Filter.Eventually.of_forall fun g => ?_)
  · refine Measurable.aestronglyMeasurable ?_
    simp only [hFe, hdete]
    refine Measurable.mul ?_ (hF.measurable.comp he)
    refine Finset.measurable_prod _ fun τ _ => ?_
    exact Measurable.pow_const ((hdetc τ).measurable.comp he) _
  · rw [norm_mul, norm_prod]
    simp only [norm_zpow, norm_det_unitary, one_zpow, Finset.prod_const_one, one_mul, hFe]
    exact hC _ (hball g)

theorem average_monomial_eq_sum_prodMinors : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (m : ι → ℤ), ∃ n : ι → ℕ,
  ∀ {K : Type} [Group K] [MeasurableSpace K] (ν : Measure K), IsProbabilityMeasure ν → ν.IsMulLeftInvariant →
  (∀ g0 : K, AEMeasurable (g0 * ·) ν) →
  ∀ (ρ : K →* (ι → Matrix.unitaryGroup (Fin a) ℂ)), (∀ τ i j, Measurable fun g => (ρ g τ : Matrix (Fin a) (Fin a) ℂ) i j) → Function.Surjective ρ →
  ∀ (Λ : GlobalTheory.MinorFrame.Pol ι d a →ₗ[ℂ] ℂ) (k : GlobalTheory.MinorFrame.Var ι d a →₀ ℕ),
  ∃ (M : ℕ) (r : Fin M → ℂ) (U : Fin M → GlobalTheory.MinorFrame.Tup ι a d n), (∀ p, IsAlgebraic ℚ (r p)) ∧
    ∫ g, (∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (m τ)) *
      Λ (GlobalTheory.MinorFrame.colSub (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) (MvPolynomial.monomial k 1)) ∂ν =
    ∑ p, r p * Λ (GlobalTheory.MinorFrame.prodMinors (U p)) := by
  intro ι _ a d m
  refine ⟨fun τ => (-m τ).toNat, ?_⟩
  intro K _ _ ν hP hInv hleft ρ hmeas hsurj Λ k
  haveI := hP
  by_cases hpos : 0 < a ∧ ∃ τ₀, 0 < m τ₀
  · obtain ⟨ha, τ₀, hτ₀⟩ := hpos
    refine ⟨0, Fin.elim0, Fin.elim0, fun p => p.elim0, ?_⟩
    rw [GlobalTheory.T.integral_detCharacter_fockColumnSubstitution_eq_zero a d m τ₀ ha hτ₀ ν hP hInv hleft ρ hmeas hsurj Λ _]
    simp
  obtain ⟨M, r, U, hR⟩ := GlobalTheory.T.exists_rational_fock_projection_maximal_minors (ι := ι) a d (fun τ => (-m τ).toNat) k
  refine ⟨M, fun p => ((r p : ℚ) : ℂ), U, fun p => isAlgebraic_ratCast ℚ (r p), ?_⟩
  set R : Pol ι d a := MvPolynomial.monomial k 1 - ∑ p, ((r p : ℚ) : ℂ) • prodMinors (U p) with hRdef
  have hperp : ∀ I ∈ inv a d (fun τ => (-m τ).toNat), Formalism.L2.DIV.fockS I R = 0 := by
    intro I hI
    have hspan := GlobalTheory.T.fockDetCharInvariants_le_span_prodMaximalMinors a d (fun τ => (-m τ).toNat) hI
    clear hI
    show Formalism.L2.DIV.fockL I R = 0
    induction hspan using Submodule.span_induction with
    | mem x hx => obtain ⟨T, rfl⟩ := hx; exact hR T
    | zero => rw [map_zero, LinearMap.zero_apply]
    | add x y _ _ hx hy => rw [map_add (f := _), LinearMap.add_apply, hx, hy, add_zero]
    | smul c x _ hx => rw [map_smulₛₗ, LinearMap.smul_apply, hx, smul_zero]
  have h0 := GlobalTheory.T.unitaryAverage_kills_fock_complement_relInvariants a d (fun τ => (-m τ).toNat) ν hP hInv hleft ρ hmeas hsurj Λ R hperp
  have hdet0 : ∀ g τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ≠ 0 := fun g τ => by
    rw [← norm_ne_zero_iff, norm_det_unitary]; exact one_ne_zero
  have hD : ∀ g, (∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (m τ)) =
      ∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (-(((-m τ).toNat : ℕ) : ℤ)) := by
    intro g
    refine Finset.prod_congr rfl fun τ _ => ?_
    rcases Nat.eq_zero_or_pos a with ha | ha
    · subst ha
      simp [Matrix.det_fin_zero]
    · have hm : m τ ≤ 0 := by
        by_contra h
        exact hpos ⟨ha, τ, by omega⟩
      rw [Int.toNat_of_nonneg (by omega), neg_neg]
  have hinv : ∀ g, (∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (-(((-m τ).toNat : ℕ) : ℤ))) *
      detChar (fun τ => (-m τ).toNat) (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) = 1 := by
    intro g
    unfold detChar
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun τ _ => ?_
    rw [zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ (hdet0 g τ))]
  have hmono : MvPolynomial.monomial k 1 = ∑ p, ((r p : ℚ) : ℂ) • prodMinors (U p) + R := by
    rw [hRdef]; abel
  have hpoint : ∀ g, (∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (m τ)) *
      Λ (colSub (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) (MvPolynomial.monomial k 1)) =
      ∑ p, ((r p : ℚ) : ℂ) * Λ (prodMinors (U p)) +
        (∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (-(((-m τ).toNat : ℕ) : ℤ))) *
          Λ (colSub (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) R) := by
    intro g

    rw [hD g, hmono, map_add (f := _), map_sum, map_add (f := _), map_sum, mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_smul, colSub_prodMinors, smul_smul, map_smul, smul_eq_mul]
    rw [show (∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (-(((-m τ).toNat : ℕ) : ℤ))) *
        ((((r p : ℚ) : ℂ) * detChar (fun τ => (-m τ).toNat) (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ))) *
          Λ (prodMinors (U p))) =
        ((∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (-(((-m τ).toNat : ℕ) : ℤ))) *
          detChar (fun τ => (-m τ).toNat) (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ))) *
          (((r p : ℚ) : ℂ) * Λ (prodMinors (U p))) by ring, hinv g, one_mul]
  refine (integral_congr_ae (Filter.Eventually.of_forall hpoint)).trans ?_
  rw [integral_add (integrable_const _) (integrable_avg ν ρ hmeas _ Λ R), integral_const, h0]
  simp

end GlobalTheory.MinorFrame.AvgCore
end
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.ArchUniq MeasureTheory
open scoped SchwartzMap Classical

noncomputable section

namespace GlobalTheory.ArchFam

open scoped Matrix

variable {F : Type} [Field F] [NumberField F]

theorem at_liftV {κ : Type} (y : κ → mixedEmbedding.mixedSpace F) : At (evI F) (liftV y) := by
  intro u hu
  have h : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.1 hu
  funext i
  refine Prod.ext ?_ ?_
  · change u.1 * _ = 0
    rw [h, zero_mul]
  · change u.2 * 0 = 0
    exact mul_zero _

theorem rho_tens (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) {W' : Type} [AddCommGroup W'] [Module (AF F) W']
    {Bf : W' → W' → AF F} {κ : Type} [Fintype κ] (dc : Darboux Bf κ) (w : W') (hw : At (evI F) w)
    (φ : (κ → mixedEmbedding.mixedSpace F) → ℂ) (r : (κ → AF F) → ℂ)
    (hr : ∀ x z, At (evI F) z → r (x + z) = r x) :
    dc.rho ψ w (tens (evI F) φ r) =
      tens (evI F) (schrF (trP F κ) (locV (dc.e w).1, locV (dc.e w).2) φ) r := by
  have hab : ∀ u : AF F, evI F u = 0 → u • dc.e w = 0 := fun u hu => by
    rw [← map_smul, hw u hu, map_zero]
  have ha : At (evI F) (dc.e w).1 := fun u hu => congrArg Prod.fst (hab u hu)
  have hb : At (evI F) (dc.e w).2 := fun u hu => congrArg Prod.snd (hab u hu)
  funext x
  have ht : At (evI F) (x ⬝ᵥ (dc.e w).2 + ⅟(2 : AF F) * (dc.e w).1 ⬝ᵥ (dc.e w).2) := fun u hu => by
    have h : ∀ y : κ → AF F, u * (y ⬝ᵥ (dc.e w).2) = 0 := fun y => by
      rw [← smul_eq_mul, ← dotProduct_smul, hb u hu, dotProduct_zero]
    rw [smul_eq_mul, mul_add, h, mul_left_comm, h, mul_zero, add_zero]
  have hloc : (fun i => evI F ((x + (dc.e w).1) i)) = locV x + locV (dc.e w).1 := by
    funext i
    simp only [Pi.add_apply, locV, evI_eq_evIHom, map_add (f := _)]
  simp only [Darboux.rho, schr, tens]
  rw [hψ.2.2 _ ht, trace_evI_heis, hr x _ ha, hloc, schrF]
  exact (mul_assoc _ _ _).symm

theorem tens_inj {κ : Type} (r : (κ → AF F) → ℂ) (hr : ∀ x z, At (evI F) z → r (x + z) = r x)
    (x₀ : κ → AF F) (h0 : r x₀ ≠ 0) (φ₁ φ₂ : (κ → mixedEmbedding.mixedSpace F) → ℂ)
    (h : tens (evI F) φ₁ r = tens (evI F) φ₂ r) : φ₁ = φ₂ := by
  funext y
  have hz : At (evI F) (liftV (y - locV x₀)) := at_liftV _
  have hx := congrFun h (x₀ + liftV (y - locV x₀))
  simp only [tens] at hx
  have hl : (fun i => evI F ((x₀ + liftV (y - locV x₀)) i)) = y := by
    change locV (x₀ + liftV (y - locV x₀)) = y
    rw [Coord.loc_add, Coord.loc_lift]
    abel
  rw [hl, hr _ _ hz] at hx
  exact mul_right_cancel₀ h0 hx

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

def wv (M : Model σ X W)
    (v : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) :
    Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
  M.co.e.symm (liftV v.1, liftV v.2)

theorem at_wv (M : Model σ X W)
    (v : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) :
    At (evI F) (wv M v) := by
  intro u hu
  rw [wv, ← map_smul, Prod.smul_mk, at_liftV v.1 u hu, at_liftV v.2 u hu, Prod.mk_zero_zero, map_zero]

theorem at_mul {w : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))} (hw : At (evI F) w) (m : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :
    At (evI F) (w * m) := by
  intro u hu
  rw [← Matrix.smul_mul, hw u hu, Matrix.zero_mul]

def amap (M : Model σ X W) (m : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :
    ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
      ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) where
  toFun v := Coord.coordI M (wv M v * m)
  map_add' v v' := by
    simp only [wv, Prod.fst_add, Prod.snd_add, Coord.lift_add, ← Prod.mk_add_mk, map_add (f := _), Matrix.add_mul,
      Coord.coordI_add]
  map_smul' c v := by
    simp only [wv, Prod.smul_fst, Prod.smul_snd, Coord.lift_smul, ← Prod.smul_mk, map_smul, Matrix.smul_mul,
      Coord.coordI_smul, RingHom.id_apply]

end GlobalTheory.ArchFam

namespace GlobalTheory.ArchFam

open scoped Matrix


open GlobalTheory.ArchUniq.Coord in
theorem schr_equiv : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    IsStd ψ → M.IsWeil ψ χX χW om → ∀ γ ∈ Lines σ W, ∀ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
    (∀ t (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) ⇑f ⇑(T t f)) →
    ∃ A : ℝ → ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
        ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)),
      (∀ v, Continuous fun t => A t v) ∧
      ∀ t v (f f₁ : SInf F (Fin n × Fin d)), ⇑f₁ = schrF (trP F (Fin n × Fin d)) v ⇑f →
        ⇑(T t f₁) = schrF (trP F (Fin n × Fin d)) (A t v) ⇑(T t f) := by
  intro F E _ _ _ _ _ σ n d X W M ψ χX χW om hψ hW γ hγ T hT
  refine ⟨fun t => amap M (mat (γ (Multiplicative.ofAdd t)))ᵀ, fun v => ?_, fun t v f f₁ hf => ?_⟩
  · haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
    haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
    haveI : IsModuleTopology (AF F) (Matrix (Fin n) (Fin d) (AE F E)) :=
      inferInstanceAs (IsModuleTopology (AF F) (Fin n → Fin d → AE F E))
    have hm : Continuous fun t : ℝ => (mat (γ (Multiplicative.ofAdd t)))ᵀ :=
      ((Units.continuous_val.comp continuous_subtype_val).comp (hγ.1.comp continuous_ofAdd)).matrix_transpose
    have he : Continuous M.co.e := IsModuleTopology.continuous_of_linearMap M.co.e.toLinearMap
    have hev : Continuous (evI F) := by
      change Continuous fun a : AF F => InfiniteAdeleRing.ringEquiv_mixedSpace F a.1
      refine Continuous.comp ?_ continuous_fst
      change Continuous fun x : InfiniteAdeleRing F =>
        ((fun (v : {w : InfinitePlace F // w.IsReal}) => InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
         (fun (v : {w : InfinitePlace F // w.IsComplex}) => InfinitePlace.Completion.extensionEmbedding v.1 (x v)))
      refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
      · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
      · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)
    have hl : Continuous (locV : (Fin n × Fin d → AF F) → _) := continuous_pi fun i => hev.comp (continuous_apply i)
    show Continuous fun t => (locV (M.co.e (wv M v * (mat (γ (Multiplicative.ofAdd t)))ᵀ)).1,
      locV (M.co.e (wv M v * (mat (γ (Multiplicative.ofAdd t)))ᵀ)).2)
    exact ((hl.comp continuous_fst).prodMk (hl.comp continuous_snd)).comp (he.comp (continuous_const.matrix_mul hm))
  · obtain ⟨r₀, hr₀, hinj⟩ := GlobalTheory.T.exists_admissible_finiteFactor_archimedeanSchwartz (F := F) (Fin n × Fin d)
    have hrr := (hr₀ 0).1
    by_cases hz : ∀ x, r₀ x = 0
    · have h0 : ∀ g : SInf F (Fin n × Fin d), g = 0 := fun g => hinj g 0 (by funext x; simp [tens, hz])
      rw [h0 (T t f₁), h0 (T t f)]
      funext y
      simp [schrF]
    simp only [not_forall] at hz
    obtain ⟨x₀, hx₀⟩ := hz
    have hs := hW.isUSplitting
    have hc : (locV (M.co.e (wv M v)).1, locV (M.co.e (wv M v)).2) = v := coordI_lift M v
    have e1 : tens (evI F) ⇑f₁ r₀ = M.co.rho ψ (wv M v) (tens (evI F) ⇑f r₀) := by
      rw [rho_tens ψ hψ M.co _ (at_wv M v) _ _ hrr, hc, ← hf]
    have e2 : om (1, γ (Multiplicative.ofAdd t)) (M.co.rho ψ (wv M v) (tens (evI F) ⇑f r₀)) =
        M.co.rho ψ (wv M v * (mat (γ (Multiplicative.ofAdd t)))ᵀ)
          (om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) ⇑f r₀)) := by
      rw [hs.impl (1, γ (Multiplicative.ofAdd t)) (wv M v) _ (hr₀ f).2]
      congr 2
      simp only [actAB, mat, OneMemClass.coe_one, Units.val_one, Matrix.one_mul]
    have e3 := hT t f r₀ (hr₀ f)
    have e4 := hT t f₁ r₀ (hr₀ f₁)
    apply tens_inj r₀ hrr x₀ hx₀
    rw [← e4, e1, e2, e3, rho_tens ψ hψ M.co _ (at_mul (at_wv M v) _) _ _ hrr]
    rfl

end GlobalTheory.ArchFam
end
end

section

open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

theorem _root_.GlobalTheory.T.heisenbergQuotientOpSum_vacuum_commensurable_selfDualLattice : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ Λ : Submodule R X, SelfDual γ Λ → ∀ s : M, s ≠ 0 → Fixes W Λ s → Submodule.span ℂ (Set.range fun x => W x s) = ⊤ → ∀ Λ' : Submodule R X, SelfDual γ Λ' → idx Λ Λ' ≠ 0 → (sumOp W Λ Λ' s ≠ 0 ∧ Fixes W Λ' (sumOp W Λ Λ' s) ∧ Submodule.span ℂ (Set.range fun x => W x (sumOp W Λ Λ' s)) = ⊤) ∧ ∀ e : M →ₗ[ℂ] ℂ, e s = 1 → (∀ a ∈ Λ, ∀ v, e (W a v) = e v) → ∀ v, Fixes W Λ' v → v = e v • sumOp W Λ Λ' s := by
  first | exact @GlobalTheory.SphTheta.sumOp_vacuum_lift | exact GlobalTheory.SphTheta.sumOp_vacuum_lift | (intros; apply GlobalTheory.SphTheta.sumOp_vacuum_lift <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.mem_closedSubgroup_of_localStabilizerPairs : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (H : Subgroup (GA D S × GA D T)), IsClosed (H : Set (GA D S × GA D T)) → (∀ v ε, IsPlaceIdem D v ε → ∀ g h, Stab S βS g → Stab T βT h → SuppPl ε S g → SuppPl ε T h → (g, h) ∈ H) → ∀ g h, Stab S βS g → Stab T βT h → (g, h) ∈ H := by
  first | exact @GlobalTheory.StabDense.mem_of_local | exact GlobalTheory.StabDense.mem_of_local | (intros; apply GlobalTheory.StabDense.mem_of_local <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.gluing_law_holds : ∀ (D : D7) (a b : ℕ), GlueLaw D a b := by
  first | exact @GlobalTheory.Chain.RealIt.GlueProof.glueLaw | exact GlobalTheory.Chain.RealIt.GlueProof.glueLaw | (intros; apply GlobalTheory.Chain.RealIt.GlueProof.glueLaw <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt GlobalTheory.Chain.RealLine
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_cover_kFinite_pairing_of_realIntertwiner : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (τ : D.what₂.Tau) (p q r s : ℕ) (T₁ : GrpData p q) (T₂ : GrpData r s) (R₁ : DSRep T₁) (R₂ : DSRep T₂) (e : Ix p q ≃ Fin V.rank) (e' : Ix r s ≃ Fin W.rank) (m m' : ℤ) (aS aT : ℚ) (U : M.H τ ≃ₗᵢ[ℂ] R₁.U.H) (U' : M'.H τ ≃ₗᵢ⋆[ℂ] R₂.U.H) (κ : LPol W.rank V.rank ≃ₗ[ℂ] Pol p q r s) (A : LPol W.rank V.rank →ₗ[ℂ] M'.sm τ →ₗ[ℂ] M.H τ), (m : ℚ) = 2 * aT → (m' : ℚ) = 2 * aS → GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.Matches R₁ M τ (GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.barMat e) m U → GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.Matches R₂ M' τ (GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.plainMat e') m' U' → IsPolyIso (M.ε τ) (M'.ε τ) e e' κ → LocW M M' τ aS aT A → ∃ B : Pol p q r s →ₗ[ℂ] R₂.HK.V →ₛₗ[starRingEnd ℂ] R₁.HK.V, CoverW R₁ R₂ B ∧ ∀ (P : LPol W.rank V.rank) (x : R₂.HK.V) (y : M'.sm τ), U' (y : M'.H τ) = R₂.ι x → R₁.ι (B (κ P) x) = U (A P y) := by
  first | exact @GlobalTheory.Chain.RealLine.CoverFromLocal.exists_coverW | exact GlobalTheory.Chain.RealLine.CoverFromLocal.exists_coverW | (intros; apply GlobalTheory.Chain.RealLine.CoverFromLocal.exists_coverW <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt GlobalTheory.Chain.RealLine
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.covariant_pairing_unique_up_to_scalar : ∀ (X : ProvA) (p q r s : ℕ) (lam : Ix p q → ℚ) (lam' : Ix r s → ℚ), Formalism.MainNotions.SchurIrreducible.AdmGK (X.ds p q lam).HK → Formalism.MainNotions.SchurIrreducible.ARiiiLine X lam lam' → ∃ B₀ : Pol p q r s → (X.ds r s lam').HK.V → (X.ds p q lam).HK.V, ∀ B : Pol p q r s →ₗ[ℂ] (X.ds r s lam').HK.V →ₛₗ[starRingEnd ℂ] (X.ds p q lam).HK.V, CoverW (X.ds p q lam) (X.ds r s lam') B → ∃ c : ℂ, ∀ P y, B P y = c • B₀ P y := by
  first | exact @GlobalTheory.PairingLine.pairing_line | exact GlobalTheory.PairingLine.pairing_line | (intros; apply GlobalTheory.PairingLine.pairing_line <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt GlobalTheory.Chain.RealLine
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.realIntertwinerContraction_values_kFinite : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (τ : D.what₂.Tau) (aS aT : ℚ) (A : PolF D W.rank V.rank →ₗ[ℂ] M'.sm τ →ₗ[ℂ] M.H τ), SemiW M M' τ aS aT A → (∀ φ y, Formalism.MainNotions.S.IsKFin (M.ε τ) (M.σ τ) (A φ y)) ∧ ∀ φ u, ∃ b : M'.H τ, Formalism.MainNotions.S.IsKFin (M'.ε τ) (M'.σ τ) b ∧ ∀ y : M'.sm τ, ⟪u, A φ y⟫_ℂ = ⟪b, (y : M'.H τ)⟫_ℂ := by
  first | exact @GlobalTheory.Chain.RealLineKFin.kfin | exact GlobalTheory.Chain.RealLineKFin.kfin | (intros; apply GlobalTheory.Chain.RealLineKFin.kfin <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.SplitDblGen

theorem tMat_mul_tMat_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (c : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (K K' : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
    K * K' = 1 → (c * c) • (K - 1) = K - 1 →
    GlobalTheory.SplitDblGen.tMat c K * GlobalTheory.SplitDblGen.tMat c K' = 1 := by
  intro F E _ _ _ _ _ d c K K' hKK hc
  have h2 : (half : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) * 2 = 1 := by
    unfold half
    rw [show (2 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) = algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) 2 from (map_ofNat _ 2).symm, ← map_mul, invOf_mul_self, map_one]
  have hP : (c * c) • ((K - 1) * (K' - 1)) = (K - 1) * (K' - 1) := by rw [← smul_mul_assoc, hc]
  have hsum : (K - 1) + (K' - 1) + (K - 1) * (K' - 1) = 0 := by
    rw [sub_mul, mul_sub, mul_sub, hKK]; noncomm_ring
  have hff : ((half * (1 + c)) * (half * (1 + c))) • ((K - 1) * (K' - 1))
      = (half * (1 + c)) • ((K - 1) * (K' - 1)) := by
    rw [show (half * (1 + c)) * (half * (1 + c)) = half * half * (1 + 2 * c) + half * half * (c * c) by ring,
      add_smul, ← smul_smul (half * half) (c * c), hP, ← add_smul]
    congr 1
    linear_combination (half * (1 + c)) * h2
  unfold tMat
  generalize half * (1 + c) = f at hff ⊢
  have e : (1 + f • (K - 1)) * (1 + f • (K' - 1))
      = 1 + f • ((K - 1) + (K' - 1)) + (f * f) • ((K - 1) * (K' - 1)) := by
    rw [add_mul, one_mul, mul_add, mul_one, smul_mul_smul_comm, smul_add]; abel
  rw [e, hff, add_assoc, ← smul_add, hsum, smul_zero, add_zero]

end GlobalTheory.SplitDblGen
end

section

open Formalism.MainNotions.S GlobalTheory.ArchRec

namespace GlobalTheory.ArchRec

theorem isDS_conj_rev : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Mn n → (H →L[ℂ] H)), IsDS ε lam σ → IsDS (fun a => ε a.rev) (fun a => -lam a.rev) (fun g => σ ((g.map (starRingEnd ℂ)).submatrix Fin.rev Fin.rev)) :=
  fun _ _ _ _ _ _ _ hσ => GlobalTheory.CoverModel.isDS_barRev (fun _ => rfl) hσ

end GlobalTheory.ArchRec
end
