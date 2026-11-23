module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.BumpLat
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SchurStep
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle010
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle024
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
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle001

@[expose] public section

section

open scoped Matrix
open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels UpperTheory.TP.BA

open scoped TensorProduct
open PositivityTheory.ThKH.Iwas (at_sg ev_sg mul_sg)

private theorem e0 {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (a : AF F) (x : E) :
    a • inclR (F := F) (AF F) x = a ⊗ₜ[F] x := by
  change (a * 1) ⊗ₜ[F] x = _
  rw [mul_one]

private theorem unit_at {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) {s : 𝓞 F} (hs : s ∉ v.asIdeal) :
    ∃ t : Fv F v, t ∈ v.adicCompletionIntegers F ∧ (s : F) • sg v t = sg v 1 := by
  have hs0 : (s : F) ≠ 0 := fun h => hs (by
    rw [show s = 0 from RingOfIntegers.coe_injective (by simpa using h)]; exact zero_mem _)
  refine ⟨algebraMap F (Fv F v) (s : F)⁻¹, ?_, ?_⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    have h1 : v.valuation F (s : F) = 1 := (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := F) v).2 hs
    have h2 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (s : F)⁻¹
    exact (h2.trans ((map_inv₀ _ _).trans ((congrArg _ h1).trans inv_one))).le
  · rw [← map_smul, Algebra.smul_def, ← map_mul, mul_inv_cancel₀ hs0, map_one]

private theorem key {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (v : Pl (F := F)) {s : F} {t : Fv F v}
    (h : s • sg v t = sg v 1) (x : E) :
    sg v t • inclR (F := F) (AF F) (algebraMap F E s * x) = sg v 1 • inclR (F := F) (AF F) x := by
  rw [e0, e0, ← Algebra.smul_def, ← TensorProduct.smul_tmul, h]

private theorem at_one {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) {M : Type} [AddCommGroup M] [Module (AF F) M] (m : M) :
    At (evFin F v) (sg v 1 • m) := fun u hu => by
  rw [smul_smul, mul_sg, hu, zero_mul, map_zero, zero_smul]

theorem UpperTheory.unitaryLattice_exists_frame :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (X : Spc F E n) (v : Pl (F := F)), X.L.IsFullLattice E → ∃ b c, IsFr X v b c := by
  intro F E _ _ _ _ _ n X v hL
  haveI := hL
  obtain ⟨P, h1, h2⟩ := GlobalTheory.AdelicU.Frames.exists_rational_frame (F := F) X.L v
  have hss : sg v 1 * sg v 1 = sg v 1 := by rw [mul_sg, ev_sg, mul_one]
  have hPQ : incM F P.1 * incM F (P⁻¹).1 = 1 := by
    rw [incM, incM, ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hQP : incM F (P⁻¹).1 * incM F P.1 = 1 := by
    rw [incM, incM, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨sg v 1 • incM F P.1, sg v 1 • incM F (P⁻¹).1, ⟨at_one v _, at_one v _, ?_, ?_, ?_, ?_⟩⟩
  · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hss, hPQ]
  · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hss, hQP]
  · intro j
    obtain ⟨s, hs, hy⟩ := h1 j
    obtain ⟨t, ht, hst⟩ := unit_at v hs
    refine AddSubgroup.subset_closure ⟨sg v t, at_sg t, by rwa [ev_sg], _, hy, funext fun i => ?_⟩
    exact (key v hst (P.1 i j)).symm
  · intro z hz i
    induction hz using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, ha', x, hx, rfl⟩ := hy
      obtain ⟨s, hs, hsx⟩ := h2 x hx
      obtain ⟨t, ht, hst⟩ := unit_at v hs
      obtain ⟨o, ho⟩ := hsx i (Set.mem_univ i)
      refine AddSubgroup.subset_closure ⟨a * sg v t, ?_, ?_, o, ?_⟩
      · exact fun u hu => by rw [smul_eq_mul, mul_comm u, mul_assoc, mul_comm _ u, ← smul_eq_mul u, at_sg t u hu, mul_zero]
      · rw [map_mul, ev_sg]
        exact mul_mem ha' ht
      · have ho' : ((o : 𝓞 E) : E) = algebraMap F E (s : F) * ((P⁻¹).1 *ᵥ x) i := by
          simpa using ho
        rw [ho', mul_smul, key v hst]

        simp only [Matrix.mulVec, dotProduct, map_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul, Matrix.smul_apply, smul_mul_assoc, mul_smul_comm, smul_comm]
        rfl
    | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [Matrix.mulVec_add]; exact add_mem hy hz
    | neg y _ hy => rw [Matrix.mulVec_neg]; exact neg_mem hy
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions UpperTheory.TP

namespace UpperTheory.MatrixCoefficientBound

open scoped Pointwise

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {Γ : Subgroup G} [Countable Γ] {D : Set G}

private theorem sq_shift (hD : IsFundamentalDomain Γ D μ) {f : G → ℝ} (hi : ∀ γ ∈ Γ, ∀ y, f (γ * y) = f y) (g : G) :
    ∫ y in D, f (y * g) ∂μ = ∫ y in D, f y ∂μ :=
  _root_.UpperTheory.Reformulated.B.Qk59.sq_shift hD hi g

private theorem coef_le (hfin : μ D < ⊤) (hD : IsFundamentalDomain Γ D μ) {φ : G → ℂ} (hc : Continuous φ)
    (hi : ∀ γ ∈ Γ, ∀ y, φ (γ * y) = φ y) {C : ℝ} (hC : ∀ y, ‖φ y‖ ≤ C) (g : G) :
    ‖∫ y in D, φ (y * g) * star (φ y) ∂μ‖ ≤ ∫ y in D, ‖φ y‖ ^ 2 ∂μ := by
  have hb : ∀ {ψ : G → ℂ}, Continuous ψ → (∀ y, ‖ψ y‖ ≤ C) → IntegrableOn (fun y => ‖ψ y‖ ^ 2) D μ := fun {ψ} h1 h2 =>
    Measure.integrableOn_of_bounded (M := C ^ 2) hfin.ne (h1.norm.pow 2).aestronglyMeasurable
      (Eventually.of_forall fun y => by
        rw [norm_pow, norm_norm]; exact pow_le_pow_left₀ (norm_nonneg _) (h2 y) 2)
  have hcg : Continuous fun y => φ (y * g) := hc.comp (continuous_mul_const g)
  have i1 := hb hcg fun y => hC _
  have i2 := hb hc hC
  have e := sq_shift (μ := μ) hD (f := fun y => ‖φ y‖ ^ 2) (fun γ hγ y => by simp only [hi γ hγ y]) g
  calc ‖∫ y in D, φ (y * g) * star (φ y) ∂μ‖ ≤ ∫ y in D, ‖φ (y * g) * star (φ y)‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ y in D, (‖φ (y * g)‖ ^ 2 + ‖φ y‖ ^ 2) / 2 ∂μ := by
      refine integral_mono_of_nonneg (Eventually.of_forall fun y => norm_nonneg _) ((i1.add i2).div_const 2) (Eventually.of_forall fun y => ?_)
      simp only [norm_mul, norm_star]
      nlinarith [sq_nonneg (‖φ (y * g)‖ - ‖φ y‖)]
    _ = ∫ y in D, ‖φ y‖ ^ 2 ∂μ := by
      rw [integral_div, integral_add i1 i2, e]
      ring

end UpperTheory.MatrixCoefficientBound

theorem UpperTheory.matrix_coefficient_bounded_by_value_at_one :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W}, Cpt σ X.J → M.μ.IsHaarMeasure → IsFundamentalDomain (ratU σ X.J) M.dom M.μ → ∀ {φ : UA σ X.J → ℂ}, IsFn φ → φ ≠ 0 → ∃ r : ℝ, 0 < r ∧ mc M φ 1 = r ∧ ∀ g, ‖mc M φ g‖ ≤ r := by
  intro F E _ _ _ _ _ σ n d X W M hK hμ hD φ hφ h0
  haveI := hK.cnt
  haveI := hK.right M.μ hμ
  obtain ⟨C, hC⟩ := hK.bdd hφ.1 hφ.2
  have e1 : mc M φ 1 = ((∫ y in M.dom, ‖φ y‖ ^ 2 ∂M.μ : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    simp only [mc, pet, mul_one]
    exact integral_congr_ae (Eventually.of_forall fun y => by simpa using Complex.mul_conj' (φ y))
  have hp : (∫ y in M.dom, ‖φ y‖ ^ 2 ∂M.μ) ≠ 0 := fun h => h0 <| hK.eq_zero hμ hD hφ.1 hφ.2 (by
    have : pet M.μ M.dom φ φ = mc M φ 1 := by simp [mc]
    rw [this, e1, h]; simp)
  refine ⟨_, lt_of_le_of_ne (integral_nonneg fun y => by positivity) hp.symm, e1, fun g => ?_⟩
  exact UpperTheory.MatrixCoefficientBound.coef_le (hK.fin M.μ M.dom hμ hD) hD hφ.1 hφ.2 hC g
end
