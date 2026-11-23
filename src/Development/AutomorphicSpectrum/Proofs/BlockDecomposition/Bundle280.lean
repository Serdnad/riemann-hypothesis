module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle249
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle273
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle226
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle227
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle277
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle261
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle275
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle276
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle212
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle274
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle018
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.FormQuasiInvariantMirabolic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.NeutralLocalFields.Bundle001
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet

@[expose] public section

section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

theorem _root_.GlobalTheory.T.left_convolution_approximation : ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V], Unimod → ∀ φ : Mat n → ℝ, IsTest φ → (∀ y, 0 ≤ φ y) → (∫ y : G n, φ y.val ∂μ = 1) → ∀ (x : Lp V 2 μ) (ε : ℝ), (∀ y : G n, φ y.val ≠ 0 → ‖lT μ V y x - x‖ ≤ ε) → ‖lConv μ V φ x - x‖ ≤ ε := by
  first | exact @GlobalTheory.CompanionTheory.PresSobA.norm_lConv_sub_le | exact GlobalTheory.CompanionTheory.PresSobA.norm_lConv_sub_le | (intros; apply GlobalTheory.CompanionTheory.PresSobA.norm_lConv_sub_le <;> assumption)
end
end

section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

namespace GlobalTheory.CompanionTheory.PresSobA.IntForm

theorem val_mem_GLs {n : ℕ} (y : G n) : y.val ∈ GLs n :=
  ((isUnit_iff_isUnit_det _).1 y.isUnit).ne_zero

theorem Rd_continuousOn {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (X : Mat n) :
    ContinuousOn (Rd X f) (GLs n) :=
  (GlobalTheory.CompanionTheory.SobGL.Smooth.contDiffOn_fderiv_apply' (GlobalTheory.CompanionTheory.SobGL.Smooth.isOpen_GLs' n) hf
    (GlobalTheory.CompanionTheory.SobGL.Smooth.mulRight' X).contDiff.contDiffOn).continuousOn

theorem hasDerivAt_curve {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (X : Mat n) (z : G n) (s : ℝ) :
    HasDerivAt (fun r : ℝ => f (z.val * (expC X r).val)) (Rd X f (z.val * (expC X s).val)) s := by
  have hγ := (GlobalTheory.T.matrix_exp_curve_derivative n X).2 s
  let L : CLof (Mat n) (Mat n) := LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ z.val)
  have h1 : HasDerivAt (fun r : ℝ => z.val * (expC X r).val) (z.val * ((expC X s).val * X)) s :=
    L.hasFDerivAt.comp_hasDerivAt s hγ
  have hw : (z.val * (expC X s).val) ∈ GLs n := val_mem_GLs (z * expC X s)
  have h2 : HasFDerivAt f (fderiv ℝ f (z.val * (expC X s).val)) (z.val * (expC X s).val) :=
    ((hf.contDiffAt ((GlobalTheory.CompanionTheory.SobGL.Smooth.isOpen_GLs' n).mem_nhds hw)).differentiableAt
      (by simp)).hasFDerivAt
  have h3 := h2.comp_hasDerivAt s h1
  have e : z.val * ((expC X s).val * X) = (z.val * (expC X s).val) * X := (Matrix.mul_assoc _ _ _).symm
  rw [e] at h3
  exact h3

theorem continuous_F {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (X : Mat n) :
    Continuous (fun p : ℝ × G n => Rd X f (p.2.val * (expC X p.1).val)) := by
  have hc : Continuous (fun p : ℝ × G n => p.2 * expC X p.1) :=
    continuous_snd.mul ((GlobalTheory.T.matrix_exp_curve_derivative n X).1.comp continuous_fst)
  have hv : Continuous (fun p : ℝ × G n => (p.2 * expC X p.1).val) := Units.continuous_val.comp hc
  exact (Rd_continuousOn hf X).comp_continuous hv (fun p => val_mem_GLs (p.2 * expC X p.1))

section L2

variable {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem rR_cls_ae (hU : Unimod) {g : Mat n → V} (hg : MemLp (fun y : G n => g y.val) 2 μ) (h : G n) :
    rR μ V h (cls μ g) =ᵐ[μ] fun z => g (z.val * h.val) := by
  haveI := (hU n μ).1
  have hm : MeasurePreserving (fun y : G n => y * h) μ μ := measurePreserving_mul_right μ h
  have h1 := hm.quasiMeasurePreserving.ae_eq_comp (coe_cls μ hg)
  filter_upwards [rR_coe μ hU h (cls μ g), h1] with z hz1 hz2
  rw [hz1]
  simpa using hz2

theorem setIntegral_ae (hU : Unimod) {f : Mat n → V} (X : Mat n) (hf : ContDiffOn ℝ ∞ f (GLs n))
    (hg : MemLp (fun y : G n => Rd X f y.val) 2 μ) (a b : ℝ) :
    (⇑(∫ s in Set.Ioc a b, rR μ V (expC X s) (cls μ (Rd X f))) : G n → V) =ᵐ[μ]
      fun z => ∫ s in Set.Ioc a b, Rd X f (z.val * (expC X s).val) := by
  have hc : Continuous (fun s : ℝ => rR μ V (expC X s) (cls μ (Rd X f))) :=
    ((GlobalTheory.T.regular_representation_continuous n μ V hU (cls μ (Rd X f))).1).comp (GlobalTheory.T.matrix_exp_curve_derivative n X).1
  have hint : Integrable (fun s : ℝ => rR μ V (expC X s) (cls μ (Rd X f)))
      (volume.restrict (Set.Ioc a b)) := hc.integrableOn_Ioc
  refine GlobalTheory.T.lp_integral_ae_pointwise ℝ (G n) V (volume.restrict (Set.Ioc a b)) μ _
    (fun s z => Rd X f (z.val * (expC X s).val)) hint ?_ ?_
  · have : Continuous (Function.uncurry fun (s : ℝ) (z : G n) => Rd X f (z.val * (expC X s).val)) :=
      continuous_F hf X
    exact this.aestronglyMeasurable
  · exact ae_of_all _ fun s => rR_cls_ae μ hU hg (expC X s)

end L2

theorem rR_sub_cls_eq_integral : ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V], Unimod → ∀ (f : Mat n → V) (X : Mat n), ContDiffOn ℝ ∞ f (GLs n) → MemLp (fun y : G n => f y.val) 2 μ → MemLp (fun y : G n => Rd X f y.val) 2 μ → ∀ t : ℝ, rR μ V (expC X t) (cls μ f) - cls μ f = ∫ s in (0 : ℝ)..t, rR μ V (expC X s) (cls μ (Rd X f)) := by
  intro n _ _ μ _ V _ _ _ hU f X hf hfm hg t
  apply Lp.ext
  rw [intervalIntegral]
  have hsub1 := Lp.coeFn_sub (rR μ V (expC X t) (cls μ f)) (cls μ f)
  have hsub2 := Lp.coeFn_sub (∫ s in Set.Ioc 0 t, rR μ V (expC X s) (cls μ (Rd X f)))
    (∫ s in Set.Ioc t 0, rR μ V (expC X s) (cls μ (Rd X f)))
  filter_upwards [hsub1, hsub2, rR_cls_ae μ hU hfm (expC X t), coe_cls μ hfm,
    setIntegral_ae μ hU X hf hg 0 t, setIntegral_ae μ hU X hf hg t 0] with z h1 h2 h3 h4 h5 h6
  rw [h1, h2, Pi.sub_apply, Pi.sub_apply, h3, h4, h5, h6]
  have hcont : Continuous (fun s : ℝ => Rd X f (z.val * (expC X s).val)) :=
    (continuous_F hf X).comp (Continuous.prodMk continuous_id continuous_const)
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) (b := t) (f := fun r : ℝ => f (z.val * (expC X r).val))
    (f' := fun s : ℝ => Rd X f (z.val * (expC X s).val))
    (fun s _ => hasDerivAt_curve hf X z s) (hcont.intervalIntegrable _ _)
  rw [intervalIntegral] at key
  rw [key]
  simp [expC_zero]

end GlobalTheory.CompanionTheory.PresSobA.IntForm
end
end

section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt

theorem _root_.GlobalTheory.T.lubin_tate_teichmuller_sequence_compatibility : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)) (z : ℕ → Om l) (f : ℕ), 0 < f →
    ‖(l : ℂ_[l])‖ ≤ ‖oc K π‖ → ‖oc K π‖ < 1 →
    (∀ n, ‖omC (z n)‖ < 1) → (∀ n, 2 ≤ n → ‖oc K π‖ < ‖omC (z n)‖) →
    ∀ (u : ℕ → Tl l), (∀ n, u (n + 1) ^ l ^ f = u n) → (∀ n, ‖sh (u n) - omC (z n)‖ ≤ ‖oc K π‖) →
    ∀ (r₀ : ↥(OL K) →+* Tl l), (∀ c, r₀ c ^ l ^ f = r₀ c) → (∀ c, ‖sh (r₀ c) - oc K c‖ ≤ ‖oc K π‖) →
    (∀ n, u n ≠ 0) → ∀ (g : GQ l) (c : ℕ → ↥(OL K)),
    (∀ n, HasSum (fun k : ℕ => ((c k : ↥K.1) : Om l) * z n ^ k) (g (z n))) → ∀ n D : ℕ,
    u n ^ D ∣ actT g (u n) - ∑ i ∈ Finset.range D, r₀ (c i) * u n ^ i := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.Tilt.GalDiv.galdiv | exact GlobalTheory.CompanionTheory.LTPer.Tilt.GalDiv.galdiv | (intros; apply GlobalTheory.CompanionTheory.LTPer.Tilt.GalDiv.galdiv <;> assumption)
end
end

section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt

theorem _root_.GlobalTheory.T.teichmuller_character_eq_residue_lift : ∀ {l : ℕ} [Fact l.Prime] (q : ℕ), 2 ≤ q → l ∣ q → ∀ (x : Tl l) (y : Om l),
    x ^ q = x → y ^ q = y → sh x = omC y → tch l x = rB l y := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.Tilt.tch_eq_rB_of_sh_eq | exact GlobalTheory.CompanionTheory.LTPer.Tilt.tch_eq_rB_of_sh_eq | (intros; apply GlobalTheory.CompanionTheory.LTPer.Tilt.tch_eq_rB_of_sh_eq <;> assumption)
end
end

section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt

theorem _root_.GlobalTheory.T.teichmuller_residue_congruence : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)) (f : ℕ), 0 < f → qOf π = l ^ f →
    ‖(l : ℂ_[l])‖ ≤ ‖oc K π‖ → ‖oc K π‖ < 1 → π ≠ 0 → ∀ (x : Tl l) (c : ↥(OL K)), x ^ l ^ f = x →
    ‖sh x - oc K c‖ ≤ ‖oc K π‖ → ∃ c' : ↥(OL K), sh x = oc K (c + π * c') := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.Tilt.sh_root_near_integer | exact GlobalTheory.CompanionTheory.LTPer.Tilt.sh_root_near_integer | (intros; apply GlobalTheory.CompanionTheory.LTPer.Tilt.sh_root_near_integer <;> assumption)
end
end

section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt

theorem _root_.GlobalTheory.T.lubin_tate_sequence_norm_bounds : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) (π : ↥(OL K)) (z : ℕ → Om l),
    LTData K χ π z → 2 ≤ qOf π → ‖oc K π‖ < 1 →
    (∀ n, ‖omC (z n)‖ < 1) ∧ ∀ n, 2 ≤ n → ‖oc K π‖ < ‖omC (z n)‖ := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.Tilt.Normz.norm_z_bounds | exact GlobalTheory.CompanionTheory.LTPer.Tilt.Normz.norm_z_bounds | (intros; apply GlobalTheory.CompanionTheory.LTPer.Tilt.Normz.norm_z_bounds <;> assumption)
end
end

section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt

theorem _root_.GlobalTheory.T.teichmuller_compatible_sequence_approximation : ∀ {l : ℕ} [Fact l.Prime] (f : ℕ) (ρ : ℝ), 0 < f → ‖(l : ℂ_[l])‖ ≤ ρ → ρ < 1 → ∀ Z : ℕ → ℂ_[l],
    (∀ n, ‖Z n‖ ≤ 1) → (∀ n, ‖Z (n + 1) ^ l ^ f - Z n‖ ≤ ρ) →
    ∃ u : ℕ → Tl l, (∀ n, u (n + 1) ^ l ^ f = u n) ∧ ∀ n, ‖sh (u n) - Z n‖ ≤ ρ := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.Tilt.exists_tilt_lift_compat | exact GlobalTheory.CompanionTheory.LTPer.Tilt.exists_tilt_lift_compat | (intros; apply GlobalTheory.CompanionTheory.LTPer.Tilt.exists_tilt_lift_compat <;> assumption)
end
end

section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt

theorem _root_.GlobalTheory.T.teichmuller_fixed_point_approximation : ∀ {l : ℕ} [Fact l.Prime] (f : ℕ) (ρ : ℝ), 0 < f → ‖(l : ℂ_[l])‖ ≤ ρ → ρ < 1 → ∀ c : ℂ_[l],
    ‖c‖ ≤ 1 → ‖c ^ l ^ f - c‖ ≤ ρ → ∃ y : Tl l, y ^ l ^ f = y ∧ ‖sh y - c‖ ≤ ρ := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.Tilt.exists_fixed_near | exact GlobalTheory.CompanionTheory.LTPer.Tilt.exists_fixed_near | (intros; apply GlobalTheory.CompanionTheory.LTPer.Tilt.exists_fixed_near <;> assumption)
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

namespace GlobalTheory.CompanionTheory.KunGlue.GlueGen

variable {K : Type} [Field K] {C D : Type 1} [Category.{0} C] [Category.{0} D]

theorem mem_bot (F : C ⥤ ModuleCat.{0} K) (U : ObjectProperty C) (n : ℕ) (z : CH.Cn (U.ι ⋙ F) n) :
    z ∈ relS (U.ι ⋙ F) (fun T => (⊥ : ObjectProperty C) T.obj) n :=
  fun _ hs => False.elim hs

noncomputable def up (F : C ⥤ ModuleCat.{0} K) (U : ObjectProperty C) (n : ℕ) :
    CH.Cn (U.ι ⋙ F) n →ₗ[K] (RC F U (cosieve_bot (C := C))).X n :=
  LinearMap.codRestrict _ LinearMap.id (mem_bot F U n)

def inc (F : C ⥤ ModuleCat.{0} K) (U : ObjectProperty C) :
    Cx.Hom (RC F U (cosieve_bot (C := C))) (CH.cx (U.ι ⋙ F)) (RingHom.id K) :=
  ⟨fun _ => Submodule.subtype _, fun _ _ => rfl⟩

theorem inc_bij (F : C ⥤ ModuleCat.{0} K) (U : ObjectProperty C) (n : ℕ) :
    Function.Bijective ((inc F U).f n) :=
  ⟨Subtype.val_injective, fun z => ⟨⟨z, mem_bot F U n z⟩, rfl⟩⟩

noncomputable def relPr {M : Cx.{1} K} (F : C ⥤ ModuleCat.{0} K) (G : D ⥤ ModuleCat.{0} K) (U : ObjectProperty C)
    (U' : ObjectProperty D) (p : CxPairing M (CH.cx (U.ι ⋙ F)) (CH.cx (U'.ι ⋙ G))) :
    CxPairing M (RC F U (cosieve_bot (C := C))) (RC G U' (cosieve_bot (C := D))) where
  μ {i j n} h := ((p.μ h).compl₂ ((inc F U).f j)).compr₂ (up G U' n)
  leib h x y := Subtype.ext (p.leib h x y.1)

theorem kun_iff (F : ℕ → C ⥤ ModuleCat.{0} K) (E : ℕ → D ⥤ ModuleCat.{0} K) (P : ℕ → Cx.{1} K)
    (U : ObjectProperty C) (U' : ObjectProperty D)
    (p : ∀ {a a' c : ℕ}, a + a' = c → CxPairing (P a) (CH.cx (U.ι ⋙ F a')) (CH.cx (U'.ι ⋙ E c))) :
    KunE (P := P) (Q := fun a => RC (F a) U (cosieve_bot (C := C))) (T := fun c => RC (E c) U' (cosieve_bot (C := D)))
        (fun {a a' c} ha => relPr (F a') (E c) U U' (p ha)) ↔
      KunE (P := P) (Q := fun a => CH.cx (U.ι ⋙ F a)) (T := fun c => CH.cx (U'.ι ⋙ E c)) (fun {a a' c} ha => p ha) :=
  GlobalTheory.T.pairing_iso_of_component_isos _ _ (fun a => Cx.Hom.id (C := P a)) (fun a => inc (F a) U) (fun c => inc (E c) U')
    (fun a n => CrystallineSemistableComparison.P.mapH_bij _ (fun _ => Function.bijective_id) n)
    (fun a n => CrystallineSemistableComparison.P.mapH_bij _ (inc_bij (F a) U) n)
    (fun c n => CrystallineSemistableComparison.P.mapH_bij _ (inc_bij (E c) U') n)
    (fun _ _ _ _ _ _ _ => rfl)

end GlobalTheory.CompanionTheory.KunGlue.GlueGen

open GlobalTheory.CompanionTheory.KunGlue.GlueGen in
theorem GlobalTheory.CompanionTheory.KunGlue.glue_gen : MVBij → CovDesc → ∀ {K : Type} [Field K] {C D : Type 1} [Category.{0} C] [Category.{0} D] (F : ℕ → C ⥤ ModuleCat.{0} K) (E : ℕ → D ⥤ ModuleCat.{0} K) (P : ℕ → Cx.{1} K) (Rel : ObjectProperty C → ObjectProperty D → Prop) (pr : ∀ (U : ObjectProperty C) (U' : ObjectProperty D), Rel U U' → ∀ {a a' c : ℕ}, a + a' = c → CxPairing (P a) (CH.cx (U.ι ⋙ F a')) (CH.cx (U'.ι ⋙ E c))), (∀ {U₁ U₂ : ObjectProperty C} {U₁' U₂' : ObjectProperty D} (r₁ : Rel U₁ U₁') (r₂ : Rel U₂ U₂') (k : U₂ ≤ U₁) (k' : U₂' ≤ U₁') {a a' c : ℕ} (ha : a + a' = c) {i j n : ℕ} (hn : i + j = n) (x : (P a).X i) (y : CH.Cn (U₁.ι ⋙ F a') j), (resU (E c) k').pullC n ((pr U₁ U₁' r₁ ha).μ hn x y) = (pr U₂ U₂' r₂ ha).μ hn x ((resU (F a') k).pullC j y)) → ∀ {ι : Type} [DecidableEq ι] [Fintype ι] (V : ι → ObjectProperty C) (W : ι → ObjectProperty D), (∀ α, Cosieve (V α)) → (∀ α, Cosieve (W α)) → ∀ (hR : ∀ S : Finset ι, Rel (capU V S) (capU W S)), (∀ S : Finset ι, S.Nonempty → KunE (P := P) (Q := fun a => CH.cx ((capU V S).ι ⋙ F a)) (T := fun c => CH.cx ((capU W S).ι ⋙ E c)) (fun {a a' c} ha => pr (capU V S) (capU W S) (hR S) ha)) → KunE (P := P) (Q := fun a => CH.cx ((capU V ∅).ι ⋙ F a)) (T := fun c => CH.cx ((capU W ∅).ι ⋙ E c)) (fun {a a' c} ha => pr (capU V ∅) (capU W ∅) (hR ∅) ha) := by
  intro hmv hcd K _ C D _ _ F E P Rel pr hnat ι _ _ V W cV cW hR hS
  have key := GlobalTheory.T.pairing_restriction_natural hmv (K := K) (ι := ι) P (fun a => covSy (F a) V (cosieve_bot (C := C)))
    (fun c => covSy (E c) W (cosieve_bot (C := D)))
    (fun S {a a' c} ha => relPr (F a') (E c) (capU V S) (capU W S) (pr (capU V S) (capU W S) (hR S) ha))
    (fun {S S'} h {a a' c} ha {i j n} hn x y => Subtype.ext
      (hnat (hR S) (hR S') (fun _ hT => ⟨hT.1, fun α hα => hT.2 α (h hα)⟩)
        (fun _ hT => ⟨hT.1, fun α hα => hT.2 α (h hα)⟩) ha hn x y.1))
    (fun a => hcd K ι C (F a) V ⊥ cosieve_bot cV)
    (fun c => hcd K ι D (E c) W ⊥ cosieve_bot cW)
    (fun S hne => (kun_iff F E P (capU V S) (capU W S) (fun {a a' c} ha => pr (capU V S) (capU W S) (hR S) ha)).2 (hS S hne))
  exact (kun_iff F E P (capU V ∅) (capU W ∅) (fun {a a' c} ha => pr (capU V ∅) (capU W ∅) (hR ∅) ha)).1 key
end

section

set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem DL_int_valued {r : ℕ} (g : (Fin r → ℕ) → ℂ) (hg : ∀ m, ∃ z : ℤ, g m = (z : ℂ))
    (cs : List (Fin r)) : ∀ m, ∃ z : ℤ, DL cs g m = (z : ℂ) := by
  induction cs with
  | nil => exact hg
  | cons c cs ih =>
    intro m
    obtain ⟨z1, h1⟩ := ih (m + Pi.single c 1)
    obtain ⟨z2, h2⟩ := ih m
    refine ⟨z1 - z2, ?_⟩
    show DL cs g (m + Pi.single c 1) - DL cs g m = ((z1 - z2 : ℤ) : ℂ)
    rw [h1, h2]
    push_cast
    ring

theorem coneTerm_neg_nat {ι : Type} [Fintype ι] {r : ℕ} (a : ι → Fin r → ℝ) (b : ι → ℝ) (p : ℕ)
    (m : Fin r → ℕ) :
    coneTerm a b (-(p : ℂ)) m = ((∏ j, (b j + ∑ i, a j i * (m i : ℝ)) ^ p : ℝ) : ℂ) := by
  unfold coneTerm
  rw [Complex.ofReal_prod]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [neg_neg, Complex.cpow_natCast, Complex.ofReal_pow]

theorem tsum_mem_of_denominator {α : Type} (f : α → ℂ) (K l : ℕ) (hl : 0 < l)
    (hf : ∀ m, ∃ x : ℤ, ((l : ℂ) ^ K) * f m = (x : ℂ)) :
    ∃ (q : ℚ) (z : ℤ), ∑' m, f m = (q : ℂ) ∧ (l : ℚ) ^ K * q = z := by
  have hmem : ((l : ℂ) ^ K) * ∑' m, f m ∈ Set.range (Int.cast : ℤ → ℂ) := by
    by_cases hs : Summable f
    · rw [← tsum_mul_left]
      have hs' : Summable (fun m => (l : ℂ) ^ K * f m) := hs.mul_left _
      apply Complex.isClosed_range_intCast.mem_of_tendsto hs'.hasSum
      refine Filter.Eventually.of_forall (fun S => ?_)
      choose x hx using hf
      exact ⟨∑ b ∈ S, x b, by push_cast; exact Finset.sum_congr rfl (fun b _ => (hx b).symm)⟩
    · rw [tsum_eq_zero_of_not_summable hs, mul_zero]
      exact ⟨0, by simp⟩
  obtain ⟨z, hz⟩ := hmem
  have hlC : ((l : ℂ) ^ K) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hl.ne')
  have hlQ : ((l : ℚ) ^ K) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hl.ne')
  refine ⟨(z : ℚ) / (l : ℚ) ^ K, z, ?_, ?_⟩
  · push_cast
    rw [hz]
    exact (mul_div_cancel_left₀ (∑' m, f m) hlC).symm
  · rw [mul_div_assoc']
    exact mul_div_cancel_left₀ _ hlQ

theorem value_neg_nat_mem : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ) (u : (Fin r → ℕ) → ℚ) (cs : List (Fin r)) (p K l : ℕ), 0 < l → (∀ m, ∃ z : ℤ, (l : ℚ) ^ K * u m = z) → (∀ m : Fin r → ℕ, ∃ z : ℤ, ∏ j, (b j + ∑ i, a j i * (m i : ℝ)) ^ p = (z : ℝ)) → ∃ (q : ℚ) (z : ℤ), ∑' m, (u m : ℂ) * DL cs (coneTerm a b (-(p : ℂ))) m = (q : ℂ) ∧ (l : ℚ) ^ K * q = z := by
  intro ι _ r a b u cs p K l hl hu hprod
  apply tsum_mem_of_denominator _ K l hl
  intro m
  obtain ⟨z2, h2⟩ := DL_int_valued (coneTerm a b (-(p : ℂ))) (fun m' => by
      obtain ⟨z, hz⟩ := hprod m'
      exact ⟨z, by rw [coneTerm_neg_nat, hz, Complex.ofReal_intCast]⟩) cs m
  obtain ⟨z1, h1⟩ := hu m
  refine ⟨z1 * z2, ?_⟩
  rw [h2, ← mul_assoc]
  have h1' : ((l : ℂ) ^ K) * (u m : ℂ) = (z1 : ℂ) := by exact_mod_cast h1
  rw [h1']
  push_cast
  ring

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
end
end

section

open PositivityTheory.JacquetShalikaLocal GroundTheory.Automorphic GroundTheory.Automorphic.Spherical

namespace GlobalTheory.CompanionTheory.JSBound

theorem evalAt_esymmL_eq_sum_prod {n : ℕ} (z : Fin n → ℂˣ) (r : ℕ) :
    evalAt z (esymmL n r) =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, ∏ i ∈ S, (z i : ℂ) := by
  unfold esymmL

  rw [map_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  simp only [evalAt, monomial, AddMonoidAlgebra.lift_single, one_smul, pointHom, monomialChar,
    MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, lamS]
  rw [← Fintype.prod_ite_mem S]
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs <;> simp

theorem prod_one_add_mul_eq {n : ℕ} (w : Fin n → ℂ) (t : ℂ) :
    ∏ j, (1 + t * w j) = ∑ r ∈ Finset.range (n + 1),
      t ^ r * ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, ∏ i ∈ S, w i := by
  have h := Finset.prod_add (fun j => t * w j) (fun _ => (1 : ℂ)) (Finset.univ : Finset (Fin n))
  simp only [Finset.prod_const_one, mul_one, Finset.prod_mul_distrib, Finset.prod_const] at h
  rw [show (∏ j, (1 + t * w j)) = ∏ j, (t * w j + 1) from Finset.prod_congr rfl fun _ _ => add_comm _ _, h,
    Finset.sum_powerset, Finset.card_univ, Fintype.card_fin]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun S hS => ?_
  rw [(Finset.mem_powersetCard.1 hS).2]

theorem prod_add_eq {n : ℕ} (z : Fin n → ℂ) (t : ℂ) :
    ∏ j, (t + z j) = ∑ r ∈ Finset.range (n + 1),
      t ^ (n - r) * ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, ∏ i ∈ S, z i := by
  rw [show (∏ j, (t + z j)) = ∏ j, (z j + t) from Finset.prod_congr rfl fun _ _ => add_comm _ _,
    Finset.prod_add, Finset.sum_powerset, Finset.card_univ, Fintype.card_fin]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun S hS => ?_
  rw [Finset.prod_const, ← Finset.compl_eq_univ_sdiff, Finset.card_compl, Fintype.card_fin,
    (Finset.mem_powersetCard.1 hS).2, mul_comm]

theorem mul_prod_one_add_conj_eq {n : ℕ} (z : Fin n → ℂˣ)
    (h : ∀ r ≤ n, starRingEnd ℂ (evalAt z (esymmL n r)) * evalAt z (esymmL n n) =
      evalAt z (esymmL n (n - r))) (t : ℂ) :
    evalAt z (esymmL n n) * ∏ j, (1 + t * starRingEnd ℂ (z j : ℂ)) = ∏ j, (t + (z j : ℂ)) := by
  simp only [evalAt_esymmL_eq_sum_prod] at h ⊢
  rw [prod_one_add_mul_eq, prod_add_eq, Finset.mul_sum]
  conv_rhs => rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hrn : r ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)
  have key := h r hrn

  simp only [map_sum, map_prod] at key
  rw [Nat.add_sub_cancel, Nat.sub_sub_self hrn, ← key]
  ring

theorem symmetric_function_absolute_values : ParameterAbsoluteValues := by
  unfold ParameterAbsoluteValues
  intro n z h i
  have h0 := mul_prod_one_add_conj_eq z h 0
  have h1 := mul_prod_one_add_conj_eq z h (-(z i : ℂ))
  simp only [zero_mul, add_zero, zero_add, Finset.prod_const_one, mul_one] at h0
  have hne : evalAt z (esymmL n n) ≠ 0 := by
    rw [h0]
    exact Finset.prod_ne_zero_iff.2 fun j _ => (z j).ne_zero
  have hz : ∏ j, (-(z i : ℂ) + z j) = 0 := Finset.prod_eq_zero (Finset.mem_univ i) (by ring)
  rw [hz, mul_eq_zero] at h1
  obtain ⟨j, -, hj⟩ := Finset.prod_eq_zero_iff.1 (h1.resolve_left hne)
  refine ⟨j, ?_⟩
  have hc : (z i : ℂ) * starRingEnd ℂ (z j : ℂ) = 1 := by linear_combination -hj
  have hn := congrArg norm hc
  rw [norm_mul, Complex.norm_conj, norm_one] at hn
  rw [mul_comm]
  exact hn

end GlobalTheory.CompanionTheory.JSBound
end
