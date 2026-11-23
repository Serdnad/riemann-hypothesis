module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle249
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle227
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.EtaleComparisonMapOfFacts
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Analysis.Calculus.BumpFunction.Basic

@[expose] public section

section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

namespace GlobalTheory.CompanionTheory.PresSobA

theorem one_mem_GLs (n : ℕ) : (1 : Mat n) ∈ GLs n := by
  simp [GLs]

theorem exists_mollifiers (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n))
    [μ.IsHaarMeasure] :
    ∃ φ : ℕ → Mat n → ℝ, (∀ k, IsTest (φ k)) ∧ (∀ k y, 0 ≤ φ k y) ∧
      (∀ k, ∫ y : G n, φ k y.val ∂μ = 1) ∧
      ∀ N ∈ 𝓝 (1 : G n), ∀ᶠ k in atTop, ∀ y : G n, φ k y.val ≠ 0 → y ∈ N := by
  haveI : ProperSpace (Mat n) := FiniteDimensional.proper ℝ _
  have hemb := GlobalTheory.CompanionTheory.SobGL.HaarDom.isOpenEmbedding_valG n
  obtain ⟨r, hr0, hr⟩ : ∃ r > 0, Metric.closedBall (1 : Mat n) r ⊆ GLs n :=
    Metric.nhds_basis_closedBall.mem_iff.1 (isOpen_GLs.mem_nhds (one_mem_GLs n))
  have hrange : ∀ x ∈ GLs n, x ∈ Set.range (Units.val : G n → Mat n) := by
    intro x hx
    have hu : IsUnit x := (Matrix.isUnit_iff_isUnit_det x).2 (isUnit_iff_ne_zero.2 hx)
    exact ⟨hu.unit, rfl⟩
  let b : ℕ → ContDiffBump (1 : Mat n) := fun k =>
    { rIn := r / (2 * ((k : ℝ) + 1))
      rOut := r / ((k : ℝ) + 1)
      rIn_pos := by positivity
      rIn_lt_rOut := by
        have : (0 : ℝ) < (k : ℝ) + 1 := by positivity
        exact div_lt_div_of_pos_left hr0 this (by linarith) }
  have hbOut : ∀ k, (b k).rOut ≤ r := by
    intro k
    exact div_le_self hr0.le (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
  have hcont : ∀ k, Continuous fun y : G n => b k y.val := fun k =>
    (b k).continuous.comp Units.continuous_val
  have hcomp : ∀ k, HasCompactSupport fun y : G n => b k y.val := by
    intro k
    have hK : IsCompact ((Units.val : G n → Mat n) ⁻¹' Metric.closedBall (1 : Mat n) r) :=
      (hemb.isInducing.isCompact_preimage_iff (fun x hx => hrange x (hr hx))).2
        (isCompact_closedBall _ _)
    refine HasCompactSupport.intro hK ?_
    intro y hy
    have : y.val ∉ Function.support (b k) := by
      rw [(b k).support_eq]
      intro h
      exact hy (Metric.closedBall_subset_closedBall (hbOut k) (Metric.ball_subset_closedBall h))
    simpa using this
  have hpos : ∀ k, 0 < ∫ y : G n, b k y.val ∂μ := by
    intro k
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := (1 : G n)) (hcont k)
      (hcomp k) (fun y => (b k).nonneg) ?_
    simpa using (b k).one_of_mem_closedBall (x := (1 : Mat n)) (by simp [(b k).rIn_pos.le]) |>.symm ▸ one_ne_zero
  refine ⟨fun k x => (∫ y : G n, b k y.val ∂μ)⁻¹ * b k x, ?_, ?_, ?_, ?_⟩
  · intro k
    have hts : tsupport (b k) ⊆ Metric.closedBall (1 : Mat n) r := by
      exact (b k).tsupport_eq.le.trans (Metric.closedBall_subset_closedBall (hbOut k))
    have hsub : tsupport (fun x => (∫ y : G n, b k y.val ∂μ)⁻¹ * b k x) ⊆ tsupport (b k) :=
      closure_mono fun x hx h => hx (by simp [h])
    refine ⟨contDiff_const.mul (b k).contDiff, ((b k).hasCompactSupport).mul_left, ?_⟩
    exact hsub.trans (hts.trans hr)
  · intro k y
    exact mul_nonneg (inv_nonneg.2 (hpos k).le) (b k).nonneg
  · intro k
    simp only []
    rw [integral_const_mul, inv_mul_cancel₀ (hpos k).ne']
  · intro N hN
    have himg : (Units.val : G n → Mat n) '' N ∈ 𝓝 (1 : Mat n) := by
      have := hemb.isOpenMap.image_mem_nhds hN
      simpa using this
    obtain ⟨ε, hε0, hε⟩ := Metric.mem_nhds_iff.1 himg
    obtain ⟨K, hK⟩ := exists_nat_gt (r / ε)
    filter_upwards [eventually_ge_atTop K] with k hk y hy
    have hne : b k y.val ≠ 0 := right_ne_zero_of_mul hy
    have hsupp : y.val ∈ Metric.ball (1 : Mat n) (b k).rOut := by
      rw [← (b k).support_eq]
      exact hne
    have hlt : (b k).rOut < ε := by
      have h1 : r / ε < (k : ℝ) + 1 := by
        have : (K : ℝ) ≤ k := by exact_mod_cast hk
        linarith
      have h2 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      show r / ((k : ℝ) + 1) < ε
      rw [div_lt_iff₀ h2]
      rw [div_lt_iff₀ hε0] at h1
      linarith
    obtain ⟨z, hz, e⟩ := hε (Metric.ball_subset_ball hlt.le hsupp)
    have : z = y := hemb.injective e
    exact this ▸ hz

end GlobalTheory.CompanionTheory.PresSobA
end
end

section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

namespace GlobalTheory.CompanionTheory.PresSobA.MolBounded

open GlobalTheory.CompanionTheory.SobGL.HaarDom

variable {n : ℕ}

theorem kernel_continuous {φ : Mat n → ℝ} (hφ : Continuous φ) (z : Mat n) :
    Continuous fun u : G n => φ (z * (u⁻¹ : G n).val) :=
  hφ.comp (continuous_const.matrix_mul (Units.continuous_val.comp continuous_inv))

theorem kernel_hasCompactSupport {φ : Mat n → ℝ} (hφ : IsTest φ) {z : Mat n} (hz : z ∈ GLs n) :
    HasCompactSupport fun u : G n => φ (z * (u⁻¹ : G n).val) := by
  obtain ⟨-, hK, hKs⟩ := hφ
  have unit_of : ∀ w ∈ GLs n, ∃ y : G n, y.val = w := by
    intro w hw
    have hd : IsUnit w := (Matrix.isUnit_iff_isUnit_det w).2 (isUnit_iff_ne_zero.2 hw)
    obtain ⟨y, hy⟩ := hd
    exact ⟨y, hy⟩
  obtain ⟨zG, rfl⟩ := unit_of z hz
  have hS : IsCompact ((Units.val : G n → Mat n) ⁻¹' tsupport φ) := by
    refine (isOpenEmbedding_valG n).isInducing.isCompact_preimage_iff ?_ |>.2 hK
    intro w hw
    obtain ⟨y, hy⟩ := unit_of w (hKs hw)
    exact ⟨y, hy⟩
  have hI : IsCompact ((fun w : G n => w⁻¹ * zG) '' ((Units.val : G n → Mat n) ⁻¹' tsupport φ)) :=
    hS.image (continuous_inv.mul continuous_const)
  refine HasCompactSupport.intro hI fun u hu => ?_
  by_contra hne
  refine hu ⟨zG * u⁻¹, ?_, by group⟩
  have : (zG * u⁻¹).val ∈ Function.support φ := by
    simpa [Function.mem_support] using hne
  exact subset_tsupport φ this

theorem mol_bounded : ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n))
    [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V],
    Unimod → ∀ φ : Mat n → ℝ, IsTest φ → ∀ z ∈ GLs n,
      ∃ L : Lp V 2 μ →L[ℝ] V, ∀ x : Lp V 2 μ, L x = Mol μ φ (⇑x) z := by
  intro n _ _ μ _ V _ _ _ _ φ hφ z hz
  set g : G n → ℝ := fun u => φ (z * (u⁻¹ : G n).val) with hgdef
  have hgc : Continuous g := kernel_continuous hφ.1.continuous z
  have hg2 : MemLp g 2 μ := hgc.memLp_of_hasCompactSupport (kernel_hasCompactSupport hφ hz)
  have hmem : ∀ x : Lp V 2 μ, MemLp (g • (x : G n → V)) 1 μ := fun x =>
    hg2.smul (Lp.memLp x)
  have hint : ∀ x : Lp V 2 μ, Integrable (fun u => g u • (x : G n → V) u) μ := fun x =>
    memLp_one_iff_integrable.1 (hmem x)
  have hb : ∀ x : Lp V 2 μ,
      ‖∫ u, g u • (x : G n → V) u ∂μ‖ ≤ (eLpNorm g 2 μ).toReal * ‖x‖ := by
    intro x
    have h1 : eLpNorm (g • (x : G n → V)) 1 μ ≤ eLpNorm g 2 μ * eLpNorm x 2 μ :=
      eLpNorm_smul_le_mul_eLpNorm hg2.aestronglyMeasurable (Lp.aestronglyMeasurable x)
    have h2 : ∫ u, ‖g u • (x : G n → V) u‖ ∂μ = (eLpNorm (g • (x : G n → V)) 1 μ).toReal := by
      rw [eLpNorm_one_eq_lintegral_enorm, integral_norm_eq_lintegral_enorm (hint x).1]
      · rfl
      · exact (hmem x).aestronglyMeasurable
    calc ‖∫ u, g u • (x : G n → V) u ∂μ‖ ≤ ∫ u, ‖g u • (x : G n → V) u‖ ∂μ :=
          norm_integral_le_integral_norm _
      _ = (eLpNorm (g • (x : G n → V)) 1 μ).toReal := h2
      _ ≤ (eLpNorm g 2 μ * eLpNorm x 2 μ).toReal :=
          ENNReal.toReal_mono (ENNReal.mul_ne_top hg2.ne (Lp.eLpNorm_ne_top x)) h1
      _ = (eLpNorm g 2 μ).toReal * ‖x‖ := by
          rw [ENNReal.toReal_mul, Lp.norm_def]
  let Lin : Lp V 2 μ →ₗ[ℝ] V :=
    { toFun := fun x => ∫ u, g u • (x : G n → V) u ∂μ
      map_add' := fun x y => by
        rw [← integral_add (hint x) (hint y)]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_add x y] with u hu
        rw [hu, Pi.add_apply, smul_add]
      map_smul' := fun c x => by
        rw [RingHom.id_apply, ← integral_smul]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_smul c x] with u hu
        rw [hu, Pi.smul_apply, smul_comm] }
  exact ⟨Lin.mkContinuous _ hb, fun x => rfl⟩

end GlobalTheory.CompanionTheory.PresSobA.MolBounded
end
end

section

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA

namespace GlobalTheory.CompanionTheory.PresSobA.Frame

section Norm

attribute [-instance] instTopologicalSpaceMatrix

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
  Matrix.linftyOpNormedSpace

def chartM (n : ℕ) : (Fin n → Fin n → ℂ) ≃L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  (Matrix.ofLinearEquiv ℝ).toContinuousLinearEquiv

theorem contDiffOn_invPi (n : ℕ) :
    ContDiffOn ℝ ∞ (fun M : Fin n → Fin n → ℂ => (chartM n).symm (Ring.inverse (chartM n M)))
      {M | IsUnit (chartM n M)} := by
  have : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.completeSpace ℝ _
  intro M hM
  obtain ⟨u, hu⟩ := hM
  have h1 : ContDiffAt ℝ ∞ (Ring.inverse : Matrix (Fin n) (Fin n) ℂ → _) (chartM n M) := by
    rw [← hu]
    exact contDiffAt_ringInverse ℝ u
  have h2 : ContDiffAt ℝ ∞ (fun M => (chartM n).symm (Ring.inverse (chartM n M))) M :=
    (chartM n).symm.contDiff.contDiffAt.comp M (h1.comp M (chartM n).contDiff.contDiffAt)
  exact h2.contDiffWithinAt

end Norm

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem contDiffOn_inverse : ContDiffOn ℝ ∞ (Ring.inverse : Mat n → Mat n) (GLs n) := by
  refine (contDiffOn_invPi n).mono ?_
  intro M hM
  exact (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hM)

def mulB (n : ℕ) : CLof (Mat n) (CLof (Mat n) (Mat n)) :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap :
      (Mat n →ₗ[ℝ] Mat n) ≃ₗ[ℝ] CLof (Mat n) (Mat n)).toLinearMap ∘ₗ
      LinearMap.mk₂ ℝ (fun P Z : Mat n => P * Z) add_mul (fun c P Z => Matrix.smul_mul c P Z)
        mul_add (fun c P Z => Matrix.mul_smul P c Z))

def coordL (p : Bool × Fin n × Fin n) : CLof (Mat n) ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.proj p : ((Bool × Fin n × Fin n) → ℝ) →ₗ[ℝ] ℝ) ∘ₗ
      (GlobalTheory.CompanionTheory.SobGL.HaarDom.cmE n).symm.toLinearMap)

theorem sum_coordL (M : Mat n) : ∑ p, coordL p M • bs p = M :=
  (GlobalTheory.CompanionTheory.SobGL.HaarDom.cmE n).apply_symm_apply M

def frameA (p : Bool × Fin n × Fin n) (z : Mat n) : CLof (Mat n) ℝ :=
  (coordL p).comp (mulB n (Ring.inverse z))

theorem contDiffOn_frameA (p : Bool × Fin n × Fin n) : ContDiffOn ℝ ∞ (frameA p) (GLs n) := by
  let L : Mat n →ₗ[ℝ] CLof (Mat n) ℝ :=
    { toFun := fun x => (coordL p).comp (mulB n x)
      map_add' := by
        intro x y
        ext v
        simp
      map_smul' := by
        intro c x
        ext v
        simp }
  exact L.toContinuousLinearMap.contDiff.comp_contDiffOn contDiffOn_inverse

theorem frame_eq {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (D : CLof (Mat n) V)
    {z : Mat n} (hz : z ∈ GLs n) : D = ∑ p, (frameA p z).smulRight (D (z * bs p)) := by
  have hu : IsUnit z := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hz)
  apply ContinuousLinearMap.ext
  intro v
  have hv : z * (Ring.inverse z * v) = v := by
    rw [← mul_assoc, Ring.mul_inverse_cancel z hu, one_mul]
  have hs := sum_coordL (Ring.inverse z * v)
  have h0 : v = ∑ p, coordL p (Ring.inverse z * v) • (z * bs p) := by
    conv_lhs => rw [← hv, ← hs]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => Matrix.mul_smul _ _ _
  simp only [sum_apply, ContinuousLinearMap.smulRight_apply]
  conv_lhs => rw [h0]

  rw [map_sum]
  exact Finset.sum_congr rfl fun p _ => D.map_smul _ _

theorem frame :
    ∀ n : ℕ, ∃ A : (Bool × Fin n × Fin n) → Mat n → CLof (Mat n) ℝ,
      (∀ p, ContDiffOn ℝ ∞ (A p) (GLs n)) ∧
      ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (D : CLof (Mat n) V), ∀ z ∈ GLs n,
        D = ∑ p, (A p z).smulRight (D (z * bs p)) :=
  fun _ => ⟨frameA, contDiffOn_frameA, fun _ _ _ D _ hz => frame_eq D hz⟩

end GlobalTheory.CompanionTheory.PresSobA.Frame
end
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.FrobLc

variable {l : ℕ} [Fact l.Prime]

theorem frob_idem (A : PAlg l) (e : A.A) (he : IsIdempotentElem e) : A.frob e = e := by
  change e ^ l = e
  have h := IsIdempotentElem.pow_succ_eq (l - 1) he
  rwa [Nat.sub_add_cancel (Fact.out : l.Prime).one_lt.le] at h

theorem lcRes_id (A : PAlg l) (n : ℕ) (f : LocallyConstant (SU A) (ZMod (l ^ n))) :
    lcRes (l ^ n) (Spec.map (CommRingCat.ofHom (RingHom.id A.Ug))) f = f := by
  have e : Spec.map (CommRingCat.ofHom (RingHom.id A.Ug)) = 𝟙 (SU A) := by
    change Spec.map (𝟙 (CommRingCat.of A.Ug)) = 𝟙 _
    exact Spec.map_id _
  rw [e]
  ext x
  rfl

theorem phi_lcA (hN : LcNat) (H : RIn l) (A : PAlg l) (hA : A.IsTest) (n : ℕ)
    (f : LocallyConstant (SU A) (ZMod (l ^ n))) : A.phi n (lcA A n f) = lcA A n f := by
  have h := (hN l H A hA n).1 A hA A.frob A.pdOk_frob (RingHom.id A.Ug)
    (fun e he => by rw [frob_idem A e he]; rfl) f
  rw [lcRes_id] at h
  exact h

section Gen
universe w w' u v u' v'
variable {R R' S : Type} [CommRing R] [CommRing R'] [CommRing S] {C : Type u} [Category.{v} C]
  {C' : Type u'} [Category.{v'} C'] {F : C ⥤ ModuleCat.{w} R} {F' : C' ⥤ ModuleCat.{w'} R'}
  {σ : R →+* R'} {ρ : R' →+* R'}

theorem cls_congr {K : CrystallineSemistableComparison.Cx.{w} R} {k : ℕ} {x y : K.X k} (h : x = y) (hx : K.d k x = 0) (hy : K.d k y = 0) :
    K.cls x hx = K.cls y hy := by
  subst h; rfl

theorem pull_fix (m : Mor F F' σ) (p : Mor F' F' ρ) (j : ℕ) (h : ∀ z, p.pullC j (m.pullC j z) = m.pullC j z)
    (c : CH.H F j) : p.pull j (m.pull j c) = m.pull j c := by
  obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  exact cls_congr (h z) _ _
end Gen

variable {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

def lcM (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K) (n : ℕ) :
    Mor (probe H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n).L (modF (AcrEl M.P n)) (Int.castRingHom (Acris l)) :=
  lcMor hN H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n

theorem phi_lcM (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K) (n j : ℕ)
    (z : Cn (probe H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n).L j) :
    (phiMor M.P n).pullC j ((lcM hN H r M n).pullC j z) = (lcM hN H r M n).pullC j z := by
  funext s
  exact phi_lcA hN H _ (s.obj (Fin.last j)).1.property n _

theorem fPhi : CrystallineSemistableComparison.E.FPhi := fun hN l _ H r K M n j x =>
  pull_fix (lcM hN H r M n) (phiMor M.P n) j (phi_lcM hN H r M n j) ((pts H r M (𝟭 _) n).et 0 j x)

end GlobalTheory.CompanionTheory.FrobLc
end
end

section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.LineBase

theorem u_eq {X : Scheme.{0}} (D : LineData X) {V : Scheme.{0}} {a a' b b' : V ⟶ D.Y}
    (ha : a = a') (hb : b = b') (h : a ≫ D.f = b ≫ D.f) (h' : a' ≫ D.f = b' ≫ D.f) :
    D.u a b h = D.u a' b' h' := by
  subst ha hb
  rfl

noncomputable def pull {X' X : Scheme.{0}} (g : X' ⟶ X) (D : LineData X) : LineData X' where
  Y := pullback D.f g
  f := pullback.snd D.f g
  sm := by
    exact MorphismProperty.pullback_snd (P := @Smooth) D.f g D.sm
  surj := by
    exact MorphismProperty.pullback_snd (P := @Surjective) D.f g D.surj
  u := fun {V} a b h => D.u (a ≫ pullback.fst D.f g) (b ≫ pullback.fst D.f g) (by
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc, ← Category.assoc, h])
  nat := fun {V' V} k a b h => by
    rw [← D.nat k (a ≫ pullback.fst D.f g) (b ≫ pullback.fst D.f g)]
    exact u_eq D (Category.assoc _ _ _) (Category.assoc _ _ _) _ _
  coc := fun {V} a b c h h' => D.coc _ _ _ _ _

theorem lineBC : CrystallineSemistableComparison.E.LineBC := by
  intro X' X g D
  refine ⟨pull g D, pullback.fst D.f g, pullback.condition, ?_, ?_⟩
  · intro V a x h
    exact ⟨pullback.lift a x h, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  · intro V a b h h'
    rfl

end GlobalTheory.CompanionTheory.LineBase
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EtCupF

variable {l : ℕ} [Fact l.Prime]

noncomputable def lcRing (hS : LcSpec) (H : RIn l) (A : PAlg l) (hA : A.IsTest) (n : ℕ) :
    LocallyConstant (SU A) (ZMod (l ^ n)) →+* A.Acr n where
  toFun := lcA A n
  map_one' := (hS l H A hA n).2.1
  map_mul' := (hS l H A hA n).2.2.1
  map_zero' := map_zero _
  map_add' := map_add _

theorem lcMor_cup (hM : MorCup) (hS : LcSpec) (hN : LcNat) (H : RIn l) (r : Roots l) {C : Type 1} [Category.{0} C]
    (T : C ⥤ Test l) (n p q m : ℕ) (h : p + q = m) (x : CH.H (probe H r T n).L p) (y : CH.H (probe H r T n).L q) :
    (lcMor hN H r T n).pull m ((mulP (lcF (probe H r T n).S (l ^ n))).cup h x y) =
      (mulP ((T ⋙ testι l) ⋙ AcrA l n)).cup h ((lcMor hN H r T n).pull p x) ((lcMor hN H r T n).pull q y) :=
  (hM ℤ (Acris l) (Int.castRingHom (Acris l)) C (lcF (probe H r T n).S (l ^ n)) ((T ⋙ testι l) ⋙ AcrA l n)
    (lcMor hN H r T n) (fun c => lcRing hS H (T.obj c).obj (T.obj c).property n) (fun c x => rfl)).2 p q m h x y

variable {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem eG_cup (hE : EtCup) (hM : MorCup) (hS : LcSpec) (E : EtIn) (hN : LcNat) (H : RIn l) (r : Roots l)
    (M : Model l K) {C : Type 1} [Category.{0} C] (G : C ⥤ El M.P) (n : ℕ) (i i' i'' : ℤ) (hi : i + i' = i'')
    (j j' j'' : ℕ) (hj : j + j' = j'') (x : Ht (l ^ n) (sch.obj (gb M)) j i) (y : Ht (l ^ n) (sch.obj (gb M)) j' i') :
    eG hN H r M G n i'' j'' ((cup (l ^ n) x y).cast (by omega) hi) =
      (mulP ((((G ⋙ CategoryOfElements.π _) ⋙ testι l)) ⋙ AcrA l n)).cup hj (eG hN H r M G n i j x) (eG hN H r M G n i' j' y) := by
  have h1 := hE E.gen E.tw (l ^ n) C (probe H r (G ⋙ CategoryOfElements.π _) n) (gb M)
    (pts H r M G n) i i' i'' hi j j' j'' hj x y
  have h2 := lcMor_cup hM hS hN H r (G ⋙ CategoryOfElements.π _) n j j' j'' hj
    ((pts H r M G n).et i j x) ((pts H r M G n).et i' j' y)
  exact (congrArg ((lcMor hN H r (G ⋙ CategoryOfElements.π _) n).pull j'') h1).trans h2

theorem fCup : CrystallineSemistableComparison.E.EtCup → CrystallineSemistableComparison.E.MorCup → CrystallineSemistableComparison.E.LcSpec → CrystallineSemistableComparison.E.FCup := by
  intro hE hM hS E hN l _ H r K M n i i' i'' hi j j' j'' hj x y
  exact eG_cup hE hM hS E hN H r M (𝟭 _) n i i' i'' hi j j' j'' hj x y

end GlobalTheory.CompanionTheory.EtCupF
end
