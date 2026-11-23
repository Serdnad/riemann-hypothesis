module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle040
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle001
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle043
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LieAlgebraOfLinearGroupClosed
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle041
public import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
public import GroundTheory.GlobalFields.TateThesis.HeckeLFunction
public import GroundTheory.GlobalFields.TateThesis.NonvanishingPrimes
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import GroundTheory.AutomorphicForms.GL2.FiniteIdeleDecomp
public import GroundTheory.AutomorphicForms.GL2.Bundle003
import GroundTheory.LocalFields.Bundle001

@[expose] public section

section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

theorem _root_.GlobalTheory.T.derived_action_conjugation : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {v : H} (hv : IsSmoothVec G π v) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ G), π g (dRep π X v) = dRep π (g * X * g⁻¹) (π g v) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.dRep_equivariant | exact GlobalTheory.CompanionTheory.Hypotheses₂.HCA.dRep_equivariant | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.HCA.dRep_equivariant <;> assumption)
end

section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

theorem _root_.GlobalTheory.T.derived_action_of_smooth_vector : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {v : H} (hv : IsSmoothVec G π v) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G), HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) v) (dRep π X v) 0 ∧ IsSmoothVec G π (dRep π X v) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.hasDerivAt_dRep_and_isSmoothVec | exact GlobalTheory.CompanionTheory.Hypotheses₂.HCA.hasDerivAt_dRep_and_isSmoothVec | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.HCA.hasDerivAt_dRep_and_isSmoothVec <;> assumption)
end

section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

theorem _root_.GlobalTheory.T.smooth_vectors_invariant_subspace : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π), (∀ u v : H, IsSmoothVec G π u → IsSmoothVec G π v → IsSmoothVec G π (u + v)) ∧ (∀ (c : ℂ) (v : H), IsSmoothVec G π v → IsSmoothVec G π (c • v)) ∧ (∀ g ∈ G, ∀ v : H, IsSmoothVec G π v → IsSmoothVec G π (π g v)) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.smooth_closed | exact GlobalTheory.CompanionTheory.Hypotheses₂.HCA.smooth_closed | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.HCA.smooth_closed <;> assumption)
end

section

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA.SmoothLin

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem hasDerivAt_exp_entries (X : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => (Matrix.of.symm (NormedSpace.exp (t • X)) : Fin n → Fin n → ℂ))
      (Matrix.of.symm X) 0 := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] (Fin n → Fin n → ℂ) :=
    { toFun := fun M => Matrix.of.symm M
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h

theorem hasDerivAt_orbit {G : Set (Matrix (Fin n) (Fin n) ℂ)} {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {v : H}
    {F : (Fin n → Fin n → ℂ) → H} (hF : ContDiff ℝ ∞ F) (hFG : ∀ z, Matrix.of z ∈ G → π (Matrix.of z) v = F z)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) :
    HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) v)
      (fderiv ℝ F (Matrix.of.symm (1 : Matrix (Fin n) (Fin n) ℂ)) (Matrix.of.symm X)) 0 := by
  have hfun : (fun t : ℝ => π (NormedSpace.exp (t • X)) v) =
      fun t : ℝ => F (Matrix.of.symm (NormedSpace.exp (t • X))) := by
    funext t
    have hmem : Matrix.of (Matrix.of.symm (NormedSpace.exp (t • X))) ∈ G := by
      rw [Matrix.of.apply_symm_apply]
      exact hX t
    simpa only [Matrix.of.apply_symm_apply] using hFG _ hmem
  rw [hfun]
  have hdiff : DifferentiableAt ℝ F (Matrix.of.symm (NormedSpace.exp ((0 : ℝ) • X))) :=
    (hF.differentiable (by simp)) _
  have h := hdiff.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_exp_entries X)
  rw [zero_smul, NormedSpace.exp_zero] at h
  exact h

theorem differentiableAt_orbit {G : Set (Matrix (Fin n) (Fin n) ℂ)} {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    {v : H} (hv : IsSmoothVec G π v) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) :
    DifferentiableAt ℝ (fun t : ℝ => π (NormedSpace.exp (t • X)) v) 0 := by
  obtain ⟨F, hF, hFG⟩ := hv
  exact (hasDerivAt_orbit hF hFG hX).differentiableAt

theorem dRep_linear : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G)
    (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {u v : H} (hu : IsSmoothVec G π u) (hv : IsSmoothVec G π v)
    {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) (hY : Y ∈ HCSS.lieOf G),
    dRep π (X + Y) v = dRep π X v + dRep π Y v ∧ dRep π X (u + v) = dRep π X u + dRep π X v ∧
      ∀ c : ℂ, dRep π X (c • v) = c • dRep π X v := by
  intro n G H _ _ π hG _hrep u v hu hv X Y hX hY
  have hXY : X + Y ∈ HCSS.lieOf G := (lieOf_isLieSubalgebra hG).1 X Y hX hY
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨F, hF, hFG⟩ := hv
    simp only [dRep]
    rw [(hasDerivAt_orbit hF hFG hXY).deriv, (hasDerivAt_orbit hF hFG hX).deriv,
      (hasDerivAt_orbit hF hFG hY).deriv]
    exact (fderiv ℝ F (Matrix.of.symm (1 : Matrix (Fin n) (Fin n) ℂ))).map_add
      (Matrix.of.symm X) (Matrix.of.symm Y)
  · simp only [dRep, map_add (f := _)]
    exact deriv_add (differentiableAt_orbit hu hX) (differentiableAt_orbit hv hX)
  · intro c
    simp only [dRep, map_smul]
    exact deriv_const_smul c (differentiableAt_orbit hv hX)

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA.SmoothLin

end
end

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps GlobalTheory.CompanionTheory.HeckeBridge GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.IdeleGroup
open GroundTheory.Automorphic.GodementSection (localChar)
open Formalism.L2.Host (unif atFin unif_spec)

namespace GlobalTheory.CompanionTheory.HeckeBridge

variable {E : Type} [Field E] [NumberField E]

theorem comp_finiteUnitsSingle (χ : HChar E) (hu : IsUnitary χ) (v : HeightOneSpectrum (𝓞 E)) :
    (((toHecke χ hu).toIdele.comp ofFinite).comp (finiteUnitsSingle v)) =
      ((toHecke χ hu).localComponent v : (v.adicCompletion E)ˣ →* Circle) := by
  refine MonoidHom.ext fun a => ?_
  show (toHecke χ hu).toIdele (ofFinite (finiteUnitsSingle v a)) = (toHecke χ hu).localComponent v a
  rw [GroundTheory.Global.IdeleGroup.ofFinite_finiteUnitsSingle, GroundTheory.Global.HeckeCharacter.localComponent_apply]

private theorem toHecke_local_eq_one_iff (χ : HChar E) (hu : IsUnitary χ) (v : HeightOneSpectrum (𝓞 E))
    (x : (v.adicCompletion E)ˣ) :
    (((toHecke χ hu).toIdele.comp ofFinite).comp (finiteUnitsSingle v)) x = 1 ↔ χ.loc v x = 1 := by
  rw [comp_finiteUnitsSingle χ hu v]
  have h := coe_localComponent χ hu v x
  constructor
  · intro h1
    apply Units.ext
    rw [← h]
    have h1' : (toHecke χ hu).localComponent v x = 1 := h1
    rw [h1', Circle.coe_one, Units.val_one]
  · intro h1
    have h1' : (toHecke χ hu).localComponent v x = 1 := by
      apply Circle.ext
      rw [h, h1, Units.val_one, Circle.coe_one]
    exact h1'

theorem levelLe_iff_unitsLevel_le_ker (χ : HChar E) (hu : IsUnitary χ) (v : HeightOneSpectrum (𝓞 E)) (n : ℕ) :
    χ.LevelLe v n ↔
      unitsLevel v n ≤ (((toHecke χ hu).toIdele.comp ofFinite).comp (finiteUnitsSingle v)).ker := by
  unfold Formalism.L2.Host.HChar.LevelLe
  constructor
  · intro h x hx
    rw [GroundTheory.Global.mem_unitsLevel] at hx
    rw [MonoidHom.mem_ker, toHecke_local_eq_one_iff χ hu v x]
    exact h x hx.1 hx.2
  · intro h x hux hx
    rw [← toHecke_local_eq_one_iff χ hu v x]
    exact h (GroundTheory.Global.mem_unitsLevel.mpr ⟨hux, hx⟩)

theorem levelLe_iff_conductorExponentAt (χ : HChar E) (hu : IsUnitary χ) (v : HeightOneSpectrum (𝓞 E)) (n : ℕ) :
    χ.LevelLe v n ↔ conductorExponentAt ((toHecke χ hu).toIdele.comp ofFinite) v ≤ n := by
  rw [levelLe_iff_unitsLevel_le_ker χ hu v n]
  exact GroundTheory.Global.unitsLevel_le_ker_iff v GroundTheory.Global.Circle.noSmallSubgroups _
    (((toHecke χ hu).continuous_toIdele.comp GroundTheory.Global.IdeleGroup.continuous_ofFinite).comp
      (GroundTheory.Global.IdeleGroup.continuous_finiteUnitsSingle v))

private theorem asIdeal_pow_dvd_finprod_iff {R : Type*} [CommRing R] [IsDedekindDomain R]
    {a : HeightOneSpectrum R → ℕ} (ha : (Function.support a).Finite) (v : HeightOneSpectrum R) (k : ℕ) :
    v.asIdeal ^ k ∣ ∏ᶠ w : HeightOneSpectrum R, w.asIdeal ^ a w ↔ k ≤ a v := by
  classical
  have hfin : (Function.mulSupport fun w : HeightOneSpectrum R => w.asIdeal ^ a w).Finite := by
    rw [GroundTheory.Global.mulSupport_asIdeal_pow]; exact ha
  constructor
  · intro hk
    by_contra hlt
    rw [not_le] at hlt
    set b : HeightOneSpectrum R → ℕ := Function.update a v 0 with hb
    have hbfin : (Function.support b).Finite := by
      refine ha.subset (fun w hw => ?_)
      by_cases hwv : w = v
      · subst hwv
        simp [hb] at hw
      · simpa [hb, Function.update_of_ne hwv] using hw
    have hcfin : (Function.mulSupport fun w : HeightOneSpectrum R =>
        w.asIdeal ^ (if w = v then a v else 0)).Finite := by
      refine (Set.finite_singleton v).subset (fun w hw => ?_)
      rw [Set.mem_singleton_iff]
      by_contra hwv
      exact hw (by simp [hwv])
    have hbfin' : (Function.mulSupport fun w : HeightOneSpectrum R => w.asIdeal ^ b w).Finite := by
      rw [GroundTheory.Global.mulSupport_asIdeal_pow]; exact hbfin
    have hsingle : ∏ᶠ w : HeightOneSpectrum R, w.asIdeal ^ (if w = v then a v else 0) = v.asIdeal ^ a v := by
      rw [finprod_eq_single _ v (fun w hw => by simp [hw])]
      simp
    have hsplit : ∏ᶠ w : HeightOneSpectrum R, w.asIdeal ^ a w =
        v.asIdeal ^ a v * ∏ᶠ w : HeightOneSpectrum R, w.asIdeal ^ b w := by
      rw [← hsingle, ← finprod_mul_distrib hcfin hbfin']
      refine finprod_congr fun w => ?_
      by_cases hwv : w = v
      · subst hwv
        simp [hb]
      · simp [hb, hwv, Function.update_of_ne hwv]
    rw [hsplit] at hk
    have hpow : v.asIdeal ^ k = v.asIdeal ^ a v * v.asIdeal ^ (k - a v) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hpow] at hk
    have hne0 : v.asIdeal ^ a v ≠ 0 := pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact v.ne_bot)
    have hk' := (mul_dvd_mul_iff_left hne0).mp hk
    have hv : v.asIdeal ∣ ∏ᶠ w : HeightOneSpectrum R, w.asIdeal ^ b w :=
      (dvd_pow_self _ (by omega)).trans hk'
    have h1 := (GroundTheory.Global.asIdeal_dvd_finprod_iff hbfin v).mp hv
    simp [hb] at h1
  · intro hk
    exact (pow_dvd_pow _ hk).trans
      (finprod_mem_dvd (f := fun w : HeightOneSpectrum R => w.asIdeal ^ a w) v hfin)

theorem multiplicity_conductor_toHecke (E : Type) [Field E] [NumberField E] (χ : HChar E) (hu : IsUnitary χ)
    (v : HeightOneSpectrum (𝓞 E)) (m : ℕ) (h : ExpAt χ v m) :
    multiplicity v.asIdeal (toHecke χ hu).conductor = m := by
  have hcont : Continuous ((toHecke χ hu).toIdele.comp ofFinite) :=
    (toHecke χ hu).continuous_toIdele.comp GroundTheory.Global.IdeleGroup.continuous_ofFinite
  have hfin := GroundTheory.Global.IdeleGroup.finite_support_conductorExponentAt
    GroundTheory.Global.Circle.noSmallSubgroups _ hcont
  have hne := (toHecke χ hu).conductor_ne_bot
  have hcond : χ.IsCond (toHecke χ hu).conductor := by
    unfold Formalism.L2.Host.HChar.IsCond
    refine ⟨hne, fun w n => ?_⟩
    rw [levelLe_iff_conductorExponentAt χ hu w n]
    have h1 := asIdeal_pow_dvd_finprod_iff hfin w (n + 1)
    change _ ↔ ¬ w.asIdeal ^ (n + 1) ∣ ∏ᶠ u : HeightOneSpectrum (𝓞 E),
      u.asIdeal ^ conductorExponentAt ((toHecke χ hu).toIdele.comp ofFinite) u
    rw [h1]
    constructor <;> intro h2 <;> omega
  exact (GlobalTheory.CMVal.ExpAt.unique h ((GlobalTheory.CMVal.isCond_iff_expAt χ hne).mp hcond v)).symm

end GlobalTheory.CompanionTheory.HeckeBridge
end
end

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps GlobalTheory.CompanionTheory.HeckeBridge GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.IdeleGroup
open GroundTheory.Automorphic.GodementSection (localChar)
open Formalism.L2.Host (unif atFin unif_spec)

namespace GlobalTheory.CompanionTheory.HeckeBridge

variable {E : Type} [Field E] [NumberField E]

theorem unrAt_iff_not_dvd_conductor (χ : HChar E) (hu : IsUnitary χ) (v : HeightOneSpectrum (𝓞 E)) :
    χ.UnrAt v ↔ ¬ v.asIdeal ∣ (toHecke χ hu).conductor := by
  rw [HeckeCharacter.not_dvd_conductor_iff]
  constructor
  · intro h a ha
    rw [Submonoid.mem_units_iff] at ha
    have h1 : Valued.v (a : v.adicCompletion E) ≤ 1 := ha.1
    have h2 : Valued.v ((a⁻¹ : (v.adicCompletion E)ˣ) : v.adicCompletion E) ≤ 1 := ha.2
    have h3 : Valued.v (a : v.adicCompletion E) = 1 := by
      refine le_antisymm h1 ?_
      rw [Units.val_inv_eq_inv_val, map_inv₀] at h2
      exact (inv_le_one₀ (by simp [zero_lt_iff])).1 h2
    rw [MonoidHom.mem_ker]
    show (toHecke χ hu).localComponent v a = 1
    apply Circle.ext
    rw [coe_localComponent, h a h3]
    simp
  · intro h x hx
    have hx' : x ∈ (Submonoid.ofClass (v.adicCompletionIntegers E)).units := by
      rw [Submonoid.mem_units_iff]
      refine ⟨le_of_eq hx, ?_⟩
      show Valued.v ((x⁻¹ : (v.adicCompletion E)ˣ) : v.adicCompletion E) ≤ 1
      rw [Units.val_inv_eq_inv_val, map_inv₀]
      have hx1 : Valued.v (x : v.adicCompletion E) = 1 := hx
      rw [hx1, inv_one]
    have h1 : (toHecke χ hu).localComponent v x = 1 := MonoidHom.mem_ker.1 (h hx')
    have h2 := coe_localComponent χ hu v x
    rw [h1] at h2
    ext
    simpa using h2.symm

theorem coeff_eq_val (χ : HChar E) (hu : IsUnitary χ) {v : HeightOneSpectrum (𝓞 E)}
    (hv : ¬ v.asIdeal ∣ (toHecke χ hu).conductor) :
    (toHecke χ hu).coeff v.asIdeal = (χ.val v : ℂ) := by
  rw [(toHecke χ hu).coeff_asIdeal_eq_toIdele hv (unif_spec v), ← HeckeCharacter.localComponent_apply,
    coe_localComponent]
  rfl

theorem hasProd_eulerFactor_toHecke : ∀ (E : Type) [Field E] [NumberField E] (χ : HChar E) (hu : IsUnitary χ) (s : ℂ),
    1 < s.re → HasProd (eulerFactor χ s) ((toHecke χ hu).LFunction s) := by
  intro E _ _ χ hu s hs
  have h : eulerFactor χ s = fun v : HeightOneSpectrum (𝓞 E) ↦
      (1 - (toHecke χ hu).coeff v.asIdeal * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹ := by
    funext v
    unfold eulerFactor
    by_cases hv : χ.UnrAt v
    · rw [if_pos hv, coeff_eq_val χ hu ((unrAt_iff_not_dvd_conductor χ hu v).1 hv)]
    · rw [if_neg hv, HeckeCharacter.coeff_asIdeal_of_dvd _
        (not_not.1 (mt (unrAt_iff_not_dvd_conductor χ hu v).2 hv))]
      simp
  rw [h]
  exact (toHecke χ hu).LFunction_hasProd_all hs

end GlobalTheory.CompanionTheory.HeckeBridge
end
end
