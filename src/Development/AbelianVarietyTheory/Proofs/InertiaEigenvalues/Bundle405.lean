module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle016
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle386
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle017
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle382
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle286
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle236
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle344
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGammaLayerPadicCoordinates
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle388
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle227
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle042
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle270
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle271
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle323
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle247
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle389
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle345
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle295
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008

@[expose] public section

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf Formalism.MainNotions.PairedCharacterCondition
open scoped TensorProduct

theorem _root_.GlobalTheory.T.mem_heckeEig_of_image_moved_by_centre : ∀ (D : D7) (i : D.nd.Loc) (S : Sec D i), OnMtPreservesTypeV D → ∀ (c : MonoidAlgebra ℂ (G0g D.nd)) (x : D.nd.X i) (u w : TensorProduct (D.nd.O i) (KK D.nd i) (D.nd.Mt i)), u ∈ heckeEig (D.nd.T i) (D.nd.act i) x → S.Φ w = D.ntypes.onMt (D.nd.mu i) (D.nd.j i) c (S.Φ u) → w ∈ heckeEig (D.nd.T i) (D.nd.act i) x := by
  first | exact @GlobalTheory.PendOf.CenEig.main | exact GlobalTheory.PendOf.CenEig.main | (intros; apply GlobalTheory.PendOf.CenEig.main <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

theorem _root_.GlobalTheory.T.heckeStableLocalLattice_of_integral : ∀ (D : D7) (M : MtFam D) (B : NLocBase D M) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (w : D.what₂.places.Pl), LatInt D M (B.Qc j w) j h1 h2 w → LatStable B j w := by
  first | exact @GlobalTheory.LatStab.latStable_of_latInt | exact GlobalTheory.LatStab.latStable_of_latInt | (intros; apply GlobalTheory.LatStab.latStable_of_latInt <;> assumption)
end

section

noncomputable section

open PowerSeries GlobalTheory.BK

namespace GlobalTheory.Proof.exists_monodromy_eq_leadingCoeff_breuilKisinDescent

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] {η H : ℕ}

omit [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] in
theorem natCast_l_ne_zero : (l : K) ≠ 0 := by
  rw [← map_natCast (algebraMap ℚ_[l] K)]
  exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)

theorem exists_Mon_eq_Lc_cls : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H) (U : Finset ℤ) (N : ℕ), D.jumps ⊆ U → U ⊆ Finset.Icc (-(η : ℤ)) H → U.card ≤ N + 1 → 1 ≤ η → η < H → 14 * H + (N + 2) * η < l → 10 * H + 2 ≤ l → IsAdicComplete (Ideal.span {(l : O)}) D.Y' → IsHausdorff (Ideal.span {(l : O)}) D.Z → ∀ y ∈ D.Y', ∃ y₀ ∈ D.Y', D.Mon y₀ = D.Lc (D.cls y) := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D U N hU hUI hUc hη1 hηH hl hl2 hC hS y hy
  have hlK : (l : K) ≠ 0 := natCast_l_ne_zero
  set k : ℕ := l - 14 * H with hk
  have hlk : ((l : K) ^ k) ≠ 0 := pow_ne_zero _ hlK
  have hint := GlobalTheory.T.breuilKisin_descent_operator_preserves_lattice O K l e a ι η H D hηH hl2
  have hcomp := GlobalTheory.T.breuilKisin_integrality_computation O K l e a ι η H D hηH hl2
  have hY'Y : ∀ {y : Vec K a ι}, y ∈ D.Y' → y ∈ D.Y := fun h => D.desc.Y'_le_Y η h

  let LcK : Vec K a ι →ₗ[K] D.Pol := D.Lc ∘ₗ D.cls
  have hLc : ∀ v : D.Y', LcK.restrictScalars O (v : Vec K a ι) ∈ D.Z := fun v =>
    hint _ (D.desc.cls_mem_Z (hY'Y v.2))
  let Lc' : D.Y' →ₗ[O] D.Z := ((LcK.restrictScalars O).comp D.Y'.subtype).codRestrict D.Z hLc

  let PK : Vec K a ι →ₗ[K] D.Pol := -((l : K) ^ k)⁻¹ • (D.cls ∘ₗ mulV K a ι (E K l e) ∘ₗ D.zeta)
  have hPK : ∀ y : Vec K a ι, PK y = -((l : K) ^ k)⁻¹ • D.cls (E K l e • D.zeta y) := fun y => by
    simp [PK]
  have hP : ∀ v : D.Y', PK.restrictScalars O (v : Vec K a ι) ∈ D.Z := by
    intro v
    have hv := v.2
    obtain ⟨p, hp, f, hf, hz⟩ := GlobalTheory.T.breuilKisin_zeta_fine_bound_second_basis O K l e a ι η H D hη1 hηH (by omega) v hv
    have hEf : D.cls (E K l e • f) = 0 := by
      rw [PhiMod.cls_eq_zero_iff]
      have h1 := hcomp.2.1 f hf
      have h2 := D.smul_mem_Man (pow_mem (A_le_Rpi l e (E_mem l e (A O K))) (2 * H + 1)) h1
      rwa [smul_smul, ← Ezpow_natCast, ← Ezpow_add, show ((2 * H + 1 : ℕ) : ℤ) + -(2 * H : ℤ) = 1 by push_cast; ring,
        show (1 : ℤ) = ((1 : ℕ) : ℤ) by rfl, Ezpow_natCast, pow_one] at h2
    have hval : PK (v : Vec K a ι) = D.cls (-(E K l e • p)) := by
      rw [hPK, hz, smul_add, smul_comm (E K l e) ((l : K) ^ k) p,
        smul_comm (E K l e) (((l : K) ^ (3 * H))⁻¹) f, map_add, map_smul D.cls ((l : K) ^ k), map_smul D.cls ((l : K) ^ (3 * H))⁻¹, hEf, smul_zero, add_zero,
        smul_smul, neg_mul, inv_mul_cancel₀ hlk, neg_smul, one_smul, map_neg]
    refine D.desc.mem_Z.2 ⟨⟨-(E K l e • p), ?_, hval.symm⟩, fun g => ?_⟩
    · refine neg_mem ?_
      rw [mem_divE, smul_comm]
      exact D.M.smul_mem (EIn l e (A O K)) (D.upper p hp)
    · have h : D.cls (E K l e • D.zeta v) = D.Lc (D.cls v) - D.Mon v := by
        rw [D.Mon_eq, sub_sub_cancel]
      have hinv : D.cls (E K l e • D.zeta v) ∈ D.desc.actPol.invariants := by
        rw [h]
        refine sub_mem (fun g => ?_) (D.desc.Mon_mem_invariants (hY'Y hv).2)
        rw [BKDat.actPol_Lc, D.desc.cls_mem_invariants (hY'Y hv).2 g]
      have h2 : PK v ∈ D.desc.actPol.invariants := by
        rw [hPK]
        exact Submodule.smul_mem _ _ hinv
      exact h2 g
  let P : D.Y' →ₗ[O] D.Z := ((PK.restrictScalars O).comp D.Y'.subtype).codRestrict D.Z hP
  have hLc'apply : ∀ v : D.Y', (Lc' v : D.Pol) = D.Lc (D.cls v) := fun v => rfl
  have hPapply : ∀ v : D.Y', (P v : D.Pol) = PK v := fun v => rfl
  have hsum : ∀ v : D.Y', (((Lc' + (l : O) ^ k • P) v : D.Z) : D.Pol) = D.Mon v := by
    intro v
    rw [LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add, Submodule.coe_smul_of_tower,
      hLc'apply, hPapply, hPK, ← algebraMap_smul K ((l : O) ^ k), map_pow, map_natCast, smul_smul, mul_neg,
      mul_inv_cancel₀ hlk, neg_one_smul, D.Mon_eq, sub_eq_add_neg]
  let W : Submodule O D.Z := ((D.Zl.map D.Lc).restrictScalars O).comap D.Z.subtype
  have hW : ∀ z : D.Z, z ∈ W ↔ ∃ w ∈ D.Zl, D.Lc w = z := fun z => Iff.rfl
  have hc : η + (N + 1) * η < k := by
    have : (N + 2) * η = η + (N + 1) * η := by ring
    omega
  have h1 : ∀ v, Lc' v ∈ W ∧ (Lc' + (l : O) ^ k • P) v ∈ W := by
    intro v
    refine ⟨(hW _).2 ⟨D.cls v, D.desc.mem_Zl_of_mem_Z (D.desc.cls_mem_Z (hY'Y v.2)), rfl⟩, (hW _).2 ?_⟩
    rw [hsum]
    obtain ⟨-, w, hw, h⟩ := GlobalTheory.T.monodromy_mem_range_of_invariant_vector O K l e a ι η H D v
      (D.desc.mem_Yl_iff.2 ⟨0, by rw [pow_zero, one_smul]; exact hY'Y v.2⟩)
    exact ⟨w, hw, h⟩
  have h2 : ∀ z : D.Z, (l : O) • z ∈ W → z ∈ W := by
    intro z hz
    obtain ⟨w, hw, h⟩ := (hW _).1 hz
    refine (hW _).2 ⟨((l : K))⁻¹ • w, D.Zl.smul_mem _ hw, ?_⟩
    rw [map_smul, h, Submodule.coe_smul_of_tower, ← algebraMap_smul K (l : O), map_natCast, smul_smul,
      inv_mul_cancel₀ hlK, one_smul]
  have h3 : ∀ z ∈ W, (l : O) ^ (η + (N + 1) * η) • z ∈ LinearMap.range Lc' := by
    intro z hz
    obtain ⟨w, hw, h⟩ := (hW z).1 hz
    obtain ⟨y', hy', hy'eq⟩ := GlobalTheory.T.exists_mem_tameDescent_class_eq_of_pow_mem O K l e a ι η H D U N hU hUI hUc hηH (by omega) hl2 0 w hw
      (by rw [pow_zero, one_smul, h]; exact z.2)
    refine ⟨⟨y', hy'⟩, Subtype.ext ?_⟩
    rw [hLc'apply, Submodule.coe_smul_of_tower, ← algebraMap_smul K ((l : O) ^ (η + (N + 1) * η)), map_pow, map_natCast, ← h, hy'eq,
      zero_add]
  obtain ⟨y₁, hy₁⟩ := GlobalTheory.successive_approximation (l : O) Lc' P W (η + (N + 1) * η) k hc h1 h2 h3 ⟨y, hy⟩
  refine ⟨y₁, y₁.2, ?_⟩
  have := congrArg Subtype.val hy₁
  rw [hsum] at this
  exact this

end GlobalTheory.Proof.exists_monodromy_eq_leadingCoeff_breuilKisinDescent
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

theorem _root_.GlobalTheory.T.exists_gammaLayer_padic_coordinates : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ Γ : GamS P K s LL, (∃ lam : ↥Γ.GKs →* Multiplicative ℤ_[l], Continuous lam ∧ (∀ g, lam g = 1 ↔ Γ.resΓ (g : ↥(GK K)) = 1) ∧ (∀ g, lam g = Multiplicative.ofAdd 1 ↔ Γ.resΓ (g : ↥(GK K)) = Γ.gam) ∧ (∃ g, lam g = Multiplicative.ofAdd 1) ∧ IsClosed (Γ.GKs : Set ↥(GK K))) ∧ ∃ lam : ↥(GK K) →* Multiplicative ℤ_[l], Continuous lam ∧ (∀ g, lam g = 1 ↔ Γ.resΓ g ∈ Γ.DelF) ∧ (∀ g, Γ.resΓ g = Γ.gamK → lam g = Multiplicative.ofAdd 1) := by
  first | exact @GlobalTheory.HWL.Coord.exists_gamma_coordinates | exact GlobalTheory.HWL.Coord.exists_gamma_coordinates | (intros; apply GlobalTheory.HWL.Coord.exists_gamma_coordinates <;> assumption)
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass

theorem _root_.GlobalTheory.T.jump_range_positive_sign_place : StepJumpDirect := by
  first | exact @GlobalTheory.Pass.stepJumpDirect_holds | exact GlobalTheory.Pass.stepJumpDirect_holds | (intros; apply GlobalTheory.Pass.stepJumpDirect_holds <;> assumption)
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass

theorem _root_.GlobalTheory.T.lengths_modulo_submodule_agree : (∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (A H : Submodule O M), lenModN A H = BlochKatoDuality.lenMod A H) ∧ ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (Xs : Set (D.nd.X i)) (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (e : ℕ), LocBoundP i w hw r Xs M e ↔ LocBound i w hw r Xs M e := by
  first | exact @GlobalTheory.LenModAgree.main | exact GlobalTheory.LenModAgree.main | (intros; apply GlobalTheory.LenModAgree.main <;> assumption)
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass

theorem _root_.GlobalTheory.T.blochKatoCharactersTypePrime_proof : StepHfChar := by
  first | exact @GlobalTheory.Pass.HfCharStep.main | exact GlobalTheory.Pass.HfCharStep.main | (intros; apply GlobalTheory.Pass.HfCharStep.main <;> assumption)
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass

theorem _root_.GlobalTheory.T.central_elements_from_idempotent_coeffs : StepCentral := by
  first | exact @GlobalTheory.Pass.CentralStep.main | exact GlobalTheory.Pass.CentralStep.main | (intros; apply GlobalTheory.Pass.CentralStep.main <;> assumption)
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass

theorem _root_.GlobalTheory.T.dualJumpRangeNegativeSignPlace_proof : StepJumpDual := by
  first | exact @GlobalTheory.Pass.JumpDualStep.jumpDual_main | exact GlobalTheory.Pass.JumpDualStep.jumpDual_main | (intros; apply GlobalTheory.Pass.JumpDualStep.jumpDual_main <;> assumption)
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass

theorem _root_.GlobalTheory.T.twisted_galois_rep_character_blocks : StepSub := by
  first | exact @GlobalTheory.Pass.stepSub_holds | exact GlobalTheory.Pass.stepSub_holds | (intros; apply GlobalTheory.Pass.stepSub_holds <;> assumption)
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass

theorem _root_.GlobalTheory.T.typePrimeCompletionDegreeOneCount_proof : StepDeg := by
  first | exact @GlobalTheory.Pass.stepDeg_main | exact GlobalTheory.Pass.stepDeg_main | (intros; apply GlobalTheory.Pass.stepDeg_main <;> assumption)
end

section

namespace GlobalTheory.Models
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

theorem exists_of_resCount_ne_zero_sq {k : Type} [Field k] {U : Multiset ℤ} {w : ℤ} {x : k}
    (h : resCount U w x ≠ 0) : ∃ u ∈ U, ((u - w : ℤ) : k) = x := by
  classical
  unfold resCount at h
  rw [Ne, Multiset.card_eq_zero] at h
  obtain ⟨u, hu⟩ := Multiset.exists_mem_of_ne_zero h
  rw [Multiset.mem_filter] at hu
  exact ⟨u, hu.1, hu.2⟩

theorem ModTh.sen_model_subquot_mem_U : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt), Dt.T1 l → Dt.T2 l → Dt.T3 l → ∀ (A₁ A : Ob k G) (j : (Fin A₁.m → k) →ₗ[k] (Fin M.T.m → k)) (p : (Fin A₁.m → k) →ₗ[k] (Fin A.m → k)) (N : Lats k n A.m), IsHom A₁ M.T j → Function.Injective j → IsHom A₁ A p → Function.Surjective p → M.Model A N → ∀ i x, sen ((F.D A).γ i) (N i) x ≠ 0 → ∃ u ∈ Dt.U i, ((u - Dt.w i : ℤ) : k) = x := by
  intro k G _ _ l n _ _ _ R F r Dt M h1 h2 h3 A₁ A j p N hj hji hp hps hN i x hx
  have hT := GlobalTheory.T.obj_and_abc_of_model F M M.T M.Nstd M.std_model
  have hm1 := GlobalTheory.T.model_preimage_of_injective_finDimRepModelHom F M A₁ M.T j M.Nstd hj hji M.std_model
  have hm := ModTh.model_push_of_surjective F M A₁ A p _ hp hps hm1
  have habc0 := (GlobalTheory.T.obj_and_abc_of_model F M A _ hm).2
  have habc := (GlobalTheory.T.obj_and_abc_of_model F M A N hN).2
  obtain ⟨c, hc, hs⟩ := GlobalTheory.T.senWeights_close_of_height_gamma_conditions (F.D A) Dt _ N habc0 habc i x hx
  have hle := GlobalTheory.T.senMultiplicity_subquotient_lattice_le F M.T A₁ A j p Dt.w Dt.wst M.Nstd hT.1 hj hji hp hps hT.2 i (x + c)
  have hs' : sen ((F.D M.T).γ i) (M.Nstd i) (x + c) ≠ 0 := fun h0 => hs (by
    rw [h0] at hle; exact Nat.le_zero.mp hle)
  rw [M.std_sen] at hs'
  obtain ⟨u, hu, hux⟩ := exists_of_resCount_ne_zero_sq hs'
  obtain ⟨u', hu', hux'⟩ := GlobalTheory.T.model_senWeight_mem_weight_residues F M A N hN i x hx
  rcases Multiset.mem_add.mp hu' with hU | hB
  · exact ⟨u', hU, hux'⟩
  · exfalso
    obtain ⟨hb1, hb2⟩ := mem_block.mp hB
    obtain ⟨hc1, hc2⟩ := abs_le.mp hc
    refine (GlobalTheory.T.admissibleLetterData_window_arithmetic (k := k) Dt h1 h2 h3 i).2.1 u hu (u' + c) (by omega) (by omega) ?_
    rw [← hux'] at hux
    push_cast at hux ⊢
    linear_combination hux

end GlobalTheory.Models
end
