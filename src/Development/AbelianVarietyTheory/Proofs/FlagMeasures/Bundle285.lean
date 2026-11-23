module

public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle143
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle276
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle142
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentRadicalIntegralPointsCovolume
public import Formalism.HermitianCurvature.StatementB
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle280
public import Formalism.LocalRingCardinality.DataCoeff
public import Formalism.LocalToGlobal.GroupLattices.DownNaturalLevelZero
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle003
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.LevelIntersectParabolic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle281
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianOrbitUniqueLatticeIntegralFrames
public import Formalism.SharpRestriction.CuspSpanNormBounds.KappaEndpoints
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.NormAdditiveCharacterTypePrimeEqOne
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalModelPeriodLattices
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle009
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas

theorem genLinVolume : GenLinVolume := by
  intro E _ _ hE j hj
  induction j, hj using Nat.le_induction with
  | base => simpa using GlobalTheory.T.glNormOneAdelicQuotientVolume_one_eq_residue E hE
  | succ j hj ih =>
    have hv : 0 ≤ Formalism.HermitianLatticesTheory.vInv E := by
      unfold Formalism.HermitianLatticesTheory.vInv
      positivity
    have hz : 0 ≤ zetaE E (j + 1) := zero_le_one.trans (GlobalTheory.T.one_le_dedekindZetaRealValue_and_le_zeta_pow E (j + 1) (by omega)).1
    have h := GlobalTheory.T.glNormOneAdelicQuotientVolume_siegel_step E hE (j + 1) (by omega)
      (by rw [Nat.add_sub_cancel, ih]; exact ENNReal.ofReal_lt_top)
    rw [h, Nat.add_sub_cancel, ih, ← ENNReal.ofReal_mul' (mul_nonneg (pow_nonneg hv _) hz),
      Finset.prod_Icc_succ_top (by omega)]
    congr 1
    have e : Formalism.HermitianLatticesTheory.fDeg E * (j + 1) ^ 2 =
        Formalism.HermitianLatticesTheory.fDeg E * j ^ 2 + Formalism.HermitianLatticesTheory.fDeg E * (2 * (j + 1) - 1) := by
      have : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
      rw [this]; ring
    rw [e, pow_add]
    ring

end GlobalTheory.FlagMeas
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.unipotentRadical_integral_points_covolume : RadicalCovolume := by
  first | exact @GlobalTheory.RadCov.radicalCovolume | exact GlobalTheory.RadCov.radicalCovolume | (intros; apply GlobalTheory.RadCov.radicalCovolume <;> assumption)
end

section

open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.hcTypeW_continuous_unitary_irreducible : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (u : Fin k → ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (π : B.Mat k r → (Wp →L[ℂ] Wp)), inWb k r z → 0 < Tz k r z → Formalism.MainNotions.S.IsHCTypeW k r z u π → Nontrivial Wp ∧ IsCRepOn (UWset k r z) π ∧ ContinuousOn π (UWset k r z) ∧ (∀ h ∈ UWset k r z, ∀ v, ‖π h v‖ = ‖v‖) ∧ (∀ S : Submodule ℂ Wp, (∀ h ∈ UWset k r z, ∀ v ∈ S, π h v ∈ S) → S = ⊥ ∨ S = ⊤) := by
  first | exact @GlobalTheory.ThA.hcType_rep | exact GlobalTheory.ThA.hcType_rep | (intros; apply GlobalTheory.ThA.hcType_rep <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

theorem _root_.GlobalTheory.T.delSq_unitary_stable_and_irreducible : ∀ (n : ℕ) (lam : DomWeight n), FiniteDimensional ℂ (delSq ℂ n lam) ∧ delSq ℂ n lam = nablaSq ℂ n lam ∧ (∀ (g : Matrix (Fin n) (Fin n) ℂ), ∀ p ∈ delSq ℂ n lam, Formalism.GradedWeylDivisibility.rowAct ℂ g p ∈ delSq ℂ n lam) ∧ ∀ U : Submodule ℂ (MvPolynomial (Fin n × Fin n) ℂ), U ≤ delSq ℂ n lam → (∀ g ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ p ∈ U, Formalism.GradedWeylDivisibility.rowAct ℂ g p ∈ U) → U = ⊥ ∨ U = delSq ℂ n lam := by
  first | exact @GlobalTheory.WeylUnitary.delSq_irreducible_unitary | exact GlobalTheory.WeylUnitary.delSq_irreducible_unitary | (intros; apply GlobalTheory.WeylUnitary.delSq_irreducible_unitary <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions.S
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IsoOrthHyp

open Matrix

theorem exists_norm_one {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) (n : ℕ) (h : S.rank = n)
    (hn : 0 < n) (C : GL (Fin n) E)
    (hC : (C.1.map (starRingEnd E))ᵀ * C.1 = S.gram.reindex (finCongr h) (finCongr h)) :
    ∃ x : S.V, S.hT x x = 1 := by
  classical
  set e : Fin S.rank ≃ Fin n := finCongr h with he
  set M : Matrix (Fin n) (Fin n) E := ((C⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) with hM
  set i₀ : Fin n := ⟨0, hn⟩ with hi₀
  refine ⟨∑ j : Fin n, M j i₀ • S.frame (e.symm j), ?_⟩
  have hCM : C.1 * M = 1 := by
    rw [hM, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hstar : (C.1.map (starRingEnd E))ᵀ = C.1ᴴ := rfl
  have hprod : Mᴴ * S.gram.reindex e e * M = (C.1 * M)ᴴ * (C.1 * M) := by
    rw [← hC, hstar, conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  have key : (Mᴴ * S.gram.reindex e e * M) i₀ i₀ = 1 := by
    rw [hprod, hCM]
    simp
  rw [← key]

  simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
  Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
  HSpace.gram, starRingEnd_apply]
  simp only [Finset.mul_sum, Finset.sum_mul, RingHom.id_apply]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem star_eq_hostConj (D : D7) (x : D.host.E) : starRingEnd D.host.E x = D.host.conj x := by
  have := D.host.isCMField_hostE
  obtain ⟨ψ⟩ := (inferInstance : Nonempty (D.host.E →+* ℂ))
  apply ψ.injective
  have h1 : ∀ y, ψ (D.host.conj y) = starRingEnd ℂ (ψ y) :=
    (D.host.der.conj_iff ψ D.host.conj).2 (MulEquiv.apply_symm_apply _ _)
  rw [h1]
  exact NumberField.IsCMField.complexEmbedding_complexConj D.host.E ψ x

theorem exists_isotropic_orth_hyp : ∀ (D : D7), Formalism.L2.Forms.Forms0 D D.u₀ → ∃ w : (VS D).V, w ≠ 0 ∧ (VS D).hT w w = 0 ∧ ∀ i, (VS D).hT (D.sp.hypE i) w = 0 ∧ (VS D).hT (D.sp.hypF i) w = 0 := by
  intro D hF
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have hi : (0 : ℕ) ≤ D.R.m := Nat.zero_le _
  obtain ⟨C, hC, -⟩ := hF.val0.de
  have hN : 0 < D.R.N 0 := by
    show 0 < D.R.k + 0 * (D.R.t + 1)
    have := D.R.m_add_three_le_k
    omega
  have hC' : (C.1.map (starRingEnd D.host.E))ᵀ * C.1 =
      (D.sp.X 0).gram.reindex (finCongr (Formalism.L2.Forms.rankN D 0 hi))
        (finCongr (Formalism.L2.Forms.rankN D 0 hi)) := hC
  obtain ⟨x, hx⟩ := exists_norm_one (D.sp.X 0) (D.R.N 0) (Formalism.L2.Forms.rankN D 0 hi) hN C hC'
  have hπ : (hF.atT.piU : D.host.E) * D.host.conj (hF.atT.piU : D.host.E) =
      ((D.mem D.u₀).A.T : D.host.E) := hF.atT.piU_norm
  have hT0 : ((D.mem D.u₀).A.T : D.host.E) ≠ 0 := by
    rw [← D.sp_T]
    exact_mod_cast D.sp.T_prime.ne_zero
  have hsym : ∀ a b : (VS D).V, (VS D).hT a b = 0 → (VS D).hT b a = 0 := by
    intro a b hab
    rw [← (VS D).herm.eq a b, hab, map_zero]
  have hvv : (VS D).hT (D.sp.iXY 0 ((hF.atT.piU : D.host.E) • x))
      (D.sp.iXY 0 ((hF.atT.piU : D.host.E) • x)) = ((D.mem D.u₀).A.T : D.host.E) := by
    rw [D.sp.iXY_isom 0 hm]
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hx, mul_one, RingHom.id_apply,
      star_eq_hostConj]
    linear_combination hπ
  have hvz : (VS D).hT (D.sp.iXY 0 ((hF.atT.piU : D.host.E) • x)) D.sp.zm = 0 := D.sp.zm_orth _
  have hzv := hsym _ _ hvz
  have hzz : (VS D).hT D.sp.zm D.sp.zm = -((D.mem D.u₀).A.T : D.host.E) := by
    rw [D.sp.zm_norm, D.sp_T]
  refine ⟨D.sp.iXY 0 ((hF.atT.piU : D.host.E) • x) + D.sp.zm, ?_, ?_, ?_⟩
  · intro h0
    have h1 : (VS D).hT (D.sp.iXY 0 ((hF.atT.piU : D.host.E) • x) + D.sp.zm) D.sp.zm = 0 := by
      rw [h0, map_zero, LinearMap.zero_apply]
    rw [map_add (f := _), LinearMap.add_apply, hvz, hzz, zero_add, neg_eq_zero] at h1
    exact hT0 h1
  · simp only [map_add (f := _), LinearMap.add_apply, hvv, hvz, hzv, hzz]
    ring
  · intro i
    constructor
    · rw [map_add (f := _), hsym _ _ (D.sp.hyp_orthX i _).1, hsym _ _ (D.sp.hyp_orthz i).1, add_zero]
    · rw [map_add (f := _), hsym _ _ (D.sp.hyp_orthX i _).2, hsym _ _ (D.sp.hyp_orthz i).2, add_zero]

end GlobalTheory.IsoOrthHyp
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

theorem _root_.GlobalTheory.T.exists_smul_localWitt_free_tuple_gram : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → ∀ y : Fin (r + 1) → Fin n → Fv F v ⊗[F] E, LinearIndependent (Fv F v ⊗[F] E) y → gramR (Fv F v) σ J y = (gramE σ J (F0 P)).map (inclR (Fv F v)) → ∃ g : HA (Fv F v) σ J, g • ratTup (Fv F v) (F0 P) = y := by
  first | exact @GlobalTheory.LocalWittFree.exists_smul_ratTup_eq | exact GlobalTheory.LocalWittFree.exists_smul_ratTup_eq | (intros; apply GlobalTheory.LocalWittFree.exists_smul_ratTup_eq <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermitian_orbit_unique_lattice_integral_frames : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), 4 * r + 7 ≤ k → Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → P.PrimeTo → ∀ (A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E), (∀ a b, b < a → A a b = 0 ∧ A' a b = 0) → (∀ a, A a a = 1 ∧ A' a a = 1) → (∀ a b, A a b ∈ M.L.O ∧ A' a b ∈ M.L.O) → ∀ (f f' : Fin (r + 1) → V), (∀ j, f j = ∑ i, A i j • P.A.f i) → (∀ j, f' j = ∑ i, A' i j • P.B.f i) → ∀ d0 : LocNG.Datum P, (∃ t, LocNG.IsTermOver P d0 t) → ∀ d : LocNG.Datum P, (LocNG.Datum.Rel d0 d → ∃! Λ : Submodule M.L.O V, LocNG.IsTermOver P d (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) ∧ ¬ LocNG.BBne (H := H) (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r)) ∧ ((∃ t, LocNG.IsTermOver P d t) → LocNG.Datum.Rel d0 d) := by
  first | exact @GlobalTheory.HL.GoodFrames.main | exact GlobalTheory.HL.GoodFrames.main | (intros; apply GlobalTheory.HL.GoodFrames.main <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.StabLat

open Formalism.MainNotions.S.LocNG Formalism.MainNotions.KappaEndpoints Formalism.MainNotions.BridgeLemma

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r : ℕ}

theorem perpX_of (Fr : FrameD H r) {k : V} (h : ∀ a : Fin r, H.h k (Fr.f a.castSucc) = 0) :
    k ∈ H.perp (H.X Fr.f) := by
  intro x hx
  unfold HermSp.X at hx
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨a, rfl⟩ := hx; exact h a
  | zero => rw [H.h_herm 0 _, H.h_zero_left, map_zero]
  | add x y _ _ hx hy => rw [H.h_herm (x + y) _, H.h_add_left, map_add (f := _), ← H.h_herm, ← H.h_herm, hx, hy, add_zero]
  | smul c x _ hx => rw [H.h_herm (c • x) _, H.h_smul_left, map_mul, ← H.h_herm, hx, mul_zero]

theorem e_mem_X (Fr : FrameD H r) (a : Fin r) : Fr.e a ∈ H.X Fr.f :=
  Submodule.subset_span ⟨a, rfl⟩

theorem sub_prF_mem (Fr : FrameD H r) {y : V} (hy : y ∈ H.perp (H.X Fr.f)) : y - Fr.prF y ∈ H.X Fr.f := by
  have h0 : ∀ a, H.h y (Fr.e a) = 0 := fun a => hy _ (e_mem_X Fr a)
  have e : y - Fr.prF y = ∑ a, H.h y (Fr.es a) • Fr.e a := by
    unfold FrameD.prF
    simp only [h0, zero_smul, Finset.sum_const_zero, sub_zero, sub_sub_cancel]
  rw [e]
  exact Submodule.sum_mem _ (fun a _ => Submodule.smul_mem _ _ (e_mem_X Fr a))

theorem prF_mem_perp (Fr : FrameD H r) (y : V) : Fr.prF y ∈ H.perp (H.X Fr.f) :=
  perpX_of Fr (fun a => ng_prF_e (Fr := Fr) y a)

theorem mkW_eq (Fr : FrameD H r) {x y : ↥(H.perp (H.X Fr.f))} (h : (x : V) - y ∈ H.X Fr.f) :
    H.mkW Fr.f x = H.mkW Fr.f y := by
  unfold HermSp.mkW
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  exact h

theorem prF_mem_LamStd (Fr : FrameD H r) {L : Submodule M.L.O (H.Wb Fr.f)} {y : V}
    (hy : y ∈ H.perp (H.X Fr.f)) (hyL : H.mkW Fr.f ⟨y, hy⟩ ∈ L) : Fr.prF y ∈ Fr.LamStd L := by
  apply Submodule.subset_span
  refine ⟨fun a => ?_, fun a => ?_, ⟨Fr.prF (Fr.prF y), prF_mem_perp Fr _⟩, rfl, ?_⟩
  · rw [ng_prF_es]; exact M.L.O.zero_mem
  · rw [ng_prF_e]; exact M.L.O.zero_mem
  · have e : H.mkW Fr.f ⟨Fr.prF (Fr.prF y), prF_mem_perp Fr _⟩ = H.mkW Fr.f ⟨y, hy⟩ := by
      apply mkW_eq
      have h1 := sub_prF_mem Fr hy
      have h2 := sub_prF_mem Fr (prF_mem_perp Fr y)
      have : Fr.prF (Fr.prF y) - y = -((y - Fr.prF y) + (Fr.prF y - Fr.prF (Fr.prF y))) := by abel
      rw [show ((⟨Fr.prF (Fr.prF y), prF_mem_perp Fr _⟩ : ↥(H.perp (H.X Fr.f))) : V) = Fr.prF (Fr.prF y) from rfl,
        show ((⟨y, hy⟩ : ↥(H.perp (H.X Fr.f))) : V) = y from rfl, this]
      exact Submodule.neg_mem _ (Submodule.add_mem _ h1 h2)
    rw [e]; exact hyL

variable {P : FPair H r}

theorem h_add_right' (k u y : V) : H.h k (u + y) = H.h k u + H.h k y := by
  rw [H.h_herm (u + y) k, H.h_add_left, map_add (f := _), ← H.h_herm, ← H.h_herm]

theorem cls_mem {d : Datum P} {t : Term V M r} (ht : IsTermOver P d t) {k : V} (hk : k ∈ t.abelian₂)
    (hkp : k ∈ H.perp (H.X P.A.f)) : H.mkW P.A.f ⟨k, hkp⟩ ∈ d.L := by
  have ht' := ht
  obtain ⟨_, _, ⟨n, hn, -, hL⟩, _, _⟩ := ht'
  have hN := mem_NSet_of_mem_N P.A hn
  refine ((d.hL.2.1 ⟨k, hkp⟩).2) (fun y hyL => ?_)
  have hy := y.2
  have hyL' : H.mkW P.A.f ⟨(y : V), hy⟩ ∈ d.L := hyL
  have h0 := prF_mem_LamStd P.A hy hyL'
  have hny : n (P.A.prF y) ∈ t.abelian₂ := by rw [hL]; exact ⟨_, h0, rfl⟩
  have hint := ng_term_int ht hk hny
  have hu : n (P.A.prF y) - y ∈ H.X P.A.f := by
    have h1 := hN.2.2 _ (prF_mem_perp P.A (y : V))
    have h2 := sub_prF_mem P.A hy
    have : n (P.A.prF y) - y = (n (P.A.prF y) - P.A.prF y) - ((y : V) - P.A.prF y) := by abel
    rw [this]; exact Submodule.sub_mem _ h1 h2
  have e : n (P.A.prF y) = (n (P.A.prF y) - y) + y := by abel
  rw [e, h_add_right', hkp _ hu, zero_add] at hint
  exact hint

theorem mem_of_cls (hP : P.PrimeTo) {d : Datum P} {t : Term V M r} (ht : IsTermOver P d t) {k : V}
    (ho : NgOrth P k) (hkL : H.mkW P.A.f ⟨k, ng_orth_perp P.A ho.1⟩ ∈ d.L) : k ∈ t.abelian₂ := by
  have ht' := ht
  obtain ⟨_, _, ⟨n, hn, -, hL⟩, _, _⟩ := ht'
  have hN := mem_NSet_of_mem_N P.A hn
  have hkp := ng_orth_perp P.A ho.1
  have h0 := prF_mem_LamStd P.A hkp hkL
  have hny : n (P.A.prF k) ∈ t.abelian₂ := by rw [hL]; exact ⟨_, h0, rfl⟩
  obtain ⟨m0, hm0, hk', hko⟩ := ng_term_split hP ht hny
  have hXle : H.X P.A.f ≤ Submodule.span E (Set.range (Sum.elim P.A.f P.B.f)) := by
    unfold HermSp.X
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact Submodule.subset_span ⟨Sum.inl a.castSucc, rfl⟩
  have hx : n (P.A.prF k) - k ∈ H.X P.A.f := by
    have h1 := hN.2.2 _ (prF_mem_perp P.A k)
    have h2 := sub_prF_mem P.A hkp
    have : n (P.A.prF k) - k = (n (P.A.prF k) - P.A.prF k) - (k - P.A.prF k) := by abel
    rw [this]; exact Submodule.sub_mem _ h1 h2
  have hz : k - (n (P.A.prF k) - m0) = 0 := by
    refine ng_zero (H := H) (Sum.elim P.A.f P.B.f) ?_ ?_ ?_
    · rw [ng_gram_base]
      exact IsUnit.mul (IsUnit.pow _ isUnit_one.neg) (ng_G_unit (by
        intro h0
        obtain ⟨_, y, _, hy⟩ := hP.2.1
        rw [h0, zero_mul] at hy
        have := Formalism.MainNotions.LocalModelPeriodLattices.nontrivial_E M.L
        exact zero_ne_one hy))
    · have e : k - (n (P.A.prF k) - m0) = m0 - (n (P.A.prF k) - k) := by abel
      rw [e]
      exact Submodule.sub_mem _ (ng_span_base ht hm0) (hXle hx)
    · rintro (b | b)
      · rw [Sum.elim_inl, h_sub_left, ho.1, hko.1, sub_zero]
      · rw [Sum.elim_inr, h_sub_left, ho.2, hko.2, sub_zero]
  rw [sub_eq_zero.1 hz]; exact hk'

theorem complementUnitary_isUnitary_fixes_frames {g : V ≃ₗ[E] V} (hg : g ∈ P.UW0) :
    IsUnitary H g ∧ ∀ b, g (P.A.f b) = P.A.f b ∧ g (P.B.f b) = P.B.f b := by
  unfold FPair.UW0 at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one => exact ⟨fun x y => rfl, fun b => ⟨rfl, rfl⟩⟩
  | mul x y _ _ hx hy =>
    refine ⟨fun u v => ?_, fun b => ⟨?_, ?_⟩⟩
    · show H.h (x (y u)) (x (y v)) = H.h u v
      rw [hx.1, hy.1]
    · show x (y (P.A.f b)) = P.A.f b
      rw [(hy.2 b).1, (hx.2 b).1]
    · show x (y (P.B.f b)) = P.B.f b
      rw [(hy.2 b).2, (hx.2 b).2]
  | inv x _ hx =>
    have e : ∀ u, x ((x⁻¹ : V ≃ₗ[E] V) u) = u := fun u => LinearEquiv.apply_symm_apply x u
    refine ⟨fun u v => ?_, fun b => ⟨?_, ?_⟩⟩
    · rw [← hx.1, e, e]
    · conv_lhs => rw [← (hx.2 b).1]
      exact LinearEquiv.symm_apply_apply x _
    · conv_lhs => rw [← (hx.2 b).2]
      exact LinearEquiv.symm_apply_apply x _

theorem img_le (hP : P.PrimeTo) {d : Datum P} {t : Term V M r} (ht : IsTermOver P d t) {g : V ≃ₗ[E] V}
    (hU : IsUnitary H g) (hfix : ∀ b, g (P.A.f b) = P.A.f b ∧ g (P.B.f b) = P.B.f b)
    (hmov : ∀ x y : ↥(H.perp (H.X P.A.f)), (y : V) = g x → H.mkW P.A.f x ∈ d.L → H.mkW P.A.f y ∈ d.L) :
    img g t.abelian₂ ≤ t.abelian₂ := by
  have hf := ng_term_f ht
  have hM : Submodule.span M.L.O (Set.range (Sum.elim t.f t.f')) ≤ t.abelian₂ := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rcases j with b | b
    · exact (hf b).1
    · exact (hf b).2
  have hfixME : ∀ x ∈ Submodule.span E (Set.range (Sum.elim P.A.f P.B.f)), g x = x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      rcases j with b | b
      · exact (hfix b).1
      · exact (hfix b).2
    | zero => exact map_zero g
    | add x y _ _ hx hy => rw [map_add (f := _), hx, hy]
    | smul c x _ hx => rw [map_smul, hx]
  rintro _ ⟨v, hv, rfl⟩
  obtain ⟨m0, hm0, hk, hko⟩ := ng_term_split hP ht hv
  show g v ∈ t.abelian₂
  have e : g v = m0 + g (v - m0) := by
    rw [map_sub, hfixME m0 (ng_span_base ht hm0)]; abel
  rw [e]
  refine t.abelian₂.add_mem (hM hm0) ?_
  have hgo : NgOrth P (g (v - m0)) := by
    constructor
    · intro b; rw [← (hfix b).1, hU, hko.1]
    · intro b; rw [← (hfix b).2, hU, hko.2]
  apply mem_of_cls hP ht hgo
  exact hmov ⟨v - m0, ng_orth_perp P.A hko.1⟩ _ rfl (cls_mem ht hk _)

theorem stab_le_aut : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → P.PrimeTo → ∀ (d : LocNG.Datum P) (τ : Term V M r), LocNG.IsTermOver P d τ → LocNG.Datum.Stab d ≤ LocNG.Aut τ.abelian₂ := by
  intro F _ _ _ E _ _ _ _ M _ V _ _ H r k P _ _ hP d τ ht
  unfold Datum.Stab
  rw [Subgroup.closure_le]
  rintro g ⟨hg, hmv⟩
  obtain ⟨hU, hfix⟩ := complementUnitary_isUnitary_fixes_frames hg
  rw [SetLike.mem_coe, ng_mem_Aut]
  have e : ∀ u, g ((g⁻¹ : V ≃ₗ[E] V) u) = u := fun u => LinearEquiv.apply_symm_apply g u
  have h1 := img_le hP ht hU hfix (fun x y hxy hx => (hmv.1 x y hxy).1 hx)
  have hU' : IsUnitary H g⁻¹ := fun u v => by rw [← hU, e, e]
  have hfix' : ∀ b, (g⁻¹ : V ≃ₗ[E] V) (P.A.f b) = P.A.f b ∧ (g⁻¹ : V ≃ₗ[E] V) (P.B.f b) = P.B.f b := fun b => by
    constructor
    · conv_lhs => rw [← (hfix b).1]
      exact LinearEquiv.symm_apply_apply g _
    · conv_lhs => rw [← (hfix b).2]
      exact LinearEquiv.symm_apply_apply g _
  have h2 := img_le hP ht hU' hfix' (fun x y hxy hx => by
    refine (hmv.1 y x ?_).2 hx
    rw [hxy]; exact (e x).symm)
  refine le_antisymm h1 ?_
  have h3 := ng_img_mono g h2
  rwa [← ng_img_mul, mul_inv_cancel, ng_img_one] at h3

end GlobalTheory.HL.StabLat
end
