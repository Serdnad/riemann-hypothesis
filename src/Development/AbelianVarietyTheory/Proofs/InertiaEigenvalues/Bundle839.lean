module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle017
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.ExpDefs
public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle029
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle013
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle601
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle650
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle780
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle343
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
public import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle722
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeDiscPeriodDataOfAcrisPeriods
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle684
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle836
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle768
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle794
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle738
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle744
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1827
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2161
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPlaceModelPlaceMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1083
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle554
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle067
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle837
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

section

open Formalism.BasicNotions GlobalTheory.HeightCounting

theorem _root_.GlobalTheory.T.good_idempotent_irreducible_character_generic_sum_ne_zero : ∀ (D : D7), GrpSide D → ∀ [Fintype (G0g D.nd)] (U : Subgroup (G0g D.nd)) [Fintype U], U = Formalism.L2.NX.Uup (fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.host.g kv.1) D.R.r → ∀ ψ : U →* ℂˣ, Formalism.L2.NX.IsStdGeneric (fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.host.g kv.1) D.R.r ψ → 2 ≤ D.R.r → ∀ χ : G0g D.nd → ℂ, Formalism.L2.NT.IsIrrChar χ → ∑ g, D.ntypes.e0.coeff g * χ g = χ 1 → ∑ u : U, χ u * (((ψ u)⁻¹ : ℂˣ) : ℂ) ≠ 0 := by
  first | exact @GlobalTheory.WhittakerMeets.sum_ne_zero | exact GlobalTheory.WhittakerMeets.sum_ne_zero | (intros; apply GlobalTheory.WhittakerMeets.sum_ne_zero <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.groupAlgebraCentre_keeps_typeSpaces_at_localisations : ∀ (D : D7) (M : MtFam D), AVTied D M → GlobalTheory.HeightCounting.Up.CenLoc D M → OnMtPreservesTypeV D := by
  first | exact @GlobalTheory.CenKeepsTypeLoc.main | exact GlobalTheory.CenKeepsTypeLoc.main | (intros; apply GlobalTheory.CenKeepsTypeLoc.main <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem matThm_holds : MatThm :=
  GlobalTheory.T.padicMonodromyMatrixForm_of_induction_cases GlobalTheory.T.deRham_iff_framed_galois_representation GlobalTheory.T.lubinTateTwistTotalWeightZero_proof GlobalTheory.T.weightZero_potentiallySemistable_of_sen_theorem GlobalTheory.T.potentially_semistable_reducible_unramified_split GlobalTheory.T.monodromy_irreducible_elementary_weightModification

end GlobalTheory.PMon
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.InertHeckeCmp.satU_eq : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (π : NG.AutRep L n) (U : Submodule ℂ (UA L n → ℂ)), Dict F π U → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ), NG.SatAt π Dv α → ∀ α0 : Fin (n / 2) → ℂˣ, HasSatAt U w Dv.σw Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) α0 → ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n), Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) h α = Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) h (fun i => (α0 i : ℂ)) := by
  intro L _ _ _ n F π U hD v w hw Dv α hα α0 hα0 h hh
  rcases Nat.eq_zero_or_pos (n / 2) with h2 | h2
  · congr 1
    funext i
    exact absurd i.2 (by omega)
  have hn : 0 < n := by omega
  obtain ⟨b, hbK, hbJ, p, hp, σ, hcomp, hsat⟩ := hα0
  obtain ⟨hs, hsurj⟩ := GlobalTheory.T.inert_frame_conj_extends_and_frame_map_surjective L n hn v w hw Dv b hbK hbJ p hp
  obtain ⟨φ, hφU, hφ0, hfix, hAe⟩ := GlobalTheory.T.exists_lift_satake_vector_local_hecke_eigen L n F π U hD v w hw Dv α hα hs b hbK hbJ p hp
  have e1 := (hAe h hh).symm.trans (GlobalTheory.T.satake_parameters_unramified_unitary L n U hD.1 w Dv.σw Dv.ϖ _ Dv.unram p hsurj σ hcomp α0 hsat φ hφU hfix h hh)
  rw [← sub_eq_zero, ← sub_smul] at e1
  exact sub_eq_zero.1 ((smul_eq_zero.1 e1).resolve_right hφ0)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_breuilKisin_frame_height_of_jumps_le : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (C : Core l), C.InvdR → ∀ (N N₀ d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (F : Frame bk N d ρ), F.IsDR → ∀ H : Hodge C (bk.ev bk.E) (fun g => (ρ g).map (zOm l)) K, (∀ i, |(H.p i : ℤ) - H.q| ≤ N₀) → ∃ F₀ : Frame bk N₀ d ρ, F₀.T = F.T ∧ F₀.ε = F.ε := by
  first | (exact @GlobalTheory.BKLim.Lower.exists_frame_of_jumps_le) | (exact GlobalTheory.BKLim.Lower.exists_frame_of_jumps_le) | (intros; apply GlobalTheory.BKLim.Lower.exists_frame_of_jumps_le  <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.WPre

theorem map_smul_hom {R S F : Type*} [CommRing R] [CommRing S] [FunLike F R S] [RingHomClass F R S] {m n : Type*}
    (f : F) (c : R) (M : Matrix m n R) : (c • M).map f = f c • M.map f :=
  Matrix.ext fun i j => by simp

theorem smul_cancel {R : Type*} [CommRing R] {m n : Type*} {c : R} (hc : IsUnit c) {M M' : Matrix m n R}
    (h : c • M = c • M') : M = M' := by
  ext i j
  have := congrFun (congrFun h i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  exact hc.mul_left_cancel this

end GlobalTheory.BKLim.WPre

namespace GlobalTheory.BKLim


open GlobalTheory.BKLim.WPre in
theorem exists_pre_of_wseed : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])), (∀ g, IsUnit (ρ g)) → ∀ (s : WSeed bk d ρ τ), ∃ (N : ℕ) (F : Pre bk N d ρ) (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Z : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)), Y.map (inclW l) = inclW l τ ^ s.N • F.T ∧ IsUnit Z ∧ ∀ i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev i → s.W * Z.map i = Y.map bk.iA := by
  intro l _ K bk τ hτ d ρ hρ s
  classical
  obtain ⟨Y, Z, b, A, A', hYu, hZu, hWZ, hAA', hφY⟩ := GlobalTheory.T.exists_finiteHeight_breuilKisin_lattice_semistable l K bk τ hτ d ρ hρ s
  obtain ⟨htu, -, -, hστ⟩ := GlobalTheory.BSP.isUnit_inclW_of_isPer l K bk τ hτ
  obtain ⟨hmaps, hgal, -, h0, -, -⟩ := GlobalTheory.BSP.exists_discMaps l K bk
  obtain ⟨i0, hi0⟩ := hmaps bk.S (Ainf l) bk.ev X (bk.ev X) bk.ρ₀ bk.ρ₀ 1 h0 (by rw [pow_one]) (by rw [pow_one])
  have hinj : Function.Injective bk.iA := GlobalTheory.BSP.SeedAsm.iA_injective bk
  obtain ⟨u, hu⟩ := htu
  set n := s.N with hn
  set t := inclW l τ with ht
  set e := bk.evW bk.E with he
  set T : Matrix (Fin d) (Fin d) (WCb l) := (u⁻¹ ^ n : (WCb l)ˣ) • Y.map (inclW l) with hT
  have hYT : Y.map (inclW l) = t ^ n • T := by
    rw [hT, Units.smul_def, smul_smul, ← hu, Units.val_pow_eq_pow_val, ← mul_pow, Units.mul_inv, one_pow, one_smul]
  have htn : IsUnit (t ^ n) := by rw [← hu]; exact (Units.isUnit u).pow n

  have hft : frobW l t = e * t := by
    rw [ht, GlobalTheory.Prism.frobW_inclW, hτ.1, map_mul]; rfl
  have hφT : e ^ n • T.map (frobW l) = T * A.map bk.evW := by
    have h1 := congrArg (fun M => Matrix.map M (inclW l)) hφY
    simp only [Matrix.map_mul] at h1
    have h2 : (Y.map WittVector.frobenius).map (inclW l) = (Y.map (inclW l)).map (frobW l) := by
      ext i j; simp [GlobalTheory.Prism.frobW_inclW]
    rw [h2, hYT, show (A.map bk.ev).map (inclW l) = A.map bk.evW from rfl] at h1
    apply smul_cancel htn
    calc t ^ n • e ^ n • T.map (frobW l) = (t ^ n • T).map (frobW l) := by
          rw [map_smul_hom, map_pow, hft, mul_pow, mul_comm, smul_smul]
      _ = t ^ n • (T * A.map bk.evW) := by rw [h1, Matrix.smul_mul]

  have hfix : ∀ g : ↥(GK K), bk.FixFlat g → zW (ρ g) * T.map (galW l (g : GQ l)) = T := by
    intro g hg
    obtain ⟨G, hG⟩ := hgal bk.ρ₀ h0 (g : GQ l)
    obtain ⟨hGfix, hGW⟩ := GlobalTheory.T.semistable_periods_galois_fixing_flat l K bk τ hτ d ρ hρ s g hg G hG
    set R := (ρ g).map (bk.iA.comp (algebraMap ℤ_[l] (Ainf l))) with hR
    have hGZ : (Z.map i0).map G = Z.map i0 := by
      exact Matrix.ext fun i j => hGfix i0 hi0 _
    have hYG : (Y.map (Per.σA (g : GQ l))).map bk.iA = (Y.map bk.iA).map G := by
      exact Matrix.ext fun i j => (hG.ext _).symm
    have hA1 : (τ ^ n • ((ρ g).map (algebraMap ℤ_[l] (Ainf l)) * Y.map (Per.σA (g : GQ l)))).map bk.iA =
        (Per.σA (g : GQ l) τ ^ n • Y).map bk.iA := by
      rw [map_smul_hom, map_smul_hom, Matrix.map_mul, hYG, ← hWZ i0 hi0, Matrix.map_mul, hGZ, map_pow, map_pow,
        show ((ρ g).map (algebraMap ℤ_[l] (Ainf l))).map bk.iA = R from Matrix.ext fun i j => rfl, ← Matrix.mul_assoc,
        ← Matrix.smul_mul, hGW, Matrix.smul_mul, ← hG.ext]
    have hA2 : τ ^ n • ((ρ g).map (algebraMap ℤ_[l] (Ainf l)) * Y.map (Per.σA (g : GQ l))) =
        Per.σA (g : GQ l) τ ^ n • Y := by
      refine Matrix.ext fun i j => hinj ?_
      have := congrFun (congrFun hA1 i) j
      simpa only [Matrix.map_apply] using this
    have hA3 := congrArg (fun M => Matrix.map M (inclW l)) hA2
    simp only [map_smul_hom, Matrix.map_mul, map_pow] at hA3
    have hz : ((ρ g).map (algebraMap ℤ_[l] (Ainf l))).map (inclW l) = zW (ρ g) := by
      exact Matrix.ext fun i j => (inclWA l).commutes _
    have hg' : (Y.map (Per.σA (g : GQ l))).map (inclW l) = (Y.map (inclW l)).map (galW l (g : GQ l)) := by
      exact Matrix.ext fun i j => (GlobalTheory.Prism.galW_inclW _ _).symm
    rw [hz, hg', hYT, map_smul_hom, map_pow, ht, GlobalTheory.Prism.galW_inclW] at hA3
    have hsu : IsUnit (inclW l (Per.σA (g : GQ l) τ) ^ n) := (hστ _).pow n
    apply smul_cancel (htn.mul hsu)
    have e1 : (t ^ n * inclW l (Per.σA (g : GQ l) τ) ^ n) • (zW (ρ g) * T.map (galW l (g : GQ l))) =
        t ^ n • (zW (ρ g) * (inclW l (Per.σA (g : GQ l) τ) ^ n • T.map (galW l (g : GQ l)))) := by
      rw [Matrix.mul_smul, smul_smul]
    have e2 : (t ^ n * inclW l (Per.σA (g : GQ l) τ) ^ n) • T = inclW l (Per.σA (g : GQ l) τ) ^ n • t ^ n • T := by
      rw [smul_smul, mul_comm]
    rw [e1, e2]
    exact hA3
  refine ⟨n + b, Pre.mk T ?_ (bk.E ^ b • A) (bk.E ^ (2 * n) • A') ?_ ?_ hfix, Y, Z, hYT, hZu, hWZ⟩
  · rw [hT]; exact hYu.smul _
  · rw [Matrix.smul_mul, Matrix.mul_smul, hAA', smul_smul, smul_smul, ← pow_add, ← pow_add]
    congr 2; ring
  · rw [map_smul_hom, Matrix.mul_smul, ← hφT, pow_add, mul_comm, ← smul_smul, map_pow]

end GlobalTheory.BKLim
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_deRhamFrame_limitLattice_breuilKisinTower : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Frame bk N (tw.d' n) fun g => (tw.ρ' n g).val), (∀ n, (F n).IsDR) → ∃ F₀ : Frame bk N d (fun g => (ρ g).val), F₀.IsDR ∧ ((∀ n, (F n).IsCr) → F₀.IsCr) ∧ ∃ r, ∀ n, ∃ m, n ≤ m ∧ Link bk F₀.T (F m).T (tw.Pi m) n r := by
  first | (exact @GlobalTheory.BKLim.limit_frame_exists) | (exact GlobalTheory.BKLim.limit_frame_exists) | (intros; apply GlobalTheory.BKLim.limit_frame_exists  <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_comparison_matrix_prismCoproduct : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s), bk.IsPer τ → (∀ g, IsUnit (ρ g)) → ∀ (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)), ∃ ε : Matrix (Fin d) (Fin d) En.Q.A, ht.Rel (BK.hf En.inl X) En.inl En.inr (ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀)) := by
  first | exact @GlobalTheory.BSP.Height.exists_rel_env | exact GlobalTheory.BSP.Height.exists_rel_env | (intros; apply GlobalTheory.BSP.Height.exists_rel_env <;> assumption)
end

section

open ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.RecT

namespace GlobalTheory.RecT

theorem geometricLemma_holds : GlobalTheory.Published.GeometricLemma :=
  GlobalTheory.geometricLemma_of_filtration GlobalTheory.bernsteinZelevinskyFiniteness_holds GlobalTheory.geometricLemmaFiltration_holds

theorem good_toral_of_isSubquotient_prodIrr : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (t : ℕ) (y : Fin t → IrrGL (k := k)) (x : IrrGL (k := k)) (hd : ∑ i, (y i).1 = x.1),
    IsSubquotient x.rep (prodIrr y hd) → (Good x → ∀ i, Good (y i)) ∧ (Toral x → ∀ i, Toral (y i)) ∧
      ((∀ i, Good (y i)) → Good x) ∧ ((∀ i, Toral (y i)) → Toral x) := by
  intro k _ _ _ _ t y x hd hsq
  have hG := geometricLemma_holds
  have hBZ := GlobalTheory.bernsteinZelevinskyFiniteness_holds
  choose s hs using fun i => GlobalTheory.CompanionTheory.Hypotheses₂.TD.exists_hasSupport hBZ hG (y i)
  have hx : HasSupport x.rep (∑ i, s i) :=
    GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr hs x.2.rep.irr hsq

  have down : ∀ P : IrrGL (k := k) → Prop, (∃ u, HasSupport x.rep u ∧ ∀ z ∈ u, P z) →
      ∀ i, ∃ u, HasSupport (y i).rep u ∧ ∀ z ∈ u, P z := by
    rintro P ⟨u, hu, hP⟩ i
    have := GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique hG hBZ hu hx
    exact ⟨s i, hs i, fun z hz => hP z (this ▸ Multiset.mem_sum.2 ⟨i, Finset.mem_univ _, hz⟩)⟩

  have up : ∀ P : IrrGL (k := k) → Prop, (∀ i, ∃ u, HasSupport (y i).rep u ∧ ∀ z ∈ u, P z) →
      ∃ u, HasSupport x.rep u ∧ ∀ z ∈ u, P z := by
    intro P h
    choose u hu hP using h
    refine ⟨∑ i, u i, GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr hu x.2.rep.irr hsq, fun z hz => ?_⟩
    obtain ⟨i, -, hz⟩ := Multiset.mem_sum.1 hz
    exact hP i z hz
  exact ⟨down _, down _, up _, up _⟩

end GlobalTheory.RecT
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open scoped TensorProduct

namespace GlobalTheory.RedHalfDrop

variable {D : D7}

theorem toEAf_cA_sig (a : AE D) :
    toEAf D (cA D a) = Formalism.UG.sigR D.sp.cm.sig (Af D.host.F) (toEAf D a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp only [RingHom.map_zero]
  | add a b ha hb => simp only [RingHom.map_add (f := _), ha, hb]
  | tmul y e => rfl

theorem int_idemAt {P : Finset (Pl D.host.E)} (h : SplitSet P) {PP : Pl D.host.E} (hPP : PP ∈ P) :
    toEAf D (idemAt PP) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  obtain ⟨hu, -⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D _ PP (h.isIdemAt hPP)
  exact hu

theorem int_cA_idemAt {P : Finset (Pl D.host.E)} (h : SplitSet P) {PP : Pl D.host.E} (hPP : PP ∈ P) :
    toEAf D (cA D (idemAt PP)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  rw [toEAf_cA_sig]
  exact GlobalTheory.ResConjPlace.conj_mem_int _ (int_idemAt h hPP)

theorem resS_eq_zero_of_mul {e a : AE D} {PP : Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt e PP)
    (ha : toEAf D a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (h0 : e * a = 0) :
    resS D.host.F PP ⟨toEAf D a, ha⟩ = 0 := by
  obtain ⟨hu, h1⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D e PP he
  have hm : (⟨toEAf D e, hu⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) *
      ⟨toEAf D a, ha⟩ = 0 :=
    Subtype.ext (by show toEAf D e * toEAf D a = 0; rw [← map_mul, h0, map_zero])
  have h2 := congrArg (resS D.host.F PP) hm
  rwa [map_mul, h1, one_mul, map_zero] at h2

theorem subring_hom_dite_sub_mul_eq_of_kernel {R k : Type} [CommRing R] [CommRing k] (O : Subring R) (f : O →+* k) (x c : R) (hx : x ∈ O)
    (hc : c ∈ O) (h0 : f ⟨c, hc⟩ = 0) [Decidable (x - c * x ∈ O)] [Decidable (x ∈ O)] :
    (if h : x - c * x ∈ O then f ⟨x - c * x, h⟩ else 0) = if h : x ∈ O then f ⟨x, h⟩ else 0 := by
  have hm : x - c * x ∈ O := sub_mem hx (mul_mem hc hx)
  rw [dite_eq_left hm, dite_eq_left hx]
  have e : (⟨x - c * x, hm⟩ : O) = ⟨x, hx⟩ - ⟨c, hc⟩ * ⟨x, hx⟩ := rfl
  rw [e, map_sub, map_mul, h0, zero_mul, sub_zero]

theorem redM_sub_smul (PP : Pl D.host.E) {b a : ℕ} {N : Matrix (Fin b) (Fin a) (EAf D)} (hN : IsIntM N) {c : EAf D}
    (hc : c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (h0 : resS D.host.F PP ⟨c, hc⟩ = 0) :
    redM PP (N - c • N) = redM PP N := by
  ext i j
  unfold redM
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  exact subring_hom_dite_sub_mul_eq_of_kernel _ (resS D.host.F PP) _ _ (hN i j) hc h0

theorem frMapO_smul_eq {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e : AE D)
    (x : WO S T) : frMapO S T βS βT (e • x) = toEAf D e • frMapO S T βS βT x := by
  unfold frMapO
  have : (e • x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (toEAf D) = toEAf D e • x.map (toEAf D) :=
    Matrix.ext fun i j => by simp [Matrix.smul_apply, map_mul]
  rw [this, Matrix.mul_smul, Matrix.smul_mul]

theorem frMapAdj_smul_eq {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e : AE D)
    (x : WO S T) : frMapAdj S T βS βT (e • x) = toEAf D (cA D e) • frMapAdj S T βS βT x := by
  unfold frMapAdj
  have h1 : ((e • x : WO S T) : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D) =
      cA D e • (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D) :=
    Matrix.ext fun i j => by simp [Matrix.smul_apply, map_mul]
  have h2 : ∀ M : Matrix (Fin S.rank) (Fin T.rank) (AE D),
      (cA D e • M).map (toEAf D) = toEAf D (cA D e) • M.map (toEAf D) :=
    fun M => Matrix.ext fun i j => by simp [Matrix.smul_apply, map_mul]
  rw [h1, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, h2, Matrix.mul_smul, Matrix.smul_mul]

theorem redM_drop : ∀ {D : D7} {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) {Pg Qa Qb : Finset (Pl D.host.E)}, PlacesOK Pg Qa → Qb ⊆ Qa → ∀ {x : WO S T}, IsHalf (halfIdem Pg Qa) x → IsIntM (frMapAdj S T βS βT x) → IsIntM (frMapO S T βS βT x) → (∀ PP ∈ Pg, redM PP (frMapAdj S T βS βT x) = redM PP (frMapAdj S T βS βT (halfIdem Pg Qb • x))) ∧ (∀ PP ∈ Qb, redM PP (frMapO S T βS βT x) = redM PP (frMapO S T βS βT (halfIdem Pg Qb • x))) := by
  intro D S T βS βT Pg Qa Qb hP hQ x hx h1 h2
  obtain ⟨P, hPg, hQa, hS⟩ := hP.split
  have hab : halfIdem Pg Qa = halfIdem Pg Qb + idem (Qa \ Qb) := by
    unfold halfIdem idem
    rw [← Finset.sum_sdiff hQ]
    ring
  have hxx : (halfIdem Pg Qb + idem (Qa \ Qb)) • x = x := by
    rw [← hab]
    ext i j
    exact hx i j
  have hsub : ∀ P' ∈ Qa \ Qb, P' ∈ P := fun P' hP' => hQa (Finset.sdiff_subset hP')
  constructor
  · intro PP hPP
    have e1 := frMapAdj_smul_eq βS βT (halfIdem Pg Qb + idem (Qa \ Qb)) x
    rw [hxx, map_add (f := _), map_add (f := _), add_smul] at e1
    have e2 : frMapAdj S T βS βT (halfIdem Pg Qb • x) =
        frMapAdj S T βS βT x - toEAf D (cA D (idem (Qa \ Qb))) • frMapAdj S T βS βT x := by
      rw [frMapAdj_smul_eq]
      exact eq_sub_of_add_eq e1.symm
    have hint : toEAf D (cA D (idem (Qa \ Qb))) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
      unfold idem

      rw [map_sum, map_sum]
      exact sum_mem fun P' hP' => int_cA_idemAt hS (hsub P' hP')
    have hz : resS D.host.F PP ⟨_, hint⟩ = 0 := resS_eq_zero_of_mul (hS.isIdemAt (hPg hPP)) hint (by
      unfold idem

      rw [map_sum, Finset.mul_sum]
      exact Finset.sum_eq_zero fun P' hP' => hS.mul_conj (hPg hPP) (hsub P' hP'))
    rw [e2, redM_sub_smul PP h1 hint hz]
  · intro PP hPP
    have e1 := frMapO_smul_eq βS βT (halfIdem Pg Qb + idem (Qa \ Qb)) x
    rw [hxx, map_add (f := _), add_smul] at e1
    have e2 : frMapO S T βS βT (halfIdem Pg Qb • x) =
        frMapO S T βS βT x - toEAf D (idem (Qa \ Qb)) • frMapO S T βS βT x := by
      rw [frMapO_smul_eq]
      exact eq_sub_of_add_eq e1.symm
    have hint : toEAf D (idem (Qa \ Qb)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
      unfold idem

      rw [map_sum]
      exact sum_mem fun P' hP' => int_idemAt hS (hsub P' hP')
    have hz : resS D.host.F PP ⟨_, hint⟩ = 0 := resS_eq_zero_of_mul (hS.isIdemAt (hQa (hQ hPP))) hint (by
      unfold idem
      rw [Finset.mul_sum]
      exact Finset.sum_eq_zero fun P' hP' => hS.mul_eq_zero (hQa (hQ hPP)) (hsub P' hP')
        fun e => (Finset.mem_sdiff.1 hP').2 (e ▸ hPP))
    rw [e2, redM_sub_smul PP h2 hint hz]

end GlobalTheory.RedHalfDrop
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.filtration_jumps_breuilKisin_subset_galoisJumps : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → IsCrisCmp I jB → IsHoriz (thetaW a LL) ϖ (sQ l) P jB → (∀ m ∈ P.M, P.EN m ∈ P.Man) → ∀ U : Set ℤ, (∀ τ, JumpsInV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ τ U) → P.jumps ⊆ U := by
  first | exact @GlobalTheory.JumpsOfM.main | exact GlobalTheory.JumpsOfM.main | (intros; apply GlobalTheory.JumpsOfM.main <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.galoisClass_of_monodromy_eq_zero : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat ↥(OL LL) ↥LL.1 l e a ι η H) (T : QLat LL) (R : GalDat (thetaW a LL) ϖ (sQ l) D T) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → η < H → 8 * H + 1 < l → ∀ y ∈ D.Y, D.Mon y = 0 → ∀ c : ℕ, (l : ↥LL.1) ^ c • D.zeta y ∈ D.MM → ∃ κ₁ ∈ latticeFiniteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.L, R.ClassOf ((l : ↥LL.1) ^ c • y) κ₁ := by
  first | exact @GlobalTheory.BKGal.classOf_of_mon_eq_zero | exact GlobalTheory.BKGal.classOf_of_mon_eq_zero | (intros; apply GlobalTheory.BKGal.classOf_of_mon_eq_zero <;> assumption)
end
