module

public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle547
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle546
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle255
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle548
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle501
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle048
public import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle219
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle163
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle159
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle022
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle023
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle181
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical

namespace GlobalTheory.Per.CharJumps

section General

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem ιV_act (g : G) (w : V ⊗[Qp] B) :
    ιV PD (LL := LL) (V := V) (actVB PD ρ g w) = actVdR PD ρ g (ιV PD (LL := LL) (V := V) w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    simp [ιV, actVB, actVdR, AlgebraTensorModule.map_tmul, PD.ι_comm]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem ιV_mem_DdR {w : V ⊗[Qp] B} (hw : w ∈ Dcris PD ρ) :
    ιV PD (LL := LL) (V := V) w ∈ DdR PD ρ := by
  simp only [Dcris, DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero] at hw ⊢
  intro g
  rw [← ιV_act, hw g]

theorem ιV_mul (a : K₀) (w : V ⊗[Qp] B) :
    ιV PD (LL := LL) (V := V) (mulVB (B := B) (V := V) (LL := LL) a w) =
      mulVdR (BdR := BdR) (V := V) (LL := LL) (algebraMap K₀ K a) (ιV PD (LL := LL) (V := V) w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    simp [ιV, mulVB, mulVdR, AlgebraTensorModule.map_tmul, ← IsScalarTower.algebraMap_apply]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem ιV_mem_DdRE (hs : Function.Surjective (algebraMap K₀ K)) (τ : K →ₐ[Qp] LL)
    {w : V ⊗[Qp] B} (hw : w ∈ DcrisL PD ρ (τ.comp (IsScalarTower.toAlgHom Qp K₀ K))) :
    ιV PD (LL := LL) (V := V) w ∈ DdRE PD ρ τ := by
  unfold DcrisL at hw
  unfold DdRE
  rw [Submodule.mem_inf] at hw ⊢
  refine ⟨ιV_mem_DdR PD ρ hw.1, ?_⟩
  have h2 := hw.2
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero] at h2 ⊢
  intro c
  obtain ⟨a, rfl⟩ := hs c
  rw [← ιV_mul, h2 a, map_smul]
  simp

theorem FilV_succ_le (a : ℤ) :
    FilV PD (LL := LL) (V := V) (a + 1) ≤ FilV PD (LL := LL) (V := V) a := by
  rintro _ ⟨y, rfl⟩
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v s =>
    exact ⟨v ⊗ₜ ⟨(s : BdR), PD.Fil_anti a s.2⟩, by simp [AlgebraTensorModule.map_tmul]⟩
  | add x y hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy

theorem FilV_anti : Antitone fun a : ℤ => FilV PD (LL := LL) (V := V) a :=
  antitone_int_of_succ_le (FilV_succ_le PD)

end General

end GlobalTheory.Per.CharJumps

namespace GlobalTheory.Per.CharJumps

theorem inf_of_line {LL M : Type} [Field LL] [AddCommGroup M] [Module LL M] (D : Submodule LL M)
    (hD : finrank LL ↥D = 1) (F : ℤ → Submodule LL M) (hF : Antitone F) {x : M} (hx : x ∈ D)
    (d : ℤ) (h1 : x ∈ F d) (h2 : x ∉ F (d + 1)) (b : ℤ) :
    D ⊓ F b = if b ≤ d then D else ⊥ := by
  have hx0 : x ≠ 0 := fun h => h2 (h ▸ (F (d + 1)).zero_mem)
  have hspan : ∀ y ∈ D, ∃ c : LL, c • x = y := by
    intro y hy
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨x, hx⟩ : ↥D)
      (fun h => hx0 (congrArg Subtype.val h))).1 hD ⟨y, hy⟩
    exact ⟨c, congrArg Subtype.val hc⟩
  split_ifs with hb
  · refine inf_eq_left.2 fun y hy => ?_
    obtain ⟨c, rfl⟩ := hspan y hy
    exact (F b).smul_mem c (hF hb h1)
  · rw [eq_bot_iff]
    intro y hy
    rw [Submodule.mem_inf] at hy
    obtain ⟨c, rfl⟩ := hspan _ hy.1
    rw [Submodule.mem_bot]
    by_cases hc : c = 0
    · simp [hc]
    · exfalso
      apply h2
      have hxe : x = c⁻¹ • (c • x) := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
      rw [hxe]
      exact hF (by omega) ((F b).smul_mem _ hy.2)

theorem jumps_of_exact_degree : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l), CaseA K LL → ∀ μ : ↥(GK K) →* (↥LL.1)ˣ, Continuous (fun g : ↥(GK K) => ((μ g : (↥LL.1)ˣ) : ↥LL.1)) → ∀ d : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℤ, (∀ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, ∃ w ∈ DcrisL (P.PD K) (charRep μ) (τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1)), ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w ∈ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) (d τ) ∧ ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w ∉ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) (d τ + 1)) → IsCrys (P.PD K) (charRep μ) → ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (b : ℤ), multV (P.PD K) (charRep μ) τ b = if b = d τ then 1 else 0 := by
  intro l _ P AI T K LL hA μ hμ d hw hcrys τ b
  haveI := LL.2
  haveI := K.2
  have hdr : IsDR (P.PD K) (charRep μ) := by
    let A : GRep ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL) :=
      { V := ↥LL.1, ρ := charRep μ,
        cont := fun x => by
          show Continuous fun g => ((μ g : (↥LL.1)ˣ) : ↥LL.1) • LinearMap.id x
          exact hμ.smul continuous_const }
    exact ((GlobalTheory.Per.FontaineTied.fontCore_all_of_tied l P AI T K) ↥LL.1 ↥(OL LL)
      (GlobalTheory.LocalIntegers.good_integers l LL).1 A).2.2 hcrys
  obtain ⟨-, -, hdim⟩ := (GlobalTheory.Per.Components.components_finrank l P AI T K LL ↥LL.1 (charRep μ)).1 τ
  set_option synthInstance.maxHeartbeats 200000 in
  have h1 : finrank ↥LL.1 ↥(DdRE (P.PD K) (charRep μ) τ) = 1 := by
    rw [hdim hdr, Module.finrank_self]
  have hs : Function.Surjective (algebraMap ↥(K0 K) ↥K.1) :=
    fun c => ⟨⟨c.1, c.2, hA.1 c.2⟩, rfl⟩
  obtain ⟨w, hwD, hin, hout⟩ := hw τ
  have hx := ιV_mem_DdRE (P.PD K) (charRep μ) hs τ hwD
  have key := inf_of_line _ h1 _ (FilV_anti (P.PD K)) hx (d τ) hin hout
  have fk : ∀ c : ℤ, (finrank ↥LL.1 ↥(FildR (P.PD K) (charRep μ) τ c) : ℤ) = if c ≤ d τ then 1 else 0 := by
    intro c
    unfold FildR
    rw [key c]
    by_cases hc : c ≤ d τ
    · rw [if_pos hc, if_pos hc, h1]
      rfl
    · rw [if_neg hc, if_neg hc, finrank_bot]
      rfl
  unfold multV
  rw [fk b, fk (b + 1)]
  split_ifs <;> omega

end GlobalTheory.Per.CharJumps
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

theorem _root_.GlobalTheory.T.negCycPowerBlock_crys_deRham_jumps : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (t : ℕ) (ρ : Representation ↥LL.1 ↥(GK K) (Fin t → ↥LL.1)), (∀ g v (c : Fin t), ρ g v c = (((cycLL (P.PD K) ↥LL.1 g)⁻¹ ^ (c : ℕ) : (↥LL.1)ˣ) : ↥LL.1) * v c) → IsCrys (P.PD K) ρ ∧ IsDR (P.PD K) ρ ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), multV (P.PD K) ρ τ a = if 0 ≤ a ∧ a < (t : ℤ) then 1 else 0 := by
  first | exact @GlobalTheory.negCycBlock_jumps | exact GlobalTheory.negCycBlock_jumps | (intros; apply GlobalTheory.negCycBlock_jumps <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.deRhamComponents_crystallineLetters_finrank : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), (∀ τ, FiniteDimensional ↥LL.1 ↥(DdRE (P.PD K) ρ τ) ∧ finrank ↥LL.1 ↥(DdRE (P.PD K) ρ τ) ≤ finrank ↥LL.1 V ∧ (IsDR (P.PD K) ρ → finrank ↥LL.1 ↥(DdRE (P.PD K) ρ τ) = finrank ↥LL.1 V)) ∧ ∀ τ, IsCrys (P.PD K) ρ → finrank ↥LL.1 ↥(DcrisL (P.PD K) ρ τ) = finrank ↥LL.1 V := by
  first | exact @GlobalTheory.Per.Components.components_finrank | exact GlobalTheory.Per.Components.components_finrank | (intros; apply GlobalTheory.Per.Components.components_finrank <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.de_rham_representation_tensor_comparison : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V₀ : Type) [AddCommGroup V₀] [Module ↥LL.1 V₀] [Module ℚ_[l] V₀] [IsScalarTower ℚ_[l] ↥LL.1 V₀] [FiniteDimensional ↥LL.1 V₀] (ρ₀ : Representation ↥LL.1 ↥(GK K) V₀) (V₁ : Type) [AddCommGroup V₁] [Module ↥LL.1 V₁] [Module ℚ_[l] V₁] [IsScalarTower ℚ_[l] ↥LL.1 V₁] [FiniteDimensional ↥LL.1 V₁] (ρ₁ : Representation ↥LL.1 ↥(GK K) V₁) (V₂ : Type) [AddCommGroup V₂] [Module ↥LL.1 V₂] [Module ℚ_[l] V₂] [IsScalarTower ℚ_[l] ↥LL.1 V₂] [FiniteDimensional ↥LL.1 V₂] (ρ₂ : Representation ↥LL.1 ↥(GK K) V₂) (ι : V₀ →ₗ[↥LL.1] V₁) (π : V₁ →ₗ[↥LL.1] V₂), (∀ g x, ι (ρ₀ g x) = ρ₁ g (ι x)) → (∀ g x, π (ρ₁ g x) = ρ₂ g (π x)) → Function.Injective ι → Function.Surjective π → LinearMap.range ι = LinearMap.ker π → IsDR (P.PD K) ρ₁ → IsDR (P.PD K) ρ₀ ∧ IsDR (P.PD K) ρ₂ ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), finrank ↥LL.1 ↥(FildR (P.PD K) ρ₁ τ a) = finrank ↥LL.1 ↥(FildR (P.PD K) ρ₀ τ a) + finrank ↥LL.1 ↥(FildR (P.PD K) ρ₂ τ a) ∧ multV (P.PD K) ρ₁ τ a = multV (P.PD K) ρ₀ τ a + multV (P.PD K) ρ₂ τ a ∧ (IsJumpV (P.PD K) ρ₁ τ a ↔ IsJumpV (P.PD K) ρ₀ τ a ∨ IsJumpV (P.PD K) ρ₂ τ a) := by
  first | exact @GlobalTheory.Per.ExactMult.exact_hodge_add | exact GlobalTheory.Per.ExactMult.exact_hodge_add | (intros; apply GlobalTheory.Per.ExactMult.exact_hodge_add <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

theorem _root_.GlobalTheory.T.convolution_singleFactor_goodProjector_eq_zero : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (eR : G ≃* G0g D.nd) (kv0 : Σ k : Fin 2, D.nd.PlG k),
    haveI : ∀ k, Fact (D.host.g k).Prime := fun k => ⟨D.host.g_prime k⟩
    ∀ M : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g kv0.1))),
    (∀ a : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), (Fin D.R.r → ZMod (D.host.g kv.1))),
      D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) →
      M * D.ntypes.eSer kv0.1 (Formalism.CyclotomicNorms.monicOf (a kv0)) = 0) → ∀ x : G,
    ∑ y : G, (open Classical in if ∀ kv, kv ≠ kv0 → eR y kv = 1 then M.coeff (eR y kv0) else 0) *
      D.ntypes.e0.coeff (eR (y⁻¹ * x)) = 0 := by
  first | exact @GlobalTheory.DownLift.conv_single_goodProj_eq_zero | exact GlobalTheory.DownLift.conv_single_goodProj_eq_zero | (intros; apply GlobalTheory.DownLift.conv_single_goodProj_eq_zero <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.CrysDdR

theorem finrank_DdRE_of_isCrys : ∀ D : D7, ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l), (∃ s, Good K s LL) → ∀ T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL), IsCrys ((D.loc l).PD K) T.ρ → ∀ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, finrank ↥LL.1 ↥(DdRE ((D.loc l).PD K) T.ρ τ) = finrank ↥LL.1 T.V := by
  intro D l _ K LL _ T hc τ
  have hdr := (GlobalTheory.Per.CrisDR.isDR_of_isCrys l (D.loc l) (D.locA l) (D.locT l) K LL T.V T.ρ hc).1
  exact ((GlobalTheory.Per.Components.components_finrank l (D.loc l) (D.locA l) (D.locT l) K LL T.V T.ρ).1 τ).2.2 hdr

end GlobalTheory.CrysDdR
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory

theorem exists_uniformiser_family_host :
    ∀ (D : D7), ∃ ϖ : Pl D.host.E → 𝓞 D.host.E, ∀ PP : Pl D.host.E, ϖ PP ∈ PP.asIdeal ∧ ϖ PP ∉ PP.asIdeal ^ 2 := by
  intro D
  have h : ∀ PP : Pl D.host.E, ∃ x : 𝓞 D.host.E, x ∈ PP.asIdeal ∧ x ∉ PP.asIdeal ^ 2 := by
    intro PP
    have hlt : PP.asIdeal ^ 2 < PP.asIdeal :=
      Ideal.pow_lt_self _ PP.ne_bot PP.isPrime.ne_top 2 le_rfl
    obtain ⟨x, hx1, hx2⟩ := SetLike.exists_of_lt hlt
    exact ⟨x, hx1, hx2⟩
  choose f hf using h
  exact ⟨f, hf⟩

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

namespace GlobalTheory.LieSpanConj

theorem exists_decomp {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (hd : H.det ≠ 0)
    (Z : Matrix (Fin n) (Fin n) ℂ) :
    ∃ X Y : Matrix (Fin n) (Fin n) ℂ, Xᴴ * H + H * X = 0 ∧ Yᴴ * H + H * Y = 0 ∧
      Z = X + Complex.I • Y := by
  have hu : IsUnit H.det := isUnit_iff_ne_zero.2 hd
  set Zb : Matrix (Fin n) (Fin n) ℂ := -(H⁻¹ * Zᴴ * H) with hZb
  have hA : Zbᴴ * H = -(H * Z) := by
    rw [hZb, conjTranspose_neg, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
      conjTranspose_nonsing_inv, hH, neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu,
      Matrix.mul_one]
  have hB : H * Zb = -(Zᴴ * H) := by
    rw [hZb, Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]
  refine ⟨(1 / 2 : ℂ) • (Z + Zb), (-(Complex.I / 2)) • (Z - Zb), ?_, ?_, ?_⟩
  · rw [conjTranspose_smul, conjTranspose_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add,
      hA, hB]
    have : star (1 / 2 : ℂ) = 1 / 2 := by simp
    rw [this, ← smul_add]
    rw [show Zᴴ * H + -(H * Z) + (H * Z + -(Zᴴ * H)) = 0 by abel, smul_zero]
  · rw [conjTranspose_smul, conjTranspose_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub,
      hA, hB]
    have : star (-(Complex.I / 2)) = Complex.I / 2 := by
      simp [Complex.conj_I]
      ring
    rw [this]
    rw [show Zᴴ * H - -(H * Z) = H * Z + Zᴴ * H by abel, show H * Z - -(Zᴴ * H) = H * Z + Zᴴ * H by abel]
    rw [← add_smul]
    simp
  · rw [smul_smul, smul_add, smul_sub]
    have h1 : Complex.I * -(Complex.I / 2) = 1 / 2 := by
      have := Complex.I_sq
      linear_combination (-(1 / 2 : ℂ)) * this
    rw [h1]
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring

theorem span_conj_lieAt_eq_top : ∀ (D : D7) (V : HSp D) (τ : D.what₂.Tau) (Fm : Matrix (Fin V.rank) (Fin V.rank) ℂ),
    IsUnit Fm → Submodule.span ℂ {Z : Matrix (Fin V.rank) (Fin V.rank) ℂ | ∃ Y ∈ lieAt V τ, Z = Fm * Y * Fm⁻¹} = ⊤ := by
  intro D V τ Fm hF
  have hFd : IsUnit Fm.det := (Matrix.isUnit_iff_isUnit_det Fm).1 hF
  have hd : (gramAt D V τ).det ≠ 0 := by
    rw [gramAt, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero _).2 (Formalism.L2.Theta.gram_det_ne V)
  rw [eq_top_iff]
  intro Z' _
  obtain ⟨X, Y, hX, hY, hZ⟩ :=
    GlobalTheory.LieSpanConj.exists_decomp (gramAt D V τ) (SmoothForms.RealPts.gramAt_herm V τ) hd (Fm⁻¹ * Z' * Fm)
  have hmX : Fm * X * Fm⁻¹ ∈ Submodule.span ℂ {Z : Matrix (Fin V.rank) (Fin V.rank) ℂ | ∃ Y ∈ lieAt V τ, Z = Fm * Y * Fm⁻¹} :=
    Submodule.subset_span ⟨X, hX, rfl⟩
  have hmY : Fm * Y * Fm⁻¹ ∈ Submodule.span ℂ {Z : Matrix (Fin V.rank) (Fin V.rank) ℂ | ∃ Y ∈ lieAt V τ, Z = Fm * Y * Fm⁻¹} :=
    Submodule.subset_span ⟨Y, hY, rfl⟩
  have hZ' : Z' = Fm * X * Fm⁻¹ + Complex.I • (Fm * Y * Fm⁻¹) := by
    have : Z' = Fm * (Fm⁻¹ * Z' * Fm) * Fm⁻¹ := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hFd, Matrix.one_mul, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ hFd, Matrix.mul_one]
    rw [this, hZ, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [hZ']
  exact Submodule.add_mem _ hmX (Submodule.smul_mem _ _ hmY)

end GlobalTheory.LieSpanConj
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.Member GlobalTheory.CoverHalf Formalism.IndefR.FWT Formalism.L2.DIV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnivCover.OpenKerChar



theorem map_eq_one_of_finPart_eq_one : ∀ (D : D7) {A : Type} [Group A] (χ : (AE D)ˣ →* A),
    IsOpen (χ.ker : Set (AE D)ˣ) → ∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 → χ x = 1 := by
  intro D A _ χ hχ x hx
  obtain ⟨hcm, -⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  have hfam : GlobalTheory.Mem.Vol.IsCMFam (fun w : InfinitePlace D.host.E => w.embedding) := by
    unfold GlobalTheory.Mem.Vol.IsCMFam
    simp only [InfinitePlace.mk_embedding]
    exact Function.bijective_id
  choose θ hθ using fun w : InfinitePlace D.host.E =>
    (GlobalTheory.Mem.VolEmb.existsUnique_infEmb D.host.F D.host.E D.sp.cm.sig hcm w.embedding).exists
  obtain ⟨e2, -, hc2, hc2', -⟩ :=
    GlobalTheory.Mem.VolInfIso.exists_infAdele_equiv D.host.F D.host.E D.sp.cm.sig (InfinitePlace D.host.E) _ θ hcm hfam hθ
  obtain ⟨e1, he1, hc1, hc1'⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have h2 : (e1 (x : AE D)).2 = 1 := (he1 _).2.trans hx
  set c : InfinitePlace D.host.E → ℂ := e2 (e1 (x : AE D)).1 with hcdef
  have hcu : IsUnit c := by
    have hu : IsUnit (e1 (x : AE D)) := x.isUnit.map e1
    exact (Prod.isUnit_iff.1 hu).1.map e2
  have hc0 : ∀ w, c w ≠ 0 := fun w => (Pi.isUnit_iff.1 hcu w).ne_zero
  let p : ℝ → (InfinitePlace D.host.E → ℂ) := fun t w => Complex.exp (t * Complex.log (c w))
  let γ : ℝ → AE D := fun t => e1.symm (e2.symm (p t), 1)
  have hpc : Continuous p := continuous_pi fun w =>
    Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)
  have hγc : Continuous γ := hc1'.comp ((hc2'.comp hpc).prodMk continuous_const)
  have hpmul : ∀ s t, p s * p t = p (s + t) := fun s t => by
    funext w
    simp only [p, Pi.mul_apply, ← Complex.exp_add, Complex.ofReal_add, add_mul]
  have hγmul : ∀ s t, γ s * γ t = γ (s + t) := fun s t => by
    simp only [γ, ← map_mul, Prod.mk_mul_mk, mul_one, hpmul]
  have hp0 : p 0 = 1 := by funext w; simp [p]
  have hγ0 : γ 0 = 1 := by simp only [γ, hp0, map_one, Prod.mk_one_one]
  have hp1 : p 1 = c := by funext w; simp [p, Complex.exp_log (hc0 w)]
  have hγ1 : γ 1 = x := by
    simp only [γ, hp1, hcdef, RingEquiv.symm_apply_apply]
    rw [← h2, Prod.mk.eta, RingEquiv.symm_apply_apply]
  have hr : ∀ t, γ t * γ (-t) = 1 := fun t =>
    (hγmul t (-t)).trans ((congrArg γ (add_neg_cancel t)).trans hγ0)
  have hl : ∀ t, γ (-t) * γ t = 1 := fun t =>
    (hγmul (-t) t).trans ((congrArg γ (neg_add_cancel t)).trans hγ0)
  let f : ℝ → (AE D)ˣ := fun t => Units.mk (γ t) (γ (-t)) (hr t) (hl t)
  have hf : Continuous f := Units.continuous_iff.2 ⟨hγc, hγc.comp continuous_neg⟩
  have hcl : IsClosed (χ.ker : Set (AE D)ˣ) := Subgroup.isClosed_of_isOpen _ hχ
  have hS : IsClopen (f ⁻¹' (χ.ker : Set (AE D)ˣ)) := ⟨hcl.preimage hf, hχ.preimage hf⟩
  have h0 : (0 : ℝ) ∈ f ⁻¹' (χ.ker : Set (AE D)ˣ) := by
    have : f 0 = 1 := Units.ext hγ0
    simp [this]
  rcases isClopen_iff.1 hS with h | h
  · rw [h] at h0; exact absurd h0 (Set.notMem_empty _)
  · have h1 : (1 : ℝ) ∈ f ⁻¹' (χ.ker : Set (AE D)ˣ) := h ▸ Set.mem_univ _
    have hf1 : f 1 = x := Units.ext hγ1
    rw [Set.mem_preimage, hf1] at h1
    exact h1

end GlobalTheory.UnivCover.OpenKerChar
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical




namespace GlobalTheory.FlatLift

theorem kmul_int : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (ϖ : 𝓞 D.host.E), ϖ ≠ 0 → ∃ k : ℕ, 0 < k ∧ ∀ u : WO S T, IsIntM (frMapO S T βS βT (u.map fun w => incA D (ϖ : D.host.E) * w)) → IsIntM (frMapO S T βS βT (k • u)) := by
  intro D S T βS βT ϖ hϖ
  let I : Ideal (𝓞 D.host.E) := Ideal.span {ϖ}
  have hI : I ≠ ⊥ := by simpa [I, Ideal.span_singleton_eq_bot] using hϖ
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem I)
  refine ⟨Ideal.absNorm I, Nat.pos_of_ne_zero (fun h => hI (Ideal.absNorm_eq_zero_iff.1 h)), fun u hu => ?_⟩
  have hk : ((Ideal.absNorm I : ℕ) : D.host.E) = (c : D.host.E) * (ϖ : D.host.E) := by
    have := congrArg (fun z : 𝓞 D.host.E => (z : D.host.E)) hc
    simpa using this.symm
  have hm : (((Ideal.absNorm I) • u : WO S T) : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (Formalism.IndefR.Datum.toEAf D) =
      Formalism.IndefR.Datum.eToEAf D (c : D.host.E) •
        ((u.map fun w => incA D (ϖ : D.host.E) * w : WO S T) : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map
          (Formalism.IndefR.Datum.toEAf D) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, nsmul_eq_mul]
    rw [map_natCast]
    have h1 : Formalism.IndefR.Datum.toEAf D (incA D (ϖ : D.host.E)) = Formalism.IndefR.Datum.eToEAf D (ϖ : D.host.E) := rfl
    rw [h1, ← mul_assoc, ← map_mul, ← hk, map_natCast]
  intro i j
  have he : frMapO S T βS βT ((Ideal.absNorm I) • u) =
      Formalism.IndefR.Datum.eToEAf D (c : D.host.E) • frMapO S T βS βT (u.map fun w => incA D (ϖ : D.host.E) * w) := by
    simp only [frMapO]
    rw [hm, Matrix.mul_smul, Matrix.smul_mul]
  rw [he, Matrix.smul_apply, smul_eq_mul]
  exact (Formalism.L2.Herm.intAf D.host.F D.host.E).mul_mem (Subring.subset_closure (Or.inl ⟨⟨((c : 𝓞 D.host.E) : D.host.E), ⟨c, rfl⟩⟩, rfl⟩)) (hu i j)

end GlobalTheory.FlatLift
end
