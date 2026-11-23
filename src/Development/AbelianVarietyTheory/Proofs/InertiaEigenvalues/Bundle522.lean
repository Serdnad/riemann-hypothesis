module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle495
public import GroundTheory.AutomorphicForms.Bundle012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqColGenMulBlkU
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle194
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle496
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfForallMemFilV
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DeRhamJumpDescent
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle411
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdemNotMemFilVOne
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle005
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle063
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle002
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle030
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBlochKatoConditionOfWachModules
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle006
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedIntegersTensorEqLetterwiseProductAinf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle097
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle511
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodDiscExtensionTateElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivOfNotLinearIndependent
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped ENNReal nonZeroDivisors

namespace GlobalTheory.CellDec

theorem exists_isFundamentalDomain_NE : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (μ : Measure (GA E a)),
    ∃ 𝓕₀ : Set (GA E a), IsFundamentalDomain (GlobalTheory.CellDec.NE E a) 𝓕₀ μ := by
  intro E _ _ a μ
  haveI : DiscreteTopology (GlobalTheory.CellDec.NE E a) :=
    GlobalTheory.MirTower.discrete_of_le_range (Subgroup.map_le_range _ _)
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  haveI : SecondCountableTopology (Matrix (Fin a) (Fin a) (Ad E)) :=
    inferInstanceAs (SecondCountableTopology (Fin a → Fin a → Ad E))
  haveI : SecondCountableTopology (Matrix (Fin a) (Fin a) (Ad E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology (GA E a) :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  exact GlobalTheory.FundDomDiscrete.exists_isFundamentalDomain _ μ

end GlobalTheory.CellDec
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.HWL.Cmp

namespace GlobalTheory.HWL.Letter

variable {l : ℕ} [Fact l.Prime]

theorem lin_ext (K : FinExt l) {M : Type} [AddCommGroup M] [Module ℚ_[l] M] (σ τ : ↥(K0 K) →ₗ[ℚ_[l]] M)
    (h : ∀ (c : ↥(K0 K)) (m : ℕ), 0 < m → ¬ l ∣ m → (c : Om l) ^ m = 1 → σ c = τ c) (c : ↥(K0 K)) :
    σ c = τ c := by
  have h1 : ∀ c : ↥(K0 K), ‖(c : Om l)‖ ≤ 1 → σ c = τ c := by
    intro c hc
    obtain ⟨n, z, ω, hω, hsum⟩ := GlobalTheory.UnramSpan.exists_sum_rootsOfUnity l K c c.2 hc
    have h2 : c = ∑ i, (z i : ℚ_[l]) • (⟨ω i, (hω i).1⟩ : ↥(K0 K)) := by
      apply Subtype.ext
      rw [hsum]
      push_cast
      simp only [Algebra.smul_def]

    rw [h2, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    obtain ⟨m, hm, hl, hx⟩ := (hω i).2
    rw [map_smul, map_smul, h _ m hm hl hx]
  have hl : ‖(l : Om l)‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] (Om l)), PadicAlgCl.norm_extends]
    exact Padic.norm_p_lt_one
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hl).mul_const ‖(c : Om l)‖
  rw [zero_mul] at ht
  obtain ⟨n, hn⟩ := (ht.eventually (ge_mem_nhds one_pos)).exists
  have h3 := h1 (((l : ℚ_[l]) ^ n) • c) (by
    rw [Algebra.smul_def]
    push_cast
    rwa [norm_mul, norm_pow])
  rw [map_smul, map_smul] at h3
  have h0 : ((l : ℚ_[l]) ^ n) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  rw [← inv_smul_smul₀ h0 (σ c), h3, inv_smul_smul₀ h0]

theorem mul_ext (K : FinExt l) {L B : Type} [Field L] [Algebra ℚ_[l] L] [CommRing B] [Algebra ℚ_[l] B]
    (e : ↥(K0 K) →ₐ[ℚ_[l]] L) (f : ↥(K0 K) →ₐ[ℚ_[l]] B) (x : L ⊗[ℚ_[l]] B)
    (h : ∀ (c : ↥(K0 K)) (m : ℕ), 0 < m → ¬ l ∣ m → (c : Om l) ^ m = 1 →
      ((1 : L) ⊗ₜ[ℚ_[l]] f c) * x = e c • x) (c : ↥(K0 K)) : ((1 : L) ⊗ₜ[ℚ_[l]] f c) * x = e c • x :=
  lin_ext K ((LinearMap.mulRight ℚ_[l] x).comp ((TensorProduct.mk ℚ_[l] L B 1).comp f.toLinearMap))
    (((LinearMap.toSpanSingleton L _ x).restrictScalars ℚ_[l]).comp e.toLinearMap) h c

theorem const_mul_letE {O : Type} [CommRing O] {n : ℕ} (o : ZMod n → O) (i : ZMod n) :
    (fun j => PowerSeries.C (o j) : LetA O n) * letE i = algebraMap O (LetA O n) (o i) * letE i := by
  funext j
  by_cases hj : j = i
  · subst hj; rfl
  · simp [letE, hj]

theorem step {O R Q L B : Type} [CommRing O] [CommRing R] [Algebra O R] [Field Q] [Field L] [Algebra Q L]
    [CommRing B] [Algebra Q B] {n : ℕ} (io : LetA O n →ₐ[O] R) (β : R →+* L ⊗[Q] B) (o : ZMod n → O)
    (i : ZMod n) (a : L) (b : B) (h3 : β (io (fun j => PowerSeries.C (o j))) = (1 : L) ⊗ₜ[Q] b)
    (h5 : β (algebraMap O R (o i)) = a ⊗ₜ[Q] (1 : B)) :
    ((1 : L) ⊗ₜ[Q] b) * β (io (letE i)) = a • β (io (letE i)) := by
  rw [← h3, ← map_mul, ← map_mul, const_mul_letE, map_mul, AlgHom.commutes, map_mul, h5, Algebra.smul_def]
  rfl

theorem letter : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → ∀ β : RA LL →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B, IsBeta AI β → ∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (c : ↥(K0 K)), ((1 : ↥LL.1) ⊗ₜ[ℚ_[l]] algebraMap ↥(K0 K) P.R.B c) * β (I.io (letE i)) = Γ.emb i c • β (I.io (letE i)) := by
  intro l _ P AI _ K s LL _ Γ R I hI β hβ i c
  refine mul_ext K (Γ.emb i) (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) P.R.B) _ (fun c m hm hl hc => ?_) c
  obtain ⟨xb, hxb⟩ := GlobalTheory.MemLoc.exists_isTiltOf (c : Om l) m hm hl hc
  have hc' : c ^ m = 1 := by exact_mod_cast hc
  obtain ⟨o, ho⟩ := GlobalTheory.UnramIdem.exists_vec Γ.emb hm hc'
  have h1 := hI c m hm hl hc xb hxb o ho
  have h2 : AI.ιA (WittVector.teichmuller l xb) = algebraMap ↥(K0 K) P.R.B c :=
    AI.ιA_teich ⟨c, c.2.2⟩ m hm hl hc xb hxb
  have h3 := hβ 1 (WittVector.teichmuller l xb)
  have h5 := hβ (o i) 1
  rw [map_one, ho] at h5
  rw [h2] at h3
  exact step I.io β o i _ _ ((congrArg β h1).trans h3) h5

end GlobalTheory.HWL.Letter
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.JumpRestrict

open GlobalTheory.DRFil

variable {l : ℕ} [Fact l.Prime]

theorem algebraMap_inclusion (P : LocPrime l) {K K' : FinExt l} (h : K.1 ≤ K'.1) (c : ↥K.1) :
    algebraMap ↥K'.1 P.R.BdR (IntermediateField.inclusion h c) = algebraMap ↥K.1 P.R.BdR c := rfl

theorem idem_restrict_mul (P : LocPrime l) {K K' LL : FinExt l} (h : K.1 ≤ K'.1)
    (τ : ↥K'.1 →ₐ[ℚ_[l]] ↥LL.1) :
    haveI := K.2; haveI := K'.2
    idem (K := ↥K.1) P.R.BdR (τ.comp (IntermediateField.inclusion h)) * idem (K := ↥K'.1) P.R.BdR τ =
      idem (K := ↥K'.1) P.R.BdR τ := by
  haveI := K.2; haveI := K'.2
  obtain ⟨n, a, c, hrep, h1⟩ := idem_repr (K := ↥K.1) P.R.BdR (τ.comp (IntermediateField.inclusion h))
  have e := exists_smul_idem (K := ↥K'.1) (F := P.R.BdR) τ n a (fun i => IntermediateField.inclusion h (c i))
  simp only [algebraMap_inclusion] at e
  rw [hrep, mul_comm, e]
  simp only [AlgHom.comp_apply] at h1
  rw [h1, one_smul]

theorem multV_restrict : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K K' LL : FinExt l) (h : K.1 ≤ K'.1) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), IsDR (P.PD K) ρ → ∀ (τ : ↥K'.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), multV (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h))) τ a = multV (P.PD K) ρ (τ.comp (IntermediateField.inclusion h)) a := by
  intro l _ P AI T K K' LL h V _ _ _ _ _ ρ hdr τ a
  haveI := K.2; haveI := K'.2; haveI := LL.2
  haveI := (GlobalTheory.T.concretePeriod_deRham_module_finrank_le l P AI T K LL V ρ).1
  obtain ⟨m, d, k, hA⟩ := exists_adapted (P.PD K) (isField_dR T) ρ (filSpans T K LL ρ hdr)
    (τ.comp (IntermediateField.inclusion h))
  have hI := idem_restrict_mul P h τ
  have hA' : Adapted (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h))) τ
      (fun i => sm ℚ_[l] P.R.BdR ↥LL.1 V (idem P.R.BdR τ) (d i)) k := by
    refine ⟨fun i => ?_, fun r hr i => ?_, fun n y hy => ?_⟩
    · have hm := hA.mem i
      refine ⟨sm_idem_mem_DdRE (P.PD K') _ τ
        (GlobalTheory.Per.TiedRestrict.ddR_le h ρ (Submodule.mem_inf.1 (Submodule.mem_inf.1 hm).1).1), ?_⟩
      refine sm_idem_mem_FilV (P.PD K') τ ?_
      rw [GlobalTheory.JumpDescent.FilV_eq P K K']
      exact (Submodule.mem_inf.1 hm).2
    · have := hA.indep (fun i => r i * idem P.R.BdR τ) (by
        simpa only [sm_mul] using hr) i
      rw [mul_left_comm, hI] at this
      rw [mul_comm]; exact this
    · rw [GlobalTheory.JumpDescent.FilV_eq P K K'] at hy
      obtain ⟨r, hr, hy'⟩ := hA.span n y hy
      refine ⟨r, fun i => ?_, ?_⟩
      · rw [GlobalTheory.JumpDescent.FilV_eq P K K']; exact hr i
      · have e : sm ℚ_[l] P.R.BdR ↥LL.1 V (idem P.R.BdR τ) y = sm ℚ_[l] P.R.BdR ↥LL.1 V (idem P.R.BdR τ)
            (sm ℚ_[l] P.R.BdR ↥LL.1 V (idem P.R.BdR (τ.comp (IntermediateField.inclusion h))) y) := by
          rw [← sm_mul, mul_comm, hI]

        rw [e, hy', map_sum]
        exact Finset.sum_congr rfl fun i _ => sm_comm _ _ _
  rw [hA.multV_eq, hA'.multV_eq]

end GlobalTheory.JumpRestrict
end
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Module

namespace GlobalTheory.NL.PhiD

section General

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B F : Type} [CommRing B] [CommRing F] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp F] [Algebra K₀ F] [Algebra K F] [IsScalarTower Qp K F]
    [IsScalarTower K₀ K F] [IsScalarTower Qp K₀ F]
    (PD : PeriodData G Qp K₀ K B F)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem mem_letter (τ : K₀ →ₐ[Qp] LL) (x : V ⊗[Qp] B) :
    x ∈ DcrisL PD ρ τ ↔ (∀ g, actVB PD ρ g x = x) ∧
      ∀ c : K₀, mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c x = τ c • x := by
  simp [DcrisL, Dcris, Submodule.mem_iInf, sub_eq_zero]

theorem phi_injective : Function.Injective (φVB PD (LL := LL) (V := V)) :=
  Module.Flat.lTensor_preserves_injective_linearMap (M := V) PD.φ.toLinearMap PD.φ_inj

theorem iota_injective : Function.Injective (ιV PD (LL := LL) (V := V)) :=
  Module.Flat.lTensor_preserves_injective_linearMap (M := V)
    (PD.ι.toLinearMap.restrictScalars Qp) PD.ι_inj

theorem phi_mem (τ τ' : K₀ →ₐ[Qp] LL) (h : ∀ c, τ' c = τ (PD.σ c)) :
    ∀ x ∈ DcrisL PD ρ τ', φVB PD (LL := LL) x ∈ DcrisL PD ρ τ := by
  have h1 : ∀ g x, φVB PD (LL := LL) (actVB PD ρ g x) = actVB PD ρ g (φVB PD (LL := LL) x) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [actVB, φVB, PD.φ_comm]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have h2 : ∀ (c : K₀) (x : V ⊗[Qp] B),
      φVB PD (LL := LL) (mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c x) =
      mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) (PD.σ c) (φVB PD (LL := LL) x) := by
    intro c x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [mulVB, φVB, PD.φ_K₀]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  intro x hx
  rw [mem_letter] at hx ⊢
  refine ⟨fun g => by rw [← h1, hx.1], fun c => ?_⟩
  obtain ⟨c, rfl⟩ := PD.σ_bij.2 c
  rw [← h2, hx.2, map_smul, h]

theorem iSupIndep_letter : iSupIndep fun τ : K₀ →ₐ[Qp] LL => DcrisL PD ρ τ := by
  have h := iSupIndep.iInf
    (fun (c : K₀) (a : LL) => Module.End.eigenspace
      (mulVB (Qp := Qp) (K₀ := K₀) (B := B) (V := V) (LL := LL) c) a)
    (fun c => Module.End.eigenspaces_iSupIndep _)
  have h' := h.comp (f := fun τ : K₀ →ₐ[Qp] LL => (τ : K₀ → LL)) DFunLike.coe_injective
  refine h'.mono fun τ x hx => ?_
  simp only [Function.comp, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
  exact ((mem_letter PD ρ τ x).1 hx).2

variable [FiniteDimensional LL V] [IsDomain B]

theorem phi_bijOn (hc : Nat.card (K₀ →ₐ[Qp] LL) = finrank Qp K₀) (hV : IsCrys PD ρ)
    (τ τ' : K₀ →ₐ[Qp] LL) (h : ∀ c, τ' c = τ (PD.σ c)) :
    Set.BijOn (φVB PD (LL := LL) (V := V)) (DcrisL PD ρ τ') (DcrisL PD ρ τ) := by
  haveI := GlobalTheory.Per.LetterDim.finite_Dcris PD ρ hV
  haveI : ∀ τ, FiniteDimensional LL ↥(DcrisL PD ρ τ) := fun τ =>
    Submodule.finiteDimensional_of_le (S₂ := Dcris PD ρ) inf_le_left
  refine ⟨phi_mem PD ρ τ τ' h, (phi_injective PD).injOn, fun y hy => ?_⟩
  have hi : Function.Injective ((φVB PD (LL := LL) (V := V)).restrict (phi_mem PD ρ τ τ' h)) :=
    fun x y hxy => Subtype.ext (phi_injective PD (congrArg Subtype.val hxy))
  have hs := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
    rw [GlobalTheory.Per.LetterDim.letter_eq PD ρ hc hV, GlobalTheory.Per.LetterDim.letter_eq PD ρ hc hV])).1 hi
  obtain ⟨x, hx⟩ := hs ⟨y, hy⟩
  exact ⟨x, x.2, congrArg Subtype.val hx⟩

theorem iSup_letter (hc : Nat.card (K₀ →ₐ[Qp] LL) = finrank Qp K₀) (hV : IsCrys PD ρ) :
    (⨆ τ : K₀ →ₐ[Qp] LL, DcrisL PD ρ τ) = Dcris PD ρ := by
  classical
  haveI := PD.finK₀
  haveI := GlobalTheory.Per.LetterDim.finite_Dcris PD ρ hV
  haveI : ∀ τ, FiniteDimensional LL ↥(DcrisL PD ρ τ) := fun τ =>
    Submodule.finiteDimensional_of_le (S₂ := Dcris PD ρ) inf_le_left
  refine Submodule.eq_of_le_of_finrank_eq (iSup_le fun τ => inf_le_left) ?_
  have hinj := (iSupIndep_letter PD ρ).dfinsupp_lsum_injective
  rw [Submodule.iSup_eq_range_dfinsupp_lsum, LinearMap.finrank_range_of_inj hinj]
  change finrank LL (DirectSum _ fun τ => ↥(DcrisL PD ρ τ)) = _
  rw [Module.finrank_directSum]
  simp only [GlobalTheory.Per.LetterDim.letter_eq PD ρ hc hV, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [← Nat.card_eq_fintype_card, hc]
  exact hV.symm

end General

theorem phi_letters : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → (∀ i : Let K, Set.BijOn (φVB ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V)) (Di (HW l) h T (i - 1)) (Di (HW l) h T i)) ∧ (⨆ i : Let K, Di (HW l) h T i) = Dcris ((D.loc l).PD K) T.ρ ∧ iSupIndep (fun i : Let K => Di (HW l) h T i) ∧ Function.Injective (ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V)) := by
  intro D HW l _ K s LL h W T hV
  haveI := GlobalTheory.RegularRing.isDomain_of_tied (D.locT l) K
  have hc : Nat.card (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1) = finrank ℚ_[l] ↥(K0 K) := by
    rw [← Nat.card_eq_of_bijective _ W.emb_bij, Nat.card_zmod]
  refine ⟨fun i => phi_bijOn _ T.ρ hc hV _ _ fun c => ?_, ?_,
    (iSupIndep_letter ((D.loc l).PD K) T.ρ).comp W.emb_bij.1, iota_injective _⟩
  · have := AlgHom.congr_fun (W.emb_σ (i - 1)) c
    rw [sub_add_cancel] at this
    exact this.symm
  · rw [← iSup_letter _ T.ρ hc hV]
    exact W.emb_bij.2.iSup_comp (fun τ => DcrisL ((D.loc l).PD K) T.ρ τ)

end GlobalTheory.NL.PhiD
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar



namespace GlobalTheory.IdemFin

theorem toEAf_mem_intAf_of_idem : ∀ {D : D7} {e : AE D}, e * e = e → toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  intro D e he
  have h1 : finPart D e * finPart D e = finPart D e := by rw [← map_mul, he]
  exact GlobalTheory.LevSplit.swapAE_int (GlobalTheory.AdIdem.idempotent_mem_intAE D _ h1)

end GlobalTheory.IdemFin
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix
open scoped ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DictDom

theorem frame_mem_dom : ∀ {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
    {c : Coeff l} {σ : c.F →+* ℂ} (V : HSp D) (U : Unf Xo c σ V.rank) (dict : GA D V → Σ k, Frame (U.X k).Ψ V.rank)
    (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) {g : ℕ} (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ)
    (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (hσ : GoodEmb c σ) (hA : l.A = 1) (hU : IsUnf U) (hW : ∀ k, ModelW V rfl (U.X k))
    (hD : DictLat U V rfl dict io e F ik φ th x₀) (hth : ∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ))
    (hx₀ : ∀ k, IsOrthogonalFrame (U.X k) x₀), ∀ h, (dict h).2 ∈ (U.X (dict h).1).dom := by
  intro D H Dw l Xo c σ V U dict io g e F ik φ th x₀ hσ hA hU hW hD hth hx₀ h
  obtain ⟨γ, -, -, -, hmat⟩ := hD.2 h
  have hX := hW (dict h).1
  refine ((GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular _ _ (U.X (dict h).1).p0 (U.X (dict h).1).Ψ
    (U.X (dict h).1).Gm (U.X (dict h).1).Gm_herm).2.1 _ fun τ => ?_).1
  rw [← hx₀ (dict h).1 τ.1 τ.2, hmat τ, GlobalTheory.RecDictModel.gram_eq, GlobalTheory.RecDictModel.gram_eq, hX.1]
  have hu := GlobalTheory.RecDictModel.archM_unitary V (hth (dict h).1 τ) (γ * h)
  have e1 : ∀ A : Matrix (Fin V.rank) (Fin V.rank) ℂ, Matrix.reindex (finCongr rfl) (finCongr rfl) A = A :=
    fun A => rfl
  have e2 : ((-(Matrix.reindex (finCongr rfl) (finCongr rfl) V.gram).transpose).map τ.1).transpose =
      -(V.gram.map τ.1) := by
    ext a b; simp
  rw [e1, e2, Matrix.conjTranspose_mul]
  congr 1
  conv_rhs => rw [← hu]
  simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]

end GlobalTheory.DictDom
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

theorem _root_.GlobalTheory.T.unramifiedIntegers_tensor_eq_letterwise_product_Ainf : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ emb : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1), Function.Bijective emb → ∃ u : (ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ↥(OL LL)) →ₐ[↥(OL LL)] RA LL, (∀ (c : ↥(K0 K)) (m : ℕ), 0 < m → ¬ l ∣ m → (c : Om l) ^ m = 1 → ∀ xb : OCb l, IsTiltOf (c : Om l) m xb → ∀ o : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ↥(OL LL), (∀ i, ((o i : ↥(OL LL)) : ↥LL.1) = emb i c) → u o = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] WittVector.teichmuller l xb) ∧ ∀ (S : Type) [CommRing S] [Algebra ↥(OL LL) S] (f f' : (ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ↥(OL LL)) →ₐ[↥(OL LL)] S), (∀ (c : ↥(K0 K)) (m : ℕ), 0 < m → ¬ l ∣ m → (c : Om l) ^ m = 1 → ∀ o : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ↥(OL LL), (∀ i, ((o i : ↥(OL LL)) : ↥LL.1) = emb i c) → f o = f' o) → f = f' := by
  first | exact @GlobalTheory.UnramIdem.exists_prod_hom | exact GlobalTheory.UnramIdem.exists_prod_hom | (intros; apply GlobalTheory.UnramIdem.exists_prod_hom <;> assumption)
end

section

noncomputable section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.TBLocalW

theorem tb_of_localW : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (M0 h0 cB : ℕ),
    LocalSituation.Conclusion4 D HW F →
    (∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
      (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (h : Good (D.nbr i w hw).Kw 1 C.LL),
      EmbeddingTypeJumps.WachHypothesisLocal (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL h)
        ((F (D.nd.l i)).E (D.nbr i w hw).Kw 1 C.LL h).tie) →
    TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i → JointConditionTameBound D HW F i r π M0 h0 cB → TruncatedSeriesCountingIdentities.admTB i r π cB := by
  intro D HW F i r π M0 h0 cB hP hW hF hJ
  obtain ⟨hl2, hJw⟩ := hJ
  intro w hw C hG
  obtain ⟨hIn, hKs, hJC⟩ := hJw w hw
  have hs : Good (D.nbr i w hw).Kw 1 C.LL := hG.good_one hl2 hKs
  have hP1 := hP (D.nd.l i) (D.nbr i w hw).Kw 1 C.LL hs
  have hTB := hP1.1
  have hTBe := hP1.2
  have hWs := hW w hw C hs
  have hFa := hF w hw C
  refine ⟨?_, ?_⟩
  · intro Vy _ _ _ _ _ _ _ _ _ _ _ ρy Ly hcy hcrys hjmp p hp hint e₀ he₀ hpe e he Ve _ _ _ _ _ _ _ _ _ _ _ ρe Le hce hMat φ hφ
    have hE := GlobalTheory.TBLocal.eps_lat (Br.PD D.loc D.nbr i w hw) (O := ↥(OL C.LL)) Le.T e hMat
    let Yt : LocLat (Br.G D.nbr i w hw) ℚ_[D.nd.l i] ↥C.LL.1 ↥(OL C.LL) :=
      { V := Vy, ρ := ρy, cont := hcy, L := Ly }
    let Y := kerY Yt p e₀ hpe hp hint he₀
    let VeL : LocLat (Br.G D.nbr i w hw) ℚ_[D.nd.l i] ↥C.LL.1 ↥(OL C.LL) :=
      { V := Ve, ρ := ρe, cont := hce, L := Le }
    have hcjY := cj_sub hFa (GRep.ofLat Yt) (LinearMap.ker p) (ker_stable Yt p hp) ⟨hcrys, hjmp⟩
    have hJY := hJC C hs Y hcjY.1 hcjY.2
    have hWY := hWs Y M0 h0 hcjY.1 hJY.1
    have hJYt := hJC C hs Yt hcrys hjmp
    have hCt := (hWs Yt M0 h0 hcrys hJYt.1).1
    haveI : IsTopologicalRing (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL hs).LL :=
      inferInstanceAs (IsTopologicalRing ↥C.LL.1)
    haveI : IsDomain (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL hs).O :=
      inferInstanceAs (IsDomain ↥(OL C.LL))
    haveI : IsPrincipalIdealRing (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL hs).O :=
      inferInstanceAs (IsPrincipalIdealRing ↥(OL C.LL))
    exact GlobalTheory.TBLocal.tb_part1 (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL hs)
      Yt p e₀ hpe hp hint he₀ Subtype.val_injective _ hTB e M0 h0 cB VeL hE.1 hE.2 hCt hWY (hJY.2 e he) φ hφ
  · intro e he Ve _ _ _ _ _ _ _ _ _ _ _ ρe Le hce hMat
    have hE := GlobalTheory.TBLocal.eps_lat (Br.PD D.loc D.nbr i w hw) (O := ↥(OL C.LL)) Le.T e hMat
    let VeL : LocLat (Br.G D.nbr i w hw) ℚ_[D.nd.l i] ↥C.LL.1 ↥(OL C.LL) :=
      { V := Ve, ρ := ρe, cont := hce, L := Le }
    have hT := hTBe e VeL hE.1 hE.2
    exact GlobalTheory.TBLocal.tbe_clauses (Br.PD D.loc D.nbr i w hw) Le _ _ hIn e cB hT.2.1 hT.2.2 (hT.1 cB)

end GlobalTheory.TBLocalW
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.lattice_dual_cyclotomic : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l), ∀ (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∀ S : Submodule O (↥(GK K) → A'.V ⧸ LA'.T), BD LA' ≤ S → S ≤ divisibleCocycles LA' → ∀ c ∈ divisibleCocycles LA', (∀ d ∈ latticeCocycles LA, (∀ s ∈ S, CobO (P.PD K) L1 (cupLD LA' m d s)) → CobO (P.PD K) L1 (cupLD LA' m d c)) → c ∈ S := by
  first | exact @GlobalTheory.tate_double_annihilator | exact GlobalTheory.tate_double_annihilator | (intros; apply GlobalTheory.tate_double_annihilator <;> assumption)
end
