module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle008
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle001
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle002
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.StabilizerLattices
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryUnfoldingVolumeVectorStabilizer
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle011
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle017
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle339
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle212
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle236
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle204
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TransportedLatticeLocalizationFreeLeCoefficientS
import Formalism.HermitianLattices.HermitianLatticesProofs.LocBasic
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalGlobalInclusion.SmulMemIdealSmul
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle136
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitOfConjPNe
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle003
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumPlacesEqTrace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle197
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle280
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle082
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PeriodLatticeHalfLatticeInclusionsSplitPrime
public import Formalism.LocalToGlobal.GlobalTheory.GL5.PClassDecomp
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle133
public import Formalism.SharpRestriction.Divisibility.StatementFT.PeriodPointConditions
public import Formalism.LocalToGlobal.GroupLattices.AdmissibleAtGeneratorPlaces
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle135
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles

@[expose] public section

section


theorem _root_.GlobalTheory.T.unitaryUnfolding_volume_vectorStabilizer : GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.QuotientMeasures → GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure.AdelicUnitaryHaar → GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers.StabTransitive → ∀ D : Formalism.BasicNotions.D7, GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold.Unfolding D := by
  first | exact @GlobalTheory.VolumeUnfolding.unfolding | exact GlobalTheory.VolumeUnfolding.unfolding | (intros; apply GlobalTheory.VolumeUnfolding.unfolding <;> assumption)
end

section

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint
open scoped Matrix

namespace GlobalTheory.HAtBasis

variable {K : Type} [Field K] [NumberField K]


open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] [NumberField K] in
theorem _root_.GlobalTheory.HAtBasis.isLattice_of_basisAt {n : ℕ} (w : HeightOneSpectrum (𝓞 K))
    {M : Submodule (𝓞 K) (Fin n → K)} (hM : M.FG)
    {B : GL (Fin n) K} (hB : _root_.Formalism.L2.DIV.IsBasisAt w M B) : Submodule.IsFullLattice K M := by
  haveI : Submodule.IsLattice K M := ⟨hM, fun s hs hli =>
    (LinearIndependent.iff_fractionRing _ _).mp hli⟩
  refine ⟨?_⟩
  have hcol : ∀ j, (fun i => (B : Matrix (Fin n) (Fin n) K) i j) ∈
      Submodule.span K (M : Set (Fin n → K)) := by
    intro j
    have h1 : (fun i => (B : Matrix (Fin n) (Fin n) K) i j) ∈ _root_.Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M := by
      unfold _root_.Formalism.L2.DIV.IsBasisAt at hB
      rw [hB]
      apply _root_.Formalism.HermitianLatticesTheory.locBasic_le_locS
      exact Submodule.subset_span ⟨j, rfl⟩
    obtain ⟨s, hs, hsx⟩ := (_root_.PI.LocGlobInclWork.mem_localization_iff w.asIdeal M _).1 h1
    have hs0 : (s : K) ≠ 0 := by
      intro h0
      apply hs
      have hs' : s = 0 := by exact_mod_cast h0
      rw [hs']
      exact w.asIdeal.zero_mem
    have h2 := Submodule.smul_mem (Submodule.span K (M : Set (Fin n → K))) ((s : K)⁻¹)
      (Submodule.subset_span hsx)
    convert h2 using 1
    funext i
    simp [Algebra.smul_def, hs0]
  apply top_unique
  intro x hx
  have hrange : LinearMap.range (B : Matrix (Fin n) (Fin n) K).mulVecLin ≤
      Submodule.span K (M : Set (Fin n → K)) := by
    rw [Matrix.range_mulVecLin]
    exact Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hcol j)
  apply hrange
  refine ⟨(B⁻¹ : GL (Fin n) K).val *ᵥ x, ?_⟩
  change B.val *ᵥ ((B⁻¹).val *ᵥ x) = x
  rw [Matrix.mulVec_mulVec, show B.val * (B⁻¹).val = 1 from B.mul_inv, Matrix.one_mulVec]
variable {ι : Type} [Fintype ι] {a : ℕ}


open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] [NumberField K] in
variable {ι : Type} [Fintype ι] {a : ℕ} in
omit [NumberField K] in
theorem _root_.GlobalTheory.HAtBasis.polyAction_invTranspose_inv (lam : ι → _root_.Formalism.BasicNotions.DomWeight a)
    (B : ι → GL (Fin a) K) (F : _root_.Formalism.L2.DIV.Pol K ι a) :
    _root_.Formalism.L2.DIV.actP lam (fun τ => _root_.Formalism.BasicNotions.inside₂ K a (B τ))⁻¹ F =
      (∏ τ, (B τ : Matrix (Fin a) (Fin a) K).det ^ (lam τ).detShift) •
        _root_.Formalism.GradedWeylDivisibility.blockAct K (fun τ => (B τ : Matrix (Fin a) (Fin a) K)) F := by
  have hg : ∀ τ, (((fun τ => _root_.Formalism.BasicNotions.inside₂ K a (B τ))⁻¹ τ : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) =
      (B τ : Matrix (Fin a) (Fin a) K)ᵀ := fun τ => rfl
  simp only [_root_.Formalism.L2.DIV.actP, _root_.Formalism.L2.DIV.trAct, _root_.Formalism.L2.DIV.detTw_eq, LinearMap.smul_apply, AlgHom.toLinearMap_apply, hg,
    Matrix.det_transpose, Matrix.transpose_transpose]

open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] [NumberField K] in
variable {ι : Type} [Fintype ι] {a : ℕ} in
private theorem valuation_coe_eq_one_of_notMem {K : Type} [Field K] [NumberField K]
    (w : HeightOneSpectrum (𝓞 K)) {s : 𝓞 K} (hs : s ∉ w.asIdeal) : w.valuation K (s : K) = 1 := by
  rw [show (s : K) = algebraMap (𝓞 K) K s from rfl, HeightOneSpectrum.valuation_of_algebraMap]
  exact (HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl w s).2 hs

open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] [NumberField K] in
variable {ι : Type} [Fintype ι] {a : ℕ} in
private theorem exists_notMem_mul_eq_integer_of_valuation_le_one {K : Type} [Field K] [NumberField K]
    (w : HeightOneSpectrum (𝓞 K)) (x : K) (hx : w.valuation K x ≤ 1) :
    ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ ∃ c : 𝓞 K, (s : K) * x = (c : K) := by
  have h1 : x ∈ (w.valuation K).valuationSubring := hx
  rw [← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring] at h1
  have h3 : x ∈ (HeightOneSpectrum.valuationSubringAtPrime K w).toSubring := h1
  rw [HeightOneSpectrum.valuationSubringAtPrime_toSubring] at h3
  have h2 : x ∈ _root_.GlobalTheory.LatBasisAt.locRing w := by
    unfold _root_.GlobalTheory.LatBasisAt.locRing
    exact h3
  obtain ⟨c, s, hs, rfl⟩ := (_root_.GlobalTheory.LatBasisAt.mem_locRing w x).1 h2
  refine ⟨s, hs, c, ?_⟩
  have hs0 : algebraMap (𝓞 K) K s ≠ 0 := _root_.GlobalTheory.LatBasisAt.algebraMap_ne_zero w hs
  change algebraMap (𝓞 K) K s * (algebraMap (𝓞 K) K c * (algebraMap (𝓞 K) K s)⁻¹) =
    algebraMap (𝓞 K) K c
  field_simp


open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] [NumberField K] in
variable {ι : Type} [Fintype ι] {a : ℕ} in
theorem _root_.GlobalTheory.HAtBasis.mem_HAt_iff : ∀ (K : Type) [Field K]
    [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (ι : Type) [Fintype ι] (a : ℕ)
    (lam : ι → _root_.Formalism.BasicNotions.DomWeight a) (M : ι → Submodule (𝓞 K) (Fin a → K)) (B : ι → GL (Fin a) K),
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.LatWithBasis w M B → ∀ F : _root_.Formalism.L2.DIV.VV K lam,
      F ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.HAt w lam M ↔
        ∀ m, w.valuation K (((∏ τ, (B τ : Matrix (Fin a) (Fin a) K).det ^ (lam τ).detShift) •
          _root_.Formalism.GradedWeylDivisibility.blockAct K (fun τ => (B τ : Matrix (Fin a) (Fin a) K)) (F : _root_.Formalism.L2.DIV.Pol K ι a)).coeff m) ≤ 1 := by
  intro K _ _ w ι _ a lam M B hMB F
  have hB' : ∀ τ, _root_.Formalism.L2.DIV.IsBasisAt w (_root_.Formalism.L2.DIV.dualFr (M τ)) (_root_.Formalism.BasicNotions.inside₂ K a (B τ)) :=
    fun τ => _root_.GlobalTheory.DualWeylDual.isBasisAt_dualFr w (hMB τ).1 (hMB τ).2
  have hlat : ∀ τ, Submodule.IsFullLattice K (_root_.Formalism.L2.DIV.dualFr (M τ)) := fun τ =>
    _root_.GlobalTheory.DualLat.isLattice_dualFr _ (_root_.GlobalTheory.HAtBasis.isLattice_of_basisAt w (hMB τ).1 (hMB τ).2)
  have hloc := (_root_.GlobalTheory.TransLoc.nabDelLoc_free_leVV.1 K ι a lam
    (fun τ => _root_.Formalism.L2.DIV.dualFr (M τ)) hlat w (fun τ => _root_.Formalism.BasicNotions.inside₂ K a (B τ)) hB').1
  have step1 : F ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.HAt w lam M ↔
      (F : _root_.Formalism.L2.DIV.Pol K ι a) ∈ _root_.Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (_root_.Formalism.L2.DIV.nabP lam fun τ => _root_.Formalism.L2.DIV.dualFr (M τ)) := by
    unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.HAt _root_.Formalism.L2.DIV.nabK
    rw [_root_.PI.LocGlobInclWork.mem_localization_iff, _root_.PI.LocGlobInclWork.mem_localization_iff]
    rfl
  rw [step1, hloc, _root_.GlobalTheory.TransLoc.mem_map_actP, _root_.GlobalTheory.HAtBasis.polyAction_invTranspose_inv]
  set G : _root_.Formalism.L2.DIV.Pol K ι a := (∏ τ, (B τ : Matrix (Fin a) (Fin a) K).det ^ (lam τ).detShift) •
    _root_.Formalism.GradedWeylDivisibility.blockAct K (fun τ => (B τ : Matrix (Fin a) (Fin a) K)) (F : _root_.Formalism.L2.DIV.Pol K ι a) with hG
  have hcoeff : ∀ (s : 𝓞 K) m, AddMonoidAlgebra.coeff (s • G) m = (s : K) * AddMonoidAlgebra.coeff G m := by
    intro s m
    erw [Algebra.smul_def, MvPolynomial.algebraMap_apply, coeff_C_mul]
  constructor
  · intro hGm m
    obtain ⟨s, hs, hsG⟩ := (_root_.PI.LocGlobInclWork.mem_localization_iff _ _ _).1 hGm
    obtain ⟨P, hP⟩ := _root_.GlobalTheory.LocInt.exists_map_eq_of_mem_nabStd lam hsG
    have hc : AddMonoidAlgebra.coeff (s • G) m = ((AddMonoidAlgebra.coeff P m : 𝓞 K) : K) := by
      have h' : AddMonoidAlgebra.coeff (_root_.Formalism.L2.DIV.toK K _ P) m = AddMonoidAlgebra.coeff (s • G) m := congrArg (AddMonoidAlgebra.coeff · m) hP
      rw [← h']
      simp [_root_.Formalism.L2.DIV.toK, coeff_map]
    rw [hcoeff] at hc
    have hs0 : (s : K) ≠ 0 := _root_.GlobalTheory.LatBasisAt.algebraMap_ne_zero w hs
    have e : AddMonoidAlgebra.coeff G m = (s : K)⁻¹ * ((AddMonoidAlgebra.coeff P m : 𝓞 K) : K) := by
      rw [← hc, ← mul_assoc, inv_mul_cancel₀ hs0, one_mul]
    rw [e, map_mul, map_inv₀, valuation_coe_eq_one_of_notMem w hs, inv_one, one_mul]
    exact HeightOneSpectrum.valuation_le_one w _
  · intro hint
    choose sf hsf c hc using fun m => exists_notMem_mul_eq_integer_of_valuation_le_one w _ (hint m)
    refine (_root_.PI.LocGlobInclWork.mem_localization_iff _ _ _).2 ⟨∏ m ∈ G.support, sf m, ?_, ?_⟩
    · intro hmem
      obtain ⟨m, _, hm⟩ := Ideal.IsPrime.prod_mem_iff.1 hmem
      exact hsf m hm
    · have hGV : G ∈ _root_.Formalism.L2.DIV.VV K lam :=
        Submodule.smul_mem _ _ (_root_.Formalism.L2.DIV.ps_blockAct_mem_VV lam _ F.2)
      refine _root_.GlobalTheory.DetSat.mem_nabStd_of_det_mul_integral K ι a lam (fun _ => 0) _
        (Submodule.smul_of_tower_mem _ _ hGV) fun m => ?_
      simp only [pow_zero, Finset.prod_const_one, one_mul]
      change IsIntegral ℤ (AddMonoidAlgebra.coeff ((∏ m ∈ G.support, sf m) • G) m)
      rw [hcoeff]
      by_cases hm : m ∈ G.support
      · rw [← Finset.mul_prod_erase _ _ hm]
        push_cast
        rw [mul_comm ((sf m : 𝓞 K) : K), mul_assoc, hc m]
        have hI := RingOfIntegers.isIntegral_coe ((∏ i ∈ G.support.erase m, sf i) * c m)
        convert hI using 1
        simp
      · rw [notMem_support_iff.1 hm, mul_zero]
        exact isIntegral_zero

end GlobalTheory.HAtBasis
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

noncomputable section

namespace GlobalTheory.MuOffMove

variable {X : Fields} {Pr : Primes X} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S}

theorem ordDet_congr {E : Type} [Field E] [NumberField E] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)}
    {N₁ N₂ : Submodule (𝓞 E) (Sp E n)} (h : localization₂ P.asIdeal N₁ = localization₂ P.asIdeal N₂) : ordDet P N₁ = ordDet P N₂ := by
  unfold ordDet frameAt
  rw [h]

theorem under_conjP (hX : X.Ok) (Q : HeightOneSpectrum (𝓞 X.E)) :
    (conjPrime₂ Q).asIdeal.under (𝓞 X.F) = Q.asIdeal.under (𝓞 X.F) := by
  ext r
  have e : cO X.E (algebraMap (𝓞 X.F) (𝓞 X.E) r) = algebraMap (𝓞 X.F) (𝓞 X.E) r :=
    RingOfIntegers.ext (hX.star_F (r : X.F))
  rw [Ideal.under_def, Ideal.under_def, Ideal.mem_comap, Ideal.mem_comap, mem_conjP, e]

theorem natCast_mem_under (Q : HeightOneSpectrum (𝓞 X.E)) (p : ℕ) :
    ((p : ℕ) : 𝓞 X.F) ∈ Q.asIdeal.under (𝓞 X.F) ↔ ((p : ℕ) : 𝓞 X.E) ∈ Q.asIdeal := by
  rw [Ideal.under_def, Ideal.mem_comap, map_natCast]

theorem good_of_mem_QE {P : HeightOneSpectrum (𝓞 X.E)} (h : P ∈ QE sel (mu : Chr X.F X.E X.K)) :
    ∃ v, GoodPl X.E S v ∧ sel v = P := by
  classical
  unfold QE at h
  split_ifs at h with h2
  · obtain ⟨v, hv, e⟩ := Finset.mem_image.1 h
    have hv1 : v ∈ Qprime (mu : Chr X.F X.E X.K) := by simpa using hv
    refine ⟨v, ?_, e⟩
    by_contra hn
    have h4 := (Subgroup.mem_inf.1 mu.2).2
    exact hv1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h4 v) hn)
  · simp at h

theorem notMem_of_mem_QE (hsel : IsSel X sel) {P : HeightOneSpectrum (𝓞 X.E)} (h : P ∈ QE sel (mu : Chr X.F X.E X.K))
    {l : ℕ} (hl : l.Prime) (hS : l ∈ S) : (l : 𝓞 X.E) ∉ P.asIdeal := by
  intro hm
  obtain ⟨v, hgood, e⟩ := good_of_mem_QE h
  have h5 : (l : 𝓞 X.F) ∈ v.asIdeal := by
    rw [← hsel v, e, Ideal.under_def, Ideal.mem_comap, map_natCast]
    exact hm
  apply hgood.2.2
  have h6 : ringChar (𝓞 X.F ⧸ v.asIdeal) ∣ l := by
    rw [← ringChar.spec, ← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact h5
  haveI := v.isPrime
  rcases (Nat.dvd_prime hl).1 h6 with h7 | h7
  · exact absurd h7 CharP.ringChar_ne_one
  · change ringChar (𝓞 X.F ⧸ v.asIdeal) ∈ S
    rw [h7]
    exact hS

theorem level_notMem_rowSG (hPr : Pr.Ok) (hsel : IsSel X sel) {u : Pr.Word} (hS : Pr.T u ∈ S)
    {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ rowSG Pr sel mu) : (Pr.T u : 𝓞 X.E) ∉ P.asIdeal := by
  classical
  rcases Finset.mem_union.1 hP with h | h
  · exact T_notMem_vGs hPr u ⟨P, h⟩
  · exact notMem_of_mem_QE hsel h (hPr.T_prime u) hS

theorem mem_vT (hPr : Pr.Ok) (u : Pr.Word) (P : HeightOneSpectrum (𝓞 X.E)) : P ∈ Pr.vT u ↔ Pr.piT u ∈ P.asIdeal := by
  have h0 : Pr.piT u ≠ 0 := by
    refine left_ne_zero_of_mul (b := X.conjO (Pr.piT u)) ?_
    rw [hPr.piT_norm u]
    exact_mod_cast (hPr.T_prime u).ne_zero
  refine ⟨decoFin_mem_of_mem_divs, fun h => ?_⟩
  unfold Primes.vT divs
  have hf : {P : HeightOneSpectrum (𝓞 X.E) | Pr.piT u ∈ P.asIdeal}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {Pr.piT u}) (by simpa using h0)).subset fun Q hQ => ?_
    exact Ideal.dvd_span_singleton.2 hQ
  rw [dite_eq_left hf]
  simpa using h

theorem conjP_notMem_vT (hPr : Pr.Ok) {u : Pr.Word} {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Pr.vT u) : conjPrime₂ P ∉ Pr.vT u :=
  fun h => conj_piT_notMem hPr u ⟨P, hP⟩ ((mem_conjP _ _).1 ((mem_vT hPr u _).1 h))


open Classical in
def term (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (SB : Finset (HeightOneSpectrum (𝓞 X.E)))
    (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) {n : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E n)) (v : HeightOneSpectrum (𝓞 X.F)) : X.K :=
  if ∃ P ∈ SB, P.asIdeal.under (𝓞 X.F) = v.asIdeal then 1 else ((mU (sel v) ^ ordDet (sel v) N : X.Kˣ) : X.K)

theorem term_finite (hsel : IsSel X sel) (SB : Finset (HeightOneSpectrum (𝓞 X.E)))
    (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) {n : ℕ} {N : Submodule (𝓞 X.E) (Sp X.E n)} (hN : IsSdLat N) :
    (Function.mulSupport (term sel SB mU N)).Finite := by
  have hinj : Function.Injective sel := fun v w h => HeightOneSpectrum.ext (by rw [← hsel v, h, hsel w])
  refine ((GlobalTheory.OrdDetConj.ordDet_conj_finite X.E n N hN).2.preimage hinj.injOn).subset fun v hv h0 => hv ?_
  unfold term
  split_ifs
  · rfl
  · rw [h0, zpow_zero, Units.val_one]

open Classical in
theorem term_eq (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) {u : Pr.Word} (hS : Pr.T u ∈ S)
    {mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ} (hU : ∀ P ∈ Pr.vT u, mU (conjPrime₂ P) = (mU P)⁻¹) {n : ℕ}
    {N₁ N₂ : Submodule (𝓞 X.E) (Sp X.E n)} (h₁ : IsSdLat N₁) (h₂ : IsSdLat N₂) (hA : AgreeOff (Pr.T u) N₁ N₂)
    (v : HeightOneSpectrum (𝓞 X.F)) :
    term sel (rowSG Pr sel mu) mU N₁ v =
      (∏ P ∈ Pr.vT u with P.under (𝓞 X.F) = v, ((mU P ^ (-idxExp P N₁ N₂) : X.Kˣ) : X.K)) * term sel (rowSG Pr sel mu) mU N₂ v := by
  by_cases hv : ∃ P ∈ Pr.vT u, P.under (𝓞 X.F) = v
  · obtain ⟨P, hP, hPv⟩ := hv
    have hPv' : P.asIdeal.under (𝓞 X.F) = v.asIdeal := congrArg HeightOneSpectrum.asIdeal hPv
    have hc := conjP_notMem_vT hPr hP
    have hsp := (split_of_conj_ne₂ X P v hX (fun e => hc (e.symm ▸ hP)) hPv').2
    have hfil : (Pr.vT u).filter (fun Q => Q.under (𝓞 X.F) = v) = {P} := by
      ext Q
      rw [Finset.mem_filter, Finset.mem_singleton]
      refine ⟨fun ⟨hQ, hQv⟩ => ?_, fun e => e ▸ ⟨hP, hPv⟩⟩
      exact ((hsp Q).1 (congrArg HeightOneSpectrum.asIdeal hQv)).resolve_right fun e => hc (e ▸ hQ)
    have hno : ¬ ∃ Q ∈ rowSG Pr sel mu, Q.asIdeal.under (𝓞 X.F) = v.asIdeal := by
      rintro ⟨Q, hQ, hQv⟩
      refine level_notMem_rowSG hPr hsel hS hQ ?_
      rw [← natCast_mem_under, hQv, ← hPv', natCast_mem_under]
      exact T_mem hPr u ⟨P, hP⟩
    unfold term
    rw [hfil, Finset.prod_singleton, if_neg hno, if_neg hno, ← Units.val_mul]
    congr 1
    unfold idxExp
    rcases (hsp (sel v)).1 (hsel v) with e | e
    · rw [e, ← zpow_add]
      congr 1
      ring
    · rw [e, hU P hP, GlobalTheory.OrdDetConj.ordDet_conjP h₁, GlobalTheory.OrdDetConj.ordDet_conjP h₂, inv_zpow', inv_zpow', ← zpow_add]
      congr 1
      ring
  · have hfil : (Pr.vT u).filter (fun Q => Q.under (𝓞 X.F) = v) = ∅ :=
      Finset.filter_eq_empty_iff.2 fun Q hQ e => hv ⟨Q, hQ, e⟩
    have hT : ((Pr.T u : ℕ) : 𝓞 X.E) ∉ (sel v).asIdeal := by
      intro h
      rw [← hPr.piT_norm u] at h
      rcases (sel v).isPrime.mem_or_mem h with h | h
      · exact hv ⟨sel v, (mem_vT hPr u _).2 h, HeightOneSpectrum.ext (hsel v)⟩
      · exact hv ⟨conjPrime₂ (sel v), (mem_vT hPr u _).2 ((mem_conjP _ _).2 h),
          HeightOneSpectrum.ext ((under_conjP hX _).trans (hsel v))⟩
    unfold term
    rw [hfil, Finset.prod_empty, one_mul, ordDet_congr (hA _ hT)]

theorem muOff_move : ∀ (X : Fields) (Pr : Primes X) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (u : Pr.Word) (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) (n : ℕ) (N₁ N₂ : Submodule (𝓞 X.E) (Sp X.E n)), X.Ok → Pr.Ok → IsSel X sel → Pr.T u ∈ S → (∀ k, Pr.g k ∈ S) → (∀ P ∈ Pr.vT u, mU (conjPrime₂ P) = (mU P)⁻¹) → IsSdLat N₁ → IsSdLat N₂ → AgreeOff (Pr.T u) N₁ N₂ → muOff sel (rowSG Pr sel mu) mU N₁ = (∏ P ∈ Pr.vT u, ((mU P ^ (-idxExp P N₁ N₂) : X.Kˣ) : X.K)) * muOff sel (rowSG Pr sel mu) mU N₂ := by
  intro X Pr sel S mu u mU n N₁ N₂ hX hPr hsel hS _ hU h₁ h₂ hA
  classical
  change ∏ᶠ v, term sel (rowSG Pr sel mu) mU N₁ v = _ * ∏ᶠ v, term sel (rowSG Pr sel mu) mU N₂ v
  have hsub : Function.mulSupport (fun v : HeightOneSpectrum (𝓞 X.F) =>
      ∏ P ∈ Pr.vT u with P.under (𝓞 X.F) = v, ((mU P ^ (-idxExp P N₁ N₂) : X.Kˣ) : X.K)) ⊆
      ((Pr.vT u).image fun P => P.under (𝓞 X.F) : Finset _) := by
    intro v hv
    by_contra hn
    apply hv
    refine Finset.prod_eq_one fun P hP => absurd ?_ hn
    rw [Finset.mem_filter] at hP
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨P, hP.1, hP.2⟩)
  rw [finprod_congr (term_eq (mu := mu) hX hPr hsel hS hU h₁ h₂ hA),
    finprod_mul_distrib ((Finset.finite_toSet _).subset hsub) (term_finite hsel _ mU h₂),
    finprod_eq_prod_of_mulSupport_subset _ hsub,
    Finset.prod_fiberwise_of_maps_to (g := fun P : HeightOneSpectrum (𝓞 X.E) => P.under (𝓞 X.F))
      fun P hP => Finset.mem_image_of_mem (fun P : HeightOneSpectrum (𝓞 X.E) => P.under (𝓞 X.F)) hP]

end GlobalTheory.MuOffMove
end
end

section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

theorem _root_.GlobalTheory.T.evenThetaFunction_cmLattice_integral_splitPrime : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → jacobiSym (-(D.host.d : ℤ)) q = 1 → Nat.Coprime (Ideal.absNorm cc) q → ∀ (ι : ℂ ≃+* ℂ_[q]) (δ₀ : ℂ) (θ : ℂ → ℂ) (Ω : ℂ_[q]), Per D.host.d ι δ₀ θ Ω → LatInt ι (Ω / ι δ₀) (lamOf D cc δ) B.th0 := by
  first | exact @GlobalTheory.MomN.latInt_th0_of_split_prime | exact GlobalTheory.MomN.latInt_th0_of_split_prime | (intros; apply GlobalTheory.MomN.latInt_th0_of_split_prime <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.SWQ.LamExists

theorem re_mul_of_isReal {F : Type} [Field F] [NumberField F] (hF : IsTotallyReal F) (a : F) (x : Ainf F)
    (w : InfinitePlace F) : re (algebraMap F (Ainf F) a * x) w = re (algebraMap F (Ainf F) a) w * re x w := by
  have hr : (InfinitePlace.Completion.extensionEmbedding w (algebraMap F (Ainf F) a w)).im = 0 := by
    rw [InfiniteAdeleRing.algebraMap_apply]
    rw [InfinitePlace.Completion.extensionEmbedding_coe]
    have := InfinitePlace.isReal_iff.1 (hF.isReal w)
    exact Complex.conj_eq_iff_im.1 (RingHom.congr_fun this a)
  show (InfinitePlace.Completion.extensionEmbedding w (algebraMap F (Ainf F) a w * x w)).re = _
  rw [map_mul, Complex.mul_re, hr, zero_mul, sub_zero]
  rfl

theorem re_ne_zero {F : Type} [Field F] [NumberField F] (a : F) (ha : a ≠ 0) (w : InfinitePlace F)
    (hF : IsTotallyReal F) : re (algebraMap F (Ainf F) a) w ≠ 0 := by
  have hr : (InfinitePlace.Completion.extensionEmbedding w (algebraMap F (Ainf F) a w)).im = 0 := by
    rw [InfiniteAdeleRing.algebraMap_apply]
    rw [InfinitePlace.Completion.extensionEmbedding_coe]
    have := InfinitePlace.isReal_iff.1 (hF.isReal w)
    exact Complex.conj_eq_iff_im.1 (RingHom.congr_fun this a)
  intro h0
  have : InfinitePlace.Completion.extensionEmbedding w (algebraMap F (Ainf F) a w) = 0 :=
    Complex.ext h0 hr
  rw [InfiniteAdeleRing.algebraMap_apply] at this
  rw [InfinitePlace.Completion.extensionEmbedding_coe, map_eq_zero] at this
  exact ha this

end GlobalTheory.SWQ.LamExists

theorem GlobalTheory.SWQ.exists_isLam : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∃ lam, IsLam ψ lam := by
  intro F _ _ hF ψ hψ
  haveI := hF
  obtain ⟨ψ₀, h₀⟩ := GlobalTheory.SnMass.Inhab.exists_isStdChar F
  obtain ⟨a, ha, h⟩ := GlobalTheory.AdeleCharTwist.exists_mul_eq F ψ₀ ψ h₀.1 hψ
  refine ⟨fun w => re (algebraMap F (Ainf F) a) w, fun w => GlobalTheory.SWQ.LamExists.re_ne_zero a ha w hF, fun x => ?_⟩
  rw [GlobalTheory.GaugeEx.CharLoc.psiInf_twist h, h₀.2.1]
  exact congrArg (fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I * (t : ℂ)))
    (Finset.sum_congr rfl fun w _ => GlobalTheory.SWQ.LamExists.re_mul_of_isReal hF a x w)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

theorem _root_.GlobalTheory.T.periodLattice_halfLattice_inclusions_splitPrime : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (S SG : Finset (HeightOneSpectrum (𝓞 X.E))) (ϖ : 𝓞 X.E) (p g cA : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), Ctx A a b S SG ϖ p g cA → IsSdLat N → IsSdLat N' → A.AA ≠ ⊥ ∧ (∀ y ∈ per A N N', ((g : X.E) * ((ϖ : X.E) / star (ϖ : X.E))) • y ∈ halfBO S (per A N N') (p * g)) ∧ (∀ y ∈ halfBO S (per A N N') (p * g), ((g : X.E) * (star (ϖ : X.E) / (ϖ : X.E))) • y ∈ per A N N') ∧ (∀ x ∈ divLat cA (homAt S N N'), x ∈ homAt (divs ϖ) N N' → ∀ t ∈ halfAO S (per A N N') (cA * (p * g)), t - x ∈ mulLat (p * g) (homAt S N N') → ((cA * g : ℕ) : X.E) • t ∈ per A N N') ∧ (∀ y ∈ per A N N', y ∈ homAt S N N' ∧ (((cA * g : ℕ) : X.E) * star (ϖ : X.E)) • y ∈ halfAO S (per A N N') (cA * (p * g)) ∧ (((cA * g : ℕ) : X.E) * star (ϖ : X.E)) • y ∈ mulLat (p * g) (homAt SG N N') ∧ ((((cA * g : ℕ) : X.E) * star (ϖ : X.E)) • y ∈ mulLat (p * g) (homAt S N N') ↔ y ∈ smulLat (ϖ : X.E) (per A N N'))) ∧ (∀ (y : HomE X.E a b) (n : ℕ), Nat.Coprime n p → (n : X.E) • y ∈ smulLat ((ϖ : X.E) / star (ϖ : X.E)) (per A N N') → y ∈ mulLat p (homAt (divs ϖ) N N')) ∧ (∀ x ∈ halfBO S (per A N N') (p * g), ∀ y ∈ halfBO S (per A N N') (p * g), ∃ n : ℤ, coc A x y = n) ∧ ∀ x ∈ halfAO S (per A N N') (cA * (p * g)), ∀ y ∈ halfAO S (per A N N') (cA * (p * g)), ∃ n : ℤ, coc A x y = n := by
  first | exact @GlobalTheory.MomT.HalfIncl.half_inclusions | exact GlobalTheory.MomT.HalfIncl.half_inclusions | (intros; apply GlobalTheory.MomT.HalfIncl.half_inclusions <;> assumption)
end

section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.lattice_stabilizer_doubleCosets_classRest_mass : ∀ D : D7, DefClassRest D := by
  first | exact @GlobalTheory.ClassRestObj.defClassRest | exact GlobalTheory.ClassRestObj.defClassRest | (intros; apply GlobalTheory.ClassRestObj.defClassRest <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Forms

theorem _root_.GlobalTheory.T.admissiblePeriodTwists_reduction_placeTuples : ∀ (D : D7) (Dx : DivX D) (T : TwForms D), (∀ u μ, μ ≠ D.what₂.mu0 → (∃ w, μ = D.what₂.muAt w) → Formalism.MainNotions.RT.PeriodPointConditions.PerDecTw D Dx T u μ) → Formalism.L2.G.Adm2InU.TwistedPeriodAdmissible D Dx T := by
  first | exact @GlobalTheory.PerRedU.main | exact GlobalTheory.PerRedU.main | (intros; apply GlobalTheory.PerRedU.main <;> assumption)
end
