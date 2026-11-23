module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle116
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle229
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AutomorphicFormsFiniteIdeal
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle098
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle042
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmoothFunctionsOfClosedRightDerivatives
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.KoszulLowersPower
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SpecialLinearGeneratedByTransvections
public import Formalism.LocalRingCardinality.DataHost
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

namespace GlobalTheory.RealPairBound

theorem trace_conjT_mul_single {r s : ℕ} (X : Matrix (Fin r) (Fin s) ℂ) (i : Fin r) (j : Fin s) (a : ℂ) :
    (Xᴴ * Matrix.single i j a).trace = star (X i j) * a := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply, ite_and]

theorem gramAt_det_ne (D : D7) (T : HSp D) (τ : D.what₂.Tau) : (gramAt D T τ).det ≠ 0 := by
  rw [gramAt, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (map_ne_zero _).2 (Formalism.L2.Theta.gram_det_ne T)

theorem pair_single (D : D7) (T : HSp D) {ρ : ℕ} (τ : D.what₂.Tau) (X : Matrix (Fin T.rank) (Fin ρ) ℂ)
    (i : Fin T.rank) (j : Fin ρ) (a : ℂ) :
    tauE D τ D.host.xi0 * (Xᴴ * gramAt D T τ * ((gramAt D T τ)⁻¹ * Matrix.single i j a)).trace
      = tauE D τ D.host.xi0 * (star (X i j) * a) := by
  have hu : IsUnit (gramAt D T τ).det := isUnit_iff_ne_zero.2 (gramAt_det_ne D T τ)
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (gramAt D T τ), Matrix.mul_nonsing_inv _ hu, Matrix.one_mul,
    trace_conjT_mul_single]

theorem realSize_le_pairing : ∀ (D : D7) (θ : InfFam D) (T : HSp D) (ρ : ℕ), ∃ (k : ℕ) (τs : Fin k → D.what₂.Tau)
    (zs : Fin k → Matrix (Fin T.rank) (Fin ρ) ℂ) (C : ℝ), ∀ x : Mx D T.rank ρ,
      realSize θ x ≤ C * ∑ i, |2 * (tauE D (τs i) D.host.xi0 * ((compAt θ (τs i) x)ᴴ * gramAt D T (τs i) * zs i).trace).re| := by
  intro D θ T ρ
  classical
  let c : D.what₂.Tau → ℂ := fun τ => tauE D τ D.host.xi0
  have hc : ∀ τ, c τ ≠ 0 := fun τ => (map_ne_zero _).2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)
  let α : D.what₂.Tau → Bool → ℂ := fun τ b => if b then (c τ)⁻¹ * Complex.I else (c τ)⁻¹
  let z : D.what₂.Tau × Fin T.rank × Fin ρ × Bool → Matrix (Fin T.rank) (Fin ρ) ℂ :=
    fun p => (gramAt D T p.1)⁻¹ * Matrix.single p.2.1 p.2.2.1 (α p.1 p.2.2.2)
  let e := (Fintype.equivFin (D.what₂.Tau × Fin T.rank × Fin ρ × Bool)).symm
  refine ⟨_, fun n => (e n).1, fun n => z (e n), 1, fun x => ?_⟩
  rw [one_mul]
  let v : D.what₂.Tau × Fin T.rank × Fin ρ × Bool → ℝ := fun p =>
    |2 * (tauE D p.1 D.host.xi0 * ((compAt θ p.1 x)ᴴ * gramAt D T p.1 * z p).trace).re|
  change realSize θ x ≤ ∑ n, v (e n)
  rw [Equiv.sum_comp e v, Fintype.sum_prod_type, realSize]
  refine Finset.sum_le_sum fun τ _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [Fintype.sum_bool]
  have hv : ∀ b, v (τ, i, j, b) = |2 * (c τ * (star (compAt θ τ x i j) * α τ b)).re| := fun b => by
    simp only [v, z]
    rw [pair_single]
  rw [hv, hv]
  have h1 : c τ * (star (compAt θ τ x i j) * α τ true) = star (compAt θ τ x i j) * Complex.I := by
    simp only [α, if_true]
    field_simp [hc τ]
  have h0 : c τ * (star (compAt θ τ x i j) * α τ false) = star (compAt θ τ x i j) := by
    simp only [α, Bool.false_eq_true, if_false]
    field_simp [hc τ]
  rw [h1, h0]
  have hn := Complex.norm_le_abs_re_add_abs_im (compAt θ τ x i j)
  simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.I_re, Complex.I_im,
    abs_mul, mul_zero, mul_one, zero_sub, abs_neg, abs_two]
  linarith [abs_nonneg (compAt θ τ x i j).re, abs_nonneg (compAt θ τ x i j).im]

end GlobalTheory.RealPairBound
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.BoxSlice

open GlobalTheory.MixModel.OrthDec

variable {D : D7} {S A B : HSp D} (d : GlobalTheory.MixModel.OrthDec S A B)

theorem heisO_zero' (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f : WO S T → ℂ) : heisO ψ S T 0 f = f := by
  funext w
  simp only [heisO, GlobalTheory.MixModel.symplOH_zero_right, AddChar.map_zero_eq_one, one_mul, add_zero]

theorem resS_symm_left (T : HSp D) (u : WO A T) :
    (d.resS T).symm (u, 0) = GlobalTheory.MixModel.sandwich (1 : Mx D T.rank T.rank) d.pA u := by
  rw [resS_symm_apply, GlobalTheory.MixModel.sandwich_apply, Matrix.one_mul, Matrix.zero_mul, add_zero]

theorem isThetaFunO_slice_left {ψ : AddChar (AF D.host.F) ℂ} {T : HSp D} {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (v : WO B T) : IsThetaFunO ψ A T fun u => f ((d.resS T).symm (u, v)) := {
  quasi γ u := by
    have e0 : (d.resS T).symm (ratW T A γ, 0) = ratW T S (γ * d.qA) := by
      rw [resS_symm_apply, Matrix.zero_mul, add_zero, ratW_eq, ratW_eq, rat_mul]; rfl
    have e : ((ratW T A γ + u, v) : WO A T × WO B T) = (ratW T A γ, (0 : WO B T)) + (u, v) := by simp
    show f ((d.resS T).symm (ratW T A γ + u, v)) = ψ (-(symplOH A T (ratW T A γ) u)) * f ((d.resS T).symm (u, v))
    rw [e, map_add (f := _), e0, hf.quasi, ← e0, d.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
      GlobalTheory.MixModel.symplOH_zero_left, add_zero]
  level := by
    obtain ⟨U, hU, k⟩ := hf.level
    refine ⟨U.comap (GlobalTheory.MixModel.sandwich (1 : Mx D T.rank T.rank) d.pA),
      hU.preimage (GlobalTheory.MixModel.continuous_sandwich _ _), fun u hu h0 => ?_⟩
    funext w
    have e1 := congrFun (k _ hu (GlobalTheory.MixModel.map_sandwich _ _ _ h0)) ((d.resS T).symm (w, v))
    rw [← resS_symm_left] at e1
    simp only [heisO] at e1 ⊢
    rw [← e1, ← map_add (d.resS T).symm, Prod.mk_add_mk, add_zero, d.symplOH_resS, AddEquiv.apply_symm_apply,
      AddEquiv.apply_symm_apply, GlobalTheory.MixModel.symplOH_zero_right, add_zero]
  cont := hf.cont.comp ((d.continuous_resS_symm T).comp (continuous_id.prodMk continuous_const))
  smooth k L hL h0 w := by
    have e : ∀ t, (d.resS T).symm (w + L t, v) =
        (d.resS T).symm (w, v) + ((GlobalTheory.MixModel.sandwich (1 : Mx D T.rank T.rank) d.pA).comp L) t := by
      intro t
      rw [AddMonoidHom.comp_apply, ← resS_symm_left, ← map_add (d.resS T).symm, Prod.mk_add_mk, add_zero]
    simp only [e]
    exact hf.smooth k ((GlobalTheory.MixModel.sandwich (1 : Mx D T.rank T.rank) d.pA).comp L)
      ((GlobalTheory.MixModel.continuous_sandwich _ _).comp hL) (fun t => GlobalTheory.MixModel.map_sandwich _ _ _ (h0 t)) _ }

theorem isThetaFunO_slice_right {ψ : AddChar (AF D.host.F) ℂ} {T : HSp D} {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (u : WO A T) : IsThetaFunO ψ B T fun v => f ((d.resS T).symm (u, v)) := by
  have h := isThetaFunO_slice_left d.symm hf u
  have e : ∀ v, (d.symm.resS T).symm (v, u) = (d.resS T).symm (u, v) := fun v => by
    rw [resS_symm_apply, resS_symm_apply, add_comm]; rfl
  simp only [e] at h
  exact h

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S A B T : HSp D) (o : OrthDec S A B), (∀ fA fB, IsThetaFunO ψ A T fA → IsThetaFunO ψ B T fB → IsThetaFunO ψ S T (o.boxS T fA fB)) ∧ (∀ fA fB, o.boxS T fA fB 0 = fA 0 * fB 0) ∧ (∀ fA fB, (∀ u, heisO ψ S T ((o.resS T).symm (u, 0)) (o.boxS T fA fB) = o.boxS T (heisO ψ A T u fA) fB) ∧ ∀ v, heisO ψ S T ((o.resS T).symm (0, v)) (o.boxS T fA fB) = o.boxS T fA (heisO ψ B T v fB)) ∧ ∀ f, IsThetaFunO ψ S T f → (∀ v, IsThetaFunO ψ A T fun u => f ((o.resS T).symm (u, v))) ∧ ∀ u, IsThetaFunO ψ B T fun v => f ((o.resS T).symm (u, v)) := by
  intro D ψ _ S A B T o
  refine ⟨fun fA fB hA hB => o.isThetaFunO_boxS hA hB, fun fA fB => o.boxS_zero T fA fB,
    fun fA fB => ⟨fun u => ?_, fun v => ?_⟩, fun f hf => ⟨fun v => isThetaFunO_slice_left o hf v,
      fun u => isThetaFunO_slice_right o hf u⟩⟩
  · rw [o.heisO_boxS, AddEquiv.apply_symm_apply, heisO_zero']
  · rw [o.heisO_boxS, AddEquiv.apply_symm_apply, heisO_zero']

end GlobalTheory.BoxSlice

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.skewHermitian_tracePairing_standardCharacter_perfect : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ρ : ℕ) (M : Matrix (Fin ρ) (Fin ρ) D.host.E), Mᴴ = -M → (∀ c : skewA D ρ, ψ (algebraMap D.host.F (AF D.host.F) (1 / 2) * Algebra.trace (AF D.host.F) (AE D) ((rat M : Mx D ρ ρ) ⬝ c.1).trace) = 1) → M = 0 := by
  first | exact @GlobalTheory.SkewPairing.skew_perfect | exact GlobalTheory.SkewPairing.skew_perfect | (intros; apply GlobalTheory.SkewPairing.skew_perfect <;> assumption)
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.SkewVol

variable (D : D7) (ρ : ℕ)

def skewPart (x : Mx D ρ ρ) : Mx D ρ ρ := half D • (x - adj x)

variable {D ρ}

theorem skewPart_mem (x : Mx D ρ ρ) : skewPart D ρ x ∈ skewA D ρ := by
  rw [mem_skewA, skewPart, adj_smul, cA_half, adj_sub, adj_adj, ← smul_neg, neg_sub]

theorem skewPart_of_mem {c : Mx D ρ ρ} (hc : c ∈ skewA D ρ) : skewPart D ρ c = c := by
  rw [skewPart, (mem_skewA).1 hc, sub_neg_eq_add, smul_add, half_smul_add]

theorem skewPart_add (x y : Mx D ρ ρ) : skewPart D ρ (x + y) = skewPart D ρ x + skewPart D ρ y := by
  rw [skewPart, skewPart, skewPart, adj_add, add_sub_add_comm, smul_add]

theorem skewPart_rat {x : Mx D ρ ρ} (hx : x ∈ ratMx D ρ ρ) : skewPart D ρ x ∈ ratMx D ρ ρ := by
  obtain ⟨γ, rfl⟩ := (mem_ratMx).1 hx
  refine (mem_ratMx).2 ⟨(1 / 2 : D.host.E) • (γ - γᴴ), ?_⟩
  rw [rat_smul, rat_sub, rat_conjTranspose]; rfl

set_option synthInstance.maxHeartbeats 400000 in
theorem continuous_skewPart : Continuous (skewPart D ρ) :=
  haveI : IsTopologicalAddGroup (Mx D ρ ρ) := (lattice_Mx D ρ ρ).1
  show Continuous fun x => half D • (x - adj x) from (continuous_id.sub continuous_adj).const_smul (half D)

theorem isClosed_skewA : IsClosed (skewA D ρ : Set (Mx D ρ ρ)) :=
  haveI : T2Space (Mx D ρ ρ) := (lattice_Mx D ρ ρ).2.2.2.1
  isClosed_eq continuous_adj continuous_neg

theorem isCoLat_skew :
    GlobalTheory.CuspGeneric.IsCoLat ((ratMx D ρ ρ).addSubgroupOf (skewA D ρ)) := by
  obtain ⟨-, -, -, -, i5, K, hK, hKc⟩ := lattice_Mx D ρ ρ
  refine ⟨?_, ?_⟩
  · let φ : (ratMx D ρ ρ).addSubgroupOf (skewA D ρ) → ratMx D ρ ρ := fun q => ⟨q.1.1, q.2⟩
    have hinj : Function.Injective φ := fun a b h =>
      Subtype.ext (Subtype.ext (by simpa [φ] using congrArg Subtype.val h))
    have hcont : Continuous φ :=
      ((continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _
    exact DiscreteTopology.of_continuous_injective hcont hinj
  · let P : Mx D ρ ρ → skewA D ρ := fun x => ⟨skewPart D ρ x, skewPart_mem x⟩
    have hP : Continuous P := continuous_skewPart.subtype_mk _
    refine ⟨P '' K, hK.image hP, fun x => ?_⟩
    obtain ⟨γ, hγ, hx⟩ := hKc x.1
    refine ⟨P γ, AddSubgroup.mem_addSubgroupOf.2 (skewPart_rat hγ), γ + x.1, hx, ?_⟩
    apply Subtype.ext
    change skewPart D ρ (γ + x.1) = skewPart D ρ γ + x.1
    rw [skewPart_add, skewPart_of_mem x.2]

theorem exists_haar_covol_one : ∀ (D : D7) (ρ : ℕ), ∃ (lC : Measure (skewA D ρ)) (𝓒 : Set (skewA D ρ)), lC.IsAddHaarMeasure ∧ SFinite lC ∧ IsAddFundamentalDomain ((ratMx D ρ ρ).addSubgroupOf (skewA D ρ)) 𝓒 lC ∧ lC 𝓒 = 1 := by
  intro D ρ
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D ρ ρ
  haveI : IsTopologicalAddGroup (Mx D ρ ρ) := i1
  haveI : LocallyCompactSpace (Mx D ρ ρ) := i2
  haveI : SecondCountableTopology (Mx D ρ ρ) := i3
  haveI : T2Space (Mx D ρ ρ) := i4
  haveI : SecondCountableTopology (skewA D ρ) := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : T2Space (skewA D ρ) := Topology.IsEmbedding.subtypeVal.t2Space
  haveI : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  haveI : LocallyCompactSpace (skewA D ρ) := (isClosed_skewA (D := D) (ρ := ρ)).locallyCompactSpace
  obtain ⟨μ, 𝓕, hμ, hF, h1⟩ :=
    GlobalTheory.CuspGeneric.exists_fundamentalDomain_mass_one (skewA D ρ) _ isCoLat_skew
  exact ⟨μ, 𝓕, hμ, inferInstance, hF, h1⟩

end GlobalTheory.SkewVol
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory GlobalTheory.AutFinLit GlobalTheory.Published.AutFin
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies (LieAt LieInf atPlace IsExpFam IsSmoothInf wordDer)
open scoped TensorProduct DirectSum Classical

noncomputable section

namespace GlobalTheory.FrameCompact

open GlobalTheory.SmoothForms Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}
  {ε : D.what₂.Tau → Fin V.rank → Bool} {fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}

def comps (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (k : ∀ τ, Formalism.REAL.KG (ε τ)) : AlgInf V :=
  fun τ => (fr τ)⁻¹ * Formalism.REAL.toMK (k τ) * fr τ

theorem comps_unit (R : RealPoints θ V) (h : IsFrameFam V ε fr) (k : ∀ τ, Formalism.REAL.KG (ε τ)) :
    sigInf V (comps fr k) * comps fr k = 1 :=
  (unit_iff R _).2 fun τ => conj_mem_UH (h τ).1 (h τ).2 (k τ)

theorem continuous_comps : Continuous (comps (ε := ε) fr) := by
  have key : Continuous fun (k : ∀ τ, Formalism.REAL.KG (ε τ)) (τ : D.what₂.Tau) =>
      (fr τ)⁻¹ * Formalism.REAL.toMK (k τ) * fr τ := by
    refine continuous_pi fun τ => ?_
    have h1 : Continuous fun k : Formalism.REAL.KG (ε τ) => Formalism.REAL.toMK k :=
      (Formalism.REAL.isClosedEmbeddingMatrix _ (ε τ)).1.continuous.comp continuous_subtype_val
    exact (continuous_const.matrix_mul (h1.comp (continuous_apply τ))).matrix_mul continuous_const
  exact key

def frameHom (R : RealPoints θ V) (h : IsFrameFam V ε fr) : (∀ τ, Formalism.REAL.KG (ε τ)) →* GA D V :=
  MonoidHom.mk' (fun k => secInf θ V (comps fr k)) fun k l => by
    have a := secInf_spec R (comps_unit R h k)
    have b := secInf_spec R (comps_unit R h l)
    have c := secInf_spec R (comps_unit R h (k * l))
    refine R.2.2.1 _ c.1 _ (mul_mem a.1 b.1) fun τ => ?_
    have hd : IsUnit (fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (h τ).1
    rw [R.2.2.2.1, c.2, a.2, b.2]
    change (fr τ)⁻¹ * (Formalism.REAL.toMK (k τ) * Formalism.REAL.toMK (l τ)) * fr τ =
      (fr τ)⁻¹ * Formalism.REAL.toMK (k τ) * fr τ * ((fr τ)⁻¹ * Formalism.REAL.toMK (l τ) * fr τ)
    simp only [Matrix.mul_assoc]
    rw [mul_nonsing_inv_cancel_left _ _ hd]

theorem frameHom_spec (R : RealPoints θ V) (h : IsFrameFam V ε fr) (k : ∀ τ, Formalism.REAL.KG (ε τ)) :
    frameHom R h k ∈ GinfC V ∧ ∀ τ, infMat D.sp.cm.sig V.gram (θ τ) (frameHom R h k) =
      (fr τ)⁻¹ * Formalism.REAL.toMK (k τ) * fr τ :=
  secInf_spec R (comps_unit R h k)

theorem frameHom_single (hθ : IsInfFam θ) (R : RealPoints θ V) (h : IsFrameFam V ε fr) (τ : D.what₂.Tau)
    (k : Formalism.REAL.KG (ε τ)) : frameHom R h (Pi.mulSingle τ k) = kAt θ V τ (ε τ) (fr τ) k := by
  have a := frameHom_spec R h (Pi.mulSingle τ k)
  have b := isAtTau_kAt θ V hθ τ (h τ).1 (h τ).2 k
  refine R.2.2.1 _ a.1 _ b.1 fun τ' => ?_
  rw [a.2]
  by_cases c : τ' = τ
  · subst c
    rw [b.2.1, Pi.mulSingle_eq_same]
  · rw [b.2.2 _ c, Pi.mulSingle_eq_of_ne c]
    change (fr τ')⁻¹ * 1 * fr τ' = 1
    rw [Matrix.mul_one, nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (h τ').1)]

theorem isCompact_frameRange (hθ : IsInfFam θ) (R : RealPoints θ V) (h : IsFrameFam V ε fr) :
    IsCompact ((frameHom R h).range : Set (GA D V)) := by
  have hc : Continuous (frameHom R h) :=
    (GlobalTheory.Mem.DerClosed.continuousOn_secInf hθ V).comp_continuous continuous_comps (comps_unit R h)
  rw [MonoidHom.coe_range]
  exact _root_.isCompact_range hc

theorem conj_mem_Kset (hθ : IsInfFam θ) (R : RealPoints θ V) (h : IsFrameFam V ε fr) (K' : Subgroup (GA D V))
    (hc : IsCompact (K' : Set (GA D V))) (hle : (frameHom R h).range ≤ K') (τ : D.what₂.Tau) {g : GA D V}
    (hg : g ∈ K') : fr τ * infMat D.sp.cm.sig V.gram (θ τ) g * (fr τ)⁻¹ ∈ Formalism.REAL.Kset (ε τ) := by
  have hd : IsUnit (fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (h τ).1
  let f : GA D V → Matrix (Fin V.rank) (Fin V.rank) ℂ :=
    fun g => fr τ * infMat D.sp.cm.sig V.gram (θ τ) g * (fr τ)⁻¹
  have fc : Continuous f :=
    (continuous_const.matrix_mul (GlobalTheory.Mem.VolExists.continuous_infMat V.gram (hθ τ))).matrix_mul continuous_const
  have fm : ∀ a b, f (a * b) = f a * f b := fun a b => by
    simp only [f, R.2.2.2.1, Matrix.mul_assoc]
    rw [nonsing_inv_mul_cancel_left _ _ hd]
  have fk : ∀ k, f (frameHom R h k) = Formalism.REAL.toMK (k τ) := fun k => by
    simp only [f, (frameHom_spec R h k).2, Matrix.mul_assoc]
    rw [mul_nonsing_inv_cancel_left _ _ hd, mul_nonsing_inv _ hd, Matrix.mul_one]
  have f1 : f 1 = 1 := by
    rw [← map_one (frameHom R h), fk]
    rfl
  have key := GlobalTheory.T.bounded_subgroup_of_indefinite_unitary_eq_maximalCompact V.rank (ε τ) (f '' K') ?_ ?_ ?_ ?_ ?_
  · rw [← key]
    exact ⟨g, hg, rfl⟩
  · rintro _ ⟨a, -, rfl⟩
    have hu : (infMat D.sp.cm.sig V.gram (θ τ) a)ᴴ * gramAt D V τ * infMat D.sp.cm.sig V.gram (θ τ) a = gramAt D V τ :=
      GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V a τ
    have h1 : ((fr τ)⁻¹)ᴴ * (fr τ)ᴴ = 1 := by rw [← conjTranspose_mul, mul_nonsing_inv _ hd, conjTranspose_one]
    change (f a)ᴴ * Formalism.REAL.Jm (ε τ) * f a = Formalism.REAL.Jm (ε τ)
    calc (f a)ᴴ * Formalism.REAL.Jm (ε τ) * f a
        = ((fr τ)⁻¹)ᴴ * ((infMat D.sp.cm.sig V.gram (θ τ) a)ᴴ * ((fr τ)ᴴ * Formalism.REAL.Jm (ε τ) * fr τ) *
            infMat D.sp.cm.sig V.gram (θ τ) a) * (fr τ)⁻¹ := by
          simp only [f, conjTranspose_mul, Matrix.mul_assoc]
      _ = (((fr τ)⁻¹)ᴴ * (fr τ)ᴴ) * Formalism.REAL.Jm (ε τ) * (fr τ * (fr τ)⁻¹) := by
          rw [(h τ).2, hu, ← (h τ).2]
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, mul_nonsing_inv _ hd, Matrix.one_mul, Matrix.mul_one]
  · rw [← Formalism.REAL.range_toMK]
    rintro _ ⟨k, rfl⟩
    refine ⟨frameHom R h (Pi.mulSingle τ k), hle ⟨_, rfl⟩, ?_⟩
    rw [fk, Pi.mulSingle_eq_same]
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact ⟨a * b, mul_mem ha hb, fm a b⟩
  · rintro _ ⟨a, ha, rfl⟩
    refine ⟨a⁻¹, inv_mem ha, (inv_eq_left_inv ?_).symm⟩
    rw [← fm, inv_mul_cancel, f1]
  · have : ∀ i j, ∃ C : ℝ, ∀ a ∈ K', ‖f a i j‖ ≤ C := fun i j =>
      hc.exists_bound_of_continuousOn (fc.matrix_elem i j).continuousOn
    choose C hC using this
    obtain ⟨B, hB⟩ := (Set.finite_range fun p : Fin V.rank × Fin V.rank => C p.1 p.2).bddAbove
    refine ⟨B, ?_⟩
    rintro _ ⟨a, ha, rfl⟩ i j
    exact (hC i j a ha).trans (hB ⟨(i, j), rfl⟩)

theorem isMaxCompactInf_range (hθ : IsInfFam θ) (R : RealPoints θ V) (h : IsFrameFam V ε fr) :
    IsMaxCompactInf V (frameHom R h).range := by
  refine ⟨?_, isCompact_frameRange hθ R h, fun K' hi hc hle => le_antisymm (fun g hg => ?_) hle⟩
  · rintro _ ⟨k, rfl⟩
    exact (frameHom_spec R h k).1
  · have : ∀ τ, ∃ k : Formalism.REAL.KG (ε τ),
        Formalism.REAL.toMK k = fr τ * infMat D.sp.cm.sig V.gram (θ τ) g * (fr τ)⁻¹ := fun τ => by
      have := conj_mem_Kset hθ R h K' hc hle τ hg
      rw [← Formalism.REAL.range_toMK] at this
      exact this
    choose k hk using this
    refine ⟨k, R.2.2.1 _ (frameHom_spec R h k).1 _ (hi g hg) fun τ => ?_⟩
    have hd : IsUnit (fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (h τ).1
    rw [(frameHom_spec R h k).2, hk]
    simp only [Matrix.mul_assoc]
    rw [nonsing_inv_mul_cancel_left _ _ hd, nonsing_inv_mul _ hd, Matrix.mul_one]

theorem exists_maxCompact_of_frames : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D), ∀ (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsFrameFam V ε fr → ∃ K : Subgroup (GA D V), IsMaxCompactInf V K ∧ (∃ j : (∀ τ, Formalism.REAL.KG (ε τ)) →* K, Function.Surjective j ∧ ∀ τ k, (j (Pi.mulSingle τ k) : GA D V) = kAt θ V τ (ε τ) (fr τ) k) := by
  intro D θ hθ V ε fr h
  have R := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V
  exact ⟨(frameHom R h).range, isMaxCompactInf_range hθ R h, (frameHom R h).rangeRestrict,
    (frameHom R h).rangeRestrict_surjective, fun τ k => frameHom_single hθ R h τ k⟩

end GlobalTheory.FrameCompact

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.HeckeSplitAll

def splitLoc (D : D7) : Set (AE D)ˣ :=
  {x | ∃ e, IsSplitIdem D e ∧ (e + cA D e) * ((x : AE D) - 1) = (x : AE D) - 1}

def modSet (D : D7) (N : ℕ) : Set (AE D)ˣ :=
  {x | infPart D (x : AE D) = 1 ∧
    (∃ r ∈ intAE D, finPart D (x : AE D) - 1 = (N : Af D.host.F ⊗[D.host.F] D.host.E) * r) ∧
    finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D}

def grpH (D : D7) (N : ℕ) : Subgroup (AE D)ˣ :=
  Subgroup.closure (Set.range (Units.map (incA D).toMonoidHom) ∪ splitLoc D ∪ modSet D N)

end GlobalTheory.HeckeSplitAll
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.special_linear_generated_by_transvections : ∀ (R : Type) [CommRing R], (∀ a b : R, IsCoprime a b → ∃ t : R, IsUnit (a + t * b)) → ∀ (n : ℕ) (H : Subgroup (GL (Fin n) R)), (∀ (i j : Fin n), i ≠ j → ∀ (t : R) (u : GL (Fin n) R), u.1 = Matrix.transvection i j t → u ∈ H) → ∀ a : GL (Fin n) R, Matrix.GeneralLinearGroup.det a = 1 → a ∈ H := by
  first | exact @GlobalTheory.GLGen.mem_of_det_eq_one | exact GlobalTheory.GLGen.mem_of_det_eq_one | (intros; apply GlobalTheory.GLGen.mem_of_det_eq_one <;> assumption)
end

end

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff


theorem _root_.GlobalTheory.T.adelicMatrixRealSize_le_realSymplecticPairing_sum : ∀ (D : D7) (θ : InfFam D) (T : HSp D) (ρ : ℕ), ∃ (k : ℕ) (τs : Fin k → D.what₂.Tau) (zs : Fin k → Matrix (Fin T.rank) (Fin ρ) ℂ) (C : ℝ), ∀ x : Mx D T.rank ρ, realSize θ x ≤ C * ∑ i, |2 * (tauE D (τs i) D.host.xi0 * ((compAt θ (τs i) x)ᴴ * gramAt D T (τs i) * zs i).trace).re| := by
  first | exact @GlobalTheory.RealPairBound.realSize_le_pairing | exact GlobalTheory.RealPairBound.realSize_le_pairing | (intros; apply GlobalTheory.RealPairBound.realSize_le_pairing <;> assumption)

end
end
