module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle127
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle254
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle252
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle128
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle242
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle304
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsGlOfEquiv
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle015
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SobContId
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped ComplexOrder

namespace GlobalTheory.SeeSaw.YRat

theorem star_eq_conj (D : D7) (x : D.host.E) : star x = D.host.conj x := by
  apply D.host.φ₀.injective
  have h1 : D.host.φ₀ (D.host.conj x) = starRingEnd ℂ (D.host.φ₀ x) := Formalism.HC.HostAx.conjE_apply _ _ _
  rw [h1]
  haveI := D.host.isCMField_hostE
  exact IsCMField.complexEmbedding_complexConj _ _ _

theorem posDef_of_sig {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (h : Formalism.UG.HasSignature G n 0) : G.PosDef := by
  obtain ⟨e, P, hP⟩ := h
  have hJ : Formalism.UG.Jpq n 0 = 1 := by
    ext i j
    rcases i with i | i
    · rcases j with j | j
      · simp [Formalism.UG.Jpq, Matrix.one_apply]
      · exact j.elim0
    · exact i.elim0
  have hcT : Formalism.UG.cT (starRingEnd ℂ) P.val = P.valᴴ := by
    ext i j; simp [Formalism.UG.cT, Matrix.conjTranspose_apply]
  rw [hcT, hJ] at hP
  have h1 : (P.valᴴ * G.reindex e e * P.val).PosDef := by rw [hP]; exact Matrix.PosDef.one
  have h2 : (G.reindex e e).PosDef := (Matrix.IsUnit.posDef_star_left_conjugate_iff P.isUnit).1 h1
  have h3 : G = (G.reindex e e).submatrix e e := by ext i j; simp
  rw [h3]
  exact h2.submatrix e.injective

theorem defSpace {D : D7} (hX : ∀ j, j ≤ D.R.m → (D.sp.X j).IsPosDef) {j : ℕ} (hj : j ≤ D.R.m) :
    (D.sp.X j).SigOK ∧ (∀ τ, (D.sp.X j).sig τ = (D.R.N j, 0)) ∧ CoCpt (D.sp.X j) := by
  have hs : (D.sp.X j).SigOK := D.sp.X_sig j
  have hr : (D.sp.X j).rank = D.R.N j := D.sp.X_rank j hj
  refine ⟨hs, fun τ => by rw [hX j hj τ, hr], ?_⟩
  refine (GlobalTheory.Unf.CoCptOf.coCpt_of_isAniso_or_posDef D (D.sp.X j)).2 fun τ => ?_
  have h1 := hs (tauE D τ)
  rw [hX j hj (tauE D τ)] at h1
  exact posDef_of_sig _ h1

theorem spaces_of_index : ∀ (D : D7) (u : D.what₂.Word), (∀ j, j ≤ D.R.m → (D.sp.X j).IsPosDef) → (∀ j ρ, j + 2 * ρ + 2 = D.R.m → ∃ (V : HSp D) (b : BesAt V (D.sp.X j) ρ), V.rank = D.R.rankY j ∧ V.SigOK ∧ (∀ τ, V.sig τ = sigYD D.R j) ∧ (star b.ζ ⬝ᵥ b.L.gram *ᵥ b.ζ) * (D.host.xi0 * star D.host.xi0) ^ (j / 2) = -(((D.mem u).A.T : ℕ) : D.host.E)) ∧ ∀ j ρ, j + 2 * ρ + 2 = D.R.m → ∃ (V : HSp D) (_ : JacAt V (D.sp.X (j + 1)) ρ), V.rank = D.R.rankY (j + 1) ∧ V.SigOK ∧ ∀ τ, V.sig τ = sigYD D.R (j + 1) := by
  intro D u hX
  have hsum := GlobalTheory.T.exists_orthogonalSum_and_hyperbolicSum_spaces D
  have hvol := GlobalTheory.Unf.VolExist.measures_exist D
  have hxi : D.host.xi0 ≠ 0 := GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero
  obtain ⟨π, -, hπ, -⟩ := D.T_norm u
  have hππ : (π : D.host.E) * star (π : D.host.E) = (((D.mem u).A.T : ℕ) : D.host.E) := by
    rw [star_eq_conj]; exact hπ
  have hT0 : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 := by
    have := (D.mem u).A.T_prime.ne_zero
    exact_mod_cast this
  have hπ0 : (π : D.host.E) ≠ 0 := by
    intro h0; apply hT0; rw [← hππ, h0, zero_mul]
  refine ⟨?_, ?_⟩
  · intro j ρ h
    obtain ⟨hXs, hXsig, hXc⟩ := defSpace hX (j := j) (by omega)
    have hXr : (D.sp.X j).rank = D.R.N j := D.sp.X_rank j (by omega)
    set c : D.host.E := (π : D.host.E) / D.host.xi0 ^ (j / 2) with hc
    have hc0 : c ≠ 0 := div_ne_zero hπ0 (pow_ne_zero _ hxi)
    obtain ⟨L, ζ, hline, hLs, hLn, hLsig⟩ := GlobalTheory.T.exists_hermitianLine_vector_prescribed_norm D c (-1) hc0
    obtain ⟨V₀, o, hV₀s, hV₀sig⟩ := hsum.1 (D.sp.X j) L hXs hLs
    obtain ⟨V, d, hVs, hVsig⟩ := hsum.2 V₀ ρ hV₀s
    refine ⟨V, ⟨V₀, L, d, o, ζ, hline, hXc, (hvol.2.1 _ _ _ d).some⟩, ?_, hVs, ?_, ?_⟩
    · have h1 := d.rank_add
      have h2 := o.rank_add
      have h3 : L.rank = 1 := hline.1
      have h4 : j * (D.R.t + 1) = j * D.R.t + j := by ring
      simp only [Ranks.rankY, Ranks.r]
      rw [hXr] at h2
      simp only [Ranks.N] at h2
      omega
    · intro τ
      have hL : L.sig τ = (0, 1) := by rw [hLsig τ]; decide
      rw [hVsig τ, hV₀sig τ, hXsig τ, hL]
      have h4 : j * (D.R.t + 1) = j * D.R.t + j := by ring
      simp only [sigYD, Ranks.rankY, Ranks.r, Ranks.N, Prod.mk_add_mk, Prod.mk.injEq]
      constructor <;> omega
    · show (star ζ ⬝ᵥ L.gram *ᵥ ζ) * (D.host.xi0 * star D.host.xi0) ^ (j / 2) = _
      rw [hLn, ← hππ, hc, star_div₀, star_pow]
      have hs0 : star D.host.xi0 ≠ 0 := star_ne_zero.2 hxi
      field_simp
      push_cast
      ring
  · intro j ρ h
    obtain ⟨hXs, hXsig, hXc⟩ := defSpace hX (j := j + 1) (by omega)
    have hXr : (D.sp.X (j + 1)).rank = D.R.N (j + 1) := D.sp.X_rank (j + 1) (by omega)
    obtain ⟨V, d, hVs, hVsig⟩ := hsum.2 (D.sp.X (j + 1)) ρ hXs
    refine ⟨V, ⟨d, hXc, (hvol.2.1 _ _ _ d).some⟩, ?_, hVs, ?_⟩
    · have h1 := d.rank_add
      rw [hXr] at h1
      have h4 : (j + 1) * (D.R.t + 1) = (j + 1) * D.R.t + (j + 1) := by ring
      simp only [Ranks.N] at h1
      simp only [Ranks.rankY, Ranks.r]
      omega
    · intro τ
      rw [hVsig τ, hXsig τ]
      have h4 : (j + 1) * (D.R.t + 1) = (j + 1) * D.R.t + (j + 1) := by ring
      simp only [sigYD, Ranks.rankY, Ranks.r, Ranks.N, Prod.mk_add_mk, Prod.mk.injEq]
      constructor <;> omega

end GlobalTheory.SeeSaw.YRat

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.TrcProof

variable {D : D7}

theorem contAut_add {V : HSp D} {f g : GA D V → ℂ} (hf : IsContAut V f) (hg : IsContAut V g) :
    IsContAut V (f + g) :=
  ⟨fun γ hγ x => by simp only [Pi.add_apply, hf.1 γ hγ x, hg.1 γ hγ x], hf.2.add hg.2⟩

theorem contAut_smul {V : HSp D} {f : GA D V → ℂ} (hf : IsContAut V f) (c : ℂ) : IsContAut V (c • f) :=
  ⟨fun γ hγ x => by simp only [Pi.smul_apply, hf.1 γ hγ x], hf.2.const_smul c⟩

theorem contAut_rTrans {V : HSp D} {f : GA D V → ℂ} (h : GA D V) (hf : IsContAut V f) : IsContAut V (rTrans h f) :=
  ⟨fun γ hγ x => by simp only [rTrans, mul_assoc, hf.1 γ hγ], hf.2.comp (continuous_mul_const h)⟩

theorem contAut_sum {V : HSp D} {I : Type} (s : Finset I) (a : I → ℂ) (f : I → GA D V → ℂ)
    (hf : ∀ i ∈ s, IsContAut V (f i)) : IsContAut V (∑ i ∈ s, a i • f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ _ _ => by simp, continuous_const⟩
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact contAut_add (contAut_smul (hf i (Finset.mem_insert_self i s)) (a i))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem per_sum_right {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {ρ : ℕ} (B : BesLev D ρ)
    {φ : GA D B.A → ℂ} (hφ : IsContAut B.A φ) {I : Type} (s : Finset I) (a : I → ℂ) (f : I → GA D B.V → ℂ)
    (hf : ∀ i ∈ s, IsContAut B.V (f i)) :
    B.per ψ φ (∑ i ∈ s, a i • f i) = ∑ i ∈ s, a i * B.per ψ φ (f i) := by
  have hconv := fun i (hi : i ∈ s) => PerSumProof.conv hψ B (hf i hi) hφ
  simp only [BesLev.per, besPer]
  have e1 : ∀ h n, besFun ψ 1 B.d B.o B.ζ φ (∑ i ∈ s, a i • f i) h n =
      ∑ i ∈ s, a i * besFun ψ 1 B.d B.o B.ζ φ (f i) h n := by
    intro h n
    simp only [besFun, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [e1]
  have e2 : (fun h => ∫ n in B.vN.𝓝, ∑ i ∈ s, a i * besFun ψ 1 B.d B.o B.ζ φ (f i) h n ∂B.vN.ν) =
      fun h => ∑ i ∈ s, a i * ∫ n in B.vN.𝓝, besFun ψ 1 B.d B.o B.ζ φ (f i) h n ∂B.vN.ν := by
    funext h
    rw [integral_finsetSum s fun i hi => ((hconv i hi).1 h).const_mul (a i)]
    exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  rw [e2, integral_finsetSum s fun i hi => (hconv i hi).2.const_mul (a i)]
  exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _

end GlobalTheory.SeeSaw.TrcProof

namespace GlobalTheory.SeeSaw

theorem per_linear_trc : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ρ : ℕ) (B : BesLev D ρ) (φ : GA D B.A → ℂ), IsContAut B.A φ → (∀ (I : Type) (s : Finset I) (a : I → ℂ) (f : I → GA D B.V → ℂ), (∀ i ∈ s, IsContAut B.V (f i)) → B.per ψ φ (∑ i ∈ s, a i • f i) = ∑ i ∈ s, a i * B.per ψ φ (f i)) ∧ ∀ (e : GA D B.V →₀ ℂ) (f : GA D B.V → ℂ), IsContAut B.V f → IsContAut B.V (trc e f) ∧ B.per ψ φ (trc e f) = ∑ g ∈ e.support, e g * B.per ψ φ (rTrans g f) := by
  intro D ψ hψ ρ B φ hφ
  refine ⟨fun I s a f hf => TrcProof.per_sum_right hψ B hφ s a f hf, fun e f hf => ?_⟩
  have hT : ∀ g ∈ e.support, IsContAut B.V (rTrans g f) := fun g _ => TrcProof.contAut_rTrans g hf
  exact ⟨TrcProof.contAut_sum e.support e (fun g => rTrans g f) hT,
    TrcProof.per_sum_right hψ B hφ e.support e (fun g => rTrans g f) hT⟩

end GlobalTheory.SeeSaw

end
end

section

open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

noncomputable section

namespace GlobalTheory.ThetaDens.WeilCompact

variable {D : D7}

theorem mt_mul_eq (V : HSp D) (g h : GA D V) :
    Formalism.L2.Theta.mt V (g * h) = Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V h := by
  unfold Formalism.L2.Theta.mt; rw [map_mul]; rfl

theorem mt_one_eq (V : HSp D) : Formalism.L2.Theta.mt V 1 = 1 := by
  unfold Formalism.L2.Theta.mt; rw [map_one]; rfl

theorem continuous_mt_eq (V : HSp D) : Continuous (Formalism.L2.Theta.mt V) :=
  Units.continuous_val.comp continuous_subtype_val

theorem actO_actO_inv {S T : HSp D} (g : GA D S) (h : GA D T) (x : WO S T) :
    Formalism.IndefR.Datum.actO S T g h (Formalism.IndefR.Datum.actO S T g⁻¹ h⁻¹ x) = x := by
  unfold Formalism.IndefR.Datum.actO
  rw [inv_inv]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Formalism.L2.Theta.mt T h), ← mt_mul_eq, ← mt_mul_eq, mul_inv_cancel, mul_inv_cancel,
    mt_one_eq, mt_one_eq, Matrix.one_mul, Matrix.mul_one]


open GlobalTheory.Size in
theorem dRho_om {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ)
    (g : GA D S) (h : GA D T) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) :
    Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z (om (g, h) f) =
      om (g, h) (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ
        (compAt θ τ (Formalism.L2.Theta.mt T h⁻¹) * z * compAt θ τ (Formalism.L2.Theta.mt S g)) f) := by
  rw [GlobalTheory.OrientedHeis.om_dRho hom hθ g h τ _ hf]
  congr 1
  have e1 := GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := θ) τ h
  have e2 := GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := θ) τ g
  simp only [Matrix.mul_assoc]
  rw [e2, Matrix.mul_one, ← Matrix.mul_assoc, e1, Matrix.one_mul]

def dirSize (θ : InfFam D) (S T : HSp D) (x : GA D S × GA D T) : ℝ :=
  ∑ a : D.what₂.Tau × Fin T.rank × Fin S.rank × Bool, ∑ i, ∑ j,
    (|((compAt θ a.1 (Formalism.L2.Theta.mt T x.2⁻¹) * Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1) *
      compAt θ a.1 (Formalism.L2.Theta.mt S x.1)) i j).re| +
     |((compAt θ a.1 (Formalism.L2.Theta.mt T x.2⁻¹) * Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1) *
      compAt θ a.1 (Formalism.L2.Theta.mt S x.1)) i j).im|)

theorem continuous_dirSize {θ : InfFam D} (hθ : IsInfFam θ) (S T : HSp D) : Continuous (dirSize θ S T) := by
  unfold dirSize
  refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  have h1 : Continuous fun x : GA D S × GA D T => compAt θ a.1 (Formalism.L2.Theta.mt T x.2⁻¹) :=
    (GlobalTheory.RealWeil.continuous_compAt hθ a.1 _ _).comp ((continuous_mt_eq T).comp continuous_snd.inv)
  have h2 : Continuous fun x : GA D S × GA D T => compAt θ a.1 (Formalism.L2.Theta.mt S x.1) :=
    (GlobalTheory.RealWeil.continuous_compAt hθ a.1 _ _).comp ((continuous_mt_eq S).comp continuous_fst)
  have h3 := ((h1.matrix_mul (continuous_const (y := Matrix.single a.2.1 a.2.2.1
    (if a.2.2.2 then Complex.I else 1)))).matrix_mul h2).matrix_elem i j
  exact (continuous_abs.comp (Complex.continuous_re.comp h3)).add (continuous_abs.comp (Complex.continuous_im.comp h3))

theorem actO_add' {S T : HSp D} (g : GA D S) (h : GA D T) (x y : WO S T) :
    Formalism.IndefR.Datum.actO S T g h (x + y) = Formalism.IndefR.Datum.actO S T g h x + Formalism.IndefR.Datum.actO S T g h y := by
  unfold Formalism.IndefR.Datum.actO
  rw [Matrix.mul_add, Matrix.add_mul]

theorem actO_zero' {S T : HSp D} (g : GA D S) (h : GA D T) : Formalism.IndefR.Datum.actO S T g h 0 = 0 := by
  unfold Formalism.IndefR.Datum.actO
  rw [Matrix.mul_zero, Matrix.zero_mul]

theorem actO_neg' {S T : HSp D} (g : GA D S) (h : GA D T) (x : WO S T) :
    Formalism.IndefR.Datum.actO S T g h (-x) = -Formalism.IndefR.Datum.actO S T g h x := by
  unfold Formalism.IndefR.Datum.actO
  rw [Matrix.mul_neg, Matrix.neg_mul]


open GlobalTheory.Size in
theorem word_om_le {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ)
    {μ : Measure (WO S T)} {𝓕 : Set (WO S T)} (hμ : IsCovolOne (ratL T S) μ 𝓕) {K : Set (GA D S × GA D T)}
    (B : ℝ≥0) (hB : ∀ x ∈ K, dirSize θ S T x ≤ B) (k : ℕ) :
    ∃ C : ℝ≥0, ∀ l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool), l.length = k → ∀ x ∈ K,
      ∀ g, IsThetaFunO ψ S T g → l2O μ 𝓕 (wordAct (heisDer ψ θ) l (om x g)) ≤ C * sobO ψ θ μ 𝓕 k g := by
  induction k with
  | zero =>
    refine ⟨1, fun l hl x _ g hg => ?_⟩
    obtain rfl : l = [] := List.eq_nil_of_length_eq_zero hl
    rw [wordAct_nil, l2O_om_apply_eq_of_isThetaFunO hom hμ.1 hμ.2.1 hg, sobO_zero, ENNReal.coe_one, one_mul]
  | succ k ih =>
    obtain ⟨C, hC⟩ := ih
    refine ⟨C * B, fun l hl x hx g hg => ?_⟩
    obtain ⟨g1, h1⟩ := x
    have hne : l ≠ [] := by rintro rfl; simp at hl
    rw [← List.dropLast_append_getLast hne, wordAct_append, wordAct_cons, wordAct_nil]
    set a := l.getLast hne
    have e := dRho_om hom hθ g1 h1 a.1 (Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1)) hg
    have e' : heisDer ψ θ a (om (g1, h1) g) = Formalism.IndefR.Datum.dRho (heisO ψ S T) θ a.1
        (Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1)) (om (g1, h1) g) := rfl
    rw [e', e]
    have hg' := GlobalTheory.OrientedHeis.theta_dRho hθ hom.std a.1 (compAt θ a.1 (Formalism.L2.Theta.mt T h1⁻¹) *
      Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1) * compAt θ a.1 (Formalism.L2.Theta.mt S g1)) hg
    have hs : ENNReal.ofReal (∑ i, ∑ j, (|((compAt θ a.1 (Formalism.L2.Theta.mt T h1⁻¹) *
        Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1) * compAt θ a.1 (Formalism.L2.Theta.mt S g1)) i j).re| +
        |((compAt θ a.1 (Formalism.L2.Theta.mt T h1⁻¹) *
        Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1) * compAt θ a.1 (Formalism.L2.Theta.mt S g1)) i j).im|))
        ≤ B := by
      rw [← ENNReal.ofReal_coe_nnreal]
      refine ENNReal.ofReal_le_ofReal (le_trans ?_ (hB _ hx))
      unfold dirSize
      exact Finset.single_le_sum (f := fun a : D.what₂.Tau × Fin T.rank × Fin S.rank × Bool => ∑ i, ∑ j,
        (|((compAt θ a.1 (Formalism.L2.Theta.mt T h1⁻¹) * Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1) *
          compAt θ a.1 (Formalism.L2.Theta.mt S g1)) i j).re| +
         |((compAt θ a.1 (Formalism.L2.Theta.mt T h1⁻¹) * Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1) *
          compAt θ a.1 (Formalism.L2.Theta.mt S g1)) i j).im|))
        (fun b _ => by positivity) (Finset.mem_univ a)
    calc _ ≤ (C : ℝ≥0∞) * sobO ψ θ μ 𝓕 k _ := hC _ (by simp [hl]) _ hx _ hg'
      _ ≤ C * (ENNReal.ofReal _ * sobO ψ θ μ 𝓕 (k + 1) g) := by
          gcongr
          exact sobO_dRho_le hom.std hθ hg a.1 _ k
      _ ≤ C * (B * sobO ψ θ μ 𝓕 (k + 1) g) := by gcongr
      _ = ((C * B : ℝ≥0) : ℝ≥0∞) * sobO ψ θ μ 𝓕 (k + 1) g := by push_cast; ring

end GlobalTheory.ThetaDens.WeilCompact


open GlobalTheory.ThetaDens.WeilCompact GlobalTheory.Size in
theorem GlobalTheory.ThetaDens.om_compact_sobCont : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ K : Set (GA D S × GA D T), IsCompact K → ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∃ U' : AddSubgroup (WO S T), IsOpen (U' : Set (WO S T)) ∧ (∀ f ∈ _root_.GlobalTheory.Size.thetaLevel ψ S T U, ∀ x ∈ K, om x f ∈ _root_.GlobalTheory.Size.thetaLevel ψ S T U') ∧ ∀ d : ℕ, ∃ (d' : ℕ) (C : ℝ≥0), ∀ f ∈ _root_.GlobalTheory.Size.thetaLevel ψ S T U, ∀ x ∈ K, sobO ψ θ μ 𝓕 d (om x f) ≤ C * sobO ψ θ μ 𝓕 d' f := by
  intro D ψ S T χS χT om hom θ hθ μ 𝓕 hμ K hK U hU
  let U' : AddSubgroup (WO S T) :=
    { carrier := {u | ∀ x ∈ K, Formalism.IndefR.Datum.actO S T x.1⁻¹ x.2⁻¹ u ∈ U}
      add_mem' := fun {a b} ha hb x hx => by
        rw [Set.mem_setOf_eq] at ha hb
        show Formalism.IndefR.Datum.actO S T x.1⁻¹ x.2⁻¹ (a + b) ∈ U
        rw [actO_add']; exact U.add_mem (ha x hx) (hb x hx)
      zero_mem' := fun x _ => by
        show Formalism.IndefR.Datum.actO S T x.1⁻¹ x.2⁻¹ 0 ∈ U
        rw [actO_zero']; exact U.zero_mem
      neg_mem' := fun {a} ha x hx => by
        show Formalism.IndefR.Datum.actO S T x.1⁻¹ x.2⁻¹ (-a) ∈ U
        rw [actO_neg']; exact U.neg_mem (ha x hx) }
  have hU' : IsOpen (U' : Set (WO S T)) := by
    refine U'.isOpen_of_mem_nhds (g := 0) ?_
    refine hK.eventually_forall_of_forall_eventually (x₀ := (0 : WO S T))
      (P := fun u x => Formalism.IndefR.Datum.actO S T x.1⁻¹ x.2⁻¹ u ∈ U) fun x _ => ?_
    have hc : Continuous fun p : WO S T × (GA D S × GA D T) => Formalism.IndefR.Datum.actO S T p.2.1⁻¹ p.2.2⁻¹ p.1 := by
      unfold Formalism.IndefR.Datum.actO
      exact (((continuous_mt_eq T).comp continuous_snd.snd.inv).matrix_mul continuous_fst).matrix_mul
        ((continuous_mt_eq S).comp continuous_snd.fst.inv.inv)
    refine (hU.preimage hc).mem_nhds ?_
    show Formalism.IndefR.Datum.actO S T x.1⁻¹ x.2⁻¹ 0 ∈ U
    rw [actO_zero']; exact U.zero_mem
  obtain ⟨B0, hB0⟩ := hK.bddAbove_image (continuous_dirSize hθ S T).continuousOn
  have hB : ∀ x ∈ K, dirSize θ S T x ≤ (B0.toNNReal : ℝ) := fun x hx =>
    (hB0 ⟨x, hx, rfl⟩).trans (Real.le_coe_toNNReal B0)
  refine ⟨U', hU', fun f hf x hx => ⟨hom.om_pres x f hf.1, fun u hu h0 => ?_⟩, fun d => ?_⟩
  · obtain ⟨g, h⟩ := x
    have hv : Formalism.IndefR.Datum.actO S T g⁻¹ h⁻¹ u ∈ U := hu (g, h) hx
    have hv0 : (Formalism.IndefR.Datum.actO S T g⁻¹ h⁻¹ u).map (infPart D) = 0 := by
      unfold Formalism.IndefR.Datum.actO
      rw [Matrix.map_mul, Matrix.map_mul, h0]; simp
    calc heisO ψ S T u (om (g, h) f)
        = heisO ψ S T (Formalism.IndefR.Datum.actO S T g h (Formalism.IndefR.Datum.actO S T g⁻¹ h⁻¹ u)) (om (g, h) f) := by
          rw [actO_actO_inv]
      _ = om (g, h) (heisO ψ S T (Formalism.IndefR.Datum.actO S T g⁻¹ h⁻¹ u) f) := (hom.om_heis g h _ f hf.1).symm
      _ = om (g, h) f := by rw [hf.2 _ hv hv0]
  · choose C hC using word_om_le hom hθ hμ _ hB
    refine ⟨d, ∑ k ∈ Finset.range (d + 1), ∑ _a : Fin k → D.what₂.Tau × Fin T.rank × Fin S.rank × Bool, C k,
      fun f hf x hx => ?_⟩
    show wordSum (heisDer ψ θ) (l2O μ 𝓕) d (om x f) ≤ _
    unfold wordSum
    rw [ENNReal.ofNNReal_finsetSum, Finset.sum_mul]
    refine Finset.sum_le_sum fun k hk => ?_
    rw [ENNReal.ofNNReal_finsetSum, Finset.sum_mul]
    refine Finset.sum_le_sum fun a _ => ?_
    calc _ ≤ (C k : ℝ≥0∞) * sobO ψ θ μ 𝓕 k f := hC k _ (List.length_ofFn) x hx f hf.1
      _ ≤ C k * sobO ψ θ μ 𝓕 d f := by
          gcongr
          exact sobO_mono (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))

end
end

section

noncomputable section

open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

namespace GlobalTheory.ThetaLimDeriv

theorem tendstoUniformly_heisO {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    {G : ℕ → WO S T → ℂ} {F : WO S T → ℂ} (h : TendstoUniformly G F Filter.atTop) (x : ℝ → WO S T) (w : WO S T) :
    TendstoUniformly (fun j t => heisO ψ S T (x t) (G j) w) (fun t => heisO ψ S T (x t) F w) Filter.atTop := by
  rw [Metric.tendstoUniformly_iff] at h ⊢
  intro ε hε
  filter_upwards [h ε hε] with j hj t
  have := hj (w + x t)
  rw [dist_eq_norm] at this ⊢
  simp only [heisO]
  rw [← mul_sub, norm_mul, hψ.1.2.1, one_mul]
  exact this

theorem heisDer_of_tendstoUniformly : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S T : HSp D) (G : ℕ → WO S T → ℂ) (F F' : WO S T → ℂ), (∀ j, IsThetaFunO ψ S T (G j)) → TendstoUniformly G F Filter.atTop → ∀ a : (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool), TendstoUniformly (fun j => GlobalTheory.Size.heisDer ψ θ a (G j)) F' Filter.atTop → GlobalTheory.Size.heisDer ψ θ a F = F' := by
  intro D ψ hψ θ hθ S T G F F' hG hF a hF'
  have hL := GlobalTheory.OrientedHeis.isRealDir_lineAt (S := S) (T := T) hθ a.1
    (Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1))
  have e : ∀ f, GlobalTheory.Size.heisDer ψ θ a f = GlobalTheory.OrientedHeis.dLine ψ S T
      (lineAt θ a.1 (Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1))) f := fun _ => rfl
  simp only [e] at hF' ⊢
  generalize lineAt θ a.1 (Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1)) = L at hL hF' ⊢
  funext w
  have h1 := tendstoUniformly_heisO hψ hF L w
  have h2 := tendstoUniformly_heisO hψ hF' L w
  have h3 := hasDerivAt_of_tendstoUniformly h2
    (Filter.Eventually.of_forall fun j s => GlobalTheory.OrientedHeis.hasDerivAt_heisO hθ hψ hL (hG j) w s)
    (fun s => h1.tendsto_at s) 0
  have h4 := h3.deriv
  rw [map_zero, GlobalTheory.OrientedHeis.heisO_zero] at h4
  exact h4

end GlobalTheory.ThetaLimDeriv

end
end
