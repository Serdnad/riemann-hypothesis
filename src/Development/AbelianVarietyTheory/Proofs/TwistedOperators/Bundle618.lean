module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle014
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle611
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle019
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle226
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsOverVacuaDenseThetaFunctions
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle320
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignBlockDeterminantOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle590
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle020
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle197
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SqrtDivMulEqSqrtMul
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.LocalToGlobal.IndefiniteReal.Bundle014
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConjugateAdjointDagger
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle123
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsConjAdjointPullbackBijection
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle612
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.Deriv.Star
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle223

@[expose] public section

section

open Formalism.BasicNotions

namespace GlobalTheory

theorem vacChar_of_record : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.VacChar D :=
  GlobalTheory.T.thetaVacuumCharacters_realPlaces

end GlobalTheory
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.ChainFr GlobalTheory.Size GlobalTheory.Grow GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift
open scoped ENNReal NNReal

namespace GlobalTheory.LowVanishObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Kernel

variable {V W : HSp D} (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (g : GA D V) (h : GA D W)

theorem thetaKO_zero : thetaKO ω g h 0 = 0 := by
  simp [thetaKO]

theorem thetaKO_add (f f' : WO V W → ℂ) : thetaKO ω g h (f + f') = thetaKO ω g h f + thetaKO ω g h f' := by
  simp [thetaKO]

theorem thetaKO_sub (f f' : WO V W → ℂ) : thetaKO ω g h (f - f') = thetaKO ω g h f - thetaKO ω g h f' := by
  simp [thetaKO]

theorem thetaKO_smul (c : ℂ) (f : WO V W → ℂ) : thetaKO ω g h (c • f) = c * thetaKO ω g h f := by
  simp [thetaKO]

end Kernel

theorem multT_apply_cusp {W : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel W S) (J : Set (GA D W))
    (χ : GA D W → ℂ) (F : SmT M →ₗ[ℂ] (GA D W → ℂ)) (hF : F ∈ MultT θ M J χ) (v : SmT M) :
    IsAutFunSm θ W (F v) ∧ IsCuspFun W (F v) := by
  have hT : IsMultMap θ M J χ (PiTensorProduct.lift.symm F) :=
    (GlobalTheory.MultMem.mem_mult_iff D θ W S M J χ _).1 ((mem_multT θ M J χ F).1 hF)
  have hFv : ∀ x, F x = PiTensorProduct.lift (PiTensorProduct.lift.symm F) x := fun x => by
    rw [LinearEquiv.apply_symm_apply]
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    rw [hFv, LinearMap.map_smul, PiTensorProduct.lift.tprod]
    exact ⟨GlobalTheory.MultMem.isAutFunSm_smul r (hT.aut x), GlobalTheory.MultMem.isCuspFun_smul r (hT.cusp x)⟩
  | add a b ha hb =>
    rw [map_add (f := _)]
    exact ⟨GlobalTheory.MultMem.isAutFunSm_add ha.1 hb.1,
      GlobalTheory.MultMem.isCuspFun_add ha.1.toIsAutFun hb.1.toIsAutFun ha.2 hb.2⟩

theorem liftInt_span_eq_zero {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {ν : Measure (GA D W)} {𝓕 : Set (GA D W)} {Φ : GA D W → ℂ}
    (hI : ∀ f, IsThetaFunO ψ V W f → ∀ x, IntegrableOn (fun h => thetaKO ω x h f * Φ h) 𝓕 ν)
    {s : Set (WO V W → ℂ)} (hs : ∀ g ∈ s, IsThetaFunO ψ V W g ∧ Lift.liftInt ν 𝓕 (thetaKO ω) g Φ = 0) :
    ∀ g ∈ Submodule.span ℂ s, IsThetaFunO ψ V W g ∧ Lift.liftInt ν 𝓕 (thetaKO ω) g Φ = 0 := by
  intro g hg
  induction hg using Submodule.span_induction with
  | mem x hx => exact hs x hx
  | zero =>
    refine ⟨GlobalTheory.OrientedHeis.theta_zero, ?_⟩
    funext x
    simp [Lift.liftInt, thetaKO_zero]
  | add a b _ _ ha hb =>
    refine ⟨GlobalTheory.OrientedHeis.theta_add ha.1 hb.1, ?_⟩
    funext x
    have h1 := congrFun ha.2 x
    have h2 := congrFun hb.2 x
    simp only [Lift.liftInt, Pi.zero_apply] at h1 h2 ⊢
    simp only [thetaKO_add, add_mul]
    rw [integral_add (hI a ha.1 x) (hI b hb.1 x), h1, h2, add_zero]
  | smul c a _ ha =>
    refine ⟨GlobalTheory.OrientedHeis.theta_smul c ha.1, ?_⟩
    funext x
    have h1 := congrFun ha.2 x
    simp only [Lift.liftInt, Pi.zero_apply] at h1 ⊢
    simp only [thetaKO_smul, mul_assoc]
    rw [integral_const_mul, h1, mul_zero]

theorem eq_zero_of_le_mul_pos {a K : ℝ≥0∞} (hK : K ≠ ∞) (h : ∀ δ : ℝ≥0∞, 0 < δ → a ≤ K * δ) : a = 0 := by
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) bot_le
  rw [zero_add]
  rcases eq_or_ne K 0 with rfl | hK0
  · exact (h 1 one_pos).trans (by simp)
  · have hε' : (ε : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.2 hε.ne'
    have := h (ε / K) (ENNReal.div_pos hε' hK)
    rwa [ENNReal.mul_div_cancel hK0 hK] at this

theorem liftInt_eq_zero_of_approx {θ : InfFam D} {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {ν : Measure (GA D W)} {𝓕 : Set (GA D W)}
    {cls : (GA D W → ℂ) → Prop} (hL : LiftLaws θ ψ ω ν 𝓕 cls) {Φ : GA D W → ℂ} (hΦ : cls Φ)
    {μ : Measure (WO V W)} {𝓓 : Set (WO V W)} (hμ : μ.IsAddHaarMeasure)
    (h𝓓 : IsAddFundamentalDomain (ratL W V) 𝓓 μ) {U : AddSubgroup (WO V W)} (hU : IsOpen (U : Set (WO V W)))
    {f : WO V W → ℂ} (hf : f ∈ GlobalTheory.Size.thetaLevel ψ V W U)
    (happ : ∀ (d : ℕ) (δ : ℝ≥0∞), 0 < δ → ∃ g ∈ GlobalTheory.Size.thetaLevel ψ V W U,
      Lift.liftInt ν 𝓕 (thetaKO ω) g Φ = 0 ∧ sobO ψ θ μ 𝓓 d (f - g) < δ) :
    Lift.liftInt ν 𝓕 (thetaKO ω) f Φ = 0 := by
  obtain ⟨A, hA⟩ := hL.bound
  obtain ⟨d, hd⟩ := hA 0
  obtain ⟨C, hC⟩ := hd μ 𝓓 hμ h𝓓 U hU
  have hint : ∀ f', IsThetaFunO ψ V W f' → ∀ x,
      IntegrableOn (fun h => thetaKO ω x h f' * Φ h) 𝓕 ν := fun f' hf' x => by
    simpa [rTr] using hL.integ f' Φ hf' hΦ x 1
  have key : ∀ g ∈ GlobalTheory.Size.thetaLevel ψ V W U, Lift.liftInt ν 𝓕 (thetaKO ω) g Φ = 0 →
      growthSob θ V 0 A (lift ω ν 𝓕 f Φ) ≤ C * sobO ψ θ μ 𝓓 d (f - g) * decayInt ν 𝓕 A Φ := by
    intro g hg hg0
    have hb := hC (f - g) (sub_mem hf hg) Φ hΦ
    have heq : lift ω ν 𝓕 (f - g) Φ = lift ω ν 𝓕 f Φ := by
      funext x
      have h0 := congrFun hg0 x
      simp only [lift, Lift.liftInt, Pi.zero_apply] at h0 ⊢
      simp only [thetaKO_sub, sub_mul]
      rw [integral_sub (hint f hf.1 x) (hint g hg.1 x), h0, sub_zero]
    rwa [heq] at hb
  have hdec := hL.decay_ne_top Φ hΦ A
  have hz : growthSob θ V 0 A (lift ω ν 𝓕 f Φ) = 0 := by
    refine eq_zero_of_le_mul_pos (K := C * decayInt ν 𝓕 A Φ) (ENNReal.mul_ne_top ENNReal.coe_ne_top hdec) ?_
    intro δ hδ
    obtain ⟨g, hg, hg0, hsm⟩ := happ d δ hδ
    calc growthSob θ V 0 A (lift ω ν 𝓕 f Φ)
        ≤ C * sobO ψ θ μ 𝓓 d (f - g) * decayInt ν 𝓕 A Φ := key g hg hg0
      _ ≤ C * δ * decayInt ν 𝓕 A Φ := by gcongr
      _ = C * decayInt ν 𝓕 A Φ * δ := by ring
  have hz' : growthSize V A (lift ω ν 𝓕 f Φ) = 0 := by simpa [growthSob] using hz
  unfold growthSize at hz'
  funext x
  have hx := ENNReal.ofReal_eq_zero.1 ((ENNReal.iSup_eq_zero.1 hz') x)
  have hpos : 0 < height V x ^ A := pow_pos (lt_of_lt_of_le one_pos ((height_laws V).1 x)) A
  rw [div_le_iff₀ hpos, zero_mul] at hx
  exact norm_le_zero_iff.1 hx

theorem lowVanish_obj : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay →
    ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing.LowVanish D := by
  intro h1 h2 h3 D k i V' W M' θ ψ hθ hk hi hsig ω' hω' ν 𝓕 hν h𝓕 J χ F hF v f' hf'
  obtain ⟨χS, χT, hW, hexp⟩ := hω'
  have hLaws := GlobalTheory.Chain.LiftReg.liftProps_obj h3 D V' W θ ψ χS χT ω' hθ hW ν 𝓕 hν h𝓕
  have hcv := multT_apply_cusp θ M' J χ F hF v
  obtain ⟨A⟩ := (GlobalTheory.FrameExists.frame_exists_signCompat D V').1
  obtain ⟨μ, 𝓓, hcov⟩ := GlobalTheory.Size.exists_isCovolOne V' W
  have hstd : IsStdChar D ψ (-1) := hW.std
  obtain ⟨U, hU, hfU, happ⟩ :=
    GlobalTheory.FockDensity.fockDense D V' W A (Fr.ofModel M') θ ψ hstd hθ μ 𝓓 hcov f' hf'
  have hint : ∀ f, IsThetaFunO ψ V' W f → ∀ x, IntegrableOn (fun h => thetaKO ω' x h f * F v h) 𝓕 ν :=
    fun f hf x => by simpa [rTr] using hLaws.integ f (F v) hf hcv x 1
  refine liftInt_eq_zero_of_approx hLaws hcv (μ := μ) (𝓓 := 𝓓) hcov.1 hcov.2.1 hU hfU ?_
  intro d δ hδ
  obtain ⟨g, hg, hgU, hsm⟩ := happ d δ hδ
  refine ⟨g, hgU, ?_, hsm⟩
  refine (liftInt_span_eq_zero hint ?_ g hg).2
  rintro _ ⟨f₀, P, hvac, -, rfl⟩
  refine ⟨?_, ?_⟩
  · exact GlobalTheory.Chain.InnerSteps.theta_pureTensorO hstd hθ A.cart A.onb (Fr.ofModel M').cart
      (Fr.ofModel M').onb hvac.1 P
  · exact GlobalTheory.LowerMembers.lowVanishFock h1 h2 h3 D k i V' W M' θ ψ hθ hk hi hsig ω' ⟨χS, χT, hW, hexp⟩
      ν 𝓕 hν h𝓕 J χ F hF v A f₀ hvac P

end GlobalTheory.LowVanishObj

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Datum ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.NTheta (IsIdemAt)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.FinApprox

variable {D : D7}

def finRat (D : D7) : D.host.E →+ AE D := TensorProduct.mk D.host.F (AF D.host.F) D.host.E (pairA D.host.F 0 1)

theorem finRat_apply (a : D.host.E) : finRat D a = pairA D.host.F 0 1 ⊗ₜ[D.host.F] a := rfl

theorem finRat_eq (a : D.host.E) : incA D a - pairA D.host.F 1 0 ⊗ₜ[D.host.F] a = finRat D a := by
  have h1 : (1 : AF D.host.F) = pairA D.host.F 1 0 + pairA D.host.F 0 1 :=
    Prod.ext (add_zero (1 : Ainf D.host.F)).symm (zero_add (1 : Af D.host.F)).symm
  rw [finRat_apply]
  show (1 : AF D.host.F) ⊗ₜ[D.host.F] a - _ = _
  rw [h1, TensorProduct.add_tmul, add_sub_cancel_left]

private theorem infPart_tmul' (a : AF D.host.F) (e : D.host.E) :
    infPart D (a ⊗ₜ[D.host.F] e) = fstA D.host.F a ⊗ₜ[D.host.F] e := by
  show Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) (a ⊗ₜ[D.host.F] e) = _
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]

theorem infPart_finRat (a : D.host.E) : infPart D (finRat D a) = 0 := by
  rw [finRat_apply, infPart_tmul']
  have h0 : fstA D.host.F (pairA D.host.F 0 1) = 0 := rfl
  rw [h0, TensorProduct.zero_tmul]

private theorem exists_witt_eq_teich_add_p_teich_frob_symm_add_p_sq_mul (w : AE D) :
    w = ∑ i, (Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E)).repr w i ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E i := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E)).sum_repr w]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

private theorem fstA_basis_repr_eq_zero_of_infPart_eq_zero {z : AE D} (hz : infPart D z = 0) (i : Fin (Module.finrank D.host.F D.host.E)) :
    fstA D.host.F ((Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E)).repr z i) = 0 := by
  have h1 : infPart D z = ∑ j, fstA D.host.F ((Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E)).repr z j) •
      Algebra.TensorProduct.basis (Ainf D.host.F) (Module.finBasis D.host.F D.host.E) j := by
    conv_lhs => rw [exists_witt_eq_teich_add_p_teich_frob_symm_add_p_sq_mul z]

    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [infPart_tmul', Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have h2 := congrArg
    (fun v => (Algebra.TensorProduct.basis (Ainf D.host.F) (Module.finBasis D.host.F D.host.E)).repr v i) h1
  simp only [hz, map_zero, Finsupp.coe_zero, Pi.zero_apply, Module.Basis.repr_sum_self] at h2
  exact h2.symm

private theorem eq_sum_pairA_zero_tmul_finBasis_of_infPart_eq_zero {z : AE D} (hz : infPart D z = 0) :
    z = ∑ i, pairA D.host.F 0 (sndA D.host.F ((Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E)).repr z i)) ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E i := by
  conv_lhs => rw [exists_witt_eq_teich_add_p_teich_frob_symm_add_p_sq_mul z]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  exact Prod.ext (fstA_basis_repr_eq_zero_of_infPart_eq_zero hz i) rfl

theorem mem_closure_finRat {z : AE D} (hz : infPart D z = 0) : z ∈ closure (Set.range (finRat D)) := by
  have hd : DenseRange (Pi.map fun _ : Fin (Module.finrank D.host.F D.host.E) =>
      ⇑(algebraMap D.host.F (Af D.host.F))) :=
    DenseRange.piMap fun _ => AdeleCharTwist.denseRange_fin
  have hc : Continuous fun y : Fin (Module.finrank D.host.F D.host.E) → Af D.host.F =>
      ∑ i, pairA D.host.F 0 (y i) ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E i := by
    refine continuous_finsetSum _ fun i _ => ?_
    have h1 : Continuous fun a : AF D.host.F => a ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E i := by
      have he : (fun a : AF D.host.F => a ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E i) =
          fun a => a • ((1 : AF D.host.F) ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E i) := by
        funext a
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [he]
      exact Continuous.smul (M := AF D.host.F) (X := AE D) continuous_id continuous_const
    have h2 : Continuous fun y : Fin (Module.finrank D.host.F D.host.E) → Af D.host.F => pairA D.host.F 0 (y i) := by
      show Continuous fun y : Fin (Module.finrank D.host.F D.host.E) → Af D.host.F => ((0 : Ainf D.host.F), y i)
      exact continuous_const.prodMk (continuous_apply i)
    exact h1.comp h2
  have hm : Set.MapsTo (fun y : Fin (Module.finrank D.host.F D.host.E) → Af D.host.F =>
      ∑ i, pairA D.host.F 0 (y i) ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E i)
      (Set.range (Pi.map fun _ : Fin (Module.finrank D.host.F D.host.E) => ⇑(algebraMap D.host.F (Af D.host.F))))
      (Set.range (finRat D)) := by
    rintro _ ⟨q, rfl⟩
    refine ⟨∑ i, q i • Module.finBasis D.host.F D.host.E i, ?_⟩

    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [finRat_apply, ← TensorProduct.smul_tmul]
    congr 1
    exact Prod.ext (smul_zero (q i)) ((Algebra.smul_def (q i) (1 : Af D.host.F)).trans (mul_one _))
  have hz' := map_mem_closure hc (hd fun i => sndA D.host.F ((Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E)).repr z i)) hm
  rw [eq_sum_pairA_zero_tmul_finBasis_of_infPart_eq_zero hz]
  exact hz'

theorem mem_closure_mat {m n : ℕ} {y : Mx D m n} (hy : y.map (infPart D) = 0) :
    y ∈ closure (Set.range fun ℓ : Matrix (Fin m) (Fin n) D.host.E => (ℓ.map (finRat D) : Mx D m n)) := by
  have h1 : ∀ i j, y i j ∈ closure (Set.range (finRat D)) := fun i j =>
    mem_closure_finRat (by simpa using congrFun (congrFun hy i) j)
  have h2 : (y : Fin m → Fin n → AE D) ∈
      closure (Set.univ.pi fun _ : Fin m => Set.univ.pi fun _ : Fin n => Set.range (finRat D)) := by
    refine mem_closure_pi.mpr fun i _ => ?_
    refine mem_closure_pi.mpr fun j _ => ?_
    exact h1 i j
  refine closure_mono ?_ h2
  intro x hx
  have hx' : ∀ i j, ∃ a, finRat D a = x i j := fun i j => hx i (Set.mem_univ i) j (Set.mem_univ j)
  choose ℓ hℓ using hx'
  exact ⟨Matrix.of ℓ, by ext i j; exact hℓ i j⟩

theorem actO_fin {S T : HSp D} (g : GA D S) (h : GA D T) {x : WO S T} (hx : x.map (infPart D) = 0) :
    (actO S T g h x).map (infPart D) = 0 := by
  unfold actO
  rw [Matrix.map_mul, Matrix.map_mul, hx, Matrix.mul_zero, Matrix.zero_mul]

private theorem continuous_actO_one {S T : HSp D} (h : GA D T) : Continuous (actO S T 1 h) := by
  haveI := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  unfold actO
  fun_prop

theorem exists_approx {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (g : GA D T) {x : WO S T} (hx : x.map (infPart D) = 0) :
    ∃ (ℓ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (w : WO S T), w.map (infPart D) = 0 ∧ heisO ψ S T w f = f ∧
      x = actO S T 1 g⁻¹ (ratW T S ℓ - GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt S T ℓ) + w := by
  haveI := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  obtain ⟨U, hUo, hU⟩ := hf.level
  have hy : (actO S T 1 g x).map (infPart D) = 0 := actO_fin 1 g hx
  have hVo : IsOpen {v : WO S T | actO S T 1 g⁻¹ (actO S T 1 g x - v) ∈ U} :=
    hUo.preimage ((continuous_actO_one (S := S) g⁻¹).comp (continuous_const.sub continuous_id))
  have h0 : actO S T 1 g⁻¹ 0 = 0 := by
    have h00 := GlobalTheory.HeckeVacuum.act_sub g⁻¹ (0 : WO S T) 0
    rwa [sub_self, sub_self] at h00
  have hyV : actO S T 1 g x ∈ {v : WO S T | actO S T 1 g⁻¹ (actO S T 1 g x - v) ∈ U} := by
    show actO S T 1 g⁻¹ (actO S T 1 g x - actO S T 1 g x) ∈ U
    rw [sub_self, h0]
    exact U.zero_mem
  obtain ⟨_, hvV, ℓ, rfl⟩ := mem_closure_iff.mp (mem_closure_mat (m := T.rank) (n := S.rank) hy) _ hVo hyV
  have hrat : ratW T S ℓ - GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt S T ℓ = (ℓ.map (finRat D) : WO S T) := by
    ext i j
    exact finRat_eq (ℓ i j)
  have key : actO S T 1 g⁻¹ (ratW T S ℓ - GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt S T ℓ) =
      actO S T 1 g⁻¹ (ℓ.map (finRat D)) := congrArg _ hrat
  have hw : (actO S T 1 g⁻¹ (actO S T 1 g x - ℓ.map (finRat D))).map (infPart D) = 0 := by
    refine actO_fin 1 g⁻¹ ?_
    ext i j
    have hij : infPart D (actO S T 1 g x i j) = 0 := by simpa using congrFun (congrFun hy i) j
    simp [hij, infPart_finRat]
  refine ⟨ℓ, actO S T 1 g⁻¹ (actO S T 1 g x - ℓ.map (finRat D)), hw,
    hU (actO S T 1 g⁻¹ (actO S T 1 g x - ℓ.map (finRat D))) hvV hw, ?_⟩
  rw [key, GlobalTheory.HeckeVacuum.act_sub, add_sub_cancel, ← GlobalTheory.HeckeVacuum.act_mul, inv_mul_cancel,
    GlobalTheory.HeckeVacuum.act_one]

theorem exists_rat_approx : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F),
    R.toLevCh.Is A.μ0 → R.IsFam → R.IsThP → ∀ (i : Fin D.R.m) (g : GA D (Wc D i)) (x : WO (Vc D i) (Wc D i)),
    x.map (infPart D) = 0 → ∃ (ℓ : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E) (w : WO (Vc D i) (Wc D i)),
      w.map (infPart D) = 0 ∧ heisO R.ψ (Vc D i) (Wc D i) w (R.vacP i) = R.vacP i ∧
      x = actO (Vc D i) (Wc D i) 1 g⁻¹ (ratW (Wc D i) (Vc D i) ℓ - GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) ℓ) + w := by
  intro D G _ _ Pl0 T0 A T _ R _ _ hP i g x hx
  exact exists_approx (hP.vP i A.μ0).1.2.theta g hx

end GlobalTheory.FinApprox
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Chain.RealIt GlobalTheory.PairLift

noncomputable section

namespace GlobalTheory.VacCjNeg

variable {D : D7}


open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger in
theorem dRho_cj {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (θ : InfFam D)
    (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (f : WO S T → ℂ) :
    dRho (heisO ψ S T) θ τ z (cj id f) = cj id (dRho (heisO ψ (GlobalTheory.Grid.neg S) T) θ τ z f) := by
  funext x
  show deriv (fun t : ℝ => heisO ψ S T (lineAt θ τ z t) (cj id f) x) 0 =
    starRingEnd ℂ (deriv (fun t : ℝ => heisO ψ (GlobalTheory.Grid.neg S) T (lineAt θ τ z t) f x) 0)
  have e : (fun t : ℝ => heisO ψ S T (lineAt θ τ z t) (cj id f) x) =
      fun t => star (heisO ψ (GlobalTheory.Grid.neg S) T (lineAt θ τ z t) f x) := by
    funext t
    rw [GlobalTheory.CjNeg.heis_negS' hψ]
    rfl
  rw [e, deriv.star]
  rfl

theorem isVacVec_cj_of_isVac_neg : ∀ {D : D7} (S T : GlobalTheory.Grid.Node D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (f : WO S.V T.V → ℂ), GlobalTheory.Grid.IsVac ψ θ true S T f →
      GlobalTheory.Chain.IsVacVec ψ θ S.M T.M (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f) := by
  intro D S T ψ θ f h
  obtain ⟨hψ, hv⟩ := h
  have hth : IsThetaFunO ψ (GlobalTheory.Grid.neg S.V) T.V f := hv.theta
  refine ⟨GlobalTheory.CjNeg.theta_negS' hψ (show IsThetaFunO ψ (GlobalTheory.ChiGrid.negSp S.V) T.V f from hth), ?_, fun τ => ?_⟩
  · intro h0
    have hf0 : f = 0 := by
      rw [← GlobalTheory.CjNeg.cj_id_cj_id f, h0]
      funext x
      simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]
    obtain ⟨⟨p, hp⟩, hall⟩ := hv.norm
    have h1 := hall p hp
    rw [hf0] at h1
    simp [nrm2] at h1
  · intro z
    have h0 : annih (heisO ψ (GlobalTheory.Grid.neg S.V) T.V) θ τ (cplxO (-(cart S.M τ)) (cart T.M τ)) z f = 0 :=
      hv.fock τ z
    have hJ : cplxO (-(cart S.M τ)) (cart T.M τ) z = -cplxO (cart S.M τ) (cart T.M τ) z := by
      simp [cplxO]
    unfold annih at h0 ⊢
    rw [hJ, GlobalTheory.FockAdjoint.dRho_neg' hψ hv.inf hth] at h0
    rw [dRho_cj hψ, dRho_cj hψ]
    funext x
    have h2 := congrFun h0 x
    simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, Pi.zero_apply] at h2 ⊢
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, id_eq]
    have e := congrArg (starRingEnd ℂ) h2
    simp only [map_add (f := _), map_mul, map_neg, Complex.conj_I, map_zero] at e
    linear_combination e

end GlobalTheory.VacCjNeg

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

theorem _root_.GlobalTheory.T.moyal_orthogonality_heisenberg_thetaFunctions : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (v : VolM D T.rank S.rank) f f₀, IsThetaFunO ψ S T f → IsThetaFunO ψ S T f₀ → Integrable (fun w => thPair v.μ v.𝓕 f (heisO ψ S T w f₀)) v.μ ∧ ∀ x, ∫ w, thPair v.μ v.𝓕 f (heisO ψ S T w f₀) * heisO ψ S T w f₀ x ∂v.μ = thPair v.μ v.𝓕 f₀ f₀ * f x := by
  first | exact @GlobalTheory.MoyalTheta.orthogonality | exact GlobalTheory.MoyalTheta.orthogonality | (intros; apply GlobalTheory.MoyalTheta.orthogonality <;> assumption)
end
