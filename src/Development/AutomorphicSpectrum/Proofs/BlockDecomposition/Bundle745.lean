module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle035
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle711
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2130
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle744
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspFormSiegelBound
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockTranslateSchwartzMajorant
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle020
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianIsSchwartzFunction
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle525
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle268
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtAndIsTheta
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.SatakeSocle.SocleOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle296
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle375
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.ExhaustionOfThree
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.Bundle004
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnitaryDualGLOfTwo
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LFunctionSideEquidistribution
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle607
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle467
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore

@[expose] public section

section

noncomputable section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.CompanionTheory.QKAvg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SkewMod

open GlobalTheory.CompanionTheory.IwaAd GlobalTheory.CompanionTheory.CgMod

variable {D : D7} {n : ℕ}

def skewPart (D : D7) (n : ℕ) (x : Mx D n n) : Mx D n n := half D • (x - adj x)

theorem skewPart_add (x y : Mx D n n) : skewPart D n (x + y) = skewPart D n x + skewPart D n y := by
  simp only [skewPart, adj_add]
  rw [← smul_add]
  congr 1
  abel

def skewPartHom (D : D7) (n : ℕ) : Mx D n n →+ Mx D n n := AddMonoidHom.mk' (skewPart D n) skewPart_add

theorem skewPart_mem (x : Mx D n n) : skewPart D n x ∈ skewA D n := by
  rw [mem_skewA, skewPart, adj_smul, cA_half, adj_sub, adj_adj, ← smul_neg, neg_sub]

theorem skewPart_of_mem {s : Mx D n n} (hs : s ∈ skewA D n) : skewPart D n s = s := by
  rw [skewPart, mem_skewA.1 hs, sub_neg_eq_add, smul_add]
  exact half_smul_add s

theorem skewPart_anti {c : AE D} (hc : cA D c = -c) {s : Mx D n n} (hs : s ∈ skewA D n) :
    skewPart D n (c • s) = 0 := by
  rw [skewPart, adj_smul, mem_skewA.1 hs, hc, neg_smul, smul_neg, neg_neg, sub_self, smul_zero]

theorem skewPart_split {d e : AE D} (he : cA D e = -e) (hde : d * e = 1) (x : Mx D n n) :
    skewPart D n x + d • skewPart D n (e • x) = x := by
  have h : d * half D * e = half D := by rw [mul_comm d, mul_assoc, hde, mul_one]
  rw [skewPart, skewPart, adj_smul, he, neg_smul, sub_neg_eq_add, ← smul_add, smul_smul, smul_smul, h, smul_add,
    smul_sub]
  have := half_smul_add x
  rw [sub_add_add_cancel]
  exact this

set_option synthInstance.maxHeartbeats 400000 in
theorem continuous_skewPart : Continuous (skewPartHom D n) := by
  haveI : IsTopologicalAddGroup (Mx D n n) := (lattice_Mx D n n).1
  have h : Continuous fun x : Mx D n n => x - adj x := continuous_id.sub (continuous_adj (D := D) (m := n) (n := n))
  change Continuous fun x : Mx D n n => half D • (x - adj x)
  exact h.const_smul (half D)

theorem lr_skew (a : GL (Fin n) (AE D)) : ∀ s ∈ skewA D n, GlobalTheory.ModuLR.lrCE a (ad a)⁻¹ s ∈ skewA D n :=
  fun s hs => (skewConj a.1 ⟨s, hs⟩).2

theorem lr_skew_symm (a : GL (Fin n) (AE D)) :
    ∀ s ∈ skewA D n, (GlobalTheory.ModuLR.lrCE a (ad a)⁻¹).symm s ∈ skewA D n :=
  fun s hs => (skewConj (a⁻¹).1 ⟨s, hs⟩).2


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem map_skewConj : ∀ (D : D7) (r : ℕ) (κ : Measure (skewA D r)), κ.IsAddHaarMeasure → ∀ a : GL (Fin r) (AE D), κ.map (skewConj a.1) = ((absA D (Matrix.GeneralLinearGroup.det a) ^ r)⁻¹ : ℝ≥0) • κ := by
  intro D n κ hκ a
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D n n
  haveI : IsTopologicalAddGroup (Mx D n n) := i1
  haveI : LocallyCompactSpace (Mx D n n) := i2
  haveI : SecondCountableTopology (Mx D n n) := i3
  haveI : T2Space (Mx D n n) := i4
  haveI : BorelSpace (Mx D n n) := ⟨rfl⟩
  haveI : BorelSpace (skewA D n) := Subtype.borelSpace _
  haveI : SecondCountableTopology (skewA D n) := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : T2Space (skewA D n) := Topology.IsEmbedding.subtypeVal.t2Space
  have hcl : IsClosed (skewA D n : Set (Mx D n n)) := isClosed_eq continuous_adj continuous_neg
  haveI : LocallyCompactSpace (skewA D n) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  obtain ⟨d, e, hde, hd, he⟩ := exists_anti_units D
  have hsq := char_sq (skewA D n) (skewPartHom D n) continuous_skewPart skewPart_mem
    (fun s hs => skewPart_of_mem hs) (mulCE d e hde)
    (fun s hs => skewPart_anti hd hs) (fun s hs => skewPart_anti he hs)
    (fun x => skewPart_split he hde x) (GlobalTheory.ModuLR.lrCE a (ad a)⁻¹)
    (lr_smul a d e hde) (lr_skew a) (lr_skew_symm a)
  have hlr : addEquivAddHaarChar (GlobalTheory.ModuLR.lrCE a (ad a)⁻¹) =
      absA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) ^ n * absA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) ^ n := by
    have h := GlobalTheory.ResidueEisenstein.ModMat.addEquivAddHaarChar_lrCE _ _ D.sp.cm.sig (isCMExt_host D) n n a (ad a)⁻¹
    rw [h]
    exact congrArg (fun t => absA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) ^ n * t ^ n) (absA_det_ad_inv a)
  have hT : addEquivAddHaarChar (restr (skewA D n) _ (lr_skew a) (lr_skew_symm a)) =
      absA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) ^ n :=
    (pow_left_inj₀ zero_le zero_le two_ne_zero).1 ((hsq.trans hlr).trans (sq _).symm)
  have h := addEquivAddHaarChar_smul_map κ (restr (skewA D n) _ (lr_skew a) (lr_skew_symm a))
  have e1 : (⇑(restr (skewA D n) _ (lr_skew a) (lr_skew_symm a)) : skewA D n → skewA D n) = skewConj a.1 := rfl
  rw [hT, e1] at h
  have hne : absA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) ^ n ≠ 0 := pow_ne_zero _ (absA_pos _).ne'
  conv_rhs => rw [← h]
  rw [smul_smul, inv_mul_cancel₀ hne, one_smul]

end GlobalTheory.CompanionTheory.SkewMod
end
end

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.cusp_form_siegel_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (K : Subgroup (GAd σ J)) (Ω : Set (GAd σ J)) (c : ℝ), IsCompact (K : Set (GAd σ J)) → IsCompact Ω → Ω ⊆ minParOne σ J X → 0 < c → ∃ (C : ℝ≥0) (A : ℕ), ∀ g ∈ siegelSet σ J X Y Ω c K, ∀ γ ∈ ratPts σ J, height σ J g ≤ C * height σ J (γ * g) ^ A := by
  first | exact @GlobalTheory.CompanionTheory.SiegelHt.height_le_pow | exact GlobalTheory.CompanionTheory.SiegelHt.height_le_pow | (intros; apply GlobalTheory.CompanionTheory.SiegelHt.height_le_pow <;> assumption)
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

theorem _root_.GlobalTheory.T.hermitian_measure_conjugation : ∀ (D : D7) (n : ℕ) (lam : Measure (hermA D n)), lam.IsAddHaarMeasure → ∀ (a : GL (Fin n) (AE D)) (f : hermA D n → ℂ), ∫ c, f (GlobalTheory.CompanionTheory.IwaAd.cg a c) ∂lam = npow (absA D (Matrix.GeneralLinearGroup.det a)) (-(n : ℂ)) * ∫ c, f c ∂lam := by
  first | exact @GlobalTheory.CompanionTheory.CgMod.integral_cg | exact GlobalTheory.CompanionTheory.CgMod.integral_cg | (intros; apply GlobalTheory.CompanionTheory.CgMod.integral_cg <;> assumption)
end
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.CompanionTheory.ThTot
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.ThTot.OneRow

variable {D : D7}

theorem evalPoly_temperate {m n : ℕ} (p : MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ) :
    Function.HasTemperateGrowth
      (fun z : D.what₂.Tau → Fin m → Fin n → ℂ => evalPoly p (fun τ => Matrix.of (z τ))) := by
  have coord : ∀ k : D.what₂.Tau × Fin m × Fin n × Bool, Function.HasTemperateGrowth
      (fun z : D.what₂.Tau → Fin m → Fin n → ℂ =>
        if k.2.2.2 then conj (z k.1 k.2.1 k.2.2.1) else z k.1 k.2.1 k.2.2.1) := by
    rintro ⟨τ, i, j, b⟩
    let L : (D.what₂.Tau → Fin m → Fin n → ℂ) →L[ℝ] ℂ :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) j).comp
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) i).comp
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : D.what₂.Tau => Fin m → Fin n → ℂ) τ))
    cases b
    · exact L.hasTemperateGrowth
    · exact (Complex.conjCLE.toContinuousLinearMap.comp L).hasTemperateGrowth
  induction p using MvPolynomial.induction_on with
  | C a => simpa [evalPoly] using Function.HasTemperateGrowth.const a
  | add p q hp hq =>
    have : (fun z : D.what₂.Tau → Fin m → Fin n → ℂ => evalPoly (p + q) (fun τ => Matrix.of (z τ))) =
        (fun z => evalPoly p (fun τ => Matrix.of (z τ))) + fun z => evalPoly q (fun τ => Matrix.of (z τ)) := by
      funext z; simp [evalPoly]
    rw [this]; exact hp.add hq
  | mul_X p k hp =>
    have : (fun z : D.what₂.Tau → Fin m → Fin n → ℂ => evalPoly (p * MvPolynomial.X k) (fun τ => Matrix.of (z τ))) =
        (fun z => evalPoly p (fun τ => Matrix.of (z τ))) * fun z =>
          if k.2.2.2 then conj (z k.1 k.2.1 k.2.2.1) else z k.1 k.2.1 k.2.2.1 := by
      funext z; simp [evalPoly]
    rw [this]; exact hp.mul (coord k)

theorem exists_schwartz_poly_gauss (n : ℕ) (V : HSp D) (l : D.what₂.Tau → ℝ) (hl : ∀ τ, l τ ≠ 0)
    (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (hs : ∀ τ, IsCartanInv (gramAt D V τ) (s τ))
    (p : MvPolynomial (D.what₂.Tau × Fin V.rank × Fin n × Bool) ℂ) :
    ∃ f : SchwartzMap (D.what₂.Tau → Fin V.rank → Fin n → ℂ) ℂ, ∀ z,
      f z = evalPoly p (fun τ => Matrix.of (z τ)) * gauss V l s (fun τ => Matrix.of (z τ)) := by
  obtain ⟨f, hf⟩ := GlobalTheory.GaussSchwartz.exists_schwartz_gauss D n V l hl s hs
  refine ⟨SchwartzMap.smulLeftCLM (𝕜 := ℂ) ℂ (fun z : D.what₂.Tau → Fin V.rank → Fin n → ℂ =>
    evalPoly p (fun τ => Matrix.of (z τ))) f, fun z => ?_⟩
  rw [SchwartzMap.smulLeftCLM_apply (evalPoly_temperate p)]
  simp [hf]

theorem fockA_le_schwartzA (θ : InfFam D) (V : HSp D) (n : ℕ) (l : D.what₂.Tau → ℝ) (hl : ∀ τ, l τ ≠ 0)
    (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (hs : ∀ τ, IsCartanInv (gramAt D V τ) (s τ)) :
    fockA θ V n l s ≤ schwartzA θ V.rank n := by
  refine Submodule.span_le.2 ?_
  rintro φ ⟨p, g, hg, rfl⟩
  obtain ⟨f, hf⟩ := exists_schwartz_poly_gauss n V l hl s hs p
  refine Submodule.subset_span ⟨f, g, hg, ?_⟩
  funext x
  rw [hf]
  rfl

theorem gram_rank_one_one : (V1 D).gram = 1 := by
  refine Matrix.ext fun (i j : Fin 1) => ?_
  obtain rfl : i = 0 := Subsingleton.elim _ _
  obtain rfl : j = 0 := Subsingleton.elim _ _
  show ∑ k : Fin 1, star ((Pi.basisFun D.host.E (Fin 1)) 0 k) * Formalism.BasicNotions.Examples₂.sgn false * (Pi.basisFun D.host.E (Fin 1)) 0 k =
    (1 : Matrix (Fin 1) (Fin 1) D.host.E) 0 0
  simp [Formalism.BasicNotions.Examples₂.sgn]

theorem gram_at_place_rank_one (τ : D.what₂.Tau) : gramAt D (V1 D) τ = 1 := by
  unfold gramAt
  rw [gram_rank_one_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem cartan_involution_rank_one (τ : D.what₂.Tau) : IsCartanInv (gramAt D (V1 D) τ) 1 := by
  rw [gram_at_place_rank_one]
  refine ⟨by simp, by simp, ?_⟩
  rw [Matrix.mul_one]
  exact Matrix.PosDef.one

theorem gram_rank_one_eq_one : gA (V1 D) = (1 : Mx D (V1 D).rank (V1 D).rank) := by
  unfold gA rat
  rw [gram_rank_one_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)


theorem incA_algebraMap (c : D.host.F) :
    incA D (algebraMap D.host.F D.host.E c) = (algebraMap D.host.F (AF D.host.F) c) • (1 : AE D) := by
  show (1 : AF D.host.F) ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E c) =
    (algebraMap D.host.F (AF D.host.F) c) • ((1 : AF D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E))
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, Algebra.algebraMap_eq_smul_one,
    Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

theorem pr_eq {p : ℕ} (b₀ : HermE D 1) (c : D.host.F) (hc : algebraMap D.host.F D.host.E c = b₀.1 0 0)
    (x y : Mx D 1 p) :
    pr b₀ x y = (algebraMap D.host.F (AF D.host.F) c) • (inner (V1 D) x y : Mx D p p) := by
  have h1 : b₀.1.map (incA D) = (algebraMap D.host.F (AF D.host.F) c) • (1 : Mx D 1 1) := by
    refine Matrix.ext fun (i j : Fin 1) => ?_
    fin_cases i; fin_cases j
    simp [← hc, incA_algebraMap]
  have h2 : (inner (V1 D) x y : Mx D p p) = HMul.hMul (adj x) y := by
    unfold GlobalTheory.StdUnn.inner
    rw [gram_rank_one_eq_one]
    exact congrArg (fun t : Mx D 1 p => (HMul.hMul (adj x) t : Mx D p p)) (Matrix.one_mul y)
  rw [h2]
  unfold pr
  rw [h1, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul]

theorem trA_smul (a : AF D.host.F) (z : AE D) : trA (a • z) = a * trA z := by
  simp [trA, map_smul]

theorem halfTr_smul (a : AF D.host.F) (z : AE D) : halfTr (a • z) = a * halfTr z := by
  simp only [halfTr, trA_smul]; ring

theorem exists_base (b₀ : HermE D 1) (h : b₀.1.det ≠ 0) :
    ∃ c : D.host.F, c ≠ 0 ∧ algebraMap D.host.F D.host.E c = b₀.1 0 0 := by
  have h0 : b₀.1 0 0 ≠ 0 := by simpa [Matrix.det_fin_one] using h
  have hfix : star (b₀.1 0 0) = b₀.1 0 0 := congrFun (congrFun b₀.2 0) 0
  have hF : b₀.1 0 0 ∈ D.host.F :=
    (NumberField.IsCMField.complexConj_eq_self_iff D.host.E _).1 hfix
  exact ⟨⟨_, hF⟩, fun e => h0 (by simpa using congrArg (fun u : D.host.F => (u : D.host.E)) e), rfl⟩

theorem exists_par (ψ₀ : AddChar (AF D.host.F) ℂ) (h₀ : IsStdChar D ψ₀ (-1)) (θ : InfFam D) (hθ : IsInfFam θ)
    (a : D.host.F) (ha : a ≠ 0) :
    IsCharAF D.host.F (shift ψ₀ a) ∧ ∃ l : D.what₂.Tau → ℝ, HasRealPar (shift ψ₀ a) θ l ∧ ∀ τ, l τ ≠ 0 := by
  have hxi : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  have haE : algebraMap D.host.F D.host.E a ≠ 0 := (map_ne_zero _).2 ha
  have hst : star (algebraMap D.host.F D.host.E a) = algebraMap D.host.F D.host.E a :=
    (NumberField.IsCMField.complexConj_eq_self_iff D.host.E _).2 a.2
  have hsk : IsSkew (-D.host.xi0 / algebraMap D.host.F D.host.E a) := by
    refine ⟨div_ne_zero (neg_ne_zero.2 hxi) haE, ?_⟩
    rw [star_div₀, star_neg, hst, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg D, neg_div]
  obtain ⟨lam, hlam, hc, l, hp, habs⟩ := shift_char_realPar D ψ₀ h₀ θ hθ _ hsk
  have : lam = a := by
    apply (algebraMap D.host.F D.host.E).injective
    rw [hlam]
    field_simp
  subst this
  refine ⟨hc, l, hp, fun τ h => ?_⟩
  have := habs τ
  rw [h, abs_zero] at this
  have h1 : tauE D τ D.host.xi0 ≠ 0 := (map_ne_zero _).2 hxi
  have h2 : tauE D τ (-D.host.xi0 / algebraMap D.host.F D.host.E lam) ≠ 0 := (map_ne_zero _).2 hsk.1
  exact (div_ne_zero (norm_ne_zero_iff.2 h1) (norm_ne_zero_iff.2 h2)) this.symm

theorem oneTotal : WeilCont → FockTranslateSchwartzMajorant → FockTotal → OneTotal := by
  intro hC hM hF D p μ 𝓕 hμ ψ hψ b₀ hdet χ hχ hr θ hθ
  obtain ⟨c, hc0, hc⟩ := exists_base b₀ hdet
  obtain ⟨ψ₀, h₀, lam, hlam0, hlam⟩ := GlobalTheory.ThetaAllChar.exists_std hψ
  have hne : lam * c ≠ 0 := mul_ne_zero hlam0 hc0
  obtain ⟨hψ₁, l, hpar, hl⟩ := exists_par ψ₀ h₀ θ hθ (lam * c) hne
  have hs : ∀ t, shift ψ₀ (lam * c) t = ψ (algebraMap D.host.F (AF D.host.F) c * t) := by
    intro t
    rw [hlam]
    simp [shift, AddChar.mulShift_apply, map_mul, mul_assoc]
  obtain ⟨ω, hω⟩ := GlobalTheory.StdUnn.Inhab.weil_exists D p (V1 D) ψ₀ h₀ (lam * c) hne χ hχ hr θ hθ μ 𝓕 hμ
  intro u huc hub hu
  refine hF D p θ hθ l hl μ 𝓕 hμ u huc hub fun φ hφ => ?_
  have hφS := fockA_le_schwartzA θ (V1 D) p l hl _ (fun τ => cartan_involution_rank_one τ) hφ
  let Φ : schwartzA θ (V1 D).rank p := ⟨φ, hφS⟩
  have e : ∀ g h : G D p, ω (g * h) Φ = ω g (ω h Φ) := fun g h => by rw [map_mul]; rfl
  have hT : IsTh ψ χ θ b₀ μ (fun h => (ω h Φ).1) :=
    { mem := fun h => (ω h Φ).2
      cont := hC D p (V1 D) _ hψ₁ χ hχ hr θ hθ μ 𝓕 hμ ω hω Φ
      maj := hM D p _ hψ₁ χ hχ hr θ hθ μ 𝓕 hμ ω hω l hpar hl Φ hφ
      levi := by
        intro g a hg h y
        show (ω (g * h) Φ).1 y = _
        rw [e]
        exact hω.levi g a hg _ y
      unip := by
        intro g b hg h y
        show (ω (g * h) Φ).1 y = _
        rw [e, hω.unip g b hg _ y, hs, pr_eq b₀ c hc, Matrix.mul_smul, Matrix.trace_smul, halfTr_smul]
      weyl := by
        intro g hg h x
        show (ω (g * h) Φ).1 x = _
        rw [e, hω.weyl g hg _ x]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        show _ * shift ψ₀ (lam * c) _ = _ * ψ _
        rw [hs, pr_eq b₀ c hc x y, Matrix.trace_smul, trA_smul] }
  have h1 : ∫ y, u y * conj ((ω 1 Φ).1 y) ∂μ = 0 := hu _ hT
  have h2 : (ω 1 Φ).1 = φ := by rw [map_one]; rfl
  rw [h2] at h1
  exact h1

end GlobalTheory.CompanionTheory.ThTot.OneRow

end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.CompanionTheory.LocGL

theorem isSocle_prodIrr_congr {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {h N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin N) k) V} {y z : Fin h → IrrGL (k := k)} (e : y = z)
    (hy : ∑ a, (y a).1 = N) (hz : ∑ a, (z a).1 = N) (H : IsSocle π (prodIrr y hy)) :
    IsSocle π (prodIrr z hz) := by
  subst e
  exact H

theorem socleOne : PositivityTheory.SphericalProduct.SocleOne := by
  intro k _ _ _ _ _ n ξ hξ hanti hd
  let x : Fin n → IrrGL (k := k) := fun i =>
    IrrGL.ofChar (ξ (Fin.rev i)) (isSmoothChar_of_isUnram (hξ (Fin.rev i)))
  have hLF : LFactors (PositivityTheory.SphericalProduct.msOne ξ hξ) x :=
    ⟨_, GlobalTheory.CompanionTheory.OneTermOrder.isOrderedForm_single_rev k n ξ hξ hanti, fun i => isLSeg_single k _ _⟩
  have hd1 : ∑ a, (x a).1 = n := by simp [x, IrrGL.ofChar]
  have hd2 : ∑ a, (x (Fin.rev a)).1 = n := by simp [x, IrrGL.ofChar]
  refine ⟨?_, ?_⟩
  · obtain ⟨π, hπ⟩ := PositivityTheory.Exh.standardCosocleGL_holds k _ n n x hd1 hLF
    have hL : IsL (PositivityTheory.SphericalProduct.msOne ξ hξ) π.ρ := ⟨n, x, hd1, hLF, hπ⟩
    exact ⟨IrrGL.of π.ρ π.smooth π.irr, rfl, hL.of_equiv (IrrGL.equivOf _ _ _)⟩
  · intro V _ _ π hL
    have hS := PositivityTheory.Exh.lSocleGL_of GlobalTheory.RgGu.Holds.lUnlinkedIrr_holds k _ n n x hd2 hLF π hL
    refine isSocle_prodIrr_congr ?_ _ hd hS
    funext a
    simp only [x, Function.comp, Fin.rev_rev]

end GlobalTheory.CompanionTheory.LocGL
end

section

open PositivityTheory.Rg.Base1

theorem _root_.GlobalTheory.T.l_function_side_equidistribution : PositivityTheory.Rg.Mass.Equi → LSide := by
  first | exact @GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.lside | exact GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.lside | (intros; apply GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.lside <;> assumption)
end
