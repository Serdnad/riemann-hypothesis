module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle137
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle353
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle165
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle333
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentBesselCharacterLaws
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IsMulRightInvariantOfLattice
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle343
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle346
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorThetaFunctionalMixedSourceMode
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergTranslateThetaContinuousDifferentiable
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinateDecayRealEntries
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerFunctionLinearThetaFunctions
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle347
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOneComb
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ToOneSucc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle324
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open Filter Topology

namespace GlobalTheory.PlaceSplitPt

section Val

variable {K K' : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field K'] [ValuativeRel K'] [TopologicalSpace K'] [IsNonarchimedeanLocalField K']

theorem tendsto_pow_zero {x : K} (h : valuation K x < 1) : Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) := by
  rw [(IsValuativeTopology.hasBasis_nhds_zero' K).tendsto_right_iff]
  intro γ hγ
  have : MulArchimedean (ValueGroupWithZero K) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨n, hn⟩ := exists_pow_lt₀ h (Units.mk0 γ hγ)
  filter_upwards [eventually_ge_atTop n] with m hm
  rw [map_pow]
  exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' h.le hm) hn

theorem lt_one_mem_nhds : {y : K' | valuation K' y < 1} ∈ 𝓝 (0 : K') :=
  (IsValuativeTopology.hasBasis_nhds_zero' K').mem_iff.2 ⟨1, one_ne_zero, fun _ hy => hy⟩

theorem lt_one_of_map (i : K →+* K') (hi : Continuous i) {x : K} (h : valuation K x < 1) :
    valuation K' (i x) < 1 := by
  have h1 : Tendsto (fun n : ℕ => i x ^ n) atTop (𝓝 0) := by
    have := (hi.tendsto 0).comp (tendsto_pow_zero h)
    simpa [Function.comp_def, map_pow] using this
  obtain ⟨N, hN⟩ := (h1.eventually lt_one_mem_nhds).exists
  by_contra hc
  push_neg at hc
  have : 1 ≤ valuation K' (i x ^ N) := by rw [map_pow]; exact one_le_pow₀ hc
  exact absurd hN (not_lt.2 this)

theorem le_one_of_map (i : K →+* K') (hi : Continuous i) {y : K} (h : valuation K' (i y) ≤ 1) :
    valuation K y ≤ 1 := by
  by_contra hc
  push_neg at hc
  have hy : y ≠ 0 := fun h0 => by simp [h0] at hc
  have h1 : valuation K y⁻¹ < 1 := by rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hc
  have h2 := lt_one_of_map i hi h1
  rw [map_inv₀, map_inv₀] at h2
  have h0 : (0 : ValueGroupWithZero K') < valuation K' (i y) := by
    rw [zero_lt_iff, Valuation.ne_zero_iff]
    exact (map_ne_zero i).2 hy
  exact absurd h (not_le.2 ((inv_lt_one₀ h0).1 h2))

theorem mem_integer_iff_of_equiv (σ : K ≃+* K') (h1 : Continuous σ) (h2 : Continuous σ.symm) (a : K) :
    a ∈ 𝒪[K] ↔ σ a ∈ 𝒪[K'] := by
  rw [Valuation.mem_integer_iff, Valuation.mem_integer_iff]
  constructor
  · intro h
    refine le_one_of_map σ.symm.toRingHom h2 ?_
    change valuation K (σ.symm (σ a)) ≤ 1
    rwa [σ.symm_apply_apply]
  · exact le_one_of_map σ.toRingHom h1

end Val

open GlobalTheory.FinPl GlobalTheory.FinPl.SplitPoint GlobalTheory.IdemModTwo GlobalTheory.SplitIdem GlobalTheory.SplitChart GlobalTheory.SplitHecke GlobalTheory.LocMod

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem ι_mul (p : Place D k) (x y : k) : p.ι (x * y) = p.ι x * p.ι y := by
  conv_lhs => rw [← p.π_ι x, ← p.π_ι y, ← RingHom.map_mul, p.ι_π, ← mul_assoc, Witness.e_ι]

section Chart

variable {v : Pl D} (p : Place D k) (he : SplitAt D v p.e)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def toFv : k ≃+* Fv D.host.F v where
  toFun a := comp he (p.ι a)
  invFun b := p.π (sec D v p.e b)
  left_inv a := by
    change p.π (sec D v p.e (comp he (p.ι a))) = a
    rw [GlobalTheory.LocMod.SplitCompl.sec_comp, Witness.e_ι, p.π_ι]
  right_inv b := by
    change comp he (p.ι (p.π (sec D v p.e b))) = b
    rw [p.ι_π, map_mul, comp_self, one_mul, GlobalTheory.LocMod.SplitCompl.comp_sec]
  map_mul' x y := by
    change comp he (p.ι (x * y)) = comp he (p.ι x) * comp he (p.ι y)
    rw [ι_mul, map_mul]
  map_add' x y := by
    change comp he (p.ι (x + y)) = comp he (p.ι x) + comp he (p.ι y)
    rw [map_add (f := _), map_add (f := _)]

theorem continuous_toFv : Continuous (toFv p he) := (continuous_comp he).comp p.cont_ι

theorem continuous_toFv_symm : Continuous (toFv p he).symm := p.cont_π.comp continuous_sec

include he in
theorem int_iff (a : k) : a ∈ 𝒪[k] ↔ finPart D (p.ι a) ∈ intAE D := by
  rw [mem_integer_iff_of_equiv (toFv p he) (continuous_toFv p he) (continuous_toFv_symm p he) a,
    GlobalTheory.LocMod.SplitCompl.int_iff_sec he]
  change finPart D (sec D v p.e (comp he (p.ι a))) ∈ intAE D ↔ _
  rw [GlobalTheory.LocMod.SplitCompl.sec_comp, Witness.e_ι]

end Chart

theorem exists_splitPt : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : GlobalTheory.LocMod.Place D k), ∃ q : GlobalTheory.FinPl.SplitPt D k, GlobalTheory.LocMod.Place.ofSplitPt q = p := by
  intro D k _ _ _ _ p
  obtain ⟨-, -, v, ε, hε, hs⟩ := p.split
  have he : SplitAt D v p.e := splitAt_of p.split hε hs
  exact ⟨⟨v, p.e, p.split, ⟨ε, hε, hs⟩, p.π, p.ι, p.π_ι, p.ι_π, p.cont_π, p.cont_ι, int_iff p he⟩, rfl⟩

end GlobalTheory.PlaceSplitPt

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.NormalFramePeriod

variable {D : D7}

theorem setIntegral_mul_right_N {ρ : ℕ} (B : BesLev D ρ) (G : flagN B.d → ℂ)
    (hG : ∀ γ ∈ NFlagQ B.V B.d.e, ∀ n, G (γ * n) = G n) (y : flagN B.d) :
    ∫ n in B.vN.𝓝, G (n * y) ∂B.vN.ν = ∫ n in B.vN.𝓝, G n ∂B.vN.ν := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.V
  obtain ⟨j1, j2, j3, j4⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag B.V (isIsoSub_e B.d)
  obtain ⟨u1, u2, u3⟩ := B.vN.unit
  haveI : DiscreteTopology (NFlagQ B.V B.d.e) := by
    refine DiscreteTopology.of_continuous_injective
      (f := fun γ : NFlagQ B.V B.d.e => (⟨γ.1.1, γ.2⟩ : GQ B.V)) ?_ ?_
    · exact Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
    · intro a b hab
      exact Subtype.ext (Subtype.ext (congrArg (fun x : GQ B.V => (x : GA D B.V)) hab))
  obtain ⟨K, hK, hcov⟩ := (GlobalTheory.T.isotropic_unipotentRadicals_rational_cocompact D B.V ρ B.d.e (isIsoSub_e B.d)).1
  have hcov' : ∀ x : flagN B.d, ∃ s ∈ NFlagQ B.V B.d.e, s * x ∈ K := fun x => by
    obtain ⟨γ, hγ, k, hk, e⟩ := hcov x
    exact ⟨γ⁻¹, inv_mem hγ, by rw [e, ← mul_assoc, inv_mul_cancel, one_mul]; exact hk⟩
  have hr : ∀ a : flagN B.d, B.vN.ν.map (· * a) = B.vN.ν := fun a =>
    Formalism.L2.SG.CovariantRepresentation.haar_map_mul_right_of_lattice B.vN.ν (NFlagQ B.V B.d.e) hK hcov' a
  have hmp : MeasurePreserving (· * y) B.vN.ν B.vN.ν := ⟨measurable_mul_const y, hr y⟩
  have hmp' : MeasurePreserving (· * y⁻¹) B.vN.ν B.vN.ν := ⟨measurable_mul_const y⁻¹, hr y⁻¹⟩
  rw [← hmp.setIntegral_image_emb (measurableEmbedding_mulRight y) G B.vN.𝓝, Set.image_mul_right]
  have hF : IsFundamentalDomain (NFlagQ B.V B.d.e) ((· * y⁻¹) ⁻¹' B.vN.𝓝) B.vN.ν :=
    u2.preimage_of_equiv hmp'.quasiMeasurePreserving (e := id) Function.bijective_id
      fun g x => by simp [Subgroup.smul_def, smul_eq_mul, mul_assoc]
  exact (u2.setIntegral_eq hF fun γ x => hG γ γ.2 x).symm

theorem inner_N {ρ : ℕ} (B : BesLev D ρ) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ)
    (φ : GA D B.A → ℂ) (f : GA D B.V → ℂ) (hf : ∀ γ ∈ GQ B.V, ∀ g, f (γ * g) = f g)
    {x : GA D B.V} (hx : x ∈ flagN B.d) (h : GA D B.A) :
    ∫ n in B.vN.𝓝, besFun ψ 1 B.d B.o B.ζ φ (rTrans x f) h n ∂B.vN.ν =
      psiBes ψ B.d 1 (vecB B.o B.ζ) x * ∫ n in B.vN.𝓝, besFun ψ 1 B.d B.o B.ζ φ f h n ∂B.vN.ν := by
  obtain ⟨-, -, hconj, -, -⟩ := GlobalTheory.Unf.besSemi D ρ B
  obtain ⟨-, hψrat, hψconj, -⟩ := GlobalTheory.MixPer.charLaws D ψ hψ B.V B.V₀ B.A B.L ρ B.d B.o B.ζ 1
  have hx' : GlobalTheory.MixPer.embA B.d B.o h * x * (GlobalTheory.MixPer.embA B.d B.o h)⁻¹ ∈ flagN B.d := hconj x hx h
  have hpy : psiBes ψ B.d 1 (vecB B.o B.ζ) (GlobalTheory.MixPer.embA B.d B.o h * x * (GlobalTheory.MixPer.embA B.d B.o h)⁻¹) =
      psiBes ψ B.d 1 (vecB B.o B.ζ) x := hψconj x h
  have hn1 : psiBes ψ B.d 1 (vecB B.o B.ζ) x * star (psiBes ψ B.d 1 (vecB B.o B.ζ) x) = 1 := by
    have hnorm : ‖psiBes ψ B.d 1 (vecB B.o B.ζ) x‖ = 1 := by simp only [psiBes, psiE]; exact hψ.2.1 _
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]
    norm_num
  have hG : ∀ γ ∈ NFlagQ B.V B.d.e, ∀ n : flagN B.d,
      besFun ψ 1 B.d B.o B.ζ φ f h (γ * n) = besFun ψ 1 B.d B.o B.ζ φ f h n := fun γ' hγ' n => by
    have hγ'Q : (γ' : GA D B.V) ∈ GQ B.V := Subgroup.mem_subgroupOf.1 hγ'
    simp only [besFun, Subgroup.coe_mul]
    rw [psiBes_mul B.d ψ 1 _ γ'.2 n.2, hψrat _ _ hγ'Q, one_mul, mul_assoc (γ' : GA D B.V), hf _ hγ'Q]
  let y : flagN B.d := ⟨_, hx'⟩
  have hpt : ∀ n : flagN B.d, besFun ψ 1 B.d B.o B.ζ φ (rTrans x f) h n =
      psiBes ψ B.d 1 (vecB B.o B.ζ) x * besFun ψ 1 B.d B.o B.ζ φ f h (n * y) := fun n => by
    simp only [besFun, rTrans, Subgroup.coe_mul, y]
    rw [psiBes_mul B.d ψ 1 _ n.2 hx', hpy, star_mul]
    have e1 : (n : GA D B.V) * (GlobalTheory.MixPer.embA B.d B.o h * x * (GlobalTheory.MixPer.embA B.d B.o h)⁻¹) *
        GlobalTheory.MixPer.embA B.d B.o h = (n : GA D B.V) * GlobalTheory.MixPer.embA B.d B.o h * x := by group
    rw [e1]
    linear_combination (-(φ h * f ((n : GA D B.V) * GlobalTheory.MixPer.embA B.d B.o h * x) *
      star (psiBes ψ B.d 1 (vecB B.o B.ζ) (n : GA D B.V)))) * hn1
  simp_rw [hpt]
  rw [integral_const_mul, setIntegral_mul_right_N B _ hG y]

theorem per_flagN {ρ : ℕ} (B : BesLev D ρ) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1))
    (φ : GA D B.A → ℂ) (f : GA D B.V → ℂ) (hf : ∀ γ ∈ GQ B.V, ∀ g, f (γ * g) = f g)
    {x : GA D B.V} (hx : x ∈ flagN B.d) :
    B.per ψ φ (rTrans x f) = psiBes ψ B.d 1 (vecB B.o B.ζ) x * B.per ψ φ f := by
  unfold BesLev.per besPer
  simp_rw [inner_N B ψ hψ.1 φ f hf hx]
  exact integral_const_mul _ _

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isLoc_embA (p : Place D k) {n : Type} [Fintype n] [DecidableEq n] {c ρ : ℕ} (B : BesLev D ρ) (s : k)
    (FA : Frame k B.A.rank n) (F : Frame k B.V.rank (n ⊕ Fin c)) (hF : p.IsBesFrame B s FA F) {g : GL n k}
    {h : GA D B.A} (hh : p.IsLoc FA h g) : p.IsLoc F (GlobalTheory.MixPer.embA B.d B.o h) (embX c g) := by
  obtain ⟨rfl, h0, hX, hz, hY⟩ := hF
  have eA : mt B.V (B.d.emb0 (B.o.emb (h, 1))) ⬝ (B.d.j0 ⬝ B.o.jA) = B.d.j0 ⬝ B.o.jA ⬝ mt B.A h := by
    rw [cancel₂ (B.d.wittDecomp_anisotropicEmbedding_inclAnisotropic _), Matrix.mul_assoc, B.o.emb_jA, Matrix.mul_assoc]
  have eB : mt B.V (B.d.emb0 (B.o.emb (h, 1))) ⬝ (B.d.j0 ⬝ B.o.jB) = B.d.j0 ⬝ B.o.jB := by
    rw [cancel₂ (B.d.wittDecomp_anisotropicEmbedding_inclAnisotropic _), Matrix.mul_assoc, B.o.emb_jB, GlobalTheory.MixModel.mt_one, Matrix.mul_one]
  have rA : B.d.j0 ⬝ B.o.jA = rat (B.d.i₀ * B.o.iA) := (rat_mul _ _).symm
  have rB : B.d.j0 ⬝ B.o.jB = rat (B.d.i₀ * B.o.iB) := (rat_mul _ _).symm
  rw [rA] at eA
  rw [rB] at eB
  rw [GlobalTheory.MixPer.embA_apply]
  refine ⟨GlobalTheory.LocGrp.suppAt_wittLeviEmbedding B.d (GlobalTheory.LocGrp.suppAt_emb B.o hh.1),
    GlobalTheory.LocGrp.eq_embX F _ g ((rat (B.d.i₀ * B.o.iA)).map p.π * FA.β) h0 (GlobalTheory.LocGrp.intertwine p eA hh) fun j => ?_⟩
  rcases lt_trichotomy j.val ρ with hj | hj | hj
  · exact GlobalTheory.LocGrp.fix_col (GlobalTheory.LocGrp.map_fix p (B.d.wittDecomp_anisotropicEmbedding_inclX _)) _ ⟨j.val, hj⟩ (hX _ j rfl)
  · refine GlobalTheory.LocGrp.fix_vec (GlobalTheory.LocGrp.map_fix p eB) s (Witness.prH p ∘ B.ζ) fun r =>
      (hz j hj r).trans (congrArg (s * ·) ?_)
    rw [vecB, Matrix.mulVec_mulVec]
    exact RingHom.map_mulVec (Witness.prH p) _ _ r
  · exact GlobalTheory.LocGrp.fix_col (GlobalTheory.LocGrp.map_fix p (B.d.wittDecomp_anisotropicEmbedding_inclY _)) _ ⟨2 * ρ - j.val, by omega⟩
      (hY _ j (by simp only; omega))

end GlobalTheory.NormalFramePeriod

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.LocOm

theorem _root_.GlobalTheory.T.localSelfDualLattice_split_place_decomposition : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y), ∃ Λ : AddSubgroup (WO S T), (∀ u ∈ Λ, ∀ u' ∈ Λ, ψ (symplO S T u u') = 1) ∧ (∀ y, IsHalf p.e y → y ∉ Λ → ∃ l ∈ Λ, IsHalf (cA D p.e) l ∧ ψ (symplO S T l y) ≠ 1) ∧ (∀ y, IsHalf (cA D p.e) y → y ∉ Λ → ∃ l ∈ Λ, IsHalf p.e l ∧ ψ (symplO S T l y) ≠ 1) ∧ (∀ x : Matrix Y Y' k, p.up FS FT x ∈ Λ ↔ ∀ r q, x r q ∈ 𝒪[k]) ∧ (∀ u ∈ Λ, IsHalf p.e u → ∃ x : Matrix Y Y' k, (∀ r q, x r q ∈ 𝒪[k]) ∧ u = p.up FS FT x) ∧ (∀ u ∈ Λ, IsHalf (cA D p.e) u → ∀ t : Matrix Y Y' k, (∀ r q, t r q ∈ 𝒪[k]) → ψ (symplO S T (p.up FS FT t) u) = 1) := by
  first | exact @GlobalTheory.SplitSelfDual.selfDual_lattice_split | exact GlobalTheory.SplitSelfDual.selfDual_lattice_split | (intros; apply GlobalTheory.SplitSelfDual.selfDual_lattice_split <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.LocOm

theorem _root_.GlobalTheory.T.splitLocalComponents_one_mul_inv : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (V : HSp D) (Z : Type) [Fintype Z] [DecidableEq Z] (F : Frame k V.rank Z), p.IsLoc F 1 1 ∧ (∀ (g g' : GA D V) (gk gk' : GL Z k), p.IsLoc F g gk → p.IsLoc F g' gk' → p.IsLoc F (g * g') (gk * gk')) ∧ ∀ (g : GA D V) (gk : GL Z k), p.IsLoc F g gk → p.IsLoc F g⁻¹ gk⁻¹ := by
  first | exact @GlobalTheory.LocOm.isLoc_one_mul_inv | exact GlobalTheory.LocOm.isLoc_one_mul_inv | (intros; apply GlobalTheory.LocOm.isLoc_one_mul_inv <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.LocOm

theorem _root_.GlobalTheory.T.conj_splitLocalModel_by_supported_pair : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : Om S T), IsWeilDatumO ψ S T χS χT ω → ∀ (μS μT : kˣ →* ℂˣ) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (Tm : SB (Matrix Y Y' k) →ₗ[ℂ] (WO S T → ℂ)), p.IsModel ψ FS FT Tm → ∀ (g : GA D S) (gk : GL Y' k) (h : GA D T) (hk : GL Y k), p.IsLoc FS g gk → p.IsLoc FT h hk → ∃ T₂ : SB (Matrix Y Y' k) →ₗ[ℂ] (WO S T → ℂ), p.IsModel ψ FS FT T₂ ∧ ∀ Φ Φ' : SB (Matrix Y Y' k), Φ'.1 = (((μS * μT⁻¹) (Matrix.GeneralLinearGroup.det gk) : ℂˣ) : ℂ) • om μS⁻¹ gk hk Φ.1 → T₂ Φ = ω (g⁻¹, h⁻¹) (Tm Φ') := by
  first | exact @GlobalTheory.LocTwist.conj_isModel | exact GlobalTheory.LocTwist.conj_isModel | (intros; apply GlobalTheory.LocTwist.conj_isModel <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.LocOm

theorem _root_.GlobalTheory.T.exists_splitLocal_supported_scalar_component : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (V : HSp D) (Z : Type) [Fintype Z] [DecidableEq Z] (F : Frame k V.rank Z) (c : kˣ) (zk : GL Z k), (zk : Matrix Z Z k) = (c : k) • (1 : Matrix Z Z k) → ∃ z : GA D V, p.IsLoc F z zk := by
  first | exact @GlobalTheory.LocScalar.exists_isLoc_scalar | exact GlobalTheory.LocScalar.exists_isLoc_scalar | (intros; apply GlobalTheory.LocScalar.exists_isLoc_scalar <;> assumption)
end

section

open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW
open scoped ContDiff

namespace GlobalTheory.SchLine

theorem sch_hasDerivAt_line : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A B : HSp D) (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ f, IsThetaFunO ψ (dblSp A) B f → ∀ M : ℝ →+ Mx D B.rank A.rank, Continuous M → (∀ t, (M t).map (finPart D) = 0) → ∃ f', IsThetaFunO ψ (dblSp A) B f' ∧ ∀ x, HasDerivAt (fun t : ℝ => sch ψ A B ν 𝓨 f (x + M t)) (sch ψ A B ν 𝓨 f' x) 0 := by
  intro D ψ hψ A B ν 𝓨 hν f hf M hM hMf
  obtain ⟨θ, hθ⟩ := GlobalTheory.DualPairCompare.exists_infFam D
  let v : GlobalTheory.Unf.VolM D B.rank A.rank := ⟨ν, 𝓨, hν⟩
  let L : ℝ →+ WO (dblSp A) B := ((dblDec A).extX B).comp M
  have hLc : Continuous L := (continuous_id.matrix_mul continuous_const).comp hM
  have hLf : ∀ t, (L t).map (finPart D) = 0 := by
    intro t
    show (((dblDec A).extX B) (M t)).map (finPart D) = 0
    rw [HypDec.extX_apply, Matrix.map_mul, hMf t, Matrix.zero_mul]
  obtain ⟨_, hT⟩ := GlobalTheory.HeisTaylor.heisO_taylor D ψ hψ θ hθ (dblSp A) B 0 f hf
  obtain ⟨hf', hlim⟩ := hT L hLc hLf
  refine ⟨_, hf', fun x => ?_⟩
  set f' := fun p => deriv (fun t : ℝ => heisO ψ (dblSp A) B (L t) f p) 0 with hf'def
  obtain ⟨C, hC⟩ := GlobalTheory.Unf.mixS_decay D ψ hψ θ hθ (dblSp A) (zeroSp D) B A.rank (dblDec A) v 0
  have hS := (GlobalTheory.HeisMixSource.heis_mixS D ψ hψ (dblSp A) (zeroSp D) B A.rank (dblDec A) v f hf).1
  have hth : ∀ t, IsThetaFunO ψ (dblSp A) B (heisO ψ (dblSp A) B (L t) f) := fun t =>
    GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf _
  have lin := GlobalTheory.StdUnn.sch_linear D ψ hψ A B ν 𝓨 hν

  have htr : ∀ t : ℝ, sch ψ A B ν 𝓨 f (x + M t) = sch ψ A B ν 𝓨 (heisO ψ (dblSp A) B (L t) f) x := by
    intro t
    exact (congrFun (hS x (M t)) 0).symm

  have key : ∀ t : ℝ, IsThetaFunO ψ (dblSp A) B ((t⁻¹ : ℂ) • (heisO ψ (dblSp A) B (L t) f - f) - f') ∧
      sch ψ A B ν 𝓨 ((t⁻¹ : ℂ) • (heisO ψ (dblSp A) B (L t) f - f) - f') x =
        (t⁻¹ : ℂ) * (sch ψ A B ν 𝓨 (heisO ψ (dblSp A) B (L t) f) x - sch ψ A B ν 𝓨 f x) - sch ψ A B ν 𝓨 f' x := by
    intro t
    have e : (t⁻¹ : ℂ) • (heisO ψ (dblSp A) B (L t) f - f) - f' =
        ((t⁻¹ : ℂ) • heisO ψ (dblSp A) B (L t) f + (-(t⁻¹ : ℂ)) • f) + (-1 : ℂ) • f' := by
      funext p
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have h1 := lin _ _ (hth t) hf (t⁻¹ : ℂ)
    have h2 := lin _ _ hf hf (-(t⁻¹ : ℂ))
    have ha := GlobalTheory.OrientedHeis.theta_smul (t⁻¹ : ℂ) (hth t)
    have hb := GlobalTheory.OrientedHeis.theta_smul (-(t⁻¹ : ℂ)) hf
    have hc := GlobalTheory.OrientedHeis.theta_smul (-1 : ℂ) hf'
    have hab := GlobalTheory.OrientedHeis.theta_add ha hb
    rw [e]
    refine ⟨GlobalTheory.OrientedHeis.theta_add hab hc, ?_⟩
    rw [(lin _ _ hab hc 1).2.2.1, (lin _ _ ha hb 1).2.2.1, (lin _ _ (hth t) hf (t⁻¹ : ℂ)).2.2.2,
      (lin _ _ hf hf (-(t⁻¹ : ℂ))).2.2.2, (lin _ _ hf' hf' (-1 : ℂ)).2.2.2]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hasDerivAt_iff_tendsto_slope_zero, tendsto_iff_edist_tendsto_0]
  have hup : Filter.Tendsto (fun t : ℝ => (C : ℝ≥0∞) * GlobalTheory.Unf.supSob ψ θ 0
      ((t⁻¹ : ℂ) • (heisO ψ (dblSp A) B (L t) f - f) - f')) (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hlim (Or.inr ENNReal.coe_ne_top)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun _ => by simp) (fun t => ?_)
  have hb := hC _ (key t).1 x 0
  rw [pow_zero, ENNReal.ofReal_one, mul_one] at hb
  have e2 : t⁻¹ • (sch ψ A B ν 𝓨 f (x + M (0 + t)) - sch ψ A B ν 𝓨 f (x + M 0)) =
      (t⁻¹ : ℂ) * (sch ψ A B ν 𝓨 (heisO ψ (dblSp A) B (L t) f) x - sch ψ A B ν 𝓨 f x) := by
    rw [zero_add, htr t, map_zero, add_zero, Complex.real_smul, Complex.ofReal_inv]
  simp only
  rw [e2, edist_eq_enorm_sub, ← (key t).2]
  exact hb

end GlobalTheory.SchLine
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section



namespace GlobalTheory.SplitIntComp

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

open GlobalTheory.FinPl GlobalTheory.FinPl.FrameLat

theorem eq_sec_add_csec (q : SplitPt D k) {a : AE D} (ha : a ∈ idAt D (· = q.v)) :
    a = q.sec (q.pr a) + cA D (q.sec (q.pr (cA D a))) := by
  have h := (idem_iff q a).1 ha
  rw [q.sec_pr, q.sec_pr, map_mul, cA_cA]
  conv_lhs => rw [← h]
  ring

theorem mem_intAt_iff (q : SplitPt D k) {a : AE D} (ha : a ∈ idAt D (· = q.v)) :
    a ∈ intAt D (· = q.v) ↔ q.pr a ∈ 𝒪[k] ∧ q.pr (cA D a) ∈ 𝒪[k] := by
  constructor
  · intro h
    refine ⟨(q.int_iff _).2 ?_, (q.int_iff _).2 ?_⟩
    · rw [q.sec_pr, RingHom.map_mul]; exact mul_mem_intAE (e_mem_intAt q).2 h.2
    · rw [q.sec_pr, RingHom.map_mul]; exact mul_mem_intAE (e_mem_intAt q).2 ((cA_int_iff a).2 h.2)
  · rintro ⟨h1, h2⟩
    refine ⟨ha, ?_⟩
    rw [eq_sec_add_csec q ha, RingHom.map_add (f := _)]
    exact add_mem ((q.int_iff _).1 h1) ((cA_int_iff _).2 ((q.int_iff _).1 h2))

theorem val_xi (q : SplitPt D k) (h : q.UnitAA) : valuation k ((ofSplit q).xi) = 1 := by
  have he := e_mem_intAt q
  have hpe : q.pr q.e = 1 := by rw [← sec_one q, q.pr_sec]
  have h1 := ((mem_intAt_iff q (h.1 q.e he).1.1).1 (h.1 q.e he).1).1
  have h2 := ((mem_intAt_iff q (h.1 q.e he).2.1).1 (h.1 q.e he).2).1
  rw [map_mul, hpe, mul_one] at h1 h2
  have hne : D.host.xi0 ≠ 0 := GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero
  have hprod : q.pr (incA D D.host.xi0⁻¹) * q.pr (incA D D.host.xi0) = 1 := by
    rw [← map_mul, ← map_mul, inv_mul_cancel₀ hne, map_one, map_one]
  change valuation k (q.pr (incA D D.host.xi0)) = 1
  have v1 := (Valuation.mem_integer_iff _ _).1 h1
  have v2 := (Valuation.mem_integer_iff _ _).1 h2
  have v3 := congrArg (valuation k) hprod
  rw [map_mul, map_one] at v3
  refine le_antisymm v1 ?_
  by_contra hlt
  push_neg at hlt
  have := mul_lt_mul_of_le_of_lt_of_nonneg_of_pos v2 hlt zero_le' zero_lt_one
  rw [v3, mul_one] at this
  exact lt_irrefl _ this

end GlobalTheory.SplitIntComp
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.StepData NumberField
open scoped Classical

theorem _root_.GlobalTheory.T.isSchwartzBruhatHalf_splitPlace_product : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), Submodule.IsFullLattice D.host.E ΛS → Submodule.IsFullLattice D.host.E ΛT → ∀ e : AE D, e * e = e → q.e * e = q.e → ∀ Ω : WO S T → ℂ, IsSBHalf (e - q.e) (latO S T ΛS ΛT fun _ => True) Ω → ∀ Φ : SB (Matrix Y Y' k), IsSBHalf e (latO S T ΛS ΛT fun _ => True) (fun x : WO S T => if IsHalf e x then Φ.1 ((ofSplit q).down FS FT x) * Ω ((1 - q.e) • x) else 0) := by
  intro D k _ _ _ _ q Y Y' _ _ _ _ S T FS FT ΛS ΛT hS hT
  letI := hS
  letI := hT
  exact GlobalTheory.SplitSBProd.isSBHalf_splitProd D k q Y Y' S T FS FT ΛS ΛT
    inferInstance inferInstance
end
