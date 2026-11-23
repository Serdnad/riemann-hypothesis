module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSplitIdempotentsOfRelTraceOneModTwo
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle067
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle141
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle142
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle156
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle319
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle340
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle192
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle164
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle193
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle196
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Mathlib.Topology.UniformSpace.Uniformizable
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.VolumeFlatSection
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero

@[expose] public section

section

noncomputable section

open MeasureTheory ValuativeRel Matrix IsLocalRing GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (cosetInd mainDatum InDual Lifts)
open GlobalTheory.FinPl.Comm (fpair)

namespace GlobalTheory.FinPl.Comm.DualCosets

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]

theorem inDual_add {L : Submodule 𝒪[k] (n → k)} {η ξ : n → k} (h : InDual L η) (h' : InDual L ξ) :
    InDual L (η + ξ) := by
  intro y hy
  rw [add_dotProduct]
  exact add_mem (h y hy) (h' y hy)

theorem inDual_sub {L : Submodule 𝒪[k] (n → k)} {η ξ : n → k} (h : InDual L η) (h' : InDual L ξ) :
    InDual L (η - ξ) := by
  intro y hy
  rw [sub_dotProduct]
  exact sub_mem (h y hy) (h' y hy)

theorem inDual_smul {L : Submodule 𝒪[k] (n → k)} {η : n → k} (h : InDual L η) (s : 𝒪[k]) :
    InDual L (s • η) := by
  intro y hy
  rw [smul_dotProduct, Algebra.smul_def]
  exact mul_mem s.2 (h y hy)

theorem isLocallyConstant_of_periodic (L : Submodule 𝒪[k] (n → k)) [L.IsFullLattice k] {g : (n → k) → ℂ}
    (hg : ∀ η ξ, InDual L ξ → g (η + ξ) = g η) : IsLocallyConstant g := by
  have hD := (dual_compact_open L).2
  refine (IsLocallyConstant.iff_exists_open g).2 fun x => ?_
  refine ⟨{η | InDual L (η - x)}, hD.preimage (continuous_sub_right x), ?_, fun η hη => ?_⟩
  · intro y _
    simp
  · have h := hg x (η - x) hη
    rwa [add_sub_cancel] at h

private theorem secondCountableTopology_localField' (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : SecondCountableTopology K := by
  letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  haveI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  obtain ⟨r⟩ := (IsRankLeOne.nonempty : Nonempty (ValuativeRel.RankLeOneStruct K))
  letI : (Valued.v (R := K) (Γ₀ := ValueGroupWithZero K)).RankOne :=
    { hom' := r.emb.comp MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := r.strictMono.comp MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  letI : NontriviallyNormedField K := Valued.toNontriviallyNormedField K (ValueGroupWithZero K)
  haveI : ProperSpace K := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K
  exact secondCountable_of_proper

variable [MeasurableSpace k] [BorelSpace k]

theorem integrable_of_periodic (μ : Measure (n → k)) [μ.IsAddHaarMeasure] (q : Unif k)
    (L : Submodule 𝒪[k] (n → k)) [L.IsFullLattice k] {g : (n → k) → ℂ}
    (hg : ∀ η ξ, InDual L ξ → g (η + ξ) = g η) (hs : ∀ η, g η ≠ 0 → InDual L (q.1 • η)) : Integrable g μ := by
  haveI := secondCountableTopology_localField' k
  have hlc := isLocallyConstant_of_periodic L hg
  have hK : IsCompact {η : n → k | InDual L (q.1 • η)} := by
    have h2 : {η : n → k | InDual L (q.1 • η)} =
        (Homeomorph.smulOfNeZero ((q.1 : 𝒪[k]) : k) q.ne_zero) ⁻¹' {η | InDual L η} := by
      ext η
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Homeomorph.smulOfNeZero_apply, Algebra.smul_def]
      rfl
    rw [h2, Homeomorph.isCompact_preimage]
    exact (dual_compact_open L).1
  have hcs : HasCompactSupport g := HasCompactSupport.intro hK fun η hη => by
    by_contra h
    exact hη (hs η h)
  exact hlc.continuous.integrable_of_hasCompactSupport hcs

end GlobalTheory.FinPl.Comm.DualCosets

namespace GlobalTheory.FinPl.Comm.DualCosets

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]

theorem dualInd_add (L : Submodule 𝒪[k] (n → k)) (η ξ : n → k) (hξ : InDual L ξ) :
    dualInd L (η + ξ) = dualInd L η := by
  unfold dualInd
  by_cases h : InDual L η
  · rw [if_pos (inDual_add h hξ), if_pos h]
  · rw [if_neg h, if_neg]
    intro h'
    apply h
    simpa using inDual_sub h' hξ

theorem dualInd_supp (q : Unif k) (L : Submodule 𝒪[k] (n → k)) (η : n → k) (h : dualInd L η ≠ 0) :
    InDual L (q.1 • η) := by
  unfold dualInd at h
  by_cases hd : InDual L η
  · exact inDual_smul hd q.1
  · exact absurd (if_neg hd) h

theorem cosetInd_add (q : Unif k) (L : Submodule 𝒪[k] (n → k)) (f : Module.Dual 𝓀[k] (Red L)) (η ξ : n → k)
    (hξ : InDual L ξ) : cosetInd q L f (η + ξ) = cosetInd q L f η := by
  unfold cosetInd
  have e : (∃ F : n → k, Lifts L F f ∧ InDual L (η + ξ - q.inv • F)) ↔
      ∃ F : n → k, Lifts L F f ∧ InDual L (η - q.inv • F) := by
    constructor
    · rintro ⟨F, hF, hd⟩
      refine ⟨F, hF, ?_⟩
      have h := inDual_sub hd hξ
      rwa [show η + ξ - q.inv • F - ξ = η - q.inv • F by abel] at h
    · rintro ⟨F, hF, hd⟩
      refine ⟨F, hF, ?_⟩
      have h := inDual_add hd hξ
      rwa [show η - q.inv • F + ξ = η + ξ - q.inv • F by abel] at h
  by_cases h : ∃ F : n → k, Lifts L F f ∧ InDual L (η - q.inv • F)
  · rw [if_pos (e.2 h), if_pos h]
  · rw [if_neg (fun h' => h (e.1 h')), if_neg h]

theorem inDual_of_lifts {L : Submodule 𝒪[k] (n → k)} {F : n → k} {f : Module.Dual 𝓀[k] (Red L)} (h : Lifts L F f) :
    InDual L F := by
  intro y hy
  obtain ⟨s, hs, -⟩ := h ⟨y, hy⟩
  rw [← hs]
  exact s.2

theorem cosetInd_supp (q : Unif k) (L : Submodule 𝒪[k] (n → k)) (f : Module.Dual 𝓀[k] (Red L)) (η : n → k)
    (h : cosetInd q L f η ≠ 0) : InDual L (q.1 • η) := by
  unfold cosetInd at h
  by_cases hc : ∃ F : n → k, Lifts L F f ∧ InDual L (η - q.inv • F)
  · obtain ⟨F, hF, hd⟩ := hc
    have hq1 : q.1 • q.inv = 1 := by
      rw [Algebra.smul_def, Unif.inv]
      exact mul_inv_cancel₀ q.ne_zero
    have hq : q.1 • (q.inv • F) = F := by
      rw [← smul_assoc, hq1, one_smul]
    have h3 : q.1 • η = q.1 • (η - q.inv • F) + F := by
      rw [smul_sub, hq, sub_add_cancel]
    rw [h3]
    exact inDual_add (inDual_smul hd q.1) (inDual_of_lifts hF)
  · exact absurd (if_neg hc) h

theorem inner_add (χ : AddChar k Circle) (hχ : HasConductor χ 1) {e : k} (he : e = 1 ∨ e = -1)
    [MeasurableSpace k] (μ : Measure (n → k)) (L : Submodule 𝒪[k] (n → k)) {a : (n → k) → ℂ}
    (ha : ∀ y, y ∉ L → a y = 0) (η ξ : n → k) (hξ : InDual L ξ) :
    ∫ y, a y * (χ (e * ((η + ξ) ⬝ᵥ y)) : ℂ) ∂μ = ∫ y, a y * (χ (e * (η ⬝ᵥ y)) : ℂ) ∂μ := by
  congr 1
  funext y
  by_cases hy : y ∈ L
  · have hm : e * (ξ ⬝ᵥ y) ∈ 𝒪[k] := by
      rcases he with rfl | rfl
      · simpa using hξ y hy
      · simpa using neg_mem (hξ y hy)
    have h1 : χ (e * (ξ ⬝ᵥ y)) = 1 := apply_int_eq_one hχ ⟨_, hm⟩
    rw [add_dotProduct, mul_add, AddChar.map_add_eq_mul, h1, mul_one]
  · rw [ha y hy, zero_mul, zero_mul]

end GlobalTheory.FinPl.Comm.DualCosets

namespace GlobalTheory.FinPl.Comm.DualCosets

theorem fpair_charInd_dualInd_add_cosets : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (q : Unif k) (χ : AddChar k Circle) (hχ : HasConductor χ 1) (e : k), (e = 1 ∨ e = -1) → ∀ (μ : Measure (n → k)) [μ.IsAddHaarMeasure] (Q : Pair k n), fpair χ e μ (charInd (resChar χ hχ q) Q) (dualInd Q.lat + ∑ Q'' ∈ withLat Q.lat, cosetInd q Q''.lat Q''.red) = fpair χ e μ (vecInd Q.lat) (dualInd Q.lat) := by
  intro k _ _ _ _ _ _ n _ _ q χ hχ e he μ _ Q
  have ha : ∀ y, y ∉ Q.lat → charInd (resChar χ hχ q) Q y = 0 := fun y hy => by
    simp [charInd, vecInd, hy]
  have hF : ∀ (L : Submodule 𝒪[k] (n → k)), L = Q.lat → ∀ η ξ, InDual L ξ →
      (∫ y, charInd (resChar χ hχ q) Q y * (χ (e * ((η + ξ) ⬝ᵥ y)) : ℂ) ∂μ) =
        ∫ y, charInd (resChar χ hχ q) Q y * (χ (e * (η ⬝ᵥ y)) : ℂ) ∂μ := by
    rintro L rfl η ξ hξ
    exact inner_add χ hχ he μ Q.lat ha η ξ hξ
  have hint1 : Integrable (fun η => (∫ y, charInd (resChar χ hχ q) Q y * (χ (e * (η ⬝ᵥ y)) : ℂ) ∂μ) *
      dualInd Q.lat η) μ := by
    refine integrable_of_periodic μ q Q.lat (fun η ξ hξ => ?_) (fun η h => ?_)
    · simp only [hF Q.lat rfl η ξ hξ, dualInd_add Q.lat η ξ hξ]
    · exact dualInd_supp q Q.lat η (right_ne_zero_of_mul h)
  have hint2 : ∀ Q'' ∈ withLat Q.lat, Integrable (fun η => (∫ y, charInd (resChar χ hχ q) Q y *
      (χ (e * (η ⬝ᵥ y)) : ℂ) ∂μ) * cosetInd q Q''.lat Q''.red η) μ := by
    intro Q'' hQ''
    have hl : Q''.lat = Q.lat := mem_withLat.1 hQ''
    refine integrable_of_periodic μ q Q''.lat (fun η ξ hξ => ?_) (fun η h => ?_)
    · simp only [hF Q''.lat hl η ξ hξ, cosetInd_add q Q''.lat Q''.red η ξ hξ]
    · exact cosetInd_supp q Q''.lat Q''.red η (right_ne_zero_of_mul h)
  have key : fpair χ e μ (charInd (resChar χ hχ q) Q)
      (dualInd Q.lat + ∑ Q'' ∈ withLat Q.lat, cosetInd q Q''.lat Q''.red) =
      fpair χ e μ (charInd (resChar χ hχ q) Q) (dualInd Q.lat) +
        ∑ Q'' ∈ withLat Q.lat, fpair χ e μ (charInd (resChar χ hχ q) Q) (cosetInd q Q''.lat Q''.red) := by
    simp only [fpair]
    rw [← integral_finsetSum _ hint2, ← integral_add hint1 (integrable_finsetSum _ hint2)]
    congr 1
    funext η
    simp [mul_add, Finset.mul_sum]
  obtain ⟨ε, hε⟩ : ∃ ε : 𝓀[k]ˣ, (e = 1 ∧ ε = 1) ∨ (e = -1 ∧ ε = -1) := by
    rcases he with h | h
    · exact ⟨1, Or.inl ⟨h, rfl⟩⟩
    · exact ⟨-1, Or.inr ⟨h, rfl⟩⟩
  rw [key, GlobalTheory.T.fourierPairing_pairCharIndicator_dualLatticeIndicator_zero k n q χ hχ e he μ Q, zero_add, Finset.sum_eq_single (ε • Q)]
  · exact (GlobalTheory.T.fourierPairing_pairCharIndicator_cosetIndicator k n q χ hχ e ε hε μ Q (ε • Q) (Pair.dia_lat ε Q)).1 rfl
  · intro Q'' hQ'' hne
    exact (GlobalTheory.T.fourierPairing_pairCharIndicator_cosetIndicator k n q χ hχ e ε hε μ Q Q'' (mem_withLat.1 hQ'')).2 hne
  · intro h
    exact absurd (mem_withLat.2 (Pair.dia_lat ε Q)) h

end GlobalTheory.FinPl.Comm.DualCosets
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section




namespace GlobalTheory.LevelPlaces

open GlobalTheory.IdemModTwo GlobalTheory.SplitIdem

variable {D : D7}

theorem splitAt_of {v : HeightOneSpectrum (𝓞 D.host.F)} {e : AE D} {ε : AF D.host.F} (he : IsSplitIdem D e)
    (hε : IsPlaceIdem D v ε) (h : e + cA D e = algebraMap (AF D.host.F) (AE D) ε) : SplitAt D v e := by
  obtain ⟨α, rfl, h3, h4⟩ := hε
  have : α = singleV D.host.F v 1 := _root_.GlobalTheory.SplitIdem.af_ext _ fun w => by
    by_cases hw : w = v
    · subst hw; rw [h3, evalV_singleV_same]
    · rw [h4 w hw, evalV_singleV_ne _ v _ hw]
  subst this
  exact ⟨he.1, he.2.1, h⟩

theorem ne_zero_of_isIdemAt {e : AE D} {P : HeightOneSpectrum (𝓞 D.host.E)} (hP : Formalism.L2.NTheta.IsIdemAt e P) : e ≠ 0 := by
  rintro rfl
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
  exact ((hP.2 x hx0).1 hx) (by rw [zero_mul, map_zero]; exact zero_mem _)

end GlobalTheory.LevelPlaces
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl IsBase onHalf phiQ rdQ)

namespace GlobalTheory.SBTwist

theorem viaRed_mem_SB {D : D7} {v : FinPl D} {k : Type} [CommRing k] {a b : ℕ}
    (r : v.adicCompletionIntegers D.host.F →+* k)
    (hr : ∀ a : v.adicCompletionIntegers D.host.F, r a = 0 ↔ Valued.v (a : Fv D.host.F v) < 1)
    (ω : Matrix (Fin b) (Fin a) k → ℂ) :
    GlobalTheory.StepVec.viaRed r ω ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin b) (Fin a) (Fv D.host.F v)) := by
  classical
  constructor
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have hU : ∀ᶠ y in nhds x, ∀ i j, Valued.v (y i j - x i j) < 1 := by
      rw [Filter.eventually_all]; intro i
      rw [Filter.eventually_all]; intro j
      have hc : Continuous fun y : Matrix (Fin b) (Fin a) (Fv D.host.F v) => y i j :=
        continuous_id.matrix_elem i j
      have hn : {z : Fv D.host.F v | Valued.v (z - x i j) < 1} ∈ nhds (x i j) :=
        Valued.mem_nhds.2 ⟨1, fun z hz => by simpa using hz⟩
      exact hc.continuousAt.preimage_mem_nhds hn
    filter_upwards [hU] with y hy
    have hint : ∀ i j, y i j ∈ v.adicCompletionIntegers D.host.F ↔ x i j ∈ v.adicCompletionIntegers D.host.F := by
      intro i j
      simp only [HeightOneSpectrum.mem_adicCompletionIntegers]
      have h1 := hy i j
      constructor
      · intro h
        have : x i j = y i j - (y i j - x i j) := by ring
        rw [this]
        refine le_trans (Valuation.map_sub _ _ _) (max_le h (le_of_lt h1))
      · intro h
        have : y i j = (y i j - x i j) + x i j := by ring
        rw [this]
        exact le_trans (Valuation.map_add _ _ _) (max_le (le_of_lt h1) h)
    unfold GlobalTheory.StepVec.viaRed
    by_cases hx : ∀ i j, x i j ∈ v.adicCompletionIntegers D.host.F
    · have hy' : ∀ i j, y i j ∈ v.adicCompletionIntegers D.host.F := fun i j => (hint i j).2 (hx i j)
      rw [dite_eq_left hy', dite_eq_left hx]
      congr 1
      ext i j
      simp only [Matrix.of_apply]
      have hs : (⟨y i j, hy' i j⟩ : v.adicCompletionIntegers D.host.F) - ⟨x i j, hx i j⟩ =
          ⟨y i j - x i j, Subring.sub_mem _ (hy' i j) (hx i j)⟩ := rfl
      have h0 := (hr ⟨y i j - x i j, Subring.sub_mem _ (hy' i j) (hx i j)⟩).2 (hy i j)
      rw [← hs, map_sub, sub_eq_zero] at h0
      exact h0
    · have hy' : ¬ ∀ i j, y i j ∈ v.adicCompletionIntegers D.host.F := fun h => hx fun i j => (hint i j).1 (h i j)
      rw [dif_neg hy', dif_neg hx]
  · haveI := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers D.host.F v
    have hK : IsCompact {Y : Matrix (Fin b) (Fin a) (Fv D.host.F v) | ∀ i j, Y i j ∈ v.adicCompletionIntegers D.host.F} := by
      have he : {Y : Matrix (Fin b) (Fin a) (Fv D.host.F v) | ∀ i j, Y i j ∈ v.adicCompletionIntegers D.host.F} =
          Set.pi Set.univ (fun _ : Fin b => Set.pi Set.univ (fun _ : Fin a => (v.adicCompletionIntegers D.host.F : Set (Fv D.host.F v)))) := by
        ext Y
        exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩
      rw [he]
      exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_iff_compactSpace.2 ‹_›
    refine HasCompactSupport.intro hK ?_
    intro Y hY
    have hY' : ¬ ∀ i j, Y i j ∈ v.adicCompletionIntegers D.host.F := hY
    unfold GlobalTheory.StepVec.viaRed
    exact dif_neg hY'

theorem phiQ_mem_SB : ∀ (D : D7) (PP : Pl D.host.E) (v : FinPl D) (φ : SplitProj D v), IsProjAt φ PP → ∀ (a b r : ℕ) (ξ : (kP PP)ˣ →* ℂˣ) (mu : (Fv D.host.F v)ˣ →* ℂˣ), LiftsChar φ PP mu ξ → phiQ (a := a) (b := b) v r mu ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin b) (Fin a) (Fv D.host.F v)) := by
  intro D PP v φ hφ a b r ξ mu hmu
  obtain ⟨⟨rr, hrr⟩, -⟩ := GlobalTheory.PlaceRed.red_dict D v φ PP hφ
  have hred : GlobalTheory.StepVec.IsRedMap φ PP rr := hrr
  have hmu' : LiftsChar φ PP mu ξ⁻¹⁻¹ := by rwa [inv_inv]
  have heq : phiQ (a := a) (b := b) v r mu = GlobalTheory.StepVec.viaRed rr (GlobalTheory.StepVec.qLoc r PP ξ⁻¹) :=
    funext fun Y => GlobalTheory.StepVec.phiQ_eq_viaRed_qLoc D v φ PP rr hred a b r mu ξ⁻¹ hmu' Y
  rw [heq]
  exact viaRed_mem_SB rr hred.2.1 _

end GlobalTheory.SBTwist
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.LFun.StarParam

open GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.FinZeta

theorem isParamVec_of_map {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)}
    {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} {h : w.under (𝓞 F) = v}
    {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    {ρ : Representation ℂ (GLoc σ J v) X} {ρ' : Representation ℂ (GLoc σ J v) Y} (f : X →ₗ[ℂ] Y)
    (hf : ∀ g y, f (ρ g y) = ρ' g (f y)) (hi : Function.Injective f) {x : X} {B : Multiset ℂˣ}
    (hx : IsParamVec σ J L h ρ' (f x) B) : IsParamVec σ J L h ρ x B := by
  rcases hx with ⟨hv, e, he, hx⟩ | ⟨hw, c, ϖ, e, α, hU, he, hx, hB⟩
  · exact Or.inl ⟨hv, e, he, IsSatVecGL.of_map f (fun g y => hf _ y) hi hx⟩
  · exact Or.inr ⟨hw, c, ϖ, e, α, hU, he, IsSatVecU.of_map hU f (fun g y => hf _ y) hi hx, hB⟩

theorem param_star (D : D7) (V : HSp D) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) :
    ∀ f ∈ GlobalTheory.FinZeta.bddAut V, ∀ B : GlobalTheory.LFun.Fam D.host.E, GlobalTheory.LFun.IsParamFunV V S f B →
    ∀ w ∉ GlobalTheory.LFun.above D.host.E (S : Set (HeightOneSpectrum (𝓞 D.host.F))),
      (∀ w' : HeightOneSpectrum (𝓞 D.host.E), w'.under (𝓞 D.host.F) = w.under (𝓞 D.host.F) → w ≠ w' →
        B w' = (B w).map star) ∧
      (¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (w.under (𝓞 D.host.F)) → (B w).map star = B w) := by
  intro f hf B hB w hw
  have hcm := GlobalTheory.AdelicU.isCMExt_host D
  have hJ := GlobalTheory.Mem.VolExists.isHermND D.sp.cm V
  have hv : w.under (𝓞 D.host.F) ∉ S := hw
  have hd := SelfDual.isSelfDualAt_frameLat D V (w.under (𝓞 D.host.F))
  have hun := (GlobalTheory.T.boundedAutomorphicRightTranslation_unitarisable_bounded D V).1
  have hloc : GlobalTheory.LGrp.IsUnitarisable ((bddRep V).comp (embV V (w.under (𝓞 D.host.F)))) := by
    obtain ⟨b, b1, b2, b3⟩ := hun
    exact ⟨b, b1, b2, fun g => b3 _⟩
  have hpar : ∀ (u : HeightOneSpectrum (𝓞 D.host.E)) (h : u.under (𝓞 D.host.F) = w.under (𝓞 D.host.F)),
      IsParamVec D.sp.cm.sig V.gram (frameLat V) h ((bddRep V).comp (embV V (w.under (𝓞 D.host.F))))
        (⟨f, hf⟩ : bddAut V) (B u) :=
    fun u h => isParamVec_of_map (bddAut V).subtype (fun _ _ => rfl) Subtype.val_injective
      (hB _ hv u h)
  refine ⟨fun w' h' hne => ?_, fun hns => ?_⟩
  · have hB' : B w' = (B w).map (·⁻¹) :=
      ConjPlace.eq_map_inv_of_isParamVec hcm hJ hd hne (hpar w rfl) (hpar w' h')
    rcases hpar w rfl with ⟨-, e, he, hsat⟩ | ⟨hi, -⟩
    · rw [hB', GlobalTheory.T.satakeParameterGL_star_eq_inv_of_unitarisable _ w _ _ _ _ (B w) (hloc.imp fun _ hb => ⟨hb.1, hb.2.1, fun g => hb.2.2 (e.symm g)⟩) hsat]
    · exact absurd (ConjPlace.isSplit_of_ne hne rfl h') (not_isSplit_of_isInertAt hi)
  · rcases hpar w rfl with ⟨hs, -⟩ | ⟨-, c, ϖ, e, α, hUI, he, hsat, hBw⟩
    · exact absurd hs hns
    · rw [hBw]
      have := bcParam_eq_of_satU_eq (α := fun i => star (α i)) hUI
        (GlobalTheory.T.unitarySatakeTransform_star_parameter_eq_of_unitarisable _ ϖ c _ _ hUI _ _ _ α (hloc.imp fun _ hb => ⟨hb.1, hb.2.1, fun g => hb.2.2 (e.symm g)⟩) hsat)
      conv_rhs => rw [← this]
      simp [GlobalTheory.LGrp.bcParam, star_inv, Function.comp_def]

end GlobalTheory.LFun.StarParam
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP


theorem _root_.GlobalTheory.T.siegelEisenstein_spherical_moderateGrowth_real_point : GlobalTheory.Published.SiegelEisensteinContinuation → ∀ (D : D7) (V : HSp D), 0 < V.rank → ∀ a : GL (Fin V.rank) (AE D), IsMaj V a → HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a) → ∀ σ : ℝ, (V.rank : ℝ) / 2 < σ → GlobalTheory.Grow.ModGrowth (dblSp V) (GlobalTheory.Eis.eis V (GlobalTheory.Eis.sph V a (σ : ℂ))) := by
  first | exact @GlobalTheory.Eis.modGrowth_eis_sph | exact GlobalTheory.Eis.modGrowth_eis_sph | (intros; apply GlobalTheory.Eis.modGrowth_eis_sph <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.heisenberg_combination_comm_fockPolynomialVectors : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ sS sT BS BT (f : WO S T → ℂ), IsThetaFunO ψ S T f → ∀ (n : ℕ) (a : Fin n → ℂ) (y : Fin n → WO S T), (∀ i, (y i).map (infPart D) = 0) → ∀ φ, ∑ i, a i • heisO ψ S T (y i) (pureTensorO ψ θ S T sS sT BS BT f φ) = pureTensorO ψ θ S T sS sT BS BT (∑ i, a i • heisO ψ S T (y i) f) φ ∧ pureTensorO ψ θ S T sS sT BS BT (0 : WO S T → ℂ) φ = 0 := by
  first | exact @GlobalTheory.FockFiniteHeis.heis_comb_pureTensorO | exact GlobalTheory.FockFiniteHeis.heis_comb_pureTensorO | (intros; apply GlobalTheory.FockFiniteHeis.heis_comb_pureTensorO <;> assumption)
end
