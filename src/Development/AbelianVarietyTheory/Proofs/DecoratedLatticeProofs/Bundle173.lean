module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle152
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1679
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle048
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle219
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle160
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle159
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle179
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle180
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle035
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle142
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle156
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle155
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
import Mathlib.RingTheory.PicardGroup
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord

@[expose] public section

section

noncomputable section

open MeasureTheory ValuativeRel Matrix IsLocalRing GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (cosetInd mainDatum Lifts InDual)
open GlobalTheory.FinPl.Comm (fpair)

namespace GlobalTheory.FinPl.CosetPairing

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type} [Fintype n]

theorem exists_lifts [DecidableEq n] (P : Pair k n) : ∃ F, Lifts P.lat F P.red := by
  haveI := Submodule.IsLattice.free k P.lat
  obtain ⟨g, hg⟩ := Module.projective_lifting_property (Algebra.linearMap 𝒪[k] 𝓀[k]) P.fn residue_surjective
  let b := Module.Free.chooseBasis 𝒪[k] P.lat
  let G : (n → k) →ₗ[k] k := (b.extendOfIsFullLattice k).constr k fun i => (g (b i) : k)
  have h1 : (G.restrictScalars 𝒪[k]) ∘ₗ P.lat.subtype = (Algebra.linearMap 𝒪[k] k) ∘ₗ g := b.ext fun i => by
    have := (b.extendOfIsFullLattice k).constr_basis k (fun i => (g (b i) : k)) i
    rw [Module.Basis.extendOfIsFullLattice_apply] at this
    exact this
  refine ⟨fun i => G (Pi.single i 1), fun y => ⟨g y, ?_, LinearMap.congr_fun hg y⟩⟩
  have h2 : G y = (g y : k) := LinearMap.congr_fun h1 y
  rw [← h2, LinearMap.pi_apply_eq_sum_univ G]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_mul, mul_comm]
  congr 2
  ext j
  simp [Pi.single_apply, eq_comm]

theorem inDual_of_lifts (q : Unif k) {L : Submodule 𝒪[k] (n → k)} {f : Module.Dual 𝓀[k] (Red L)} {F F' : n → k}
    (hF : Lifts L F f) (hF' : Lifts L F' f) : InDual L (q.inv • F - q.inv • F') := fun y hy => by
  obtain ⟨s, hs, hr⟩ := hF ⟨y, hy⟩
  obtain ⟨t, ht, hr'⟩ := hF' ⟨y, hy⟩
  obtain ⟨u, hu⟩ := q.mem_max_iff.1 ((residue_eq_zero_iff (s - t)).1 (by rw [map_sub, hr, hr', sub_self]))
  have hu' : (s : k) - t = q.1 * u := by exact_mod_cast congrArg Subtype.val hu
  rw [← smul_sub, smul_dotProduct, sub_dotProduct, ← hs, ← ht, hu', smul_eq_mul, Unif.inv,
    inv_mul_cancel_left₀ q.ne_zero]
  exact u.2

theorem cosetInd_add (q : Unif k) {L : Submodule 𝒪[k] (n → k)} {f : Module.Dual 𝓀[k] (Red L)} {F : n → k}
    (hF : Lifts L F f) (η : n → k) : cosetInd q L f (η + q.inv • F) = dualInd L η := by
  classical
  refine if_congr ⟨?_, fun h => ⟨F, hF, by simpa using h⟩⟩ rfl rfl
  rintro ⟨F', hF', h⟩ y hy
  have := sub_mem (h y hy) (inDual_of_lifts q hF hF' y hy)
  rwa [← sub_dotProduct, show η + q.inv • F - q.inv • F' - (q.inv • F - q.inv • F') = η by abel] at this

variable {χ : AddChar k Circle} (hχ : HasConductor χ 1) {e : k}


include hχ in
theorem char_dual (he : e = 1 ∨ e = -1) {L : Submodule 𝒪[k] (n → k)} {η y : n → k} (hη : InDual L η) (hy : y ∈ L) :
    χ (e * (η ⬝ᵥ y)) = 1 := by
  rcases he with rfl | rfl
  · simpa using apply_int_eq_one hχ ⟨_, hη y hy⟩
  · simpa using apply_int_eq_one hχ (-⟨_, hη y hy⟩)

theorem char_coset (q : Unif k) {ε : 𝓀[k]ˣ} (he : (e = 1 ∧ ε = 1) ∨ (e = -1 ∧ ε = -1)) {P : Pair k n} {F η y : n → k}
    (hF : Lifts P.lat F P.red) (hη : InDual P.lat η) (hy : y ∈ P.lat) :
    (χ (e * ((η + q.inv • F) ⬝ᵥ y)) : ℂ) = resChar χ hχ q (ε * P.ev y) := by
  obtain ⟨s, hs, hr⟩ := hF ⟨y, hy⟩
  have hr' : P.ev y = residue 𝒪[k] s := ((P.hasVal_fn ⟨y, hy⟩).ev_eq).trans hr.symm
  rw [add_dotProduct, mul_add, AddChar.map_add_eq_mul, char_dual hχ (he.imp And.left And.left) hη hy, one_mul,
    smul_dotProduct, ← hs, hr']
  rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp [resChar_residue]
  · have := resChar_residue hχ q (-s)
    simpa using this.symm

theorem exists_char_ne (q : Unif k) {ε : 𝓀[k]ˣ} (hε : ε = 1 ∨ ε = -1) {Q Q'' : Pair k n} (h : Q''.lat = Q.lat)
    (hne : Q'' ≠ ε • Q) : ∃ y ∈ Q.lat, resChar χ hχ q (-Q.ev y + ε * Q''.ev y) ≠ 1 := by
  have hi : ε⁻¹ = ε := by rcases hε with rfl | rfl <;> simp
  obtain ⟨y, hy, hc⟩ : ∃ y ∈ Q.lat, -Q.ev y + ε * Q''.ev y ≠ 0 := by
    by_contra hc
    push Not at hc
    refine hne (Pair.ext fun x a => ?_)
    rw [Pair.dia_hasVal, hi]
    constructor
    · intro hx
      have hx' := h ▸ hx.mem
      have := hc x hx'
      rw [hx.ev_eq, neg_add_eq_zero] at this
      exact this ▸ Pair.hasVal_ev hx'
    · intro hx
      have := hc x hx.mem
      rw [hx.ev_eq, neg_add_eq_zero, Units.mul_right_inj] at this
      exact this ▸ Pair.hasVal_ev (h ▸ hx.mem)
  obtain ⟨a, ha⟩ := AddChar.ne_one_iff.1 (resChar_ne_one hχ q)
  obtain ⟨s, hs⟩ := residue_surjective (R := 𝒪[k]) (a * (-Q.ev y + ε * Q''.ev y)⁻¹)
  refine ⟨s • y, Q.lat.smul_mem s hy, ?_⟩
  rw [((Pair.hasVal_ev hy).smul s).ev_eq, ((Pair.hasVal_ev (h ▸ hy : y ∈ Q''.lat)).smul s).ev_eq]
  convert ha using 2
  rw [← inv_mul_cancel_right₀ hc a, ← hs]
  ring

theorem fpair_charInd_cosetInd (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (q : Unif k) (χ : AddChar k Circle)
    (hχ : HasConductor χ 1) (e : k) (ε : 𝓀[k]ˣ) (he : (e = 1 ∧ ε = 1) ∨ (e = -1 ∧ ε = -1)) (μ : Measure (n → k))
    [μ.IsAddHaarMeasure] (Q Q'' : Pair k n) (h : Q''.lat = Q.lat) :
    (Q'' = ε • Q → fpair χ e μ (charInd (resChar χ hχ q) Q) (cosetInd q Q''.lat Q''.red) =
      fpair χ e μ (vecInd Q.lat) (dualInd Q.lat)) ∧
    (Q'' ≠ ε • Q → fpair χ e μ (charInd (resChar χ hχ q) Q) (cosetInd q Q''.lat Q''.red) = 0) := by
  haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k
  haveI := secondCountable k
  obtain ⟨F, hF⟩ := exists_lifts Q''
  have hε : ε = 1 ∨ ε = -1 := he.imp And.right And.right
  have key : fpair χ e μ (charInd (resChar χ hχ q) Q) (cosetInd q Q''.lat Q''.red) =
      ∫ η, (∫ y, vecInd Q.lat y * resChar χ hχ q (-Q.ev y + ε * Q''.ev y) ∂μ) * dualInd Q.lat η ∂μ := by
    unfold fpair
    rw [← integral_add_right_eq_self _ (q.inv • F)]
    congr 1
    funext η
    rw [cosetInd_add q hF, h]
    by_cases hη : InDual Q.lat η
    swap
    · rw [dualInd, if_neg hη, mul_zero, mul_zero]
    congr 2
    funext y
    by_cases hy : y ∈ Q.lat
    · rw [char_coset hχ q he hF (h ▸ hη) (h ▸ hy), charInd, AddChar.map_add_eq_mul]
      ring
    · rw [charInd, vecInd, if_neg hy, mul_zero, zero_mul, zero_mul]
  rw [key]
  constructor
  · rintro rfl
    unfold fpair
    congr 1
    funext η
    by_cases hη : InDual Q.lat η
    swap
    · rw [dualInd, if_neg hη, mul_zero, mul_zero]
    congr 2
    funext y
    by_cases hy : y ∈ Q.lat
    · have h1 : Q.ev y = (ε⁻¹ : 𝓀[k]ˣ) * (ε • Q).ev y := (Pair.dia_hasVal.1 (Pair.hasVal_ev (P := ε • Q) hy)).ev_eq
      have hi : ε⁻¹ = ε := by rcases hε with rfl | rfl <;> simp
      rw [hi] at h1
      rw [char_dual hχ (he.imp And.left And.left) hη hy, ← h1, neg_add_cancel]
      simp
    · rw [vecInd, if_neg hy, zero_mul, zero_mul]
  · intro hne
    obtain ⟨y₀, hy₀, hc⟩ := exists_char_ne hχ q hε h hne
    have e1 := integral_add_right_eq_self (μ := μ)
      (fun y => vecInd Q.lat y * resChar χ hχ q (-Q.ev y + ε * Q''.ev y)) y₀
    have e2 : ∀ y, vecInd Q.lat (y + y₀) * resChar χ hχ q (-Q.ev (y + y₀) + ε * Q''.ev (y + y₀)) =
        resChar χ hχ q (-Q.ev y₀ + ε * Q''.ev y₀) * (vecInd Q.lat y * resChar χ hχ q (-Q.ev y + ε * Q''.ev y)) := fun y => by
      by_cases hy : y ∈ Q.lat
      · rw [vecInd, vecInd, if_pos hy, if_pos (add_mem hy hy₀), one_mul, one_mul, ← AddChar.map_add_eq_mul,
          ((Pair.hasVal_ev hy).add (Pair.hasVal_ev hy₀)).ev_eq,
          ((Pair.hasVal_ev (h ▸ hy : y ∈ Q''.lat)).add (Pair.hasVal_ev (h ▸ hy₀ : y₀ ∈ Q''.lat))).ev_eq]
        congr 1
        ring
      · rw [vecInd, vecInd, if_neg hy, if_neg fun h' => hy ((Q.lat.add_mem_iff_left hy₀).1 h')]
        simp
    simp only [e2] at e1
    rw [integral_const_mul] at e1
    have h0 : ∫ y, vecInd Q.lat y * resChar χ hχ q (-Q.ev y + ε * Q''.ev y) ∂μ = 0 := by
      by_contra h0
      exact hc ((mul_eq_right₀ h0).1 e1)
    simp [h0]

end GlobalTheory.FinPl.CosetPairing

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.RealBoxMeasure

variable {D : D7}

theorem exists_realPart (θ : InfFam D) (hθ : IsInfFam θ) (W : HSp D) (hW : W.SigOK) (Fr : Frames W)
    (hFr : IsFrames W Fr) :
    ∃ φ : GA D W → ∀ ρ, Upq W ρ, Continuous φ ∧
      ∀ h ρ, UpqT.mat (φ h ρ) * Fr ρ = Fr ρ * infMat D.sp.cm.sig W.gram (θ ρ) h := by
  have hτ : GlobalTheory.Mem.Vol.IsCMFam (tauE D) := GlobalTheory.Mem.Vol.isCMFam_host _ D.host _ D.eTau
  obtain ⟨hcm, -⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  obtain ⟨e1, he1⟩ := GlobalTheory.Mem.InfGroup.real_points D.host.F D.host.E D.sp.cm.sig W.rank W.gram D.what₂.Tau (tauE D) θ
    (fun ρ => (W.sig (tauE D ρ)).1) (fun ρ => (W.sig (tauE D ρ)).2) Fr hcm hτ hθ (fun i => hW (tauE D i)) hFr
  obtain ⟨e0, he0⟩ := GlobalTheory.Mem.VolSplit.exists_adelic_split D.host.F D.host.E D.sp.cm.sig W.rank W.gram
  refine ⟨fun h => e1 (e0 h).1, e1.continuous.comp (continuous_fst.comp e0.continuous), fun h i => ?_⟩
  show UpqT.mat (e1 (e0 h).1 i) * Fr i = _
  rw [he1, (he0 h).2]; rfl

theorem mat_cancel (W : HSp D) (hW : W.SigOK) (Fr : Frames W) (hFr : IsFrames W Fr) (ρ : D.what₂.Tau)
    {b b' : Upq W ρ} (h : UpqT.mat b * Fr ρ = UpqT.mat b' * Fr ρ) : b = b' := by
  obtain ⟨C, h1, -⟩ := (GlobalTheory.Mem.SignatureFactor.exists_factor _ _ _ _ (hW (tauE D ρ))).2.2 (Fr ρ) (hFr ρ)
  apply (GlobalTheory.UpqTopology.upq_lcsc _ _).2.2.2.2.2.injective
  have h5 := congrArg (· * C) h
  simpa only [Matrix.mul_assoc, h1, Matrix.mul_one] using h5

theorem realMat_of (W : HSp D) (Fr : Frames W) (hFr : IsFrames W Fr) (ρ : D.what₂.Tau) (b : Upq W ρ)
    (M : Matrix (Fin W.rank) (Fin W.rank) ℂ) (h : UpqT.mat b * Fr ρ = Fr ρ * M) : realMat W Fr ρ b = M := by
  have hG := GlobalTheory.SmoothForms.RealPts.gramAt_unit W ρ
  unfold realMat conjFrame
  have e : (Fr ρ)ᴴ * Formalism.UG.Jpq (W.sig (tauE D ρ)).1 (W.sig (tauE D ρ)).2 * (Fr ρ * M) = gramAt D W ρ * M := by
    rw [← Matrix.mul_assoc, hFr ρ]
  rw [Matrix.mul_assoc (_ * _), h, e, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hG, Matrix.one_mul]

theorem realMat_mem (W : HSp D) (hW : W.SigOK) (Fr : Frames W) (hFr : IsFrames W Fr) (ρ : D.what₂.Tau) (b : Upq W ρ) :
    realMat W Fr ρ b ∈ Formalism.QuantumDeterminants.UH (gramAt D W ρ) :=
  conjFrame_mem_UH _ _ _ (GlobalTheory.Mem.SignatureFactor.exists_factor _ _ _ _ (hW (tauE D ρ))).1 _ _ (hFr ρ)
    (GlobalTheory.SmoothForms.RealPts.gramAt_unit W ρ) b

theorem infMat_realElt (θ : InfFam D) (hθ : IsInfFam θ) (W : HSp D) (u : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ)
    (hu : ∀ τ, u τ ∈ Formalism.QuantumDeterminants.UH (gramAt D W τ)) (ρ : D.what₂.Tau) :
    infMat D.sp.cm.sig W.gram (θ ρ) (realElt θ W u) = u ρ := by
  rw [realElt, GlobalTheory.RealTransSm.infMat_list_prod hθ u hu ρ _ (Finset.nodup_toList _),
    if_pos (Finset.mem_toList.2 (Finset.mem_univ ρ))]

theorem realElt_mem (θ : InfFam D) (W : HSp D) (u : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) :
    realElt θ W u ∈ GinfC W := by
  refine list_prod_mem fun x hx => ?_
  obtain ⟨τ, -, rfl⟩ := List.mem_map.1 hx
  exact GlobalTheory.PointAtPlaceHom.atTau_mem W τ (u τ)

theorem finE_realElt (θ : InfFam D) (W : HSp D) (u : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) :
    finE W (realElt θ W u) = 1 := by
  rw [Lev.finE_eq, (MonoidHom.mem_ker).1 (realElt_mem θ W u), map_one]

theorem continuous_realElt (θ : InfFam D) (hθ : IsInfFam θ) (W : HSp D) (hW : W.SigOK) (Fr : Frames W)
    (hFr : IsFrames W Fr) :
    Continuous fun b : (∀ ρ, Upq W ρ) => realElt θ W fun ρ => realMat W Fr ρ (b ρ) := by
  haveI : IsTopologicalGroup (GA D W) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  unfold realElt
  refine continuous_list_prod _ fun ρ _ => ?_
  have hκ : Continuous fun b : (∀ ρ, Upq W ρ) => realMat W Fr ρ (b ρ) := by
    unfold realMat conjFrame
    exact continuous_const.matrix_mul (((continuous_const.matrix_mul
      ((GlobalTheory.UpqTopology.upq_lcsc _ _).2.2.2.2.2.continuous.comp (continuous_apply ρ))).matrix_mul continuous_const))
  exact (GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ W ρ).comp_continuous hκ
    fun b => realMat_mem W hW Fr hFr ρ (b ρ)

theorem lintegral_levelSet_eq_pi : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (W : HSp D), W.SigOK → ∀ (K : Subgroup (GL (Fin W.rank) (Lev.EAf D))) (ν : Measure (GA D W)), IsMeasLev W K ν → ∀ Fr : Frames W, IsFrames W Fr → ∀ mR : ∀ ρ, Measure (Upq W ρ), (∀ ρ, Lev.IsMinf (mR ρ)) → ∀ Z : GA D W → ENNReal, Measurable Z → (∀ g, ∀ k ∈ levA W K, Z (g * k) = Z g) → MeasurableSet {h : GA D W | finE W h ∈ K} → ∫⁻ g in {h : GA D W | finE W h ∈ K}, Z g ∂ν = ∫⁻ b, Z (realElt θ W fun ρ => realMat W Fr ρ (b ρ)) ∂(Measure.pi mR) := by
  intro D θ hθ W hW K ν hν Fr hFr mR hmR Z hZ hZK hS
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.1
  obtain ⟨-, hsc, hbo, -⟩ := GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable W
  haveI := hsc
  haveI := hbo
  haveI : ∀ ρ, SigmaFinite (mR ρ) := fun ρ => by haveI := (hmR ρ).1; infer_instance
  obtain ⟨φ, hφc, hφ⟩ := exists_realPart θ hθ W hW Fr hFr
  have hφm : Measurable φ := hφc.measurable
  set sec : (∀ ρ, Upq W ρ) → GA D W := fun b => realElt θ W fun ρ => realMat W Fr ρ (b ρ) with hsec
  have hsecm : Measurable (fun b => Z (sec b)) := hZ.comp (continuous_realElt θ hθ W hW Fr hFr).measurable
  obtain ⟨-, -, H⟩ := hν
  obtain ⟨-, H1⟩ := H θ hθ
  obtain ⟨-, H2⟩ := H1 Fr hFr
  have hpi : Measure.pi mR = Measure.map φ (ν.restrict {h : GA D W | finE W h ∈ K}) := by
    refine Measure.pi_eq fun B hB => ?_
    have hm : MeasurableSet (φ ⁻¹' Set.univ.pi B) := hφm (MeasurableSet.univ_pi hB)
    rw [Measure.map_apply hφm (MeasurableSet.univ_pi hB), Measure.restrict_apply hm, ← H2 mR hmR B hB]
    congr 1
    ext h
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_univ_pi, Set.mem_setOf_eq]
    rw [and_comm]
    refine and_congr_right fun _ => forall_congr' fun ρ => ⟨fun hb => ⟨φ h ρ, hb, hφ h ρ⟩, ?_⟩
    rintro ⟨b, hb, hbe⟩
    rwa [mat_cancel W hW Fr hFr ρ (hbe.trans (hφ h ρ).symm)] at hb
  have hfac : ∀ h ∈ {h : GA D W | finE W h ∈ K}, Z h = Z (sec (φ h)) := by
    intro h hh
    have e : ∀ ρ, infMat D.sp.cm.sig W.gram (θ ρ) (sec (φ h)) = infMat D.sp.cm.sig W.gram (θ ρ) h := fun ρ => by
      rw [hsec]
      dsimp only
      rw [infMat_realElt θ hθ W _ (fun τ => realMat_mem W hW Fr hFr τ _) ρ]
      exact realMat_of W Fr hFr ρ _ _ (hφ h ρ)
    have hk : (sec (φ h))⁻¹ * h ∈ levA W K := by
      refine ⟨(GlobalTheory.SmoothForms.RealPts.glue θ hθ W).1 _ fun ρ => ?_, ?_⟩
      · rw [GlobalTheory.PointAtPlaceHom.infMat_mul, ← e ρ, ← GlobalTheory.PointAtPlaceHom.infMat_mul, inv_mul_cancel,
          GlobalTheory.PointAtPlaceHom.infMat_one]
      · show finE W ((sec (φ h))⁻¹ * h) ∈ K
        rw [map_mul, map_inv, hsec]
        dsimp only
        rw [finE_realElt, inv_one, one_mul]
        exact hh
    rw [← hZK (sec (φ h)) _ hk, mul_inv_cancel_left]
  calc ∫⁻ g in {h : GA D W | finE W h ∈ K}, Z g ∂ν
      = ∫⁻ g in {h : GA D W | finE W h ∈ K}, Z (sec (φ g)) ∂ν := setLIntegral_congr_fun hS hfac
    _ = ∫⁻ b, Z (sec b) ∂(Measure.map φ (ν.restrict {h : GA D W | finE W h ∈ K})) :=
        (lintegral_map hsecm hφm).symm
    _ = _ := by rw [← hpi]

end GlobalTheory.RealBoxMeasure
end
end

section

noncomputable section

namespace GlobalTheory.Core.Rk.IP.Cartan

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

section Complex

variable {n : ℕ} {G s b c : Matrix (Fin n) (Fin n) ℂ}

theorem herm_of_isCartanInv (hs : IsCartanInv G s) : Gᴴ = G := by
  obtain ⟨h1, h2, h3⟩ := hs
  have h4 : sᴴ * Gᴴ = G * s := by rw [← Matrix.conjTranspose_mul]; exact h3.1
  have h5 : sᴴ * sᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  calc Gᴴ = sᴴ * (sᴴ * Gᴴ) := by rw [← mul_assoc, h5, one_mul]
    _ = G := by rw [h4, ← mul_assoc, h2]

theorem frame_gram_eq (hbc : b * c = 1) (hs : s * s = 1) (h : bᴴ * (G * s) * b = 1) : bᴴ * G * b = c * s * b := by
  calc bᴴ * G * b = bᴴ * (G * (s * (b * c) * s)) * b := by rw [hbc, mul_one, hs, mul_one]
    _ = (bᴴ * (G * s) * b) * (c * s * b) := by simp only [mul_assoc]
    _ = _ := by rw [h, one_mul]

theorem frame_gram_sq (hbc : b * c = 1) (hs : s * s = 1) (h : bᴴ * (G * s) * b = 1) :
    (bᴴ * G * b) * (bᴴ * G * b) = 1 := by
  rw [frame_gram_eq hbc hs h]
  calc c * s * b * (c * s * b) = c * (s * (b * c) * s) * b := by simp only [mul_assoc]
    _ = 1 := by rw [hbc, mul_one, hs, mul_one, mul_eq_one_comm.1 hbc]

theorem frame_inv_eq (hbc : b * c = 1) (hs : s * s = 1) (h : bᴴ * (G * s) * b = 1) : b * bᴴ * G = s := by
  rw [mul_conjTranspose_mul_eq hbc (frame_gram_eq hbc hs h)]
  calc b * (c * s * b) * c = (b * c) * s * (b * c) := by simp only [mul_assoc]
    _ = s := by rw [hbc, one_mul, mul_one]

theorem blkMat_conjTranspose (x y : Matrix (Fin n) (Fin n) ℂ) :
    (blkMat finSumFinEquiv x y)ᴴ = blkMat finSumFinEquiv xᴴ yᴴ := by
  simp [blkMat, Matrix.fromBlocks_conjTranspose]

end Complex

variable {D : D7} {θ : InfFam D}

theorem compAt_blkGL (τ : D.what₂.Tau) {n : ℕ} (a : GL (Fin n) (AE D)) :
    compAt θ τ (blkGL finSumFinEquiv (a, a)).1 = blkMat finSumFinEquiv (compAt θ τ a.1) (compAt θ τ a.1) :=
  blkMat_map finSumFinEquiv ((θ τ).comp (infPart D)) (map_zero _) _ _

theorem commute_of_mem_Kmax (hθ : IsInfFam θ) {V : HSp D} {a : GL (Fin V.rank) (AE D)} (τ : D.what₂.Tau)
    (hd : ((compAt θ τ a.1)ᴴ * gramAt D V τ * compAt θ τ a.1) * ((compAt θ τ a.1)ᴴ * gramAt D V τ * compAt θ τ a.1) = 1)
    {g : GA D V} (hg : g ∈ Kmax V a) :
    Commute (Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram (θ τ) g) (frameInv θ V a τ) := by
  refine (unitary_iff_commute (compAt_mul_inv τ a) rfl hd (infMat_isometry hθ τ g)).1 ?_
  rw [compAt_eq_map hθ, compAt_eq_map hθ, eq_infProj hθ (embOverOf D τ) rfl]
  exact (mem_stabArch_iff_unitary (isCMExt_host D) (embOverOf D τ) V.gram a g).1
    (((mem_levelAll (σ := D.sp.cm.sig) (J := V.gram) (L := frameLat V) (a := a) (g := g)).1 hg).2 _)

theorem cartan_dbl : ∀ (D : D7) (θ : InfFam D) (A : HSp D) (sA : RealMat A) (a : GL (Fin A.rank) (AE D)), IsInfFam θ → (∀ τ, IsCartanInv (gramAt D A τ) (sA τ)) → (∀ τ, (compAt θ τ a.1)ᴴ * (gramAt D A τ * sA τ) * compAt θ τ a.1 = 1) → (∀ τ, IsCartanInv (gramAt D (dblSp A) τ) ((Matrix.fromBlocks (sA τ) 0 0 (-sA τ)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm)) ∧ ∀ k ∈ Khat A a, ∀ τ, compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k) * (Matrix.fromBlocks (sA τ) 0 0 (-sA τ)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm = (Matrix.fromBlocks (sA τ) 0 0 (-sA τ)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm * compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k) := by
  intro D θ A sA a hθ hs ha
  have hbc := fun τ => compAt_mul_inv (θ := θ) τ a
  have e : ∀ τ, frameInv θ (dblSp A) (blkGL finSumFinEquiv (a, a)) τ = blkMat finSumFinEquiv (sA τ) (-sA τ) := fun τ => by
    rw [frameInv_dblSp, show frameInv θ A a τ = sA τ from frame_inv_eq (hbc τ) (hs τ).1 (ha τ)]
  have hd : ∀ τ, (compAt θ τ (blkGL finSumFinEquiv (a, a)).1)ᴴ * blkMat finSumFinEquiv (gramAt D A τ) (-gramAt D A τ) *
      compAt θ τ (blkGL finSumFinEquiv (a, a)).1 =
      blkMat finSumFinEquiv ((compAt θ τ a.1)ᴴ * gramAt D A τ * compAt θ τ a.1)
        (-((compAt θ τ a.1)ᴴ * gramAt D A τ * compAt θ τ a.1)) := fun τ => by
    rw [compAt_blkGL, blkMat_conjTranspose, blkMat_mul, blkMat_mul, Matrix.mul_neg, Matrix.neg_mul]
  have hd2 : ∀ τ, blkMat finSumFinEquiv ((compAt θ τ a.1)ᴴ * gramAt D A τ * compAt θ τ a.1)
        (-((compAt θ τ a.1)ᴴ * gramAt D A τ * compAt θ τ a.1)) *
      blkMat finSumFinEquiv ((compAt θ τ a.1)ᴴ * gramAt D A τ * compAt θ τ a.1)
        (-((compAt θ τ a.1)ᴴ * gramAt D A τ * compAt θ τ a.1)) = 1 := fun τ => by
    rw [blkMat_mul, neg_mul_neg, frame_gram_sq (hbc τ) (hs τ).1 (ha τ), blkMat_one]
  refine ⟨fun τ => ?_, fun k hk τ => ?_⟩
  · have h := isCartanInv_of_frame (compAt_mul_inv (θ := θ) τ (blkGL finSumFinEquiv (a, a))) (hd τ) (hd2 τ) (by
      rw [blkMat_conjTranspose, Matrix.conjTranspose_neg, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, herm_of_isCartanInv (hs τ), ← mul_assoc])
    rw [← gramAt_dblSp] at h
    have h' : IsCartanInv (gramAt D (dblSp A) τ) (frameInv θ (dblSp A) (blkGL finSumFinEquiv (a, a)) τ) := h
    rw [e] at h'
    exact h'
  · rw [Khat_eq] at hk
    have h := commute_of_mem_Kmax hθ (V := dblSp A) (a := blkGL finSumFinEquiv (a, a)) τ (by
      rw [gramAt_dblSp]
      exact (congrArg₂ (· * ·) (hd τ) (hd τ)).trans (hd2 τ)) hk
    rw [e] at h
    exact h

end GlobalTheory.Core.Rk.IP.Cartan

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel ValuativeRel
open scoped Pointwise

theorem _root_.GlobalTheory.T.eq_of_splitPart_agree_supportedAtSplitPlace : ∀ (D : D7) (S : HSp D) (e : AE D) (h h' : GA D S), IsSplitIdem D e → SuppAt e S h → SuppAt e S h' →
    (∀ i j, e * Formalism.L2.Theta.mt S h i j = e * Formalism.L2.Theta.mt S h' i j) → h = h' := by
  first | exact @GlobalTheory.UnitSplit.eq_of_split_part | exact GlobalTheory.UnitSplit.eq_of_split_part | (intros; apply GlobalTheory.UnitSplit.eq_of_split_part <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta MeasureTheory NumberField Matrix GlobalTheory.CuspGeo
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.norm_le_of_cuspidal_variation_unipotentRadical : ∀ (D : D7) (V : HSp D) (φ : GA D V → ℂ), IsAutFun V φ → IsCuspFun V φ → ∀ (r : ℕ) (C₀ : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C₀ → ∀ (g : GA D V) (e : ℝ), (∀ m ∈ NI V C₀, ‖φ (m * g) - φ g‖ ≤ e) → ‖φ g‖ ≤ e := by
  first | exact @GlobalTheory.CuspGeo.norm_le_of_unipRad_variation | exact GlobalTheory.CuspGeo.norm_le_of_unipRad_variation | (intros; apply GlobalTheory.CuspGeo.norm_le_of_unipRad_variation <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.heisenbergOperator_disjointSupport_smul_add : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c c' : AF D.host.F) (x y : WO S T) (f : WO S T → ℂ), c * c' = 0 → heisO ψ S T (c • x + c' • y) f = heisO ψ S T (c • x) (heisO ψ S T (c' • y) f) := by
  first | exact @GlobalTheory.HeisDisj.heisO_smul_add_smul | exact GlobalTheory.HeisDisj.heisO_smul_add_smul | (intros; apply GlobalTheory.HeisDisj.heisO_smul_add_smul <;> assumption)
end
