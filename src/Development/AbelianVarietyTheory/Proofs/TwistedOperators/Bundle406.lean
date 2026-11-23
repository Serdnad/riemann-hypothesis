module

public import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle162
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle378
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle377
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Formalism.LocalToGlobal.IndefiniteReal.Bundle015

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.Per

theorem besPer_haar_scale : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ {A B : HSp D} {c : ℕ} {ε : D.host.E} (a : HermitianOrthogonalExtensionData A B c ε) (dd : BesDat A B a.ι), GlobalTheory.Unf.CoCpt A → ∀ (μ μ' : Measure (GA D A)) (𝓕 𝓕' : Set (GA D A)) (ν ν' : Measure (NFlag B dd.e)) (𝓝 𝓝' : Set (NFlag B dd.e)), μ.IsHaarMeasure → IsFundamentalDomain (GQ A) 𝓕 μ → μ'.IsHaarMeasure → IsFundamentalDomain (GQ A) 𝓕' μ' → GlobalTheory.Per.IsUnitN B dd.e ν 𝓝 → GlobalTheory.Per.IsUnitN B dd.e ν' 𝓝' → ∀ (φ : GA D A → ℂ) (F : GA D B → ℂ), (∀ γ ∈ GQ A, ∀ g, φ (γ * g) = φ g) → (∀ γ ∈ GQ B, ∀ g, F (γ * g) = F g) → ∃ r : ℝ, 0 < r ∧ GlobalTheory.Per.besPer ψ dd μ 𝓕 ν 𝓝 (stabilizerEmbedding a) φ F = r * GlobalTheory.Per.besPer ψ dd μ' 𝓕' ν' 𝓝' (stabilizerEmbedding a) φ F := by
  intro D ψ hψ A B c ε a dd _ μ μ' 𝓕 𝓕' ν ν' 𝓝 𝓝' hμ h𝓕 hμ' h𝓕' hN hN' φ F hφ hF
  obtain ⟨_, _, _, _, _, -, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D A
  obtain ⟨-, -, -, -, _, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  obtain ⟨_, _, _, _⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag B dd.e_iso
  obtain ⟨s, -, hs, hq⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D B A a.ι a.isom
  have hsa : stabilizerEmbedding a = s := funext fun h => ((embRel_iff a h _).1 ((hs _ _).2 rfl)).symm

  have hl : ∀ h, ∀ γ ∈ NFlagQ B dd.e, ∀ n : NFlag B dd.e,
      besFun ψ dd (stabilizerEmbedding a) φ F h (γ * n) = besFun ψ dd (stabilizerEmbedding a) φ F h n := by
    intro h γ hγ n
    simp only [besFun, Subgroup.coe_mul]
    rw [GlobalTheory.BesselChar.besChar_mul ψ dd γ n γ.2 n.2, GlobalTheory.BesselChar.besChar_rat ψ hψ.1 dd γ γ.2 hγ, one_mul,
      mul_assoc (γ : GA D B), mul_assoc (γ : GA D B), hF (γ : GA D B) hγ]

  have e1 : ∀ h, ∫ n in 𝓝, besFun ψ dd (stabilizerEmbedding a) φ F h n ∂ν = ∫ n in 𝓝', besFun ψ dd (stabilizerEmbedding a) φ F h n ∂ν' :=
    fun h => GlobalTheory.Mem.TrueRecord.integral_unit _ hN.1 hN.2.1 hN.2.2 hN'.1 hN'.2.1 hN'.2.2 _ (hl h)

  have e2 : ∀ γ ∈ GQ A, ∀ g, ∫ n in 𝓝, besFun ψ dd (stabilizerEmbedding a) φ F (γ * g) n ∂ν =
      ∫ n in 𝓝, besFun ψ dd (stabilizerEmbedding a) φ F g n ∂ν := by
    intro γ hγ g
    have r2 : EmbRel B A a.ι (s γ)⁻¹ γ⁻¹ := (hs _ _).2 (map_inv s _).symm
    have r1 : EmbRel B A a.ι (s γ) γ := (hs _ _).2 rfl
    let k : NFlag B dd.e ≃ₜ* NFlag B dd.e :=
      { toFun := fun n => ⟨(s γ)⁻¹ * n * (s γ)⁻¹⁻¹, (GlobalTheory.BesselChar.besChar_conj ψ dd _ _ r2 n n.2).1⟩
        invFun := fun n => ⟨s γ * n * (s γ)⁻¹, (GlobalTheory.BesselChar.besChar_conj ψ dd _ _ r1 n n.2).1⟩
        left_inv := fun n => Subtype.ext (by simp [mul_assoc])
        right_inv := fun n => Subtype.ext (by simp [mul_assoc])
        map_mul' := fun x y => Subtype.ext (by simp [mul_assoc])
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
    have hk : ∀ n, k n ∈ NFlagQ B dd.e ↔ n ∈ NFlagQ B dd.e := fun n => by
      change (s γ)⁻¹ * (n : GA D B) * (s γ)⁻¹⁻¹ ∈ GQ B ↔ (n : GA D B) ∈ GQ B
      rw [Subgroup.mul_mem_cancel_right _ (inv_mem (inv_mem (hq _ hγ))),
        Subgroup.mul_mem_cancel_left _ (inv_mem (hq _ hγ))]
    refine Eq.trans ?_ (GlobalTheory.Mem.TrueRecord.integral_aut _ hN.1 hN.2.1 hN.2.2 k hk _ (hl g))
    congr 1
    funext n
    have hc := (GlobalTheory.BesselChar.besChar_conj ψ dd _ _ r2 n n.2).2
    simp only [besFun, k, ContinuousMulEquiv.coe_mk, MulEquiv.coe_mk, Equiv.coe_fn_mk]
    rw [hc, hsa, hφ γ hγ, map_mul, ← hF _ (inv_mem (hq γ hγ)) ((n : GA D B) * (s γ * s g) * (dd.y : GA D B))]
    simp only [mul_assoc, inv_inv]

  have hc := Measure.haarScalarFactor_pos_of_isHaarMeasure μ μ'
  have e := Measure.isMulLeftInvariant_eq_smul μ μ'
  have hac : μ' ≪ μ := by
    intro t ht
    rw [e, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, mul_eq_zero] at ht
    exact ht.resolve_left (by simpa using hc.ne')
  have h𝓕₁ : IsFundamentalDomain (GQ A) 𝓕 μ' := h𝓕.mono hac
  refine ⟨(μ.haarScalarFactor μ' : ℝ), by exact_mod_cast hc, ?_⟩
  show ∫ h in 𝓕, ∫ n in 𝓝, besFun ψ dd (stabilizerEmbedding a) φ F h n ∂ν ∂μ =
    _ * ∫ h in 𝓕', ∫ n in 𝓝', besFun ψ dd (stabilizerEmbedding a) φ F h n ∂ν' ∂μ'
  simp_rw [← e1]
  rw [← h𝓕₁.setIntegral_eq h𝓕' (fun γ g => e2 γ γ.2 g)]
  conv_lhs => rw [e]
  rw [Measure.restrict_smul, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

end GlobalTheory.Per
end
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S

noncomputable section
namespace GlobalTheory.FinMeasEq

variable {D : D7}

theorem locallyCompactSpace_GfC (V : HSp D) : LocallyCompactSpace (GfC V) :=
  locallyCompactSpace_finPts D.sp.cm.sig V.gram

theorem tensorFin_unitLoc (V : HSp D) (g : GFin D.sp.cm.sig V.gram) :
    tensorFin D.sp.cm.sig V.gram (unitLoc D.sp.cm.sig V.gram (frameLat V)) g =
      (levelOffFin D.sp.cm.sig V.gram (frameLat V) ∅ : Set (GFin D.sp.cm.sig V.gram)).indicator 1 g := by
  letI : Submodule.IsFullLattice D.host.E (frameLat V) := SelfDual.isLattice_frameLat V
  by_cases hg : g ∈ levelOffFin D.sp.cm.sig V.gram (frameLat V) ∅
  · rw [Set.indicator_of_mem hg]
    have hv := (mem_levelOffFin.1 hg).2
    unfold tensorFin
    rw [Pi.one_apply]
    refine (finprod_congr fun v => ?_).trans finprod_one
    simp [unitLoc, hv v (Finset.notMem_empty v)]
  · rw [Set.indicator_of_notMem hg]
    by_contra hne
    refine hg (mem_levelOffFin.2 ⟨fun v hv => absurd hv (Finset.notMem_empty v), fun v _ => ?_⟩)
    have := (isFinFamily_unit.tensorFin_ne_zero_iff g).1 hne v
    by_contra hv
    exact this (by simp [unitLoc, hv])

theorem finMeas_eq : ∀ (D : D7) (V : HSp D) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v))
    (νF : Measure (GFin D.sp.cm.sig V.gram)), IsRestrictedProdFin D.sp.cm.sig V.gram (frameLat V) μf νF →
    ∀ (ν : Measure (GfC V)), IsFinMeas V μf ν → ∀ s : Set (GfC V), IsCompact (closure s) →
      ν s = νF ((finPtsEquiv D.sp.cm.sig V.gram) ⁻¹' s) := by
  intro D V μf νF hF ν hν s hs
  letI : Submodule.IsFullLattice D.host.E (frameLat V) := SelfDual.isLattice_frameLat V
  haveI := locallyCompactSpace_GfC V
  haveI : ν.IsHaarMeasure := hν.1
  set e := finPtsEquiv D.sp.cm.sig V.gram
  set ν' : Measure (GfC V) := νF.map e with hν'
  have hmap : ∀ t : Set (GfC V), ν' t = νF (e ⁻¹' t) := fun t =>
    e.toHomeomorph.toMeasurableEquiv.map_apply t
  haveI : ν'.IsHaarMeasure := (isRestrictedProdFinPts_iff.1 hF.map_finPts).2.1

  set Kf : Set (GFin D.sp.cm.sig V.gram) := (levelOffFin D.sp.cm.sig V.gram (frameLat V) ∅ : Set (GFin D.sp.cm.sig V.gram))
  set K : Set (GfC V) := e.symm ⁻¹' Kf with hK
  have hKo : IsOpen K := (isOpen_levelOffFin_empty _ _ _).preimage e.symm.continuous
  have hKf_closed : IsClosed Kf :=
    Subgroup.isClosed_of_isOpen _ (isOpen_levelOffFin_empty _ _ _)
  have hKc : IsClosed K := hKf_closed.preimage e.symm.continuous
  have hKcpt : IsCompact K := by
    have : K = e '' Kf := (e.toHomeomorph.image_eq_preimage_symm Kf).symm
    rw [this]
    exact (isCompact_levelOffFin _ _ _ ∅).image e.continuous
  have hKne : K.Nonempty := ⟨1, by
    change e.symm 1 ∈ Kf
    rw [map_one]
    exact Subgroup.one_mem _⟩

  have h1 : ν' K = ∏ᶠ v, μf v (stabLoc D.sp.cm.sig V.gram (frameLat V) v) := by
    rw [hmap]
    refine (congrArg νF (Set.ext fun x => ?_)).trans hF.measure_level
    change e.symm (e x) ∈ Kf ↔ _
    rw [e.symm_apply_apply]
  have hfin : (Function.mulSupport fun v => μf v (stabLoc D.sp.cm.sig V.gram (frameLat V) v)).Finite :=
    Filter.eventually_cofinite.1 (isRestrictedProdFin_iff.1 hF).2.2.1
  have h2 : ν.real K = ∏ᶠ v, (μf v).real (stabLoc D.sp.cm.sig V.gram (frameLat V) v) := by
    have hi := hν.2 _ isFinFamily_unit
    have hfn : finFn V (unitLoc D.sp.cm.sig V.gram (frameLat V)) = K.indicator (fun _ => (1 : ℂ)) := by
      funext y
      rw [GlobalTheory.TrConv.finFn_eq_tensorFin, tensorFin_unitLoc]
      rfl
    rw [hfn, integral_indicator_const _ hKo.measurableSet] at hi
    have hloc : ∀ v, ∫ x, unitLoc D.sp.cm.sig V.gram (frameLat V) v x ∂μf v =
        (((μf v).real (stabLoc D.sp.cm.sig V.gram (frameLat V) v) : ℝ) : ℂ) := fun v => by
      have := (isOpen_stabLoc D.sp.cm.sig V.gram (frameLat V) v).measurableSet
      rw [unitLoc, show (1 : GLoc D.sp.cm.sig V.gram v → ℂ) = fun _ => 1 from rfl,
        integral_indicator_const _ this]
      simp
    simp_rw [hloc] at hi
    have hc : (∏ᶠ v, (((μf v).real (stabLoc D.sp.cm.sig V.gram (frameLat V) v) : ℝ) : ℂ)) =
        ((∏ᶠ v, (μf v).real (stabLoc D.sp.cm.sig V.gram (frameLat V) v) : ℝ) : ℂ) :=
      (Complex.ofRealHom.toMonoidHom.map_finprod_of_injective Complex.ofReal_injective _).symm
    rw [Complex.real_smul, mul_one, hc] at hi
    exact_mod_cast hi
  have h3 : ν K = ν' K := by
    rw [h1]
    have hK' : ν K ≠ ⊤ := hKcpt.measure_lt_top.ne
    have hP : ∏ᶠ v, μf v (stabLoc D.sp.cm.sig V.gram (frameLat V) v) ≠ ⊤ := by
      rw [← h1]; exact hKcpt.measure_lt_top.ne
    rw [← ENNReal.toReal_eq_toReal_iff' hK' hP]
    rw [show (ν K).toReal = ν.real K from rfl, h2]
    exact (ENNReal.toRealHom.map_finprod hfin).symm
  have hc := Measure.measure_isMulInvariant_eq_smul_of_isCompact_closure ν ν' (s := K)
    (by rw [hKc.closure_eq]; exact hKcpt)
  have hc1 : Measure.haarScalarFactor ν ν' = 1 := by
    have hpos : ν' K ≠ 0 := hKo.measure_ne_zero ν' hKne
    have htop : ν' K ≠ ⊤ := hKcpt.measure_lt_top.ne
    rw [h3, ENNReal.smul_def, smul_eq_mul] at hc
    have := (ENNReal.mul_left_inj hpos htop).1 ((one_mul _).trans hc)
    exact_mod_cast this.symm
  rw [Measure.measure_isMulInvariant_eq_smul_of_isCompact_closure ν ν' hs, hc1, one_smul, hmap]

end GlobalTheory.FinMeasEq
end
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

theorem _root_.GlobalTheory.T.convolution_finiteAdelicPureTensor_eq_localConvolutions : ∀ (D : D7) (V : HSp D) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)), (∀ v, (μf v).IsHaarMeasure) → (∀ᶠ v in cofinite, μf v (Kv V v) = 1) → ∀ ν, IsFinMeas V μf ν → ∀ a b, IsFinFamily D.sp.cm.sig V.gram (frameLat V) a → IsFinFamily D.sp.cm.sig V.gram (frameLat V) b → IsFinFamily D.sp.cm.sig V.gram (frameLat V) (fun v => conv (μf v) (a v) (b v)) ∧ finFn V (fun v => conv (μf v) (a v) (b v)) = conv ν (finFn V a) (finFn V b) ∧ finFn V a ∈ GlobalTheory.SplitWeil.SB (GfC V) := by
  first | exact @GlobalTheory.TrConv.conv_finFn | exact GlobalTheory.TrConv.conv_finFn | (intros; apply GlobalTheory.TrConv.conv_finFn <;> assumption)
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.TrIdem

noncomputable section

namespace GlobalTheory.TrIdem

theorem integralOp_normInd_fix : ∀ (D : D7) (V : HSp D) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)), (∀ v, (μf v).IsHaarMeasure) → (∀ᶠ v in cofinite, μf v (Kv V v) = 1) → ∀ ν, IsFinMeas V μf ν → ∀ (K' : ∀ v, Subgroup (GLoc D.sp.cm.sig V.gram v)), (∀ v, IsOpen (K' v : Set (GLoc D.sp.cm.sig V.gram v))) → (∀ v, K' v ≤ Kv V v) → (∀ᶠ v in cofinite, K' v = Kv V v) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W) (x : W), (∀ g : GfC V, (∀ v, finLoc V v g ∈ K' v) → σ g x = x) → ∀ P, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ (finFn V (fun v => normInd (μf v) (K' v : Set (GLoc D.sp.cm.sig V.gram v)))) P → P x = x := by
  intro D V μf hH h1 ν hν K' hO hle hcof W _ _ σ x hx P hP
  letI : Submodule.IsFullLattice D.host.E (frameLat V) := SelfDual.isLattice_frameLat V
  set c : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ :=
    fun v => normInd (μf v) (K' v : Set (GLoc D.sp.cm.sig V.gram v)) with hc
  have hcpt : ∀ v, IsCompact (K' v : Set (GLoc D.sp.cm.sig V.gram v)) := fun v =>
    (isCompact_stabLoc _ _ (frameLat V) v).of_isClosed_subset ((K' v).isClosed_of_isOpen (hO v)) (hle v)
  have hpos : ∀ v, (μf v).real (K' v : Set (GLoc D.sp.cm.sig V.gram v)) ≠ 0 := fun v => by
    have := hH v
    rw [Measure.real, ENNReal.toReal_ne_zero]
    exact ⟨(hO v).measure_ne_zero (μf v) ⟨1, (K' v).one_mem⟩, (hcpt v).measure_lt_top.ne⟩
  have hint : ∀ v, ∫ y, c v y ∂μf v = 1 := fun v => by
    simp only [hc, normInd, Pi.smul_apply]
    rw [integral_smul]
    erw [integral_indicator_const (μ := μf v) (1 : ℂ) (hO v).measurableSet]
    simp only [Complex.real_smul, smul_eq_mul, mul_one]
    exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.2 (hpos v))
  have hfam : IsFinFamily D.sp.cm.sig V.gram (frameLat V) c := by
    refine ⟨fun v => Submodule.smul_mem _ _ (indicator_mem_SB (hO v) (hcpt v)), ?_⟩
    filter_upwards [hcof, h1] with v hv hv1
    simp only [hc, normInd, unitLoc, hv]
    simp [Measure.real, hv1]
  have hI : ∫ g, finFn V c g ∂ν = 1 := by
    rw [hν.2 c hfam]
    simp [hint]
  have hsupp : ∀ g : GfC V, finFn V c g ≠ 0 → ∀ v, finLoc V v g ∈ K' v := by
    intro g hg v
    have hfin : (Function.mulSupport fun v => c v (proj D.sp.cm.sig V.gram v (g : GA D V))).Finite :=
      Filter.eventually_cofinite.1 ((hfam.2.and (eventually_proj_mem_stabLoc _ _ (frameLat V) (g : GA D V))).mono
        fun v hv => by show c v _ = 1; rw [hv.1, unitLoc, indicator_of_mem hv.2, Pi.one_apply])
    by_contra hv
    apply hg
    refine finprod_eq_zero _ v ?_ hfin
    change normInd (μf v) (K' v : Set (GLoc D.sp.cm.sig V.gram v)) (finLoc V v g) = 0
    simp [normInd, Set.indicator_of_notMem hv]
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro l
  have e : (fun g => finFn V c g * l (σ g x)) = fun g => finFn V c g * l x := by
    funext g
    by_cases h : finFn V c g = 0
    · simp [h]
    · rw [hx g (hsupp g h)]
  rw [map_sub, (hP x l).2, e, integral_mul_const, hI, one_mul, sub_self]

end GlobalTheory.TrIdem
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open ValuativeRel Formalism.L2.Host

noncomputable section

namespace GlobalTheory.GivenField

open GlobalTheory.StepData

section Local

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable (F : Subfield ℂ)

theorem lam_principal_mem {a : Type*} [Fintype a] [DecidableEq a] (g : (TypeDatum.principal k a).J) :
    (((TypeDatum.principal k a).lam g : ℂˣ) : ℂ) ∈ F := by
  change ((1 : ℂˣ) : ℂ) ∈ F
  rw [Units.val_one]
  exact one_mem F

theorem lam_reindex_mem {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (P : TypeDatum k a)
    (e : a ≃ b) (hP : ∀ g, ((P.lam g : ℂˣ) : ℂ) ∈ F) (g : (P.reindex e).J) : (((P.reindex e).lam g : ℂˣ) : ℂ) ∈ F :=
  hP _

theorem lam_step_mem {a t : Type*} [Fintype a] [DecidableEq a] [Fintype t] [DecidableEq t] (P : TypeDatum k a)
    (μ : kˣ →* ℂˣ) (hμ : IsTame μ) (hP : ∀ g, ((P.lam g : ℂˣ) : ℂ) ∈ F) (hμF : ∀ x, ((μ x : ℂˣ) : ℂ) ∈ F)
    (h : (P.step t μ hμ).J) : (((P.step t μ hμ).lam h : ℂˣ) : ℂ) ∈ F := by
  rw [P.step_lam μ hμ h (P.corner h) (P.corner_val h), Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val]
  exact mul_mem (mul_mem (hP _) (inv_mem (hμF _))) (hμF _)

theorem lam_iter_mem {r t : Type*} [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] (P : TypeDatum k r)
    (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (hP : ∀ g, ((P.lam g : ℂˣ) : ℂ) ∈ F)
    (hμF : ∀ j x, ((μ j x : ℂˣ) : ℂ) ∈ F) (j : ℕ) : ∀ g, (((P.iter t μ hμ j).lam g : ℂˣ) : ℂ) ∈ F := by
  induction j with
  | zero => exact lam_reindex_mem F P _ hP
  | succ j ih => exact lam_reindex_mem F _ _ (lam_step_mem F _ _ _ ih (hμF _))

theorem Phi_mem {a t : Type*} [Fintype a] [DecidableEq a] (P : TypeDatum k a) (μ : kˣ →* ℂˣ)
    (hP : ∀ g, ((P.lam g : ℂˣ) : ℂ) ∈ F) (hμF : ∀ x, ((μ x : ℂˣ) : ℂ) ∈ F) (x : Matrix (a ⊕ t) a k) :
    P.Phi t μ x ∈ F := by
  by_cases h : P.Phi t μ x = 0
  · rw [h]; exact zero_mem F
  · obtain ⟨⟨g, hg, e⟩, h2⟩ := (P.Phi_ne_zero_iff μ).1 h
    rw [P.Phi_of_mem μ ⟨g, hg⟩ e h2, Units.val_inv_eq_inv_val]
    exact mul_mem (hP _) (inv_mem (hμF _))

theorem iterPhi_mem {r t : Type*} [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] (P : TypeDatum k r)
    (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (hP : ∀ g, ((P.lam g : ℂˣ) : ℂ) ∈ F)
    (hμF : ∀ j x, ((μ j x : ℂˣ) : ℂ) ∈ F) (j : ℕ) (x : Matrix (Ix r t (j + 1)) (Ix r t j) k) :
    P.iterPhi t μ hμ j x ∈ F :=
  Phi_mem F _ _ (lam_iter_mem F P μ hμ hP hμF j) (hμF _) _

theorem parPhi_mem {r s s' : Type*} [Fintype r] [DecidableEq r] (δ : kˣ →* ℂˣ) (hδ : ∀ x, ((δ x : ℂˣ) : ℂ) ∈ F)
    (x : Matrix (r ⊕ s) (r ⊕ s') k) : parPhi δ x ∈ F := by
  by_cases h : parPhi δ x = 0
  · rw [h]; exact zero_mem F
  · obtain ⟨⟨g, hg, e⟩, h21, h12, h22⟩ := (parPhi_ne_zero_iff δ).1 h
    rw [parPhi_of_mem δ hg e h21 h12 h22, Units.val_inv_eq_inv_val]
    exact inv_mem (hδ _)

theorem indicator_one_mem {X : Type*} (S : Set X) (x : X) : S.indicator (1 : X → ℂ) x ∈ F := by
  classical
  rw [Set.indicator_apply]
  split_ifs
  · exact one_mem F
  · exact zero_mem F

end Local

section Global

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (F : Subfield ℂ) (w : Pl D.host.E)

theorem muBase_mem (hmu : ∀ j x, ((L.C.mu0 j).loc w x : ℂ) ∈ F) (c : ℕ) (x : (Kw w)ˣ) :
    (((muBase L c).loc w x : ℂˣ) : ℂ) ∈ F := by
  rcases c with _ | c
  · simp [muBase, HChar.loc]
  · simp only [muBase]
    split_ifs with h
    · exact hmu _ _
    · simp [HChar.loc]

variable {t : T} (hmu : ∀ j x, ((L.C.mu0 j).loc w x : ℂ) ∈ F) (hxi : ∀ x, ((L.xiH t).loc w x : ℂ) ∈ F)
include hmu hxi

theorem stepFn_mem (j : ℕ) (x) : stepFn L t w j x ∈ F := by
  unfold stepFn
  split_ifs
  · refine iterPhi_mem F _ _ _ (lam_principal_mem F) (fun c y => ?_) _ _
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
    exact inv_mem (muBase_mem F w hmu c y)
  · refine parPhi_mem F _ (fun y => ?_) _
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
    exact inv_mem (hxi y)
  · exact indicator_one_mem F _ _

theorem givenDatum_mem (B : Frames G) (Φ : G.Datum) (b : Edge) (x) : givenDatum t w B Φ b x ∈ F := by
  rcases b with ⟨i, j⟩ | ⟨i, j⟩
  · rcases i with _ | i
    · simp only [givenDatum]
      exact stepFn_mem F w hmu hxi _ _
    · simp only [givenDatum]
      exact zero_mem F
  · rcases j with _ | j
    · simp only [givenDatum]
      split_ifs
      · exact indicator_one_mem F _ _
      · exact zero_mem F
    · simp only [givenDatum]
      exact zero_mem F

end Global

theorem tensor_givenStage_mem : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (F : Subfield ℂ) (B : Frames G) (t : T) (Φ : G.Datum) (w : Pl D.host.E), (∀ j x, ((L.C.mu0 j).loc w x : ℂ) ∈ F) → (∀ x, ((L.xiH t).loc w x : ℂ) ∈ F) → ∀ z : (locGrid G t w).Args, (givenStage t w B Φ).tensor z ∈ F := by
  intro D T L sc G F B t Φ w hmu hxi z
  show ((GlobalTheory.SplitFlip.givenPath D.R.m).map fun b => givenDatum t w B Φ b (z b)).prod ∈ F
  refine list_prod_mem fun y hy => ?_
  obtain ⟨b, -, rfl⟩ := List.mem_map.1 hy
  exact givenDatum_mem F w hmu hxi B Φ b _

end GlobalTheory.GivenField
end
end
