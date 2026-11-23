module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle011
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle051
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KummerNotCoboundary
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle418
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle384
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle567
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle167
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle145
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle148
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle137
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle144
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle146
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle147
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle163
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle149
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle183
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicMatrixOneAtPlaceScaledPreservesCompletedLa
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.KernelLattices.Bundle003
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle180
public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Columns
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle182
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
import Formalism.LocalToGlobal.InertKernelTheory.Bundle009
import Formalism.LocalToGlobal.InertKernelTheory.Bundle003
import Formalism.SharpRestriction.GrowthBounds.ChartComparison.NrmAMemAdForms
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.IsOrthCo
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle014

@[expose] public section

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU

theorem lamPosG_of_lamPos : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v), LamPos X E.toCEmb pos lam ρ → RepFrame.LamPosG X E D pos lam ρ := by
  intro p _ X _ E D pos lam ρ h v s x
  change TaylorLogMetric.lamC lam (TaylorLogMetric.embT D (pos ⟨v, s⟩) x) = _
  rw [h v s x]
  rfl

end GlobalTheory.TwU
end

section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

namespace GlobalTheory.Pst

theorem StLat.not_frac (l : ℕ) [Fact l.Prime] (Co : Core l) (ϖ : Per.Fl l)
    (hϖ : ϖ.untilt = ((l : ℕ) : Per.OC l)) (u : Per.BdRp l) (hu : IsLogP (beta ϖ) u) (x y : Per.Bcris l)
    (hx : Co.ι x ≠ 0) : Co.ι y ≠ Co.ι x * algebraMap (Per.BdRp l) (Per.BdR l) u := by
  intro h
  obtain ⟨hdom, hdvr, hmax, hmaxθ, -, hfilt, hfr⟩ := BdRDVR.core_dvr l Co
  have hker := GlobalTheory.T.kerP_eq_span_beta_of_untilt_eq l ϖ hϖ
  have hfil := GlobalTheory.T.filP_eq_span_betaD_pow_of_kerP_eq_span_beta l Co ϖ hker
  have hinjD : Function.Injective (algebraMap (Per.BdRp l) (Per.BdR l)) := IsFractionRing.injective _ _
  have hβ0 : betaD ϖ ≠ 0 := by
    intro h0
    apply IsDiscreteValuationRing.not_a_field (Per.BdRp l)
    rw [hmax, ← pow_one (Co.j Co.t), ← hfilt 1, hfil 1, h0, pow_one, Ideal.span_singleton_eq_bot]
  have hsep : ∀ z : Per.BdRp l, (∀ n : ℕ, betaD ϖ ^ n ∣ z) → z = 0 := by
    intro z hz
    have hne : Ideal.span {betaD ϖ} ≠ ⊤ := by
      rw [← pow_one (betaD ϖ), ← hfil 1, hfilt 1, pow_one, ← hmax]
      exact (IsLocalRing.maximalIdeal.isMaximal (Per.BdRp l)).ne_top
    have h1 : z ∈ ⨅ n : ℕ, Ideal.span {betaD ϖ} ^ n := by
      refine (Submodule.mem_iInf _).2 fun n => ?_
      rw [Ideal.span_singleton_pow]
      exact Ideal.mem_span_singleton.2 (hz n)
    rwa [Ideal.iInf_pow_eq_bot_of_isDomain _ hne, Ideal.mem_bot] at h1
  obtain ⟨r, ax, hax⟩ := bcris_eq_acris_localization_periodT_alt l Co x
  obtain ⟨r', ay, hay⟩ := bcris_eq_acris_localization_periodT_alt l Co y
  set tt := algebraMap (Per.Acris l) (Per.Bcris l) Co.t with htt
  have e1 : algebraMap (Per.Acris l) (Per.Bcris l) (ax * Co.t ^ r') = x * tt ^ (r + r') := by
    rw [map_mul, map_pow, ← hax, pow_add]; ring
  have e2 : algebraMap (Per.Acris l) (Per.Bcris l) (ay * Co.t ^ r) = y * tt ^ (r + r') := by
    rw [map_mul, map_pow, ← hay, pow_add]; ring
  have e3 : Co.j (ay * Co.t ^ r) = Co.j (ax * Co.t ^ r') * u := by
    apply hinjD
    rw [map_mul (algebraMap (Per.BdRp l) (Per.BdR l)), ← Co.ι_j, ← Co.ι_j, e1, e2, map_mul Co.ι, map_mul Co.ι, h]
    ring
  have hA := GlobalTheory.T.acris_mem_betaAdicClosure_ainfAdjoinBeta l Co.j Co.j_cris ϖ (GlobalTheory.T.divPowerEnvelope_mem_ainfAdjoinBeta l ϖ hϖ) hfil
  have hz := GlobalTheory.T.eq_zero_of_mem_clos_of_pow_mul_mul_mem_clos l (Fact.out : l.Prime) (isUnit_l_BdRp l) (betaD ϖ) hβ0 hsep (Sg ϖ)
    (GlobalTheory.T.ainfAdjoinBetaImage_div_beta_pow l ϖ hϖ hker hfil) (GlobalTheory.T.betaImageDeRhamPlus_dvd_of_lAdic_residues l ϖ hker hfil) u
    (GlobalTheory.T.log_period_congruence_bdr l ϖ hker hfil u hu) (Co.j (ax * Co.t ^ r')) 0 (hA _) (by
      rw [pow_zero, one_mul, ← e3]; exact hA _)
  have hz2 : Co.ι (x * tt ^ (r + r')) = 0 := by
    rw [← e1, Co.ι_j, hz, map_zero]
  have htne : Co.ι tt ≠ 0 := by
    rw [htt, Co.ι_j]
    intro h0
    have h3 : Co.j Co.t = 0 := hinjD (h0.trans (map_zero _).symm)
    apply IsDiscreteValuationRing.not_a_field (Per.BdRp l)
    rw [hmax, h3, Ideal.span_singleton_eq_bot]
  haveI : IsDomain (Per.BdR l) := IsFractionRing.isDomain (Per.BdRp l)
  rw [map_mul, map_pow] at hz2
  exact mul_ne_zero hx (pow_ne_zero _ htne) hz2

theorem StLat.kummer_not_frac : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (b b' : P.R.B), b ≠ 0 →
  ¬ ∀ g ∈ GK K, b * P.actQ g b' - P.actQ g b * b' = b * P.actQ g b * ((kummer P g : ℚ_[l]) • P.tB) := by
  intro l _ P AI T K b b' hb h
  haveI : IsDomain P.R.B := GlobalTheory.RegularRing.isDomain_of_tied T (botExt l)
  obtain ⟨x, y, hx, hxy⟩ := GlobalTheory.T.exists_kummerFracCoboundary_full_galois l P K b b' hb h
  obtain ⟨Co, hC⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l P AI T
  obtain ⟨ϖ, hr⟩ := exists_tilt (lRoot l) (lRoot_succ l) l (lRoot_zero l)
  have hϖ : ϖ.untilt = ((l : ℕ) : Per.OC l) := Subtype.ext (by
    have := hr 0
    rw [lRoot_zero, map_natCast] at this
    exact this.trans (SubringClass.coe_natCast _ _).symm)
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_logOnePlus_kerTheta_deRhamPlus l (beta ϖ) (by
    rw [GlobalTheory.T.kerP_eq_span_beta_of_untilt_eq l ϖ hϖ]; exact Ideal.mem_span_singleton_self _)
  have hg := GlobalTheory.T.galois_logTeichmullerRatio_eq_add_kummer l P Co hC.ζ ϖ hr hϖ u hu
  letI : Field P.R.BdR := (GlobalTheory.RegularRing.isField_of_tied T).toField
  set U := T.eD.symm (algebraMap (Per.BdRp l) (Per.BdR l) u) with hUdef
  have hct : ∀ g : GQ l, T.eD (P.ιB ((kummer P g : ℚ_[l]) • P.tB)) =
      algebraMap (Per.BdRp l) (Per.BdR l)
        (Co.j (algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l (kummer P g)) * Co.t)) := by
    intro g
    rw [hC.ι, Algebra.smul_def, map_mul, T.zB, hC.t, ← Co.ι_j]
    simp only [Core.tB, GlobalTheory.RingIface.zB_alg, map_mul]
  have hU : ∀ g : GQ l, P.actQdR g U = U + P.ιB ((kummer P g : ℚ_[l]) • P.tB) := by
    intro g
    apply T.eD.injective
    rw [T.actD, hUdef, RingEquiv.apply_symm_apply, map_add (f := _), RingEquiv.apply_symm_apply, hct]
    rw [show Per.σD g (algebraMap (Per.BdRp l) (Per.BdR l) u) =
      algebraMap (Per.BdRp l) (Per.BdR l) (Per.σDp g u) from
        GlobalTheory.RingIface.sigD_alg l g u, hg, map_add]
  have hcomm : ∀ (g : GQ l) (z : P.R.B), P.ιB (P.actQ g z) = P.actQdR g (P.ιB z) := by
    intro g z
    have := (P.PD (botExt l)).ι_comm ⟨g, mem_GK_botExt g⟩ z
    rwa [P.PD_ι, P.PD_actB, P.PD_ι, P.PD_actdR] at this
  have hX : P.ιB x ≠ 0 := fun h0 => hx ((P.PD (botExt l)).ι_inj (by rw [P.PD_ι, h0, map_zero]))
  have hgX : ∀ g : GQ l, P.actQdR g (P.ιB x) ≠ 0 := fun g h0 =>
    hX ((P.actQdR g).injective (h0.trans (map_zero _).symm))
  have hW : ∀ g : GQ l, P.actQdR g (P.ιB y * (P.ιB x)⁻¹ - U) = P.ιB y * (P.ιB x)⁻¹ - U := by
    intro g
    have h1 := congrArg P.ιB (hxy g)
    simp only [map_sub, map_mul, hcomm] at h1
    rw [map_sub, map_mul, map_inv₀, hU]
    have hx1 := mul_inv_cancel₀ hX
    have hx2 := mul_inv_cancel₀ (hgX g)
    linear_combination ((P.ιB x)⁻¹ * (P.actQdR g (P.ιB x))⁻¹) * h1
      - (P.actQdR g (P.ιB y) * (P.actQdR g (P.ιB x))⁻¹) * hx1 + (P.ιB y * (P.ιB x)⁻¹) * hx2
      + (P.ιB ((kummer P g : ℚ_[l]) • P.tB) * P.actQdR g (P.ιB x) * (P.actQdR g (P.ιB x))⁻¹) * hx1
      + P.ιB ((kummer P g : ℚ_[l]) • P.tB) * hx2
  obtain ⟨c, hc⟩ := (P.PD (botExt l)).invdR (P.ιB y * (P.ιB x)⁻¹ - U) fun g => by
    rw [P.PD_actdR]; exact hW g
  obtain ⟨a, ha⟩ := IntermediateField.mem_bot.1 c.2
  have hca : algebraMap ↥(botExt l).1 P.R.BdR c = algebraMap ℚ_[l] P.R.BdR a := by
    have e : c = algebraMap ℚ_[l] ↥(botExt l).1 a := Subtype.ext ha.symm
    rw [e, ← IsScalarTower.algebraMap_apply]
  rw [hca] at hc
  have hY : P.ιB (y - a • x) = P.ιB x * U := by
    rw [map_sub, map_smul, Algebra.smul_def]
    have hx1 := mul_inv_cancel₀ hX
    linear_combination (-P.ιB x) * hc - P.ιB y * hx1
  apply StLat.not_frac l Co ϖ hϖ u hu (T.eB x) (T.eB (y - a • x))
  · rw [← hC.ι]
    exact fun h0 => hX (T.eD.injective (h0.trans (map_zero _).symm))
  · rw [← hC.ι, ← hC.ι, hY, map_mul, hUdef, RingEquiv.apply_symm_apply]

theorem stRegular : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    IsDomain (Bst P) ∧
    (∀ (K : FinExt l) (b b' : Bst P), b ≠ 0 →
      (∀ g : ↥(GK K), b * actSt P (g : GQ l) b' = actSt P (g : GQ l) b * b') →
      ∃ c : ↥(MaximalUnramifiedExtension l), (c : Om l) ∈ K.1 ∧ b' = algebraMap ↥(MaximalUnramifiedExtension l) (Bst P) c * b) ∧
    (∀ (K : FinExt l) (b : Bst P), b ≠ 0 →
      (∀ g : ↥(GK K), ∃ x : ℚ_[l], actSt P (g : GQ l) b = algebraMap ℚ_[l] (Bst P) x * b) → IsUnit b) := by
  intro l _ P AI ⟨T⟩
  haveI : IsDomain P.R.B := GlobalTheory.RegularRing.isDomain_of_tied T (botExt l)
  obtain ⟨Co, hC⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l P AI T
  have hinj : Co.TensorInj := GlobalTheory.Published.FontaineBcris_holds.tensorInj Co
  have hreg : Co.Regular := GlobalTheory.Published.FontaineBcris_holds.regular Co
  refine ⟨inferInstance, fun K b b' hb h => ?_, fun K b hb h => ?_⟩
  · haveI : CharZero P.R.B := by
      have := (algebraMap ℚ_[l] P.R.B).injective
      exact charZero_of_injective_algebraMap this
    have hA : ∀ (g : GQ l) (p : Bst P), actSt P g p = (p.map ((P.actQ g).toRingEquiv : P.R.B →+* P.R.B)).comp (X + C ((kummer P g : ℚ_[l]) • P.tB)) :=
      fun g p => stHom_apply P (P.actQ g) _ p
    obtain ⟨d, d', hd, e, hf⟩ := GlobalTheory.T.twistedShift_fixed_ratio_const_domain (fun g : ↥(GK K) => (P.actQ (g : GQ l)).toRingEquiv)
      (fun g => (kummer P (g : GQ l) : ℚ_[l]) • P.tB)
      (fun d d' hd hh => StLat.kummer_not_frac l P AI T K d d' hd fun g hg => hh ⟨g, hg⟩) b' b hb (fun g => by
        rw [← hA, ← hA]; exact h g)
    obtain ⟨c, hc⟩ := GlobalTheory.RegularRing.fracInv hC hinj K d d' hd fun g => by
      rw [P.PD_actB, P.PD_actB]; exact hf g
    refine ⟨⟨c, c.2.2⟩, c.2.1, ?_⟩
    have hd' : (C d : Bst P) ≠ 0 := C_ne_zero.2 hd
    apply mul_left_cancel₀ hd'
    have hK0 : algebraMap ↥(K0 K) P.R.B c = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B ⟨c, c.2.2⟩ := rfl
    rw [e, hc, Polynomial.algebraMap_apply, C_mul, hK0]
    ring
  · have hK : ∀ b : P.R.B, ¬ ∀ g ∈ GK K, P.actQ g b - b = (kummer P g : ℚ_[l]) • P.tB :=
      GlobalTheory.Pst.NoLog.kummer_not_coboundary l P AI T K
    exact GlobalTheory.T.isUnit_of_stable_line' l P K hK (GlobalTheory.RegularRing.lineUnit hC hreg K) b hb h

end GlobalTheory.Pst
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.mem_hyperspecial_of_split_place_stabilizer : ∀ {D : D7} (V : HSp D) (e : Formalism.L2.Theta.AE D) (g : GA D V), IsSplitIdem D e → Formalism.L2.Theta.SuppAt e V g → (∀ y ∈ LamHat V, (fun a => finPart D e * (finMat D.sp.cm.sig V.gram g).mulVec y a) ∈ LamHat V) → (∀ y ∈ LamHat V, ∃ z ∈ LamHat V, (fun a => finPart D e * y a) = fun a => finPart D e * (finMat D.sp.cm.sig V.gram g).mulVec z a) → g ∈ KsphC V ∅ := by
  first | exact @GlobalTheory.SplitStab.mem_ksph_of_split | exact GlobalTheory.SplitStab.mem_ksph_of_split | (intros; apply GlobalTheory.SplitStab.mem_ksph_of_split <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.completedLattice_integrality : ∀ {D : D7} (V : HSp D), (∀ a ∈ intAE D, ∀ y ∈ LamHat V, (fun i => a * y i) ∈ LamHat V) ∧ (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D) (ϖ ϖ' : 𝓞 D.host.E), IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → ϖ' ∈ P.asIdeal → ϖ' ∉ P.asIdeal ^ 2 → ∀ n : ℤ, finPart D e * finPart D (incA D ((ϖ' : D.host.E) ^ n / (ϖ : D.host.E) ^ n)) ∈ intAE D) ∧ ∀ (ε : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) (B : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)), ε * ε = ε → (∀ y ∈ LamHat V, ∃ z, (fun a => ε * y a) = fun a => ε * B.mulVec z a) → ∃ C : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E), ε • (B * C) = ε • (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) ∧ ε • (C * B) = ε • (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) := by
  first | exact @GlobalTheory.LatIntFacts.int_facts | exact GlobalTheory.LatIntFacts.int_facts | (intros; apply GlobalTheory.LatIntFacts.int_facts <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat
open Formalism.UG (bc prV)
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.adelicMatrix_one_at_place_scaled_preserves_completedLattice : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    (Lb : Submodule (𝓞 E) (Fin N → E)), Lb.FG → Submodule.span E (Lb : Set (Fin N → E)) = ⊤ →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (k : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)), bc (prV (E := E) v) k = 1 →
    ∃ t : 𝓞 F, t ∉ v.asIdeal ∧ ∀ z ∈ Formalism.L2.Herm.hatL (F := F) Lb,
      Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((algebraMap (𝓞 F) (𝓞 E) t : 𝓞 E) : E) •
        ((k : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ z) ∈ Formalism.L2.Herm.hatL (F := F) Lb := by
  first | exact @GlobalTheory.AwayScale.main | exact GlobalTheory.AwayScale.main | (intros; apply GlobalTheory.AwayScale.main <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.upward_theta_lift_injective_on_carried_part : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.PThmB → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → ∀ p c, R.Carries p c → ∀ w ∈ R.EEc c, w ≠ 0 → LinearMap.adjoint (R.Th A3.A.μ0) w ≠ 0 := by
  first | exact @GlobalTheory.thetaUp_injective_on_carried | exact GlobalTheory.thetaUp_injective_on_carried | (intros; apply GlobalTheory.thetaUp_injective_on_carried <;> assumption)
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

theorem _root_.GlobalTheory.T.kappa_norm_at_splitPrimes : ∀ D : D7, KappaSplit D := by
  first | exact @GlobalTheory.kappaSplit_all | exact GlobalTheory.kappaSplit_all | (intros; apply GlobalTheory.kappaSplit_all <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms Formalism.L2.Col Formalism.L2.DIV Formalism.HermitianLatticesTheory GlobalTheory.KerJ NumberField IsDedekindDomain Classical

namespace GlobalTheory.KerTieEntire

theorem kerTie_entire : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), ∀ u μ, ∀ i < D.R.m, ∀ c c', Differentiable ℂ ((t.O u μ).Th i c c') := by
  intro D L hT Gi Gl K Y cX ex t u μ i _ c c'
  have hEven : ∀ j, Even (D.R.N j) := fun j => D.R.k_even.add (D.R.t_odd.add_one.mul_left j)
  have hAdm : TaylorLogMetric.admitted D _ _ ((t.O u μ).lat i c).1 ((t.O u μ).lat (i + 1) c').1 :=
    ⟨hEven i, hEven (i + 1), ((t.O u μ).lat i c).2, ((t.O u μ).lat (i + 1) c').2⟩
  rw [t.O_lat u μ i c, t.O_lat u μ (i + 1) c'] at hAdm
  rw [t.O_Th u μ i c c']
  have hF := GlobalTheory.KerFinEntire.kerFin_entire D t.X t.seam t.cc t.δ t.B t.χ t.cD t.seam_ok t.cc_ok t.δ_ok t.χ_ok _ _
    ((t.rd u μ).N i c) ((t.rd u μ).N (i + 1) c') hAdm (t.rd u μ).SS (t.rd u μ).lev ((t.rd u μ).Xi i c c')
  let T : TaylorLogMetric.VC D (D.R.N i) (D.R.N (i + 1)) →L[ℂ] VCx t.X.Tau (D.R.N i) (D.R.N (i + 1)) :=
    ContinuousLinearMap.pi fun τ => ContinuousLinearMap.proj (t.seam.iT τ)
  exact hF.comp T.differentiable

end GlobalTheory.KerTieEntire
end
end

section

open Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory.SatakeUnitDeterminantBasis

theorem detB : ∀ (D : D7) (Dx : DivX D) (Tw : TwForms D) (E : KerEnt D Dx Tw) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (O : GL3Theta.LiftObj D (D.chTw u μ)) (w : D.what₂.places.Pl) (T : GL3Columns.KFTie E O w), T.detB := by
  intro D Dx Tw E u μ O w T idl hp i hi c τ
  have hb := T.B_bas i hi c τ
  rw [O.dt_lat, hp.2.2.2.2]
  exact GlobalTheory.T.padic_norm_det_lattice_basis_eq_det_ideal_norm D _ (E.lam w) τ _ _ _ _ (O.lattice_integral_coordinates i) hb.1 hb.2.1 hb.2.2

end GlobalTheory.SatakeUnitDeterminantBasis
end
